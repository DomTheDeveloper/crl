#include <algorithm>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <numeric>
#include <optional>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

#include <omp.h>

namespace {

struct Point {
    int x{};
    int y{};
};

struct LineKey {
    int a{};
    int b{};
    int c{};
    bool operator<(const LineKey& other) const noexcept {
        return std::tie(a, b, c) < std::tie(other.a, other.b, other.c);
    }
};

struct Instance {
    int n{};
    int parity{};
    std::vector<Point> points;
    std::vector<std::vector<int>> lines;
    std::vector<std::vector<int>> incident;
    std::vector<int> pair_line; // N*N; -1 if the pair's maximal line has <3 available points.
};

struct Options {
    int n = 22;
    int parity = 0;
    int target = 34;
    int threads = 0;
    std::uint64_t seed = 0xD1A0'0022'34ULL;
    std::uint64_t trials = 20000;
    std::uint64_t steps = 250000;
    std::uint64_t restart_steps = 25000;
    std::uint64_t breakout_period = 2500;
    std::uint64_t progress_period = 250;
    double random_walk = 0.025;
    double temperature = 0.18;
    std::string witness_path = "dmono22_witness.txt";
    bool quiet = false;
    bool double_boundary = false;
    std::array<int, 4> boundary_masks{-1, -1, -1, -1};
};

class SplitMix64 {
public:
    explicit SplitMix64(std::uint64_t seed) : state_(seed) {}
    std::uint64_t operator()() noexcept {
        std::uint64_t z = (state_ += 0x9E3779B97F4A7C15ULL);
        z = (z ^ (z >> 30U)) * 0xBF58476D1CE4E5B9ULL;
        z = (z ^ (z >> 27U)) * 0x94D049BB133111EBULL;
        return z ^ (z >> 31U);
    }
    int uniform_int(int bound) noexcept {
        if (bound <= 1) return 0;
        const std::uint64_t threshold = -static_cast<std::uint64_t>(bound) % static_cast<std::uint64_t>(bound);
        while (true) {
            const std::uint64_t r = (*this)();
            if (r >= threshold) return static_cast<int>(r % static_cast<std::uint64_t>(bound));
        }
    }
    double uniform01() noexcept {
        return static_cast<double>((*this)() >> 11U) * (1.0 / 9007199254740992.0);
    }
private:
    std::uint64_t state_;
};

std::uint64_t split_seed(std::uint64_t base, std::uint64_t trial) {
    SplitMix64 g(base ^ (0xD6E8FEB86659FD93ULL * (trial + 1)));
    return g();
}

long long choose2(int x) noexcept {
    return x >= 2 ? static_cast<long long>(x) * (x - 1) / 2 : 0;
}

long long choose3(int x) noexcept {
    return x >= 3 ? static_cast<long long>(x) * (x - 1) * (x - 2) / 6 : 0;
}

LineKey line_key(const Point& p, const Point& q) {
    int dx = q.x - p.x;
    int dy = q.y - p.y;
    const int g = std::gcd(std::abs(dx), std::abs(dy));
    dx /= g;
    dy /= g;
    if (dx < 0 || (dx == 0 && dy < 0)) {
        dx = -dx;
        dy = -dy;
    }
    // Primitive normal (a,b)=(dy,-dx), fixed by the canonical direction above.
    const int a = dy;
    const int b = -dx;
    const int c = -(a * p.x + b * p.y);
    return {a, b, c};
}

Instance build_instance(int n, int parity) {
    Instance inst;
    inst.n = n;
    inst.parity = parity;
    for (int y = 0; y < n; ++y) {
        for (int x = 0; x < n; ++x) {
            if (((x + y) & 1) == parity) inst.points.push_back({x, y});
        }
    }

    std::map<LineKey, std::set<int>> by_key;
    const int N = static_cast<int>(inst.points.size());
    for (int i = 0; i < N; ++i) {
        for (int j = i + 1; j < N; ++j) {
            const LineKey key = line_key(inst.points[i], inst.points[j]);
            auto& s = by_key[key];
            s.insert(i);
            s.insert(j);
        }
    }

    std::map<LineKey, int> key_to_line;
    for (const auto& [key, pts] : by_key) {
        if (pts.size() >= 3) {
            key_to_line.emplace(key, static_cast<int>(inst.lines.size()));
            inst.lines.emplace_back(pts.begin(), pts.end());
        }
    }

    inst.incident.assign(N, {});
    for (int l = 0; l < static_cast<int>(inst.lines.size()); ++l) {
        for (int p : inst.lines[l]) inst.incident[p].push_back(l);
    }

    inst.pair_line.assign(N * N, -1);
    for (int i = 0; i < N; ++i) {
        for (int j = i + 1; j < N; ++j) {
            const auto it = key_to_line.find(line_key(inst.points[i], inst.points[j]));
            if (it != key_to_line.end()) {
                inst.pair_line[i * N + j] = it->second;
                inst.pair_line[j * N + i] = it->second;
            }
        }
    }
    return inst;
}

bool exact_verify(const Instance& inst, const std::vector<int>& selected, std::string* reason = nullptr) {
    if (selected.empty()) {
        if (reason) *reason = "empty selection";
        return false;
    }
    std::vector<int> s = selected;
    std::sort(s.begin(), s.end());
    if (std::adjacent_find(s.begin(), s.end()) != s.end()) {
        if (reason) *reason = "duplicate point index";
        return false;
    }
    for (int idx : s) {
        if (idx < 0 || idx >= static_cast<int>(inst.points.size())) {
            if (reason) *reason = "point index out of range";
            return false;
        }
        const Point p = inst.points[idx];
        if (p.x < 0 || p.x >= inst.n || p.y < 0 || p.y >= inst.n || ((p.x + p.y) & 1) != inst.parity) {
            if (reason) *reason = "point outside requested checkerboard class";
            return false;
        }
    }
    for (std::size_t i = 0; i < s.size(); ++i) {
        const auto& a = inst.points[s[i]];
        for (std::size_t j = i + 1; j < s.size(); ++j) {
            const auto& b = inst.points[s[j]];
            for (std::size_t k = j + 1; k < s.size(); ++k) {
                const auto& c = inst.points[s[k]];
                const long long det = static_cast<long long>(b.x - a.x) * (c.y - a.y)
                                    - static_cast<long long>(b.y - a.y) * (c.x - a.x);
                if (det == 0) {
                    if (reason) {
                        std::ostringstream out;
                        out << "collinear triple: (" << a.x << ',' << a.y << ") ("
                            << b.x << ',' << b.y << ") (" << c.x << ',' << c.y << ')';
                        *reason = out.str();
                    }
                    return false;
                }
            }
        }
    }
    return true;
}

void write_witness(const Instance& inst, const std::vector<int>& selected, const Options& opt,
                   std::uint64_t trial, std::uint64_t trial_seed) {
    std::vector<Point> pts;
    pts.reserve(selected.size());
    for (int idx : selected) pts.push_back(inst.points[idx]);
    std::sort(pts.begin(), pts.end(), [](const Point& a, const Point& b) {
        return std::tie(a.y, a.x) < std::tie(b.y, b.x);
    });
    std::ofstream out(opt.witness_path);
    if (!out) throw std::runtime_error("cannot open witness output: " + opt.witness_path);
    out << "# D_mono checkerboard NTIL witness\n";
    out << "# n=" << inst.n << " parity=" << inst.parity << " size=" << pts.size() << '\n';
    out << "# trial=" << trial << " trial_seed=" << trial_seed << '\n';
    for (const Point& p : pts) out << p.x << ' ' << p.y << '\n';
}


struct TrialConstraint {
    std::vector<unsigned char> fixed;
    std::vector<unsigned char> forbidden;
    std::array<int, 4> masks{-1, -1, -1, -1};
    bool valid = true;
};

int point_index(const Instance& inst, int x, int y) {
    for (int i = 0; i < static_cast<int>(inst.points.size()); ++i) {
        if (inst.points[i].x == x && inst.points[i].y == y) return i;
    }
    return -1;
}

TrialConstraint make_double_boundary_constraint(const Instance& inst, const Options& opt, SplitMix64& rng) {
    TrialConstraint tc;
    const int N = static_cast<int>(inst.points.size());
    tc.fixed.assign(N, 0);
    tc.forbidden.assign(N, 0);
    if (inst.n != 22 || inst.parity != 0) {
        tc.valid = false;
        return tc;
    }

    std::array<std::vector<int>, 4> boundary;
    for (int i = 0; i < 11; ++i) {
        boundary[0].push_back(point_index(inst, 0, 2 * i));
        boundary[1].push_back(point_index(inst, 2 * i, 0));
        boundary[2].push_back(point_index(inst, 21, 21 - 2 * i));
        boundary[3].push_back(point_index(inst, 21 - 2 * i, 21));
    }
    for (const auto& b : boundary) {
        if (std::find(b.begin(), b.end(), -1) != b.end()) {
            tc.valid = false;
            return tc;
        }
    }

    std::vector<int> doubles;
    for (int i = 0; i < 11; ++i) {
        for (int j = i + 1; j < 11; ++j) doubles.push_back((1 << i) | (1 << j));
    }
    // Canonical top mask: the other three oriented masks are at least top.
    auto is_double = [](int m) { return m >= 0 && __builtin_popcount(static_cast<unsigned>(m)) == 2 && m < (1 << 11); };
    const int top = opt.boundary_masks[0] >= 0 ? opt.boundary_masks[0]
                                                  : doubles[rng.uniform_int(static_cast<int>(doubles.size()))];
    if (!is_double(top)) { tc.valid = false; return tc; }
    const bool all_explicit = std::all_of(opt.boundary_masks.begin(), opt.boundary_masks.end(), [](int m) { return m >= 0; });
    std::vector<int> allowed;
    for (int m : doubles) if (all_explicit || m >= top) allowed.push_back(m);
    std::vector<int> left_allowed;
    for (int m : allowed) if (bool(m & 1) == bool(top & 1)) left_allowed.push_back(m);
    if (left_allowed.empty()) {
        tc.valid = false;
        return tc;
    }
    const int left = opt.boundary_masks[1] >= 0 ? opt.boundary_masks[1]
                                                   : left_allowed[rng.uniform_int(static_cast<int>(left_allowed.size()))];
    if (!is_double(left) || (!all_explicit && left < top) || bool(left & 1) != bool(top & 1)) { tc.valid = false; return tc; }
    const int rb = opt.boundary_masks[2] >= 0 ? opt.boundary_masks[2]
                                               : allowed[rng.uniform_int(static_cast<int>(allowed.size()))];
    if (!is_double(rb) || (!all_explicit && rb < top)) { tc.valid = false; return tc; }
    std::vector<int> rr_allowed;
    for (int m : allowed) if (bool(m & 1) == bool(rb & 1)) rr_allowed.push_back(m);
    if (rr_allowed.empty()) {
        tc.valid = false;
        return tc;
    }
    const int rr = opt.boundary_masks[3] >= 0 ? opt.boundary_masks[3]
                                               : rr_allowed[rng.uniform_int(static_cast<int>(rr_allowed.size()))];
    if (!is_double(rr) || (!all_explicit && rr < top) || bool(rr & 1) != bool(rb & 1)) { tc.valid = false; return tc; }
    tc.masks = {top, left, rb, rr};

    for (int k = 0; k < 4; ++k) {
        for (int i = 0; i < 11; ++i) {
            const int p = boundary[k][i];
            if ((tc.masks[k] >> i) & 1) tc.fixed[p] = 1;
            else tc.forbidden[p] = 1;
        }
    }
    // A point shared by two boundaries must have consistent assignments.
    for (int p = 0; p < N; ++p) {
        if (tc.fixed[p] && tc.forbidden[p]) {
            tc.valid = false;
            return tc;
        }
    }
    return tc;
}

struct SearchState {
    const Instance& inst;
    const Options& opt;
    SplitMix64 rng;
    const int N;
    const int L;

    std::vector<unsigned char> in;
    std::vector<unsigned char> fixed;
    std::vector<unsigned char> forbidden;
    std::vector<int> selected;
    std::vector<int> pos;
    std::vector<int> count;
    std::vector<int> weight;
    std::vector<std::uint64_t> tabu_until;
    long long raw_score = 0;
    long long weighted_score = 0;

    SearchState(const Instance& instance, const Options& options, std::uint64_t seed,
                const TrialConstraint* constraint = nullptr)
        : inst(instance), opt(options), rng(seed), N(static_cast<int>(instance.points.size())),
          L(static_cast<int>(instance.lines.size())), in(N, 0), fixed(N, 0), forbidden(N, 0),
          pos(N, -1), count(L, 0), weight(L, 1), tabu_until(N, 0) {
        if (constraint) {
            fixed = constraint->fixed;
            forbidden = constraint->forbidden;
        }
        selected.reserve(opt.target);
    }

    void clear() {
        std::fill(in.begin(), in.end(), 0);
        std::fill(pos.begin(), pos.end(), -1);
        std::fill(count.begin(), count.end(), 0);
        std::fill(weight.begin(), weight.end(), 1);
        std::fill(tabu_until.begin(), tabu_until.end(), 0);
        selected.clear();
        raw_score = 0;
        weighted_score = 0;
    }

    void add_raw(int p) {
        in[p] = 1;
        pos[p] = static_cast<int>(selected.size());
        selected.push_back(p);
        for (int l : inst.incident[p]) {
            raw_score += choose2(count[l]);
            weighted_score += static_cast<long long>(weight[l]) * choose2(count[l]);
            ++count[l];
        }
    }

    void remove_raw(int p) {
        for (int l : inst.incident[p]) {
            --count[l];
            raw_score -= choose2(count[l]);
            weighted_score -= static_cast<long long>(weight[l]) * choose2(count[l]);
        }
        const int at = pos[p];
        const int last = selected.back();
        selected[at] = last;
        pos[last] = at;
        selected.pop_back();
        pos[p] = -1;
        in[p] = 0;
    }

    long long point_conflict(int p, bool weighted) const {
        long long value = 0;
        for (int l : inst.incident[p]) {
            const long long contribution = choose2(count[l] - 1);
            value += weighted ? static_cast<long long>(weight[l]) * contribution : contribution;
        }
        return value;
    }

    std::pair<long long, long long> swap_delta(int out, int in_point) const {
        long long dr = 0;
        long long dw = 0;
        for (int l : inst.incident[out]) {
            const long long v = choose2(count[l] - 1);
            dr -= v;
            dw -= static_cast<long long>(weight[l]) * v;
        }
        for (int l : inst.incident[in_point]) {
            const long long v = choose2(count[l]);
            dr += v;
            dw += static_cast<long long>(weight[l]) * v;
        }
        const int shared = inst.pair_line[out * N + in_point];
        if (shared >= 0) {
            const long long correction = count[shared] - 1;
            dr -= correction;
            dw -= static_cast<long long>(weight[shared]) * correction;
        }
        return {dr, dw};
    }

    void do_swap(int out, int in_point, std::uint64_t step) {
        remove_raw(out);
        add_raw(in_point);
        tabu_until[out] = step + 7 + static_cast<std::uint64_t>(rng.uniform_int(11));
    }

    bool initialise_greedy() {
        clear();
        for (int p = 0; p < N; ++p) if (fixed[p]) add_raw(p);
        if (raw_score != 0 || static_cast<int>(selected.size()) > opt.target) return false;
        std::vector<int> order(N);
        std::iota(order.begin(), order.end(), 0);
        for (int i = N - 1; i > 0; --i) std::swap(order[i], order[rng.uniform_int(i + 1)]);

        // Randomized greedy construction that strongly prefers additions creating no triples.
        while (static_cast<int>(selected.size()) < opt.target) {
            int best = -1;
            long long best_cost = std::numeric_limits<long long>::max();
            int ties = 0;
            for (int p : order) {
                if (in[p] || forbidden[p]) continue;
                long long cost = 0;
                for (int l : inst.incident[p]) cost += choose2(count[l]);
                // Mild occupancy penalty helps distribute points before violations appear.
                long long spread = 0;
                for (int l : inst.incident[p]) spread += count[l];
                const long long key = 1000 * cost + spread;
                if (key < best_cost) {
                    best_cost = key;
                    best = p;
                    ties = 1;
                } else if (key == best_cost && rng.uniform_int(++ties) == 0) {
                    best = p;
                }
            }
            if (best < 0) break;
            add_raw(best);
        }
        return static_cast<int>(selected.size()) == opt.target;
    }

    int choose_out_point() {
        std::vector<int> movable;
        movable.reserve(selected.size());
        for (int p : selected) if (!fixed[p]) movable.push_back(p);
        if (movable.empty()) return -1;
        if (rng.uniform01() < 0.08) return movable[rng.uniform_int(static_cast<int>(movable.size()))];
        long long total = 0;
        std::vector<long long> contribution(movable.size());
        for (std::size_t i = 0; i < movable.size(); ++i) {
            contribution[i] = point_conflict(movable[i], true);
            total += contribution[i];
        }
        if (total <= 0) return movable[rng.uniform_int(static_cast<int>(movable.size()))];
        std::uint64_t r = rng() % static_cast<std::uint64_t>(total);
        for (std::size_t i = 0; i < movable.size(); ++i) {
            if (r < static_cast<std::uint64_t>(contribution[i])) return movable[i];
            r -= static_cast<std::uint64_t>(contribution[i]);
        }
        return movable.back();
    }

    void breakout() {
        for (int l = 0; l < L; ++l) {
            if (count[l] >= 3) {
                weighted_score += choose3(count[l]);
                if (weight[l] < 1000000) ++weight[l];
            }
        }
        // Prevent unbounded weights while preserving relative pressure.
        int max_w = *std::max_element(weight.begin(), weight.end());
        if (max_w > 4096) {
            weighted_score = 0;
            for (int l = 0; l < L; ++l) {
                weight[l] = std::max(1, weight[l] / 2);
                weighted_score += static_cast<long long>(weight[l]) * choose3(count[l]);
            }
        }
    }

    bool run(std::uint64_t max_steps, std::atomic<bool>& found,
             long long& local_best_score, std::vector<int>& local_best) {
        if (!initialise_greedy()) {
            local_best_score = std::numeric_limits<long long>::max();
            local_best.clear();
            return false;
        }
        local_best_score = raw_score;
        local_best = selected;
        if (raw_score == 0) return true;

        std::uint64_t last_improvement = 0;
        long long best_weighted = weighted_score;

        for (std::uint64_t step = 1; step <= max_steps && !found.load(std::memory_order_relaxed); ++step) {
            if (opt.restart_steps > 0 && step - last_improvement >= opt.restart_steps) {
                if (!initialise_greedy()) return false;
                last_improvement = step;
                best_weighted = weighted_score;
                if (raw_score < local_best_score) {
                    local_best_score = raw_score;
                    local_best = selected;
                }
                if (raw_score == 0) return true;
                continue;
            }

            if (opt.breakout_period > 0 && step % opt.breakout_period == 0) breakout();

            const int out = choose_out_point();
            if (out < 0) return false;
            int chosen_in = -1;
            long long chosen_dw = std::numeric_limits<long long>::max();
            long long chosen_dr = std::numeric_limits<long long>::max();
            int ties = 0;

            if (rng.uniform01() < opt.random_walk) {
                do {
                    chosen_in = rng.uniform_int(N);
                } while (in[chosen_in] || forbidden[chosen_in]);
                const auto [dr, dw] = swap_delta(out, chosen_in);
                chosen_dr = dr;
                chosen_dw = dw;
            } else {
                for (int q = 0; q < N; ++q) {
                    if (in[q] || forbidden[q]) continue;
                    const auto [dr, dw] = swap_delta(out, q);
                    const bool tabu = tabu_until[q] > step;
                    const bool aspiration = raw_score + dr < local_best_score;
                    if (tabu && !aspiration) continue;
                    if (dw < chosen_dw || (dw == chosen_dw && dr < chosen_dr)) {
                        chosen_dw = dw;
                        chosen_dr = dr;
                        chosen_in = q;
                        ties = 1;
                    } else if (dw == chosen_dw && dr == chosen_dr && rng.uniform_int(++ties) == 0) {
                        chosen_in = q;
                    }
                }
            }

            if (chosen_in < 0) continue;
            bool accept = chosen_dw <= 0;
            if (!accept && opt.temperature > 0.0) {
                const double scale = opt.temperature * (1.0 + std::log1p(static_cast<double>(weighted_score)));
                const double probability = std::exp(-static_cast<double>(chosen_dw) / std::max(1e-9, scale));
                accept = rng.uniform01() < probability;
            }
            if (!accept) {
                // Forced least-damaging move avoids frozen local minima.
                accept = (step % 17 == 0);
            }
            if (!accept) continue;

            do_swap(out, chosen_in, step);
            if (weighted_score < best_weighted) {
                best_weighted = weighted_score;
                last_improvement = step;
            }
            if (raw_score < local_best_score) {
                local_best_score = raw_score;
                local_best = selected;
                last_improvement = step;
                if (raw_score == 0) return true;
            }
        }
        return false;
    }
};

void usage(const char* argv0) {
    std::cerr
        << "Usage: " << argv0 << " [options]\n"
        << "  --n N                 grid side (default 22)\n"
        << "  --parity P            checkerboard parity 0 or 1 (default 0)\n"
        << "  --target K            fixed selected cardinality (default 34)\n"
        << "  --threads T           OpenMP threads; 0 uses runtime default\n"
        << "  --seed S              base uint64 seed\n"
        << "  --trials R            independent replicas (default 20000)\n"
        << "  --steps M             local-search steps per replica\n"
        << "  --restart-steps M     restart after M nonimproving steps\n"
        << "  --breakout-period M   increment violated-line weights every M steps\n"
        << "  --random-walk P       random move probability\n"
        << "  --temperature X       uphill acceptance temperature\n"
        << "  --witness FILE        witness output path\n"
        << "  --double-boundary     fix exactly two points on each outer boundary per replica\n"
        << "  --top-mask M          exact oriented top mask (two of 11 bits)\n"
        << "  --left-mask M         exact oriented left mask\n"
        << "  --rb-mask M           exact oriented reversed-bottom mask\n"
        << "  --rr-mask M           exact oriented reversed-right mask\n"
        << "  --quiet               suppress progress lines\n";
}

Options parse_options(int argc, char** argv) {
    Options opt;
    auto need = [&](int& i) -> std::string {
        if (++i >= argc) throw std::runtime_error(std::string("missing value after ") + argv[i - 1]);
        return argv[i];
    };
    for (int i = 1; i < argc; ++i) {
        const std::string a = argv[i];
        if (a == "--n") opt.n = std::stoi(need(i));
        else if (a == "--parity") opt.parity = std::stoi(need(i));
        else if (a == "--target") opt.target = std::stoi(need(i));
        else if (a == "--threads") opt.threads = std::stoi(need(i));
        else if (a == "--seed") opt.seed = std::stoull(need(i), nullptr, 0);
        else if (a == "--trials") opt.trials = std::stoull(need(i));
        else if (a == "--steps") opt.steps = std::stoull(need(i));
        else if (a == "--restart-steps") opt.restart_steps = std::stoull(need(i));
        else if (a == "--breakout-period") opt.breakout_period = std::stoull(need(i));
        else if (a == "--random-walk") opt.random_walk = std::stod(need(i));
        else if (a == "--temperature") opt.temperature = std::stod(need(i));
        else if (a == "--witness") opt.witness_path = need(i);
        else if (a == "--double-boundary") opt.double_boundary = true;
        else if (a == "--top-mask") { opt.double_boundary = true; opt.boundary_masks[0] = std::stoi(need(i), nullptr, 0); }
        else if (a == "--left-mask") { opt.double_boundary = true; opt.boundary_masks[1] = std::stoi(need(i), nullptr, 0); }
        else if (a == "--rb-mask") { opt.double_boundary = true; opt.boundary_masks[2] = std::stoi(need(i), nullptr, 0); }
        else if (a == "--rr-mask") { opt.double_boundary = true; opt.boundary_masks[3] = std::stoi(need(i), nullptr, 0); }
        else if (a == "--quiet") opt.quiet = true;
        else if (a == "--help" || a == "-h") {
            usage(argv[0]);
            std::exit(0);
        } else {
            throw std::runtime_error("unknown option: " + a);
        }
    }
    if (opt.n < 2 || opt.parity < 0 || opt.parity > 1 || opt.target < 1 ||
        opt.random_walk < 0.0 || opt.random_walk > 1.0 || opt.temperature < 0.0) {
        throw std::runtime_error("invalid option value");
    }
    return opt;
}

} // namespace

int main(int argc, char** argv) {
    try {
        const Options opt = parse_options(argc, argv);
        if (opt.threads > 0) omp_set_num_threads(opt.threads);
        const Instance inst = build_instance(opt.n, opt.parity);
        if (opt.target > static_cast<int>(inst.points.size())) {
            throw std::runtime_error("target exceeds parity-class size");
        }

        std::cout << "instance n=" << opt.n << " parity=" << opt.parity
                  << " points=" << inst.points.size() << " maximal_lines_ge3=" << inst.lines.size()
                  << " target=" << opt.target << " threads=" << omp_get_max_threads() << '\n';

        std::atomic<bool> found(false);
        std::atomic<std::uint64_t> completed(0);
        std::atomic<long long> global_best(std::numeric_limits<long long>::max());
        std::vector<int> best_set;
        std::vector<int> witness;
        std::uint64_t witness_trial = 0;
        std::uint64_t witness_seed = 0;

        const auto start = std::chrono::steady_clock::now();

        #pragma omp parallel
        {
            #pragma omp for schedule(static, 1)
            for (std::uint64_t trial = 0; trial < opt.trials; ++trial) {
                if (found.load(std::memory_order_relaxed)) continue;
                const std::uint64_t t_seed = split_seed(opt.seed, trial);
                SplitMix64 constraint_rng(t_seed ^ 0xB0A7D4A55ULL);
                TrialConstraint constraint;
                const TrialConstraint* constraint_ptr = nullptr;
                if (opt.double_boundary) {
                    constraint = make_double_boundary_constraint(inst, opt, constraint_rng);
                    if (!constraint.valid) {
                        completed.fetch_add(1, std::memory_order_relaxed);
                        continue;
                    }
                    constraint_ptr = &constraint;
                }
                SearchState state(inst, opt, t_seed, constraint_ptr);
                long long local_best_score = std::numeric_limits<long long>::max();
                std::vector<int> local_best;
                const bool hit = state.run(opt.steps, found, local_best_score, local_best);

                long long observed = global_best.load(std::memory_order_relaxed);
                if (local_best_score < observed) {
                    #pragma omp critical(best_update)
                    {
                        if (local_best_score < global_best.load(std::memory_order_relaxed)) {
                            global_best.store(local_best_score, std::memory_order_relaxed);
                            best_set = local_best;
                            if (!opt.quiet) {
                                const auto now = std::chrono::steady_clock::now();
                                const double sec = std::chrono::duration<double>(now - start).count();
                                std::cerr << "best triples=" << local_best_score << " trial=" << trial
                                          << " elapsed=" << std::fixed << std::setprecision(2) << sec << "s\n";
                            }
                        }
                    }
                }

                if (hit) {
                    std::string reason;
                    if (!exact_verify(inst, state.selected, &reason)) {
                        #pragma omp critical(io)
                        std::cerr << "INTERNAL ERROR: candidate failed exact verification: " << reason << '\n';
                        std::abort();
                    }
                    bool expected = false;
                    if (found.compare_exchange_strong(expected, true, std::memory_order_acq_rel)) {
                        #pragma omp critical(witness_update)
                        {
                            witness = state.selected;
                            witness_trial = trial;
                            witness_seed = t_seed;
                        }
                    }
                }

                const std::uint64_t done = completed.fetch_add(1, std::memory_order_relaxed) + 1;
                if (!opt.quiet && opt.progress_period > 0 && done % opt.progress_period == 0) {
                    #pragma omp critical(io)
                    {
                        const auto now = std::chrono::steady_clock::now();
                        const double sec = std::chrono::duration<double>(now - start).count();
                        std::cerr << "completed=" << done << '/' << opt.trials
                                  << " best_triples=" << global_best.load(std::memory_order_relaxed)
                                  << " rate=" << std::fixed << std::setprecision(1)
                                  << (sec > 0 ? done / sec : 0.0) << " trials/s\n";
                    }
                }
            }
        }

        const auto end = std::chrono::steady_clock::now();
        const double seconds = std::chrono::duration<double>(end - start).count();
        if (found.load(std::memory_order_acquire)) {
            std::string reason;
            if (static_cast<int>(witness.size()) != opt.target || !exact_verify(inst, witness, &reason)) {
                throw std::runtime_error("stored witness verification failed: " + reason);
            }
            write_witness(inst, witness, opt, witness_trial, witness_seed);
            std::cout << "SAT witness_size=" << witness.size() << " trial=" << witness_trial
                      << " trial_seed=" << witness_seed << " elapsed_seconds=" << std::fixed
                      << std::setprecision(3) << seconds << " output=" << opt.witness_path << '\n';
            return 0;
        }

        if (!best_set.empty()) {
            const std::string near_path = opt.witness_path + ".best";
            Options near_opt = opt;
            near_opt.witness_path = near_path;
            write_witness(inst, best_set, near_opt, std::numeric_limits<std::uint64_t>::max(), 0);
            std::cout << "NO_WITNESS completed_trials=" << completed.load() << " steps_per_trial=" << opt.steps
                      << " best_collinear_triples=" << global_best.load() << " elapsed_seconds="
                      << std::fixed << std::setprecision(3) << seconds << " best_output=" << near_path << '\n';
        } else {
            std::cout << "NO_WITNESS completed_trials=" << completed.load() << " steps_per_trial=" << opt.steps
                      << " best_collinear_triples=" << global_best.load() << " elapsed_seconds="
                      << std::fixed << std::setprecision(3) << seconds << '\n';
        }
        std::cout << "NOTE heuristic search exhaustion is not an UNSAT certificate.\n";
        return 2;
    } catch (const std::exception& e) {
        std::cerr << "error: " << e.what() << '\n';
        return 1;
    }
}
