// Exhaustive independent audit of the all-double boundary symmetry partition.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <vector>

using Quad = std::array<int, 4>;  // top, left, right-boundary, right-row

static Quad transform(const Quad& q, int g) {
  static constexpr int p[4][4] = {
      {0, 1, 2, 3},  // identity
      {1, 0, 3, 2},  // transpose
      {2, 3, 0, 1},  // half turn
      {3, 2, 1, 0},  // anti-diagonal reflection
  };
  return {q[p[g][0]], q[p[g][1]], q[p[g][2]], q[p[g][3]]};
}

static bool canonical(const Quad& q) {
  const auto [top, left, rb, rr] = q;
  if (left < top || rb < top || rr < top) return false;
  if ((left & 1) != (top & 1) || (rr & 1) != (rb & 1)) return false;
  Quad least = q;
  for (int g = 1; g < 4; ++g) least = std::min(least, transform(q, g));
  return q == least;
}

int main() {
  std::vector<int> masks;
  std::array<std::vector<int>, 2> by_corner;
  for (int i = 0; i < 11; ++i) {
    for (int j = i + 1; j < 11; ++j) {
      const int m = (1 << i) | (1 << j);
      masks.push_back(m);
      by_corner[m & 1].push_back(m);
    }
  }
  std::sort(masks.begin(), masks.end());
  std::sort(by_corner[0].begin(), by_corner[0].end());
  std::sort(by_corner[1].begin(), by_corner[1].end());

  std::uint64_t valid = 0;
  std::uint64_t orbits = 0;
  std::uint64_t representatives = 0;
  std::uint64_t bad = 0;

  for (int top : masks) {
    for (int left : by_corner[top & 1]) {
      for (int rb : masks) {
        for (int rr : by_corner[rb & 1]) {
          const Quad q{top, left, rb, rr};
          ++valid;
          Quad orbit_min = q;
          std::vector<Quad> orbit;
          for (int g = 0; g < 4; ++g) {
            const Quad z = transform(q, g);
            orbit_min = std::min(orbit_min, z);
            orbit.push_back(z);
          }
          if (q != orbit_min) continue;
          ++orbits;
          std::sort(orbit.begin(), orbit.end());
          orbit.erase(std::unique(orbit.begin(), orbit.end()), orbit.end());
          int count = 0;
          for (const Quad& z : orbit) count += canonical(z);
          representatives += count;
          if (count != 1) ++bad;
        }
      }
    }
  }

  const bool pass = valid == 4515625ULL && orbits == 1130725ULL &&
                    representatives == orbits && bad == 0;
  std::cout << "{\"valid_quadruples\":" << valid
            << ",\"orbits\":" << orbits
            << ",\"canonical_representatives\":" << representatives
            << ",\"bad_orbits\":" << bad
            << ",\"PASS\":" << (pass ? "true" : "false") << "}\n";
  return pass ? 0 : 1;
}
