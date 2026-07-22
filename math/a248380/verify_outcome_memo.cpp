#include <bits/stdc++.h>
using namespace std;
using u64 = uint64_t;

struct Key {
  array<u64, 4> w{};
  bool operator==(Key const& o) const { return w == o.w; }
};

struct Hash {
  size_t operator()(Key const& k) const {
    u64 h = 0x9e3779b97f4a7c15ULL;
    for (u64 v : k.w) {
      v += 0x9e3779b97f4a7c15ULL;
      v = (v ^ (v >> 30)) * 0xbf58476d1ce4e5b9ULL;
      v = (v ^ (v >> 27)) * 0x94d049bb133111ebULL;
      v ^= v >> 31;
      h ^= v + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
    }
    return h;
  }
};

inline bool bit(Key const& k, int n) {
  return (k.w[n >> 6] >> (n & 63)) & 1ULL;
}

inline void setb(Key& k, int n) {
  k.w[n >> 6] |= 1ULL << (n & 63);
}

Key child(Key const& gaps, int x, int frobenius) {
  Key result;
  for (int residue = 1; residue <= min(x - 1, frobenius); residue++)
    for (int n = residue; n <= frobenius && bit(gaps, n); n += x)
      setb(result, n);
  return result;
}

Key gapmask(vector<int> generators, int frobenius) {
  int multiplicity = *min_element(generators.begin(), generators.end());
  const long long infinity = 1e18;
  vector<long long> distance(multiplicity, infinity);
  distance[0] = 0;
  using QueueItem = pair<long long, int>;
  priority_queue<QueueItem, vector<QueueItem>, greater<QueueItem>> queue;
  queue.push({0, 0});
  while (!queue.empty()) {
    auto [current, residue] = queue.top();
    queue.pop();
    if (current != distance[residue]) continue;
    for (int generator : generators) {
      long long next = current + generator;
      int nextResidue = next % multiplicity;
      if (next < distance[nextResidue]) {
        distance[nextResidue] = next;
        queue.push({next, nextResidue});
      }
    }
  }
  Key result;
  for (int n = 1; n <= frobenius; n++)
    if (n < distance[n % multiplicity]) setb(result, n);
  return result;
}

int main(int argc, char** argv) {
  if (argc < 2) {
    cerr << "usage: verify_outcome_memo memo.bin\n";
    return 2;
  }

  ifstream input(argv[1], ios::binary);
  char magic[8];
  int frobenius;
  input.read(magic, 8);
  input.read(reinterpret_cast<char*>(&frobenius), sizeof(frobenius));
  if (!input || string(magic, 8) != "SYLVMEM1") {
    cerr << "invalid memo header\n";
    return 2;
  }

  unordered_map<Key, int16_t, Hash> memo;
  memo.reserve(22000000);
  Key state;
  int16_t outcome;
  while (input.read(reinterpret_cast<char*>(state.w.data()), sizeof(u64) * 4)) {
    input.read(reinterpret_cast<char*>(&outcome), sizeof(outcome));
    if (!input) break;
    memo[state] = outcome;
  }

  cerr << "loaded=" << memo.size() << " F=" << frobenius << "\n";
  Key root = gapmask({16, 26, 83, 127}, frobenius);
  auto rootIt = memo.find(root);
  if (rootIt == memo.end()) {
    cerr << "root is absent\n";
    return 3;
  }
  cerr << "root outcome=" << rootIt->second << "\n";

  vector<Key> stack{root};
  size_t visited = 0, pCount = 0, nCount = 0, edges = 0;
  size_t missing = 0, inconsistent = 0, maxStack = 1;

  auto isP = [](int16_t value) { return value == -1 || value == -2; };
  auto isVisited = [](int16_t value) { return value == -2 || value >= 256; };
  auto witness = [](int16_t value) { return value >= 256 ? int(value - 256) : int(value); };

  while (!stack.empty()) {
    Key current = stack.back();
    stack.pop_back();
    auto currentIt = memo.find(current);
    if (currentIt == memo.end()) {
      missing++;
      continue;
    }
    int16_t raw = currentIt->second;
    if (isVisited(raw)) continue;

    bool pState = isP(raw);
    int selectedMove = witness(raw);
    currentIt->second = pState ? -2 : int16_t(selectedMove + 256);
    visited++;

    if (pState) {
      pCount++;
      for (int move = 2; move <= frobenius; move++) {
        if (!bit(current, move)) continue;
        Key next = child(current, move, frobenius);
        edges++;
        auto nextIt = memo.find(next);
        if (nextIt == memo.end()) {
          missing++;
          continue;
        }
        if (isP(nextIt->second)) {
          inconsistent++;
          cerr << "P state has P child at move " << move << "\n";
          if (inconsistent > 10) break;
        }
        stack.push_back(next);
      }
    } else {
      nCount++;
      if (selectedMove < 2 || selectedMove > frobenius || !bit(current, selectedMove)) {
        inconsistent++;
        cerr << "invalid N witness " << selectedMove << "\n";
        if (inconsistent > 10) break;
        continue;
      }
      Key next = child(current, selectedMove, frobenius);
      edges++;
      auto nextIt = memo.find(next);
      if (nextIt == memo.end()) {
        missing++;
        continue;
      }
      if (!isP(nextIt->second)) {
        inconsistent++;
        cerr << "N witness does not lead to P at move " << selectedMove << "\n";
        if (inconsistent > 10) break;
      }
      stack.push_back(next);
    }
    maxStack = max(maxStack, stack.size());
  }

  cout << "visited=" << visited
       << " P=" << pCount
       << " N=" << nCount
       << " edges=" << edges
       << " missing=" << missing
       << " inconsistent=" << inconsistent
       << " maxStack=" << maxStack << "\n";
  return (missing || inconsistent) ? 1 : 0;
}
