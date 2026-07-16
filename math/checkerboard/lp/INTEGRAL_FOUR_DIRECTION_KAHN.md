# Integral rounding in the four fixed directions

## Scope boundary

This theorem concerns only rows, columns, and diagonals of slopes `+1` and `-1`. It does not forbid triples on any other slope and therefore does not prove the checkerboard no-three-in-line conjecture.

Let `I4(n, eps)` be the maximum size of a subset of one checkerboard parity class having at most two points on every line in those four direction families. Let `L4(n, eps)` be the corresponding fractional packing optimum.

Assuming the separately proved fractional theorem

```text
L4(n, eps) = alpha n + o(n),
```

the fixed-direction integral theorem is

```text
I4(n, eps) = alpha n + o(n).
```

Equivalently, the additive integrality gap for the four-direction relaxation is `o(n)`.

## Diffuse capacitated rounding theorem

Fix integers `r`, `b`, and `C`. Let `H_n=(V_n,E_n)` be finite hypergraphs such that:

1. every edge has size at most `r`;
2. every vertex `v` has an integral capacity `1 <= b_v <= b`;
3. every pair of distinct vertices belongs together to at most `C` edges.

Let `x_e >= 0` satisfy

```text
sum_{e contains v} x_e <= b_v.
```

Assume

```text
eta_n = max_e x_e -> 0,
W_n = sum_e x_e = Theta(s_n),
s_n -> infinity.
```

Then there are sets of distinct edges `M_n` such that

```text
|M_n| >= W_n - o(s_n),
|{e in M_n : v in e}| <= b_v
```

for every vertex `v`.

### Reduction to Kahn's bounded-rank edge-colouring theorem

Choose an integer scale `N=N(n)` tending to infinity and put

```text
m_e = floor(N x_e).
```

Choose `N` sufficiently large that the total rounding loss `|E_n|/N` is `o(s_n)` and the degree threshold in Kahn's theorem is met.

For each original vertex `v`, create `b_v` clones and distribute the `sum_{e contains v} m_e` copy-incidences evenly among them. Each clone has degree at most `N`.

For every original edge `e`, create one identity vertex `z_e`. For every copy `(e,j)`, create one private dummy vertex. The blown-up edge contains:

- the assigned clone of each original vertex in `e`;
- the identity vertex `z_e`;
- its private dummy vertex.

The blown-up hypergraph has rank at most `r+2`, maximum degree at most `N`, and pair-codegree at most

```text
C N eta_n + C + 1 = o(N).
```

Kahn's asymptotic edge-colouring theorem partitions these blown-up edges into `(1+o(1))N` matchings. Since the number of blown-up edges is `N W_n-o(Ns_n)`, one matching has size `W_n-o(s_n)`. Identity vertices make projection to original edges injective, and clone-disjointness enforces the capacities.

## Checkerboard application

Create one hypergraph vertex for every row, column, slope-`+1` diagonal, and slope-`-1` diagonal meeting the parity class. A checkerboard point is a rank-four hyperedge containing its four incident lines.

Any two distinct line constraints occur together in at most one point-edge: parallel lines never meet, and two nonparallel lines meet in at most one point. Thus `r=4`, `b=2`, and `C=1`.

The continuum-to-finite proof can be arranged to produce diffuse point-level fractional solutions with

```text
sum_p x_p = alpha n-o(n),
max_p x_p = o(1).
```

Applying the rounding theorem gives an integral four-direction packing of size `alpha n-o(n)`. The fractional upper bound gives the reverse inequality.

## Formalization status and dependency boundary

The exact fractional LP theorem is intended to be fully formalized in Lean in this repository.

The integral result depends on Kahn's deep asymptotic hypergraph edge-colouring theorem. It must remain in a separate theorem/document unless that external theorem and the blow-up reduction are independently formalized. It must not be imported as an axiom into the fractional theorem.

## Explicit non-claim

The result above does not imply

```text
D_mono(n) >= (alpha-o(1)) n.
```

The true no-three-in-line problem has a growing collection of rational slope families. The bounded-rank four-direction hypergraph argument does not control them.
