# Generic translated-mesh saturation theorem: explicit version

## Periodic reference mesh

Tile the plane by unit squares and split each square along the southwest-to-northeast
diagonal.  Each reference triangle is a right isosceles triangle with inradius

```text
R = 1 - 1/sqrt(2).
```

Fix an erosion radius

```text
0 < r < R.
```

The set of points whose distance from all three edges of their containing triangle is
at least `r` is the union of two homothetic inner triangles.  Its exact area fraction
inside one unit square is

```text
p_r = ((R-r)/R)^2.
```

For example, at `r=0.08`,

```text
p_r approximately 0.5283.
```

## Translation space

For mesh size `h`, translate the scaled periodic triangulation by `h tau`, where

```text
tau in Q = [0,1)^2.
```

Let `Gamma` be a compact rectifiable free-boundary arc of length `L`.  Define

```text
X_h(tau)
  = H^1({x in Gamma : dist(x, skeleton(T_h(tau))) >= r h}).
```

For each fixed `x`, the reduced coordinate `x/h-tau mod Z^2` is uniformly distributed
in `Q`.  Therefore

```text
int_Q X_h(tau) d tau = p_r L.
```

Define the good-translation set

```text
A_h = {tau : X_h(tau) >= p_r L/2}.
```

Since `0 <= X_h <= L`,

```text
|A_h| >= q_r,
q_r = p_r/(2-p_r) > 0.
```

This lower bound is independent of `h`, the position of `Gamma`, and the tangent
orientation of `Gamma`.

## Retained-element count

Assume `Gamma` is `C^2` with curvature bounded by `K`.  Fix a separation constant `D`
larger than a uniform bound for the arclength of `Gamma` inside one mesh triangle,
measured in units of `h`.  For `tau in A_h`, choose a maximal `D h`-separated set of
points in the good subset of `Gamma`.  Then

```text
m_h >= p_r L/(4 D h).
```

After reducing `D` by a harmless bounded-overlap constant, the selected points may be
associated with distinct retained triangles.

## Explicit local prisms

Set

```text
c = r/8,
ell = 2 c h.
```

At a selected point `x_T`, use the tangent and normal at `x_T`.  For sufficiently small
`h`, the flat rectangle

```text
[-c h,c h] x [-c h,c h]
```

in tangent-normal coordinates lies inside the Euclidean ball `B_(r h)(x_T)`, hence
inside the containing triangle.  Its normal fiber length is `ell`, its phase is
`theta=1/2`, and its tangential width is `ell`.

The normal-coordinate Jacobian satisfies

```text
J >= 1/2
```

whenever

```text
h <= 1/(2 K c).
```

Thus the mapped-prism constants can be chosen uniformly as

```text
eta = 1/2,
M = 1,
J0 = 1/2,
local scale = ell = 2 c h.
```

In terms of the local scale `ell`, the retained count becomes

```text
m_h >= N_r/ell,
N_r = p_r c L/(2D).
```

## Regular-profile reduction

On each retained triangle choose the fixed center normal `nu_T` and the center contact
coefficient `a_T`.  Write

```text
u-psi = a_T (t_+)^2 + R_T
```

in the flat tangent-normal coordinates.  Curvature, normal variation, amplitude
variation, and the PDE's higher-order expansion are included in `R_T`.

Assume uniformly

```text
a_T >= a0 > 0,
|grad R_T| <= C_R h^(1+kappa).
```

Then the certified prism and remainder theorems give, for every translated mesh with
`tau in A_h`,

```text
c_lower ell^(3/2) <= inf_(v_h in V_h) |u-v_h|_(H1),
```

where `c_lower>0` depends on `a0,r,L,D` and the curvature/remainder bounds, but not on
`h` or the selected good translation.

Since `ell=2ch`, this is equivalent to

```text
c h^(3/2) <= inf_(v_h in V_h) |u-v_h|_(H1).
```

Combining with the existing upper recovery theorem yields a two-sided sharp estimate.

## Consequences

### Per-level positive-measure theorem

For every sufficiently small `h`, the set of translations producing the sharp lower
bound has measure at least `q_r`.

### Deterministic translated family

Selecting any `tau_h in A_h` at each level gives a deterministic mesh family with a
sharp estimate at every sufficiently small level.

### One fixed shift, infinitely many levels

For any sequence `h_n -> 0`,

```text
|limsup_n A_(h_n)| >= q_r.
```

Indeed each tail union has measure at least `q_r`, and the tail unions decrease to the
limsup.  Therefore a positive-measure set of fixed shifts is good for infinitely many
levels, yielding a sharp subsequence theorem.

### Independently randomized shifts

If `tau_n` are independent and uniform, each level is good with probability at least
`q_r`.  Hence good levels occur infinitely often almost surely.  Resampling at each
level until a good translation is found has expected trial count at most `1/q_r`.

## Limitation

The argument does not imply that one fixed shift is good for all sufficiently small
nested mesh levels.  Such an eventual-all-level statement requires additional
arithmetic or equidistribution hypotheses and is false in aligned periodic examples.
