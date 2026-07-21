# Exact constants for the deterministic flat-interface benchmark

## Problem

Let

```text
Omega = (0,W) x (-H,H),
psi = 0,
u(x,y) = a (y_+)^2,
f = -2a,
a > 0.
```

Use Dirichlet data equal to `u`.  Then `u` solves the obstacle problem and its free
boundary in the interior is the line `y=0`.

Let the mesh be the uniform square grid of side `h`, shifted so that the interface row
is midway between `y=-h/2` and `y=h/2`, with every square split along the
southwest-to-northeast diagonal.  Assume for simplicity that `W/h` is an integer.

## Explicit lower bound

In every interface square `[jh,(j+1)h] x [-h/2,h/2]`, retain the two rectangles

```text
[jh, jh+h/4]       x [-h/4,h/4],
[jh+3h/4, jh+h]    x [-h/4,h/4].
```

The first lies in the upper-left triangle and the second lies in the lower-right
triangle.  Each is an exact product prism with

```text
normal length ell = h/2,
phase theta = 1/2,
tangential width = h/4,
Jacobian = 1.
```

For every scalar quadratic polynomial restricted to a vertical fiber, the exact
one-dimensional best derivative error is

```text
(4/3) a^2 theta^3 (1-theta)^3 ell^3
  = a^2 h^3 / 384.
```

The total tangential width of the two prisms is `h/2`, so every interface square
contributes at least

```text
a^2 h^4 / 768
```

to the squared `H1` seminorm error.  There are `W/h` interface squares.  Hence every
conforming piecewise-quadratic function `v_h` satisfies

```text
|u-v_h|_(H1(Omega))^2 >= a^2 W h^3 / 768,
|u-v_h|_(H1(Omega))   >= a sqrt(W/768) h^(3/2).
```

In particular this applies to the discrete obstacle solution.

## Explicit feasible upper comparison

Define the globally continuous piecewise-quadratic comparison field

```text
v_h(y) = 0                              for y <= -h/2,
v_h(y) = (a/4) (y+h/2)^2               for -h/2 <= y <= h/2,
v_h(y) = a y^2                          for y >= h/2.
```

It is nonnegative and is a scalar quadratic on every mesh triangle.

On the contact half of the strip,

```text
integral_(-h/2)^0 |v_h'|^2 dy = a^2 h^3 / 96.
```

On the noncontact half,

```text
integral_0^(h/2) |u'-v_h'|^2 dy = a^2 h^3 / 32.
```

Therefore

```text
|u-v_h|_(H1(Omega))^2 = a^2 W h^3 / 24.
```

The obstacle multiplier is

```text
lambda = -Delta u - f = 2a on {y<0},
lambda = 0 on {y>0}.
```

Its comparison term is

```text
<lambda,v_h-u> = a^2 W h^3 / 48.
```

The conforming Falk estimate

```text
|u-u_h|_a^2 <= |u-v_h|_a^2 + 2 <lambda,v_h-u>
```

then yields

```text
|u-u_h|_(H1(Omega))^2 <= a^2 W h^3 / 12,
|u-u_h|_(H1(Omega))   <= a sqrt(W/12) h^(3/2).
```

## Final concrete sharp theorem

For this manufactured classical obstacle problem and deterministic half-cell-shifted
triangular mesh,

```text
a sqrt(W/768) h^(3/2)
  <= |u-u_h|_(H1(Omega))
  <= a sqrt(W/12) h^(3/2).
```

No free-boundary regularity citation, asymptotic remainder, genericity assumption, or
hidden clipping model is needed.  The solution, multiplier, mesh geometry, feasible
comparison, and both constants are explicit.

## Remaining formalization tasks

1. represent the finite rectangular mesh and its two triangle types;
2. prove the two rectangle inclusions by affine inequalities;
3. instantiate the existing reference-prism theorem on both retained rectangles;
4. formalize the one-dimensional integrals in the upper comparison;
5. connect the comparison estimate to the repository's Hilbert/VI layer.
