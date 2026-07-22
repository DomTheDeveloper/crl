# Exact odd-mesh Green interpolant energy

## Statement

Let

\[
\phi(x)=\frac{\sinh(1-|x|)}{\sinh 1},\qquad -1\le x\le1,
\]

and let the uniform mesh have an odd number

\[
N=2m+1
\]

of cells, with

\[
h=\frac{2}{2m+1}.
\]

The contact point `0` lies at the midpoint of the central cell
`[-h/2,h/2]`. Let `I_h phi` be the continuous piecewise-linear nodal
interpolant. Then

\[
\|I_h\phi\|_{H^1(-1,1)}^2\longrightarrow
\frac{2}{\tanh 1},
\]

and hence

\[
\|I_h\phi\|_{H^1(-1,1)}\longrightarrow
\sqrt{\frac{2}{\tanh 1}}.
\]

This supplies the missing concrete profile-norm input in the Green recovery
sequence.

## Exact discrete energy

Write `S = sinh 1`. On the positive half of the mesh, reindex the nodal
values from the boundary toward the contact cell:

\[
y_r=\frac{\sinh(rh)}{S},\qquad r=0,\ldots,m.
\]

Thus `y_0=0`, while the two central-cell endpoint values are both `y_m`.
The interpolant is constant on the central cell. On every other cell, the
exact `H^1` energy of the affine segment joining `y_{r-1}` and `y_r` is

\[
\frac{(y_r-y_{r-1})^2}{h}
+\frac h3\left(y_r^2+y_ry_{r-1}+y_{r-1}^2\right).
\]

By symmetry,

\[
E_m:=\|I_h\phi\|_{H^1(-1,1)}^2
=h y_m^2+2\sum_{r=1}^m
\left[
\frac{(y_r-y_{r-1})^2}{h}
+\frac h3\left(y_r^2+y_ry_{r-1}+y_{r-1}^2\right)
\right].
\]

## Hyperbolic finite sums

Set `s_r=sinh(rh)`. The following identities are elementary consequences of
product-to-sum and the finite geometric series:

\[
\sum_{r=1}^m(s_r-s_{r-1})^2
=2m\sinh^2\frac h2
+\frac{\sinh^2(h/2)\sinh(2mh)}{\sinh h},
\]

\[
Q_m:=\sum_{r=1}^m s_r^2
=\frac12\left(
\frac{\sinh(mh)\cosh((m+1)h)}{\sinh h}-m
\right),
\]

and

\[
P_m:=\sum_{r=1}^m s_rs_{r-1}
=\frac{\sinh(2mh)}{4\sinh h}-\frac m2\cosh h.
\]

The quadratic-value contribution is

\[
\sum_{r=1}^m(s_r^2+s_rs_{r-1}+s_{r-1}^2)
=Q_m+Q_{m-1}+P_m.
\]

These formulas give a closed expression for `E_m`.

## Closed expression in the mesh width

Since

\[
m h=1-\frac h2,
\]

the discrete energy can be written as

\[
E_m=C(h)+D(h)+L(h),
\]

where

\[
C(h)=h\left(\frac{\sinh(1-h/2)}{\sinh1}\right)^2,
\]

\[
D(h)=\frac1{\sinh^2 1}
\left[
\left(1-\frac h2\right)
\left(\frac{\sinh(h/2)}{h/2}\right)^2
+
\frac{\sinh(h/2)}{h/2}
\frac{\sinh(h/2)}{\sinh h}
\sinh(2-h)
\right],
\]

and

\[
\begin{aligned}
L(h)=\frac{2}{3\sinh^2 1}\Bigg[&
\frac{h}{\sinh h}
\frac{\sinh2+\sinh(2-h)+\sinh(2-2h)-2\sinh h}{4}\\
&-(1-h)-\left(\frac12-\frac h4\right)\cosh h
\Bigg].
\end{aligned}
\]

The three terms are respectively the central-cell value energy, the derivative
energy, and the noncentral value energy.

## Limit

As `h -> 0+`,

\[
\frac{\sinh h}{h}\to1,
\qquad
\frac{\sinh(h/2)}{h/2}\to1,
\qquad
\frac{\sinh(h/2)}{\sinh h}\to\frac12.
\]

Therefore

\[
C(h)\to0,
\]

\[
D(h)\to
\frac{1+\frac12\sinh2}{\sinh^21},
\]

and

\[
L(h)\to
\frac{\frac12\sinh2-1}{\sinh^21}.
\]

Adding gives

\[
E_m\to\frac{\sinh2}{\sinh^21}.
\]

Using

\[
\sinh2=2\sinh1\cosh1,
\]

we obtain

\[
\frac{\sinh2}{\sinh^21}
=2\frac{\cosh1}{\sinh1}
=\frac2{\tanh1}.
\]

Continuity of the square root then yields

\[
\|I_h\phi\|_{H^1(-1,1)}
\to\sqrt{\frac2{\tanh1}}.
\]

## Interpretation

The derivative of `phi` jumps at the contact point. On an odd mesh the central
interpolant segment is flat, so the strong `H^1` interpolation error is only
expected to be `O(sqrt h)`. Nevertheless, the squared norm loses only `O(h)`
energy on the shrinking central cell, and the interpolant norm converges to the
exact Green norm. This is precisely what the sharp recovery-sequence argument
requires.
