# A387471 — proof manuscript

## Theorem

Let `a(n)` be the number of interior triple concurrencies when an equilateral
triangle has `2n-1` equally spaced cevians from each vertex. Then

\[
a(n)=6n-5+12\mathbf 1_{5\mid n}
=
\begin{cases}
6n-5,&5\nmid n,\\
6n+7,&5\mid n.
\end{cases}
\]

More precisely, the concurrent ordered triples are the permutations of

\[
(r,n,2n-r),\qquad 1\le r<n,
\]

together with `(n,n,n)`. If `n=5q`, there are also the permutations of

\[
(q,7q,8q),\qquad (2q,3q,9q).
\]

## 1. Trigonometric Ceva

Put

\[
\theta=\frac{\pi}{6n},\qquad x=i\theta,\quad y=j\theta,\quad z=k\theta.
\]

Trigonometric Ceva gives concurrence exactly when

\[
\frac{\sin x}{\sin(\pi/3-x)}
\frac{\sin y}{\sin(\pi/3-y)}
\frac{\sin z}{\sin(\pi/3-z)}=1.
\]

Since all six sine factors are positive, this is equivalent to

\[
\sin x\sin y\sin z
=
\sin(\pi/3-x)\sin(\pi/3-y)\sin(\pi/3-z).
\tag{1}
\]

The following identity is elementary and is kernel-checked in
`A387471Trig.lean`:

\[
\begin{aligned}
&\sin x\sin y\sin z
-\sin(\pi/3-x)\sin(\pi/3-y)\sin(\pi/3-z)\\
&\quad=\frac{\sqrt3}{4}\bigl(
 \sin(x+y-z-\pi/6)
+\sin(x+z-y-\pi/6)
+\sin(y+z-x-\pi/6)\bigr).
\end{aligned}
\tag{2}
\]

Define

\[
A=i+j-k-n,\qquad B=i+k-j-n,\qquad C=j+k-i-n.
\]

Then (1) is equivalent to

\[
\sin(A\theta)+\sin(B\theta)+\sin(C\theta)=0.
\tag{3}
\]

## 2. The admissible-angle bounds

Because `1 <= i,j,k <= 2n-1`,

\[
|A|,|B|,|C|<3n,
\]

and hence

\[
-\frac\pi2<A\theta,B\theta,C\theta<\frac\pi2.
\tag{4}
\]

Also

\[
A+B=2(i-n),\quad A+C=2(j-n),\quad B+C=2(k-n),
\]

so

\[
|(A+B)\theta|,\ |(A+C)\theta|,\ |(B+C)\theta|<\frac\pi3.
\tag{5}
\]

## 3. Classification lemma

### Lemma

Let `alpha,beta,gamma` be rational multiples of `pi` satisfying

\[
-\frac\pi2<\alpha,\beta,\gamma<\frac\pi2,
\]

\[
|\alpha+\beta|,|\alpha+\gamma|,|\beta+\gamma|<\frac\pi3,
\]

and

\[
\sin\alpha+\sin\beta+\sin\gamma=0.
\]

Up to permutation, one has exactly one of

\[
(\alpha,\beta,\gamma)=(0,t,-t),
\tag{6}
\]

\[
(\alpha,\beta,\gamma)=(-\pi/6,-\pi/10,3\pi/10),
\tag{7}
\]

\[
(\alpha,\beta,\gamma)=(-3\pi/10,\pi/10,\pi/6).
\tag{8}
\]

### Proof

Consider the six-term sum of roots of unity

\[
S=e^{i\alpha}+e^{i\beta}+e^{i\gamma}
-e^{-i\alpha}-e^{-i\beta}-e^{-i\gamma}=0.
\tag{9}
\]

Every vanishing sum is a disjoint union of minimal vanishing subsums.
The classification of minimal vanishing sums of weight at most six says
that the only minimal types relevant here are

\[
R_2,\quad R_3,\quad R_5,\quad (R_5:R_3),
\]

of respective weights `2,3,5,6`. Therefore a six-term vanishing sum has
one of three decompositions:

1. `R_2 + R_2 + R_2`;
2. `R_3 + R_3`;
3. one minimal sum of type `(R_5:R_3)`.

This is the weight-six row of Theorem 3.3, Table 1, in:

Louis Christie, Kenneth J. Dykema, and Igor Klep,
*Classifying minimal vanishing sums of roots of unity*, arXiv:2008.11268.
Their Remark 2.5(c) also states that a type `(R_p:R_q)` determines the sum
uniquely up to rotation.

#### Three opposite pairs

The roots `e^(i alpha),e^(i beta),e^(i gamma)` lie in the open right
half-plane, whereas `-e^(-i alpha),-e^(-i beta),-e^(-i gamma)` lie in the
open left half-plane. Hence each opposite pair contains one root from each
half. An equality

\[
e^{iu}+(-e^{-iv})=0
\]

forces `u=-v`, because `u,v` lie in `(-pi/2,pi/2)`. Thus the multiset
`{alpha,beta,gamma}` is invariant under negation. A three-element multiset
invariant under negation is `{0,t,-t}`, proving (6).

#### Two equilateral triples

A vanishing triple of roots of unity is a rotated copy of
`{1,omega,omega^2}`, where `omega=e^(2pi i/3)`. It cannot lie entirely in
one open half-plane. Thus one of the triples contains two right-half-plane
roots and one left-half-plane root, say

\[
e^{i\alpha},\ e^{i\beta},\ -e^{-i\gamma}.
\]

The ratio of the first and third terms is a nontrivial cube root of unity,
so

\[
\alpha+\gamma\equiv\pm\frac\pi3\pmod{2\pi}.
\]

The angle ranges reduce this to `alpha+gamma=+-pi/3`, contradicting the
strict pair-sum bound. Hence this case is impossible.

#### The minimal six-term relation

A representative of `(R_5:R_3)` is

\[
-\omega-\omega^2+\eta+\eta^2+\eta^3+\eta^4=0,
\]

where `omega=e^(2pi i/3)` and `eta=e^(2pi i/5)`. Its argument multiset is

\[
P=\{\pi/3,2\pi/5,4\pi/5,6\pi/5,8\pi/5,5\pi/3\}.
\]

The type `(R_5:R_3)` determines the relation uniquely up to rotation, so
`S=rho P` for some root of unity `rho`.

The multiset `S` is invariant under `T(z)=-conj(z)`. The multiset `P` is
invariant under conjugation and has no nontrivial rotational symmetry.
Consequently

\[
rho P=T(rho P)=-\overline{rho}P
\]

forces `rho=-conj(rho)`. Since `|rho|=1`, `rho=+i` or `rho=-i`.

For `rho=i`, the three terms in the open right half-plane have arguments

\[
-3\pi/10,\quad \pi/10,\quad \pi/6.
\]

For `rho=-i`, they have arguments

\[
-\pi/6,\quad -\pi/10,\quad 3\pi/10.
\]

This proves (7) and (8), and completes the classification lemma.

## 4. Recover the index triples

Apply the lemma with

\[
\alpha=A\theta,\quad\beta=B\theta,\quad\gamma=C\theta.
\]

The inverse linear relations are

\[
2i=2n+A+B,\quad 2j=2n+A+C,\quad 2k=2n+B+C.
\tag{10}
\]

For `(A,B,C)=Perm(0,s,-s)`, (10) says that one of `i,j,k` equals `n`
and the other two sum to `2n`. This gives exactly the permutations of
`(r,n,2n-r)` with `1<=r<n`, plus `(n,n,n)`.

For the first exceptional angle pattern, integrality requires

\[
\frac{\pi/10}{\theta}=\frac{3n}{5}\in\mathbb Z,
\]

hence `5|n`. Write `n=5q`. The two exceptional coefficient patterns are,
up to permutation,

\[
(-5q,-3q,9q),\qquad (-9q,3q,5q).
\]

Substitution into (10) gives, respectively,

\[
(q,7q,8q),\qquad (2q,3q,9q),
\]

up to permutation.

## 5. Count

For each `r=1,...,n-1`, the entries of `(r,n,2n-r)` are distinct, giving
six ordered permutations. The central triple contributes one. Thus the
ordinary count is

\[
6(n-1)+1=6n-5.
\]

When `5|n`, each exceptional triple has three distinct entries and contributes
six further permutations. The exceptional contribution is therefore `12`.
This proves

\[
a(n)=6n-5+12\mathbf 1_{5\mid n}.
\]

## Formal-verification status

The Lean development now kernel-checks, without `sorryAx`:

- identity (2);
- equivalence between trigonometric Ceva and (3);
- the exact integer reconstruction (10);
- ordinary and exceptional index-family reconstruction;
- the final arithmetic formula;
- transfer from a grid-level six-root classification to the index classification.

The remaining Lean work is to formalize the published weight-six
vanishing-sum classification and package the final finite-set cardinality.
The mathematical proof above uses that published theorem exactly as stated.