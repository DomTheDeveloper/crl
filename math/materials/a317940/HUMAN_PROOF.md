# Strict positivity of the Dirichlet square root behind OEIS A317940

## Abstract

Let \(g\) be the multiplicative arithmetic function determined on prime powers by
\[
g(p^e)=2^{A005187(e)},\qquad
A005187(e)=\sum_{k\ge 0}\left\lfloor\frac{e}{2^k}\right\rfloor.
\]
Let \(f\) be the unique arithmetic function with \(f(1)=1\) and Dirichlet square
\(f*f=g\). OEIS A317940 records the numerators of the rational values \(f(n)\) and asks whether they are nonnegative. We prove the stronger statement
\[
f(n)>0\qquad(n\ge 1).
\]
The proof reduces the problem to positivity of the coefficients of the formal square root of a binary Euler product. A Lean 4 formalization proves the exact theorem `A317940_f_nonnegative` in the Google DeepMind Formal Conjectures specification.

## 1. The arithmetic function and its local factors

For arithmetic functions, Dirichlet convolution is
\[
(u*v)(n)=\sum_{d\mid n}u(d)v(n/d).
\]
Since \(g\) is multiplicative and \(g(1)=1\), its unique Dirichlet square root with value \(1\) at \(1\) is multiplicative. Therefore it is enough to understand
\[
c_e:=f(p^e),
\]
which is independent of the prime \(p\). The local convolution relation is
\[
\sum_{j=0}^{e}c_jc_{e-j}=2^{A005187(e)}. \tag{1}
\]

Define the binary digit sum \(s_2(e)\). The classical identity
\[
A005187(e)=2e-s_2(e) \tag{2}
\]
follows either from Legendre's formula or from the recurrence
\[
A005187(e)=e+A005187(\lfloor e/2\rfloor).
\]
Hence
\[
2^{A005187(e)}=4^e2^{-s_2(e)}.
\]
Put
\[
b_e:=2^{-s_2(e)}.
\]
Then
\[
b_{2r}=b_r,\qquad b_{2r+1}=\frac{b_r}{2}. \tag{3}
\]

## 2. The binary Euler product

Let
\[
B(z)=\sum_{e\ge0}b_ez^e.
\]
Unique binary expansion gives the coefficientwise identity
\[
B(z)=\prod_{r\ge0}\left(1+\frac{z^{2^r}}2\right). \tag{4}
\]
Indeed, choosing the term \(z^{2^r}/2\) from a factor records the presence of the \(r\)-th binary digit and contributes one factor \(1/2\).

Let \(A(z)\) be the formal square root with constant coefficient \(1\):
\[
A(z)^2=B(z),\qquad A(z)=\sum_{e\ge0}a_ez^e. \tag{5}
\]
We will prove \(a_e>0\) for every \(e\).

## 3. Positive logarithmic coefficients

In the formal power-series ring,
\[
\log A(z)=\frac12\log B(z)
 =\frac12\sum_{r\ge0}\log\left(1+\frac{z^{2^r}}2\right).
\]
For \(n=2^vm\), where \(m\) is odd, the coefficient \(\ell_n=[z^n]\log A(z)\) is
\[
\ell_n=
\frac1{2m}\left(2^{-m}-\sum_{j=1}^{v}2^{-j-2^jm}\right). \tag{6}
\]
To see this, the contribution with odd exponent occurs once, at \(m\), and all other representations of \(n\) as \(k2^r\) have even \(k\) and therefore negative sign in the logarithmic expansion.

Now
\[
\sum_{j=1}^{v}2^{-j-2^jm}
<2^{-2m}\sum_{j=1}^{\infty}2^{-j}
=2^{-2m}<2^{-m}.
\]
Consequently
\[
\ell_n>0\qquad(n\ge1). \tag{7}
\]
Since
\[
A(z)=\exp\left(\sum_{n\ge1}\ell_nz^n\right),
\]
every nonconstant coefficient of \(A\) is strictly positive: the coefficient of \(z^n\) receives the positive contribution \(\ell_n\) from the linear term of the exponential, while every other contribution is nonnegative. Thus
\[
a_e>0\qquad(e\ge0). \tag{8}
\]

An equivalent recurrence, used in the formal proof, comes from the logarithmic derivative. If
\[
D(z)=\frac{B'(z)}{B(z)}=\sum_{n\ge0}d_nz^n,
\]
then all \(d_n>0\) and
\[
A'(z)=\frac12D(z)A(z).
\]
Therefore
\[
(n+1)a_{n+1}=\frac12\sum_{i=0}^{n}d_i a_{n-i}, \tag{9}
\]
which proves positivity inductively.

## 4. Rescaling and the prime-power convolution

Define
\[
c_e:=4^ea_e.
\]
Then \(c_e>0\). Rescaling (5) by \(z\mapsto4z\), and using \(4^eb_e=2^{A005187(e)}\), gives
\[
\sum_{j=0}^{e}c_jc_{e-j}=2^{A005187(e)}.
\]
This is exactly the required prime-power relation (1).

Define a multiplicative function \(h\) by
\[
h(p^e)=c_e.
\]
The preceding identity implies prime-powerwise that
\[
(h*h)(p^e)=g(p^e).
\]
Both sides are multiplicative, hence
\[
h*h=g. \tag{10}
\]

## 5. Identification with the OEIS recursion

For \(n>1\), separating the endpoint divisors \(1\) and \(n\) in (10) gives
\[
g(n)=2h(n)+
\sum_{\substack{d\mid n\\1<d<n}}h(d)h(n/d).
\]
Therefore
\[
h(n)=\frac12\left(g(n)-
\sum_{\substack{d\mid n\\1<d<n}}h(d)h(n/d)\right). \tag{11}
\]
This is precisely the well-founded recursion defining the rational function behind A317940. Strong induction gives
\[
f(n)=h(n)\qquad(n\ge0).
\]
Since \(h(n)\) is a finite product of positive values \(c_e\),
\[
\boxed{f(n)>0\quad(n\ge1).}
\]
In particular, all signed numerators in OEIS A317940 are positive, proving and strengthening the stated nonnegativity conjecture.

## 6. A general coefficient-positivity theorem

The same argument gives a broader result. Let \(0<q\le1\) and \(\alpha>0\), and define coefficientwise
\[
F_{q,\alpha}(z)=\prod_{r\ge0}(1+qz^{2^r})^{\alpha}.
\]
For \(n=2^vm\), \(m\) odd,
\[
[z^n]\log F_{q,\alpha}(z)
=\frac{\alpha}{m}
\left(q^m-\sum_{j=1}^{v}\frac{q^{2^jm}}{2^j}\right)>0.
\]
Thus every coefficient of \(F_{q,\alpha}\) is strictly positive. A317940 is the case \(q=1/2\), \(\alpha=1/2\), followed by the rescaling \(z\mapsto4z\) and multiplicative lifting.

## 7. Formal verification

The Lean proof:

1. uses the exact DeepMind definitions of `A005187`, `A046644`, and `A317940_f`;
2. proves the local positivity and power-series identities coefficientwise;
3. proves the global Dirichlet-convolution square identity;
4. identifies the constructed multiplicative root with the exact well-founded recursion;
5. proves the exact global theorem
   `A317940_f_nonnegative (n : ℕ) (h : n > 0)`;
6. contains no `sorry`, `admit`, or custom axiom.

The formal proof also establishes the stronger internal fact that the values are strictly positive for every positive argument.
