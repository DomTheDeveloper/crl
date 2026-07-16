# OEIS A063880 — classification of two-prime powerful cores

## Statement

Let

\[
R(p,e)=\frac{1+p+\cdots+p^e}{1+p^e}.
\]

Suppose a powerful integer with exactly two distinct prime divisors,

\[
m=p^a q^b,\qquad p<q,\qquad a,b\ge 2,
\]

satisfies

\[
\sigma(m)=2\sigma^*(m),
\]

where \(\sigma^*\) is the sum of unitary divisors. Then

\[
\boxed{m=2^2 3^3=108}.
\]

Consequently, if an A063880 term has powerful core supported on exactly two
primes, then it is \(108s\), where \(s\) is squarefree and coprime to \(108\),
and hence is congruent to \(108\pmod{216}\).

## Proof

Multiplicativity gives

\[
R(p,a)R(q,b)=2.
\]

### 1. One of the primes is 2

For every prime \(r\) and exponent \(e\ge 1\),

\[
R(r,e)<\frac r{r-1},
\]

because

\[
(r-1)(1+r+\cdots+r^e)=r^{e+1}-1
 <r^{e+1}+r=r(1+r^e).
\]

If both primes were odd, then \(p\ge3\), \(q\ge5\), and therefore

\[
R(p,a)R(q,b)<\frac32\cdot\frac54=\frac{15}{8}<2,
\]

a contradiction. Thus \(p=2\).

### 2. The odd prime is 3

The defining equation is

\[
\sigma(2^a)\sigma(q^b)
 =2(1+2^a)(1+q^b).
\]

Reduce modulo \(q\). Since

\[
\sigma(q^b)\equiv1\pmod q,
\qquad 1+q^b\equiv1\pmod q,
\]

we obtain

\[
2^{a+1}-1\equiv2(1+2^a)=2^{a+1}+2\pmod q.
\]

Hence \(q\mid3\). As \(q\) is an odd prime, \(q=3\).

### 3. The exponents are 2 and 3

Substituting \(q=3\) and the prime-power formulas gives

\[
(2^{a+1}-1)\frac{3^{b+1}-1}{2}
 =2(2^a+1)(3^b+1).
\]

After multiplying by 2 and expanding,

\[
3^b(2^{a+1}-7)=3(2^{a+1}+1).
\]

Therefore

\[
3^{b-1}(2^{a+1}-7)=2^{a+1}+1,
\]

and subtracting \(2^{a+1}-7\) from both sides yields

\[
\bigl(3^{b-1}-1\bigr)\bigl(2^{a+1}-7\bigr)=8.
\]

Both factors are positive because \(a,b\ge2\). Thus
\(3^{b-1}-1\le8\), so \(b\le3\).

- If \(b=2\), then \(2(2^{a+1}-7)=8\), giving
  \(2^{a+1}=11\), impossible.
- If \(b=3\), then \(8(2^{a+1}-7)=8\), giving
  \(2^{a+1}=8\), so \(a=2\).

Hence \(m=2^2 3^3=108\). ∎

## Formalization target

A Lean proof should be split into:

1. the prime-power formulas for `σ` and `usigma`;
2. cancellation of coprime squarefree factors;
3. the ratio bound excluding two odd primes;
4. the modulo-`q` argument forcing `q = 3`;
5. the final natural-number factorization of 8.

This is a partial result toward `OeisA63880.mod_216_of_a`; it does not rule out
powerful primitive cores supported on three or more primes.
