from fractions import Fraction
from itertools import product
import json


def binom(a: Fraction, k: int) -> Fraction:
    out = Fraction(1)
    for j in range(k):
        out *= a - j
        out /= j + 1
    return out


def multiply(a, b, N):
    c = [Fraction(0) for _ in range(N + 1)]
    for i, x in enumerate(a):
        if not x:
            continue
        for j, y in enumerate(b[: N + 1 - i]):
            if y:
                c[i + j] += x * y
    return c


def product_coeffs(q: Fraction, alpha: Fraction, N: int):
    out = [Fraction(0)] * (N + 1)
    out[0] = Fraction(1)
    m = 1
    while m <= N:
        factor = [Fraction(0)] * (N + 1)
        for k in range(N // m + 1):
            factor[k * m] = binom(alpha, k) * q**k
        out = multiply(out, factor, N)
        m *= 2
    return out


def d_coeffs(q: Fraction, N: int):
    d = [Fraction(0)] * (N + 1)
    d[0] = q
    for n in range(1, N + 1):
        if n % 2 == 0:
            r = n // 2
            d[n] = q ** (2 * r + 1)
        else:
            r = (n - 1) // 2
            d[n] = 2 * d[r] - q ** (2 * r + 2)
    return d


def recurrence_coeffs(q: Fraction, alpha: Fraction, N: int):
    d = d_coeffs(q, N)
    a = [Fraction(0)] * (N + 1)
    a[0] = Fraction(1)
    for n in range(N):
        a[n + 1] = alpha * sum(d[i] * a[n - i] for i in range(n + 1)) / (n + 1)
    return a, d


N = 160
qs = [Fraction(1, 7), Fraction(1, 3), Fraction(1, 2), Fraction(3, 4), Fraction(1)]
alphas = [Fraction(1, 5), Fraction(1, 3), Fraction(1, 2), Fraction(1), Fraction(5, 3), Fraction(2)]
results = []
for q, alpha in product(qs, alphas):
    direct = product_coeffs(q, alpha, N)
    recurrence, d = recurrence_coeffs(q, alpha, N)
    assert direct == recurrence, (q, alpha)
    assert all(x > 0 for x in recurrence), (q, alpha, 'nonpositive a')
    assert all(d[n] >= q ** (n + 1) > 0 for n in range(N + 1)), (q, alpha, 'd bound')
    results.append({
        'q': str(q),
        'alpha': str(alpha),
        'degree': N,
        'direct_equals_recurrence': True,
        'all_coefficients_positive': True,
        'log_derivative_lower_bound': True,
        'last_coefficient_numerator_digits': len(str(abs(recurrence[-1].numerator))),
        'last_coefficient_denominator_digits': len(str(recurrence[-1].denominator)),
    })

out = {
    'engine': 'Python fractions.Fraction',
    'number_of_parameter_pairs': len(results),
    'maximum_degree': N,
    'results': results,
}
with open('digital_euler_general_verification.json', 'w') as f:
    json.dump(out, f, indent=2)
print(f'PASS: {len(results)} rational parameter pairs through degree {N}')
