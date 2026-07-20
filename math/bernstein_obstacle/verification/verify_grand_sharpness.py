#!/usr/bin/env python3
"""Exact symbolic verification of the phase-locked quadratic clipping law."""

import sympy as sp

h, theta, x = sp.symbols("h theta x", positive=True)
t = x / h

# In the phase-locked regime theta >= 1/2, the first two interpolation values
# at x=0 and x=h/2 vanish, while the right endpoint value is positive.
v0 = sp.Integer(0)
vhalf = sp.Integer(0)
v1 = (1 - theta) ** 2 * h ** 2

# Degree-two Bernstein coefficients recovered from values at t=0, 1/2, 1.
b0 = v0
b2 = v1
b1 = sp.simplify(2 * vhalf - sp.Rational(1, 2) * (b0 + b2))

# Clipping changes only b1.  B_1^2(t)=2t(1-t).
correction = sp.simplify((-b1) * 2 * t * (1 - t))
derivative = sp.diff(correction, x)
energy = sp.simplify(sp.integrate(derivative ** 2, (x, 0, h)))
expected = sp.Rational(1, 3) * (1 - theta) ** 4 * h ** 3

assert sp.simplify(
    b1 + sp.Rational(1, 2) * (1 - theta) ** 2 * h ** 2
) == 0
assert sp.simplify(
    correction - (1 - theta) ** 2 * x * (h - x)
) == 0
assert sp.simplify(energy - expected) == 0

print("b0 =", b0)
print("b1 =", b1)
print("b2 =", b2)
print("correction =", correction)
print("derivative =", derivative)
print("energy =", energy)
print(
    "H1 seminorm =",
    (1 - theta) ** 2 / sp.sqrt(3) * h ** sp.Rational(3, 2),
)
print("VERIFIED")
