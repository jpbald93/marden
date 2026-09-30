"""Exact check (sympy) of the explicit one-parameter family of reflection-law solutions
for the triangle a=0, b=4, c=1+3i (referee example, issue 8).

For every real t, the roots f1, f2 of z^2 - s z + p with
    s = 3 + 4t + 2i,   p = 1/2 + 10t + 4i
satisfy the three reflection equations
    (m_i - f1)(m_i - f2) = -lambda_i d_i^2      (m_i side midpoints, d_i side directions)
with lambda_1 = 3/32 - t/8, lambda_2 = 1/9 - t/3, lambda_3 = t,
all nonnegative exactly for 0 <= t <= 1/3.  Only t = 1/12 gives lambda_i = 1/12 and the
Marden foci (Vieta for the critical points); the equal-focal-sum condition is what pins it down.
"""
import sympy as sp

t = sp.symbols('t', real=True)
z = sp.symbols('z')
I = sp.I
a, b, c = sp.Integer(0), sp.Integer(4), 1 + 3*I
s = 3 + 4*t + 2*I
p = sp.Rational(1, 2) + 10*t + 4*I
lam = [sp.Rational(3, 32) - t/8, sp.Rational(1, 9) - t/3, t]
sides = [(a, b), (b, c), (c, a)]

# roots of z^2 - s z + p, exactly (symbolic in t)
f1, f2 = sp.solve(sp.Eq(z**2 - s*z + p, 0), z)
assert sp.simplify(f1 + f2 - s) == 0 and sp.simplify(f1*f2 - p) == 0

for i, ((x, y), l) in enumerate(zip(sides, lam), 1):
    m, d = (x + y)/2, y - x
    lhs = (m - f1)*(m - f2)
    rhs = -l*d**2
    assert sp.simplify(sp.expand(lhs - rhs)) == 0, i
    # same identity via Vieta only (polynomial in t, no radicals)
    assert sp.expand(m**2 - s*m + p + l*d**2) == 0, i
print("reflection equations hold identically in t: ok")

# nonnegativity window
sol = sp.reduce_inequalities([l >= 0 for l in lam], t)
print("all lambda_i >= 0 iff", sol)
assert sp.Intersection(*[sp.solve_univariate_inequality(l >= 0, t, relational=False) for l in lam]) \
    == sp.Interval(0, sp.Rational(1, 3))

# Marden member: t = 1/12
t0 = sp.Rational(1, 12)
assert all(sp.simplify(l.subs(t, t0) - sp.Rational(1, 12)) == 0 for l in lam)
assert sp.simplify(s.subs(t, t0) - sp.Rational(2, 3)*(a + b + c)) == 0
assert sp.simplify(p.subs(t, t0) - (a*b + b*c + c*a)/3) == 0
print("t = 1/12: lambda_i = 1/12 and (s, p) = Vieta of the critical points: ok")

# the family is genuinely non-constant: distinct t give distinct focal pairs
assert sp.simplify(s.subs(t, 0) - s.subs(t, sp.Rational(1, 3))) != 0

# equal focal sums fail for other members (numerical sample)
def fsum(F1, F2, w):
    return abs(complex(w - F1)) + abs(complex(w - F2))
mids = [complex((x + y)/2) for x, y in sides]
for tv in [0, sp.Rational(1, 24), t0, sp.Rational(1, 6), sp.Rational(1, 3)]:
    F1, F2 = [complex(sp.N(r.subs(t, tv), 30)) for r in (f1, f2)]
    v = [fsum(F1, F2, m) for m in mids]
    print(f"t = {str(tv):>5}: midpoint focal sums {[round(x, 12) for x in v]}")
print("check_family: all exact checks passed")
