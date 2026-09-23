"""Verify the symbolic and combinatorial derivations of the average-case paper.

Two independent checks:
  (1) the central-binomial generating-function identity (Lemma "Central-binomial GF")
        [z^n] (z C^2)^k / sqrt(1-4z) = binom(2n, n-k),     C = (1-sqrt(1-4z))/(2z);
  (2) exact enumeration of all Lukasiewicz codewords of length n-1, giving the
        totals, expectations, variances and covariance of S (total pops) and
        P_2 (double pops), checked against the closed forms in the paper.
Run: python3 verify_derivations.py
"""
from fractions import Fraction as F
from math import comb as _comb
import sympy as sp

def comb(a, b):                  # binomial, with C(a,b)=0 when b<0 or b>a
    return _comb(a, b) if 0 <= b <= a else 0

# (1) Generating-function identity, Lemma L --------------------------------
z = sp.symbols('z')
C = (1 - sp.sqrt(1 - 4*z)) / (2*z)
ORD = 10
for k in range(0, 4):
    ser = sp.series((z*C**2)**k / sp.sqrt(1 - 4*z), z, 0, ORD).removeO()
    for n in range(k, ORD):
        assert sp.nsimplify(ser.coeff(z, n)) == sp.binomial(2*n, n-k), (k, n)
print("(1) Lemma L identity  [z^n](zC^2)^k/sqrt(1-4z)=C(2n,n-k):  OK  (k<=3, n<10)")

# (2) Exact enumeration of codewords --------------------------------------
def codewords(n):
    out = []
    def rec(i, s, cur):
        if i == n:
            out.append(tuple(cur)); return
        for x in range(0, i - s + 1):       # x_i in [0, i - s_{i-1}], s_i<=i
            cur.append(x); rec(i+1, s+x, cur); cur.pop()
    rec(1, 0, [])
    return out

def mean(xs):            return sum(xs, F(0)) / len(xs)
def var(xs):
    m = mean(xs);        return sum((x-m)**2 for x in xs) / len(xs)
def cov(xs, ys):
    mx, my = mean(xs), mean(ys)
    return sum((x-mx)*(y-my) for x, y in zip(xs, ys)) / len(xs)

for n in range(2, 15):
    cws = codewords(n)
    assert len(cws) == comb(2*n, n)//(n+1)                    # Catalan count
    S  = [sum(c) for c in cws]
    P2 = [sum(1 for x in c if x >= 2) for c in cws]
    AN = [s + p + (n+2) for s, p in zip(S, P2)]
    AM = [s + 2*n - 1   for s in S]
    assert sum(S)  == comb(2*n, n-2)                          # total pops
    assert sum(P2) == comb(2*n-2, n-3)                        # total double pops
    assert mean(S)  == F(n*(n-1), n+2)
    assert mean(P2) == F((n-1)*(n-2), 2*(2*n-1))
    assert var(S)   == F(2*n*(2*n+1)*(n-1), (n+2)**2*(n+3))
    assert var(P2)  == F(n*(n+1)*(n-1)*(n-2), 2*(2*n-1)**2*(2*n-3))
    assert cov(S, P2) == F(2*(n-1)*(n-2), (n+2)*(2*n-1))
    assert mean(AN) == F(n*(n-1), n+2) + (n+2) + F((n-1)*(n-2), 2*(2*n-1))
    assert mean(AM) == F(n*(n-1), n+2) + 2*n - 1
print("(2) totals, E, Var, Cov of S and P_2, and E[A_N],E[A_M]:  OK  (n=2..14)")
print("all checks passed")
