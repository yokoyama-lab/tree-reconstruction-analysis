"""Transfer-matrix dynamic programming over pop-count codewords.

This is verification method (2) of the paper: exact rational moments of the
tree functionals (and hence of the comparison counts) for every n up to a few
hundred, and the finite-size distribution of the comparison counts at large n
(n = 2400 in Figure 3).

Model.  A binary tree on n nodes is encoded by its preorder pop-count codeword
(x_1, ..., x_{n-1}).  Reading it left to right, the reconstruction stack starts
at height q = 1 (the root) and step i replaces q by q + 1 - x_i with
x_i in [0, q].  The final height is h = n - S, where S = sum_i x_i is the total
number of pops, and P_2 = #{i : x_i >= 2} is the number of double pops.  The
comparison counts of the two algorithms are

    A_M = S + 2n - 1,        A_N = S + P_2 + (n + 2).

Transfer step.  From height q a step reaches every q' in [1, q+1], and the step
is a double pop exactly when q' <= q - 1.  Summing over q therefore only needs
suffix sums, which makes one step O(state space) instead of O(state space^2).

Usage:
    python3 transfer_dp.py --moments 500     # exact rationals, checked
    python3 transfer_dp.py --dist 2400       # finite-size distribution (float)
    python3 transfer_dp.py --dist 2400 --dump fig3.txt   # pgfplots coordinates
"""

from __future__ import annotations

import argparse
from fractions import Fraction as F
from math import comb as _comb


def binom(a: int, b: int) -> int:
    """Binomial coefficient with the paper's convention C(a,b)=0 for b<0 or b>a."""
    return _comb(a, b) if 0 <= b <= a else 0


# ---------------------------------------------------------------- moments ---
def moments(n: int):
    """Exact integer totals over all C_n binary trees on n nodes.

    Returns (C_n, sum S, sum P_2, sum S^2, sum P_2^2, sum S*P_2) as ints.
    The state carries, per stack height q, the number of prefixes, the sum of
    P_2 and the sum of P_2^2 over them; S is recovered from the final height.
    """
    # c[q], p[q], pp[q] for q = 0..n+1 (q = 0 unused)
    size = n + 2
    c = [0] * size
    p = [0] * size
    pp = [0] * size
    c[1] = 1
    for _ in range(n - 1):
        # suffix sums: suf[k] = sum_{q >= k} .
        sc = [0] * (size + 1)
        sp = [0] * (size + 1)
        spp = [0] * (size + 1)
        for q in range(size - 1, 0, -1):
            sc[q] = sc[q + 1] + c[q]
            sp[q] = sp[q + 1] + p[q]
            spp[q] = spp[q + 1] + pp[q]
        nc = [0] * size
        np_ = [0] * size
        npp = [0] * size
        for q2 in range(1, size):
            lo = q2 - 1 if q2 - 1 >= 1 else 1
            hi = q2 + 1
            # x <= 1 (no double pop): q >= q2 - 1
            nc[q2] = sc[lo]
            np_[q2] = sp[lo]
            npp[q2] = spp[lo]
            # x >= 2 (double pop): q >= q2 + 1, and P_2 increases by one
            if hi < size:
                nc[q2] += 0  # already counted in sc[lo]
                np_[q2] += sc[hi]
                npp[q2] += 2 * sp[hi] + sc[hi]
        c, p, pp = nc, np_, npp

    Cn = sum(c)
    sumS = sum((n - q) * c[q] for q in range(1, size))
    sumS2 = sum((n - q) ** 2 * c[q] for q in range(1, size))
    sumP2 = sum(p)
    sumP22 = sum(pp)
    sumSP2 = sum((n - q) * p[q] for q in range(1, size))
    return Cn, sumS, sumP2, sumS2, sumP22, sumSP2


def check_moments(nmax: int) -> None:
    """Compare the DP against the closed forms of the paper for n <= nmax."""
    bad = 0
    for n in range(1, nmax + 1):
        Cn, sS, sP, sS2, sP2sq, sSP = moments(n)
        assert Cn == binom(2 * n, n) // (n + 1), f"Catalan mismatch at n={n}"
        assert sS == binom(2 * n, n - 2), f"sum S at n={n}"
        assert sP == binom(2 * n - 2, n - 3), f"sum P_2 at n={n}"
        ES, EP = F(sS, Cn), F(sP, Cn)
        VarS = F(sS2, Cn) - ES * ES
        VarP = F(sP2sq, Cn) - EP * EP
        Cov = F(sSP, Cn) - ES * EP
        want = (
            F(n * (n - 1), n + 2),
            F((n - 1) * (n - 2), 2 * (2 * n - 1)),
            F(2 * n * (2 * n + 1) * (n - 1), (n + 2) ** 2 * (n + 3)),
            F(n * (n + 1) * (n - 1) * (n - 2), 2 * (2 * n - 1) ** 2 * (2 * n - 3))
            if n >= 2
            else F(0),
            F(2 * (n - 1) * (n - 2), (n + 2) * (2 * n - 1)),
        )
        got = (ES, EP, VarS, VarP, Cov)
        if got != want:
            print(f"MISMATCH n={n}: {got} != {want}")
            bad += 1
        # comparison counts
        EAM = ES + 2 * n - 1
        EAN = ES + EP + (n + 2)
        assert EAM == F(n * (n - 1), n + 2) + 2 * n - 1
        assert EAN == F(n * (n - 1), n + 2) + (n + 2) + F((n - 1) * (n - 2), 2 * (2 * n - 1))
        VarAN = VarS + VarP + 2 * Cov
        if n == nmax:
            print(f"n={n}:  E[A_M]={float(EAM):.6f}  E[A_N]={float(EAN):.6f}")
            print(f"        Var[A_M]={float(VarS):.6f}  Var[A_N]={float(VarAN):.6f}")
            print(f"        Var[A_N] - n/16 = {float(VarAN - F(n,16)):.6f}  (-> 193/32 = {193/32})")
    print(f"moments: closed forms confirmed for n = 1..{nmax}" if not bad else f"{bad} mismatches")


# ----------------------------------------------------------- distribution ---
def distribution(n: int, qcap: int | None = None):
    """Finite-size distribution (floating-point probabilities) at size n.

    Returns (dist_AM, dist_AN) as dicts value -> probability.  `qcap` bounds the
    stack height; the default n + 1 retains the full reachable state space.
    """
    import numpy as np

    if qcap is None:
        qcap = n + 1  # no truncation: the height after i steps is at most i+1
    pmax = (n + 1) // 2  # P_2 <= ceil(n/2) - 1
    # state[q, t] = mass of prefixes with current height q and P_2 = t
    state = np.zeros((qcap + 2, pmax + 2))
    state[1, 0] = 1.0
    lost = 0.0
    for _ in range(n - 1):
        # suffix sums over the height axis: suf[k] = sum_{q >= k} state[q]
        suf = np.cumsum(state[::-1], axis=0)[::-1]
        new = np.zeros_like(state)
        # x = 0 or 1  (no double pop): the source height is q'-1 or q'
        new[1:-1] += state[:-2]  # q = q'-1
        new[1:-1] += state[1:-1]  # q = q'
        # x >= 2  (double pop): every source height q >= q'+1, and P_2 += 1
        new[1:-1, 1:] += suf[2:, :-1]
        lost += float(state[qcap + 1].sum())  # mass that would exceed the cap
        tot = new.sum()
        state = new / tot
    mass = state.sum()
    dist_AM: dict[int, float] = {}
    dist_AN: dict[int, float] = {}
    for q in range(1, qcap + 2):
        row = state[q]
        if not row.any():
            continue
        S = n - q
        am = S + 2 * n - 1
        dist_AM[am] = dist_AM.get(am, 0.0) + row.sum()
        for t in np.nonzero(row)[0]:
            an = S + int(t) + (n + 2)
            dist_AN[an] = dist_AN.get(an, 0.0) + float(row[t])
    return dist_AM, dist_AN, mass, lost


def report_distribution(n: int, dump: str | None) -> None:
    dist_AM, dist_AN, mass, _ = distribution(n)
    mean = lambda d: sum(v * p for v, p in d.items()) / sum(d.values())  # noqa: E731
    print(f"n={n}: total mass {mass:.12f}")
    print(f"  E[A_M] = {mean(dist_AM):.4f}   (closed form {float(F(n*(n-1), n+2)) + 2*n - 1:.4f})")
    print(
        f"  E[A_N] = {mean(dist_AN):.4f}   (closed form "
        f"{float(F(n*(n-1), n+2) + F((n-1)*(n-2), 2*(2*n-1))) + n + 2:.4f})"
    )
    # the windows plotted in Figure 3
    for name, d, lo, hi in (
        ("A_N", dist_AN, 5348, 5448),
        ("A_M", dist_AM, 7180, 7198),
    ):
        if n == 2400:
            out = sum(p for v, p in d.items() if not (lo <= v <= hi))
            print(f"  {name}: mass outside [{lo},{hi}] = {out:.3e}")
    if dump:
        with open(dump, "w", encoding="utf-8") as fh:
            for name, d in (("A_N", dist_AN), ("A_M", dist_AM)):
                fh.write(f"% {name}\n")
                for v in sorted(d):
                    if d[v] > 1e-5:
                        fh.write(f"({v},{d[v]:.7e}) ")
                fh.write("\n")
        print(f"  coordinates written to {dump}")


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--moments", type=int, metavar="N", help="check closed forms for n <= N")
    ap.add_argument("--dist", type=int, metavar="N", help="exact distribution at size N")
    ap.add_argument("--dump", metavar="FILE", help="write pgfplots coordinates")
    args = ap.parse_args()
    if not args.moments and not args.dist:
        args.moments = 500
    if args.moments:
        check_moments(args.moments)
    if args.dist:
        report_distribution(args.dist, args.dump)
