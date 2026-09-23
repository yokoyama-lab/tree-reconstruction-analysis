"""独立の全数列挙器（Overleaf 側の実験レポート notes/experiment-report.tex 第 3.1 節）.

長さ n-1 の符号語 (x_1, ..., x_{n-1})，x_i in [0, i - s_{i-1}]，を深さ優先で列挙し，
S = sum x_i と P2 = #{i : x_i >= 2} の和・二乗和・積和を整数で集計する．
得た E[S], E[P2], Var[S], Var[P2], Cov[S,P2] と符号語数 C_n を，原稿の閉形式と
厳密な有理数で照合する（n = 1..14）．依存は標準ライブラリだけ．

実行: python3 enum_moments.py
"""
from fractions import Fraction as F
from math import comb


def moments(n):
    cnt = s1 = p1 = ss = pp = sp = 0

    def go(i, s, p):
        nonlocal cnt, s1, p1, ss, pp, sp
        if i == n:
            cnt += 1
            s1 += s
            p1 += p
            ss += s * s
            pp += p * p
            sp += s * p
            return
        for x in range(i - s + 1):
            go(i + 1, s + x, p + (x >= 2))

    go(1, 0, 0)
    c = F(cnt)
    es, ep = s1 / c, p1 / c
    return cnt, es, ep, ss / c - es**2, pp / c - ep**2, sp / c - es * ep


def closed_forms(n):
    N = F(n)
    return (
        comb(2 * n, n) // (n + 1),
        N * (N - 1) / (N + 2),
        (N - 1) * (N - 2) / (2 * (2 * N - 1)),
        2 * N * (2 * N + 1) * (N - 1) / ((N + 2) ** 2 * (N + 3)),
        N * (N + 1) * (N - 1) * (N - 2) / (2 * (2 * N - 1) ** 2 * (2 * N - 3)),
        2 * (N - 1) * (N - 2) / ((N + 2) * (2 * N - 1)),
    )


def main():
    ok = True
    for n in range(1, 15):
        got = moments(n)
        good = all(F(a) == F(b) for a, b in zip(got, closed_forms(n)))
        ok &= good
        _, _, _, vs, vp, cov = got
        print(n, got[0], "OK" if good else "MISMATCH",
              f"Var[S]={vs} Var[P2]={vp} Cov={cov}")
    print("all match" if ok else "MISMATCH")


if __name__ == "__main__":
    main()
