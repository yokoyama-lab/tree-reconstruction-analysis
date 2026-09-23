# 検証スクリプト（本文で参照するプログラム）

対応論文の数値検証プログラム。原稿自体は別途配布する。
依存関係と手順は [REPRODUCING.md](../REPRODUCING.md) を参照。
いずれも外部ローカル依存のない自己完結ファイル。

| ファイル | 本文での参照 | 役割 |
|---|---|---|
| `average.hs` | 付録 `app:scripts` / 数値検証(1) | 全 $C_n$ 個の符号語を遅延列挙し，$S,P_2$ と平均比較回数を厳密有理で計算（$1\le n\le14$）。 |
| `verify_derivations.py` | 付録 `app:scripts`（`scripts/verify_derivations.py`） | (i) 中心二項係数恒等式を SymPy の級数展開で照合，(ii) 全符号語を列挙して総和・期待値・分散・共分散・平均比較回数を閉形式と厳密照合（$2\le n\le14$）。`all checks passed` を印字。 |
| `enum_moments.py` | 数値検証(1) | 符号語を深さ優先で列挙し，整数で和を集計する独立の列挙器。$\mathbb E[S]$, $\mathbb E[P_2]$, $\mathrm{Var}[S]$, $\mathrm{Var}[P_2]$, $\mathrm{Cov}[S,P_2]$ と $C_n$ を閉形式と厳密照合（$1\le n\le14$，実行時間は環境依存）。標準ライブラリのみ。 |
| `transfer_dp.py` | 数値検証(2)（`scripts/transfer_dp.py`） | 転送行列型の動的計画法。符号語の格子路を高さで畳み込み，(i) $n\le500$ のモーメント（$\mathbb E,\mathrm{Var},\mathrm{Cov}$）を厳密有理数で求めて閉形式と照合，(ii) $n=2400$ の比較回数の有限サイズ分布（図 3、浮動小数点演算）を計算する。 |
| `theme6/count_mnc.c` | 数値検証(3)（`scripts/theme6/count_mnc.c`） | 2アルゴリズム（および Algorithm C）を C で実装し，Rémy 生成の一様ランダム木で比較回数を直接計数。$M\to3n$, $N\to\tfrac94 n$ を実測で再現。 |
| `theme6/remy_means.py` | 数値検証(3) の脚注 | `count_mnc` を種 1..k で繰り返し，$n=10^3$〜$10^7$ の $A_M/n$・$A_N/n$ の標本平均と標準誤差を厳密平均と比べる。 |

## 実行

```bash
# (1) 参照列挙器（要 GHC）
runghc average.hs                     # n = 1..14（約 30 秒）

# 付録: 計算機代数検証（要 Python3 + SymPy: pip install sympy）
python3 verify_derivations.py        # => all checks passed
python3 enum_moments.py              # => all match（n = 1..14）

# (2) 転送行列 DP（要 Python3。分布計算のみ NumPy）
python3 transfer_dp.py --moments 500   # => moments: closed forms confirmed for n = 1..500
python3 transfer_dp.py --dist 2400     # => E[A_M]=7196.0025, E[A_N]=5398.3776（約 90 秒）

# (3) 直接実行カウンタ（要 C コンパイラ）
gcc -O2 -o count_mnc theme6/count_mnc.c
./count_mnc 1000 rand                 # 引数順は  n  mode(rand|best|mworst|nworst)
python3 theme6/remy_means.py          # 脚注の標本平均（数分）
```
