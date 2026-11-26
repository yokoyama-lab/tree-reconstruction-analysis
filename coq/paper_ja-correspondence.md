# 和文原稿と機械証明の対応

和文原稿の最終稿（情報処理学会論文誌プログラミング，2026-11-26）に対応する表。番号は改稿で変わるため、ラベルも併記する。
最終稿では補題 3（最終スタックの高さと最右パス長の同分布）と補題 4（比較回数のループ不変条件）が加わり、
2026-09-23 の原稿の補題 3 以降は番号が 2 つ大きい。
比較回数は `Cmp_M`・`Cmp_N` と表すが、定理名の `EAM_*`・`AN_*` は旧記法を保持する。
Lean の検査対象の定理は `lean/check-axioms.sh` の一覧、Rocq は 80 定理。
検証手順は [REPRODUCING.md](../REPRODUCING.md) を参照。

Lean の `EAN_rational`・`CovSP2_rational` と対応する木・実行形は `1 ≤ n` を仮定する。
`sum_P2` は自然数の減算の扱いにより `3 ≤ n` を仮定する。
符号語上の量と実行時のカウンタは `ExecBridge` の定理で結ばれる。

| 和文の番号 | ラベル | 主張 | 状態 | Rocq / Lean の定理名（モジュール） |
|---|---|---|:--:|---|
| 補題 1 | `lem:bij` | 符号語と木の全単射，$h=n-S$ | ✅ | Lean: `toPop_bijOn`, `image_toPop_eq_suffixes`, `finalH_add_sum_numNodes`（`TreeIdentities`）; Rocq: `bijection_decode_encode`, `height_eq_n_minus_S`（`Codewords`）, `ip_injective`, `ip_roundtrip`（`IpInjective`）; Lean にも `ip_injective` と、2026-09-20 から復号器の往復 `ipDec_ipo`, `ip_roundtrip`（`ExecModel`）がある |
| 補題 2 | `lem:ballot` | $P(h=m)=B(n,m)/C_n$ | ✅ | Lean: `hProb_eq_count`（`Asymptotics.lean`; `BallotCount.lean` の `W_add_choose`, `card_suffixes_eq_catalan`）＋ Rocq の全単射 |
| 補題 3 | `lem:equidist` | $\#\{T:R(T)+1=m\}=\#\{T:h(T)=m\}=B(n,m)$（$R+1$ と $h$ の同分布） | ✅ | Lean: `lemma_equidist`, `card_spine_eq_card_rlen`, `card_rlen_eq_W`, `rlen_chi`, `chi_injective`（`SpineEquidist`。節点数を保ち右の背骨の節点数を最終スタックの高さに移す全単射 `chi` による） |
| 補題 4 | `lem:inv` | 比較回数のループ不変条件 $\beta_i=i+s_i$，$\alpha_i=i$（$\mathcal M$）／$d_i$（$\mathcal N$） | ✅ | Lean: `stepM_delta`, `runM_delta`, `stepN_delta`, `runN_delta`（`ExecModel`。1 反復ごとにラベル比較はポップより 1 多く増える）; Rocq: `stepM_step`, `runM_aux_count`（`ReconstructM`）, `stepN_delta`, `runN_aux_count`（`ReconstructN`）。終了判定比較の $d_i$ の側は、終了時の値（2 子節点の数 + 1 = $P_2+1$）を `lcountN_eq`（`ExecStack`）／`lcount_N_full`（`ReconstructLcount`）が与える |
| 補題 5 | `lem:leaves` | $P_2=L-1$ | ✅ | Lean: `P2_add_one_eq_leaves`, `leaves_eq_twoNodes_succ`（`TreeIdentities`）; Rocq: `P2_identity`（`Trees`）, `full_leaves`（`ReconstructMoments`） |
| 系 6 | `cor:central` | $\mathrm{Cmp}_M=3n-1-h$, $\mathrm{Cmp}_N=2n+1-h+L$ | ✅ | Lean: **`central_M_exec`, `central_N_exec`（`ExecBridge`。i-p 列の上で実際に走らせたカウンタについての系 6 そのもの）**。費用モデルの式は `cmpsM_exec`（式 (2)）・`cmpsN_exec`（式 (3)）、その土台は `cmpsM_eq`/`cmpsN_eq`（`ExecModel`）, `popsM_eq_Srec`/`popsN_eq_Srec`, `lcountN_eq`（`ExecStack`）, `sum_toPop_eq_Srec`（`ExecModel`）。構造的な半分は `central_M`, `central_N`（`TreeIdentities`）; Rocq: `total_comparisons_M_count`, `total_comparisons_N_count`（`ReconstructM`/`ReconstructN`）＋ `height_eq_n_minus_S`, `lcount_N_full`, `pops_M_Srec`/`pops_N_Srec` |
| 命題 7 | `thm:sums` | $\sum S$, $\sum P_2$, $\mathbb E[S]$, $\mathbb E[P_2]$ | ✅ | Lean: `sum_pops`, `sum_P2`, `ES_rational`, `EP2_rational`（`ExactMoments`）, `ES_rational_trees`, `EP2_rational_trees`（`TreeIdentities`）; Rocq: `ES_rational`, `EP2_rational`, `avg_decomp_M`/`avg_decomp_N` |
| 注意 8 | `rem:oeis` | （主張ではない） | — | — |
| 系 9 | `cor:avg` | $\mathbb E[\mathrm{Cmp}_M]$, $\mathbb E[\mathrm{Cmp}_N]$ の閉形式 | ✅ | Lean: `EAM_rational`, `EAN_rational`（`ExactMoments`）, `EAM_rational_trees`, `EAN_rational_trees`（`TreeIdentities`）, `EAM_eq`, `EAN_eq`（`MomentBridge`）; $1/n$ 展開（すべての $n\ge1$ で明示定数つき）: `EAN_expansion`, `EAM_expansion`, `EP2_expansion`, `EAN_isBigO`, `EAM_isBigO`（`Expansions`）; Rocq: `EAM_rational`, `EAN_rational` |
| 命題 10 | `prop:varcov` | $\mathrm{Var}[S]$, $\mathrm{Var}[P_2]$, $\mathrm{Cov}[S,P_2]$ の閉形式 | ✅ | Lean: `VarP2_rational`, `CovSP2_rational`, `sum_pops_sq`（`ExactMoments`）, `VarP2_rational_trees`, `CovSP2_rational_trees`（`TreeIdentities`）, `VarS_eq`, `VarP2_eq`, `CovSP2_eq`, `VarAN_eq`（`MomentBridge`）; Rocq: `VarS_catalan`, `ESQ_rational`（`ReconstructES2`）; `VarP2_rational`, `CovSP2_rational`（`ReconstructES3`、2026-09-04。分母を払った形 $2(2n-1)^2(2n-3)\,C_n\sum P_2^2=n(n+1)(n-1)(n-2)C_n^2+2(2n-1)^2(2n-3)(\sum P_2)^2$ と $(n+2)(2n-1)\,C_n\sum SP_2=2(n-1)(n-2)C_n^2+(n+2)(2n-1)\sum S\sum P_2$。経由する閉形式は `SL2_closed`（$\sum L^2$）と `SLR_closed`（$\sum hL$）） |
| 定理 11 | `thm:vardich` | 分散の二分性 | ✅ | 厳密な閉形式は命題 10（Rocq）。漸近: Lean `VarS_asymp`（→4）, `VarAN_asymp`（$/n\to1/16$）, `CovSP2_asymp`（→1）。$1/n$ 展開（係数 $-30$，定数項 $193/32$，剰余の位数）: `VarS_expansion`（$\le144/n^2$）, `VarAN_expansion`（$\le40/n$）, `VarS_isBigO`, `VarAN_isBigO`（`Expansions`） |
| 命題 12 | `thm:Mlimit` | 負の二項極限 | ✅ | Lean: `thm_Mlimit`, `thm_Mlimit_count`; 一様評価 $P(h=m)\le m2^{-m}$（$n\ge2$）は `hProb_le_uniform`（`UniformBound`） |
| 系 13 | `cor:Mconc` | 最悪時への集中 | ✅ | Rocq: `M_worst`; Lean: `AM_worst_case_limit`, `AM_concentration`（`Concentration.lean`） |
| 命題 14 | `prop:leafclt` | 葉数の中心極限定理 | ✅ | Lean: `leafCLT_charFun`（`FinalAssembly.lean`）, `leafCLT_tendsto`（`WeakConvergence.lean`） |
| 定理 15 | `thm:Nclt` | $\mathrm{Cmp}_N$ の中心極限定理 | ✅ | Lean: `AN_CLT_charFun`（`AN_CLT_of_leafCLT` 経由）, `AN_CLT_tendsto` |
| 系 16 | `cor:sep` | 優位の定量化 | ✅ | Lean: 決定論的な分離は `gap_add`, `gap_ge`, `gap_ge_six`, `cmpsN_lt_cmpsM`, `exists_gap_attained`（`ExecBridge`）＋ `two_twoNodes_succ_le`, `two_leaves_le`, `comb`/`combL`（`TreeIdentities`）。CLT は `gap_CLT_charFun`, `gap_CLT_charFun_explicit`, `gap_CLT_tendsto`（`GapCLT`）; Rocq: `M_worst`, `N_worst_sharp`, `N_best`, `full_bound`, `P2_identity`。⚠️ **Rocq のこれらは表 1 の値の裏づけであって、点ごとの差 $\mathrm{Cmp}_M-\mathrm{Cmp}_N$ についての主張ではない**（`coq/` を grep して確認済み）。不等式とその達成は 2026-09-20 に Lean で初めて機械検証された |

`MomentBridge.lean` は、`Asymptotics.lean` の `EAM`・`EAN`・`VarS`・`VarP2`・`CovSP2`・`VarAN` が「論文に印刷された有理式の定義」にすぎなかったのを、標本空間上の実際の平均・分散・共分散と等しいと示して塞いだもの（2026-09-19）。これ以前は、定理 11 と系 9 の漸近が Rocq でしか裏づけられていない定義についての主張だった。

検査コマンド: `coq/check-axioms.sh`（80/80 が公理なし）、`lean/check-axioms.sh`（一覧の全定理が `propext`, `Classical.choice`, `Quot.sound` の部分集合）、`lean/check-statements.sh`（`STATEMENTS.lock` に凍結した定理の型のドリフト検出）。
