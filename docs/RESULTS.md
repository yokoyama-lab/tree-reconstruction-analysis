# Paper-to-proof correspondence

The labels below are from the Japanese manuscript (2026-09-23). Numbering in
earlier English drafts differs. Lean theorem names belong to `MakinenAnalysis`.
The exact types of all 114 audited Lean theorems are in
[`STATEMENTS.lock`](../lean/STATEMENTS.lock).

| Paper label / result | Lean modules and representative theorems | Rocq counterparts |
|---|---|---|
| `lem:bij`: codewords and final height | `TreeIdentities`: `toPop_bijOn`, `finalH_add_sum_numNodes` | `Codewords`: `bijection_decode_encode`, `height_eq_n_minus_S` |
| `lem:ballot`: ballot distribution | `BallotCount`, `Asymptotics`: `card_suffixes_eq_catalan`, `hProb_eq_count` | Tree/codeword bijection in `Codewords` |
| `lem:leaves`: double pops and leaves | `TreeIdentities`: `P2_add_one_eq_leaves` | `Trees`: `P2_identity`; `ReconstructMoments`: `full_leaves` |
| `cor:central`: execution comparison counts | `ExecBridge`: `cmpsM_exec`, `cmpsN_exec`, `central_M_exec`, `central_N_exec` | `ReconstructM`, `ReconstructN`: `total_comparisons_M_count`, `total_comparisons_N_count` |
| `thm:sums`: totals and expectations | `ExactMoments`: `sum_pops`, `sum_P2`, `ES_rational`, `EP2_rational` | `ReconstructES`: `ES_rational`; `ReconstructAverage`: `EP2_rational` |
| `cor:avg`: mean comparisons | `ExecBridge`: `EAM_exec_rational_trees`, `EAN_exec_rational_trees`; `Expansions`: `EAM_expansion`, `EAN_expansion` | `ReconstructES`: `EAM_rational`, `EAN_rational` |
| `prop:varcov`: variances and covariance | `ExactMoments`: `VarP2_rational`, `CovSP2_rational`; `MomentBridge`: `VarS_eq`, `VarP2_eq`, `CovSP2_eq`, `VarAN_eq` | `ReconstructES2`: `VarS_catalan`; `ReconstructES3`: `VarP2_rational`, `CovSP2_rational` |
| `thm:vardich`: variance asymptotics | `Asymptotics`: `VarS_asymp`, `VarAN_asymp`, `CovSP2_asymp`; `Expansions`: `VarS_expansion`, `VarAN_expansion` | Exact formulas above |
| `thm:Mlimit`: negative-binomial limit | `Asymptotics`: `thm_Mlimit`, `thm_Mlimit_count` | — |
| `cor:Mconc`: worst-case concentration | `Concentration`: `AM_worst_case_limit`, `AM_concentration` | `ReconstructBounds`: `M_worst` (deterministic bound) |
| `prop:leafclt`: leaf-count CLT | `FinalAssembly`: `leafCLT_charFun`; `WeakConvergence`: `leafCLT_tendsto` | — |
| `thm:Nclt`: comparison-count CLT | `FinalAssembly`: `AN_CLT_charFun`; `WeakConvergence`: `AN_CLT_tendsto` | — |
| `cor:sep`: deterministic gap and its CLT | `ExecBridge`: deterministic separation; `GapCLT`: `gap_CLT_charFun_explicit`, `gap_CLT_tendsto` | `ReconstructBounds`, `Trees`, `ReconstructM`, `ReconstructN` |

## Scope

Execution-count identities hold generally for the algorithms run on an i-p
sequence. Lean's additional reconstruction-correctness enumeration covers
`n ≤ 8` (2,055 nonempty trees over sizes 1–8); Rocq proves reconstruction
correctness for all sizes and also provides an imperative/heap development.
The Lean CLTs include convergence in distribution using Mathlib's continuity
theorem, not only convergence of characteristic functions.

Lean's exact mean/covariance rational identities include `n = 1`. Some auxiliary
identities, notably `sum_P2`, require `n ≥ 3` because natural-number subtraction
is truncated. Explicit remainder bounds in `Expansions` hold for all `n ≥ 1`.
Read the theorem types when applying these lemmas. Numerical experiments are
independent cross-checks, not proofs of the asymptotic results.

The [Japanese table](../coq/paper_ja-correspondence.md) gives additional details.
Theorem names retaining `A_M` / `A_N` denote the paper's `Cmp_M` / `Cmp_N`.
