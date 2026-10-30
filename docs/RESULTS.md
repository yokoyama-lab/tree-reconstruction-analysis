# Paper-to-proof correspondence

The labels below are from the Japanese manuscript (2026-09-23). Numbering in
earlier English drafts differs. Lean theorem names belong to `MakinenAnalysis`.
The exact types of all 208 audited Lean theorems are in
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

## Random BST model

These modules apply the same per-tree identities `central_M_exec` and
`central_N_exec` to the random BST model, where the keys `1, …, n` are inserted
in a uniformly random order. They accompany a separate manuscript on this model
(WiNF2026, cited as A2 in the source comments); that manuscript is not part of
this artifact. Parts were ported from a Rocq development that is not included.

| Result | Lean modules and representative theorems |
|---|---|
| BST weights and the law of `h` | `BstModel`: `bstE_one`, `bst_Pge`; `BstLimits`: `bst_Ph` |
| BST weights as random insertion orders | `BstPerm`: `bst_perm_count`, `bst_perm_law` |
| `h` and `L` read from the insertion times | `BstLemma1`: `lemma1_h`, `lemma1_L`; `BstRun`: `run_ge`, `run_eq` |
| Moments of `h`, `L` and the comparison counts | `BstModel`: `bst_Eh`, `bst_VarL`, `bst_CovhL`, `bst_EAM`, `bst_EAN`, `bst_VarAN`, `bst_CovAMAN` |
| Conditional moments and cumulants of `L` | `BstCond`: `bst_EqL`, `bst_EqL2`; `BstCumulant`: `bst_kappa3`, `bst_kappa4` |
| Limit law of `h` and total variation | `BstLimits`: `bst_h_tendsto`, `bst_dTV`, `bst_dTV_event`; `BstAM`: `bst_AM_tendsto`, `bst_AM_dTV` |
| Limits and error bounds of the moments | `BstLimits`: `bst_EAM_err`, `bst_VarAN_tendsto`, `bst_VarAN_err_le`, `bst_EAN_lt_EAM_iff` |
| Gap `D = Cmp_M − Cmp_N` and small cases | `BstLimits`: `D_eq`, `bst_ED`, `bst_VarD`, `bst_outcome_three`; `BstAM`: `D_ge`; `UnifOutcome`: `unif_outcome_three` |
| CLTs | `BstCLT`: `bst_leafCLT`, `bst_AN_CLT`, `bst_D_CLT` |

## One-pass lower bound

`OnePass` models a one-pass algorithm, which fixes the parent of each element
before reading the next. At each step it picks, from the whole history, an
ordered decision tree over the possible pop counts `0, …, m` (questions "is
`k ≥ j`?"). A leaf's depth is the number of informative label comparisons
(comparisons with a sentinel are not counted).

| Result | Theorem |
|---|---|
| Every one-pass algorithm needs `2n − 3` comparisons on the codeword `0, 1, …, 1` | `onePass_lower` |
| M makes exactly `(n − 1) + S − Q` comparisons (`Q`: steps that empty the stack) | `costM_eq` |
| M makes at most `2n − 3` comparisons on every codeword | `costM_le` |
| Hence the worst-case optimum among one-pass algorithms is `2n − 3` (`n ≥ 2`) | `onePass_worst_case` |

`OnePassProg`, `OnePassBridge` and `OnePassParent` carry the bound over to
programs run on actual trees. A program asks "is the label of `a` smaller than
that of `b`?" about elements already read (a question about an unread element
is answered "no") and outputs the parent of each element before reading the
next.

| Result | Theorem |
|---|---|
| Each question is monotone or antitone in the pop count; a step tree becomes an ordered tree, no deeper | `lt_mono_or_anti`, `extract_depth` |
| A correct program asks at least as many questions as the extracted ordered trees | `progCost_ge`, `prog_lower` |
| The stack run on the labels of `ip t` pops the codeword of `t` | `runL_ip` |
| i-p sequences avoid the pattern `231`; the oracle is the order of the labels | `ipo_noPat`, `lt_ip` |
| The parent chosen by the stack is the parent in the tree, for every tree | `tree_run`, `parentOf_eq_treePar` |
| Every correct one-pass program makes `2n − 3` comparisons on some tree; M makes at most `2n − 3` | `onePass_trees_real` |

The remaining modelling choice is that a program also knows the codeword
prefix of the elements read so far; a correct program can compute it from its
own outputs, so this only strengthens the lower bound.

The full list with one-line statements is in [`check-axioms.sh`](../lean/check-axioms.sh).

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
