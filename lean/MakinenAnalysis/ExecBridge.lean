import MakinenAnalysis.ExecStack
import MakinenAnalysis.TreeIdentities
import MakinenAnalysis.MomentBridge
import MakinenAnalysis.TreeEnum

/-!
# Corollary 4, in full: the cost model is a theorem

`TreeIdentities` proves the *structural* half of Corollary 4 of `paper_ja.tex`:
given the cost model `A_M = S + 2n-1` and `A_N = S + P₂ + (n+2)` (equations `eq:AM`
and `eq:AN`), substituting `S = n - h` and `P₂ = L - 1` yields `A_M = 3n-1-h` and
`A_N = 2n+1-h+L`.  The cost model itself was left to Rocq.

This file closes that gap.  `ExecModel` and `ExecStack` give

* `cmpsM_eq` : `A_M = 2n - 1 + pops_M`   (the counter invariant)
* `popsM_eq_Srec`, `popsN_eq_Srec` : the run's pop count is `Srec`
* `lcountN_eq` : the index tests are `n₂ + 1`
* `sum_toPop_eq_Srec` : `Srec t = Σ toPop t`, the join with the codeword side

and composing them here gives equations `eq:AM` and `eq:AN` as theorems about the *runs*
(`cmpsM_exec`, `cmpsN_exec`), hence Corollary 4 itself
(`central_M_exec`, `central_N_exec`), and then Theorem 5, Corollary 7 and the
covariance of Proposition 8 as statements about the runs
(`ES_exec_rational_trees`, `EAM_exec_rational_trees`, `EAN_exec_rational_trees`,
`CovSP2_exec_rational_trees`), and finally the printed rational functions as the
actual means of the comparison counts over uniform `n`-node trees
(`EAM_eq_exec`, `EAN_eq_exec`).

Rocq counterparts: `ReconstructES.EAN_rational` and `ReconstructES3.CovSP2_rational`
are stated about `total_comparisons_N (ip t)` and `pops_N (ip t)` exactly as the
`*_exec_*` theorems here are.
-/

namespace MakinenAnalysis

open Finset

/-! ## 1. The cost model of the paper, proved from the runs -/

theorem popsM_eq_sum_toPop (t : T) : popsM (ip t) = (toPop t).sum := by
  rw [popsM_eq_Srec, ← sum_toPop_eq_Srec]

theorem popsN_eq_sum_toPop (t : T) : popsN (ip t) = (toPop t).sum := by
  rw [popsN_eq_Srec, ← sum_toPop_eq_Srec]

theorem lcountN_eq_P2 (t : T) (h : t ≠ .nil) : lcountN (ip t) = P2 (toPop t) + 1 := by
  rw [lcountN_eq t h, toPop_P2]

theorem cmpsM_exec (t : T) (h : t ≠ .nil) :
    cmpsM (ip t) = (toPop t).sum + (2 * t.numNodes - 1) := by
  rw [cmpsM_eq t h, popsM_eq_sum_toPop]; omega

theorem cmpsN_exec (t : T) (h : t ≠ .nil) :
    cmpsN (ip t) = (toPop t).sum + P2 (toPop t) + (t.numNodes + 2) := by
  rw [cmpsN_eq t h, popsN_eq_sum_toPop, lcountN_eq_P2 t h]; omega

/-! ## 2. Corollary 4, in full -/

theorem central_M_exec (t : T) (h : t ≠ .nil) :
    cmpsM (ip t) + finalH 1 (toPop t) + 1 = 3 * t.numNodes := by
  rw [cmpsM_exec t h]; exact central_M t h

theorem central_N_exec (t : T) (h : t ≠ .nil) :
    cmpsN (ip t) + finalH 1 (toPop t) = 2 * t.numNodes + 1 + leaves t := by
  rw [cmpsN_exec t h]; exact central_N t h

/-! ## 2b. Corollary 14: the deterministic separation

`A_M - A_N = (n-3) - P₂ ≥ ⌊n/2⌋ - 2`, and the bound is attained for every `n`.
The first equality is Corollary 4; the inequality is the leaf bound
`two_twoNodes_succ_le` (Rocq: `ReconstructBounds.full_bound`); the attainment is
the two cherry-chain families `comb`/`combL` of `TreeIdentities`.

Neither half of the inequality is in the Rocq development: Rocq proves the
individual best/worst cases (`M_best`, `M_worst`, `N_best`, `N_worst_sharp`) and
that `M`'s worst and `N`'s best are attained for every `n`, but not the pointwise
gap.  Subtraction is avoided throughout, so the statements hold in ℕ for every
`n ≥ 1`. -/

/-- **Corollary 14, the identity** `A_M - A_N = (n - 3) - P₂`, additively. -/
theorem gap_add (t : T) (h : t ≠ .nil) :
    cmpsM (ip t) + P2 (toPop t) + 3 = cmpsN (ip t) + t.numNodes := by
  have hpos : 1 ≤ t.numNodes := by
    cases t with
    | nil => exact absurd rfl h
    | node _ _ _ => simp [BinaryTree.numNodes]
  rw [cmpsM_exec t h, cmpsN_exec t h]
  omega

/-- **Corollary 14, the lower bound**, in the sharp additive form
    `A_N + ⌊n/2⌋ ≤ A_M + 2`. -/
theorem gap_ge (t : T) (h : t ≠ .nil) :
    cmpsN (ip t) + t.numNodes / 2 ≤ cmpsM (ip t) + 2 := by
  have hg := gap_add t h
  have hb := two_twoNodes_succ_le t h
  rw [← toPop_P2] at hb
  omega

/-- The paper's form: on every tree with `n ≥ 6` nodes, `N` makes at least
    `⌊n/2⌋ - 2` fewer comparisons than `M`. -/
theorem gap_ge_six (t : T) (h : 6 ≤ t.numNodes) :
    cmpsN (ip t) + (t.numNodes / 2 - 2) ≤ cmpsM (ip t) := by
  have hne : t ≠ .nil := by rintro rfl; simp [BinaryTree.numNodes] at h
  have := gap_ge t hne
  omega

/-- In particular `A_N < A_M` for every tree on `n ≥ 6` nodes (Glück--Yokoyama's
    deterministic comparison, re-derived from the central identities). -/
theorem cmpsN_lt_cmpsM (t : T) (h : 6 ≤ t.numNodes) : cmpsN (ip t) < cmpsM (ip t) := by
  have := gap_ge_six t h
  omega

/-- **The bound is attained**, odd sizes: `comb m` has `2m+1` nodes and makes the
    gap exactly `⌊n/2⌋ - 2`. -/
theorem gap_attained_odd (m : ℕ) :
    cmpsN (ip (comb m)) + (comb m).numNodes / 2 = cmpsM (ip (comb m)) + 2 := by
  have hg := gap_add (comb m) (comb_ne_nil m)
  rw [toPop_P2, twoNodes_comb, numNodes_comb] at hg
  rw [numNodes_comb]
  omega

/-- **The bound is attained**, even sizes: `combL m` has `2m+2` nodes. -/
theorem gap_attained_even (m : ℕ) :
    cmpsN (ip (combL m)) + (combL m).numNodes / 2 = cmpsM (ip (combL m)) + 2 := by
  have hg := gap_add (combL m) (combL_ne_nil m)
  rw [toPop_P2, twoNodes_combL, numNodes_combL] at hg
  rw [numNodes_combL]
  omega

/-- **Corollary 14's lower bound is attained for every size** `n ≥ 1`. -/
theorem exists_gap_attained (n : ℕ) (hn : 1 ≤ n) :
    ∃ t : T, t.numNodes = n ∧ cmpsN (ip t) + n / 2 = cmpsM (ip t) + 2 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · refine ⟨combL (k - 1), ?_, ?_⟩
    · rw [numNodes_combL]; omega
    · have := gap_attained_even (k - 1)
      rw [numNodes_combL] at this
      rw [show n = 2 * (k - 1) + 2 by omega]
      exact this
  · refine ⟨comb k, ?_, ?_⟩
    · rw [numNodes_comb]; omega
    · have := gap_attained_odd k
      rw [numNodes_comb] at this
      rw [show n = 2 * k + 1 by omega]
      exact this

/-! ## 3. The sums over the paper's sample space -/

lemma ne_nil_of_mem_trees {n : ℕ} (hn : 1 ≤ n) {t : T}
    (ht : t ∈ BinaryTree.treesOfNumNodesEq n) : t ≠ .nil ∧ t.numNodes = n := by
  rw [BinaryTree.mem_treesOfNumNodesEq] at ht
  refine ⟨?_, ht⟩
  rintro rfl
  simp [BinaryTree.numNodes] at ht
  omega

theorem ES_exec_rational_trees (n : ℕ) (hn : 1 ≤ n) :
    (n + 2) * (∑ t ∈ BinaryTree.treesOfNumNodesEq n, popsN (ip t))
      = n * (n - 1) * catalan n := by
  rw [Finset.sum_congr rfl (fun t _ => popsN_eq_sum_toPop t)]
  exact ES_rational_trees n hn

theorem EAM_exec_rational_trees (n : ℕ) (hn : 1 ≤ n) :
    (n + 2) * (∑ t ∈ BinaryTree.treesOfNumNodesEq n, cmpsM (ip t))
      = (n * (n - 1) + (2 * n - 1) * (n + 2)) * catalan n := by
  rw [Finset.sum_congr rfl (fun t ht => by
    obtain ⟨hne, hnn⟩ := ne_nil_of_mem_trees hn ht
    rw [cmpsM_exec t hne, hnn])]
  exact EAM_rational_trees n hn

theorem EAN_exec_rational_trees (n : ℕ) (hn : 1 ≤ n) :
    2 * (n + 2) * (2 * n - 1) * (∑ t ∈ BinaryTree.treesOfNumNodesEq n, cmpsN (ip t))
      = (2 * (2 * n - 1) * n * (n - 1) + 2 * (n + 2) * (n + 2) * (2 * n - 1)
          + (n + 2) * (n - 1) * (n - 2)) * catalan n := by
  rw [Finset.sum_congr rfl (fun t ht => by
    obtain ⟨hne, hnn⟩ := ne_nil_of_mem_trees (by omega : 1 ≤ n) ht
    rw [cmpsN_exec t hne, hnn])]
  exact EAN_rational_trees n hn

theorem CovSP2_exec_rational_trees (n : ℕ) (hn : 1 ≤ n) :
    (n + 2) * (2 * n - 1)
        * (catalan n
            * ∑ t ∈ BinaryTree.treesOfNumNodesEq n, popsN (ip t) * (lcountN (ip t) - 1))
      = 2 * (n - 1) * (n - 2) * (catalan n * catalan n)
        + (n + 2) * (2 * n - 1)
          * ((∑ t ∈ BinaryTree.treesOfNumNodesEq n, popsN (ip t))
              * ∑ t ∈ BinaryTree.treesOfNumNodesEq n, (lcountN (ip t) - 1)) := by
  have hrw : ∀ t ∈ BinaryTree.treesOfNumNodesEq n,
      popsN (ip t) * (lcountN (ip t) - 1) = (toPop t).sum * P2 (toPop t) := by
    intro t ht
    obtain ⟨hne, -⟩ := ne_nil_of_mem_trees (by omega : 1 ≤ n) ht
    rw [popsN_eq_sum_toPop, lcountN_eq_P2 t hne]
    simp
  have hrw2 : ∀ t ∈ BinaryTree.treesOfNumNodesEq n,
      lcountN (ip t) - 1 = P2 (toPop t) := by
    intro t ht
    obtain ⟨hne, -⟩ := ne_nil_of_mem_trees (by omega : 1 ≤ n) ht
    rw [lcountN_eq_P2 t hne]; omega
  rw [Finset.sum_congr rfl hrw, Finset.sum_congr rfl hrw2,
    Finset.sum_congr rfl (fun t _ => popsN_eq_sum_toPop t)]
  exact CovSP2_rational_trees n hn

/-! ## 4. The printed rational functions are the means of the runs -/

noncomputable def EofTree (n : ℕ) (f : T → ℕ) : ℝ :=
  ((∑ t ∈ BinaryTree.treesOfNumNodesEq n, f t : ℕ) : ℝ) / (catalan n : ℝ)

theorem EAM_eq_exec (n : ℕ) (hn : 1 ≤ n) :
    EAM n = EofTree n (fun t => cmpsM (ip t)) := by
  rw [EAM_eq n hn, Eof, EofTree]
  congr 2
  rw [← sum_tree_eq_sum_suffixes n hn (fun w => w.sum + (2 * n - 1))]
  exact (Finset.sum_congr rfl (fun t ht => by
    obtain ⟨hne, hnn⟩ := ne_nil_of_mem_trees hn ht
    rw [cmpsM_exec t hne, hnn])).symm

theorem EAN_eq_exec (n : ℕ) (hn : 1 ≤ n) :
    EAN n = EofTree n (fun t => cmpsN (ip t)) := by
  rw [EAN_eq n hn, Eof, EofTree]
  congr 2
  rw [← sum_tree_eq_sum_suffixes n (by omega) (fun w => w.sum + P2 w + (n + 2))]
  exact (Finset.sum_congr rfl (fun t ht => by
    obtain ⟨hne, hnn⟩ := ne_nil_of_mem_trees (by omega : 1 ≤ n) ht
    rw [cmpsN_exec t hne, hnn])).symm

/-! ## 5. The model really is the reconstruction algorithm

The two runs carry the node array, and `runMN_agree` says they fill it in
identically.  That the array they fill in is the tree's own child relation is
checked here on explicit trees (Rocq checks all trees of size ≤ 9 by
reflection: `Reconstruct.reconstruct_correct_upto_10`,
`ReconstructN.correctN_upto_9`). -/

/-- The root's inorder label, as an option (`none` for the empty tree). -/
def rootOpt (off : ℕ) : T → Option ℕ
  | .nil => none
  | .node _ l _ => some (off + l.numNodes)

/-- The tree's own child relation: every node label paired with its
    `(left, right)` children (Rocq: `Reconstruct.child_assoc`). -/
def childAssoc : ℕ → T → List (ℕ × Cell)
  | _, .nil => []
  | off, .node _ l r =>
      (off + l.numNodes, (rootOpt off l, rootOpt (off + l.numNodes + 1) r))
        :: (childAssoc off l ++ childAssoc (off + l.numNodes + 1) r)

/-- `N`'s run rebuilds the child relation of `t`. -/
def rebuildsN (t : T) : Prop := ∀ p ∈ childAssoc 0 t, (runNFull (ip t)).arr p.1 = p.2

/-- `M`'s run rebuilds the child relation of `t`. -/
def rebuildsM (t : T) : Prop := ∀ p ∈ childAssoc 0 t, (runMFull (ip t)).arr p.1 = p.2

instance (t : T) : Decidable (rebuildsN t) := List.decidableBAll _ _
instance (t : T) : Decidable (rebuildsM t) := List.decidableBAll _ _

/-- **The two algorithms produce the same node array.**  A consequence of the
    simulation `runMN_agree`; it makes the reconstruction checks below
    interchangeable. -/
theorem runMFull_arr_eq (t : T) : (runMFull (ip t)).arr = (runNFull (ip t)).arr := by
  by_cases h : t = .nil
  · subst h; rfl
  · obtain ⟨x0, rest, hip, -⟩ := ip_eq_cons h
    rw [hip, runMFull_cons, runNFull_cons]
    exact (runMN_agree _ _ _ rfl rfl rfl).1

theorem rebuildsM_iff_rebuildsN (t : T) : rebuildsM t ↔ rebuildsN t := by
  unfold rebuildsM rebuildsN; rw [runMFull_arr_eq]

/-! ## 6. Machine-pinned instances

Cross-check run on 2026-09-20 against the Rocq development (`vm_compute` on
`trees_upto 8`, i.e. all 2055 trees with `1 ≤ n ≤ 8`) and against
`paper_ja.tex`.  Every per-tree record
`(ip, Srec, rlen, pops_M, A_M, pops_N, lcount_N, A_N, n₂, L)` was identical on
the two sides for `n ≤ 6` (196 trees, compared as sorted multisets keyed by the
i-p sequence), and every column total was identical for `n ≤ 8`:

| n | #trees | Σ S | Σ A_M | Σ lcount_N | Σ A_N | Σ n₂ | Σ L |
|---|---|---|---|---|---|---|---|
| 1 | 1 | 0 | 1 | 1 | 3 | 0 | 1 |
| 2 | 2 | 1 | 7 | 2 | 9 | 0 | 2 |
| 3 | 5 | 6 | 31 | 6 | 32 | 1 | 6 |
| 4 | 14 | 28 | 126 | 20 | 118 | 6 | 20 |
| 5 | 42 | 120 | 498 | 70 | 442 | 28 | 70 |
| 6 | 132 | 495 | 1947 | 252 | 1671 | 120 | 252 |
| 7 | 429 | 2002 | 7579 | 924 | 6358 | 495 | 924 |
| 8 | 1430 | 8008 | 29458 | 3432 | 24310 | 2002 | 3432 |

The five per-tree identities proved above (`popsM_eq_sum_toPop`,
`lcountN_eq_P2`, `cmpsM_exec`, `cmpsN_exec` and both halves of Corollary 4) were
also checked by `#eval` on all 2055 trees with `n ≤ 8`: zero counterexamples.
The instances below pin the same facts inside the build, on the paper's running
example and on the two spines.  (`BinaryTree.treesOfNumNodesEq` is defined by
well-founded recursion and does not reduce in the kernel, so the pins are stated
on explicit trees, as in `TreeIdentities`.) -/

section Regression

set_option maxRecDepth 4000

/-- The paper's Figure 2: `ip = [4,1,0,2,3,6,5]` (Rocq: `ip_tree7`). -/
example : ip tree7 = [4, 1, 0, 2, 3, 6, 5] := by decide

/-- ... and the decoder reads Figure 2 back (`ip_roundtrip`, run in the kernel). -/
example : ipDec 0 (ip tree7) = tree7 := by decide

/-- Figure 2's node array (Rocq: `run_tree7_nodes`). -/
example : ((runNFull (ip tree7)).arr 4, (runNFull (ip tree7)).arr 1,
    (runNFull (ip tree7)).arr 2, (runNFull (ip tree7)).arr 6)
      = ((some 1, some 6), (some 0, some 2), (none, some 3), (some 5, none)) := by decide

/-! The reconstruction is checked exhaustively, not on samples: see
`rebuildsN_le_eight` / `rebuildsM_le_eight` below. -/

/-- The counters on `tree7` (Rocq: `mcount_tree7`, `ncount_tree7`,
    `Srec_tree7`, `lcount_N_full_tree7`): `S = 5`, `A_M = 18 = 2·7-1+5`,
    `A_N = 16 = 5+2+7+2`, `lcount_N = 3 = n₂+1`. -/
example : (Srec tree7, popsM (ip tree7), cmpsM (ip tree7),
    popsN (ip tree7), lcountN (ip tree7), cmpsN (ip tree7))
      = (5, 5, 18, 5, 3, 16) := by decide

/-- The bridge and both halves of Corollary 4, on three explicit trees. -/
example : ∀ t ∈ [tree7, rspine5, lspine5],
    popsM (ip t) = (toPop t).sum
      ∧ popsN (ip t) = (toPop t).sum
      ∧ lcountN (ip t) = P2 (toPop t) + 1
      ∧ cmpsM (ip t) = (toPop t).sum + (2 * BinaryTree.numNodes t - 1)
      ∧ cmpsN (ip t) = (toPop t).sum + P2 (toPop t) + (BinaryTree.numNodes t + 2)
      ∧ cmpsM (ip t) + finalH 1 (toPop t) + 1 = 3 * BinaryTree.numNodes t
      ∧ cmpsN (ip t) + finalH 1 (toPop t) = 2 * BinaryTree.numNodes t + 1 + leaves t := by
  decide

/-- **Corollary 14** on explicit trees: the leaf bound, the gap identity and the
    gap lower bound.  `comb 3` (`n = 7`) and `combL 3` (`n = 8`) are the members
    of the two attaining families at those sizes. -/
example : ∀ t ∈ [tree7, rspine5, lspine5, comb 3, combL 3],
    2 * twoNodes t + 1 ≤ BinaryTree.numNodes t
      ∧ cmpsM (ip t) + P2 (toPop t) + 3 = cmpsN (ip t) + BinaryTree.numNodes t
      ∧ cmpsN (ip t) + BinaryTree.numNodes t / 2 ≤ cmpsM (ip t) + 2 := by decide

/-- The two families attain the bound with equality, and have the maximal number
    of leaves for their size. -/
example : BinaryTree.numNodes (comb 3) = 7 ∧ BinaryTree.numNodes (combL 3) = 8
    ∧ leaves (comb 3) = 4 ∧ leaves (combL 3) = 4
    ∧ cmpsN (ip (comb 3)) + 7 / 2 = cmpsM (ip (comb 3)) + 2
    ∧ cmpsN (ip (combL 3)) + 8 / 2 = cmpsM (ip (combL 3)) + 2 := by decide

end Regression

/-! ## 7. The reconstruction, checked exhaustively in the kernel

That the two machines fill in the node array with the tree's own child relation
is the one statement of this development that is *not* proved for all `n` — in
either system.  Rocq checks it by reflection up to `n ≤ 10` for the
Algorithm-C model and `n ≤ 9` for `N` (`reconstruct_correct_upto_10`,
`correctN_upto_9`); Rocq's all-`n` theorem `reconstruct_correct_all` is about
Algorithm C's machine, which pushes conditionally and is not the machine costed
here.  Rocq has no all-`n` correctness theorem for `M` or `N`.

Below is the same bounded check, but as a theorem quantified over *all* trees of
the given size (`TreeEnum.forall_numNodes_eq`), evaluated by the kernel and
therefore re-run by `lake build` and by CI.  `n ≤ 8` is 2055 trees and costs
about 46 s and 5 GB locally (`n ≤ 7`, 626 trees, took twelve seconds); the CI
runner has 16 GB, so the bound was raised from 7 to 8 on 2026-09-20. -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- **`N`'s run rebuilds the tree**, for every tree with at most 8 internal
    nodes (2055 trees, kernel-checked).  The array condition is written out rather
    than hidden behind `rebuildsN`, so that `STATEMENTS.lock` pins the meaning and
    not just the name: weakening the *definition* then breaks this proof. -/
theorem rebuildsN_le_eight (t : T) (h : t.numNodes ≤ 8) :
    ∀ p ∈ childAssoc 0 t, (runNFull (ip t)).arr p.1 = p.2 := by
  have key : ∀ n ≤ 8, ∀ s : T, s.numNodes = n → rebuildsN s := by
    intro n hn
    interval_cases n <;> exact forall_numNodes_eq (by decide)
  exact key t.numNodes h t rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- **`M`'s run rebuilds the tree**, likewise.  (`runMFull_arr_eq` shows the two
    arrays coincide for every `n`, so this and the previous theorem are the same
    bounded fact seen twice; both are pinned because the two definitions are
    what a reader checks against Figure 1.) -/
theorem rebuildsM_le_eight (t : T) (h : t.numNodes ≤ 8) :
    ∀ p ∈ childAssoc 0 t, (runMFull (ip t)).arr p.1 = p.2 := by
  have key : ∀ n ≤ 8, ∀ s : T, s.numNodes = n → rebuildsM s := by
    intro n hn
    interval_cases n <;> exact forall_numNodes_eq (by decide)
  exact key t.numNodes h t rfl


end MakinenAnalysis
