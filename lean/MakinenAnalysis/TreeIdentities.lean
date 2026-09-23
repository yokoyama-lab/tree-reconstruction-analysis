import MakinenAnalysis.PopDegreeBridge
import MakinenAnalysis.ExactMoments

/-!
# The structural identities of the paper, on the tree side

`paper_ja.tex` Lemma 1 (`lem:bij`), Lemma 3 (`lem:leaves`) and the structural
half of Corollary 4 (`cor:central`), ported from the Rocq development
(`../../coq/Codewords.v`, `Trees.v`, `ReconstructMoments.v`).

Everything here is carried by the encoder `toPop : T → List ℕ` of
`PopDegreeBridge` (the Lean port of Rocq's `Codewords.v` structural encoder)
and by the conservation law `finalH_add_sum` of `LeafCount`:

| here | paper | Rocq counterpart |
|---|---|---|
| `toPop_bijOn` | Lemma 1, the bijection | `bijection_decode_encode` (`Codewords`) |
| `finalH_add_sum_numNodes` | Lemma 1, `h = n - S` | `height_eq_n_minus_S` (`Codewords`) |
| `toPop_P2` (`PopDegreeBridge`) | Lemma 3, `P₂ = #two-children nodes` | `P2_identity` (`Trees`) |
| `leaves_eq_twoNodes_succ` | Lemma 3, `n₂ = n₀ - 1` | `full_leaves` (`ReconstructMoments`) |
| `central_M` / `central_N` | Corollary 4, **structural half** | part of `total_comparisons_M/N_count` |

**Where the other half is.**  Corollary 4 as the paper states it is the
composition of two facts: the *cost model* `A_M = S + 2n-1`,
`A_N = S + P₂ + (n+2)` (equations `eq:AM` and `eq:AN`; these are statements about the
*runs* of the two algorithms, and need their operational semantics) and the
*structural substitution* `S = n - h`, `P₂ = L - 1`.  This file proves the
second.  The first is proved in `ExecModel`/`ExecStack`/`ExecBridge` (ported
from `ReconstructM.total_comparisons_M_count`,
`ReconstructN.total_comparisons_N_count`, `ReconstructPops.pops_M_Srec` /
`pops_N_Srec`, `ReconstructLcount.lcount_N_full`), and `ExecBridge` composes the
two into Corollary 4 itself: `central_M_exec`, `central_N_exec`, about the
comparison counters of the runs.  Those files import this one, so the theorems
below are stated with the cost model's right-hand side written out; the
substitution is what is proved here, nothing is assumed.  See
`PORT-STATUS-EXEC.md`.
-/

namespace MakinenAnalysis

open Finset

/-! ## Lemma 1: the codeword bijection and `h = n - S` -/

/-- **Lemma 1, second half** (Rocq: `height_eq_n_minus_S`).  Every node is
    pushed exactly once and `S` of them are popped, so the final stack height
    is `h = n - S`; stated additively to stay inside ℕ. -/
theorem finalH_add_sum_numNodes (t : T) (h : t ≠ .nil) :
    finalH 1 (toPop t) + (toPop t).sum = BinaryTree.numNodes t := by
  obtain ⟨hlen, hval⟩ := (mem_suffixes _ _ _).mp (toPop_mem_suffixes t h)
  have hcons := finalH_add_sum (toPop t) 1 hval
  have hl := toPop_length t h
  omega

/-- `toPop` is injective on the `n`-node trees. -/
lemma toPop_injOn (n : ℕ) (hn : 1 ≤ n) :
    Set.InjOn toPop (BinaryTree.treesOfNumNodesEq n : Set T) := by
  intro t1 h1 t2 h2 he
  rw [Finset.mem_coe, BinaryTree.mem_treesOfNumNodesEq] at h1 h2
  have hne1 : t1 ≠ .nil := by rintro rfl; simp [BinaryTree.numNodes] at h1; omega
  have hne2 : t2 ≠ .nil := by rintro rfl; simp [BinaryTree.numNodes] at h2; omega
  exact toPop_inj hne1 hne2 he

lemma toPop_mapsTo (n : ℕ) (hn : 1 ≤ n) :
    ∀ t ∈ BinaryTree.treesOfNumNodesEq n, toPop t ∈ suffixes (n - 1) 1 := by
  intro t ht
  rw [BinaryTree.mem_treesOfNumNodesEq] at ht
  have hne : t ≠ .nil := by rintro rfl; simp [BinaryTree.numNodes] at ht; omega
  have := toPop_mem_suffixes t hne
  rwa [ht] at this

/-- The image of the `n`-node trees under `toPop` is *all* of the codewords. -/
theorem image_toPop_eq_suffixes (n : ℕ) (hn : 1 ≤ n) :
    (BinaryTree.treesOfNumNodesEq n).image toPop = suffixes (n - 1) 1 := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro w hw
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hw
    exact toPop_mapsTo n hn t ht
  · rw [Finset.card_image_of_injOn (toPop_injOn n hn),
      BinaryTree.treesOfNumNodesEq_card_eq_catalan, card_suffixes_eq_catalan n hn]

/-- **Lemma 1, first half** (Rocq: `bijection_decode_encode`).  The pop-count
    encoder is a bijection from the `n`-node binary trees onto the codewords
    satisfying the ballot constraint. -/
theorem toPop_bijOn (n : ℕ) (hn : 1 ≤ n) :
    Set.BijOn toPop (BinaryTree.treesOfNumNodesEq n : Set T)
      (suffixes (n - 1) 1 : Set (List ℕ)) := by
  refine ⟨fun t ht => by
      simpa using toPop_mapsTo n hn t (by simpa using ht), toPop_injOn n hn, ?_⟩
  intro w hw
  rw [Finset.mem_coe, ← image_toPop_eq_suffixes n hn] at hw
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hw
  exact ⟨t, by simpa using ht, rfl⟩

/-! ## Lemma 3: `P₂ = L - 1` -/

/-- Number of leaves of a binary tree (internal nodes both of whose children
    are external). -/
def leaves : T → ℕ
  | .nil => 0
  | .node _ l r => (if isNode l || isNode r then 0 else 1) + leaves l + leaves r

@[simp] lemma leaves_nil : leaves (.nil : T) = 0 := rfl

/-- **Lemma 3, counting half** (Rocq: `full_leaves`).  In every non-empty
    binary tree the number of two-children nodes is one less than the number of
    leaves: `n₂ = n₀ - 1`, stated additively. -/
theorem leaves_eq_twoNodes_succ : ∀ t : T, t ≠ .nil → leaves t = twoNodes t + 1 := by
  intro t
  induction t with
  | nil => intro h; exact absurd rfl h
  | node v L R ihL ihR =>
    intro _
    by_cases hL : L = .nil <;> by_cases hR : R = .nil
    · subst hL; subst hR; simp [leaves, twoNodes]
    · subst hL
      have h1 := ihR hR
      have e1 : leaves (BinaryTree.node v .nil R) = leaves R := by
        simp [leaves, isNode_eq_true.mpr hR]
      have e2 : twoNodes (BinaryTree.node v .nil R) = twoNodes R := by
        simp [twoNodes]
      rw [e1, e2, h1]
    · subst hR
      have h1 := ihL hL
      have e1 : leaves (BinaryTree.node v L .nil) = leaves L := by
        simp [leaves, isNode_eq_true.mpr hL]
      have e2 : twoNodes (BinaryTree.node v L .nil) = twoNodes L := by
        simp [twoNodes]
      rw [e1, e2, h1]
    · have h1 := ihL hL
      have h2 := ihR hR
      have e1 : leaves (BinaryTree.node v L R) = leaves L + leaves R := by
        simp [leaves, isNode_eq_true.mpr hL, isNode_eq_true.mpr hR]
      have e2 : twoNodes (BinaryTree.node v L R) = 1 + twoNodes L + twoNodes R := by
        simp [twoNodes, isNode_eq_true.mpr hL, isNode_eq_true.mpr hR]
      rw [e1, e2, h1, h2]
      ring

/-- **Lemma 3** (`lem:leaves`, Rocq: `P2_identity` + `full_leaves`).
    The double-pop count of the codeword of `t` is `leaves t - 1`; additively,
    `P₂ + 1 = L`.  (`toPop_P2` is the first half: `P₂` counts the
    two-children nodes.) -/
theorem P2_add_one_eq_leaves (t : T) (h : t ≠ .nil) :
    P2 (toPop t) + 1 = leaves t := by
  rw [toPop_P2, leaves_eq_twoNodes_succ t h]

/-! ## Corollary 4, structural half

Substituting `S = n - h` and `P₂ = L - 1` into the cost model `A_M = S + 2n-1`
and `A_N = S + P₂ + (n+2)` (equations `eq:AM` and `eq:AN` of the paper) gives the
paper's central identities `A_M = 3n-1-h` and `A_N = 2n+1-h+L`.  Both are
stated additively.  The two theorems below are exactly that substitution: the
left-hand sides are the cost model's expressions, not the algorithms' counters.
That the counters really equal those expressions is `ExecBridge.cmpsM_exec` and
`ExecBridge.cmpsN_exec`, and `ExecBridge.central_M_exec` /
`ExecBridge.central_N_exec` are the resulting statements about the runs. -/

/-- **Corollary 4 for `A_M`, structural half**: from `A_M = S + 2n - 1`,
    `A_M + h + 1 = 3n`, i.e. `A_M = 3n - 1 - h`.  For the version whose `A_M`
    is the comparison counter of a run of `M`, see `ExecBridge.central_M_exec`. -/
theorem central_M (t : T) (h : t ≠ .nil) :
    ((toPop t).sum + (2 * BinaryTree.numNodes t - 1)) + finalH 1 (toPop t) + 1
      = 3 * BinaryTree.numNodes t := by
  have hns := finalH_add_sum_numNodes t h
  have hpos : 1 ≤ BinaryTree.numNodes t := by
    cases t with
    | nil => exact absurd rfl h
    | node _ _ _ => simp [BinaryTree.numNodes]
  omega

/-- **Corollary 4 for `A_N`, structural half**: from `A_N = S + P₂ + (n+2)`,
    `A_N + h = 2n + 1 + L`, i.e. `A_N = 2n + 1 - h + L`.  For the version whose
    `A_N` is the comparison counter of a run of `N`, see
    `ExecBridge.central_N_exec`. -/
theorem central_N (t : T) (h : t ≠ .nil) :
    ((toPop t).sum + P2 (toPop t) + (BinaryTree.numNodes t + 2))
        + finalH 1 (toPop t)
      = 2 * BinaryTree.numNodes t + 1 + leaves t := by
  have hns := finalH_add_sum_numNodes t h
  have hl := P2_add_one_eq_leaves t h
  omega

/-! ## The leaf bound `L ≤ ⌈n/2⌉`, and the trees that attain it

Corollary 14 of the paper needs one more structural fact beyond Lemma 3: a
binary tree on `n` internal nodes has at most `⌈n/2⌉` leaves, equivalently
`2·P₂ + 1 ≤ n`.  (Rocq: `ReconstructBounds.full_bound`.)  Every two-children
node forces its own pair of subtrees, so the two-children nodes cannot be more
than half of the tree.

`comb` and `combL` are the trees that make this an equality (resp. come within
one): a right-leaning chain of "cherries".  Together they realise every size
`n ≥ 1`, which is what makes Corollary 14's lower bound attained for every `n`. -/

/-- **The leaf bound** (Rocq: `ReconstructBounds.full_bound`).  Each
    two-children node consumes two non-empty subtrees, so `2·n₂ + 1 ≤ n`. -/
theorem two_twoNodes_succ_le : ∀ t : T, t ≠ .nil → 2 * twoNodes t + 1 ≤ t.numNodes := by
  intro t
  induction t with
  | nil => intro h; exact absurd rfl h
  | node v L R ihL ihR =>
    intro _
    by_cases hL : L = .nil <;> by_cases hR : R = .nil
    · subst hL; subst hR; simp [twoNodes]
    · subst hL
      have h1 := ihR hR
      have e2 : twoNodes (BinaryTree.node v .nil R) = twoNodes R := by simp [twoNodes]
      rw [e2]
      simp only [BinaryTree.numNodes] at *
      omega
    · subst hR
      have h1 := ihL hL
      have e2 : twoNodes (BinaryTree.node v L .nil) = twoNodes L := by simp [twoNodes]
      rw [e2]
      simp only [BinaryTree.numNodes] at *
      omega
    · have h1 := ihL hL
      have h2 := ihR hR
      have e2 : twoNodes (BinaryTree.node v L R) = 1 + twoNodes L + twoNodes R := by
        simp [twoNodes, isNode_eq_true.mpr hL, isNode_eq_true.mpr hR]
      rw [e2]
      simp only [BinaryTree.numNodes] at *
      omega

/-- `L ≤ ⌈n/2⌉`, stated without division: `2L ≤ n + 1`. -/
theorem two_leaves_le (t : T) (h : t ≠ .nil) : 2 * leaves t ≤ t.numNodes + 1 := by
  have h1 := two_twoNodes_succ_le t h
  rw [leaves_eq_twoNodes_succ t h]
  omega

/-- A right-leaning chain of `m` cherries with one cherry at the end:
    `2m + 1` nodes, `m + 1` leaves, `m` two-children nodes — the maximum
    possible for an odd size. -/
def comb : ℕ → T
  | 0 => .node () .nil .nil
  | m + 1 => .node () (.node () .nil .nil) (comb m)

/-- `comb m` hung under one unary node: `2m + 2` nodes, still `m + 1` leaves and
    `m` two-children nodes — the maximum possible for an even size. -/
def combL (m : ℕ) : T := .node () (comb m) .nil

lemma comb_ne_nil (m : ℕ) : comb m ≠ .nil := by cases m <;> simp [comb]

@[simp] lemma numNodes_comb (m : ℕ) : (comb m).numNodes = 2 * m + 1 := by
  induction m with
  | zero => simp [comb]
  | succ m ih => simp only [comb, BinaryTree.numNodes, ih]; omega

@[simp] lemma twoNodes_comb (m : ℕ) : twoNodes (comb m) = m := by
  induction m with
  | zero => simp [comb, twoNodes]
  | succ m ih =>
    have hc : twoNodes (BinaryTree.node () (.nil : T) .nil) = 0 := by simp [twoNodes]
    have he : twoNodes (BinaryTree.node () (.node () (.nil : T) .nil) (comb m))
        = 1 + twoNodes (.node () (.nil : T) .nil) + twoNodes (comb m) := by
      simp [twoNodes, isNode_eq_true.mpr (comb_ne_nil m)]
    rw [comb, he, hc, ih]
    omega

@[simp] lemma numNodes_combL (m : ℕ) : (combL m).numNodes = 2 * m + 2 := by
  simp only [combL, BinaryTree.numNodes, numNodes_comb]

@[simp] lemma twoNodes_combL (m : ℕ) : twoNodes (combL m) = m := by
  simp [combL, twoNodes]

lemma combL_ne_nil (m : ℕ) : combL m ≠ .nil := by simp [combL]

/-! ## Transport to the tree sample space

The paper's sums run over `𝒯_n`, the binary trees; the exact results of
`ExactMoments` run over the codewords.  Lemma 1 (`toPop_bijOn`) lets any
codeword statistic be summed on either side, so the paper's statements can be
stated literally over `BinaryTree.treesOfNumNodesEq n`. -/

/-- **Transport along the codeword bijection.**  Any statistic of the codeword
    sums to the same total over the trees and over the codewords. -/
theorem sum_tree_eq_sum_suffixes (n : ℕ) (hn : 1 ≤ n) (f : List ℕ → ℕ) :
    (∑ t ∈ BinaryTree.treesOfNumNodesEq n, f (toPop t))
      = ∑ w ∈ suffixes (n - 1) 1, f w := by
  rw [← image_toPop_eq_suffixes n hn,
    Finset.sum_image fun x hx y hy hxy =>
      toPop_injOn n hn (by simpa using hx) (by simpa using hy) hxy]

/-- **Theorem 5 over the trees** (Rocq: `ES_rational` over `trees_of_size`):
    `(n+2)·Σ_T S = n(n-1)·C_n`. -/
theorem ES_rational_trees (n : ℕ) (hn : 1 ≤ n) :
    (n + 2) * (∑ t ∈ BinaryTree.treesOfNumNodesEq n, (toPop t).sum)
      = n * (n - 1) * catalan n := by
  rw [sum_tree_eq_sum_suffixes n hn (fun w => w.sum)]
  exact ES_rational n hn

/-- **Theorem 5 over the trees**: `2(2n-1)·Σ_T P₂ = (n-1)(n-2)·C_n`. -/
theorem EP2_rational_trees (n : ℕ) (hn : 1 ≤ n) :
    2 * (2 * n - 1) * (∑ t ∈ BinaryTree.treesOfNumNodesEq n, P2 (toPop t))
      = (n - 1) * (n - 2) * catalan n := by
  rw [sum_tree_eq_sum_suffixes n (by omega) (fun w => P2 w)]
  exact EP2_rational n hn

/-- **Corollary 7 over the trees** (Rocq: `EAM_rational`). -/
theorem EAM_rational_trees (n : ℕ) (hn : 1 ≤ n) :
    (n + 2) * (∑ t ∈ BinaryTree.treesOfNumNodesEq n, ((toPop t).sum + (2 * n - 1)))
      = (n * (n - 1) + (2 * n - 1) * (n + 2)) * catalan n := by
  rw [sum_tree_eq_sum_suffixes n hn (fun w => w.sum + (2 * n - 1))]
  exact EAM_rational n hn

/-- **Corollary 7 over the trees** (Rocq: `EAN_rational`). -/
theorem EAN_rational_trees (n : ℕ) (hn : 1 ≤ n) :
    2 * (n + 2) * (2 * n - 1)
        * (∑ t ∈ BinaryTree.treesOfNumNodesEq n,
            ((toPop t).sum + P2 (toPop t) + (n + 2)))
      = (2 * (2 * n - 1) * n * (n - 1) + 2 * (n + 2) * (n + 2) * (2 * n - 1)
          + (n + 2) * (n - 1) * (n - 2)) * catalan n := by
  rw [sum_tree_eq_sum_suffixes n (by omega) (fun w => w.sum + P2 w + (n + 2))]
  exact EAN_rational n hn

/-- **Proposition 8 over the trees** (Rocq: `VarP2_rational`). -/
theorem VarP2_rational_trees (n : ℕ) (hn : 1 ≤ n) :
    2 * (2 * n - 1) * (2 * n - 1) * (2 * n - 3)
        * (catalan n
            * ∑ t ∈ BinaryTree.treesOfNumNodesEq n, P2 (toPop t) * P2 (toPop t))
      = n * (n + 1) * (n - 1) * (n - 2) * (catalan n * catalan n)
        + 2 * (2 * n - 1) * (2 * n - 1) * (2 * n - 3)
          * ((∑ t ∈ BinaryTree.treesOfNumNodesEq n, P2 (toPop t))
              * ∑ t ∈ BinaryTree.treesOfNumNodesEq n, P2 (toPop t)) := by
  rw [sum_tree_eq_sum_suffixes n (by omega) (fun w => P2 w * P2 w),
    sum_tree_eq_sum_suffixes n (by omega) (fun w => P2 w)]
  exact VarP2_rational n hn

/-- **Proposition 8 over the trees** (Rocq: `CovSP2_rational`). -/
theorem CovSP2_rational_trees (n : ℕ) (hn : 1 ≤ n) :
    (n + 2) * (2 * n - 1)
        * (catalan n
            * ∑ t ∈ BinaryTree.treesOfNumNodesEq n, (toPop t).sum * P2 (toPop t))
      = 2 * (n - 1) * (n - 2) * (catalan n * catalan n)
        + (n + 2) * (2 * n - 1)
          * ((∑ t ∈ BinaryTree.treesOfNumNodesEq n, (toPop t).sum)
              * ∑ t ∈ BinaryTree.treesOfNumNodesEq n, P2 (toPop t)) := by
  rw [sum_tree_eq_sum_suffixes n (by omega) (fun w => w.sum * P2 w),
    sum_tree_eq_sum_suffixes n (by omega) (fun w => w.sum),
    sum_tree_eq_sum_suffixes n (by omega) (fun w => P2 w)]
  exact CovSP2_rational n hn

/-! ## Machine-pinned instances (the numeric checks this port rests on)

Every general theorem of this port was checked against the Rocq development and
against the closed forms of `paper_ja.tex` before the general proof was
attempted.  The instances are pinned here (kernel-evaluated, `decide`) so that a
later change to a definition cannot slip past unnoticed.  `catalan` is defined
by well-founded recursion and does **not** reduce in the kernel, so the Catalan
numbers appear below only as literals.

Cross-check run on 2026-09-19 — Rocq `trees_of_size n n` (tree side, by
`vm_compute`) against Lean `suffixes (n-1) 1` (codeword side, by `#eval`),
`n = 1..8`, every column identical:

| n | C_n | Σ S | Σ P₂ | Σ P₂² | Σ S·P₂ |
|---|---|---|---|---|---|
| 3 | 5 | 6 | 1 | 1 | 2 |
| 4 | 14 | 28 | 6 | 6 | 16 |
| 5 | 42 | 120 | 28 | 32 | 96 |
| 6 | 132 | 495 | 120 | 160 | 510 |
| 7 | 429 | 2002 | 495 | 765 | 2530 |
| 8 | 1430 | 8008 | 2002 | 3542 | 12012 |
-/

section Regression

set_option maxRecDepth 100000

/-- `Σ P₂²` at `n = 5, 6` against `sum_P2_sq`. -/
example : (∑ w ∈ suffixes 4 1, P2 w * P2 w) = 32 := by decide
example : (5 - 1) * ((2 * 5 - 4).choose (5 - 5)) + (2 * 5 - 2).choose (5 - 3) = 32 := by decide
example : (∑ w ∈ suffixes 5 1, P2 w * P2 w) = 160 := by decide
example : (6 - 1) * ((2 * 6 - 4).choose (6 - 5)) + (2 * 6 - 2).choose (6 - 3) = 160 := by decide

/-- `Σ S·P₂` (Rocq `SSP2`) and `Σ h·P₂` (Rocq `SLR`) at small `n`. -/
example : (∑ w ∈ suffixes 3 1, w.sum * P2 w) = 16 := by decide
example : (∑ w ∈ suffixes 4 1, w.sum * P2 w) = 96 := by decide
example : (∑ w ∈ suffixes 5 1, w.sum * P2 w) = 510 := by decide
example : (∑ w ∈ suffixes 2 1, finalH 1 w * P2 w) = 1 := by decide
example : (∑ w ∈ suffixes 3 1, finalH 1 w * P2 w) = 8 := by decide
example : (∑ w ∈ suffixes 4 1, finalH 1 w * P2 w) = 44 := by decide

/-- The paper's kernel-method value `Σ h·P₂ = (n-2)(n-1)(3n-4)/(2(2n-1)(n+2))·C_n`,
    cleared, at `n = 4, 5` — an independent check of Proposition 8's proof. -/
example : 2 * (2 * 4 - 1) * (4 + 2) * 8 = (4 - 2) * (4 - 1) * (3 * 4 - 4) * 14 := by decide
example : 2 * (2 * 5 - 1) * (5 + 2) * 44 = (5 - 2) * (5 - 1) * (3 * 5 - 4) * 42 := by decide

/-! The tree-side pins are stated on explicit trees rather than by quantifying
over `BinaryTree.treesOfNumNodesEq n`: that finset is defined by well-founded
recursion and does not reduce in the kernel, so `decide` cannot see it.  (The
exhaustive check over all trees with `n ≤ 6` was run with `#eval`, outside the
kernel: zero counterexamples.)  `tree7` is the cross-check tree of Rocq's
`ReconstructM.v`. -/

/-- The 7-node cross-check tree of the Rocq development. -/
def tree7 : T :=
  .node () (.node () (.node () .nil .nil) (.node () .nil (.node () .nil .nil)))
           (.node () (.node () .nil .nil) .nil)

/-- A right spine on 5 nodes (`S = 0`, `h = n`, one leaf). -/
def rspine5 : T :=
  .node () .nil (.node () .nil (.node () .nil (.node () .nil (.node () .nil .nil))))

/-- A left spine on 5 nodes (`S` maximal). -/
def lspine5 : T :=
  .node () (.node () (.node () (.node () (.node () .nil .nil) .nil) .nil) .nil) .nil

/-- Lemma 1, Lemma 3 and both structural halves of Corollary 4, on three
    explicit trees. -/
example : ∀ t ∈ [tree7, rspine5, lspine5],
    leaves t = twoNodes t + 1
      ∧ P2 (toPop t) + 1 = leaves t
      ∧ finalH 1 (toPop t) + (toPop t).sum = BinaryTree.numNodes t
      ∧ (toPop t).sum + (2 * BinaryTree.numNodes t - 1) + finalH 1 (toPop t) + 1
          = 3 * BinaryTree.numNodes t
      ∧ (toPop t).sum + P2 (toPop t) + (BinaryTree.numNodes t + 2) + finalH 1 (toPop t)
          = 2 * BinaryTree.numNodes t + 1 + leaves t := by decide

end Regression

end MakinenAnalysis
