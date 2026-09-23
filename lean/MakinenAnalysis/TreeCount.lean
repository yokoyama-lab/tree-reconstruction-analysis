import Mathlib
import MakinenAnalysis.PopDegreeBridge

/-!
# The closed form in the language of trees

The refined count `U_mul_closed` of `PopDegreeBridge` is stated over Mäkinen
pop-codewords, and `card_dominating_closed` of `PopClosed` over dominating
degree words.  Both are encodings; the object the paper is *about* is the
binary tree.  This file states the closed form for trees themselves, using
Mathlib's `BinaryTree.treesOfNumNodesEq` as the sample space:

  `card_trees_twoNodes`
  `: n · #{t : n internal nodes, k two-children nodes}`
  `    = C(n,k) · C(n-k, n-1-2k) · 2^(n-1-2k)`.

The bridge `card_Tk_eq_Dk` (`PopDegreeBridge`, the `toDeg` bijection) does all
the work; this file is the composition, plus two corollaries:

* `sum_card_trees_twoNodes` — summing the closed form over `k` recovers
  `catalan n`, i.e. the binomial identity
  `Σ_k (1/n)·C(n,k)·C(n-k,n-1-2k)·2^(n-1-2k) = C_n`
  (a by-product of the development: a Stirling-free proof);
* `card_trees_twoNodes_eq_zero` — the count vanishes off the support `2k+1 ≤ n`.
-/

namespace MakinenAnalysis

open Finset

/-- The finset of `n`-node binary trees with exactly `k` two-children nodes. -/
noncomputable def treesTwo (n k : ℕ) : Finset (BinaryTree Unit) :=
  (BinaryTree.treesOfNumNodesEq n).filter (fun t => twoNodes t = k)

/-- **The closed form, over trees.**  For `1 ≤ n` and `2k + 1 ≤ n`, the number
    of binary trees on `n` internal nodes having exactly `k` two-children nodes
    is `(1/n)·C(n,k)·C(n-k, n-1-2k)·2^(n-1-2k)`, stated multiplicatively to stay
    in `ℕ`.

    This is the tree-side form of `U_mul_closed` (pop-codewords) and
    `card_dominating_closed` (degree words); the encodings are related by the
    `toDeg` bijection `card_Tk_eq_Dk`. -/
theorem card_trees_twoNodes (n k : ℕ) (hn : 1 ≤ n) (hk : 2 * k + 1 ≤ n) :
    n * (treesTwo n k).card
      = n.choose k * (n - k).choose (n - 1 - 2 * k) * 2 ^ (n - 1 - 2 * k) := by
  rw [treesTwo, card_Tk_eq_Dk n k hn, card_dominating_closed n k hk]

/-- Off the support the count is zero: a tree on `n` nodes cannot have `k`
    two-children nodes once `n < 2k + 1` (each two-children node needs its own
    pair of subtrees). -/
theorem card_trees_twoNodes_eq_zero (n k : ℕ) (hn : 1 ≤ n) (h : n < 2 * k + 1) :
    (treesTwo n k).card = 0 := by
  have hmul : n * (treesTwo n k).card = 0 := by
    rw [treesTwo, card_Tk_eq_Dk n k hn, card_dominating_mul, card_degWords,
      Nat.choose_eq_zero_of_lt (by omega : n - k < k + 1), mul_zero, zero_mul]
  rcases Nat.mul_eq_zero.mp hmul with h0 | h0
  · omega
  · exact h0

/-- **The counts sum to the Catalan number.**  Refining `catalan n` by the
    number of two-children nodes:
    `Σ_{k ≤ n} #{n-node trees with k two-children nodes} = catalan n`.

    Together with `card_trees_twoNodes` this is the binomial identity
    `Σ_k (1/n)·C(n,k)·C(n-k, n-1-2k)·2^(n-1-2k) = C_n`, obtained here without
    Stirling or singularity analysis. -/
theorem sum_card_trees_twoNodes (n : ℕ) :
    (∑ k ∈ range (n + 1), (treesTwo n k).card) = catalan n := by
  classical
  rw [← BinaryTree.treesOfNumNodesEq_card_eq_catalan n]
  simp only [treesTwo]
  refine (Finset.card_eq_sum_card_fiberwise (f := fun t => twoNodes t)
    (t := range (n + 1)) ?_).symm
  intro t ht
  rw [Finset.mem_coe, BinaryTree.mem_treesOfNumNodesEq] at ht
  rw [Finset.mem_coe, Finset.mem_range]
  show twoNodes t < n + 1
  -- a tree has at most as many two-children nodes as internal nodes
  have hle : twoNodes t ≤ BinaryTree.numNodes t := by
    clear ht
    induction t with
    | nil => simp [twoNodes]
    | node _ l r ihl ihr =>
      simp only [twoNodes, BinaryTree.numNodes]
      split <;> omega
  omega

end MakinenAnalysis
