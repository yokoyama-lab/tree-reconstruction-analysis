import MakinenAnalysis.TreeCount
import MakinenAnalysis.BstLimits

/-!
# Who wins under the uniform model, for `n = 3, 4, 5`

A2 compares the probabilities that `N` wins (`A_N < A_M`), ties, and loses at
`n = 3, 4, 5` under the BST model (`BstLimits.bst_outcome_*`) with those under the
uniform model: `(0, 4/5, 1/5)`, `(4/7, 3/7, 0)`, `(20/21, 1/21, 0)`.  This file
proves the uniform-model triples.

Per tree, `A_M − A_N = n − 2 − L` (`D_eq`) and `L = twoNodes + 1`
(`leaves_eq_twoNodes_succ`), so each event is a condition on the number of
two-children nodes, whose counts are the closed form `card_trees_twoNodes`.

| here | A2 |
|---|---|
| `unif_outcome_three`, `_four`, `_five` | the uniform-model triples quoted in §5 |
-/

namespace MakinenAnalysis

open Finset

/-- Uniform-model probability of an event on the `n`-node trees. -/
noncomputable def uP (n : ℕ) (p : T → Prop) [DecidablePred p] : ℚ :=
  ((trees n).filter p).card / (catalan n : ℚ)

/-- On an `n`-node tree, the outcome is decided by `twoNodes` against `n − 3`. -/
lemma outcome_iff (t : T) (h : t ≠ .nil) :
    (cmpsN (ip t) < cmpsM (ip t) ↔ twoNodes t + 3 < t.numNodes) ∧
    (cmpsN (ip t) = cmpsM (ip t) ↔ twoNodes t + 3 = t.numNodes) ∧
    (cmpsM (ip t) < cmpsN (ip t) ↔ t.numNodes < twoNodes t + 3) := by
  obtain ⟨hM, hN, _, _⟩ := gap_facts t h
  have hL := leaves_eq_twoNodes_succ t h
  refine ⟨⟨fun _ => by omega, fun _ => by omega⟩, ⟨fun _ => by omega, fun _ => by omega⟩,
    ⟨fun _ => by omega, fun _ => by omega⟩⟩

lemma card_two (n k c : ℕ) (hn : 1 ≤ n) (hk : 2 * k + 1 ≤ n)
    (h : n.choose k * (n - k).choose (n - 1 - 2 * k) * 2 ^ (n - 1 - 2 * k) = n * c) :
    (treesTwo n k).card = c := by
  have := card_trees_twoNodes n k hn hk
  rw [h] at this
  exact Nat.eq_of_mul_eq_mul_left (by omega) this

lemma filter_twoNodes_eq (n k : ℕ) :
    (trees n).filter (fun t => twoNodes t = k) = treesTwo n k := rfl

lemma catalan_three : catalan 3 = 5 := by rw [catalan_eq_centralBinom_div]; rfl
lemma catalan_four : catalan 4 = 14 := by rw [catalan_eq_centralBinom_div]; rfl
lemma catalan_five : catalan 5 = 42 := by rw [catalan_eq_centralBinom_div]; rfl

lemma ne_nil_of_mem {n : ℕ} (hn : 1 ≤ n) {t : T} (ht : t ∈ trees n) : t ≠ .nil :=
  ne_nil_of_numNodes hn (BinaryTree.mem_treesOfNumNodesEq.mp ht)

/-- **`n = 3`: `(0, 4/5, 1/5)`.** -/
theorem unif_outcome_three :
    uP 3 (fun t => cmpsN (ip t) < cmpsM (ip t)) = 0 ∧
    uP 3 (fun t => cmpsN (ip t) = cmpsM (ip t)) = 4 / 5 ∧
    uP 3 (fun t => cmpsM (ip t) < cmpsN (ip t)) = 1 / 5 := by
  have hn : (1 : ℕ) ≤ 3 := by norm_num
  have c0 := card_two 3 0 4 hn (by norm_num) (by norm_num [Nat.choose])
  have c1 := card_two 3 1 1 hn (by norm_num) (by norm_num [Nat.choose])
  have e1 : (trees 3).filter (fun t => cmpsN (ip t) < cmpsM (ip t)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro t ht
    have h1 := (outcome_iff t (ne_nil_of_mem hn ht)).1
    rw [BinaryTree.mem_treesOfNumNodesEq.mp ht] at h1
    omega
  have e2 : (trees 3).filter (fun t => cmpsN (ip t) = cmpsM (ip t)) = treesTwo 3 0 := by
    rw [← filter_twoNodes_eq]
    refine Finset.filter_congr (fun t ht => ?_)
    have h1 := (outcome_iff t (ne_nil_of_mem hn ht)).2.1
    rw [BinaryTree.mem_treesOfNumNodesEq.mp ht] at h1
    omega
  have e3 : (trees 3).filter (fun t => cmpsM (ip t) < cmpsN (ip t)) = treesTwo 3 1 := by
    rw [← filter_twoNodes_eq]
    refine Finset.filter_congr (fun t ht => ?_)
    have h1 := (outcome_iff t (ne_nil_of_mem hn ht)).2.2
    have hb := two_twoNodes_succ_le t (ne_nil_of_mem hn ht)
    rw [BinaryTree.mem_treesOfNumNodesEq.mp ht] at h1 hb
    omega
  simp only [uP, e1, e2, e3, c0, c1, catalan_three]
  norm_num

/-- **`n = 4`: `(4/7, 3/7, 0)`.** -/
theorem unif_outcome_four :
    uP 4 (fun t => cmpsN (ip t) < cmpsM (ip t)) = 4 / 7 ∧
    uP 4 (fun t => cmpsN (ip t) = cmpsM (ip t)) = 3 / 7 ∧
    uP 4 (fun t => cmpsM (ip t) < cmpsN (ip t)) = 0 := by
  have hn : (1 : ℕ) ≤ 4 := by norm_num
  have c0 := card_two 4 0 8 hn (by norm_num) (by norm_num [Nat.choose])
  have c1 := card_two 4 1 6 hn (by norm_num) (by norm_num [Nat.choose])
  have e1 : (trees 4).filter (fun t => cmpsN (ip t) < cmpsM (ip t)) = treesTwo 4 0 := by
    rw [← filter_twoNodes_eq]
    refine Finset.filter_congr (fun t ht => ?_)
    have h1 := (outcome_iff t (ne_nil_of_mem hn ht)).1
    rw [BinaryTree.mem_treesOfNumNodesEq.mp ht] at h1
    omega
  have e2 : (trees 4).filter (fun t => cmpsN (ip t) = cmpsM (ip t)) = treesTwo 4 1 := by
    rw [← filter_twoNodes_eq]
    refine Finset.filter_congr (fun t ht => ?_)
    have h1 := (outcome_iff t (ne_nil_of_mem hn ht)).2.1
    rw [BinaryTree.mem_treesOfNumNodesEq.mp ht] at h1
    omega
  have e3 : (trees 4).filter (fun t => cmpsM (ip t) < cmpsN (ip t)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro t ht
    have h1 := (outcome_iff t (ne_nil_of_mem hn ht)).2.2
    have hb := two_twoNodes_succ_le t (ne_nil_of_mem hn ht)
    rw [BinaryTree.mem_treesOfNumNodesEq.mp ht] at h1 hb
    omega
  simp only [uP, e1, e2, e3, c0, c1, catalan_four]
  norm_num

/-- **`n = 5`: `(20/21, 1/21, 0)`.** -/
theorem unif_outcome_five :
    uP 5 (fun t => cmpsN (ip t) < cmpsM (ip t)) = 20 / 21 ∧
    uP 5 (fun t => cmpsN (ip t) = cmpsM (ip t)) = 1 / 21 ∧
    uP 5 (fun t => cmpsM (ip t) < cmpsN (ip t)) = 0 := by
  have hn : (1 : ℕ) ≤ 5 := by norm_num
  have c0 := card_two 5 0 16 hn (by norm_num) (by norm_num [Nat.choose])
  have c1 := card_two 5 1 24 hn (by norm_num) (by norm_num [Nat.choose])
  have c2 := card_two 5 2 2 hn (by norm_num) (by norm_num [Nat.choose])
  have e1 : (trees 5).filter (fun t => cmpsN (ip t) < cmpsM (ip t))
      = treesTwo 5 0 ∪ treesTwo 5 1 := by
    rw [← filter_twoNodes_eq, ← filter_twoNodes_eq, ← Finset.filter_or]
    refine Finset.filter_congr (fun t ht => ?_)
    have h1 := (outcome_iff t (ne_nil_of_mem hn ht)).1
    rw [BinaryTree.mem_treesOfNumNodesEq.mp ht] at h1
    omega
  have hdisj : Disjoint (treesTwo 5 0) (treesTwo 5 1) := by
    rw [← filter_twoNodes_eq, ← filter_twoNodes_eq]
    exact Finset.disjoint_filter.mpr (fun t _ h1 h2 => by omega)
  have e2 : (trees 5).filter (fun t => cmpsN (ip t) = cmpsM (ip t)) = treesTwo 5 2 := by
    rw [← filter_twoNodes_eq]
    refine Finset.filter_congr (fun t ht => ?_)
    have h1 := (outcome_iff t (ne_nil_of_mem hn ht)).2.1
    rw [BinaryTree.mem_treesOfNumNodesEq.mp ht] at h1
    omega
  have e3 : (trees 5).filter (fun t => cmpsM (ip t) < cmpsN (ip t)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro t ht
    have h1 := (outcome_iff t (ne_nil_of_mem hn ht)).2.2
    have hb := two_twoNodes_succ_le t (ne_nil_of_mem hn ht)
    rw [BinaryTree.mem_treesOfNumNodesEq.mp ht] at h1 hb
    omega
  simp only [uP, e1, e2, e3, Finset.card_union_of_disjoint hdisj, c0, c1, c2, catalan_five]
  norm_num

end MakinenAnalysis
