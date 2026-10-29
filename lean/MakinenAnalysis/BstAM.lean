import MakinenAnalysis.BstLimits

/-!
# A2's Table 1 in the form `A_M`, and the gap bound in integers

`BstLimits` states the limit law of `M` through `h` (`bst_h_tendsto`, `bst_dTV`,
`bst_Varh_tendsto`).  A2's Table 1 writes them for the comparison count itself:
`(3n − 1) − A_M →d H` with `d_TV = 1/(n+1)!`, and `Var[A_M] → 3e − e²`.  Since
`(3n − 1) − A_M = h` on every non-empty tree (`central_M_exec`), these are
corollaries; this file states them in that form.  It also restates the
model-independent bound `D ≥ ⌊n/2⌋ − 2` (`ExecBridge.gap_ge`) in integers.

| here | A2 |
|---|---|
| `bst_AM_tendsto`, `bst_AM_dTV` | `(3n − 1) − A_M →d H`, `d_TV = 1/(n+1)!` (Table 1) |
| `bst_VarAM_tendsto` | `Var[A_M] → 3e − e²` (Table 1) |
| `D_ge` | `D ≥ ⌊n/2⌋ − 2` for every tree with `n ≥ 1` nodes (§5) |
-/

namespace MakinenAnalysis

open Filter
open scoped Topology

/-- `P((3n − 1) − A_M = m)` under the BST model. -/
def bstPAM (n m : ℕ) : ℚ := bstE n (fun t => if 3 * n - 1 - cmpsM (ip t) = m then 1 else 0)

lemma bstPAM_eq (n m : ℕ) (hn : 1 ≤ n) : bstPAM n m = bstPh n m := by
  refine bstE_congr (fun t ht => ?_)
  obtain ⟨hM, _, _, _⟩ := gap_facts t (ne_nil_of_numNodes hn ht)
  rw [ht] at hM
  have : 3 * n - 1 - cmpsM (ip t) = rlen t := by omega
  rw [this]

/-- **`(3n − 1) − A_M →d H`.** -/
theorem bst_AM_tendsto (m : ℕ) :
    Tendsto (fun n => (bstPAM n m : ℝ)) atTop (𝓝 (Hpmf m)) := by
  refine (bst_h_tendsto m).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [bstPAM_eq n m hn]

/-- **`d_TV((3n − 1) − A_M, H) = 1/(n+1)!`**: the absolute differences sum to `2/(n+1)!`. -/
theorem bst_AM_dTV (n : ℕ) (hn : 1 ≤ n) :
    HasSum (fun m => |(bstPAM n m : ℝ) - Hpmf m|) (2 / ((n + 1).factorial : ℝ)) := by
  simpa only [bstPAM_eq n _ hn] using bst_dTV n hn

/-- `Var[A_M] = Var[h]` (`n ≥ 1`), since `A_M = 3n − 1 − h`. -/
lemma bst_VarAM_eq (n : ℕ) (hn : 1 ≤ n) :
    bstE n (fun t => (cmpsM (ip t) : ℚ) ^ 2) - bstE n (fun t => (cmpsM (ip t) : ℚ)) ^ 2
      = bstE n (fun t => (rlen t : ℚ) ^ 2) - bstE n (fun t => (rlen t : ℚ)) ^ 2 := by
  have hq : ∀ t : T, t.numNodes = n → (cmpsM (ip t) : ℚ) = (3 * n - 1) - rlen t :=
    fun t ht => by rw [cmpsM_q t (ne_nil_of_numNodes hn ht), ht]
  rw [bstE_congr (f := fun t => (cmpsM (ip t) : ℚ) ^ 2)
      (g := fun t => ((3 * (n : ℚ) - 1) ^ 2 - 2 * (3 * n - 1) * rlen t) + (rlen t : ℚ) ^ 2)
      (fun t ht => by rw [hq t ht]; ring),
    bstE_congr (f := fun t => (cmpsM (ip t) : ℚ)) (g := fun t => (3 * (n : ℚ) - 1) - rlen t) hq,
    bstE_add, bstE_sub, bstE_const, bstE_smul, bstE_sub, bstE_const]
  ring

/-- **`Var[A_M] → 3e − e²`**. -/
theorem bst_VarAM_tendsto :
    Tendsto (fun n => ((bstE n (fun t => (cmpsM (ip t) : ℚ) ^ 2)
      - bstE n (fun t => (cmpsM (ip t) : ℚ)) ^ 2 : ℚ) : ℝ)) atTop
      (𝓝 (3 * Real.exp 1 - Real.exp 1 ^ 2)) := by
  refine bst_Varh_tendsto.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [bst_VarAM_eq n hn]

/-- **`D ≥ ⌊n/2⌋ − 2`** in integers, for every tree with `n ≥ 1` nodes (from `gap_ge`). -/
theorem D_ge (t : T) (ht : 1 ≤ t.numNodes) :
    ((t.numNodes / 2 : ℕ) : ℤ) - 2 ≤ (cmpsM (ip t) : ℤ) - cmpsN (ip t) := by
  have := gap_ge t (by rintro rfl; simp [BinaryTree.numNodes] at ht)
  omega

end MakinenAnalysis
