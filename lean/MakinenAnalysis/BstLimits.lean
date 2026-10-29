import MakinenAnalysis.BstModel

/-!
# The random BST model: the limit law of `h`, the gap `D`, and the limits of the moments

Continues `BstModel` (the exact finite-`n` closed forms) with the statements of
WiNF2026 A2 that are about `n → ∞`, about total variation, and about the gap
`D = A_M − A_N`.

| here | A2 |
|---|---|
| `bst_Ph` | `P(h=m) = m/(m+1)!` (`1 ≤ m < n`), `P(h=n) = 1/n!` |
| `hasSum_Hpmf`, `hasSum_Hpmf_tail` | `H` with `P(H=m) = m/(m+1)!` is a law, `P(H ≥ m) = 1/m!` |
| `bst_h_tendsto` | `h →d H` (pointwise convergence of the probabilities) |
| `bst_dTV` | `½ Σ_m |P(h=m) − P(H=m)| = 1/(n+1)!` exactly |
| `bst_dTV_event` | `max_A |P(h∈A) − P(H∈A)| = 1/(n+1)!` (attained at `A = {n}`) |
| `hasSum_H_mean`, `hasSum_H_sq`, `hasSum_H_pgf` | `E[H] = e−1`, `E[H²] = e+1` (so `Var[H] = 3e−e²`), `E[z^H] = (1+(z−1)e^z)/z` |
| `tendsto_Ee`, `tendsto_Fe`, `bst_Varh_tendsto`, `bst_CovhL_tendsto` | `E_n → e−1`, `F_n → e+1`, `Var[h] → 3e−e²`, `Cov(h,L) → 2−5e/6` |
| `bst_VarAN_tendsto`, `bst_CovAMAN_tendsto` | `Var[A_N] − 2n/45 → 2/45+14e/3−e²−4`, `Cov[A_M,A_N] → 23e/6−e²−2` |
| `bst_EAM_err` | `E[A_M] = 3n − e + O(1/n!)`, explicitly `|E[A_M] − (3n−e)| ≤ 1/n!` |
| `bst_VarAN_err_eq`, `bst_VarAN_err_le`, `bst_VarAN_n10` | the error of `Var[A_N] − 2n/45` in closed form, `≤ 1/(n−1)!`, and `< 2·10⁻⁷` at `n = 10` |
| `bst_EAM_sub_tendsto`, `bst_ratio_tendsto` | `E[A_M] − (3n−4) → 4−e`, `1 − E[A_N]/E[A_M] → 2/9` |
| `bst_EAN_lt_EAM_iff` | `E[A_N] < E[A_M] ↔ n ≥ 4` |
| `D_eq` | `D = n−2−L` on every tree (`L ≤ ⌈n/2⌉` and `D ≥ ⌊n/2⌋−2` are the model-independent `two_leaves_le`, `ExecBridge.gap_ge`) |
| `bst_ED`, `bst_VarD` | `E[D] = (2n−7)/3`, `Var[D] = 2(n+1)/45` |
| `bst_PAM_max` | `P(A_M = 3n−2) = 1/2` |
| `bst_outcome_three`, `_four`, `_five` | `N` wins, ties, loses with probabilities `(0,2/3,1/3)`, `(1/3,2/3,0)`, `(13/15,2/15,0)` |

The central limit theorems are in `BstCLT`, the identification of `bstW` with
random-permutation insertion in `BstPerm`.
-/

namespace MakinenAnalysis

open Finset Filter
open scoped Topology Nat

/-! ## 1. The exact law of `h` -/

/-- `P(h = m)` for the `n`-node BST. -/
def bstPh (n m : ℕ) : ℚ := bstE n (fun t => if rlen t = m then 1 else 0)

lemma bstPh_eq_sub (n m : ℕ) : bstPh n m = bstPge n m - bstPge n (m + 1) := by
  rw [bstPh, bstPge, bstPge, ← bstE_sub]
  refine bstE_congr (fun t _ => ?_)
  by_cases h1 : rlen t = m
  · simp [h1]
  · by_cases h2 : m ≤ rlen t
    · rw [if_neg h1, if_pos h2, if_pos (by omega)]; ring
    · rw [if_neg h1, if_neg h2, if_neg (by omega)]; ring

/-- **The law of `h`.** -/
theorem bst_Ph (n m : ℕ) (hn : 1 ≤ n) :
    bstPh n m = if m = 0 then 0 else if m < n then (m : ℚ) / (m + 1).factorial
      else if m = n then 1 / (n.factorial : ℚ) else 0 := by
  rw [bstPh_eq_sub, bst_Pge, bst_Pge]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [if_pos (Nat.zero_le n), if_pos hn, if_pos rfl]; simp
  rcases lt_trichotomy m n with h | rfl | h
  · rw [if_pos h.le, if_pos (show m + 1 ≤ n by omega), if_neg (show ¬m = 0 by omega), if_pos h,
      fact_succ_q]
    have := fact_ne_zero_q m
    field_simp
    ring
  · rw [if_pos le_rfl, if_neg (show ¬m + 1 ≤ m by omega), if_neg (show ¬m = 0 by omega),
      if_neg (lt_irrefl m), if_pos rfl]
    ring
  · rw [if_neg (show ¬m ≤ n by omega), if_neg (show ¬m + 1 ≤ n by omega),
      if_neg (show ¬m = 0 by omega), if_neg (show ¬m < n by omega), if_neg (show ¬m = n by omega)]
    ring

/-! ## 2. The limit law `H` -/

/-- `P(H = m) = m/(m+1)!`. -/
noncomputable def Hpmf (m : ℕ) : ℝ := (m : ℝ) / (m + 1).factorial

lemma fact_succ_r (n : ℕ) : ((n + 1).factorial : ℝ) = (n + 1) * n.factorial := by
  rw [Nat.factorial_succ]; push_cast; ring

lemma fact_pos_r (n : ℕ) : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n

/-- `m/(m+1)! = 1/m! − 1/(m+1)!`. -/
lemma Hpmf_eq (m : ℕ) : Hpmf m = 1 / (m.factorial : ℝ) - 1 / ((m + 1).factorial : ℝ) := by
  rw [Hpmf, fact_succ_r]
  have := fact_pos_r m
  field_simp
  ring

lemma Hpmf_nonneg (m : ℕ) : 0 ≤ Hpmf m := by
  rw [Hpmf]; exact div_nonneg (Nat.cast_nonneg _) (fact_pos_r _).le

lemma hasSum_of_eq {f g : ℕ → ℝ} {a b : ℝ} (h : HasSum f a) (hf : ∀ n, f n = g n) (ha : a = b) :
    HasSum g b := by
  subst ha; rwa [← show f = g from funext hf]

lemma tendsto_inv_fact : Tendsto (fun n : ℕ => 1 / (n.factorial : ℝ)) atTop (𝓝 0) := by
  have : Tendsto (fun n : ℕ => (n.factorial : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp factorial_tendsto_atTop
  exact this.inv_tendsto_atTop.congr (fun n => by simp)

/-- Partial sums of the tail `Σ_{k<N} P(H = m+k) = 1/m! − 1/(m+N)!`. -/
lemma sum_Hpmf_tail (m N : ℕ) :
    ∑ k ∈ range N, Hpmf (m + k) = 1 / (m.factorial : ℝ) - 1 / ((m + N).factorial : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ, ih, Hpmf_eq, ← add_assoc]; ring

/-- **`P(H ≥ m) = 1/m!`** for every `m` (for `m = 0` this is `1`, `P(H = 0) = 0`). -/
theorem hasSum_Hpmf_tail (m : ℕ) : HasSum (fun k => Hpmf (m + k)) (1 / (m.factorial : ℝ)) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => Hpmf_nonneg _)]
  simp_rw [sum_Hpmf_tail]
  have h : Tendsto (fun N => 1 / ((m + N).factorial : ℝ)) atTop (𝓝 0) :=
    (tendsto_inv_fact.comp (tendsto_add_atTop_nat m)).congr
      (fun N => by simp only [Function.comp, add_comm])
  simpa using (tendsto_const_nhds (x := 1 / (m.factorial : ℝ))).sub h

/-- **`H` is a probability law.** -/
theorem hasSum_Hpmf : HasSum Hpmf 1 := by
  simpa using hasSum_Hpmf_tail 0

/-- **`h →d H`**: for every `m`, `P(h_n = m) → P(H = m)` (the probabilities agree once
    `n > m`). -/
theorem bst_h_tendsto (m : ℕ) :
    Tendsto (fun n => (bstPh n m : ℝ)) atTop (𝓝 (Hpmf m)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop m] with n hn
  rw [bst_Ph n m (by omega)]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [Hpmf]
  · rw [if_neg (by omega), if_pos hn, Hpmf]; push_cast; rfl

/-! ## 3. Total variation -/

/-- The individual differences: `0` below `n`, `1/(n+1)!` at `n`, `P(H=m)` above. -/
lemma absdiff_eq (n m : ℕ) (hn : 1 ≤ n) :
    |(bstPh n m : ℝ) - Hpmf m|
      = if m < n then 0 else if m = n then 1 / ((n + 1).factorial : ℝ) else Hpmf m := by
  rw [bst_Ph n m hn]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [Hpmf, show 0 < n by omega]
  rw [if_neg (show ¬m = 0 by omega)]
  rcases lt_trichotomy m n with h | rfl | h
  · rw [if_pos h, if_pos h, Hpmf]; push_cast; simp
  · rw [if_neg (lt_irrefl m), if_pos rfl, if_neg (lt_irrefl m), if_pos rfl, Hpmf, fact_succ_r]
    have := fact_pos_r m
    rw [abs_of_nonneg]
    · push_cast; field_simp; ring
    · push_cast
      rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  · rw [if_neg (show ¬m < n by omega), if_neg (show ¬m = n by omega),
      if_neg (show ¬m < n by omega), if_neg (show ¬m = n by omega)]
    simp [abs_of_nonneg (Hpmf_nonneg m)]

/-- **Total variation, exactly**: `Σ_m |P(h=m) − P(H=m)| = 2/(n+1)!`, i.e.
    `d_TV(h, H) = ½ Σ_m |P(h=m) − P(H=m)| = 1/(n+1)!`. -/
theorem bst_dTV (n : ℕ) (hn : 1 ≤ n) :
    HasSum (fun m => |(bstPh n m : ℝ) - Hpmf m|) (2 / ((n + 1).factorial : ℝ)) := by
  rw [← hasSum_nat_add_iff' (n + 1)]
  have hhead : ∑ i ∈ range (n + 1), |(bstPh n i : ℝ) - Hpmf i| = 1 / ((n + 1).factorial : ℝ) := by
    rw [sum_range_succ, absdiff_eq n n hn, if_neg (lt_irrefl n), if_pos rfl]
    rw [Finset.sum_eq_zero (fun i hi => by
      rw [absdiff_eq n i hn, if_pos (Finset.mem_range.mp hi)])]
    simp
  rw [hhead]
  refine hasSum_of_eq (hasSum_Hpmf_tail (n + 1)) (fun k => ?_) (by ring)
  rw [absdiff_eq n (k + (n + 1)) hn, if_neg (by omega), if_neg (by omega), add_comm]

/-- `P(h ∈ A)` for the `n`-node BST. -/
noncomputable def bstPA (n : ℕ) (A : Set ℕ) : ℚ := bstE n (fun t => A.indicator (fun _ => 1) (rlen t))

/-- `P(H ∈ A)`. -/
noncomputable def PHA (A : Set ℕ) : ℝ := ∑' m, A.indicator Hpmf m

lemma bstPA_eq (n : ℕ) (A : Set ℕ) :
    bstPA n A = ∑ m ∈ range (n + 1), A.indicator (fun m => bstPh n m) m := by
  rw [bstPA]
  rw [bstE_congr (g := fun t => ∑ m ∈ range (n + 1),
      A.indicator (fun _ => (1 : ℚ)) m * (if rlen t = m then 1 else 0)) (fun t ht => ?_)]
  · rw [bstE_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [bstE_smul]
    by_cases hm : m ∈ A
    · simp [Set.indicator_of_mem hm, bstPh]
    · simp [Set.indicator_of_notMem hm]
  · have hle : rlen t ≤ n := ht ▸ rlen_le_numNodes t
    rw [Finset.sum_eq_single (rlen t)]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

lemma summable_indicator_Hpmf (A : Set ℕ) : Summable (A.indicator Hpmf) :=
  hasSum_Hpmf.summable.of_nonneg_of_le (fun m => Set.indicator_nonneg (fun m _ => Hpmf_nonneg m) m)
    (fun m => Set.indicator_le_self' (fun m _ => (Hpmf_nonneg m)) m)

/-- **Total variation as a maximum over events**: every event moves by at most
    `1/(n+1)!` … -/
theorem bst_dTV_event (n : ℕ) (hn : 1 ≤ n) (A : Set ℕ) :
    |(bstPA n A : ℝ) - PHA A| ≤ 1 / ((n + 1).factorial : ℝ) := by
  have hs := summable_indicator_Hpmf A
  rw [PHA, ← hs.sum_add_tsum_nat_add (n + 1), bstPA_eq, Rat.cast_sum]
  have hhead : ∑ m ∈ range (n + 1), ((A.indicator (fun m => bstPh n m) m : ℚ) : ℝ)
      - ∑ m ∈ range (n + 1), A.indicator Hpmf m
      = A.indicator (fun _ => 1 / ((n + 1).factorial : ℝ)) n := by
    rw [← Finset.sum_sub_distrib, sum_range_succ, Finset.sum_eq_zero (fun i hi => ?_)]
    · by_cases hA : n ∈ A
      · simp only [Set.indicator_of_mem hA, zero_add]
        have := absdiff_eq n n hn
        rw [if_neg (lt_irrefl n), if_pos rfl] at this
        rw [← this, abs_of_nonneg]
        have h2 := bst_Ph n n hn
        rw [if_neg (by omega), if_neg (lt_irrefl n), if_pos rfl] at h2
        rw [h2, Hpmf, fact_succ_r]; push_cast
        have := fact_pos_r n
        rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
      · simp [Set.indicator_of_notMem hA]
    · have hi' := Finset.mem_range.mp hi
      by_cases hA : i ∈ A
      · simp only [Set.indicator_of_mem hA]
        have := absdiff_eq n i hn
        rw [if_pos hi'] at this
        exact abs_eq_zero.mp this
      · simp [Set.indicator_of_notMem hA]
  have htail : 0 ≤ ∑' k, A.indicator Hpmf (k + (n + 1)) ∧
      ∑' k, A.indicator Hpmf (k + (n + 1)) ≤ 1 / ((n + 1).factorial : ℝ) := by
    have ht := hasSum_Hpmf_tail (n + 1)
    refine ⟨tsum_nonneg (fun k => Set.indicator_nonneg (fun m _ => Hpmf_nonneg m) _), ?_⟩
    rw [← ht.tsum_eq]
    refine Summable.tsum_le_tsum (fun k => ?_) ((summable_nat_add_iff (n + 1)).mpr hs) ht.summable
    rw [add_comm]; exact Set.indicator_le_self' (fun m _ => Hpmf_nonneg m) _
  have hpos : (0 : ℝ) ≤ 1 / ((n + 1).factorial : ℝ) := by have := fact_pos_r (n + 1); positivity
  rw [show ∀ a b c : ℝ, a - (b + c) = (a - b) - c from fun a b c => by ring, hhead, abs_le]
  by_cases hA : n ∈ A
  · simp only [Set.indicator_of_mem hA]; constructor <;> linarith [htail.1, htail.2]
  · simp only [Set.indicator_of_notMem hA]; constructor <;> linarith [htail.1, htail.2]

/-- … and the event `A = {n}` attains it. -/
theorem bst_dTV_event_attained (n : ℕ) (hn : 1 ≤ n) :
    |(bstPA n {n} : ℝ) - PHA {n}| = 1 / ((n + 1).factorial : ℝ) := by
  have h1 : bstPA n {n} = bstPh n n := by
    rw [bstPA_eq, Finset.sum_eq_single n]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have h2 : PHA {n} = Hpmf n := by
    rw [PHA, tsum_eq_single n]
    · simp
    · intro b hb; simp [hb]
  rw [h1, h2, absdiff_eq n n hn, if_neg (lt_irrefl n), if_pos rfl]

/-! ## 4. Moments and generating function of `H` -/

lemma hasSum_inv_fact : HasSum (fun k : ℕ => 1 / (k.factorial : ℝ)) (Real.exp 1) := by
  have := NormedSpace.expSeries_div_hasSum_exp (1 : ℝ)
  rw [← Real.exp_eq_exp_ℝ] at this
  simpa using this

lemma hasSum_pow_div_fact (z : ℝ) : HasSum (fun k : ℕ => z ^ k / (k.factorial : ℝ)) (Real.exp z) := by
  have := NormedSpace.expSeries_div_hasSum_exp z
  rwa [← Real.exp_eq_exp_ℝ] at this

/-- `Σ_{m≥1} 1/(m-1)! = e`, written with the zero term at `m = 0`. -/
lemma hasSum_shift_inv_fact (j : ℕ) :
    HasSum (fun m : ℕ => if m < j then 0 else 1 / ((m - j).factorial : ℝ)) (Real.exp 1) := by
  rw [← hasSum_nat_add_iff' j]
  have : ∑ i ∈ range j, (if i < j then (0 : ℝ) else 1 / ((i - j).factorial : ℝ)) = 0 :=
    Finset.sum_eq_zero (fun i hi => if_pos (Finset.mem_range.mp hi))
  rw [this, sub_zero]
  exact hasSum_of_eq hasSum_inv_fact (fun k => by rw [if_neg (by omega), Nat.add_sub_cancel]) rfl

/-- **`E[H] = e − 1`.** -/
theorem hasSum_H_mean : HasSum (fun m : ℕ => (m : ℝ) * Hpmf m) (Real.exp 1 - 1) := by
  refine hasSum_of_eq ((hasSum_shift_inv_fact 1).sub hasSum_Hpmf) (fun m => ?_) rfl
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [Hpmf]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [if_neg (by omega), Nat.add_sub_cancel]
    simp only [Hpmf]
    rw [fact_succ_r, fact_succ_r]
    have := fact_pos_r k
    push_cast
    field_simp
    ring

/-- **`E[H²] = e + 1`**, so `Var[H] = 3e − e²`. -/
theorem hasSum_H_sq : HasSum (fun m : ℕ => (m : ℝ) ^ 2 * Hpmf m) (Real.exp 1 + 1) := by
  refine hasSum_of_eq ((hasSum_shift_inv_fact 2).add hasSum_Hpmf) (fun m => ?_) rfl
  rcases (show m = 0 ∨ m = 1 ∨ 2 ≤ m by omega) with rfl | rfl | hm
  · simp [Hpmf]
  · simp [Hpmf, Nat.factorial]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    rw [if_neg (by omega), Nat.add_sub_cancel]
    simp only [Hpmf]
    rw [fact_succ_r, fact_succ_r, fact_succ_r]
    have := fact_pos_r k
    push_cast
    field_simp
    ring

theorem H_var : (Real.exp 1 + 1) - (Real.exp 1 - 1) ^ 2 = 3 * Real.exp 1 - Real.exp 1 ^ 2 := by ring

/-- **The generating function `E[z^H] = (1 + (z−1)e^z)/z`** (`z ≠ 0`). -/
theorem hasSum_H_pgf (z : ℝ) (hz : z ≠ 0) :
    HasSum (fun m : ℕ => Hpmf m * z ^ m) ((1 + (z - 1) * Real.exp z) / z) := by
  have h1 := hasSum_pow_div_fact z
  have h2 : HasSum (fun m : ℕ => z ^ (m + 1) / ((m + 1).factorial : ℝ)) (Real.exp z - 1) := by
    have := (hasSum_nat_add_iff' 1).mpr h1
    simpa using this
  refine hasSum_of_eq (h1.sub (h2.div_const z)) (fun m => ?_) ?_
  · rw [Hpmf_eq, pow_succ]
    field_simp
  · field_simp
    ring

/-! ## 5. Limits of `E_n`, `F_n` and of the moments -/

lemma Ee_cast (n : ℕ) : (Ee n : ℝ) = ∑ m ∈ range n, 1 / ((m + 1).factorial : ℝ) := by
  rw [Ee]; push_cast; rfl

lemma Fe_cast (n : ℕ) : (Fe n : ℝ) = ∑ m ∈ range n, (2 * m + 1) / ((m + 1).factorial : ℝ) := by
  rw [Fe]; push_cast; rfl

lemma hasSum_inv_fact_succ :
    HasSum (fun m : ℕ => 1 / ((m + 1).factorial : ℝ)) (Real.exp 1 - 1) := by
  have := (hasSum_nat_add_iff' 1).mpr hasSum_inv_fact
  simpa using this

/-- **`E_n → e − 1`.** -/
theorem tendsto_Ee : Tendsto (fun n => (Ee n : ℝ)) atTop (𝓝 (Real.exp 1 - 1)) := by
  simp_rw [Ee_cast]; exact hasSum_inv_fact_succ.tendsto_sum_nat

/-- **`F_n → e + 1`.** -/
theorem tendsto_Fe : Tendsto (fun n => (Fe n : ℝ)) atTop (𝓝 (Real.exp 1 + 1)) := by
  simp_rw [Fe_cast]
  have := hasSum_of_eq (g := fun m : ℕ => (2 * (m : ℝ) + 1) / ((m + 1).factorial : ℝ))
    ((hasSum_inv_fact.mul_left 2).sub hasSum_inv_fact_succ) (fun m => by
    rw [fact_succ_r]
    have := fact_pos_r m
    field_simp
    try ring) (by ring : 2 * Real.exp 1 - (Real.exp 1 - 1) = Real.exp 1 + 1)
  exact this.tendsto_sum_nat

lemma tendsto_lin_div_fact (a b : ℝ) :
    Tendsto (fun n : ℕ => (a * n + b) / (n.factorial : ℝ)) atTop (𝓝 0) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have h : Tendsto (fun n : ℕ => a / (n.factorial : ℝ) + b / ((n + 1).factorial : ℝ))
      atTop (𝓝 (a * 0 + b * 0)) :=
    ((tendsto_inv_fact.const_mul a).add
      ((tendsto_inv_fact.comp (tendsto_add_atTop_nat 1)).const_mul b)).congr
      (fun n => by simp [Function.comp, div_eq_mul_inv])
  simp only [mul_zero, add_zero] at h
  refine h.congr (fun n => ?_)
  rw [fact_succ_r]
  have := fact_pos_r n
  push_cast
  field_simp
  try ring

/-- **`Var[h] → 3e − e²`.** -/
theorem bst_Varh_tendsto :
    Tendsto (fun n => ((bstE n (fun t => (rlen t : ℚ) ^ 2)
      - bstE n (fun t => (rlen t : ℚ)) ^ 2 : ℚ) : ℝ)) atTop
      (𝓝 (3 * Real.exp 1 - Real.exp 1 ^ 2)) := by
  simp_rw [bst_Varh]; push_cast
  convert tendsto_Fe.sub (tendsto_Ee.pow 2) using 2; ring

/-- **`Cov(h, L) → 2 − 5e/6`.** -/
theorem bst_CovhL_tendsto :
    Tendsto (fun n => ((bstE n (fun t => (rlen t : ℚ) * leaves t)
      - bstE n (fun t => (rlen t : ℚ)) * bstE n (fun t => (leaves t : ℚ)) : ℚ) : ℝ)) atTop
      (𝓝 (2 - 5 * Real.exp 1 / 6)) := by
  have hlim := ((tendsto_const_nhds (x := (7 / 6 : ℝ))).sub (tendsto_Ee.const_mul (5 / 6))).sub
    ((tendsto_lin_div_fact (1 / 6) (-1 / 2)))
  refine (hlim.congr' ?_).trans (by rw [show (7 / 6 : ℝ) - 5 / 6 * (Real.exp 1 - 1) - 0
    = 2 - 5 * Real.exp 1 / 6 by ring])
  filter_upwards [eventually_ge_atTop 2] with n hn
  have := bst_CovhL n hn
  rw [bstEhL, bst_Eh, bstEL] at *
  rw [show bstE n (fun t => (rlen t : ℚ) * leaves t) - Ee n * bstE n (fun t => (leaves t : ℚ))
    = _ from this]
  have := fact_pos_r n
  push_cast
  field_simp
  ring

/-- **`Var[A_N] − 2n/45 → 2/45 + 14e/3 − e² − 4`.** -/
theorem bst_VarAN_tendsto :
    Tendsto (fun n : ℕ => ((bstE n (fun t => (cmpsN (ip t) : ℚ) ^ 2)
      - bstE n (fun t => (cmpsN (ip t) : ℚ)) ^ 2 : ℚ) : ℝ) - 2 * n / 45) atTop
      (𝓝 (2 / 45 + 14 * Real.exp 1 / 3 - Real.exp 1 ^ 2 - 4)) := by
  have hlim := ((((tendsto_const_nhds (x := (2 / 45 : ℝ))).add tendsto_Fe).sub
    (tendsto_Ee.pow 2)).sub (tendsto_const_nhds (x := (7 / 3 : ℝ)))).add
    ((tendsto_Ee.const_mul (5 / 3)).add (tendsto_lin_div_fact (1 / 3) (-1)))
  refine (hlim.congr' ?_).trans (by ring_nf; rfl)
  filter_upwards [eventually_ge_atTop 4] with n hn
  rw [bst_VarAN n hn]
  have := fact_pos_r n
  push_cast
  field_simp
  ring

/-- **`Cov[A_M, A_N] → 23e/6 − e² − 2`.** -/
theorem bst_CovAMAN_tendsto :
    Tendsto (fun n : ℕ => ((bstE n (fun t => (cmpsM (ip t) : ℚ) * cmpsN (ip t))
        - bstE n (fun t => (cmpsM (ip t) : ℚ)) * bstE n (fun t => (cmpsN (ip t) : ℚ)) : ℚ) : ℝ))
      atTop (𝓝 (23 * Real.exp 1 / 6 - Real.exp 1 ^ 2 - 2)) := by
  have hlim := (((tendsto_Fe.sub (tendsto_Ee.pow 2)).sub
    (tendsto_const_nhds (x := (7 / 6 : ℝ)))).add
    ((tendsto_Ee.const_mul (5 / 6)).add (tendsto_lin_div_fact (1 / 6) (-1 / 2))))
  refine (hlim.congr' ?_).trans (by ring_nf; rfl)
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [bst_CovAMAN n hn]
  have := fact_pos_r n
  push_cast
  field_simp
  ring

/-! ## 6. The tail `ε_n = e − 1 − E_n` and explicit error terms -/

/-- `ε_n = e − 1 − E_n = Σ_{m>n} 1/m!`. -/
noncomputable def epsE (n : ℕ) : ℝ := Real.exp 1 - 1 - Ee n

lemma hasSum_epsE (n : ℕ) :
    HasSum (fun k => 1 / ((k + (n + 1)).factorial : ℝ)) (epsE n) := by
  refine hasSum_of_eq ((hasSum_nat_add_iff' (n + 1)).mpr hasSum_inv_fact) (fun k => rfl) ?_
  rw [epsE, Ee_cast, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, div_one]
  ring

lemma epsE_nonneg (n : ℕ) : 0 ≤ epsE n :=
  (hasSum_epsE n).nonneg (fun k => by have := fact_pos_r (k + (n + 1)); positivity)

lemma epsE_le (n : ℕ) : epsE n ≤ 2 / ((n + 1).factorial : ℝ) := by
  have hg := (hasSum_geometric_two).mul_left (1 / ((n + 1).factorial : ℝ))
  have h := hasSum_le (fun k => ?_) (hasSum_epsE n) hg
  · calc epsE n ≤ 1 / ((n + 1).factorial : ℝ) * 2 := h
      _ = 2 / ((n + 1).factorial : ℝ) := by ring
  · have hnat : (n + 1).factorial * 2 ^ k ≤ (k + (n + 1)).factorial := by
      calc (n + 1).factorial * 2 ^ k ≤ (n + 1).factorial * (n + 1 + 1) ^ k :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) k)
        _ ≤ (n + 1 + k).factorial := Nat.factorial_mul_pow_le_factorial
        _ = (k + (n + 1)).factorial := by rw [add_comm]
    have hr : ((n + 1).factorial : ℝ) * 2 ^ k ≤ ((k + (n + 1)).factorial : ℝ) := by
      exact_mod_cast hnat
    have := fact_pos_r (n + 1)
    calc 1 / ((k + (n + 1)).factorial : ℝ) ≤ 1 / (((n + 1).factorial : ℝ) * 2 ^ k) :=
          one_div_le_one_div_of_le (by positivity) hr
      _ = 1 / ((n + 1).factorial : ℝ) * (1 / 2) ^ k := by rw [one_div_pow]; field_simp

lemma exp_one_bounds : 2.7182818283 < Real.exp 1 ∧ Real.exp 1 < 2.7182818286 :=
  ⟨Real.exp_one_gt_d9, Real.exp_one_lt_d9⟩

/-- **`E[A_M] = 3n − e + O(1/n!)`**, with the explicit bound `|E[A_M] − (3n − e)| ≤ 1/n!`. -/
theorem bst_EAM_err (n : ℕ) (hn : 1 ≤ n) :
    |((bstE n (fun t => (cmpsM (ip t) : ℚ)) : ℚ) : ℝ) - (3 * n - Real.exp 1)|
      ≤ 1 / (n.factorial : ℝ) := by
  rw [bst_EAM n hn]
  push_cast
  have h1 := epsE_nonneg n
  have h2 := epsE_le n
  rw [epsE] at h1 h2
  rw [fact_succ_r] at h2
  have := fact_pos_r n
  have h3 : 2 / (((n : ℝ) + 1) * n.factorial) ≤ 1 / (n.factorial : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  rw [abs_le]; constructor <;> linarith

lemma Fe_eq (n : ℕ) : (Fe n : ℝ) = 2 + Ee n - 2 / (n.factorial : ℝ) := by
  induction n with
  | zero => simp [Fe, Ee]
  | succ n ih =>
    rw [Fe_succ, Ee_succ]
    push_cast
    rw [ih, fact_succ_r]
    have := fact_pos_r n
    field_simp
    ring

/-- The limiting constant of `Var[A_N] − 2n/45`. -/
noncomputable def cVarAN : ℝ := 2 / 45 + 14 * Real.exp 1 / 3 - Real.exp 1 ^ 2 - 4

/-- **The error of `Var[A_N]` in closed form**:
    `Var[A_N] − 2n/45 − c = (n−9)/(3·n!) + (2e − 14/3) ε_n − ε_n²` (`n ≥ 4`). -/
theorem bst_VarAN_err_eq (n : ℕ) (hn : 4 ≤ n) :
    ((bstE n (fun t => (cmpsN (ip t) : ℚ) ^ 2) - bstE n (fun t => (cmpsN (ip t) : ℚ)) ^ 2 : ℚ)
        : ℝ) - 2 * n / 45 - cVarAN
      = ((n : ℝ) - 9) / (3 * n.factorial) + (2 * Real.exp 1 - 14 / 3) * epsE n - epsE n ^ 2 := by
  rw [bst_VarAN n hn]
  push_cast
  rw [Fe_eq, cVarAN, epsE]
  have := fact_pos_r n
  field_simp
  ring

/-- **`Var[A_N] = 2n/45 + c + O(1/(n−1)!)`**: the error is at most `1/(n−1)!` (`n ≥ 4`). -/
theorem bst_VarAN_err_le (n : ℕ) (hn : 4 ≤ n) :
    |((bstE n (fun t => (cmpsN (ip t) : ℚ) ^ 2) - bstE n (fun t => (cmpsN (ip t) : ℚ)) ^ 2 : ℚ)
        : ℝ) - 2 * n / 45 - cVarAN| ≤ 1 / ((n - 1).factorial : ℝ) := by
  rw [bst_VarAN_err_eq n hn]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hε0 := epsE_nonneg (m + 1)
  have hε1 := epsE_le (m + 1)
  rw [fact_succ_r, fact_succ_r] at hε1
  rw [fact_succ_r]
  have hF := fact_pos_r m
  have hF1 : (1 : ℝ) ≤ (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hm : (3 : ℝ) ≤ m := by exact_mod_cast (show 3 ≤ m by omega)
  have he := exp_one_bounds
  set F := (m.factorial : ℝ)
  set ε := epsE (m + 1)
  -- `2/((m+3)(m+2)F) ≤ 1/(10F)` and `|m−8|/(3(m+1)F) ≤ 5/(12F)`
  have h20 : (20 : ℝ) ≤ ((m : ℝ) + 1 + 1) * ((m : ℝ) + 1) := by nlinarith
  have hεF : ε ≤ 1 / (10 * F) := by
    refine hε1.trans ?_
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right h20 hF.le]
  have hε1' : ε ≤ 1 := hεF.trans (by rw [div_le_one (by positivity)]; linarith)
  have hfirst : |((m : ℝ) + 1 - 9) / (3 * ((m + 1) * F))| ≤ 5 / (12 * F) := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 3 * ((m + 1) * F)),
      div_le_div_iff₀ (by positivity) (by positivity)]
    rcases le_total ((m : ℝ) + 1 - 9) 0 with h | h
    · rw [abs_of_nonpos h]; nlinarith
    · rw [abs_of_nonneg h]; nlinarith
  have hcoef : |2 * Real.exp 1 - 14 / 3| ≤ 1 := by rw [abs_le]; constructor <;> linarith [he.1, he.2]
  have hmid : |(2 * Real.exp 1 - 14 / 3) * ε| ≤ ε := by
    rw [abs_mul, abs_of_nonneg hε0]; nlinarith [abs_nonneg (2 * Real.exp 1 - 14 / 3)]
  have hsq : ε ^ 2 ≤ ε := by nlinarith
  have hsum : 5 / (12 * F) + 2 * (1 / (10 * F)) ≤ 1 / F := by
    rw [show 5 / (12 * F) + 2 * (1 / (10 * F)) = (37 / 60) * (1 / F) by field_simp; ring]
    have : 0 < 1 / F := by positivity
    linarith
  push_cast
  calc |((m : ℝ) + 1 - 9) / (3 * ((m + 1) * F)) + (2 * Real.exp 1 - 14 / 3) * ε - ε ^ 2|
      ≤ |((m : ℝ) + 1 - 9) / (3 * ((m + 1) * F))| + |(2 * Real.exp 1 - 14 / 3) * ε| + ε ^ 2 := by
        refine (abs_sub _ _).trans ?_
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 2)]
        gcongr
        exact abs_add_le _ _
    _ ≤ 5 / (12 * F) + 2 * (1 / (10 * F)) := by linarith
    _ ≤ 1 / F := hsum

/-- **At `n = 10` the variance agrees with its limit to six decimals**: the error is
    below `2·10⁻⁷`. -/
theorem bst_VarAN_n10 :
    |((bstE 10 (fun t => (cmpsN (ip t) : ℚ) ^ 2) - bstE 10 (fun t => (cmpsN (ip t) : ℚ)) ^ 2 : ℚ)
        : ℝ) - 2 * (10 : ℕ) / 45 - cVarAN| < 2 / 10 ^ 7 := by
  rw [bst_VarAN_err_eq 10 (by norm_num)]
  have hε0 := epsE_nonneg 10
  have hε1 := epsE_le 10
  have he := exp_one_bounds
  set ε := epsE 10
  have hf : ((Nat.factorial 11 : ℕ) : ℝ) = 39916800 := by norm_num [Nat.factorial]
  have hf10 : ((Nat.factorial 10 : ℕ) : ℝ) = 3628800 := by norm_num [Nat.factorial]
  rw [show (10 + 1 : ℕ) = 11 from rfl, hf] at hε1
  rw [hf10]
  have hcoef : |2 * Real.exp 1 - 14 / 3| ≤ 1 := by rw [abs_le]; constructor <;> linarith [he.1, he.2]
  have hmid : |(2 * Real.exp 1 - 14 / 3) * ε| ≤ ε := by
    rw [abs_mul, abs_of_nonneg hε0]; nlinarith [abs_nonneg (2 * Real.exp 1 - 14 / 3)]
  have hsq : ε ^ 2 ≤ ε := by nlinarith
  calc |(((10 : ℕ) : ℝ) - 9) / (3 * 3628800) + (2 * Real.exp 1 - 14 / 3) * ε - ε ^ 2|
      ≤ |(((10 : ℕ) : ℝ) - 9) / (3 * 3628800)| + |(2 * Real.exp 1 - 14 / 3) * ε| + ε ^ 2 := by
        refine (abs_sub _ _).trans ?_
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 2)]
        gcongr
        exact abs_add_le _ _
    _ < 2 / 10 ^ 7 := by
        rw [show |(((10 : ℕ) : ℝ) - 9) / (3 * 3628800)| = 1 / 10886400 by norm_num [abs_of_pos]]
        linarith

/-! ## 7. Limits of the means -/

/-- **`E[A_M] − (3n − 4) → 4 − e`**: `M` makes `4 − e ≈ 1.28` more comparisons on average
    than the uniform model's `3n − 4`. -/
theorem bst_EAM_sub_tendsto :
    Tendsto (fun n : ℕ => ((bstE n (fun t => (cmpsM (ip t) : ℚ)) : ℚ) : ℝ) - (3 * n - 4)) atTop
      (𝓝 (4 - Real.exp 1)) := by
  have h := (tendsto_const_nhds (x := (3 : ℝ))).sub tendsto_Ee
  refine (h.congr' ?_).trans (by rw [show (3 : ℝ) - (Real.exp 1 - 1) = 4 - Real.exp 1 by ring])
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [bst_EAM n hn]; push_cast; ring

/-- **The mean reduction ratio `1 − E[A_N]/E[A_M] → 2/9`.** -/
theorem bst_ratio_tendsto :
    Tendsto (fun n : ℕ => 1 - ((bstE n (fun t => (cmpsN (ip t) : ℚ)) : ℚ) : ℝ)
      / ((bstE n (fun t => (cmpsM (ip t) : ℚ)) : ℚ) : ℝ)) atTop (𝓝 (2 / 9)) := by
  have ha : Tendsto (fun n : ℕ => (4 / 3 - (Ee n : ℝ)) / n) atTop (𝓝 0) :=
    ((tendsto_const_nhds).sub tendsto_Ee).div_atTop tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun n : ℕ => (-1 - (Ee n : ℝ)) / n) atTop (𝓝 0) :=
    ((tendsto_const_nhds).sub tendsto_Ee).div_atTop tendsto_natCast_atTop_atTop
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (((tendsto_const_nhds (x := (7 / 3 : ℝ))).add ha).div
      ((tendsto_const_nhds (x := (3 : ℝ))).add hb) (by norm_num))
  refine (h.congr' ?_).trans (by norm_num)
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [bst_EAN n hn, bst_EAM n (by omega)]
  push_cast
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  simp only [Pi.div_apply]
  field_simp
  ring

/-- **`E[A_N] < E[A_M]` exactly when `n ≥ 4`** (`n ≥ 2`). -/
theorem bst_EAN_lt_EAM_iff (n : ℕ) (hn : 2 ≤ n) :
    bstE n (fun t => (cmpsN (ip t) : ℚ)) < bstE n (fun t => (cmpsM (ip t) : ℚ)) ↔ 4 ≤ n := by
  rw [bst_EAN n hn, bst_EAM n (by omega)]
  constructor
  · intro h
    by_contra h'
    have : (n : ℚ) ≤ 3 := by exact_mod_cast (show n ≤ 3 by omega)
    linarith
  · intro h
    have : (4 : ℚ) ≤ n := by exact_mod_cast h
    linarith

/-! ## 8. The gap `D = A_M − A_N` -/

lemma one_le_leaves : ∀ t : T, t ≠ .nil → 1 ≤ leaves t
  | .nil, h => absurd rfl h
  | .node v l r, _ => by
    have h := leaves_node v l r
    have hq : (1 : ℚ) ≤ leaves (.node v l r) := by
      rw [h]
      by_cases hl : l = .nil
      · by_cases hr : r = .nil
        · subst hl hr; simp [BinaryTree.numNodes]
        · have := one_le_leaves r hr
          have : (1 : ℚ) ≤ leaves r := by exact_mod_cast this
          split_ifs <;> linarith [(Nat.cast_nonneg (leaves l) : (0 : ℚ) ≤ _)]
      · have := one_le_leaves l hl
        have : (1 : ℚ) ≤ leaves l := by exact_mod_cast this
        split_ifs <;> linarith [(Nat.cast_nonneg (leaves r) : (0 : ℚ) ≤ _)]
    exact_mod_cast hq

/-- The per-tree counting facts used below. -/
lemma gap_facts (t : T) (h : t ≠ .nil) :
    cmpsM (ip t) + rlen t + 1 = 3 * t.numNodes ∧
      cmpsN (ip t) + rlen t = 2 * t.numNodes + 1 + leaves t ∧
      1 ≤ leaves t ∧ 2 * leaves t ≤ t.numNodes + 1 := by
  have hM := central_M_exec t h
  have hN := central_N_exec t h
  rw [finalH_toPop_eq_rlen t h] at hM hN
  exact ⟨hM, hN, one_le_leaves t h, two_leaves_le t h⟩

/-- **`D = n − 2 − L`** on every non-empty tree: `h` cancels. -/
theorem D_eq (t : T) (h : t ≠ .nil) :
    (cmpsM (ip t) : ℚ) - cmpsN (ip t) = t.numNodes - 2 - leaves t := by
  rw [cmpsM_q t h, cmpsN_q t h]; ring

/-- **`E[D] = (2n − 7)/3`** (`n ≥ 2`). -/
theorem bst_ED (n : ℕ) (hn : 2 ≤ n) :
    bstE n (fun t => (cmpsM (ip t) : ℚ) - cmpsN (ip t)) = (2 * n - 7) / 3 := by
  rw [bstE_congr (g := fun t => ((n : ℚ) - 2) - leaves t) (fun t ht => by
    rw [D_eq t (ne_nil_of_numNodes (by omega) ht), ht]), bstE_sub, bstE_const]
  have := bst_EL n
  rw [bstEL] at this
  rw [this, show n = (n - 2) + 2 by omega, eC_add_two]
  push_cast [show 2 ≤ n by omega]
  ring

/-- **`Var[D] = 2(n+1)/45`** (`n ≥ 4`): `D` is `n − 2 − L`, so its variance is `Var[L]`. -/
theorem bst_VarD (n : ℕ) (hn : 4 ≤ n) :
    bstE n (fun t => ((cmpsM (ip t) : ℚ) - cmpsN (ip t)) ^ 2)
      - bstE n (fun t => (cmpsM (ip t) : ℚ) - cmpsN (ip t)) ^ 2 = 2 * ((n : ℚ) + 1) / 45 := by
  have hD : ∀ t : T, t.numNodes = n → (cmpsM (ip t) : ℚ) - cmpsN (ip t) = (n - 2) - leaves t :=
    fun t ht => by rw [D_eq t (ne_nil_of_numNodes (by omega) ht), ht]
  rw [bstE_congr (g := fun t => (((n : ℚ) - 2) ^ 2 - 2 * ((n : ℚ) - 2) * leaves t)
      + (leaves t : ℚ) ^ 2) (fun t ht => by rw [hD t ht]; ring),
    bstE_congr (g := fun t => ((n : ℚ) - 2) - leaves t) hD,
    bstE_add, bstE_sub, bstE_const, bstE_smul, bstE_sub, bstE_const]
  have h1 := bst_VarL n hn
  rw [bstEL, bstEL2] at h1
  linear_combination h1

/-- **`P(A_M = 3n − 2) = 1/2`** (`n ≥ 2`): the worst case is attained with probability one half. -/
theorem bst_PAM_max (n : ℕ) (hn : 2 ≤ n) :
    bstE n (fun t => if cmpsM (ip t) = 3 * n - 2 then 1 else 0) = 1 / 2 := by
  have key : bstE n (fun t => if cmpsM (ip t) = 3 * n - 2 then 1 else 0)
      = bstE n (fun t => if 3 * n - 2 - 0 ≤ cmpsM (ip t) then 1 else 0) := by
    refine bstE_congr (fun t ht => ?_)
    obtain ⟨hM, _, _, _⟩ := gap_facts t (ne_nil_of_numNodes (by omega) ht)
    have hp := rlen_pos (ne_nil_of_numNodes (show 1 ≤ n by omega) ht)
    rw [ht] at hM
    by_cases h : cmpsM (ip t) = 3 * n - 2
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]
  rw [key, bst_PAM_ge n 0 (by omega)]
  norm_num [Nat.factorial]

/-! ### Who wins at `n = 3, 4, 5`

`N` wins when `A_N < A_M` (`D > 0`), ties when `A_N = A_M`, loses when `A_N > A_M`.
Since `D = n − 2 − L` and `1 ≤ L ≤ ⌈n/2⌉`, each event is a polynomial of degree at most
two in `L` on the `n`-node trees, so its probability follows from `E[L]` and `E[L²]`. -/

lemma bstE_quad_of (n : ℕ) (a b c : ℚ) (f : T → ℚ)
    (hf : ∀ t, t.numNodes = n → f t = a + b * leaves t + c * (leaves t : ℚ) ^ 2) :
    bstE n f = a + b * eC n + c * sC n := by
  rw [bstE_congr hf, bstE_add, bstE_add, bstE_const, bstE_smul, bstE_smul]
  have h1 := bst_EL n
  have h2 := bst_EL2 n
  rw [bstEL] at h1
  rw [bstEL2] at h2
  rw [h1, h2]

lemma eC_three : eC 3 = 4 / 3 := by rw [show (3 : ℕ) = 1 + 2 from rfl, eC_add_two]; norm_num
lemma eC_four : eC 4 = 5 / 3 := by rw [show (4 : ℕ) = 2 + 2 from rfl, eC_add_two]; norm_num
lemma eC_five : eC 5 = 2 := by rw [show (5 : ℕ) = 3 + 2 from rfl, eC_add_two]; norm_num
lemma sC_five : sC 5 = 64 / 15 := by rw [show (5 : ℕ) = 1 + 4 from rfl, sC_add_four]; norm_num

/-- The three outcome indicators. -/
def winN (t : T) : ℚ := if cmpsN (ip t) < cmpsM (ip t) then 1 else 0
def tieN (t : T) : ℚ := if cmpsN (ip t) = cmpsM (ip t) then 1 else 0
def loseN (t : T) : ℚ := if cmpsM (ip t) < cmpsN (ip t) then 1 else 0

/-- **`n = 3`: `(P(win), P(tie), P(lose)) = (0, 2/3, 1/3)`.** -/
theorem bst_outcome_three :
    bstE 3 winN = 0 ∧ bstE 3 tieN = 2 / 3 ∧ bstE 3 loseN = 1 / 3 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [bstE_quad_of 3 0 0 0 winN (fun t ht => ?_)]; · norm_num
    obtain ⟨hM, hN, h1, h2⟩ := gap_facts t (ne_nil_of_numNodes (by omega) ht)
    rw [ht] at hM hN h2
    rw [winN, if_neg (by omega)]; ring
  · rw [bstE_quad_of 3 2 (-1) 0 tieN (fun t ht => ?_), eC_three]; · norm_num
    obtain ⟨hM, hN, h1, h2⟩ := gap_facts t (ne_nil_of_numNodes (by omega) ht)
    rw [ht] at hM hN h2
    rcases (show leaves t = 1 ∨ leaves t = 2 by omega) with h | h <;> rw [tieN, h] <;>
      split_ifs <;> first | (exfalso; omega) | norm_num
  · rw [bstE_quad_of 3 (-1) 1 0 loseN (fun t ht => ?_), eC_three]; · norm_num
    obtain ⟨hM, hN, h1, h2⟩ := gap_facts t (ne_nil_of_numNodes (by omega) ht)
    rw [ht] at hM hN h2
    rcases (show leaves t = 1 ∨ leaves t = 2 by omega) with h | h <;> rw [loseN, h] <;>
      split_ifs <;> first | (exfalso; omega) | norm_num

/-- **`n = 4`: `(1/3, 2/3, 0)`.** -/
theorem bst_outcome_four :
    bstE 4 winN = 1 / 3 ∧ bstE 4 tieN = 2 / 3 ∧ bstE 4 loseN = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [bstE_quad_of 4 2 (-1) 0 winN (fun t ht => ?_), eC_four]; · norm_num
    obtain ⟨hM, hN, h1, h2⟩ := gap_facts t (ne_nil_of_numNodes (by omega) ht)
    rw [ht] at hM hN h2
    rcases (show leaves t = 1 ∨ leaves t = 2 by omega) with h | h <;> rw [winN, h] <;>
      split_ifs <;> first | (exfalso; omega) | norm_num
  · rw [bstE_quad_of 4 (-1) 1 0 tieN (fun t ht => ?_), eC_four]; · norm_num
    obtain ⟨hM, hN, h1, h2⟩ := gap_facts t (ne_nil_of_numNodes (by omega) ht)
    rw [ht] at hM hN h2
    rcases (show leaves t = 1 ∨ leaves t = 2 by omega) with h | h <;> rw [tieN, h] <;>
      split_ifs <;> first | (exfalso; omega) | norm_num
  · rw [bstE_quad_of 4 0 0 0 loseN (fun t ht => ?_)]; · norm_num
    obtain ⟨hM, hN, h1, h2⟩ := gap_facts t (ne_nil_of_numNodes (by omega) ht)
    rw [ht] at hM hN h2
    rw [loseN, if_neg (by omega)]; ring

/-- **`n = 5`: `(13/15, 2/15, 0)`.** -/
theorem bst_outcome_five :
    bstE 5 winN = 13 / 15 ∧ bstE 5 tieN = 2 / 15 ∧ bstE 5 loseN = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [bstE_quad_of 5 0 (3 / 2) (-1 / 2) winN (fun t ht => ?_), eC_five, sC_five]; · norm_num
    obtain ⟨hM, hN, h1, h2⟩ := gap_facts t (ne_nil_of_numNodes (by omega) ht)
    rw [ht] at hM hN h2
    rcases (show leaves t = 1 ∨ leaves t = 2 ∨ leaves t = 3 by omega) with h | h | h <;>
      rw [winN, h] <;> split_ifs <;> first | (exfalso; omega) | norm_num
  · rw [bstE_quad_of 5 1 (-3 / 2) (1 / 2) tieN (fun t ht => ?_), eC_five, sC_five]; · norm_num
    obtain ⟨hM, hN, h1, h2⟩ := gap_facts t (ne_nil_of_numNodes (by omega) ht)
    rw [ht] at hM hN h2
    rcases (show leaves t = 1 ∨ leaves t = 2 ∨ leaves t = 3 by omega) with h | h | h <;>
      rw [tieN, h] <;> split_ifs <;> first | (exfalso; omega) | norm_num
  · rw [bstE_quad_of 5 0 0 0 loseN (fun t ht => ?_)]; · norm_num
    obtain ⟨hM, hN, h1, h2⟩ := gap_facts t (ne_nil_of_numNodes (by omega) ht)
    rw [ht] at hM hN h2
    rw [loseN, if_neg (by omega)]; ring

end MakinenAnalysis
