/-
Gaussian-sum asymptotics: a standalone analytic brick for a local limit theorem.

Main result:
  `gaussian_sum_div_sqrt_tendsto`:
    (∑ s ∈ range n, exp (-8 s² / n)) / √n  →  √(π/32)  as n → ∞.

Route: monotone bracketing of the sum by ∫₀ⁿ exp (-8x²/n) dx (the summand is
antitone on [0, ∞)), evaluation of the half-line Gaussian integral
∫_{0}^{∞} exp (-(8/n) x²) dx = √n · √(π/32) via `integral_gaussian_Ioi`, and a
tail estimate ∫_{n}^{∞} ≤ e^{-n} ≤ 1.  Both correction terms are O(1), hence
vanish after division by √n; conclude by the squeeze theorem.
-/
import Mathlib

open Filter Set MeasureTheory

namespace MakinenAnalysis

/-- The Gaussian integrand `x ↦ exp (-(8/n) · x²)`. -/
private noncomputable def G (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-(8 / (n : ℝ)) * x ^ 2)

private lemma G_nonneg (n : ℕ) (x : ℝ) : 0 ≤ G n x :=
  (Real.exp_pos _).le

/-- The summand of the target theorem coincides with `G n`. -/
private lemma sum_eq (n : ℕ) :
    (∑ s ∈ Finset.range n, Real.exp (-8 * (s : ℝ)^2 / n))
      = ∑ s ∈ Finset.range n, G n (s : ℝ) := by
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [G]
  congr 1
  ring

/-- `G n` is antitone on `[0, n]` (stated in the shape needed by
`AntitoneOn.integral_le_sum` / `AntitoneOn.sum_le_integral`). -/
private lemma G_antitoneOn (n : ℕ) :
    AntitoneOn (G n) (Icc (0 : ℝ) (0 + (n : ℝ))) := by
  intro a ha b hb hab
  simp only [G]
  apply Real.exp_le_exp.2
  rw [neg_mul, neg_mul, neg_le_neg_iff]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) (Nat.cast_nonneg n))
  nlinarith [mul_nonneg (sub_nonneg.2 hab) (add_nonneg ha.1 (ha.1.trans hab))]

/-- `G n` is integrable on the whole line. -/
private lemma G_integrable {n : ℕ} (hn : 1 ≤ n) : Integrable (G n) := by
  have hN0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  exact integrable_exp_neg_mul_sq (div_pos (by norm_num) hN0)

/-- Half-line Gaussian integral: `∫_{0}^{∞} G n = √n · √(π/32)`. -/
private lemma integral_Ioi_G {n : ℕ} (hn : 1 ≤ n) :
    ∫ x in Ioi (0 : ℝ), G n x = Real.sqrt n * Real.sqrt (Real.pi / 32) := by
  have hN0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  simp only [G]
  rw [integral_gaussian_Ioi]
  have hπ : Real.pi / (8 / (n : ℝ)) = (n : ℝ) * (Real.pi / 8) := by
    rw [div_div_eq_mul_div]
    ring
  have h2 : Real.sqrt (Real.pi / 8) = Real.sqrt (Real.pi / 32) * 2 := by
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    rw [← h4, ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Real.pi / 32)]
    congr 1
    ring
  rw [hπ, Real.sqrt_mul (Nat.cast_nonneg n), h2]
  ring

/-- Tail estimate: `∫_{n}^{∞} G n ≤ 1` (indeed `≤ e^{-n}`). -/
private lemma tail_le_one {n : ℕ} (hn : 1 ≤ n) :
    ∫ x in Ioi (n : ℝ), G n x ≤ 1 := by
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have h1 : ∫ x in Ioi (n : ℝ), G n x ≤ ∫ x in Ioi (n : ℝ), Real.exp (-x) := by
    apply setIntegral_mono_on
    · exact (G_integrable hn).integrableOn
    · simpa using exp_neg_integrableOn_Ioi (n : ℝ) one_pos
    · exact measurableSet_Ioi
    · intro x hx
      have hx' : (n : ℝ) < x := mem_Ioi.mp hx
      have hx0 : (0 : ℝ) < x := hN0.trans hx'
      simp only [G]
      apply Real.exp_le_exp.2
      rw [neg_mul, neg_le_neg_iff, div_mul_eq_mul_div, le_div_iff₀ hN0]
      nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr hx'.le), sq_nonneg x]
  have h2 : ∫ x in Ioi (n : ℝ), Real.exp (-x) = Real.exp (-(n : ℝ)) :=
    integral_exp_neg_Ioi _
  have h3 : Real.exp (-(n : ℝ)) ≤ 1 := by
    calc Real.exp (-(n : ℝ)) ≤ Real.exp 0 := Real.exp_le_exp.2 (by linarith)
    _ = 1 := Real.exp_zero
  linarith

/-- Lower bound for the integral over `(0, n]`: at least the half-line value
minus the tail. -/
private lemma le_integral_Ioc {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt n * Real.sqrt (Real.pi / 32) - 1
      ≤ ∫ x in Ioc (0 : ℝ) (n : ℝ), G n x := by
  have hN0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hGint := G_integrable hn
  have hsplit : ∫ x in Ioc (0 : ℝ) (n : ℝ) ∪ Ioi (n : ℝ), G n x
      = (∫ x in Ioc (0 : ℝ) (n : ℝ), G n x) + ∫ x in Ioi (n : ℝ), G n x :=
    setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      hGint.integrableOn hGint.integrableOn
  rw [Set.Ioc_union_Ioi_eq_Ioi hN0.le] at hsplit
  have htail := tail_le_one hn
  have hval := integral_Ioi_G hn
  linarith

/-- Upper bound for the integral over `(0, n]`: at most the half-line value. -/
private lemma integral_Ioc_le {n : ℕ} (hn : 1 ≤ n) :
    ∫ x in Ioc (0 : ℝ) (n : ℝ), G n x
      ≤ Real.sqrt n * Real.sqrt (Real.pi / 32) := by
  rw [← integral_Ioi_G hn]
  exact setIntegral_mono_set (G_integrable hn).integrableOn
    (Filter.Eventually.of_forall fun x => G_nonneg n x)
    (HasSubset.Subset.eventuallyLE Set.Ioc_subset_Ioi_self)

/-- Lower bracketing: `√n·√(π/32) − 1 ≤ ∑_{s<n} G n s`. -/
private lemma le_sum_G {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt n * Real.sqrt (Real.pi / 32) - 1
      ≤ ∑ s ∈ Finset.range n, G n (s : ℝ) := by
  have hN0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h1 : ∫ x in (0 : ℝ)..(0 + (n : ℝ)), G n x
      ≤ ∑ i ∈ Finset.range n, G n (0 + (i : ℝ)) :=
    (G_antitoneOn n).integral_le_sum
  simp only [zero_add] at h1
  rw [intervalIntegral.integral_of_le hN0.le] at h1
  have h2 := le_integral_Ioc hn
  linarith

/-- Upper bracketing: `∑_{s<n} G n s ≤ √n·√(π/32) + 1`. -/
private lemma sum_G_le {n : ℕ} (hn : 1 ≤ n) :
    (∑ s ∈ Finset.range n, G n (s : ℝ))
      ≤ Real.sqrt n * Real.sqrt (Real.pi / 32) + 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  have hN0 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr hn
  -- shifted sum is below the integral
  have h1 : (∑ i ∈ Finset.range (m + 1), G (m + 1) (0 + ((i + 1 : ℕ) : ℝ)))
      ≤ ∫ x in (0 : ℝ)..(0 + ((m + 1 : ℕ) : ℝ)), G (m + 1) x :=
    (G_antitoneOn (m + 1)).sum_le_integral
  simp only [zero_add] at h1
  rw [intervalIntegral.integral_of_le hN0.le] at h1
  -- peel off the first term of the sum
  have h2 : (∑ s ∈ Finset.range (m + 1), G (m + 1) (s : ℝ))
      = (∑ i ∈ Finset.range m, G (m + 1) ((i + 1 : ℕ) : ℝ)) + G (m + 1) ((0 : ℕ) : ℝ) :=
    Finset.sum_range_succ' (fun s : ℕ => G (m + 1) (s : ℝ)) m
  have h3 : (∑ i ∈ Finset.range m, G (m + 1) ((i + 1 : ℕ) : ℝ))
      ≤ ∑ i ∈ Finset.range (m + 1), G (m + 1) ((i + 1 : ℕ) : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ m))
      fun i _ _ => G_nonneg _ _
  have h4 : G (m + 1) ((0 : ℕ) : ℝ) = 1 := by simp [G]
  have h5 := integral_Ioc_le hn
  linarith

/-- **Gaussian-sum asymptotics.**  The normalised Gaussian sum converges:
`(∑_{s<n} e^{-8s²/n}) / √n → √(π/32)`. -/
theorem gaussian_sum_div_sqrt_tendsto :
    Tendsto (fun n : ℕ => (∑ s ∈ Finset.range n, Real.exp (-8 * (s : ℝ)^2 / n)) / Real.sqrt n)
      atTop (nhds (Real.sqrt (Real.pi / 32))) := by
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hsq : Tendsto (fun n : ℕ => 1 / Real.sqrt n) atTop (nhds 0) := by
    simpa [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hsqrt
  have hlo : Tendsto (fun n : ℕ => Real.sqrt (Real.pi / 32) - 1 / Real.sqrt n) atTop
      (nhds (Real.sqrt (Real.pi / 32))) := by
    simpa using tendsto_const_nhds.sub hsq
  have hhi : Tendsto (fun n : ℕ => Real.sqrt (Real.pi / 32) + 1 / Real.sqrt n) atTop
      (nhds (Real.sqrt (Real.pi / 32))) := by
    simpa using tendsto_const_nhds.add hsq
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · -- lower bound, eventually
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hs : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
    rw [le_div_iff₀ hs, sum_eq n]
    have hkey := le_sum_G hn
    have hexp : (Real.sqrt (Real.pi / 32) - 1 / Real.sqrt n) * Real.sqrt n
        = Real.sqrt n * Real.sqrt (Real.pi / 32) - 1 := by
      rw [sub_mul, one_div, inv_mul_cancel₀ hs.ne']
      ring
    linarith
  · -- upper bound, eventually
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hs : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
    rw [div_le_iff₀ hs, sum_eq n]
    have hkey := sum_G_le hn
    have hexp : (Real.sqrt (Real.pi / 32) + 1 / Real.sqrt n) * Real.sqrt n
        = Real.sqrt n * Real.sqrt (Real.pi / 32) + 1 := by
      rw [add_mul, one_div, inv_mul_cancel₀ hs.ne']
      ring
    linarith

end MakinenAnalysis
