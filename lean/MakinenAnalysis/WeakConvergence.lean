import Mathlib
import MakinenAnalysis.FinalAssembly
import MakinenAnalysis.GapCLT

/-!
# From characteristic functions to convergence in distribution

`FinalAssembly` proves the central limit theorems at the level of
characteristic functions (`leafCLT_charFun`, `AN_CLT_charFun`) and `GapCLT`
the gap CLT (`gap_CLT_charFun`).  The paper states them as convergence *in
distribution* (`→d N(0,1)`); the two are equivalent by Lévy's continuity
theorem, which Mathlib provides as
`MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun`.

This file discharges that last step.  For each standardised statistic we build
its law as a finite empirical measure — a `catalan n`-weighted sum of Dirac
masses at the standardised values over the codeword space `suffixes (n-1) 1` —
show its Mathlib `charFun` equals our hand-rolled `charP2`/`charAN`/`charGap`,
and feed the proved charFun limit through Lévy continuity to obtain weak
convergence to `gaussianReal 0 1`.

* `leafCLT_tendsto` — **Proposition 12 as `→d N(0,1)`**;
* `AN_CLT_tendsto` — **Theorem 13 as `→d N(0,1)`**;
* `gap_CLT_tendsto` — **Corollary 14 as `→d N(0,1)`**.
-/

namespace MakinenAnalysis

open Finset MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology ENNReal NNReal

/-- The standardised double-pop value of a codeword: `(P₂ − E[P₂])·4/√n`. -/
noncomputable def stdP2 (n : ℕ) (w : List ℕ) : ℝ :=
  ((P2 w : ℝ) - EP2 n) * 4 / Real.sqrt n

/-- The standardised `A_N` value of a codeword: `(A_N − E[A_N])·4/√n`. -/
noncomputable def stdAN (n : ℕ) (w : List ℕ) : ℝ :=
  ((ANw n w : ℝ) - EAN n) * 4 / Real.sqrt n

/-- The standardised gap value of a codeword: `(gap − E[gap])·4/√n`,
    `gap = n − 3 − P₂`. -/
noncomputable def stdGap (n : ℕ) (w : List ℕ) : ℝ :=
  (((gapw n w : ℝ)) - Egap n) * 4 / Real.sqrt n

/-- Empirical law of a real statistic `f` over the codeword space, as a
    `catalan n`-normalised sum of Dirac masses. -/
noncomputable def empMeas (n : ℕ) (f : List ℕ → ℝ) : Measure ℝ :=
  (catalan n : ℝ≥0∞)⁻¹ • ∑ w ∈ suffixes (n - 1) 1, Measure.dirac (f w)

/-- The empirical law is a probability measure once `n ≥ 1` (total mass
    `#codewords / catalan n = 1`). -/
lemma empMeas_isProb (n : ℕ) (f : List ℕ → ℝ) (hn : 1 ≤ n) :
    IsProbabilityMeasure (empMeas n f) := by
  constructor
  rw [empMeas, Measure.smul_apply, Measure.finsetSum_apply]
  simp only [Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ, Pi.one_apply,
    Finset.sum_const, nsmul_eq_mul, mul_one, smul_eq_mul]
  rw [card_suffixes_eq_catalan n hn]
  have hcat : catalan n ≠ 0 := by
    have h := succ_mul_catalan_eq_centralBinom n
    intro h0
    rw [h0, mul_zero] at h
    exact (Nat.centralBinom_ne_zero n) h.symm
  have hc : (catalan n : ℝ≥0∞) ≠ 0 := by simpa using hcat
  rw [ENNReal.inv_mul_cancel hc (by simp)]

/-- **Transfer lemma**: Mathlib's `charFun` of the empirical law of `f` equals
    the hand-rolled average of `exp(I·t·f w)`. -/
lemma charFun_empMeas (n : ℕ) (f : List ℕ → ℝ) (t : ℝ) :
    charFun (empMeas n f) t
      = (∑ w ∈ suffixes (n - 1) 1, Complex.exp (Complex.I * Complex.ofReal (t * f w)))
          / (catalan n : ℂ) := by
  rw [charFun_apply_real, empMeas, integral_smul_measure,
    integral_finsetSum_measure (fun w _ => (integrable_dirac (enorm_lt_top)))]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, real_smul]
  rw [Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv, mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  rw [Complex.ofReal_mul]
  ring

/-- The standard Gaussian as a `ProbabilityMeasure`. -/
noncomputable def stdGaussianPM : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 1, inferInstance⟩

lemma charFun_stdGaussian (t : ℝ) :
    charFun (stdGaussianPM : Measure ℝ) t = Complex.exp (-(t : ℂ) ^ 2 / 2) := by
  have : (stdGaussianPM : Measure ℝ) = gaussianReal 0 1 := rfl
  rw [this, charFun_gaussianReal]
  congr 1
  push_cast
  ring

/-- Package the empirical law as a `ProbabilityMeasure`, total in `n`
    (`n = 0` is junk: the standard Gaussian). -/
noncomputable def empPM (n : ℕ) (f : List ℕ → ℝ) : ProbabilityMeasure ℝ :=
  if h : 1 ≤ n then ⟨empMeas n f, empMeas_isProb n f h⟩ else stdGaussianPM

lemma empPM_coe (n : ℕ) (f : List ℕ → ℝ) (hn : 1 ≤ n) :
    (empPM n f : Measure ℝ) = empMeas n f := by
  rw [empPM, dif_pos hn]; rfl

/-- Generic weak-convergence conclusion from a charFun limit that matches the
    empirical-law charFun. -/
private lemma tendsto_of_charFun_limit (f : ℕ → List ℕ → ℝ)
    (chr : ℕ → ℝ → ℂ)
    (hchr : ∀ n t, 1 ≤ n → chr n t
      = (∑ w ∈ suffixes (n - 1) 1,
          Complex.exp (Complex.I * Complex.ofReal (t * f n w))) / (catalan n : ℂ))
    (hlim : ∀ t : ℝ, Tendsto (fun n => chr n t) atTop (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2)))) :
    Tendsto (fun n => empPM n (f n)) atTop (𝓝 stdGaussianPM) := by
  refine ProbabilityMeasure.tendsto_of_tendsto_charFun (fun t => ?_)
  rw [charFun_stdGaussian]
  refine (hlim t).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [empPM_coe n (f n) hn, charFun_empMeas, ← hchr n t hn]

/-- **Proposition 12, convergence in distribution.**  The law of the
    standardised double-pop (leaf) count converges weakly to `N(0,1)`. -/
theorem leafCLT_tendsto :
    Tendsto (fun n => empPM n (stdP2 n)) atTop (𝓝 stdGaussianPM) :=
  tendsto_of_charFun_limit stdP2 charP2
    (fun n t _ => by rw [charP2]; rfl) leafCLT_charFun

/-- **Theorem 13, convergence in distribution.**  The law of the standardised
    comparison count of `N` converges weakly to `N(0,1)`. -/
theorem AN_CLT_tendsto :
    Tendsto (fun n => empPM n (stdAN n)) atTop (𝓝 stdGaussianPM) :=
  tendsto_of_charFun_limit stdAN charAN
    (fun n t _ => by rw [charAN]; rfl) AN_CLT_charFun

/-- **Corollary 14, convergence in distribution.**  The law of the standardised
    advantage gap `A_M − A_N` converges weakly to `N(0,1)`. -/
theorem gap_CLT_tendsto :
    Tendsto (fun n => empPM n (stdGap n)) atTop (𝓝 stdGaussianPM) :=
  tendsto_of_charFun_limit stdGap charGap
    (fun n t _ => by rw [charGap]; rfl) gap_CLT_charFun

end MakinenAnalysis
