import Mathlib
import MakinenAnalysis.Normalization
import MakinenAnalysis.ModePrefactorMain
import MakinenAnalysis.CharFunWindow

/-!
# Final assembly: Proposition 12 and Theorem 13, unconditionally

Every hypothesis threaded through the local-CLT development is now a theorem:

* `hU`    = `U_mul_pmfNum`            (`Normalization`, from the pop↔degree bridge);
* `hnorm` = `sum_pmf'_eq_one`         (`Normalization`);
* `hpre`  = `mode_prefactor_tendsto`  (`ModePrefactorMain`, self-normalisation squeeze);
* `hann`  = `sum_pmf'_annulus_vanishes` (below, from `sum_pmf'_annulus_le`).

This file discharges them all and delivers the `proof_wanted` targets of
`LocalCLT`, `CharFunIntegrate` and `LeafCount`:

* `pmf'_local_limit` — the local limit theorem for the double-pop law;
* `charP2mu_tendsto` — the moving Riemann sum → Gaussian Fourier integral;
* `leafCLT_charFun`  — **Proposition 12** (`prop:leafclt`) at the charFun level;
* `AN_CLT_charFun`   — **Theorem 13** (`thm:Nclt`) at the charFun level,
  via the proved reduction `AN_CLT_of_leafCLT`.
-/

namespace MakinenAnalysis

open Filter Finset

/-- **`hann`, unconditionally**: the annulus mass `Σ_{|k−n/4| ≥ K√n} pmf'`
    is eventually `≤ ε` for a suitable `K = K(ε)`, by `sum_pmf'_annulus_le`
    (geometric far-field domination) with the normalisation
    `sum_pmf'_eq_one`. -/
theorem sum_pmf'_annulus_vanishes :
    ∀ ε > 0, ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ n : ℕ in atTop,
      ∑ k ∈ (Finset.range n).filter
        (fun k : ℕ => K * Real.sqrt n ≤ |(k : ℝ) - n / 4|), pmf' n k ≤ ε := by
  intro ε hε
  set K : ℝ := max 2 (1 - Real.log (ε / 100000000)) with hK_def
  have hK2 : 2 ≤ K := le_max_left _ _
  refine ⟨K, by linarith, ?_⟩
  have hbound : (100000000 : ℝ) * Real.exp (-(K - 1)) ≤ ε := by
    have h1 : 1 - Real.log (ε / 100000000) ≤ K := le_max_right _ _
    have h2 : Real.exp (-(K - 1)) ≤ Real.exp (Real.log (ε / 100000000)) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_log (by positivity)] at h2
    calc (100000000 : ℝ) * Real.exp (-(K - 1))
        ≤ 100000000 * (ε / 100000000) := by nlinarith [h2]
      _ = ε := by ring
  filter_upwards [eventually_ge_atTop 1000000000] with n hn
  exact le_trans
    (sum_pmf'_annulus_le hK2 hn (sum_pmf'_eq_one n (by omega))) hbound

/-- **The local limit theorem, unconditionally** (the `proof_wanted
    pmf'_local_limit` of `LocalCLT`): the double-pop law satisfies
    `σ·pmf'(n, ⌊μ + xσ⌋) → e^{−x²/2}/√(2π)`. -/
theorem pmf'_local_limit (x : ℝ) :
    Tendsto (fun n : ℕ => sigmaP2 n * pmf' n ⌊muP2 n + x * sigmaP2 n⌋₊) atTop
      (nhds (Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi))) :=
  pmf'_local_limit' sum_pmf'_eq_one x

/-- **The moving Riemann sum converges, unconditionally** (the `proof_wanted
    charP2mu_tendsto` of `CharFunIntegrate`, hypothesis-free form). -/
theorem charP2mu_tendsto (t : ℝ) :
    Tendsto (fun n : ℕ => charP2mu n t) atTop
      (nhds (Complex.exp (-(t : ℂ) ^ 2 / 2))) :=
  charP2mu_tendsto_of_prefactor_annulus sum_pmf'_eq_one
    (mode_prefactor_tendsto sum_pmf'_eq_one) sum_pmf'_annulus_vanishes t

/-- **Proposition 12 (`prop:leafclt`), charFun form — PROVED.**  The
    standardised double-pop (leaf) count is asymptotically `N(0,1)`. -/
theorem leafCLT_charFun (t : ℝ) :
    Tendsto (fun n : ℕ => charP2 n t) atTop
      (nhds (Complex.exp (-(t : ℂ) ^ 2 / 2))) :=
  leafCLT_charFun_of_prefactor_annulus U_mul_pmfNum sum_pmf'_eq_one
    (mode_prefactor_tendsto sum_pmf'_eq_one) sum_pmf'_annulus_vanishes t

/-- **Theorem 13 (`thm:Nclt`), charFun form — PROVED.**  The standardised
    comparison count of Algorithm `N` is asymptotically `N(0,1)`: the
    characteristic function of `(A_N − E[A_N])/(√n/4)` converges pointwise to
    the standard Gaussian characteristic function `e^{−t²/2}`. -/
theorem AN_CLT_charFun (t : ℝ) :
    Tendsto (fun n : ℕ => charAN n t) atTop
      (nhds (Complex.exp (-(t : ℂ) ^ 2 / 2))) :=
  AN_CLT_of_leafCLT leafCLT_charFun t

end MakinenAnalysis
