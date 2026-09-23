import Mathlib
import MakinenAnalysis.CharFunIntegrate
import MakinenAnalysis.LocalLimit

/-!
# The moving Riemann-sum → Gaussian-integral step (`charP2mu_tendsto`)

This file works towards the sole remaining analytic gap on the
characteristic-function route to the local CLT, the `proof_wanted
charP2mu_tendsto` of `CharFunIntegrate.lean`:

  `charP2mu n t → exp(-t²/2)`     (the moving Riemann sum → Gaussian Fourier integral).

The Riemann-sum algebra (`charP2_riemann`), the Gaussian Fourier fact
(`gaussian_fourier_integral`, PROVED), the centering-shift `EP2 → μ`
(`charP2_sub_charP2mu_tendsto_zero`, PROVED) and the geometric two-sided tail
(`sum_pmf'_two_sided_tail_le`, PROVED) all live in `CharFunIntegrate.lean`.

## What is added here (all with **zero sorries**)

* `charP2muTerm` / `charP2mu_eq_sum_term` — the individual Riemann summand
  `pmf'(n,k)·e^{i t (k−μ)·4/√n}` and the definitional expansion of `charP2mu`.
* `norm_charP2muTerm` — each summand has norm exactly `pmf'(n,k)` (`|e^{iθ}|=1`).
* `norm_sum_charP2muTerm_le` — the L¹→L∞ bound over an arbitrary index set
  `S`: `‖Σ_{k∈S} term‖ ≤ Σ_{k∈S} pmf'`.  Absolutely bounded, no blow-up.
* `charP2mu_norm_le_one` — the uniform bound `‖charP2mu n t‖ ≤ 1` (mass 1).
* `charP2mu_riemann` — the exact sampled Riemann-sum form of `charP2mu`
  (spacing `Δx = σ⁻¹`, samples `σ·pmf'(n,k)`), mirroring `charP2_riemann`.
* `charP2mu_head_tail_norm_le` — **tail negligibility building block**: the
  off-window contribution (head `k ≤ k₀` plus tail `k ≥ k₁`) is bounded in norm
  by the geometric two-sided tail `4·pmf'(n,k₀)+4·pmf'(n,k₁)`
  (from `sum_pmf'_two_sided_tail_le`).
* `leafCLT_charFun_of_charP2mu_tendsto` — the **assembly**, isolating the gap:
  it derives `charP2 n t → exp(-t²/2)` from the (hypothesised) `charP2mu`
  convergence, via the already-proved centering shift.  This turns the open
  `charP2mu_tendsto` into a single clean hypothesis on the full route.

The genuinely hard core — the moving Riemann sum → integral convergence itself
— is left as a documented `TODO` at the end (route + Mathlib hooks recorded),
because a rigorous dominated-convergence argument for a *moving* lattice
integrand (uniform-on-compacts upgrade of `hloc` from `pmf'_ratio_gaussian`,
window Riemann sum → `∫_{-R}^R`, then `R → ∞` against the uniform tail) is
substantial and not reducible to an existing Mathlib lemma here.
-/

namespace MakinenAnalysis

open Finset Filter Topology
open MeasureTheory ProbabilityTheory

/-! ### The individual Riemann summand -/

/-- The `k`-th summand of the μ-centred Riemann sum `charP2mu`:
`pmf'(n,k)·e^{i t (k−μ)·4/√n}`.  Isolating it lets us split `charP2mu` over
index subsets (window / head / tail). -/
noncomputable def charP2muTerm (n : ℕ) (t : ℝ) (k : ℕ) : ℂ :=
  (pmf' n k : ℂ) *
    Complex.exp (Complex.I *
      Complex.ofReal (t * (((k : ℝ) - muP2 n) * 4 / Real.sqrt n)))

/-- `charP2mu` is the sum of its summands over `range n` (definitional). -/
lemma charP2mu_eq_sum_term (n : ℕ) (t : ℝ) :
    charP2mu n t = ∑ k ∈ range n, charP2muTerm n t k := rfl

/-- **Each summand has norm exactly `pmf'(n,k)`** since `|e^{iθ}| = 1`.  This is
the reason the whole sum is absolutely bounded by the total mass. -/
lemma norm_charP2muTerm (n : ℕ) (t : ℝ) (k : ℕ) :
    ‖charP2muTerm n t k‖ = pmf' n k := by
  rw [charP2muTerm, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pmf'_nonneg n k)]

/-- **The L¹ → L∞ bound over an arbitrary index set**:
`‖Σ_{k∈S} term‖ ≤ Σ_{k∈S} pmf'`.  With `S = range n` and `Σ pmf' = 1` this gives
the uniform bound `‖charP2mu‖ ≤ 1`; with `S` a head/tail block it gives tail
negligibility. -/
lemma norm_sum_charP2muTerm_le (n : ℕ) (t : ℝ) (S : Finset ℕ) :
    ‖∑ k ∈ S, charP2muTerm n t k‖ ≤ ∑ k ∈ S, pmf' n k := by
  refine (norm_sum_le _ _).trans ?_
  exact le_of_eq (Finset.sum_congr rfl fun k _ => norm_charP2muTerm n t k)

/-- **The uniform bound `‖charP2mu n t‖ ≤ 1`** (mass 1, no blow-up), from
`Σ_k pmf' = 1` (`sum_pmf'_of_closed`) and `|e^{iθ}| = 1`. -/
theorem charP2mu_norm_le_one
    (hU : ∀ m j : ℕ, 1 ≤ m → 2 * j + 1 ≤ m → m * U (m - 1) 1 j = pmfNum m j)
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    ‖charP2mu n t‖ ≤ 1 := by
  rw [charP2mu_eq_sum_term]
  refine (norm_sum_charP2muTerm_le n t (range n)).trans ?_
  rw [sum_pmf'_of_closed hU n hn]

/-! ### The sampled Riemann-sum form -/

/-- **The Riemann-sum form of `charP2mu`** (μ-centred analogue of
`charP2_riemann`): with `σ = √n/4`,
`charP2mu n t = σ⁻¹ · Σ_k [σ·pmf'(n,k)] · e^{i t (k−μ)/σ}`,
a Riemann sum with lattice spacing `Δx = σ⁻¹` and sample values `σ·pmf'(n,k)` —
exactly the quantity `hloc` controls. -/
theorem charP2mu_riemann (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    charP2mu n t
      = Complex.ofReal (sigmaP2 n)⁻¹ * ∑ k ∈ range n,
          Complex.ofReal (sigmaP2 n * pmf' n k) *
            Complex.exp (Complex.I *
              Complex.ofReal (t * (((k : ℝ) - muP2 n) / sigmaP2 n))) := by
  rw [charP2mu, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hsq : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hσ : sigmaP2 n ≠ 0 := by rw [sigmaP2]; positivity
  have key : ((k : ℝ) - muP2 n) / sigmaP2 n = ((k : ℝ) - muP2 n) * 4 / Real.sqrt n := by
    rw [sigmaP2, div_div_eq_mul_div]
  rw [key, Complex.ofReal_mul, Complex.ofReal_inv]
  have hσC : (Complex.ofReal (sigmaP2 n)) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ
  field_simp
  rw [Complex.ofReal_mul]
  ring

/-! ### Tail negligibility (geometric two-sided tail) -/

/-- **Off-window contribution is bounded by the geometric two-sided tail**:
`‖(Σ_{k ≤ k₀} term) + (Σ_{k₁ ≤ k ≤ n} term)‖ ≤ 4·pmf'(n,k₀) + 4·pmf'(n,k₁)`,
for `n ≥ 32`, `16k₀ ≤ 3n`, `5n ≤ 16k₁`.  Combines the L∞ bound
`norm_sum_charP2muTerm_le` with `sum_pmf'_two_sided_tail_le`.  Since the RHS is
`O(1/√n)` at the fractional boundaries, this makes the head+tail blocks
negligible; the fixed-`R` window remains to be handled by the Gaussian bound. -/
theorem charP2mu_head_tail_norm_le {n k₀ k₁ : ℕ} (t : ℝ) (hn : 32 ≤ n)
    (h0 : 16 * k₀ ≤ 3 * n) (h1 : 5 * n ≤ 16 * k₁) :
    ‖(∑ k ∈ range (k₀ + 1), charP2muTerm n t k)
        + (∑ k ∈ Icc k₁ n, charP2muTerm n t k)‖
      ≤ 4 * pmf' n k₀ + 4 * pmf' n k₁ := by
  refine (norm_add_le _ _).trans ?_
  have hhead := norm_sum_charP2muTerm_le n t (range (k₀ + 1))
  have htail := norm_sum_charP2muTerm_le n t (Icc k₁ n)
  have hgeo := sum_pmf'_two_sided_tail_le hn h0 h1
  linarith

/-! ### The assembly: isolating the gap as a single hypothesis -/

/-- **The assembly of the characteristic-function route** (the two-line
reduction spelled out in `CharFunIntegrate.lean`), taking the still-open
`charP2mu` convergence as a hypothesis `hmu`.  Given `hmu`, the target
`charP2 n t → exp(-t²/2)` follows from the already-proved centering shift
`charP2_sub_charP2mu_tendsto_zero`.  This reduces the entire remaining route to
the single Riemann-sum limit `hmu`. -/
theorem leafCLT_charFun_of_charP2mu_tendsto
    (hU : ∀ m j : ℕ, 1 ≤ m → 2 * j + 1 ≤ m → m * U (m - 1) 1 j = pmfNum m j)
    (t : ℝ)
    (hmu : Tendsto (fun n : ℕ => charP2mu n t) atTop
      (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2)))) :
    Tendsto (fun n : ℕ => charP2 n t) atTop (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
  have h0 := charP2_sub_charP2mu_tendsto_zero hU t
  have hsum := h0.add hmu
  rw [zero_add] at hsum
  exact hsum.congr (fun n => by ring)

/-! ### The remaining hard core (documented TODO)

The moving Riemann sum → Gaussian Fourier integral convergence itself,

  `charP2mu_tendsto`:  `charP2mu n t → exp(-t²/2)`,

is the genuine analytic core.  Statement (matching the `proof_wanted` of
`CharFunIntegrate.lean`):

    theorem charP2mu_tendsto
        (hU : ∀ m j : ℕ, 1 ≤ m → 2 * j + 1 ≤ m → m * U (m - 1) 1 j = pmfNum m j)
        (hloc : ∀ x : ℝ, Tendsto (fun n : ℕ => sigmaP2 n * pmf' n ⌊muP2 n + x * sigmaP2 n⌋₊)
            atTop (𝓝 (Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi))))
        (t : ℝ) :
        Tendsto (fun n : ℕ => charP2mu n t) atTop (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2)))

Route (ε–R, elementary), with the pieces above:

1. `charP2mu_riemann` writes `charP2mu = σ⁻¹ Σ_k [σ·pmf'(n,k)] e^{i t x_{n,k}}`
   over the lattice `x_{n,k} = (k−μ)/σ` (spacing `1/σ → 0`).

2. Split at |x_{n,k}| ≤ R.  Tail (|x| > R): for the *fractional* boundaries
   `16k₀ ≤ 3n`, `5n ≤ 16k₁` the head+tail block is `O(1/√n)` by
   `charP2mu_head_tail_norm_le`; between fixed `R` and the fractional boundary
   the mass is controlled by the Gaussian bound `pmf'_ratio_gaussian`
   (σ·pmf' ≤ C·e^{−quadratic}), giving `Σ_{|x|>R} pmf' ≤ ε(R)` uniformly in `n`.
   [OPEN: the intermediate-annulus Gaussian tail bound, uniform in `n`.]

3. Window (|x| ≤ R): upgrade `hloc` to *uniform-on-compacts*
   `σ·pmf'(n,⌊μ+xσ⌋) → φ(x)` from `pmf'_ratio_gaussian` (already uniform in `k`
   on `|k−n/4| ≤ K√n`) + the prefactor limit; then `σ⁻¹ Σ_window [σ·pmf'] e^{itx}`
   is a Riemann sum of the continuous `g(x)=φ(x)e^{itx}`, converging to
   `∫_{-R}^R g`.  [OPEN: window Riemann sum → intervalIntegral, and the uniform
   upgrade.]

4. `R → ∞`: `∫_{-R}^R g → ∫_ℝ g = e^{-t²/2}` by `gaussian_fourier_integral`.

Measure-theoretic alternative (Mathlib hooks located, not pursued):
`MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun`
(`Mathlib/MeasureTheory/Measure/LevyConvergence.lean:214`) reduces weak
convergence of the empirical lattice measures `μ_n = Σ_k pmf'(n,k)·δ_{x_{n,k}}`
to charFun convergence — but that *is* `charP2mu`, so it is circular unless weak
convergence is obtained independently (a lattice-local-limit → weak-convergence
/ Scheffé bridge, which is not present in Mathlib for the lattice-to-continuous
case).  Hence the elementary ε–R route above is preferred.

The assembly `leafCLT_charFun_of_charP2mu_tendsto` above shows that discharging
this one statement closes the whole characteristic-function route. -/

end MakinenAnalysis
