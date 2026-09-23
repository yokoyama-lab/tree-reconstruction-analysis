import Mathlib
import MakinenAnalysis.LocalCLT
import MakinenAnalysis.LocalCLTWindow

/-!
# The characteristic-function integration step for the local CLT

This file works towards `leafCLT_charFun_of_local_limit` (Proposition 12 at the
characteristic-function level): turning the *pointwise* local limit `hloc`
(`σ·pmf'(n, ⌊μ + xσ⌋) → φ(x)`) into convergence of the characteristic function
`charP2 n t → exp(-t²/2)`.

The mathematical route (see the plan in `LocalCLT.lean`) is a Riemann-sum /
dominated-convergence argument.  The genuinely hard analytic core is the
convergence of the *moving* Riemann sum to the Gaussian Fourier integral; that
is isolated below as `proof_wanted charP2mu_tendsto`.  Everything else on the
route is proved here with **zero sorries**:

* `charP2_riemann` — the exact algebraic rewrite of `charP2` (under `hU`) as a
  Riemann sum `σ⁻¹ · Σ_k [σ·pmf'(n,k)]·e^{i t (k−E)/σ}` with lattice spacing
  `Δx = σ⁻¹` and sample values `σ·pmf'(n,k)` (the quantity controlled by `hloc`).
* `gaussian_fourier_integral` — the Gaussian Fourier fact
  `∫ e^{-x²/2}/√(2π) · e^{i t x} dx = e^{-t²/2}`, obtained from Mathlib's
  `charFun_gaussianReal`.  Independently useful.
* `norm_charP2_sub_charP2mu_le` — the `EP2 → μ` phase-reduction bound
  `‖charP2 n t − charP2mu n t‖ ≤ 4|t|·|EP2 n − μ(n)|/√n`, exactly the technique
  of `norm_charAN_sub_charP2_le`; and `charP2_sub_charP2mu_tendsto_zero`, its
  `→ 0` corollary (the centering shift is asymptotically negligible).
* `sum_pmf'_two_sided_tail_le` — the tail-negligibility corollary of the
  geometric tails of `LocalCLTWindow`.

The final assembly `leafCLT_charFun_of_local_limit` is left as a commented-out
`TODO` because it consumes the still-open `charP2mu_tendsto`; the reduction
from `charP2mu_tendsto` to it is the two-line `Tendsto` addition spelled out in
the comment.
-/

namespace MakinenAnalysis

open Finset Filter Topology
open MeasureTheory ProbabilityTheory

/-! ### The Gaussian Fourier integral

`∫ e^{-x²/2}/√(2π) · e^{i t x} dx = e^{-t²/2}`.  This is the Fourier transform
of the standard Gaussian density and the target of the Riemann sum.  We read it
off Mathlib's `charFun_gaussianReal` at `μ = 0`, `v = 1`. -/

/-- **The standard-Gaussian Fourier integral.**
`∫ (e^{-x²/2}/√(2π)) · e^{i t x} dx = e^{-t²/2}`.  Proved from
`ProbabilityTheory.charFun_gaussianReal`. -/
theorem gaussian_fourier_integral (t : ℝ) :
    ∫ x : ℝ, (Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi) : ℝ) •
        Complex.exp (t * x * Complex.I)
      = Complex.exp (-(t : ℂ) ^ 2 / 2) := by
  have h := charFun_gaussianReal (μ := 0) (v := 1) t
  rw [charFun_apply_real,
    integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (by norm_num)] at h
  -- rewrite the pdf into the explicit `e^{-x²/2}/√(2π)`
  have hpdf : (fun x : ℝ => gaussianPDFReal 0 1 x • Complex.exp ((t : ℂ) * x * Complex.I))
      = (fun x : ℝ => (Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi) : ℝ) •
          Complex.exp ((t : ℂ) * x * Complex.I)) := by
    funext x
    congr 1
    rw [gaussianPDFReal, NNReal.coe_one, mul_one,
        show -(x - (0 : ℝ)) ^ 2 / (2 * 1) = -x ^ 2 / 2 by ring]
    ring
  rw [hpdf] at h
  rw [h]
  congr 1
  push_cast
  ring

/-! ### The exact Riemann-sum rewriting

Under the closed form `hU`, `charP2` is *algebraically* a Riemann sum.  With
`σ = sigmaP2 n = √n/4` the phase `(k − E)·4/√n` is exactly `(k − E)/σ`, and the
weight `pmf'(n,k)` is `σ⁻¹ · (σ·pmf'(n,k))`.  So

`charP2 n t = σ⁻¹ · Σ_k [σ·pmf'(n,k)] · e^{i t (k − E)/σ}`,

a Riemann sum with lattice spacing `Δx = σ⁻¹` and integrand value
`σ·pmf'(n,k)` — precisely the quantity that `hloc` controls. -/

/-- **The Riemann-sum form of `charP2`** (under the closed form `hU`).  Purely
algebraic; isolates the `Δx = σ⁻¹` spacing and the `σ·pmf'` sample values. -/
theorem charP2_riemann
    (hU : ∀ m j : ℕ, 1 ≤ m → 2 * j + 1 ≤ m → m * U (m - 1) 1 j = pmfNum m j)
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    charP2 n t
      = Complex.ofReal (sigmaP2 n)⁻¹ * ∑ k ∈ range n,
          Complex.ofReal (sigmaP2 n * pmf' n k) *
            Complex.exp (Complex.I *
              Complex.ofReal (t * (((k : ℝ) - EP2 n) / sigmaP2 n))) := by
  rw [charP2_eq_sum_pmf' hU n hn t, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hsq : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hσ : sigmaP2 n ≠ 0 := by rw [sigmaP2]; positivity
  have key : ((k : ℝ) - EP2 n) / sigmaP2 n = ((k : ℝ) - EP2 n) * 4 / Real.sqrt n := by
    rw [sigmaP2, div_div_eq_mul_div]
  rw [key, Complex.ofReal_mul, Complex.ofReal_inv]
  have hσC : (Complex.ofReal (sigmaP2 n)) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ
  field_simp
  rw [Complex.ofReal_mul]
  ring

/-! ### The centering-shift (phase reduction) `EP2 → μ`

`charP2` centers at the exact mean `E[P₂]`, whereas the local limit `hloc`
centers at `μ = n/4`.  Since `E[P₂] − μ → −5/8 = O(1)` and the phase is scaled
by `4/√n`, replacing `E[P₂]` by `μ` costs an `O(1/√n)` phase — negligible.  This
is the exact analogue of `norm_charAN_sub_charP2_le`. -/

/-- `charP2` re-centered at the asymptotic mean `μ(n) = n/4`. -/
noncomputable def charP2mu (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ range n, (pmf' n k : ℂ) *
    Complex.exp (Complex.I *
      Complex.ofReal (t * (((k : ℝ) - muP2 n) * 4 / Real.sqrt n)))

/-- `|e^{i x} − e^{i y}| ≤ |x − y|` for real phases (local copy of the private
`norm_exp_I_sub_exp_I` of `LeafCount`).
(public: reused by `CharFunWindow`) -/
lemma norm_cexp_I_ofReal_sub (x y : ℝ) :
    ‖Complex.exp (Complex.I * Complex.ofReal x)
        - Complex.exp (Complex.I * Complex.ofReal y)‖ ≤ |x - y| := by
  have harg : Complex.I * (x : ℂ) = Complex.I * (y : ℂ) + Complex.I * ((x - y : ℝ) : ℂ) := by
    push_cast; ring
  have hfact : Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ))
      = Complex.exp (Complex.I * (y : ℂ))
        * (Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add, ← harg]
  rw [hfact, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  simpa using Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y)

/-- **The centering-shift bound**: `‖charP2 − charP2mu‖ ≤ 4|t|·|E[P₂] − μ|/√n`.
Same technique as `norm_charAN_sub_charP2_le`: `|e^{ix} − e^{iy}| ≤ |x − y|`,
then `Σ_k pmf' = 1` (`sum_pmf'_of_closed`). -/
theorem norm_charP2_sub_charP2mu_le
    (hU : ∀ m j : ℕ, 1 ≤ m → 2 * j + 1 ≤ m → m * U (m - 1) 1 j = pmfNum m j)
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    ‖charP2 n t - charP2mu n t‖ ≤ 4 * |t| * |EP2 n - muP2 n| / Real.sqrt n := by
  set C : ℝ := 4 * |t| * |EP2 n - muP2 n| / Real.sqrt n with hC
  rw [charP2_eq_sum_pmf' hU n hn t, charP2mu, ← Finset.sum_sub_distrib]
  -- pointwise: each term's norm is `≤ pmf' n k · C`
  have hpt : ∀ k ∈ range n,
      ‖(pmf' n k : ℂ) *
            Complex.exp (Complex.I *
              Complex.ofReal (t * (((k : ℝ) - EP2 n) * 4 / Real.sqrt n)))
          - (pmf' n k : ℂ) *
            Complex.exp (Complex.I *
              Complex.ofReal (t * (((k : ℝ) - muP2 n) * 4 / Real.sqrt n)))‖
        ≤ pmf' n k * C := by
    intro k _
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (pmf'_nonneg n k)]
    refine mul_le_mul_of_nonneg_left ?_ (pmf'_nonneg n k)
    refine le_trans (norm_cexp_I_ofReal_sub _ _) ?_
    have hargeq : t * (((k : ℝ) - EP2 n) * 4 / Real.sqrt n)
        - t * (((k : ℝ) - muP2 n) * 4 / Real.sqrt n)
        = 4 * t / Real.sqrt n * (muP2 n - EP2 n) := by ring
    rw [hargeq, hC, abs_mul, abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
        abs_of_nonneg (Real.sqrt_nonneg _), abs_sub_comm (muP2 n) (EP2 n)]
    apply le_of_eq
    ring
  calc ‖∑ k ∈ range n,
          ((pmf' n k : ℂ) *
              Complex.exp (Complex.I *
                Complex.ofReal (t * (((k : ℝ) - EP2 n) * 4 / Real.sqrt n)))
            - (pmf' n k : ℂ) *
              Complex.exp (Complex.I *
                Complex.ofReal (t * (((k : ℝ) - muP2 n) * 4 / Real.sqrt n))))‖
      ≤ ∑ k ∈ range n, pmf' n k * C := (norm_sum_le _ _).trans (Finset.sum_le_sum hpt)
    _ = (∑ k ∈ range n, pmf' n k) * C := (Finset.sum_mul _ _ _).symm
    _ = C := by rw [sum_pmf'_of_closed hU n hn, one_mul]

/-- **The centering shift is asymptotically negligible**:
`charP2 n t − charP2mu n t → 0`.  Uses `EP2_sub_muP2_tendsto` (bounded) and
`1/√n → 0`. -/
theorem charP2_sub_charP2mu_tendsto_zero
    (hU : ∀ m j : ℕ, 1 ≤ m → 2 * j + 1 ≤ m → m * U (m - 1) 1 j = pmfNum m j)
    (t : ℝ) :
    Tendsto (fun n : ℕ => charP2 n t - charP2mu n t) atTop (𝓝 0) := by
  refine squeeze_zero_norm'
    (a := fun n : ℕ => 4 * |t| * |EP2 n - muP2 n| / Real.sqrt n) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact norm_charP2_sub_charP2mu_le hU n hn t
  · have hs : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hs
    have habs : Tendsto (fun n : ℕ => |EP2 n - muP2 n|) atTop (𝓝 |(-(5 / 8) : ℝ)|) :=
      EP2_sub_muP2_tendsto.abs
    have hcoef : Tendsto (fun n : ℕ => 4 * |t| * |EP2 n - muP2 n|) atTop
        (𝓝 (4 * |t| * |(-(5 / 8) : ℝ)|)) := habs.const_mul _
    have hmul := hcoef.mul hinv
    rw [mul_zero] at hmul
    refine hmul.congr (fun n => ?_)
    rw [div_eq_mul_inv]

/-! ### Tail negligibility from the geometric tails

Off a fixed-fraction window `3n/16 < k < 5n/16`, the summed mass is dominated by
`4` times the two boundary values (`LocalCLTWindow.sum_pmf'_head_le` and
`sum_pmf'_tail_le`).  Since `|e^{iθ}| = 1`, this bounds the off-window
contribution to any charFun sum by the same quantity. -/

/-- **Two-sided tail mass** beyond the fractions `3n/16` (left) and `5n/16`
(right): `Σ_{k ≤ k₀} pmf' + Σ_{k ≥ k₁} pmf' ≤ 4·pmf'(n,k₀) + 4·pmf'(n,k₁)`. -/
theorem sum_pmf'_two_sided_tail_le {n k₀ k₁ : ℕ} (hn : 32 ≤ n)
    (h0 : 16 * k₀ ≤ 3 * n) (h1 : 5 * n ≤ 16 * k₁) :
    (∑ k ∈ range (k₀ + 1), pmf' n k) + (∑ k ∈ Icc k₁ n, pmf' n k)
      ≤ 4 * pmf' n k₀ + 4 * pmf' n k₁ := by
  have hh := sum_pmf'_head_le hn h0
  have ht := sum_pmf'_tail_le h1
  linarith

/-! ### The remaining analytic core, and the assembly

What is left is the convergence of the (moving) Riemann sum `charP2mu` to the
Gaussian Fourier integral `gaussian_fourier_integral`.  This is the genuinely
hard dominated-convergence step (uniform-on-compacts upgrade of `hloc` via the
unimodal sandwich `pmf'_mono_of_le`/`pmf'_anti_of_ge`, the uniform tail
domination `sum_pmf'_two_sided_tail_le`, and Riemann-sum → integral for a
moving integrand).  It is isolated cleanly here. -/

/-- **Wanted: the window-Riemann convergence.**  The re-centered Riemann sum
`charP2mu` converges to the Gaussian Fourier integral `= e^{-t²/2}`.  This is
the sole remaining gap on the route (window Riemann sum + unimodal tail
domination + `gaussian_fourier_integral`). -/
proof_wanted charP2mu_tendsto
    (hU : ∀ m j : ℕ, 1 ≤ m → 2 * j + 1 ≤ m → m * U (m - 1) 1 j = pmfNum m j)
    (hloc : ∀ x : ℝ,
      Tendsto (fun n : ℕ => sigmaP2 n * pmf' n ⌊muP2 n + x * sigmaP2 n⌋₊) atTop
        (𝓝 (Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi))))
    (t : ℝ) :
    Tendsto (fun n : ℕ => charP2mu n t) atTop (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2)))

/-  **The assembly (TODO — consumes `charP2mu_tendsto`).**

Once `charP2mu_tendsto` is available, the target follows in two lines from the
already-proved `charP2_sub_charP2mu_tendsto_zero`:

    theorem leafCLT_charFun_of_local_limit
        (hU : ∀ m j : ℕ, 1 ≤ m → 2 * j + 1 ≤ m → m * U (m - 1) 1 j = pmfNum m j)
        (hloc : ∀ x : ℝ,
          Tendsto (fun n : ℕ => sigmaP2 n * pmf' n ⌊muP2 n + x * sigmaP2 n⌋₊) atTop
            (𝓝 (Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi))))
        (t : ℝ) :
        Tendsto (fun n : ℕ => charP2 n t) atTop (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
      have h0 := charP2_sub_charP2mu_tendsto_zero hU t
      have h1 := charP2mu_tendsto hU hloc t
      have := h0.add h1                       -- → 0 + exp(-t²/2)
      simpa using this.congr (fun n => by ring)  -- charP2 = (charP2 − charP2mu) + charP2mu
-/
