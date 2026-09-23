import Mathlib
import MakinenAnalysis.CharFunLimit
import MakinenAnalysis.LocalLimit
import MakinenAnalysis.ModePrefactor

/-!
# The window Riemann-sum → Gaussian-Fourier-integral step (`charP2mu_tendsto`)

This file proves the moving-window Riemann-sum convergence that is the sole
remaining analytic gap of the characteristic-function route
(`proof_wanted charP2mu_tendsto` in `CharFunIntegrate.lean`), **taking as
hypotheses** the two limits that are isolated in parallel developments:

* `hpre` — the mode-prefactor limit `σ·pmf'(n,⌊n/4⌋) → 1/√(2π)`;
* `hann` — annulus (off-window) negligibility: for every `ε > 0` there is a
  `K ≥ 1` such that eventually `∑_{|k−n/4| ≥ K√n} pmf'(n,k) ≤ ε`.
  (This is implied by any bound of the shape
  `limsup_n ∑_{annulus K} ≤ A·e^{−4K²}/K` for all `K ≥ 1`, since the annulus
  mass is monotone in `K` and the right side tends to `0`.)

## Main results (zero sorries)

* `norm_riemann_sum_sub_integral_le` — the self-contained, reusable
  fixed-grid Riemann-sum → interval-integral bound for a function Lipschitz
  on the window: `‖δ·∑_{k<m} g(a+kδ) − ∫_a^{a+mδ} g‖ ≤ m·L·δ²`.
* `norm_gaussFourierKernel_sub_le` — the elementary (derivative-free)
  Lipschitz bound for the Gaussian–Fourier kernel `g(x) = e^{−x²/2}e^{itx}`
  on `|x| ≤ R`, with constant `|t| + R`.
* `pmf'_window_gauss_est` — the on-window multiplicative comparison
  `|pmf'(n,k) − P₀·e^{−x_k²/2}| ≤ pmf'(n,k)·(e^{C(K)/√n} − 1)`, obtained by
  exponentiating `pmf'_ratio_gaussian`.
* `charP2mu_window_estimate` — the complete quantitative per-`n` estimate:
  `‖charP2mu n t − e^{−t²/2}‖` is bounded by the annulus mass, three
  explicitly vanishing `O(1/√n)`-type errors, and the Gaussian truncation
  error at `±4K`.
* `charP2mu_tendsto_of_prefactor_annulus` — the assembled ε-argument:
  `charP2mu n t → e^{−t²/2}` from `hnorm`, `hpre`, `hann`.
* `leafCLT_charFun_of_prefactor_annulus` — the corollary through the proved
  assembly `leafCLT_charFun_of_charP2mu_tendsto`:
  `charP2 n t → e^{−t²/2}`.
-/

namespace MakinenAnalysis

open Finset Filter Topology
open MeasureTheory ProbabilityTheory

/-! ### Elementary exponential estimates -/

-- `|e^{ix} − e^{iy}| ≤ |x − y|` for real phases: reuses
-- `norm_cexp_I_ofReal_sub` from `CharFunIntegrate` (verbatim duplicate,
-- consolidated).

/-- Directed 1-Lipschitz bound for `exp` on the nonpositive half-line. -/
private lemma exp_sub_exp_le_of_le {u v : ℝ} (hu : u ≤ 0) (hvu : v ≤ u) :
    Real.exp u - Real.exp v ≤ u - v := by
  have h1 : Real.exp u * Real.exp (v - u) = Real.exp v := by
    rw [← Real.exp_add]; ring_nf
  have h2 := Real.add_one_le_exp (v - u)
  have h3 : Real.exp u ≤ 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr hu
  nlinarith [Real.exp_pos u, Real.exp_pos v]

/-- **`exp` is 1-Lipschitz on the nonpositive half-line** (elementary, no
mean-value theorem): `|e^u − e^v| ≤ |u − v|` for `u, v ≤ 0`. -/
lemma abs_exp_sub_exp_le {u v : ℝ} (hu : u ≤ 0) (hv : v ≤ 0) :
    |Real.exp u - Real.exp v| ≤ |u - v| := by
  rcases le_total v u with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact exp_sub_exp_le_of_le hu h
  · rw [abs_sub_comm (Real.exp u) (Real.exp v), abs_sub_comm u v,
      abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact exp_sub_exp_le_of_le hv h

/-- `|1 − e^{−D}| ≤ e^c − 1` whenever `|D| ≤ c` (the multiplicative-error
bound used to replace `e^{θ_k}` by `1` on the window). -/
lemma abs_one_sub_exp_neg_le {D c : ℝ} (h : |D| ≤ c) :
    |1 - Real.exp (-D)| ≤ Real.exp c - 1 := by
  rcases le_total 0 D with hD | hD
  · have h1 : Real.exp (-D) ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonneg (by linarith)]
    have h2 := Real.add_one_le_exp (-D)
    have h3 : D ≤ c := (le_abs_self D).trans h
    have h4 := Real.add_one_le_exp c
    linarith
  · have h1 : 1 ≤ Real.exp (-D) := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonpos (by linarith)]
    have h3 : -D ≤ c := (neg_le_abs D).trans h
    have := Real.exp_le_exp.mpr h3
    linarith

/-- `1 ≤ √(2π)`. -/
private lemma one_le_sqrt_two_pi : 1 ≤ Real.sqrt (2 * Real.pi) := by
  rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])

private lemma one_div_sqrt_two_pi_le_one : 1 / Real.sqrt (2 * Real.pi) ≤ 1 := by
  rw [div_le_one (by positivity)]
  exact one_le_sqrt_two_pi

/-! ### The Gaussian–Fourier kernel and its elementary Lipschitz bound -/

/-- The Gaussian–Fourier kernel `g(x) = e^{−x²/2}·e^{itx}`, the integrand of
the window Riemann sum. -/
noncomputable def gaussFourierKernel (t x : ℝ) : ℂ :=
  Complex.ofReal (Real.exp (-x ^ 2 / 2)) *
    Complex.exp (Complex.I * Complex.ofReal (t * x))

lemma norm_gaussFourierKernel (t x : ℝ) :
    ‖gaussFourierKernel t x‖ = Real.exp (-x ^ 2 / 2) := by
  rw [gaussFourierKernel, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

lemma norm_gaussFourierKernel_le_one (t x : ℝ) : ‖gaussFourierKernel t x‖ ≤ 1 := by
  rw [norm_gaussFourierKernel, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x])

lemma continuous_gaussFourierKernel (t : ℝ) :
    Continuous fun x : ℝ => gaussFourierKernel t x := by
  unfold gaussFourierKernel
  fun_prop

/-- **The elementary Lipschitz bound for the Gaussian–Fourier kernel** on the
ball `|x| ≤ R`, with constant `|t| + R`.  Derivative-free: the phase factor is
handled by `|e^{ix} − e^{iy}| ≤ |x − y|` and the Gaussian factor by the
1-Lipschitz bound for `exp` on the nonpositive half-line. -/
lemma norm_gaussFourierKernel_sub_le (t : ℝ) {R x y : ℝ}
    (hx : |x| ≤ R) (hy : |y| ≤ R) :
    ‖gaussFourierKernel t x - gaussFourierKernel t y‖ ≤ (|t| + R) * |x - y| := by
  have hdecomp : gaussFourierKernel t x - gaussFourierKernel t y
      = Complex.ofReal (Real.exp (-x ^ 2 / 2)) *
          (Complex.exp (Complex.I * Complex.ofReal (t * x))
            - Complex.exp (Complex.I * Complex.ofReal (t * y)))
        + Complex.ofReal (Real.exp (-x ^ 2 / 2) - Real.exp (-y ^ 2 / 2)) *
            Complex.exp (Complex.I * Complex.ofReal (t * y)) := by
    rw [gaussFourierKernel, gaussFourierKernel, Complex.ofReal_sub]; ring
  rw [hdecomp]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖Complex.ofReal (Real.exp (-x ^ 2 / 2)) *
      (Complex.exp (Complex.I * Complex.ofReal (t * x))
        - Complex.exp (Complex.I * Complex.ofReal (t * y)))‖ ≤ |t| * |x - y| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-x ^ 2 / 2) ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x])
    calc Real.exp (-x ^ 2 / 2) *
          ‖Complex.exp (Complex.I * Complex.ofReal (t * x))
            - Complex.exp (Complex.I * Complex.ofReal (t * y))‖
        ≤ 1 * ‖Complex.exp (Complex.I * Complex.ofReal (t * x))
            - Complex.exp (Complex.I * Complex.ofReal (t * y))‖ :=
          mul_le_mul_of_nonneg_right he (norm_nonneg _)
      _ = ‖Complex.exp (Complex.I * Complex.ofReal (t * x))
            - Complex.exp (Complex.I * Complex.ofReal (t * y))‖ := one_mul _
      _ ≤ |t * x - t * y| := norm_cexp_I_ofReal_sub _ _
      _ = |t| * |x - y| := by rw [← abs_mul]; ring_nf
  have h2 : ‖Complex.ofReal (Real.exp (-x ^ 2 / 2) - Real.exp (-y ^ 2 / 2)) *
      Complex.exp (Complex.I * Complex.ofReal (t * y))‖ ≤ R * |x - y| := by
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    have hexp : |Real.exp (-x ^ 2 / 2) - Real.exp (-y ^ 2 / 2)|
        ≤ |(-x ^ 2 / 2) - (-y ^ 2 / 2)| :=
      abs_exp_sub_exp_le (by nlinarith [sq_nonneg x]) (by nlinarith [sq_nonneg y])
    refine hexp.trans ?_
    have h3 : |(-(x + y)) / 2| ≤ R := by
      have habs := abs_add_le x y
      have hR2 : |x + y| ≤ 2 * R := by linarith
      rw [abs_div, abs_neg, abs_two]
      linarith
    calc |(-x ^ 2 / 2) - (-y ^ 2 / 2)| = |(x - y) * ((-(x + y)) / 2)| := by
          rw [show (-x ^ 2 / 2) - (-y ^ 2 / 2) = (x - y) * ((-(x + y)) / 2) by ring]
      _ = |x - y| * |(-(x + y)) / 2| := abs_mul _ _
      _ ≤ |x - y| * R := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      _ = R * |x - y| := mul_comm _ _
  calc ‖Complex.ofReal (Real.exp (-x ^ 2 / 2)) *
          (Complex.exp (Complex.I * Complex.ofReal (t * x))
            - Complex.exp (Complex.I * Complex.ofReal (t * y)))‖
        + ‖Complex.ofReal (Real.exp (-x ^ 2 / 2) - Real.exp (-y ^ 2 / 2)) *
            Complex.exp (Complex.I * Complex.ofReal (t * y))‖
      ≤ |t| * |x - y| + R * |x - y| := add_le_add h1 h2
    _ = (|t| + R) * |x - y| := by ring

/-! ### The fixed-grid Riemann-sum → interval-integral bound -/

/-- **The reusable Riemann-sum bound.**  For `g` continuous and `L`-Lipschitz
on `[a, a + mδ]` and an equidistant grid of mesh `δ ≥ 0`,

`‖δ·∑_{k<m} g(a + kδ) − ∫_a^{a+mδ} g‖ ≤ m·(L·δ²)`.

Cell-by-cell: on each cell `[a+kδ, a+(k+1)δ]` the sample value differs from the
integrand by at most `L·δ`, so each cell contributes at most `L·δ²`. -/
lemma norm_riemann_sum_sub_integral_le {g : ℝ → ℂ} (hg : Continuous g)
    {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) (a : ℝ) (m : ℕ)
    (hLip : ∀ x ∈ Set.Icc a (a + m * δ), ∀ y ∈ Set.Icc a (a + m * δ),
      ‖g x - g y‖ ≤ L * |x - y|) :
    ‖(δ : ℂ) * ∑ k ∈ range m, g (a + k * δ) - ∫ x in a..(a + m * δ), g x‖
      ≤ m * (L * δ ^ 2) := by
  have hint : ∀ u v : ℝ, IntervalIntegrable g MeasureTheory.volume u v :=
    fun u v => hg.intervalIntegrable u v
  have hadj : (∑ k ∈ range m, ∫ x in (a + (k : ℝ) * δ)..(a + ((k : ℝ) + 1) * δ), g x)
      = ∫ x in a..(a + (m : ℝ) * δ), g x := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (μ := MeasureTheory.volume) (f := g) (a := fun k : ℕ => a + (k : ℝ) * δ)
      (n := m) (fun k _ => hint _ _)
    push_cast at h
    simpa using h
  rw [← hadj, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hcell : ∀ k ∈ range m,
      ‖(δ : ℂ) * g (a + (k : ℝ) * δ)
          - ∫ x in (a + (k : ℝ) * δ)..(a + ((k : ℝ) + 1) * δ), g x‖ ≤ L * δ ^ 2 := by
    intro k hk
    have hk' : k < m := mem_range.mp hk
    have hkm : (k : ℝ) * δ ≤ (m : ℝ) * δ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hk'.le) hδ
    have hk1m : ((k : ℝ) + 1) * δ ≤ (m : ℝ) * δ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hk') hδ
    have hkδ : 0 ≤ (k : ℝ) * δ := mul_nonneg (Nat.cast_nonneg k) hδ
    have hle : a + (k : ℝ) * δ ≤ a + ((k : ℝ) + 1) * δ := by nlinarith
    have hconst : (δ : ℂ) * g (a + (k : ℝ) * δ)
        = ∫ _x in (a + (k : ℝ) * δ)..(a + ((k : ℝ) + 1) * δ), g (a + (k : ℝ) * δ) := by
      rw [intervalIntegral.integral_const,
        show a + ((k : ℝ) + 1) * δ - (a + (k : ℝ) * δ) = δ by ring, Complex.real_smul]
    rw [hconst, ← intervalIntegral.integral_sub intervalIntegrable_const (hint _ _)]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := L * δ) ?_).trans ?_
    · intro x hx
      rw [Set.uIoc_of_le hle] at hx
      have h1 : a ≤ a + (k : ℝ) * δ := le_add_of_nonneg_right hkδ
      have hkmem : (a + (k : ℝ) * δ) ∈ Set.Icc a (a + (m : ℝ) * δ) :=
        ⟨h1, by linarith⟩
      have hxmem : x ∈ Set.Icc a (a + (m : ℝ) * δ) :=
        ⟨h1.trans hx.1.le, hx.2.trans (by linarith)⟩
      refine (hLip _ hkmem _ hxmem).trans ?_
      have hd : |a + (k : ℝ) * δ - x| ≤ δ := by
        rw [abs_le]
        constructor
        · linarith [hx.2]
        · linarith [hx.1.le]
      exact mul_le_mul_of_nonneg_left hd hL
    · rw [show a + ((k : ℝ) + 1) * δ - (a + (k : ℝ) * δ) = δ by ring, abs_of_nonneg hδ]
      exact le_of_eq (by ring)
  refine (Finset.sum_le_sum hcell).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ### The Gaussian–Fourier integrand of `gaussian_fourier_integral` -/

/-- The integrand of `gaussian_fourier_integral`:
`F(x) = (e^{−x²/2}/√(2π))·e^{itx}`. -/
noncomputable def gaussFourierIntegrand (t x : ℝ) : ℂ :=
  (Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi) : ℝ) •
    Complex.exp (t * x * Complex.I)

/-- `∫ F = e^{−t²/2}` (restatement of the proved `gaussian_fourier_integral`). -/
lemma integral_gaussFourierIntegrand (t : ℝ) :
    ∫ x : ℝ, gaussFourierIntegrand t x = Complex.exp (-(t : ℂ) ^ 2 / 2) :=
  gaussian_fourier_integral t

/-- `F(x) = (1/√(2π))·g(x)` pointwise. -/
lemma gaussFourierIntegrand_eq (t x : ℝ) :
    gaussFourierIntegrand t x
      = Complex.ofReal (1 / Real.sqrt (2 * Real.pi)) * gaussFourierKernel t x := by
  rw [gaussFourierIntegrand, gaussFourierKernel, Complex.real_smul,
    show (t : ℂ) * x * Complex.I = Complex.I * Complex.ofReal (t * x) by push_cast; ring]
  push_cast
  ring

/-- Interval-integral version of `gaussFourierIntegrand_eq`. -/
lemma intervalIntegral_gaussFourierIntegrand (t a b : ℝ) :
    (∫ x in a..b, gaussFourierIntegrand t x)
      = Complex.ofReal (1 / Real.sqrt (2 * Real.pi)) *
          ∫ x in a..b, gaussFourierKernel t x := by
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun x _ => gaussFourierIntegrand_eq t x

lemma continuous_gaussFourierIntegrand (t : ℝ) :
    Continuous fun x : ℝ => gaussFourierIntegrand t x := by
  unfold gaussFourierIntegrand
  fun_prop

/-- `F` is integrable (dominated by the Gaussian). -/
lemma integrable_gaussFourierIntegrand (t : ℝ) :
    Integrable fun x : ℝ => gaussFourierIntegrand t x := by
  have hdom : Integrable fun x : ℝ => Real.exp (-(1 / 2) * x ^ 2) :=
    integrable_exp_neg_mul_sq (by norm_num)
  refine hdom.mono' (continuous_gaussFourierIntegrand t).aestronglyMeasurable ?_
  filter_upwards with x
  rw [gaussFourierIntegrand, norm_smul, Real.norm_eq_abs,
    show (t : ℂ) * x * Complex.I = Complex.ofReal (t * x) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one, abs_of_pos (by positivity),
    show -(1 / 2) * x ^ 2 = -x ^ 2 / 2 by ring]
  exact div_le_self (Real.exp_pos _).le one_le_sqrt_two_pi

/-! ### The standardized lattice -/

/-- The standardized lattice point `x_{n,k} = (k − μ)·4/√n = (k − μ)/σ`. -/
noncomputable def xP2 (n k : ℕ) : ℝ := ((k : ℝ) - muP2 n) * 4 / Real.sqrt n

/-- `charP2muTerm` through the lattice point (definitional). -/
lemma charP2muTerm_eq_xP2 (n : ℕ) (t : ℝ) (k : ℕ) :
    charP2muTerm n t k
      = (pmf' n k : ℂ) * Complex.exp (Complex.I * Complex.ofReal (t * xP2 n k)) := rfl

/-- The lattice is equidistant with mesh `4/√n = σ⁻¹`. -/
lemma xP2_add (n a j : ℕ) (hn : (0 : ℝ) < n) :
    xP2 n (a + j) = xP2 n a + (j : ℝ) * (4 / Real.sqrt n) := by
  have hs : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hn)
  simp only [xP2, muP2]
  push_cast
  field_simp
  ring

/-- The Gaussian quadratic in lattice coordinates: `x_k²/2 = 8(k−n/4)²/n`. -/
lemma xP2_sq (n k : ℕ) (hn : (0 : ℝ) < n) :
    xP2 n k ^ 2 / 2 = 8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n := by
  simp only [xP2, muP2]
  rw [div_pow, mul_pow, Real.sq_sqrt hn.le]
  ring

/-! ### The on-window multiplicative Gaussian comparison -/

/-- **On-window multiplicative Gaussian comparison** (exponentiated
`pmf'_ratio_gaussian`): for `K ≥ 1`, `n ≥ (64K)²` and `|k − n/4| ≤ K√n`,

`|pmf'(n,k) − P₀·e^{−x_k²/2}| ≤ pmf'(n,k)·(e^{C(K)/√n} − 1)`,

with `P₀ = pmf'(n,⌊n/4⌋)` and `C(K) = 10000K(1+K²)+16K+8`. -/
lemma pmf'_window_gauss_est {n : ℕ} {K : ℝ} (hK : 1 ≤ K)
    (hthr : (64 * K) ^ 2 ≤ (n : ℝ)) {k : ℕ}
    (hk : |(k : ℝ) - (n : ℝ) / 4| ≤ K * Real.sqrt n) :
    |pmf' n k - pmf' n ⌊(n : ℝ) / 4⌋₊ * Real.exp (-xP2 n k ^ 2 / 2)|
      ≤ pmf' n k *
        (Real.exp ((10000 * K * (1 + K ^ 2) + 16 * K + 8) / Real.sqrt n) - 1) := by
  have hn4096 : (4096 : ℝ) ≤ (n : ℝ) := le_trans (by nlinarith) hthr
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hn64 : 64 ≤ n := by exact_mod_cast (by linarith : (64 : ℝ) ≤ (n : ℝ))
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hsq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have h64K : 64 * K ≤ Real.sqrt n := by
    have h1 : Real.sqrt ((64 * K) ^ 2) ≤ Real.sqrt n := Real.sqrt_le_sqrt hthr
    rwa [Real.sqrt_sq (by positivity)] at h1
  have hKn : K * Real.sqrt n ≤ (n : ℝ) / 64 := by nlinarith
  -- support bounds, hence positivity of both pmf' values
  have hkR : (k : ℝ) ≤ (n : ℝ) / 4 + (n : ℝ) / 64 := by
    have := (abs_le.mp hk).2
    linarith
  have h2k : 2 * k + 1 ≤ n := by
    have : 2 * (k : ℝ) + 1 ≤ (n : ℝ) := by linarith
    exact_mod_cast this
  have hfl : ((⌊(n : ℝ) / 4⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) / 4 := Nat.floor_le (by positivity)
  have h2k0 : 2 * ⌊(n : ℝ) / 4⌋₊ + 1 ≤ n := by
    have : 2 * ((⌊(n : ℝ) / 4⌋₊ : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by linarith
    exact_mod_cast this
  have hp : 0 < pmf' n k := pmf'_pos h2k
  have hp0 : 0 < pmf' n ⌊(n : ℝ) / 4⌋₊ := pmf'_pos h2k0
  -- the log-ratio bound
  have hlog := pmf'_ratio_gaussian hK hn64 hthr hk
  set D := Real.log (pmf' n k) - Real.log (pmf' n ⌊(n : ℝ) / 4⌋₊)
      + 8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ) with hD
  -- multiplicative identity  P₀·e^{−8d²/n} = pmf'·e^{−D}
  have hid : pmf' n ⌊(n : ℝ) / 4⌋₊ * Real.exp (-(8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n))
      = pmf' n k * Real.exp (-D) := by
    conv_lhs => rw [← Real.exp_log hp0]
    conv_rhs => rw [← Real.exp_log hp]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hD]; ring
  -- rewrite the exponent through the lattice coordinate
  have hxsq : -xP2 n k ^ 2 / 2 = -(8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n) := by
    have := xP2_sq n k hn0
    linarith
  rw [hxsq, hid, show pmf' n k - pmf' n k * Real.exp (-D)
      = pmf' n k * (1 - Real.exp (-D)) by ring, abs_mul, abs_of_pos hp]
  exact mul_le_mul_of_nonneg_left (abs_one_sub_exp_neg_le hlog) hp.le

/-! ### The complete quantitative per-`n` window estimate -/

set_option maxHeartbeats 800000 in
/-- **The quantitative window estimate.**  For `K ≥ 1` and `n ≥ (64K)²`,

`‖charP2mu n t − e^{−t²/2}‖ ≤ [annulus mass] + (e^{C(K)/√n} − 1)
    + |σP₀ − 1/√(2π)|·(8K+4) + ((32K+16)(|t|+4K+1)+12)/√n
    + ‖∫_{−4K}^{4K} F − e^{−t²/2}‖`.

The five error terms are: the off-window (annulus) mass; the multiplicative
window comparison from `pmf'_ratio_gaussian`; the prefactor swap `σP₀ → 1/√(2π)`;
the Riemann-sum → integral error (mesh `4/√n`, Lipschitz constant `|t|+4K+1`,
plus the two boundary-cell errors); and the Gaussian truncation at `±4K`. -/
theorem charP2mu_window_estimate
    (hnorm : ∀ n : ℕ, 1 ≤ n → ∑ k ∈ Finset.range n, pmf' n k = 1)
    {K : ℝ} (hK : 1 ≤ K) (t : ℝ) {n : ℕ} (hthr : (64 * K) ^ 2 ≤ (n : ℝ)) :
    ‖charP2mu n t - Complex.exp (-(t : ℂ) ^ 2 / 2)‖
      ≤ (∑ k ∈ (range n).filter
            (fun k : ℕ => K * Real.sqrt n ≤ |(k : ℝ) - (n : ℝ) / 4|), pmf' n k)
        + (Real.exp ((10000 * K * (1 + K ^ 2) + 16 * K + 8) / Real.sqrt n) - 1)
        + |sigmaP2 n * pmf' n ⌊(n : ℝ) / 4⌋₊ - 1 / Real.sqrt (2 * Real.pi)|
            * (8 * K + 4)
        + ((32 * K + 16) * (|t| + (4 * K + 1)) + 12) / Real.sqrt n
        + ‖(∫ x in (-(4 * K))..(4 * K), gaussFourierIntegrand t x)
            - Complex.exp (-(t : ℂ) ^ 2 / 2)‖ := by
  -- ambient numerics
  have hn4096 : (4096 : ℝ) ≤ (n : ℝ) := le_trans (by nlinarith) hthr
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hn1 : 1 ≤ n := by exact_mod_cast (by linarith : (1 : ℝ) ≤ (n : ℝ))
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hsq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have h64K : 64 * K ≤ Real.sqrt n := by
    have h1 : Real.sqrt ((64 * K) ^ 2) ≤ Real.sqrt n := Real.sqrt_le_sqrt hthr
    rwa [Real.sqrt_sq (by positivity)] at h1
  have hs64 : (64 : ℝ) ≤ Real.sqrt n := by nlinarith
  have hKn : K * Real.sqrt n ≤ (n : ℝ) / 64 := by nlinarith
  have hsn : Real.sqrt n ≤ (n : ℝ) := by nlinarith
  have hKs0 : 0 ≤ K * Real.sqrt n := mul_nonneg (by linarith) hs0.le
  -- the mesh
  set δ : ℝ := 4 / Real.sqrt n with hδ_def
  have hδ0 : 0 < δ := by rw [hδ_def]; positivity
  have hδ1 : δ ≤ 1 := by rw [hδ_def, div_le_one hs0]; linarith
  have hσδ : sigmaP2 n * δ = 1 := by
    rw [hδ_def]; simp only [sigmaP2]; field_simp
  have hxP2_eq : ∀ k : ℕ, xP2 n k = ((k : ℝ) - (n : ℝ) / 4) * δ := by
    intro k
    simp only [xP2, muP2]
    rw [hδ_def]
    exact mul_div_assoc _ _ _
  have hKδ : (K * Real.sqrt n) * δ = 4 * K := by
    rw [hδ_def]; field_simp
  -- window boundaries
  set y : ℝ := (n : ℝ) / 4 - K * Real.sqrt n with hy_def
  set z : ℝ := (n : ℝ) / 4 + K * Real.sqrt n with hz_def
  have hy0 : 0 ≤ y := by rw [hy_def]; linarith
  have hz0 : 0 ≤ z := by rw [hz_def]; linarith
  have hzn : z < (n : ℝ) := by rw [hz_def]; linarith
  set a : ℕ := ⌊y⌋₊ + 1 with ha_def
  set c : ℕ := ⌊z⌋₊ + 1 with hc_def
  have hya : y < (a : ℝ) := by
    rw [ha_def]; push_cast; exact Nat.lt_floor_add_one y
  have hay : (a : ℝ) ≤ y + 1 := by
    rw [ha_def]; push_cast
    have := Nat.floor_le hy0
    linarith
  have hzc : z < (c : ℝ) := by
    rw [hc_def]; push_cast; exact Nat.lt_floor_add_one z
  have hcz : (c : ℝ) ≤ z + 1 := by
    rw [hc_def]; push_cast
    have := Nat.floor_le hz0
    linarith
  have hyz : y + 1 ≤ z := by rw [hy_def, hz_def]; nlinarith
  have hac : a ≤ c := by
    have h1 : (a : ℝ) < (c : ℝ) := by linarith
    exact_mod_cast h1.le
  -- the window
  set W : Finset ℕ :=
    (range n).filter (fun k : ℕ => ¬ K * Real.sqrt n ≤ |(k : ℝ) - (n : ℝ) / 4|) with hW_def
  have hmemW : ∀ k : ℕ, k ∈ W ↔ k < n ∧ |(k : ℝ) - (n : ℝ) / 4| < K * Real.sqrt n := by
    intro k
    simp only [hW_def, mem_filter, mem_range, not_le]
  have hWsub : W ⊆ Finset.Ico a c := by
    intro k hk
    obtain ⟨hkn, hkw⟩ := (hmemW k).mp hk
    obtain ⟨hkl, hkr⟩ := abs_lt.mp hkw
    rw [Finset.mem_Ico]
    constructor
    · rw [ha_def, Nat.add_one_le_iff, Nat.floor_lt hy0, hy_def]
      linarith
    · rw [hc_def, Nat.lt_add_one_iff]
      exact Nat.le_floor (by rw [hz_def]; linarith)
  have hIco_mem : ∀ k ∈ Finset.Ico a c, y < (k : ℝ) ∧ (k : ℝ) ≤ z := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have h1 : ⌊y⌋₊ < k := by omega
    have h2 : k ≤ ⌊z⌋₊ := by omega
    refine ⟨(Nat.floor_lt hy0).mp h1, le_trans ?_ (Nat.floor_le hz0)⟩
    exact_mod_cast h2
  have hIco_sub_range : Finset.Ico a c ⊆ range n := by
    intro k hk
    rw [mem_range]
    have h1 : (k : ℝ) < (n : ℝ) := lt_of_le_of_lt (hIco_mem k hk).2 hzn
    exact_mod_cast h1
  have hsdiff : ∀ k ∈ (Finset.Ico a c) \ W, (k : ℝ) = z := by
    intro k hk
    rw [Finset.mem_sdiff] at hk
    obtain ⟨hkIco, hkW⟩ := hk
    obtain ⟨hky, hkz⟩ := hIco_mem k hkIco
    by_contra hne
    apply hkW
    rw [hmemW]
    refine ⟨mem_range.mp (hIco_sub_range hkIco), ?_⟩
    rw [abs_lt]
    constructor
    · rw [hy_def] at hky; linarith
    · have h1 : (k : ℝ) < z := lt_of_le_of_ne hkz hne
      rw [hz_def] at h1; linarith
  have hdiff_card : ((Finset.Ico a c) \ W).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro p hp p' hp'
    have h1 := hsdiff p hp
    have h2 := hsdiff p' hp'
    have h3 : (p : ℝ) = (p' : ℝ) := by rw [h1, h2]
    exact_mod_cast h3
  have hIco_card : ((Finset.Ico a c).card : ℝ) ≤ 2 * K * Real.sqrt n + 1 := by
    rw [Nat.card_Ico]
    have h1 : ((c - a : ℕ) : ℝ) = (c : ℝ) - (a : ℝ) := by
      rw [Nat.cast_sub hac]
    rw [h1]
    linarith [hya, hcz]
  -- lattice endpoint bounds
  have hxa_l : -(4 * K) < xP2 n a := by
    rw [hxP2_eq a]
    have h2 : -(K * Real.sqrt n) < (a : ℝ) - (n : ℝ) / 4 := by
      rw [hy_def] at hya; linarith
    have h3 := mul_lt_mul_of_pos_right h2 hδ0
    rw [neg_mul, hKδ] at h3
    exact h3
  have hxa_u : xP2 n a ≤ -(4 * K) + δ := by
    rw [hxP2_eq a]
    have h2 : (a : ℝ) - (n : ℝ) / 4 ≤ -(K * Real.sqrt n) + 1 := by
      rw [hy_def] at hay; linarith
    have h3 := mul_le_mul_of_nonneg_right h2 hδ0.le
    rw [add_mul, neg_mul, hKδ, one_mul] at h3
    exact h3
  have hxc_l : 4 * K < xP2 n c := by
    rw [hxP2_eq c]
    have h2 : K * Real.sqrt n < (c : ℝ) - (n : ℝ) / 4 := by
      rw [hz_def] at hzc; linarith
    have h3 := mul_lt_mul_of_pos_right h2 hδ0
    rw [hKδ] at h3
    exact h3
  have hxc_u : xP2 n c ≤ 4 * K + δ := by
    rw [hxP2_eq c]
    have h2 : (c : ℝ) - (n : ℝ) / 4 ≤ K * Real.sqrt n + 1 := by
      rw [hz_def] at hcz; linarith
    have h3 := mul_le_mul_of_nonneg_right h2 hδ0.le
    rw [add_mul, hKδ, one_mul] at h3
    exact h3
  -- the chain quantities
  set P₀ : ℝ := pmf' n ⌊(n : ℝ) / 4⌋₊ with hP₀_def
  set q : ℝ := 1 / Real.sqrt (2 * Real.pi) with hq_def
  have hq0 : 0 ≤ q := by rw [hq_def]; positivity
  have hq1 : q ≤ 1 := by rw [hq_def]; exact one_div_sqrt_two_pi_le_one
  set G : ℕ → ℂ := fun k => gaussFourierKernel t (xP2 n k) with hG_def
  set T1 : ℂ := ∑ k ∈ W, charP2muTerm n t k with hT1
  set T2 : ℂ := (P₀ : ℂ) * ∑ k ∈ W, G k with hT2
  set T3 : ℂ := (q : ℂ) * ((δ : ℂ) * ∑ k ∈ W, G k) with hT3
  set T4 : ℂ := (q : ℂ) * ((δ : ℂ) * ∑ k ∈ Finset.Ico a c, G k) with hT4
  set T5 : ℂ := (q : ℂ) * ∫ x in (xP2 n a)..(xP2 n c), gaussFourierKernel t x with hT5
  set T6 : ℂ := ∫ x in (-(4 * K))..(4 * K), gaussFourierIntegrand t x with hT6
  -- (0) off-window block
  have hb0 : ‖charP2mu n t - T1‖
      ≤ ∑ k ∈ (range n).filter
          (fun k : ℕ => K * Real.sqrt n ≤ |(k : ℝ) - (n : ℝ) / 4|), pmf' n k := by
    have hWc : W = range n \ (range n).filter
        (fun k : ℕ => K * Real.sqrt n ≤ |(k : ℝ) - (n : ℝ) / 4|) := by
      rw [hW_def]; exact Finset.filter_not _ _
    have hsum := Finset.sum_sdiff (f := charP2muTerm n t)
      (Finset.filter_subset
        (fun k : ℕ => K * Real.sqrt n ≤ |(k : ℝ) - (n : ℝ) / 4|) (range n))
    have hthis : charP2mu n t - T1
        = ∑ k ∈ (range n).filter
            (fun k : ℕ => K * Real.sqrt n ≤ |(k : ℝ) - (n : ℝ) / 4|),
              charP2muTerm n t k := by
      rw [charP2mu_eq_sum_term, ← hsum, hT1, hWc]
      ring
    rw [hthis]
    exact norm_sum_charP2muTerm_le n t _
  -- (1) window comparison to the Gaussian summand
  have hWk : ∀ k ∈ W, |(k : ℝ) - (n : ℝ) / 4| ≤ K * Real.sqrt n :=
    fun k hk => ((hmemW k).mp hk).2.le
  have hb1 : ‖T1 - T2‖
      ≤ Real.exp ((10000 * K * (1 + K ^ 2) + 16 * K + 8) / Real.sqrt n) - 1 := by
    rw [hT1, hT2, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ k ∈ W,
        ‖charP2muTerm n t k - (P₀ : ℂ) * G k‖
          ≤ pmf' n k *
            (Real.exp ((10000 * K * (1 + K ^ 2) + 16 * K + 8) / Real.sqrt n) - 1) := by
      intro k hk
      have hdiff : charP2muTerm n t k - (P₀ : ℂ) * G k
          = Complex.ofReal (pmf' n k - P₀ * Real.exp (-xP2 n k ^ 2 / 2)) *
              Complex.exp (Complex.I * Complex.ofReal (t * xP2 n k)) := by
        rw [charP2muTerm_eq_xP2]
        simp only [hG_def, gaussFourierKernel]
        push_cast
        ring
      rw [hdiff, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      exact pmf'_window_gauss_est hK hthr (hWk k hk)
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul]
    have hWle1 : ∑ k ∈ W, pmf' n k ≤ 1 := by
      rw [← hnorm n hn1]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => pmf'_nonneg n k)
      rw [hW_def]; exact Finset.filter_subset _ _
    have hexp1 : 0 ≤ Real.exp ((10000 * K * (1 + K ^ 2) + 16 * K + 8) / Real.sqrt n) - 1 := by
      have h1 : (0 : ℝ) ≤ (10000 * K * (1 + K ^ 2) + 16 * K + 8) / Real.sqrt n := by
        positivity
      have h2 := Real.add_one_le_exp ((10000 * K * (1 + K ^ 2) + 16 * K + 8) / Real.sqrt n)
      linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hWle1) hexp1]
  -- (2) prefactor swap
  have hsumG : ‖∑ k ∈ W, G k‖ ≤ ((Finset.Ico a c).card : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ W, ‖G k‖ ≤ ∑ k ∈ W, 1 :=
          Finset.sum_le_sum (fun k _ => by
            simp only [hG_def]; exact norm_gaussFourierKernel_le_one t _)
      _ = (W.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ((Finset.Ico a c).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hWsub
  have hδcard : δ * ((Finset.Ico a c).card : ℝ) ≤ 8 * K + 4 := by
    have h1 : δ * (2 * K * Real.sqrt n + 1) = 8 * K + δ := by
      rw [hδ_def]; field_simp; ring
    calc δ * ((Finset.Ico a c).card : ℝ) ≤ δ * (2 * K * Real.sqrt n + 1) :=
          mul_le_mul_of_nonneg_left hIco_card hδ0.le
      _ = 8 * K + δ := h1
      _ ≤ 8 * K + 4 := by linarith
  have hb2 : ‖T2 - T3‖ ≤ |sigmaP2 n * P₀ - q| * (8 * K + 4) := by
    have hfact : Complex.ofReal (sigmaP2 n * P₀ - q) * ((δ : ℂ) * ∑ k ∈ W, G k)
        = T2 - T3 := by
      rw [hT2, hT3]
      have h1 : (Complex.ofReal (sigmaP2 n) * (δ : ℂ)) = 1 := by
        rw [← Complex.ofReal_mul, hσδ, Complex.ofReal_one]
      calc Complex.ofReal (sigmaP2 n * P₀ - q) * ((δ : ℂ) * ∑ k ∈ W, G k)
          = (Complex.ofReal (sigmaP2 n) * (δ : ℂ)) * ((P₀ : ℂ) * ∑ k ∈ W, G k)
            - (q : ℂ) * ((δ : ℂ) * ∑ k ∈ W, G k) := by
            push_cast
            ring
        _ = (P₀ : ℂ) * ∑ k ∈ W, G k - (q : ℂ) * ((δ : ℂ) * ∑ k ∈ W, G k) := by
            rw [h1, one_mul]
    rw [← hfact, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0]
    calc δ * ‖∑ k ∈ W, G k‖ ≤ δ * ((Finset.Ico a c).card : ℝ) :=
          mul_le_mul_of_nonneg_left hsumG hδ0.le
      _ ≤ 8 * K + 4 := hδcard
  -- (3) window → interval hull (at most one boundary point)
  have hb3 : ‖T3 - T4‖ ≤ 4 / Real.sqrt n := by
    have hsd : ∑ k ∈ Finset.Ico a c, G k - ∑ k ∈ W, G k
        = ∑ k ∈ (Finset.Ico a c) \ W, G k := by
      rw [← Finset.sum_sdiff hWsub]
      ring
    have hnorm_sd : ‖∑ k ∈ (Finset.Ico a c) \ W, G k‖ ≤ 1 := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ k ∈ (Finset.Ico a c) \ W, ‖G k‖ ≤ ∑ k ∈ (Finset.Ico a c) \ W, 1 :=
            Finset.sum_le_sum (fun k _ => by
              simp only [hG_def]; exact norm_gaussFourierKernel_le_one t _)
        _ = ((((Finset.Ico a c) \ W).card : ℕ) : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ 1 := by exact_mod_cast hdiff_card
    have hdiffT : T3 - T4 = -((q : ℂ) * ((δ : ℂ) * ∑ k ∈ (Finset.Ico a c) \ W, G k)) := by
      rw [hT3, hT4, ← hsd]
      ring
    rw [hdiffT, norm_neg, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hq0, abs_of_pos hδ0]
    calc q * (δ * ‖∑ k ∈ (Finset.Ico a c) \ W, G k‖) ≤ 1 * (δ * 1) := by
          refine mul_le_mul hq1 ?_ (by positivity) zero_le_one
          exact mul_le_mul_of_nonneg_left hnorm_sd hδ0.le
      _ = δ := by ring
      _ = 4 / Real.sqrt n := hδ_def
  -- (4) Riemann sum → interval integral on the hull
  have hb4 : ‖T4 - T5‖ ≤ (32 * K + 16) * (|t| + (4 * K + 1)) / Real.sqrt n := by
    set m : ℕ := c - a with hm_def
    have hmR : (m : ℝ) = (c : ℝ) - (a : ℝ) := by
      rw [hm_def, Nat.cast_sub hac]
    have hreindex : ∑ k ∈ Finset.Ico a c, G k
        = ∑ j ∈ range m, gaussFourierKernel t (xP2 n a + (j : ℝ) * δ) := by
      rw [hm_def, Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hG_def]
      rw [xP2_add n a j hn0, hδ_def]
    have hgrid_end : xP2 n a + (m : ℝ) * δ = xP2 n c := by
      rw [hmR, hxP2_eq a, hxP2_eq c]
      ring
    have hL0 : 0 ≤ |t| + (4 * K + 1) := by positivity
    have hLip : ∀ x ∈ Set.Icc (xP2 n a) (xP2 n a + (m : ℝ) * δ),
        ∀ x' ∈ Set.Icc (xP2 n a) (xP2 n a + (m : ℝ) * δ),
        ‖gaussFourierKernel t x - gaussFourierKernel t x'‖
          ≤ (|t| + (4 * K + 1)) * |x - x'| := by
      intro x hx x' hx'
      rw [hgrid_end] at hx hx'
      have hK4 : ∀ w ∈ Set.Icc (xP2 n a) (xP2 n c), |w| ≤ 4 * K + 1 := by
        intro w hw
        rw [abs_le]
        constructor
        · have := hw.1
          linarith [hxa_l]
        · have := hw.2
          linarith [hxc_u, hδ1]
      exact norm_gaussFourierKernel_sub_le t (hK4 x hx) (hK4 x' hx')
    have hriemann := norm_riemann_sum_sub_integral_le (continuous_gaussFourierKernel t)
      hL0 hδ0.le (xP2 n a) m hLip
    rw [hgrid_end] at hriemann
    have hmb : (m : ℝ) ≤ 2 * K * Real.sqrt n + 1 := by
      rw [hmR]
      have h1 : y = (n : ℝ) / 4 - K * Real.sqrt n := hy_def
      have h2 : z = (n : ℝ) / 4 + K * Real.sqrt n := hz_def
      linarith [hya, hcz]
    have hδsq : δ ^ 2 = 16 / (n : ℝ) := by
      rw [hδ_def, div_pow, hsq]
      norm_num
    have hkey : (2 * K * Real.sqrt n + 1) * 16 / (n : ℝ) ≤ (32 * K + 16) / Real.sqrt n := by
      rw [div_le_div_iff₀ hn0 hs0]
      have hexp : (2 * K * Real.sqrt n + 1) * 16 * Real.sqrt n
          = 32 * K * Real.sqrt n ^ 2 + 16 * Real.sqrt n := by ring
      rw [hexp, hsq]
      nlinarith [hsn, hK]
    have hmLδ : (m : ℝ) * ((|t| + (4 * K + 1)) * δ ^ 2)
        ≤ (32 * K + 16) * (|t| + (4 * K + 1)) / Real.sqrt n := by
      calc (m : ℝ) * ((|t| + (4 * K + 1)) * δ ^ 2)
          ≤ (2 * K * Real.sqrt n + 1) * ((|t| + (4 * K + 1)) * δ ^ 2) :=
            mul_le_mul_of_nonneg_right hmb (mul_nonneg hL0 (sq_nonneg δ))
        _ = (|t| + (4 * K + 1)) * ((2 * K * Real.sqrt n + 1) * 16 / (n : ℝ)) := by
            rw [hδsq]; ring
        _ ≤ (|t| + (4 * K + 1)) * ((32 * K + 16) / Real.sqrt n) :=
            mul_le_mul_of_nonneg_left hkey hL0
        _ = (32 * K + 16) * (|t| + (4 * K + 1)) / Real.sqrt n := by ring
    have hdiffT : T4 - T5
        = (q : ℂ) * ((δ : ℂ) * ∑ j ∈ range m,
              gaussFourierKernel t (xP2 n a + (j : ℝ) * δ)
            - ∫ x in (xP2 n a)..(xP2 n c), gaussFourierKernel t x) := by
      rw [hT4, hT5, hreindex]
      ring
    rw [hdiffT, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0]
    calc q * ‖(δ : ℂ) * ∑ j ∈ range m, gaussFourierKernel t (xP2 n a + (j : ℝ) * δ)
            - ∫ x in (xP2 n a)..(xP2 n c), gaussFourierKernel t x‖
        ≤ 1 * ‖(δ : ℂ) * ∑ j ∈ range m, gaussFourierKernel t (xP2 n a + (j : ℝ) * δ)
            - ∫ x in (xP2 n a)..(xP2 n c), gaussFourierKernel t x‖ :=
          mul_le_mul_of_nonneg_right hq1 (norm_nonneg _)
      _ = ‖(δ : ℂ) * ∑ j ∈ range m, gaussFourierKernel t (xP2 n a + (j : ℝ) * δ)
            - ∫ x in (xP2 n a)..(xP2 n c), gaussFourierKernel t x‖ := one_mul _
      _ ≤ (m : ℝ) * ((|t| + (4 * K + 1)) * δ ^ 2) := hriemann
      _ ≤ (32 * K + 16) * (|t| + (4 * K + 1)) / Real.sqrt n := hmLδ
  -- (5) hull → the fixed window ±4K
  have hb5 : ‖T5 - T6‖ ≤ 8 / Real.sqrt n := by
    have hi : ∀ u v : ℝ, IntervalIntegrable (gaussFourierKernel t) MeasureTheory.volume u v :=
      fun u v => (continuous_gaussFourierKernel t).intervalIntegrable u v
    have hsplit1 : (∫ x in (xP2 n a)..(xP2 n c), gaussFourierKernel t x)
        = (∫ x in (xP2 n a)..(4 * K), gaussFourierKernel t x)
          + ∫ x in (4 * K)..(xP2 n c), gaussFourierKernel t x :=
      (intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _)).symm
    have hsplit2 : (∫ x in (-(4 * K))..(4 * K), gaussFourierKernel t x)
        = (∫ x in (-(4 * K))..(xP2 n a), gaussFourierKernel t x)
          + ∫ x in (xP2 n a)..(4 * K), gaussFourierKernel t x :=
      (intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _)).symm
    have hT6' : T6 = (q : ℂ) * ∫ x in (-(4 * K))..(4 * K), gaussFourierKernel t x := by
      rw [hT6, intervalIntegral_gaussFourierIntegrand, hq_def]
    have hdiffT : T5 - T6
        = (q : ℂ) * ((∫ x in (4 * K)..(xP2 n c), gaussFourierKernel t x)
            - ∫ x in (-(4 * K))..(xP2 n a), gaussFourierKernel t x) := by
      rw [hT5, hT6', hsplit1, hsplit2]
      ring
    have hn1' : ‖∫ x in (4 * K)..(xP2 n c), gaussFourierKernel t x‖ ≤ δ := by
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 1)
        (fun x _ => norm_gaussFourierKernel_le_one t x)).trans ?_
      rw [one_mul, abs_of_nonneg (by linarith [hxc_l] : (0 : ℝ) ≤ xP2 n c - 4 * K)]
      linarith [hxc_u]
    have hn2' : ‖∫ x in (-(4 * K))..(xP2 n a), gaussFourierKernel t x‖ ≤ δ := by
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 1)
        (fun x _ => norm_gaussFourierKernel_le_one t x)).trans ?_
      rw [one_mul, abs_of_nonneg (by linarith [hxa_l] : (0 : ℝ) ≤ xP2 n a - -(4 * K))]
      linarith [hxa_u]
    have hsum2 : ‖(∫ x in (4 * K)..(xP2 n c), gaussFourierKernel t x)
        - ∫ x in (-(4 * K))..(xP2 n a), gaussFourierKernel t x‖ ≤ δ + δ :=
      (norm_sub_le _ _).trans (add_le_add hn1' hn2')
    rw [hdiffT, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0]
    calc q * ‖(∫ x in (4 * K)..(xP2 n c), gaussFourierKernel t x)
            - ∫ x in (-(4 * K))..(xP2 n a), gaussFourierKernel t x‖
        ≤ 1 * (δ + δ) := mul_le_mul hq1 hsum2 (norm_nonneg _) zero_le_one
      _ = 2 * δ := by ring
      _ = 8 / Real.sqrt n := by rw [hδ_def]; ring
  -- assemble the triangle chain
  have e : charP2mu n t - Complex.exp (-(t : ℂ) ^ 2 / 2)
      = (charP2mu n t - T1) + (T1 - T2) + (T2 - T3) + (T3 - T4) + (T4 - T5)
        + (T5 - T6) + (T6 - Complex.exp (-(t : ℂ) ^ 2 / 2)) := by ring
  have h7 := norm_add_le ((charP2mu n t - T1) + (T1 - T2) + (T2 - T3) + (T3 - T4)
    + (T4 - T5) + (T5 - T6)) (T6 - Complex.exp (-(t : ℂ) ^ 2 / 2))
  have h6 := norm_add_le ((charP2mu n t - T1) + (T1 - T2) + (T2 - T3) + (T3 - T4)
    + (T4 - T5)) (T5 - T6)
  have h5 := norm_add_le ((charP2mu n t - T1) + (T1 - T2) + (T2 - T3) + (T3 - T4))
    (T4 - T5)
  have h4 := norm_add_le ((charP2mu n t - T1) + (T1 - T2) + (T2 - T3)) (T3 - T4)
  have h3 := norm_add_le ((charP2mu n t - T1) + (T1 - T2)) (T2 - T3)
  have h2 := norm_add_le (charP2mu n t - T1) (T1 - T2)
  rw [e]
  have harith : 4 / Real.sqrt n + (32 * K + 16) * (|t| + (4 * K + 1)) / Real.sqrt n
      + 8 / Real.sqrt n
      = ((32 * K + 16) * (|t| + (4 * K + 1)) + 12) / Real.sqrt n := by ring
  linarith [hb0, hb1, hb2, hb3, hb4, hb5]

/-! ### The assembled ε-argument -/

/-- **The window Riemann-sum → Gaussian-Fourier-integral convergence**
(`charP2mu_tendsto`), assuming the two isolated limits: the normalisation
`hnorm`, the mode-prefactor limit `hpre`, and annulus negligibility `hann`.

Given `ε > 0`: choose `K₀` from `hann` at `ε/4`, enlarge `K` so that the
Gaussian truncation `‖∫_{−4K}^{4K} F − ∫ F‖ ≤ ε/4`
(`intervalIntegral_tendsto_integral`), note that the annulus mass is monotone
in `K`, and apply the quantitative `charP2mu_window_estimate`; the middle
errors vanish as `n → ∞`. -/
theorem charP2mu_tendsto_of_prefactor_annulus
    (hnorm : ∀ n : ℕ, 1 ≤ n → ∑ k ∈ Finset.range n, pmf' n k = 1)
    (hpre : Tendsto (fun n : ℕ => sigmaP2 n * pmf' n ⌊(n : ℝ) / 4⌋₊) atTop
      (𝓝 (1 / Real.sqrt (2 * Real.pi))))
    (hann : ∀ ε > 0, ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ n : ℕ in atTop,
      ∑ k ∈ (Finset.range n).filter
        (fun k : ℕ => K * Real.sqrt n ≤ |(k : ℝ) - n / 4|), pmf' n k ≤ ε)
    (t : ℝ) :
    Tendsto (fun n : ℕ => charP2mu n t) atTop
      (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
  have key : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ‖charP2mu n t - Complex.exp (-(t : ℂ) ^ 2 / 2)‖ ≤ ε := by
    intro ε hε
    obtain ⟨K₀, hK₀1, hK₀ann⟩ := hann (ε / 4) (by positivity)
    -- Gaussian truncation radius
    have hIcc : Tendsto (fun R : ℝ => ∫ x in (-R)..R, gaussFourierIntegrand t x) atTop
        (𝓝 (∫ x : ℝ, gaussFourierIntegrand t x)) :=
      intervalIntegral_tendsto_integral (integrable_gaussFourierIntegrand t)
        tendsto_neg_atTop_atBot tendsto_id
    have hIcc' : ∀ᶠ R : ℝ in atTop,
        ‖(∫ x in (-R)..R, gaussFourierIntegrand t x)
          - ∫ x : ℝ, gaussFourierIntegrand t x‖ ≤ ε / 4 := by
      have h1 := Metric.tendsto_nhds.mp hIcc (ε / 4) (by positivity)
      filter_upwards [h1] with R hR
      rw [← dist_eq_norm]
      exact hR.le
    obtain ⟨R₁, hR₁⟩ := eventually_atTop.mp hIcc'
    set K : ℝ := max K₀ (max (R₁ / 4) 1) with hK_def
    have hK1 : 1 ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
    have hKK₀ : K₀ ≤ K := le_max_left _ _
    have hR₁K : R₁ ≤ 4 * K := by
      have h1 : R₁ / 4 ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
      linarith
    -- annulus mass at the enlarged K (monotone in K)
    have hannK : ∀ᶠ n : ℕ in atTop,
        ∑ k ∈ (Finset.range n).filter
          (fun k : ℕ => K * Real.sqrt n ≤ |(k : ℝ) - n / 4|), pmf' n k ≤ ε / 4 := by
      filter_upwards [hK₀ann] with n hn
      refine le_trans ?_ hn
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => pmf'_nonneg n k)
      intro k hk
      rw [Finset.mem_filter] at hk ⊢
      refine ⟨hk.1, le_trans ?_ hk.2⟩
      exact mul_le_mul_of_nonneg_right hKK₀ (Real.sqrt_nonneg _)
    -- Gaussian truncation at ±4K
    have hgauss : ‖(∫ x in (-(4 * K))..(4 * K), gaussFourierIntegrand t x)
        - Complex.exp (-(t : ℂ) ^ 2 / 2)‖ ≤ ε / 4 := by
      have h1 := hR₁ (4 * K) hR₁K
      rwa [integral_gaussFourierIntegrand] at h1
    -- the vanishing middle errors
    have hsqrt_at : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun n : ℕ => 1 / Real.sqrt n) atTop (𝓝 0) := by
      simpa [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hsqrt_at
    have hmid1 : Tendsto (fun n : ℕ =>
        Real.exp ((10000 * K * (1 + K ^ 2) + 16 * K + 8) / Real.sqrt n) - 1)
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ =>
          (10000 * K * (1 + K ^ 2) + 16 * K + 8) / Real.sqrt n) atTop (𝓝 0) := by
        have h2 := hinv.const_mul (10000 * K * (1 + K ^ 2) + 16 * K + 8)
        rw [mul_zero] at h2
        simpa [div_eq_mul_inv] using h2
      have h3 : Tendsto (fun n : ℕ =>
          Real.exp ((10000 * K * (1 + K ^ 2) + 16 * K + 8) / Real.sqrt n)) atTop
          (𝓝 (Real.exp 0)) := (Real.continuous_exp.tendsto 0).comp h1
      rw [Real.exp_zero] at h3
      have h4 := h3.sub_const 1
      rw [sub_self] at h4
      exact h4
    have hmid2 : Tendsto (fun n : ℕ =>
        |sigmaP2 n * pmf' n ⌊(n : ℝ) / 4⌋₊ - 1 / Real.sqrt (2 * Real.pi)|
          * (8 * K + 4)) atTop (𝓝 0) := by
      have h1 := (hpre.sub_const (1 / Real.sqrt (2 * Real.pi))).abs
      rw [sub_self, abs_zero] at h1
      have h2 := h1.mul_const (8 * K + 4)
      rw [zero_mul] at h2
      exact h2
    have hmid3 : Tendsto (fun n : ℕ =>
        ((32 * K + 16) * (|t| + (4 * K + 1)) + 12) / Real.sqrt n) atTop (𝓝 0) := by
      have h1 := hinv.const_mul ((32 * K + 16) * (|t| + (4 * K + 1)) + 12)
      rw [mul_zero] at h1
      simpa [div_eq_mul_inv] using h1
    have hmid : Tendsto (fun n : ℕ =>
        (Real.exp ((10000 * K * (1 + K ^ 2) + 16 * K + 8) / Real.sqrt n) - 1)
          + |sigmaP2 n * pmf' n ⌊(n : ℝ) / 4⌋₊ - 1 / Real.sqrt (2 * Real.pi)|
              * (8 * K + 4)
          + ((32 * K + 16) * (|t| + (4 * K + 1)) + 12) / Real.sqrt n) atTop (𝓝 0) := by
      have h1 := (hmid1.add hmid2).add hmid3
      simpa using h1
    have hmid' : ∀ᶠ n : ℕ in atTop,
        (Real.exp ((10000 * K * (1 + K ^ 2) + 16 * K + 8) / Real.sqrt n) - 1)
          + |sigmaP2 n * pmf' n ⌊(n : ℝ) / 4⌋₊ - 1 / Real.sqrt (2 * Real.pi)|
              * (8 * K + 4)
          + ((32 * K + 16) * (|t| + (4 * K + 1)) + 12) / Real.sqrt n ≤ ε / 2 :=
      (hmid.eventually_lt_const (by positivity : (0 : ℝ) < ε / 2)).mono
        fun n hn => hn.le
    -- eventual threshold n ≥ (64K)²
    have hthr_ev : ∀ᶠ n : ℕ in atTop, (64 * K) ^ 2 ≤ (n : ℝ) :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop ((64 * K) ^ 2)
    filter_upwards [hannK, hmid', hthr_ev] with n hann_n hmid_n hthr_n
    have hest := charP2mu_window_estimate hnorm hK1 t hthr_n
    linarith [hest, hann_n, hmid_n, hgauss]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (key (ε / 2) (by positivity))
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (hN n hn) (by linarith)

/-- **Corollary through the proved assembly**
`leafCLT_charFun_of_charP2mu_tendsto`: under the closed form `hU`, the
normalisation `hnorm`, the prefactor limit `hpre` and annulus negligibility
`hann`, the characteristic function of the standardized double-pop count
converges to the Gaussian one: `charP2 n t → e^{−t²/2}`. -/
theorem leafCLT_charFun_of_prefactor_annulus
    (hU : ∀ m j : ℕ, 1 ≤ m → 2 * j + 1 ≤ m → m * U (m - 1) 1 j = pmfNum m j)
    (hnorm : ∀ n : ℕ, 1 ≤ n → ∑ k ∈ Finset.range n, pmf' n k = 1)
    (hpre : Tendsto (fun n : ℕ => sigmaP2 n * pmf' n ⌊(n : ℝ) / 4⌋₊) atTop
      (𝓝 (1 / Real.sqrt (2 * Real.pi))))
    (hann : ∀ ε > 0, ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ n : ℕ in atTop,
      ∑ k ∈ (Finset.range n).filter
        (fun k : ℕ => K * Real.sqrt n ≤ |(k : ℝ) - n / 4|), pmf' n k ≤ ε)
    (t : ℝ) :
    Tendsto (fun n : ℕ => charP2 n t) atTop
      (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))) :=
  leafCLT_charFun_of_charP2mu_tendsto hU t
    (charP2mu_tendsto_of_prefactor_annulus hnorm hpre hann t)

end MakinenAnalysis
