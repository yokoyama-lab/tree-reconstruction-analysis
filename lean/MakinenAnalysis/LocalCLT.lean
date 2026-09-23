import Mathlib
import MakinenAnalysis.LeafCount

/-!
# Local CLT for the double-pop count: the explicit law and its ratio analysis

Phases 4–5 of `README.md`: towards `leafCLT_charFun` (Proposition 12) via a
local-limit analysis of the explicit law

  `P(P₂ = k) = pmf' n k = C(n,k)·C(n−k,k+1)·2^(n−1−2k) / (n·catalan n)`

(the Lagrange-inversion closed form pinned in `LeafCount.lean`; note
`C(n−k, k+1) = C(n−k, n−1−2k)` by symmetry, `pmfNum_eq_closed` below).

## What is PROVED here

* `pmfNum_mul_ratio` / `pmf'_succ_mul` / `pmf'_ratio`: the **exact one-step
  ratio** `pmf'(n,k+1)/pmf'(n,k) = (n−2k−1)(n−2k−2) / (4(k+1)(k+2))`
  (pure `Nat.choose` algebra, zero analysis).
* `pmf'_mono_of_le` / `pmf'_anti_of_ge`: **unimodality with mode ≈ n/4**
  (increasing for `4k+8 ≤ n`, decreasing for `n ≤ 4k+4`).
* `pmfRatio_sub_one`: the exact first-order form
  `r − 1 = −((n/2)(8s+9) + 6s + 6)/(4(k+1)(k+2))`, `s = k − n/4`, exhibiting
  the Gaussian drift `log r ≈ −16s/n = −(k − μ)/σ²` with `σ² = n/16`.
* `log_pmfRatio_le` / `le_log_pmfRatio` / `log_pmf'_succ_sub`: elementary
  two-sided log bounds (`Real.log_le_sub_one_of_pos` and its inverse form).
* `EP2_sub_muP2_tendsto`: `E[P₂] − n/4 → −5/8` (so centering at `μ = n/4`
  differs from the exact mean `EP2` by `O(1)`, harmless at scale `√n`);
  `sigmaP2_sq`: `σ(n)² = n/16`; `VarP2_div_tendsto`: `Var[P₂]/n → 1/16`.
* `U_eq_zero_of_le_two_mul`: support bound `P₂ ≤ (n−1)/2` at the `U`-level.
* `charP2_eq_sum_U` / `sum_U_div_catalan`: the characteristic function of the
  standardised `P₂` **as a `k`-indexed sum against the exact law**
  (unconditional), and, **conditionally on the closed form** `U_mul_closed`
  (hypothesis `hU`), `charP2_eq_sum_pmf'` and `sum_pmf'_of_closed`
  (`Σ pmf' = 1`).

## Survey: the Mathlib v4.31.0 toolbox for the remaining analysis

### Stirling (`Mathlib.Analysis.SpecialFunctions.Stirling`, namespace `Stirling`)

* `stirlingSeq (n : ℕ) : ℝ := n ! / (√(2 * n) * (n / exp 1) ^ n)`.
* `tendsto_stirlingSeq_sqrt_pi : Tendsto stirlingSeq atTop (𝓝 (√π))` — the
  main theorem.
* `factorial_isEquivalent_stirling :
    (fun n ↦ n ! : ℕ → ℝ) ~[atTop] fun n ↦ √(2 * n * π) * (n / exp 1) ^ n`
  — Stirling as `Asymptotics.IsEquivalent`; `IsEquivalent.div/mul` then give
  the asymptotics of any fixed rational expression in factorials, which is
  exactly what the pointwise local limit needs (each of `C(n,k)`,
  `C(n−k,k+1)` is a ratio of three factorials).
* Effective bounds (all `n`, not just eventually):
  `sqrt_pi_le_stirlingSeq : n ≠ 0 → √π ≤ stirlingSeq n`,
  `le_factorial_stirling : √(2πn)·(n/e)^n ≤ n !`,
  `le_log_factorial_stirling : n log n − n + (log n)/2 + (log 2π)/2 ≤ log n !`,
  and monotonicity `stirlingSeq'_antitone` with the Robbins-type successive
  bound `log_stirlingSeq_sdiff_le (n) : … ≤ 1/(4k(k+1)) …` — together these
  give **two-sided nonasymptotic** `n!` bounds
  (`√(2πn)(n/e)^n ≤ n! ≤ e^{1/12-ish}·√(2πn)(n/e)^n` after summing).

### Central binomial / choose bounds (`Mathlib.Data.Nat.Choose.Central`)

* `Nat.centralBinom_le_four_pow : centralBinom n ≤ 4 ^ n`,
  `Nat.four_pow_lt_mul_centralBinom : 4 ≤ n → 4 ^ n < n * centralBinom n`,
  `Nat.four_pow_le_two_mul_self_mul_centralBinom`.
  With `succ_mul_catalan_eq_centralBinom : (n+1)·catalan n = centralBinom n`
  these give `4^n/(n(n+1)) ≤ catalan n ≤ 4^n/(n+1)` — enough for crude
  exponential-scale control of the denominator `n·catalan n`; the sharp
  `catalan n ∼ 4^n/(√π n^{3/2})` must come from Stirling (not in Mathlib).
* Exact ratio recurrences (used below):
  `Nat.choose_succ_right_eq : C(n,k+1)·(k+1) = C(n,k)·(n−k)`,
  `Nat.succ_mul_choose_eq : (n+1)·C(n,k) = C(n+1,k+1)·(k+1)`.

### Specific limits / log expansions

* `Mathlib.Analysis.SpecificLimits.{Basic,Normed}`:
  `tendsto_pow_atTop_nhds_zero_of_lt_one`, geometric series, and
  `tendsto_inv_atTop_zero`, `Real.tendsto_sqrt_atTop` (used already in
  `LeafCount`).
* `Complex.tendsto_one_add_div_pow_exp : (1 + t/n)^n → exp t` and the o-form
  `Complex.tendsto_pow_exp_of_isLittleO_sub_add_div :
     (f − (1 + t/n)) =o[atTop] (1/n) → f^n → exp t`
  (`Mathlib.Analysis.SpecialFunctions.Complex.LogBounds`) — the engine of
  Mathlib's own CLT; directly reusable for product-form charFun estimates.
* `Real.abs_log_sub_add_sum_range_le : |x| < 1 →
     |Σ_{i<m} x^{i+1}/(i+1) + log (1−x)| ≤ |x|^{m+1}/(1−|x|)`
  (`Mathlib.Analysis.SpecialFunctions.Log.Deriv`) — with `m = 1` this is the
  quantitative `|log(1−x) + x| ≤ x²/(1−|x|)` needed for
  `log_pmfRatio_taylor` below.
* `Real.log_le_sub_one_of_pos`, `Real.one_sub_inv_le_log_of_pos`,
  `Real.add_one_le_exp` — the crude sandwich, used here.

### charFun / CLT infrastructure

* `MeasureTheory.Measure.LevyConvergence`:
  `ProbabilityMeasure.tendsto_iff_tendsto_charFun` (Lévy continuity), the
  bridge from `leafCLT_charFun` back to Proposition 12 proper.
* `Mathlib.Probability.CentralLimitTheorem` (new): a **finished iid CLT**
  `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`, built on
  `taylor_charFun_two` (second-order charFun Taylor expansion,
  `Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion`).
  Not directly applicable — `P₂` under the uniform Catalan law is **not** an
  iid sum — but `taylor_charFun_two` + `tendsto_pow_exp_of_isLittleO_sub_add_div`
  is the pattern to imitate for a triangular-array/exchangeable-pairs variant.

## Route assessment (see also final section)

1. **Stirling pointwise local limit + summation** (scaffolded here): ratio
   lemma (proved) ⇒ unimodality (proved) ⇒ Stirling at `k = n/4 + O(√n)`
   (`pmf'_local_limit`, wanted) ⇒ dominated summation using unimodality +
   `Σ pmf' = 1` (`leafCLT_charFun_of_local_limit`, wanted). All ingredients
   are elementary; the missing analysis is a Riemann-sum argument.
2. **Direct charFun product estimate**: no product structure available for
   this law — ruled out.
3. **Bernoulli decomposition**: would need a combinatorial coupling of `P₂`
   with an iid array; not visible from the codeword recursion.
Route 1 is the viable one; its only genuinely hard step is uniformity of the
Stirling estimate over the `O(√n)` window, which the exact ratio form
(`pmf'_ratio` + `log_pmfRatio_taylor`) reduces to summing explicit rational
bounds — no further special-function input needed.
-/

namespace MakinenAnalysis

open Finset Filter Topology

/-! ### The explicit law, centering and scaling -/

/-- Integer numerator of the closed-form law of `P₂`:
`pmfNum n k = C(n,k)·C(n−k,k+1)·2^(n−1−2k)` (equal to `n · U (n−1) 1 k` by
the Lagrange-inversion identity `U_mul_closed`, machine-checked for `n ≤ 8`
below).  The binomial `C(n−k,k+1)` is the symmetric twin of the
`C(n−k, n−1−2k)` in `LeafCount` (`pmfNum_eq_closed`) — this form makes the
one-step ratio exact algebra. -/
def pmfNum (n k : ℕ) : ℕ :=
  n.choose k * (n - k).choose (k + 1) * 2 ^ (n - 1 - 2 * k)

/-- The explicit pmf of the double-pop count as a real function:
`pmf' n k = pmfNum n k / (n · catalan n)`. -/
noncomputable def pmf' (n k : ℕ) : ℝ :=
  (pmfNum n k : ℝ) / ((n : ℝ) * (catalan n : ℝ))

/-- Asymptotic centering: `μ(n) = n/4`.  The exact mean is
`EP2 n = (n−1)(n−2)/(2(2n−1))` and `EP2 n − n/4 → −5/8`
(`EP2_sub_muP2_tendsto`), so the two centerings agree at scale `√n`. -/
noncomputable def muP2 (n : ℕ) : ℝ := (n : ℝ) / 4

/-- Asymptotic scaling: `σ(n) = √n/4`, i.e. `σ² = n/16`
(`sigmaP2_sq`; justified by `Var[P₂]/n → 1/16`, `VarP2_div_tendsto`). -/
noncomputable def sigmaP2 (n : ℕ) : ℝ := Real.sqrt n / 4

/-- The exact one-step ratio of the law as a rational function:
`pmfRatio n k = (n−2k−1)(n−2k−2) / (4(k+1)(k+2))`
(`= pmf' n (k+1) / pmf' n k`, `pmf'_ratio`). -/
noncomputable def pmfRatio (n k : ℕ) : ℝ :=
  (((n : ℝ) - 2 * k - 1) * ((n : ℝ) - 2 * k - 2))
    / (4 * ((k : ℝ) + 1) * ((k : ℝ) + 2))

/-! ### Basic structure of `pmfNum` -/

/-- `pmfNum` agrees with the multiplicative closed form of `LeafCount`
(`U_mul_closed`'s right-hand side) on the support. -/
lemma pmfNum_eq_closed (n k : ℕ) (h : 2 * k + 1 ≤ n) :
    pmfNum n k = n.choose k * (n - k).choose (n - 1 - 2 * k) * 2 ^ (n - 1 - 2 * k) := by
  unfold pmfNum
  rw [show n - 1 - 2 * k = n - k - (k + 1) by omega,
    Nat.choose_symm (by omega : k + 1 ≤ n - k)]

/-- Outside the support (`k > (n−1)/2`) the numerator vanishes. -/
lemma pmfNum_eq_zero {n k : ℕ} (h : n < 2 * k + 1) : pmfNum n k = 0 := by
  unfold pmfNum
  rw [Nat.choose_eq_zero_of_lt (by omega : n - k < k + 1), mul_zero, zero_mul]

/-- On the support the numerator is positive. -/
lemma pmfNum_pos {n k : ℕ} (h : 2 * k + 1 ≤ n) : 0 < pmfNum n k :=
  Nat.mul_pos
    (Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega : k + 1 ≤ n - k)))
    (pow_pos (by norm_num) _)

/-- Kernel-checked sanity: `pmfNum` is exactly `n · U (n−1) 1 k` for all
`n ≤ 8` (the Lagrange-inversion identity `U_mul_closed` of `LeafCount`,
restated through `pmfNum`). -/
example : ∀ n < 9, ∀ k < 5, 2 * k + 1 ≤ n → n * U (n - 1) 1 k = pmfNum n k := by
  decide

/-- Numeric sanity for the ratio: `pmfRatio 8 1 = (8−3)(8−4)/(4·2·3) = 5/6`. -/
example : pmfRatio 8 1 = 5 / 6 := by norm_num [pmfRatio]

/-- Numeric sanity for the exact mean: `EP2 4 = 3·2/(2·7) = 3/7`. -/
example : EP2 4 = 3 / 7 := by norm_num [EP2]

lemma catalan_pos' (n : ℕ) : 0 < catalan n := by
  have h1 := succ_mul_catalan_eq_centralBinom n
  have h2 := Nat.centralBinom_pos n
  rcases Nat.eq_zero_or_pos (catalan n) with h0 | h0
  · rw [h0, mul_zero] at h1; omega
  · exact h0

lemma pmf'_nonneg (n k : ℕ) : 0 ≤ pmf' n k :=
  div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

lemma pmf'_pos {n k : ℕ} (h : 2 * k + 1 ≤ n) : 0 < pmf' n k := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hcat : (0 : ℝ) < (catalan n : ℝ) := by exact_mod_cast catalan_pos' n
  exact div_pos (by exact_mod_cast pmfNum_pos h) (mul_pos hn hcat)

/-! ### Centering and scaling constants

The exact mean is `EP2 n = (n−1)(n−2)/(2(2n−1))` (`LeafCount`, from
Theorem 5); the exact variance `VarP2 n = n(n+1)(n−1)(n−2)/(2(2n−1)²(2n−3))`
(`Asymptotics`, eq. `varcov`).  We pin `μ = n/4` and `σ² = n/16` against
them. -/

/-- `σ(n)² = n/16`. -/
lemma sigmaP2_sq (n : ℕ) : sigmaP2 n ^ 2 = (n : ℝ) / 16 := by
  rw [sigmaP2, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  norm_num

/-- **The exact mean is `n/4 + O(1)`**: `EP2 n − μ(n) → −5/8`.  Hence the
standardisations by `EP2` (as in `charP2`) and by `n/4` differ by `O(1/√n)`
and are interchangeable in all CLT statements. -/
theorem EP2_sub_muP2_tendsto :
    Tendsto (fun n : ℕ => EP2 n - muP2 n) atTop (𝓝 (-(5 / 8))) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => (-5 + 4 * ((n : ℝ))⁻¹) / (8 - 4 * ((n : ℝ))⁻¹))
      atTop (𝓝 (-(5 / 8))) := by
    have h := (tendsto_const_nhds (α := ℕ) (x := (-5 : ℝ)) (f := atTop)).add
      (hinv.const_mul 4) |>.div
      (((tendsto_const_nhds (α := ℕ) (x := (8 : ℝ)) (f := atTop))).sub
        (hinv.const_mul 4)) (by norm_num)
    convert h using 2 <;> norm_num
  refine Tendsto.congr' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hy : ((n : ℝ))⁻¹ * (n : ℝ) = 1 := inv_mul_cancel₀ hn0
  have h2 : (0 : ℝ) < 2 * (2 * (n : ℝ) - 1) := by nlinarith
  have h8 : (0 : ℝ) < 8 - 4 * ((n : ℝ))⁻¹ := by
    have hpos : 0 < ((n : ℝ))⁻¹ := by positivity
    have hle : ((n : ℝ))⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]; right; exact hn1
    nlinarith
  have hd1 : (0 : ℝ) < 8 * (n : ℝ) - 4 := by nlinarith
  have step1 : (-5 + 4 * ((n : ℝ))⁻¹) / (8 - 4 * ((n : ℝ))⁻¹)
      = (-5 * (n : ℝ) + 4) / (8 * (n : ℝ) - 4) := by
    rw [div_eq_div_iff h8.ne' hd1.ne']
    linear_combination (12 : ℝ) * hy
  rw [step1]
  simp only [EP2, muP2]
  rw [div_sub_div _ _ h2.ne' (by norm_num : (4 : ℝ) ≠ 0),
    div_eq_div_iff hd1.ne' (mul_pos h2 (by norm_num : (0 : ℝ) < 4)).ne']
  ring

/-- **The variance scale**: `Var[P₂]/n → 1/16 = σ(n)²/n`. -/
theorem VarP2_div_tendsto :
    Tendsto (fun n : ℕ => VarP2 n / (n : ℝ)) atTop (𝓝 (1 / 16)) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ =>
      ((1 + ((n : ℝ))⁻¹) * (1 - ((n : ℝ))⁻¹) * (1 - 2 * ((n : ℝ))⁻¹))
        / (2 * (2 - ((n : ℝ))⁻¹) ^ 2 * (2 - 3 * ((n : ℝ))⁻¹)))
      atTop (𝓝 (1 / 16)) := by
    have hnum : Tendsto (fun n : ℕ =>
        (1 + ((n : ℝ))⁻¹) * (1 - ((n : ℝ))⁻¹) * (1 - 2 * ((n : ℝ))⁻¹))
        atTop (𝓝 ((1 + 0) * (1 - 0) * (1 - 2 * 0))) :=
      ((tendsto_const_nhds.add hinv).mul (tendsto_const_nhds.sub hinv)).mul
        (tendsto_const_nhds.sub (hinv.const_mul 2))
    have hden : Tendsto (fun n : ℕ =>
        2 * (2 - ((n : ℝ))⁻¹) ^ 2 * (2 - 3 * ((n : ℝ))⁻¹))
        atTop (𝓝 (2 * (2 - 0) ^ 2 * (2 - 3 * 0))) :=
      (((tendsto_const_nhds.sub hinv).pow 2).const_mul 2).mul
        (tendsto_const_nhds.sub (hinv.const_mul 3))
    have hval : ((1 : ℝ) + 0) * (1 - 0) * (1 - 2 * 0)
        / (2 * (2 - 0) ^ 2 * (2 - 3 * 0)) = 1 / 16 := by norm_num
    rw [← hval]
    exact hnum.div hden (by norm_num)
  refine Tendsto.congr' ?_ hlim
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hypos : (0 : ℝ) < ((n : ℝ))⁻¹ := by positivity
  have h1 : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
  have h3 : (0 : ℝ) < 2 * (n : ℝ) - 3 := by linarith
  -- pull one `n⁻¹` into each linear factor
  have f1 : (1 : ℝ) + ((n : ℝ))⁻¹ = ((n : ℝ) + 1) * ((n : ℝ))⁻¹ := by
    rw [add_mul, one_mul, mul_inv_cancel₀ hn0]
  have f2 : (1 : ℝ) - ((n : ℝ))⁻¹ = ((n : ℝ) - 1) * ((n : ℝ))⁻¹ := by
    rw [sub_mul, one_mul, mul_inv_cancel₀ hn0]
  have f3 : (1 : ℝ) - 2 * ((n : ℝ))⁻¹ = ((n : ℝ) - 2) * ((n : ℝ))⁻¹ := by
    rw [sub_mul, mul_inv_cancel₀ hn0]
  have f4 : (2 : ℝ) - ((n : ℝ))⁻¹ = (2 * (n : ℝ) - 1) * ((n : ℝ))⁻¹ := by
    rw [sub_mul, one_mul, mul_assoc, mul_inv_cancel₀ hn0, mul_one]
  have f5 : (2 : ℝ) - 3 * ((n : ℝ))⁻¹ = (2 * (n : ℝ) - 3) * ((n : ℝ))⁻¹ := by
    rw [sub_mul, mul_assoc, mul_inv_cancel₀ hn0, mul_one]
  have hB : (0 : ℝ) < 2 * (2 * (n : ℝ) - 1) ^ 2 * (2 * (n : ℝ) - 3) :=
    mul_pos (mul_pos (by norm_num) (pow_pos h1 2)) h3
  have hAB : VarP2 n / (n : ℝ)
      = ((n : ℝ) + 1) * ((n : ℝ) - 1) * ((n : ℝ) - 2)
        / (2 * (2 * (n : ℝ) - 1) ^ 2 * (2 * (n : ℝ) - 3)) := by
    simp only [VarP2]
    rw [div_div, div_eq_div_iff (mul_ne_zero hB.ne' hn0) hB.ne']
    ring
  rw [f1, f2, f3, f4, f5, hAB]
  have hden1 : (0 : ℝ) < 2 * ((2 * (n : ℝ) - 1) * ((n : ℝ))⁻¹) ^ 2
      * ((2 * (n : ℝ) - 3) * ((n : ℝ))⁻¹) :=
    mul_pos (mul_pos (by norm_num) (pow_pos (mul_pos h1 hypos) 2))
      (mul_pos h3 hypos)
  rw [div_eq_div_iff hden1.ne' hB.ne']
  ring

/-! ### The exact one-step ratio (pure `choose` algebra)

`pmf'(n,k+1)/pmf'(n,k) = (n−2k−1)(n−2k−2)/(4(k+1)(k+2))`.  This is the
combinatorial heart of the local CLT: everything Gaussian about `P₂` is a
consequence of this rational function crossing `1` at `k ≈ n/4` with slope
`≈ −16/n` in log scale. -/

/-- Cross-multiplied ratio identity for the integer numerator, over `ℝ`. -/
theorem pmfNum_mul_ratio (n k : ℕ) (h : 2 * k + 3 ≤ n) :
    (pmfNum n (k + 1) : ℝ) * (4 * ((k : ℝ) + 1) * ((k : ℝ) + 2))
      = (pmfNum n k : ℝ) * (((n : ℝ) - 2 * k - 1) * ((n : ℝ) - 2 * k - 2)) := by
  -- the four `Nat.choose` recurrences
  have e1 := Nat.choose_succ_right_eq n k
  have e2 := Nat.choose_succ_right_eq (n - k) (k + 1)
  rw [show k + 1 + 1 = k + 2 by omega] at e2
  have e3 := Nat.add_one_mul_choose_eq (n - k - 1) (k + 2)
  rw [show n - k - 1 + 1 = n - k by omega, show k + 2 + 1 = k + 3 by omega] at e3
  have e4 := Nat.choose_succ_right_eq (n - k) (k + 2)
  rw [show k + 2 + 1 = k + 3 by omega] at e4
  -- cast the `ℕ`-subtractions
  have hcnk : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := by
    rw [Nat.cast_sub (by omega)]
  have hsub1 : ((n - k - (k + 1) : ℕ) : ℝ) = (n : ℝ) - 2 * k - 1 := by
    rw [show n - k - (k + 1) = n - (2 * k + 1) by omega, Nat.cast_sub (by omega)]
    push_cast; ring
  have hsub2 : ((n - k - (k + 2) : ℕ) : ℝ) = (n : ℝ) - 2 * k - 2 := by
    rw [show n - k - (k + 2) = n - (2 * k + 2) by omega, Nat.cast_sub (by omega)]
    push_cast; ring
  have E1 : (n.choose (k + 1) : ℝ) * ((k : ℝ) + 1)
      = (n.choose k : ℝ) * ((n : ℝ) - k) := by
    rw [← hcnk]; exact_mod_cast e1
  have E2 : ((n - k).choose (k + 2) : ℝ) * ((k : ℝ) + 2)
      = ((n - k).choose (k + 1) : ℝ) * ((n : ℝ) - 2 * k - 1) := by
    rw [← hsub1]; exact_mod_cast e2
  have E3 : ((n : ℝ) - k) * ((n - k - 1).choose (k + 2) : ℝ)
      = ((n - k).choose (k + 3) : ℝ) * ((k : ℝ) + 3) := by
    rw [← hcnk]; exact_mod_cast e3
  have E4 : ((n - k).choose (k + 3) : ℝ) * ((k : ℝ) + 3)
      = ((n - k).choose (k + 2) : ℝ) * ((n : ℝ) - 2 * k - 2) := by
    rw [← hsub2]; exact_mod_cast e4
  -- expand `pmfNum` on both sides, sharing the power of two
  have hP1 : (pmfNum n (k + 1) : ℝ)
      = (n.choose (k + 1) : ℝ) * ((n - k - 1).choose (k + 2) : ℝ)
        * (2 : ℝ) ^ (n - 1 - 2 * (k + 1)) := by
    unfold pmfNum
    rw [show n - (k + 1) = n - k - 1 by omega]
    push_cast
    ring
  have hP0 : (pmfNum n k : ℝ)
      = (n.choose k : ℝ) * ((n - k).choose (k + 1) : ℝ)
        * ((2 : ℝ) ^ (n - 1 - 2 * (k + 1)) * 4) := by
    unfold pmfNum
    rw [show n - 1 - 2 * k = n - 1 - 2 * (k + 1) + 2 by omega]
    push_cast [pow_add]
    ring
  have hnk : (0 : ℝ) < (n : ℝ) - k := by
    have : (k : ℝ) + 3 ≤ (n : ℝ) := by exact_mod_cast (by omega : k + 3 ≤ n)
    linarith
  -- multiply through by `(n − k)` and cancel
  have key : ((n : ℝ) - k)
        * ((pmfNum n (k + 1) : ℝ) * (4 * ((k : ℝ) + 1) * ((k : ℝ) + 2)))
      = ((n : ℝ) - k)
        * ((pmfNum n k : ℝ) * (((n : ℝ) - 2 * k - 1) * ((n : ℝ) - 2 * k - 2))) := by
    rw [hP1, hP0]
    linear_combination
      (4 * ((k : ℝ) + 2) * ((n : ℝ) - k) * ((n - k - 1).choose (k + 2) : ℝ)
        * (2 : ℝ) ^ (n - 1 - 2 * (k + 1))) * E1
      + (4 * (n.choose k : ℝ) * ((k : ℝ) + 2) * ((n : ℝ) - k)
        * (2 : ℝ) ^ (n - 1 - 2 * (k + 1))) * E3
      + (4 * (n.choose k : ℝ) * ((k : ℝ) + 2) * ((n : ℝ) - k)
        * (2 : ℝ) ^ (n - 1 - 2 * (k + 1))) * E4
      + (4 * (n.choose k : ℝ) * ((n : ℝ) - k) * ((n : ℝ) - 2 * k - 2)
        * (2 : ℝ) ^ (n - 1 - 2 * (k + 1))) * E2
  exact mul_left_cancel₀ hnk.ne' key

/-- The ratio identity at the pmf level (same denominator on both sides). -/
theorem pmf'_succ_mul (n k : ℕ) (h : 2 * k + 3 ≤ n) :
    pmf' n (k + 1) * (4 * ((k : ℝ) + 1) * ((k : ℝ) + 2))
      = pmf' n k * (((n : ℝ) - 2 * k - 1) * ((n : ℝ) - 2 * k - 2)) := by
  unfold pmf'
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, pmfNum_mul_ratio n k h]

/-- **The exact one-step ratio**:
`pmf'(n,k+1)/pmf'(n,k) = (n−2k−1)(n−2k−2)/(4(k+1)(k+2))` on the support. -/
theorem pmf'_ratio (n k : ℕ) (h : 2 * k + 3 ≤ n) :
    pmf' n (k + 1) / pmf' n k = pmfRatio n k := by
  have hpos : 0 < pmf' n k := pmf'_pos (by omega)
  have hden : (0 : ℝ) < 4 * ((k : ℝ) + 1) * ((k : ℝ) + 2) := by positivity
  rw [pmfRatio, div_eq_div_iff hpos.ne' hden.ne']
  linear_combination pmf'_succ_mul n k h

/-! ### Unimodality: the mode sits at `n/4 + O(1)` -/

/-- Left of `n/4 − 2` the law is nondecreasing: if `4k + 8 ≤ n` then
`pmf' n k ≤ pmf' n (k+1)`. -/
theorem pmf'_mono_of_le {n k : ℕ} (h : 4 * k + 8 ≤ n) :
    pmf' n k ≤ pmf' n (k + 1) := by
  have h3 : 2 * k + 3 ≤ n := by omega
  have hkey := pmf'_succ_mul n k h3
  have hden : (0 : ℝ) < 4 * ((k : ℝ) + 1) * ((k : ℝ) + 2) := by positivity
  have hn : (4 * (k : ℝ) + 8) ≤ (n : ℝ) := by exact_mod_cast h
  have hcmp : 4 * ((k : ℝ) + 1) * ((k : ℝ) + 2)
      ≤ ((n : ℝ) - 2 * k - 1) * ((n : ℝ) - 2 * k - 2) := by
    have a1 : (2 * (k : ℝ) + 7) ≤ (n : ℝ) - 2 * k - 1 := by linarith
    have a2 : (2 * (k : ℝ) + 6) ≤ (n : ℝ) - 2 * k - 2 := by linarith
    have hprod := mul_le_mul a1 a2 (by positivity) (by linarith)
    nlinarith
  have hstep : pmf' n k * (4 * ((k : ℝ) + 1) * ((k : ℝ) + 2))
      ≤ pmf' n (k + 1) * (4 * ((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
    rw [hkey]
    exact mul_le_mul_of_nonneg_left hcmp (pmf'_nonneg n k)
  exact le_of_mul_le_mul_right hstep hden

/-- Right of `n/4 − 1` the law is nonincreasing: if `2k+3 ≤ n ≤ 4k + 4` then
`pmf' n (k+1) ≤ pmf' n k`.  Together with `pmf'_mono_of_le` this locates the
mode in the window `[(n−8)/4, (n−1)/4]`, i.e. at `n/4 + O(1)`. -/
theorem pmf'_anti_of_ge {n k : ℕ} (h3 : 2 * k + 3 ≤ n) (h4 : n ≤ 4 * k + 4) :
    pmf' n (k + 1) ≤ pmf' n k := by
  have hkey := pmf'_succ_mul n k h3
  have hden : (0 : ℝ) < 4 * ((k : ℝ) + 1) * ((k : ℝ) + 2) := by positivity
  have hn3 : (2 * (k : ℝ) + 3) ≤ (n : ℝ) := by exact_mod_cast h3
  have hn4 : (n : ℝ) ≤ 4 * (k : ℝ) + 4 := by exact_mod_cast h4
  have hcmp : ((n : ℝ) - 2 * k - 1) * ((n : ℝ) - 2 * k - 2)
      ≤ 4 * ((k : ℝ) + 1) * ((k : ℝ) + 2) := by
    have a1 : (n : ℝ) - 2 * k - 1 ≤ 2 * (k : ℝ) + 3 := by linarith
    have a2 : (n : ℝ) - 2 * k - 2 ≤ 2 * (k : ℝ) + 2 := by linarith
    have hpos2 : (0 : ℝ) ≤ (n : ℝ) - 2 * k - 2 := by linarith
    have hprod := mul_le_mul a1 a2 hpos2 (by positivity)
    nlinarith
  have hstep : pmf' n (k + 1) * (4 * ((k : ℝ) + 1) * ((k : ℝ) + 2))
      ≤ pmf' n k * (4 * ((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
    rw [hkey]
    exact mul_le_mul_of_nonneg_left hcmp (pmf'_nonneg n k)
  exact le_of_mul_le_mul_right hstep hden

/-! ### The log-ratio: Gaussian drift -/

lemma pmfRatio_pos {n k : ℕ} (h : 2 * k + 3 ≤ n) : 0 < pmfRatio n k := by
  have hn : (2 * (k : ℝ) + 3) ≤ (n : ℝ) := by exact_mod_cast h
  unfold pmfRatio
  apply div_pos
  · nlinarith
  · positivity

/-- Crude upper log bound: `log r ≤ r − 1`. -/
lemma log_pmfRatio_le {n k : ℕ} (h : 2 * k + 3 ≤ n) :
    Real.log (pmfRatio n k) ≤ pmfRatio n k - 1 :=
  Real.log_le_sub_one_of_pos (pmfRatio_pos h)

/-- Crude lower log bound: `1 − r⁻¹ ≤ log r`. -/
lemma le_log_pmfRatio {n k : ℕ} (h : 2 * k + 3 ≤ n) :
    1 - (pmfRatio n k)⁻¹ ≤ Real.log (pmfRatio n k) :=
  Real.one_sub_inv_le_log_of_pos (pmfRatio_pos h)

/-- The one-step log-increment of the law is exactly `log (pmfRatio n k)`. -/
lemma log_pmf'_succ_sub (n k : ℕ) (h : 2 * k + 3 ≤ n) :
    Real.log (pmf' n (k + 1)) - Real.log (pmf' n k)
      = Real.log (pmfRatio n k) := by
  rw [← Real.log_div (pmf'_pos (by omega : 2 * (k + 1) + 1 ≤ n)).ne'
      (pmf'_pos (by omega : 2 * k + 1 ≤ n)).ne', pmf'_ratio n k h]

/-- **Exact first-order form of the ratio.**  With `s = k − n/4`,
`r − 1 = −((n/2)(8s+9) + 6s + 6) / (4(k+1)(k+2))`, so `log r ≈ r − 1 ≈
−16s/n − 18/n = −(k − μ)/σ² + O(1/n)` with `σ² = n/16`: the Gaussian drift,
as an identity of rational functions (no hypotheses needed). -/
theorem pmfRatio_sub_one (n k : ℕ) :
    pmfRatio n k - 1
      = -(((n : ℝ) / 2) * (8 * ((k : ℝ) - (n : ℝ) / 4) + 9)
          + 6 * ((k : ℝ) - (n : ℝ) / 4) + 6)
        / (4 * ((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
  have hden : (4 * ((k : ℝ) + 1) * ((k : ℝ) + 2)) ≠ 0 := by positivity
  unfold pmfRatio
  field_simp
  ring

/-- Exact numerator of the Taylor remainder of the ratio: with `s = k − n/4`
and `D = 4(k+1)(k+2)`,
`r − 1 + 16s/n = (32ns² + 64s³ − (9/2)n² + 42ns − 6n + 192s² + 128s)/(D·n)`
(the `n²s` terms of `16s·D` and `−((n/2)(8s+9)+6s+6)·n` cancel; pure algebra
from `pmfRatio_sub_one`, only `n ≠ 0` is needed). -/
private lemma pmfRatio_taylor_num (n k : ℕ) (hn : 1 ≤ n) :
    pmfRatio n k - 1 + 16 * ((k : ℝ) - (n : ℝ) / 4) / (n : ℝ)
      = (32 * (n : ℝ) * ((k : ℝ) - (n : ℝ) / 4) ^ 2
          + 64 * ((k : ℝ) - (n : ℝ) / 4) ^ 3
          - 9 / 2 * (n : ℝ) ^ 2
          + 42 * (n : ℝ) * ((k : ℝ) - (n : ℝ) / 4)
          - 6 * (n : ℝ)
          + 192 * ((k : ℝ) - (n : ℝ) / 4) ^ 2
          + 128 * ((k : ℝ) - (n : ℝ) / 4))
        / (4 * ((k : ℝ) + 1) * ((k : ℝ) + 2) * (n : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hD : (4 * ((k : ℝ) + 1) * ((k : ℝ) + 2)) ≠ 0 := by positivity
  rw [pmfRatio_sub_one]
  field_simp
  ring

/-- Quantitative rational estimate: on the window `|k − n/4| ≤ n/64` (and
`64 ≤ n`) the Taylor remainder of the ratio obeys
`|r − 1 + 16s/n| ≤ 180(n + s²)/n²` (numerator `≤ 36n(n+s²)`, denominator
`D·n ≥ (225/1024)n³` since `k ≥ 15n/64` on the window). -/
private lemma pmfRatio_taylor_rational {n k : ℕ} (hn : 64 ≤ n)
    (hwin : |(k : ℝ) - (n : ℝ) / 4| ≤ (n : ℝ) / 64) :
    |pmfRatio n k - 1 + 16 * ((k : ℝ) - (n : ℝ) / 4) / (n : ℝ)|
      ≤ 180 * ((n : ℝ) + ((k : ℝ) - (n : ℝ) / 4) ^ 2) / (n : ℝ) ^ 2 := by
  have hnR : (64 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  obtain ⟨hs1, hs2⟩ := abs_le.mp hwin
  have hk : (15 : ℝ) / 64 * (n : ℝ) ≤ (k : ℝ) := by linarith
  have hD : (0 : ℝ) < 4 * ((k : ℝ) + 1) * ((k : ℝ) + 2) := by positivity
  have hDn : (0 : ℝ) < 4 * ((k : ℝ) + 1) * ((k : ℝ) + 2) * (n : ℝ) := mul_pos hD hn0
  have hDge : 225 / 1024 * (n : ℝ) ^ 2 ≤ 4 * ((k : ℝ) + 1) * ((k : ℝ) + 2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hk)
      (by positivity : (0 : ℝ) ≤ (k : ℝ) + 15 / 64 * (n : ℝ)),
      (by positivity : (0 : ℝ) ≤ (k : ℝ))]
  have h1 : (0 : ℝ) ≤ (n : ℝ) / 64 - ((k : ℝ) - (n : ℝ) / 4) := by linarith
  have h2 : (0 : ℝ) ≤ ((k : ℝ) - (n : ℝ) / 4) + (n : ℝ) / 64 := by linarith
  have h3 : (0 : ℝ) ≤ (n : ℝ) - 64 := by linarith
  have hnum : |32 * (n : ℝ) * ((k : ℝ) - (n : ℝ) / 4) ^ 2
      + 64 * ((k : ℝ) - (n : ℝ) / 4) ^ 3
      - 9 / 2 * (n : ℝ) ^ 2
      + 42 * (n : ℝ) * ((k : ℝ) - (n : ℝ) / 4)
      - 6 * (n : ℝ)
      + 192 * ((k : ℝ) - (n : ℝ) / 4) ^ 2
      + 128 * ((k : ℝ) - (n : ℝ) / 4)|
      ≤ 36 * (n : ℝ) * ((n : ℝ) + ((k : ℝ) - (n : ℝ) / 4) ^ 2) := by
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg (sq_nonneg ((k : ℝ) - (n : ℝ) / 4)) h2,
        mul_nonneg (sq_nonneg ((k : ℝ) - (n : ℝ) / 4)) h3,
        mul_nonneg hn0.le h2, mul_nonneg hn0.le h3,
        mul_nonneg hn0.le (sq_nonneg ((k : ℝ) - (n : ℝ) / 4)),
        sq_nonneg ((k : ℝ) - (n : ℝ) / 4)]
    · nlinarith [mul_nonneg (sq_nonneg ((k : ℝ) - (n : ℝ) / 4)) h1,
        mul_nonneg (sq_nonneg ((k : ℝ) - (n : ℝ) / 4)) h3,
        mul_nonneg hn0.le h1, mul_nonneg hn0.le h3,
        mul_nonneg hn0.le (sq_nonneg ((k : ℝ) - (n : ℝ) / 4)),
        sq_nonneg ((k : ℝ) - (n : ℝ) / 4)]
  rw [pmfRatio_taylor_num n k (by omega), abs_div, abs_of_pos hDn,
    div_le_div_iff₀ hDn (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)]
  have hA : |32 * (n : ℝ) * ((k : ℝ) - (n : ℝ) / 4) ^ 2
      + 64 * ((k : ℝ) - (n : ℝ) / 4) ^ 3
      - 9 / 2 * (n : ℝ) ^ 2
      + 42 * (n : ℝ) * ((k : ℝ) - (n : ℝ) / 4)
      - 6 * (n : ℝ)
      + 192 * ((k : ℝ) - (n : ℝ) / 4) ^ 2
      + 128 * ((k : ℝ) - (n : ℝ) / 4)| * (n : ℝ) ^ 2
      ≤ 36 * (n : ℝ) * ((n : ℝ) + ((k : ℝ) - (n : ℝ) / 4) ^ 2) * (n : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right hnum (sq_nonneg _)
  have hB : 180 * ((n : ℝ) + ((k : ℝ) - (n : ℝ) / 4) ^ 2)
        * (225 / 1024 * (n : ℝ) ^ 2 * (n : ℝ))
      ≤ 180 * ((n : ℝ) + ((k : ℝ) - (n : ℝ) / 4) ^ 2)
        * (4 * ((k : ℝ) + 1) * ((k : ℝ) + 2) * (n : ℝ)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hDge hn0.le)
      (by positivity)
  nlinarith [hA, hB,
    mul_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 3)
      (by positivity : (0 : ℝ) ≤ (n : ℝ) + ((k : ℝ) - (n : ℝ) / 4) ^ 2)]

/-- On the window `|k − n/4| ≤ n/64` (and `64 ≤ n`) the ratio is within `2/3`
of `1` — in particular `|1 − r| < 1`, so the log series applies at `x = 1 − r`. -/
private lemma abs_pmfRatio_sub_one_le {n k : ℕ} (hn : 64 ≤ n)
    (hwin : |(k : ℝ) - (n : ℝ) / 4| ≤ (n : ℝ) / 64) :
    |pmfRatio n k - 1| ≤ 2 / 3 := by
  have hnR : (64 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  obtain ⟨hs1, hs2⟩ := abs_le.mp hwin
  have hk : (15 : ℝ) / 64 * (n : ℝ) ≤ (k : ℝ) := by linarith
  have hk2 : (k : ℝ) ≤ 17 / 64 * (n : ℝ) := by linarith
  have hD : (0 : ℝ) < 4 * ((k : ℝ) + 1) * ((k : ℝ) + 2) := by positivity
  rw [pmfRatio_sub_one, abs_div, abs_neg, abs_of_pos hD, div_le_iff₀ hD, abs_le]
  constructor
  · nlinarith [mul_nonneg hn0.le (sub_nonneg.mpr hk),
      mul_nonneg (sub_nonneg.mpr hk)
        (by positivity : (0 : ℝ) ≤ (k : ℝ) + 15 / 64 * (n : ℝ)),
      (by positivity : (0 : ℝ) ≤ (k : ℝ)), mul_nonneg hn0.le hn0.le]
  · nlinarith [mul_nonneg hn0.le (sub_nonneg.mpr hk2),
      mul_nonneg (sub_nonneg.mpr hk)
        (by positivity : (0 : ℝ) ≤ (k : ℝ) + 15 / 64 * (n : ℝ)),
      (by positivity : (0 : ℝ) ≤ (k : ℝ)),
      mul_nonneg hn0.le (by linarith : (0 : ℝ) ≤ (n : ℝ) - 64)]

/-- Purely algebraic collection step for `log_pmfRatio_taylor`: if
`|e| ≤ 180b ≤ 3` and `f² ≤ 256b` then `3(e−f)² ≤ 4820b`
(`3(e−f)² ≤ 6e² + 6f² ≤ 6·540b + 6·256b = 4776b`). -/
private lemma taylor_sq_combine {e f b : ℝ} (hb : 0 ≤ b) (he : |e| ≤ 180 * b)
    (hb3 : 180 * b ≤ 3) (hf : f ^ 2 ≤ 256 * b) :
    3 * (e - f) ^ 2 ≤ 4820 * b := by
  have h0 : (0 : ℝ) ≤ |e| := abs_nonneg e
  have h1 : e ^ 2 ≤ 540 * b := by
    nlinarith [sq_abs e,
      mul_nonneg (sub_nonneg.mpr he)
        (add_nonneg (by linarith : (0 : ℝ) ≤ 180 * b) h0),
      mul_nonneg (sub_nonneg.mpr hb3) (by linarith : (0 : ℝ) ≤ 180 * b)]
  nlinarith [sq_nonneg (e + f), h1, hf, hb]

/-- **The quantitative log-ratio Taylor bound.**
On the central window `|k − n/4| ≤ n/64` the log-ratio matches the Gaussian
drift `−(k − μ)/σ² = −16(k − n/4)/n` to order `1/n` plus a quadratic error:

  `|log r + 16s/n| ≤ 5000·(n + s²)/n²`, `s = k − n/4`.

Deviations from the originally posted shape: the window is `n/64` instead of
`n/8` (still of width `Θ(n)`, so it eventually contains any `|s| ≤ K√n`
regime; the shrinkage keeps `|r − 1| ≤ 2/3 < 1`, as required by the log
series `Real.abs_log_sub_add_sum_range_le` at `x = 1 − r`), the threshold
`64 ≤ n` is assumed, and the constant is the explicit `C = 5000`
(`≤ 3(r−1)² + 180(n+s²)/n² ≤ (4820 + 180)(n+s²)/n²`, generously rounded). -/
theorem log_pmfRatio_taylor {n k : ℕ} (h3 : 2 * k + 3 ≤ n) (hn : 64 ≤ n)
    (hwin : |(k : ℝ) - (n : ℝ) / 4| ≤ (n : ℝ) / 64) :
    |Real.log (pmfRatio n k) + 16 * ((k : ℝ) - (n : ℝ) / 4) / (n : ℝ)|
      ≤ 5000 * ((n : ℝ) + ((k : ℝ) - (n : ℝ) / 4) ^ 2) / (n : ℝ) ^ 2 := by
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by norm_num : 0 < 2 * k + 3) h3
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hnR : (64 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  obtain ⟨hs1, hs2⟩ := abs_le.mp hwin
  have hmd : 180 * ((n : ℝ) + ((k : ℝ) - (n : ℝ) / 4) ^ 2) / (n : ℝ) ^ 2
      = 180 * (((n : ℝ) + ((k : ℝ) - (n : ℝ) / 4) ^ 2) / (n : ℝ) ^ 2) := by
    rw [mul_div_assoc]
  have hrat := (pmfRatio_taylor_rational hn hwin).trans_eq hmd
  have hone := abs_pmfRatio_sub_one_le hn hwin
  -- the log series at `x = 1 − r`, truncated after the linear term
  have hxlt : |1 - pmfRatio n k| < 1 := by
    rw [abs_sub_comm]; linarith
  have hlog := Real.abs_log_sub_add_sum_range_le hxlt 1
  norm_num [Finset.sum_range_one, sub_sub_cancel] at hlog
  have h13 : (1 : ℝ) / 3 ≤ 1 - |1 - pmfRatio n k| := by
    rw [abs_sub_comm]; linarith
  have hlog2 : |1 - pmfRatio n k + Real.log (pmfRatio n k)|
      ≤ 3 * (pmfRatio n k - 1) ^ 2 := by
    refine hlog.trans ?_
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - |1 - pmfRatio n k|)]
    nlinarith [sq_abs (1 - pmfRatio n k),
      mul_nonneg (sq_nonneg (1 - pmfRatio n k))
        (by linarith : (0 : ℝ) ≤ 1 - |1 - pmfRatio n k| - 1 / 3)]
  -- window facts about `b = (n + s²)/n²`
  have hbnn : (0 : ℝ) ≤ ((n : ℝ) + ((k : ℝ) - (n : ℝ) / 4) ^ 2) / (n : ℝ) ^ 2 := by
    positivity
  have hsq4096 : ((k : ℝ) - (n : ℝ) / 4) ^ 2 ≤ (n : ℝ) ^ 2 / 4096 := by
    nlinarith [mul_nonneg
      (by linarith : (0 : ℝ) ≤ (n : ℝ) / 64 - ((k : ℝ) - (n : ℝ) / 4))
      (by linarith : (0 : ℝ) ≤ ((k : ℝ) - (n : ℝ) / 4) + (n : ℝ) / 64)]
  have hb3 : 180 * (((n : ℝ) + ((k : ℝ) - (n : ℝ) / 4) ^ 2) / (n : ℝ) ^ 2) ≤ 3 := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)]
    nlinarith [hsq4096, mul_nonneg hn0.le (by linarith : (0 : ℝ) ≤ (n : ℝ) - 64)]
  have hfrac : (16 * ((k : ℝ) - (n : ℝ) / 4) / (n : ℝ)) ^ 2
      ≤ 256 * (((n : ℝ) + ((k : ℝ) - (n : ℝ) / 4) ^ 2) / (n : ℝ) ^ 2) := by
    rw [div_pow, ← mul_div_assoc,
      div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)
        (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)]
    nlinarith [mul_nonneg hn0.le (mul_nonneg hn0.le hn0.le)]
  have hcomb := taylor_sq_combine hbnn hrat hb3 hfrac
  have hsq : 3 * (pmfRatio n k - 1) ^ 2
      ≤ 4820 * (((n : ℝ) + ((k : ℝ) - (n : ℝ) / 4) ^ 2) / (n : ℝ) ^ 2) := by
    calc 3 * (pmfRatio n k - 1) ^ 2
        = 3 * ((pmfRatio n k - 1 + 16 * ((k : ℝ) - (n : ℝ) / 4) / (n : ℝ))
            - 16 * ((k : ℝ) - (n : ℝ) / 4) / (n : ℝ)) ^ 2 := by ring
      _ ≤ _ := hcomb
  -- assemble
  have hsplit : Real.log (pmfRatio n k) + 16 * ((k : ℝ) - (n : ℝ) / 4) / (n : ℝ)
      = (1 - pmfRatio n k + Real.log (pmfRatio n k))
        + (pmfRatio n k - 1 + 16 * ((k : ℝ) - (n : ℝ) / 4) / (n : ℝ)) := by ring
  calc |Real.log (pmfRatio n k) + 16 * ((k : ℝ) - (n : ℝ) / 4) / (n : ℝ)|
      = |(1 - pmfRatio n k + Real.log (pmfRatio n k))
          + (pmfRatio n k - 1 + 16 * ((k : ℝ) - (n : ℝ) / 4) / (n : ℝ))| := by
        rw [hsplit]
    _ ≤ |1 - pmfRatio n k + Real.log (pmfRatio n k)|
          + |pmfRatio n k - 1 + 16 * ((k : ℝ) - (n : ℝ) / 4) / (n : ℝ)| :=
        abs_add_le _ _
    _ ≤ 3 * (pmfRatio n k - 1) ^ 2
          + 180 * (((n : ℝ) + ((k : ℝ) - (n : ℝ) / 4) ^ 2) / (n : ℝ) ^ 2) :=
        add_le_add hlog2 hrat
    _ ≤ 4820 * (((n : ℝ) + ((k : ℝ) - (n : ℝ) / 4) ^ 2) / (n : ℝ) ^ 2)
          + 180 * (((n : ℝ) + ((k : ℝ) - (n : ℝ) / 4) ^ 2) / (n : ℝ) ^ 2) :=
        add_le_add hsq le_rfl
    _ = 5000 * ((n : ℝ) + ((k : ℝ) - (n : ℝ) / 4) ^ 2) / (n : ℝ) ^ 2 := by ring

/-! ### The law behind `charP2`: fiberwise decomposition

`charP2` (defined in `LeafCount` as a sum over codewords) collapses to a
`k`-indexed sum against the exact law `U (n−1) 1 k / catalan n`; conditional
on the closed form `U_mul_closed`, that law is `pmf'`. -/

/-- A word has at most `length` letters `≥ 2`. -/
lemma P2_le_length : ∀ w : List ℕ, P2 w ≤ w.length := by
  intro w
  induction w with
  | nil => exact le_rfl
  | cons x v ih =>
    show (if 2 ≤ x then 1 else 0) + P2 v ≤ v.length + 1
    by_cases hx : 2 ≤ x
    · rw [if_pos hx]; omega
    · rw [if_neg hx]; omega

/-- Support bound at the `U`-level: from height `h ≥ 1`, a word of length `ℓ`
cannot have `k ≥ (ℓ + h)/2` double pops (each double pop needs a spare unit
of height).  In particular `U (n−1) 1 k = 0` for `2k + 1 > n`, matching
`pmfNum_eq_zero`. -/
lemma U_eq_zero_of_le_two_mul : ∀ ℓ h k : ℕ, 1 ≤ h → ℓ + h ≤ 2 * k → U ℓ h k = 0 := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro h k h1 hk
    show (if k = 0 then 1 else 0) = 0
    rw [if_neg (by omega)]
  | succ ℓ ih =>
    intro h k h1 hk
    show (∑ x ∈ range (h + 1),
        if 2 ≤ x then (if k = 0 then 0 else U ℓ (h + 1 - x) (k - 1))
        else U ℓ (h + 1 - x) k) = 0
    refine Finset.sum_eq_zero fun x hx => ?_
    have hxle : x ≤ h := by
      have := Finset.mem_range.mp hx; omega
    by_cases h2x : 2 ≤ x
    · rw [if_pos h2x]
      by_cases hk0 : k = 0
      · rw [if_pos hk0]
      · rw [if_neg hk0]
        exact ih (h + 1 - x) (k - 1) (by omega) (by omega)
    · rw [if_neg h2x]
      exact ih (h + 1 - x) k (by omega) (by omega)

/-- The exact law is a probability law: `Σ_k U (n−1) 1 k / catalan n = 1`
(unconditional; via `sum_U_eq_card` and `card_suffixes_eq_catalan`). -/
theorem sum_U_div_catalan (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ range n, (U (n - 1) 1 k : ℝ) / (catalan n : ℝ) = 1 := by
  rw [← Finset.sum_div]
  have h := sum_U_eq_card (n - 1) 1
  rw [show n - 1 + 1 = n by omega, card_suffixes_eq_catalan n hn] at h
  have hsum : ∑ k ∈ range n, (U (n - 1) 1 k : ℝ) = (catalan n : ℝ) := by
    exact_mod_cast h
  rw [hsum, div_self]
  exact_mod_cast (catalan_pos' n).ne'

/-- **`charP2` as a sum against the exact law** (unconditional): grouping the
codeword sum by the value of `P₂`. -/
theorem charP2_eq_sum_U (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    charP2 n t
      = (∑ k ∈ range n, (U (n - 1) 1 k : ℂ) *
          Complex.exp (Complex.I *
            Complex.ofReal (t * (((k : ℝ) - EP2 n) * 4 / Real.sqrt n))))
        / (catalan n : ℂ) := by
  unfold charP2
  congr 1
  have hmaps : ∀ w ∈ suffixes (n - 1) 1, P2 w ∈ range n := by
    intro w hw
    obtain ⟨hlen, -⟩ := (mem_suffixes _ _ w).mp hw
    have := P2_le_length w
    exact Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hconst : ∀ w ∈ (suffixes (n - 1) 1).filter (fun w => P2 w = k),
      Complex.exp (Complex.I *
          Complex.ofReal (t * (((P2 w : ℝ) - EP2 n) * 4 / Real.sqrt n)))
        = Complex.exp (Complex.I *
          Complex.ofReal (t * (((k : ℝ) - EP2 n) * 4 / Real.sqrt n))) := by
    intro w hw
    rw [(Finset.mem_filter.mp hw).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, card_filter_P2, nsmul_eq_mul]

/-- **`charP2` against `pmf'`, conditionally on the closed form**
(`hU` = `U_mul_closed`, stated through `pmfNum`).  This is the exact bridge
on which the integration step `leafCLT_charFun_of_local_limit` operates. -/
theorem charP2_eq_sum_pmf'
    (hU : ∀ m j : ℕ, 1 ≤ m → 2 * j + 1 ≤ m → m * U (m - 1) 1 j = pmfNum m j)
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    charP2 n t
      = ∑ k ∈ range n, (pmf' n k : ℂ) *
          Complex.exp (Complex.I *
            Complex.ofReal (t * (((k : ℝ) - EP2 n) * 4 / Real.sqrt n))) := by
  rw [charP2_eq_sum_U n hn t, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hreal : (U (n - 1) 1 k : ℝ) / (catalan n : ℝ) = pmf' n k := by
    by_cases h2k : 2 * k + 1 ≤ n
    · have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      simp only [pmf']
      rw [← hU n k hn h2k]
      push_cast
      rw [mul_div_mul_left _ _ hn0]
    · rw [U_eq_zero_of_le_two_mul (n - 1) 1 k le_rfl (by omega)]
      simp only [pmf', pmfNum_eq_zero (by omega : n < 2 * k + 1)]
      simp
  rw [← hreal]
  push_cast
  ring

/-- **Normalisation, conditionally on the closed form**: `Σ_k pmf' n k = 1`. -/
theorem sum_pmf'_of_closed
    (hU : ∀ m j : ℕ, 1 ≤ m → 2 * j + 1 ≤ m → m * U (m - 1) 1 j = pmfNum m j)
    (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ range n, pmf' n k = 1 := by
  have hNat : ∑ k ∈ range n, pmfNum n k = n * catalan n := by
    have h1 : ∑ k ∈ range n, pmfNum n k = ∑ k ∈ range n, n * U (n - 1) 1 k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      by_cases h2k : 2 * k + 1 ≤ n
      · exact (hU n k hn h2k).symm
      · rw [pmfNum_eq_zero (by omega : n < 2 * k + 1),
          U_eq_zero_of_le_two_mul (n - 1) 1 k le_rfl (by omega), mul_zero]
    rw [h1, ← Finset.mul_sum]
    have h2 := sum_U_eq_card (n - 1) 1
    rw [show n - 1 + 1 = n by omega, card_suffixes_eq_catalan n hn] at h2
    rw [h2]
  simp only [pmf']
  rw [← Finset.sum_div]
  have hcast : ∑ k ∈ range n, (pmfNum n k : ℝ) = (n : ℝ) * (catalan n : ℝ) := by
    exact_mod_cast hNat
  rw [hcast, div_self]
  have hpos : (0 : ℝ) < (n : ℝ) * (catalan n : ℝ) := by
    have h1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h2 : (0 : ℝ) < (catalan n : ℝ) := by exact_mod_cast catalan_pos' n
    exact mul_pos h1 h2
  exact hpos.ne'

/-! ### The two remaining analytic targets

With the ratio analysis above, the road to `leafCLT_charFun` is:

1. `pmf'_local_limit` — the pointwise local limit.  Plan: Stirling
   (`Stirling.factorial_isEquivalent_stirling` for the three factorials in
   each binomial, plus `catalan n = centralBinom n / (n+1)` and Stirling once
   more for the denominator) at the *single* point `k₀ = ⌊n/4⌋`, then
   transport along the window by summing `log_pmfRatio_taylor` over
   `|j − n/4| ≤ x√n/4` steps (telescoping `log_pmf'_succ_sub`); the
   accumulated drift is `−Σ 16(j − n/4)/n → −x²/2` (a Riemann sum) and the
   accumulated error is `O(√n · (√n/n)²·n) = O(1/√n) → 0`.
2. `leafCLT_charFun_of_local_limit` — the integration step.  Plan: by
   `charP2_eq_sum_pmf'` the charFun is `Σ_k pmf'(n,k)·e^{it·(k−EP2)·4/√n}`;
   split at `|k − n/4| ≤ M√n`.  On the window, the local limit (uniformly on
   compacts — upgrade `hloc` via monotonicity `pmf'_mono_of_le`/
   `pmf'_anti_of_ge`, which sandwich `pmf'` between consecutive window
   values) makes the sum a Riemann sum for `∫ φ(x) e^{itx} dx`.  Off the
   window, unimodality + `Σ pmf' = 1` give
   `pmf'(n,k) ≤ pmf'(n, mode ± M√n) ≤ C/√n·e^{−cM²}`-type tail domination
   (Gauss-type bound from summing `log_pmfRatio_taylor`), so the tail mass is
   `≲ e^{−cM²}`, uniformly in `n`; let `M → ∞`.  Finally replace `EP2` by
   `n/4` using `EP2_sub_muP2_tendsto` (an `O(1/√n)` phase, handled exactly as
   in `norm_charAN_sub_charP2_le`). -/

/-- **Wanted: the pointwise local limit.**  The law, rescaled by `σ = √n/4`,
converges at `k = ⌊μ + xσ⌋` to the standard Gaussian density.
TODO: see the plan in the section header (Stirling at the mode + telescoped
ratio bounds along the window). -/
proof_wanted pmf'_local_limit (x : ℝ) :
    Tendsto (fun n : ℕ => sigmaP2 n * pmf' n ⌊muP2 n + x * sigmaP2 n⌋₊) atTop
      (𝓝 (Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi)))

/-- **Wanted: the integration step** — Proposition 12 at the charFun level
from the closed form (`hU` = `U_mul_closed`) and the local limit.
TODO: see the plan in the section header (window Riemann sum + unimodal tail
domination); this consumes `charP2_eq_sum_pmf'`, `sum_pmf'_of_closed`,
`pmf'_mono_of_le`, `pmf'_anti_of_ge`, `EP2_sub_muP2_tendsto`. -/
proof_wanted leafCLT_charFun_of_local_limit
    (hU : ∀ m j : ℕ, 1 ≤ m → 2 * j + 1 ≤ m → m * U (m - 1) 1 j = pmfNum m j)
    (hloc : ∀ x : ℝ,
      Tendsto (fun n : ℕ => sigmaP2 n * pmf' n ⌊muP2 n + x * sigmaP2 n⌋₊) atTop
        (𝓝 (Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi))))
    (t : ℝ) :
    Tendsto (fun n : ℕ => charP2 n t) atTop (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2)))

end MakinenAnalysis
