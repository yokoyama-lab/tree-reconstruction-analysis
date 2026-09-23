import Mathlib
import MakinenAnalysis.LocalCLT

/-!
# Window and tail estimates for the local limit theorem

This file builds the **window/tail layer** of the local-limit programme for the
double-pop count `P₂` (see `LocalCLT.lean`).  The target normalisation argument
runs by *self-normalisation*: `Σ_k pmf' n k = 1` (`sum_pmf'_of_closed`) is
squeezed between two Gaussian Riemann sums over the central window
`|k − n/4| ≤ O(√n)`, provided the mass **outside** any fixed-fraction window is
negligible and the log-profile **inside** the window is quadratic.  The two
halves proved here are exactly those inputs:

* **Geometric tails** (`pmf'_add_le`, `pmf'_sub_le`, `sum_pmf'_tail_le`,
  `sum_pmf'_head_le`): beyond the fixed fractions `k ≥ 5n/16` (right) and
  `k ≤ 3n/16` (left) the one-step ratio
  `pmfRatio n k = (n−2k−1)(n−2k−2)/(4(k+1)(k+2))` is uniformly `≤ 3/4`
  (resp. `≥ 4/3`), so the law decays geometrically away from the mode
  `k ≈ n/4` and each tail carries at most `4·pmf'` of its boundary value —
  in particular `O(1/√n)`-small once the mode value is known to be
  `O(1/√n)`.

* **Window telescope** (`log_pmf'_add_sub`, `abs_log_pmf'_window_sum`,
  `abs_log_pmf'_window`): *conditionally on* the one-step Taylor bound
  `|log (pmfRatio n m) + 16(m − n/4)/n| ≤ C(n + (m − n/4)²)/n²`
  (hypothesis `htaylor`, being proved separately from `pmfRatio_sub_one`),
  summing `log_pmf'_succ_sub` over `s` steps inside the window
  `[n/4 − n/64, n/4 + n/64]` gives
  `log pmf'(k₀+s) − log pmf'(k₀) ≈ −16(s(k₀ − n/4) + s(s−1)/2)/n`
  with total error `≤ s·C(n + (n/32)²)/n²`.  At `s = O(√n)` this drift is the
  Gaussian exponent `−(k − n/4)²/(2σ²) + O(1/√n)`, `σ² = n/16`, and the error
  is `O(1/√n)` — the quantitative heart of `pmf'_local_limit`.

Everything is nonasymptotic and fully explicit; no limits are taken.
-/

namespace MakinenAnalysis

open Finset

/-! ### Vanishing outside the support, and the product form of the recurrence -/

/-- Outside the support (`n < 2k+1`) the law vanishes (numerator zero by
`pmfNum_eq_zero`).  Used to run the geometric telescope past the right end of
the support without side conditions. -/
lemma pmf'_eq_zero {n k : ℕ} (h : n < 2 * k + 1) : pmf' n k = 0 := by
  simp [pmf', pmfNum_eq_zero h]

/-- The one-step recurrence of the law in product form:
`pmf' n (k+1) = pmf' n k · pmfRatio n k` on the support.  (Division-free
restatement of `pmf'_ratio`, convenient for telescoping.) -/
lemma pmf'_succ_eq {n k : ℕ} (h : 2 * k + 3 ≤ n) :
    pmf' n (k + 1) = pmf' n k * pmfRatio n k := by
  have h0 : 0 < pmf' n k := pmf'_pos (by omega)
  have hr := pmf'_ratio n k h
  rw [div_eq_iff h0.ne'] at hr
  rw [hr, mul_comm]

/-! ### Right tail: geometric decay for `k ≥ 5n/16`

At `k = (1/4 + δ)n` the ratio is `≈ ((1/2 − 2δ)/(1/2 + 2δ))²`; at `δ = 1/16`
this is `(3/8 / 5/8)² = 9/25`, comfortably below the round constant `3/4` used
throughout. -/

/-- **Uniform ratio bound on the right tail**: for `k ≥ 5n/16` (inside the
support) the one-step ratio is at most `3/4`. -/
theorem pmfRatio_le_of_ge {n k : ℕ} (hk : 5 * n ≤ 16 * k) (h : 2 * k + 3 ≤ n) :
    pmfRatio n k ≤ 3 / 4 := by
  have hn : (2 * (k : ℝ) + 3) ≤ (n : ℝ) := by exact_mod_cast h
  have hk' : 5 * (n : ℝ) ≤ 16 * (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [pmfRatio, div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 16 * (k : ℝ) - 5 * (n : ℝ))
      (by linarith : (0 : ℝ) ≤ (n : ℝ) - 2 * (k : ℝ) - 3),
    mul_nonneg (by linarith : (0 : ℝ) ≤ 16 * (k : ℝ) - 5 * (n : ℝ)) hk0,
    sq_nonneg (k : ℝ)]

/-- One-step geometric decay on the right tail, with the support boundary
handled by `pmf'_eq_zero`: for `k ≥ 5n/16`, `pmf' n (k+1) ≤ (3/4)·pmf' n k`. -/
theorem pmf'_succ_le_right {n k : ℕ} (hk : 5 * n ≤ 16 * k) :
    pmf' n (k + 1) ≤ pmf' n k * (3 / 4) := by
  by_cases h : 2 * k + 3 ≤ n
  · rw [pmf'_succ_eq h]
    exact mul_le_mul_of_nonneg_left (pmfRatio_le_of_ge hk h) (pmf'_nonneg n k)
  · rw [pmf'_eq_zero (by omega : n < 2 * (k + 1) + 1)]
    exact mul_nonneg (pmf'_nonneg n k) (by norm_num)

/-- **Telescoped right-tail decay**: for `k₀ ≥ 5n/16`,
`pmf' n (k₀ + j) ≤ pmf' n k₀ · (3/4)^j` for every `j`. -/
theorem pmf'_add_le {n k₀ : ℕ} (hk : 5 * n ≤ 16 * k₀) (j : ℕ) :
    pmf' n (k₀ + j) ≤ pmf' n k₀ * (3 / 4) ^ j := by
  induction j with
  | zero => simp
  | succ m ih =>
    calc pmf' n (k₀ + (m + 1)) = pmf' n ((k₀ + m) + 1) := by rw [add_assoc]
      _ ≤ pmf' n (k₀ + m) * (3 / 4) := pmf'_succ_le_right (by omega)
      _ ≤ (pmf' n k₀ * (3 / 4) ^ m) * (3 / 4) :=
          mul_le_mul_of_nonneg_right ih (by norm_num)
      _ = pmf' n k₀ * (3 / 4) ^ (m + 1) := by ring

/-- Explicit bound for the partial geometric series with ratio `3/4`:
`Σ_{j<m} (3/4)^j ≤ 4 = 1/(1 − 3/4)`. -/
lemma geom_sum_three_quarters_le (m : ℕ) : ∑ j ∈ range m, ((3 : ℝ) / 4) ^ j ≤ 4 := by
  rw [geom_sum_eq (by norm_num) m]
  have h : (0 : ℝ) ≤ ((3 : ℝ) / 4) ^ m := by positivity
  have he : (((3 : ℝ) / 4) ^ m - 1) / ((3 : ℝ) / 4 - 1)
      = 4 - 4 * ((3 : ℝ) / 4) ^ m := by ring
  rw [he]
  linarith

/-- **Summed right tail**: for `k₀ ≥ 5n/16` the whole tail mass is dominated
by four times its boundary value, `Σ_{k=k₀}^{n} pmf' n k ≤ 4·pmf' n k₀`.
(Together with a mode bound `pmf' n k₀ = O(1/√n)` this makes the right tail
`O(1/√n)`, negligible in the self-normalisation.) -/
theorem sum_pmf'_tail_le {n k₀ : ℕ} (hk : 5 * n ≤ 16 * k₀) :
    ∑ k ∈ Icc k₀ n, pmf' n k ≤ pmf' n k₀ * 4 := by
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  calc ∑ j ∈ range (n + 1 - k₀), pmf' n (k₀ + j)
      ≤ ∑ j ∈ range (n + 1 - k₀), pmf' n k₀ * (3 / 4) ^ j :=
        Finset.sum_le_sum fun j _ => pmf'_add_le hk j
    _ = pmf' n k₀ * ∑ j ∈ range (n + 1 - k₀), ((3 : ℝ) / 4) ^ j := by
        rw [Finset.mul_sum]
    _ ≤ pmf' n k₀ * 4 :=
        mul_le_mul_of_nonneg_left (geom_sum_three_quarters_le _) (pmf'_nonneg n k₀)

/-! ### Left tail: geometric growth for `k ≤ 3n/16`

Mirror image: at `k = (1/4 − δ)n` the ratio is `≈ ((1/2 + 2δ)/(1/2 − 2δ))²`;
at `δ = 1/16` this is `25/9`, comfortably above the round constant `4/3`.
The `O(1)` corrections in the exact ratio force a mild size hypothesis
`n ≥ 32` (e.g. `pmfRatio 6 1 = 1/4 < 4/3` even though `1 ≤ 3·6/16`). -/

/-- **Uniform ratio bound on the left tail**: for `n ≥ 32` and `k ≤ 3n/16`
the one-step ratio is at least `4/3` (in particular the law is increasing
there, sharpening `pmf'_mono_of_le` to a geometric rate).  Note the support
guard `2k+3 ≤ n` is implied by the two hypotheses. -/
theorem le_pmfRatio_of_le {n k : ℕ} (hn : 32 ≤ n) (hk : 16 * k ≤ 3 * n) :
    4 / 3 ≤ pmfRatio n k := by
  have hn' : (32 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hk' : 16 * (k : ℝ) ≤ 3 * (n : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [pmfRatio, le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * (n : ℝ) - 16 * (k : ℝ))
      (by linarith : (0 : ℝ) ≤ (n : ℝ) - 32),
    mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * (n : ℝ) - 16 * (k : ℝ)) hk0,
    mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) - 32) hk0]

/-- One-step geometric growth on the left tail, in downward form:
for `n ≥ 32` and `k ≤ 3n/16`, `pmf' n k ≤ (3/4)·pmf' n (k+1)`. -/
theorem pmf'_le_succ_left {n k : ℕ} (hn : 32 ≤ n) (hk : 16 * k ≤ 3 * n) :
    pmf' n k ≤ pmf' n (k + 1) * (3 / 4) := by
  have h : 2 * k + 3 ≤ n := by omega
  have hr := mul_le_mul_of_nonneg_left (le_pmfRatio_of_le hn hk) (pmf'_nonneg n k)
  rw [pmf'_succ_eq h]
  linarith

/-- **Telescoped left-tail decay**: for `k₀ ≤ 3n/16` (and `n ≥ 32`),
`pmf' n (k₀ − j) ≤ pmf' n k₀ · (3/4)^j` for every `j ≤ k₀`. -/
theorem pmf'_sub_le {n k₀ : ℕ} (hn : 32 ≤ n) (hk : 16 * k₀ ≤ 3 * n) :
    ∀ j, j ≤ k₀ → pmf' n (k₀ - j) ≤ pmf' n k₀ * (3 / 4) ^ j := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have hstep := pmf'_le_succ_left hn (show 16 * (k₀ - m - 1) ≤ 3 * n by omega)
    rw [show k₀ - m - 1 + 1 = k₀ - m by omega] at hstep
    rw [show k₀ - (m + 1) = k₀ - m - 1 by omega]
    calc pmf' n (k₀ - m - 1) ≤ pmf' n (k₀ - m) * (3 / 4) := hstep
      _ ≤ (pmf' n k₀ * (3 / 4) ^ m) * (3 / 4) :=
          mul_le_mul_of_nonneg_right (ih (by omega)) (by norm_num)
      _ = pmf' n k₀ * (3 / 4) ^ (m + 1) := by ring

/-- **Summed left tail**: for `n ≥ 32` and `k₀ ≤ 3n/16` the whole head mass
is dominated by four times its boundary value,
`Σ_{k=0}^{k₀} pmf' n k ≤ 4·pmf' n k₀` — the mirror of `sum_pmf'_tail_le`. -/
theorem sum_pmf'_head_le {n k₀ : ℕ} (hn : 32 ≤ n) (hk : 16 * k₀ ≤ 3 * n) :
    ∑ k ∈ range (k₀ + 1), pmf' n k ≤ pmf' n k₀ * 4 := by
  calc ∑ k ∈ range (k₀ + 1), pmf' n k
      = ∑ j ∈ range (k₀ + 1), pmf' n (k₀ - j) :=
        -- `k₀ + 1 - 1 - j` is definitionally `k₀ - j`
        (Finset.sum_range_reflect (fun k => pmf' n k) (k₀ + 1)).symm
    _ ≤ ∑ j ∈ range (k₀ + 1), pmf' n k₀ * (3 / 4) ^ j :=
        Finset.sum_le_sum fun j hj =>
          pmf'_sub_le hn hk j (by have := Finset.mem_range.mp hj; omega)
    _ = pmf' n k₀ * ∑ j ∈ range (k₀ + 1), ((3 : ℝ) / 4) ^ j := by
        rw [Finset.mul_sum]
    _ ≤ pmf' n k₀ * 4 :=
        mul_le_mul_of_nonneg_left (geom_sum_three_quarters_le _) (pmf'_nonneg n k₀)

/-! ### The window telescope, conditional on the one-step Taylor bound

Summing the one-step log-increment `log_pmf'_succ_sub` over `s` steps starting
at `k₀` turns the (hypothesised) Taylor bound for `log (pmfRatio n m)` into a
quadratic profile for `log (pmf' n (k₀+s))` with an explicit error linear in
`s`.  The arithmetic drift sum is evaluated in closed form (Gauss sum). -/

/-- Gauss sum over the reals: `Σ_{j<s} j = s(s−1)/2`. -/
lemma sum_range_natCast (s : ℕ) :
    ∑ j ∈ range s, (j : ℝ) = s * ((s : ℝ) - 1) / 2 := by
  induction s with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Closed form of the accumulated drift:
`Σ_{j<s} ((k₀+j) − n/4) = s(k₀ − n/4) + s(s−1)/2`. -/
lemma drift_sum_eq (n k₀ s : ℕ) :
    ∑ j ∈ range s, (((k₀ : ℝ) + (j : ℝ)) - (n : ℝ) / 4)
      = s * ((k₀ : ℝ) - (n : ℝ) / 4) + s * ((s : ℝ) - 1) / 2 := by
  have h : ∀ j ∈ range s,
      ((k₀ : ℝ) + (j : ℝ)) - (n : ℝ) / 4 = ((k₀ : ℝ) - (n : ℝ) / 4) + (j : ℝ) :=
    fun j _ => by ring
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, sum_range_natCast, nsmul_eq_mul]

/-- **Exact log telescope** along `s` steps inside the support:
`log pmf'(n, k₀+s) − log pmf'(n, k₀) = Σ_{j<s} log (pmfRatio n (k₀+j))`. -/
theorem log_pmf'_add_sub (n k₀ s : ℕ) (hguard : 2 * (k₀ + s) + 1 ≤ n) :
    Real.log (pmf' n (k₀ + s)) - Real.log (pmf' n k₀)
      = ∑ j ∈ range s, Real.log (pmfRatio n (k₀ + j)) := by
  have h := Finset.sum_range_sub (fun j => Real.log (pmf' n (k₀ + j))) s
  simp only [Nat.add_zero] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < s := Finset.mem_range.mp hj
  exact log_pmf'_succ_sub n (k₀ + j) (by omega)

/-- **The window sum estimate, conditional formulation.**  Assume the one-step
Taylor bound `htaylor` (proved separately from `pmfRatio_sub_one`):
`|log (pmfRatio n m) + 16(m − n/4)/n| ≤ C(n + (m − n/4)²)/n²` on the window
`|m − n/4| ≤ n/64` of the support.  Then for any block `[k₀, k₀+s]` contained
in the window `[n/4 − n/64, n/4 + n/64]`,

`|log pmf'(n, k₀+s) − log pmf'(n, k₀) + Σ_{j<s} 16((k₀+j) − n/4)/n|
   ≤ s · C(n + (n/32)²)/n²`.

At `s = O(√n)` the right side is `O(1/√n)`: the log-profile of the law is the
Gaussian quadratic to vanishing error, uniformly over the window. -/
theorem abs_log_pmf'_window_sum (n k₀ s : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (htaylor : ∀ m : ℕ, 2 * m + 3 ≤ n →
      |(m : ℝ) - (n : ℝ) / 4| ≤ (n : ℝ) / 64 →
      |Real.log (pmfRatio n m) + 16 * ((m : ℝ) - (n : ℝ) / 4) / (n : ℝ)|
        ≤ C * ((n : ℝ) + ((m : ℝ) - (n : ℝ) / 4) ^ 2) / (n : ℝ) ^ 2)
    (hguard : 2 * (k₀ + s) + 1 ≤ n)
    (hlo : (n : ℝ) / 4 - (n : ℝ) / 64 ≤ (k₀ : ℝ))
    (hhi : (k₀ : ℝ) + (s : ℝ) ≤ (n : ℝ) / 4 + (n : ℝ) / 64) :
    |Real.log (pmf' n (k₀ + s)) - Real.log (pmf' n k₀)
        + ∑ j ∈ range s, 16 * (((k₀ : ℝ) + (j : ℝ)) - (n : ℝ) / 4) / (n : ℝ)|
      ≤ s * (C * ((n : ℝ) + ((n : ℝ) / 32) ^ 2) / (n : ℝ) ^ 2) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  rw [log_pmf'_add_sub n k₀ s hguard, ← Finset.sum_add_distrib]
  calc |∑ j ∈ range s, (Real.log (pmfRatio n (k₀ + j))
          + 16 * (((k₀ : ℝ) + (j : ℝ)) - (n : ℝ) / 4) / (n : ℝ))|
      ≤ ∑ j ∈ range s, |Real.log (pmfRatio n (k₀ + j))
          + 16 * (((k₀ : ℝ) + (j : ℝ)) - (n : ℝ) / 4) / (n : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range s, C * ((n : ℝ) + ((n : ℝ) / 32) ^ 2) / (n : ℝ) ^ 2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' : j < s := Finset.mem_range.mp hj
        have hjs : (j : ℝ) + 1 ≤ (s : ℝ) := by exact_mod_cast hj'
        have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        have hcast : ((k₀ + j : ℕ) : ℝ) = (k₀ : ℝ) + (j : ℝ) := by push_cast; ring
        have hwin : |((k₀ + j : ℕ) : ℝ) - (n : ℝ) / 4| ≤ (n : ℝ) / 64 := by
          rw [hcast, abs_le]
          constructor <;> linarith
        have hb := htaylor (k₀ + j) (by omega) hwin
        rw [hcast] at hb
        refine hb.trans ?_
        have hsq : (((k₀ : ℝ) + (j : ℝ)) - (n : ℝ) / 4) ^ 2 ≤ ((n : ℝ) / 32) ^ 2 := by
          rw [hcast] at hwin
          have habs := abs_le.mp hwin
          exact sq_le_sq' (by linarith [habs.1, hn1]) (by linarith [habs.2, hn1])
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) hC) (by positivity)
    _ = s * (C * ((n : ℝ) + ((n : ℝ) / 32) ^ 2) / (n : ℝ) ^ 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The window sum estimate with the drift evaluated** (Gauss sum):
under the hypotheses of `abs_log_pmf'_window_sum`,

`|log pmf'(n, k₀+s) − log pmf'(n, k₀) + 16(s(k₀ − n/4) + s(s−1)/2)/n|
   ≤ s · C(n + (n/32)²)/n²`.

Taking `k₀ = ⌈n/4⌉` (so `|k₀ − n/4| ≤ 1`) and `s ≈ x√n/4`, the drift is
`16·(s²/2)/n + O(s/n) = x²/2 + O(1/√n)`: the Gaussian exponent at `x`
standard deviations, with `σ² = n/16`. -/
theorem abs_log_pmf'_window (n k₀ s : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (htaylor : ∀ m : ℕ, 2 * m + 3 ≤ n →
      |(m : ℝ) - (n : ℝ) / 4| ≤ (n : ℝ) / 64 →
      |Real.log (pmfRatio n m) + 16 * ((m : ℝ) - (n : ℝ) / 4) / (n : ℝ)|
        ≤ C * ((n : ℝ) + ((m : ℝ) - (n : ℝ) / 4) ^ 2) / (n : ℝ) ^ 2)
    (hguard : 2 * (k₀ + s) + 1 ≤ n)
    (hlo : (n : ℝ) / 4 - (n : ℝ) / 64 ≤ (k₀ : ℝ))
    (hhi : (k₀ : ℝ) + (s : ℝ) ≤ (n : ℝ) / 4 + (n : ℝ) / 64) :
    |Real.log (pmf' n (k₀ + s)) - Real.log (pmf' n k₀)
        + 16 * ((s : ℝ) * ((k₀ : ℝ) - (n : ℝ) / 4)
            + (s : ℝ) * ((s : ℝ) - 1) / 2) / (n : ℝ)|
      ≤ s * (C * ((n : ℝ) + ((n : ℝ) / 32) ^ 2) / (n : ℝ) ^ 2) := by
  have h := abs_log_pmf'_window_sum n k₀ s hC htaylor hguard hlo hhi
  have hd : ∑ j ∈ range s, 16 * (((k₀ : ℝ) + (j : ℝ)) - (n : ℝ) / 4) / (n : ℝ)
      = 16 * ((s : ℝ) * ((k₀ : ℝ) - (n : ℝ) / 4)
          + (s : ℝ) * ((s : ℝ) - 1) / 2) / (n : ℝ) := by
    rw [← Finset.sum_div, ← Finset.mul_sum, drift_sum_eq]
  rw [hd] at h
  exact h

/-! ### Kernel-checked sanity examples -/

/-- Right-tail ratio bound at `n = 32`, `k = 10 = 5n/16`:
`pmfRatio 32 10 = 11·10/(4·11·12) = 5/24 ≤ 3/4`. -/
example : pmfRatio 32 10 ≤ 3 / 4 := pmfRatio_le_of_ge (by norm_num) (by norm_num)

/-- The same ratio computed exactly. -/
example : pmfRatio 32 10 = 5 / 24 := by norm_num [pmfRatio]

/-- Left-tail ratio bound at `n = 32`, `k = 6 = 3n/16`:
`pmfRatio 32 6 = 19·18/(4·7·8) = 171/112 ≥ 4/3`. -/
example : 4 / 3 ≤ pmfRatio 32 6 := le_pmfRatio_of_le (by norm_num) (by norm_num)

/-- The same ratio computed exactly. -/
example : pmfRatio 32 6 = 171 / 112 := by norm_num [pmfRatio]

/-- Instantiated geometric tail: two steps beyond `k₀ = 10` at `n = 32`. -/
example : pmf' 32 12 ≤ pmf' 32 10 * (3 / 4) ^ 2 := pmf'_add_le (by norm_num) 2

/-- Instantiated summed tail at `n = 32`, `k₀ = 10`. -/
example : ∑ k ∈ Icc 10 32, pmf' 32 k ≤ pmf' 32 10 * 4 := sum_pmf'_tail_le (by norm_num)

/-- Instantiated summed head at `n = 32`, `k₀ = 6`. -/
example : ∑ k ∈ range 7, pmf' 32 k ≤ pmf' 32 6 * 4 :=
  sum_pmf'_head_le (by norm_num) (by norm_num)

/-- Gauss drift sum sanity: `Σ_{j<5} j = 10`. -/
example : ∑ j ∈ range 5, (j : ℝ) = 10 := by
  rw [sum_range_natCast]; norm_num

/-- **The unconditional window estimate**: `abs_log_pmf'_window` with the
    proved Taylor bound `log_pmfRatio_taylor` (C = 5000) plugged in.  For
    `n ≥ 64` and any block `[k₀, k₀+s]` inside the window
    `[n/4 − n/64, n/4 + n/64]`,
    `|log pmf'(n,k₀+s) − log pmf'(n,k₀) + 16(s(k₀−n/4) + s(s−1)/2)/n|
       ≤ s · 5000(n + (n/32)²)/n²`.
    At `s = O(√n)` the error is `O(1/√n) → 0` while the drift is the Gaussian
    exponent — the quantitative heart of `pmf'_local_limit`. -/
theorem abs_log_pmf'_window_final (n k₀ s : ℕ) (hn : 64 ≤ n)
    (hguard : 2 * (k₀ + s) + 1 ≤ n)
    (hlo : (n : ℝ) / 4 - (n : ℝ) / 64 ≤ (k₀ : ℝ))
    (hhi : (k₀ : ℝ) + (s : ℝ) ≤ (n : ℝ) / 4 + (n : ℝ) / 64) :
    |Real.log (pmf' n (k₀ + s)) - Real.log (pmf' n k₀)
        + 16 * ((s : ℝ) * ((k₀ : ℝ) - (n : ℝ) / 4)
            + (s : ℝ) * ((s : ℝ) - 1) / 2) / (n : ℝ)|
      ≤ s * (5000 * ((n : ℝ) + ((n : ℝ) / 32) ^ 2) / (n : ℝ) ^ 2) :=
  abs_log_pmf'_window n k₀ s (by norm_num)
    (fun m hm hwin => log_pmfRatio_taylor hm hn hwin) hguard hlo hhi

end MakinenAnalysis
