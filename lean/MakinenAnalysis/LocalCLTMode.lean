import Mathlib
import MakinenAnalysis.LocalCLTWindow

/-!
# Self-normalisation at the mode: `√n·pmf'(n, k₀) ≍ 1`

Final assembly layer for `pmf'_local_limit` (see `LocalCLT.lean`): the value of
the law at the mode `k₀ ≈ n/4` is pinned to the scale `1/√n` **without any
Stirling input**, purely by self-normalisation.

The two mechanisms, both driven by the exact ratio analysis of `LocalCLT.lean`:

* **Flatness on the `√n`-window** (`abs_log_pmf'_window_right/left`,
  `pmf'_window_lower/upper` and their left mirrors): re-telescoping
  `log_pmf'_add_sub` with the one-step Taylor bound `log_pmfRatio_taylor`
  applied on the *narrow* window `|m − n/4| ≤ 2√n` (where the per-step error
  is `≤ 25000/n`, not the `O(1)` of the coarse `n/64`-window constant of
  `abs_log_pmf'_window_final`) shows that over `0 ≤ s ≤ ⌊√n⌋` steps the
  log-profile moves by at most
  `(drift ≤ 8 + O(1/√n)) + (error ≤ 25000·s/n ≤ O(1/√n)) ≤ 9`, i.e.
  `e⁻⁹·pmf'(k₀) ≤ pmf'(k₀ ± s) ≤ e⁹·pmf'(k₀)` uniformly on the window.

* **Uniform geometric decay beyond the window** (`pmf'_succ_le_far_right`,
  `pmf'_le_succ_far_left` and their telescopes): at distance `≥ √n − 1` from
  `n/4` the one-step ratio is `≤ 1 − 7√n/n` (right) resp. `≥ 1 + 7√n/n`
  (left), so each tail carries at most `n/(7√n) ≈ √n/7` times its boundary
  value.

Together with the normalisation `Σ_k pmf' n k = 1` — supplied here as the
hypothesis `hnorm`, to be discharged by `sum_pmf'_of_closed` once the closed
form `U_mul_closed` is proved — these give the **two-sided mode bounds**

  `1/(25000·√n) ≤ pmf' n k₀ ≤ 8104/√n`   (`mode_lower`, `mode_upper`)

for every `n ≥ 10⁹` and every centre `|k₀ − n/4| ≤ 1`.  All constants and the
threshold are explicit numerals; nothing is asymptotic.
-/

namespace MakinenAnalysis

open Finset

/-! ### Small arithmetic helpers -/

/-- Cast of the defining property of `Nat.sqrt`: `s ≤ ⌊√n⌋ → s² ≤ n` in `ℝ`.
(public: reused by `ModePrefactorMain`) -/
lemma cast_sq_le_of_le_sqrt {n s : ℕ} (hs : s ≤ Nat.sqrt n) :
    (s : ℝ) ^ 2 ≤ (n : ℝ) := by
  have h : s * s ≤ n := le_trans (Nat.mul_le_mul hs hs) (Nat.sqrt_le n)
  have h2 : ((s * s : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  calc (s : ℝ) ^ 2 = ((s * s : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (n : ℝ) := h2

/-- Support guard for a `√n`-block near the centre: if `|k₁ − n/4| ≤ s + 1`
and `s ≤ ⌊√n⌋` then `2(k₁ + s) + 1 ≤ n` (for `n ≥ 10⁹`), so every point of
the block `[k₁, k₁ + s]` is deep inside the support of `pmf' n ·`. -/
private lemma guard_of_near {n k₁ s : ℕ} (hn : 1000000000 ≤ n)
    (hs : s ≤ Nat.sqrt n)
    (hk₁ : |(k₁ : ℝ) - (n : ℝ) / 4| ≤ (s : ℝ) + 1) :
    2 * (k₁ + s) + 1 ≤ n := by
  have hnR : (1000000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsq := cast_sq_le_of_le_sqrt hs
  have hk := (abs_le.mp hk₁).2
  have hR : ((2 * (k₁ + s) + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    push_cast
    nlinarith [sq_nonneg ((s : ℝ) - 9), (by positivity : (0 : ℝ) ≤ (s : ℝ))]
  exact_mod_cast hR

/-- Numeric bound for the window constant: `e⁹ ≤ 8104`.
(public: reused by `ModePrefactorMain`) -/
lemma exp_nine_le : Real.exp 9 ≤ 8104 := by
  have h1 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  have h2 : Real.exp 9 = Real.exp 1 ^ 9 := by
    rw [Real.exp_one_pow]; norm_num
  rw [h2]
  calc Real.exp 1 ^ 9 ≤ 2.7182818286 ^ 9 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le h1 9
    _ ≤ 8104 := by norm_num

/-- Partial geometric series with ratio `1 − x`, `0 < x ≤ 1`:
`Σ_{j<m} (1−x)^j ≤ 1/x`.
(public: reused by `ModePrefactorMain`) -/
lemma geom_sum_le_inv {x : ℝ} (h0 : 0 < x) (h1 : x ≤ 1) (m : ℕ) :
    ∑ j ∈ range m, (1 - x) ^ j ≤ 1 / x := by
  have hne : (1 : ℝ) - x ≠ 1 := by intro h; nlinarith
  rw [geom_sum_eq hne]
  have hxne : (1 - x) - 1 ≠ 0 := by
    intro h; apply h0.ne'; linarith
  have h2 : ((1 - x) ^ m - 1) / ((1 - x) - 1) = (1 - (1 - x) ^ m) / x := by
    rw [div_eq_div_iff hxne h0.ne']; ring
  rw [h2]
  have h3 : (0 : ℝ) ≤ (1 - x) ^ m := pow_nonneg (by linarith) m
  gcongr
  linarith

/-! ### The `√n`-window telescope with the sharp error constant

`abs_log_pmf'_window_final` (in `LocalCLTWindow`) bounds the per-step Taylor
error by its worst case over the whole `n/64`-window, which is `O(1)` per step
— useless over `√n` steps.  Here the telescope is redone for blocks of length
`s ≤ ⌊√n⌋` starting at distance `≤ s + 1` from `n/4`: every intermediate point
`m` then has `|m − n/4| ≤ 2s ≤ 2√n`, where `log_pmfRatio_taylor` gives the
per-step error `5000(n + 4n)/n² = 25000/n`, hence total error `≤ 25000·s/n
= O(1/√n)`. -/

/-- **Narrow-window telescope.**  For `n ≥ 10⁹`, `s ≤ ⌊√n⌋` and a base point
`k₁` with `|k₁ − n/4| ≤ s + 1`,

`|log pmf'(n,k₁+s) − log pmf'(n,k₁) + 16(s(k₁−n/4) + s(s−1)/2)/n| ≤ 25000·s/n`.

This is the drift-plus-`O(1/√n)` profile that all window-transport lemmas
below exponentiate. -/
theorem abs_log_pmf'_sqrt_telescope {n k₁ s : ℕ} (hn : 1000000000 ≤ n)
    (hs : s ≤ Nat.sqrt n)
    (hk₁ : |(k₁ : ℝ) - (n : ℝ) / 4| ≤ (s : ℝ) + 1) :
    |Real.log (pmf' n (k₁ + s)) - Real.log (pmf' n k₁)
        + 16 * ((s : ℝ) * ((k₁ : ℝ) - (n : ℝ) / 4)
            + (s : ℝ) * ((s : ℝ) - 1) / 2) / (n : ℝ)|
      ≤ 25000 * (s : ℝ) / (n : ℝ) := by
  have hnR : (1000000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hsq := cast_sq_le_of_le_sqrt hs
  obtain ⟨hk₁l, hk₁r⟩ := abs_le.mp hk₁
  have hs128 : 128 * (s : ℝ) ≤ (n : ℝ) := by
    nlinarith [sq_nonneg ((s : ℝ) - 128), (by positivity : (0 : ℝ) ≤ (s : ℝ))]
  have hguard : 2 * (k₁ + s) + 1 ≤ n := guard_of_near hn hs hk₁
  have hd : ∑ j ∈ range s, 16 * (((k₁ : ℝ) + (j : ℝ)) - (n : ℝ) / 4) / (n : ℝ)
      = 16 * ((s : ℝ) * ((k₁ : ℝ) - (n : ℝ) / 4)
          + (s : ℝ) * ((s : ℝ) - 1) / 2) / (n : ℝ) := by
    rw [← Finset.sum_div, ← Finset.mul_sum, drift_sum_eq]
  rw [log_pmf'_add_sub n k₁ s hguard, ← hd, ← Finset.sum_add_distrib]
  calc |∑ j ∈ range s, (Real.log (pmfRatio n (k₁ + j))
          + 16 * (((k₁ : ℝ) + (j : ℝ)) - (n : ℝ) / 4) / (n : ℝ))|
      ≤ ∑ j ∈ range s, |Real.log (pmfRatio n (k₁ + j))
          + 16 * (((k₁ : ℝ) + (j : ℝ)) - (n : ℝ) / 4) / (n : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range s, 25000 / (n : ℝ) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' : j < s := Finset.mem_range.mp hj
        have hjs : (j : ℝ) + 1 ≤ (s : ℝ) := by exact_mod_cast hj'
        have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
        have hs1 : (1 : ℝ) ≤ (s : ℝ) := by linarith
        have hcast : ((k₁ + j : ℕ) : ℝ) = (k₁ : ℝ) + (j : ℝ) := by
          push_cast; ring
        have hdev : |((k₁ + j : ℕ) : ℝ) - (n : ℝ) / 4| ≤ 2 * (s : ℝ) := by
          rw [hcast, abs_le]
          constructor <;> linarith
        have hwin : |((k₁ + j : ℕ) : ℝ) - (n : ℝ) / 4| ≤ (n : ℝ) / 64 :=
          hdev.trans (by linarith)
        have ht := log_pmfRatio_taylor (show 2 * (k₁ + j) + 3 ≤ n by omega)
          (show 64 ≤ n by omega) hwin
        rw [hcast] at ht hdev
        refine ht.trans ?_
        have hdev' := abs_le.mp hdev
        have hsqdev : ((k₁ : ℝ) + (j : ℝ) - (n : ℝ) / 4) ^ 2 ≤ 4 * (n : ℝ) := by
          nlinarith [mul_nonneg
            (by linarith : (0 : ℝ) ≤ 2 * (s : ℝ) - ((k₁ : ℝ) + (j : ℝ) - (n : ℝ) / 4))
            (by linarith : (0 : ℝ) ≤ ((k₁ : ℝ) + (j : ℝ) - (n : ℝ) / 4) + 2 * (s : ℝ))]
        have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos hn0 2
        calc 5000 * ((n : ℝ) + ((k₁ : ℝ) + (j : ℝ) - (n : ℝ) / 4) ^ 2) / (n : ℝ) ^ 2
            ≤ 5000 * ((n : ℝ) + 4 * (n : ℝ)) / (n : ℝ) ^ 2 := by gcongr
          _ = 25000 / (n : ℝ) := by
              rw [div_eq_div_iff hn2.ne' hn0.ne']; ring
    _ = 25000 * (s : ℝ) / (n : ℝ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-! ### Flatness of the log-profile over the `√n`-window -/

/-- **Right flatness**: for `n ≥ 10⁹`, a centre `|k₀ − n/4| ≤ 1` and any
`0 ≤ s ≤ ⌊√n⌋`, the log-profile moves by at most
`(drift ≤ 8 + 16s/n) + (error ≤ 25000·s/n) ≤ 9`:
`|log pmf'(n,k₀+s) − log pmf'(n,k₀)| ≤ 9`. -/
theorem abs_log_pmf'_window_right {n k₀ s : ℕ} (hn : 1000000000 ≤ n)
    (hk₀ : |(k₀ : ℝ) - (n : ℝ) / 4| ≤ 1) (hs : s ≤ Nat.sqrt n) :
    |Real.log (pmf' n (k₀ + s)) - Real.log (pmf' n k₀)| ≤ 9 := by
  have hnR : (1000000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hsq := cast_sq_le_of_le_sqrt hs
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := by positivity
  have hδ := abs_le.mp hk₀
  have hk₁ : |(k₀ : ℝ) - (n : ℝ) / 4| ≤ (s : ℝ) + 1 := hk₀.trans (by linarith)
  have h := abs_log_pmf'_sqrt_telescope hn hs hk₁
  have hs01 : (0 : ℝ) ≤ (s : ℝ) * ((s : ℝ) - 1) := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · simp [h0]
    · have h1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast h0
      nlinarith
  have hX : |(s : ℝ) * ((k₀ : ℝ) - (n : ℝ) / 4) + (s : ℝ) * ((s : ℝ) - 1) / 2|
      ≤ (s : ℝ) + (s : ℝ) ^ 2 / 2 := by
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg hs0
        (by linarith : (0 : ℝ) ≤ ((k₀ : ℝ) - (n : ℝ) / 4) + 1), sq_nonneg (s : ℝ)]
    · nlinarith [mul_nonneg hs0
        (by linarith : (0 : ℝ) ≤ 1 - ((k₀ : ℝ) - (n : ℝ) / 4)), sq_nonneg (s : ℝ)]
  have hDabs : |16 * ((s : ℝ) * ((k₀ : ℝ) - (n : ℝ) / 4)
      + (s : ℝ) * ((s : ℝ) - 1) / 2) / (n : ℝ)|
      ≤ 16 * (s : ℝ) / (n : ℝ) + 8 := by
    rw [abs_div, abs_of_pos hn0, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 16), div_le_iff₀ hn0]
    have hid : (16 * (s : ℝ) / (n : ℝ) + 8) * (n : ℝ)
        = 16 * (s : ℝ) + 8 * (n : ℝ) := by
      field_simp
    rw [hid]
    nlinarith [hX]
  set A := Real.log (pmf' n (k₀ + s)) - Real.log (pmf' n k₀) with hA
  set D := 16 * ((s : ℝ) * ((k₀ : ℝ) - (n : ℝ) / 4)
      + (s : ℝ) * ((s : ℝ) - 1) / 2) / (n : ℝ) with hD
  have htri : |A| ≤ |A + D| + |D| := by
    have h1 := abs_add_le (A + D) (-D)
    rw [abs_neg] at h1
    simpa using h1
  have hsn : 25016 * (s : ℝ) ≤ (n : ℝ) := by
    nlinarith [sq_nonneg ((s : ℝ) - 25016)]
  have hfrac : 25016 * (s : ℝ) / (n : ℝ) ≤ 1 := by
    rw [div_le_one hn0]; exact hsn
  have hsum : 25000 * (s : ℝ) / (n : ℝ) + 16 * (s : ℝ) / (n : ℝ)
      = 25016 * (s : ℝ) / (n : ℝ) := by ring
  linarith [htri, h, hDabs]

/-- **Left flatness** (mirror of `abs_log_pmf'_window_right`, telescoping
upward from `k₀ − s` to `k₀`): `|log pmf'(n,k₀) − log pmf'(n,k₀−s)| ≤ 9`. -/
theorem abs_log_pmf'_window_left {n k₀ s : ℕ} (hn : 1000000000 ≤ n)
    (hk₀ : |(k₀ : ℝ) - (n : ℝ) / 4| ≤ 1) (hs : s ≤ Nat.sqrt n) :
    |Real.log (pmf' n k₀) - Real.log (pmf' n (k₀ - s))| ≤ 9 := by
  have hnR : (1000000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hsq := cast_sq_le_of_le_sqrt hs
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := by positivity
  have hδ := abs_le.mp hk₀
  have hskR : (s : ℝ) ≤ (k₀ : ℝ) := by
    nlinarith [sq_nonneg ((s : ℝ) - 8)]
  have hsk : s ≤ k₀ := by exact_mod_cast hskR
  have hk₁ : |((k₀ - s : ℕ) : ℝ) - (n : ℝ) / 4| ≤ (s : ℝ) + 1 := by
    rw [Nat.cast_sub hsk, abs_le]
    constructor <;> linarith
  have h := abs_log_pmf'_sqrt_telescope hn hs hk₁
  rw [show k₀ - s + s = k₀ by omega, Nat.cast_sub hsk] at h
  have hs01 : (0 : ℝ) ≤ (s : ℝ) * ((s : ℝ) - 1) := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · simp [h0]
    · have h1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast h0
      nlinarith
  have hX : |(s : ℝ) * (((k₀ : ℝ) - (s : ℝ)) - (n : ℝ) / 4)
      + (s : ℝ) * ((s : ℝ) - 1) / 2|
      ≤ 3 / 2 * (s : ℝ) + (s : ℝ) ^ 2 / 2 := by
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg hs0
        (by linarith : (0 : ℝ) ≤ ((k₀ : ℝ) - (n : ℝ) / 4) + 1), sq_nonneg (s : ℝ)]
    · nlinarith [mul_nonneg hs0
        (by linarith : (0 : ℝ) ≤ 1 - ((k₀ : ℝ) - (n : ℝ) / 4)), sq_nonneg (s : ℝ)]
  have hDabs : |16 * ((s : ℝ) * (((k₀ : ℝ) - (s : ℝ)) - (n : ℝ) / 4)
      + (s : ℝ) * ((s : ℝ) - 1) / 2) / (n : ℝ)|
      ≤ 24 * (s : ℝ) / (n : ℝ) + 8 := by
    rw [abs_div, abs_of_pos hn0, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 16), div_le_iff₀ hn0]
    have hid : (24 * (s : ℝ) / (n : ℝ) + 8) * (n : ℝ)
        = 24 * (s : ℝ) + 8 * (n : ℝ) := by
      field_simp
    rw [hid]
    nlinarith [hX]
  set A := Real.log (pmf' n k₀) - Real.log (pmf' n (k₀ - s)) with hA
  set D := 16 * ((s : ℝ) * (((k₀ : ℝ) - (s : ℝ)) - (n : ℝ) / 4)
      + (s : ℝ) * ((s : ℝ) - 1) / 2) / (n : ℝ) with hD
  have htri : |A| ≤ |A + D| + |D| := by
    have h1 := abs_add_le (A + D) (-D)
    rw [abs_neg] at h1
    simpa using h1
  have hsn : 25024 * (s : ℝ) ≤ (n : ℝ) := by
    nlinarith [sq_nonneg ((s : ℝ) - 25024)]
  have hfrac : 25024 * (s : ℝ) / (n : ℝ) ≤ 1 := by
    rw [div_le_one hn0]; exact hsn
  have hsum : 25000 * (s : ℝ) / (n : ℝ) + 24 * (s : ℝ) / (n : ℝ)
      = 25024 * (s : ℝ) / (n : ℝ) := by ring
  linarith [htri, h, hDabs]

/-! ### Window transport, exponentiated

The four inequalities `e⁻⁹·pmf'(k₀) ≤ pmf'(k₀ ± s) ≤ e⁹·pmf'(k₀)` for
`0 ≤ s ≤ ⌊√n⌋`.  These are the Riemann-sum inputs of the self-normalisation:
the window sum of `pmf'` is `(⌊√n⌋+1)·pmf'(k₀)·e^{±9}`-comparable. -/

/-- **Window lower bound (right)**: `pmf'(k₀)·e⁻⁹ ≤ pmf'(k₀+s)` for
`s ≤ ⌊√n⌋`. -/
theorem pmf'_window_lower {n k₀ s : ℕ} (hn : 1000000000 ≤ n)
    (hk₀ : |(k₀ : ℝ) - (n : ℝ) / 4| ≤ 1) (hs : s ≤ Nat.sqrt n) :
    pmf' n k₀ * Real.exp (-9) ≤ pmf' n (k₀ + s) := by
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := by positivity
  have hk₁ : |(k₀ : ℝ) - (n : ℝ) / 4| ≤ (s : ℝ) + 1 := hk₀.trans (by linarith)
  have hguard := guard_of_near hn hs hk₁
  have hp1 : 0 < pmf' n (k₀ + s) := pmf'_pos hguard
  have hp0 : 0 < pmf' n k₀ := pmf'_pos (by omega)
  have habs := abs_log_pmf'_window_right hn hk₀ hs
  have hlow := (abs_le.mp habs).1
  calc pmf' n k₀ * Real.exp (-9)
      = Real.exp (Real.log (pmf' n k₀) + -9) := by
        rw [Real.exp_add, Real.exp_log hp0]
    _ ≤ Real.exp (Real.log (pmf' n (k₀ + s))) := Real.exp_le_exp.mpr (by linarith)
    _ = pmf' n (k₀ + s) := Real.exp_log hp1

/-- **Window upper bound (right)**: `pmf'(k₀+s) ≤ pmf'(k₀)·e⁹` for
`s ≤ ⌊√n⌋`. -/
theorem pmf'_window_upper {n k₀ s : ℕ} (hn : 1000000000 ≤ n)
    (hk₀ : |(k₀ : ℝ) - (n : ℝ) / 4| ≤ 1) (hs : s ≤ Nat.sqrt n) :
    pmf' n (k₀ + s) ≤ pmf' n k₀ * Real.exp 9 := by
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := by positivity
  have hk₁ : |(k₀ : ℝ) - (n : ℝ) / 4| ≤ (s : ℝ) + 1 := hk₀.trans (by linarith)
  have hguard := guard_of_near hn hs hk₁
  have hp1 : 0 < pmf' n (k₀ + s) := pmf'_pos hguard
  have hp0 : 0 < pmf' n k₀ := pmf'_pos (by omega)
  have habs := abs_log_pmf'_window_right hn hk₀ hs
  have hup := (abs_le.mp habs).2
  calc pmf' n (k₀ + s) = Real.exp (Real.log (pmf' n (k₀ + s))) :=
        (Real.exp_log hp1).symm
    _ ≤ Real.exp (Real.log (pmf' n k₀) + 9) := Real.exp_le_exp.mpr (by linarith)
    _ = pmf' n k₀ * Real.exp 9 := by rw [Real.exp_add, Real.exp_log hp0]

/-- **Window lower bound (left mirror)**: `pmf'(k₀)·e⁻⁹ ≤ pmf'(k₀−s)` for
`s ≤ ⌊√n⌋`. -/
theorem pmf'_window_lower_left {n k₀ s : ℕ} (hn : 1000000000 ≤ n)
    (hk₀ : |(k₀ : ℝ) - (n : ℝ) / 4| ≤ 1) (hs : s ≤ Nat.sqrt n) :
    pmf' n k₀ * Real.exp (-9) ≤ pmf' n (k₀ - s) := by
  have hk₁ : |(k₀ : ℝ) - (n : ℝ) / 4| ≤ ((0 : ℕ) : ℝ) + 1 := by
    simpa using hk₀
  have hguard := guard_of_near hn (Nat.zero_le _) hk₁
  have hp0 : 0 < pmf' n k₀ := pmf'_pos (by omega)
  have hp2 : 0 < pmf' n (k₀ - s) := pmf'_pos (by omega)
  have habs := abs_log_pmf'_window_left hn hk₀ hs
  have hup := (abs_le.mp habs).2
  calc pmf' n k₀ * Real.exp (-9)
      = Real.exp (Real.log (pmf' n k₀) + -9) := by
        rw [Real.exp_add, Real.exp_log hp0]
    _ ≤ Real.exp (Real.log (pmf' n (k₀ - s))) := Real.exp_le_exp.mpr (by linarith)
    _ = pmf' n (k₀ - s) := Real.exp_log hp2

/-- **Window upper bound (left mirror)**: `pmf'(k₀−s) ≤ pmf'(k₀)·e⁹` for
`s ≤ ⌊√n⌋`. -/
theorem pmf'_window_upper_left {n k₀ s : ℕ} (hn : 1000000000 ≤ n)
    (hk₀ : |(k₀ : ℝ) - (n : ℝ) / 4| ≤ 1) (hs : s ≤ Nat.sqrt n) :
    pmf' n (k₀ - s) ≤ pmf' n k₀ * Real.exp 9 := by
  have hk₁ : |(k₀ : ℝ) - (n : ℝ) / 4| ≤ ((0 : ℕ) : ℝ) + 1 := by
    simpa using hk₀
  have hguard := guard_of_near hn (Nat.zero_le _) hk₁
  have hp0 : 0 < pmf' n k₀ := pmf'_pos (by omega)
  have hp2 : 0 < pmf' n (k₀ - s) := pmf'_pos (by omega)
  have habs := abs_log_pmf'_window_left hn hk₀ hs
  have hlow := (abs_le.mp habs).1
  calc pmf' n (k₀ - s) = Real.exp (Real.log (pmf' n (k₀ - s))) :=
        (Real.exp_log hp2).symm
    _ ≤ Real.exp (Real.log (pmf' n k₀) + 9) := Real.exp_le_exp.mpr (by linarith)
    _ = pmf' n k₀ * Real.exp 9 := by rw [Real.exp_add, Real.exp_log hp0]

/-! ### The mode upper bound, by self-normalisation

The window `[k₀, k₀ + ⌊√n⌋]` carries mass `≥ (⌊√n⌋+1)·e⁻⁹·pmf'(k₀)` by
`pmf'_window_lower`; since the total mass is `1` (hypothesis `hnorm`), the
mode value is at most `e⁹/(⌊√n⌋+1) ≤ 8104/√n`. -/

/-- **Mode upper bound**, conditional on the normalisation
`hnorm : Σ_{k<n} pmf' n k = 1` (discharged by `sum_pmf'_of_closed` once the
closed form `U_mul_closed` is proved): for `n ≥ 10⁹` and `|k₀ − n/4| ≤ 1`,

  `pmf' n k₀ ≤ 8104 / √n`. -/
theorem mode_upper {n k₀ : ℕ} (hn : 1000000000 ≤ n)
    (hk₀ : |(k₀ : ℝ) - (n : ℝ) / 4| ≤ 1)
    (hnorm : ∑ k ∈ range n, pmf' n k = 1) :
    pmf' n k₀ ≤ 8104 / Real.sqrt n := by
  have hnR : (1000000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hm0 : (0 : ℝ) ≤ ((Nat.sqrt n : ℕ) : ℝ) := by positivity
  have hk₁ : |(k₀ : ℝ) - (n : ℝ) / 4| ≤ ((Nat.sqrt n : ℕ) : ℝ) + 1 :=
    hk₀.trans (by linarith)
  have hguard := guard_of_near hn le_rfl hk₁
  -- the window sits inside `range n` and its mass is at most `1`
  have hsub : Ico k₀ (k₀ + Nat.sqrt n + 1) ⊆ range n := by
    intro x hx
    rw [Finset.mem_Ico] at hx
    rw [Finset.mem_range]
    omega
  have hW1 : ∑ k ∈ Ico k₀ (k₀ + Nat.sqrt n + 1), pmf' n k ≤ 1 := by
    rw [← hnorm]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => pmf'_nonneg n i
  -- the window mass dominates `(⌊√n⌋+1)·e⁻⁹·pmf'(k₀)`
  have hWlow : (((Nat.sqrt n : ℕ) : ℝ) + 1) * (pmf' n k₀ * Real.exp (-9))
      ≤ ∑ k ∈ Ico k₀ (k₀ + Nat.sqrt n + 1), pmf' n k := by
    rw [Finset.sum_Ico_eq_sum_range,
      show k₀ + Nat.sqrt n + 1 - k₀ = Nat.sqrt n + 1 by omega]
    calc (((Nat.sqrt n : ℕ) : ℝ) + 1) * (pmf' n k₀ * Real.exp (-9))
        = ∑ _j ∈ range (Nat.sqrt n + 1), pmf' n k₀ * Real.exp (-9) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast; ring
      _ ≤ ∑ j ∈ range (Nat.sqrt n + 1), pmf' n (k₀ + j) :=
          Finset.sum_le_sum fun j hj =>
            pmf'_window_lower hn hk₀ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  have hkey : (((Nat.sqrt n : ℕ) : ℝ) + 1) * (pmf' n k₀ * Real.exp (-9)) ≤ 1 :=
    hWlow.trans hW1
  -- unfold the `e⁻⁹` normalisation
  have hexp : Real.exp (-9) * Real.exp 9 = 1 := by
    rw [← Real.exp_add]; norm_num
  have hm1 : (0 : ℝ) < ((Nat.sqrt n : ℕ) : ℝ) + 1 := by positivity
  have hp : pmf' n k₀ * (((Nat.sqrt n : ℕ) : ℝ) + 1) ≤ Real.exp 9 := by
    calc pmf' n k₀ * (((Nat.sqrt n : ℕ) : ℝ) + 1)
        = ((((Nat.sqrt n : ℕ) : ℝ) + 1) * (pmf' n k₀ * Real.exp (-9)))
            * Real.exp 9 := by
          linear_combination
            (-((((Nat.sqrt n : ℕ) : ℝ) + 1) * pmf' n k₀)) * hexp
      _ ≤ 1 * Real.exp 9 := mul_le_mul_of_nonneg_right hkey (Real.exp_pos 9).le
      _ = Real.exp 9 := one_mul _
  -- compare `⌊√n⌋ + 1` with `√n`
  have hsqrt_le : Real.sqrt n ≤ ((Nat.sqrt n : ℕ) : ℝ) + 1 := by
    rw [show ((Nat.sqrt n : ℕ) : ℝ) + 1 = ((Nat.sqrt n + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.sqrt_le_left (by positivity)]
    have h : n < (Nat.sqrt n + 1) ^ 2 := Nat.lt_succ_sqrt' n
    exact_mod_cast h.le
  have hsqrt0 : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn0
  calc pmf' n k₀ ≤ Real.exp 9 / (((Nat.sqrt n : ℕ) : ℝ) + 1) := by
        rw [le_div_iff₀ hm1]; exact hp
    _ ≤ 8104 / (((Nat.sqrt n : ℕ) : ℝ) + 1) := by gcongr; exact exp_nine_le
    _ ≤ 8104 / Real.sqrt n :=
        div_le_div_of_nonneg_left (by norm_num) hsqrt0 hsqrt_le

/-! ### Uniform geometric decay beyond the `√n`-window

At distance `≥ √n − 1` to the right of `n/4` the one-step ratio is uniformly
`≤ 1 − 7√n/n` (from the exact ratio: polynomially for `k ≤ 5n/16`, from the
crude tail bound `pmfRatio ≤ 3/4` beyond, and trivially past the support).
Mirror on the left with `≥ 1 + 7√n/n`.  Consequently each far tail sums to at
most `n/(7√n) + 1 ≈ √n/7` times its boundary value — the same `√n` scale as
the window itself, which is what makes the self-normalisation close. -/

/-- Ratio bound in the right intermediate region `n/4 + σ − 1 ≤ k ≤ 5n/16`
(with `σ = ⌊√n⌋ ≥ 30000`, `σ² ≤ n`): `pmfRatio n k ≤ 1 − 7σ/n`.
(public: reused by `ModePrefactorMain`) -/
lemma pmfRatio_le_far_right {n k s₀ : ℕ} (hn : 1000000000 ≤ n)
    (hσsq : ((s₀ : ℝ)) ^ 2 ≤ (n : ℝ)) (hσ30 : 30000 ≤ s₀)
    (hfar : (n : ℝ) / 4 + (s₀ : ℝ) - 1 ≤ (k : ℝ))
    (hk5 : 16 * (k : ℝ) ≤ 5 * (n : ℝ)) (h3 : 2 * k + 3 ≤ n) :
    pmfRatio n k ≤ 1 - 7 * (s₀ : ℝ) / (n : ℝ) := by
  have hnR : (1000000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hσR : (30000 : ℝ) ≤ (s₀ : ℝ) := by exact_mod_cast hσ30
  have hσn : 7 * (s₀ : ℝ) ≤ (n : ℝ) := by nlinarith
  have h3R : 2 * (k : ℝ) + 3 ≤ (n : ℝ) := by exact_mod_cast h3
  have hD : (0 : ℝ) < 4 * ((k : ℝ) + 1) * ((k : ℝ) + 2) := by positivity
  rw [pmfRatio, div_le_iff₀ hD,
    show (1 : ℝ) - 7 * (s₀ : ℝ) / (n : ℝ) = ((n : ℝ) - 7 * (s₀ : ℝ)) / (n : ℝ) by
      field_simp,
    div_mul_eq_mul_div, le_div_iff₀ hn0]
  -- N·n ≤ (n − 7σ)·D with N ≤ (n/2 − 2σ + 1)² and D ≥ 4(n/4 + σ)²
  have h2σ : 2 * (s₀ : ℝ) ≤ (n : ℝ) / 2 := by nlinarith
  have hf1 : (0 : ℝ) ≤ (n : ℝ) - 2 * (k : ℝ) - 2 := by linarith
  have hf2 : (n : ℝ) - 2 * (k : ℝ) - 1 ≤ (n : ℝ) / 2 - 2 * (s₀ : ℝ) + 1 := by
    linarith
  have hf3 : (n : ℝ) - 2 * (k : ℝ) - 2 ≤ (n : ℝ) / 2 - 2 * (s₀ : ℝ) + 1 := by
    linarith
  have hN : ((n : ℝ) - 2 * (k : ℝ) - 1) * ((n : ℝ) - 2 * (k : ℝ) - 2)
      ≤ ((n : ℝ) / 2 - 2 * (s₀ : ℝ) + 1) ^ 2 := by
    rw [sq]
    exact mul_le_mul hf2 hf3 hf1
      (by linarith : (0 : ℝ) ≤ (n : ℝ) / 2 - 2 * (s₀ : ℝ) + 1)
  have hg1 : (n : ℝ) / 4 + (s₀ : ℝ) ≤ (k : ℝ) + 1 := by linarith
  have hg2 : (n : ℝ) / 4 + (s₀ : ℝ) ≤ (k : ℝ) + 2 := by linarith
  have hD2 : 4 * ((n : ℝ) / 4 + (s₀ : ℝ)) ^ 2
      ≤ 4 * ((k : ℝ) + 1) * ((k : ℝ) + 2) := by
    have h := mul_le_mul hg1 hg2 (by positivity)
      (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)
    calc 4 * ((n : ℝ) / 4 + (s₀ : ℝ)) ^ 2
        = 4 * (((n : ℝ) / 4 + (s₀ : ℝ)) * ((n : ℝ) / 4 + (s₀ : ℝ))) := by ring
      _ ≤ 4 * (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by linarith
      _ = 4 * ((k : ℝ) + 1) * ((k : ℝ) + 2) := by ring
  have hn7σ : (0 : ℝ) ≤ (n : ℝ) - 7 * (s₀ : ℝ) := by linarith
  have hσlen : (s₀ : ℝ) ≤ (n : ℝ) := by nlinarith
  have hmid : ((n : ℝ) / 2 - 2 * (s₀ : ℝ) + 1) ^ 2 * (n : ℝ)
      ≤ ((n : ℝ) - 7 * (s₀ : ℝ)) * (4 * ((n : ℝ) / 4 + (s₀ : ℝ)) ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hσsq
        (by linarith : (0 : ℝ) ≤ 14 * (n : ℝ)),
      mul_le_mul_of_nonneg_left hσsq
        (by positivity : (0 : ℝ) ≤ 28 * (s₀ : ℝ)),
      mul_le_mul_of_nonneg_right hσR (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2),
      mul_le_mul_of_nonneg_left hσlen
        (by linarith : (0 : ℝ) ≤ 24 * (n : ℝ))]
  calc ((n : ℝ) - 2 * (k : ℝ) - 1) * ((n : ℝ) - 2 * (k : ℝ) - 2) * (n : ℝ)
      ≤ ((n : ℝ) / 2 - 2 * (s₀ : ℝ) + 1) ^ 2 * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hN hn0.le
    _ ≤ ((n : ℝ) - 7 * (s₀ : ℝ)) * (4 * ((n : ℝ) / 4 + (s₀ : ℝ)) ^ 2) := hmid
    _ ≤ ((n : ℝ) - 7 * (s₀ : ℝ)) * (4 * ((k : ℝ) + 1) * ((k : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hD2 hn7σ

/-- Ratio bound in the left far region `k ≤ n/4 − σ`
(with `σ = ⌊√n⌋ ≥ 30000`, `σ² ≤ n`): `pmfRatio n k ≥ 1 + 7σ/n`.
(public: reused by `ModePrefactorMain`) -/
lemma le_pmfRatio_far_left {n k s₀ : ℕ} (hn : 1000000000 ≤ n)
    (hσsq : ((s₀ : ℝ)) ^ 2 ≤ (n : ℝ)) (hσ30 : 30000 ≤ s₀)
    (hfar : (k : ℝ) ≤ (n : ℝ) / 4 - (s₀ : ℝ)) :
    1 + 7 * (s₀ : ℝ) / (n : ℝ) ≤ pmfRatio n k := by
  have hnR : (1000000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hσR : (30000 : ℝ) ≤ (s₀ : ℝ) := by exact_mod_cast hσ30
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hD : (0 : ℝ) < 4 * ((k : ℝ) + 1) * ((k : ℝ) + 2) := by positivity
  rw [pmfRatio, le_div_iff₀ hD,
    show (1 : ℝ) + 7 * (s₀ : ℝ) / (n : ℝ) = ((n : ℝ) + 7 * (s₀ : ℝ)) / (n : ℝ) by
      field_simp,
    div_mul_eq_mul_div, div_le_iff₀ hn0]
  -- (n + 7σ)·D ≤ N·n with N ≥ (n/2 + 2σ − 2)² and D ≤ 4(n/4 − σ + 2)²
  have hσn : 7 * (s₀ : ℝ) ≤ (n : ℝ) := by nlinarith
  have hσlen : (s₀ : ℝ) ≤ (n : ℝ) := by nlinarith
  have ha : (n : ℝ) / 2 + 2 * (s₀ : ℝ) - 2 ≤ (n : ℝ) - 2 * (k : ℝ) - 2 := by
    linarith
  have hb : (n : ℝ) / 2 + 2 * (s₀ : ℝ) - 2 ≤ (n : ℝ) - 2 * (k : ℝ) - 1 := by
    linarith
  have h0 : (0 : ℝ) ≤ (n : ℝ) / 2 + 2 * (s₀ : ℝ) - 2 := by linarith
  have hN : ((n : ℝ) / 2 + 2 * (s₀ : ℝ) - 2) ^ 2
      ≤ ((n : ℝ) - 2 * (k : ℝ) - 1) * ((n : ℝ) - 2 * (k : ℝ) - 2) := by
    rw [sq]
    exact mul_le_mul hb ha h0
      (by linarith : (0 : ℝ) ≤ (n : ℝ) - 2 * (k : ℝ) - 1)
  have hc : (k : ℝ) + 1 ≤ (n : ℝ) / 4 - (s₀ : ℝ) + 2 := by linarith
  have hd : (k : ℝ) + 2 ≤ (n : ℝ) / 4 - (s₀ : ℝ) + 2 := by linarith
  have hD2 : 4 * ((k : ℝ) + 1) * ((k : ℝ) + 2)
      ≤ 4 * ((n : ℝ) / 4 - (s₀ : ℝ) + 2) ^ 2 := by
    have h := mul_le_mul hc hd (by positivity : (0 : ℝ) ≤ (k : ℝ) + 2)
      (by linarith : (0 : ℝ) ≤ (n : ℝ) / 4 - (s₀ : ℝ) + 2)
    calc 4 * ((k : ℝ) + 1) * ((k : ℝ) + 2)
        = 4 * (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by ring
      _ ≤ 4 * (((n : ℝ) / 4 - (s₀ : ℝ) + 2) * ((n : ℝ) / 4 - (s₀ : ℝ) + 2)) := by
          linarith
      _ = 4 * ((n : ℝ) / 4 - (s₀ : ℝ) + 2) ^ 2 := by ring
  have hmid : ((n : ℝ) + 7 * (s₀ : ℝ)) * (4 * ((n : ℝ) / 4 - (s₀ : ℝ) + 2) ^ 2)
      ≤ ((n : ℝ) / 2 + 2 * (s₀ : ℝ) - 2) ^ 2 * (n : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hσsq
        (by positivity : (0 : ℝ) ≤ 28 * (s₀ : ℝ)),
      mul_le_mul_of_nonneg_right hσR (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2),
      mul_le_mul_of_nonneg_left hσlen
        (by linarith : (0 : ℝ) ≤ 48 * (n : ℝ)),
      mul_le_mul_of_nonneg_left hσsq (by norm_num : (0 : ℝ) ≤ 14)]
  calc ((n : ℝ) + 7 * (s₀ : ℝ)) * (4 * ((k : ℝ) + 1) * ((k : ℝ) + 2))
      ≤ ((n : ℝ) + 7 * (s₀ : ℝ)) * (4 * ((n : ℝ) / 4 - (s₀ : ℝ) + 2) ^ 2) := by
        have h7 : (0 : ℝ) ≤ (n : ℝ) + 7 * (s₀ : ℝ) := by linarith
        exact mul_le_mul_of_nonneg_left hD2 h7
    _ ≤ ((n : ℝ) / 2 + 2 * (s₀ : ℝ) - 2) ^ 2 * (n : ℝ) := hmid
    _ ≤ ((n : ℝ) - 2 * (k : ℝ) - 1) * ((n : ℝ) - 2 * (k : ℝ) - 2) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hN hn0.le

/-- One-step decay everywhere to the right of `n/4 + σ − 1` (intermediate
region, geometric tail region, and past the support alike):
`pmf'(k+1) ≤ pmf'(k)·(1 − 7σ/n)`.
(public: reused by `ModePrefactorMain`) -/
lemma pmf'_succ_le_far_right {n k s₀ : ℕ} (hn : 1000000000 ≤ n)
    (hσsq : ((s₀ : ℝ)) ^ 2 ≤ (n : ℝ)) (hσ30 : 30000 ≤ s₀)
    (hfar : (n : ℝ) / 4 + (s₀ : ℝ) - 1 ≤ (k : ℝ)) :
    pmf' n (k + 1) ≤ pmf' n k * (1 - 7 * (s₀ : ℝ) / (n : ℝ)) := by
  have hnR : (1000000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hσR : (30000 : ℝ) ≤ (s₀ : ℝ) := by exact_mod_cast hσ30
  have hσn : 7 * (s₀ : ℝ) ≤ (n : ℝ) := by nlinarith
  have hfac : (0 : ℝ) ≤ 1 - 7 * (s₀ : ℝ) / (n : ℝ) := by
    rw [sub_nonneg, div_le_one hn0]; exact hσn
  by_cases h3 : 2 * k + 3 ≤ n
  · rw [pmf'_succ_eq h3]
    refine mul_le_mul_of_nonneg_left ?_ (pmf'_nonneg n k)
    by_cases hk5 : 5 * n ≤ 16 * k
    · -- geometric tail region: `pmfRatio ≤ 3/4 ≤ 1 − 7σ/n` since `28σ ≤ n`
      have h34 := pmfRatio_le_of_ge hk5 h3
      have h28 : 28 * (s₀ : ℝ) ≤ (n : ℝ) := by nlinarith
      have : 7 * (s₀ : ℝ) / (n : ℝ) ≤ 1 / 4 := by
        rw [div_le_div_iff₀ hn0 (by norm_num : (0 : ℝ) < 4)]
        linarith
      linarith
    · have hk' : 16 * (k : ℝ) ≤ 5 * (n : ℝ) := by
        exact_mod_cast (show 16 * k ≤ 5 * n by omega)
      exact pmfRatio_le_far_right hn hσsq hσ30 hfar hk' h3
  · rw [pmf'_eq_zero (show n < 2 * (k + 1) + 1 by omega)]
    exact mul_nonneg (pmf'_nonneg n k) hfac

/-- One-step growth everywhere in the left far region `k ≤ n/4 − σ`:
`pmf'(k)·(1 + 7σ/n) ≤ pmf'(k+1)`.
(public: reused by `ModePrefactorMain`) -/
lemma pmf'_le_succ_far_left {n k s₀ : ℕ} (hn : 1000000000 ≤ n)
    (hσsq : ((s₀ : ℝ)) ^ 2 ≤ (n : ℝ)) (hσ30 : 30000 ≤ s₀)
    (hfar : (k : ℝ) ≤ (n : ℝ) / 4 - (s₀ : ℝ)) :
    pmf' n k * (1 + 7 * (s₀ : ℝ) / (n : ℝ)) ≤ pmf' n (k + 1) := by
  have hnR : (1000000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hσR : (30000 : ℝ) ≤ (s₀ : ℝ) := by exact_mod_cast hσ30
  have h3 : 2 * k + 3 ≤ n := by
    have h3R : ((2 * k + 3 : ℕ) : ℝ) ≤ (n : ℝ) := by push_cast; linarith
    exact_mod_cast h3R
  rw [pmf'_succ_eq h3]
  exact mul_le_mul_of_nonneg_left (le_pmfRatio_far_left hn hσsq hσ30 hfar)
    (pmf'_nonneg n k)

/-- Telescoped decay right of `n/4 + σ − 1`:
`pmf'(b+j) ≤ pmf'(b)·(1 − 7σ/n)^j` for every `j`.
(public: reused by `ModePrefactorMain`) -/
lemma pmf'_add_le_far_right {n b s₀ : ℕ} (hn : 1000000000 ≤ n)
    (hσsq : ((s₀ : ℝ)) ^ 2 ≤ (n : ℝ)) (hσ30 : 30000 ≤ s₀)
    (hb : (n : ℝ) / 4 + (s₀ : ℝ) - 1 ≤ (b : ℝ)) (j : ℕ) :
    pmf' n (b + j) ≤ pmf' n b * (1 - 7 * (s₀ : ℝ) / (n : ℝ)) ^ j := by
  have hnR : (1000000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hσR : (30000 : ℝ) ≤ (s₀ : ℝ) := by exact_mod_cast hσ30
  have hσn : 7 * (s₀ : ℝ) ≤ (n : ℝ) := by nlinarith
  have hfac : (0 : ℝ) ≤ 1 - 7 * (s₀ : ℝ) / (n : ℝ) := by
    rw [sub_nonneg, div_le_one hn0]; exact hσn
  induction j with
  | zero => simp
  | succ m ih =>
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
    have hstep := pmf'_succ_le_far_right hn hσsq hσ30
      (show (n : ℝ) / 4 + (s₀ : ℝ) - 1 ≤ ((b + m : ℕ) : ℝ) by push_cast; linarith)
    calc pmf' n (b + (m + 1)) = pmf' n ((b + m) + 1) := by
          rw [show b + (m + 1) = (b + m) + 1 by omega]
      _ ≤ pmf' n (b + m) * (1 - 7 * (s₀ : ℝ) / (n : ℝ)) := hstep
      _ ≤ (pmf' n b * (1 - 7 * (s₀ : ℝ) / (n : ℝ)) ^ m)
            * (1 - 7 * (s₀ : ℝ) / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right ih hfac
      _ = pmf' n b * (1 - 7 * (s₀ : ℝ) / (n : ℝ)) ^ (m + 1) := by ring

/-- Telescoped decay left of a base `b ≤ n/4 − σ + 1`:
`pmf'(b−j) ≤ pmf'(b)·(n/(n+7σ))^j` for every `j ≤ b`.
(public: reused by `ModePrefactorMain`) -/
lemma pmf'_sub_le_far_left {n b s₀ : ℕ} (hn : 1000000000 ≤ n)
    (hσsq : ((s₀ : ℝ)) ^ 2 ≤ (n : ℝ)) (hσ30 : 30000 ≤ s₀)
    (hb : (b : ℝ) ≤ (n : ℝ) / 4 - (s₀ : ℝ) + 1) :
    ∀ j, j ≤ b → pmf' n (b - j)
      ≤ pmf' n b * ((n : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ))) ^ j := by
  have hnR : (1000000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hσR : (30000 : ℝ) ≤ (s₀ : ℝ) := by exact_mod_cast hσ30
  have hden : (0 : ℝ) < (n : ℝ) + 7 * (s₀ : ℝ) := by linarith
  intro j
  induction j with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have hb1 : 1 ≤ b := by omega
    have hkfar : ((b - m - 1 : ℕ) : ℝ) ≤ (n : ℝ) / 4 - (s₀ : ℝ) := by
      have h1 : b - m - 1 ≤ b - 1 := by omega
      have h2 : ((b - m - 1 : ℕ) : ℝ) ≤ ((b - 1 : ℕ) : ℝ) := by exact_mod_cast h1
      have h3 : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
        rw [Nat.cast_sub hb1]; norm_num
      rw [h3] at h2
      linarith
    have hstep := pmf'_le_succ_far_left hn hσsq hσ30 hkfar
    rw [show b - m - 1 + 1 = b - m by omega] at hstep
    have hρ : pmf' n (b - m - 1)
        ≤ pmf' n (b - m) * ((n : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ))) := by
      have hid : pmf' n (b - m - 1)
          = pmf' n (b - m - 1) * (1 + 7 * (s₀ : ℝ) / (n : ℝ))
              * ((n : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ))) := by
        field_simp
      rw [hid]
      exact mul_le_mul_of_nonneg_right hstep (by positivity)
    rw [show b - (m + 1) = b - m - 1 by omega]
    calc pmf' n (b - m - 1)
        ≤ pmf' n (b - m) * ((n : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ))) := hρ
      _ ≤ (pmf' n b * ((n : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ))) ^ m)
            * ((n : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ))) :=
          mul_le_mul_of_nonneg_right (ih (by omega)) (by positivity)
      _ = pmf' n b * ((n : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ))) ^ (m + 1) := by ring

/-! ### The mode lower bound

Split `1 = Σ_{k<n} pmf'` at `a := k₀ − ⌊√n⌋` and `b := k₀ + ⌊√n⌋`:

* head `Σ_{k ≤ a}`: geometric with ratio `n/(n+7σ)`, sums to
  `≤ pmf'(a)·(n/(7σ) + 1)`;
* window `Σ_{a < k < b}`: at most `2σ` terms, each `≤ e⁹·pmf'(k₀)`;
* tail `Σ_{b ≤ k < n}`: geometric with ratio `1 − 7σ/n`, sums to
  `≤ pmf'(b)·n/(7σ)`;

and `pmf'(a), pmf'(b) ≤ e⁹·pmf'(k₀)` by window transport.  With
`n < (σ+1)²` all three pieces are `≤ e⁹·pmf'(k₀)·O(σ)`, giving
`1 ≤ 25000·√n·pmf'(k₀)`. -/

/-- **Mode lower bound**, conditional on the normalisation
`hnorm : Σ_{k<n} pmf' n k = 1` (discharged by `sum_pmf'_of_closed` once the
closed form `U_mul_closed` is proved): for `n ≥ 10⁹` and `|k₀ − n/4| ≤ 1`,

  `1/(25000·√n) ≤ pmf' n k₀`. -/
theorem mode_lower {n k₀ : ℕ} (hn : 1000000000 ≤ n)
    (hk₀ : |(k₀ : ℝ) - (n : ℝ) / 4| ≤ 1)
    (hnorm : ∑ k ∈ range n, pmf' n k = 1) :
    1 / (25000 * Real.sqrt n) ≤ pmf' n k₀ := by
  have hnR : (1000000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hδ := abs_le.mp hk₀
  set s₀ := Nat.sqrt n with hs₀def
  have hσsq : ((s₀ : ℝ)) ^ 2 ≤ (n : ℝ) := cast_sq_le_of_le_sqrt le_rfl
  have hσ30 : 30000 ≤ s₀ := Nat.le_sqrt.mpr (by omega)
  have hσR : (30000 : ℝ) ≤ (s₀ : ℝ) := by exact_mod_cast hσ30
  have hσn : 7 * (s₀ : ℝ) ≤ (n : ℝ) := by nlinarith
  -- `σ ≤ k₀` so that `a = k₀ − σ` behaves; and the support guard at `b`
  have hskR : (s₀ : ℝ) ≤ (k₀ : ℝ) := by
    nlinarith [sq_nonneg ((s₀ : ℝ) - 8)]
  have hsk : s₀ ≤ k₀ := by exact_mod_cast hskR
  have hk₁ : |(k₀ : ℝ) - (n : ℝ) / 4| ≤ (s₀ : ℝ) + 1 := hk₀.trans (by linarith)
  have hguard := guard_of_near hn le_rfl hk₁
  have hbn : k₀ + s₀ ≤ n := by omega
  have hcast_a : ((k₀ - s₀ : ℕ) : ℝ) = (k₀ : ℝ) - (s₀ : ℝ) := Nat.cast_sub hsk
  -- the three pieces
  have hsplit1 : ∑ k ∈ range (k₀ - s₀ + 1), pmf' n k
      + ∑ k ∈ Ico (k₀ - s₀ + 1) n, pmf' n k = ∑ k ∈ range n, pmf' n k :=
    Finset.sum_range_add_sum_Ico _ (by omega)
  have hsplit2 : ∑ k ∈ Ico (k₀ - s₀ + 1) (k₀ + s₀), pmf' n k
      + ∑ k ∈ Ico (k₀ + s₀) n, pmf' n k = ∑ k ∈ Ico (k₀ - s₀ + 1) n, pmf' n k :=
    Finset.sum_Ico_consecutive _ (by omega) (by omega)
  -- head: geometric down from `a = k₀ − σ`
  have hA : ∑ k ∈ range (k₀ - s₀ + 1), pmf' n k
      ≤ pmf' n (k₀ - s₀) * (((n : ℝ) + 7 * (s₀ : ℝ)) / (7 * (s₀ : ℝ))) := by
    have hbase : ((k₀ - s₀ : ℕ) : ℝ) ≤ (n : ℝ) / 4 - (s₀ : ℝ) + 1 := by
      rw [hcast_a]; linarith
    calc ∑ k ∈ range (k₀ - s₀ + 1), pmf' n k
        = ∑ j ∈ range (k₀ - s₀ + 1), pmf' n (k₀ - s₀ - j) :=
          (Finset.sum_range_reflect (fun k => pmf' n k) (k₀ - s₀ + 1)).symm
      _ ≤ ∑ j ∈ range (k₀ - s₀ + 1),
            pmf' n (k₀ - s₀) * ((n : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ))) ^ j :=
          Finset.sum_le_sum fun j hj =>
            pmf'_sub_le_far_left hn hσsq hσ30 hbase j
              (by have := Finset.mem_range.mp hj; omega)
      _ = pmf' n (k₀ - s₀)
            * ∑ j ∈ range (k₀ - s₀ + 1),
                ((n : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ))) ^ j := by
          rw [Finset.mul_sum]
      _ ≤ pmf' n (k₀ - s₀) * (((n : ℝ) + 7 * (s₀ : ℝ)) / (7 * (s₀ : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (pmf'_nonneg n _)
          have hden : (0 : ℝ) < (n : ℝ) + 7 * (s₀ : ℝ) := by linarith
          have hx0 : (0 : ℝ) < 7 * (s₀ : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ)) := by
            positivity
          have hx1 : 7 * (s₀ : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ)) ≤ 1 := by
            rw [div_le_one hden]; linarith
          have h1x : (1 : ℝ) - 7 * (s₀ : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ))
              = (n : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ)) := by
            field_simp
            ring
          have hg := geom_sum_le_inv hx0 hx1 (k₀ - s₀ + 1)
          rw [h1x, one_div_div] at hg
          exact hg
  -- tail: geometric up from `b = k₀ + σ`
  have hC : ∑ k ∈ Ico (k₀ + s₀) n, pmf' n k
      ≤ pmf' n (k₀ + s₀) * ((n : ℝ) / (7 * (s₀ : ℝ))) := by
    have hbase : (n : ℝ) / 4 + (s₀ : ℝ) - 1 ≤ ((k₀ + s₀ : ℕ) : ℝ) := by
      push_cast; linarith
    rw [Finset.sum_Ico_eq_sum_range]
    calc ∑ j ∈ range (n - (k₀ + s₀)), pmf' n ((k₀ + s₀) + j)
        ≤ ∑ j ∈ range (n - (k₀ + s₀)),
            pmf' n (k₀ + s₀) * (1 - 7 * (s₀ : ℝ) / (n : ℝ)) ^ j :=
          Finset.sum_le_sum fun j _ =>
            pmf'_add_le_far_right hn hσsq hσ30 hbase j
      _ = pmf' n (k₀ + s₀)
            * ∑ j ∈ range (n - (k₀ + s₀)), (1 - 7 * (s₀ : ℝ) / (n : ℝ)) ^ j := by
          rw [Finset.mul_sum]
      _ ≤ pmf' n (k₀ + s₀) * ((n : ℝ) / (7 * (s₀ : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (pmf'_nonneg n _)
          have hy0 : (0 : ℝ) < 7 * (s₀ : ℝ) / (n : ℝ) := by positivity
          have hy1 : 7 * (s₀ : ℝ) / (n : ℝ) ≤ 1 := by
            rw [div_le_one hn0]; exact hσn
          have hg := geom_sum_le_inv hy0 hy1 (n - (k₀ + s₀))
          rwa [one_div_div] at hg
  -- window: at most `2σ` terms, each `≤ e⁹·pmf'(k₀)`
  have hB : ∑ k ∈ Ico (k₀ - s₀ + 1) (k₀ + s₀), pmf' n k
      ≤ 2 * (s₀ : ℝ) * (pmf' n k₀ * Real.exp 9) := by
    have hbound : ∀ k ∈ Ico (k₀ - s₀ + 1) (k₀ + s₀),
        pmf' n k ≤ pmf' n k₀ * Real.exp 9 := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      by_cases hkk : k ≤ k₀
      · rw [show k = k₀ - (k₀ - k) by omega]
        exact pmf'_window_upper_left hn hk₀ (show k₀ - k ≤ s₀ by omega)
      · rw [show k = k₀ + (k - k₀) by omega]
        exact pmf'_window_upper hn hk₀ (show k - k₀ ≤ s₀ by omega)
    calc ∑ k ∈ Ico (k₀ - s₀ + 1) (k₀ + s₀), pmf' n k
        ≤ #(Ico (k₀ - s₀ + 1) (k₀ + s₀)) • (pmf' n k₀ * Real.exp 9) :=
          Finset.sum_le_card_nsmul _ _ _ hbound
      _ = ((k₀ + s₀ - (k₀ - s₀ + 1) : ℕ) : ℝ) * (pmf' n k₀ * Real.exp 9) := by
          rw [Nat.card_Ico, nsmul_eq_mul]
      _ ≤ 2 * (s₀ : ℝ) * (pmf' n k₀ * Real.exp 9) := by
          refine mul_le_mul_of_nonneg_right ?_
            (mul_nonneg (pmf'_nonneg n k₀) (Real.exp_pos 9).le)
          have h1 : k₀ + s₀ - (k₀ - s₀ + 1) ≤ 2 * s₀ := by omega
          calc ((k₀ + s₀ - (k₀ - s₀ + 1) : ℕ) : ℝ) ≤ ((2 * s₀ : ℕ) : ℝ) := by
                exact_mod_cast h1
            _ = 2 * (s₀ : ℝ) := by push_cast; ring
  -- transport the two boundary values to the mode
  have hpa : pmf' n (k₀ - s₀) ≤ pmf' n k₀ * Real.exp 9 :=
    pmf'_window_upper_left hn hk₀ le_rfl
  have hpb : pmf' n (k₀ + s₀) ≤ pmf' n k₀ * Real.exp 9 :=
    pmf'_window_upper hn hk₀ le_rfl
  -- assemble the self-normalisation inequality
  have hfrac_nonneg : (0 : ℝ) ≤ ((n : ℝ) + 7 * (s₀ : ℝ)) / (7 * (s₀ : ℝ)) := by
    positivity
  have hfrac_nonneg' : (0 : ℝ) ≤ (n : ℝ) / (7 * (s₀ : ℝ)) := by positivity
  have hone : (1 : ℝ) ≤ pmf' n k₀ * Real.exp 9
      * (((n : ℝ) + 7 * (s₀ : ℝ)) / (7 * (s₀ : ℝ)) + 2 * (s₀ : ℝ)
          + (n : ℝ) / (7 * (s₀ : ℝ))) := by
    have hA' : ∑ k ∈ range (k₀ - s₀ + 1), pmf' n k
        ≤ pmf' n k₀ * Real.exp 9 * (((n : ℝ) + 7 * (s₀ : ℝ)) / (7 * (s₀ : ℝ))) :=
      hA.trans (mul_le_mul_of_nonneg_right hpa hfrac_nonneg)
    have hC' : ∑ k ∈ Ico (k₀ + s₀) n, pmf' n k
        ≤ pmf' n k₀ * Real.exp 9 * ((n : ℝ) / (7 * (s₀ : ℝ))) :=
      hC.trans (mul_le_mul_of_nonneg_right hpb hfrac_nonneg')
    calc (1 : ℝ) = ∑ k ∈ range n, pmf' n k := hnorm.symm
      _ = ∑ k ∈ range (k₀ - s₀ + 1), pmf' n k
            + (∑ k ∈ Ico (k₀ - s₀ + 1) (k₀ + s₀), pmf' n k
              + ∑ k ∈ Ico (k₀ + s₀) n, pmf' n k) := by
          rw [hsplit2, hsplit1]
      _ ≤ pmf' n k₀ * Real.exp 9 * (((n : ℝ) + 7 * (s₀ : ℝ)) / (7 * (s₀ : ℝ)))
            + (2 * (s₀ : ℝ) * (pmf' n k₀ * Real.exp 9)
              + pmf' n k₀ * Real.exp 9 * ((n : ℝ) / (7 * (s₀ : ℝ)))) :=
          add_le_add hA' (add_le_add hB hC')
      _ = pmf' n k₀ * Real.exp 9
            * (((n : ℝ) + 7 * (s₀ : ℝ)) / (7 * (s₀ : ℝ)) + 2 * (s₀ : ℝ)
              + (n : ℝ) / (7 * (s₀ : ℝ))) := by ring
  -- the bracket is at most `(5/2)σ`, using `n < (σ+1)²`
  have hnlt : (n : ℝ) < ((s₀ : ℝ) + 1) ^ 2 := by
    have h : n < (Nat.sqrt n + 1) ^ 2 := Nat.lt_succ_sqrt' n
    calc (n : ℝ) < ((Nat.sqrt n + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast h
      _ = ((s₀ : ℝ) + 1) ^ 2 := by rw [← hs₀def]; push_cast; ring
  have hσ0 : (0 : ℝ) < 7 * (s₀ : ℝ) := by linarith
  have hbr : ((n : ℝ) + 7 * (s₀ : ℝ)) / (7 * (s₀ : ℝ)) + 2 * (s₀ : ℝ)
      + (n : ℝ) / (7 * (s₀ : ℝ)) ≤ 5 / 2 * (s₀ : ℝ) := by
    have hkey : ((n : ℝ) + 7 * (s₀ : ℝ)) + 2 * (s₀ : ℝ) * (7 * (s₀ : ℝ))
        + (n : ℝ) ≤ 5 / 2 * (s₀ : ℝ) * (7 * (s₀ : ℝ)) := by
      nlinarith [hnlt, hσR]
    have hid : ((n : ℝ) + 7 * (s₀ : ℝ)) / (7 * (s₀ : ℝ)) + 2 * (s₀ : ℝ)
        + (n : ℝ) / (7 * (s₀ : ℝ))
        = (((n : ℝ) + 7 * (s₀ : ℝ)) + 2 * (s₀ : ℝ) * (7 * (s₀ : ℝ))
            + (n : ℝ)) / (7 * (s₀ : ℝ)) := by
      field_simp
    rw [hid, div_le_iff₀ hσ0]
    linarith
  -- conclude
  have hσle : (s₀ : ℝ) ≤ Real.sqrt n := Real.le_sqrt_of_sq_le hσsq
  have hsqrt0 : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hp0 : (0 : ℝ) ≤ pmf' n k₀ := pmf'_nonneg n k₀
  have hfin : (1 : ℝ) ≤ 25000 * Real.sqrt n * pmf' n k₀ := by
    calc (1 : ℝ) ≤ pmf' n k₀ * Real.exp 9
          * (((n : ℝ) + 7 * (s₀ : ℝ)) / (7 * (s₀ : ℝ)) + 2 * (s₀ : ℝ)
            + (n : ℝ) / (7 * (s₀ : ℝ))) := hone
      _ ≤ pmf' n k₀ * Real.exp 9 * (5 / 2 * (s₀ : ℝ)) :=
          mul_le_mul_of_nonneg_left hbr
            (mul_nonneg hp0 (Real.exp_pos 9).le)
      _ ≤ pmf' n k₀ * 8104 * (5 / 2 * (s₀ : ℝ)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left exp_nine_le hp0)
            (by positivity)
      _ ≤ pmf' n k₀ * 8104 * (5 / 2 * Real.sqrt n) :=
          mul_le_mul_of_nonneg_left (by linarith)
            (mul_nonneg hp0 (by norm_num))
      _ = 20260 * Real.sqrt n * pmf' n k₀ := by ring
      _ ≤ 25000 * Real.sqrt n * pmf' n k₀ := by
          nlinarith [mul_nonneg hp0 hsqrt0.le]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 25000 * Real.sqrt n)]
  linarith

end MakinenAnalysis
