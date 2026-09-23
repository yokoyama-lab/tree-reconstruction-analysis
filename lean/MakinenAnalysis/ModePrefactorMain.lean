import Mathlib
import MakinenAnalysis.LocalLimit
import MakinenAnalysis.ModePrefactor
import MakinenAnalysis.LocalCLTMode
import MakinenAnalysis.LocalCLTWindow

/-!
# The mode-prefactor limit: `σ(n)·pmf'(n, ⌊n/4⌋) → 1/√(2π)`

This file closes the `hpre` gap of the local limit theorem
(`pmf'_local_limit_of_mode`, `LocalLimit.lean`): conditionally on the
normalisation `Σ_{k<n} pmf' n k = 1` (hypothesis `hnorm`, discharged by
`sum_pmf'_of_closed` once the closed form `U_mul_closed` is proved), the value
of the law at the mode is *exactly* Gaussian-normalised:

  `sigmaP2 n · pmf'(n, ⌊n/4⌋) → 1/√(2π)`   (`mode_prefactor_tendsto`).

## Architecture (self-normalisation with a moving window)

Fix the moving window radius `K(n) = n^{1/8}` (as `√√√n`, so `K⁴ = √n` exactly)
and write `P₀ = pmf'(n,⌊n/4⌋)`, `W = {k < n : |k − n/4| < K√n}`.

* **Window bracket** (`window_sum_le` / `window_sum_ge`): summing the pointwise
  Gaussian ratio `pmf'_ratio_gaussian` over `W`,
  `e^{−C(K)/√n} · P₀ · Σ_W G ≤ Σ_W pmf' ≤ e^{C(K)/√n} · P₀ · Σ_W G`
  with `G(k) = exp(−8(k−n/4)²/n)` and `C(K) = 10000K(1+K²)+16K+8`; at
  `K = n^{1/8}` the error `C(K)/√n ≤ 20024/K → 0`.

* **Annulus tail** (`sum_pmf'_annulus_le`, **deliverable 1**): the pmf'-mass at
  distance `≥ K√n` from `n/4` is at most `10⁸·e^{−(K−1)}`, for every `K ≥ 2`
  and `n ≥ 10⁹`.  Proof: uniform geometric decay of the one-step ratio beyond
  the `√n`-scale (`1 ∓ 7√n/n` per step, re-proved here from the exact ratio),
  telescoped over the `≥ (K−1)√n` steps separating the annulus from the
  `√n`-window, plus the mode bound `mode_upper` and window transport.  Hence
  `1 − 10⁸e^{−(K−1)} ≤ Σ_W pmf' ≤ 1`.

* **Gaussian off-window mass** (`sum_gauss_notwindow_le`): trivially
  `Σ_{W^c} G ≤ n·e^{−8K²}`, and `n·e^{−8K²}/√n = K⁴e^{−8K²} → 0` at
  `K = n^{1/8}`; with the exact constant `Σ_{k<n} G/√n → √(π/8)`
  (`centred_gaussian_sum_tendsto`) this gives `Σ_W G/√n → √(π/8)`.

* **Squeeze**: `P₀·Σ_W G ∈ [e^{−C/√n}(1 − 10⁸e^{−(K−1)}), e^{C/√n}] → 1`, so
  `√n·P₀ = (P₀·Σ_W G)/(Σ_W G/√n) → 1/√(π/8) = √(8/π)`, and
  `σ·P₀ = √n·P₀/4 → √(8/π)/4 = 1/√(2π)`.

Everything is unconditional on `hnorm` alone; zero `sorry`s.
-/

namespace MakinenAnalysis

open Finset Filter Topology

/-! ### Small helpers
`mode_dev` (`LocalLimit`), `cast_sq_le_of_le_sqrt`, `exp_nine_le` and
`geom_sum_le_inv` (`LocalCLTMode`) used to be re-proved here verbatim under
primed names; they are now reused directly (un-privated in their home files)
since `ModePrefactorMain` already imports both. -/

/-- Exponential domination of the decayed geometric factor:
`(1−x)^m ≤ e^{−c}` whenever `0 ≤ x ≤ 1` and `c ≤ m·x`. -/
private lemma pow_one_sub_le_exp {x : ℝ} (_h0 : 0 ≤ x) (h1 : x ≤ 1) (m : ℕ) {c : ℝ}
    (hc : c ≤ (m : ℝ) * x) : (1 - x) ^ m ≤ Real.exp (-c) := by
  have hbase : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x)
    linarith
  calc (1 - x) ^ m ≤ Real.exp (-x) ^ m :=
        pow_le_pow_left₀ (by linarith) hbase m
    _ = Real.exp ((m : ℝ) * (-x)) := (Real.exp_nat_mul (-x) m).symm
    _ ≤ Real.exp (-c) := Real.exp_le_exp.mpr (by nlinarith)

/-! ### Far-field geometric decay
`pmfRatio_le_far_right`, `le_pmfRatio_far_left`, `pmf'_succ_le_far_right`,
`pmf'_le_succ_far_left`, `pmf'_add_le_far_right` and `pmf'_sub_le_far_left`
used to be re-proved here verbatim under primed names; they are now reused
directly from `LocalCLTMode` (un-privated there). -/

/-! ### Deliverable 1: the intermediate-annulus tail bound

The pmf'-mass at distance `≥ K√n` from `n/4` is at most `10⁸·e^{−(K−1)}`:
each side of the annulus is separated from the flat `√n`-window by
`≥ (K−1)√n` one-step ratios each `≤ 1 − 7√n/n` (right) resp. `≥ 1 + 7√n/n`
(left), so its boundary value is `≤ e⁹·pmf'(k₀)·e^{−(K−1)}` and the geometric
tail sums to `≤ √n/5` times that; `mode_upper` closes with
`pmf'(k₀) ≤ 8104/√n`. -/

set_option maxHeartbeats 1600000 in
/-- **The annulus tail bound.**  For `K ≥ 2`, `n ≥ 10⁹`, conditionally on the
normalisation `hnorm`,

`Σ_{k < n, |k − n/4| ≥ K√n} pmf' n k ≤ 10⁸ · e^{−(K−1)}`. -/
theorem sum_pmf'_annulus_le {n : ℕ} {K : ℝ} (hK : 2 ≤ K) (hn : 1000000000 ≤ n)
    (hnorm : ∑ k ∈ Finset.range n, pmf' n k = 1) :
    ∑ k ∈ (Finset.range n).filter
        (fun k : ℕ => K * Real.sqrt n ≤ |(k : ℝ) - (n : ℝ) / 4|), pmf' n k
      ≤ 100000000 * Real.exp (-(K - 1)) := by
  have hnR : (1000000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  set r := Real.sqrt n with hr_def
  have hr0 : 0 < r := Real.sqrt_pos.mpr hn0
  have hr2 : r ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hr316 : (31622 : ℝ) ≤ r := by
    have h1 : ((31622 : ℝ)) ^ 2 ≤ (n : ℝ) := by norm_num; linarith
    calc (31622 : ℝ) = Real.sqrt (31622 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt h1
  -- the natural `√n` and its basic estimates
  set s₀ := Nat.sqrt n with hs₀_def
  have hσsq : ((s₀ : ℝ)) ^ 2 ≤ (n : ℝ) := cast_sq_le_of_le_sqrt le_rfl
  have hσ30 : 30000 ≤ s₀ := Nat.le_sqrt.mpr (by omega)
  have hσR : (30000 : ℝ) ≤ (s₀ : ℝ) := by exact_mod_cast hσ30
  have hσ_le_r : (s₀ : ℝ) ≤ r := Real.le_sqrt_of_sq_le hσsq
  have hr_le_σ1 : r ≤ (s₀ : ℝ) + 1 := by
    have h : n < (s₀ + 1) ^ 2 := Nat.lt_succ_sqrt' n
    have hR : (n : ℝ) ≤ (((s₀ + 1 : ℕ)) : ℝ) ^ 2 := by exact_mod_cast h.le
    calc r ≤ Real.sqrt ((((s₀ + 1 : ℕ)) : ℝ) ^ 2) := Real.sqrt_le_sqrt hR
      _ = (((s₀ + 1 : ℕ)) : ℝ) := Real.sqrt_sq (by positivity)
      _ = (s₀ : ℝ) + 1 := by push_cast; ring
  have hσn : 7 * (s₀ : ℝ) ≤ (n : ℝ) := by
    nlinarith [hσsq, hσR, sq_nonneg ((s₀ : ℝ) - 7)]
  -- the mode and the annulus boundary index
  set k₀ := ⌊(n : ℝ) / 4⌋₊ with hk₀_def
  have hk₀dev : |(k₀ : ℝ) - (n : ℝ) / 4| ≤ 1 := mode_dev n
  obtain ⟨hk₀l, hk₀u⟩ := abs_le.mp hk₀dev
  have hk₀_le : (k₀ : ℝ) ≤ (n : ℝ) / 4 := Nat.floor_le (by positivity)
  have hs₀k₀ : s₀ ≤ k₀ := by
    have : (s₀ : ℝ) ≤ (k₀ : ℝ) := by
      nlinarith [hσ_le_r, hk₀l, hr2, sq_nonneg (r - 4), hr316]
    exact_mod_cast this
  set t := ⌈K * r⌉₊ with ht_def
  have htKr : K * r ≤ (t : ℝ) := Nat.le_ceil _
  have htub : (t : ℝ) < K * r + 1 := Nat.ceil_lt_add_one (by positivity)
  have hst : s₀ + 2 ≤ t := by
    have : ((s₀ : ℝ)) + 2 ≤ (t : ℝ) := by
      nlinarith [htKr, mul_le_mul_of_nonneg_right hK hr0.le, hσ_le_r, hr316]
    exact_mod_cast this
  have hKr_pos : (0 : ℝ) < K * r := by positivity
  -- mode value and window transport
  have hP₀ : pmf' n k₀ ≤ 8104 / Real.sqrt n := mode_upper hn hk₀dev hnorm
  rw [← hr_def] at hP₀
  have hbR : pmf' n (k₀ + s₀) ≤ pmf' n k₀ * Real.exp 9 :=
    pmf'_window_upper hn hk₀dev le_rfl
  have hbL : pmf' n (k₀ - s₀) ≤ pmf' n k₀ * Real.exp 9 :=
    pmf'_window_upper_left hn hk₀dev le_rfl
  have hboundary : pmf' n (k₀ + s₀) ≤ 8104 * 8104 / r ∧
      pmf' n (k₀ - s₀) ≤ 8104 * 8104 / r := by
    constructor
    · calc pmf' n (k₀ + s₀) ≤ pmf' n k₀ * Real.exp 9 := hbR
        _ ≤ (8104 / r) * 8104 :=
            mul_le_mul hP₀ exp_nine_le (Real.exp_pos 9).le (by positivity)
        _ = 8104 * 8104 / r := by ring
    · calc pmf' n (k₀ - s₀) ≤ pmf' n k₀ * Real.exp 9 := hbL
        _ ≤ (8104 / r) * 8104 :=
            mul_le_mul hP₀ exp_nine_le (Real.exp_pos 9).le (by positivity)
        _ = 8104 * 8104 / r := by ring
  -- split the annulus into the two sides
  have hsub : (Finset.range n).filter
        (fun k : ℕ => K * r ≤ |(k : ℝ) - (n : ℝ) / 4|)
      ⊆ (Finset.range n).filter (fun k : ℕ => (n : ℝ) / 4 + K * r ≤ (k : ℝ))
        ∪ (Finset.range n).filter (fun k : ℕ => (k : ℝ) ≤ (n : ℝ) / 4 - K * r) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases le_abs.mp hk.2 with h | h
    · exact Or.inl ⟨hk.1, by linarith⟩
    · exact Or.inr ⟨hk.1, by linarith⟩
  have hdisj : Disjoint
      ((Finset.range n).filter (fun k : ℕ => (n : ℝ) / 4 + K * r ≤ (k : ℝ)))
      ((Finset.range n).filter (fun k : ℕ => (k : ℝ) ≤ (n : ℝ) / 4 - K * r)) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    rw [Finset.mem_filter] at hk1 hk2
    linarith [hk1.2, hk2.2]
  have hmono : ∑ k ∈ (Finset.range n).filter
        (fun k : ℕ => K * r ≤ |(k : ℝ) - (n : ℝ) / 4|), pmf' n k
      ≤ (∑ k ∈ (Finset.range n).filter
            (fun k : ℕ => (n : ℝ) / 4 + K * r ≤ (k : ℝ)), pmf' n k)
        + ∑ k ∈ (Finset.range n).filter
            (fun k : ℕ => (k : ℝ) ≤ (n : ℝ) / 4 - K * r), pmf' n k := by
    rw [← Finset.sum_union hdisj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => pmf'_nonneg n i)
  -- ### right side
  have hRight : ∑ k ∈ (Finset.range n).filter
        (fun k : ℕ => (n : ℝ) / 4 + K * r ≤ (k : ℝ)), pmf' n k
      ≤ 50000000 * Real.exp (-(K - 1)) := by
    have hq0 : (0 : ℝ) < 7 * (s₀ : ℝ) / (n : ℝ) := by positivity
    have hq1 : 7 * (s₀ : ℝ) / (n : ℝ) ≤ 1 := by
      rw [div_le_one hn0]; exact hσn
    have hqnn : (0 : ℝ) ≤ 1 - 7 * (s₀ : ℝ) / (n : ℝ) := by linarith
    have hbaseR : (n : ℝ) / 4 + (s₀ : ℝ) - 1 ≤ ((k₀ + s₀ : ℕ) : ℝ) := by
      push_cast; linarith
    -- the decayed prefix: `q^{t−1−s₀} ≤ e^{−(K−1)}`
    have hj₀cast : ((t - 1 - s₀ : ℕ) : ℝ) = (t : ℝ) - 1 - (s₀ : ℝ) := by
      rw [Nat.cast_sub (by omega : s₀ ≤ t - 1), Nat.cast_sub (by omega : 1 ≤ t)]
      push_cast; ring
    have hexpR : (1 - 7 * (s₀ : ℝ) / (n : ℝ)) ^ (t - 1 - s₀)
        ≤ Real.exp (-(K - 1)) := by
      refine pow_one_sub_le_exp hq0.le hq1 _ ?_
      rw [hj₀cast]
      have hs₀_lb : r - 1 ≤ (s₀ : ℝ) := by linarith
      have hj₀_lb : (K - 1) * r - 1 ≤ (t : ℝ) - 1 - (s₀ : ℝ) := by
        nlinarith [htKr, hσ_le_r]
      have hf1 : (0 : ℝ) ≤ (K - 1) * r - 1 := by nlinarith [hr316]
      have hf2 : (r - 1) * ((K - 1) * r - 1) ≤ (s₀ : ℝ) * ((t : ℝ) - 1 - (s₀ : ℝ)) :=
        mul_le_mul hs₀_lb hj₀_lb hf1 (by positivity)
      have h1 : (K - 1) * (n : ℝ) ≤ ((t : ℝ) - 1 - (s₀ : ℝ)) * (7 * (s₀ : ℝ)) := by
        nlinarith [hf2, hr2, hr316,
          mul_nonneg (by linarith : (0 : ℝ) ≤ K - 2)
            (by nlinarith [hr316] : (0 : ℝ) ≤ 6 * r ^ 2 - 7 * r),
          mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * r)
            (by linarith : (0 : ℝ) ≤ 3 * r - 7)]
      rw [show ((t : ℝ) - 1 - (s₀ : ℝ)) * (7 * (s₀ : ℝ) / (n : ℝ))
          = (((t : ℝ) - 1 - (s₀ : ℝ)) * (7 * (s₀ : ℝ))) / (n : ℝ) by ring,
        le_div_iff₀ hn0]
      linarith [h1]
    -- the geometric factor: `Σ q^j ≤ n/(7s₀) ≤ r/6`
    have hgeomR : ∑ j ∈ Finset.range (n + 1 - (k₀ + (t - 1))),
        (1 - 7 * (s₀ : ℝ) / (n : ℝ)) ^ j ≤ (n : ℝ) / (7 * (s₀ : ℝ)) := by
      have h := geom_sum_le_inv hq0 hq1 (n + 1 - (k₀ + (t - 1)))
      rwa [one_div_div] at h
    have hn7s : (n : ℝ) / (7 * (s₀ : ℝ)) ≤ r / 6 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 6)]
      nlinarith [mul_le_mul_of_nonneg_right
          (show r - 1 ≤ (s₀ : ℝ) by linarith) hr0.le,
        mul_le_mul_of_nonneg_right hr316 hr0.le, hr2]
    -- cover the right side by `Icc (k₀ + (t−1)) n` and telescope
    have hsubR : (Finset.range n).filter
          (fun k : ℕ => (n : ℝ) / 4 + K * r ≤ (k : ℝ))
        ⊆ Finset.Ico (k₀ + (t - 1)) (n + 1) := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      rw [Finset.mem_Ico]
      refine ⟨?_, by omega⟩
      have hcast : ((k₀ + (t - 1) : ℕ) : ℝ) = (k₀ : ℝ) + ((t : ℝ) - 1) := by
        rw [Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ t)]; push_cast; ring
      have hlt : ((k₀ + (t - 1) : ℕ) : ℝ) < (k : ℝ) := by
        rw [hcast]; linarith [hk.2]
      exact_mod_cast hlt.le
    have hXnn : (0 : ℝ) ≤ pmf' n (k₀ + s₀)
        * (1 - 7 * (s₀ : ℝ) / (n : ℝ)) ^ (t - 1 - s₀) :=
      mul_nonneg (pmf'_nonneg n _) (pow_nonneg hqnn _)
    calc ∑ k ∈ (Finset.range n).filter
          (fun k : ℕ => (n : ℝ) / 4 + K * r ≤ (k : ℝ)), pmf' n k
        ≤ ∑ k ∈ Finset.Ico (k₀ + (t - 1)) (n + 1), pmf' n k :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubR (fun i _ _ => pmf'_nonneg n i)
      _ = ∑ j ∈ Finset.range (n + 1 - (k₀ + (t - 1))), pmf' n ((k₀ + (t - 1)) + j) := by
          rw [Finset.sum_Ico_eq_sum_range]
      _ ≤ ∑ j ∈ Finset.range (n + 1 - (k₀ + (t - 1))),
            pmf' n (k₀ + s₀) * (1 - 7 * (s₀ : ℝ) / (n : ℝ)) ^ (t - 1 - s₀)
              * (1 - 7 * (s₀ : ℝ) / (n : ℝ)) ^ j := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [show (k₀ + (t - 1)) + j = (k₀ + s₀) + ((t - 1 - s₀) + j) by omega]
          calc pmf' n ((k₀ + s₀) + ((t - 1 - s₀) + j))
              ≤ pmf' n (k₀ + s₀)
                  * (1 - 7 * (s₀ : ℝ) / (n : ℝ)) ^ ((t - 1 - s₀) + j) :=
                pmf'_add_le_far_right hn hσsq hσ30 hbaseR _
            _ = pmf' n (k₀ + s₀) * (1 - 7 * (s₀ : ℝ) / (n : ℝ)) ^ (t - 1 - s₀)
                  * (1 - 7 * (s₀ : ℝ) / (n : ℝ)) ^ j := by
                rw [pow_add]; ring
      _ = pmf' n (k₀ + s₀) * (1 - 7 * (s₀ : ℝ) / (n : ℝ)) ^ (t - 1 - s₀)
            * ∑ j ∈ Finset.range (n + 1 - (k₀ + (t - 1))),
                (1 - 7 * (s₀ : ℝ) / (n : ℝ)) ^ j := by
          rw [Finset.mul_sum]
      _ ≤ pmf' n (k₀ + s₀) * (1 - 7 * (s₀ : ℝ) / (n : ℝ)) ^ (t - 1 - s₀)
            * ((n : ℝ) / (7 * (s₀ : ℝ))) :=
          mul_le_mul_of_nonneg_left hgeomR hXnn
      _ ≤ (8104 * 8104 / r) * Real.exp (-(K - 1)) * (r / 6) := by
          refine mul_le_mul ?_ hn7s (by positivity) ?_
          · exact mul_le_mul hboundary.1 hexpR (pow_nonneg hqnn _)
              (div_nonneg (by norm_num) hr0.le)
          · exact mul_nonneg (div_nonneg (by norm_num) hr0.le) (Real.exp_pos _).le
      _ = (8104 * 8104 / 6) * Real.exp (-(K - 1)) := by
          field_simp
      _ ≤ 50000000 * Real.exp (-(K - 1)) := by
          have h : (8104 : ℝ) * 8104 / 6 ≤ 50000000 := by norm_num
          exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
  -- ### left side
  have hLeft : ∑ k ∈ (Finset.range n).filter
        (fun k : ℕ => (k : ℝ) ≤ (n : ℝ) / 4 - K * r), pmf' n k
      ≤ 50000000 * Real.exp (-(K - 1)) := by
    by_cases hm₂k : t - 2 ≤ k₀
    · -- the left annulus sits below `k₀ − (t−2)`
      have hden : (0 : ℝ) < (n : ℝ) + 7 * (s₀ : ℝ) := by linarith
      have hx'0 : (0 : ℝ) < 7 * (s₀ : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ)) := by positivity
      have hx'1 : 7 * (s₀ : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ)) ≤ 1 := by
        rw [div_le_one hden]; linarith
      have hρ_eq : (n : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ))
          = 1 - 7 * (s₀ : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ)) := by
        field_simp
        ring
      have hρnn : (0 : ℝ) ≤ (n : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ)) := by positivity
      have hbaseL : ((k₀ - s₀ : ℕ) : ℝ) ≤ (n : ℝ) / 4 - (s₀ : ℝ) + 1 := by
        rw [Nat.cast_sub hs₀k₀]
        linarith
      -- decayed prefix on the left: `ρ^{t−2−s₀} ≤ e^{−(K−1)}`
      have hj₁cast : ((t - 2 - s₀ : ℕ) : ℝ) = (t : ℝ) - 2 - (s₀ : ℝ) := by
        rw [Nat.cast_sub (by omega : s₀ ≤ t - 2), Nat.cast_sub (by omega : 2 ≤ t)]
        push_cast; ring
      have hexpL : ((n : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ))) ^ (t - 2 - s₀)
          ≤ Real.exp (-(K - 1)) := by
        rw [hρ_eq]
        refine pow_one_sub_le_exp hx'0.le hx'1 _ ?_
        rw [hj₁cast]
        have hs₀_lb : r - 1 ≤ (s₀ : ℝ) := by linarith
        have hj₁_lb : (K - 1) * r - 2 ≤ (t : ℝ) - 2 - (s₀ : ℝ) := by
          nlinarith [htKr, hσ_le_r]
        have hf1 : (0 : ℝ) ≤ (K - 1) * r - 2 := by nlinarith [hr316]
        have hf2 : (r - 1) * ((K - 1) * r - 2)
            ≤ (s₀ : ℝ) * ((t : ℝ) - 2 - (s₀ : ℝ)) :=
          mul_le_mul hs₀_lb hj₁_lb hf1 (by positivity)
        have h1 : (K - 1) * ((n : ℝ) + 7 * (s₀ : ℝ))
            ≤ ((t : ℝ) - 2 - (s₀ : ℝ)) * (7 * (s₀ : ℝ)) := by
          nlinarith [hf2, hr2, hr316, hσ_le_r,
            mul_nonneg (by linarith : (0 : ℝ) ≤ K - 2)
              (by nlinarith [hr316] : (0 : ℝ) ≤ 6 * r ^ 2 - 21 * r),
            mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * r)
              (by linarith : (0 : ℝ) ≤ 3 * r - 14)]
        rw [show ((t : ℝ) - 2 - (s₀ : ℝ))
              * (7 * (s₀ : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ)))
            = (((t : ℝ) - 2 - (s₀ : ℝ)) * (7 * (s₀ : ℝ)))
              / ((n : ℝ) + 7 * (s₀ : ℝ)) by ring,
          le_div_iff₀ hden]
        linarith [h1]
      -- geometric factor on the left: `Σ ρ^j ≤ (n+7s₀)/(7s₀) ≤ r/5`
      have hgeomL : ∑ j ∈ Finset.range (k₀ - (t - 2) + 1),
          ((n : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ))) ^ j
          ≤ ((n : ℝ) + 7 * (s₀ : ℝ)) / (7 * (s₀ : ℝ)) := by
        have h := geom_sum_le_inv hx'0 hx'1 (k₀ - (t - 2) + 1)
        rw [one_div_div] at h
        calc ∑ j ∈ Finset.range (k₀ - (t - 2) + 1),
              ((n : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ))) ^ j
            = ∑ j ∈ Finset.range (k₀ - (t - 2) + 1),
              (1 - 7 * (s₀ : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ))) ^ j := by
              rw [hρ_eq]
          _ ≤ ((n : ℝ) + 7 * (s₀ : ℝ)) / (7 * (s₀ : ℝ)) := h
      have hn7s' : ((n : ℝ) + 7 * (s₀ : ℝ)) / (7 * (s₀ : ℝ)) ≤ r / 5 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 5)]
        nlinarith [mul_le_mul_of_nonneg_right
            (show r - 1 ≤ (s₀ : ℝ) by linarith) hr0.le,
          mul_le_mul_of_nonneg_right hr316 hr0.le, hr2, hσ_le_r]
      -- cover the left side by `range (k₀ − (t−2) + 1)` and telescope downward
      have hsubL : (Finset.range n).filter
            (fun k : ℕ => (k : ℝ) ≤ (n : ℝ) / 4 - K * r)
          ⊆ Finset.range (k₀ - (t - 2) + 1) := by
        intro k hk
        rw [Finset.mem_filter] at hk
        rw [Finset.mem_range]
        have hcast : ((k₀ - (t - 2) : ℕ) : ℝ) = (k₀ : ℝ) - ((t : ℝ) - 2) := by
          rw [Nat.cast_sub hm₂k, Nat.cast_sub (by omega : 2 ≤ t)]; push_cast; ring
        have hlt : (k : ℝ) < ((k₀ - (t - 2) : ℕ) : ℝ) := by
          rw [hcast]; linarith [hk.2]
        have : k < k₀ - (t - 2) := by exact_mod_cast hlt
        omega
      have hXnn : (0 : ℝ) ≤ pmf' n (k₀ - s₀)
          * ((n : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ))) ^ (t - 2 - s₀) :=
        mul_nonneg (pmf'_nonneg n _) (pow_nonneg hρnn _)
      calc ∑ k ∈ (Finset.range n).filter
            (fun k : ℕ => (k : ℝ) ≤ (n : ℝ) / 4 - K * r), pmf' n k
          ≤ ∑ k ∈ Finset.range (k₀ - (t - 2) + 1), pmf' n k :=
            Finset.sum_le_sum_of_subset_of_nonneg hsubL (fun i _ _ => pmf'_nonneg n i)
        _ = ∑ j ∈ Finset.range (k₀ - (t - 2) + 1), pmf' n (k₀ - (t - 2) - j) :=
            (Finset.sum_range_reflect (fun k => pmf' n k) (k₀ - (t - 2) + 1)).symm
        _ ≤ ∑ j ∈ Finset.range (k₀ - (t - 2) + 1),
              pmf' n (k₀ - s₀) * ((n : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ))) ^ (t - 2 - s₀)
                * ((n : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ))) ^ j := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hjle : j ≤ k₀ - (t - 2) := by
              have := Finset.mem_range.mp hj; omega
            rw [show k₀ - (t - 2) - j = (k₀ - s₀) - ((t - 2 - s₀) + j) by omega]
            calc pmf' n ((k₀ - s₀) - ((t - 2 - s₀) + j))
                ≤ pmf' n (k₀ - s₀)
                    * ((n : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ))) ^ ((t - 2 - s₀) + j) :=
                  pmf'_sub_le_far_left hn hσsq hσ30 hbaseL _ (by omega)
              _ = pmf' n (k₀ - s₀)
                    * ((n : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ))) ^ (t - 2 - s₀)
                    * ((n : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ))) ^ j := by
                  rw [pow_add]; ring
        _ = pmf' n (k₀ - s₀) * ((n : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ))) ^ (t - 2 - s₀)
              * ∑ j ∈ Finset.range (k₀ - (t - 2) + 1),
                  ((n : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ))) ^ j := by
            rw [Finset.mul_sum]
        _ ≤ pmf' n (k₀ - s₀) * ((n : ℝ) / ((n : ℝ) + 7 * (s₀ : ℝ))) ^ (t - 2 - s₀)
              * (((n : ℝ) + 7 * (s₀ : ℝ)) / (7 * (s₀ : ℝ))) :=
            mul_le_mul_of_nonneg_left hgeomL hXnn
        _ ≤ (8104 * 8104 / r) * Real.exp (-(K - 1)) * (r / 5) := by
            refine mul_le_mul ?_ hn7s' (by positivity) ?_
            · exact mul_le_mul hboundary.2 hexpL (pow_nonneg hρnn _)
                (div_nonneg (by norm_num) hr0.le)
            · exact mul_nonneg (div_nonneg (by norm_num) hr0.le) (Real.exp_pos _).le
        _ = (8104 * 8104 / 5) * Real.exp (-(K - 1)) := by
            field_simp
        _ ≤ 50000000 * Real.exp (-(K - 1)) := by
            have h : (8104 : ℝ) * 8104 / 5 ≤ 50000000 := by norm_num
            exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    · -- `k₀ < t − 2`: the left annulus is empty
      have hempty : (Finset.range n).filter
          (fun k : ℕ => (k : ℝ) ≤ (n : ℝ) / 4 - K * r) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro k _
        rw [not_le]
        have hk₀t : (k₀ : ℝ) + 3 ≤ (t : ℝ) := by
          have : k₀ + 3 ≤ t := by omega
          exact_mod_cast this
        have : (n : ℝ) / 4 - K * r < 0 := by linarith [htub]
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
        linarith
      rw [hempty, Finset.sum_empty]
      positivity
  calc ∑ k ∈ (Finset.range n).filter
        (fun k : ℕ => K * r ≤ |(k : ℝ) - (n : ℝ) / 4|), pmf' n k
      ≤ _ + _ := hmono
    _ ≤ 50000000 * Real.exp (-(K - 1)) + 50000000 * Real.exp (-(K - 1)) :=
        add_le_add hRight hLeft
    _ = 100000000 * Real.exp (-(K - 1)) := by ring

/-! ### The exponentiated window bracket

`pmf'_ratio_gaussian` (`LocalLimit`) bounds the log-ratio to the mode by the
Gaussian quadratic with error `C(K)/√n`; exponentiating and summing over the
window `|k − n/4| < K√n` brackets the window pmf'-mass between
`e^{∓C(K)/√n}·pmf'(k₀)·Σ_W exp(−8(k−n/4)²/n)`. -/

/-- Support guards and positivity on the window `|k − n/4| ≤ K√n`. -/
private lemma window_supports {n : ℕ} {K : ℝ} (hK : 1 ≤ K)
    (hn : 64 ≤ n) (hthr : (64 * K) ^ 2 ≤ (n : ℝ)) {k : ℕ}
    (hk : |(k : ℝ) - (n : ℝ) / 4| ≤ K * Real.sqrt n) :
    0 < pmf' n k ∧ 0 < pmf' n ⌊(n : ℝ) / 4⌋₊ := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (64 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hn64R : (64 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hr0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hr2 : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hr64K : 64 * K ≤ Real.sqrt n := by
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 64 * K by positivity)]
    exact Real.sqrt_le_sqrt hthr
  have hKr_le : K * Real.sqrt n ≤ (n : ℝ) / 64 := by
    nlinarith [mul_nonneg hr0.le (show (0 : ℝ) ≤ Real.sqrt n - 64 * K by linarith), hr2]
  constructor
  · apply pmf'_pos
    have hkub := (abs_le.mp hk).2
    have : ((2 * k + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      push_cast
      nlinarith [hkub, hKr_le, hn64R]
    exact_mod_cast this
  · apply pmf'_pos
    have hfl : ((⌊(n : ℝ) / 4⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) / 4 := Nat.floor_le (by positivity)
    have : ((2 * ⌊(n : ℝ) / 4⌋₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this

/-- **Pointwise upper bracket** on the window `|k − n/4| ≤ K√n`:
`pmf'(k) ≤ pmf'(k₀)·exp(−8(k−n/4)²/n)·e^{C(K)/√n}`. -/
private lemma pmf'_bracket_upper {n : ℕ} {K : ℝ} (hK : 1 ≤ K)
    (hn : 64 ≤ n) (hthr : (64 * K) ^ 2 ≤ (n : ℝ)) {k : ℕ}
    (hk : |(k : ℝ) - (n : ℝ) / 4| ≤ K * Real.sqrt n) :
    pmf' n k ≤ pmf' n ⌊(n : ℝ) / 4⌋₊
        * Real.exp (-8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n)
        * Real.exp ((10000 * K * (1 + K ^ 2) + 16 * K + 8) / Real.sqrt n) := by
  obtain ⟨hkpos, hk₀pos⟩ := window_supports hK hn hthr hk
  have hg := (abs_le.mp (pmf'_ratio_gaussian hK hn hthr hk)).2
  calc pmf' n k = Real.exp (Real.log (pmf' n k)) := (Real.exp_log hkpos).symm
    _ ≤ Real.exp (Real.log (pmf' n ⌊(n : ℝ) / 4⌋₊)
          + (-8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n)
          + (10000 * K * (1 + K ^ 2) + 16 * K + 8) / Real.sqrt n) :=
        Real.exp_le_exp.mpr (by
          have hq : -8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n
              = -(8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n) := by ring
          linarith [hg, hq])
    _ = pmf' n ⌊(n : ℝ) / 4⌋₊ * Real.exp (-8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n)
          * Real.exp ((10000 * K * (1 + K ^ 2) + 16 * K + 8) / Real.sqrt n) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log hk₀pos]

/-- **Pointwise lower bracket** on the window `|k − n/4| ≤ K√n`:
`pmf'(k₀)·exp(−8(k−n/4)²/n)·e^{−C(K)/√n} ≤ pmf'(k)`. -/
private lemma pmf'_bracket_lower {n : ℕ} {K : ℝ} (hK : 1 ≤ K)
    (hn : 64 ≤ n) (hthr : (64 * K) ^ 2 ≤ (n : ℝ)) {k : ℕ}
    (hk : |(k : ℝ) - (n : ℝ) / 4| ≤ K * Real.sqrt n) :
    pmf' n ⌊(n : ℝ) / 4⌋₊
        * Real.exp (-8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n)
        * Real.exp (-((10000 * K * (1 + K ^ 2) + 16 * K + 8) / Real.sqrt n))
      ≤ pmf' n k := by
  obtain ⟨hkpos, hk₀pos⟩ := window_supports hK hn hthr hk
  have hg := (abs_le.mp (pmf'_ratio_gaussian hK hn hthr hk)).1
  calc pmf' n ⌊(n : ℝ) / 4⌋₊ * Real.exp (-8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n)
        * Real.exp (-((10000 * K * (1 + K ^ 2) + 16 * K + 8) / Real.sqrt n))
      = Real.exp (Real.log (pmf' n ⌊(n : ℝ) / 4⌋₊)
          + (-8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n)
          + -((10000 * K * (1 + K ^ 2) + 16 * K + 8) / Real.sqrt n)) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log hk₀pos]
    _ ≤ Real.exp (Real.log (pmf' n k)) := Real.exp_le_exp.mpr (by
          have hq : -8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n
              = -(8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n) := by ring
          linarith [hg, hq])
    _ = pmf' n k := Real.exp_log hkpos

/-- **Summed upper bracket** over the window. -/
private lemma window_sum_le {n : ℕ} {K : ℝ} (hK : 1 ≤ K)
    (hn : 64 ≤ n) (hthr : (64 * K) ^ 2 ≤ (n : ℝ)) :
    ∑ k ∈ (Finset.range n).filter
        (fun k : ℕ => |(k : ℝ) - (n : ℝ) / 4| < K * Real.sqrt n), pmf' n k
      ≤ Real.exp ((10000 * K * (1 + K ^ 2) + 16 * K + 8) / Real.sqrt n)
        * (pmf' n ⌊(n : ℝ) / 4⌋₊
          * ∑ k ∈ (Finset.range n).filter
              (fun k : ℕ => |(k : ℝ) - (n : ℝ) / 4| < K * Real.sqrt n),
              Real.exp (-8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n)) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [Finset.mem_filter] at hk
  calc pmf' n k
      ≤ pmf' n ⌊(n : ℝ) / 4⌋₊ * Real.exp (-8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n)
          * Real.exp ((10000 * K * (1 + K ^ 2) + 16 * K + 8) / Real.sqrt n) :=
        pmf'_bracket_upper hK hn hthr hk.2.le
    _ = Real.exp ((10000 * K * (1 + K ^ 2) + 16 * K + 8) / Real.sqrt n)
          * (pmf' n ⌊(n : ℝ) / 4⌋₊
            * Real.exp (-8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n)) := by ring

/-- **Summed lower bracket** over the window. -/
private lemma window_sum_ge {n : ℕ} {K : ℝ} (hK : 1 ≤ K)
    (hn : 64 ≤ n) (hthr : (64 * K) ^ 2 ≤ (n : ℝ)) :
    Real.exp (-((10000 * K * (1 + K ^ 2) + 16 * K + 8) / Real.sqrt n))
        * (pmf' n ⌊(n : ℝ) / 4⌋₊
          * ∑ k ∈ (Finset.range n).filter
              (fun k : ℕ => |(k : ℝ) - (n : ℝ) / 4| < K * Real.sqrt n),
              Real.exp (-8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n))
      ≤ ∑ k ∈ (Finset.range n).filter
          (fun k : ℕ => |(k : ℝ) - (n : ℝ) / 4| < K * Real.sqrt n), pmf' n k := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [Finset.mem_filter] at hk
  calc Real.exp (-((10000 * K * (1 + K ^ 2) + 16 * K + 8) / Real.sqrt n))
        * (pmf' n ⌊(n : ℝ) / 4⌋₊
          * Real.exp (-8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n))
      = pmf' n ⌊(n : ℝ) / 4⌋₊ * Real.exp (-8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n)
          * Real.exp (-((10000 * K * (1 + K ^ 2) + 16 * K + 8) / Real.sqrt n)) := by
        ring
    _ ≤ pmf' n k := pmf'_bracket_lower hK hn hthr hk.2.le

/-! ### The Gaussian off-window mass -/

/-- Off the window `|k − n/4| < K√n`, every Gaussian term is `≤ e^{−8K²}`,
so the off-window Gaussian mass is at most `n·e^{−8K²}`. -/
private lemma sum_gauss_notwindow_le (n : ℕ) {K : ℝ} (hK0 : 0 ≤ K) :
    ∑ k ∈ (Finset.range n).filter
        (fun k : ℕ => ¬ |(k : ℝ) - (n : ℝ) / 4| < K * Real.sqrt n),
      Real.exp (-8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n)
      ≤ (n : ℝ) * Real.exp (-8 * K ^ 2) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
    have hterm : ∀ k ∈ (Finset.range n).filter
        (fun k : ℕ => ¬ |(k : ℝ) - (n : ℝ) / 4| < K * Real.sqrt n),
        Real.exp (-8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n) ≤ Real.exp (-8 * K ^ 2) := by
      intro k hk
      rw [Finset.mem_filter, not_lt] at hk
      have hsq : K ^ 2 * (n : ℝ) ≤ ((k : ℝ) - (n : ℝ) / 4) ^ 2 := by
        have h1 : (K * Real.sqrt n) ^ 2 ≤ |(k : ℝ) - (n : ℝ) / 4| ^ 2 :=
          pow_le_pow_left₀ (by positivity) hk.2 2
        rwa [mul_pow, Real.sq_sqrt hn0.le, sq_abs] at h1
      refine Real.exp_le_exp.mpr ?_
      rw [div_le_iff₀ hn0]
      nlinarith [hsq]
    calc ∑ k ∈ (Finset.range n).filter
          (fun k : ℕ => ¬ |(k : ℝ) - (n : ℝ) / 4| < K * Real.sqrt n),
          Real.exp (-8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n)
        ≤ ((Finset.range n).filter
            (fun k : ℕ => ¬ |(k : ℝ) - (n : ℝ) / 4| < K * Real.sqrt n)).card
              • Real.exp (-8 * K ^ 2) :=
          Finset.sum_le_card_nsmul _ _ _ hterm
      _ ≤ (n : ℝ) * Real.exp (-8 * K ^ 2) := by
          rw [nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          have h := Finset.card_filter_le (Finset.range n)
            (fun k : ℕ => ¬ |(k : ℝ) - (n : ℝ) / 4| < K * Real.sqrt n)
          rw [Finset.card_range] at h
          exact_mod_cast h

/-! ### Arithmetic of the moving window radius `K(n) = n^{1/8} = √√√n` -/

/-- `(√√√n)⁴ = √n` (so the window error `C(K)/√n` is `O(1/K)`). -/
private lemma sqrt_sqrt_sqrt_pow_four (n : ℕ) :
    Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 4 = Real.sqrt n := by
  have h1 : Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2 = Real.sqrt (Real.sqrt n) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have h2 : Real.sqrt (Real.sqrt n) ^ 2 = Real.sqrt n :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  calc Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 4
      = (Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2) ^ 2 := by ring
    _ = Real.sqrt (Real.sqrt n) ^ 2 := by rw [h1]
    _ = Real.sqrt n := h2

/-- The window error at radius `K`: `C(K)/K⁴ ≤ 20024/K`. -/
private lemma eps_le_aux {K : ℝ} (hK : 1 ≤ K) :
    (10000 * K * (1 + K ^ 2) + 16 * K + 8) / K ^ 4 ≤ 20024 * K⁻¹ := by
  have hK0 : (0 : ℝ) < K := by linarith
  have h1 : K ≤ K ^ 2 := by nlinarith
  have h2 : K ^ 2 ≤ K ^ 4 := by
    nlinarith [mul_nonneg (sq_nonneg K) (show (0 : ℝ) ≤ K ^ 2 - 1 by nlinarith)]
  rw [show (20024 : ℝ) * K⁻¹ = 20024 / K from by rw [div_eq_mul_inv],
    div_le_div_iff₀ (by positivity) hK0]
  nlinarith [h1, h2]

/-- The window-threshold `(64K)² ≤ n = K⁸` holds once `K ≥ 4`. -/
private lemma thr_aux {K : ℝ} (hK : 4 ≤ K) : (64 * K) ^ 2 ≤ (K ^ 4) ^ 2 := by
  have h46 : (4096 : ℝ) ≤ K ^ 6 := by
    calc (4096 : ℝ) = 4 ^ 6 := by norm_num
      _ ≤ K ^ 6 := pow_le_pow_left₀ (by norm_num) hK 6
  nlinarith [mul_le_mul_of_nonneg_right h46 (sq_nonneg K)]

/-! ### The mode-prefactor limit -/

/-- **The mode-prefactor limit** (the `hpre` input of
`pmf'_local_limit_of_mode`), conditional on the normalisation:

  `σ(n) · pmf'(n, ⌊n/4⌋) → 1/√(2π)`.

Self-normalisation squeeze with the moving window `|k − n/4| < K√n`,
`K = n^{1/8}`: the window pmf'-mass is `1 − O(e^{−(K−1)})` (annulus bound) and
equals `pmf'(n,⌊n/4⌋)·Σ_W e^{−8(k−n/4)²/n}` up to `e^{±C(K)/√n} → 1` (window
bracket), while `Σ_W e^{−8(k−n/4)²/n}/√n → √(π/8)` (Gaussian brick plus the
off-window bound `√n·e^{−8K²} → 0`).  Hence `√n·pmf'(n,⌊n/4⌋) → √(8/π)` and
`σ·pmf' = √n·pmf'/4 → √(8/π)/4 = 1/√(2π)`. -/
theorem mode_prefactor_tendsto
    (hnorm : ∀ n : ℕ, 1 ≤ n → ∑ k ∈ Finset.range n, pmf' n k = 1) :
    Tendsto (fun n : ℕ => sigmaP2 n * pmf' n ⌊(n : ℝ) / 4⌋₊) atTop
      (𝓝 (1 / Real.sqrt (2 * Real.pi))) := by
  classical
  -- `√n → ∞` and `K(n) = √√√n → ∞`
  have hsqrtN : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hK2top : Tendsto (fun n : ℕ => Real.sqrt (Real.sqrt n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hsqrtN
  have hKtop : Tendsto (fun n : ℕ => Real.sqrt (Real.sqrt (Real.sqrt n))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hK2top
  -- the window error `ε(n) = C(K(n))/√n → 0`, so `e^{±ε} → 1`
  have heps : Tendsto (fun n : ℕ =>
      (10000 * Real.sqrt (Real.sqrt (Real.sqrt n))
          * (1 + Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2)
        + 16 * Real.sqrt (Real.sqrt (Real.sqrt n)) + 8) / Real.sqrt n)
      atTop (𝓝 0) := by
    have hb : Tendsto (fun n : ℕ =>
        20024 * (Real.sqrt (Real.sqrt (Real.sqrt n)))⁻¹) atTop (𝓝 0) := by
      have h2 := hKtop.inv_tendsto_atTop.const_mul (20024 : ℝ)
      simpa using h2
    refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hb
    filter_upwards [hKtop.eventually_ge_atTop 1] with n hK1
    have h := eps_le_aux hK1
    rwa [sqrt_sqrt_sqrt_pow_four n] at h
  have hexp_pos : Tendsto (fun n : ℕ =>
      Real.exp ((10000 * Real.sqrt (Real.sqrt (Real.sqrt n))
          * (1 + Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2)
        + 16 * Real.sqrt (Real.sqrt (Real.sqrt n)) + 8) / Real.sqrt n))
      atTop (𝓝 1) := by
    have h := (Real.continuous_exp.tendsto 0).comp heps
    simpa [Function.comp_def] using h
  have hexp_neg : Tendsto (fun n : ℕ =>
      Real.exp (-((10000 * Real.sqrt (Real.sqrt (Real.sqrt n))
          * (1 + Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2)
        + 16 * Real.sqrt (Real.sqrt (Real.sqrt n)) + 8) / Real.sqrt n)))
      atTop (𝓝 1) := by
    have hneg : Tendsto (fun n : ℕ =>
        -((10000 * Real.sqrt (Real.sqrt (Real.sqrt n))
            * (1 + Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2)
          + 16 * Real.sqrt (Real.sqrt (Real.sqrt n)) + 8) / Real.sqrt n))
        atTop (𝓝 0) := by
      simpa using heps.neg
    have h := (Real.continuous_exp.tendsto 0).comp hneg
    simpa [Function.comp_def] using h
  -- the annulus mass bound `α(n) = 10⁸·e^{−(K−1)} → 0`
  have halpha : Tendsto (fun n : ℕ =>
      (100000000 : ℝ) * Real.exp (-(Real.sqrt (Real.sqrt (Real.sqrt n)) - 1)))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => Real.sqrt (Real.sqrt (Real.sqrt n)) + (-1 : ℝ))
        atTop atTop := tendsto_atTop_add_const_right atTop (-1 : ℝ) hKtop
    have h2 : Tendsto (fun n : ℕ => -(Real.sqrt (Real.sqrt (Real.sqrt n)) - 1))
        atTop atBot := by
      refine (tendsto_neg_atTop_atBot.comp h1).congr (fun n => ?_)
      simp only [Function.comp_apply]
      ring
    have h3 : Tendsto (fun n : ℕ =>
        Real.exp (-(Real.sqrt (Real.sqrt (Real.sqrt n)) - 1))) atTop (𝓝 0) := by
      have h := Real.tendsto_exp_atBot.comp h2
      simpa [Function.comp_def] using h
    have h4 := h3.const_mul (100000000 : ℝ)
    simpa using h4
  -- the scaled off-window Gaussian mass `√n·e^{−8K²} → 0`
  have hbeta : Tendsto (fun n : ℕ =>
      Real.sqrt n * Real.exp (-8 * Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2))
      atTop (𝓝 0) := by
    have h8 : Tendsto (fun n : ℕ => 8 * Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2)
        atTop atTop := by
      refine tendsto_atTop_mono' atTop ?_ hKtop
      filter_upwards [hKtop.eventually_ge_atTop 1] with n h1
      nlinarith [h1]
    have h2 : Tendsto (fun n : ℕ =>
        (8 * Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2) ^ 2
          * Real.exp (-(8 * Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2)))
        atTop (𝓝 0) := by
      have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp h8
      simpa [Function.comp_def] using h
    have h3 := h2.const_mul ((64 : ℝ)⁻¹)
    rw [mul_zero] at h3
    refine h3.congr (fun n => ?_)
    calc (64 : ℝ)⁻¹ * ((8 * Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2) ^ 2
          * Real.exp (-(8 * Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2)))
        = Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 4
            * Real.exp (-(8 * Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2)) := by
          ring
      _ = Real.sqrt n * Real.exp (-(8 * Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2)) := by
          rw [sqrt_sqrt_sqrt_pow_four n]
      _ = Real.sqrt n * Real.exp (-8 * Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2) := by
          rw [show -(8 * Real.sqrt (Real.sqrt (Real.sqrt (n : ℝ))) ^ 2)
              = -8 * Real.sqrt (Real.sqrt (Real.sqrt (n : ℝ))) ^ 2 from by ring]
  -- scaled off-window Gaussian sum `→ 0`
  have hoff : Tendsto (fun n : ℕ =>
      (∑ k ∈ (Finset.range n).filter
          (fun k : ℕ => ¬ |(k : ℝ) - (n : ℝ) / 4|
            < Real.sqrt (Real.sqrt (Real.sqrt n)) * Real.sqrt n),
        Real.exp (-8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n)) / Real.sqrt n)
      atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hbeta
    filter_upwards [eventually_ge_atTop 1] with n hn1
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hr0 : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn0
    rw [div_le_iff₀ hr0]
    calc ∑ k ∈ (Finset.range n).filter
          (fun k : ℕ => ¬ |(k : ℝ) - (n : ℝ) / 4|
            < Real.sqrt (Real.sqrt (Real.sqrt n)) * Real.sqrt n),
          Real.exp (-8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n)
        ≤ (n : ℝ) * Real.exp (-8 * Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2) :=
          sum_gauss_notwindow_le n (Real.sqrt_nonneg _)
      _ = Real.sqrt n * Real.exp (-8 * Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2)
            * Real.sqrt n := by
          linear_combination
            (- Real.exp (-8 * Real.sqrt (Real.sqrt (Real.sqrt (n : ℝ))) ^ 2))
              * Real.mul_self_sqrt hn0.le
  -- scaled window Gaussian sum `→ √(π/8)`
  have hSGdiv : Tendsto (fun n : ℕ =>
      (∑ k ∈ (Finset.range n).filter
          (fun k : ℕ => |(k : ℝ) - (n : ℝ) / 4|
            < Real.sqrt (Real.sqrt (Real.sqrt n)) * Real.sqrt n),
        Real.exp (-8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n)) / Real.sqrt n)
      atTop (𝓝 (Real.sqrt (Real.pi / 8))) := by
    have h := centred_gaussian_sum_tendsto.sub hoff
    rw [sub_zero] at h
    refine h.congr (fun n => ?_)
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range n)
      (fun k : ℕ => |(k : ℝ) - (n : ℝ) / 4|
        < Real.sqrt (Real.sqrt (Real.sqrt n)) * Real.sqrt n)
      (fun k : ℕ => Real.exp (-8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n))
    rw [← hsplit]
    ring
  -- the squeeze: `pmf'(k₀)·Σ_W G → 1`
  have hv : Tendsto (fun n : ℕ =>
      pmf' n ⌊(n : ℝ) / 4⌋₊
        * ∑ k ∈ (Finset.range n).filter
            (fun k : ℕ => |(k : ℝ) - (n : ℝ) / 4|
              < Real.sqrt (Real.sqrt (Real.sqrt n)) * Real.sqrt n),
            Real.exp (-8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n))
      atTop (𝓝 1) := by
    have hlo : Tendsto (fun n : ℕ =>
        Real.exp (-((10000 * Real.sqrt (Real.sqrt (Real.sqrt n))
            * (1 + Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2)
          + 16 * Real.sqrt (Real.sqrt (Real.sqrt n)) + 8) / Real.sqrt n))
          * (1 - 100000000
              * Real.exp (-(Real.sqrt (Real.sqrt (Real.sqrt n)) - 1))))
        atTop (𝓝 1) := by
      have h2 : Tendsto (fun n : ℕ =>
          1 - 100000000 * Real.exp (-(Real.sqrt (Real.sqrt (Real.sqrt n)) - 1)))
          atTop (𝓝 1) := by
        have h3 := (tendsto_const_nhds
          (x := (1 : ℝ)) (f := (atTop : Filter ℕ))).sub halpha
        simpa using h3
      have h := hexp_neg.mul h2
      simpa using h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hexp_pos ?_ ?_
    · -- lower bound: `e^{−ε}(1−α) ≤ pmf'(k₀)·Σ_W G`
      filter_upwards [eventually_ge_atTop 1000000000, hKtop.eventually_ge_atTop 4]
        with n hn9 hK4'
      have hK1 : (1 : ℝ) ≤ Real.sqrt (Real.sqrt (Real.sqrt n)) := by linarith
      have hK2 : (2 : ℝ) ≤ Real.sqrt (Real.sqrt (Real.sqrt n)) := by linarith
      have hn64 : 64 ≤ n := by omega
      have hthr : (64 * Real.sqrt (Real.sqrt (Real.sqrt n))) ^ 2 ≤ (n : ℝ) := by
        have h := thr_aux hK4'
        rw [sqrt_sqrt_sqrt_pow_four n] at h
        rwa [Real.sq_sqrt (Nat.cast_nonneg n)] at h
      have hnorm' := hnorm n (by omega)
      have hfilter_eq : (Finset.range n).filter
            (fun k : ℕ => ¬ |(k : ℝ) - (n : ℝ) / 4|
              < Real.sqrt (Real.sqrt (Real.sqrt n)) * Real.sqrt n)
          = (Finset.range n).filter
            (fun k : ℕ => Real.sqrt (Real.sqrt (Real.sqrt n)) * Real.sqrt n
              ≤ |(k : ℝ) - (n : ℝ) / 4|) :=
        Finset.filter_congr (fun k _ => not_lt)
      have hann := sum_pmf'_annulus_le hK2 hn9 hnorm'
      rw [← hfilter_eq] at hann
      have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range n)
        (fun k : ℕ => |(k : ℝ) - (n : ℝ) / 4|
          < Real.sqrt (Real.sqrt (Real.sqrt n)) * Real.sqrt n)
        (fun k : ℕ => pmf' n k)
      have hSp_ge : 1 - 100000000
            * Real.exp (-(Real.sqrt (Real.sqrt (Real.sqrt n)) - 1))
          ≤ ∑ k ∈ (Finset.range n).filter
              (fun k : ℕ => |(k : ℝ) - (n : ℝ) / 4|
                < Real.sqrt (Real.sqrt (Real.sqrt n)) * Real.sqrt n), pmf' n k := by
        linarith [hsplit, hnorm', hann]
      have hbr := window_sum_le hK1 hn64 hthr
      have hcancel : Real.exp (-((10000 * Real.sqrt (Real.sqrt (Real.sqrt n))
            * (1 + Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2)
          + 16 * Real.sqrt (Real.sqrt (Real.sqrt n)) + 8) / Real.sqrt n))
          * Real.exp ((10000 * Real.sqrt (Real.sqrt (Real.sqrt n))
            * (1 + Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2)
          + 16 * Real.sqrt (Real.sqrt (Real.sqrt n)) + 8) / Real.sqrt n) = 1 := by
        rw [← Real.exp_add]; simp
      calc Real.exp (-((10000 * Real.sqrt (Real.sqrt (Real.sqrt n))
            * (1 + Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2)
          + 16 * Real.sqrt (Real.sqrt (Real.sqrt n)) + 8) / Real.sqrt n))
          * (1 - 100000000
              * Real.exp (-(Real.sqrt (Real.sqrt (Real.sqrt n)) - 1)))
          ≤ Real.exp (-((10000 * Real.sqrt (Real.sqrt (Real.sqrt n))
              * (1 + Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2)
            + 16 * Real.sqrt (Real.sqrt (Real.sqrt n)) + 8) / Real.sqrt n))
            * ∑ k ∈ (Finset.range n).filter
                (fun k : ℕ => |(k : ℝ) - (n : ℝ) / 4|
                  < Real.sqrt (Real.sqrt (Real.sqrt n)) * Real.sqrt n), pmf' n k :=
            mul_le_mul_of_nonneg_left hSp_ge (Real.exp_pos _).le
        _ ≤ Real.exp (-((10000 * Real.sqrt (Real.sqrt (Real.sqrt n))
              * (1 + Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2)
            + 16 * Real.sqrt (Real.sqrt (Real.sqrt n)) + 8) / Real.sqrt n))
            * (Real.exp ((10000 * Real.sqrt (Real.sqrt (Real.sqrt n))
                * (1 + Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2)
              + 16 * Real.sqrt (Real.sqrt (Real.sqrt n)) + 8) / Real.sqrt n)
              * (pmf' n ⌊(n : ℝ) / 4⌋₊
                * ∑ k ∈ (Finset.range n).filter
                    (fun k : ℕ => |(k : ℝ) - (n : ℝ) / 4|
                      < Real.sqrt (Real.sqrt (Real.sqrt n)) * Real.sqrt n),
                    Real.exp (-8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n))) :=
            mul_le_mul_of_nonneg_left hbr (Real.exp_pos _).le
        _ = pmf' n ⌊(n : ℝ) / 4⌋₊
              * ∑ k ∈ (Finset.range n).filter
                  (fun k : ℕ => |(k : ℝ) - (n : ℝ) / 4|
                    < Real.sqrt (Real.sqrt (Real.sqrt n)) * Real.sqrt n),
                  Real.exp (-8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n) := by
            rw [← mul_assoc, hcancel, one_mul]
    · -- upper bound: `pmf'(k₀)·Σ_W G ≤ e^{ε}`
      filter_upwards [eventually_ge_atTop 1000000000, hKtop.eventually_ge_atTop 4]
        with n hn9 hK4'
      have hK1 : (1 : ℝ) ≤ Real.sqrt (Real.sqrt (Real.sqrt n)) := by linarith
      have hn64 : 64 ≤ n := by omega
      have hthr : (64 * Real.sqrt (Real.sqrt (Real.sqrt n))) ^ 2 ≤ (n : ℝ) := by
        have h := thr_aux hK4'
        rw [sqrt_sqrt_sqrt_pow_four n] at h
        rwa [Real.sq_sqrt (Nat.cast_nonneg n)] at h
      have hnorm' := hnorm n (by omega)
      have hbr := window_sum_ge hK1 hn64 hthr
      have hSp_le : ∑ k ∈ (Finset.range n).filter
            (fun k : ℕ => |(k : ℝ) - (n : ℝ) / 4|
              < Real.sqrt (Real.sqrt (Real.sqrt n)) * Real.sqrt n), pmf' n k ≤ 1 := by
        rw [← hnorm']
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => pmf'_nonneg n i)
      have hcancel : Real.exp ((10000 * Real.sqrt (Real.sqrt (Real.sqrt n))
            * (1 + Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2)
          + 16 * Real.sqrt (Real.sqrt (Real.sqrt n)) + 8) / Real.sqrt n)
          * Real.exp (-((10000 * Real.sqrt (Real.sqrt (Real.sqrt n))
            * (1 + Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2)
          + 16 * Real.sqrt (Real.sqrt (Real.sqrt n)) + 8) / Real.sqrt n)) = 1 := by
        rw [← Real.exp_add]; simp
      calc pmf' n ⌊(n : ℝ) / 4⌋₊
            * ∑ k ∈ (Finset.range n).filter
                (fun k : ℕ => |(k : ℝ) - (n : ℝ) / 4|
                  < Real.sqrt (Real.sqrt (Real.sqrt n)) * Real.sqrt n),
                Real.exp (-8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n)
          = Real.exp ((10000 * Real.sqrt (Real.sqrt (Real.sqrt n))
              * (1 + Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2)
            + 16 * Real.sqrt (Real.sqrt (Real.sqrt n)) + 8) / Real.sqrt n)
            * (Real.exp (-((10000 * Real.sqrt (Real.sqrt (Real.sqrt n))
                * (1 + Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2)
              + 16 * Real.sqrt (Real.sqrt (Real.sqrt n)) + 8) / Real.sqrt n))
              * (pmf' n ⌊(n : ℝ) / 4⌋₊
                * ∑ k ∈ (Finset.range n).filter
                    (fun k : ℕ => |(k : ℝ) - (n : ℝ) / 4|
                      < Real.sqrt (Real.sqrt (Real.sqrt n)) * Real.sqrt n),
                    Real.exp (-8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n))) := by
            rw [← mul_assoc, hcancel, one_mul]
        _ ≤ Real.exp ((10000 * Real.sqrt (Real.sqrt (Real.sqrt n))
              * (1 + Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2)
            + 16 * Real.sqrt (Real.sqrt (Real.sqrt n)) + 8) / Real.sqrt n)
            * ∑ k ∈ (Finset.range n).filter
                (fun k : ℕ => |(k : ℝ) - (n : ℝ) / 4|
                  < Real.sqrt (Real.sqrt (Real.sqrt n)) * Real.sqrt n), pmf' n k :=
            mul_le_mul_of_nonneg_left hbr (Real.exp_pos _).le
        _ ≤ Real.exp ((10000 * Real.sqrt (Real.sqrt (Real.sqrt n))
              * (1 + Real.sqrt (Real.sqrt (Real.sqrt n)) ^ 2)
            + 16 * Real.sqrt (Real.sqrt (Real.sqrt n)) + 8) / Real.sqrt n) :=
            mul_le_of_le_one_right (Real.exp_pos _).le hSp_le
  -- the window Gaussian sum is eventually positive (the mode is in the window)
  have hSGpos : ∀ᶠ n : ℕ in atTop,
      0 < ∑ k ∈ (Finset.range n).filter
          (fun k : ℕ => |(k : ℝ) - (n : ℝ) / 4|
            < Real.sqrt (Real.sqrt (Real.sqrt n)) * Real.sqrt n),
          Real.exp (-8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n) := by
    filter_upwards [eventually_ge_atTop 1000000000, hKtop.eventually_ge_atTop 4]
      with n hn9 hK4'
    have hnR : (1000000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn9
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hr1 : (1 : ℝ) ≤ Real.sqrt n := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by linarith)
    have hmem : ⌊(n : ℝ) / 4⌋₊ ∈ (Finset.range n).filter
        (fun k : ℕ => |(k : ℝ) - (n : ℝ) / 4|
          < Real.sqrt (Real.sqrt (Real.sqrt n)) * Real.sqrt n) := by
      rw [Finset.mem_filter, Finset.mem_range]
      constructor
      · have hfl : ((⌊(n : ℝ) / 4⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) / 4 :=
          Nat.floor_le (by positivity)
        have hlt : ((⌊(n : ℝ) / 4⌋₊ : ℕ) : ℝ) < (n : ℝ) := by linarith
        exact_mod_cast hlt
      · have h1 := mode_dev n
        have h4r : (4 : ℝ) * 1 ≤ Real.sqrt (Real.sqrt (Real.sqrt n)) * Real.sqrt n :=
          mul_le_mul hK4' hr1 (by norm_num) (by positivity)
        calc |((⌊(n : ℝ) / 4⌋₊ : ℕ) : ℝ) - (n : ℝ) / 4| ≤ 1 := h1
          _ < Real.sqrt (Real.sqrt (Real.sqrt n)) * Real.sqrt n := by linarith
    exact Finset.sum_pos' (fun i _ => (Real.exp_pos _).le)
      ⟨⌊(n : ℝ) / 4⌋₊, hmem, Real.exp_pos _⟩
  -- divide: `√n·pmf'(k₀) → 1/√(π/8) = √(8/π)`
  have hu : Tendsto (fun n : ℕ => Real.sqrt n * pmf' n ⌊(n : ℝ) / 4⌋₊) atTop
      (𝓝 (Real.sqrt (8 / Real.pi))) := by
    have hne : Real.sqrt (Real.pi / 8) ≠ 0 := by positivity
    have hdiv := hv.div hSGdiv hne
    have hval : (1 : ℝ) / Real.sqrt (Real.pi / 8) = Real.sqrt (8 / Real.pi) := by
      rw [one_div, ← Real.sqrt_inv, inv_div]
    rw [hval] at hdiv
    refine hdiv.congr' ?_
    filter_upwards [hSGpos, eventually_ge_atTop 1] with n hpos hn1
    simp only [Pi.div_apply]
    rw [div_div_eq_mul_div, mul_right_comm, mul_div_assoc, div_self hpos.ne',
      mul_one, mul_comm]
  -- conclude: `σ·pmf'(k₀) = √n·pmf'(k₀)/4 → √(8/π)/4 = 1/√(2π)`
  have hval2 : Real.sqrt (8 / Real.pi) / 4 = 1 / Real.sqrt (2 * Real.pi) := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have h2π : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    have hmul : Real.sqrt (8 / Real.pi) * Real.sqrt (2 * Real.pi) = 4 := by
      rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 8 / Real.pi)]
      rw [show 8 / Real.pi * (2 * Real.pi) = 16 from by field_simp; ring]
      rw [show (16 : ℝ) = 4 ^ 2 from by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [div_eq_div_iff (by norm_num : (4 : ℝ) ≠ 0) h2π.ne']
    rw [hmul]; norm_num
  have hfinal := hu.div_const 4
  rw [hval2] at hfinal
  refine hfinal.congr (fun n => ?_)
  simp only [sigmaP2]
  ring

/-! ### The unconditional local limit -/

/-- **The pointwise local limit**, with the prefactor limit discharged by
`mode_prefactor_tendsto`: conditionally on the normalisation `hnorm` alone,

  `σ(n)·pmf'(n, ⌊μ+xσ⌋) → exp(−x²/2)/√(2π)`   for every `x`. -/
theorem pmf'_local_limit'
    (hnorm : ∀ n : ℕ, 1 ≤ n → ∑ k ∈ Finset.range n, pmf' n k = 1) (x : ℝ) :
    Tendsto (fun n : ℕ => sigmaP2 n * pmf' n ⌊muP2 n + x * sigmaP2 n⌋₊) atTop
      (𝓝 (Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi))) :=
  pmf'_local_limit_of_mode (mode_prefactor_tendsto hnorm) x

end MakinenAnalysis
