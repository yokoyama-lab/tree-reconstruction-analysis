import Mathlib
import MakinenAnalysis.LocalCLTMode
import MakinenAnalysis.LocalCLTGauss

/-!
# The pointwise local central limit for the double-pop law

This file assembles the pointwise **local limit theorem** for the explicit law
`pmf'` of the double-pop count `P₂` (see `LocalCLT.lean` for the definitions and
the exact ratio analysis, `LocalCLTWindow`/`LocalCLTMode` for the window/tail and
self-normalisation layers, and `LocalCLTGauss` for the Gaussian-sum brick).

The target is the pointwise local limit

  `σ(n) · pmf'(n, ⌊μ(n) + x·σ(n)⌋) → exp(−x²/2)/√(2π)`   (`μ = n/4`, `σ = √n/4`).

## What is proved here (all with **zero sorries**)

* `abs_log_pmf'_telescope_B` — the sharp `√n`-window telescope with an explicit
  quadratic error, parametrised by a deviation bound `B` (the workhorse; a
  `B`-parametrised version of `abs_log_pmf'_window_sum`, keeping the *true*
  quadratic per-step error rather than its worst case over the coarse window).

* `abs_log_ratio_gauss_dir` — the **directed Gaussian ratio bound**: for
  `a ≤ b` both within `K√n` of `n/4` (and `n ≥ (64K)²`),
  `|log pmf'(n,b) − log pmf'(n,a) + 8((b−n/4)² − (a−n/4)²)/n|
      ≤ (10000·K(1+K²) + 16K)/√n`.

* `pmf'_ratio_gaussian` — **Deliverable 1**, the pointwise Gaussian ratio at the
  mode `k₀ = ⌊n/4⌋`: for `|k − n/4| ≤ K√n` (and `n ≥ (64K)²`),
  `|log pmf'(n,k) − log pmf'(n,k₀) + 8(k−n/4)²/n| ≤ C(K)/√n`,
  `C(K) = 10000·K(1+K²) + 16K + 8`.  This is the analytic core.

* `pmf'_ratio_tendsto` — the ratio converges: for every fixed `x`,
  `pmf'(n, ⌊μ+xσ⌋) / pmf'(n, ⌊n/4⌋) → exp(−x²/2)`.

* `pmf'_local_limit_of_mode` — **Deliverable 3**, the full local limit, derived
  from `pmf'_ratio_tendsto` and the prefactor limit
  `σ(n)·pmf'(n, ⌊n/4⌋) → 1/√(2π)` supplied as a hypothesis `hpre`.

The one genuinely missing analytic input is the **prefactor limit** `hpre`
(`σ·pmf'(n, mode) → 1/√(2π)`), whose exact constant is fixed by
self-normalisation against the Gaussian sum `gaussian_sum_div_sqrt_tendsto`
(`LocalCLTGauss`).  It is isolated as an explicit hypothesis; the bracketing
bounds `mode_upper`/`mode_lower` (`LocalCLTMode`) already pin the prefactor to
the interval `[1/100000, 2026]`, but not to the exact constant.
-/

namespace MakinenAnalysis

open Finset Filter Topology

/-! ### A convergence helper -/

/-- If `Q → c`, `err → 0` and eventually `|L − Q| ≤ err`, then `L → c`. -/
private lemma tendsto_of_abs_sub_le {L Q err : ℕ → ℝ} {c : ℝ}
    (hQ : Tendsto Q atTop (𝓝 c)) (herr : Tendsto err atTop (𝓝 0))
    (h : ∀ᶠ n in atTop, |L n - Q n| ≤ err n) :
    Tendsto L atTop (𝓝 c) := by
  have hz : Tendsto (fun n => L n - Q n) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ herr
    filter_upwards [h] with n hn
    simpa [Real.norm_eq_abs] using hn
  have key : Tendsto (fun n => Q n + (L n - Q n)) atTop (𝓝 (c + 0)) := hQ.add hz
  rw [add_zero] at key
  exact key.congr (fun n => by ring)

/-! ### The `B`-parametrised sharp window telescope -/

/-- **Sharp telescope with an explicit deviation bound `B`.**  For `64 ≤ n`, a
block `[k₀, k₀+s]` inside the support of `pmf' n ·` with every intermediate
point `k₀+j` (`j < s`) at deviation `≤ n/64` from `n/4` (so `log_pmfRatio_taylor`
applies) and `≤ B`,

`|log pmf'(n,k₀+s) − log pmf'(n,k₀) + 16(s(k₀−n/4)+s(s−1)/2)/n| ≤ s·5000(n+B²)/n²`.

Unlike `abs_log_pmf'_window_sum` this keeps the *true* per-step quadratic error
(bounded by `B²`, not `(n/32)²`), which is `O(1/√n)`-summable when `B = O(√n)`. -/
private lemma abs_log_pmf'_telescope_B {n k₀ s : ℕ} (hn : 64 ≤ n)
    (hguard : 2 * (k₀ + s) + 1 ≤ n) {B : ℝ}
    (hwin : ∀ j : ℕ, j < s → |((k₀ : ℝ) + (j : ℝ)) - (n : ℝ) / 4| ≤ (n : ℝ) / 64)
    (hdev : ∀ j : ℕ, j < s → |((k₀ : ℝ) + (j : ℝ)) - (n : ℝ) / 4| ≤ B) :
    |Real.log (pmf' n (k₀ + s)) - Real.log (pmf' n k₀)
        + 16 * ((s : ℝ) * ((k₀ : ℝ) - (n : ℝ) / 4)
            + (s : ℝ) * ((s : ℝ) - 1) / 2) / (n : ℝ)|
      ≤ (s : ℝ) * (5000 * ((n : ℝ) + B ^ 2) / (n : ℝ) ^ 2) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (64 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos hn0 2
  have hd : ∑ j ∈ Finset.range s, 16 * (((k₀ : ℝ) + (j : ℝ)) - (n : ℝ) / 4) / (n : ℝ)
      = 16 * ((s : ℝ) * ((k₀ : ℝ) - (n : ℝ) / 4)
          + (s : ℝ) * ((s : ℝ) - 1) / 2) / (n : ℝ) := by
    rw [← Finset.sum_div, ← Finset.mul_sum, drift_sum_eq]
  rw [log_pmf'_add_sub n k₀ s hguard, ← hd, ← Finset.sum_add_distrib]
  calc |∑ j ∈ Finset.range s, (Real.log (pmfRatio n (k₀ + j))
          + 16 * (((k₀ : ℝ) + (j : ℝ)) - (n : ℝ) / 4) / (n : ℝ))|
      ≤ ∑ j ∈ Finset.range s, |Real.log (pmfRatio n (k₀ + j))
          + 16 * (((k₀ : ℝ) + (j : ℝ)) - (n : ℝ) / 4) / (n : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range s, 5000 * ((n : ℝ) + B ^ 2) / (n : ℝ) ^ 2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' : j < s := Finset.mem_range.mp hj
        have hcast : ((k₀ + j : ℕ) : ℝ) = (k₀ : ℝ) + (j : ℝ) := by push_cast; ring
        have hwj := hwin j hj'
        rw [← hcast] at hwj
        have ht := log_pmfRatio_taylor (show 2 * (k₀ + j) + 3 ≤ n by omega) hn hwj
        rw [hcast] at ht
        refine ht.trans ?_
        have hh := abs_le.mp (hdev j hj')
        have hsqB : (((k₀ : ℝ) + (j : ℝ)) - (n : ℝ) / 4) ^ 2 ≤ B ^ 2 := by
          nlinarith [hh.1, hh.2]
        rw [div_le_div_iff₀ hn2 hn2]
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ B ^ 2
          - (((k₀ : ℝ) + (j : ℝ)) - (n : ℝ) / 4) ^ 2) hn2.le]
    _ = (s : ℝ) * (5000 * ((n : ℝ) + B ^ 2) / (n : ℝ) ^ 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ### The directed Gaussian ratio bound -/

/-- **Directed Gaussian ratio bound.**  For `a ≤ b` both within `K√n` of `n/4`
(with `1 ≤ K` and `(64K)² ≤ n`, so the whole block lies in the `n/64`-window and
`log_pmfRatio_taylor` applies at every step),

`|log pmf'(n,b) − log pmf'(n,a) + 8(b−n/4)²/n − 8(a−n/4)²/n|
    ≤ (10000·K(1+K²) + 16K)/√n`.

The drift `16(s(a−n/4)+s(s−1)/2)/n` from `abs_log_pmf'_telescope_B` telescopes to
`8((b−n/4)² − (a−n/4)²)/n − 8s/n`; the residual `8s/n ≤ 16K/√n` and the sharp
telescope error `s·5000(n+(K√n)²)/n² ≤ 10000·K(1+K²)/√n` give the bound. -/
private lemma abs_log_ratio_gauss_dir {n a b : ℕ} {K : ℝ} (hK : 1 ≤ K)
    (hn : 64 ≤ n) (hthr : (64 * K) ^ 2 ≤ (n : ℝ)) (hab : a ≤ b)
    (ha : |(a : ℝ) - (n : ℝ) / 4| ≤ K * Real.sqrt n)
    (hb : |(b : ℝ) - (n : ℝ) / 4| ≤ K * Real.sqrt n) :
    |Real.log (pmf' n b) - Real.log (pmf' n a)
        + 8 * ((b : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ)
        - 8 * ((a : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ)|
      ≤ (10000 * K * (1 + K ^ 2) + 16 * K) / Real.sqrt n := by
  -- real-analytic scaffolding in terms of `r = √n`
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (64 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  set r := Real.sqrt n with hr_def
  have hr0 : 0 < r := Real.sqrt_pos.mpr hn0
  have hr2 : r ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hr64K : 64 * K ≤ r := by
    have h1 : Real.sqrt ((64 * K) ^ 2) ≤ Real.sqrt n := Real.sqrt_le_sqrt hthr
    rwa [Real.sqrt_sq (by positivity)] at h1
  have hr1 : (1 : ℝ) ≤ r := by nlinarith [hr64K, hK]
  have hKr_le : K * r ≤ (n : ℝ) / 64 := by
    rw [← hr2]
    nlinarith [mul_nonneg hr0.le (show (0 : ℝ) ≤ r - 64 * K by linarith)]
  have hKr_ge1 : (1 : ℝ) ≤ K * r := by
    nlinarith [mul_le_mul_of_nonneg_left hr64K hK0, hK]
  -- window facts
  have haR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  obtain ⟨haL, haU⟩ := abs_le.mp ha
  obtain ⟨hbL, hbU⟩ := abs_le.mp hb
  -- deviation and window hypotheses for the telescope
  have hdev : ∀ j : ℕ, j < b - a →
      |((a : ℝ) + (j : ℝ)) - (n : ℝ) / 4| ≤ K * r := by
    intro j hj
    have hj1 : j + 1 ≤ b - a := hj
    have hjr : (j : ℝ) ≤ (b : ℝ) - (a : ℝ) - 1 := by
      have hcast : ((j + 1 : ℕ) : ℝ) ≤ ((b - a : ℕ) : ℝ) := by exact_mod_cast hj1
      rw [Nat.cast_sub hab] at hcast; push_cast at hcast; linarith
    have hjnn : (0 : ℝ) ≤ (j : ℝ) := by positivity
    rw [abs_le]; constructor
    · linarith [haL, hKr_ge1]
    · linarith [hbU, hjr]
  have hwin : ∀ j : ℕ, j < b - a →
      |((a : ℝ) + (j : ℝ)) - (n : ℝ) / 4| ≤ (n : ℝ) / 64 :=
    fun j hj => (hdev j hj).trans hKr_le
  have h2b : 2 * b + 1 ≤ n := by
    have hbn : (b : ℝ) ≤ (n : ℝ) / 4 + K * r := by linarith [hbU]
    have : ((2 * b + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      push_cast; nlinarith [hbn, hKr_le, hn0]
    exact_mod_cast this
  have hbnat : a + (b - a) = b := by omega
  -- apply the telescope with base `a`, length `b − a`, `B = K r`
  have hguard : 2 * (a + (b - a)) + 1 ≤ n := by omega
  have hT := abs_log_pmf'_telescope_B (n := n) (k₀ := a) (s := b - a) hn hguard
    (B := K * r) hwin hdev
  rw [hbnat] at hT
  have hsR : ((b - a : ℕ) : ℝ) = (b : ℝ) - (a : ℝ) := by rw [Nat.cast_sub hab]
  rw [hsR] at hT
  -- rewrite the target so the telescope drift appears
  have heq : (Real.log (pmf' n b) - Real.log (pmf' n a))
        + 8 * ((b : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ)
        - 8 * ((a : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ)
      = ((Real.log (pmf' n b) - Real.log (pmf' n a))
          + 16 * (((b : ℝ) - (a : ℝ)) * ((a : ℝ) - (n : ℝ) / 4)
              + ((b : ℝ) - (a : ℝ)) * (((b : ℝ) - (a : ℝ)) - 1) / 2) / (n : ℝ))
        + 8 * ((b : ℝ) - (a : ℝ)) / (n : ℝ) := by
    field_simp
    ring
  rw [heq]
  -- triangle inequality and piece bounds
  have hnn8s : (0 : ℝ) ≤ 8 * ((b : ℝ) - (a : ℝ)) / (n : ℝ) :=
    div_nonneg (by linarith [haR]) hn0.le
  have hsR_le : (b : ℝ) - (a : ℝ) ≤ 2 * K * r := by linarith [hbU, haL]
  have hfac_nn : (0 : ℝ) ≤ 5000 * ((n : ℝ) + (K * r) ^ 2) / (n : ℝ) ^ 2 := by positivity
  -- Tb ≤ 10000 K (1+K²) / r
  have hp1 : ((b : ℝ) - (a : ℝ)) * (5000 * ((n : ℝ) + (K * r) ^ 2) / (n : ℝ) ^ 2)
      ≤ 10000 * K * (1 + K ^ 2) / r := by
    calc ((b : ℝ) - (a : ℝ)) * (5000 * ((n : ℝ) + (K * r) ^ 2) / (n : ℝ) ^ 2)
        ≤ (2 * K * r) * (5000 * ((n : ℝ) + (K * r) ^ 2) / (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hsR_le hfac_nn
      _ = 10000 * K * (1 + K ^ 2) / r := by
          rw [← hr2]; field_simp; ring
  -- 8 s / n ≤ 16 K / r
  have hp3 : 8 * ((b : ℝ) - (a : ℝ)) / (n : ℝ) ≤ 16 * K / r := by
    rw [div_le_div_iff₀ hn0 hr0]
    nlinarith [mul_le_mul_of_nonneg_right hsR_le hr0.le, hr2]
  have hsum : 10000 * K * (1 + K ^ 2) / r + 16 * K / r
      = (10000 * K * (1 + K ^ 2) + 16 * K) / r := by ring
  calc |((Real.log (pmf' n b) - Real.log (pmf' n a))
          + 16 * (((b : ℝ) - (a : ℝ)) * ((a : ℝ) - (n : ℝ) / 4)
              + ((b : ℝ) - (a : ℝ)) * (((b : ℝ) - (a : ℝ)) - 1) / 2) / (n : ℝ))
          + 8 * ((b : ℝ) - (a : ℝ)) / (n : ℝ)|
      ≤ |(Real.log (pmf' n b) - Real.log (pmf' n a))
          + 16 * (((b : ℝ) - (a : ℝ)) * ((a : ℝ) - (n : ℝ) / 4)
              + ((b : ℝ) - (a : ℝ)) * (((b : ℝ) - (a : ℝ)) - 1) / 2) / (n : ℝ)|
          + 8 * ((b : ℝ) - (a : ℝ)) / (n : ℝ) := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact (abs_of_nonneg hnn8s).le
    _ ≤ ((b : ℝ) - (a : ℝ)) * (5000 * ((n : ℝ) + (K * r) ^ 2) / (n : ℝ) ^ 2)
          + 8 * ((b : ℝ) - (a : ℝ)) / (n : ℝ) := by
        gcongr
    _ ≤ (10000 * K * (1 + K ^ 2) + 16 * K) / r := by
        rw [← hsum]; exact add_le_add hp1 hp3

/-! ### Deliverable 1: the pointwise Gaussian ratio at the mode -/

/-- The mode-centre `k₀ = ⌊n/4⌋`, at deviation `≤ 1` from `n/4`.
(public: reused by `ModePrefactorMain`) -/
lemma mode_dev (n : ℕ) : |((⌊(n : ℝ) / 4⌋₊ : ℕ) : ℝ) - (n : ℝ) / 4| ≤ 1 := by
  have h1 : ((⌊(n : ℝ) / 4⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) / 4 := Nat.floor_le (by positivity)
  have h2 : (n : ℝ) / 4 < ((⌊(n : ℝ) / 4⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [abs_le]; constructor <;> linarith

/-- **Deliverable 1 — the pointwise Gaussian ratio.**  Write `k₀ = ⌊n/4⌋`.  For
`1 ≤ K`, `n ≥ (64K)²`, and any `k` within `K√n` of `n/4`,

`|log pmf'(n,k) − log pmf'(n,k₀) + 8(k−n/4)²/n| ≤ (10000·K(1+K²) + 16K + 8)/√n`.

This is the analytic heart: the law's log-profile is the Gaussian quadratic
`−8(k−n/4)²/n = −(k−n/4)²/(2σ²)` (with `σ² = n/16`), uniformly on the window, to
error `O(1/√n)`.  Constants and threshold are explicit numerals. -/
theorem pmf'_ratio_gaussian {n : ℕ} {K : ℝ} (hK : 1 ≤ K)
    (hn : 64 ≤ n) (hthr : (64 * K) ^ 2 ≤ (n : ℝ)) {k : ℕ}
    (hk : |(k : ℝ) - (n : ℝ) / 4| ≤ K * Real.sqrt n) :
    |Real.log (pmf' n k) - Real.log (pmf' n (⌊(n : ℝ) / 4⌋₊))
        + 8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ)|
      ≤ (10000 * K * (1 + K ^ 2) + 16 * K + 8) / Real.sqrt n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (64 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  set r := Real.sqrt n with hr_def
  have hr0 : 0 < r := Real.sqrt_pos.mpr hn0
  have hr2 : r ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hr1 : (1 : ℝ) ≤ r := by
    have hr64K : 64 * K ≤ r := by
      have h1 : Real.sqrt ((64 * K) ^ 2) ≤ Real.sqrt n := Real.sqrt_le_sqrt hthr
      rwa [Real.sqrt_sq (by positivity)] at h1
    nlinarith [hr64K, hK]
  set k₀ := ⌊(n : ℝ) / 4⌋₊ with hk₀_def
  have hk₀ : |(k₀ : ℝ) - (n : ℝ) / 4| ≤ K * r := by
    refine (mode_dev n).trans ?_
    have : (1 : ℝ) ≤ K * r := by nlinarith [hr1, hK, mul_le_mul hK hr1 (by norm_num) (by linarith)]
    exact this
  have hk₀sq : ((k₀ : ℝ) - (n : ℝ) / 4) ^ 2 ≤ 1 := by
    have hh := abs_le.mp (mode_dev n)
    nlinarith [hh.1, hh.2]
  -- `8 (k₀ − n/4)² / n ≤ 8 / r`
  have hcorr : 8 * ((k₀ : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ) ≤ 8 / r := by
    rw [div_le_div_iff₀ hn0 hr0]
    nlinarith [mul_le_mul_of_nonneg_right (le_trans hk₀sq hr1) hr0.le, hr2, hr0]
  have hD8 : (10000 * K * (1 + K ^ 2) + 16 * K) / r + 8 / r
      = (10000 * K * (1 + K ^ 2) + 16 * K + 8) / r := by ring
  by_cases hkk : k₀ ≤ k
  · -- `k ≥ k₀`: directed bound with `a = k₀`, `b = k`
    have hdir := abs_log_ratio_gauss_dir hK hn hthr hkk hk₀ hk
    -- add the small `8 (k₀−n/4)²/n` correction
    have htri : |Real.log (pmf' n k) - Real.log (pmf' n k₀)
          + 8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ)|
        ≤ |Real.log (pmf' n k) - Real.log (pmf' n k₀)
            + 8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ)
            - 8 * ((k₀ : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ)|
          + 8 * ((k₀ : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ) := by
      have h := abs_add_le
        (Real.log (pmf' n k) - Real.log (pmf' n k₀)
            + 8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ)
            - 8 * ((k₀ : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ))
        (8 * ((k₀ : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ))
      have hnn : (0 : ℝ) ≤ 8 * ((k₀ : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ) := by positivity
      rw [abs_of_nonneg hnn] at h
      calc |Real.log (pmf' n k) - Real.log (pmf' n k₀)
              + 8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ)|
          = |(Real.log (pmf' n k) - Real.log (pmf' n k₀)
              + 8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ)
              - 8 * ((k₀ : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ))
              + 8 * ((k₀ : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ)| := by ring_nf
        _ ≤ _ := h
    refine htri.trans ?_
    rw [← hD8]
    exact add_le_add hdir hcorr
  · -- `k < k₀`: directed bound with `a = k`, `b = k₀`, then negate
    have hkle : k ≤ k₀ := by omega
    have hdir := abs_log_ratio_gauss_dir hK hn hthr hkle hk hk₀
    have hneg : |Real.log (pmf' n k) - Real.log (pmf' n k₀)
          + 8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ)
          - 8 * ((k₀ : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ)|
        ≤ (10000 * K * (1 + K ^ 2) + 16 * K) / r := by
      rw [show Real.log (pmf' n k) - Real.log (pmf' n k₀)
              + 8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ)
              - 8 * ((k₀ : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ)
            = -(Real.log (pmf' n k₀) - Real.log (pmf' n k)
              + 8 * ((k₀ : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ)
              - 8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ)) by ring,
        abs_neg]
      exact hdir
    have htri : |Real.log (pmf' n k) - Real.log (pmf' n k₀)
          + 8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ)|
        ≤ |Real.log (pmf' n k) - Real.log (pmf' n k₀)
            + 8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ)
            - 8 * ((k₀ : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ)|
          + 8 * ((k₀ : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ) := by
      have h := abs_add_le
        (Real.log (pmf' n k) - Real.log (pmf' n k₀)
            + 8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ)
            - 8 * ((k₀ : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ))
        (8 * ((k₀ : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ))
      have hnn : (0 : ℝ) ≤ 8 * ((k₀ : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ) := by positivity
      rw [abs_of_nonneg hnn] at h
      calc |Real.log (pmf' n k) - Real.log (pmf' n k₀)
              + 8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ)|
          = |(Real.log (pmf' n k) - Real.log (pmf' n k₀)
              + 8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ)
              - 8 * ((k₀ : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ))
              + 8 * ((k₀ : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ)| := by ring_nf
        _ ≤ _ := h
    refine htri.trans ?_
    rw [← hD8]
    exact add_le_add hneg hcorr

/-! ### Deliverable 2 (ratio form): the ratio converges to the Gaussian factor -/

/-- **The Gaussian ratio converges.**  For every fixed `x`,
`pmf'(n, ⌊μ+xσ⌋) / pmf'(n, ⌊n/4⌋) → exp(−x²/2)`.

The log-ratio equals `−8(k−n/4)²/n + O(1/√n)` (`pmf'_ratio_gaussian`), and
`8(k−n/4)²/n → x²/2` because `k − n/4 = x√n/4 + O(1)`. -/
theorem pmf'_ratio_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ =>
        pmf' n ⌊muP2 n + x * sigmaP2 n⌋₊ / pmf' n ⌊(n : ℝ) / 4⌋₊)
      atTop (𝓝 (Real.exp (-x ^ 2 / 2))) := by
  set K := |x| / 4 + 1 with hKdef
  have hK : 1 ≤ K := by rw [hKdef]; have := abs_nonneg x; linarith
  -- `√n → ∞`, hence `1/√n → 0`
  have hsqrt_tendsto : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv_sqrt : Tendsto (fun n : ℕ => 1 / Real.sqrt n) atTop (𝓝 0) := by
    simpa [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hsqrt_tendsto
  -- Step A: `(⌊μ+xσ⌋ − n/4)/√n → x/4`
  have hd_over_r : Tendsto (fun n : ℕ =>
      (((⌊muP2 n + x * sigmaP2 n⌋₊ : ℕ) : ℝ) - (n : ℝ) / 4) / Real.sqrt n)
      atTop (𝓝 (x / 4)) := by
    refine tendsto_of_abs_sub_le (Q := fun _ => x / 4) tendsto_const_nhds hinv_sqrt ?_
    filter_upwards [eventually_ge_atTop (max 1 ⌈x ^ 2⌉₊)] with n hn
    have h1 : 1 ≤ n := le_trans (le_max_left _ _) hn
    have hx2N : ⌈x ^ 2⌉₊ ≤ n := le_trans (le_max_right _ _) hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h1
    have hr0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    have hr2 : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
    have hx2 : x ^ 2 ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hx2N)
    have hxr : |x| ≤ Real.sqrt n := (Real.le_sqrt (abs_nonneg x) hn0.le).mpr (by rw [sq_abs]; exact hx2)
    have hAeq : muP2 n + x * sigmaP2 n = (n : ℝ) / 4 + x * Real.sqrt n / 4 := by
      simp only [muP2, sigmaP2]; ring
    have hAge : 0 ≤ muP2 n + x * sigmaP2 n := by
      rw [hAeq]
      have hxge : -Real.sqrt n ≤ x := (abs_le.mp hxr).1
      nlinarith [mul_le_mul_of_nonneg_right hxge hr0.le, hr2]
    have hkxAn : |(((⌊muP2 n + x * sigmaP2 n⌋₊ : ℕ) : ℝ)) - (muP2 n + x * sigmaP2 n)| ≤ 1 := by
      have hle := Nat.floor_le hAge
      have hlt := Nat.lt_floor_add_one (muP2 n + x * sigmaP2 n)
      rw [abs_le]; constructor <;> linarith
    -- `d/√n − x/4 = (⌊An⌋ − An)/√n`
    have hstep : (((⌊muP2 n + x * sigmaP2 n⌋₊ : ℕ) : ℝ) - (n : ℝ) / 4) / Real.sqrt n - x / 4
        = ((((⌊muP2 n + x * sigmaP2 n⌋₊ : ℕ) : ℝ)) - (muP2 n + x * sigmaP2 n)) / Real.sqrt n := by
      rw [hAeq]; field_simp; ring
    rw [hstep, abs_div, abs_of_pos hr0, div_le_div_iff₀ hr0 hr0]
    nlinarith [mul_le_mul_of_nonneg_right hkxAn hr0.le, hr0]
  -- Step A': `(⌊μ+xσ⌋ − n/4)² / n → (x/4)²`
  have hApow : Tendsto (fun n : ℕ =>
      ((((⌊muP2 n + x * sigmaP2 n⌋₊ : ℕ) : ℝ) - (n : ℝ) / 4) / Real.sqrt n) ^ 2)
      atTop (𝓝 ((x / 4) ^ 2)) := hd_over_r.pow 2
  have hA : Tendsto (fun n : ℕ =>
      (((⌊muP2 n + x * sigmaP2 n⌋₊ : ℕ) : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ))
      atTop (𝓝 ((x / 4) ^ 2)) := by
    refine hApow.congr (fun n => ?_)
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  -- Step B: the log-ratio converges to `−x²/2`
  have hlog : Tendsto (fun n : ℕ =>
      Real.log (pmf' n ⌊muP2 n + x * sigmaP2 n⌋₊) - Real.log (pmf' n ⌊(n : ℝ) / 4⌋₊))
      atTop (𝓝 (-x ^ 2 / 2)) := by
    refine tendsto_of_abs_sub_le
      (Q := fun n => -(8 * ((((⌊muP2 n + x * sigmaP2 n⌋₊ : ℕ) : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ))))
      (err := fun n => (10000 * K * (1 + K ^ 2) + 16 * K + 8) / Real.sqrt n)
      ?_ ?_ ?_
    · have h := (hA.const_mul (8 : ℝ)).neg
      have hval : -(8 * (x / 4) ^ 2) = -x ^ 2 / 2 := by ring
      rw [hval] at h
      exact h
    · have h0 := hinv_sqrt.const_mul (10000 * K * (1 + K ^ 2) + 16 * K + 8)
      simpa [div_eq_mul_inv] using h0
    · filter_upwards [eventually_ge_atTop (max 64 (max ⌈(64 * K) ^ 2⌉₊ ⌈x ^ 2⌉₊))] with n hn
      have h64 : 64 ≤ n := le_trans (le_max_left _ _) hn
      have hthrN : ⌈(64 * K) ^ 2⌉₊ ≤ n :=
        le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
      have hx2N : ⌈x ^ 2⌉₊ ≤ n :=
        le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by
        have : (64 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h64
        linarith
      have hr0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
      have hr2 : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
      have hthr : (64 * K) ^ 2 ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hthrN)
      have hx2 : x ^ 2 ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hx2N)
      have hxr : |x| ≤ Real.sqrt n :=
        (Real.le_sqrt (abs_nonneg x) hn0.le).mpr (by rw [sq_abs]; exact hx2)
      have hr64K : 64 * K ≤ Real.sqrt n := by
        rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 64 * K by positivity)]
        exact Real.sqrt_le_sqrt hthr
      have hr1 : (1 : ℝ) ≤ Real.sqrt n := by nlinarith [hr64K, hK]
      have hAeq : muP2 n + x * sigmaP2 n = (n : ℝ) / 4 + x * Real.sqrt n / 4 := by
        simp only [muP2, sigmaP2]; ring
      have hAge : 0 ≤ muP2 n + x * sigmaP2 n := by
        rw [hAeq]
        have hxge : -Real.sqrt n ≤ x := (abs_le.mp hxr).1
        nlinarith [mul_le_mul_of_nonneg_right hxge hr0.le, hr2]
      have hkxAn : |(((⌊muP2 n + x * sigmaP2 n⌋₊ : ℕ) : ℝ)) - (muP2 n + x * sigmaP2 n)| ≤ 1 := by
        have hle := Nat.floor_le hAge
        have hlt := Nat.lt_floor_add_one (muP2 n + x * sigmaP2 n)
        rw [abs_le]; constructor <;> linarith
      -- `|⌊μ+xσ⌋ − n/4| ≤ K√n`
      have hk_bound : |(((⌊muP2 n + x * sigmaP2 n⌋₊ : ℕ) : ℝ)) - (n : ℝ) / 4| ≤ K * Real.sqrt n := by
        have hsplit : (((⌊muP2 n + x * sigmaP2 n⌋₊ : ℕ) : ℝ)) - (n : ℝ) / 4
            = ((((⌊muP2 n + x * sigmaP2 n⌋₊ : ℕ) : ℝ)) - (muP2 n + x * sigmaP2 n))
              + x * Real.sqrt n / 4 := by rw [hAeq]; ring
        have hxrq : |x * Real.sqrt n / 4| = |x| * Real.sqrt n / 4 := by
          rw [abs_div, abs_mul, abs_of_nonneg hr0.le]; norm_num
        have hKr : K * Real.sqrt n = |x| * Real.sqrt n / 4 + Real.sqrt n := by
          rw [hKdef]; ring
        calc |(((⌊muP2 n + x * sigmaP2 n⌋₊ : ℕ) : ℝ)) - (n : ℝ) / 4|
            = |((((⌊muP2 n + x * sigmaP2 n⌋₊ : ℕ) : ℝ)) - (muP2 n + x * sigmaP2 n))
                + x * Real.sqrt n / 4| := by rw [hsplit]
          _ ≤ |(((⌊muP2 n + x * sigmaP2 n⌋₊ : ℕ) : ℝ)) - (muP2 n + x * sigmaP2 n)|
                + |x * Real.sqrt n / 4| := abs_add_le _ _
          _ ≤ 1 + |x| * Real.sqrt n / 4 := by rw [hxrq]; linarith [hkxAn]
          _ ≤ K * Real.sqrt n := by rw [hKr]; linarith [hr1]
      have hgauss := pmf'_ratio_gaussian hK h64 hthr hk_bound
      have hLQeq :
          (Real.log (pmf' n ⌊muP2 n + x * sigmaP2 n⌋₊) - Real.log (pmf' n ⌊(n : ℝ) / 4⌋₊))
            - (-(8 * ((((⌊muP2 n + x * sigmaP2 n⌋₊ : ℕ) : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ))))
          = Real.log (pmf' n ⌊muP2 n + x * sigmaP2 n⌋₊) - Real.log (pmf' n ⌊(n : ℝ) / 4⌋₊)
            + 8 * (((⌊muP2 n + x * sigmaP2 n⌋₊ : ℕ) : ℝ) - (n : ℝ) / 4) ^ 2 / (n : ℝ) := by
        ring
      rw [hLQeq]
      exact hgauss
  -- Step C: exponentiate
  have hexp : Tendsto (fun n : ℕ => Real.exp
      (Real.log (pmf' n ⌊muP2 n + x * sigmaP2 n⌋₊) - Real.log (pmf' n ⌊(n : ℝ) / 4⌋₊)))
      atTop (𝓝 (Real.exp (-x ^ 2 / 2))) :=
    (Real.continuous_exp.tendsto _).comp hlog
  refine hexp.congr' ?_
  filter_upwards [eventually_ge_atTop (max 64 ⌈(64 * K) ^ 2⌉₊)] with n hn
  have h64 : 64 ≤ n := le_trans (le_max_left _ _) hn
  have hthrN : ⌈(64 * K) ^ 2⌉₊ ≤ n := le_trans (le_max_right _ _) hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (64 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h64
    linarith
  have hr0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hthr : (64 * K) ^ 2 ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hthrN)
  have hr64K : 64 * K ≤ Real.sqrt n := by
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 64 * K by positivity)]
    exact Real.sqrt_le_sqrt hthr
  have hKr_le : K * Real.sqrt n ≤ (n : ℝ) / 64 := by
    have hr2 : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
    nlinarith [mul_nonneg hr0.le (show (0 : ℝ) ≤ Real.sqrt n - 64 * K by linarith), hr2]
  -- support guards for positivity of the two pmf' values
  have hAeq : muP2 n + x * sigmaP2 n = (n : ℝ) / 4 + x * Real.sqrt n / 4 := by
    simp only [muP2, sigmaP2]; ring
  have h64R : (64 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h64
  -- `⌊μ+xσ⌋ ≤ n/4 + K√n`, hence `2·⌊μ+xσ⌋+1 ≤ n`
  have hkxle : (((⌊muP2 n + x * sigmaP2 n⌋₊ : ℕ) : ℝ)) ≤ (n : ℝ) / 4 + K * Real.sqrt n := by
    by_cases hA0 : 0 ≤ muP2 n + x * sigmaP2 n
    · have h1 := Nat.floor_le hA0
      have hxle : x * Real.sqrt n / 4 ≤ K * Real.sqrt n := by
        have hxr : x ≤ 4 * (K - 1) := by
          rw [hKdef]; have := le_abs_self x; linarith
        nlinarith [mul_le_mul_of_nonneg_right hxr hr0.le, hr0]
      have hub : muP2 n + x * sigmaP2 n ≤ (n : ℝ) / 4 + K * Real.sqrt n := by
        rw [hAeq]; linarith [hxle]
      linarith [h1, hub]
    · rw [not_le] at hA0
      have hz : ((⌊muP2 n + x * sigmaP2 n⌋₊ : ℕ) : ℝ) = 0 := by
        rw [Nat.floor_eq_zero.mpr (by linarith)]; simp
      have : (0 : ℝ) ≤ K * Real.sqrt n := mul_nonneg (by linarith [hK]) hr0.le
      rw [hz]; linarith
  have hkxsupp : 2 * ⌊muP2 n + x * sigmaP2 n⌋₊ + 1 ≤ n := by
    have : ((2 * ⌊muP2 n + x * sigmaP2 n⌋₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      push_cast; nlinarith [hkxle, hKr_le, h64R]
    exact_mod_cast this
  have hk0supp : 2 * ⌊(n : ℝ) / 4⌋₊ + 1 ≤ n := by
    have : ((2 * ⌊(n : ℝ) / 4⌋₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      push_cast
      have := Nat.floor_le (show (0 : ℝ) ≤ (n : ℝ) / 4 by positivity)
      linarith
    exact_mod_cast this
  have hkxpos : 0 < pmf' n ⌊muP2 n + x * sigmaP2 n⌋₊ := pmf'_pos hkxsupp
  have hk0pos : 0 < pmf' n ⌊(n : ℝ) / 4⌋₊ := pmf'_pos hk0supp
  rw [Real.exp_sub, Real.exp_log hkxpos, Real.exp_log hk0pos]

/-! ### Deliverable 3: the pointwise local limit, given the prefactor -/

/-- **The pointwise local limit, given the prefactor limit.**  Assuming the
prefactor converges to the exact Gaussian normalisation
`hpre : σ(n)·pmf'(n, ⌊n/4⌋) → 1/√(2π)` (the self-normalisation constant, pinned
by `gaussian_sum_div_sqrt_tendsto`; only its *interval* `[1/100000, 2026]` is
proved in `LocalCLTMode`), the full pointwise local limit holds:

  `σ(n)·pmf'(n, ⌊μ+xσ⌋) → exp(−x²/2)/√(2π)`. -/
theorem pmf'_local_limit_of_mode
    (hpre : Tendsto (fun n : ℕ => sigmaP2 n * pmf' n ⌊(n : ℝ) / 4⌋₊) atTop
      (𝓝 (1 / Real.sqrt (2 * Real.pi))))
    (x : ℝ) :
    Tendsto (fun n : ℕ => sigmaP2 n * pmf' n ⌊muP2 n + x * sigmaP2 n⌋₊) atTop
      (𝓝 (Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi))) := by
  have hmul := hpre.mul (pmf'_ratio_tendsto x)
  have hval : 1 / Real.sqrt (2 * Real.pi) * Real.exp (-x ^ 2 / 2)
      = Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi) := by
    rw [div_mul_eq_mul_div, one_mul]
  rw [hval] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have h2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hk0pos : 0 < pmf' n ⌊(n : ℝ) / 4⌋₊ := by
    apply pmf'_pos
    have : ((2 * ⌊(n : ℝ) / 4⌋₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      push_cast
      have := Nat.floor_le (show (0 : ℝ) ≤ (n : ℝ) / 4 by positivity)
      linarith
    exact_mod_cast this
  field_simp [hk0pos.ne']

end MakinenAnalysis
