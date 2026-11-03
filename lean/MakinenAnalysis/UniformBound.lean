/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.

# The uniform bound `P(h = m) ≤ m 2^{-m}`

`paper_ja.tex`, Theorem `thm:Mlimit`, uses the uniform estimate
`P(h = m) ≤ m·2^{-m}` (`n ≥ 2`) to pass to the limit of the moments of `h` by
dominated convergence.  The limits themselves were verified in Lean another way
(the variance expansions in `Expansions`); this file proves the estimate itself.

Proof: `P(h = 1) = (n+1)/(2(2n-1)) ≤ 1/2`, and one step of the ballot ladder
multiplies by `(k+2)(n-k-1)/((k+1)(2n-k-2)) ≤ (k+2)/(2(k+1))`.  Beyond `m = n`
the probability is `0`.  The two ladder facts are restated here (with the range
widened to `n ≥ k + 2`) because the versions in `Asymptotics` are private.
-/
import MakinenAnalysis.Asymptotics

namespace MakinenAnalysis

open Filter

noncomputable section

/-- `P(h = 1) = (n+1)/(2(2n-1))` for `n ≥ 1`. -/
lemma hProb_one_closed {n : ℕ} (hn : 1 ≤ n) :
    hProb n 1 = ((n : ℝ) + 1) / (2 * (2 * (n : ℝ) - 1)) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have e1 : 2 * (j + 1) - 1 - 1 = 2 * j := by omega
  have e2 : j + 1 - 1 = j := by omega
  have hcat : ((j : ℝ) + 2) * Cat (j + 1) = (Nat.centralBinom (j + 1) : ℝ) := by
    simp only [Cat]
    exact_mod_cast succ_mul_catalan_eq_centralBinom (j + 1)
  have hcb : ((j : ℝ) + 1) * (Nat.centralBinom (j + 1) : ℝ)
      = 2 * (2 * (j : ℝ) + 1) * (Nat.centralBinom j : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ j
  simp only [hProb, ballot, e1, e2, ← Nat.centralBinom_eq_two_mul_choose]
  push_cast
  have hd : (0 : ℝ) < 2 * (2 * ((j : ℝ) + 1) - 1) := by
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    nlinarith
  rw [div_eq_div_iff (Cat_ne_zero (j + 1)) hd.ne']
  field_simp
  linear_combination -hcb - ((j : ℝ) + 1) * hcat

/-- One rung of the ballot ladder, for `n ≥ k + 2`:
    `P(h = k+2) = P(h = k+1) · (k+2)(n-k-1) / ((k+1)(2n-k-2))`. -/
lemma hProb_rung {k n : ℕ} (hn : k + 2 ≤ n) :
    hProb n (k + 2) = hProb n (k + 1) *
      (((k : ℝ) + 2) * ((n : ℝ) - (k : ℝ) - 1) /
        (((k : ℝ) + 1) * (2 * (n : ℝ) - (k : ℝ) - 2))) := by
  have hch := Nat.choose_mul_succ_eq (2 * n - k - 3) (n - 1)
  have e1 : 2 * n - k - 3 + 1 = 2 * n - k - 2 := by omega
  rw [e1] at hch
  have e2 : 2 * n - k - 2 - (n - 1) = n - k - 1 := by omega
  rw [e2] at hch
  have c1 : ((2 * n - k - 2 : ℕ) : ℝ) = 2 * (n : ℝ) - (k : ℝ) - 2 := by
    have h2 : k + 2 ≤ 2 * n := by omega
    rw [show 2 * n - k - 2 = 2 * n - (k + 2) by omega, Nat.cast_sub h2]
    push_cast; ring
  have c2 : ((n - k - 1 : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) - 1 := by
    have h2 : k + 1 ≤ n := by omega
    rw [show n - k - 1 = n - (k + 1) by omega, Nat.cast_sub h2]
    push_cast; ring
  have hchR : ((2 * n - k - 3).choose (n - 1) : ℝ) * (2 * (n : ℝ) - (k : ℝ) - 2)
      = ((2 * n - k - 2).choose (n - 1) : ℝ) * ((n : ℝ) - (k : ℝ) - 1) := by
    rw [← c1, ← c2]
    exact_mod_cast hch
  have hCatne : Cat n ≠ 0 := Cat_ne_zero n
  have hnk : (k : ℝ) + 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hden : (0 : ℝ) < 2 * (n : ℝ) - (k : ℝ) - 2 := by linarith
  have i1 : 2 * n - (k + 2) - 1 = 2 * n - k - 3 := by omega
  have i2 : 2 * n - (k + 1) - 1 = 2 * n - k - 2 := by omega
  simp only [hProb, ballot, i1, i2]
  push_cast
  field_simp
  linear_combination hchR

lemma hProb_nonneg (n m : ℕ) : 0 ≤ hProb n m := by
  unfold hProb ballot Cat
  positivity

/-- Beyond `m = n` no tree has final height `m` (for `n ≥ 2`; at `n = 1` the
    truncated subtraction in `ballot` makes the formula nonzero). -/
lemma hProb_eq_zero_of_lt {n m : ℕ} (hn : 2 ≤ n) (h : n < m) : hProb n m = 0 := by
  have hlt : 2 * n - m - 1 < n - 1 := by omega
  have hc : (2 * n - m - 1).choose (n - 1) = 0 := Nat.choose_eq_zero_of_lt hlt
  simp [hProb, ballot, hc]

/-- The ladder bound for `1 ≤ m ≤ n`. -/
lemma hProb_le_ladder {n : ℕ} (hn : 2 ≤ n) :
    ∀ k, k + 1 ≤ n → hProb n (k + 1) ≤ ((k : ℝ) + 1) * (1 / 2 : ℝ) ^ (k + 1) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  intro k
  induction k with
  | zero =>
    intro _
    rw [hProb_one_closed (by omega)]
    have hd : (0 : ℝ) < 2 * (2 * (n : ℝ) - 1) := by linarith
    rw [div_le_iff₀ hd]
    push_cast
    nlinarith
  | succ k ih =>
    intro hk
    have hrung := hProb_rung (k := k) (n := n) (by omega)
    rw [show k + 1 + 1 = k + 2 by omega, hrung]
    have hIH := ih (by omega)
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hnk : (k : ℝ) + 2 ≤ (n : ℝ) := by exact_mod_cast (show k + 2 ≤ n by omega)
    have hden : (0 : ℝ) < ((k : ℝ) + 1) * (2 * (n : ℝ) - (k : ℝ) - 2) := by
      have : (0 : ℝ) < 2 * (n : ℝ) - (k : ℝ) - 2 := by linarith
      positivity
    -- the rung ratio is at most (k+2)/(2(k+1))
    have hratio : ((k : ℝ) + 2) * ((n : ℝ) - (k : ℝ) - 1) /
        (((k : ℝ) + 1) * (2 * (n : ℝ) - (k : ℝ) - 2)) ≤ ((k : ℝ) + 2) / (2 * ((k : ℝ) + 1)) := by
      rw [div_le_div_iff₀ hden (by positivity)]
      have e : ((k : ℝ) + 2) * (((k : ℝ) + 1) * (2 * (n : ℝ) - (k : ℝ) - 2))
          - ((k : ℝ) + 2) * ((n : ℝ) - (k : ℝ) - 1) * (2 * ((k : ℝ) + 1))
          = ((k : ℝ) + 2) * ((k : ℝ) + 1) * (k : ℝ) := by ring
      have : (0 : ℝ) ≤ ((k : ℝ) + 2) * ((k : ℝ) + 1) * (k : ℝ) := by positivity
      linarith
    have hr0 : 0 ≤ ((k : ℝ) + 2) * ((n : ℝ) - (k : ℝ) - 1) /
        (((k : ℝ) + 1) * (2 * (n : ℝ) - (k : ℝ) - 2)) := by
      apply div_nonneg _ hden.le
      have : (0 : ℝ) ≤ (n : ℝ) - (k : ℝ) - 1 := by linarith
      positivity
    calc hProb n (k + 1) * (((k : ℝ) + 2) * ((n : ℝ) - (k : ℝ) - 1) /
          (((k : ℝ) + 1) * (2 * (n : ℝ) - (k : ℝ) - 2)))
        ≤ (((k : ℝ) + 1) * (1 / 2 : ℝ) ^ (k + 1)) * (((k : ℝ) + 2) / (2 * ((k : ℝ) + 1))) :=
          mul_le_mul hIH hratio hr0 (by positivity)
      _ = (((k + 1 : ℕ) : ℝ) + 1) * (1 / 2 : ℝ) ^ (k + 1 + 1) := by
          have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
          push_cast
          field_simp
          ring

/-- **The uniform bound (`thm:Mlimit`).**  For `n ≥ 2` and every `m`,
    `P(h = m) ≤ m · 2^{-m}`. -/
theorem hProb_le_uniform (n m : ℕ) (hn : 2 ≤ n) : hProb n m ≤ (m : ℝ) * (1 / 2 : ℝ) ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [hProb, ballot]
  rcases Nat.lt_or_ge n m with hnm | hmn
  · rw [hProb_eq_zero_of_lt (by omega) hnm]; positivity
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have := hProb_le_ladder hn k hmn
    push_cast
    exact this

end

end MakinenAnalysis
