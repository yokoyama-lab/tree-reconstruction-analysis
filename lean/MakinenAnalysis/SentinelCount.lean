/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.

# The number of sentinel comparisons, and M's informative comparisons on average

`Q = #{i : x_i = h_{i-1}}` counts the steps that pop the whole stack, i.e. the
comparisons of M with the sentinel (`OnePass.qcount`).  Under the uniform model

* `sum_qcount_add_catalan`: `Σ_w Q + C_n = Σ_w h`, so `E[Q] = E[h] - 1`;
* `sum_qcount_rational`: `(n+2)·Σ_w Q = 2(n-1)·C_n`, i.e. `E[Q] = 2(n-1)/(n+2)`;
* `sum_costM_rational`: M's informative comparisons (label comparisons other
  than with the sentinel, `OnePass.cost OnePass.algM`) average `2n(n-1)/(n+2)`.

The key identity (`qsum_succ`): summing `Q` over the words of length `ℓ+1` read
from height `h` gives the number of words of length `ℓ` read from height `h+2`.
It follows from the first-letter recursion.  (On paper, `Q` equals the rightmost
path length of the tree; this file does not need that.)
-/
import MakinenAnalysis.ExactMoments
import MakinenAnalysis.OnePass

namespace MakinenAnalysis

open Finset

/-- Total of `Q` over the valid words of length `ℓ` read from height `h`. -/
def Qsum (ℓ h : ℕ) : ℕ := ∑ w ∈ suffixes ℓ h, OnePass.qcount h w

/-- In the first-letter split, only the letter `x = h` empties the stack. -/
lemma sum_range_ite_eq_top (h : ℕ) (f : ℕ → ℕ) :
    (∑ x ∈ range (h + 1), if x = h then f x else 0) = f h := by
  rw [Finset.sum_ite_eq' (range (h + 1)) h f]
  simp

/-- **The key identity.**  `Σ_{|w| = ℓ+1, from h} Q(w) = #{words of length ℓ from h+2}`. -/
theorem qsum_succ : ∀ (ℓ h : ℕ), Qsum (ℓ + 1) h = (suffixes ℓ (h + 2)).card := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro h
    unfold Qsum
    rw [sum_suffixes_succ]
    simp only [suffixes, Finset.sum_singleton, OnePass.qcount, Nat.add_zero, Finset.card_singleton]
    exact sum_range_ite_eq_top h (fun _ => 1)
  | succ ℓ ih =>
    intro h
    -- split the outer sum along the first letter
    have hsplit : Qsum (ℓ + 2) h
        = (suffixes (ℓ + 1) 1).card + ∑ x ∈ range (h + 1), Qsum (ℓ + 1) (h + 1 - x) := by
      unfold Qsum
      rw [sum_suffixes_succ]
      have e : ∀ x ∈ range (h + 1),
          (∑ w ∈ suffixes (ℓ + 1) (h + 1 - x), OnePass.qcount h (x :: w))
            = (if x = h then (suffixes (ℓ + 1) (h + 1 - x)).card else 0)
              + ∑ w ∈ suffixes (ℓ + 1) (h + 1 - x), OnePass.qcount (h + 1 - x) w := by
        intro x _
        simp only [OnePass.qcount]
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
        split <;> simp
      rw [Finset.sum_congr rfl e, Finset.sum_add_distrib,
        sum_range_ite_eq_top h (fun x => (suffixes (ℓ + 1) (h + 1 - x)).card)]
      simp
    rw [hsplit, Finset.sum_congr rfl (fun x _ => ih (h + 1 - x))]
    -- both sides are sums of `c(ℓ, j)`
    have hA : (suffixes (ℓ + 1) (h + 2)).card
        = (∑ x ∈ range (h + 1), (suffixes ℓ (h + 2 + 1 - x)).card)
          + (suffixes ℓ 2).card + (suffixes ℓ 1).card := by
      rw [card_suffixes_succ ℓ (h + 2), show h + 2 + 1 = (h + 1) + 1 + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ,
        show h + 1 + 1 + 1 - (h + 1) = 2 by omega, show h + 1 + 1 + 1 - (h + 1 + 1) = 1 by omega]
    have hB : (suffixes (ℓ + 1) 1).card = (suffixes ℓ 2).card + (suffixes ℓ 1).card := by
      rw [card_suffixes_succ ℓ 1]
      simp [Finset.sum_range_succ]
    have hC : (∑ x ∈ range (h + 1), (suffixes ℓ (h + 1 - x + 2)).card)
        = ∑ x ∈ range (h + 1), (suffixes ℓ (h + 2 + 1 - x)).card := by
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [Finset.mem_range] at hx
      rw [show h + 1 - x + 2 = h + 2 + 1 - x by omega]
    rw [hA, hB, hC]
    ring

/-- **`Σ Q + C_n = Σ h`** over the codewords of size `n`, so `E[Q] = E[h] - 1`. -/
theorem sum_qcount_add_catalan (n : ℕ) (hn : 1 ≤ n) :
    (∑ w ∈ suffixes (n - 1) 1, OnePass.qcount 1 w) + catalan n
      = ∑ w ∈ suffixes (n - 1) 1, finalH 1 w := by
  rcases Nat.eq_or_lt_of_le hn with rfl | hn2
  · simp [suffixes, OnePass.qcount, finalH]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hQ : (∑ w ∈ suffixes (m + 2 - 1) 1, OnePass.qcount 1 w) = (suffixes m 3).card := by
    rw [show m + 2 - 1 = m + 1 by omega]
    exact qsum_succ m 1
  have hH := Hsum_add_card (m + 1) 1
  have hc := card_suffixes_eq_catalan (m + 2) (by omega)
  rw [show m + 2 - 1 = m + 1 by omega] at hc
  have c2 := card_suffixes_succ (m + 1) 1
  have c1 := card_suffixes_succ m 2
  have c0 := card_suffixes_succ m 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add,
    show 1 + 1 - 0 = 2 by rfl, show 1 + 1 - 1 = 1 by rfl,
    show 2 + 1 - 0 = 3 by rfl] at c2 c1 c0
  unfold Hsum at hH
  rw [hQ, ← hc, show m + 2 - 1 = m + 1 by omega]
  omega

/-- **`E[Q] = 2(n-1)/(n+2)`**, cleared: `(n+2)·Σ Q = 2(n-1)·C_n`. -/
theorem sum_qcount_rational (n : ℕ) (hn : 1 ≤ n) :
    (n + 2) * (∑ w ∈ suffixes (n - 1) 1, OnePass.qcount 1 w) = 2 * (n - 1) * catalan n := by
  have h1 := sum_qcount_add_catalan n hn
  have h2 := sum_finalH_add_catalan n hn
  have h3 := catalan_ratio n
  -- Σ Q = C_{n+1} - 2 C_n and (n+2) C_{n+1} = 2(2n+1) C_n
  have hq : (∑ w ∈ suffixes (n - 1) 1, OnePass.qcount 1 w) + 2 * catalan n = catalan (n + 1) := by
    omega
  have : (n + 2) * (∑ w ∈ suffixes (n - 1) 1, OnePass.qcount 1 w) + (n + 2) * (2 * catalan n)
      = 2 * (2 * n + 1) * catalan n := by
    rw [← Nat.mul_add, hq, h3]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  nlinarith [this]

/-- **M's informative comparisons on average: `2n(n-1)/(n+2)`**, cleared:
    `(n+2)·Σ_w cost_M(w) = 2n(n-1)·C_n`. -/
theorem sum_costM_rational (n : ℕ) (hn : 1 ≤ n) :
    (n + 2) * (∑ w ∈ suffixes (n - 1) 1, OnePass.cost OnePass.algM [] 1 w)
      = 2 * n * (n - 1) * catalan n := by
  -- per word: cost + Q = (n-1) + S
  have hper : ∀ w ∈ suffixes (n - 1) 1,
      OnePass.cost OnePass.algM [] 1 w + OnePass.qcount 1 w = (n - 1) + w.sum := by
    intro w hw
    obtain ⟨hlen, hv⟩ := (mem_suffixes _ _ _).1 hw
    rw [OnePass.costM_eq w hv, hlen]
  have hsum : (∑ w ∈ suffixes (n - 1) 1, OnePass.cost OnePass.algM [] 1 w)
      + (∑ w ∈ suffixes (n - 1) 1, OnePass.qcount 1 w)
      = (n - 1) * catalan n + ∑ w ∈ suffixes (n - 1) 1, w.sum := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hper, Finset.sum_add_distrib,
      Finset.sum_const, smul_eq_mul, card_suffixes_eq_catalan n hn, Nat.mul_comm]
  have hS := sum_pops n hn
  have hQ := sum_qcount_rational n hn
  have h3 := catalan_ratio n
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  nlinarith [hsum, hS, hQ, h3]

end MakinenAnalysis
