import MakinenAnalysis.TreeIdentities

/-!
# The paper's rational functions are the actual moments

`MakinenAnalysis.Asymptotics` introduces `EAM`, `EAN`, `VarS`, `VarP2`,
`CovSP2`, `VarAN` as **definitions** — the closed forms printed in
`paper_ja.tex` — and proves their asymptotics (Corollary 7, Theorem 9).  That
leaves a hole the Lean gates could not see: nothing inside the Lean development
said that those rational functions *are* the mean and the variance of anything.
The justification lived in the Rocq half.

This file closes it.  With the exact sums of `ExactMoments` the identification
is elementary: each statement below says that the defined rational function
equals the literal average, variance or covariance over the `C_n` codewords of
size `n`.

| here | states |
|---|---|
| `EAM_eq` | `EAM n` is the mean of `A_M = S + 2n - 1` |
| `EAN_eq` | `EAN n` is the mean of `A_N = S + P₂ + (n+2)` |
| `VarS_eq` | `VarS n` is the variance of `S` |
| `VarP2_eq` | `VarP2 n` is the variance of `P₂` |
| `CovSP2_eq` | `CovSP2 n` is the covariance of `S` and `P₂` |
| `VarAN_eq` | `VarAN n` is the variance of `A_N` |

Consequently `EAM_asymp`, `EAN_asymp`, `VarS_asymp`, `VarAN_asymp` and
`CovSP2_asymp` are now statements about the actual moments, inside Lean alone.
-/

namespace MakinenAnalysis

open Finset

/-- Expectation of a codeword statistic under the uniform Catalan model on the
    `C_n` codewords of size `n`. -/
noncomputable def Eof (n : ℕ) (f : List ℕ → ℕ) : ℝ :=
  ((∑ w ∈ suffixes (n - 1) 1, f w : ℕ) : ℝ) / (catalan n : ℝ)

/-- Variance of a codeword statistic. -/
noncomputable def Vof (n : ℕ) (f : List ℕ → ℕ) : ℝ :=
  Eof n (fun w => f w * f w) - (Eof n f) ^ 2

/-- Covariance of two codeword statistics. -/
noncomputable def Cof (n : ℕ) (f g : List ℕ → ℕ) : ℝ :=
  Eof n (fun w => f w * g w) - Eof n f * Eof n g

lemma cat_ne_zero (n : ℕ) : (catalan n : ℝ) ≠ 0 := Cat_ne_zero n

/-- `n = 1`: the single (empty) codeword, evaluated directly.  The closed forms
    below are proved for `n ≥ 2` from the cleared identities; this closes `n = 1`. -/
lemma Eof_one (f : List ℕ → ℕ) : Eof 1 f = (f [] : ℝ) := by
  simp [Eof, suffixes]

/-! ### Casting helpers -/

private lemma cast_sub_one (n : ℕ) (h : 1 ≤ n) : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
  rw [Nat.cast_sub h]; norm_num

private lemma cast_sub_two (n : ℕ) (h : 2 ≤ n) : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
  rw [Nat.cast_sub h]; norm_num

private lemma cast_two_sub_one (n : ℕ) : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 ∨ n = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · exact Or.inr rfl
  · exact Or.inl (by rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]; push_cast; ring)

/-! ### Corollary 7: the defined means are the actual means -/

/-- **`EAM` is the mean of `A_M`.** -/
theorem EAM_eq (n : ℕ) (hn : 1 ≤ n) :
    EAM n = Eof n (fun w => w.sum + (2 * n - 1)) := by
  have hC := cat_ne_zero n
  have hn2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  have c1 := cast_sub_one n hn
  have c2 : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]; push_cast; ring
  have key := EAM_rational n hn
  simp only [Eof]
  set A : ℕ := ∑ w ∈ suffixes (n - 1) 1, (w.sum + (2 * n - 1)) with hA
  have hR : ((n : ℝ) + 2) * (A : ℝ)
      = ((n : ℝ) * ((n : ℝ) - 1) + (2 * (n : ℝ) - 1) * ((n : ℝ) + 2))
        * (catalan n : ℝ) := by
    have h := congrArg (fun x : ℕ => (x : ℝ)) key
    push_cast [c1, c2] at h
    linarith [h]
  rw [eq_div_iff hC]
  refine mul_left_cancel₀ hn2 ?_
  calc ((n : ℝ) + 2) * (EAM n * (catalan n : ℝ))
      = ((n : ℝ) * ((n : ℝ) - 1) + (2 * (n : ℝ) - 1) * ((n : ℝ) + 2))
          * (catalan n : ℝ) := by rw [EAM]; field_simp; ring
    _ = ((n : ℝ) + 2) * (A : ℝ) := hR.symm

/-- **`EAN` is the mean of `A_N`.** -/
theorem EAN_eq (n : ℕ) (hn : 1 ≤ n) :
    EAN n = Eof n (fun w => w.sum + P2 w + (n + 2)) := by
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn
  · rw [Eof_one]; norm_num [EAN, P2]
  have hC := cat_ne_zero n
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  have hn1 : (2 * (n : ℝ) - 1) ≠ 0 := by nlinarith
  have c1 := cast_sub_one n (by omega)
  have c2 := cast_sub_two n (by omega)
  have c3 : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]; push_cast; ring
  have key := EAN_rational n (by omega)
  simp only [Eof]
  set A : ℕ := ∑ w ∈ suffixes (n - 1) 1, (w.sum + P2 w + (n + 2)) with hA
  have hR : 2 * ((n : ℝ) + 2) * (2 * (n : ℝ) - 1) * (A : ℝ)
      = (2 * (2 * (n : ℝ) - 1) * (n : ℝ) * ((n : ℝ) - 1)
          + 2 * ((n : ℝ) + 2) * ((n : ℝ) + 2) * (2 * (n : ℝ) - 1)
          + ((n : ℝ) + 2) * ((n : ℝ) - 1) * ((n : ℝ) - 2)) * (catalan n : ℝ) := by
    have h := congrArg (fun x : ℕ => (x : ℝ)) key
    push_cast [c1, c2, c3] at h
    linarith [h]
  rw [eq_div_iff hC]
  refine mul_left_cancel₀
    (show 2 * ((n : ℝ) + 2) * (2 * (n : ℝ) - 1) ≠ 0 from
      mul_ne_zero (mul_ne_zero two_ne_zero hn2) hn1) ?_
  calc 2 * ((n : ℝ) + 2) * (2 * (n : ℝ) - 1) * (EAN n * (catalan n : ℝ))
      = (2 * (2 * (n : ℝ) - 1) * (n : ℝ) * ((n : ℝ) - 1)
          + 2 * ((n : ℝ) + 2) * ((n : ℝ) + 2) * (2 * (n : ℝ) - 1)
          + ((n : ℝ) + 2) * ((n : ℝ) - 1) * ((n : ℝ) - 2)) * (catalan n : ℝ) := by
        rw [EAN]; field_simp
    _ = 2 * ((n : ℝ) + 2) * (2 * (n : ℝ) - 1) * (A : ℝ) := hR.symm

/-! ### Proposition 8: the defined second moments are the actual ones -/

/-- **`VarP2` is the variance of `P₂`.** -/
theorem VarP2_eq (n : ℕ) (hn : 1 ≤ n) : VarP2 n = Vof n P2 := by
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn
  · simp only [Vof, Eof_one]; norm_num [VarP2, P2]
  have hC := cat_ne_zero n
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (2 * (n : ℝ) - 1) ≠ 0 := by nlinarith
  have h3 : (2 * (n : ℝ) - 3) ≠ 0 := by nlinarith
  have h1' : ((n : ℝ) * 2 - 1) ≠ 0 := by nlinarith
  have h3' : ((n : ℝ) * 2 - 3) ≠ 0 := by nlinarith
  have c1 := cast_sub_one n (by omega)
  have c2 := cast_sub_two n hn
  have c3 : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]; push_cast; ring
  have c4 : ((2 * n - 3 : ℕ) : ℝ) = 2 * (n : ℝ) - 3 := by
    rw [Nat.cast_sub (by omega : 3 ≤ 2 * n)]; push_cast; ring
  have key := VarP2_rational n (by omega)
  simp only [Vof, Eof]
  set Q : ℕ := ∑ w ∈ suffixes (n - 1) 1, P2 w * P2 w with hQ
  set B : ℕ := ∑ w ∈ suffixes (n - 1) 1, P2 w with hB
  have hR : 2 * (2 * (n : ℝ) - 1) * (2 * (n : ℝ) - 1) * (2 * (n : ℝ) - 3)
        * ((catalan n : ℝ) * (Q : ℝ))
      = (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) - 1) * ((n : ℝ) - 2)
          * ((catalan n : ℝ) * (catalan n : ℝ))
        + 2 * (2 * (n : ℝ) - 1) * (2 * (n : ℝ) - 1) * (2 * (n : ℝ) - 3)
          * ((B : ℝ) * (B : ℝ)) := by
    have h := congrArg (fun x : ℕ => (x : ℝ)) key
    push_cast [c1, c2, c3, c4] at h
    linarith [h]
  rw [VarP2]
  field_simp
  linarith [hR]

/-- **`CovSP2` is the covariance of `S` and `P₂`.** -/
theorem CovSP2_eq (n : ℕ) (hn : 1 ≤ n) :
    CovSP2 n = Cof n (fun w => w.sum) P2 := by
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn
  · simp only [Cof, Eof_one]; norm_num [CovSP2, P2]
  have hC := cat_ne_zero n
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  have h1 : (2 * (n : ℝ) - 1) ≠ 0 := by nlinarith
  have h1' : ((n : ℝ) * 2 - 1) ≠ 0 := by nlinarith
  have c1 := cast_sub_one n (by omega)
  have c2 := cast_sub_two n (by omega)
  have c3 : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]; push_cast; ring
  have key := CovSP2_rational n (by omega)
  simp only [Cof, Eof]
  set X : ℕ := ∑ w ∈ suffixes (n - 1) 1, w.sum * P2 w with hX
  set A : ℕ := ∑ w ∈ suffixes (n - 1) 1, w.sum with hA
  set B : ℕ := ∑ w ∈ suffixes (n - 1) 1, P2 w with hB
  have hR : ((n : ℝ) + 2) * (2 * (n : ℝ) - 1) * ((catalan n : ℝ) * (X : ℝ))
      = 2 * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((catalan n : ℝ) * (catalan n : ℝ))
        + ((n : ℝ) + 2) * (2 * (n : ℝ) - 1) * ((A : ℝ) * (B : ℝ)) := by
    have h := congrArg (fun x : ℕ => (x : ℝ)) key
    push_cast [c1, c2, c3] at h
    linarith [h]
  rw [CovSP2]
  field_simp
  linarith [hR]

/-- **`VarS` is the variance of `S`.** -/
theorem VarS_eq (n : ℕ) (hn : 1 ≤ n) : VarS n = Vof n (fun w => w.sum) := by
  have hC := cat_ne_zero n
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  have hn3 : ((n : ℝ) + 3) ≠ 0 := by positivity
  have c1 := cast_sub_one n hn
  have k1 := congrArg (fun x : ℕ => (x : ℝ)) (sum_pops_sq n hn)
  have k2 := congrArg (fun x : ℕ => (x : ℝ)) (ES_rational n hn)
  have k3 := congrArg (fun x : ℕ => (x : ℝ)) (catalan_ratio n)
  have k4 := congrArg (fun x : ℕ => (x : ℝ)) (catalan_ratio (n + 1))
  have hsq : (∑ w ∈ suffixes (n - 1) 1, w.sum * w.sum)
      = ∑ w ∈ suffixes (n - 1) 1, w.sum ^ 2 :=
    Finset.sum_congr rfl fun w _ => by ring
  simp only [Vof, Eof]
  rw [hsq]
  set Q : ℕ := ∑ w ∈ suffixes (n - 1) 1, w.sum ^ 2 with hQ
  set A : ℕ := ∑ w ∈ suffixes (n - 1) 1, w.sum with hA
  push_cast [c1] at k1 k2 k3 k4
  -- eliminate `catalan (n+2)` and `catalan (n+1)` in favour of `catalan n`
  have hE : ((n : ℝ) + 2) * ((n : ℝ) + 3) * (catalan (n + 2) : ℝ)
      = 4 * (2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 1) * (catalan n : ℝ) := by
    calc ((n : ℝ) + 2) * ((n : ℝ) + 3) * (catalan (n + 2) : ℝ)
        = ((n : ℝ) + 2) * (((n : ℝ) + 1 + 2) * (catalan (n + 1 + 1) : ℝ)) := by
          ring
      _ = ((n : ℝ) + 2) * (2 * (2 * ((n : ℝ) + 1) + 1) * (catalan (n + 1) : ℝ)) := by
          rw [k4]
      _ = 2 * (2 * ((n : ℝ) + 1) + 1) * (((n : ℝ) + 2) * (catalan (n + 1) : ℝ)) := by ring
      _ = 2 * (2 * ((n : ℝ) + 1) + 1) * (2 * (2 * (n : ℝ) + 1) * (catalan n : ℝ)) := by
          rw [k3]
      _ = 4 * (2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 1) * (catalan n : ℝ) := by ring
  -- the second moment, cleared of `catalan (n+1)` and `catalan (n+2)`
  have hQ2 : ((n : ℝ) + 2) * ((n : ℝ) + 3) * (Q : ℝ)
      = (((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) * ((n : ℝ) + 3)
          + 8 * (2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 1)
          - 2 * (2 * (n : ℝ) + 5) * ((n : ℝ) + 3) * (2 * (n : ℝ) + 1)) * (catalan n : ℝ) := by
    have e : ((n : ℝ) + 2) * ((n : ℝ) + 3)
        * ((Q : ℝ) + (2 * (n : ℝ) + 5) * (catalan (n + 1) : ℝ))
        = ((n : ℝ) + 2) * ((n : ℝ) + 3)
          * (((n : ℝ) + 1) ^ 2 * (catalan n : ℝ) + 2 * (catalan (n + 2) : ℝ)) := by
      rw [k1]
    nlinarith [e, hE, k3]
  have k2sq : ((n : ℝ) + 2) ^ 2 * (A : ℝ) ^ 2
      = ((n : ℝ) * ((n : ℝ) - 1)) ^ 2 * (catalan n : ℝ) ^ 2 := by
    have h : (((n : ℝ) + 2) * (A : ℝ)) ^ 2
        = ((n : ℝ) * ((n : ℝ) - 1) * (catalan n : ℝ)) ^ 2 := by rw [k2]
    linarith [h]
  -- multiply the two cleared facts up to the shape the goal needs
  have hQ3 : ((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 3) * ((Q : ℝ) * (catalan n : ℝ))
      = ((n : ℝ) + 2) * (((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) * ((n : ℝ) + 3)
            + 8 * (2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 1)
            - 2 * (2 * (n : ℝ) + 5) * ((n : ℝ) + 3) * (2 * (n : ℝ) + 1)) * (catalan n : ℝ) ^ 2 := by
    calc ((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 3) * ((Q : ℝ) * (catalan n : ℝ))
        = ((n : ℝ) + 2) * (catalan n : ℝ)
            * (((n : ℝ) + 2) * ((n : ℝ) + 3) * (Q : ℝ)) := by ring
      _ = ((n : ℝ) + 2) * (catalan n : ℝ) * ((((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) * ((n : ℝ) + 3)
            + 8 * (2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 1)
            - 2 * (2 * (n : ℝ) + 5) * ((n : ℝ) + 3) * (2 * (n : ℝ) + 1)) * (catalan n : ℝ)) := by rw [hQ2]
      _ = ((n : ℝ) + 2) * (((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) * ((n : ℝ) + 3)
            + 8 * (2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 1)
            - 2 * (2 * (n : ℝ) + 5) * ((n : ℝ) + 3) * (2 * (n : ℝ) + 1)) * (catalan n : ℝ) ^ 2 := by ring
  have hA3 : ((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 3) * (A : ℝ) ^ 2
      = ((n : ℝ) + 3) * ((n : ℝ) * ((n : ℝ) - 1)) ^ 2 * (catalan n : ℝ) ^ 2 := by
    calc ((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 3) * (A : ℝ) ^ 2
        = ((n : ℝ) + 3) * (((n : ℝ) + 2) ^ 2 * (A : ℝ) ^ 2) := by ring
      _ = ((n : ℝ) + 3) * (((n : ℝ) * ((n : ℝ) - 1)) ^ 2 * (catalan n : ℝ) ^ 2) := by
            rw [k2sq]
      _ = ((n : ℝ) + 3) * ((n : ℝ) * ((n : ℝ) - 1)) ^ 2 * (catalan n : ℝ) ^ 2 := by ring
  rw [VarS]
  field_simp
  linarith [hQ3, hA3]

/-- **`VarAN` is the variance of `A_N`** (`A_N` differs from `S + P₂` by a constant). -/
theorem VarAN_eq (n : ℕ) (hn : 1 ≤ n) :
    VarAN n = Vof n (fun w => w.sum) + Vof n P2 + 2 * Cof n (fun w => w.sum) P2 := by
  rw [VarAN, VarS_eq n (by omega), VarP2_eq n (by omega), CovSP2_eq n hn]

end MakinenAnalysis
