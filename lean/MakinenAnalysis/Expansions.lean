import MakinenAnalysis.Asymptotics
import MakinenAnalysis.LeafCount

/-!
# Asymptotic expansions with explicit remainders

The paper states the `1/n` expansions of the means and variances
(`cor:avg`, Table 1, `thm:vardich`):

* `E[A_N] = (9/4)n - 13/8 + O(1/n)`,  `E[A_M] = 3n - 4 + O(1/n)`,
  `E[P₂] = n/4 - 5/8 + O(1/n)`;
* `Var[S] = 4 - 30/n + O(n⁻²)`,  `Var[A_N] = n/16 + 193/32 + O(1/n)`.

`Asymptotics.lean` proves only the leading-term limits.  Here the correction
terms and the order of the remainder are proved as well, with **explicit
constants valid for every `n ≥ 1`** (not merely eventually).  The closed forms
`EAN`, `EAM`, `EP2`, `VarS`, `VarAN` are the ones `MomentBridge`/`ExecBridge`
identify with the actual moments.  Each remainder is computed exactly as a
rational function and then bounded; the constants are close to the true
`limsup` (`99/16`, `6`, `3/16`, `144`, `1251/32`).
-/

namespace MakinenAnalysis

open Filter Asymptotics

/-- `E[A_N] = (9/4)n - 13/8 + R`, `|R| ≤ 7/n`
    (exactly `R = 3(33n-14)/(8(n+2)(2n-1))`). -/
theorem EAN_expansion (n : ℕ) (hn : 1 ≤ n) :
    |EAN n - (9 / 4 * (n : ℝ) - 13 / 8)| ≤ 7 / (n : ℝ) := by
  have x1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hR : EAN n - (9 / 4 * (n : ℝ) - 13 / 8)
      = 3 * (33 * (n : ℝ) - 14) / (8 * ((n : ℝ) + 2) * (2 * (n : ℝ) - 1)) := by
    have h1 : (n : ℝ) + 2 ≠ 0 := by positivity
    have h2 : 2 * (n : ℝ) - 1 ≠ 0 := by linarith
    have h2' : (n : ℝ) * 2 - 1 ≠ 0 := by linarith
    simp only [EAN]; field_simp; ring
  have hpos : 0 < 8 * ((n : ℝ) + 2) * (2 * (n : ℝ) - 1) := by nlinarith
  rw [hR, abs_of_nonneg (div_nonneg (by nlinarith) hpos.le),
    div_le_div_iff₀ hpos (by linarith)]
  nlinarith

/-- `E[A_M] = 3n - 4 + R`, `R = 6/(n+2)`, so `0 < R ≤ 6/n`. -/
theorem EAM_expansion (n : ℕ) (hn : 1 ≤ n) :
    |EAM n - (3 * (n : ℝ) - 4)| ≤ 6 / (n : ℝ) := by
  have x1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hR : EAM n - (3 * (n : ℝ) - 4) = 6 / ((n : ℝ) + 2) := by
    have h1 : (n : ℝ) + 2 ≠ 0 := by positivity
    simp only [EAM]; field_simp; ring
  rw [hR, abs_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

/-- `E[P₂] = n/4 - 5/8 + R`, `R = 3/(8(2n-1))`, so `0 < R ≤ 3/(8n)`. -/
theorem EP2_expansion (n : ℕ) (hn : 1 ≤ n) :
    |EP2 n - ((n : ℝ) / 4 - 5 / 8)| ≤ 3 / (8 * (n : ℝ)) := by
  have x1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hR : EP2 n - ((n : ℝ) / 4 - 5 / 8) = 3 / (8 * (2 * (n : ℝ) - 1)) := by
    have h2 : 2 * (n : ℝ) - 1 ≠ 0 := by linarith
    have h2' : (n : ℝ) * 2 - 1 ≠ 0 := by linarith
    simp only [EP2]; field_simp; ring
  have hpos : 0 < 8 * (2 * (n : ℝ) - 1) := by linarith
  rw [hR, abs_of_nonneg (div_nonneg (by norm_num) hpos.le)]
  exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

/-- `Var[S] = 4 - 30/n + R`, `|R| ≤ 144/n²`
    (exactly `R = 72(2n²+6n+5)/(n(n+2)²(n+3))`). -/
theorem VarS_expansion (n : ℕ) (hn : 1 ≤ n) :
    |VarS n - (4 - 30 / (n : ℝ))| ≤ 144 / (n : ℝ) ^ 2 := by
  have x1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : (0 : ℝ) < n := by linarith
  have hR : VarS n - (4 - 30 / (n : ℝ))
      = 72 * (2 * (n : ℝ) ^ 2 + 6 * n + 5)
          / ((n : ℝ) * ((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 3)) := by
    have h1 : (n : ℝ) + 2 ≠ 0 := by positivity
    have h3 : (n : ℝ) + 3 ≠ 0 := by positivity
    simp only [VarS]; field_simp; ring
  have hpos : 0 < (n : ℝ) * ((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 3) := by positivity
  rw [hR, abs_of_nonneg (div_nonneg (by positivity) hpos.le),
    div_le_div_iff₀ hpos (by positivity)]
  nlinarith [sq_nonneg (n : ℝ), mul_pos hx hx, mul_pos (mul_pos hx hx) hx]

/-- `Var[A_N] = n/16 + 193/32 + R`, `|R| ≤ 40/n`
    (exactly `R = -3(3336n⁵+1072n⁴-9465n³-6055n²+12624n-3852)
    / (32(n+2)²(n+3)(2n-3)(2n-1)²)`, whose `n·|R|` tends to `1251/32 < 40`). -/
theorem VarAN_expansion (n : ℕ) (hn : 1 ≤ n) :
    |VarAN n - ((n : ℝ) / 16 + 193 / 32)| ≤ 40 / (n : ℝ) := by
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
  · norm_num [VarAN, VarS, VarP2, CovSP2, abs_le]
  have x2 : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  set x : ℝ := (n : ℝ) with hxdef
  have hR : VarAN n - (x / 16 + 193 / 32)
      = -(3 * (3336 * x ^ 5 + 1072 * x ^ 4 - 9465 * x ^ 3 - 6055 * x ^ 2
            + 12624 * x - 3852))
          / (32 * (x + 2) ^ 2 * (x + 3) * (2 * x - 3) * (2 * x - 1) ^ 2) := by
    have h1 : x + 2 ≠ 0 := by positivity
    have h3 : x + 3 ≠ 0 := by positivity
    have h4 : 2 * x - 3 ≠ 0 := by linarith
    have h5 : 2 * x - 1 ≠ 0 := by linarith
    have h4' : x * 2 - 3 ≠ 0 := by linarith
    have h5' : x * 2 - 1 ≠ 0 := by linarith
    simp only [VarAN, VarS, VarP2, CovSP2, ← hxdef]; field_simp; ring
  have hD : 0 < 32 * (x + 2) ^ 2 * (x + 3) * (2 * x - 3) * (2 * x - 1) ^ 2 := by
    have h3p : 0 < 2 * x - 3 := by linarith
    have h1p : 0 < 2 * x - 1 := by linarith
    have hx2 : 0 < x + 2 := by linarith
    have hx3 : 0 < x + 3 := by linarith
    exact mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hx2 2)) hx3) h3p)
      (pow_pos h1p 2)
  have hP : 0 ≤ 3 * (3336 * x ^ 5 + 1072 * x ^ 4 - 9465 * x ^ 3 - 6055 * x ^ 2
      + 12624 * x - 3852) := by
    nlinarith [pow_le_pow_left₀ (by norm_num) x2 3, pow_le_pow_left₀ (by norm_num) x2 4,
      pow_le_pow_left₀ (by norm_num) x2 5, mul_le_mul x2 x2 (by norm_num) (by linarith)]
  rw [hR, neg_div, abs_neg, abs_of_nonneg (div_nonneg hP hD.le),
    div_le_div_iff₀ hD (by linarith)]
  nlinarith [pow_le_pow_left₀ (by norm_num) x2 3, pow_le_pow_left₀ (by norm_num) x2 4,
    pow_le_pow_left₀ (by norm_num) x2 5, pow_le_pow_left₀ (by norm_num) x2 6,
    mul_le_mul x2 x2 (by norm_num) (by linarith)]

/-! ### The same statements in `IsBigO` form -/

private lemma bigO_of_bound {f : ℕ → ℝ} {g : ℕ → ℝ} (C : ℝ)
    (h : ∀ n : ℕ, 1 ≤ n → |f n| ≤ C * |g n|) : f =O[atTop] g :=
  IsBigO.of_bound C (by
    filter_upwards [eventually_ge_atTop 1] with n hn
    simpa [Real.norm_eq_abs] using h n hn)

theorem EAN_isBigO :
    (fun n : ℕ => EAN n - (9 / 4 * (n : ℝ) - 13 / 8)) =O[atTop] (fun n : ℕ => 1 / (n : ℝ)) :=
  bigO_of_bound 7 fun n hn => by
    have := EAN_expansion n hn
    have hx : (0 : ℝ) < n := by exact_mod_cast hn
    rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / n)]
    simpa [div_eq_mul_inv] using this

theorem EAM_isBigO :
    (fun n : ℕ => EAM n - (3 * (n : ℝ) - 4)) =O[atTop] (fun n : ℕ => 1 / (n : ℝ)) :=
  bigO_of_bound 6 fun n hn => by
    have := EAM_expansion n hn
    have hx : (0 : ℝ) < n := by exact_mod_cast hn
    rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / n)]
    simpa [div_eq_mul_inv] using this

theorem VarS_isBigO :
    (fun n : ℕ => VarS n - (4 - 30 / (n : ℝ))) =O[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
  bigO_of_bound 144 fun n hn => by
    have := VarS_expansion n hn
    have hx : (0 : ℝ) < n := by exact_mod_cast hn
    rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / (n : ℝ) ^ 2)]
    simpa [div_eq_mul_inv] using this

theorem VarAN_isBigO :
    (fun n : ℕ => VarAN n - ((n : ℝ) / 16 + 193 / 32)) =O[atTop] (fun n : ℕ => 1 / (n : ℝ)) :=
  bigO_of_bound 40 fun n hn => by
    have := VarAN_expansion n hn
    have hx : (0 : ℝ) < n := by exact_mod_cast hn
    rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / n)]
    simpa [div_eq_mul_inv] using this

end MakinenAnalysis
