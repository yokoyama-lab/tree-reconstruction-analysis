import Mathlib
import MakinenAnalysis.FinalAssembly

/-!
# Corollary 14 (`cor:sep`), CLT part — quantified advantage gap

`paper_en.tex`, Corollary 14 asserts that the deterministic gap
`A_M − A_N` between Mäkinen's algorithm `M` and the improved algorithm `N`
is, on every `n`-node binary tree,
`A_M − A_N = (n−3) − P₂ = (n−3) − (Leaves_n − 1)` (eq. `eq:gap`), and moreover
that its standardised version is asymptotically `N(0,1)`:
`((A_M − A_N) − (¾n − 19/8)) / (√n/4) ⇝ N(0,1)`.

The codebase has no per-codeword `A_M` function (`MakinenAnalysis.Asymptotics`
only carries the mean `EAM`; `MakinenAnalysis.LeafCount` only carries the
per-codeword `A_N` as `ANw`). Since the paper's identity shows the gap is a
*deterministic affine function of `P₂` alone* — the final stack height `h`
cancels between `A_M = 3n−1−h` and `A_N = 2n+2−h+P₂` — we define `gapw`
directly from that identity, `gapw n w = (n−3) − P₂ w`, and prove the CLT for
its standardisation by a charFun sign flip: the standardised gap is
`(gap − E[gap])/(√n/4) = −(P₂ − E[P₂])/(√n/4)`, so `charGap n t = charP2 n (−t)`,
and `leafCLT_charFun` at `s = −t` (with `(−t)² = t²`) gives the limit.
-/

namespace MakinenAnalysis

open Filter Finset

/-- The per-codeword gap `A_M − A_N` (paper, eq. `eq:gap`): since
    `A_M = 3n−1−h` and `A_N = S+P₂+(n+2) = (n−h)+P₂+(n+2) = 2n+2−h+P₂`, the
    final stack height `h` cancels and `A_M − A_N = (n−3) − P₂` is
    deterministic and affine in `P₂` alone. No per-codeword `A_M` function
    exists in this codebase (only the mean `EAM` of `MakinenAnalysis.Asymptotics`),
    so `gapw` is defined directly from this identity rather than as a
    difference of two per-codeword functions. Valued in `ℤ` since the gap can
    be negative for small `n` / large `P₂ w`. -/
def gapw (n : ℕ) (w : List ℕ) : ℤ := (n : ℤ) - 3 - (P2 w : ℤ)

/-- Exact mean of `gapw` under the uniform law: `E[gap] = (n−3) − E[P₂]`. -/
noncomputable def Egap (n : ℕ) : ℝ := (n : ℝ) - 3 - EP2 n

/-- Characteristic function of the standardised gap `(gap − E[gap])/(√n/4)`
    under the uniform law on valid codewords, exactly parallel to `charP2` /
    `charAN`'s definition (same Finset, same `·*4/√n` scaling, same centring
    style with the exact mean `Egap`). -/
noncomputable def charGap (n : ℕ) (t : ℝ) : ℂ :=
  (∑ w ∈ suffixes (n - 1) 1,
      Complex.exp (Complex.I *
        Complex.ofReal (t * (((gapw n w : ℝ) - Egap n) * 4 / Real.sqrt n))))
    / (catalan n : ℂ)

/-- The centred, scaled argument of `charGap` is literally the negation of
    the one for `charP2`: `gapw n w − Egap n = −(P₂ w − EP₂ n)`. -/
private lemma gapw_sub_Egap (n : ℕ) (w : List ℕ) :
    (gapw n w : ℝ) - Egap n = -((P2 w : ℝ) - EP2 n) := by
  have hgapw : (gapw n w : ℝ) = (n : ℝ) - 3 - (P2 w : ℝ) := by
    unfold gapw; push_cast; ring
  unfold Egap
  rw [hgapw]; ring

/-- **The charFun sign flip**: `charGap n t = charP2 n (−t)`, since the
    standardised gap is exactly `−1` times the standardised `P₂`. -/
lemma charGap_eq_charP2_neg (n : ℕ) (t : ℝ) : charGap n t = charP2 n (-t) := by
  unfold charGap charP2
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  have harg : t * (((gapw n w : ℝ) - Egap n) * 4 / Real.sqrt n)
      = (-t) * (((P2 w : ℝ) - EP2 n) * 4 / Real.sqrt n) := by
    rw [gapw_sub_Egap]; ring
  rw [harg]

/-- **Corollary 14 (`cor:sep`), CLT part.** The standardised deterministic
    advantage gap `A_M − A_N` is asymptotically `N(0,1)`. -/
theorem gap_CLT_charFun (t : ℝ) :
    Tendsto (fun n : ℕ => charGap n t) atTop (nhds (Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
  have hfun : (fun n : ℕ => charGap n t) = fun n : ℕ => charP2 n (-t) :=
    funext fun n => charGap_eq_charP2_neg n t
  rw [hfun]
  have h := leafCLT_charFun (-t)
  have hcast : ((-t : ℝ) : ℂ) = -(t : ℂ) := by push_cast; ring
  have heq : (-(((-t : ℝ) : ℂ)) ^ 2 / 2 : ℂ) = -(t : ℂ) ^ 2 / 2 := by
    rw [hcast]; ring
  rwa [heq] at h

/-! ### The paper's explicit asymptotic centring

Corollary 14 states the CLT with the explicit centring `3n/4 − 19/8` rather
than the exact mean `Egap n`. Since `Egap n − (3n/4 − 19/8) = −3/(8(2n−1)) =
O(1/n)`, the two standardisations differ by a *constant* (`w`-independent)
phase shift of size `O(1/(n√n))`, which vanishes in the limit — a strictly
easier variant of the `AN_CLT_of_leafCLT` reduction, since here the shift
does not even depend on the codeword `w`. -/

/-- `charGap`, but centred at the paper's explicit asymptotic centring
    `3n/4 − 19/8` (Corollary 14, eq. `eq:gap`) instead of the exact mean
    `Egap n`. -/
noncomputable def charGapExplicit (n : ℕ) (t : ℝ) : ℂ :=
  (∑ w ∈ suffixes (n - 1) 1,
      Complex.exp (Complex.I *
        Complex.ofReal
          (t * (((gapw n w : ℝ) - (3 * (n : ℝ) / 4 - 19 / 8)) * 4 / Real.sqrt n))))
    / (catalan n : ℂ)

/-- **The exact mean is `O(1/n)`-close to the paper's explicit centring**:
    `|Egap n − (3n/4 − 19/8)| ≤ (3/8)/n` for `n ≥ 1`, in fact with equality
    `Egap n − (3n/4 − 19/8) = −3/(8(2n−1))`. -/
lemma Egap_sub_explicit_small (n : ℕ) (hn : 1 ≤ n) :
    |Egap n - (3 * (n : ℝ) / 4 - 19 / 8)| ≤ (3 / 8) / n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2n1 : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
  have hpos8 : (0 : ℝ) < 8 * (2 * (n : ℝ) - 1) := by linarith
  have hden8 : (8 * (2 * (n : ℝ) - 1)) ≠ 0 := hpos8.ne'
  have hpos2 : (0 : ℝ) < 2 * (2 * (n : ℝ) - 1) := by linarith
  have hden2 : (2 * (2 * (n : ℝ) - 1)) ≠ 0 := hpos2.ne'
  have hX : (2 * (n : ℝ) - 1) ≠ 0 := h2n1.ne'
  have hcancel : ((n : ℝ) - 1) * ((n : ℝ) - 2) / (2 * (2 * (n : ℝ) - 1))
      * (8 * (2 * (n : ℝ) - 1)) = 4 * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
    rw [div_mul_eq_mul_div, div_eq_iff hden2]
    ring
  have heq : Egap n - (3 * (n : ℝ) / 4 - 19 / 8) = -(3 / (8 * (2 * (n : ℝ) - 1))) := by
    rw [← neg_div, eq_div_iff hden8]
    unfold Egap EP2
    linear_combination -hcancel
  rw [heq, abs_neg, abs_of_pos (div_pos (by norm_num) hpos8)]
  rw [div_le_div_iff₀ hpos8 hn0]
  nlinarith

/-- A constant-phase shift is a Lipschitz bound: shifting the argument of
    `Complex.exp (Complex.I * ·)` moves the value by at most the shift's size
    (the content of `LeafCount.norm_exp_I_sub_exp_I`, reproved locally since
    that lemma is `private` to its file). -/
private lemma norm_exp_I_sub_exp_I' (x y : ℝ) :
    ‖Complex.exp (Complex.I * Complex.ofReal x) - Complex.exp (Complex.I * Complex.ofReal y)‖
      ≤ |x - y| := by
  have harg : Complex.I * (x : ℂ) = Complex.I * (y : ℂ) + Complex.I * ((x - y : ℝ) : ℂ) := by
    push_cast; ring
  have hfact : Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ))
      = Complex.exp (Complex.I * (y : ℂ))
        * (Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add, ← harg]
  rw [hfact, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  simpa using Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y)

/-- **The two centrings' charFuns are `O(1/(n√n))`-close**, uniformly in `w`
    (the shift between the two standardised arguments does not depend on the
    codeword `w`, unlike the `A_N`-vs-`P₂` reduction of `AN_CLT_of_leafCLT`). -/
private lemma norm_charGapExplicit_sub_charGap_le (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    ‖charGapExplicit n t - charGap n t‖ ≤ 4 * |t| * (3 / 8) / ((n : ℝ) * Real.sqrt n) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hcatpos : (0 : ℝ) < (catalan n : ℝ) := by
    have h := Cat_ne_zero n
    simp only [Cat] at h
    exact_mod_cast Nat.pos_of_ne_zero (by exact_mod_cast h)
  -- pointwise: the two standardised arguments differ by the SAME constant for every `w`
  have hargs : ∀ w ∈ suffixes (n - 1) 1,
      t * (((gapw n w : ℝ) - (3 * (n : ℝ) / 4 - 19 / 8)) * 4 / Real.sqrt n)
        - t * (((gapw n w : ℝ) - Egap n) * 4 / Real.sqrt n)
      = 4 * t / Real.sqrt n * (Egap n - (3 * (n : ℝ) / 4 - 19 / 8)) := by
    intro w _
    field_simp
    ring
  have hquot : charGapExplicit n t - charGap n t
      = (∑ w ∈ suffixes (n - 1) 1,
          (Complex.exp (Complex.I *
              Complex.ofReal
                (t * (((gapw n w : ℝ) - (3 * (n : ℝ) / 4 - 19 / 8)) * 4 / Real.sqrt n)))
            - Complex.exp (Complex.I *
              Complex.ofReal (t * (((gapw n w : ℝ) - Egap n) * 4 / Real.sqrt n)))))
        / (catalan n : ℂ) := by
    simp only [charGapExplicit, charGap, div_sub_div_same, ← Finset.sum_sub_distrib]
  have hpt : ∀ w ∈ suffixes (n - 1) 1,
      ‖Complex.exp (Complex.I *
          Complex.ofReal
            (t * (((gapw n w : ℝ) - (3 * (n : ℝ) / 4 - 19 / 8)) * 4 / Real.sqrt n)))
        - Complex.exp (Complex.I *
          Complex.ofReal (t * (((gapw n w : ℝ) - Egap n) * 4 / Real.sqrt n)))‖
      ≤ |4 * t / Real.sqrt n * (Egap n - (3 * (n : ℝ) / 4 - 19 / 8))| := by
    intro w hw
    have h1 := norm_exp_I_sub_exp_I'
      (t * (((gapw n w : ℝ) - (3 * (n : ℝ) / 4 - 19 / 8)) * 4 / Real.sqrt n))
      (t * (((gapw n w : ℝ) - Egap n) * 4 / Real.sqrt n))
    rwa [hargs w hw] at h1
  -- this bound is uniform in `w`, hence survives averaging unchanged
  have hcbound : |4 * t / Real.sqrt n * (Egap n - (3 * (n : ℝ) / 4 - 19 / 8))|
      ≤ 4 * |t| * (3 / 8) / ((n : ℝ) * Real.sqrt n) := by
    rw [abs_mul, abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg (n : ℝ)),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    have h2 := Egap_sub_explicit_small n hn
    have hnum : 4 * |t| / Real.sqrt n * |Egap n - (3 * (n : ℝ) / 4 - 19 / 8)|
        ≤ 4 * |t| / Real.sqrt n * ((3 / 8) / n) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    calc 4 * |t| / Real.sqrt n * |Egap n - (3 * (n : ℝ) / 4 - 19 / 8)|
        ≤ 4 * |t| / Real.sqrt n * ((3 / 8) / n) := hnum
      _ = 4 * |t| * (3 / 8) / ((n : ℝ) * Real.sqrt n) := by
          field_simp
  rw [hquot, norm_div, Complex.norm_natCast, div_le_iff₀ hcatpos]
  have hstep1 := norm_sum_le (suffixes (n - 1) 1)
    (fun w => Complex.exp (Complex.I *
        Complex.ofReal
          (t * (((gapw n w : ℝ) - (3 * (n : ℝ) / 4 - 19 / 8)) * 4 / Real.sqrt n)))
      - Complex.exp (Complex.I *
        Complex.ofReal (t * (((gapw n w : ℝ) - Egap n) * 4 / Real.sqrt n))))
  have hstep2 := Finset.sum_le_sum hpt
  have hstep3 : (∑ _w ∈ suffixes (n - 1) 1,
      |4 * t / Real.sqrt n * (Egap n - (3 * (n : ℝ) / 4 - 19 / 8))|)
      = (catalan n : ℝ) * |4 * t / Real.sqrt n * (Egap n - (3 * (n : ℝ) / 4 - 19 / 8))| := by
    rw [Finset.sum_const, card_suffixes_eq_catalan n hn, nsmul_eq_mul]
  have hstep4 : (catalan n : ℝ)
      * |4 * t / Real.sqrt n * (Egap n - (3 * (n : ℝ) / 4 - 19 / 8))|
      ≤ (catalan n : ℝ) * (4 * |t| * (3 / 8) / ((n : ℝ) * Real.sqrt n)) :=
    mul_le_mul_of_nonneg_left hcbound (le_of_lt hcatpos)
  linarith [hstep1, hstep2, hstep3 ▸ hstep4]

/-- **Corollary 14 (`cor:sep`), CLT part, explicit-centring form.** The
    paper's literal statement `((A_M−A_N) − (¾n − 19/8))/(√n/4) ⇝ N(0,1)`. -/
theorem gap_CLT_charFun_explicit (t : ℝ) :
    Tendsto (fun n : ℕ => charGapExplicit n t) atTop
      (nhds (Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
  have hdiff : Tendsto (fun n : ℕ => charGapExplicit n t - charGap n t) atTop (nhds 0) := by
    refine squeeze_zero_norm' (a := fun n : ℕ => 4 * |t| * (3 / 8) / ((n : ℝ) * Real.sqrt n)) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact norm_charGapExplicit_sub_charGap_le n hn t
    · have hs : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
      have hinv : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (nhds 0) :=
        tendsto_inv_atTop_zero.comp hs
      have hb : Tendsto (fun n : ℕ => 4 * |t| * (3 / 8) / Real.sqrt n) atTop (nhds 0) := by
        have hmul := hinv.const_mul (4 * |t| * (3 / 8))
        simpa [div_eq_mul_inv, mul_zero] using hmul
      refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hb
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hsqrt : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn0
      have hkey : (0 : ℝ) ≤ |t| * (Real.sqrt n * ((n : ℝ) - 1)) :=
        mul_nonneg (abs_nonneg t) (mul_nonneg (Real.sqrt_nonneg _) (by linarith))
      rw [div_le_div_iff₀ (by positivity) hsqrt]
      nlinarith [hkey]
  have hsum := hdiff.add (gap_CLT_charFun t)
  simpa using hsum

end MakinenAnalysis
