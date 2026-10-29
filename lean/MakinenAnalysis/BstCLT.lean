import MakinenAnalysis.BstModel
import MakinenAnalysis.WeakConvergence

/-!
# Central limit theorems under the random BST model

WiNF2026 A2 (§5) states three limit laws under the
random binary search tree model (`bstW`, `BstModel.lean`):

| here | A2 |
|---|---|
| `bst_leafCLT` | `(L − n/3)/√(2n/45) →d N(0,1)` (leaf count, Devroye 1991) |
| `bst_AN_CLT` | `(Cmp_N − 7n/3)/√(2n/45) →d N(0,1)` |
| `bst_D_CLT` | `(D − 2n/3)/√(2n/45) →d N(0,1)`, `D = Cmp_M − Cmp_N` |

`Cmp_M`, `Cmp_N` are the comparison counts of the *executions* `cmpsM (ip t)`,
`cmpsN (ip t)` of `ExecModel`; they enter only through the per-tree identities
`central_M_exec` / `central_N_exec` shared with the uniform model.

## Route (no singularity analysis)

1. `leafGF x n = E[x^L]` satisfies `(n+1) m_{n+1} = Σ_{a+b=n} m_a m_b` (`n ≥ 1`),
   i.e. the Riccati equation `M' = M² + (x−1)` for `M = Σ m_n zⁿ`.
2. With `w = x − 1` and `Y(z) = cos(ωz) − sin(ωz)/ω` (`ω² = w`, coefficients `yc w`),
   `Y·M + Y' = 0` (`linrec`): `Z = Y·M + Y'` has `Z' = M·Z`, `Z(0) = 0`.
3. `ρ(w) = Σ (−w)^k/(2k+1) = arctan ω / ω` is a root of `Y` (`hasSum_yc_rho`).
4. Writing `μ_n = m_n ρⁿ`, the differences `d_n = μ_n − μ_{n−1}` satisfy a
   convolution recursion whose kernel is the tail of `Y(ρ·)`; an induction gives
   `‖μ_n − 1‖ ≤ E₆‖w‖` uniformly in `n` for small `‖w‖` (`mu_uniform`).
5. `ρ(e^{iu}−1)·e^{iu/3} = 1 + u²/45 + O(u³)` (`g_bound`), so the characteristic
   function `μ_n / g(u_n)ⁿ` tends to `e^{−s²/2}`; Lévy's continuity theorem finishes.
6. `Cmp_N − 7n/3 = (L − n/3) + (1 − h)` and `E[h] = E_n ≤ 2` move the leaf CLT to
   `Cmp_N` (`charB_sub_le`); `D − 2n/3 = −(L − n/3) − 2` gives the `D` CLT.

The law of a statistic `X` is `bstMeas n X = Σ_t bstW t · δ_{X t}` (`bstPM` as a
`ProbabilityMeasure`; total mass one by `bstE_one`).  All auxiliary definitions and
lemmas live in the namespace `MakinenAnalysis.BstCLT`; only the three headline
theorems are in `MakinenAnalysis`.
-/

namespace MakinenAnalysis

open Finset MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology ENNReal NNReal

noncomputable section

namespace BstCLT

/-! ## 1. The leaf generating function and its root recursion -/

/-- Complex expectation under the BST weight. -/
def cE (n : ℕ) (f : T → ℂ) : ℂ := ∑ t ∈ trees n, ((bstW t : ℚ) : ℂ) * f t

lemma cE_succ (n : ℕ) (f : T → ℂ) :
    cE (n + 1) f = (∑ p ∈ antidiagonal n, ∑ l ∈ trees p.1, ∑ r ∈ trees p.2,
        ((bstW l : ℚ) : ℂ) * ((bstW r : ℚ) : ℂ) * f (.node () l r)) / (n + 1) := by
  rw [cE]
  show ∑ t ∈ BinaryTree.treesOfNumNodesEq (n + 1), _ = _
  rw [BinaryTree.treesOfNumNodesEq_succ, Finset.sum_biUnion]
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.sum_map, Finset.sum_product, Finset.sum_div]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    rw [BinaryTree.mem_treesOfNumNodesEq] at hl hr
    have hp' : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
    show ((bstW (.node () l r) : ℚ) : ℂ) * f (.node () l r)
      = ((bstW l : ℚ) : ℂ) * ((bstW r : ℚ) : ℂ) * f (.node () l r) / (n + 1)
    rw [bstW, hl, hr, hp']
    push_cast
    ring
  · simp_rw [Set.PairwiseDisjoint, Set.Pairwise, Finset.disjoint_left]
    aesop

lemma cdsum_mul (i j : ℕ) (g k : T → ℂ) :
    ∑ l ∈ trees i, ∑ r ∈ trees j, ((bstW l : ℚ) : ℂ) * ((bstW r : ℚ) : ℂ) * (g l * k r)
      = cE i g * cE j k := by
  rw [cE, cE, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => by ring))

/-- `E[x^L]` over the `n`-node BST. -/
def leafGF (x : ℂ) (n : ℕ) : ℂ := cE n (fun t => x ^ leaves t)

lemma leafGF_zero (x : ℂ) : leafGF x 0 = 1 := by
  simp [leafGF, cE, bstW]

lemma leafGF_one (x : ℂ) : leafGF x 1 = x := by
  rw [leafGF, cE_succ]
  simp [bstW, leaves, isNode]

lemma leafGF_succ (x : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℂ) + 1) * leafGF x (n + 1)
      = ∑ p ∈ antidiagonal n, leafGF x p.1 * leafGF x p.2 := by
  rw [leafGF, cE_succ, mul_div_cancel₀ _ (by exact_mod_cast Nat.succ_ne_zero n)]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  show _ = cE p.1 _ * cE p.2 _
  rw [← cdsum_mul]
  refine Finset.sum_congr rfl (fun l hl => Finset.sum_congr rfl (fun r hr => ?_))
  rw [BinaryTree.mem_treesOfNumNodesEq] at hl hr
  have hp' : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
  have hL := leaves_node () l r
  rw [if_neg (by omega)] at hL
  have hL' : ((leaves (.node () l r) : ℕ) : ℚ) = ((leaves l + leaves r : ℕ) : ℚ) := by
    push_cast; simpa using hL
  have : leaves (.node () l r) = leaves l + leaves r := by exact_mod_cast hL'
  rw [this, pow_add]

/-! ## 2. Linearisation: `Y·M + Y' = 0` -/

/-- Coefficients of `Y(z) = cos(ωz) − sin(ωz)/ω` with `ω² = w`. -/
def yc (w : ℂ) (j : ℕ) : ℂ := (-1) ^ j * (-w) ^ (j / 2) / (j.factorial : ℂ)

lemma yc_zero (w : ℂ) : yc w 0 = 1 := by simp [yc]
lemma yc_one (w : ℂ) : yc w 1 = -1 := by simp [yc]

lemma yc_add_two (w : ℂ) (j : ℕ) :
    yc w (j + 2) * ((j : ℂ) + 2) * ((j : ℂ) + 1) = -(w * yc w j) := by
  rw [yc, yc, show (j + 2) / 2 = j / 2 + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
  have hf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have h1 : (j : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  have h2 : (j : ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (j + 1)
  have h3 : (2 : ℂ) + j ≠ 0 := by rw [add_comm]; exact h2
  have h4 : (j : ℂ) + 1 + 1 ≠ 0 := by rw [add_assoc]; norm_num; exact h2
  push_cast
  rw [pow_succ (-w), pow_add (-1 : ℂ) j 2]
  field_simp
  ring

open PowerSeries in
/-- **Linearisation** of the leaf recursion: `Σ_{a+b=n} y_a m_b = −(n+1) y_{n+1}`. -/
theorem linrec (w : ℂ) (n : ℕ) :
    ∑ p ∈ antidiagonal n, yc w p.1 * leafGF (1 + w) p.2 = -(((n : ℂ) + 1) * yc w (n + 1)) := by
  set m := leafGF (1 + w)
  set M : PowerSeries ℂ := PowerSeries.mk m
  set Y : PowerSeries ℂ := PowerSeries.mk (yc w)
  set D := d⁄dX ℂ
  have hM : D M = M ^ 2 + C w := by
    ext k
    rw [coeff_derivative, map_add, coeff_C, pow_two, coeff_mul]
    simp only [M, coeff_mk]
    rcases k with _ | k
    · simp [m, leafGF_zero, leafGF_one]
    · rw [if_neg (Nat.succ_ne_zero k), add_zero, ← leafGF_succ (1 + w) (by omega : 1 ≤ k + 1)]
      push_cast; ring
  have hY : D (D Y) = -(C w * Y) := by
    ext k
    rw [coeff_derivative, coeff_derivative, map_neg, coeff_C_mul]
    simp only [Y, coeff_mk]
    have := yc_add_two w k
    push_cast
    linear_combination this
  set Z := Y * M + D Y with hZdef
  have hZ : D Z = M * Z := by
    rw [hZdef, map_add, Derivation.leibniz, hM, hY, smul_eq_mul, smul_eq_mul]
    ring
  have hZ0 : ∀ k, coeff k Z = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases k with _ | k
      · rw [hZdef, map_add, coeff_mul, coeff_derivative]
        simp [Y, M, yc_zero, yc_one, m, leafGF_zero]
      · have h1 := congrArg (coeff k) hZ
        rw [coeff_derivative, coeff_mul] at h1
        have h2 : ∑ p ∈ antidiagonal k, coeff p.1 M * coeff p.2 Z = 0 := by
          refine Finset.sum_eq_zero (fun p hp => ?_)
          rw [ih p.2 (by have := Finset.antidiagonal.snd_le hp; omega), mul_zero]
        rw [h2] at h1
        have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
        exact (mul_eq_zero.mp h1).resolve_right hk
  have := hZ0 n
  rw [hZdef, map_add, coeff_mul, coeff_derivative] at this
  simp only [Y, M, coeff_mk] at this
  linear_combination this

/-! ## 3. The root `ρ(w) = arctan ω / ω` of `Y` -/

/-- Terms of `ρ(w) = Σ (−w)^k/(2k+1)`. -/
def rhoT (w : ℂ) (k : ℕ) : ℂ := (-w) ^ k / ((2 * k + 1 : ℕ) : ℂ)

/-- `ρ(w) = arctan ω / ω` (`ω² = w`), the smallest zero of `Y`. -/
def rho (w : ℂ) : ℂ := ∑' k, rhoT w k

lemma norm_rhoT_le (w : ℂ) (k : ℕ) : ‖rhoT w k‖ ≤ ‖w‖ ^ k := by
  rw [rhoT, norm_div, norm_pow, norm_neg]
  have : (1 : ℝ) ≤ ‖((2 * k + 1 : ℕ) : ℂ)‖ := by
    rw [Complex.norm_natCast]; exact_mod_cast (by omega : 1 ≤ 2 * k + 1)
  exact div_le_self (by positivity) this

lemma hasSum_rho {w : ℂ} (hw : ‖w‖ < 1) : HasSum (rhoT w) (rho w) :=
  (Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) hw)
    (norm_rhoT_le w)).hasSum

lemma neg_sq_pow (ω : ℂ) (k : ℕ) : (-(ω ^ 2)) ^ k = (-1) ^ k * ω ^ (2 * k) := by
  rw [neg_pow, pow_mul]

lemma neg_one_pow_two_mul (k : ℕ) : (-1 : ℂ) ^ (2 * k) = 1 := by
  rw [pow_mul, neg_one_sq, one_pow]

/-- The coefficients `yc w` are those of `cos(ωz) − sin(ωz)/ω`. -/
lemma hasSum_Y {ω : ℂ} (hω0 : ω ≠ 0) (z : ℂ) :
    HasSum (fun j => yc (ω ^ 2) j * z ^ j) (Complex.cos (ω * z) - Complex.sin (ω * z) / ω) := by
  rw [sub_eq_add_neg]
  refine HasSum.even_add_odd ?_ ?_
  · have e : (fun k => yc (ω ^ 2) (2 * k) * z ^ (2 * k))
        = fun k => (-1) ^ k * (ω * z) ^ (2 * k) / ((2 * k).factorial : ℂ) := by
      funext k
      rw [yc, show 2 * k / 2 = k by omega, neg_sq_pow, neg_one_pow_two_mul, mul_pow]
      ring
    rw [e]; exact Complex.hasSum_cos (ω * z)
  · have e : (fun k => yc (ω ^ 2) (2 * k + 1) * z ^ (2 * k + 1))
        = fun k => -((-1) ^ k * (ω * z) ^ (2 * k + 1) / ((2 * k + 1).factorial : ℂ) / ω) := by
      funext k
      rw [yc, show (2 * k + 1) / 2 = k by omega, neg_sq_pow, pow_succ (-1 : ℂ),
        neg_one_pow_two_mul, mul_pow, pow_succ ω, pow_succ z]
      field_simp
    rw [e]; exact ((Complex.hasSum_sin (ω * z)).div_const ω).neg

/-- **`ρ(w)` is a root of `Y`**: `Σ_j y_j ρ^j = 0` for `‖w‖ < 1`. -/
theorem hasSum_yc_rho {w : ℂ} (hw : ‖w‖ < 1) : HasSum (fun j => yc w j * rho w ^ j) 0 := by
  by_cases h0 : w = 0
  · subst h0
    have hr : rho 0 = 1 := by
      rw [rho, tsum_eq_single 0]
      · simp [rhoT]
      · intro k hk; simp [rhoT, hk]
    rw [hr]
    have := hasSum_sum_of_ne_finset_zero (f := fun j => yc 0 j * (1 : ℂ) ^ j) (s := range 2)
      (L := SummationFilter.unconditional ℕ) (by
        intro j hj
        simp only [Finset.mem_range, not_lt] at hj
        have : j / 2 ≠ 0 := by omega
        simp [yc, this])
    simpa [Finset.sum_range_succ, yc_zero, yc_one] using this
  · set ω := w ^ (2⁻¹ : ℂ) with hωdef
    have hω : ω ^ 2 = w := Complex.cpow_ofNat_inv_pow w 2
    have hω0 : ω ≠ 0 := by
      intro h; rw [h] at hω; simp at hω; exact h0 hω.symm
    have hωn : ‖ω‖ < 1 := by
      have : ‖ω‖ ^ 2 < 1 := by rw [← norm_pow, hω]; exact hw
      nlinarith [norm_nonneg ω]
    have harc : Complex.arctan ω = ω * rho w := by
      refine (Complex.hasSum_arctan hωn).unique ?_
      have e : (fun k => ω * rhoT w k)
          = fun n : ℕ => (-1) ^ n * ω ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℂ) := by
        funext k
        rw [rhoT, ← hω, neg_sq_pow, pow_succ ω]
        ring
      rw [← e]; exact (hasSum_rho hw).mul_left ω
    have hI : ω ≠ Complex.I := by
      intro h; rw [h, Complex.norm_I] at hωn; exact lt_irrefl _ hωn
    have hI' : ω ≠ -Complex.I := by
      intro h; rw [h, norm_neg, Complex.norm_I] at hωn; exact lt_irrefl _ hωn
    have ht := Complex.tan_arctan hI hI'
    rw [Complex.tan_eq_sin_div_cos] at ht
    have hY := hasSum_Y hω0 (rho w)
    rw [hω, ← harc] at hY
    convert hY using 1
    by_cases hc : Complex.cos (Complex.arctan ω) = 0
    · rw [hc, div_zero] at ht; exact absurd ht.symm hω0
    · rw [div_eq_iff hc] at ht
      rw [ht, mul_div_cancel_left₀ _ hω0, sub_self]

/-! ## 4. The uniform estimate `‖m_n ρⁿ − 1‖ ≤ E₆‖w‖` -/

/-- `c_j = y_j ρ^j`, the coefficients of `Y(ρz)`; they sum to `0`. -/
def cc (w : ℂ) (j : ℕ) : ℂ := yc w j * rho w ^ j

/-- Partial sums `γ_i = Σ_{j≤i} c_j` (the coefficients of `Y(ρz)/(1−z)`). -/
def gam (w : ℂ) (i : ℕ) : ℂ := ∑ j ∈ range (i + 1), cc w j

/-- `μ_n = m_n ρⁿ`. -/
def mu (w : ℂ) (n : ℕ) : ℂ := leafGF (1 + w) n * rho w ^ n

/-- Differences `d_0 = μ_0`, `d_{n+1} = μ_{n+1} − μ_n`. -/
def dd (w : ℂ) : ℕ → ℂ
  | 0 => mu w 0
  | n + 1 => mu w (n + 1) - mu w n

/-- Right-hand side `f_n = −(n+1) y_{n+1} ρⁿ`. -/
def ff (w : ℂ) (n : ℕ) : ℂ := -(((n : ℂ) + 1) * yc w (n + 1)) * rho w ^ n

/-- The constant `E₆ = Σ 6^k/k! (= e⁶)`. -/
def E6 : ℝ := ∑' k : ℕ, (6 : ℝ) ^ k / k.factorial

lemma pow_div_fact_le_E6 (k : ℕ) : (6 : ℝ) ^ k / k.factorial ≤ E6 :=
  (Real.summable_pow_div_factorial 6).le_tsum k (fun j _ => by positivity)

lemma one_le_E6 : 1 ≤ E6 := by simpa using pow_div_fact_le_E6 0

lemma mu_zero (w : ℂ) : mu w 0 = 1 := by simp [mu, leafGF_zero]

lemma sum_dd (w : ℂ) (k : ℕ) : ∑ j ∈ range (k + 1), dd w j = mu w k := by
  induction k with
  | zero => simp [dd]
  | succ k ih => rw [Finset.sum_range_succ, ih, dd]; ring

lemma sum_cc_mu (w : ℂ) (n : ℕ) :
    ∑ p ∈ antidiagonal n, cc w p.1 * mu w p.2 = ff w n := by
  rw [ff, ← linrec, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [cc, mu, ← Finset.mem_antidiagonal.mp hp, pow_add]
  ring

open PowerSeries in
lemma sum_gam_dd (w : ℂ) (n : ℕ) :
    ∑ p ∈ antidiagonal n, gam w p.1 * dd w p.2 = ff w n := by
  set one : PowerSeries ℂ := PowerSeries.mk (fun _ => 1)
  have hg : PowerSeries.mk (gam w) = PowerSeries.mk (cc w) * one := by
    ext k
    rw [coeff_mul, coeff_mk, gam]
    simp only [one, coeff_mk, mul_one]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i _ => cc w i)]
  have hm : PowerSeries.mk (mu w) = PowerSeries.mk (dd w) * one := by
    ext k
    rw [coeff_mul, coeff_mk, ← sum_dd]
    simp only [one, coeff_mk, mul_one]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i _ => dd w i)]
  have h := congrArg (coeff n)
    (show PowerSeries.mk (gam w) * PowerSeries.mk (dd w)
        = PowerSeries.mk (cc w) * PowerSeries.mk (mu w) by rw [hg, hm]; ring)
  rw [coeff_mul, coeff_mul] at h
  simp only [coeff_mk] at h
  rw [h, sum_cc_mu]

lemma gam_zero (w : ℂ) : gam w 0 = 1 := by simp [gam, cc, yc_zero]

lemma dd_succ_eq (w : ℂ) (n : ℕ) :
    dd w (n + 1) = ff w (n + 1) - ∑ p ∈ antidiagonal n, gam w (p.1 + 1) * dd w p.2 := by
  have h := sum_gam_dd w (n + 1)
  rw [Finset.Nat.sum_antidiagonal_succ, gam_zero, one_mul] at h
  rw [← h]; ring

section bounds

variable {w : ℂ} (hw : ‖w‖ ≤ 1 / 4)
include hw

lemma rho_sub_one_le : ‖rho w - 1‖ ≤ 2 * ‖w‖ := by
  have hw1 : ‖w‖ < 1 := by linarith
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_rho hw1)
  simp only [Finset.sum_range_one, rhoT, pow_zero, mul_zero, zero_add,
    Nat.cast_one, div_one] at h
  have hb := (hasSum_geometric_of_lt_one (norm_nonneg w) hw1).mul_left ‖w‖
  refine (h.norm_le_of_bounded hb (fun k => ?_)).trans ?_
  · exact (norm_rhoT_le w (k + 1)).trans_eq (pow_succ' _ _)
  · have : (1 - ‖w‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    nlinarith [norm_nonneg w]

lemma norm_rho_le : ‖rho w‖ ≤ 3 / 2 := by
  have := rho_sub_one_le hw
  calc ‖rho w‖ = ‖(rho w - 1) + 1‖ := by ring_nf
    _ ≤ ‖rho w - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ 3 / 2 := by rw [norm_one]; linarith

lemma rho_ne_zero : rho w ≠ 0 := by
  intro h
  have := rho_sub_one_le hw
  rw [h, zero_sub, norm_neg, norm_one] at this
  linarith

lemma norm_yc_le {j : ℕ} (hj : 2 ≤ j) : ‖yc w j‖ ≤ ‖w‖ / j.factorial := by
  rw [yc, norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_neg, norm_one, one_pow,
    one_mul, Complex.norm_natCast]
  gcongr
  exact pow_le_of_le_one (norm_nonneg w) (by linarith) (by omega)

omit hw in
lemma three_halves_le (j : ℕ) : (3 / 2 : ℝ) ^ j / j.factorial ≤ E6 * (1 / 4) ^ j := by
  have h := pow_div_fact_le_E6 j
  have e : (3 / 2 : ℝ) ^ j / j.factorial = (6 : ℝ) ^ j / j.factorial * (1 / 4) ^ j := by
    rw [show (3 / 2 : ℝ) = 6 * (1 / 4) by norm_num, mul_pow]; ring
  rw [e]
  exact mul_le_mul_of_nonneg_right h (by positivity)

lemma norm_cc_le {j : ℕ} (hj : 2 ≤ j) : ‖cc w j‖ ≤ ‖w‖ * E6 * (1 / 4) ^ j := by
  rw [cc, norm_mul, norm_pow]
  have h1 := norm_yc_le hw hj
  have h2 : ‖rho w‖ ^ j ≤ (3 / 2) ^ j := pow_le_pow_left₀ (norm_nonneg _) (norm_rho_le hw) j
  have h3 := three_halves_le j
  calc ‖yc w j‖ * ‖rho w‖ ^ j ≤ ‖w‖ / j.factorial * (3 / 2) ^ j :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = ‖w‖ * ((3 / 2) ^ j / j.factorial) := by ring
    _ ≤ ‖w‖ * (E6 * (1 / 4) ^ j) := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = ‖w‖ * E6 * (1 / 4) ^ j := by ring

lemma norm_gam_le {i : ℕ} (hi : 1 ≤ i) : ‖gam w i‖ ≤ ‖w‖ * E6 * (1 / 4) ^ i / 3 := by
  have hw1 : ‖w‖ < 1 := by linarith
  have h := (hasSum_nat_add_iff' (i + 1)).mpr (hasSum_yc_rho hw1)
  rw [zero_sub] at h
  have hb := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num)).mul_left (‖w‖ * E6 * (1 / 4) ^ (i + 1))
  have := h.norm_le_of_bounded hb (fun k => by
    have := norm_cc_le hw (j := k + (i + 1)) (by omega)
    calc ‖cc w (k + (i + 1))‖ ≤ ‖w‖ * E6 * (1 / 4) ^ (k + (i + 1)) := this
      _ = ‖w‖ * E6 * (1 / 4) ^ (i + 1) * (1 / 4) ^ k := by rw [pow_add]; ring)
  rw [norm_neg] at this
  calc ‖gam w i‖ = ‖∑ j ∈ range (i + 1), cc w j‖ := rfl
    _ ≤ ‖w‖ * E6 * (1 / 4) ^ (i + 1) * (1 - 1 / 4)⁻¹ := this
    _ = ‖w‖ * E6 * (1 / 4) ^ i / 3 := by rw [pow_succ]; norm_num; ring

lemma norm_ff_le {n : ℕ} (hn : 1 ≤ n) : ‖ff w n‖ ≤ ‖w‖ * E6 * (1 / 4) ^ n := by
  rw [ff, norm_mul, norm_neg, norm_mul, norm_pow]
  have h1 := norm_yc_le hw (j := n + 1) (by omega)
  have h2 : ‖rho w‖ ^ n ≤ (3 / 2) ^ n := pow_le_pow_left₀ (norm_nonneg _) (norm_rho_le hw) n
  have h3 := three_halves_le n
  have hn1 : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
    rw [show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast; ring
  rw [hn1, Nat.factorial_succ] at *
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  calc ((n : ℝ) + 1) * ‖yc w (n + 1)‖ * ‖rho w‖ ^ n
      ≤ ((n : ℝ) + 1) * (‖w‖ / ((n + 1) * n.factorial : ℕ)) * (3 / 2) ^ n := by
        gcongr
    _ = ‖w‖ * ((3 / 2) ^ n / n.factorial) := by push_cast; field_simp
    _ ≤ ‖w‖ * (E6 * (1 / 4) ^ n) := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = ‖w‖ * E6 * (1 / 4) ^ n := by ring

omit hw in
lemma half_geom (n : ℕ) : ∑ k ∈ range n, (1 / 2 : ℝ) ^ (k + 1) = 1 - (1 / 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

omit hw in
lemma sum_quarter_half (n : ℕ) :
    ∑ p ∈ antidiagonal n, (1 / 4 : ℝ) ^ (p.1 + 1) * (1 / 2) ^ p.2 ≤ (1 / 2) ^ (n + 1) := by
  have e : ∀ p ∈ antidiagonal n, (1 / 4 : ℝ) ^ (p.1 + 1) * (1 / 2) ^ p.2
      = (1 / 2) ^ (n + 1) * (1 / 2) ^ (p.1 + 1) := by
    intro p hp
    have hp' := Finset.mem_antidiagonal.mp hp
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, ← pow_mul, ← pow_add, ← pow_add]
    congr 1; omega
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i _ => (1 / 2 : ℝ) ^ (i + 1)), half_geom]
  have : (0 : ℝ) ≤ (1 / 2) ^ (n + 1) := by positivity
  exact mul_le_of_le_one_right this (sub_le_self _ (by positivity))

lemma norm_dd_succ_le (hK : ‖w‖ * E6 ≤ 1) (n : ℕ) :
    ‖dd w (n + 1)‖ ≤ ‖w‖ * E6 * (1 / 2) ^ (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have aux : ∀ b ≤ n, ‖dd w b‖ ≤ (1 / 2) ^ b := by
      intro b hb
      rcases b with _ | b
      · simp [dd, mu_zero]
      · refine (ih b (by omega)).trans ?_
        have : (0 : ℝ) ≤ (1 / 2) ^ (b + 1) := by positivity
        nlinarith
    rw [dd_succ_eq]
    have hsum : ‖∑ p ∈ antidiagonal n, gam w (p.1 + 1) * dd w p.2‖
        ≤ ‖w‖ * E6 / 3 * (1 / 2) ^ (n + 1) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ p ∈ antidiagonal n, ‖gam w (p.1 + 1) * dd w p.2‖
          ≤ ∑ p ∈ antidiagonal n, ‖w‖ * E6 / 3 * ((1 / 4) ^ (p.1 + 1) * (1 / 2) ^ p.2) := by
            refine Finset.sum_le_sum (fun p hp => ?_)
            rw [norm_mul]
            have h1 := norm_gam_le hw (i := p.1 + 1) (by omega)
            have h2 := aux p.2 (Finset.antidiagonal.snd_le hp)
            calc ‖gam w (p.1 + 1)‖ * ‖dd w p.2‖
                ≤ (‖w‖ * E6 * (1 / 4) ^ (p.1 + 1) / 3) * (1 / 2) ^ p.2 :=
                  mul_le_mul h1 h2 (norm_nonneg _)
                    (div_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _)
                      (zero_le_one.trans one_le_E6)) (by positivity)) (by norm_num))
              _ = _ := by ring
        _ = ‖w‖ * E6 / 3 * ∑ p ∈ antidiagonal n, (1 / 4 : ℝ) ^ (p.1 + 1) * (1 / 2) ^ p.2 := by
            rw [Finset.mul_sum]
        _ ≤ ‖w‖ * E6 / 3 * (1 / 2) ^ (n + 1) :=
            mul_le_mul_of_nonneg_left (sum_quarter_half n)
              (div_nonneg (mul_nonneg (norm_nonneg _) (zero_le_one.trans one_le_E6)) (by norm_num))
    have hf := norm_ff_le hw (n := n + 1) (by omega)
    have hq : (1 / 4 : ℝ) ^ (n + 1) ≤ (1 / 2) ^ (n + 1) / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2) * (1 / 2) by norm_num, mul_pow]
      have : (1 / 2 : ℝ) ^ (n + 1) ≤ 1 / 2 := by
        rw [pow_succ]; nlinarith [pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := n)]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (n + 1)]
    have hWE : 0 ≤ ‖w‖ * E6 := mul_nonneg (norm_nonneg _) (zero_le_one.trans one_le_E6)
    calc ‖ff w (n + 1) - ∑ p ∈ antidiagonal n, gam w (p.1 + 1) * dd w p.2‖
        ≤ ‖ff w (n + 1)‖ + ‖∑ p ∈ antidiagonal n, gam w (p.1 + 1) * dd w p.2‖ :=
          norm_sub_le _ _
      _ ≤ ‖w‖ * E6 * (1 / 4) ^ (n + 1) + ‖w‖ * E6 / 3 * (1 / 2) ^ (n + 1) := add_le_add hf hsum
      _ ≤ ‖w‖ * E6 * (1 / 2) ^ (n + 1) := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (n + 1)]

/-- **Uniform estimate.** `‖m_n(1+w) ρ(w)ⁿ − 1‖ ≤ E₆‖w‖` for all `n`. -/
theorem mu_uniform (hK : ‖w‖ * E6 ≤ 1) (n : ℕ) : ‖mu w n - 1‖ ≤ E6 * ‖w‖ := by
  rw [← sum_dd, Finset.sum_range_succ', dd, mu_zero, add_sub_cancel_right]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k ∈ range n, ‖dd w (k + 1)‖ ≤ ∑ k ∈ range n, ‖w‖ * E6 * (1 / 2) ^ (k + 1) :=
        Finset.sum_le_sum (fun k _ => norm_dd_succ_le hw hK k)
    _ = ‖w‖ * E6 * (1 - (1 / 2) ^ n) := by rw [← Finset.mul_sum, half_geom]
    _ ≤ E6 * ‖w‖ := by
        have : 0 ≤ ‖w‖ * E6 := mul_nonneg (norm_nonneg _) (zero_le_one.trans one_le_E6)
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]

end bounds

/-! ## 5. `ρ(e^{iu}−1)·e^{iu/3} = 1 + u²/45 + O(u³)` -/

lemma rho_cubic {w : ℂ} (hw : ‖w‖ ≤ 1 / 4) :
    ‖rho w - (1 - w / 3 + w ^ 2 / 5)‖ ≤ 2 * ‖w‖ ^ 3 := by
  have hw1 : ‖w‖ < 1 := by linarith
  have h := (hasSum_nat_add_iff' 3).mpr (hasSum_rho hw1)
  have hs : ∑ i ∈ range 3, rhoT w i = 1 - w / 3 + w ^ 2 / 5 := by
    norm_num [Finset.sum_range_succ, rhoT]; ring
  rw [hs] at h
  have hb := (hasSum_geometric_of_lt_one (norm_nonneg w) hw1).mul_left (‖w‖ ^ 3)
  refine (h.norm_le_of_bounded hb
    (fun k => (norm_rhoT_le w (k + 3)).trans_eq (by ring))).trans ?_
  have : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  nlinarith [pow_nonneg (norm_nonneg w) 3]

lemma exp_quad {x : ℂ} (hx : ‖x‖ ≤ 1) : ‖Complex.exp x - (1 + x + x ^ 2 / 2)‖ ≤ ‖x‖ ^ 3 := by
  have h := Complex.exp_bound hx (n := 3) (by norm_num)
  have hs : ∑ m ∈ range 3, x ^ m / (m.factorial : ℂ) = 1 + x + x ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [hs] at h
  refine h.trans ?_
  norm_num [Nat.factorial]
  nlinarith [pow_nonneg (norm_nonneg x) 3]

/-- `g(u) = ρ(e^{iu}−1)·e^{iu/3}`: the characteristic function of the standardised
    leaf count is `μ_n / g(u)ⁿ`. -/
def gfun (u : ℝ) : ℂ := rho (Complex.exp (Complex.I * u) - 1) * Complex.exp (Complex.I * u / 3)

/-- **Cubic expansion** `‖g(u) − (1 + u²/45)‖ ≤ 6|u|³` for `|u| ≤ 1/4`. -/
theorem g_bound {u : ℝ} (hu : |u| ≤ 1 / 4) : ‖gfun u - (1 + (u : ℂ) ^ 2 / 45)‖ ≤ 6 * |u| ^ 3 := by
  set t := |u| with htdef
  have ht0 : 0 ≤ t := abs_nonneg u
  set a : ℂ := Complex.I * u with hadef
  have ha : ‖a‖ = t := by rw [hadef, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  set w := Complex.exp a - 1 with hwdef
  have hw : ‖w‖ ≤ t := by
    rw [hwdef, hadef]; have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := u)
    rwa [Real.norm_eq_abs] at this
  have hw4 : ‖w‖ ≤ 1 / 4 := hw.trans hu
  set e1 := w - (a + a ^ 2 / 2) with he1def
  have he1 : ‖e1‖ ≤ t ^ 3 := by
    have := exp_quad (x := a) (by rw [ha]; linarith)
    rw [ha] at this
    rw [he1def, hwdef]; convert this using 2; ring
  set r := rho w - (1 - w / 3 + w ^ 2 / 5) with hrdef
  have hr : ‖r‖ ≤ 2 * t ^ 3 := by
    have h1 := rho_cubic hw4
    have h2 : ‖w‖ ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hw 3
    linarith
  set P : ℂ := 1 - a / 3 + a ^ 2 / 30 with hPdef
  set E := Complex.exp (Complex.I * u / 3) with hEdef
  set e2 := E - (1 + a / 3 + (a / 3) ^ 2 / 2) with he2def
  have he2 : ‖e2‖ ≤ t ^ 3 := by
    have hn : ‖a / 3‖ = t / 3 := by rw [norm_div, ha]; norm_num
    have := exp_quad (x := a / 3) (by rw [hn]; linarith)
    rw [hn] at this
    have h3 : (t / 3) ^ 3 ≤ t ^ 3 := by
      rw [div_pow]; have : (0 : ℝ) ≤ t ^ 3 := by positivity
      linarith
    rw [he2def, hEdef, show Complex.I * (u : ℂ) / 3 = a / 3 by rw [hadef]]
    exact this.trans h3
  have hE : ‖E‖ = 1 := by
    rw [hEdef, Complex.norm_exp]
    simp
  have hP : ‖P‖ ≤ 2 := by
    calc ‖P‖ ≤ ‖(1 : ℂ)‖ + ‖a / 3‖ + ‖a ^ 2 / 30‖ := by
          rw [hPdef]; exact (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ = 1 + t / 3 + t ^ 2 / 30 := by rw [norm_one, norm_div, norm_div, norm_pow, ha]; norm_num
      _ ≤ 2 := by nlinarith
  -- ε₁ = ρ − P
  have heps : ‖rho w - P‖ ≤ 3 * t ^ 3 := by
    have hwa : ‖w - a‖ ≤ t ^ 2 := by
      have : w - a = e1 + a ^ 2 / 2 := by rw [he1def]; ring
      rw [this]
      calc ‖e1 + a ^ 2 / 2‖ ≤ ‖e1‖ + ‖a ^ 2 / 2‖ := norm_add_le _ _
        _ ≤ t ^ 3 + t ^ 2 / 2 := by
            rw [norm_div, norm_pow, ha]; norm_num; linarith
        _ ≤ t ^ 2 := by nlinarith
    have hwpa : ‖w + a‖ ≤ 2 * t := by
      calc ‖w + a‖ ≤ ‖w‖ + ‖a‖ := norm_add_le _ _
        _ ≤ 2 * t := by rw [ha]; linarith
    have e : rho w - P = -e1 / 3 + (w - a) * (w + a) / 5 + r := by
      rw [he1def, hrdef, hPdef]; ring
    rw [e]
    calc ‖-e1 / 3 + (w - a) * (w + a) / 5 + r‖
        ≤ ‖-e1 / 3‖ + ‖(w - a) * (w + a) / 5‖ + ‖r‖ := norm_add₃_le
      _ = ‖e1‖ / 3 + ‖w - a‖ * ‖w + a‖ / 5 + ‖r‖ := by
          rw [norm_div, norm_div, norm_neg, norm_mul]; norm_num
      _ ≤ t ^ 3 / 3 + t ^ 2 * (2 * t) / 5 + 2 * t ^ 3 := by
          gcongr
      _ ≤ 3 * t ^ 3 := by nlinarith [pow_nonneg ht0 3]
  have hpoly : ‖-a ^ 3 / 135 + a ^ 4 / 540‖ ≤ t ^ 3 := by
    calc ‖-a ^ 3 / 135 + a ^ 4 / 540‖ ≤ ‖-a ^ 3 / 135‖ + ‖a ^ 4 / 540‖ := norm_add_le _ _
      _ = t ^ 3 / 135 + t ^ 4 / 540 := by
          rw [norm_div, norm_div, norm_neg, norm_pow, norm_pow, ha]; norm_num
      _ ≤ t ^ 3 := by nlinarith [pow_nonneg ht0 3, pow_nonneg ht0 4]
  have hu2 : (u : ℂ) ^ 2 = -a ^ 2 := by rw [hadef, mul_pow, Complex.I_sq]; ring
  have key : gfun u - (1 + (u : ℂ) ^ 2 / 45)
      = (rho w - P) * E + P * e2 + (-a ^ 3 / 135 + a ^ 4 / 540) := by
    rw [gfun, hu2, he2def, hPdef]
    rw [← hEdef, ← hadef, ← hwdef]
    ring
  rw [key]
  calc ‖(rho w - P) * E + P * e2 + (-a ^ 3 / 135 + a ^ 4 / 540)‖
      ≤ ‖(rho w - P) * E‖ + ‖P * e2‖ + ‖-a ^ 3 / 135 + a ^ 4 / 540‖ := norm_add₃_le
    _ = ‖rho w - P‖ * ‖E‖ + ‖P‖ * ‖e2‖ + ‖-a ^ 3 / 135 + a ^ 4 / 540‖ := by
        rw [norm_mul, norm_mul]
    _ ≤ 3 * t ^ 3 * 1 + 2 * t ^ 3 + t ^ 3 := by
        rw [hE]
        gcongr
    _ = 6 * t ^ 3 := by ring

/-! ## 6. Laws, characteristic functions, Lévy -/

lemma bstW_nonneg (t : T) : 0 ≤ bstW t := by
  induction t with
  | nil => simp [bstW]
  | node _ l r ihl ihr => simp only [bstW]; positivity

lemma sum_bstW (n : ℕ) : ∑ t ∈ trees n, (bstW t : ℝ) = 1 := by
  have := bstE_one n
  simp only [bstE, mul_one] at this
  exact_mod_cast this

/-- The law of a statistic `X` of the `n`-node BST. -/
def bstMeas (n : ℕ) (X : T → ℝ) : Measure ℝ :=
  ∑ t ∈ trees n, ENNReal.ofReal (bstW t : ℝ) • Measure.dirac (X t)

instance bstMeas_isProb (n : ℕ) (X : T → ℝ) : IsProbabilityMeasure (bstMeas n X) := by
  constructor
  rw [bstMeas, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ,
    Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun t _ => by exact_mod_cast bstW_nonneg t), sum_bstW,
    ENNReal.ofReal_one]

/-- The law as a `ProbabilityMeasure`. -/
def bstPM (n : ℕ) (X : T → ℝ) : ProbabilityMeasure ℝ := ⟨bstMeas n X, inferInstance⟩

/-- Characteristic function of `X` under the BST weight, by hand. -/
def charB (n : ℕ) (X : T → ℝ) (s : ℝ) : ℂ :=
  ∑ t ∈ trees n, ((bstW t : ℚ) : ℂ) * Complex.exp (Complex.I * ((s * X t : ℝ) : ℂ))

lemma charFun_bstPM (n : ℕ) (X : T → ℝ) (s : ℝ) :
    charFun (bstPM n X : Measure ℝ) s = charB n X s := by
  show charFun (bstMeas n X) s = _
  rw [charFun_apply_real, bstMeas, integral_finsetSum_measure
    (fun t _ => (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (by exact_mod_cast bstW_nonneg t),
    Complex.real_smul]
  push_cast
  ring_nf

/-- Lévy's continuity theorem in the form used below. -/
lemma tendsto_bstPM_of_charB (X : ℕ → T → ℝ)
    (h : ∀ s : ℝ, Tendsto (fun n => charB n (X n) s) atTop
      (𝓝 (Complex.exp (-(s : ℂ) ^ 2 / 2)))) :
    Tendsto (fun n => bstPM n (X n)) atTop (𝓝 stdGaussianPM) := by
  refine ProbabilityMeasure.tendsto_of_tendsto_charFun (fun s => ?_)
  rw [charFun_stdGaussian]
  exact (h s).congr (fun n => (charFun_bstPM n (X n) s).symm)

/-- `σ_n = √(2n/45)`. -/
def sig (n : ℕ) : ℝ := Real.sqrt (2 * n / 45)

lemma sig_sq (n : ℕ) : sig n ^ 2 = 2 * n / 45 := Real.sq_sqrt (by positivity)

lemma sig_pos {n : ℕ} (hn : 1 ≤ n) : 0 < sig n := by
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact Real.sqrt_pos.mpr (by positivity)

lemma tendsto_sig : Tendsto sig atTop atTop :=
  Real.tendsto_sqrt_atTop.comp
    ((tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).atTop_div_const
      (by norm_num))

/-- The standardised leaf count `(L − n/3)/σ_n`. -/
def stdL (n : ℕ) (t : T) : ℝ := ((leaves t : ℝ) - n / 3) / sig n

lemma charL_eq (n : ℕ) (s : ℝ)
    (hρ : rho (Complex.exp (Complex.I * ((s / sig n : ℝ) : ℂ)) - 1) ≠ 0) :
    charB n (stdL n) s
      = mu (Complex.exp (Complex.I * ((s / sig n : ℝ) : ℂ)) - 1) n / gfun (s / sig n) ^ n := by
  set u : ℝ := s / sig n with hu
  set E := Complex.exp (Complex.I * (u : ℂ) / 3) with hE
  have hE0 : E ≠ 0 := Complex.exp_ne_zero _
  have hterm : ∀ t : T, Complex.exp (Complex.I * ((s * stdL n t : ℝ) : ℂ))
      = Complex.exp (Complex.I * u) ^ leaves t / E ^ n := by
    intro t
    have : Complex.I * ((s * stdL n t : ℝ) : ℂ)
        = (leaves t : ℂ) * (Complex.I * u) - (n : ℂ) * (Complex.I * u / 3) := by
      rw [stdL, hu]; push_cast; field_simp
    rw [this, Complex.exp_sub, Complex.exp_nat_mul, Complex.exp_nat_mul]
  rw [mu, gfun, ← hE, show 1 + (Complex.exp (Complex.I * u) - 1) = Complex.exp (Complex.I * u)
    by ring, mul_pow, mul_comm (leafGF _ n), mul_div_mul_left _ _ (pow_ne_zero n hρ)]
  rw [charB, leafGF, cE, Finset.sum_div]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [hterm]; ring

/-- **The leaf CLT at the level of characteristic functions.** -/
theorem charL_tendsto (s : ℝ) :
    Tendsto (fun n => charB n (stdL n) s) atTop (𝓝 (Complex.exp (-(s : ℂ) ^ 2 / 2))) := by
  set u : ℕ → ℝ := fun n => s / sig n with hudef
  set w : ℕ → ℂ := fun n => Complex.exp (Complex.I * (u n : ℂ)) - 1 with hwdef
  have hu : Tendsto u atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_sig
  have hinvσ : Tendsto (fun n => 1 / sig n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_sig
  have hE6 : 0 < E6 := zero_lt_one.trans_le one_le_E6
  set δ : ℝ := min (1 / 4) E6⁻¹ with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (inv_pos.mpr hE6)
  have hsmall : ∀ᶠ n in atTop, |u n| < δ := by
    have := (tendsto_order.1 hu.abs).2 δ (by simpa using hδ0)
    simpa using this
  have hw_le : ∀ n, ‖w n‖ ≤ |u n| := fun n => by
    have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := u n)
    rwa [Real.norm_eq_abs] at this
  -- `μ_n → 1`
  have hmu : Tendsto (fun n => mu (w n) n) atTop (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : Tendsto (fun n => E6 * |u n|) atTop (𝓝 0) := by
      simpa using hu.abs.const_mul E6
    refine squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _)) ?_ hb
    filter_upwards [hsmall] with n hn
    have h1 : ‖w n‖ ≤ 1 / 4 := (hw_le n).trans (hn.le.trans (min_le_left _ _))
    have h2 : ‖w n‖ * E6 ≤ 1 := by
      have : ‖w n‖ ≤ E6⁻¹ := (hw_le n).trans (hn.le.trans (min_le_right _ _))
      calc ‖w n‖ * E6 ≤ E6⁻¹ * E6 := mul_le_mul_of_nonneg_right this hE6.le
        _ = 1 := inv_mul_cancel₀ hE6.ne'
    exact (mu_uniform h1 h2 n).trans (mul_le_mul_of_nonneg_left (hw_le n) hE6.le)
  -- `n (g(u_n) − 1) → s²/2`
  have hng : Tendsto (fun n : ℕ => (n : ℂ) * (gfun (u n) - 1)) atTop (𝓝 ((s : ℂ) ^ 2 / 2)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : Tendsto (fun n => 6 * |s| ^ 3 * (45 / 2) * (1 / sig n)) atTop (𝓝 0) := by
      simpa using hinvσ.const_mul (6 * |s| ^ 3 * (45 / 2))
    refine squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _)) ?_ hb
    filter_upwards [hsmall, eventually_ge_atTop 1] with n hn hn1
    have hσ := sig_pos hn1
    have hu4 : |u n| ≤ 1 / 4 := hn.le.trans (min_le_left _ _)
    have hgb := g_bound hu4
    have hsq : (n : ℂ) * ((u n : ℂ) ^ 2 / 45) = (s : ℂ) ^ 2 / 2 := by
      have h2 : ((sig n : ℝ) : ℂ) ^ 2 = 2 * (n : ℂ) / 45 := by
        rw [← Complex.ofReal_pow, sig_sq]; push_cast; ring
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      have hσ0 : ((sig n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
      rw [hudef]; push_cast
      rw [div_pow, h2]; field_simp
    have e : (n : ℂ) * (gfun (u n) - 1) - (s : ℂ) ^ 2 / 2
        = (n : ℂ) * (gfun (u n) - (1 + (u n : ℂ) ^ 2 / 45)) := by rw [← hsq]; ring
    rw [e, norm_mul, Complex.norm_natCast]
    have hun : |u n| = |s| / sig n := by rw [hudef]; simp [abs_div, abs_of_pos hσ]
    have hσ3 : (n : ℝ) / sig n ^ 3 = (45 / 2) * (1 / sig n) := by
      rw [pow_succ, sig_sq]; field_simp
    calc (n : ℝ) * ‖gfun (u n) - (1 + (u n : ℂ) ^ 2 / 45)‖ ≤ n * (6 * |u n| ^ 3) :=
          mul_le_mul_of_nonneg_left hgb (Nat.cast_nonneg n)
      _ = 6 * |s| ^ 3 * ((n : ℝ) / sig n ^ 3) := by rw [hun, div_pow]; ring
      _ = 6 * |s| ^ 3 * (45 / 2) * (1 / sig n) := by rw [hσ3]; ring
  have hgpow : Tendsto (fun n : ℕ => gfun (u n) ^ n) atTop (𝓝 (Complex.exp ((s : ℂ) ^ 2 / 2))) := by
    have := Complex.tendsto_one_add_pow_exp_of_tendsto hng
    simpa using this
  have hlim := hmu.div hgpow (Complex.exp_ne_zero _)
  rw [one_div, ← Complex.exp_neg, show -((s : ℂ) ^ 2 / 2) = -(s : ℂ) ^ 2 / 2 by ring] at hlim
  refine hlim.congr' ?_
  filter_upwards [hsmall, eventually_ge_atTop 1] with n hn hn1
  have hw4 : ‖w n‖ ≤ 1 / 4 := (hw_le n).trans (hn.le.trans (min_le_left _ _))
  exact (charL_eq n s (rho_ne_zero hw4)).symm

/-! ## 7. The comparison counts `Cmp_N` and `D = Cmp_M − Cmp_N` -/

lemma Ee_le_two (n : ℕ) : (Ee n : ℝ) ≤ 2 := by
  have hf : ∀ m : ℕ, (2 : ℝ) ^ m ≤ ((m + 1).factorial : ℝ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.factorial_succ, pow_succ]; push_cast
      nlinarith [ih, (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ m)]
  rw [Ee]; push_cast
  have hgeom : ∑ m ∈ range n, (1 / 2 : ℝ) ^ m = 2 * (1 - (1 / 2) ^ n) := by
    rw [← half_geom, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => by rw [pow_succ]; ring)
  calc ∑ m ∈ range n, 1 / (((m + 1).factorial : ℕ) : ℝ) ≤ ∑ m ∈ range n, (1 / 2 : ℝ) ^ m := by
        refine Finset.sum_le_sum (fun m _ => ?_)
        rw [one_div_pow]
        exact one_div_le_one_div_of_le (by positivity) (hf m)
    _ = 2 * (1 - (1 / 2) ^ n) := hgeom
    _ ≤ 2 := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]

lemma sum_bstW_rlen (n : ℕ) : ∑ t ∈ trees n, (bstW t : ℝ) * rlen t = Ee n := by
  have := bst_Eh n
  simp only [bstE] at this
  exact_mod_cast this

lemma norm_ratCast_bstW (t : T) : ‖((bstW t : ℚ) : ℂ)‖ = (bstW t : ℝ) := by
  rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by exact_mod_cast bstW_nonneg t)]

/-- Characteristic functions of two statistics differ by at most `|s|·E|X − Y|`. -/
lemma charB_sub_le (n : ℕ) (X Y : T → ℝ) (s : ℝ) :
    ‖charB n X s - charB n Y s‖ ≤ ∑ t ∈ trees n, (bstW t : ℝ) * (|s| * |X t - Y t|) := by
  rw [charB, charB, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun t _ => ?_))
  rw [← mul_sub, norm_mul, norm_ratCast_bstW]
  refine mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast bstW_nonneg t)
  have e : Complex.exp (Complex.I * ((s * X t : ℝ) : ℂ))
      = Complex.exp (Complex.I * ((s * Y t : ℝ) : ℂ))
        * Complex.exp (Complex.I * ((s * X t - s * Y t : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e, ← mul_sub_one, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans_eq ?_
  rw [← mul_sub, Real.norm_eq_abs, abs_mul]

lemma bst_ne_nil {n : ℕ} (hn : 1 ≤ n) {t : T} (ht : t ∈ trees n) : t ≠ .nil := by
  rintro rfl
  rw [BinaryTree.mem_treesOfNumNodesEq] at ht
  simp [BinaryTree.numNodes] at ht; omega

lemma cmpsN_real {n : ℕ} (hn : 1 ≤ n) {t : T} (ht : t ∈ trees n) :
    (cmpsN (ip t) : ℝ) = 2 * n + 1 + leaves t - rlen t := by
  have h := central_N_exec t (bst_ne_nil hn ht)
  rw [finalH_toPop_eq_rlen t (bst_ne_nil hn ht),
    BinaryTree.mem_treesOfNumNodesEq.mp ht] at h
  have : ((cmpsN (ip t) + rlen t : ℕ) : ℝ) = ((2 * n + 1 + leaves t : ℕ) : ℝ) := by rw [h]
  push_cast at this; linarith

lemma cmpsM_real {n : ℕ} (hn : 1 ≤ n) {t : T} (ht : t ∈ trees n) :
    (cmpsM (ip t) : ℝ) = 3 * n - 1 - rlen t := by
  have h := central_M_exec t (bst_ne_nil hn ht)
  rw [finalH_toPop_eq_rlen t (bst_ne_nil hn ht),
    BinaryTree.mem_treesOfNumNodesEq.mp ht] at h
  have : ((cmpsM (ip t) + rlen t + 1 : ℕ) : ℝ) = ((3 * n : ℕ) : ℝ) := by rw [h]
  push_cast at this; linarith

/-- The standardised comparison count of `N`. -/
def stdANb (n : ℕ) (t : T) : ℝ := ((cmpsN (ip t) : ℝ) - 7 * n / 3) / sig n

/-- The standardised advantage `D = Cmp_M − Cmp_N`. -/
def stdDb (n : ℕ) (t : T) : ℝ := (((cmpsM (ip t) : ℝ) - cmpsN (ip t)) - 2 * n / 3) / sig n

theorem charAN_tendsto (s : ℝ) :
    Tendsto (fun n => charB n (stdANb n) s) atTop (𝓝 (Complex.exp (-(s : ℂ) ^ 2 / 2))) := by
  have hdiff : Tendsto (fun n => charB n (stdANb n) s - charB n (stdL n) s) atTop (𝓝 0) := by
    have hb : Tendsto (fun n => 3 * |s| * (1 / sig n)) atTop (𝓝 0) := by
      have := ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop tendsto_sig).const_mul (3 * |s|)
      rwa [mul_zero] at this
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hσ := sig_pos hn
    refine (charB_sub_le n _ _ s).trans ?_
    calc ∑ t ∈ trees n, (bstW t : ℝ) * (|s| * |stdANb n t - stdL n t|)
        ≤ ∑ t ∈ trees n, (bstW t : ℝ) * (|s| * ((1 + rlen t) * (1 / sig n))) := by
          refine Finset.sum_le_sum (fun t ht => mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left ?_ (abs_nonneg s)) (by exact_mod_cast bstW_nonneg t))
          have e : stdANb n t - stdL n t = (1 - rlen t) * (1 / sig n) := by
            rw [stdANb, stdL, cmpsN_real hn ht]; field_simp; ring
          rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / sig n)]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [abs_le]; constructor <;> linarith [(Nat.cast_nonneg (rlen t) : (0 : ℝ) ≤ rlen t)]
      _ = |s| * (1 / sig n) * (∑ t ∈ trees n, (bstW t : ℝ) + ∑ t ∈ trees n, (bstW t : ℝ) * rlen t) := by
          rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun t _ => by ring)
      _ ≤ 3 * |s| * (1 / sig n) := by
          rw [sum_bstW, sum_bstW_rlen]
          have := Ee_le_two n
          have h0 : 0 ≤ |s| * (1 / sig n) := by positivity
          nlinarith
  have := (charL_tendsto s).add hdiff
  simpa using this

theorem charD_tendsto (s : ℝ) :
    Tendsto (fun n => charB n (stdDb n) s) atTop (𝓝 (Complex.exp (-(s : ℂ) ^ 2 / 2))) := by
  have hc : Tendsto (fun n => Complex.exp (Complex.I * ((-2 * s / sig n : ℝ) : ℂ))) atTop (𝓝 1) := by
    have h0 : Tendsto (fun n => -2 * s / sig n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_sig
    have hcont : Continuous (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ))) := by fun_prop
    have := (hcont.tendsto 0).comp h0
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at this
    exact this
  have hL := charL_tendsto (-s)
  rw [show (((-s : ℝ)) : ℂ) = -(s : ℂ) by push_cast; ring, neg_sq] at hL
  have := hc.mul hL
  rw [one_mul] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hσ := (sig_pos hn).ne'
  rw [charB, charB, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  have e : Complex.I * ((s * stdDb n t : ℝ) : ℂ)
      = Complex.I * ((-2 * s / sig n : ℝ) : ℂ) + Complex.I * ((-s * stdL n t : ℝ) : ℂ) := by
    rw [stdDb, stdL, cmpsM_real hn ht, cmpsN_real hn ht]
    push_cast; field_simp; ring
  rw [e, Complex.exp_add]; ring

end BstCLT

open BstCLT

/-! ## Headline theorems -/

/-- **Leaf CLT under the BST model** (A2 §5, Devroye 1991):
    `(L − n/3)/√(2n/45) →d N(0,1)`. -/
theorem bst_leafCLT :
    Tendsto (fun n => bstPM n (fun t => ((leaves t : ℝ) - n / 3) / Real.sqrt (2 * n / 45)))
      atTop (𝓝 stdGaussianPM) :=
  tendsto_bstPM_of_charB stdL charL_tendsto

/-- **CLT for the comparison count of `N` under the BST model** (A2 §5):
    `(Cmp_N − 7n/3)/√(2n/45) →d N(0,1)`, for the executed comparison count. -/
theorem bst_AN_CLT :
    Tendsto (fun n => bstPM n (fun t => ((cmpsN (ip t) : ℝ) - 7 * n / 3) / Real.sqrt (2 * n / 45)))
      atTop (𝓝 stdGaussianPM) :=
  tendsto_bstPM_of_charB stdANb charAN_tendsto

/-- **CLT for the advantage `D = Cmp_M − Cmp_N` under the BST model** (A2 §5):
    `(D − 2n/3)/√(2n/45) →d N(0,1)`. -/
theorem bst_D_CLT :
    Tendsto (fun n => bstPM n
        (fun t => (((cmpsM (ip t) : ℝ) - cmpsN (ip t)) - 2 * n / 3) / Real.sqrt (2 * n / 45)))
      atTop (𝓝 stdGaussianPM) :=
  tendsto_bstPM_of_charB stdDb charD_tendsto

end

end MakinenAnalysis
