import Mathlib
import MakinenAnalysis.BallotCount

/-!
# Asymptotic / probabilistic-limit results of `paper_en.tex` — Lean 4 + Mathlib

This file proves the results of `../../paper_en.tex` that the Rocq development
in `../../coq/` does **not** cover (they are analytic): the distribution law,
the negative-binomial limit, and the asymptotic expansions of the moments.
See `../../coq/paper_en-correspondence.md` for the statement-by-statement
status, and `MakinenAnalysis.LeafCount` for the CLT programme
(Proposition 12 / Theorem 13).

## Status

All five theorems are **fully proved** against **Mathlib `v4.31.0`** and
axiom-clean (`#print axioms` reports only `propext, Classical.choice,
Quot.sound` — no `sorryAx`):

* `thm_Mlimit` — the negative-binomial limit `P(h = m+1) → (m+1)·2^{-(m+2)}`
  (Theorem 10), by induction on `m`: closed form at the bottom rung via the
  `centralBinom` recurrence, then one-step `choose` ratios up the ladder;
* `EAM_asymp` (`E[A_M] ∼ 3n`), `EAN_asymp` (`E[A_N] ∼ 9n/4`) — Corollary 7;
* `VarS_asymp` (`Var[S] → 4`) and `VarAN_asymp` (`Var[A_N] ∼ n/16`) — the two
  sides of the variance dichotomy (Theorem 9).

In addition, **Lemma 2** is machine-checked on the codeword sample space
(see `MakinenAnalysis.BallotCount` and the bridge section at the end of this
file): `hProb_eq_count` shows `hProb n m` is the literal counting proportion
`#(hw (n-1) 1 m) / #(suffixes (n-1) 1)`, with `#(suffixes (n-1) 1) = catalan n`
(`card_suffixes_eq_catalan`), and `thm_Mlimit_count` restates Theorem 10 for the
literal counts — discharging the former caveat on `thm_Mlimit`.  (Trees ↔
codewords and `h = n - S` are machine-checked in the Rocq development.)

Rebuild with

```sh
lake exe cache get      # fetch the prebuilt Mathlib cache
lake build
```
-/

namespace MakinenAnalysis

open Filter Topology

noncomputable section

/-- `C_n`, the `n`-th Catalan number (Mathlib's `catalan`): the number of
    size-`n` unlabelled binary trees / valid codewords. -/
def Cat (n : ℕ) : ℝ := (catalan n : ℝ)

/-- Ballot number `B(n,m) = (m/n)·C(2n-m-1, n-1)` (Catalan triangle, OEIS
    A009766): the number of size-`n` trees whose final stack height `h`
    (rightmost-path length `+1`) equals `m`.  Kept real-valued to sidestep the
    exactness of the integer division. -/
def ballot (n m : ℕ) : ℝ := (m : ℝ) / (n : ℝ) * (Nat.choose (2 * n - m - 1) (n - 1) : ℝ)

/-- `P(h = m)` under the uniform Catalan model `= B(n,m)/C_n` (Lemma 2). -/
def hProb (n m : ℕ) : ℝ := ballot n m / Cat n

/-- Exact mean comparison count of the improved algorithm `N` (Corollary 7):
    `E[A_N] = n(n-1)/(n+2) + (n+2) + (n-1)(n-2)/(2(2n-1))`. -/
def EAN (n : ℕ) : ℝ :=
  (n : ℝ) * ((n : ℝ) - 1) / ((n : ℝ) + 2)
    + ((n : ℝ) + 2)
    + ((n : ℝ) - 1) * ((n : ℝ) - 2) / (2 * (2 * (n : ℝ) - 1))

/-- Exact mean comparison count of Mäkinen's `M`: `E[A_M] = n(n-1)/(n+2) + 2n-1`. -/
def EAM (n : ℕ) : ℝ :=
  (n : ℝ) * ((n : ℝ) - 1) / ((n : ℝ) + 2) + 2 * (n : ℝ) - 1

/-- `Var[S] = 2n(2n+1)(n-1) / ((n+2)^2 (n+3))` (eq. `varcov`). -/
def VarS (n : ℕ) : ℝ :=
  2 * (n : ℝ) * (2 * (n : ℝ) + 1) * ((n : ℝ) - 1)
    / (((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 3))

/-- `Var[P_2] = n(n+1)(n-1)(n-2) / (2(2n-1)^2 (2n-3))` (eq. `varcov`). -/
def VarP2 (n : ℕ) : ℝ :=
  (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) - 1) * ((n : ℝ) - 2)
    / (2 * (2 * (n : ℝ) - 1) ^ 2 * (2 * (n : ℝ) - 3))

/-- `Cov[S,P_2] = 2(n-1)(n-2) / ((n+2)(2n-1))` (eq. `varcov`). -/
def CovSP2 (n : ℕ) : ℝ :=
  2 * ((n : ℝ) - 1) * ((n : ℝ) - 2) / (((n : ℝ) + 2) * (2 * (n : ℝ) - 1))

/-- `Var[A_N] = Var[S] + Var[P_2] + 2 Cov[S,P_2]`. -/
def VarAN (n : ℕ) : ℝ := VarS n + VarP2 n + 2 * CovSP2 n

/-- PMF of `NB(2, 1/2)` at `m`: `(m+1)·2^{-(m+2)}`. -/
def nbPMF (m : ℕ) : ℝ := ((m : ℝ) + 1) * (1 / 2 : ℝ) ^ (m + 2)

/-! ### Shared helpers -/

/-- `catalan n ≠ 0` over ℝ, from `(n+1)·catalan n = centralBinom n ≠ 0`. -/
lemma Cat_ne_zero (n : ℕ) : Cat n ≠ 0 := by
  have h := succ_mul_catalan_eq_centralBinom n
  have hcat : catalan n ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h
    exact Nat.centralBinom_ne_zero n h.symm
  show (catalan n : ℝ) ≠ 0
  exact_mod_cast hcat

/-- Replace the limit point of a `Tendsto` by an equal value (used to
    normalise limits assembled from `tendsto_const_nhds` blocks). -/
private lemma tendsto_lim_eq {α : Type*} {l : Filter α} {f : α → ℝ} {a b : ℝ}
    (h : Tendsto f l (nhds a)) (hab : a = b) : Tendsto f l (nhds b) := hab ▸ h

/-- `(n : ℝ)⁻¹ → 0` along `ℕ`. -/
private lemma tendsto_inv_natCast :
    Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

/-- `(1 - 1/n) / (1 + 2/n) → 1` — the normalised form of `(n-1)/(n+2)`,
    shared by the two mean asymptotics. -/
private lemma tendsto_ratio_one :
    Tendsto (fun n : ℕ => (1 - ((n : ℝ))⁻¹) / (1 + 2 * ((n : ℝ))⁻¹))
      atTop (nhds 1) :=
  tendsto_lim_eq
    ((tendsto_const_nhds.sub tendsto_inv_natCast).div
      (tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_inv_natCast))
      (by norm_num))
    (by norm_num)

/-! ### Theorem 10: the negative-binomial limit -/

/-- Closed form at the bottom of the ladder: for `n ≥ 1`,
    `P(h = 1) = B(n,1)/C_n = (n+1) / (2(2n-1))`.
    From `(n+1)·catalan n = centralBinom n` and the `centralBinom` recurrence
    `(n+1)·CB(n+1) = 2(2n+1)·CB n`. -/
private lemma hProb_one_eq {n : ℕ} (hn : 1 ≤ n) :
    hProb n 1 = ((n : ℝ) + 1) / (2 * (2 * (n : ℝ) - 1)) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  -- the codeword count in `ballot (j+1) 1` is `centralBinom j`
  have e1 : 2 * (j + 1) - 1 - 1 = 2 * j := by omega
  have e2 : j + 1 - 1 = j := by omega
  -- the two structural relations, over ℝ
  have hcat : ((j : ℝ) + 2) * Cat (j + 1) = (Nat.centralBinom (j + 1) : ℝ) := by
    simp only [Cat]
    exact_mod_cast succ_mul_catalan_eq_centralBinom (j + 1)
  have hcb : ((j : ℝ) + 1) * (Nat.centralBinom (j + 1) : ℝ)
      = 2 * (2 * (j : ℝ) + 1) * (Nat.centralBinom j : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ j
  simp only [hProb, ballot, e1, e2, ← Nat.centralBinom_eq_two_mul_choose]
  push_cast
  have hj1 : ((j : ℝ) + 1) ≠ 0 := by positivity
  have hd : (0 : ℝ) < 2 * (2 * ((j : ℝ) + 1) - 1) := by
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    nlinarith
  rw [div_eq_div_iff (Cat_ne_zero (j + 1)) hd.ne']
  field_simp
  linear_combination -hcb - ((j : ℝ) + 1) * hcat

/-- Base case of the induction: `P(h = 1) → 1/4`. -/
private lemma hProb_one_tendsto :
    Tendsto (fun n : ℕ => hProb n 1) atTop (nhds (1 / 4)) := by
  have h : Tendsto (fun n : ℕ => (1 + ((n : ℝ))⁻¹) / (2 * (2 - ((n : ℝ))⁻¹)))
      atTop (nhds (1 / 4)) :=
    tendsto_lim_eq
      ((tendsto_const_nhds.add tendsto_inv_natCast).div
        (tendsto_const_nhds.mul (tendsto_const_nhds.sub tendsto_inv_natCast))
        (by norm_num))
      (by norm_num)
  refine Filter.Tendsto.congr' ?_ h
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [hProb_one_eq hn]
  have hge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hmul : (n : ℝ) * ((n : ℝ))⁻¹ = 1 := mul_inv_cancel₀ hn0.ne'
  have hinv0 : (0 : ℝ) ≤ ((n : ℝ))⁻¹ := by positivity
  have hd2 : (0 : ℝ) < 2 - ((n : ℝ))⁻¹ := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) - 1) hinv0]
  have hd1 : (0 : ℝ) < 2 * (n : ℝ) - 1 := by nlinarith
  field_simp

/-- One rung of the ladder: for `n ≥ k+3`,
    `P(h = k+2) = P(h = k+1) · (k+2)(n-k-1) / ((k+1)(2n-k-2))`,
    from `choose(a,r)·(a+1) = choose(a+1,r)·(a+1-r)` at `a = 2n-k-3`, `r = n-1`. -/
private lemma hProb_succ_eq {k n : ℕ} (hn : k + 3 ≤ n) :
    hProb n (k + 2) = hProb n (k + 1) *
      (((k : ℝ) + 2) * ((n : ℝ) - (k : ℝ) - 1) /
        (((k : ℝ) + 1) * (2 * (n : ℝ) - (k : ℝ) - 2))) := by
  -- the ℕ-level choose identity
  have hch := Nat.choose_mul_succ_eq (2 * n - k - 3) (n - 1)
  have e1 : 2 * n - k - 3 + 1 = 2 * n - k - 2 := by omega
  rw [e1] at hch
  have e2 : 2 * n - k - 2 - (n - 1) = n - k - 1 := by omega
  rw [e2] at hch
  -- cast it to ℝ, converting the ℕ-subtractions
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
  -- nonvanishing
  have hCatne : Cat n ≠ 0 := Cat_ne_zero n
  have hnk : (k : ℝ) + 3 ≤ (n : ℝ) := by exact_mod_cast hn
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hden : (0 : ℝ) < 2 * (n : ℝ) - (k : ℝ) - 2 := by nlinarith
  -- unfold, align the codeword indices, and clear denominators
  have i1 : 2 * n - (k + 2) - 1 = 2 * n - k - 3 := by omega
  have i2 : 2 * n - (k + 1) - 1 = 2 * n - k - 2 := by omega
  simp only [hProb, ballot, i1, i2]
  push_cast
  field_simp
  linear_combination hchR

/-- Limit of the rung ratio: `(k+2)(n-k-1) / ((k+1)(2n-k-2)) → (k+2)/(2(k+1))`. -/
private lemma ratio_tendsto (k : ℕ) :
    Tendsto (fun n : ℕ => ((k : ℝ) + 2) * ((n : ℝ) - (k : ℝ) - 1) /
        (((k : ℝ) + 1) * (2 * (n : ℝ) - (k : ℝ) - 2)))
      atTop (nhds (((k : ℝ) + 2) / (((k : ℝ) + 1) * 2))) := by
  have h : Tendsto (fun n : ℕ =>
      (((k : ℝ) + 2) * (1 - ((k : ℝ) + 1) * ((n : ℝ))⁻¹)) /
        (((k : ℝ) + 1) * (2 - ((k : ℝ) + 2) * ((n : ℝ))⁻¹)))
      atTop (nhds (((k : ℝ) + 2) / (((k : ℝ) + 1) * 2))) := by
    refine tendsto_lim_eq (Filter.Tendsto.div
      (tendsto_const_nhds.mul
        (tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_inv_natCast)))
      (tendsto_const_nhds.mul
        (tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_inv_natCast))) ?_)
      (by ring)
    simp only [mul_zero, sub_zero]
    positivity
  refine Filter.Tendsto.congr' ?_ h
  filter_upwards [eventually_ge_atTop (k + 3)] with n hn
  have hnk : (k : ℝ) + 3 ≤ (n : ℝ) := by exact_mod_cast hn
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hmul : (n : ℝ) * ((n : ℝ))⁻¹ = 1 := mul_inv_cancel₀ hn0.ne'
  have hinv0 : (0 : ℝ) ≤ ((n : ℝ))⁻¹ := by positivity
  have hd2 : (0 : ℝ) < 2 - ((k : ℝ) + 2) * ((n : ℝ))⁻¹ := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) - ((k : ℝ) + 2)) hinv0]
  have hd1 : (0 : ℝ) < 2 * (n : ℝ) - (k : ℝ) - 2 := by nlinarith
  rw [div_eq_div_iff (mul_ne_zero hk1 hd2.ne') (mul_ne_zero hk1 hd1.ne')]
  field_simp [hn0.ne']
  ring

/-- **Theorem 10 (`thm:Mlimit`) — negative-binomial limit of `M`.**
    Since `(3n-2) - A_M = h - 1` and `P(h = m) = B(n,m)/C_n`, the deficit from
    the worst case converges in law to `NB(2, 1/2)`: pointwise in `m`,
    `P((3n-2)-A_M = m) = P(h = m+1) → (m+1) 2^{-(m+2)}`.
    Proof: closed form at `m = 0` via the `centralBinom` recurrence, then a
    ladder of one-step `choose` ratios (`hProb_succ_eq`), inducting on `m`. -/
theorem thm_Mlimit (m : ℕ) :
    Tendsto (fun n : ℕ => hProb n (m + 1)) atTop (nhds (nbPMF m)) := by
  induction m with
  | zero =>
    have h0 : nbPMF 0 = 1 / 4 := by norm_num [nbPMF]
    rw [h0]
    exact hProb_one_tendsto
  | succ k ih =>
    have hlim := ih.mul (ratio_tendsto k)
    have hval : nbPMF k * (((k : ℝ) + 2) / (((k : ℝ) + 1) * 2)) = nbPMF (k + 1) := by
      have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      simp only [nbPMF]
      push_cast
      field_simp
      ring
    rw [hval] at hlim
    refine Filter.Tendsto.congr' ?_ hlim
    filter_upwards [eventually_ge_atTop (k + 3)] with n hn
    exact (hProb_succ_eq hn).symm

/-- **Corollary 7 asymptotics (`cor:avg`): `E[A_N] ∼ (9/4) n`.** -/
theorem EAN_asymp :
    Tendsto (fun n : ℕ => EAN n / (n : ℝ)) atTop (nhds (9 / 4)) := by
  -- term3 = (n-1)(n-2)/(2n(2n-1)) = (1-c)(1-2c)/(2(2-c)) → 1/4
  have ht3 : Tendsto (fun n : ℕ =>
      (1 - ((n : ℝ))⁻¹) * (1 - 2 * ((n : ℝ))⁻¹) / (2 * (2 - ((n : ℝ))⁻¹)))
      atTop (nhds (1 / 4)) :=
    tendsto_lim_eq
      (((tendsto_const_nhds.sub tendsto_inv_natCast).mul
        (tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_inv_natCast))).div
        (tendsto_const_nhds.mul (tendsto_const_nhds.sub tendsto_inv_natCast))
        (by norm_num))
      (by norm_num)
  -- term1 + (1+2c) + term3 → 1 + 1 + 1/4 = 9/4
  have hsum : Tendsto (fun n : ℕ =>
      (1 - ((n : ℝ))⁻¹) / (1 + 2 * ((n : ℝ))⁻¹) + (1 + 2 * ((n : ℝ))⁻¹)
        + (1 - ((n : ℝ))⁻¹) * (1 - 2 * ((n : ℝ))⁻¹) / (2 * (2 - ((n : ℝ))⁻¹)))
      atTop (nhds (9 / 4)) :=
    tendsto_lim_eq
      ((tendsto_ratio_one.add
        (tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_inv_natCast))).add ht3)
      (by norm_num)
  refine Filter.Tendsto.congr' ?_ hsum
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have hge1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2' : 2 * (n : ℝ) - 1 ≠ 0 := by
    have hx : (0 : ℝ) < 2 * (n : ℝ) - 1 := by nlinarith [hge1]
    exact hx.ne'
  simp only [EAN]
  field_simp [hn0.ne', h2, h2']

/-- **Mäkinen mean is `∼ 3n`.** -/
theorem EAM_asymp :
    Tendsto (fun n : ℕ => EAM n / (n : ℝ)) atTop (nhds 3) := by
  -- (1-c)/(1+2c) + 2 - c → 1 + 2 - 0 = 3
  have hsum : Tendsto (fun n : ℕ =>
      (1 - ((n : ℝ))⁻¹) / (1 + 2 * ((n : ℝ))⁻¹) + 2 - ((n : ℝ))⁻¹)
      atTop (nhds 3) :=
    tendsto_lim_eq
      ((tendsto_ratio_one.add tendsto_const_nhds).sub tendsto_inv_natCast)
      (by norm_num)
  refine Filter.Tendsto.congr' ?_ hsum
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  simp only [EAM]
  field_simp [hn0.ne', h2]

/-- **Theorem 9 (`thm:vardich`) — variance dichotomy, bounded side: `Var[A_M] = Var[S] → 4`.** -/
theorem VarS_asymp :
    Tendsto (fun n : ℕ => VarS n) atTop (nhds 4) := by
  -- numerator/n³ → 4
  have hN : Tendsto (fun n : ℕ => 2 * (2 + ((n : ℝ))⁻¹) * (1 - ((n : ℝ))⁻¹))
      atTop (nhds 4) :=
    tendsto_lim_eq
      ((tendsto_const_nhds.mul (tendsto_const_nhds.add tendsto_inv_natCast)).mul
        (tendsto_const_nhds.sub tendsto_inv_natCast))
      (by norm_num)
  -- denominator/n³ → 1
  have hD : Tendsto (fun n : ℕ => (1 + 2 * ((n : ℝ))⁻¹) ^ 2 * (1 + 3 * ((n : ℝ))⁻¹))
      atTop (nhds 1) :=
    tendsto_lim_eq
      (((tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_inv_natCast)).pow 2).mul
        (tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_inv_natCast)))
      (by norm_num)
  have hdiv := hN.div hD (by norm_num)
  rw [div_one] at hdiv
  refine Filter.Tendsto.congr' ?_ hdiv
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have h3 : (n : ℝ) + 3 ≠ 0 := by positivity
  simp only [VarS, Pi.div_apply]
  field_simp [hn0.ne', h2, h3]

/-- **Covariance limit (`thm:vardich` supporting): `Cov[S,P₂] → 1`.**  The
    exact covariance `2(n-1)(n-2)/((n+2)(2n-1))` (paper eq. for `Cov[S,P₂]`)
    tends to `1`; this is the cross term of the `Var[A_N] ∼ n/16` dichotomy. -/
theorem CovSP2_asymp :
    Tendsto (fun n : ℕ => CovSP2 n) atTop (nhds 1) := by
  have h : Tendsto (fun n : ℕ =>
      2 * (1 - ((n : ℝ))⁻¹) * (1 - 2 * ((n : ℝ))⁻¹)
        / ((1 + 2 * ((n : ℝ))⁻¹) * (2 - ((n : ℝ))⁻¹)))
      atTop (nhds 1) :=
    tendsto_lim_eq
      (((tendsto_const_nhds.mul (tendsto_const_nhds.sub tendsto_inv_natCast)).mul
        (tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_inv_natCast))).div
        ((tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_inv_natCast)).mul
          (tendsto_const_nhds.sub tendsto_inv_natCast)) (by norm_num))
      (by norm_num)
  refine Filter.Tendsto.congr' ?_ h
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have hge1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2' : 2 * (n : ℝ) - 1 ≠ 0 := by
    have hx : (0 : ℝ) < 2 * (n : ℝ) - 1 := by nlinarith [hge1]
    exact hx.ne'
  simp only [CovSP2]
  field_simp [hn0.ne', h2, h2']

/-- **Theorem 9 (`thm:vardich`) — variance dichotomy, linear side: `Var[A_N] ∼ n/16`.** -/
theorem VarAN_asymp :
    Tendsto (fun n : ℕ => VarAN n / (n : ℝ)) atTop (nhds (1 / 16)) := by
  -- Var[S]/n → 0 (Var[S] → 4 is bounded)
  have hS0 : Tendsto (fun n : ℕ => VarS n / (n : ℝ)) atTop (nhds 0) := by
    have h := Filter.Tendsto.mul VarS_asymp tendsto_inv_natCast
    simpa [div_eq_mul_inv] using h
  -- Cov[S,P₂] → 1, hence Cov/n → 0
  have hCov1 : Tendsto (fun n : ℕ => CovSP2 n) atTop (nhds 1) := CovSP2_asymp
  have hC0 : Tendsto (fun n : ℕ => CovSP2 n / (n : ℝ)) atTop (nhds 0) := by
    have h := Filter.Tendsto.mul hCov1 tendsto_inv_natCast
    simpa [div_eq_mul_inv] using h
  -- Var[P₂]/n → 1/16 (the substantive linear part)
  have hP2 : Tendsto (fun n : ℕ => VarP2 n / (n : ℝ)) atTop (nhds (1 / 16)) := by
    have h : Tendsto (fun n : ℕ =>
        (1 + ((n : ℝ))⁻¹) * (1 - ((n : ℝ))⁻¹) * (1 - 2 * ((n : ℝ))⁻¹)
          / (2 * (2 - ((n : ℝ))⁻¹) ^ 2 * (2 - 3 * ((n : ℝ))⁻¹)))
        atTop (nhds (1 / 16)) :=
      tendsto_lim_eq
        ((((tendsto_const_nhds.add tendsto_inv_natCast).mul
          (tendsto_const_nhds.sub tendsto_inv_natCast)).mul
          (tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_inv_natCast))).div
          ((tendsto_const_nhds.mul
            ((tendsto_const_nhds.sub tendsto_inv_natCast).pow 2)).mul
            (tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_inv_natCast)))
          (by norm_num))
        (by norm_num)
    refine Filter.Tendsto.congr' ?_ h
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hge2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have h2' : 2 * (n : ℝ) - 1 ≠ 0 := by
      have hx : (0 : ℝ) < 2 * (n : ℝ) - 1 := by nlinarith [hge2]
      exact hx.ne'
    have h3' : 2 * (n : ℝ) - 3 ≠ 0 := by
      have hx : (0 : ℝ) < 2 * (n : ℝ) - 3 := by nlinarith [hge2]
      exact hx.ne'
    simp only [VarP2]
    field_simp [hn0.ne', h2', h3']
  -- Var[A_N]/n = Var[S]/n + Var[P₂]/n + 2·(Cov/n) → 0 + 1/16 + 0
  have hsum : Tendsto (fun n : ℕ =>
      VarS n / (n : ℝ) + VarP2 n / (n : ℝ) + 2 * (CovSP2 n / (n : ℝ)))
      atTop (nhds (1 / 16)) :=
    tendsto_lim_eq ((hS0.add hP2).add (tendsto_const_nhds.mul hC0)) (by norm_num)
  refine Filter.Tendsto.congr' ?_ hsum
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [VarAN]
  field_simp [hn0.ne']

/-!
### Lemma 2: the closed form is the counting proportion

`MakinenAnalysis.BallotCount` supplies the codeword model (`suffixes`, `hw`)
and the reflection count (`W_add_choose`).  Here we cast those counts to ℝ and
identify them with `ballot` and `catalan`, obtaining Lemma 2 on the codeword
sample space: `hProb n m = #(hw (n-1) 1 m) / #(suffixes (n-1) 1)`.
Together with the Rocq-side `bijection_decode_encode` (trees ↔ valid codewords)
and `height_eq_n_minus_S` (`h = n - S`), this machine-checks the paper's
Lemma 2 across the two systems.
-/

/-- The sample space has the right size: valid codewords of length `n-1`
    number `catalan n`. -/
theorem card_suffixes_eq_catalan (n : ℕ) (hn : 1 ≤ n) :
    (suffixes (n - 1) 1).card = catalan n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [show j + 1 - 1 = j by omega, card_suffixes]
  -- W (j+1) 1 1 + C(2j+1, j+2) = C(2j+1, j)
  have hW := W_add_choose j 1 1 le_rfl (by omega)
  rw [show 2 * j + 1 + 1 - 1 = 2 * j + 1 by omega,
      show j + 1 + 1 = j + 2 by omega] at hW
  -- centralBinom (j+1) = C(2j+1, j) + C(2j+1, j+1)   (Pascal)
  have hP : Nat.centralBinom (j + 1) = (2 * j + 1).choose j + (2 * j + 1).choose (j + 1) := by
    rw [Nat.centralBinom_eq_two_mul_choose,
        show 2 * (j + 1) = (2 * j + 1) + 1 by omega, Nat.choose_succ_succ']
  -- C(2j+1, j) = C(2j+1, j+1)   (symmetry)
  have hS : (2 * j + 1).choose j = (2 * j + 1).choose (j + 1) := by
    have h := Nat.choose_symm (show j + 1 ≤ 2 * j + 1 by omega)
    rwa [show 2 * j + 1 - (j + 1) = j by omega] at h
  -- C(2j+1, j+2)·(j+2) = C(2j+1, j+1)·j   (one-step ratio)
  have hR : (2 * j + 1).choose (j + 2) * (j + 2) = (2 * j + 1).choose (j + 1) * j := by
    have h := Nat.choose_succ_right_eq (2 * j + 1) (j + 1)
    rwa [show 2 * j + 1 - (j + 1) = j by omega] at h
  -- (j+2)·catalan (j+1) = centralBinom (j+1)
  have hcat := succ_mul_catalan_eq_centralBinom (j + 1)
  rw [show j + 1 + 1 = j + 2 by omega] at hcat
  -- assemble over ℝ and cancel (j+2)
  have hWR : (W (j + 1) 1 1 : ℝ) + ((2 * j + 1).choose (j + 2) : ℝ)
      = ((2 * j + 1).choose j : ℝ) := by exact_mod_cast hW
  have hPR : (Nat.centralBinom (j + 1) : ℝ)
      = ((2 * j + 1).choose j : ℝ) + ((2 * j + 1).choose (j + 1) : ℝ) := by
    exact_mod_cast hP
  have hSR : ((2 * j + 1).choose j : ℝ) = ((2 * j + 1).choose (j + 1) : ℝ) := by
    exact_mod_cast hS
  have hRR : ((2 * j + 1).choose (j + 2) : ℝ) * ((j : ℝ) + 2)
      = ((2 * j + 1).choose (j + 1) : ℝ) * (j : ℝ) := by exact_mod_cast hR
  have hcatR : ((j : ℝ) + 2) * (catalan (j + 1) : ℝ)
      = (Nat.centralBinom (j + 1) : ℝ) := by exact_mod_cast hcat
  have key : ((j : ℝ) + 2) * (W (j + 1) 1 1 : ℝ)
      = ((j : ℝ) + 2) * (catalan (j + 1) : ℝ) := by
    linear_combination ((j : ℝ) + 2) * hWR - hRR - hcatR - hPR + ((j : ℝ) + 1) * hSR
  exact_mod_cast mul_left_cancel₀ (by positivity : ((j : ℝ) + 2) ≠ 0) key

/-- The height-`m` count of valid codewords is exactly the ballot closed form:
    `#(hw (n-1) 1 m) = B(n,m) = (m/n)·C(2n-m-1, n-1)` over ℝ. -/
theorem W_cast_eq_ballot {n m : ℕ} (h1 : 1 ≤ m) (hmn : m ≤ n) :
    (W (n - 1) 1 m : ℝ) = ballot n m := by
  by_cases hnm : m = n
  · -- maximal height: the all-zero word, count 1; ballot n n = 1
    subst hnm
    have hWm : W (m - 1) 1 m = 1 := by
      have h := W_max (m - 1) 1
      rwa [show m - 1 + 1 = m by omega] at h
    rw [hWm]
    simp only [ballot]
    rw [show 2 * m - m - 1 = m - 1 by omega, Nat.choose_self]
    have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp [div_self hm0]
  · -- 1 ≤ m ≤ n-1, so n = k+2
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [show k + 2 - 1 = k + 1 by omega]
    -- W (k+1) 1 m + C(2k+2-m, k+2) = C(2k+2-m, k)
    have hW := W_add_choose k 1 m h1 (by omega)
    rw [show 2 * k + 1 + 1 - m = 2 * k + 2 - m by omega,
        show k + 1 + 1 = k + 2 by omega] at hW
    -- Pascal: C(2k+3-m, k+1) = C(2k+2-m, k) + C(2k+2-m, k+1)
    have hP : (2 * k + 3 - m).choose (k + 1)
        = (2 * k + 2 - m).choose k + (2 * k + 2 - m).choose (k + 1) := by
      rw [show 2 * k + 3 - m = (2 * k + 2 - m) + 1 by omega, Nat.choose_succ_succ']
    -- ratios
    have hZ : (2 * k + 2 - m).choose (k + 1) * (k + 1)
        = (2 * k + 2 - m).choose k * (k + 2 - m) := by
      have h := Nat.choose_succ_right_eq (2 * k + 2 - m) k
      rwa [show 2 * k + 2 - m - k = k + 2 - m by omega] at h
    have hY : (2 * k + 2 - m).choose (k + 2) * (k + 2)
        = (2 * k + 2 - m).choose (k + 1) * (k + 1 - m) := by
      have h := Nat.choose_succ_right_eq (2 * k + 2 - m) (k + 1)
      rwa [show 2 * k + 2 - m - (k + 1) = k + 1 - m by omega] at h
    -- ℝ casts (m ≤ k+1 makes all the ℕ-subtractions real)
    have hWR : (W (k + 1) 1 m : ℝ) + ((2 * k + 2 - m).choose (k + 2) : ℝ)
        = ((2 * k + 2 - m).choose k : ℝ) := by exact_mod_cast hW
    have hPR : ((2 * k + 3 - m).choose (k + 1) : ℝ)
        = ((2 * k + 2 - m).choose k : ℝ) + ((2 * k + 2 - m).choose (k + 1) : ℝ) := by
      exact_mod_cast hP
    have hc1 : ((k + 2 - m : ℕ) : ℝ) = (k : ℝ) + 2 - m := by
      have : (m : ℕ) ≤ k + 2 := by omega
      rw [Nat.cast_sub this]; push_cast; ring
    have hc2 : ((k + 1 - m : ℕ) : ℝ) = (k : ℝ) + 1 - m := by
      have : (m : ℕ) ≤ k + 1 := by omega
      rw [Nat.cast_sub this]; push_cast; ring
    have hZR : ((2 * k + 2 - m).choose (k + 1) : ℝ) * ((k : ℝ) + 1)
        = ((2 * k + 2 - m).choose k : ℝ) * ((k : ℝ) + 2 - m) := by
      rw [← hc1]; exact_mod_cast hZ
    have hYR : ((2 * k + 2 - m).choose (k + 2) : ℝ) * ((k : ℝ) + 2)
        = ((2 * k + 2 - m).choose (k + 1) : ℝ) * ((k : ℝ) + 1 - m) := by
      rw [← hc2]; exact_mod_cast hY
    -- assemble and cancel (k+1)
    have key : ((k : ℝ) + 1) * (((k : ℝ) + 2) * (W (k + 1) 1 m : ℝ))
        = ((k : ℝ) + 1) * ((m : ℝ) * ((2 * k + 3 - m).choose (k + 1) : ℝ)) := by
      linear_combination ((k : ℝ) + 1) * ((k : ℝ) + 2) * hWR - ((k : ℝ) + 1) * hYR
        - ((k : ℝ) + 1) * hZR - (m : ℝ) * ((k : ℝ) + 1) * hPR
    have key2 := mul_left_cancel₀ (by positivity : ((k : ℝ) + 1) ≠ 0) key
    simp only [ballot]
    rw [show 2 * (k + 2) - m - 1 = 2 * k + 3 - m by omega,
        show k + 2 - 1 = k + 1 by omega]
    push_cast
    have hk2 : ((k : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    linear_combination key2

/-- **Lemma 2 (`lem:ballot`) on the codeword sample space.**  The closed-form
    probability `hProb n m = B(n,m)/C_n` is the literal counting proportion of
    valid codewords with final stack height `m` among all `catalan n` valid
    codewords of length `n-1`.  (Trees ↔ codewords and `h = n - S` are
    machine-checked in the Rocq development.) -/
theorem hProb_eq_count {n m : ℕ} (h1 : 1 ≤ m) (hmn : m ≤ n) :
    hProb n m = ((hw (n - 1) 1 m).card : ℝ) / ((suffixes (n - 1) 1).card : ℝ) := by
  rw [card_hw, card_suffixes_eq_catalan n (le_trans h1 hmn), W_cast_eq_ballot h1 hmn]
  rfl

/-- **Theorem 10, fully combinatorial.**  The literal counting proportions
    converge to the negative-binomial pmf — the caveat on `thm_Mlimit` is
    discharged on the codeword sample space. -/
theorem thm_Mlimit_count (m : ℕ) :
    Tendsto (fun n : ℕ => ((hw (n - 1) 1 (m + 1)).card : ℝ) /
        ((suffixes (n - 1) 1).card : ℝ)) atTop (nhds (nbPMF m)) := by
  refine Filter.Tendsto.congr' ?_ (thm_Mlimit m)
  filter_upwards [eventually_ge_atTop (m + 1)] with n hn
  exact hProb_eq_count (by omega) hn

/-!
### What remains

**Proposition 12 (`prop:leafclt`)** and **Theorem 13 (`thm:Nclt`)** — the two
CLTs — are stated precisely (as `proof_wanted` targets at the
characteristic-function level, with the refined counting infrastructure
proved) in `MakinenAnalysis.LeafCount`.
-/

end

end MakinenAnalysis
