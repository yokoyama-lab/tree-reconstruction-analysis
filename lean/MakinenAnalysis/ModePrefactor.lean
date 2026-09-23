import Mathlib
import MakinenAnalysis.LocalLimit
import MakinenAnalysis.LocalCLTGauss

/-!
# The centred Gaussian sum (self-normalisation brick)

This file proves the **centred Gaussian-sum limit**

  `(∑_{k<n} exp(-8(k - n/4)²/n)) / √n → √(π/8)`   (`centred_gaussian_sum_tendsto`),

the two-sided companion of `LocalCLTGauss.gaussian_sum_div_sqrt_tendsto`
(`(∑_{s<n} exp(-8 s²/n))/√n → √(π/32)`).  Where the one-sided brick sums a
*monotone* summand centred at `0`, here the summand is *unimodal* centred at the
mode `n/4`, so the argument is a direct integral bracketing of the whole line by
the sum over `range n`, split once at the peak `⌊n/4⌋`:

* the full-line integral `∫ exp(-(8/n)(x-n/4)²) dx = √n·√(π/8)` (`integral_H`,
  by translation invariance and `integral_gaussian`);
* a pointwise Riemann comparison of the sum and the integral on the increasing
  part `[0, ⌊n/4⌋]` and the decreasing part `[⌊n/4⌋+1, n]`, peeling the two
  peak terms (each `≤ 1`);
* `O(1)` tail integrals `∫_{Iic 0}, ∫_{Ioi n} ≤ 1` (`tail_Iic`, `tail_Ioi`),
  bounded by `exp` majorants.

The result brackets the sum as `√n·√(π/8) - 4 ≤ ∑ ≤ √n·√(π/8) + 2` for `n ≥ 16`,
whence the `√(π/8)` limit after dividing by `√n`.

This is the exact Gaussian constant against which the mode value of `pmf'`
self-normalises: two-sided total mass `√(π/8) = 2·√(π/32)`.  It is the standalone
analytic input (Deliverable 1) toward the prefactor limit
`σ(n)·pmf'(n, ⌊n/4⌋) → 1/√(2π)`; the pmf'-side window/tail self-normalisation is
*not* proved here (see the report).  Zero `sorry`s.
-/

open Filter Set MeasureTheory Topology

namespace MakinenAnalysis

/-- Centred Gaussian integrand `x ↦ exp(-(8/n)(x - n/4)²)`. -/
private noncomputable def H (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-(8 / (n : ℝ)) * (x - (n : ℝ) / 4) ^ 2)

private lemma H_nonneg (n : ℕ) (x : ℝ) : 0 ≤ H n x := (Real.exp_pos _).le

private lemma H_le_one (n : ℕ) (x : ℝ) : H n x ≤ 1 := by
  simp only [H]
  rw [show (1 : ℝ) = Real.exp 0 by simp]
  refine Real.exp_le_exp.2 ?_
  rw [neg_mul]
  exact neg_nonpos.mpr (by positivity)

/-- Monotone comparison: closer to the centre ⇒ larger value. -/
private lemma H_le_H (n : ℕ) {x y : ℝ}
    (h : (x - (n : ℝ) / 4) ^ 2 ≤ (y - (n : ℝ) / 4) ^ 2) : H n y ≤ H n x := by
  simp only [H]
  refine Real.exp_le_exp.2 ?_
  have hb : (0 : ℝ) ≤ 8 / (n : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h hb]

private lemma H_integrable {n : ℕ} (hn : 1 ≤ n) : Integrable (H n) := by
  have hb : (0 : ℝ) < 8 / (n : ℝ) := by
    have : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    positivity
  exact (integrable_exp_neg_mul_sq hb).comp_sub_right ((n : ℝ) / 4)

private lemma H_shift_integrable {n : ℕ} (hn : 1 ≤ n) :
    Integrable (fun x => H n (x - 1)) :=
  (H_integrable hn).comp_sub_right 1

/-- The full-line integral: `∫ H n = √n · √(π/8)`. -/
private lemma integral_H {n : ℕ} (hn : 1 ≤ n) :
    ∫ x, H n x = Real.sqrt n * Real.sqrt (Real.pi / 8) := by
  have hN0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hshift : ∫ x, H n x = ∫ x : ℝ, Real.exp (-(8 / (n : ℝ)) * x ^ 2) :=
    integral_sub_right_eq_self
      (fun x : ℝ => Real.exp (-(8 / (n : ℝ)) * x ^ 2)) ((n : ℝ) / 4)
  rw [hshift, integral_gaussian,
    show Real.pi / (8 / (n : ℝ)) = (n : ℝ) * (Real.pi / 8) by
      rw [div_div_eq_mul_div]; ring,
    Real.sqrt_mul (Nat.cast_nonneg n)]

/-- Right tail: `∫_{Ioi n} H n ≤ 1`. -/
private lemma tail_Ioi {n : ℕ} (hn : 1 ≤ n) : ∫ x in Ioi (n : ℝ), H n x ≤ 1 := by
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have h1 : ∫ x in Ioi (n : ℝ), H n x ≤ ∫ x in Ioi (n : ℝ), Real.exp (-x) := by
    apply setIntegral_mono_on (H_integrable hn).integrableOn
      (by simpa using exp_neg_integrableOn_Ioi (n : ℝ) one_pos) measurableSet_Ioi
    intro x hx
    have hx' : (n : ℝ) < x := mem_Ioi.mp hx
    simp only [H]
    refine Real.exp_le_exp.2 ?_
    rw [neg_mul, neg_le_neg_iff, div_mul_eq_mul_div, le_div_iff₀ hN0]
    nlinarith [hx', hN0]
  have h2 : ∫ x in Ioi (n : ℝ), Real.exp (-x) = Real.exp (-(n : ℝ)) := integral_exp_neg_Ioi _
  have h3 : Real.exp (-(n : ℝ)) ≤ 1 := by
    calc Real.exp (-(n : ℝ)) ≤ Real.exp 0 := Real.exp_le_exp.2 (by linarith)
      _ = 1 := Real.exp_zero
  linarith

/-- Left tail: `∫_{Iic 0} H n ≤ 1`. -/
private lemma tail_Iic {n : ℕ} (hn : 1 ≤ n) : ∫ x in Iic (0 : ℝ), H n x ≤ 1 := by
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have h1 : ∫ x in Iic (0 : ℝ), H n x ≤ ∫ x in Iic (0 : ℝ), Real.exp x := by
    apply setIntegral_mono_on (H_integrable hn).integrableOn
      (integrableOn_exp_Iic 0) measurableSet_Iic
    intro x hx
    have hx' : x ≤ 0 := mem_Iic.mp hx
    simp only [H]
    refine Real.exp_le_exp.2 ?_
    have hkey : (0 : ℝ) ≤ x * (n : ℝ) + 8 * (x - (n : ℝ) / 4) ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -x) hN0.le, sq_nonneg x, hN0]
    have hdiv : (0 : ℝ) ≤ x + 8 / (n : ℝ) * (x - (n : ℝ) / 4) ^ 2 := by
      have h := div_nonneg hkey hN0.le
      have heq : (x * (n : ℝ) + 8 * (x - (n : ℝ) / 4) ^ 2) / (n : ℝ)
          = x + 8 / (n : ℝ) * (x - (n : ℝ) / 4) ^ 2 := by field_simp
      rwa [heq] at h
    rw [neg_mul]
    linarith
  have h2 : ∫ x in Iic (0 : ℝ), Real.exp x = 1 := integral_exp_Iic_zero
  linarith

/-- Lower decomposition: the full integral is at most the two window integrals
plus a bounded remainder. -/
private lemma I_ge {n : ℕ} (hn : 16 ≤ n) :
    Real.sqrt n * Real.sqrt (Real.pi / 8)
      ≤ (∫ x in (-1 : ℝ)..((⌊(n:ℝ)/4⌋₊ : ℝ) - 1), H n x)
        + (∫ x in ((⌊(n:ℝ)/4⌋₊ : ℝ) + 1)..(n : ℝ), H n x) + 4 := by
  have hn1 : 1 ≤ n := by omega
  have hN0 : (0 : ℝ) < n := by
    have h16 : (16:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set p := (⌊(n:ℝ)/4⌋₊ : ℝ) with hp
  have hp_le : p ≤ (n:ℝ)/4 := Nat.floor_le (by positivity)
  have hpn : p + 1 ≤ (n:ℝ) := by
    have : (16:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [hp_le]
  have hp0 : (0:ℝ) ≤ p := by positivity
  have hintOn : ∀ s : Set ℝ, IntegrableOn (H n) s := fun s => (H_integrable hn1).integrableOn
  -- split at -1
  have e1 : ∫ x, H n x = (∫ x in Iic (-1:ℝ), H n x) + ∫ x in Ioi (-1:ℝ), H n x :=
    (intervalIntegral.integral_Iic_add_Ioi (hintOn _) (hintOn _)).symm
  -- split Ioi(-1) at p+1
  have e2 : ∫ x in Ioi (-1:ℝ), H n x
      = (∫ x in Ioc (-1:ℝ) (p+1), H n x) + ∫ x in Ioi (p+1), H n x := by
    rw [← Ioc_union_Ioi_eq_Ioi (by linarith : (-1:ℝ) ≤ p+1)]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi (hintOn _) (hintOn _)
  -- split Ioi(p+1) at n
  have e3 : ∫ x in Ioi (p+1), H n x
      = (∫ x in Ioc (p+1) (n:ℝ), H n x) + ∫ x in Ioi (n:ℝ), H n x := by
    rw [← Ioc_union_Ioi_eq_Ioi hpn]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi (hintOn _) (hintOn _)
  -- interval integrals
  have e4 : ∫ x in Ioc (-1:ℝ) (p+1), H n x = ∫ x in (-1:ℝ)..(p+1), H n x :=
    (intervalIntegral.integral_of_le (by linarith)).symm
  have e5 : ∫ x in Ioc (p+1) (n:ℝ), H n x = ∫ x in (p+1)..(n:ℝ), H n x :=
    (intervalIntegral.integral_of_le hpn).symm
  have e6 : ∫ x in (-1:ℝ)..(p+1), H n x
      = (∫ x in (-1:ℝ)..(p-1), H n x) + ∫ x in (p-1)..(p+1), H n x :=
    (intervalIntegral.integral_add_adjacent_intervals
      (H_integrable hn1).intervalIntegrable (H_integrable hn1).intervalIntegrable).symm
  -- bounds on the three remainder pieces
  have bIic : ∫ x in Iic (-1:ℝ), H n x ≤ 1 := by
    calc ∫ x in Iic (-1:ℝ), H n x ≤ ∫ x in Iic (0:ℝ), H n x := by
          apply setIntegral_mono_set (hintOn _)
            (Filter.Eventually.of_forall (H_nonneg n))
          exact (HasSubset.Subset.eventuallyLE (Iic_subset_Iic.mpr (by norm_num)))
      _ ≤ 1 := tail_Iic hn1
  have bMid : ∫ x in (p-1)..(p+1), H n x ≤ 2 := by
    calc ∫ x in (p-1)..(p+1), H n x ≤ ∫ _ in (p-1)..(p+1), (1:ℝ) := by
          apply intervalIntegral.integral_mono_on (by linarith)
            (H_integrable hn1).intervalIntegrable intervalIntegrable_const
          intro x _; exact H_le_one n x
      _ = 2 := by rw [intervalIntegral.integral_const]; norm_num
  have bIoi : ∫ x in Ioi (n:ℝ), H n x ≤ 1 := tail_Ioi hn1
  rw [integral_H hn1] at e1
  rw [e1, e2, e3, e4, e5, e6]
  linarith [bIic, bMid, bIoi]

/-- Upper decomposition: the two window integrals are at most the full integral. -/
private lemma two_integrals_le {n : ℕ} (hn : 16 ≤ n) :
    (∫ x in (0:ℝ)..(⌊(n:ℝ)/4⌋₊ : ℝ), H n x)
      + (∫ x in ((⌊(n:ℝ)/4⌋₊ : ℝ) + 1)..((n:ℝ) - 1), H n x)
      ≤ Real.sqrt n * Real.sqrt (Real.pi / 8) := by
  have hn1 : 1 ≤ n := by omega
  have hN0 : (0 : ℝ) < n := by
    have h16 : (16:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set p := (⌊(n:ℝ)/4⌋₊ : ℝ) with hp
  have hp_le : p ≤ (n:ℝ)/4 := Nat.floor_le (by positivity)
  have hp0 : (0:ℝ) ≤ p := by positivity
  have hpn1 : p + 1 ≤ (n:ℝ) - 1 := by
    have : (16:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [hp_le]
  have hintOn : ∀ s : Set ℝ, IntegrableOn (H n) s := fun s => (H_integrable hn1).integrableOn
  -- convert interval integrals to Ioc
  have e1 : ∫ x in (0:ℝ)..(p), H n x = ∫ x in Ioc (0:ℝ) p, H n x :=
    intervalIntegral.integral_of_le hp0
  have e2 : ∫ x in (p+1)..((n:ℝ)-1), H n x = ∫ x in Ioc (p+1) ((n:ℝ)-1), H n x :=
    intervalIntegral.integral_of_le (by linarith)
  -- disjoint union
  have hdisj : Disjoint (Ioc (0:ℝ) p) (Ioc (p+1) ((n:ℝ)-1)) := by
    apply Set.disjoint_left.mpr
    rintro x hx1 hx2
    exact absurd (mem_Ioc.mp hx2).1 (by have := (mem_Ioc.mp hx1).2; linarith)
  have hunion : (∫ x in Ioc (0:ℝ) p, H n x) + (∫ x in Ioc (p+1) ((n:ℝ)-1), H n x)
      = ∫ x in (Ioc (0:ℝ) p ∪ Ioc (p+1) ((n:ℝ)-1)), H n x :=
    (setIntegral_union hdisj measurableSet_Ioc (hintOn _) (hintOn _)).symm
  rw [e1, e2, hunion, ← integral_H hn1]
  exact setIntegral_le_integral (H_integrable hn1) (Filter.Eventually.of_forall (H_nonneg n))

private lemma sum_lower {n : ℕ} (hn : 16 ≤ n) :
    (∫ x in (-1:ℝ)..((⌊(n:ℝ)/4⌋₊:ℝ)-1), H n x)
      + (∫ x in ((⌊(n:ℝ)/4⌋₊:ℝ)+1)..(n:ℝ), H n x)
      ≤ ∑ k ∈ Finset.range n, H n k := by
  have hn1 : 1 ≤ n := by omega
  have hN0 : (0:ℝ) < n := by have : (16:ℝ) ≤ n := by exact_mod_cast hn
                             linarith
  set m₀ := ⌊(n:ℝ)/4⌋₊ with hm0
  set c := (n:ℝ)/4 with hc
  have hpc : (m₀:ℝ) ≤ c := Nat.floor_le (by positivity)
  have hcp : c < (m₀:ℝ) + 1 := Nat.lt_floor_add_one _
  have h16 : (16:ℝ) ≤ n := by exact_mod_cast hn
  have hm2R : (m₀:ℝ) + 2 ≤ n := by rw [hc] at hpc; nlinarith
  have hm2n : m₀ + 2 ≤ n := by exact_mod_cast (by push_cast; linarith : ((m₀+2:ℕ):ℝ) ≤ (n:ℝ))
  -- increasing part: ∫_{-1}^{m₀-1} H ≤ ∑_{Ico 0 m₀} H
  have linc : (∫ x in (-1:ℝ)..((m₀:ℝ)-1), H n x) ≤ ∑ k ∈ Finset.Ico 0 m₀, H n k := by
    have key := integral_le_sum_Ico_of_le (f := fun x => H n x)
      (g := fun x => H n (x - 1)) (a := 0) (b := m₀) (Nat.zero_le m₀)
      (by
        intro i hi x hx
        rw [Set.mem_Ico] at hi
        rw [Set.mem_Ico] at hx
        have hilt : (i:ℝ) < (m₀:ℝ) := by exact_mod_cast hi.2
        have hic : (i:ℝ) ≤ c := by linarith [hpc]
        have hxu : x < (i:ℝ) + 1 := by exact_mod_cast hx.2
        refine H_le_H n ?_
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (i:ℝ) - (x - 1))
          (by linarith : (0:ℝ) ≤ 2 * c - (x - 1) - (i:ℝ))])
      (H_shift_integrable hn1).integrableOn
    rw [intervalIntegral.integral_comp_sub_right (H n) 1] at key
    simpa using key
  -- decreasing part: ∫_{m₀+1}^n H ≤ ∑_{Ico (m₀+1) n} H
  have ldec : (∫ x in ((m₀:ℝ)+1)..(n:ℝ), H n x) ≤ ∑ k ∈ Finset.Ico (m₀+1) n, H n k := by
    have key := integral_le_sum_Ico_of_le (f := fun x => H n x)
      (g := fun x => H n x) (a := m₀+1) (b := n) (by omega)
      (by
        intro i hi x hx
        rw [Set.mem_Ico] at hi
        rw [Set.mem_Ico] at hx
        have hci : c < (i:ℝ) := by
          have : (m₀:ℝ) + 1 ≤ (i:ℝ) := by exact_mod_cast hi.1
          linarith [hcp]
        have hix : (i:ℝ) ≤ x := hx.1
        refine H_le_H n ?_
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x - (i:ℝ))
          (by linarith : (0:ℝ) ≤ x + (i:ℝ) - 2 * c)])
      (H_integrable hn1).integrableOn
    have hcast : (∫ x in ((m₀+1:ℕ):ℝ)..(n:ℝ), H n x)
        = ∫ x in ((m₀:ℝ)+1)..(n:ℝ), H n x := by push_cast; ring_nf
    rw [hcast] at key
    exact key
  -- combine: drop the middle term H n m₀ ≥ 0
  have hdisj : Disjoint (Finset.Ico 0 m₀) (Finset.Ico (m₀+1) n) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_Ico] at ha hb; omega
  have hsub : Finset.Ico 0 m₀ ∪ Finset.Ico (m₀+1) n ⊆ Finset.range n := by
    intro a ha
    rw [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico] at ha
    rw [Finset.mem_range]; omega
  have hunion : (∑ k ∈ Finset.Ico 0 m₀, H n k) + ∑ k ∈ Finset.Ico (m₀+1) n, H n k
      = ∑ k ∈ (Finset.Ico 0 m₀ ∪ Finset.Ico (m₀+1) n), H n k :=
    (Finset.sum_union hdisj).symm
  have hle : (∑ k ∈ (Finset.Ico 0 m₀ ∪ Finset.Ico (m₀+1) n), H n k)
      ≤ ∑ k ∈ Finset.range n, H n k :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => H_nonneg n i)
  calc (∫ x in (-1:ℝ)..((m₀:ℝ)-1), H n x) + ∫ x in ((m₀:ℝ)+1)..(n:ℝ), H n x
      ≤ (∑ k ∈ Finset.Ico 0 m₀, H n k) + ∑ k ∈ Finset.Ico (m₀+1) n, H n k :=
        add_le_add linc ldec
    _ = ∑ k ∈ (Finset.Ico 0 m₀ ∪ Finset.Ico (m₀+1) n), H n k := hunion
    _ ≤ ∑ k ∈ Finset.range n, H n k := hle

private lemma sum_upper {n : ℕ} (hn : 16 ≤ n) :
    ∑ k ∈ Finset.range n, H n k
      ≤ (∫ x in (0:ℝ)..(⌊(n:ℝ)/4⌋₊:ℝ), H n x)
        + (∫ x in ((⌊(n:ℝ)/4⌋₊:ℝ)+1)..((n:ℝ)-1), H n x) + 2 := by
  have hn1 : 1 ≤ n := by omega
  have hN0 : (0:ℝ) < n := by have : (16:ℝ) ≤ n := by exact_mod_cast hn
                             linarith
  set m₀ := ⌊(n:ℝ)/4⌋₊ with hm0
  set c := (n:ℝ)/4 with hc
  have hpc : (m₀:ℝ) ≤ c := Nat.floor_le (by positivity)
  have hcp : c < (m₀:ℝ) + 1 := Nat.lt_floor_add_one _
  have h16 : (16:ℝ) ≤ n := by exact_mod_cast hn
  have hm2R : (m₀:ℝ) + 2 ≤ n := by rw [hc] at hpc; nlinarith
  have hm2n : m₀ + 2 ≤ n := by exact_mod_cast (by push_cast; linarith : ((m₀+2:ℕ):ℝ) ≤ (n:ℝ))
  -- increasing upper: ∑_{Ico 0 m₀} H ≤ ∫_0^{m₀} H
  have uinc : (∑ k ∈ Finset.Ico 0 m₀, H n k) ≤ ∫ x in (0:ℝ)..(m₀:ℝ), H n x := by
    have key := sum_Ico_le_integral_of_le (f := fun x => H n x)
      (g := fun x => H n x) (a := 0) (b := m₀) (Nat.zero_le m₀)
      (by
        intro i hi x hx
        rw [Set.mem_Ico] at hi
        rw [Set.mem_Ico] at hx
        have hilt : (i:ℝ) < (m₀:ℝ) := by exact_mod_cast hi.2
        have him1 : (i:ℝ) + 1 ≤ (m₀:ℝ) := by
          have : i + 1 ≤ m₀ := hi.2
          exact_mod_cast this
        have hic : (i:ℝ) ≤ c := by linarith [hpc]
        have hxu : x < (i:ℝ) + 1 := by exact_mod_cast hx.2
        have hxc : x ≤ c := by linarith
        refine H_le_H n ?_
        nlinarith [mul_nonneg (by linarith [hx.1] : (0:ℝ) ≤ x - (i:ℝ))
          (by linarith : (0:ℝ) ≤ 2 * c - (i:ℝ) - x)])
      (H_integrable hn1).integrableOn
    simpa using key
  -- decreasing upper: ∑_{Ico (m₀+2) n} H ≤ ∫_{m₀+1}^{n-1} H
  have udec : (∑ k ∈ Finset.Ico (m₀+2) n, H n k) ≤ ∫ x in ((m₀:ℝ)+1)..((n:ℝ)-1), H n x := by
    have key := sum_Ico_le_integral_of_le (f := fun x => H n x)
      (g := fun x => H n (x - 1)) (a := m₀+2) (b := n) (by omega)
      (by
        intro i hi x hx
        rw [Set.mem_Ico] at hi
        rw [Set.mem_Ico] at hx
        have hi1 : (m₀:ℝ) + 2 ≤ (i:ℝ) := by exact_mod_cast hi.1
        have hxl : (i:ℝ) ≤ x := hx.1
        have hxu : x < (i:ℝ) + 1 := by exact_mod_cast hx.2
        refine H_le_H n ?_
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (i:ℝ) - (x - 1))
          (by linarith [hcp] : (0:ℝ) ≤ (i:ℝ) + (x - 1) - 2 * c)])
      (H_shift_integrable hn1).integrableOn
    rw [intervalIntegral.integral_comp_sub_right (H n) 1] at key
    have hb : ((m₀+2:ℕ):ℝ) - 1 = (m₀:ℝ) + 1 := by push_cast; ring
    rw [hb] at key
    exact key
  -- decompose the range sum
  have hdecomp : ∑ k ∈ Finset.range n, H n k
      = (∑ k ∈ Finset.Ico 0 m₀, H n k)
        + (∑ k ∈ Finset.Ico m₀ (m₀+2), H n k)
        + ∑ k ∈ Finset.Ico (m₀+2) n, H n k := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive (H n ·) (Nat.zero_le m₀) (by omega : m₀ ≤ n),
      ← Finset.sum_Ico_consecutive (H n ·) (by omega : m₀ ≤ m₀ + 2) hm2n]
    ring
  -- middle two terms ≤ 2
  have hmid : (∑ k ∈ Finset.Ico m₀ (m₀+2), H n k) ≤ 2 := by
    calc (∑ k ∈ Finset.Ico m₀ (m₀+2), H n k)
        ≤ (Finset.Ico m₀ (m₀+2)).card • (1:ℝ) :=
          Finset.sum_le_card_nsmul _ _ _ (fun i _ => H_le_one n i)
      _ = 2 := by rw [Nat.card_Ico]; simp
  -- combine
  rw [hdecomp]
  linarith [uinc, udec, hmid]

/-- **The centred Gaussian sum.**  `(∑_{k<n} exp(-8(k-n/4)²/n)) / √n → √(π/8)`. -/
theorem centred_gaussian_sum_tendsto :
    Tendsto (fun n : ℕ =>
        (∑ k ∈ Finset.range n, Real.exp (-8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n)) / Real.sqrt n)
      atTop (𝓝 (Real.sqrt (Real.pi / 8))) := by
  have hbridge : ∀ n : ℕ,
      (∑ k ∈ Finset.range n, Real.exp (-8 * ((k : ℝ) - (n : ℝ) / 4) ^ 2 / n))
        = ∑ k ∈ Finset.range n, H n k := by
    intro n
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [H]; congr 1; ring
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hsq : Tendsto (fun n : ℕ => 1 / Real.sqrt n) atTop (𝓝 0) := by
    simpa [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hsqrt
  have hlo : Tendsto (fun n : ℕ => Real.sqrt (Real.pi / 8) - 4 * (1 / Real.sqrt n))
      atTop (𝓝 (Real.sqrt (Real.pi / 8))) := by
    simpa using tendsto_const_nhds.sub (hsq.const_mul 4)
  have hhi : Tendsto (fun n : ℕ => Real.sqrt (Real.pi / 8) + 2 * (1 / Real.sqrt n))
      atTop (𝓝 (Real.sqrt (Real.pi / 8))) := by
    simpa using tendsto_const_nhds.add (hsq.const_mul 2)
  have hmain : Tendsto
      (fun n : ℕ => (∑ k ∈ Finset.range n, H n k) / Real.sqrt n)
      atTop (𝓝 (Real.sqrt (Real.pi / 8))) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
    · filter_upwards [eventually_ge_atTop 16] with n hn
      have hn1 : 1 ≤ n := by omega
      have hN0 : (0:ℝ) < n := by have : (16:ℝ) ≤ n := by exact_mod_cast hn
                                 linarith
      have hs : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hN0
      have hL : Real.sqrt n * Real.sqrt (Real.pi / 8) - 4
          ≤ ∑ k ∈ Finset.range n, H n k := by
        have h1 := I_ge hn
        have h2 := sum_lower hn
        linarith
      rw [le_div_iff₀ hs]
      have heq : (Real.sqrt (Real.pi / 8) - 4 * (1 / Real.sqrt n)) * Real.sqrt n
          = Real.sqrt n * Real.sqrt (Real.pi / 8) - 4 := by
        field_simp
      rw [heq]; exact hL
    · filter_upwards [eventually_ge_atTop 16] with n hn
      have hn1 : 1 ≤ n := by omega
      have hN0 : (0:ℝ) < n := by have : (16:ℝ) ≤ n := by exact_mod_cast hn
                                 linarith
      have hs : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hN0
      have hU : ∑ k ∈ Finset.range n, H n k
          ≤ Real.sqrt n * Real.sqrt (Real.pi / 8) + 2 := by
        have h1 := two_integrals_le hn
        have h2 := sum_upper hn
        linarith
      rw [div_le_iff₀ hs]
      have heq : (Real.sqrt (Real.pi / 8) + 2 * (1 / Real.sqrt n)) * Real.sqrt n
          = Real.sqrt n * Real.sqrt (Real.pi / 8) + 2 := by
        field_simp
      rw [heq]; exact hU
  exact hmain.congr (fun n => by rw [hbridge n])
