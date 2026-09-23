import Mathlib
import MakinenAnalysis.BallotCount
import MakinenAnalysis.LeafCount
import MakinenAnalysis.Asymptotics

/-!
# Corollary 11: concentration of algorithm M at its worst case

`paper_en.tex`, Corollary 11 (`cor:Mconc`): algorithm M's comparison count
`A_M = 3n - 1 - h` concentrates at its worst case `3n - 2` as `n → ∞`:
`A_M / n →p 3`, equivalently `P(h ≥ εn) → 0` for every `ε > 0`.

On the codeword sample space (`MakinenAnalysis.BallotCount`) this is pure
counting + Markov's inequality: `h = finalH 1 w ≥ 0`, and the exact mean
identity `(n+2) · Σ_w finalH 1 w = 3n · catalan n`
(`MakinenAnalysis.sum_finalH_mul_eq`) gives, for any threshold `t`,

  `t · #{w ∈ suffixes (n-1) 1 : finalH 1 w ≥ t} ≤ Σ_w finalH 1 w`,

hence `#{finalH 1 ≥ t} / catalan n ≤ 3n / ((n+2)·t) → 0` once `t` grows like
`εn`.

* `card_finalH_ge_mul_le` — the finite Markov inequality on `suffixes ℓ h`.
* `card_filter_finalH_ge_div_catalan_le` — Markov + the exact mean, phrased as
  a counting proportion on the codeword sample space `suffixes (n-1) 1`.
* `finalH_concentration` — the fraction of codewords with `finalH 1 w ≥ ε n`
  vanishes as `n → ∞`, for every `ε > 0`.
* `AM_concentration` — the paper-facing corollary: the fraction of codewords
  for which the standardised comparison count `A_M/n = (3n-1-h)/n` deviates
  from its limit `3` by at least `ε` vanishes as `n → ∞`.
-/

namespace MakinenAnalysis

open Finset Filter Topology

/-! ### The finite Markov inequality -/

/-- **Finite Markov inequality** on the codeword counting space: for any
    length `ℓ`, starting height `h` and threshold `t`, `t` times the number of
    words whose final height reaches at least `t` is at most the total sum of
    final heights over all words. -/
theorem card_finalH_ge_mul_le (ℓ h t : ℕ) :
    t * ((suffixes ℓ h).filter (fun w => t ≤ finalH h w)).card
      ≤ ∑ w ∈ suffixes ℓ h, finalH h w := by
  have hsub : (suffixes ℓ h).filter (fun w => t ≤ finalH h w) ⊆ suffixes ℓ h :=
    Finset.filter_subset _ _
  have h1 : ∑ w ∈ (suffixes ℓ h).filter (fun w => t ≤ finalH h w), finalH h w
      ≤ ∑ w ∈ suffixes ℓ h, finalH h w :=
    Finset.sum_le_sum_of_subset hsub
  have h2 : ((suffixes ℓ h).filter (fun w => t ≤ finalH h w)).card • t
      ≤ ∑ w ∈ (suffixes ℓ h).filter (fun w => t ≤ finalH h w), finalH h w :=
    Finset.card_nsmul_le_sum _ (finalH h) t (fun w hw => (Finset.mem_filter.mp hw).2)
  calc t * ((suffixes ℓ h).filter (fun w => t ≤ finalH h w)).card
      = ((suffixes ℓ h).filter (fun w => t ≤ finalH h w)).card • t := by
        rw [smul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ w ∈ (suffixes ℓ h).filter (fun w => t ≤ finalH h w), finalH h w := h2
    _ ≤ ∑ w ∈ suffixes ℓ h, finalH h w := h1

/-- **Markov + the exact mean**, as a counting proportion on the codeword
    sample space `suffixes (n-1) 1` (`catalan n` many words, mean final height
    `3n/(n+2)`, `MakinenAnalysis.sum_finalH_mul_eq`): for `n ≥ 1` and `t ≥ 1`,
    the proportion of codewords reaching final height `≥ t` is at most
    `3n / ((n+2)·t)`. -/
theorem card_filter_finalH_ge_div_catalan_le (n t : ℕ) (hn : 1 ≤ n) (ht : 1 ≤ t) :
    (((suffixes (n - 1) 1).filter (fun w => t ≤ finalH 1 w)).card : ℝ) / (catalan n : ℝ)
      ≤ 3 * (n : ℝ) / (((n : ℝ) + 2) * (t : ℝ)) := by
  have hMarkov := card_finalH_ge_mul_le (n - 1) 1 t
  have hMarkovR : (t : ℝ) * (((suffixes (n - 1) 1).filter (fun w => t ≤ finalH 1 w)).card : ℝ)
      ≤ (∑ w ∈ suffixes (n - 1) 1, finalH 1 w : ℕ) := by exact_mod_cast hMarkov
  have hmean := sum_finalH_mul_eq n hn
  have hcatpos : (0 : ℝ) < (catalan n : ℝ) := by
    have h := Cat_ne_zero n
    simp only [Cat] at h
    exact_mod_cast Nat.pos_of_ne_zero (by exact_mod_cast h)
  have h2pos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  rw [div_le_div_iff₀ hcatpos (mul_pos h2pos htpos)]
  have key : ((n : ℝ) + 2) * ((t : ℝ) * (((suffixes (n - 1) 1).filter
        (fun w => t ≤ finalH 1 w)).card : ℝ))
      ≤ 3 * (n : ℝ) * (catalan n : ℝ) := by
    rw [← hmean]
    exact mul_le_mul_of_nonneg_left hMarkovR (le_of_lt h2pos)
  calc (((suffixes (n - 1) 1).filter (fun w => t ≤ finalH 1 w)).card : ℝ)
        * (((n : ℝ) + 2) * (t : ℝ))
      = ((n : ℝ) + 2) * ((t : ℝ) * (((suffixes (n - 1) 1).filter
          (fun w => t ≤ finalH 1 w)).card : ℝ)) := by ring
    _ ≤ 3 * (n : ℝ) * (catalan n : ℝ) := key

/-! ### The concentration limit -/

open scoped Classical in
/-- **`finalH_concentration`.** For every `ε > 0`, the proportion of codewords
    (of length `n - 1`, uniform among the `catalan n` valid words) whose final
    stack height `h = finalH 1 w` reaches at least `ε n` vanishes as
    `n → ∞`. -/
theorem finalH_concentration (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
        (((suffixes (n - 1) 1).filter
            (fun w => ε * (n : ℝ) ≤ (finalH 1 w : ℝ))).card : ℝ) / (catalan n : ℝ))
      atTop (nhds 0) := by
  have hg0 : Tendsto (fun n : ℕ => 3 / (ε * ((n : ℝ) + 2))) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => ε * ((n : ℝ) + 2)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hε h1
    have h3 : Tendsto (fun n : ℕ => (ε * ((n : ℝ) + 2))⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp h2
    simpa [div_eq_mul_inv] using h3.const_mul (3 : ℝ)
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => by positivity) ?_ hg0
  filter_upwards [eventually_ge_atTop 1] with n hn
  set t := ⌈ε * (n : ℝ)⌉₊ with ht_def
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have htpos : 1 ≤ t := by
    rw [ht_def, Nat.one_le_ceil_iff]
    positivity
  have hcong : (suffixes (n - 1) 1).filter (fun w => ε * (n : ℝ) ≤ (finalH 1 w : ℝ))
      = (suffixes (n - 1) 1).filter (fun w => t ≤ finalH 1 w) := by
    apply Finset.filter_congr
    intro w _
    exact (Nat.ceil_le (a := ε * (n : ℝ)) (n := finalH 1 w)).symm
  rw [hcong]
  have hbound := card_filter_finalH_ge_div_catalan_le n t hn htpos
  have htge : ε * (n : ℝ) ≤ (t : ℝ) := Nat.le_ceil _
  have hn0' : (n : ℝ) ≠ 0 := hn0.ne'
  calc (((suffixes (n - 1) 1).filter (fun w => t ≤ finalH 1 w)).card : ℝ) / (catalan n : ℝ)
      ≤ 3 * (n : ℝ) / (((n : ℝ) + 2) * (t : ℝ)) := hbound
    _ ≤ 3 * (n : ℝ) / (((n : ℝ) + 2) * (ε * (n : ℝ))) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left htge (by positivity)
    _ = 3 / (ε * ((n : ℝ) + 2)) := by
        field_simp

/-! ### Corollary 11, paper-facing form -/

open scoped Classical in
/-- **Corollary 11 (`cor:Mconc`).** The standardised comparison count of
    Mäkinen's algorithm `M`, `A_M / n = (3n - 1 - h) / n`, concentrates at its
    limit `3`: for every `ε > 0`, the proportion of codewords for which
    `|A_M/n - 3| ≥ ε` vanishes as `n → ∞`. Since
    `A_M/n - 3 = -(h + 1)/n`, this reduces to the vanishing of
    `P(h ≥ ε n - 1)`, proved by the same Markov argument as
    `finalH_concentration`. -/
theorem AM_concentration (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
        (((suffixes (n - 1) 1).filter (fun w =>
            ε ≤ |(3 * (n : ℝ) - 1 - (finalH 1 w : ℝ)) / (n : ℝ) - 3|)).card : ℝ)
          / (catalan n : ℝ))
      atTop (nhds 0) := by
  -- eventually `ε n - 1 ≥ 1`, so the threshold `⌈ε n - 1⌉₊ ≥ 1`
  have hN : ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → (1 : ℝ) ≤ ε * (n : ℝ) - 1 := by
    refine ⟨⌈2 / ε⌉₊ + 1, by omega, fun n hn => ?_⟩
    have h1 : (2 / ε : ℝ) ≤ (⌈2 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈2 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h3 : (2 / ε : ℝ) ≤ (n : ℝ) := by
      push_cast at h2
      linarith
    have h4 : (2 : ℝ) ≤ ε * (n : ℝ) := by
      rw [div_le_iff₀ hε] at h3
      linarith
    linarith
  obtain ⟨N, hN1, hN⟩ := hN
  have hg0 : Tendsto (fun n : ℕ => 6 / (ε * ((n : ℝ) + 2))) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => ε * ((n : ℝ) + 2)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hε h1
    have h3 : Tendsto (fun n : ℕ => (ε * ((n : ℝ) + 2))⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp h2
    simpa [div_eq_mul_inv] using h3.const_mul (6 : ℝ)
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => by positivity) ?_ hg0
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn1 : 1 ≤ n := le_trans hN1 hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hn0' : (n : ℝ) ≠ 0 := hn0.ne'
  have h2pos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hshift : (1 : ℝ) ≤ ε * (n : ℝ) - 1 := hN n hn
  have hεn2 : (2 : ℝ) ≤ ε * (n : ℝ) := by linarith
  have hhalf : ε * (n : ℝ) / 2 ≤ ε * (n : ℝ) - 1 := by linarith
  set t := ⌈ε * (n : ℝ) - 1⌉₊ with ht_def
  have htpos : 1 ≤ t := by
    rw [ht_def, Nat.one_le_ceil_iff]; linarith
  -- pointwise identification of the filter predicate with `t ≤ finalH 1 w`
  have hpt : ∀ w, (ε ≤ |(3 * (n : ℝ) - 1 - (finalH 1 w : ℝ)) / (n : ℝ) - 3|)
      ↔ (ε * (n : ℝ) - 1 ≤ (finalH 1 w : ℝ)) := by
    intro w
    have hrw : (3 * (n : ℝ) - 1 - (finalH 1 w : ℝ)) / (n : ℝ) - 3
        = -(((finalH 1 w : ℝ) + 1) / (n : ℝ)) := by
      field_simp
      ring
    rw [hrw, abs_neg, abs_of_nonneg (by positivity), le_div_iff₀ hn0]
    constructor
    · intro h; linarith
    · intro h; linarith
  have hcong : (suffixes (n - 1) 1).filter (fun w =>
        ε ≤ |(3 * (n : ℝ) - 1 - (finalH 1 w : ℝ)) / (n : ℝ) - 3|)
      = (suffixes (n - 1) 1).filter (fun w => t ≤ finalH 1 w) := by
    apply Finset.filter_congr
    intro w _
    rw [hpt w, ht_def, Nat.ceil_le]
  rw [hcong]
  have hbound := card_filter_finalH_ge_div_catalan_le n t hn1 htpos
  have htge : ε * (n : ℝ) - 1 ≤ (t : ℝ) := Nat.le_ceil _
  have hpos1 : (0 : ℝ) < ε * (n : ℝ) - 1 := by linarith
  have hpos2 : (0 : ℝ) < ε * (n : ℝ) / 2 := by linarith
  calc (((suffixes (n - 1) 1).filter (fun w => t ≤ finalH 1 w)).card : ℝ) / (catalan n : ℝ)
      ≤ 3 * (n : ℝ) / (((n : ℝ) + 2) * (t : ℝ)) := hbound
    _ ≤ 3 * (n : ℝ) / (((n : ℝ) + 2) * (ε * (n : ℝ) - 1)) := by
        apply div_le_div_of_nonneg_left (by positivity) (mul_pos h2pos hpos1)
        exact mul_le_mul_of_nonneg_left htge (le_of_lt h2pos)
    _ ≤ 3 * (n : ℝ) / (((n : ℝ) + 2) * (ε * (n : ℝ) / 2)) := by
        apply div_le_div_of_nonneg_left (by positivity) (mul_pos h2pos hpos2)
        exact mul_le_mul_of_nonneg_left hhalf (le_of_lt h2pos)
    _ = 6 / (ε * ((n : ℝ) + 2)) := by
        field_simp
        ring

/-! ### The sharper limit law: the worst-case CDF

The paper's actual Corollary 11 is sharper than mere vanishing of the tail:
for every fixed `c`, `P(A_M ≥ 3n - 2 - c) → 1 - (c+3)·2^{-(c+2)}`, the
negative-binomial CDF value at `c`.  Since `A_M = 3n - 1 - h`, the event
`{A_M ≥ 3n - 2 - c}` is exactly `{h ≤ c + 1}`.  On the codeword sample space
`h = finalH 1 w` never drops below `1` (`finalH_ge_one`), so `{h ≤ c+1}`
partitions into the `c+1` disjoint layers `{h = m}`, `m ∈ Icc 1 (c+1)`, each
of which is handled by the exact counting form of Theorem 10
(`thm_Mlimit_count`); the limit values sum to the closed form `nb_cdf_sum`. -/

/-- Every valid codeword's final stack height never drops below the height it
    started at reaching `1`: since a valid letter `x` pops at most the current
    height, the new height `h + 1 - x ≥ 1`. -/
private lemma finalH_ge_one : ∀ (w : List ℕ) (h : ℕ), 1 ≤ h → Valid h w → 1 ≤ finalH h w := by
  intro w
  induction w with
  | nil => intro h hh _; simpa [finalH] using hh
  | cons x v ih =>
    intro h _ hv
    obtain ⟨hx, hv'⟩ := hv
    exact ih (h + 1 - x) (by omega) hv'

/-- **Finite negative-binomial CDF, closed form**:
    `∑_{m=1}^{c+1} m / 2^{m+1} = 1 - (c+3)/2^{c+2}`. -/
lemma nb_cdf_sum (c : ℕ) :
    ∑ m ∈ Finset.Icc 1 (c + 1), (m : ℝ) / 2 ^ (m + 1)
      = 1 - ((c : ℝ) + 3) / 2 ^ (c + 2) := by
  induction c with
  | zero =>
    rw [Finset.Icc_self, Finset.sum_singleton]
    norm_num
  | succ c ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ c + 1 + 1), ih]
    have h2ne : (2 : ℝ) ^ (c + 2) ≠ 0 := by positivity
    have hpow : (2 : ℝ) ^ (c + 1 + 1 + 1) = 2 ^ (c + 2) * 2 := by ring
    push_cast
    rw [hpow]
    field_simp
    ring

/-- The codewords of `suffixes (n-1) 1` reaching final height exactly `m`,
    filtered from the sample space, are exactly `hw (n-1) 1 m`. -/
private lemma suffixes_filter_finalH_eq (n m : ℕ) :
    (suffixes (n - 1) 1).filter (fun w => finalH 1 w = m) = hw (n - 1) 1 m := by
  apply Finset.ext
  intro w
  rw [Finset.mem_filter, mem_suffixes, mem_hw]
  constructor
  · rintro ⟨⟨hlen, hval⟩, heq⟩
    exact ⟨hlen, hval, heq⟩
  · rintro ⟨hlen, hval, heq⟩
    exact ⟨⟨hlen, hval⟩, heq⟩

/-- **Theorem 10, cumulative — the paper's sharper Corollary 11.**  For every
    fixed `c`, the proportion of codewords with final stack height at most
    `c + 1` — equivalently `A_M = 3n - 1 - h ≥ 3n - 2 - c` — converges to the
    negative-binomial CDF value `1 - (c+3)/2^{c+2}`. -/
theorem AM_worst_case_limit (c : ℕ) :
    Tendsto (fun n : ℕ =>
        (((suffixes (n - 1) 1).filter (fun w => finalH 1 w ≤ c + 1)).card : ℝ)
          / (catalan n : ℝ))
      atTop (nhds (1 - ((c : ℝ) + 3) / 2 ^ (c + 2))) := by
  -- each layer `{h = m}`, `m ∈ Icc 1 (c+1)`, converges to `m / 2^{m+1}`
  have hterm : ∀ m ∈ Finset.Icc 1 (c + 1),
      Tendsto (fun n : ℕ => ((hw (n - 1) 1 m).card : ℝ) / (catalan n : ℝ))
        atTop (nhds ((m : ℝ) / 2 ^ (m + 1))) := by
    intro m hm
    simp only [Finset.mem_Icc] at hm
    obtain ⟨m', rfl⟩ : ∃ m', m' + 1 = m := ⟨m - 1, by omega⟩
    have hM := thm_Mlimit_count m'
    have hval : nbPMF m' = ((m' + 1 : ℕ) : ℝ) / 2 ^ (m' + 1 + 1) := by
      simp only [nbPMF]
      push_cast
      rw [show m' + 1 + 1 = m' + 2 by ring, one_div, inv_pow]
      ring
    rw [hval] at hM
    refine Filter.Tendsto.congr' ?_ hM
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [card_suffixes_eq_catalan n hn]
  have hsum := tendsto_finsetSum (Finset.Icc 1 (c + 1)) hterm
  rw [nb_cdf_sum c] at hsum
  refine Filter.Tendsto.congr' ?_ hsum
  filter_upwards [eventually_ge_atTop 1] with n hn
  -- partition `{h ≤ c+1}` into the disjoint layers `{h = m}`, `m ∈ Icc 1 (c+1)`
  have hpart : (suffixes (n - 1) 1).filter (fun w => finalH 1 w ≤ c + 1)
      = (Finset.Icc 1 (c + 1)).biUnion
          (fun m => (suffixes (n - 1) 1).filter (fun w => finalH 1 w = m)) := by
    apply Finset.ext
    intro w
    constructor
    · intro hwf
      obtain ⟨hwS, hle⟩ := Finset.mem_filter.mp hwf
      obtain ⟨_, hval⟩ := (mem_suffixes _ _ w).mp hwS
      have hge := finalH_ge_one w 1 le_rfl hval
      refine Finset.mem_biUnion.mpr ⟨finalH 1 w, ?_, ?_⟩
      · exact Finset.mem_Icc.mpr ⟨hge, hle⟩
      · exact Finset.mem_filter.mpr ⟨hwS, rfl⟩
    · intro hwb
      obtain ⟨m, hm, hwm⟩ := Finset.mem_biUnion.mp hwb
      have hwS := (Finset.mem_filter.mp hwm).1
      have hmc := (Finset.mem_filter.mp hwm).2
      have hmle := (Finset.mem_Icc.mp hm).2
      exact Finset.mem_filter.mpr ⟨hwS, hmc ▸ hmle⟩
  have hdisj : (↑(Finset.Icc 1 (c + 1)) : Set ℕ).PairwiseDisjoint
      (fun m => (suffixes (n - 1) 1).filter (fun w => finalH 1 w = m)) := by
    intro m1 _ m2 _ hne
    apply Finset.disjoint_left.mpr
    intro w hw1 hw2
    have h1 := (Finset.mem_filter.mp hw1).2
    have h2 := (Finset.mem_filter.mp hw2).2
    exact hne (h1.symm.trans h2)
  have hcardeq : ((suffixes (n - 1) 1).filter (fun w => finalH 1 w ≤ c + 1)).card
      = ∑ m ∈ Finset.Icc 1 (c + 1), (hw (n - 1) 1 m).card := by
    rw [hpart, Finset.card_biUnion hdisj]
    exact Finset.sum_congr rfl fun m _ => by rw [suffixes_filter_finalH_eq]
  rw [← Finset.sum_div, ← Nat.cast_sum, ← hcardeq]

end MakinenAnalysis
