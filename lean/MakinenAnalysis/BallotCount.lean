import Mathlib

/-!
# Counting valid codewords by final stack height (towards Lemma 2)

`paper_en.tex`, Lemma 2: under the uniform distribution on the `catalan n`
binary trees of size `n`, the final stack height `h` of the reconstruction run
satisfies `P(h = m) = B(n,m)/C_n`, with `B(n,m) = (m/n)·C(2n-m-1, n-1)` the
ballot numbers.

The bijection between trees and valid codewords, and the identity
`h = n - (sum of the codeword)`, are machine-checked in the Rocq development
(`../../coq/`: `bijection_decode_encode`, `height_eq_n_minus_S`).  What remains
— and what this file proves — is the pure counting fact on the codeword side:

* the valid codewords of length `ℓ` read from stack height `h` form the finset
  `suffixes ℓ h`, those with final height `m` the finset `hw ℓ h m`
  (membership is characterised by `mem_suffixes` / `mem_hw`);
* `#(hw ℓ h m)` equals the recursively defined count `W ℓ h m` (`card_hw`), and
  `#(suffixes ℓ h) = W (ℓ+1) h 1` (`card_suffixes`, "crash-step" bijection);
* the reflection closed form, in subtraction-free shape (`W_add_choose`):
  for `1 ≤ m ≤ ℓ + 1 + h`,
  `W (ℓ+1) h m + C(2ℓ+h+1-m, ℓ+1+h) = C(2ℓ+h+1-m, ℓ)`.

The proof of `W_add_choose` is a double induction whose inductive step is the
Pascal-type recurrence `W (ℓ+2) (h+1) m = W (ℓ+2) h m + W (ℓ+1) (h+2) m`,
matching Pascal's rule on the binomial side term by term — so everything stays
additive over ℕ and no truncated subtraction ever needs to be unfolded.

The bridge to `hProb`, `ballot` and `catalan` (the actual Lemma 2 statement)
is in `MakinenAnalysis.Asymptotics`.
-/


namespace MakinenAnalysis

open Finset

/-- Final stack height after reading `w` from height `h`: each letter `x`
    pops `x` nodes and pushes one. -/
def finalH : ℕ → List ℕ → ℕ
  | h, [] => h
  | h, x :: w => finalH (h + 1 - x) w

/-- Łukasiewicz validity from height `h`: each letter pops at most the
    current stack. -/
def Valid : ℕ → List ℕ → Prop
  | _, [] => True
  | h, x :: w => x ≤ h ∧ Valid (h + 1 - x) w

/-- All valid words of length `ℓ` readable from stack height `h`. -/
def suffixes : ℕ → ℕ → Finset (List ℕ)
  | 0, _ => {[]}
  | ℓ + 1, h => (range (h + 1)).biUnion fun x =>
      (suffixes ℓ (h + 1 - x)).image (x :: ·)

/-- Valid words of length `ℓ` from height `h` whose final height is `m`. -/
def hw : ℕ → ℕ → ℕ → Finset (List ℕ)
  | 0, h, m => if m = h then {[]} else ∅
  | ℓ + 1, h, m => (range (h + 1)).biUnion fun x =>
      (hw ℓ (h + 1 - x) m).image (x :: ·)

/-- The count `#(hw ℓ h m)`, recursively. -/
def W : ℕ → ℕ → ℕ → ℕ
  | 0, h, m => if m = h then 1 else 0
  | ℓ + 1, h, m => ∑ x ∈ range (h + 1), W ℓ (h + 1 - x) m

/-! ### Membership characterisations (the finsets are the right sets) -/

lemma mem_suffixes : ∀ (ℓ h : ℕ) (w : List ℕ),
    w ∈ suffixes ℓ h ↔ w.length = ℓ ∧ Valid h w := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro h w
    cases w with
    | nil => simp [suffixes, Valid]
    | cons x v => simp [suffixes]
  | succ ℓ ih =>
    intro h w
    cases w with
    | nil => simp [suffixes]
    | cons x v =>
      simp only [suffixes, Finset.mem_biUnion, Finset.mem_range,
        Finset.mem_image, List.cons.injEq, Valid, List.length_cons,
        Nat.lt_succ_iff]
      constructor
      · rintro ⟨y, hy, u, hu, rfl, rfl⟩
        obtain ⟨hlen, hval⟩ := (ih _ u).mp hu
        exact ⟨by omega, hy, hval⟩
      · rintro ⟨hlen, hx, hval⟩
        exact ⟨x, hx, v, (ih _ v).mpr ⟨by omega, hval⟩, rfl, rfl⟩

lemma mem_hw : ∀ (ℓ h m : ℕ) (w : List ℕ),
    w ∈ hw ℓ h m ↔ w.length = ℓ ∧ Valid h w ∧ finalH h w = m := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro h m w
    cases w with
    | nil =>
      simp only [hw, Valid, finalH, List.length_nil, true_and]
      split
      · simp_all
      · simp_all
        omega
    | cons x v =>
      simp only [hw, List.length_cons]
      split <;> simp
  | succ ℓ ih =>
    intro h m w
    cases w with
    | nil => simp [hw]
    | cons x v =>
      simp only [hw, Finset.mem_biUnion, Finset.mem_range,
        Finset.mem_image, List.cons.injEq, Valid, finalH, List.length_cons,
        Nat.lt_succ_iff]
      constructor
      · rintro ⟨y, hy, u, hu, rfl, rfl⟩
        obtain ⟨hlen, hval, hfin⟩ := (ih _ _ u).mp hu
        exact ⟨by omega, ⟨hy, hval⟩, hfin⟩
      · rintro ⟨hlen, ⟨hx, hval⟩, hfin⟩
        exact ⟨x, hx, v, (ih _ _ v).mpr ⟨by omega, hval, hfin⟩, rfl, rfl⟩

/-! ### Cardinalities -/

lemma consImage_pairwiseDisjoint (t : ℕ → Finset (List ℕ)) (s : Finset ℕ) :
    (s : Set ℕ).PairwiseDisjoint fun x => (t x).image (x :: ·) := by
  intro x _ y _ hxy
  simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image]
  rintro w ⟨v1, _, rfl⟩ ⟨v2, _, heq⟩
  exact hxy (by injection heq with h1 _; exact h1.symm)

lemma card_hw : ∀ (ℓ h m : ℕ), (hw ℓ h m).card = W ℓ h m := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro h m
    simp only [hw, W]
    split <;> simp
  | succ ℓ ih =>
    intro h m
    show ((range (h + 1)).biUnion fun x => (hw ℓ (h + 1 - x) m).image (x :: ·)).card
      = ∑ x ∈ range (h + 1), W ℓ (h + 1 - x) m
    rw [Finset.card_biUnion (consImage_pairwiseDisjoint _ _)]
    exact Finset.sum_congr rfl fun x _ => by
      rw [Finset.card_image_of_injective _ List.cons_injective, ih]

/-- Appending the forced final "crash" letter is a bijection between all valid
    words of length `ℓ` and those of length `ℓ+1` ending at height 1; hence the
    total count is `W (ℓ+1) h 1`. -/
lemma card_suffixes : ∀ (ℓ h : ℕ), (suffixes ℓ h).card = W (ℓ + 1) h 1 := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro h
    show ({([] : List ℕ)} : Finset (List ℕ)).card
      = ∑ x ∈ range (h + 1), W 0 (h + 1 - x) 1
    rw [Finset.card_singleton]
    rw [Finset.sum_eq_single h
      (fun x hx hxh => by
        simp only [Finset.mem_range] at hx
        show (if 1 = h + 1 - x then 1 else 0) = 0
        rw [if_neg (by omega)])
      (fun habs => absurd (Finset.mem_range.mpr (by omega)) habs)]
    show (1 : ℕ) = if 1 = h + 1 - h then 1 else 0
    rw [if_pos (by omega)]
  | succ ℓ ih =>
    intro h
    show ((range (h + 1)).biUnion fun x => (suffixes ℓ (h + 1 - x)).image (x :: ·)).card
      = ∑ x ∈ range (h + 1), W (ℓ + 1) (h + 1 - x) 1
    rw [Finset.card_biUnion (consImage_pairwiseDisjoint _ _)]
    exact Finset.sum_congr rfl fun x _ => by
      rw [Finset.card_image_of_injective _ List.cons_injective, ih]

/-! ### The count function: vanishing, maximum, closed form -/

/-- No word can end above `ℓ + h` (each step raises the height by at most 1). -/
lemma W_eq_zero : ∀ ℓ h m : ℕ, ℓ + h < m → W ℓ h m = 0 := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro h m hlt
    show (if m = h then 1 else 0) = 0
    rw [if_neg (by omega)]
  | succ ℓ ih =>
    intro h m hlt
    show (∑ x ∈ range (h + 1), W ℓ (h + 1 - x) m) = 0
    exact Finset.sum_eq_zero fun x hx => ih _ _ (by omega)

/-- Exactly one word attains the maximal height `ℓ + h`: the all-zero word. -/
lemma W_max : ∀ ℓ h : ℕ, W ℓ h (ℓ + h) = 1 := by
  intro ℓ
  induction ℓ with
  | zero => intro h; show (if 0 + h = h then 1 else 0) = 1; rw [if_pos (by omega)]
  | succ ℓ ih =>
    intro h
    show (∑ x ∈ range (h + 1), W ℓ (h + 1 - x) (ℓ + 1 + h)) = 1
    rw [Finset.sum_range_succ']
    have hz : ∀ i ∈ range h, W ℓ (h + 1 - (i + 1)) (ℓ + 1 + h) = 0 :=
      fun i _ => W_eq_zero _ _ _ (by omega)
    rw [Finset.sum_congr rfl hz, Finset.sum_const, smul_eq_mul, mul_zero, zero_add]
    rw [show h + 1 - 0 = h + 1 by omega, show ℓ + 1 + h = ℓ + (h + 1) by omega]
    exact ih (h + 1)

/-- **Reflection closed form, subtraction-free**: for `1 ≤ m ≤ ℓ + 1 + h`,
    `W (ℓ+1) h m + C(2ℓ+h+1-m, ℓ+1+h) = C(2ℓ+h+1-m, ℓ)`.
    Equivalently `W (ℓ+1) h m = C(2ℓ+h+1-m, ℓ) - C(2ℓ+h+1-m, ℓ+1+h)`,
    the ballot-type count of Łukasiewicz paths from height `h` to height `m`. -/
lemma W_add_choose : ∀ ℓ h m : ℕ, 1 ≤ m → m ≤ ℓ + 1 + h →
    W (ℓ + 1) h m + (2 * ℓ + h + 1 - m).choose (ℓ + 1 + h)
      = (2 * ℓ + h + 1 - m).choose ℓ := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro h m hm1 hmh
    -- length-1 words: exactly one reaches each `1 ≤ m ≤ h+1`
    rw [Nat.choose_zero_right, Nat.choose_eq_zero_of_lt (by omega)]
    show (∑ x ∈ range (h + 1), W 0 (h + 1 - x) m) + 0 = 1
    rw [Finset.sum_eq_single (h + 1 - m)
      (fun x hx hxm => by
        simp only [Finset.mem_range] at hx
        show (if m = h + 1 - x then 1 else 0) = 0
        rw [if_neg (by omega)])
      (fun habs => absurd (Finset.mem_range.mpr (by omega)) habs)]
    show (if m = h + 1 - (h + 1 - m) then 1 else 0) + 0 = 1
    rw [if_pos (by omega)]
  | succ ℓ ihℓ =>
    intro h
    induction h with
    | zero =>
      intro m hm1 hmh   -- m ≤ ℓ + 2
      -- from height 0 the first letter must be 0: W (ℓ+2) 0 m = W (ℓ+1) 1 m
      have hW0 : W (ℓ + 1 + 1) 0 m = W (ℓ + 1) 1 m := by
        show (∑ x ∈ range 1, W (ℓ + 1) (0 + 1 - x) m) = W (ℓ + 1) 1 m
        rw [Finset.sum_range_one]
      have hih := ihℓ 1 m hm1 (by omega)
      -- align the choose atoms of the IH
      rw [show 2 * ℓ + 1 + 1 - m = 2 * ℓ + 2 - m by omega,
          show ℓ + 1 + 1 = ℓ + 2 by omega] at hih
      -- Pascal on both target binomials
      have hp1 : (2 * (ℓ + 1) + 0 + 1 - m).choose (ℓ + 1 + 1 + 0)
          = (2 * ℓ + 2 - m).choose (ℓ + 1) + (2 * ℓ + 2 - m).choose (ℓ + 2) := by
        rw [show 2 * (ℓ + 1) + 0 + 1 - m = (2 * ℓ + 2 - m) + 1 by omega,
            show ℓ + 1 + 1 + 0 = (ℓ + 1) + 1 by omega,
            Nat.choose_succ_succ', show ℓ + 1 + 1 = ℓ + 2 by omega]
      have hp2 : (2 * (ℓ + 1) + 0 + 1 - m).choose (ℓ + 1)
          = (2 * ℓ + 2 - m).choose ℓ + (2 * ℓ + 2 - m).choose (ℓ + 1) := by
        rw [show 2 * (ℓ + 1) + 0 + 1 - m = (2 * ℓ + 2 - m) + 1 by omega,
            show ℓ + 1 = ℓ + 1 from rfl, Nat.choose_succ_succ']
      rw [hW0, hp1, hp2]
      omega
    | succ h ihh =>
      intro m hm1 hmh   -- m ≤ ℓ + h + 3
      -- Pascal-type recurrence on the count side
      have hWrec : W (ℓ + 1 + 1) (h + 1) m
          = W (ℓ + 1 + 1) h m + W (ℓ + 1) (h + 2) m := by
        show (∑ x ∈ range (h + 1 + 1), W (ℓ + 1) (h + 1 + 1 - x) m) = _
        rw [Finset.sum_range_succ']
        have e : ∀ i ∈ range (h + 1),
            W (ℓ + 1) (h + 1 + 1 - (i + 1)) m = W (ℓ + 1) (h + 1 - i) m :=
          fun i _ => by rw [show h + 1 + 1 - (i + 1) = h + 1 - i by omega]
        rw [Finset.sum_congr rfl e, show h + 1 + 1 - 0 = h + 2 by omega]
        have hsum : (∑ i ∈ range (h + 1), W (ℓ + 1) (h + 1 - i) m)
            = W (ℓ + 1 + 1) h m := rfl
        rw [hsum]
      by_cases hcase : m ≤ ℓ + 1 + 1 + h
      · -- inner IH (height h) + outer IH (length ℓ+1, height h+2), Pascal-glued
        have h1 := ihh m hm1 hcase
        have h2 := ihℓ (h + 2) m hm1 (by omega)
        rw [show 2 * (ℓ + 1) + h + 1 - m = 2 * ℓ + h + 3 - m by omega,
            show ℓ + 1 + 1 + h = ℓ + h + 2 by omega] at h1
        rw [show 2 * ℓ + (h + 2) + 1 - m = 2 * ℓ + h + 3 - m by omega,
            show ℓ + 1 + (h + 2) = ℓ + h + 3 by omega] at h2
        have hp1 : (2 * (ℓ + 1) + (h + 1) + 1 - m).choose (ℓ + 1 + 1 + (h + 1))
            = (2 * ℓ + h + 3 - m).choose (ℓ + h + 2)
              + (2 * ℓ + h + 3 - m).choose (ℓ + h + 3) := by
          rw [show 2 * (ℓ + 1) + (h + 1) + 1 - m = (2 * ℓ + h + 3 - m) + 1 by omega,
              show ℓ + 1 + 1 + (h + 1) = (ℓ + h + 2) + 1 by omega,
              Nat.choose_succ_succ', show ℓ + h + 2 + 1 = ℓ + h + 3 by omega]
        have hp2 : (2 * (ℓ + 1) + (h + 1) + 1 - m).choose (ℓ + 1)
            = (2 * ℓ + h + 3 - m).choose ℓ + (2 * ℓ + h + 3 - m).choose (ℓ + 1) := by
          rw [show 2 * (ℓ + 1) + (h + 1) + 1 - m = (2 * ℓ + h + 3 - m) + 1 by omega,
              Nat.choose_succ_succ']
        rw [hWrec, hp1, hp2]
        omega
      · -- maximal height `m = ℓ + h + 3 = (ℓ+2) + (h+1)`: the all-zero word
        have hm : m = ℓ + 1 + 1 + (h + 1) := by omega
        subst hm
        have hWm : W (ℓ + 1 + 1) (h + 1) (ℓ + 1 + 1 + (h + 1)) = 1 := W_max _ _
        rw [hWm, show 2 * (ℓ + 1) + (h + 1) + 1 - (ℓ + 1 + 1 + (h + 1)) = ℓ + 1 by omega,
            Nat.choose_eq_zero_of_lt (by omega), Nat.choose_self]

end MakinenAnalysis
