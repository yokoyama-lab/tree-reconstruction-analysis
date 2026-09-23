/-
# The Dvoretzky–Motzkin cycle lemma

For a list `l : List ℤ` with `l.sum = 1`, exactly one rotation of `l` has all
its (nonempty) prefix sums positive.

Existence: rotate at the *last* index `r` at which the prefix sums
`S j = (l.take j).sum` attain their minimum over `j ∈ [0, l.length)`.
Uniqueness: if `r₁ < r₂` both dominated, then domination of `r₁` gives
`0 < S r₂ - S r₁` and domination of `r₂` (wrapping around) gives
`0 < 1 - S r₂ + S r₁`; over ℤ these force `0 < S r₂ - S r₁ < 1`, impossible.

Note: the hypothesis `hle : ∀ x ∈ l, x ≤ 1` is *not needed* for this
statement (uniqueness already follows from integrality and `l.sum = 1`);
it is kept in the signature for interface stability with the k-out-of-n
version of the cycle lemma, where it is essential.
-/
import Mathlib

namespace MakinenAnalysis

/-- Prefix sums of a rotation, non-wrapping case: for `r + k ≤ l.length`,
the first `k` elements of `l.rotate r` sum to `S (r + k) - S r`. -/
theorem rotate_take_sum_of_le (l : List ℤ) (r k : ℕ) (hr : r ≤ l.length)
    (hk : k ≤ l.length - r) :
    ((l.rotate r).take k).sum = (l.take (r + k)).sum - (l.take r).sum := by
  rw [List.rotate_eq_drop_append_take hr,
    List.take_append_of_le_length (by simpa using hk),
    List.take_add, List.sum_append]
  ring

/-- Prefix sums of a rotation, wrapping case: for `l.length - r ≤ k ≤ l.length`,
the first `k` elements of `l.rotate r` sum to
`l.sum - S r + S (k - (l.length - r))`. -/
theorem rotate_take_sum_of_ge (l : List ℤ) (r k : ℕ) (hr : r ≤ l.length)
    (hk₁ : l.length - r ≤ k) (hk₂ : k ≤ l.length) :
    ((l.rotate r).take k).sum
      = l.sum - (l.take r).sum + (l.take (k - (l.length - r))).sum := by
  have hsplit : (l.take r).sum + (l.drop r).sum = l.sum := by
    rw [← List.sum_append, List.take_append_drop]
  rw [List.rotate_eq_drop_append_take hr, List.take_append,
    List.take_of_length_le (by simpa using hk₁), List.length_drop,
    List.take_take, min_eq_left (by omega), List.sum_append]
  linarith

/-- Two distinct rotations cannot both have all prefix sums positive when the
total sum is `1`: this is the integrality argument at the heart of uniqueness
in the cycle lemma. -/
theorem dominating_rotation_unique {l : List ℤ} (hsum : l.sum = 1) {r₁ r₂ : ℕ}
    (h₁₂ : r₁ < r₂) (h₂ : r₂ < l.length)
    (hd₁ : ∀ k : ℕ, k < l.length → 0 < ((l.rotate r₁).take (k + 1)).sum)
    (hd₂ : ∀ k : ℕ, k < l.length → 0 < ((l.rotate r₂).take (k + 1)).sum) :
    False := by
  have h₁ : r₁ < l.length := h₁₂.trans h₂
  -- domination of `r₁`, prefix of length `r₂ - r₁`: `0 < S r₂ - S r₁`
  have p₁ : 0 < (l.take r₂).sum - (l.take r₁).sum := by
    have h := hd₁ (r₂ - r₁ - 1) (by omega)
    rwa [show r₂ - r₁ - 1 + 1 = r₂ - r₁ by omega,
      rotate_take_sum_of_le l r₁ (r₂ - r₁) h₁.le (by omega),
      show r₁ + (r₂ - r₁) = r₂ by omega] at h
  -- domination of `r₂`, wrapping prefix of length `l.length - r₂ + r₁`:
  -- `0 < 1 - S r₂ + S r₁`
  have p₂ : 0 < l.sum - (l.take r₂).sum + (l.take r₁).sum := by
    have h := hd₂ (l.length - r₂ + r₁ - 1) (by omega)
    rwa [show l.length - r₂ + r₁ - 1 + 1 = l.length - r₂ + r₁ by omega,
      rotate_take_sum_of_ge l r₂ (l.length - r₂ + r₁) h₂.le (by omega) (by omega),
      show l.length - r₂ + r₁ - (l.length - r₂) = r₁ by omega] at h
  rw [hsum] at p₂
  omega

set_option linter.unusedVariables false in
/-- **The Dvoretzky–Motzkin cycle lemma.** If `l : List ℤ` sums to `1`
(and each entry is at most `1`; this hypothesis is in fact unused here, see
the module docstring), then there is exactly one rotation of `l` all of whose
nonempty prefix sums are positive. -/
theorem dvoretzky_motzkin (l : List ℤ) (hne : l ≠ [])
    (hle : ∀ x ∈ l, x ≤ 1) (hsum : l.sum = 1) :
    ∃! r : ℕ, r < l.length ∧
      ∀ k : ℕ, k < l.length → 0 < ((l.rotate r).take (k + 1)).sum := by
  classical
  have hN : 0 < l.length := List.length_pos_iff.mpr hne
  -- Choose `r` as the LAST minimizer of the prefix sums over `[0, l.length)`.
  obtain ⟨r, hrN, hminr, hlast⟩ :
      ∃ r, r < l.length ∧
        (∀ j, j < l.length → (l.take r).sum ≤ (l.take j).sum) ∧
        (∀ j, r < j → j < l.length → (l.take r).sum < (l.take j).sum) := by
    have hFne : (Finset.range l.length).Nonempty := ⟨0, Finset.mem_range.mpr hN⟩
    -- the minimum value of the prefix sums
    set m : ℤ := (Finset.range l.length).inf' hFne (fun j => (l.take j).sum)
      with hm
    have hmin : ∀ j, j < l.length → m ≤ (l.take j).sum := fun j hj =>
      Finset.inf'_le _ (Finset.mem_range.mpr hj)
    -- the set of minimizers is nonempty
    have hMne : ((Finset.range l.length).filter
        (fun j => (l.take j).sum = m)).Nonempty := by
      obtain ⟨j, hj, hjm⟩ :=
        Finset.exists_mem_eq_inf' hFne (fun j => (l.take j).sum)
      exact ⟨j, Finset.mem_filter.mpr ⟨hj, hjm.symm⟩⟩
    refine ⟨((Finset.range l.length).filter
        (fun j => (l.take j).sum = m)).max' hMne, ?_, ?_, ?_⟩
    · have := Finset.mem_filter.mp (Finset.max'_mem _ hMne)
      exact Finset.mem_range.mp this.1
    · intro j hj
      have hrm := (Finset.mem_filter.mp (Finset.max'_mem _ hMne)).2
      rw [hrm]
      exact hmin j hj
    · intro j hrj hjN
      have hrm := (Finset.mem_filter.mp (Finset.max'_mem _ hMne)).2
      rw [hrm]
      rcases lt_or_eq_of_le (hmin j hjN) with h | h
      · exact h
      · -- `j` would be a minimizer larger than the maximum minimizer
        exfalso
        have hjM : j ∈ (Finset.range l.length).filter
            (fun j => (l.take j).sum = m) :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjN, h.symm⟩
        have := Finset.le_max' _ j hjM
        omega
  have hr0 : (l.take r).sum ≤ 0 := by simpa using hminr 0 hN
  -- The rotation at `r` dominates.
  have hdom : ∀ k : ℕ, k < l.length → 0 < ((l.rotate r).take (k + 1)).sum := by
    intro k hk
    rcases le_or_gt (k + 1) (l.length - r) with hcase | hcase
    · -- non-wrapping prefix: `S (r + k + 1) - S r`
      rw [rotate_take_sum_of_le l r (k + 1) hrN.le hcase]
      rcases eq_or_lt_of_le (show r + (k + 1) ≤ l.length by omega) with h | h
      · -- the prefix reaches the end of the list: sum is `1 - S r`
        rw [h, List.take_length, hsum]
        linarith
      · -- proper prefix: `r` is the last minimizer, so `S (r + k + 1) > S r`
        linarith [hlast (r + (k + 1)) (by omega) h]
    · -- wrapping prefix: `1 - S r + S (k + 1 - (l.length - r))`
      rw [rotate_take_sum_of_ge l r (k + 1) hrN.le (by omega) (by omega), hsum]
      linarith [hminr (k + 1 - (l.length - r)) (by omega)]
  refine ⟨r, ⟨hrN, hdom⟩, ?_⟩
  rintro r' ⟨hr'N, hdom'⟩
  rcases lt_trichotomy r' r with h | h | h
  · exact (dominating_rotation_unique hsum h hrN hdom' hdom).elim
  · exact h
  · exact (dominating_rotation_unique hsum h hr'N hdom hdom').elim

end MakinenAnalysis
