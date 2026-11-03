/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.

# M's informative comparisons on an arbitrary sequence: `2n - h - r`

Run Mäkinen's stack on any finite sequence over a linear order (no
distinctness, no pattern avoidance).  Each new element `x` pops the stack
entries below it, from the top, and is then pushed.  M compares `x` with the
popped entries and, if something is left, once more with the entry that stops
it; the comparison with the sentinel is skipped.  With `k` pops from a stack of
height `m` that is `min (k + 1) m` comparisons.

This file proves, for every list `A` of length `n`:

* `costM_add_records`: `cost + h + r = 2n`, where `h` is the final stack height
  and `r` the number of left-to-right maxima (elements greater than every
  earlier one);
* `stackRecords_ge_three`, `costM_le_seq`: `h + r ≥ 3` when `n ≥ 2`, hence at
  most `2n - 3` comparisons.

The proof: a step costs `k + 1 - e` and changes the height by `1 - k`, where `e`
is `1` iff the step empties the stack, so the sum telescopes to
`2n - h - (#emptying steps)`.  A step empties the stack iff `x` exceeds every
earlier element, because every earlier element is at most some entry still on
the stack (an entry is popped only by a larger one) — `Inv`.

On i-p sequences of trees this is `(n - 1) + S - Q` of `OnePass.costM_eq` with
`r = Q + 1`; here no tree structure is used.
-/
import Mathlib.Order.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic

namespace MakinenAnalysis.StackRecords

variable {α : Type*} [LinearOrder α]

/-- Number of entries popped by `x` (top first). -/
def pops (s : List α) (x : α) : ℕ := (s.takeWhile (· < x)).length

/-- The stack after `x`: the entries below `x` are popped, then `x` is pushed. -/
def push (s : List α) (x : α) : List α := x :: s.dropWhile (· < x)

/-- M's comparisons for the rest `xs`, from stack `s` (sentinel skipped). -/
def cost : List α → List α → ℕ
  | _, [] => 0
  | s, x :: xs => min (pops s x + 1) s.length + cost (push s x) xs

/-- The stack after reading `xs` from `s`. -/
def final : List α → List α → List α
  | s, [] => s
  | s, x :: xs => final (push s x) xs

/-- Left-to-right maxima of `xs`, after the elements `P` already read. -/
def records : List α → List α → ℕ
  | _, [] => 0
  | P, x :: xs => (if ∀ y ∈ P, y < x then 1 else 0) + records (P ++ [x]) xs

theorem pops_add_length_dropWhile (s : List α) (x : α) :
    pops s x + (s.dropWhile (· < x)).length = s.length := by
  unfold pops
  have := congrArg List.length (List.takeWhile_append_dropWhile (p := fun y => decide (y < x)) (l := s))
  rw [List.length_append] at this
  exact this

theorem pops_le (s : List α) (x : α) : pops s x ≤ s.length := by
  have := pops_add_length_dropWhile s x; omega

/-- All of `s` is popped iff every entry is below `x`. -/
theorem pops_eq_length_iff (s : List α) (x : α) :
    pops s x = s.length ↔ ∀ z ∈ s, z < x := by
  induction s with
  | nil => simp [pops]
  | cons z s ih =>
    unfold pops at ih ⊢
    by_cases hz : z < x
    · rw [List.takeWhile_cons_of_pos (by simpa using hz)]
      simp only [List.length_cons, Nat.add_right_cancel_iff, List.mem_cons, forall_eq_or_imp]
      rw [ih]; exact ⟨fun h => ⟨hz, h⟩, fun h => h.2⟩
    · rw [List.takeWhile_cons_of_neg (by simpa using hz)]
      simp only [List.length_nil, List.length_cons, List.mem_cons, forall_eq_or_imp]
      constructor
      · intro h; omega
      · intro h; exact absurd h.1 hz

theorem mem_dropWhile_or (s : List α) (x z : α) (hz : z ∈ s) :
    z < x ∨ z ∈ s.dropWhile (· < x) := by
  induction s with
  | nil => simp at hz
  | cons y s ih =>
    by_cases hy : y < x
    · rw [List.dropWhile_cons_of_pos (by simpa using hy)]
      rcases List.mem_cons.mp hz with rfl | hz
      · exact Or.inl hy
      · exact ih hz
    · rw [List.dropWhile_cons_of_neg (by simpa using hy)]
      exact Or.inr hz

theorem mem_of_mem_dropWhile' (s : List α) (x z : α) (hz : z ∈ s.dropWhile (· < x)) : z ∈ s := by
  induction s with
  | nil => simp at hz
  | cons y s ih =>
    by_cases hy : y < x
    · rw [List.dropWhile_cons_of_pos (by simpa using hy)] at hz
      exact List.mem_cons_of_mem _ (ih hz)
    · rw [List.dropWhile_cons_of_neg (by simpa using hy)] at hz
      exact hz

/-- The invariant: the stack holds earlier elements, and every earlier element
    is at most some stack entry. -/
def Inv (P s : List α) : Prop := (∀ z ∈ s, z ∈ P) ∧ ∀ y ∈ P, ∃ z ∈ s, y ≤ z

theorem inv_nil : Inv ([] : List α) [] := ⟨by simp, by simp⟩

theorem inv_push {P s : List α} (h : Inv P s) (x : α) : Inv (P ++ [x]) (push s x) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · intro z hz
    simp only [push, List.mem_cons] at hz
    rcases hz with rfl | hz
    · simp
    · exact List.mem_append_left _ (h1 z (mem_of_mem_dropWhile' s x z hz))
  · intro y hy
    rw [List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · obtain ⟨z, hz, hyz⟩ := h2 y hy
      rcases mem_dropWhile_or s x z hz with hzx | hzd
      · exact ⟨x, by simp [push], le_of_lt (lt_of_le_of_lt hyz hzx)⟩
      · exact ⟨z, by simp [push, hzd], hyz⟩
    · exact ⟨y, by simp [push], le_rfl⟩

/-- Under the invariant, a step empties the stack iff it is a record. -/
theorem empties_iff_record {P s : List α} (h : Inv P s) (x : α) :
    pops s x = s.length ↔ ∀ y ∈ P, y < x := by
  rw [pops_eq_length_iff]
  constructor
  · intro hs y hy
    obtain ⟨z, hz, hyz⟩ := h.2 y hy
    exact lt_of_le_of_lt hyz (hs z hz)
  · intro hP z hz
    exact hP z (h.1 z hz)

theorem length_push (s : List α) (x : α) :
    (push s x).length + pops s x = s.length + 1 := by
  have := pops_add_length_dropWhile s x
  simp only [push, List.length_cons]; omega

/-- **The telescoping identity**, from any state satisfying the invariant. -/
theorem cost_add_records_aux :
    ∀ (xs P s : List α), Inv P s →
      cost s xs + (final s xs).length + records P xs = 2 * xs.length + s.length := by
  intro xs
  induction xs with
  | nil => intro P s _; simp [cost, final, records]
  | cons x xs ih =>
    intro P s h
    have ih' := ih (P ++ [x]) (push s x) (inv_push h x)
    have hl := length_push s x
    have hk := pops_le s x
    have he := empties_iff_record h x
    simp only [cost, final, records, List.length_cons]
    by_cases hr : ∀ y ∈ P, y < x
    · rw [if_pos hr]
      have := he.mpr hr
      rw [show min (pops s x + 1) s.length = s.length by omega]
      omega
    · rw [if_neg hr]
      have : pops s x ≠ s.length := fun h' => hr (he.mp h')
      rw [show min (pops s x + 1) s.length = pops s x + 1 by omega]
      omega

/-- **`2n - h - r`.**  On every sequence over a linear order, M's informative
    comparisons, the final stack height `h` and the number `r` of left-to-right
    maxima add up to twice the length. -/
theorem costM_add_records (A : List α) :
    cost [] A + (final [] A).length + records [] A = 2 * A.length := by
  have := cost_add_records_aux A [] [] inv_nil
  simpa using this

/-- From a nonempty stack, reading a nonempty rest leaves at least two entries
    or meets a record. -/
theorem final_two_or_record :
    ∀ (xs P s : List α), Inv P s → s ≠ [] → xs ≠ [] →
      2 ≤ (final s xs).length ∨ 1 ≤ records P xs := by
  intro xs
  induction xs with
  | nil => intro _ _ _ _ h; exact absurd rfl h
  | cons x xs ih =>
    intro P s h hs _
    simp only [final, records]
    by_cases hr : ∀ y ∈ P, y < x
    · right; rw [if_pos hr]; omega
    · cases xs with
      | nil =>
        left
        simp only [final]
        have he : pops s x ≠ s.length := fun h' => hr ((empties_iff_record h x).mp h')
        have hl := length_push s x
        have hk := pops_le s x
        have : 1 ≤ s.length := List.length_pos_iff.mpr hs
        omega
      | cons y ys =>
        rcases ih (P ++ [x]) (push s x) (inv_push h x) (by simp [push]) (by simp) with h2 | h2
        · left; exact h2
        · right; omega

theorem final_ne_nil : ∀ (xs s : List α), s ≠ [] ∨ xs ≠ [] → final s xs ≠ [] := by
  intro xs
  induction xs with
  | nil => intro s h; simpa [final] using h
  | cons x xs ih => intro s _; exact ih (push s x) (Or.inl (by simp [push]))

/-- `h + r ≥ 3` once there are two elements. -/
theorem stackRecords_ge_three (A : List α) (hA : 2 ≤ A.length) :
    3 ≤ (final [] A).length + records [] A := by
  match A, hA with
  | x :: y :: ys, _ =>
    have h0 : push ([] : List α) x = [x] := by simp [push]
    have hi : Inv ([] ++ [x]) (push [] x) := inv_push inv_nil x
    have hfin : final [] (x :: y :: ys) = final (push [] x) (y :: ys) := rfl
    have hrec : records [] (x :: y :: ys) = 1 + records ([] ++ [x]) (y :: ys) := by
      simp [records]
    rw [hfin, hrec]
    have hne := final_ne_nil (y :: ys) (push [] x) (Or.inl (by simp [push]))
    have h1 : 1 ≤ (final (push [] x) (y :: ys)).length := List.length_pos_iff.mpr hne
    rcases final_two_or_record (y :: ys) _ _ hi (by simp [push]) (by simp) with h2 | h2 <;> omega

/-- **At most `2n - 3`** on every sequence of length `n ≥ 2`. -/
theorem costM_le_seq (A : List α) (hA : 2 ≤ A.length) : cost [] A ≤ 2 * A.length - 3 := by
  have h1 := costM_add_records A
  have h2 := stackRecords_ge_three A hA
  omega

/-! ## Computational checks -/

/-- `5 1 4 2 3 6`: M compares 0+1+2+1+2+3 = 9 times, the stack ends `[6]`,
    and the records are `5, 6`; `9 + 1 + 2 = 12`. -/
example : cost ([] : List ℕ) [5, 1, 4, 2, 3, 6] = 9 := by decide
example : (final ([] : List ℕ) [5, 1, 4, 2, 3, 6]).length = 1 := by decide
example : records ([] : List ℕ) [5, 1, 4, 2, 3, 6] = 2 := by decide
/-- Repeated values are allowed. -/
example : cost ([] : List ℕ) [2, 2, 1, 3] + (final [] [2, 2, 1, 3]).length
    + records [] [2, 2, 1, 3] = 8 := by decide

end MakinenAnalysis.StackRecords
