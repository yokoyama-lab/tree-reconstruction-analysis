/-
# The cycle-lemma orbit count for degree words

Main theorem (`card_dominating_mul`):

  `n * #((degWords n k).filter Dominating) = #(degWords n k)`.

Proof: for `w ∈ degWords n k` the *reversed negated* step list
`negRev w = ((w.map (-·.step)).reverse : List ℤ)` sums to `+1` (since
`lukSum w = -1`) and has entries `≤ 1`, so the Dvoretzky–Motzkin cycle lemma
(`dvoretzky_motzkin`) applies to it.  Prefix sums of `negRev w` are
`lukSum (w.take (w.length - m)) - lukSum w`, whence `w` is `Dominating` iff
*all* nonempty prefix sums of `negRev w` are positive
(`dominating_iff_negRev`; the reversal turns the proper-prefix condition
`lukSum ≥ 0` plus the automatic full-sum `+1 > 0` into exactly the cycle-lemma
positivity condition).  Since `negRev` intertwines rotations up to the index
reflection `r ↦ (n - r) % n` (`negRev_rotate`), each `w ∈ degWords n k` has
*exactly one* rotation index `r < n` with `w.rotate r` dominating
(`existsUnique_dominating_rotate`).  The theorem follows by double counting
the bijection `(w, r) ↦ w.rotate r` from
`(dominating words) ×ˢ range n` onto `degWords n k`.
-/
import Mathlib
import MakinenAnalysis.DegreeWords
import MakinenAnalysis.CycleLemma

namespace MakinenAnalysis

/-! ### The reversed negated step list -/

/-- The reversed, negated Łukasiewicz step list of a degree word: the list to
which the cycle lemma (`dvoretzky_motzkin`, stated for total sum `+1` and
strictly positive prefix sums) applies. -/
def negRev (w : List Deg) : List ℤ :=
  (w.map fun d => -d.step).reverse

@[simp] lemma length_negRev (w : List Deg) : (negRev w).length = w.length := by
  simp [negRev]

/-- The negated step list sums to `- lukSum`. -/
lemma sum_map_neg_step (w : List Deg) :
    (w.map fun d => -d.step).sum = - lukSum w := by
  induction w with
  | nil => simp [lukSum]
  | cons d t ih =>
    have h : lukSum (d :: t) = d.step + lukSum t := by
      rw [lukSum, List.map_cons, List.sum_cons, lukSum]
    rw [List.map_cons, List.sum_cons, ih, h]
    ring

lemma sum_negRev (w : List Deg) : (negRev w).sum = - lukSum w := by
  rw [negRev, List.sum_reverse, sum_map_neg_step]

/-- Every entry of `negRev w` is at most `1` (steps are at least `-1`). -/
lemma negRev_le_one {w : List Deg} : ∀ x ∈ negRev w, x ≤ 1 := by
  intro x hx
  rw [negRev, List.mem_reverse, List.mem_map] at hx
  obtain ⟨d, -, rfl⟩ := hx
  cases d <;> decide

/-! ### Prefix sums of `negRev` -/

/-- `take` of a reverse is the reverse of a `drop`. -/
lemma reverse_take_eq {α : Type*} (l : List α) {m : ℕ} (hm : m ≤ l.length) :
    l.reverse.take m = (l.drop (l.length - m)).reverse := by
  conv_lhs => rw [← List.take_append_drop (l.length - m) l]
  rw [List.reverse_append,
    List.take_append_of_le_length
      (by rw [List.length_reverse, List.length_drop]; omega),
    List.take_of_length_le
      (by rw [List.length_reverse, List.length_drop]; omega)]

lemma sum_drop_eq (l : List ℤ) (j : ℕ) :
    (l.drop j).sum = l.sum - (l.take j).sum := by
  have h : (l.take j).sum + (l.drop j).sum = l.sum := by
    rw [← List.sum_append, List.take_append_drop]
  linarith

/-- Prefix sums of the reversed negated step list are complementary
Łukasiewicz sums: `S^{negRev}_m = lukSum (w.take (|w| - m)) - lukSum w`. -/
lemma sum_take_negRev (w : List Deg) (m : ℕ) (hm : m ≤ w.length) :
    ((negRev w).take m).sum
      = lukSum (w.take (w.length - m)) - lukSum w := by
  rw [negRev, reverse_take_eq _ (by rw [List.length_map]; exact hm),
    List.sum_reverse, List.length_map, sum_drop_eq, sum_map_neg_step,
    ← List.map_take, sum_map_neg_step]
  ring

/-! ### Dominance as cycle-lemma positivity -/

/-- **Bridge**: a degree word with total Łukasiewicz sum `-1` is dominating
iff *all* nonempty prefix sums of its reversed negated step list are
positive.  (Prefixes of the reverse are suffixes; a proper suffix sums to
`-1 - (proper prefix sum)`, so its negation is positive iff the proper
prefix sum is `> -1`; the full prefix sums to `+1 > 0` automatically.) -/
lemma dominating_iff_negRev {w : List Deg} (hsum : lukSum w = -1) :
    Dominating w ↔
      ∀ m : ℕ, m < w.length → 0 < ((negRev w).take (m + 1)).sum := by
  constructor
  · intro hd m hm
    rw [sum_take_negRev w (m + 1) (by omega), hsum]
    rcases Nat.eq_zero_or_pos (w.length - (m + 1)) with h0 | hpos
    · rw [h0]
      norm_num [lukSum]
    · have h := hd (w.length - (m + 1) - 1) (by omega)
      rw [show w.length - (m + 1) - 1 + 1 = w.length - (m + 1) from by omega]
        at h
      linarith
  · intro h j hj
    have h' := h (w.length - (j + 1) - 1) (by omega)
    rw [sum_take_negRev w (w.length - (j + 1) - 1 + 1) (by omega),
      show w.length - (w.length - (j + 1) - 1 + 1) = j + 1 from by omega,
      hsum] at h'
    linarith

/-! ### Rotations -/

/-- Rotation invariance of `degWords` membership (letter counts are
permutation invariants, and rotations are permutations). -/
lemma rotate_mem_degWords {n k : ℕ} {w : List Deg}
    (hw : w ∈ degWords n k) (r : ℕ) : w.rotate r ∈ degWords n k := by
  rw [mem_degWords] at hw ⊢
  exact ⟨by rw [List.length_rotate]; exact hw.1,
    by rw [(List.rotate_perm w r).count_eq]; exact hw.2.1,
    by rw [(List.rotate_perm w r).count_eq]; exact hw.2.2⟩

lemma lukSum_rotate (w : List Deg) (r : ℕ) :
    lukSum (w.rotate r) = lukSum w := by
  rw [lukSum, lukSum, List.map_rotate]
  exact (List.rotate_perm _ _).sum_eq

/-- `negRev` intertwines rotation with the reflected rotation. -/
lemma negRev_rotate (w : List Deg) (r : ℕ) :
    negRev (w.rotate r) = (negRev w).rotate (w.length - r % w.length) := by
  simp only [negRev]
  rw [List.map_rotate, List.reverse_rotate, List.length_map]

/-- Rotating by `r` and then by `(n - r) % n` is the identity. -/
lemma rotate_rotate_sub {w : List Deg} {n : ℕ} (hlen : w.length = n)
    {r : ℕ} (hr : r < n) : (w.rotate r).rotate ((n - r) % n) = w := by
  rw [List.rotate_rotate]
  rcases Nat.eq_zero_or_pos r with rfl | hrpos
  · simp [Nat.mod_self]
  · rw [Nat.mod_eq_of_lt (show n - r < n by omega),
      show r + (n - r) = n from by omega, ← hlen, List.rotate_length]

/-- The reflection `r ↦ (n - r) % n` on `[0, n)` is an involution. -/
lemma sub_mod_inv {n r : ℕ} (hr : r < n) :
    (n - (n - r) % n) % n = r := by
  rcases Nat.eq_zero_or_pos r with rfl | hrpos
  · simp [Nat.mod_self]
  · rw [Nat.mod_eq_of_lt (show n - r < n by omega),
      show n - (n - r) = r from by omega, Nat.mod_eq_of_lt hr]

/-! ### The unique dominating rotation -/

/-- **Unique dominating rotation.**  Every degree word in `degWords n k`
(`n > 0`) has exactly one rotation index `r < n` making it dominating: the
Dvoretzky–Motzkin cycle lemma applied to the reversed negated step list,
transported along the index reflection `r ↦ (n - r) % n`. -/
lemma existsUnique_dominating_rotate {n k : ℕ} (hn : 0 < n) {w : List Deg}
    (hw : w ∈ degWords n k) :
    ∃! r : ℕ, r < n ∧ Dominating (w.rotate r) := by
  have hlen : w.length = n := (mem_degWords.mp hw).1
  have hsumw : lukSum w = -1 := lukSum_degWords hw
  set l : List ℤ := negRev w with hl
  have hlenl : l.length = n := by rw [hl, length_negRev, hlen]
  have hne : l ≠ [] := List.length_pos_iff.mp (by rw [hlenl]; exact hn)
  have hsuml : l.sum = 1 := by
    rw [hl, sum_negRev, hsumw]
    ring
  have hle : ∀ x ∈ l, x ≤ 1 := by
    rw [hl]
    exact negRev_le_one
  have hrot_mod : ∀ x : ℕ, l.rotate (x % n) = l.rotate x := by
    intro x
    rw [← hlenl]
    exact List.rotate_mod l x
  -- transport of the dominance condition along the reflection
  have corr : ∀ r : ℕ, r < n →
      (Dominating (w.rotate r) ↔
        ∀ m : ℕ, m < n → 0 < ((l.rotate (n - r)).take (m + 1)).sum) := by
    intro r hr
    have h1 : lukSum (w.rotate r) = -1 := by rw [lukSum_rotate, hsumw]
    have h3 : negRev (w.rotate r) = l.rotate (n - r) := by
      rw [hl, negRev_rotate, hlen, Nat.mod_eq_of_lt hr]
    rw [dominating_iff_negRev h1, List.length_rotate, hlen, h3]
  obtain ⟨r', ⟨hr'l, hpos⟩, huniq⟩ := dvoretzky_motzkin l hne hle hsuml
  have hr' : r' < n := by rwa [hlenl] at hr'l
  refine ⟨(n - r') % n, ⟨Nat.mod_lt _ hn, ?_⟩, ?_⟩
  · -- existence: the reflected cycle-lemma index dominates
    rw [corr ((n - r') % n) (Nat.mod_lt _ hn)]
    intro m hm
    have heq2 : l.rotate (n - (n - r') % n) = l.rotate r' := by
      rw [← hrot_mod (n - (n - r') % n), sub_mod_inv hr']
    rw [heq2]
    exact hpos m (by rwa [hlenl])
  · -- uniqueness: any dominating index reflects to the cycle-lemma index
    rintro r ⟨hr, hdom⟩
    have hp := (corr r hr).mp hdom
    have hkey : (n - r) % n = r' := by
      refine huniq _ ⟨by rw [hlenl]; exact Nat.mod_lt _ hn, ?_⟩
      intro m hm
      rw [hrot_mod (n - r)]
      exact hp m (by rwa [hlenl] at hm)
    have hfix := sub_mod_inv hr
    rw [hkey] at hfix
    exact hfix.symm

/-! ### The orbit count -/

/-- Degree words are nonempty (they contain `k + 1 ≥ 1` leaves), so there
are none of length `0`. -/
lemma degWords_zero (k : ℕ) : degWords 0 k = ∅ := by
  ext w
  simp only [Finset.notMem_empty, iff_false, mem_degWords]
  rintro ⟨hlen, -, hleaf⟩
  have hle := List.count_le_length (a := Deg.leaf) (l := w)
  omega

/-- **Cycle-lemma orbit count (Dvoretzky–Motzkin).**  Rotations partition
`degWords n k` into orbits of size `n`, each containing exactly one
dominating word:

  `n * #((degWords n k).filter Dominating) = #(degWords n k)`.

Proved by double counting: `(w, r) ↦ w.rotate r` is a bijection from
`(dominating degree words) ×ˢ range n` onto `degWords n k`. -/
theorem card_dominating_mul (n k : ℕ) :
    n * ((degWords n k).filter Dominating).card = (degWords n k).card := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [degWords_zero]
    simp
  · have key :
        (((degWords n k).filter Dominating) ×ˢ Finset.range n).card
          = (degWords n k).card := by
      apply Finset.card_nbij (i := fun p => p.1.rotate p.2)
      · -- maps to `degWords n k`
        rintro ⟨w, r⟩ hp
        obtain ⟨hpD, -⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hp)
        exact Finset.mem_coe.mpr
          (rotate_mem_degWords (Finset.mem_filter.mp hpD).1 r)
      · -- injective on the product
        rintro ⟨w₁, r₁⟩ hp₁ ⟨w₂, r₂⟩ hp₂ heq
        obtain ⟨hpD₁, hpr₁⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hp₁)
        obtain ⟨hpD₂, hpr₂⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hp₂)
        obtain ⟨hw₁, hd₁⟩ := Finset.mem_filter.mp hpD₁
        obtain ⟨hw₂, hd₂⟩ := Finset.mem_filter.mp hpD₂
        have hr₁ : r₁ < n := Finset.mem_range.mp hpr₁
        have hr₂ : r₂ < n := Finset.mem_range.mp hpr₂
        have hlen₁ : w₁.length = n := (mem_degWords.mp hw₁).1
        have hlen₂ : w₂.length = n := (mem_degWords.mp hw₂).1
        have heq' : w₁.rotate r₁ = w₂.rotate r₂ := heq
        have hmodrot : ∀ x : ℕ, w₁.rotate (x % n) = w₁.rotate x := by
          intro x
          rw [← hlen₁]
          exact List.rotate_mod w₁ x
        -- step 1: `w₂` is a rotation of `w₁` …
        have h : w₁.rotate (r₁ + (n - r₂) % n) = w₂ := by
          rw [← List.rotate_rotate, heq', rotate_rotate_sub hlen₂ hr₂]
        -- … so by uniqueness of the dominating rotation of `w₁`, `w₂ = w₁`
        obtain ⟨rr, -, hu⟩ := existsUnique_dominating_rotate hn hw₁
        have h0 : (0 : ℕ) = rr :=
          hu 0 ⟨hn, by rw [List.rotate_zero]; exact hd₁⟩
        have hs : (r₁ + (n - r₂) % n) % n = rr := by
          refine hu _ ⟨Nat.mod_lt _ hn, ?_⟩
          rw [hmodrot, h]
          exact hd₂
        have hww : w₂ = w₁ := by
          rw [← h, ← hmodrot, hs, ← h0, List.rotate_zero]
        rw [hww] at heq'
        -- step 2: uniqueness of the dominating rotation of `w₁.rotate r₁`
        -- forces `r₁ = r₂`
        obtain ⟨rr₂, -, hu₂⟩ :=
          existsUnique_dominating_rotate hn (rotate_mem_degWords hw₁ r₁)
        have e₁ : (n - r₁) % n = rr₂ :=
          hu₂ _ ⟨Nat.mod_lt _ hn,
            by rw [rotate_rotate_sub hlen₁ hr₁]; exact hd₁⟩
        have e₂ : (n - r₂) % n = rr₂ :=
          hu₂ _ ⟨Nat.mod_lt _ hn,
            by rw [heq', rotate_rotate_sub hlen₁ hr₂]; exact hd₁⟩
        have g₁ := sub_mod_inv hr₁
        have g₂ := sub_mod_inv hr₂
        rw [e₁] at g₁
        rw [e₂] at g₂
        have hrr : r₁ = r₂ := g₁.symm.trans g₂
        rw [hww, hrr]
      · -- surjective onto `degWords n k`
        intro u hu
        have hu' : u ∈ degWords n k := Finset.mem_coe.mp hu
        obtain ⟨r, ⟨hr, hdom⟩, -⟩ := existsUnique_dominating_rotate hn hu'
        have hlenu : u.length = n := (mem_degWords.mp hu').1
        exact ⟨(u.rotate r, (n - r) % n),
          Finset.mem_coe.mpr (Finset.mem_product.mpr
            ⟨Finset.mem_filter.mpr ⟨rotate_mem_degWords hu' r, hdom⟩,
              Finset.mem_range.mpr (Nat.mod_lt _ hn)⟩),
          rotate_rotate_sub hlenu hr⟩
    rw [Finset.card_product, Finset.card_range] at key
    rw [← key, Nat.mul_comm]

end MakinenAnalysis
