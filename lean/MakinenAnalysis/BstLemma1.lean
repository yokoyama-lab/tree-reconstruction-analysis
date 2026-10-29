import MakinenAnalysis.BstPerm

/-!
# A2 Lemma 1: `h` and `L` read off the inverse permutation

Insert the keys `0, …, n-1` in the order of the list `l` (a permutation) into an
empty BST (`BstPerm.bstOfList`), and write `w_k = l.idxOf k` for the insertion time
of key `k` (so `w = σ⁻¹`).  A2's Lemma 1 says

* `h ≥ m` iff the `m` largest keys were inserted from the largest down,
  `w_{n-1} < w_{n-2} < ⋯ < w_{n-m}`: `h` is the length of the final descending run
  of `w` (`lemma1_h`);
* `L` is the number of peaks of `w` with `w_{-1} = w_n = 0`: key `k` is a leaf iff
  both neighbours `k ± 1` (when present) were inserted before it (`lemma1_L`).

| here | A2 |
|---|---|
| `lemma1_h` | Lemma 1, first half (`h` = final descending run of `w`) |
| `lemma1_L` | Lemma 1, second half (`L` = number of peaks of `w`) |

The proofs generalise the key set to an interval `[a, b)`: the first key `x`
becomes the root, and the left and right subtrees are built from the keys of the
intervals `[a, x)` and `[x+1, b)` in their original order (`bstOfList_cons`).
"Inserted before" is the sublist relation `[a, b] <+ l` (`Before`), which
restricts to sublists by `filter` without any index bookkeeping; `before_iff_idxOf`
converts it to the comparison of insertion times.
-/

namespace MakinenAnalysis

open Finset

/-! ## 1. "Inserted before" -/

/-- Key `a` is inserted before key `b` in the insertion order `l`. -/
def Before (l : List ℕ) (a b : ℕ) : Prop := [a, b].Sublist l

instance (l : List ℕ) (a b : ℕ) : Decidable (Before l a b) :=
  inferInstanceAs (Decidable ([a, b].Sublist l))

lemma before_cons_left {x b : ℕ} {r : List ℕ} : Before (x :: r) x b ↔ b ∈ r := by
  simp [Before, List.cons_sublist_cons]

lemma before_cons_ne {x a b : ℕ} {r : List ℕ} (ha : a ≠ x) :
    Before (x :: r) a b ↔ Before r a b := by
  unfold Before
  constructor
  · intro h
    rcases List.sublist_cons_iff.mp h with h | ⟨r', hr', _⟩
    · exact h
    · simp only [List.cons.injEq] at hr'; exact absurd hr'.1 ha
  · intro h; exact h.cons x

lemma not_before_head {x a : ℕ} {r : List ℕ} (hx : x ∉ r) : ¬ Before (x :: r) a x := by
  intro h
  rcases List.sublist_cons_iff.mp h with h | ⟨r', hr', h'⟩
  · exact hx (h.subset (by simp))
  · simp only [List.cons.injEq] at hr'
    rw [← hr'.2] at h'
    exact hx (h'.subset (by simp))

lemma before_filter {r : List ℕ} {p : ℕ → Bool} {a b : ℕ} (ha : p a) (hb : p b) :
    Before (r.filter p) a b ↔ Before r a b := by
  unfold Before
  constructor
  · intro h; exact h.trans (List.filter_sublist)
  · intro h
    have := h.filter p
    simpa [List.filter, ha, hb] using this

lemma idxOf_cons_of_ne {x a : ℕ} {r : List ℕ} (h : x ≠ a) : (x :: r).idxOf a = r.idxOf a + 1 := by
  rw [List.idxOf_cons, show (x == a) = false from beq_false_of_ne h]; rfl

/-- `Before` is the comparison of insertion times `w_a < w_b`. -/
theorem before_iff_idxOf : ∀ {l : List ℕ}, l.Nodup → ∀ {a b : ℕ}, a ∈ l → b ∈ l → a ≠ b →
    (Before l a b ↔ l.idxOf a < l.idxOf b)
  | [], _, _, _, ha, _, _ => absurd ha (by simp)
  | x :: r, hl, a, b, ha, hb, hab => by
    have hx : x ∉ r := (List.nodup_cons.mp hl).1
    have hr : r.Nodup := (List.nodup_cons.mp hl).2
    by_cases hax : a = x
    · subst hax
      have hb' : b ∈ r := by
        rcases List.mem_cons.mp hb with h | h
        · exact absurd h.symm hab
        · exact h
      rw [before_cons_left, List.idxOf_cons_self, idxOf_cons_of_ne hab]
      simp [hb']
    · by_cases hbx : b = x
      · subst hbx
        rw [List.idxOf_cons_self]
        simp only [Nat.not_lt_zero, iff_false]
        exact not_before_head hx
      · have ha' : a ∈ r := by
          rcases List.mem_cons.mp ha with h | h
          · exact absurd h hax
          · exact h
        have hb' : b ∈ r := by
          rcases List.mem_cons.mp hb with h | h
          · exact absurd h hbx
          · exact h
        rw [before_cons_ne hax, before_iff_idxOf hr ha' hb' hab,
          idxOf_cons_of_ne (Ne.symm hax), idxOf_cons_of_ne (Ne.symm hbx)]
        omega

/-! ## 2. Insertion orders of an interval of keys -/

/-- `l` is an ordering of the keys `a, a+1, …, b-1`. -/
def IsPermIco (l : List ℕ) (a b : ℕ) : Prop := l.Nodup ∧ ∀ k, k ∈ l ↔ a ≤ k ∧ k < b

lemma IsPermIco.length {l : List ℕ} {a b : ℕ} (h : IsPermIco l a b) : l.length = b - a := by
  have h1 : l.toFinset = Finset.Ico a b := by
    ext k; rw [List.mem_toFinset, h.2 k, Finset.mem_Ico]
  rw [← List.toFinset_card_of_nodup h.1, h1, Nat.card_Ico]

lemma IsPermIco.head {x a b : ℕ} {r : List ℕ} (h : IsPermIco (x :: r) a b) :
    a ≤ x ∧ x < b := (h.2 x).1 (by simp)

lemma IsPermIco.mem_tail {x a b k : ℕ} {r : List ℕ} (h : IsPermIco (x :: r) a b) :
    k ∈ r ↔ a ≤ k ∧ k < b ∧ k ≠ x := by
  have hx : x ∉ r := (List.nodup_cons.mp h.1).1
  constructor
  · intro hk
    have := (h.2 k).1 (List.mem_cons_of_mem x hk)
    exact ⟨this.1, this.2, fun e => hx (e ▸ hk)⟩
  · rintro ⟨h1, h2, h3⟩
    have := (h.2 k).2 ⟨h1, h2⟩
    simpa [h3] using this

lemma IsPermIco.left {x a b : ℕ} {r : List ℕ} (h : IsPermIco (x :: r) a b) :
    IsPermIco (r.filter (· < x)) a x := by
  refine ⟨(List.nodup_cons.mp h.1).2.filter _, fun k => ?_⟩
  rw [List.mem_filter, h.mem_tail, decide_eq_true_iff]
  have := h.head
  constructor
  · rintro ⟨⟨h1, _, _⟩, h4⟩; exact ⟨h1, h4⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by omega, by omega⟩, h2⟩

lemma IsPermIco.right {x a b : ℕ} {r : List ℕ} (h : IsPermIco (x :: r) a b) :
    IsPermIco (r.filter (x < ·)) (x + 1) b := by
  refine ⟨(List.nodup_cons.mp h.1).2.filter _, fun k => ?_⟩
  rw [List.mem_filter, h.mem_tail, decide_eq_true_iff]
  have := h.head
  constructor
  · rintro ⟨⟨_, h2, _⟩, h4⟩; exact ⟨h4, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, h2, by omega⟩, h1⟩

lemma numNodes_shape_bstOfList : ∀ (N : ℕ) (l : List ℕ), l.length = N → l.Nodup →
    (shape (bstOfList l)).numNodes = l.length := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro l hN hl
    cases l with
    | nil => rfl
    | cons x r =>
      have hx : x ∉ r := (List.nodup_cons.mp hl).1
      have hr : r.Nodup := (List.nodup_cons.mp hl).2
      have hlt : (r.filter (· < x)).length < N := by
        have := List.length_filter_le (· < x) r; simp at hN; omega
      have hgt : (r.filter (x < ·)).length < N := by
        have := List.length_filter_le (x < ·) r; simp at hN; omega
      rw [bstOfList_cons, shape_node, BinaryTree.numNodes,
        ih _ hlt _ rfl (hr.filter _), ih _ hgt _ rfl (hr.filter _)]
      -- the two filters partition `r`, since `x ∉ r`
      have hpart : (r.filter (· < x)).length + (r.filter (x < ·)).length = r.length := by
        have h1 := List.length_eq_length_filter_add (l := r) (fun y => decide (y < x))
        have h2 : r.filter (fun y => !decide (y < x)) = r.filter (x < ·) := by
          refine List.filter_congr (fun y hy => ?_)
          have : y ≠ x := fun e => hx (e ▸ hy)
          by_cases h : y < x
          · simp [h, show ¬ x < y by omega]
          · simp [h, show x < y by omega]
        rw [h2] at h1; omega
      simp only [List.length_cons]; omega

/-! ## 3. The leaf count -/

lemma leaves_node_nat (sl sr : T) :
    leaves (.node () sl sr) = leaves sl + leaves sr
      + (if sl.numNodes + sr.numNodes = 0 then 1 else 0) := by
  have h := leaves_node () sl sr
  have : ((leaves (.node () sl sr) : ℕ) : ℚ)
      = ((leaves sl + leaves sr + (if sl.numNodes + sr.numNodes = 0 then 1 else 0) : ℕ) : ℚ) := by
    rw [h]; push_cast; split_ifs <;> simp
  exact_mod_cast this

/-- The peak predicate on the interval `[a, b)`: both neighbours, when present,
    were inserted earlier. -/
def IsPeak (l : List ℕ) (a b k : ℕ) : Prop :=
  (k = a ∨ Before l (k - 1) k) ∧ (k + 1 = b ∨ Before l (k + 1) k)

instance (l : List ℕ) (a b k : ℕ) : Decidable (IsPeak l a b k) := by
  unfold IsPeak; infer_instance

/-- **Leaves are peaks** (general interval form). -/
theorem leaves_eq_peaks : ∀ (N : ℕ) (l : List ℕ) (a b : ℕ), l.length = N → IsPermIco l a b →
    leaves (shape (bstOfList l)) = ((Finset.Ico a b).filter (IsPeak l a b)).card := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro l a b hN hl
    cases l with
    | nil =>
      have : b - a = 0 := by have := hl.length; simp at this; omega
      have hE : Finset.Ico a b = ∅ := by rw [Finset.Ico_eq_empty_iff]; omega
      simp [hE, bstOfList]
    | cons x r =>
      have hx : x ∉ r := (List.nodup_cons.mp hl.1).1
      obtain ⟨hax, hxb⟩ := hl.head
      set L := r.filter (· < x)
      set R := r.filter (x < ·)
      have hL := hl.left
      have hR := hl.right
      have hLlen := hL.length
      have hRlen := hR.length
      have hlen := hl.length
      have hrN : r.length + 1 = N := by simpa using hN
      have hrl : r.length + 1 = b - a := by simpa using hlen
      have hLN : L.length < N := by rw [hLlen]; omega
      have hRN : R.length < N := by rw [hRlen]; omega
      rw [bstOfList_cons, shape_node, leaves_node_nat,
        ih _ hLN L a x rfl hL, ih _ hRN R (x + 1) b rfl hR,
        numNodes_shape_bstOfList _ L rfl hL.1, numNodes_shape_bstOfList _ R rfl hR.1,
        hLlen, hRlen]
      simp only [Finset.card_filter]
      rw [← Finset.sum_Ico_consecutive _ hax hxb.le, Finset.sum_eq_sum_Ico_succ_bot hxb]
      -- membership facts in the tail
      have memr : ∀ k, a ≤ k → k < b → k ≠ x → k ∈ r := fun k h1 h2 h3 =>
        hl.mem_tail.mpr ⟨h1, h2, h3⟩
      -- left part
      have hleft : ∑ k ∈ Finset.Ico a x, (if IsPeak (x :: r) a b k then 1 else 0)
          = ∑ k ∈ Finset.Ico a x, (if IsPeak L a x k then 1 else 0) := by
        refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [Finset.mem_Ico] at hk
        congr 1
        apply propext
        unfold IsPeak
        have e1 : (k = a ∨ Before (x :: r) (k - 1) k) ↔ (k = a ∨ Before L (k - 1) k) := by
          by_cases hka : k = a
          · simp [hka]
          · rw [before_cons_ne (by omega),
              show Before L (k - 1) k ↔ Before r (k - 1) k from
                before_filter (by simpa using (show k - 1 < x by omega)) (by simpa using hk.2)]
        have e2 : (k + 1 = b ∨ Before (x :: r) (k + 1) k) ↔ (k + 1 = x ∨ Before L (k + 1) k) := by
          by_cases hkx : k + 1 = x
          · simp only [hkx, true_or, iff_true]
            right; rw [before_cons_left]; exact memr k hk.1 (by omega) (by omega)
          · rw [before_cons_ne (by omega),
              show Before L (k + 1) k ↔ Before r (k + 1) k from
                before_filter (by simpa using (show k + 1 < x by omega)) (by simpa using hk.2)]
            simp only [show ¬ k + 1 = b by omega, hkx, false_or]
        rw [e1, e2]
      -- right part
      have hright : ∑ k ∈ Finset.Ico (x + 1) b, (if IsPeak (x :: r) a b k then 1 else 0)
          = ∑ k ∈ Finset.Ico (x + 1) b, (if IsPeak R (x + 1) b k then 1 else 0) := by
        refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [Finset.mem_Ico] at hk
        congr 1
        apply propext
        unfold IsPeak
        have e1 : (k = a ∨ Before (x :: r) (k - 1) k) ↔ (k = x + 1 ∨ Before R (k - 1) k) := by
          by_cases hkx : k = x + 1
          · simp only [hkx, true_or, iff_true]
            right; rw [show x + 1 - 1 = x by omega, before_cons_left]
            exact memr (x + 1) (by omega) (by omega) (by omega)
          · rw [before_cons_ne (by omega),
              show Before R (k - 1) k ↔ Before r (k - 1) k from
                before_filter (by simpa using (show x < k - 1 by omega)) (by simpa using hk.1)]
            simp only [show ¬ k = a by omega, hkx, false_or]
        have e2 : (k + 1 = b ∨ Before (x :: r) (k + 1) k) ↔ (k + 1 = b ∨ Before R (k + 1) k) := by
          by_cases hkb : k + 1 = b
          · simp [hkb]
          · rw [before_cons_ne (by omega),
              show Before R (k + 1) k ↔ Before r (k + 1) k from
                before_filter (by simpa using (show x < k + 1 by omega)) (by simpa using hk.1)]
        rw [e1, e2]
      -- the root
      have hroot : (if IsPeak (x :: r) a b x then 1 else 0)
          = (if x - a + (b - (x + 1)) = 0 then 1 else 0) := by
        congr 1
        apply propext
        unfold IsPeak
        have n1 : ¬ Before (x :: r) (x - 1) x := not_before_head hx
        have n2 : ¬ Before (x :: r) (x + 1) x := not_before_head hx
        simp only [n1, n2, or_false]
        omega
      rw [hleft, hright, hroot]
      ring

/-! ## 4. The final stack height -/

/-- **`h ≥ m` iff the `m` largest keys came in descending order** (general interval form). -/
theorem rlen_iff_desc : ∀ (N : ℕ) (l : List ℕ) (a b : ℕ), l.length = N → IsPermIco l a b →
    ∀ m, 1 ≤ m → m ≤ b - a →
      (m ≤ rlen (shape (bstOfList l)) ↔ ∀ j, j + 1 < m → Before l (b - 1 - j) (b - 2 - j)) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro l a b hN hl m hm1 hm2
    cases l with
    | nil => have := hl.length; simp at this; omega
    | cons x r =>
      have hx : x ∉ r := (List.nodup_cons.mp hl.1).1
      obtain ⟨hax, hxb⟩ := hl.head
      set L := r.filter (· < x)
      set R := r.filter (x < ·)
      have hL := hl.left
      have hR := hl.right
      have hLlen := hL.length
      have hRlen := hR.length
      have hlen := hl.length
      have hrN : r.length + 1 = N := by simpa using hN
      have hrl : r.length + 1 = b - a := by simpa using hlen
      have hLN : L.length < N := by rw [hLlen]; omega
      have hRN : R.length < N := by rw [hRlen]; omega
      have memr : ∀ k, a ≤ k → k < b → k ≠ x → k ∈ r := fun k h1 h2 h3 =>
        hl.mem_tail.mpr ⟨h1, h2, h3⟩
      rw [bstOfList_cons, shape_node, rlen_node, numNodes_shape_bstOfList _ R rfl hR.1, hRlen]
      by_cases hxb1 : x + 1 = b
      · -- the right subtree is empty: `x = b - 1` is the maximum, `h = 1 + h(left)`
        rw [if_pos (by omega)]
        rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm
        · simp only [le_add_iff_nonneg_left, zero_le, true_iff]
          intro j hj; omega
        · have hIH := ih _ hLN L a x rfl hL (m - 1) (by omega) (by omega)
          rw [show m ≤ rlen (shape (bstOfList L)) + 1 ↔ m - 1 ≤ rlen (shape (bstOfList L)) by
            omega, hIH]
          constructor
          · intro H j hj
            rcases Nat.eq_zero_or_pos j with rfl | hj0
            · rw [show b - 1 - 0 = x by omega, before_cons_left]
              exact memr _ (by omega) (by omega) (by omega)
            · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
              have := H j' (by omega)
              rw [show b - 1 - (j' + 1) = x - 1 - j' by omega,
                show b - 2 - (j' + 1) = x - 2 - j' by omega,
                before_cons_ne (by omega),
                ← before_filter (p := (· < x)) (by simp; omega) (by simp; omega)]
              exact this
          · intro H j' hj'
            have := H (j' + 1) (by omega)
            rw [show b - 1 - (j' + 1) = x - 1 - j' by omega,
              show b - 2 - (j' + 1) = x - 2 - j' by omega,
              before_cons_ne (by omega),
              ← before_filter (p := (· < x)) (by simp; omega) (by simp; omega)] at this
            exact this
      · -- the right subtree is not empty: `h = h(right)`
        rw [if_neg (by omega)]
        by_cases hmR : m ≤ b - (x + 1)
        · rw [ih _ hRN R (x + 1) b rfl hR m hm1 hmR]
          refine forall_congr' (fun j => imp_congr_right (fun hj => ?_))
          rw [before_cons_ne (by omega)]
          exact before_filter (by simpa using (show x < b - 1 - j by omega))
            (by simpa using (show x < b - 2 - j by omega))
        · have hle := rlen_le_numNodes (shape (bstOfList R))
          rw [numNodes_shape_bstOfList _ R rfl hR.1, hRlen] at hle
          constructor
          · intro h; have := le_trans h hle; omega
          · intro H
            have := H (b - x - 2) (by omega)
            rw [show b - 1 - (b - x - 2) = x + 1 by omega,
              show b - 2 - (b - x - 2) = x by omega] at this
            exact absurd this (not_before_head hx)

/-! ## 5. Lemma 1 for the keys `0, …, n-1` -/

lemma isPermIco_of_mem {n : ℕ} {l : List ℕ} (hl : l ∈ (List.range n).permutations.toFinset) :
    IsPermIco l 0 n := by
  rw [List.mem_toFinset, List.mem_permutations] at hl
  exact ⟨hl.nodup_iff.mpr List.nodup_range, fun k => by rw [hl.mem_iff, List.mem_range]; omega⟩

/-- **A2 Lemma 1, first half.**  With `w_k = l.idxOf k` the insertion time of key `k`,
    `h ≥ m` iff `w_{n-1} < w_{n-2} < ⋯ < w_{n-m}`: `h` is the length of the final
    descending run of `w`. -/
theorem lemma1_h (n : ℕ) (l : List ℕ) (hl : l ∈ (List.range n).permutations.toFinset)
    (m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ n) :
    m ≤ rlen (shape (bstOfList l))
      ↔ ∀ j, j + 1 < m → l.idxOf (n - 1 - j) < l.idxOf (n - 2 - j) := by
  have hP := isPermIco_of_mem hl
  rw [rlen_iff_desc _ l 0 n rfl hP m hm1 (by omega)]
  refine forall_congr' (fun j => imp_congr_right (fun hj => ?_))
  exact before_iff_idxOf hP.1 ((hP.2 _).mpr (by omega)) ((hP.2 _).mpr (by omega)) (by omega)

/-- **A2 Lemma 1, second half.**  `L` is the number of peaks of `w` (with
    `w_{-1} = w_n = 0`): key `k` is a leaf iff each neighbour `k ± 1` that exists was
    inserted before `k`. -/
theorem lemma1_L (n : ℕ) (l : List ℕ) (hl : l ∈ (List.range n).permutations.toFinset) :
    leaves (shape (bstOfList l))
      = ((Finset.range n).filter (fun k => (k = 0 ∨ l.idxOf (k - 1) < l.idxOf k)
          ∧ (k + 1 = n ∨ l.idxOf (k + 1) < l.idxOf k))).card := by
  have hP := isPermIco_of_mem hl
  rw [leaves_eq_peaks _ l 0 n rfl hP, Finset.range_eq_Ico]
  congr 1
  refine Finset.filter_congr (fun k hk => ?_)
  rw [Finset.mem_Ico] at hk
  unfold IsPeak
  have e1 : (k = 0 ∨ Before l (k - 1) k) ↔ (k = 0 ∨ l.idxOf (k - 1) < l.idxOf k) := by
    by_cases hk0 : k = 0
    · simp [hk0]
    · rw [before_iff_idxOf hP.1 ((hP.2 _).mpr (by omega)) ((hP.2 _).mpr (by omega)) (by omega)]
  have e2 : (k + 1 = n ∨ Before l (k + 1) k) ↔ (k + 1 = n ∨ l.idxOf (k + 1) < l.idxOf k) := by
    by_cases hkn : k + 1 = n
    · simp [hkn]
    · rw [before_iff_idxOf hP.1 ((hP.2 _).mpr (by omega)) ((hP.2 _).mpr (by omega)) (by omega)]
  rw [e1, e2]

end MakinenAnalysis
