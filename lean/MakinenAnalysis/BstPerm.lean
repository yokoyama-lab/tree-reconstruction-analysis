import MakinenAnalysis.BstModel

/-!
# The BST weight is the law of random-permutation insertion

`BstModel` *defines* the random BST model by the weight `bstW t = ∏_v 1/|t_v|`
on shapes.  This file proves that this weight is what the model means: insert
the keys of a uniformly random permutation of `0, …, n-1` one after another into
an empty binary search tree; the probability that the resulting shape is `t` is
`bstW t`.

| here | A2 |
|---|---|
| `bstInsert`, `bstOfList` | ordinary BST insertion, keys inserted in list order |
| `card_perms_range` | there are `n!` insertion orders |
| `bst_perm_count` | `#{σ : shape(σ) = t} = n! · ∏_v 1/|t_v|` |
| `bst_perm_law` | `bstE n f` is the average of `f(shape(σ))` over the `n!` orders |

The proof decomposes a permutation by its first key `x`: the keys smaller than
`x` form the left subtree and the larger ones the right subtree, in the order
they appear (`bstOfList_cons`).  A permutation of the keys is the same as a
permutation of the smaller keys, one of the larger keys and an interleaving of
the two (`interleave_card`, `fiber_count`); exactly one first key leaves `a`
smaller keys (`rank_unique`).  This gives the recursion
`cnt (node l r) = C(|l|+|r|, |l|) · cnt l · cnt r` for the number of insertion
orders of each shape, and `cnt t = |t|! · bstW t`.
-/

namespace MakinenAnalysis

open Finset

/-! ## 1. Insertion -/

/-- Ordinary binary-search-tree insertion of the key `x` (a key already present
    leaves the tree unchanged). -/
def bstInsert (x : ℕ) : BinaryTree ℕ → BinaryTree ℕ
  | .nil => .node x .nil .nil
  | .node y l r =>
      if x < y then .node y (bstInsert x l) r
      else if y < x then .node y l (bstInsert x r)
      else .node y l r

/-- The BST obtained by inserting the keys of `l` in list order into the empty tree. -/
def bstOfList (l : List ℕ) : BinaryTree ℕ := l.foldl (fun t x => bstInsert x t) .nil

/-- The shape of a labelled tree (forget the keys). -/
def shape : BinaryTree ℕ → T := BinaryTree.map (fun _ => ())

@[simp] lemma shape_nil : shape .nil = .nil := rfl

@[simp] lemma shape_node (x : ℕ) (l r : BinaryTree ℕ) :
    shape (.node x l r) = .node () (shape l) (shape r) := rfl

/-- Inserting into a tree with root `x`: the smaller keys go to the left
    subtree, the larger ones to the right, each in their original order. -/
lemma foldl_insert_node (x : ℕ) (ys : List ℕ) (L R : BinaryTree ℕ) :
    ys.foldl (fun t y => bstInsert y t) (.node x L R)
      = .node x ((ys.filter (· < x)).foldl (fun t y => bstInsert y t) L)
          ((ys.filter (x < ·)).foldl (fun t y => bstInsert y t) R) := by
  induction ys generalizing L R with
  | nil => rfl
  | cons y ys ih =>
    rw [List.foldl_cons]
    rcases lt_trichotomy y x with h | h | h
    · have h2 : ¬ x < y := by omega
      simp only [bstInsert, h, if_true, ih, List.filter_cons, decide_eq_true_eq, h2,
        if_false, List.foldl_cons]
    · subst h
      simp only [bstInsert, lt_irrefl, if_false, ih, List.filter_cons, decide_false,
        Bool.false_eq_true]
    · have h2 : ¬ y < x := by omega
      simp only [bstInsert, h, h2, if_true, if_false, ih, List.filter_cons,
        decide_eq_true_eq, List.foldl_cons]

/-- **First key at the root.** -/
lemma bstOfList_cons (x : ℕ) (r : List ℕ) :
    bstOfList (x :: r)
      = .node x (bstOfList (r.filter (· < x))) (bstOfList (r.filter (x < ·))) := by
  simp only [bstOfList, List.foldl_cons]
  exact foldl_insert_node x r .nil .nil

/-! ## 2. Permutations of a finite set of keys -/

/-- The orderings of the finite set `S` of keys. -/
noncomputable def permsOf (S : Finset ℕ) : Finset (List ℕ) := S.toList.permutations.toFinset

lemma mem_permsOf {S : Finset ℕ} {l : List ℕ} :
    l ∈ permsOf S ↔ l.Nodup ∧ ∀ a, a ∈ l ↔ a ∈ S := by
  rw [permsOf, List.mem_toFinset, List.mem_permutations]
  constructor
  · intro h
    exact ⟨h.nodup_iff.2 S.nodup_toList, fun a => by rw [h.mem_iff, Finset.mem_toList]⟩
  · rintro ⟨hl, hm⟩
    exact (List.perm_ext_iff_of_nodup hl S.nodup_toList).2 (fun a => by rw [hm, Finset.mem_toList])

lemma length_of_mem_permsOf {S : Finset ℕ} {l : List ℕ} (h : l ∈ permsOf S) :
    l.length = S.card := by
  rw [permsOf, List.mem_toFinset, List.mem_permutations] at h
  rw [h.length_eq, Finset.length_toList]

lemma permsOf_empty : permsOf ∅ = {[]} := by
  ext l
  rw [mem_permsOf, Finset.mem_singleton]
  constructor
  · rintro ⟨_, hm⟩
    cases l with
    | nil => rfl
    | cons a _ => exact absurd ((hm a).1 (by simp)) (by simp)
  · rintro rfl; simp

/-- **Decomposition by the first key.** -/
lemma card_filter_permsOf (S : Finset ℕ) (hS : S.Nonempty) (Q : List ℕ → Prop)
    [DecidablePred Q] :
    ((permsOf S).filter Q).card
      = ∑ x ∈ S, ((permsOf (S.erase x)).filter (fun r => Q (x :: r))).card := by
  have key : (permsOf S).filter Q = S.biUnion (fun x =>
      ((permsOf (S.erase x)).filter (fun r => Q (x :: r))).image (List.cons x)) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_image, mem_permsOf]
    constructor
    · rintro ⟨⟨hnd, hm⟩, hq⟩
      obtain ⟨a, ha⟩ := hS
      cases l with
      | nil => exact absurd ((hm a).2 ha) (by simp)
      | cons x r =>
        have hxr : x ∉ r := (List.nodup_cons.1 hnd).1
        refine ⟨x, (hm x).1 (by simp), r, ⟨⟨(List.nodup_cons.1 hnd).2, fun b => ?_⟩, hq⟩, rfl⟩
        rw [Finset.mem_erase]
        constructor
        · intro hb
          exact ⟨fun e => hxr (e ▸ hb), (hm b).1 (List.mem_cons_of_mem _ hb)⟩
        · rintro ⟨hne, hb⟩
          exact ((List.mem_cons.1 ((hm b).2 hb))).resolve_left hne
    · rintro ⟨x, hx, r, ⟨⟨hnd, hm⟩, hq⟩, rfl⟩
      refine ⟨⟨List.nodup_cons.2 ⟨fun h => by simpa using (hm x).1 h, hnd⟩, fun b => ?_⟩, hq⟩
      rw [List.mem_cons, hm b, Finset.mem_erase]
      constructor
      · rintro (rfl | ⟨_, hb⟩)
        · exact hx
        · exact hb
      · intro hb
        by_cases e : b = x
        · exact Or.inl e
        · exact Or.inr ⟨e, hb⟩
  rw [key, Finset.card_biUnion]
  · refine Finset.sum_congr rfl (fun x _ => ?_)
    exact Finset.card_image_of_injective _ (List.cons_injective)
  · intro x _ y _ hxy
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro l hl hl'
    simp only [Finset.mem_image] at hl hl'
    obtain ⟨r, _, rfl⟩ := hl
    obtain ⟨r', _, e⟩ := hl'
    exact hxy (List.cons.inj e).1.symm

lemma cons_mem_permsOf {T : Finset ℕ} {x : ℕ} {p : List ℕ} (h : x :: p ∈ permsOf T) :
    x ∈ T ∧ p ∈ permsOf (T.erase x) := by
  rw [mem_permsOf] at h ⊢
  obtain ⟨hnd, hm⟩ := h
  have hxp : x ∉ p := (List.nodup_cons.1 hnd).1
  refine ⟨(hm x).1 (by simp), (List.nodup_cons.1 hnd).2, fun a => ?_⟩
  rw [Finset.mem_erase, ← hm a, List.mem_cons]
  constructor
  · intro ha; exact ⟨fun e => hxp (e ▸ ha), Or.inr ha⟩
  · rintro ⟨hne, h | h⟩
    · exact absurd h hne
    · exact h

lemma mem_permsOf_erase_of_notMem {T : Finset ℕ} {x : ℕ} {q : List ℕ} (h : q ∈ permsOf T)
    (hx : x ∉ T) : q ∈ permsOf (T.erase x) := by
  rwa [Finset.erase_eq_of_notMem hx]

/-! ## 3. Interleavings -/

/-- The orderings of `S` in which the keys with `b = true` appear in the order
    `p` and the others in the order `q` are the interleavings of `p` and `q`:
    there are `C(|p|+|q|, |p|)` of them. -/
lemma interleave_card (b : ℕ → Bool) : ∀ (n : ℕ) (S : Finset ℕ), S.card = n →
    ∀ p q : List ℕ, p ∈ permsOf (S.filter (fun a => b a = true)) →
      q ∈ permsOf (S.filter (fun a => b a = false)) →
      ((permsOf S).filter (fun r => r.filter b = p ∧ r.filter (fun a => !b a) = q)).card
        = (p.length + q.length).choose p.length := by
  intro n
  induction n with
  | zero =>
    intro S hS p q hp hq
    rw [Finset.card_eq_zero] at hS
    subst hS
    simp only [Finset.filter_empty, permsOf_empty, Finset.mem_singleton] at hp hq ⊢
    subst hp; subst hq
    rw [Finset.filter_singleton, if_pos (by simp)]
    simp
  | succ n ih =>
    intro S hS p q hp hq
    have hne : S.Nonempty := by rw [← Finset.card_pos, hS]; omega
    rw [card_filter_permsOf S hne]
    have hterm : ∀ x ∈ S,
        ((permsOf (S.erase x)).filter (fun r => (x :: r).filter b = p ∧
            (x :: r).filter (fun a => !b a) = q)).card
          = (if p.head? = some x then ((permsOf (S.erase x)).filter (fun r =>
                r.filter b = p.tail ∧ r.filter (fun a => !b a) = q)).card else 0)
            + (if q.head? = some x then ((permsOf (S.erase x)).filter (fun r =>
                r.filter b = p ∧ r.filter (fun a => !b a) = q.tail)).card else 0) := by
      intro x _
      rw [mem_permsOf] at hp hq
      cases hbx : b x
      · have hp' : p.head? ≠ some x := by
          intro e
          obtain ⟨t, rfl⟩ : ∃ t, p = x :: t := by
            cases p with
            | nil => simp at e
            | cons y t => simp only [List.head?_cons, Option.some.injEq] at e; exact ⟨t, e ▸ rfl⟩
          have := (hp.2 x).1 (by simp)
          simp [hbx] at this
        rw [if_neg hp', zero_add]
        split_ifs with hq'
        · obtain ⟨t, rfl⟩ : ∃ t, q = x :: t := by
            cases q with
            | nil => simp at hq'
            | cons y t => simp only [List.head?_cons, Option.some.injEq] at hq'; exact ⟨t, hq' ▸ rfl⟩
          congr 1
          apply Finset.filter_congr
          intro r _
          simp [hbx]
        · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          rintro r _ ⟨_, h2⟩
          apply hq'
          simp only [List.filter_cons, hbx, Bool.not_false, if_true] at h2
          rw [← h2]; rfl
      · have hq' : q.head? ≠ some x := by
          intro e
          obtain ⟨t, rfl⟩ : ∃ t, q = x :: t := by
            cases q with
            | nil => simp at e
            | cons y t => simp only [List.head?_cons, Option.some.injEq] at e; exact ⟨t, e ▸ rfl⟩
          have := (hq.2 x).1 (by simp)
          simp [hbx] at this
        rw [if_neg hq', add_zero]
        split_ifs with hp'
        · obtain ⟨t, rfl⟩ : ∃ t, p = x :: t := by
            cases p with
            | nil => simp at hp'
            | cons y t => simp only [List.head?_cons, Option.some.injEq] at hp'; exact ⟨t, hp' ▸ rfl⟩
          congr 1
          apply Finset.filter_congr
          intro r _
          simp [hbx]
        · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          rintro r _ ⟨h1, _⟩
          apply hp'
          simp only [List.filter_cons, hbx, if_true] at h1
          rw [← h1]; rfl
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    rcases p with _ | ⟨x0, p'⟩ <;> rcases q with _ | ⟨y0, q'⟩
    · exfalso
      obtain ⟨a, ha⟩ := hne
      rw [mem_permsOf] at hp hq
      cases hba : b a
      · exact absurd ((hq.2 a).2 (Finset.mem_filter.2 ⟨ha, hba⟩)) (by simp)
      · exact absurd ((hp.2 a).2 (Finset.mem_filter.2 ⟨ha, hba⟩)) (by simp)
    · obtain ⟨hy0, hq'⟩ := cons_mem_permsOf hq
      have hy0S : y0 ∈ S := (Finset.mem_filter.1 hy0).1
      have hby : b y0 = false := (Finset.mem_filter.1 hy0).2
      simp only [List.head?_nil, List.head?_cons, Option.some.injEq, reduceCtorEq, if_false,
        Finset.sum_const_zero, zero_add, List.tail_cons, Finset.sum_ite_eq, if_pos hy0S]
      have hc : (S.erase y0).card = n := by rw [Finset.card_erase_of_mem hy0S]; omega
      rw [ih (S.erase y0) hc [] q' (by
        rw [Finset.filter_erase]
        exact mem_permsOf_erase_of_notMem hp (by simp [hby])) (by rwa [Finset.filter_erase])]
      simp
    · obtain ⟨hx0, hp'⟩ := cons_mem_permsOf hp
      have hx0S : x0 ∈ S := (Finset.mem_filter.1 hx0).1
      have hbx : b x0 = true := (Finset.mem_filter.1 hx0).2
      simp only [List.head?_nil, List.head?_cons, Option.some.injEq, reduceCtorEq, if_false,
        Finset.sum_const_zero, add_zero, List.tail_cons, Finset.sum_ite_eq, if_pos hx0S]
      have hc : (S.erase x0).card = n := by rw [Finset.card_erase_of_mem hx0S]; omega
      rw [ih (S.erase x0) hc p' [] (by rwa [Finset.filter_erase]) (by
        rw [Finset.filter_erase]
        exact mem_permsOf_erase_of_notMem hq (by simp [hbx]))]
      simp
    · obtain ⟨hx0, hp'⟩ := cons_mem_permsOf hp
      have hx0S : x0 ∈ S := (Finset.mem_filter.1 hx0).1
      have hbx : b x0 = true := (Finset.mem_filter.1 hx0).2
      obtain ⟨hy0, hq'⟩ := cons_mem_permsOf hq
      have hy0S : y0 ∈ S := (Finset.mem_filter.1 hy0).1
      have hby : b y0 = false := (Finset.mem_filter.1 hy0).2
      simp only [List.head?_cons, Option.some.injEq, List.tail_cons, Finset.sum_ite_eq,
        if_pos hx0S, if_pos hy0S]
      have hc1 : (S.erase x0).card = n := by rw [Finset.card_erase_of_mem hx0S]; omega
      have hc2 : (S.erase y0).card = n := by rw [Finset.card_erase_of_mem hy0S]; omega
      rw [ih (S.erase x0) hc1 p' (y0 :: q') (by rwa [Finset.filter_erase]) (by
        rw [Finset.filter_erase]
        exact mem_permsOf_erase_of_notMem hq (by simp [hbx])),
        ih (S.erase y0) hc2 (x0 :: p') q' (by
        rw [Finset.filter_erase]
        exact mem_permsOf_erase_of_notMem hp (by simp [hby])) (by rwa [Finset.filter_erase])]
      simp only [List.length_cons]
      rw [show p'.length + 1 + (q'.length + 1) = (p'.length + (q'.length + 1)) + 1 by omega,
        Nat.choose_succ_succ, show p'.length + 1 + q'.length = p'.length + (q'.length + 1) by omega]

/-- **Regrouping by the two sub-orders.**  Counting orderings of `S` by the
    order of their `b`-keys and the order of the other keys. -/
lemma fiber_count (b : ℕ → Bool) (S : Finset ℕ) (F G : List ℕ → Prop) [DecidablePred F]
    [DecidablePred G] :
    ((permsOf S).filter (fun r => F (r.filter b) ∧ G (r.filter (fun a => !b a)))).card
      = ((S.filter (fun a => b a = true)).card + (S.filter (fun a => b a = false)).card).choose
          (S.filter (fun a => b a = true)).card
        * ((permsOf (S.filter (fun a => b a = true))).filter F).card
        * ((permsOf (S.filter (fun a => b a = false))).filter G).card := by
  set A := S.filter (fun a => b a = true)
  set B := S.filter (fun a => b a = false)
  rw [Finset.card_eq_sum_card_fiberwise (f := fun r => (r.filter b, r.filter (fun a => !b a)))
    (t := ((permsOf A).filter F) ×ˢ ((permsOf B).filter G))]
  · rw [Finset.sum_const_nat (m := (A.card + B.card).choose A.card)]
    · rw [Finset.card_product]; ring
    · rintro ⟨p, q⟩ hpq
      rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hpq
      rw [← length_of_mem_permsOf hpq.1.1, ← length_of_mem_permsOf hpq.2.1,
        ← interleave_card b _ S rfl p q hpq.1.1 hpq.2.1]
      congr 1
      ext r
      simp only [Finset.mem_filter, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hr, _⟩, h⟩; exact ⟨hr, h⟩
      · rintro ⟨hr, h1, h2⟩; exact ⟨⟨hr, h1 ▸ hpq.1.2, h2 ▸ hpq.2.2⟩, h1, h2⟩
  · intro r hr
    rw [Finset.mem_coe, Finset.mem_filter] at hr
    obtain ⟨hr, hF, hG⟩ := hr
    rw [mem_permsOf] at hr
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, mem_permsOf]
    refine ⟨⟨⟨hr.1.filter _, fun a => ?_⟩, hF⟩, ⟨⟨hr.1.filter _, fun a => ?_⟩, hG⟩⟩
    · simp [List.mem_filter, hr.2, A]
    · simp [List.mem_filter, hr.2, B]

/-- **Exactly one key has rank `a`.** -/
lemma rank_unique (S : Finset ℕ) (a : ℕ) (ha : a < S.card) :
    (S.filter (fun x => (S.filter (· < x)).card = a)).card = 1 := by
  set rk : ℕ → ℕ := fun x => (S.filter (· < x)).card with hrk
  have hlt : ∀ x ∈ S, ∀ y ∈ S, x < y → rk x < rk y := by
    intro x hx y hy hxy
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨x, by simp [hx, hxy], by simp⟩
    · intro z hz
      simp only [Finset.mem_filter] at hz ⊢
      exact ⟨hz.1, lt_trans hz.2 hxy⟩
  have hinj : Set.InjOn rk S := by
    intro x hx y hy h
    rcases lt_trichotomy x y with c | c | c
    · exact absurd h (ne_of_lt (hlt x hx y hy c))
    · exact c
    · exact absurd h (ne_of_gt (hlt y hy x hx c))
  have hmaps : Set.MapsTo rk S (range S.card) := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_range]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
    exact ⟨x, hx, by simp⟩
  have hsurj := Finset.surjOn_of_injOn_of_card_le rk hmaps hinj (by simp)
  obtain ⟨x, hx, hxa⟩ := hsurj (Finset.mem_coe.2 (Finset.mem_range.2 ha))
  rw [Finset.card_eq_one]
  refine ⟨x, ?_⟩
  ext y
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hy, hya⟩; exact hinj hy hx (hya.trans hxa.symm)
  · rintro rfl; exact ⟨hx, hxa⟩

/-! ## 4. The number of insertion orders of a shape -/

/-- The number of insertion orders producing a shape:
    `cnt (node l r) = C(|l|+|r|, |l|) · cnt l · cnt r`. -/
def cnt : T → ℕ
  | .nil => 1
  | .node _ l r => (l.numNodes + r.numNodes).choose l.numNodes * cnt l * cnt r

/-- **The count for an arbitrary key set.**  Among the orderings of a set `S`
    of keys, exactly `cnt t` produce the shape `t` when `t` has `#S` nodes. -/
theorem count_shape (t : T) : ∀ S : Finset ℕ,
    ((permsOf S).filter (fun l => shape (bstOfList l) = t)).card
      = if t.numNodes = S.card then cnt t else 0 := by
  induction t with
  | nil =>
    intro S
    have hnil : ∀ l, shape (bstOfList l) = .nil ↔ l = [] := by
      intro l
      cases l with
      | nil => simp [bstOfList]
      | cons x r => simp [bstOfList_cons]
    simp only [hnil]
    by_cases hS : S = ∅
    · subst hS
      rw [permsOf_empty, Finset.filter_singleton, if_pos rfl]
      simp [cnt]
    · rw [if_neg (by
        simp only [BinaryTree.numNodes]
        exact fun h => hS (Finset.card_eq_zero.1 h.symm))]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro l hl rfl
      obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.2 hS
      exact absurd (((mem_permsOf.1 hl).2 a).2 ha) (by simp)
  | node u l r ihl ihr =>
    intro S
    by_cases hS : S = ∅
    · subst hS
      rw [permsOf_empty, Finset.filter_singleton, if_neg (by simp [bstOfList])]
      simp
    have hne := Finset.nonempty_iff_ne_empty.2 hS
    have hpos : 1 ≤ S.card := Finset.card_pos.2 hne
    rw [card_filter_permsOf S hne]
    have hterm : ∀ x ∈ S,
        ((permsOf (S.erase x)).filter
            (fun r' => shape (bstOfList (x :: r')) = .node u l r)).card
          = if (S.filter (· < x)).card = l.numNodes ∧ l.numNodes + r.numNodes + 1 = S.card
            then cnt (.node u l r) else 0 := by
      intro x hx
      have e1 : (permsOf (S.erase x)).filter
            (fun r' => shape (bstOfList (x :: r')) = .node u l r)
          = (permsOf (S.erase x)).filter (fun r' =>
              (fun p => shape (bstOfList p) = l) (r'.filter (fun a => decide (a < x))) ∧
              (fun q => shape (bstOfList q) = r) (r'.filter (fun a => !decide (a < x)))) := by
        apply Finset.filter_congr
        intro r' hr'
        have hxr : x ∉ r' := fun h => by simpa using ((mem_permsOf.1 hr').2 x).1 h
        have hf : r'.filter (fun a => decide (x < a)) = r'.filter (fun a => !decide (a < x)) := by
          apply List.filter_congr
          intro a ha
          have : a ≠ x := fun e => hxr (e ▸ ha)
          by_cases h : a < x
          · simp [h, show ¬ x < a by omega]
          · simp [h, show x < a by omega]
        rw [bstOfList_cons, shape_node, hf]
        simp
      rw [e1, fiber_count (fun a => decide (a < x)) (S.erase x) (fun p => shape (bstOfList p) = l)
        (fun q => shape (bstOfList q) = r), ihl, ihr]
      have hA : ((S.erase x).filter (fun a => decide (a < x) = true)) = S.filter (· < x) := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_erase, decide_eq_true_eq]
        constructor
        · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h, h'⟩
        · rintro ⟨h, h'⟩; exact ⟨⟨by omega, h⟩, h'⟩
      have hAB : ((S.erase x).filter (fun a => decide (a < x) = true)).card
          + ((S.erase x).filter (fun a => decide (a < x) = false)).card = S.card - 1 := by
        rw [← Finset.card_erase_of_mem hx,
          ← Finset.card_filter_add_card_filter_not (s := S.erase x)
            (fun a => decide (a < x) = true)]
        congr 2
        ext a
        simp
      rw [hA] at hAB ⊢
      generalize (S.filter (· < x)).card = α at hAB ⊢
      generalize ((S.erase x).filter (fun a => decide (a < x) = false)).card = β at hAB ⊢
      simp only [cnt]
      by_cases hc : α = l.numNodes ∧ l.numNodes + r.numNodes + 1 = S.card
      · obtain ⟨h1, h2⟩ := hc
        have h3 : r.numNodes = β := by omega
        subst h1; subst h3
        rw [if_pos rfl, if_pos rfl, if_pos ⟨rfl, h2⟩]
      · rw [if_neg hc]
        by_cases h1 : l.numNodes = α
        · rw [if_neg (show ¬ r.numNodes = β by omega)]; simp
        · rw [if_neg h1]; simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, smul_eq_mul]
    by_cases hc : l.numNodes + r.numNodes + 1 = S.card
    · have : S.filter (fun x => (S.filter (· < x)).card = l.numNodes ∧
            l.numNodes + r.numNodes + 1 = S.card)
          = S.filter (fun x => (S.filter (· < x)).card = l.numNodes) := by
        apply Finset.filter_congr
        intro x _
        simp [hc]
      rw [this, rank_unique S _ (by omega), one_mul,
        if_pos (by simp only [BinaryTree.numNodes]; omega)]
    · rw [Finset.filter_false_of_mem (fun x _ h => hc h.2), Finset.card_empty, zero_mul,
        if_neg (by simp only [BinaryTree.numNodes]; omega)]

/-- **The hook formula for binary trees**: `cnt t = |t|! · ∏_v 1/|t_v|`. -/
lemma cnt_eq (t : T) : (cnt t : ℚ) = (t.numNodes.factorial : ℚ) * bstW t := by
  induction t with
  | nil => simp [cnt, bstW]
  | node u l r ihl ihr =>
    have h := Nat.add_choose_mul_factorial_mul_factorial r.numNodes l.numNodes
    rw [add_comm r.numNodes] at h
    have h1 : ((l.numNodes + r.numNodes).choose l.numNodes : ℚ) * r.numNodes.factorial
        * l.numNodes.factorial = (l.numNodes + r.numNodes).factorial := by exact_mod_cast h
    rw [cnt, bstW, BinaryTree.numNodes, Nat.factorial_succ]
    push_cast
    rw [ihl, ihr, ← h1]
    field_simp

/-! ## 5. The headline statements, for the keys `0, …, n-1` -/

lemma perms_range_eq (n : ℕ) :
    (List.range n).permutations.toFinset = permsOf (Finset.range n) := by
  ext l
  rw [mem_permsOf, List.mem_toFinset, List.mem_permutations]
  constructor
  · intro h
    exact ⟨h.nodup_iff.2 List.nodup_range,
      fun a => by rw [h.mem_iff, List.mem_range, Finset.mem_range]⟩
  · rintro ⟨hl, hm⟩
    exact (List.perm_ext_iff_of_nodup hl List.nodup_range).2
      (fun a => by rw [hm, List.mem_range, Finset.mem_range])

/-- There are `n!` insertion orders. -/
theorem card_perms_range (n : ℕ) :
    ((List.range n).permutations.toFinset).card = n.factorial := by
  rw [List.toFinset_card_of_nodup (List.nodup_permutations _ List.nodup_range),
    List.length_permutations, List.length_range]

/-- **The shape law.**  Of the `n!` insertion orders of the keys `0, …, n-1`,
    exactly `n! · bstW t` produce the shape `t`. -/
theorem bst_perm_count (n : ℕ) (t : T) (ht : t.numNodes = n) :
    (((List.range n).permutations.toFinset.filter
        (fun l => shape (bstOfList l) = t)).card : ℚ) = n.factorial * bstW t := by
  rw [perms_range_eq, count_shape, Finset.card_range, if_pos ht, cnt_eq, ht]

/-- **The BST expectation is the average over uniformly random insertion
    orders.**  For every statistic `f` of the shape. -/
theorem bst_perm_law (n : ℕ) (f : T → ℚ) :
    bstE n f = (∑ l ∈ (List.range n).permutations.toFinset, f (shape (bstOfList l)))
      / n.factorial := by
  have hmaps : ∀ l ∈ (List.range n).permutations.toFinset, shape (bstOfList l) ∈ trees n := by
    intro l hl
    rw [BinaryTree.mem_treesOfNumNodesEq]
    have h := count_shape (shape (bstOfList l)) (Finset.range n)
    rw [← perms_range_eq, Finset.card_range] at h
    by_contra hne
    rw [if_neg hne, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
    exact h hl rfl
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ t ∈ trees n, ∑ l ∈ (List.range n).permutations.toFinset with
      shape (bstOfList l) = t, f (shape (bstOfList l)) = n.factorial * bstW t * f t := by
    intro t ht
    rw [Finset.sum_congr rfl (fun l hl => by rw [(Finset.mem_filter.1 hl).2]),
      Finset.sum_const, nsmul_eq_mul,
      bst_perm_count n t (BinaryTree.mem_treesOfNumNodesEq.1 ht)]
  rw [Finset.sum_congr rfl hfib, eq_div_iff (by positivity), bstE, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun t _ => by ring)

end MakinenAnalysis
