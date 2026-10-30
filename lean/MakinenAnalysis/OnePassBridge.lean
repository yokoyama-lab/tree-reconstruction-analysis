/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.

# One-pass programs on actual trees

`OnePassProg` answers the questions of a program by `lt`, read off the
reconstruction stack of the codeword.  This file connects that model to the
i-p sequences of actual trees:

* `runL_ip`: running the stack on the labels of `ip t` pops `0 :: toPop t`, so
  the codeword of the model is the codeword of the tree (`toPop`, a bijection
  onto the valid codewords);
* `lt_ip`: `lt (toPop t) a b` holds iff the label of `a` is smaller than the
  label of `b` (the stack keeps the elements not yet overtaken by a larger later
  label, `runL_stack`, and i-p sequences avoid the pattern `231`, `ipo_noPat`);
* `onePass_trees_opt`: a one-pass program run on the actual labels (a question
  about an element not yet read is answered "no") that outputs the parent of
  each element before reading the next must ask at least `2n - 3` comparisons on
  some `n`-node tree, and M is correct and asks at most `2n - 3` on every tree.

Scope.  The parent of an element is specified by the reconstruction stack
(`parentOf`).  That this is the parent in the tree is the correctness of M's
reconstruction, proved for all sizes in the Rocq development
(`ReconstructFull.reconstruct_correct`) and, in Lean, only for `n ≤ 8`
(`rebuildsM_le_eight`).  A program also sees the codeword prefix of the
elements read so far, which a correct program can compute from its own outputs;
this only makes the lower bound stronger.
-/
import MakinenAnalysis.OnePassProg
import MakinenAnalysis.ExecModel
import MakinenAnalysis.TreeIdentities

namespace MakinenAnalysis.OnePass

/-! ## The stack run on labels -/

/-- Run the reconstruction stack (labels, top first) over the input labels;
    each element pops the stack labels smaller than it.  Returns the pop counts
    and the final stack. -/
def runL : List ℕ → List ℕ → List ℕ × List ℕ
  | s, [] => ([], s)
  | s, x :: xs =>
    ((s.takeWhile (· < x)).length :: (runL (x :: s.drop (s.takeWhile (· < x)).length) xs).1,
      (runL (x :: s.drop (s.takeWhile (· < x)).length) xs).2)

theorem runL_append : ∀ (A B s : List ℕ),
    runL s (A ++ B) = ((runL s A).1 ++ (runL (runL s A).2 B).1, (runL (runL s A).2 B).2) := by
  intro A
  induction A with
  | nil => intro B s; simp [runL]
  | cons x A ih => intro B s; simp only [List.cons_append, runL, ih, List.cons_append]

theorem runL_single (s : List ℕ) (x : ℕ) :
    runL s [x] = ([(s.takeWhile (· < x)).length], x :: s.drop (s.takeWhile (· < x)).length) := by
  simp [runL]

/-! ## The run on the i-p sequence of a tree pops its codeword -/

theorem takeWhile_lt_append (x : ℕ) :
    ∀ (low high : List ℕ), (∀ y ∈ low, y < x) → (∀ y ∈ high, x < y) →
      (low ++ high).takeWhile (· < x) = low := by
  intro low
  induction low with
  | nil =>
    intro high _ hh
    cases high with
    | nil => rfl
    | cons y hs =>
      have := hh y (by simp)
      rw [List.nil_append, List.takeWhile_cons_of_neg (by simp; omega)]
  | cons y low ih =>
    intro high hl hh
    have hy := hl y (by simp)
    rw [List.cons_append, List.takeWhile_cons_of_pos (by simpa using hy),
      ih high (fun z hz => hl z (by simp [hz])) hh]

theorem ipo_mem : ∀ (t : T) (off y : ℕ), y ∈ ipo off t → off ≤ y ∧ y < off + t.numNodes := by
  intro t
  induction t with
  | nil => intro off y h; simp at h
  | node v l r ihl ihr =>
    intro off y h
    simp only [ipo_node, List.mem_cons, List.mem_append] at h
    simp only [BinaryTree.numNodes]
    rcases h with rfl | h | h
    · omega
    · have := ihl off y h; omega
    · have := ihr _ y h; omega

/-- **The run on a subtree.**  Processing the i-p sequence of `t` (labels in
    `[off, off + |t|)`) from a stack `low ++ high`, where `low` lies below and
    `high` above that range, pops all of `low` at the root, then the codeword of
    `t`, and leaves `rem t` labels of `t` on top of `high`. -/
theorem runL_ipo : ∀ (t : T) (off : ℕ) (low high : List ℕ), t ≠ .nil →
    (∀ y ∈ low, y < off) → (∀ y ∈ high, off + t.numNodes ≤ y) →
    ∃ rho : List ℕ, runL (low ++ high) (ipo off t) = (low.length :: toPop t, rho ++ high) ∧
      rho.length = rem t ∧ ∀ y ∈ rho, off ≤ y ∧ y < off + t.numNodes := by
  intro t
  induction t with
  | nil => intro _ _ _ h; exact absurd rfl h
  | node v l r ihl ihr =>
    intro off low high _ hlow hhigh
    simp only [BinaryTree.numNodes] at hhigh
    -- the root, label x, pops all of `low`
    set x := off + l.numNodes with hx
    have hroot : runL (low ++ high) [x] = ([low.length], x :: high) := by
      rw [runL_single, takeWhile_lt_append x low high (fun y hy => by have := hlow y hy; omega)
        (fun y hy => by have := hhigh y hy; omega)]
      simp
    have hsplit : ipo off (.node v l r) = [x] ++ (ipo off l ++ ipo (x + 1) r) := by
      simp [ipo_node, hx]
    rw [hsplit, runL_append, hroot]
    simp only
    -- the left subtree, from `[] ++ (x :: high)`
    by_cases hl : l = .nil
    · subst hl
      have h0 : (BinaryTree.nil : T).numNodes = 0 := rfl
      simp only [h0, Nat.add_zero, Nat.zero_add] at hx hhigh
      simp only [ipo_nil, List.nil_append]
      by_cases hr : r = .nil
      · subst hr
        refine ⟨[x], ?_, ?_, ?_⟩
        · simp [runL]
        · simp
        · simp [BinaryTree.numNodes, hx]
      · obtain ⟨rho, hrun, hlen, hmem⟩ :=
          ihr (x + 1) [x] high hr (by simp) (fun y hy => by
            have := hhigh y hy; omega)
        refine ⟨rho, ?_, ?_, ?_⟩
        · rw [show x :: high = [x] ++ high from rfl, hrun, toPop_lR hr]; simp
        · rw [hlen, rem_lR hr]
        · intro y hy; have := hmem y hy; simp [BinaryTree.numNodes, hx] at this ⊢; omega
    · obtain ⟨rhoL, hrunL, hlenL, hmemL⟩ :=
        ihl off [] (x :: high) hl (by simp) (by
          intro y hy
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · omega
          · have := hhigh y hy; omega)
      rw [runL_append, show x :: high = [] ++ (x :: high) from rfl, hrunL]
      simp only [List.length_nil]
      by_cases hr : r = .nil
      · subst hr
        refine ⟨rhoL ++ [x], ?_, ?_, ?_⟩
        · simp [runL, toPop_Ln hl]
        · rw [rem_Ln hl]; simp [hlenL]
        · intro y hy
          simp only [List.mem_append, List.mem_singleton] at hy
          simp only [BinaryTree.numNodes]
          rcases hy with hy | rfl
          · have := hmemL y hy; omega
          · omega
      · obtain ⟨rho, hrun, hlen, hmem⟩ :=
          ihr (x + 1) (rhoL ++ [x]) high hr (by
            intro y hy
            simp only [List.mem_append, List.mem_singleton] at hy
            rcases hy with hy | rfl
            · have := hmemL y hy; omega
            · omega) (fun y hy => by
            have := hhigh y hy; omega)
        refine ⟨rho, ?_, ?_, ?_⟩
        · rw [show rhoL ++ x :: high = (rhoL ++ [x]) ++ high by simp, hrun, toPop_LR hl hr]
          simp [hlenL]
        · rw [hlen, rem_Rnn hr]
        · intro y hy; have := hmem y hy; simp [BinaryTree.numNodes, hx] at this ⊢; omega

/-- The run on the i-p sequence of a nonempty tree pops `0` for the root and
    then the codeword of the tree. -/
theorem runL_ip (t : T) (h : t ≠ .nil) : (runL [] (ip t)).1 = 0 :: toPop t := by
  obtain ⟨rho, hrun, _, _⟩ := runL_ipo t 0 [] [] h (by simp) (by simp)
  simp only [ip, List.nil_append] at hrun ⊢
  rw [hrun]; rfl

/-! ## Generic: the label stack keeps the elements not yet overtaken -/

theorem runL_length : ∀ (A s : List ℕ), (runL s A).1.length = A.length := by
  intro A
  induction A with
  | nil => intro s; simp [runL]
  | cons x A ih => intro s; simp [runL, ih]

/-- Pop counts and stack after appending one element. -/
theorem runL_snoc (A : List ℕ) (x : ℕ) :
    runL [] (A ++ [x]) = ((runL [] A).1 ++ [((runL [] A).2.takeWhile (· < x)).length],
      x :: (runL [] A).2.drop ((runL [] A).2.takeWhile (· < x)).length) := by
  rw [runL_append, runL_single]

/-- In a list increasing from the head, the entries left after dropping those
    below `x` are exactly the entries not below `x`. -/
theorem mem_drop_takeWhile_lt (x : ℕ) :
    ∀ (M : List ℕ), M.Pairwise (· < ·) →
      ∀ y, y ∈ M.drop (M.takeWhile (· < x)).length ↔ y ∈ M ∧ ¬ y < x := by
  intro M
  induction M with
  | nil => intro _ y; simp
  | cons z M ih =>
    intro hM y
    rw [List.pairwise_cons] at hM
    by_cases hz : z < x
    · rw [List.takeWhile_cons_of_pos (by simpa using hz), List.length_cons, List.drop_succ_cons,
        ih hM.2 y]
      simp only [List.mem_cons]
      constructor
      · intro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩
      · rintro ⟨rfl | h1, h2⟩
        · exact absurd hz h2
        · exact ⟨h1, h2⟩
    · rw [List.takeWhile_cons_of_neg (by simpa using hz)]
      simp only [List.length_nil, List.drop_zero, List.mem_cons]
      constructor
      · intro h
        refine ⟨h, ?_⟩
        rcases h with rfl | h
        · exact hz
        · have := hM.1 y h; omega
      · exact fun h => h.1

/-- **The label stack.**  For a list of distinct labels, the stack after the run
    is increasing from the top and holds exactly the labels not overtaken by a
    larger later label. -/
theorem runL_stack (A : List ℕ) (hA : A.Nodup) :
    ((runL [] A).2).Pairwise (· < ·) ∧
      ∀ y, y ∈ (runL [] A).2 ↔
        ∃ (a : ℕ) (ha : a < A.length), A[a] = y ∧ ∀ (c : ℕ) (hc : c < A.length), a < c → A[c] < A[a] := by
  induction A using List.reverseRecOn with
  | nil => simp [runL]
  | append_singleton A x ih =>
    have hA' : A.Nodup := hA.sublist (List.sublist_append_left _ _)
    have hx : x ∉ A := by
      rw [List.nodup_append] at hA
      intro hxA; exact (by simpa using hA.2.2 : ∀ a ∈ A, ¬a = x) x hxA rfl
    obtain ⟨hsort, hmem⟩ := ih hA'
    rw [runL_snoc]
    set S := (runL [] A).2 with hS
    have hdrop := mem_drop_takeWhile_lt x S hsort
    refine ⟨?_, ?_⟩
    · refine List.Pairwise.cons (fun y hy => ?_) (hsort.sublist (List.drop_sublist _ _))
      have := (hdrop y).1 hy
      have hyA : y ≠ x := by
        intro hyx; subst hyx
        obtain ⟨a, ha, hya, _⟩ := (hmem y).1 this.1
        exact hx (hya ▸ List.getElem_mem ha)
      omega
    · intro y
      simp only [List.mem_cons, hdrop, hmem, List.length_append, List.length_singleton]
      constructor
      · rintro (rfl | ⟨⟨a, ha, hya, hall⟩, hyx⟩)
        · refine ⟨A.length, by omega, by simp, fun c hc hlt => by omega⟩
        · refine ⟨a, by omega, by rw [List.getElem_append_left ha]; exact hya, ?_⟩
          intro c hc hac
          rw [List.getElem_append_left ha]
          by_cases hcA : c < A.length
          · rw [List.getElem_append_left hcA]; exact hall c hcA hac
          · have : c = A.length := by omega
            subst this
            simp only [List.getElem_append_right (le_refl _), Nat.sub_self,
              List.getElem_cons_zero]
            have hne : x ≠ A[a] := fun h => hx (h ▸ List.getElem_mem ha)
            omega
      · rintro ⟨a, ha, hya, hall⟩
        by_cases haA : a < A.length
        · right
          rw [List.getElem_append_left haA] at hya
          refine ⟨⟨a, haA, hya, fun c hc hac => ?_⟩, ?_⟩
          · have := hall c (by omega) hac
            rwa [List.getElem_append_left hc, List.getElem_append_left haA] at this
          · have := hall A.length (by simp) (by omega)
            simp only [List.getElem_append_right (le_refl _), Nat.sub_self,
              List.getElem_cons_zero, List.getElem_append_left haA] at this
            omega
        · left
          have : a = A.length := by simp at ha; omega
          subst this
          simp only [List.getElem_append_right (le_refl _), Nat.sub_self,
            List.getElem_cons_zero] at hya
          exact hya.symm

/-- The label stack is the index stack `stk` read through the labels. -/
theorem runL_stack_eq_stk (A : List ℕ) (hA : A ≠ []) :
    (runL [] A).2 = (stk (runL [] A).1.tail).map (fun i => A.getD i 0) := by
  induction A using List.reverseRecOn with
  | nil => exact absurd rfl hA
  | append_singleton A x ih =>
    by_cases hA0 : A = []
    · subst hA0; simp [runL, stk, stkFrom]
    · have hP : (runL [] A).1 ≠ [] := by
        intro h; have := runL_length A []; rw [h] at this; simp at this; exact hA0 (List.length_eq_zero_iff.1 this.symm)
      rw [runL_snoc]
      dsimp only
      rw [List.tail_append_of_ne_nil hP, stk_append_single]
      have hlen : (runL [] A).1.tail.length + 1 = A.length := by
        rw [List.length_tail, runL_length]
        have := List.length_pos_of_ne_nil hA0; omega
      have hxA : (A ++ [x]).getD A.length 0 = x := by simp
      rw [hlen, List.map_cons, List.map_drop, hxA]
      congr 1
      have hmap : (stk (runL [] A).1.tail).map (fun i => (A ++ [x]).getD i 0) =
          (stk (runL [] A).1.tail).map (fun i => A.getD i 0) := by
        apply List.map_congr_left
        intro i hi
        have := stk_lt _ i hi
        rw [hlen] at this
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left this]
      rw [hmap, ← ih hA0]

theorem tail_take_runL (L : List ℕ) (b : ℕ) (hb : b < L.length) :
    ((runL [] L).1.tail).take b = (runL [] (L.take (b + 1))).1.tail := by
  have hsplit := runL_append (L.take (b + 1)) (L.drop (b + 1)) []
  rw [List.take_append_drop] at hsplit
  have hP : (runL [] L).1 = (runL [] (L.take (b + 1))).1 ++ _ := congrArg Prod.fst hsplit
  have hlen : (runL [] (L.take (b + 1))).1.length = b + 1 := by
    rw [runL_length, List.length_take]; omega
  rw [hP]
  generalize (runL [] (L.take (b + 1))).1 = P at hlen ⊢
  cases P with
  | nil => simp at hlen
  | cons p P =>
    simp only [List.cons_append, List.tail_cons, List.length_cons] at hlen ⊢
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

/-- **An element stays on the stack iff no later element exceeds it.** -/
theorem mem_stk_runL (A : List ℕ) (hA : A.Nodup) (a : ℕ) (ha : a < A.length) :
    a ∈ stk (runL [] A).1.tail ↔ ∀ (c : ℕ) (hc : c < A.length), a < c → A[c] < A[a] := by
  have hne : A ≠ [] := by intro h; subst h; simp at ha
  have hlen : (runL [] A).1.tail.length + 1 = A.length := by
    rw [List.length_tail, runL_length]; omega
  obtain ⟨_, hmem⟩ := runL_stack A hA
  rw [runL_stack_eq_stk A hne] at hmem
  have key := hmem A[a]
  rw [List.mem_map] at key
  constructor
  · intro h
    obtain ⟨a', ha', hya, hall⟩ := key.1 ⟨a, h, by simp [List.getElem?_eq_getElem ha]⟩
    have : a' = a := (List.Nodup.getElem_inj_iff hA).1 hya
    subst this
    exact hall
  · intro h
    obtain ⟨i, hi, hia⟩ := key.2 ⟨a, ha, rfl, h⟩
    have hil : i < A.length := by have := stk_lt _ i hi; omega
    rw [List.getD_eq_getElem _ _ hil] at hia
    have : i = a := (List.Nodup.getElem_inj_iff hA).1 hia
    subst this; exact hi

/-! ## i-p sequences have distinct labels and avoid the pattern `231` -/

theorem ipo_nodup : ∀ (t : T) (off : ℕ), (ipo off t).Nodup := by
  intro t
  induction t with
  | nil => intro off; simp
  | node v l r ihl ihr =>
    intro off
    simp only [ipo_node, List.nodup_cons, List.mem_append, not_or, List.nodup_append]
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, ihl off, ihr _, ?_⟩
    · have := ipo_mem l off _ h; omega
    · have := ipo_mem r _ _ h; omega
    · intro y hy z hz hyz
      have := ipo_mem l off y hy; have := ipo_mem r _ z hz; omega

/-- No positions `a < c < b` with `L[b] < L[a] < L[c]`. -/
def NoPat (L : List ℕ) : Prop :=
  ∀ a c b, a < c → c < b → b < L.length → ¬ (L.getD b 0 < L.getD a 0 ∧ L.getD a 0 < L.getD c 0)

theorem getD_cons_append (x : ℕ) (A B : List ℕ) (i : ℕ) (hi : i < A.length + B.length + 1) :
    (x :: (A ++ B)).getD i 0 =
      if i = 0 then x else if i ≤ A.length then A.getD (i - 1) 0 else B.getD (i - 1 - A.length) 0 := by
  rcases i with _ | i
  · simp
  · simp only [List.getD_cons_succ, Nat.add_sub_cancel, Nat.add_one_ne_zero, if_false]
    split
    · rw [List.getD_append _ _ _ _ (by omega)]
    · rw [List.getD_append_right _ _ _ _ (by omega)]

theorem getD_mem_of_lt (L : List ℕ) (i : ℕ) (h : i < L.length) : L.getD i 0 ∈ L := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

theorem noPat_cons_append (x : ℕ) (A B : List ℕ) (hA : NoPat A) (hB : NoPat B)
    (hAx : ∀ y ∈ A, y < x) (hBx : ∀ y ∈ B, x < y) : NoPat (x :: (A ++ B)) := by
  intro a c b hac hcb hbl
  simp only [List.length_cons, List.length_append] at hbl
  rw [getD_cons_append x A B b (by omega), getD_cons_append x A B a (by omega),
    getD_cons_append x A B c (by omega)]
  rintro ⟨h1, h2⟩
  by_cases ha0 : a = 0
  · -- the root plays `2`: then `b` is in `A`, so is `c`, and `L[c] < x`
    simp only [ha0, if_true] at h1 h2
    have hc0 : c ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    simp only [hc0, hb0, if_false] at h1 h2
    by_cases hbA : b ≤ A.length
    · simp only [show c ≤ A.length by omega, if_true] at h2
      have := hAx _ (getD_mem_of_lt A (c - 1) (by omega)); omega
    · simp only [hbA, if_false] at h1
      have := hBx _ (getD_mem_of_lt B (b - 1 - A.length) (by omega)); omega
  · have hc0 : c ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    simp only [ha0, hc0, hb0, if_false] at h1 h2
    by_cases haA : a ≤ A.length
    · simp only [haA, if_true] at h1 h2
      have hya := hAx _ (getD_mem_of_lt A (a - 1) (by omega))
      by_cases hbA : b ≤ A.length
      · simp only [hbA, if_true, show c ≤ A.length by omega] at h1 h2
        exact hA (a - 1) (c - 1) (b - 1) (by omega) (by omega) (by omega) ⟨h1, h2⟩
      · simp only [hbA, if_false] at h1
        have := hBx _ (getD_mem_of_lt B (b - 1 - A.length) (by omega)); omega
    · simp only [haA, if_false, show ¬ c ≤ A.length by omega, show ¬ b ≤ A.length by omega] at h1 h2
      exact hB (a - 1 - A.length) (c - 1 - A.length) (b - 1 - A.length) (by omega) (by omega)
        (by omega) ⟨h1, h2⟩

theorem ipo_noPat : ∀ (t : T) (off : ℕ), NoPat (ipo off t) := by
  intro t
  induction t with
  | nil => intro off a c b _ _ hb; simp at hb
  | node v l r ihl ihr =>
    intro off
    rw [ipo_node]
    exact noPat_cons_append _ _ _ (ihl off) (ihr _)
      (fun y hy => by have := ipo_mem l off y hy; omega)
      (fun y hy => by have := ipo_mem r _ y hy; omega)

/-! ## The bridge -/

/-- **The oracle is the order of the labels.**  For a nonempty tree `t` and
    elements `a, b` of its i-p sequence, `lt (toPop t) a b` holds iff the label
    of `a` is smaller than the label of `b`. -/
theorem lt_ip (t : T) (ht : t ≠ .nil) (a b : ℕ) (ha : a < t.numNodes) (hb : b < t.numNodes) :
    lt (toPop t) a b = decide ((ip t).getD a 0 < (ip t).getD b 0) := by
  set L := ip t with hL
  have hlen : L.length = t.numNodes := ip_length t
  have hnd : L.Nodup := ipo_nodup t 0
  have hpat : NoPat L := ipo_noPat t 0
  have hw : toPop t = (runL [] L).1.tail := by rw [hL, runL_ip t ht]; rfl
  -- distinct positions have distinct labels
  have hne : ∀ i j, i < L.length → j < L.length → i ≠ j → L.getD i 0 ≠ L.getD j 0 := by
    intro i j hi hj hij h
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h
    exact hij ((List.Nodup.getElem_inj_iff hnd).1 h)
  -- membership in the stack after element `b`, for `a < b`
  have hstk : ∀ a b, a < b → b < L.length →
      (a ∈ stk ((toPop t).take b) ↔ ∀ c, a < c → c ≤ b → L.getD c 0 < L.getD a 0) := by
    intro a b hab hbl
    rw [hw, tail_take_runL L b hbl]
    have hA : (L.take (b + 1)).Nodup := hnd.sublist (List.take_sublist _ _)
    have hAl : (L.take (b + 1)).length = b + 1 := by rw [List.length_take]; omega
    rw [mem_stk_runL _ hA a (by omega)]
    constructor
    · intro h c hac hcb
      have := h c (by omega) hac
      rw [List.getElem_take, List.getElem_take] at this
      rwa [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    · intro h c hc hac
      have := h c hac (by omega)
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at this
      rw [List.getElem_take, List.getElem_take]; exact this
  unfold lt
  rcases lt_trichotomy a b with hab | rfl | hba
  · rw [if_pos hab, decide_eq_decide, hstk a b hab (by omega)]
    constructor
    · intro h
      by_contra hn
      have hlt : L.getD b 0 < L.getD a 0 := by
        have := hne a b (by omega) (by omega) (by omega); omega
      apply h
      intro c hac hcb
      rcases Nat.lt_or_ge c b with hcb' | hcb'
      · by_contra hc
        have := hne a c (by omega) (by omega) (by omega)
        exact hpat a c b hac hcb' (by omega) ⟨hlt, by omega⟩
      · have : c = b := by omega
        subst this; exact hlt
    · intro h hall
      have := hall b hab le_rfl; omega
  · simp
  · rw [if_neg (by omega), if_pos hba, decide_eq_decide, hstk b a hba (by omega)]
    constructor
    · intro hall; exact hall a hba le_rfl
    · intro h c hbc hca
      rcases Nat.lt_or_ge c a with hca' | hca'
      · by_contra hc
        have := hne b c (by omega) (by omega) (by omega)
        exact hpat b c a hbc hca' (by omega) ⟨h, by omega⟩
      · have : c = a := by omega
        subst this; exact h

/-! ## One-pass programs on actual trees -/

/-- The answer a one-pass program gets at step `i` on the tree `t`: the order of
    the labels of two elements already read (`0, …, i`); a question about an
    element not yet read gets "no". -/
def ansIP (t : T) (i a b : ℕ) : Bool :=
  decide (a ≤ i ∧ b ≤ i ∧ (ip t).getD a 0 < (ip t).getD b 0)

/-- Questions asked by `P` on the tree `t` with the actual label comparisons,
    from the prefix `hist` of its codeword on. -/
def realCostAux (P : Prog) (t : T) : List ℕ → List ℕ → ℕ
  | _, [] => 0
  | hist, x :: w => ((P.step hist).eval (ansIP t (hist.length + 1))).2 + realCostAux P t (hist ++ [x]) w

/-- Questions asked by `P` on the tree `t`. -/
def realCost (P : Prog) (t : T) : ℕ := realCostAux P t [] (toPop t)

/-- `P` reconstructs every `n`-node tree when run on the actual labels. -/
def CorrectIP (P : Prog) (n : ℕ) : Prop :=
  ∀ t ∈ BinaryTree.treesOfNumNodesEq n, ∀ hist x rest, toPop t = hist ++ x :: rest →
    ((P.step hist).eval (ansIP t (hist.length + 1))).1 = parentOf hist x

/-- Drop the questions about elements beyond `i` (their answer is "no"). -/
def prune (i : ℕ) : Step → Step
  | .out p r => .out p r
  | .ask a b y n => if a ≤ i ∧ b ≤ i then .ask a b (prune i y) (prune i n) else prune i n

theorem prune_eval (i : ℕ) (ans1 ans2 : ℕ → ℕ → Bool)
    (hin : ∀ a b, a ≤ i → b ≤ i → ans2 a b = ans1 a b)
    (hout : ∀ a b, ¬ (a ≤ i ∧ b ≤ i) → ans1 a b = false) :
    ∀ s : Step, ((prune i s).eval ans2).1 = (s.eval ans1).1 ∧
      ((prune i s).eval ans2).2 ≤ (s.eval ans1).2 := by
  intro s
  induction s with
  | out p r => simp [prune, Step.eval]
  | ask a b y n ihy ihn =>
    simp only [prune]
    split
    · rename_i h
      simp only [Step.eval, hin a b h.1 h.2]
      split
      · exact ⟨ihy.1, by omega⟩
      · exact ⟨ihn.1, by omega⟩
    · rename_i h
      simp only [Step.eval, hout a b h, Bool.false_eq_true, if_false]
      exact ⟨ihn.1, by omega⟩

theorem lt_take (w : List ℕ) (i a b : ℕ) (ha : a ≤ i) (hb : b ≤ i) :
    lt (w.take i) a b = lt w a b := by
  unfold lt
  rw [List.take_take, List.take_take, Nat.min_eq_left hb, Nat.min_eq_left ha]

/-- On a tree, the oracle at step `i` agrees with the actual comparisons of
    elements already read. -/
theorem lt_eq_ansIP (t : T) (ht : t ≠ .nil) (hist : List ℕ) (x : ℕ) (rest : List ℕ)
    (hw : toPop t = hist ++ x :: rest) (a b : ℕ) (ha : a ≤ hist.length + 1)
    (hb : b ≤ hist.length + 1) :
    lt (hist ++ [x]) a b = ansIP t (hist.length + 1) a b := by
  have hn : (toPop t).length + 1 = t.numNodes := (toPop_length t ht).symm
  have hlen : hist.length + 1 ≤ (toPop t).length := by rw [hw]; simp
  have htake : hist ++ [x] = (toPop t).take (hist.length + 1) := by
    rw [hw, show hist ++ x :: rest = (hist ++ [x]) ++ rest by simp,
      List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
  rw [htake, lt_take _ _ _ _ ha hb, lt_ip t ht a b (by omega) (by omega)]
  simp [ansIP, ha, hb]

/-- The program that drops the questions about unread elements. -/
def Prog.pruned (P : Prog) : Prog where
  step hist := prune (hist.length + 1) (P.step hist)

theorem pruned_step (P : Prog) (t : T) (ht : t ≠ .nil) (hist : List ℕ) (x : ℕ)
    (rest : List ℕ) (hw : toPop t = hist ++ x :: rest) :
    ((P.pruned.step hist).eval (lt (hist ++ [x]))).1 =
        ((P.step hist).eval (ansIP t (hist.length + 1))).1 ∧
      ((P.pruned.step hist).eval (lt (hist ++ [x]))).2 ≤
        ((P.step hist).eval (ansIP t (hist.length + 1))).2 :=
  prune_eval (hist.length + 1) _ _ (fun a b ha hb => lt_eq_ansIP t ht hist x rest hw a b ha hb)
    (fun a b h => by simp only [ansIP]; simp only [decide_eq_false_iff_not]; tauto) _

theorem trees_ne_nil {n : ℕ} (hn : 1 ≤ n) {t : T} (ht : t ∈ BinaryTree.treesOfNumNodesEq n) :
    t ≠ .nil := by
  rw [BinaryTree.mem_treesOfNumNodesEq] at ht
  rintro rfl; simp [BinaryTree.numNodes] at ht; omega

theorem progCost_pruned_le (P : Prog) (t : T) (ht : t ≠ .nil) :
    ∀ (rest hist : List ℕ), toPop t = hist ++ rest →
      progCost P.pruned hist rest ≤ realCostAux P t hist rest := by
  intro rest
  induction rest with
  | nil => intro _ _; simp [progCost, realCostAux]
  | cons x rest ih =>
    intro hist hw
    have h1 := (pruned_step P t ht hist x rest hw).2
    have h2 := ih (hist ++ [x]) (by rw [hw]; simp)
    simp only [progCost, realCostAux]
    omega

/-- **Lower bound for one-pass programs on actual trees.**  Every one-pass
    program that reconstructs all `n`-node trees from the comparisons of their
    labels asks at least `2n - 3` questions on some tree (`n ≥ 2`). -/
theorem onePass_trees (n : ℕ) (hn : 2 ≤ n) (P : Prog) (hc : CorrectIP P n) :
    ∃ t ∈ BinaryTree.treesOfNumNodesEq n, 2 * n - 3 ≤ realCost P t := by
  -- the pruned program is correct on the codeword space
  have hcorr : Correct P.pruned n := by
    intro hist x rest hmem
    rw [← image_toPop_eq_suffixes n (by omega)] at hmem
    obtain ⟨t, ht, hw⟩ := Finset.mem_image.mp hmem
    rw [(pruned_step P t (trees_ne_nil (by omega) ht) hist x rest hw).1]
    exact hc t ht hist x rest hw
  obtain ⟨w, hw, hle⟩ := prog_lower P.pruned n hn hcorr
  rw [← image_toPop_eq_suffixes n (by omega)] at hw
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hw
  refine ⟨t, ht, ?_⟩
  have := progCost_pruned_le P t (trees_ne_nil (by omega) ht) (toPop t) [] (by simp)
  unfold realCost; omega

/-! ## M on actual trees -/

/-- Every question of `s` is about elements `≤ i`. -/
def InRange (i : ℕ) : Step → Prop
  | .out _ _ => True
  | .ask a b y n => a ≤ i ∧ b ≤ i ∧ InRange i y ∧ InRange i n

theorem eval_congr (i : ℕ) (ans1 ans2 : ℕ → ℕ → Bool)
    (h : ∀ a b, a ≤ i → b ≤ i → ans1 a b = ans2 a b) :
    ∀ s : Step, InRange i s → s.eval ans1 = s.eval ans2 := by
  intro s
  induction s with
  | out p r => intro _; rfl
  | ask a b y n ihy ihn =>
    intro hs
    obtain ⟨ha, hb, hy, hn⟩ := hs
    simp only [Step.eval, h a b ha hb, ihy hy, ihn hn]

theorem popChain_inRange (i : ℕ) :
    ∀ (L : List ℕ) (prev : ℕ), (∀ y ∈ L, y ≤ i) → InRange i (popChain i prev L) := by
  intro L
  induction L with
  | nil => intro _ _; trivial
  | cons r L ih =>
    intro prev hL
    exact ⟨hL r (by simp), le_rfl, ih r (fun y hy => hL y (by simp [hy])), trivial⟩

theorem mStep_inRange (i : ℕ) (S : List ℕ) (hS : ∀ y ∈ S, y ≤ i) : InRange i (mStep i S) := by
  cases S with
  | nil => trivial
  | cons t rest =>
    exact ⟨hS t (by simp), le_rfl, popChain_inRange i rest t (fun y hy => hS y (by simp [hy])),
      trivial⟩

theorem progM_inRange (hist : List ℕ) : InRange (hist.length + 1) (progM.step hist) :=
  mStep_inRange _ _ (fun y hy => by have := stk_lt hist y hy; omega)

/-- **M reconstructs every tree** from the actual comparisons (with the parent
    of each element given by the reconstruction stack, `parentOf`). -/
theorem progM_correctIP (n : ℕ) (hn : 1 ≤ n) : CorrectIP progM n := by
  intro t ht hist x rest hw
  have hne := trees_ne_nil hn ht
  rw [← eval_congr (hist.length + 1) (lt (hist ++ [x])) _
    (fun a b ha hb => lt_eq_ansIP t hne hist x rest hw a b ha hb) _ (progM_inRange hist)]
  exact progM_correct n hist x rest (by rw [← hw]; exact toPop_mapsTo n hn t ht)

theorem realCostAux_M (t : T) (ht : t ≠ .nil) :
    ∀ (rest hist : List ℕ), toPop t = hist ++ rest →
      realCostAux progM t hist rest = progCost progM hist rest := by
  intro rest
  induction rest with
  | nil => intro _ _; simp [progCost, realCostAux]
  | cons x rest ih =>
    intro hist hw
    simp only [progCost, realCostAux]
    rw [ih (hist ++ [x]) (by rw [hw]; simp),
      eval_congr (hist.length + 1) _ (lt (hist ++ [x]))
        (fun a b ha hb => (lt_eq_ansIP t ht hist x rest hw a b ha hb).symm) _ (progM_inRange hist)]

/-- **Worst-case optimality among one-pass programs on actual trees.**  For
    `n ≥ 2`: every correct one-pass program asks at least `2n - 3` label
    comparisons on some `n`-node tree; M is correct and asks at most `2n - 3` on
    every `n`-node tree. -/
theorem onePass_trees_opt (n : ℕ) (hn : 2 ≤ n) :
    (∀ P : Prog, CorrectIP P n →
      ∃ t ∈ BinaryTree.treesOfNumNodesEq n, 2 * n - 3 ≤ realCost P t) ∧
    CorrectIP progM n ∧
    (∀ t ∈ BinaryTree.treesOfNumNodesEq n, realCost progM t ≤ 2 * n - 3) := by
  refine ⟨fun P hc => onePass_trees n hn P hc, progM_correctIP n (by omega), fun t ht => ?_⟩
  unfold realCost
  rw [realCostAux_M t (trees_ne_nil (by omega) ht) (toPop t) [] (by simp)]
  exact (onePass_programs n hn).2.2 _ (toPop_mapsTo n (by omega) t ht)

end MakinenAnalysis.OnePass
