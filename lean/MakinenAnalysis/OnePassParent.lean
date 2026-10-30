/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.

# The stack parent is the tree parent

`OnePassBridge` specifies the output of a one-pass program by the
reconstruction stack (`parentOf`).  This file shows that this is the parent in
the tree, for every tree:

* `treePar t q ctx` lists, in preorder, the parent of each node of `t` and
  whether the node is a right child (positions start at `q`; the root's parent
  is `ctx`);
* `parentOf_eq_treePar`: at the step that reads element `i`, `parentOf` is the
  `i`-th entry of `treePar t 0 _`, i.e. the actual parent of element `i`;
* `onePass_trees_real`: the optimality theorem of `OnePassBridge` with the
  outputs specified by the tree parents.

This is the correctness of the stack reconstruction for all sizes (the
reconstruction itself is the Rocq development's `ReconstructFull`; in Lean the
array-building runs of `ExecModel` were checked only for `n ≤ 8`).  The proof
uses only the stack positions and the pop counts, not the labels.
-/
import MakinenAnalysis.OnePassBridge

namespace MakinenAnalysis.OnePass

/-- The parent chosen by a step that pops `x` nodes from the stack `s`. -/
def parAt (s : List ℕ) (x : ℕ) : ℕ × Bool :=
  if x = 0 then (s.headD 0, false) else (s.getD (x - 1) 0, true)

theorem parentOf_eq_parAt (p : List ℕ) (k : ℕ) : parentOf p k = parAt (stk p) k := rfl

/-- The parents chosen while processing the pop counts `w` from the stack `s`,
    the first of them being element `j`. -/
def parentsFrom : ℕ → List ℕ → List ℕ → List (ℕ × Bool)
  | _, _, [] => []
  | j, s, x :: w => parAt s x :: parentsFrom (j + 1) (j :: s.drop x) w

theorem stkFrom_append : ∀ (u v : List ℕ) (j : ℕ) (s : List ℕ),
    stkFrom j s (u ++ v) = stkFrom (j + u.length) (stkFrom j s u) v := by
  intro u
  induction u with
  | nil => intro v j s; simp [stkFrom]
  | cons x u ih =>
    intro v j s
    simp only [List.cons_append, stkFrom, ih, List.length_cons]
    congr 1; omega

theorem parentsFrom_append : ∀ (u v : List ℕ) (j : ℕ) (s : List ℕ),
    parentsFrom j s (u ++ v) = parentsFrom j s u ++ parentsFrom (j + u.length) (stkFrom j s u) v := by
  intro u
  induction u with
  | nil => intro v j s; simp [parentsFrom, stkFrom]
  | cons x u ih =>
    intro v j s
    simp only [List.cons_append, parentsFrom, ih, stkFrom, List.length_cons,
      show j + (u.length + 1) = j + 1 + u.length by omega]

theorem parentsFrom_length : ∀ (w : List ℕ) (j : ℕ) (s : List ℕ), (parentsFrom j s w).length = w.length := by
  intro w
  induction w with
  | nil => intro j s; rfl
  | cons x w ih => intro j s; simp [parentsFrom, ih]

/-- The parent of each node of `t`, in preorder, with positions starting at `q`;
    the root's parent is `ctx`.  The second component is `true` for a right
    child. -/
def treePar : T → ℕ → ℕ × Bool → List (ℕ × Bool)
  | .nil, _, _ => []
  | .node _ l r, q, ctx =>
    ctx :: (treePar l (q + 1) (q, false) ++ treePar r (q + 1 + l.numNodes) (q, true))

/-- **The run on a subtree.**  Processing the codeword of `t` (positions from `q`)
    from a stack `low ++ high`, where the root pops exactly `low`, chooses the
    tree parents, the root's being the one the stack gives, and leaves `rem t`
    nodes of `t` on top of `high`. -/
theorem tree_run : ∀ (t : T) (q : ℕ) (low high : List ℕ), t ≠ .nil →
    parentsFrom q (low ++ high) (low.length :: toPop t) =
        treePar t q (parAt (low ++ high) low.length) ∧
      ∃ rho : List ℕ, stkFrom q (low ++ high) (low.length :: toPop t) = rho ++ high ∧
        rho.length = rem t := by
  intro t
  induction t with
  | nil => intro _ _ _ h; exact absurd rfl h
  | node v l r ihl ihr =>
    intro q low high _
    have hdrop : (low ++ high).drop low.length = high := List.drop_left
    have h0 : (BinaryTree.nil : T).numNodes = 0 := rfl
    by_cases hl : l = .nil
    · subst hl
      by_cases hr : r = .nil
      · subst hr
        refine ⟨?_, [q], ?_, ?_⟩
        · simp [parentsFrom, treePar]
        · simp [stkFrom, hdrop]
        · simp
      · obtain ⟨hp, rho, hs, hlen⟩ := ihr (q + 1) [q] high hr
        simp only [List.length_singleton, List.singleton_append, parentsFrom, stkFrom] at hp hs
        refine ⟨?_, rho, ?_, ?_⟩
        · rw [toPop_lR hr]
          simp only [parentsFrom, hdrop, treePar, List.nil_append, h0, Nat.add_zero, hp]
          simp [parAt]
        · rw [toPop_lR hr]
          simp only [stkFrom, hdrop]
          exact hs
        · rw [hlen, rem_lR hr]
    · obtain ⟨hpL, rhoL, hsL, hlenL⟩ := ihl (q + 1) [] (q :: high) hl
      simp only [List.nil_append, List.length_nil] at hpL hsL
      have hLlen : (0 :: toPop l).length = l.numNodes := by
        rw [toPop_length l hl]; simp
      have hctxL : parAt (q :: high) 0 = (q, false) := by simp [parAt]
      rw [hctxL] at hpL
      by_cases hr : r = .nil
      · subst hr
        refine ⟨?_, rhoL ++ [q], ?_, ?_⟩
        · rw [toPop_Ln hl]
          have e : parentsFrom q (low ++ high) (low.length :: 0 :: toPop l) =
              parAt (low ++ high) low.length :: parentsFrom (q + 1) (q :: high) (0 :: toPop l) := by
            simp only [parentsFrom, hdrop]
          rw [e, hpL]
          simp [treePar]
        · rw [toPop_Ln hl]
          have e : stkFrom q (low ++ high) (low.length :: 0 :: toPop l) =
              stkFrom (q + 1) (q :: high) (0 :: toPop l) := by
            simp only [stkFrom, hdrop]
          rw [e, hsL]; simp
        · rw [rem_Ln hl]; simp [hlenL]
      · obtain ⟨hpR, rho, hsR, hlenR⟩ := ihr (q + 1 + l.numNodes) (rhoL ++ [q]) high hr
        have hlow : (rhoL ++ [q]).length = rem l + 1 := by simp [hlenL]
        rw [hlow] at hpR hsR
        have hctx : parAt (rhoL ++ [q] ++ high) (rem l + 1) = (q, true) := by
          simp only [parAt, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
          rw [← hlenL, List.append_assoc, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
          simp
        rw [hctx] at hpR
        have hmid : rhoL ++ q :: high = rhoL ++ [q] ++ high := by simp
        refine ⟨?_, rho, ?_, ?_⟩
        · rw [toPop_LR hl hr]
          have e : parentsFrom q (low ++ high) (low.length :: ((0 :: toPop l) ++ (rem l + 1) :: toPop r)) =
              parAt (low ++ high) low.length ::
                parentsFrom (q + 1) (q :: high) ((0 :: toPop l) ++ (rem l + 1) :: toPop r) := by
            simp only [parentsFrom, hdrop]
          rw [e, parentsFrom_append, hpL, hLlen, hsL, hmid, hpR]
          simp [treePar]
        · rw [toPop_LR hl hr]
          have e : stkFrom q (low ++ high) (low.length :: ((0 :: toPop l) ++ (rem l + 1) :: toPop r)) =
              stkFrom (q + 1) (q :: high) ((0 :: toPop l) ++ (rem l + 1) :: toPop r) := by
            simp only [stkFrom, hdrop]
          rw [e, stkFrom_append, hsL, hLlen, hmid, hsR]
        · rw [hlenR, rem_Rnn hr]

/-- The parents chosen by the stack along the whole codeword of a tree are the
    tree parents of the elements `1, …, n - 1`. -/
theorem parentsFrom_toPop (t : T) (ht : t ≠ .nil) :
    parentsFrom 1 [0] (toPop t) = (treePar t 0 (0, false)).tail := by
  have := (tree_run t 0 [] [] ht).1
  simp only [List.nil_append, List.length_nil] at this
  have e : parAt [] 0 = (0, false) := rfl
  rw [e] at this
  rw [← this]
  simp [parentsFrom]

/-- **The stack parent is the tree parent.**  At the step reading element
    `i = |hist| + 1` of the i-p sequence of `t`, `parentOf` is the actual parent
    of element `i` (and whether it is a right child). -/
theorem parentOf_eq_treePar (t : T) (ht : t ≠ .nil) (hist : List ℕ) (x : ℕ) (rest : List ℕ)
    (hw : toPop t = hist ++ x :: rest) :
    parentOf hist x = (treePar t 0 (0, false)).getD (hist.length + 1) (0, false) := by
  have h1 := parentsFrom_toPop t ht
  rw [hw, parentsFrom_append] at h1
  have hlen := parentsFrom_length hist 1 [0]
  have hidx : (treePar t 0 (0, false)).getD (hist.length + 1) (0, false) =
      ((treePar t 0 (0, false)).tail).getD hist.length (0, false) := by
    cases treePar t 0 (0, false) with
    | nil => simp
    | cons a L => simp
  rw [hidx, ← h1, List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
  simp only [parentsFrom, List.getD_cons_zero]
  rw [parentOf_eq_parAt]
  rfl

/-- `P` reconstructs every `n`-node tree from the actual comparisons: at each
    step it outputs the actual parent of the new element. -/
def CorrectTree (P : Prog) (n : ℕ) : Prop :=
  ∀ t ∈ BinaryTree.treesOfNumNodesEq n, ∀ hist x rest, toPop t = hist ++ x :: rest →
    ((P.step hist).eval (ansIP t (hist.length + 1))).1 =
      (treePar t 0 (0, false)).getD (hist.length + 1) (0, false)

theorem correctTree_iff (P : Prog) (n : ℕ) (hn : 1 ≤ n) : CorrectTree P n ↔ CorrectIP P n := by
  constructor
  · intro h t ht hist x rest hw
    rw [h t ht hist x rest hw, parentOf_eq_treePar t (trees_ne_nil hn ht) hist x rest hw]
  · intro h t ht hist x rest hw
    rw [h t ht hist x rest hw, parentOf_eq_treePar t (trees_ne_nil hn ht) hist x rest hw]

/-- **Worst-case optimality of M among one-pass reconstruction programs.**  For
    `n ≥ 2`: every one-pass program that reconstructs all `n`-node trees from
    the comparisons of their labels (outputting the actual parent of each element
    before reading the next) makes at least `2n - 3` comparisons on some tree;
    M does so correctly and makes at most `2n - 3` on every tree. -/
theorem onePass_trees_real (n : ℕ) (hn : 2 ≤ n) :
    (∀ P : Prog, CorrectTree P n →
      ∃ t ∈ BinaryTree.treesOfNumNodesEq n, 2 * n - 3 ≤ realCost P t) ∧
    CorrectTree progM n ∧
    (∀ t ∈ BinaryTree.treesOfNumNodesEq n, realCost progM t ≤ 2 * n - 3) := by
  obtain ⟨h1, h2, h3⟩ := onePass_trees_opt n hn
  refine ⟨fun P hc => h1 P ((correctTree_iff P n (by omega)).1 hc),
    (correctTree_iff progM n (by omega)).2 h2, h3⟩

/-! ## A check on the running example (the i-p sequence `3 2 1 5 4 6`) -/

/-- The six-node tree of the paper's running example. -/
def exampleTree : T :=
  .node () (.node () (.node () .nil .nil) .nil) (.node () (.node () .nil .nil) (.node () .nil .nil))

-- positions 0..5 in preorder: 1 and 2 are left children of 0 and 1; 3 is the right child of 0;
-- 4 and 5 are the left and right children of 3
example : treePar exampleTree 0 (0, false) =
    [(0, false), (0, false), (1, false), (0, true), (3, false), (3, true)] := by decide

example : (List.range 5).map (fun i => parentOf ((toPop exampleTree).take i) ((toPop exampleTree).getD i 0)) =
    (treePar exampleTree 0 (0, false)).tail := by decide

end MakinenAnalysis.OnePass
