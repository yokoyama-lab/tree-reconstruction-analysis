/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.

# Worst-case optimality of M among one-pass algorithms

Model.  A one-pass algorithm
reads the i-p sequence left to right and fixes the parent of each element before
reading the next one.  With the stack at height `m` (sentinel excluded), the next
element pops some `k ∈ [0, m]` nodes, and the tree is determined by the sequence
of `k`s (the codeword, `Valid` in `BallotCount`).  The only comparisons that
carry information about `k` compare the new element with the `j`-th stack entry,
i.e. ask "is `k ≥ j`?".  So at each step the algorithm uses an *ordered decision
tree* over the outcomes `0, …, m` (`WF t 0 m`), and it may choose that tree from
the whole history.  The number of comparisons in a step is the depth of the leaf
reached.

This file proves, inside that model:

* `onePass_lower`: every one-pass algorithm makes at least `2n - 3` comparisons on
  the codeword `0, 1, 1, …, 1` (length `n - 1`), which is valid;
* `costM_eq`, `costM_le`: Mäkinen's algorithm M, which compares from the top of
  the stack down (and skips the comparison with the sentinel), makes exactly
  `(n - 1) + S - Q` comparisons, hence at most `2n - 3` on every valid codeword;
* `onePass_worst_case`: the two together.

The reduction from real one-pass programs to this model (which comparisons carry
information) is a paper argument and is not formalised here.
-/
import MakinenAnalysis.BallotCount

namespace MakinenAnalysis.OnePass

/-- An ordered decision tree.  `node j l r` asks "is `k ≤ j`?" and goes to `l`
    on yes, `r` on no; a leaf names the outcome. -/
inductive OTree where
  | leaf (k : ℕ)
  | node (j : ℕ) (l r : OTree)

/-- `WF t a b`: `t` decides `k ∈ [a, b]` by threshold questions, with the leaves
    `a, a+1, …, b` in order. -/
inductive WF : OTree → ℕ → ℕ → Prop
  | leaf (a : ℕ) : WF (.leaf a) a a
  | node {j a b : ℕ} {l r : OTree} :
      a ≤ j → j < b → WF l a j → WF r (j + 1) b → WF (.node j l r) a b

/-- Number of questions asked before reaching outcome `k`. -/
def depth : OTree → ℕ → ℕ
  | .leaf _, _ => 0
  | .node j l r, k => 1 + if k ≤ j then depth l k else depth r k

theorem WF.le {t : OTree} {a b : ℕ} (h : WF t a b) : a ≤ b := by
  induction h with
  | leaf => exact le_rfl
  | node h1 h2 _ _ _ _ => omega

/-- With at least two outcomes, every outcome costs a question. -/
theorem depth_pos {t : OTree} {a b : ℕ} (h : WF t a b) (hab : a < b) (k : ℕ) :
    1 ≤ depth t k := by
  cases h with
  | leaf => omega
  | node => simp only [depth]; omega

/-- An outcome that is neither the first nor the last costs two questions. -/
theorem depth_inner {t : OTree} {a b k : ℕ} (h : WF t a b) (hak : a < k) (hkb : k < b) :
    2 ≤ depth t k := by
  cases h with
  | leaf => omega
  | @node j _ _ l r h1 h2 hl hr =>
    simp only [depth]
    split
    · have := depth_pos hl (by omega) k; omega
    · have := depth_pos hr (by omega) k; omega

/-- A one-pass algorithm: from the history of outcomes and the current height
    `m`, an ordered decision tree over `0, …, m`. -/
structure Alg where
  tree : List ℕ → ℕ → OTree
  wf : ∀ hist m, WF (tree hist m) 0 m

/-- Comparisons made by `A` on the rest `w` of a codeword, from height `h`
    after history `hist`. -/
def cost (A : Alg) : List ℕ → ℕ → List ℕ → ℕ
  | _, _, [] => 0
  | hist, h, x :: w => depth (A.tree hist h) x + cost A (hist ++ [x]) (h + 1 - x) w

/-! ## The lower bound -/

/-- The adversary's codeword `0, 1, 1, …, 1` of length `n - 1`. -/
def adv (n : ℕ) : List ℕ := 0 :: List.replicate (n - 2) 1

theorem valid_replicate_one (r h : ℕ) (hh : 1 ≤ h) : Valid h (List.replicate r 1) := by
  induction r with
  | zero => simp [Valid]
  | succ r ih =>
    simp only [List.replicate_succ, Valid]
    exact ⟨hh, by rw [show h + 1 - 1 = h by omega]; exact ih⟩

theorem adv_mem (n : ℕ) (hn : 2 ≤ n) : adv n ∈ suffixes (n - 1) 1 := by
  rw [mem_suffixes]
  refine ⟨by simp [adv]; omega, ?_⟩
  simp only [adv, Valid]
  exact ⟨by omega, valid_replicate_one _ _ (by omega)⟩

/-- At height 2 the outcome 1 is the middle one of three: two questions each. -/
theorem cost_replicate (A : Alg) (r : ℕ) :
    ∀ hist, 2 * r ≤ cost A hist 2 (List.replicate r 1) := by
  induction r with
  | zero => intro hist; simp
  | succ r ih =>
    intro hist
    simp only [List.replicate_succ, cost, Nat.add_sub_cancel]
    have h1 := depth_inner (A.wf hist 2) (k := 1) (by omega) (by omega)
    have h2 := ih (hist ++ [1])
    omega

/-- **Lower bound.**  Every one-pass algorithm makes at least `2n - 3`
    informative comparisons on the valid codeword `adv n`. -/
theorem onePass_lower (A : Alg) (n : ℕ) (hn : 2 ≤ n) : 2 * n - 3 ≤ cost A [] 1 (adv n) := by
  simp only [adv, cost, Nat.sub_zero, Nat.reduceAdd]
  have h0 := depth_pos (A.wf [] 1) (by omega) 0
  have h1 := cost_replicate A (n - 2) ([] ++ [0])
  omega

/-! ## Mäkinen's algorithm attains it -/

/-- The unary tree on `a, …, b`: ask "is `k ≤ a`?", then "is `k ≤ a+1`?", … .
    This is M comparing the new element with the stack from the top down; the
    last outcome `b` needs no question about the sentinel. -/
def unary (a b : ℕ) : OTree :=
  if a < b then .node a (.leaf a) (unary (a + 1) b) else .leaf a
termination_by b - a

theorem unary_wf (a b : ℕ) (hab : a ≤ b) : WF (unary a b) a b := by
  induction h : b - a generalizing a with
  | zero =>
    rw [unary, if_neg (by omega)]
    rw [show b = a by omega]; exact .leaf a
  | succ d ih =>
    rw [unary, if_pos (by omega)]
    exact .node le_rfl (by omega) (.leaf a) (ih (a + 1) (by omega) (by omega))

theorem depth_unary (a b k : ℕ) (hak : a ≤ k) (hkb : k ≤ b) :
    depth (unary a b) k = if k < b then k - a + 1 else b - a := by
  induction h : b - a generalizing a with
  | zero =>
    rw [unary, if_neg (by omega)]
    simp only [depth]
    split <;> omega
  | succ d ih =>
    rw [unary, if_pos (by omega)]
    simp only [depth]
    by_cases hk : k ≤ a
    · rw [if_pos hk]; split <;> omega
    · rw [if_neg hk, ih (a + 1) (by omega) (by omega)]
      split <;> omega

/-- Mäkinen's algorithm in the model: the unary tree at every step. -/
def algM : Alg where
  tree _ m := unary 0 m
  wf _ m := unary_wf 0 m (Nat.zero_le m)

/-- Steps that pop the whole stack, i.e. the comparisons with the sentinel that
    M skips: `Q = #{i : x_i = h_{i-1}}`. -/
def qcount : ℕ → List ℕ → ℕ
  | _, [] => 0
  | h, x :: w => (if x = h then 1 else 0) + qcount (h + 1 - x) w

theorem costM_aux :
    ∀ (w : List ℕ) (h : ℕ) (hist : List ℕ), 1 ≤ h → Valid h w →
      cost algM hist h w + finalH h w + qcount h w = h + 2 * w.length ∧ 1 ≤ finalH h w := by
  intro w
  induction w with
  | nil => intro h hist hh _; simp [cost, finalH, qcount]; omega
  | cons x w ih =>
    intro h hist hh hv
    simp only [Valid] at hv
    obtain ⟨hxh, hv⟩ := hv
    obtain ⟨ih1, ih2⟩ := ih (h + 1 - x) (hist ++ [x]) (by omega) hv
    simp only [cost, finalH, qcount, List.length_cons]
    have hd : depth (algM.tree hist h) x = if x < h then x + 1 else h := by
      simp only [algM]; rw [depth_unary 0 h x (by omega) hxh]; split <;> omega
    rw [hd]
    refine ⟨?_, ih2⟩
    split <;> split <;> omega

/-- After at least one step, final height 1 means the last step popped the
    whole stack. -/
theorem qcount_pos_of_finalH_one :
    ∀ (w : List ℕ) (h : ℕ), 1 ≤ h → Valid h w → w ≠ [] → finalH h w = 1 → 1 ≤ qcount h w := by
  intro w
  induction w with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons x w ih =>
    intro h hh hv _ hf
    simp only [Valid] at hv
    obtain ⟨hxh, hv⟩ := hv
    simp only [finalH] at hf
    simp only [qcount]
    cases w with
    | nil =>
      simp only [finalH] at hf
      rw [if_pos (by omega)]; omega
    | cons y w' =>
      have := ih (h + 1 - x) (by omega) hv (List.cons_ne_nil _ _) hf
      omega

/-- **M's informative comparisons**: exactly `(n - 1) + S - Q`
    (`S` = total pops, `Q` = steps popping the whole stack). -/
theorem costM_eq (w : List ℕ) (hv : Valid 1 w) :
    cost algM [] 1 w + qcount 1 w = w.length + w.sum := by
  obtain ⟨h1, _⟩ := costM_aux w 1 [] le_rfl hv
  have hf : ∀ (w : List ℕ) (h : ℕ), Valid h w → finalH h w + w.sum = h + w.length := by
    intro w
    induction w with
    | nil => intro h _; simp [finalH]
    | cons x w ih =>
      intro h hv
      simp only [Valid] at hv
      have := ih (h + 1 - x) hv.2
      simp only [finalH, List.sum_cons, List.length_cons]
      omega
  have := hf w 1 hv
  omega

/-- **M attains the bound**: at most `2n - 3` on every valid codeword. -/
theorem costM_le (n : ℕ) (hn : 2 ≤ n) (w : List ℕ) (hw : w ∈ suffixes (n - 1) 1) :
    cost algM [] 1 w ≤ 2 * n - 3 := by
  rw [mem_suffixes] at hw
  obtain ⟨hlen, hv⟩ := hw
  obtain ⟨h1, h2⟩ := costM_aux w 1 [] le_rfl hv
  by_cases hf : finalH 1 w = 1
  · have := qcount_pos_of_finalH_one w 1 le_rfl hv
      (by intro h; rw [h] at hlen; simp at hlen; omega) hf
    omega
  · omega

/-- **Worst-case optimality among one-pass algorithms.**  For `n ≥ 2`, every
    one-pass algorithm makes at least `2n - 3` informative comparisons on some
    valid codeword of length `n - 1`, and M makes at most `2n - 3` on every one. -/
theorem onePass_worst_case (n : ℕ) (hn : 2 ≤ n) :
    (∀ A : Alg, ∃ w ∈ suffixes (n - 1) 1, 2 * n - 3 ≤ cost A [] 1 w) ∧
    (∀ w ∈ suffixes (n - 1) 1, cost algM [] 1 w ≤ 2 * n - 3) :=
  ⟨fun A => ⟨adv n, adv_mem n hn, onePass_lower A n hn⟩, costM_le n hn⟩

end MakinenAnalysis.OnePass
