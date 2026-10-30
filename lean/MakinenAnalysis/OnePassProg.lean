/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.

# From one-pass comparison programs to ordered decision trees

`OnePass` proves the worst-case bound `2n - 3` for *ordered decision trees*
chosen step by step.  This file closes the gap to programs.

* A **program** (`Prog`) chooses, at step `i`, a binary decision tree of
  comparison questions "is the label of element `a` smaller than that of
  element `b`?" (`Step`), whose leaves name the parent of element `i` and the
  side.  The choice may depend on everything read so far.
* **One pass** is built into the semantics: the questions at step `i` are
  answered from the codeword prefix `x_1, …, x_i` only (`lt`), i.e. from the
  elements `0, …, i` read so far.  Comparisons with sentinels are not modelled
  (their outcome is fixed) and so are not counted.
* `lt u a b` is the order of the labels, read off the reconstruction stack:
  for `a < b`, the label of `a` is smaller iff `a` is no longer on the stack
  after element `b` has been read.  `OnePassBridge` (separate file) checks this
  against the labels of actual i-p sequences.

Main results:

* `extract_wf`, `extract_depth` (generic): a step tree whose answers are
  monotone or antitone in the pop count `k` can be turned into an ordered
  decision tree on `0, …, m` that is no deeper on any `k` it must tell apart;
* `lt_mono_or_anti`: every question at a step is monotone or antitone in `k`;
* `parentOf_inj`: distinct pop counts give distinct parents;
* `progCost_ge`: a correct program asks at least as many questions as the
  extracted `Alg`, hence `prog_lower`: every correct one-pass program asks at
  least `2n - 3` questions on some valid input.
-/
import MakinenAnalysis.OnePass

namespace MakinenAnalysis.OnePass

open Classical

/-! ## Step trees and their evaluation -/

/-- The decision tree of one step.  `ask a b y n` asks "is the label of `a`
    smaller than that of `b`?" and continues with `y` on yes, `n` on no.
    `out p r` outputs the parent `p` of the new element, a right child iff `r`. -/
inductive Step where
  | out (p : ℕ) (r : Bool)
  | ask (a b : ℕ) (y n : Step)

/-- Evaluate a step tree against the answers `ans`; returns the output and the
    number of questions asked. -/
def Step.eval (ans : ℕ → ℕ → Bool) : Step → (ℕ × Bool) × ℕ
  | .out p r => ((p, r), 0)
  | .ask a b y n =>
    if ans a b then ((y.eval ans).1, (y.eval ans).2 + 1)
    else ((n.eval ans).1, (n.eval ans).2 + 1)

/-! ## Generic extraction of an ordered decision tree -/

/-- A Boolean function of `k` that can switch from `false` to `true` only. -/
def MonoB (g : ℕ → Bool) : Prop := ∀ k k', k ≤ k' → g k = true → g k' = true

/-- A Boolean function of `k` that can switch from `true` to `false` only. -/
def AntiB (g : ℕ → Bool) : Prop := ∀ k k', k ≤ k' → g k' = true → g k = true

/-- Turn a step tree into an ordered decision tree on `[lo, hi]`, where the
    answer to `ask a b` at outcome `k` is `f a b k`.  A question whose answer is
    constant on the interval is dropped; otherwise it becomes the threshold at
    the first `k` where the answer changes. -/
noncomputable def extract (f : ℕ → ℕ → ℕ → Bool) : Step → ℕ → ℕ → OTree
  | .out _ _, lo, hi => unary lo hi
  | .ask a b y n, lo, hi =>
    if h : ∃ c, lo < c ∧ c ≤ hi ∧ f a b c ≠ f a b lo then
      if f a b lo then .node (Nat.find h - 1) (extract f y lo (Nat.find h - 1)) (extract f n (Nat.find h) hi)
      else .node (Nat.find h - 1) (extract f n lo (Nat.find h - 1)) (extract f y (Nat.find h) hi)
    else if f a b lo then extract f y lo hi else extract f n lo hi

theorem extract_wf (f : ℕ → ℕ → ℕ → Bool) :
    ∀ (s : Step) (lo hi : ℕ), lo ≤ hi → WF (extract f s lo hi) lo hi := by
  intro s
  induction s with
  | out p r => intro lo hi h; exact unary_wf lo hi h
  | ask a b y n ihy ihn =>
    intro lo hi hlh
    simp only [extract]
    split
    · rename_i h
      have hc := Nat.find_spec h
      have e : Nat.find h - 1 + 1 = Nat.find h := by omega
      split
      · refine .node (by omega) (by omega) (ihy _ _ (by omega)) ?_
        rw [e]; exact ihn _ _ hc.2.1
      · refine .node (by omega) (by omega) (ihn _ _ (by omega)) ?_
        rw [e]; exact ihy _ _ hc.2.1
    · split
      · exact ihy _ _ hlh
      · exact ihn _ _ hlh

/-- Below the first change point `c` the answer equals the answer at `lo`; from
    `c` on it differs (by monotonicity or antitonicity). -/
theorem split_sides (g : ℕ → Bool) (hg : MonoB g ∨ AntiB g) (lo c hi : ℕ)
    (hc : lo < c ∧ c ≤ hi ∧ g c ≠ g lo) (hmin : ∀ k, lo < k → k < c → g k = g lo) :
    (∀ k, lo ≤ k → k < c → g k = g lo) ∧ (∀ k, c ≤ k → k ≤ hi → g k ≠ g lo) := by
  obtain ⟨hlc, hch, hne⟩ := hc
  refine ⟨fun k hk1 hk2 => ?_, fun k hk1 hk2 => ?_⟩
  · rcases Nat.eq_or_lt_of_le hk1 with rfl | hlt
    · rfl
    · exact hmin k hlt hk2
  · rcases hg with hm | ha
    · cases hlo : g lo <;> cases hgc : g c <;> simp_all
      · have := hm c k hk1 hgc; simp_all
      · have := hm lo c (by omega) hlo; simp_all
    · cases hlo : g lo <;> cases hgc : g c <;> simp_all
      · have := ha lo c (by omega) hgc; simp_all
      · cases hk : g k
        · rfl
        · have := ha c k hk1 hk; simp_all

/-- **Depth bound.**  If the outputs at the outcomes `lo, …, hi` are pairwise
    distinct, the extracted tree is no deeper than the step tree at each of them. -/
theorem extract_depth (f : ℕ → ℕ → ℕ → Bool) (hf : ∀ a b, MonoB (f a b) ∨ AntiB (f a b)) :
    ∀ (s : Step) (lo hi : ℕ), lo ≤ hi →
      (∀ k k', lo ≤ k → k ≤ hi → lo ≤ k' → k' ≤ hi →
        (s.eval (fun a b => f a b k)).1 = (s.eval (fun a b => f a b k')).1 → k = k') →
      ∀ k, lo ≤ k → k ≤ hi → depth (extract f s lo hi) k ≤ (s.eval (fun a b => f a b k)).2 := by
  intro s
  induction s with
  | out p r =>
    intro lo hi hlh hinj k hk1 hk2
    have : lo = hi := hinj lo hi le_rfl hlh hlh le_rfl (by simp [Step.eval])
    subst this
    simp only [extract, Step.eval]
    rw [unary, if_neg (lt_irrefl _)]; simp [depth]
  | ask a b y n ihy ihn =>
    intro lo hi hlh hinj k hk1 hk2
    -- outputs through a branch are the outputs of the branch
    have hy : ∀ k, f a b k = true →
        (Step.eval (fun a b => f a b k) (.ask a b y n)) =
          ((y.eval (fun a b => f a b k)).1, (y.eval (fun a b => f a b k)).2 + 1) := by
      intro k hk; simp [Step.eval, hk]
    have hn : ∀ k, f a b k = false →
        (Step.eval (fun a b => f a b k) (.ask a b y n)) =
          ((n.eval (fun a b => f a b k)).1, (n.eval (fun a b => f a b k)).2 + 1) := by
      intro k hk; simp [Step.eval, hk]
    -- injectivity restricted to a sub-interval on which the answer is constant
    have injY : ∀ l h, lo ≤ l → h ≤ hi → (∀ k, l ≤ k → k ≤ h → f a b k = true) →
        ∀ k k', l ≤ k → k ≤ h → l ≤ k' → k' ≤ h →
          (y.eval (fun a b => f a b k)).1 = (y.eval (fun a b => f a b k')).1 → k = k' := by
      intro l h hl hh hc k k' h1 h2 h3 h4 he
      apply hinj k k' (by omega) (by omega) (by omega) (by omega)
      rw [hy k (hc k h1 h2), hy k' (hc k' h3 h4)]; exact he
    have injN : ∀ l h, lo ≤ l → h ≤ hi → (∀ k, l ≤ k → k ≤ h → f a b k = false) →
        ∀ k k', l ≤ k → k ≤ h → l ≤ k' → k' ≤ h →
          (n.eval (fun a b => f a b k)).1 = (n.eval (fun a b => f a b k')).1 → k = k' := by
      intro l h hl hh hc k k' h1 h2 h3 h4 he
      apply hinj k k' (by omega) (by omega) (by omega) (by omega)
      rw [hn k (hc k h1 h2), hn k' (hc k' h3 h4)]; exact he
    simp only [extract]
    split
    · rename_i h
      have hc := Nat.find_spec h
      have hmin : ∀ k, lo < k → k < Nat.find h → f a b k = f a b lo := by
        intro k h1 h2
        have := Nat.find_min h h2
        by_contra hne; exact this ⟨h1, by omega, hne⟩
      obtain ⟨hbelow, habove⟩ := split_sides (f a b) (hf a b) lo (Nat.find h) hi hc hmin
      have hch := hc.2.1
      have hlc := hc.1
      generalize Nat.find h = c at hbelow habove hch hlc ⊢
      by_cases hlo : f a b lo = true
      · simp only [hlo, if_true, depth]
        by_cases hk : k ≤ c - 1
        · rw [if_pos hk]
          have hkt : f a b k = true := by rw [hbelow k hk1 (by omega), hlo]
          rw [hy k hkt]
          have := ihy lo (c - 1) (by omega)
            (injY lo (c - 1) le_rfl (by omega)
              (fun k h1 h2 => by rw [hbelow k h1 (by omega), hlo]))
            k hk1 hk
          simp only; omega
        · rw [if_neg hk]
          have hkf : f a b k = false := by
            have := habove k (by omega) hk2; rw [hlo] at this; simpa using this
          rw [hn k hkf]
          have := ihn c hi hch
            (injN c hi (by omega) le_rfl
              (fun k h1 h2 => by have := habove k h1 h2; rw [hlo] at this; simpa using this))
            k (by omega) hk2
          simp only; omega
      · have hlo' : f a b lo = false := by simpa using hlo
        simp only [hlo', Bool.false_eq_true, if_false, depth]
        by_cases hk : k ≤ c - 1
        · rw [if_pos hk]
          have hkf : f a b k = false := by rw [hbelow k hk1 (by omega), hlo']
          rw [hn k hkf]
          have := ihn lo (c - 1) (by omega)
            (injN lo (c - 1) le_rfl (by omega)
              (fun k h1 h2 => by rw [hbelow k h1 (by omega), hlo']))
            k hk1 hk
          simp only; omega
        · rw [if_neg hk]
          have hkt : f a b k = true := by
            have := habove k (by omega) hk2; rw [hlo'] at this; simpa using this
          rw [hy k hkt]
          have := ihy c hi hch
            (injY c hi (by omega) le_rfl
              (fun k h1 h2 => by have := habove k h1 h2; rw [hlo'] at this; simpa using this))
            k (by omega) hk2
          simp only; omega
    · rename_i h
      have hconst : ∀ k, lo ≤ k → k ≤ hi → f a b k = f a b lo := by
        intro k h1 h2
        rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
        · rfl
        · by_contra hne; exact h ⟨k, hlt, h2, hne⟩
      by_cases hlo0 : f a b lo = true
      · simp only [hlo0, if_true]
        have hkt : f a b k = true := by rw [hconst k hk1 hk2, hlo0]
        rw [hy k hkt]
        have := ihy lo hi hlh
          (injY lo hi le_rfl le_rfl (fun k h1 h2 => by rw [hconst k h1 h2, hlo0])) k hk1 hk2
        simp only; omega
      · have hlo : f a b lo = false := by simpa using hlo0
        simp only [hlo, Bool.false_eq_true, if_false]
        have hkf : f a b k = false := by rw [hconst k hk1 hk2, hlo]
        rw [hn k hkf]
        have := ihn lo hi hlh
          (injN lo hi le_rfl le_rfl (fun k h1 h2 => by rw [hconst k h1 h2, hlo])) k hk1 hk2
        simp only; omega

/-! ## The reconstruction stack of element indices -/

/-- Stack after reading the elements `0, …, j - 1 + |w|` (top first), elements
    named by their positions, starting from stack `s` before element `j`;
    `w` lists the pop counts. -/
def stkFrom : ℕ → List ℕ → List ℕ → List ℕ
  | _, s, [] => s
  | j, s, x :: w => stkFrom (j + 1) (j :: s.drop x) w

/-- Stack after reading the elements `0, …, |w|`, for the pop counts `w`. -/
def stk (w : List ℕ) : List ℕ := stkFrom 1 [0] w

theorem stkFrom_append_single :
    ∀ (p : List ℕ) (j : ℕ) (s : List ℕ) (k : ℕ),
      stkFrom j s (p ++ [k]) = (j + p.length) :: (stkFrom j s p).drop k := by
  intro p
  induction p with
  | nil => intro j s k; simp [stkFrom]
  | cons x p ih =>
    intro j s k
    simp only [List.cons_append, stkFrom, List.length_cons]
    rw [ih]; congr 1; omega

theorem stk_append_single (p : List ℕ) (k : ℕ) :
    stk (p ++ [k]) = (p.length + 1) :: (stk p).drop k := by
  simp only [stk, stkFrom_append_single]; congr 1; omega

/-- The stack is strictly decreasing from the top, hence has no repetitions. -/
theorem stkFrom_pairwise :
    ∀ (p : List ℕ) (j : ℕ) (s : List ℕ), s.Pairwise (· > ·) → (∀ y ∈ s, y < j) →
      (stkFrom j s p).Pairwise (· > ·) := by
  intro p
  induction p with
  | nil => intro j s hs _; exact hs
  | cons x p ih =>
    intro j s hs hlt
    simp only [stkFrom]
    apply ih
    · refine List.Pairwise.cons (fun y hy => hlt y (List.mem_of_mem_drop hy)) ?_
      exact hs.sublist (List.drop_sublist _ _)
    · intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · omega
      · have := hlt y (List.mem_of_mem_drop hy); omega

theorem stk_nodup (p : List ℕ) : (stk p).Nodup := by
  have h : (stk p).Pairwise (· > ·) :=
    stkFrom_pairwise p 1 [0] (by simp) (by simp)
  exact h.imp (fun h => Nat.ne_of_gt h)

theorem stkFrom_length :
    ∀ (p : List ℕ) (j : ℕ) (s : List ℕ), Valid s.length p →
      (stkFrom j s p).length = finalH s.length p := by
  intro p
  induction p with
  | nil => intro j s _; simp [stkFrom, finalH]
  | cons x p ih =>
    intro j s hv
    simp only [Valid] at hv
    have hl : (j :: s.drop x).length = s.length + 1 - x := by
      simp only [List.length_cons, List.length_drop]; omega
    simp only [stkFrom, finalH]
    rw [ih (j + 1) _ (by rw [hl]; exact hv.2), hl]

theorem stk_length (p : List ℕ) (hv : Valid 1 p) : (stk p).length = finalH 1 p :=
  stkFrom_length p 1 [0] hv

/-! ## The order oracle and its shape at one step -/

/-- "Is the label of element `a` smaller than that of element `b`?", answered
    from the pop counts `u` of the elements read so far.  For `a < b` the label
    of `a` is smaller iff `a` is no longer on the stack once `b` has been read. -/
def lt (u : List ℕ) (a b : ℕ) : Bool :=
  if a < b then decide (a ∉ stk (u.take b))
  else if b < a then decide (b ∈ stk (u.take a)) else false

theorem mem_drop_anti (L : List ℕ) (y k k' : ℕ) (hk : k ≤ k') (hy : y ∈ L.drop k') :
    y ∈ L.drop k := by
  have e : L.drop k' = (L.drop k).drop (k' - k) := by
    rw [List.drop_drop]; congr 1; omega
  rw [e] at hy; exact List.mem_of_mem_drop hy

theorem take_append_single (p : List ℕ) (k c : ℕ) :
    (p ++ [k]).take c = if c ≤ p.length then p.take c else p ++ [k] := by
  split
  · rw [List.take_append_of_le_length (by omega)]
  · rw [List.take_of_length_le (by simp; omega)]

/-- **Every question at a step is monotone or antitone in the pop count.** -/
theorem lt_mono_or_anti (p : List ℕ) (a b : ℕ) :
    MonoB (fun k => lt (p ++ [k]) a b) ∨ AntiB (fun k => lt (p ++ [k]) a b) := by
  unfold MonoB AntiB lt
  by_cases hab : a < b
  · by_cases hb : b ≤ p.length
    · left; intro k k' _ h; simpa [hab, take_append_single, hb] using h
    · left; intro k k' hkk h
      simp only [hab, if_true, take_append_single, hb, if_false, stk_append_single,
        decide_eq_true_eq, List.mem_cons, not_or] at h ⊢
      exact ⟨h.1, fun hy => h.2 (mem_drop_anti _ _ _ _ hkk hy)⟩
  · by_cases hba : b < a
    · by_cases ha : a ≤ p.length
      · left; intro k k' _ h; simpa [hab, hba, take_append_single, ha] using h
      · right; intro k k' hkk h
        simp only [hab, hba, if_false, if_true, take_append_single, ha, stk_append_single,
          decide_eq_true_eq, List.mem_cons] at h ⊢
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (mem_drop_anti _ _ _ _ hkk h)
    · left; intro k k' _ h; simp [hab, hba] at h

/-- The parent of the new element when it pops `k` nodes: the top as a left
    parent if `k = 0`, otherwise the `k`-th node from the top as a right parent. -/
def parentOf (p : List ℕ) (k : ℕ) : ℕ × Bool :=
  if k = 0 then ((stk p).headD 0, false) else ((stk p).getD (k - 1) 0, true)

/-- **Distinct pop counts give distinct parents.** -/
theorem parentOf_inj (p : List ℕ) (k k' : ℕ) (hk : k ≤ (stk p).length)
    (hk' : k' ≤ (stk p).length) (h : parentOf p k = parentOf p k') : k = k' := by
  unfold parentOf at h
  by_cases h0 : k = 0 <;> by_cases h0' : k' = 0
  · omega
  · simp [h0, h0'] at h
  · simp [h0, h0'] at h
  · simp only [h0, h0', if_false, Prod.mk.injEq, and_true] at h
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at h
    have := (List.Nodup.getElem_inj_iff (stk_nodup p)).1 h
    omega

/-! ## Programs and the reduction -/

/-- A one-pass program: at each step, from the pop counts read so far, a step
    tree that outputs the parent of the new element. -/
structure Prog where
  step : List ℕ → Step

/-- Questions asked by `P` on the rest `w` of a codeword after the prefix `hist`.
    The questions at a step are answered from the prefix including that step. -/
def progCost (P : Prog) : List ℕ → List ℕ → ℕ
  | _, [] => 0
  | hist, x :: w => ((P.step hist).eval (lt (hist ++ [x]))).2 + progCost P (hist ++ [x]) w

/-- `P` reconstructs every tree with `n` nodes: on every valid codeword, the
    output at each step is the parent of the new element. -/
def Correct (P : Prog) (n : ℕ) : Prop :=
  ∀ hist x rest, hist ++ x :: rest ∈ suffixes (n - 1) 1 →
    ((P.step hist).eval (lt (hist ++ [x]))).1 = parentOf hist x

/-- The ordered decision trees read off a program. -/
noncomputable def algOf (P : Prog) : Alg where
  tree hist m := extract (fun a b k => lt (hist ++ [k]) a b) (P.step hist) 0 m
  wf _ m := extract_wf _ _ 0 m (Nat.zero_le m)

theorem valid_append : ∀ (u v : List ℕ) (h : ℕ),
    Valid h (u ++ v) ↔ Valid h u ∧ Valid (finalH h u) v := by
  intro u
  induction u with
  | nil => intro v h; simp [Valid, finalH]
  | cons x u ih => intro v h; simp only [List.cons_append, Valid, finalH, ih]; tauto

theorem valid_replicate_zero (r h : ℕ) : Valid h (List.replicate r 0) := by
  induction r generalizing h with
  | zero => simp [Valid]
  | succ r ih => simp only [List.replicate_succ, Valid]; exact ⟨Nat.zero_le _, ih _⟩

/-- **The reduction.**  A correct program asks at least as many questions as the
    ordered decision trees extracted from it. -/
theorem progCost_ge (P : Prog) (n : ℕ) (hc : Correct P n) :
    ∀ (rest hist : List ℕ), hist ++ rest ∈ suffixes (n - 1) 1 →
      cost (algOf P) hist (stk hist).length rest ≤ progCost P hist rest := by
  intro rest
  induction rest with
  | nil => intro _ _; simp [cost, progCost]
  | cons x rest ih =>
    intro hist hmem
    have hmem' : (hist ++ [x]) ++ rest ∈ suffixes (n - 1) 1 := by simpa using hmem
    have hrec := ih (hist ++ [x]) hmem'
    obtain ⟨hlen, hv⟩ := (mem_suffixes _ _ _).1 hmem
    have hvh := (valid_append _ _ _).1 hv
    have hS : (stk hist).length = finalH 1 hist := stk_length hist hvh.1
    have hx : x ≤ (stk hist).length := by rw [hS]; exact (hvh.2).1
    have hS' : (stk (hist ++ [x])).length = (stk hist).length + 1 - x := by
      rw [stk_append_single]; simp only [List.length_cons, List.length_drop]; omega
    -- every pop count `k ≤ m` at this step extends to a valid input
    have hext : ∀ k, k ≤ (stk hist).length →
        hist ++ k :: List.replicate rest.length 0 ∈ suffixes (n - 1) 1 := by
      intro k hk
      rw [mem_suffixes]
      refine ⟨by simp at hlen ⊢; omega, ?_⟩
      rw [valid_append]
      refine ⟨hvh.1, ?_⟩
      simp only [Valid]
      exact ⟨by omega, valid_replicate_zero _ _⟩
    have hstep : depth ((algOf P).tree hist (stk hist).length) x ≤
        ((P.step hist).eval (lt (hist ++ [x]))).2 := by
      apply extract_depth (fun a b k => lt (hist ++ [k]) a b)
        (fun a b => lt_mono_or_anti hist a b) (P.step hist) 0 (stk hist).length
        (Nat.zero_le _) _ x (Nat.zero_le _) hx
      intro k k' _ hk _ hk' heq
      apply parentOf_inj hist k k' hk hk'
      rw [← hc hist k _ (hext k hk), ← hc hist k' _ (hext k' hk')]
      exact heq
    simp only [cost, progCost]
    rw [← hS']
    omega

/-- **Lower bound for programs.**  Every correct one-pass program asks at least
    `2n - 3` questions on some valid input (`n ≥ 2`). -/
theorem prog_lower (P : Prog) (n : ℕ) (hn : 2 ≤ n) (hc : Correct P n) :
    ∃ w ∈ suffixes (n - 1) 1, 2 * n - 3 ≤ progCost P [] w := by
  refine ⟨adv n, adv_mem n hn, ?_⟩
  have h1 := onePass_lower (algOf P) n hn
  have h2 := progCost_ge P n hc (adv n) [] (by simpa using adv_mem n hn)
  have e : (stk []).length = 1 := rfl
  rw [e] at h2
  omega

/-! ## M as a program, and the matching upper bound -/

theorem stkFrom_lt :
    ∀ (p : List ℕ) (j : ℕ) (s : List ℕ), (∀ y ∈ s, y < j) → ∀ y ∈ stkFrom j s p, y < j + p.length := by
  intro p
  induction p with
  | nil => intro j s hs y hy; simpa using hs y hy
  | cons x p ih =>
    intro j s hs y hy
    simp only [stkFrom] at hy
    have := ih (j + 1) (j :: s.drop x) (by
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · omega
      · have := hs z (List.mem_of_mem_drop hz); omega) y hy
    simp only [List.length_cons]; omega

theorem stk_lt (p : List ℕ) : ∀ y ∈ stk p, y < p.length + 1 := by
  intro y hy
  have := stkFrom_lt p 1 [0] (by simp) y hy
  omega

/-- In a list without repetitions, the `j`-th entry survives dropping `k`
    entries iff `k ≤ j`. -/
theorem getElem_mem_drop_iff (L : List ℕ) (hL : L.Nodup) (j k : ℕ) (hj : j < L.length) :
    L[j] ∈ L.drop k ↔ k ≤ j := by
  constructor
  · intro h
    by_contra hkj
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 h
    rw [List.getElem_drop] at he
    have := (List.Nodup.getElem_inj_iff hL).1 he
    omega
  · intro hkj
    have hlt : j - k < (L.drop k).length := by simp; omega
    have : (L.drop k)[j - k] = L[j] := by
      rw [List.getElem_drop]; congr 1; omega
    rw [← this]; exact List.getElem_mem hlt

/-- The answer to "is the `j`-th stack node smaller than the new element?" is
    "is `j < k`?". -/
theorem lt_stack (p : List ℕ) (k j : ℕ) (hj : j < (stk p).length) :
    lt (p ++ [k]) ((stk p)[j]) (p.length + 1) = decide (j < k) := by
  have hlt : (stk p)[j] < p.length + 1 := stk_lt p _ (List.getElem_mem hj)
  unfold lt
  rw [if_pos hlt, take_append_single, if_neg (by omega), stk_append_single]
  have hm := getElem_mem_drop_iff (stk p) (stk_nodup p) j k hj
  simp only [List.mem_cons, not_or, decide_eq_decide]
  constructor
  · intro ⟨_, h⟩; by_contra hc; exact h (hm.2 (by omega))
  · intro h; exact ⟨by omega, fun h' => by have := hm.1 h'; omega⟩

/-- The pop chain of M: after popping `prev`, compare the new element `i` with
    the next nodes; at the bottom the sentinel comparison is skipped. -/
def popChain (i prev : ℕ) : List ℕ → Step
  | [] => .out prev true
  | r :: rest => .ask r i (popChain i r rest) (.out prev true)

/-- M's step: compare with the top; on "smaller" go down the pop chain. -/
def mStep (i : ℕ) : List ℕ → Step
  | [] => .out 0 false
  | t :: rest => .ask t i (popChain i t rest) (.out t false)

/-- Mäkinen's algorithm as a one-pass program. -/
def progM : Prog where
  step hist := mStep (hist.length + 1) (stk hist)

theorem popChain_eval (ans : ℕ → ℕ → Bool) (i : ℕ) :
    ∀ (L : List ℕ) (prev d k : ℕ), d ≤ k → k ≤ d + L.length →
      (∀ j (hj : j < L.length), ans L[j] i = decide (d + j < k)) →
      (popChain i prev L).eval ans =
        ((if k = d then prev else L.getD (k - d - 1) 0, true),
          (k - d) + if k < d + L.length then 1 else 0) := by
  intro L
  induction L with
  | nil =>
    intro prev d k h1 h2 _
    have : k = d := by simp at h2; omega
    subst this; simp [popChain, Step.eval]
  | cons r rest ih =>
    intro prev d k h1 h2 hans
    have h0 := hans 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h0
    simp only [popChain, Step.eval, h0]
    by_cases hdk : d < k
    · simp only [hdk, decide_true, if_true]
      have := ih r (d + 1) k (by omega) (by simp only [List.length_cons] at h2; omega)
        (fun j hj => by
          have := hans (j + 1) (by simp only [List.length_cons]; omega)
          simp only [List.getElem_cons_succ] at this
          rw [this, show d + (j + 1) = d + 1 + j by omega])
      rw [this]
      simp only [List.length_cons, Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · by_cases hk1 : k = d + 1
        · simp [hk1]
        · rw [if_neg hk1, if_neg (by omega)]
          generalize hj : k - (d + 1) - 1 = j'
          have e : k - d - 1 = j' + 1 := by omega
          rw [e]; simp
      · split <;> split <;> omega
    · have : k = d := by omega
      subst this
      simp [List.length_cons]

theorem mStep_eval (p : List ℕ) (k : ℕ) (hk : k ≤ (stk p).length) :
    (mStep (p.length + 1) (stk p)).eval (lt (p ++ [k])) =
      (parentOf p k, if k < (stk p).length then k + 1 else k) := by
  have hpos : 1 ≤ (stk p).length := by
    have := stk_nodup p
    -- the stack always holds the last element read
    cases p using List.reverseRecOn with
    | nil => simp [stk, stkFrom]
    | append_singleton q x _ => rw [stk_append_single]; simp
  have hans : ∀ j (hj : j < (stk p).length),
      lt (p ++ [k]) ((stk p)[j]) (p.length + 1) = decide (j < k) := fun j hj => lt_stack p k j hj
  generalize hS : stk p = S at hk hpos hans
  cases S with
  | nil => simp at hpos
  | cons t rest =>
    have h0 := hans 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    simp only [mStep, Step.eval, h0]
    unfold parentOf
    rw [hS]
    by_cases hk0 : k = 0
    · subst hk0; simp
    · simp only [show 0 < k by omega, decide_true, if_true, hk0, if_false]
      rw [popChain_eval (lt (p ++ [k])) (p.length + 1) rest t 1 k (by omega)
        (by simp only [List.length_cons] at hk; omega)
        (fun j hj => by
          have := hans (j + 1) (by simp only [List.length_cons]; omega)
          simp only [List.getElem_cons_succ] at this
          rw [this, show j + 1 = 1 + j by omega])]
      simp only [List.length_cons, Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · by_cases hk1 : k = 1
        · simp [hk1]
        · rw [if_neg hk1]
          generalize hj : k - 1 - 1 = j'
          have e : k - 1 = j' + 1 := by omega
          rw [e]; simp
      · split <;> split <;> omega

/-- **M is correct.** -/
theorem progM_correct (n : ℕ) : Correct progM n := by
  intro hist x rest hmem
  obtain ⟨_, hv⟩ := (mem_suffixes _ _ _).1 hmem
  have hvh := (valid_append _ _ _).1 hv
  have hx : x ≤ (stk hist).length := by rw [stk_length hist hvh.1]; exact hvh.2.1
  simp only [progM]
  rw [mStep_eval hist x hx]

/-- M asks exactly what its extracted ordered tree `algM` costs. -/
theorem progCost_M :
    ∀ (rest hist : List ℕ), Valid 1 (hist ++ rest) →
      progCost progM hist rest = cost algM hist (stk hist).length rest := by
  intro rest
  induction rest with
  | nil => intro _ _; simp [cost, progCost]
  | cons x rest ih =>
    intro hist hv
    have hvh := (valid_append _ _ _).1 hv
    have hx : x ≤ (stk hist).length := by rw [stk_length hist hvh.1]; exact hvh.2.1
    have hS' : (stk (hist ++ [x])).length = (stk hist).length + 1 - x := by
      rw [stk_append_single]; simp only [List.length_cons, List.length_drop]; omega
    simp only [progCost, cost]
    rw [ih (hist ++ [x]) (by simpa using hv), hS']
    congr 1
    simp only [progM]
    rw [mStep_eval hist x hx]
    simp only [algM]
    rw [depth_unary 0 _ x (Nat.zero_le _) hx]
    split <;> omega

/-- **Worst-case optimality among one-pass programs.**  For `n ≥ 2`: every
    correct one-pass program asks at least `2n - 3` questions on some valid
    input, M is correct, and M asks at most `2n - 3` on every valid input. -/
theorem onePass_programs (n : ℕ) (hn : 2 ≤ n) :
    (∀ P : Prog, Correct P n → ∃ w ∈ suffixes (n - 1) 1, 2 * n - 3 ≤ progCost P [] w) ∧
    Correct progM n ∧
    (∀ w ∈ suffixes (n - 1) 1, progCost progM [] w ≤ 2 * n - 3) := by
  refine ⟨fun P hc => prog_lower P n hn hc, progM_correct n, fun w hw => ?_⟩
  have hv := ((mem_suffixes _ _ _).1 hw).2
  rw [progCost_M w [] (by simpa using hv)]
  exact costM_le n hn w hw

end MakinenAnalysis.OnePass
