import Mathlib
import MakinenAnalysis.PopClosed
import MakinenAnalysis.LeafCount
import MakinenAnalysis.BallotCount
import MakinenAnalysis.DegreeWords

/-!
# The pop-codeword ↔ dominating-degree-word bridge

This file proves the last combinatorial gap of the Mäkinen formalisation, the
**encoding bridge**

  `U (n-1) 1 k = ((degWords n k).filter Dominating).card`   (`U_eq_dominating`)

relating the two encodings of an `n`-node binary tree with `k` two-children
nodes: the Mäkinen pop-codeword (`suffixes (n-1) 1`, POP side) and the preorder
degree word (`degWords n k` with `Dominating`, DEGREE side).  Combined with
`U_mul_closed_of_bridge` of `PopClosed`, this closes `U_mul_closed`.

## Strategy: a binary-tree hub

The common object is Mathlib's `BinaryTree Unit` (`nil` = external/empty,
`node () l r` = internal node).  `treesOfNumNodesEq n` is the finset of trees
with `n` internal nodes, of cardinality `catalan n`
(`treesOfNumNodesEq_card_eq_catalan`).  Two maps:

* `toDeg  : T → List Deg` — the preorder degree word;
* `toPop  : T → List ℕ`  — the Mäkinen pop-codeword (`enc`, ported verbatim
  from the Rocq `Codewords.v` structural encoder).

The DEGREE leg is a **full bijection** `{trees, numNodes=n, twoNodes=k} ≃
(degWords n k).filter Dominating` (`toDeg` injective by a right-fold parser,
surjective by the Łukasiewicz split induction `exists_toDeg`).

The POP leg uses a **counting squeeze**: `toPop` is injective (encode round-trip
of the fuelled decoder `dec`) and sound into `suffixes (n-1) 1` with
`P2 = twoNodes`; since the tree total and the pop total both equal `catalan n`,
the fibrewise inequality `#trees_k ≤ #pop_k` is forced to equality.

Chaining the two legs gives `#pop_k = #trees_k = #domDeg_k`, i.e. the bridge.
-/

namespace MakinenAnalysis

open Finset

/-- The tree hub: `BinaryTree Unit`, `nil` = external, `node () l r` = internal. -/
abbrev T := BinaryTree Unit

/-- Whether a tree is an internal node (non-empty). -/
def isNode : T → Bool
  | .nil => false
  | .node _ _ _ => true

/-- Number of internal nodes both of whose children are internal
    (the "two-children" nodes; matches the `Deg.two` count). -/
def twoNodes : T → ℕ
  | .nil => 0
  | .node _ l r => (if isNode l && isNode r then 1 else 0) + twoNodes l + twoNodes r

/-- Preorder degree letter of an internal node with children `l`, `r`. -/
def rootLetter (l r : T) : Deg :=
  match isNode l, isNode r with
  | false, false => .leaf
  | true, false => .oneL
  | false, true => .oneR
  | true, true => .two

/-- **Preorder degree word** of a tree. -/
def toDeg : T → List Deg
  | .nil => []
  | .node _ l r => rootLetter l r :: (toDeg l ++ toDeg r)

/-- **Mäkinen encoder** (`enc t = (codeword, remaining)`), ported from the Rocq
    `Codewords.v` structural encoder. -/
def enc : T → List ℕ × ℕ
  | .nil => ([], 0)
  | .node _ L R =>
      let pL := match L with | .nil => (([] : List ℕ), 0) | _ => (0 :: (enc L).1, (enc L).2)
      match R with
      | .nil => (pL.1, pL.2 + 1)
      | _ => (pL.1 ++ (pL.2 + 1) :: (enc R).1, (enc R).2)

/-- The **pop-codeword** of a tree. -/
def toPop (t : T) : List ℕ := (enc t).1

/-- The `remaining` bookkeeping value of the encoder. -/
def rem (t : T) : ℕ := (enc t).2

/-! ### Elementary `append` splittings -/

lemma finalH_append (u v : List ℕ) (h : ℕ) :
    finalH h (u ++ v) = finalH (finalH h u) v := by
  induction u generalizing h with
  | nil => rfl
  | cons x u ih => simp only [List.cons_append, finalH]; rw [ih]

lemma P2_append (u v : List ℕ) : P2 (u ++ v) = P2 u + P2 v := by
  induction u with
  | nil => simp [P2]
  | cons x u ih => simp only [List.cons_append, P2, ih]; ring

lemma lukSum_append (u v : List Deg) : lukSum (u ++ v) = lukSum u + lukSum v := by
  simp only [lukSum, List.map_append, List.sum_append]

@[simp] lemma lukSum_nil : lukSum [] = 0 := rfl

lemma lukSum_singleton (d : Deg) : lukSum [d] = d.step := by
  simp [lukSum]

/-! ### `isNode` and `rem` positivity -/

@[simp] lemma toDeg_nil : toDeg (.nil : T) = [] := rfl

@[simp] lemma isNode_nil : isNode .nil = false := rfl
@[simp] lemma isNode_node (l r : T) : isNode (.node () l r) = true := rfl

lemma isNode_eq_true {t : T} : isNode t = true ↔ t ≠ .nil := by
  cases t <;> simp [isNode]

/-! ### Equational rewrite lemmas for the encoder (by nil-status of children) -/

@[simp] lemma toPop_nil : toPop .nil = [] := rfl
@[simp] lemma rem_nil : rem .nil = 0 := rfl
@[simp] lemma toPop_ll {v : Unit} : toPop (.node v .nil .nil) = [] := rfl
@[simp] lemma rem_ll {v : Unit} : rem (.node v .nil .nil) = 1 := rfl

lemma toPop_lR {v : Unit} {R : T} (hR : R ≠ .nil) : toPop (.node v .nil R) = 1 :: toPop R := by
  cases R with | nil => exact absurd rfl hR | node _ a b => rfl
lemma rem_lR {v : Unit} {R : T} (hR : R ≠ .nil) : rem (.node v .nil R) = rem R := by
  cases R with | nil => exact absurd rfl hR | node _ a b => rfl
lemma toPop_Ln {v : Unit} {L : T} (hL : L ≠ .nil) : toPop (.node v L .nil) = 0 :: toPop L := by
  cases L with | nil => exact absurd rfl hL | node _ a b => rfl
lemma rem_Ln {v : Unit} {L : T} (hL : L ≠ .nil) : rem (.node v L .nil) = rem L + 1 := by
  cases L with | nil => exact absurd rfl hL | node _ a b => rfl
lemma toPop_LR {v : Unit} {L R : T} (hL : L ≠ .nil) (hR : R ≠ .nil) :
    toPop (.node v L R) = (0 :: toPop L) ++ (rem L + 1) :: toPop R := by
  cases L with
  | nil => exact absurd rfl hL
  | node _ a b => cases R with | nil => exact absurd rfl hR | node _ c d => rfl
lemma rem_Rnn {v : Unit} {L R : T} (hR : R ≠ .nil) : rem (.node v L R) = rem R := by
  cases R with | nil => exact absurd rfl hR | node _ c d => rfl

lemma rem_pos : ∀ t : T, t ≠ .nil → 1 ≤ rem t := by
  intro t
  induction t with
  | nil => intro h; exact absurd rfl h
  | node _ L R ihL ihR =>
    intro _
    by_cases hR : R = .nil
    · subst hR
      by_cases hL : L = .nil
      · subst hL; rw [rem_ll]
      · rw [rem_Ln hL]; omega
    · rw [rem_Rnn hR]; exact ihR hR

/-! ### DEGREE-side soundness: counts, length, Łukasiewicz sum, dominance -/

lemma toDeg_length : ∀ t : T, (toDeg t).length = BinaryTree.numNodes t := by
  intro t
  induction t with
  | nil => rfl
  | node _ L R ihL ihR =>
    simp only [toDeg, List.length_cons, List.length_append, ihL, ihR, BinaryTree.numNodes]

lemma rootLetter_two_iff (L R : T) : rootLetter L R = .two ↔ (isNode L && isNode R) = true := by
  cases hL : isNode L <;> cases hR : isNode R <;> simp [rootLetter, hL, hR]

lemma rootLetter_leaf_iff (L R : T) :
    rootLetter L R = .leaf ↔ (isNode L || isNode R) = false := by
  cases hL : isNode L <;> cases hR : isNode R <;> simp [rootLetter, hL, hR]

lemma toDeg_count_two : ∀ t : T, (toDeg t).count .two = twoNodes t := by
  intro t
  induction t with
  | nil => rfl
  | node _ L R ihL ihR =>
    simp only [toDeg, List.count_cons, List.count_append, ihL, ihR, twoNodes]
    cases hL : isNode L <;> cases hR : isNode R <;>
      (simp [rootLetter, hL, hR]; try ring)

@[simp] lemma isNode_eq_false {t : T} : isNode t = false ↔ t = .nil := by
  cases t <;> simp [isNode]

lemma lukSum_cons (d : Deg) (w : List Deg) : lukSum (d :: w) = d.step + lukSum w := by
  simp [lukSum]

/-- The Łukasiewicz sum of a preorder degree word: `0` for the empty tree,
    `-1` for any non-empty tree. -/
lemma lukSum_toDeg : ∀ t : T, lukSum (toDeg t) = if t = .nil then 0 else -1 := by
  intro t
  induction t with
  | nil => rfl
  | node _ L R ihL ihR =>
    rw [if_neg (by simp), toDeg, lukSum_cons, lukSum_append, ihL, ihR]
    rcases L with _ | ⟨_, LL, LR⟩ <;> rcases R with _ | ⟨_, RL, RR⟩ <;>
      simp [rootLetter, isNode, Deg.step]

lemma toDeg_count_leaf (t : T) (h : t ≠ .nil) : (toDeg t).count .leaf = twoNodes t + 1 := by
  have hl := lukSum_toDeg t
  rw [if_neg h, lukSum_eq_count, toDeg_count_two] at hl
  have : ((toDeg t).count Deg.leaf : ℤ) = (twoNodes t : ℤ) + 1 := by linarith
  exact_mod_cast this

/-! ### DEGREE-side: prefix nonnegativity (dominance) -/

lemma rootLetter_step_two {L R : T} (hL : L ≠ .nil) (hR : R ≠ .nil) :
    (rootLetter L R).step = 1 := by
  cases L with
  | nil => exact absurd rfl hL
  | node _ a b => cases R with | nil => exact absurd rfl hR | node _ c d => rfl

lemma rootLetter_step_left_nonneg {L R : T} (hL : L ≠ .nil) :
    0 ≤ (rootLetter L R).step := by
  by_cases hR : R = .nil
  · have h0 : (rootLetter L R).step = 0 := by
      cases L with | nil => exact absurd rfl hL | node _ a b => subst hR; rfl
    omega
  · have h1 := rootLetter_step_two hL hR; omega

lemma rootLetter_step_right_zero {L R : T} (hL : L = .nil) (hR : R ≠ .nil) :
    (rootLetter L R).step = 0 := by
  subst hL
  cases R with | nil => exact absurd rfl hR | node _ c d => rfl

/-- Every proper prefix of a preorder degree word has nonnegative Łukasiewicz
    sum: `0 ≤ lukSum ((toDeg t).take i)` for `i < numNodes t`. -/
lemma toDeg_prefix_nonneg : ∀ (t : T) (i : ℕ),
    i < BinaryTree.numNodes t → 0 ≤ lukSum ((toDeg t).take i) := by
  intro t
  induction t with
  | nil => intro i hi; simp [BinaryTree.numNodes] at hi
  | node _ L R ihL ihR =>
    intro i hi
    cases i with
    | zero => simp
    | succ i' =>
      -- toDeg (node L R) = c :: (toDeg L ++ toDeg R)
      have hlenL : (toDeg L).length = BinaryTree.numNodes L := toDeg_length L
      have hnum : BinaryTree.numNodes (BinaryTree.node () L R)
          = BinaryTree.numNodes L + BinaryTree.numNodes R + 1 := by
        simp [BinaryTree.numNodes]
      rw [hnum] at hi
      have hstep : lukSum ((toDeg (BinaryTree.node () L R)).take (i' + 1))
          = (rootLetter L R).step + lukSum ((toDeg L ++ toDeg R).take i') := by
        rw [toDeg]
        rw [show (rootLetter L R :: (toDeg L ++ toDeg R)).take (i' + 1)
              = rootLetter L R :: (toDeg L ++ toDeg R).take i' from rfl]
        rw [lukSum_cons]
      rw [hstep]
      -- case on where i' falls relative to |toDeg L|
      by_cases hiL : i' ≤ (toDeg L).length
      · rw [List.take_append_of_le_length hiL]
        rcases lt_or_eq_of_le hiL with hlt | heq
        · -- i' < |toDeg L| : strictly inside the left subtree
          have hL0 : 0 ≤ lukSum ((toDeg L).take i') :=
            ihL i' (by rw [hlenL] at hlt; exact hlt)
          -- the root step is ≥ -1, and equals -1 only for a leaf (both children nil),
          -- but then |toDeg L| = 0, contradicting i' < |toDeg L|.
          have hLne : L ≠ .nil := by
            rintro rfl; simp [toDeg] at hlt
          have hs0 : 0 ≤ (rootLetter L R).step := rootLetter_step_left_nonneg hLne
          linarith
        · -- i' = |toDeg L| : the whole left subtree; its sum is -1 or 0
          subst heq
          rw [List.take_length]
          -- R must be non-empty (else `i` would exceed `numNodes`)
          have hRnn : R ≠ .nil := by
            rintro rfl
            simp only [BinaryTree.numNodes] at hi
            rw [hlenL] at hi; omega
          have hL := lukSum_toDeg L
          by_cases hLnil : L = .nil
          · rw [if_pos hLnil] at hL
            rw [hL, rootLetter_step_right_zero hLnil hRnn]; norm_num
          · rw [if_neg hLnil] at hL
            rw [hL, rootLetter_step_two hLnil hRnn]; norm_num
      · -- i' > |toDeg L| : we are inside the right subtree (L may be empty)
        rw [not_le] at hiL
        rw [List.take_append, lukSum_append]
        rw [show (toDeg L).take i' = toDeg L from
          List.take_of_length_le (le_of_lt hiL)]
        -- R must be non-empty here
        have hRnil : R ≠ .nil := by
          rintro rfl
          simp only [BinaryTree.numNodes] at hi
          rw [hlenL] at hiL
          omega
        -- the root step plus the full left-subtree sum cancels to `0`
        have hkey : (rootLetter L R).step + lukSum (toDeg L) = 0 := by
          have hL := lukSum_toDeg L
          by_cases hLnil : L = .nil
          · rw [if_pos hLnil] at hL
            rw [hL, rootLetter_step_right_zero hLnil hRnil]; ring
          · rw [if_neg hLnil] at hL
            rw [hL, rootLetter_step_two (by simpa using hLnil) hRnil]; ring
        have hidx : i' - (toDeg L).length < BinaryTree.numNodes R := by
          rw [hlenL] at hiL ⊢; omega
        have hR0 := ihR (i' - (toDeg L).length) hidx
        -- goal: 0 ≤ step + (lukSum (toDeg L) + lukSum (R-prefix))
        linarith

/-- The preorder degree word of any tree is dominating. -/
lemma dominating_toDeg (t : T) : Dominating (toDeg t) := by
  intro j hj
  rw [toDeg_length] at hj
  have := toDeg_prefix_nonneg t (j + 1) hj
  linarith

/-- Soundness: the degree word of an `n`-node tree with `k` two-nodes is a
    dominating degree word in `degWords n k`. -/
lemma toDeg_mem_degWords (t : T) (h : t ≠ .nil) :
    toDeg t ∈ degWords (BinaryTree.numNodes t) (twoNodes t) := by
  rw [mem_degWords]
  exact ⟨toDeg_length t, toDeg_count_two t, toDeg_count_leaf t h⟩

/-! ### DEGREE-side: injectivity of `toDeg` via a right-fold parser -/

/-- Right-fold reduction step: rebuild trees from a degree word read right to
    left.  Underflowing letters map to `[]` (never reached on well-formed
    words). -/
def dstep : Deg → List T → List T
  | .leaf, s => BinaryTree.node () .nil .nil :: s
  | .oneL, (L :: s) => BinaryTree.node () L .nil :: s
  | .oneL, [] => []
  | .oneR, (R :: s) => BinaryTree.node () .nil R :: s
  | .oneR, [] => []
  | .two, (L :: R :: s) => BinaryTree.node () L R :: s
  | .two, _ => []

lemma rootLetter_oneR {R : T} (hR : R ≠ .nil) : rootLetter .nil R = .oneR := by
  cases R with | nil => exact absurd rfl hR | node _ a b => rfl
lemma rootLetter_oneL {L : T} (hL : L ≠ .nil) : rootLetter L .nil = .oneL := by
  cases L with | nil => exact absurd rfl hL | node _ a b => rfl
lemma rootLetter_two' {L R : T} (hL : L ≠ .nil) (hR : R ≠ .nil) : rootLetter L R = .two := by
  cases L with
  | nil => exact absurd rfl hL
  | node _ a b => cases R with | nil => exact absurd rfl hR | node _ c d => rfl

/-- The right fold parses `toDeg t` back to `t` (pushed onto the stack). -/
lemma foldr_toDeg : ∀ (t : T) (s : List T),
    List.foldr dstep s (toDeg t) = (if t = .nil then s else t :: s) := by
  intro t
  induction t with
  | nil => intro s; rfl
  | node _ L R ihL ihR =>
    intro s
    rw [if_neg (by simp), toDeg, List.foldr_cons, List.foldr_append, ihR]
    by_cases hL : L = .nil <;> by_cases hR : R = .nil
    · subst hL; subst hR; rfl
    · subst hL
      rw [if_neg hR, ihL, if_pos rfl, rootLetter_oneR hR]; rfl
    · subst hR
      rw [if_pos rfl, ihL, if_neg hL, rootLetter_oneL hL]; rfl
    · rw [if_neg hR, ihL, if_neg hL, rootLetter_two' hL hR]; rfl

/-- `toDeg` is injective on non-empty trees. -/
lemma toDeg_inj {t1 t2 : T} (h1 : t1 ≠ .nil) (h2 : t2 ≠ .nil)
    (heq : toDeg t1 = toDeg t2) : t1 = t2 := by
  have e1 := foldr_toDeg t1 []
  have e2 := foldr_toDeg t2 []
  rw [if_neg h1] at e1
  rw [if_neg h2] at e2
  have hcons : (t1 :: [] : List T) = t2 :: [] := by rw [← e1, ← e2, heq]
  simpa using hcons

/-! ### DEGREE-side: surjectivity of `toDeg` onto dominating degree words -/

lemma Deg_step_ge (d : Deg) : (-1 : ℤ) ≤ d.step := by cases d <;> simp [Deg.step]

lemma lukSum_take_one_ge (l : List Deg) : (-1 : ℤ) ≤ lukSum (l.take 1) := by
  cases l with
  | nil => simp
  | cons x xs => rw [show (x :: xs).take 1 = [x] from rfl, lukSum_singleton]; exact Deg_step_ge x

lemma lukSum_take_succ (l : List Deg) (i : ℕ) :
    lukSum (l.take (i + 1)) = lukSum (l.take i) + lukSum ((l.drop i).take 1) := by
  rw [List.take_add, lukSum_append]

/-- **Surjectivity core** (Łukasiewicz decomposition): a degree word whose total
    sum is `-1` and all of whose proper prefixes have sum `≥ 0` is `toDeg t` for
    a (unique) tree `t`. -/
lemma exists_toDeg : ∀ (N : ℕ) (w : List Deg), w.length ≤ N → lukSum w = -1 →
    (∀ j, j + 1 < w.length → 0 ≤ lukSum (w.take (j + 1))) → ∃ t : T, toDeg t = w := by
  intro N
  induction N with
  | zero =>
    intro w hlen hsum _
    have : w = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
    subst this; simp at hsum
  | succ N ihN =>
    intro w hlen hsum hdom
    cases w with
    | nil => simp at hsum
    | cons d rest =>
      rw [lukSum_cons] at hsum
      -- length bound for `rest`
      have hrestN : rest.length ≤ N := by
        simp only [List.length_cons] at hlen; omega
      cases d with
      | leaf =>
        -- forced: rest is empty
        have hrnil : rest = [] := by
          by_contra hne
          have hpos : 0 < rest.length := List.length_pos_of_ne_nil hne
          have := hdom 0 (by simp only [List.length_cons]; omega)
          rw [show (Deg.leaf :: rest).take (0 + 1) = [Deg.leaf] from rfl, lukSum_singleton] at this
          simp [Deg.step] at this
        subst hrnil
        exact ⟨BinaryTree.node () .nil .nil, rfl⟩
      | oneL =>
        -- rest is a code; `t = node L nil`
        have hrsum : lukSum rest = -1 := by simp [Deg.step] at hsum; linarith
        have hrdom : ∀ j, j + 1 < rest.length → 0 ≤ lukSum (rest.take (j + 1)) := by
          intro j hj
          have := hdom (j + 1) (by simp only [List.length_cons]; omega)
          rw [show (Deg.oneL :: rest).take (j + 1 + 1) = Deg.oneL :: rest.take (j + 1) from rfl,
            lukSum_cons] at this
          simpa [Deg.step] using this
        obtain ⟨L, hL⟩ := ihN rest hrestN hrsum hrdom
        have hLne : L ≠ .nil := by
          rintro rfl
          rw [toDeg] at hL; rw [← hL] at hrsum; simp at hrsum
        refine ⟨BinaryTree.node () L .nil, ?_⟩
        rw [toDeg, rootLetter_oneL hLne, hL]; simp
      | oneR =>
        have hrsum : lukSum rest = -1 := by simp [Deg.step] at hsum; linarith
        have hrdom : ∀ j, j + 1 < rest.length → 0 ≤ lukSum (rest.take (j + 1)) := by
          intro j hj
          have := hdom (j + 1) (by simp only [List.length_cons]; omega)
          rw [show (Deg.oneR :: rest).take (j + 1 + 1) = Deg.oneR :: rest.take (j + 1) from rfl,
            lukSum_cons] at this
          simpa [Deg.step] using this
        obtain ⟨R, hR⟩ := ihN rest hrestN hrsum hrdom
        have hRne : R ≠ .nil := by
          rintro rfl
          rw [toDeg] at hR; rw [← hR] at hrsum; simp at hrsum
        refine ⟨BinaryTree.node () .nil R, ?_⟩
        rw [toDeg, rootLetter_oneR hRne, hR]; simp
      | two =>
        -- lukSum rest = -2 ; split at the first prefix reaching -1
        have hrsum : lukSum rest = -2 := by simp [Deg.step] at hsum; linarith
        -- dominance transported to `rest` (proper prefixes ≥ -1)
        have hdomR : ∀ i, i < rest.length → -1 ≤ lukSum (rest.take i) := by
          intro i hi
          rcases Nat.eq_zero_or_pos i with hi0 | hipos
          · subst hi0; simp
          · obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hipos.ne'
            have := hdom (i' + 1) (by simp only [List.length_cons]; omega)
            rw [show (Deg.two :: rest).take (i' + 1 + 1) = Deg.two :: rest.take (i' + 1) from rfl,
              lukSum_cons] at this
            simp only [Deg.step] at this; linarith
        -- the split index
        have hex : ∃ i, lukSum (rest.take i) ≤ -1 :=
          ⟨rest.length, by rw [List.take_length, hrsum]; norm_num⟩
        obtain ⟨m, hm_def⟩ : ∃ m, m = Nat.find hex := ⟨Nat.find hex, rfl⟩
        have hm_spec : lukSum (rest.take m) ≤ -1 := hm_def ▸ Nat.find_spec hex
        have hm_min : ∀ i, i < m → ¬ lukSum (rest.take i) ≤ -1 := by
          intro i hi; rw [hm_def] at hi; exact Nat.find_min hex hi
        have hm_le : m ≤ rest.length :=
          hm_def ▸ Nat.find_le (by rw [List.take_length, hrsum]; norm_num)
        have hm_pos : 0 < m := by
          rcases Nat.eq_zero_or_pos m with h0 | h
          · rw [h0, List.take_zero] at hm_spec; simp at hm_spec
          · exact h
        -- the prefix `rest.take m` has sum exactly -1
        have hm_val : lukSum (rest.take m) = -1 := by
          have hm1 : m - 1 + 1 = m := Nat.succ_pred_eq_of_pos hm_pos
          have hprev : (0 : ℤ) ≤ lukSum (rest.take (m - 1)) := by
            have := hm_min (m - 1) (by omega); omega
          have hstep := lukSum_take_succ rest (m - 1)
          rw [hm1] at hstep
          have hone := lukSum_take_one_ge (rest.drop (m - 1))
          rw [hstep] at hm_spec ⊢
          linarith
        -- `m < rest.length`
        have hm_lt : m < rest.length := by
          rcases lt_or_eq_of_le hm_le with h | h
          · exact h
          · exfalso; rw [h, List.take_length, hrsum] at hm_val; norm_num at hm_val
        -- the two pieces
        have hsplit : rest.take m ++ rest.drop m = rest := List.take_append_drop m rest
        have hc2sum : lukSum (rest.drop m) = -1 := by
          have : lukSum (rest.take m) + lukSum (rest.drop m) = lukSum rest := by
            rw [← lukSum_append, hsplit]
          rw [hm_val, hrsum] at this; linarith
        -- codes for the two pieces
        have hc1dom : ∀ j, j + 1 < (rest.take m).length → 0 ≤ lukSum ((rest.take m).take (j + 1)) := by
          intro j hj
          rw [List.length_take, Nat.min_eq_left hm_le] at hj
          rw [List.take_take, Nat.min_eq_left (by omega)]
          have := hm_min (j + 1) (by omega)
          omega
        have hc1len : (rest.take m).length ≤ N := by
          rw [List.length_take, Nat.min_eq_left hm_le]; omega
        obtain ⟨L, hL⟩ := ihN (rest.take m) hc1len hm_val hc1dom
        have hc2dom : ∀ j, j + 1 < (rest.drop m).length → 0 ≤ lukSum ((rest.drop m).take (j + 1)) := by
          intro j hj
          rw [List.length_drop] at hj
          -- lukSum ((rest.drop m).take (j+1)) = lukSum (rest.take (m+j+1)) + 1
          have hkey : lukSum (rest.take (m + (j + 1)))
              = lukSum (rest.take m) + lukSum ((rest.drop m).take (j + 1)) := by
            rw [List.take_add, lukSum_append]
          have hlt2 : m + (j + 1) < rest.length := by omega
          have := hdomR (m + (j + 1)) hlt2
          rw [hkey, hm_val] at this
          linarith
        have hc2len : (rest.drop m).length ≤ N := by
          rw [List.length_drop]; omega
        obtain ⟨R, hR⟩ := ihN (rest.drop m) hc2len hc2sum hc2dom
        have hLne : L ≠ .nil := by
          rintro rfl
          rw [toDeg] at hL
          have : (rest.take m).length = 0 := by rw [← hL]; rfl
          rw [List.length_take, Nat.min_eq_left hm_le] at this; omega
        have hRne : R ≠ .nil := by
          rintro rfl
          rw [toDeg] at hR
          have : (rest.drop m).length = 0 := by rw [← hR]; rfl
          rw [List.length_drop] at this; omega
        refine ⟨BinaryTree.node () L R, ?_⟩
        rw [toDeg, rootLetter_two' hLne hRne, hL, hR, hsplit]

/-! ### POP-side soundness: length, double-pop count, validity -/

lemma toPop_length : ∀ t : T, t ≠ .nil → BinaryTree.numNodes t = (toPop t).length + 1 := by
  intro t
  induction t with
  | nil => intro h; exact absurd rfl h
  | node _ L R ihL ihR =>
    intro _
    by_cases hL : L = .nil <;> by_cases hR : R = .nil
    · subst hL; subst hR; rw [toPop_ll]; simp [BinaryTree.numNodes]
    · subst hL
      rw [toPop_lR hR]; have := ihR hR
      simp only [BinaryTree.numNodes, List.length_cons] at *; omega
    · subst hR
      rw [toPop_Ln hL]; have := ihL hL
      simp only [BinaryTree.numNodes, List.length_cons] at *; omega
    · rw [toPop_LR hL hR]; have h1 := ihL hL; have h2 := ihR hR
      simp only [BinaryTree.numNodes, List.length_append, List.length_cons] at *; omega

lemma toPop_P2 : ∀ t : T, P2 (toPop t) = twoNodes t := by
  intro t
  induction t with
  | nil => rfl
  | node _ L R ihL ihR =>
    by_cases hL : L = .nil <;> by_cases hR : R = .nil
    · subst hL; subst hR; rfl
    · subst hL
      rw [toPop_lR hR]
      have htn : twoNodes (BinaryTree.node () .nil R) = twoNodes R := by
        simp [twoNodes, isNode_nil]
      rw [htn, ← ihR]
      show (if 2 ≤ 1 then 1 else 0) + P2 (toPop R) = P2 (toPop R)
      norm_num
    · subst hR
      rw [toPop_Ln hL]
      have htn : twoNodes (BinaryTree.node () L .nil) = twoNodes L := by
        simp [twoNodes, isNode_nil]
      rw [htn, ← ihL]
      show (if 2 ≤ 0 then 1 else 0) + P2 (toPop L) = P2 (toPop L)
      norm_num
    · rw [toPop_LR hL hR, P2_append]
      have hrl : 1 ≤ rem L := rem_pos L hL
      have e1 : P2 (0 :: toPop L) = twoNodes L := by
        show (if 2 ≤ 0 then 1 else 0) + P2 (toPop L) = twoNodes L
        rw [ihL]; norm_num
      have e2 : P2 ((rem L + 1) :: toPop R) = 1 + twoNodes R := by
        show (if 2 ≤ rem L + 1 then 1 else 0) + P2 (toPop R) = 1 + twoNodes R
        rw [if_pos (by omega), ihR]
      rw [e1, e2]
      have htn : twoNodes (BinaryTree.node () L R) = 1 + twoNodes L + twoNodes R := by
        simp only [twoNodes, isNode_eq_true.mpr hL, isNode_eq_true.mpr hR, Bool.and_self,
          if_true]
      rw [htn]; ring

/-- **Encoder validity invariant**: reading `toPop t` from any height `h ≥ 1`
    is Łukasiewicz-valid, and shifts the height reading of the continuation `s`
    from `h` to `h - 1 + rem t`. -/
lemma enc_valid : ∀ (t : T), t ≠ .nil → ∀ (s : List ℕ) (h : ℕ), 1 ≤ h →
    (Valid h (toPop t ++ s) ↔ Valid (h - 1 + rem t) s) := by
  intro t
  induction t with
  | nil => intro h; exact absurd rfl h
  | node _ L R ihL ihR =>
    intro _ s h hh
    by_cases hL : L = .nil <;> by_cases hR : R = .nil
    · subst hL; subst hR
      rw [toPop_ll, rem_ll, show h - 1 + 1 = h by omega]; simp
    · subst hL
      rw [toPop_lR hR, rem_lR hR, List.cons_append]
      simp only [Valid]
      rw [show h + 1 - 1 = h by omega, ihR hR s h hh]
      constructor
      · rintro ⟨_, hv⟩; exact hv
      · intro hv; exact ⟨by omega, hv⟩
    · subst hR
      rw [toPop_Ln hL, rem_Ln hL, List.cons_append]
      simp only [Valid]
      rw [show h + 1 - 0 = h + 1 by omega, ihL hL s (h + 1) (by omega),
        show h + 1 - 1 + rem L = h - 1 + (rem L + 1) by omega]
      constructor
      · rintro ⟨_, hv⟩; exact hv
      · intro hv; exact ⟨by omega, hv⟩
    · rw [toPop_LR hL hR, rem_Rnn hR, List.append_assoc, List.cons_append]
      simp only [Valid]
      rw [show h + 1 - 0 = h + 1 by omega,
        ihL hL ((rem L + 1) :: toPop R ++ s) (h + 1) (by omega),
        List.cons_append]
      simp only [Valid]
      rw [show h + 1 - 1 + rem L = h + rem L by omega,
        show h + rem L + 1 - (rem L + 1) = h by omega, ihR hR s h hh]
      constructor
      · rintro ⟨_, _, hv⟩; exact hv
      · intro hv; exact ⟨by omega, by omega, hv⟩

/-- Soundness: the pop-codeword of an `n`-node tree is a valid Mäkinen
    codeword of length `n-1` read from height `1`. -/
lemma toPop_mem_suffixes (t : T) (h : t ≠ .nil) :
    toPop t ∈ suffixes (BinaryTree.numNodes t - 1) 1 := by
  rw [mem_suffixes]
  refine ⟨?_, ?_⟩
  · rw [toPop_length t h]; omega
  · have := (enc_valid t h [] 1 (le_refl 1)).mpr (by simp [Valid])
    simpa using this

/-! ### POP-side: injectivity of `toPop` via the fuelled decoder -/

/-- Guard on the continuation: empty, or its head strictly exceeds `r`. -/
def guardR (r : ℕ) : List ℕ → Prop
  | [] => True
  | x :: _ => r < x

/-- **Fuelled decoder** (Mäkinen `buildA`), ported from Rocq `decode_node`:
    the exact structural inverse of `enc`. -/
def dec : ℕ → List ℕ → T × List ℕ × ℕ
  | 0, w => (BinaryTree.node () .nil .nil, w, 1)
  | fuel + 1, w =>
    match w with
    | 0 :: w' =>
        match dec fuel w' with
        | (L, x :: w2, remL) =>
            if x = remL + 1 then
              match dec fuel w2 with
              | (R, w3, remR) => (BinaryTree.node () L R, w3, remR)
            else (BinaryTree.node () L .nil, x :: w2, remL + 1)
        | (L, [], remL) => (BinaryTree.node () L .nil, [], remL + 1)
    | x :: w' =>
        if x = 1 then
          match dec fuel w' with
          | (R, w3, remR) => (BinaryTree.node () .nil R, w3, remR)
        else (BinaryTree.node () .nil .nil, x :: w', 1)
    | [] => (BinaryTree.node () .nil .nil, [], 1)

lemma dec_nil (f : ℕ) : dec (f + 1) [] = (BinaryTree.node () .nil .nil, [], 1) := rfl

lemma dec_cons_zero (f : ℕ) (w' : List ℕ) :
    dec (f + 1) (0 :: w') = (match dec f w' with
      | (L, x :: w2, remL) => if x = remL + 1 then
            (match dec f w2 with | (R, w3, remR) => (BinaryTree.node () L R, w3, remR))
          else (BinaryTree.node () L .nil, x :: w2, remL + 1)
      | (L, [], remL) => (BinaryTree.node () L .nil, [], remL + 1)) := rfl

lemma dec_cons_pos (f x : ℕ) (w' : List ℕ) (hx : x ≠ 0) :
    dec (f + 1) (x :: w') = (if x = 1 then
        (match dec f w' with | (R, w3, remR) => (BinaryTree.node () .nil R, w3, remR))
      else (BinaryTree.node () .nil .nil, x :: w', 1)) := by
  cases x with | zero => exact absurd rfl hx | succ x => rfl

/-- **Decoder round-trip**: `dec` (with enough fuel and a valid completing
    guard) recovers the tree and consumes exactly its codeword.  Hence `enc`
    is injective. -/
lemma dec_enc : ∀ (t : T), t ≠ .nil → ∀ (fuel : ℕ) (rest : List ℕ),
    BinaryTree.numNodes t ≤ fuel → guardR (rem t) rest →
    dec fuel (toPop t ++ rest) = (t, rest, rem t) := by
  intro t
  induction t with
  | nil => intro h; exact absurd rfl h
  | node val L R ihL ihR =>
    cases val
    intro _ fuel rest hfuel hguard
    simp only [BinaryTree.numNodes] at hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases hL : L = .nil <;> by_cases hR : R = .nil
    · -- both nil
      subst hL; subst hR
      rw [toPop_ll, List.nil_append, rem_ll]
      rw [rem_ll] at hguard
      cases rest with
      | nil => rw [dec_nil]
      | cons x rest' =>
        have hx : 1 < x := hguard
        rw [dec_cons_pos f x rest' (by omega), if_neg (by omega)]
    · -- L nil, R nonnil
      subst hL
      rw [toPop_lR hR, rem_lR hR, List.cons_append, dec_cons_pos f 1 _ (by norm_num), if_pos rfl]
      have hnR : BinaryTree.numNodes R ≤ f := by simp only [BinaryTree.numNodes] at hfuel; omega
      rw [rem_lR hR] at hguard
      rw [ihR hR f rest hnR hguard]
    · -- L nonnil, R nil
      subst hR
      rw [toPop_Ln hL, rem_Ln hL, List.cons_append, dec_cons_zero]
      have hnL : BinaryTree.numNodes L ≤ f := by simp only [BinaryTree.numNodes] at hfuel; omega
      rw [rem_Ln hL] at hguard
      have hguardL : guardR (rem L) rest := by
        cases rest with
        | nil => trivial
        | cons x rest' => exact lt_trans (Nat.lt_succ_self _) hguard
      rw [ihL hL f rest hnL hguardL]
      cases rest with
      | nil => rfl
      | cons x rest' =>
        have hx : rem L + 1 < x := hguard
        dsimp only
        rw [if_neg (by omega)]
    · -- both nonnil
      rw [toPop_LR hL hR, rem_Rnn hR, List.append_assoc, List.cons_append, List.cons_append,
        dec_cons_zero]
      have hnL : BinaryTree.numNodes L ≤ f := by omega
      have hnR : BinaryTree.numNodes R ≤ f := by omega
      have hguardL : guardR (rem L) ((rem L + 1) :: (toPop R ++ rest)) := by
        show rem L < rem L + 1; omega
      rw [rem_Rnn hR] at hguard
      rw [ihL hL f ((rem L + 1) :: (toPop R ++ rest)) hnL hguardL]
      dsimp only
      rw [if_pos rfl, ihR hR f rest hnR hguard]

/-- `toPop` is injective on non-empty trees (decoder round-trip). -/
lemma toPop_inj {t1 t2 : T} (h1 : t1 ≠ .nil) (h2 : t2 ≠ .nil)
    (heq : toPop t1 = toPop t2) : t1 = t2 := by
  have hlen : (toPop t1).length = (toPop t2).length := by rw [heq]
  have hf1 : BinaryTree.numNodes t1 ≤ (toPop t1).length + 1 := by rw [toPop_length t1 h1]
  have hf2 : BinaryTree.numNodes t2 ≤ (toPop t1).length + 1 := by
    rw [toPop_length t2 h2, hlen]
  have e1 := dec_enc t1 h1 ((toPop t1).length + 1) [] hf1 (by trivial)
  have e2 := dec_enc t2 h2 ((toPop t1).length + 1) [] hf2 (by trivial)
  rw [List.append_nil] at e1 e2
  have hkey : dec ((toPop t1).length + 1) (toPop t1)
      = dec ((toPop t1).length + 1) (toPop t2) := by rw [heq]
  rw [hkey, e2] at e1
  exact ((Prod.ext_iff.mp e1).1).symm

/-! ### Assembly: the two legs and the bridge -/

lemma twoNodes_le : ∀ t : T, twoNodes t ≤ BinaryTree.numNodes t := by
  intro t
  induction t with
  | nil => simp [twoNodes, BinaryTree.numNodes]
  | node _ L R ihL ihR =>
    simp only [twoNodes, BinaryTree.numNodes]
    have : (if isNode L && isNode R then 1 else 0) ≤ 1 := by split <;> omega
    omega

-- duplicate of LocalCLT.P2_le_length (kept private: avoiding the import edge)
private lemma P2_le_length : ∀ w : List ℕ, P2 w ≤ w.length := by
  intro w
  induction w with
  | nil => simp [P2]
  | cons x w ih =>
    simp only [P2, List.length_cons]
    have : (if 2 ≤ x then 1 else 0) ≤ 1 := by split <;> omega
    omega

/-- **DEGREE leg** (full bijection): the number of `n`-node trees with `k`
    two-children nodes equals the number of dominating degree words. -/
lemma card_Tk_eq_Dk (n k : ℕ) (hn : 1 ≤ n) :
    ((BinaryTree.treesOfNumNodesEq n).filter (fun t => twoNodes t = k)).card
      = ((degWords n k).filter Dominating).card := by
  apply Finset.card_bij (fun t _ => toDeg t)
  · intro t ht
    rw [Finset.mem_filter, BinaryTree.mem_treesOfNumNodesEq] at ht
    obtain ⟨htn, htk⟩ := ht
    have hne : t ≠ .nil := by rintro rfl; simp [BinaryTree.numNodes] at htn; omega
    rw [Finset.mem_filter]
    refine ⟨?_, dominating_toDeg t⟩
    have := toDeg_mem_degWords t hne
    rwa [htn, htk] at this
  · intro t1 ht1 t2 ht2 he
    rw [Finset.mem_filter, BinaryTree.mem_treesOfNumNodesEq] at ht1 ht2
    have hne1 : t1 ≠ .nil := by rintro rfl; simp [BinaryTree.numNodes] at ht1; omega
    have hne2 : t2 ≠ .nil := by rintro rfl; simp [BinaryTree.numNodes] at ht2; omega
    exact toDeg_inj hne1 hne2 he
  · intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨hwdeg, hwdom⟩ := hw
    obtain ⟨hlen, hcount2, _⟩ := mem_degWords.mp hwdeg
    have hsum : lukSum w = -1 := lukSum_degWords hwdeg
    obtain ⟨t, ht⟩ := exists_toDeg w.length w le_rfl hsum
      (fun j hj => by have := hwdom j hj; omega)
    have hnn : BinaryTree.numNodes t = n := by rw [← toDeg_length t, ht, hlen]
    have hkk : twoNodes t = k := by rw [← toDeg_count_two t, ht, hcount2]
    exact ⟨t, by rw [Finset.mem_filter, BinaryTree.mem_treesOfNumNodesEq]; exact ⟨hnn, hkk⟩, ht⟩

/-- **POP leg, injection**: `#trees_k ≤ #popwords_k`. -/
lemma card_filter_twoNodes_le_P2 (n k : ℕ) (hn : 1 ≤ n) :
    ((BinaryTree.treesOfNumNodesEq n).filter (fun t => twoNodes t = k)).card
      ≤ ((suffixes (n - 1) 1).filter (fun w => P2 w = k)).card := by
  apply Finset.card_le_card_of_injOn toPop
  · intro t ht
    rw [Finset.mem_coe, Finset.mem_filter, BinaryTree.mem_treesOfNumNodesEq] at ht
    obtain ⟨htn, htk⟩ := ht
    have hne : t ≠ .nil := by rintro rfl; simp [BinaryTree.numNodes] at htn; omega
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · have := toPop_mem_suffixes t hne; rwa [htn] at this
    · rw [toPop_P2, htk]
  · intro t1 ht1 t2 ht2 he
    rw [Finset.mem_coe, Finset.mem_filter, BinaryTree.mem_treesOfNumNodesEq] at ht1 ht2
    have hne1 : t1 ≠ .nil := by rintro rfl; simp [BinaryTree.numNodes] at ht1; omega
    have hne2 : t2 ≠ .nil := by rintro rfl; simp [BinaryTree.numNodes] at ht2; omega
    exact toPop_inj hne1 hne2 he

/-- Tree total, fibred by two-node count, equals `catalan n`. -/
lemma sum_card_filter_twoNodes (n : ℕ) :
    ∑ k ∈ range (n + 1),
        ((BinaryTree.treesOfNumNodesEq n).filter (fun t => twoNodes t = k)).card
      = catalan n := by
  have h := Finset.card_eq_sum_card_fiberwise (s := BinaryTree.treesOfNumNodesEq n)
    (t := range (n + 1)) (f := twoNodes) (by
      intro t ht
      rw [Finset.mem_coe, BinaryTree.mem_treesOfNumNodesEq] at ht
      rw [Finset.mem_coe, Finset.mem_range]
      have := twoNodes_le t; omega)
  rw [BinaryTree.treesOfNumNodesEq_card_eq_catalan] at h
  exact h.symm

/-- Pop-word total, fibred by double-pop count, equals `catalan n`. -/
lemma sum_card_filter_P2 (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ range (n + 1), ((suffixes (n - 1) 1).filter (fun w => P2 w = k)).card
      = catalan n := by
  have h := Finset.card_eq_sum_card_fiberwise (s := suffixes (n - 1) 1)
    (t := range (n + 1)) (f := P2) (by
      intro w hw
      rw [Finset.mem_coe] at hw
      rw [Finset.mem_coe, Finset.mem_range]
      obtain ⟨hlen, _⟩ := (mem_suffixes _ _ w).mp hw
      have := P2_le_length w; rw [hlen] at this; omega)
  rw [card_suffixes_eq_catalan n hn] at h
  exact h.symm

/-- **POP leg** (counting squeeze): `#trees_k = #popwords_k`. -/
lemma card_Tk_eq_Pk (n k : ℕ) (hn : 1 ≤ n) (hk : k < n + 1) :
    ((BinaryTree.treesOfNumNodesEq n).filter (fun t => twoNodes t = k)).card
      = ((suffixes (n - 1) 1).filter (fun w => P2 w = k)).card := by
  have hle : ∀ j ∈ range (n + 1),
      ((BinaryTree.treesOfNumNodesEq n).filter (fun t => twoNodes t = j)).card
      ≤ ((suffixes (n - 1) 1).filter (fun w => P2 w = j)).card :=
    fun j _ => card_filter_twoNodes_le_P2 n j hn
  have hsum : ∑ j ∈ range (n + 1),
        ((BinaryTree.treesOfNumNodesEq n).filter (fun t => twoNodes t = j)).card
      = ∑ j ∈ range (n + 1), ((suffixes (n - 1) 1).filter (fun w => P2 w = j)).card := by
    rw [sum_card_filter_twoNodes, sum_card_filter_P2 n hn]
  exact (Finset.sum_eq_sum_iff_of_le hle).mp hsum k (Finset.mem_range.mpr hk)

/-! ### The bridge and the closed form -/

/-- **The pop ↔ dominating-degree bridge.**  For `1 ≤ n` and `2k + 1 ≤ n`, the
    number of valid Mäkinen pop-codewords of length `n-1` from height `1` with
    `k` double pops equals the number of dominating degree words of length `n`
    with `k` two-children nodes. -/
theorem U_eq_dominating (n k : ℕ) (hn : 1 ≤ n) (hk : 2 * k + 1 ≤ n) :
    U (n - 1) 1 k = ((degWords n k).filter Dominating).card := by
  rw [← card_filter_P2, ← card_Tk_eq_Pk n k hn (by omega), card_Tk_eq_Dk n k hn]

/-- **`U_mul_closed`.**  Discharging the bridge of `PopClosed.U_mul_closed_of_bridge`,
    the pop-codeword closed form holds unconditionally. -/
theorem U_mul_closed (n k : ℕ) (hn : 1 ≤ n) (hk : 2 * k + 1 ≤ n) :
    n * U (n - 1) 1 k
      = n.choose k * (n - k).choose (n - 1 - 2 * k) * 2 ^ (n - 1 - 2 * k) :=
  U_mul_closed_of_bridge n k hk (U_eq_dominating n k hn hk)

end MakinenAnalysis
