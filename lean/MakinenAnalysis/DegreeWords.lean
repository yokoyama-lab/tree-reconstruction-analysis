import Mathlib

/-!
# Degree words of binary trees: the multinomial count

Phase 3 of the CLT roadmap: the *degree-word* model.  A binary tree on `n`
nodes is recorded in preorder by the word of its node degrees over the
four-letter alphabet `Deg = {leaf, oneL, oneR, two}`; a tree with `k`
two-children nodes has exactly `k + 1` leaves, so its degree word lies in

* `degWords n k` — words of length `n` with exactly `k` letters `two` and
  exactly `k + 1` letters `leaf` (the remaining `n - 1 - 2k` letters being
  `oneL` or `oneR`).

The **main counting theorem** (`card_degWords`) is the multinomial count

  `#(degWords n k) = C(n,k) · C(n-k, k+1) · 2^(n-1-2k)`,

proved by the textbook decomposition: choose the `k` positions of the `two`s,
then the `k+1` positions of the `leaf`s among the remaining `n-k`, then orient
each leftover one-child node.  Formally we count the tuple model
`degTuples n k ⊆ (Fin n → Deg)` by fibering it over the position data
`posPairs n k = Σ (A : |A| = k), (Aᶜ).powersetCard (k+1)`
(`Finset.card_eq_sum_card_fiberwise`); each fiber is a `Fintype.piFinset` of
pointwise constraints (`filter_posData_eq`) of cardinality `2^(n-1-2k)`
(`card_filter_posData`), and the base has cardinality
`C(n,k)·C(n-k,k+1)` (`card_posPairs`).  The identity holds *unconditionally*
(for `2k + 1 > n` both sides vanish); `card_degWords_of_le` restates it under
the natural hypothesis `2k + 1 ≤ n`.

The Łukasiewicz structure is set up at the end: `Deg.step` (children count
minus one), `lukSum`, and the dominance predicate `Dominating` (all *proper*
nonempty prefixes have partial sum `> -1`; the full word always sums to `-1`
on `degWords`, `lukSum_degWords`).  The cycle-lemma orbit count
`n · #(dominating words) = #(degWords n k)` — whence the number of `n`-node
binary trees with `k` two-children nodes is `(1/n)·C(n,k)·C(n-k,k+1)·2^(n-1-2k)`
— is stated as `proof_wanted` (`card_dominating_mul`) and kernel-checked for
small `n` below.
-/

set_option linter.unusedSimpArgs false

namespace MakinenAnalysis

open Finset

/-! ### The degree alphabet -/

/-- Node degrees of a binary tree: a leaf, a node with only a left child,
    only a right child, or two children. -/
inductive Deg : Type
  | leaf
  | oneL
  | oneR
  | two
  deriving DecidableEq, Repr

/-- A decide-friendly `Fintype` instance (explicit universe list, so that
    small instances below can be checked by the kernel). -/
instance : Fintype Deg :=
  ⟨{.leaf, .oneL, .oneR, .two}, fun d => by cases d <;> decide⟩

/-- Łukasiewicz step of a letter: number of children minus one. -/
def Deg.step : Deg → ℤ
  | .leaf => -1
  | .oneL => 0
  | .oneR => 0
  | .two => 1

/-- Indicator of the letter `two` (number of two-children nodes contributed). -/
def Deg.twoCount : Deg → ℕ
  | .two => 1
  | _ => 0

/-- The `twoCount` indicators sum to the number of `two`s of the word. -/
lemma sum_map_twoCount (w : List Deg) :
    (w.map Deg.twoCount).sum = w.count Deg.two := by
  induction w with
  | nil => rfl
  | cons d t ih => cases d <;> simp [List.count_cons, Deg.twoCount, ih, Nat.add_comm]

/-! ### Degree words -/

variable {n k : ℕ}

/-- The set of positions where the tuple `f` carries the letter `d`. -/
def degFiber (f : Fin n → Deg) (d : Deg) : Finset (Fin n) :=
  Finset.univ.filter fun i => f i = d

@[simp] lemma mem_degFiber {f : Fin n → Deg} {d : Deg} {i : Fin n} :
    i ∈ degFiber f d ↔ f i = d := by
  simp [degFiber]

/-- Degree tuples: length-`n` letter tuples with exactly `k` letters `two`
    and exactly `k + 1` letters `leaf`. -/
def degTuples (n k : ℕ) : Finset (Fin n → Deg) :=
  Finset.univ.filter fun f =>
    (degFiber f .two).card = k ∧ (degFiber f .leaf).card = k + 1

/-- **Degree words**: lists over `Deg` of length `n` with exactly `k` letters
    `two` and exactly `k + 1` letters `leaf`.  (Encoded as the image of the
    tuple model `degTuples` under `List.ofFn`; the intrinsic membership
    description is `mem_degWords`.) -/
def degWords (n k : ℕ) : Finset (List Deg) :=
  (degTuples n k).image List.ofFn

/-- Letter counts of `List.ofFn f` are fiber cardinalities. -/
lemma count_ofFn : ∀ {n : ℕ} (f : Fin n → Deg) (d : Deg),
    (List.ofFn f).count d = (degFiber f d).card := by
  intro n
  induction n with
  | zero =>
    intro f d
    simp [degFiber]
  | succ n ih =>
    intro f d
    have hcons : (List.ofFn f).count d
        = (if f 0 = d then 1 else 0) + (List.ofFn fun i => f i.succ).count d := by
      rw [List.ofFn_succ]
      by_cases hd : f 0 = d
      · subst hd
        simp [List.count_cons, Nat.add_comm]
      · simp [List.count_cons, hd, Ne.symm hd]
    have hsucc : (degFiber f d).card
        = (if f 0 = d then 1 else 0) + (degFiber (fun i => f i.succ) d).card := by
      simp only [degFiber, Finset.card_filter, Fin.sum_univ_succ]
    rw [hcons, ih, hsucc]

/-- Intrinsic description of `degWords`: the words of length `n` with `k`
    letters `two` and `k + 1` letters `leaf`. -/
lemma mem_degWords {w : List Deg} :
    w ∈ degWords n k ↔
      w.length = n ∧ w.count Deg.two = k ∧ w.count Deg.leaf = k + 1 := by
  constructor
  · intro hw
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨-, h2, hL⟩ := Finset.mem_filter.mp hf
    refine ⟨by simp, ?_, ?_⟩
    · rw [count_ofFn]; exact h2
    · rw [count_ofFn]; exact hL
  · rintro ⟨rfl, h2, hL⟩
    refine Finset.mem_image.mpr
      ⟨w.get, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, List.ofFn_get w⟩
    · have h := count_ofFn w.get Deg.two
      rw [List.ofFn_get] at h
      omega
    · have h := count_ofFn w.get Deg.leaf
      rw [List.ofFn_get] at h
      omega

/-! ### Kernel checks pinning the definition (small `n`)

Before the general proof, the closed form is verified inside the kernel for
all `n ≤ 6` and all valid `k` — guarding against a mis-stated target. -/

example : (degTuples 1 0).card = 1 := by decide
example : (degTuples 2 0).card = 4 := by decide
example : (degTuples 3 0).card = 12 := by decide
example : (degTuples 3 1).card = 3 := by decide

set_option maxRecDepth 20000 in
example : (degTuples 4 1).card = 24 := by decide

set_option maxRecDepth 20000 in
example : (degTuples 5 2).card = 10 := by decide

set_option maxRecDepth 100000 in
example : ∀ n < 7, ∀ k < 3, 2 * k + 1 ≤ n →
    (degTuples n k).card
      = n.choose k * (n - k).choose (k + 1) * 2 ^ (n - 1 - 2 * k) := by
  decide

-- the list model agrees with the tuple model
set_option maxRecDepth 20000 in
example : (degWords 4 1).card = 24 := by decide

set_option maxRecDepth 20000 in
example : (degWords 5 2).card = 10 := by decide

/-! ### The multinomial count -/

/-- Position data: a `k`-element set `A` of positions (the `two`s) together
    with a `(k+1)`-element set of positions (the `leaf`s) disjoint from `A`. -/
def posPairs (n k : ℕ) : Finset (Σ _A : Finset (Fin n), Finset (Fin n)) :=
  ((Finset.univ : Finset (Fin n)).powersetCard k).sigma fun A =>
    Aᶜ.powersetCard (k + 1)

/-- The base of the fibration: `C(n,k) · C(n-k, k+1)` choices of positions. -/
lemma card_posPairs (n k : ℕ) :
    (posPairs n k).card = n.choose k * (n - k).choose (k + 1) := by
  rw [posPairs, Finset.card_sigma]
  have h : ∀ A ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      (Aᶜ.powersetCard (k + 1)).card = (n - k).choose (k + 1) := fun A hA => by
    rw [Finset.card_powersetCard, Finset.card_compl, Fintype.card_fin,
      (Finset.mem_powersetCard.mp hA).2]
  rw [Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- The position data of a tuple. -/
def posData (f : Fin n → Deg) : Σ _A : Finset (Fin n), Finset (Fin n) :=
  ⟨degFiber f .two, degFiber f .leaf⟩

/-- The position data of a degree tuple lands in `posPairs`. -/
lemma posData_mem_posPairs {f : Fin n → Deg} (hf : f ∈ degTuples n k) :
    posData f ∈ posPairs n k := by
  obtain ⟨-, h2, hL⟩ := Finset.mem_filter.mp hf
  simp only [posData, posPairs, Finset.mem_sigma, Finset.mem_powersetCard]
  refine ⟨⟨Finset.subset_univ _, h2⟩, fun i hi => ?_, hL⟩
  rw [mem_degFiber] at hi
  rw [Finset.mem_compl, mem_degFiber, hi]
  decide

/-- Pointwise constraint attached to position data `(A, B)`: forced `two` on
    `A`, forced `leaf` on `B`, a free one-child orientation elsewhere. -/
def allowed (A B : Finset (Fin n)) (i : Fin n) : Finset Deg :=
  if i ∈ A then {.two} else if i ∈ B then {.leaf} else {.oneL, .oneR}

/-- A tuple satisfies the pointwise constraints of `(A, B)` iff its position
    data is exactly `(A, B)`. -/
lemma forall_mem_allowed_iff {A B : Finset (Fin n)} (hAB : Disjoint A B)
    {f : Fin n → Deg} :
    (∀ i, f i ∈ allowed A B i) ↔ degFiber f .two = A ∧ degFiber f .leaf = B := by
  constructor
  · intro h
    constructor
    · ext i
      rw [mem_degFiber]
      constructor
      · intro hfi
        by_contra hiA
        have hi := h i
        rw [allowed, if_neg hiA] at hi
        by_cases hiB : i ∈ B
        · rw [if_pos hiB, Finset.mem_singleton, hfi] at hi
          exact absurd hi (by decide)
        · rw [if_neg hiB, hfi] at hi
          exact absurd hi (by decide)
      · intro hiA
        have hi := h i
        rw [allowed, if_pos hiA, Finset.mem_singleton] at hi
        exact hi
    · ext i
      rw [mem_degFiber]
      constructor
      · intro hfi
        by_contra hiB
        have hi := h i
        rw [allowed] at hi
        by_cases hiA : i ∈ A
        · rw [if_pos hiA, Finset.mem_singleton, hfi] at hi
          exact absurd hi (by decide)
        · rw [if_neg hiA, if_neg hiB, hfi] at hi
          exact absurd hi (by decide)
      · intro hiB
        have hi := h i
        rw [allowed, if_neg (Finset.disjoint_right.mp hAB hiB), if_pos hiB,
          Finset.mem_singleton] at hi
        exact hi
  · rintro ⟨rfl, rfl⟩ i
    rw [allowed]
    by_cases hiA : i ∈ degFiber f .two
    · rw [if_pos hiA, Finset.mem_singleton]
      exact mem_degFiber.mp hiA
    · rw [if_neg hiA]
      by_cases hiB : i ∈ degFiber f .leaf
      · rw [if_pos hiB, Finset.mem_singleton]
        exact mem_degFiber.mp hiB
      · rw [if_neg hiB]
        rw [mem_degFiber] at hiA hiB
        cases hfi : f i with
        | leaf => exact absurd hfi hiB
        | oneL => decide
        | oneR => decide
        | two => exact absurd hfi hiA

/-- The `posData`-fiber over `(A, B)` is a box of pointwise constraints. -/
lemma filter_posData_eq {A B : Finset (Fin n)} (hA : A.card = k)
    (hB : B.card = k + 1) (hAB : Disjoint A B) :
    (degTuples n k).filter (fun f => posData f = ⟨A, B⟩)
      = Fintype.piFinset (allowed A B) := by
  ext f
  rw [Finset.mem_filter, Fintype.mem_piFinset, degTuples, Finset.mem_filter]
  constructor
  · rintro ⟨-, hpd⟩
    simp only [posData, Sigma.mk.injEq, heq_eq_eq] at hpd
    exact (forall_mem_allowed_iff hAB).mpr hpd
  · intro h
    obtain ⟨h2, hL⟩ := (forall_mem_allowed_iff hAB).mp h
    refine ⟨⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
    · rw [h2, hA]
    · rw [hL, hB]
    · simp only [posData, h2, hL]

/-- Each fiber has exactly `2^(n-1-2k)` elements: the free orientations. -/
lemma card_filter_posData {A B : Finset (Fin n)} (hA : A.card = k)
    (hB : B.card = k + 1) (hAB : Disjoint A B) :
    ((degTuples n k).filter fun f => posData f = ⟨A, B⟩).card
      = 2 ^ (n - 1 - 2 * k) := by
  rw [filter_posData_eq hA hB hAB, Fintype.card_piFinset]
  have hcard : ∀ i : Fin n,
      (allowed A B i).card = if i ∈ (A ∪ B)ᶜ then 2 else 1 := by
    intro i
    rw [allowed]
    by_cases hiA : i ∈ A
    · rw [if_pos hiA, Finset.card_singleton,
        if_neg (by simp [Finset.mem_compl, Finset.mem_union, hiA])]
    · by_cases hiB : i ∈ B
      · rw [if_neg hiA, if_pos hiB, Finset.card_singleton,
          if_neg (by simp [Finset.mem_compl, Finset.mem_union, hiB])]
      · rw [if_neg hiA, if_neg hiB,
          if_pos (by simp [Finset.mem_compl, Finset.mem_union, hiA, hiB])]
        decide
  rw [Finset.prod_congr rfl fun i _ => hcard i, Finset.prod_ite_mem,
    Finset.univ_inter, Finset.prod_const]
  congr 1
  rw [Finset.card_compl, Fintype.card_fin,
    Finset.card_union_of_disjoint hAB, hA, hB]
  omega

/-- The multinomial count on the tuple model (unconditional: for
    `2k + 1 > n` both sides vanish). -/
theorem card_degTuples (n k : ℕ) :
    (degTuples n k).card
      = n.choose k * (n - k).choose (k + 1) * 2 ^ (n - 1 - 2 * k) := by
  rw [Finset.card_eq_sum_card_fiberwise
    (fun f (hf : f ∈ degTuples n k) => posData_mem_posPairs hf)]
  have h : ∀ p ∈ posPairs n k,
      ((degTuples n k).filter fun f => posData f = p).card
        = 2 ^ (n - 1 - 2 * k) := by
    rintro ⟨A, B⟩ hp
    obtain ⟨hA, hB⟩ := Finset.mem_sigma.mp hp
    obtain ⟨-, hAcard⟩ := Finset.mem_powersetCard.mp hA
    obtain ⟨hBsub, hBcard⟩ := Finset.mem_powersetCard.mp hB
    exact card_filter_posData hAcard hBcard (le_compl_iff_disjoint_left.mp hBsub)
  rw [Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul, card_posPairs]

/-- `List.ofFn` is a bijection from the tuple model onto the word model. -/
lemma card_degWords_eq_card_degTuples (n k : ℕ) :
    (degWords n k).card = (degTuples n k).card :=
  Finset.card_image_of_injective _ List.ofFn_injective

/-- **Main counting theorem** (multinomial count of degree words):
    `#(degWords n k) = C(n,k) · C(n-k, k+1) · 2^(n-1-2k)`. -/
theorem card_degWords (n k : ℕ) :
    (degWords n k).card
      = n.choose k * (n - k).choose (k + 1) * 2 ^ (n - 1 - 2 * k) := by
  rw [card_degWords_eq_card_degTuples, card_degTuples]

/-- The main counting theorem under the natural hypothesis `2k + 1 ≤ n`
    (the statement requested by the roadmap; it holds unconditionally,
    see `card_degWords`). -/
theorem card_degWords_of_le (n k : ℕ) (_hkn : 2 * k + 1 ≤ n) :
    (degWords n k).card
      = n.choose k * (n - k).choose (k + 1) * 2 ^ (n - 1 - 2 * k) :=
  card_degWords n k

/-! ### Łukasiewicz sums and dominance -/

/-- Łukasiewicz sum of a degree word: total children count minus length. -/
def lukSum (w : List Deg) : ℤ := (w.map Deg.step).sum

set_option linter.unusedTactic false in
lemma lukSum_eq_count (w : List Deg) :
    lukSum w = (w.count Deg.two : ℤ) - (w.count Deg.leaf : ℤ) := by
  induction w with
  | nil => rfl
  | cons d t ih =>
    have hcons : lukSum (d :: t) = d.step + lukSum t := by
      rw [lukSum, List.map_cons, List.sum_cons, lukSum]
    rw [hcons, ih]
    cases d <;> simp [List.count_cons, Deg.step] <;> push_cast <;> ring

/-- Every degree word closes at `-1`: `k` up-steps, `k+1` down-steps. -/
lemma lukSum_degWords {w : List Deg} (hw : w ∈ degWords n k) :
    lukSum w = -1 := by
  obtain ⟨-, h2, hL⟩ := mem_degWords.mp hw
  rw [lukSum_eq_count, h2, hL]
  push_cast
  ring

/-- **Dominance**: every *proper* nonempty prefix has Łukasiewicz sum
    `> -1` (i.e. `≥ 0`).  Since the full word sums to `-1`
    (`lukSum_degWords`), the dominating words in `degWords n k` are exactly
    the preorder degree words of the `n`-node binary trees with `k`
    two-children nodes. -/
def Dominating (w : List Deg) : Prop :=
  ∀ j : ℕ, j + 1 < w.length → -1 < lukSum (w.take (j + 1))

instance : DecidablePred Dominating := fun w =>
  decidable_of_iff (∀ j < w.length - 1, -1 < lukSum (w.take (j + 1)))
    ⟨fun h j hj => h j (by omega), fun h j hj => h j (by omega)⟩

-- convention checks: the unique 3-node tree word with one `two`
example : Dominating [Deg.two, Deg.leaf, Deg.leaf] := by decide
example : ¬ Dominating [Deg.leaf, Deg.two, Deg.leaf] := by decide
example : lukSum [Deg.two, Deg.leaf, Deg.leaf] = -1 := by decide

-- orbit-count checks: `n · #(dominating) = #(degWords n k)` for small `n`
example : 1 * ((degWords 1 0).filter Dominating).card = (degWords 1 0).card := by
  decide
example : 3 * ((degWords 3 1).filter Dominating).card = (degWords 3 1).card := by
  decide
set_option maxRecDepth 20000 in
example : 4 * ((degWords 4 1).filter Dominating).card = (degWords 4 1).card := by
  decide
set_option maxRecDepth 20000 in
example : 5 * ((degWords 5 2).filter Dominating).card = (degWords 5 2).card := by
  decide
set_option maxRecDepth 20000 in
example : 5 * ((degWords 5 1).filter Dominating).card = (degWords 5 1).card := by
  decide

/-- **Cycle-lemma orbit count (Dvoretzky–Motzkin), TODO.**  Rotations
    partition each `degWords n k` (total step sum `-1`) into orbits of size
    `n`, each containing exactly one dominating word; hence the number of
    `n`-node binary trees with `k` two-children nodes is
    `(1/n)·C(n,k)·C(n-k,k+1)·2^(n-1-2k)`.
    -- TODO: prove via the cycle lemma — PROVED as `dvoretzky_motzkin` in
    `MakinenAnalysis.CycleLemma` (stated there for step sum `+1` and strict
    positivity; adapt by negating the steps): (i) each rotation class has
    exactly one dominating representative; (ii) the `n` rotations of a word in `degWords n k` are
    pairwise distinct (the step multiset has sum `-1 ≠ 0`, so a nontrivial
    rotation symmetry is impossible); (iii) conclude by double counting
    `(w, r) ↦ w.rotate r`. -/
proof_wanted card_dominating_mul (n k : ℕ) :
    n * ((degWords n k).filter Dominating).card = (degWords n k).card

end MakinenAnalysis
