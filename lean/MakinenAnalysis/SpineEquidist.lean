import MakinenAnalysis.BstModel
import MakinenAnalysis.Asymptotics

/-!
# The final stack height and the rightmost path length are equidistributed

Lemma 3 of the Japanese paper (`lem:equidist`): for `1 ≤ m ≤ n`,

  `#{T ∈ 𝒯ₙ : R(T) + 1 = m} = #{T ∈ 𝒯ₙ : h(T) = m} = B(n, m)`,

where `R(T)` is the rightmost path length (edges on the path from the root that
follows right children only) and `h(T)` is the final stack height.

The paper derives this from two separate ballot counts.  Here it is proved
**bijectively**: `chi : T → T` preserves the number of nodes and sends the
right-spine length (`spine = R + 1`) to the final stack height `rlen`
(`rlen_chi`).  The final stack height is `rlen` by `finalH_toPop_eq_rlen`
(`BstModel`), and its count is the ballot number by `W_cast_eq_ballot`
(`Asymptotics`, Lemma 2).

`chi (node a b)` grafts `chi b` as the left child of a new node hung at the end
of the right spine of `a` (`graftEnd`).  Since `rlen (graftEnd A L) = rlen L + 1`
whatever `A` is, `rlen ∘ chi` satisfies the recursion of `spine`.
-/

namespace MakinenAnalysis

open Finset

/-! ## The two statistics -/

/-- Rightmost path length `R`: the number of edges on the path from the root
    that follows right children only. -/
def rightPathLen : T → ℕ
  | .nil => 0
  | .node _ _ r => match r with
      | .nil => 0
      | .node _ _ _ => rightPathLen r + 1

/-- Number of nodes on the right spine (`= R + 1` on non-empty trees). -/
def spine : T → ℕ
  | .nil => 0
  | .node _ _ r => spine r + 1

lemma spine_eq_rightPathLen_succ : ∀ (t : T), t ≠ .nil → spine t = rightPathLen t + 1 := by
  intro t
  induction t with
  | nil => intro h; exact absurd rfl h
  | node v l r _ ihr =>
    intro _
    cases r with
    | nil => simp [spine, rightPathLen]
    | node v' a b =>
      have := ihr (by simp)
      simp only [spine, rightPathLen] at *
      omega

/-! ## The bijection -/

/-- Hang a new node with left child `L` at the end of the right spine of `A`. -/
def graftEnd : T → T → T
  | .nil, L => .node () L .nil
  | .node v a b, L => .node v a (graftEnd b L)

/-- The size-preserving bijection sending `spine` to `rlen`. -/
def chi : T → T
  | .nil => .nil
  | .node _ a b => graftEnd a (chi b)

lemma graftEnd_ne_nil (A L : T) : graftEnd A L ≠ .nil := by
  cases A <;> simp [graftEnd]

lemma rlen_graftEnd (A L : T) : rlen (graftEnd A L) = rlen L + 1 := by
  induction A with
  | nil => simp [graftEnd, rlen_node_nil]
  | node v a b _ ihb =>
    simp only [graftEnd]
    rw [rlen_node_node (graftEnd_ne_nil b L), ihb]

lemma numNodes_graftEnd (A L : T) :
    (graftEnd A L).numNodes = A.numNodes + L.numNodes + 1 := by
  induction A with
  | nil => simp [graftEnd, BinaryTree.numNodes]
  | node v a b _ ihb =>
    simp only [graftEnd, BinaryTree.numNodes, ihb]
    omega

lemma graftEnd_inj : ∀ {A A' L L' : T}, graftEnd A L = graftEnd A' L' → A = A' ∧ L = L' := by
  intro A
  induction A with
  | nil =>
    intro A' L L' h
    cases A' with
    | nil => simp only [graftEnd, BinaryTree.node.injEq] at h; exact ⟨rfl, h.2.1⟩
    | node v a b =>
      simp only [graftEnd, BinaryTree.node.injEq] at h
      exact absurd h.2.2.symm (graftEnd_ne_nil b L')
  | node v a b _ ihb =>
    intro A' L L' h
    cases A' with
    | nil =>
      simp only [graftEnd, BinaryTree.node.injEq] at h
      exact absurd h.2.2 (graftEnd_ne_nil b L)
    | node v' a' b' =>
      simp only [graftEnd, BinaryTree.node.injEq] at h
      obtain ⟨_, ha, hb⟩ := h
      obtain ⟨hb', hL⟩ := ihb hb
      subst ha; subst hb'
      cases v; cases v'
      exact ⟨rfl, hL⟩

/-- `chi` turns the right-spine length into the final stack height. -/
theorem rlen_chi (u : T) : rlen (chi u) = spine u := by
  induction u with
  | nil => rfl
  | node v a b _ ihb => simp only [chi, spine, rlen_graftEnd, ihb]

theorem numNodes_chi (u : T) : (chi u).numNodes = u.numNodes := by
  induction u with
  | nil => rfl
  | node v a b _ ihb =>
    simp only [chi, numNodes_graftEnd, ihb, BinaryTree.numNodes]

theorem chi_injective : Function.Injective chi := by
  intro u
  induction u with
  | nil =>
    intro u' h
    cases u' with
    | nil => rfl
    | node v a b => exact absurd h.symm (by simp only [chi]; exact graftEnd_ne_nil _ _)
  | node v a b _ ihb =>
    intro u' h
    cases u' with
    | nil => exact absurd h (by simp only [chi]; exact graftEnd_ne_nil _ _)
    | node v' a' b' =>
      simp only [chi] at h
      obtain ⟨ha, hb⟩ := graftEnd_inj h
      rw [ihb hb, ha]

/-- `chi` permutes the `n`-node trees. -/
theorem image_chi_trees (n : ℕ) :
    (BinaryTree.treesOfNumNodesEq n).image chi = BinaryTree.treesOfNumNodesEq n := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    rw [BinaryTree.mem_treesOfNumNodesEq] at hu ⊢
    rw [numNodes_chi, hu]
  · rw [Finset.card_image_of_injective _ chi_injective]

/-! ## The counts -/

/-- **Equidistribution, bijectively.**  On the `n`-node trees, the right-spine
    length and the final stack height (`rlen`) have the same counts. -/
theorem card_spine_eq_card_rlen (n m : ℕ) :
    ((BinaryTree.treesOfNumNodesEq n).filter (fun t => spine t = m)).card
      = ((BinaryTree.treesOfNumNodesEq n).filter (fun t => rlen t = m)).card := by
  conv_rhs => rw [← image_chi_trees n]
  rw [Finset.filter_image, Finset.card_image_of_injective _ chi_injective]
  congr 1
  apply Finset.filter_congr
  intro t _
  simp [rlen_chi]

/-- The final-stack-height count on trees is the codeword count `W` of Lemma 2. -/
theorem card_rlen_eq_W (n m : ℕ) (hn : 1 ≤ n) :
    ((BinaryTree.treesOfNumNodesEq n).filter (fun t => rlen t = m)).card = W (n - 1) 1 m := by
  have hcongr : (BinaryTree.treesOfNumNodesEq n).filter (fun t => rlen t = m)
      = (BinaryTree.treesOfNumNodesEq n).filter (fun t => finalH 1 (toPop t) = m) := by
    apply Finset.filter_congr
    intro t ht
    rw [BinaryTree.mem_treesOfNumNodesEq] at ht
    rw [finalH_toPop_eq_rlen t (ne_nil_of_numNodes hn ht)]
  have himg : ((BinaryTree.treesOfNumNodesEq n).filter
        (fun t => finalH 1 (toPop t) = m)).image toPop = hw (n - 1) 1 m := by
    have h1 : ((BinaryTree.treesOfNumNodesEq n).image toPop).filter (fun w => finalH 1 w = m)
        = ((BinaryTree.treesOfNumNodesEq n).filter
            (fun t => finalH 1 (toPop t) = m)).image toPop := by
      rw [Finset.filter_image]
    rw [← h1, image_toPop_eq_suffixes n hn]
    ext w
    rw [Finset.mem_filter, mem_suffixes, mem_hw]
    tauto
  rw [hcongr, ← card_hw, ← himg, Finset.card_image_of_injOn]
  exact (toPop_injOn n hn).mono (by intro t ht; exact (Finset.mem_filter.mp ht).1)

/-- **Lemma 3** (`lem:equidist`).  For `1 ≤ m ≤ n`, the number of `n`-node
    trees with `R + 1 = m` equals the number with final stack height `h = m`,
    and both equal the ballot number `B(n, m)`. -/
theorem lemma_equidist {n m : ℕ} (h1 : 1 ≤ m) (hmn : m ≤ n) :
    ((BinaryTree.treesOfNumNodesEq n).filter (fun t => rightPathLen t + 1 = m)).card
        = ((BinaryTree.treesOfNumNodesEq n).filter (fun t => finalH 1 (toPop t) = m)).card
      ∧ ((((BinaryTree.treesOfNumNodesEq n).filter
            (fun t => rightPathLen t + 1 = m)).card : ℕ) : ℝ) = ballot n m := by
  have hn : 1 ≤ n := le_trans h1 hmn
  have hR : (BinaryTree.treesOfNumNodesEq n).filter (fun t => rightPathLen t + 1 = m)
      = (BinaryTree.treesOfNumNodesEq n).filter (fun t => spine t = m) := by
    apply Finset.filter_congr
    intro t ht
    rw [BinaryTree.mem_treesOfNumNodesEq] at ht
    rw [spine_eq_rightPathLen_succ t (ne_nil_of_numNodes hn ht)]
  have hH : (BinaryTree.treesOfNumNodesEq n).filter (fun t => finalH 1 (toPop t) = m)
      = (BinaryTree.treesOfNumNodesEq n).filter (fun t => rlen t = m) := by
    apply Finset.filter_congr
    intro t ht
    rw [BinaryTree.mem_treesOfNumNodesEq] at ht
    rw [finalH_toPop_eq_rlen t (ne_nil_of_numNodes hn ht)]
  refine ⟨?_, ?_⟩
  · rw [hR, hH, card_spine_eq_card_rlen]
  · rw [hR, card_spine_eq_card_rlen, card_rlen_eq_W n m hn, W_cast_eq_ballot h1 hmn]

/-! ## Regression -/

/-- `chi` on the 3-node tree whose root has two children: spine 2, image has `rlen = 2`. -/
example : rlen (chi (.node () (.node () .nil .nil) (.node () .nil .nil))) = 2 := by decide

/-- The two statistics differ tree by tree (paper: the 3-node tree whose root has two
    children has `R + 1 = 2` but `h = 1`). -/
example : rightPathLen (.node () (.node () .nil .nil) (.node () .nil .nil)) + 1 = 2 ∧
    rlen (.node () (.node () .nil .nil) (.node () .nil .nil) : T) = 1 := by decide

end MakinenAnalysis
