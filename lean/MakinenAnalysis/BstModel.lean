import MakinenAnalysis.ExecBridge

/-!
# The random binary search tree model

The companion WiNF2026 manuscript on the random BST model (A2 below) studies the
two reconstruction algorithms under the *random BST model*: the keys `1, …, n`
are inserted in a uniformly random order.  The probability of a shape `t` is
then `∏_v 1/|t_v|` (product over the internal nodes of the subtree sizes); this
file calls that weight `bstW` and the corresponding expectation over the
`n`-node trees `bstE n`.

Ported from a separate Rocq development (not included in this artifact;
`BstStackHeight.v`, `BstStackHeightProof.v`), into the same Lean system as the
uniform model so that **one per-tree identity serves both models**: the final
stack height `h` here is the residue length `rlen` of `ExecModel` and the leaf
count `L` is `leaves` of `TreeIdentities`, exactly the statistics of
`ExecBridge.central_M_exec` / `central_N_exec`.

| here | Rocq | A2 |
|---|---|---|
| `bstE_one` | `mass_one` | the weights sum to one |
| `bst_Pge` | `law_general` | `P(h ≥ m) = 1/m!` |
| `bst_Eh`, `bst_Eh2` | `Eh_closed`, `Eh2_closed` | `E[h] = E_n`, `E[h²] = F_n` |

That `bstW` is the law of the shape produced by inserting a uniformly random
permutation is proved in `BstPerm` (`bst_perm_law`), A2's Lemma 1 (`h` and `L`
on the inverse permutation) in `BstLemma1`; the limit statements,
total variation and the gap `D` are in `BstLimits`, the central limit theorems
in `BstCLT`.
-/

namespace MakinenAnalysis

open Finset

/-! ## 1. The weight and the expectation -/

/-- The BST probability of a shape, `∏_v 1/|t_v|`. -/
def bstW : T → ℚ
  | .nil => 1
  | .node _ l r => bstW l * bstW r / ((l.numNodes + r.numNodes + 1 : ℕ) : ℚ)

/-- Expectation of `f` over the `n`-node trees under the BST weight. -/
def bstE (n : ℕ) (f : T → ℚ) : ℚ :=
  ∑ t ∈ BinaryTree.treesOfNumNodesEq n, bstW t * f t

/-- Shorthand for the trees with `n` internal nodes. -/
abbrev trees (n : ℕ) : Finset T := BinaryTree.treesOfNumNodesEq n

lemma bstE_zero (f : T → ℚ) : bstE 0 f = f .nil := by
  simp [bstE, bstW]

/-- **Root decomposition.**  The root splits an `(n+1)`-node tree into a left
    subtree with `i` nodes and a right one with `j` nodes, `i + j = n`, and the
    root contributes the factor `1/(n+1)`. -/
lemma bstE_succ (n : ℕ) (f : T → ℚ) :
    bstE (n + 1) f = (∑ p ∈ antidiagonal n, ∑ l ∈ trees p.1, ∑ r ∈ trees p.2,
        bstW l * bstW r * f (.node () l r)) / (n + 1) := by
  rw [bstE, BinaryTree.treesOfNumNodesEq_succ, Finset.sum_biUnion]
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.sum_map, Finset.sum_product, Finset.sum_div]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    rw [BinaryTree.mem_treesOfNumNodesEq] at hl hr
    have hp' : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
    show bstW (.node () l r) * f (.node () l r) = bstW l * bstW r * f (.node () l r) / (n + 1)
    rw [bstW, hl, hr, hp']
    push_cast
    ring
  · simp_rw [Set.PairwiseDisjoint, Set.Pairwise, Finset.disjoint_left]
    aesop

/-- Products separate. -/
lemma dsum_mul (i j : ℕ) (g k : T → ℚ) :
    ∑ l ∈ trees i, ∑ r ∈ trees j, bstW l * bstW r * (g l * k r) = bstE i g * bstE j k := by
  rw [bstE, bstE, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => by ring))

lemma bstE_add (n : ℕ) (f g : T → ℚ) : bstE n (fun t => f t + g t) = bstE n f + bstE n g := by
  simp only [bstE, mul_add, Finset.sum_add_distrib]

lemma bstE_smul (n : ℕ) (c : ℚ) (f : T → ℚ) : bstE n (fun t => c * f t) = c * bstE n f := by
  simp only [bstE, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

lemma bstE_congr {n : ℕ} {f g : T → ℚ} (h : ∀ t, t.numNodes = n → f t = g t) :
    bstE n f = bstE n g :=
  Finset.sum_congr rfl (fun t ht => by rw [h t (BinaryTree.mem_treesOfNumNodesEq.mp ht)])

lemma bstE_sum (n : ℕ) (s : Finset ℕ) (f : ℕ → T → ℚ) :
    bstE n (fun t => ∑ m ∈ s, f m t) = ∑ m ∈ s, bstE n (f m) := by
  simp only [bstE, Finset.mul_sum]
  exact Finset.sum_comm

/-- **The weights sum to one** (Rocq: `mass_one`). -/
theorem bstE_one (n : ℕ) : bstE n (fun _ => 1) = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [bstE_zero]
    | succ n =>
      rw [bstE_succ]
      have : ∀ p ∈ antidiagonal n, (∑ l ∈ trees p.1, ∑ r ∈ trees p.2,
          bstW l * bstW r * (fun _ : T => (1 : ℚ)) (.node () l r)) = 1 := by
        intro p hp
        have h1 := ih p.1 (by have := Finset.antidiagonal.fst_le hp; omega)
        have h2 := ih p.2 (by have := Finset.antidiagonal.snd_le hp; omega)
        have := dsum_mul p.1 p.2 (fun _ => 1) (fun _ => 1)
        simp only [mul_one] at this ⊢
        rw [this, h1, h2, mul_one]
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
      push_cast
      field_simp

/-! ## 2. The final stack height `h = rlen` -/

lemma rlen_node (v : Unit) (l r : T) :
    rlen (.node v l r) = if r.numNodes = 0 then rlen l + 1 else rlen r := by
  cases r with
  | nil => simp [rlen_node_nil]
  | node _ _ _ => simp [rlen_node_node, BinaryTree.numNodes]

lemma rlen_le_numNodes (t : T) : rlen t ≤ t.numNodes := by
  have := Srec_add_rlen t; omega

/-- `P(h ≥ m)` for the `n`-node BST. -/
def bstPge (n m : ℕ) : ℚ := bstE n (fun t => if m ≤ rlen t then 1 else 0)

lemma count_le (n m : ℕ) (c : ℚ) :
    ∑ k ∈ range n, (if m ≤ k then c else 0) = ((n - m : ℕ) : ℚ) * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : m ≤ n
    · rw [if_pos h, show n + 1 - m = (n - m) + 1 by omega]; push_cast; ring
    · rw [if_neg h, show n + 1 - m = 0 by omega, show n - m = 0 by omega]; simp

lemma count_ge (n m : ℕ) (c : ℚ) :
    ∑ k ∈ range n, (if m + 1 ≤ n - k then c else 0) = ((n - m : ℕ) : ℚ) * c := by
  rw [← Finset.sum_range_reflect, ← count_le]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have := Finset.mem_range.mp hk
  congr 1
  apply propext; omega

/-- **`P(h ≥ m) = 1/m!`** for `m ≤ n`, and `0` beyond (Rocq: `law_general`,
    `Pge_zero`).  A2: the distribution of `h` is Knuth's law of the first run. -/
theorem bst_Pge (n m : ℕ) :
    bstPge n m = if m ≤ n then 1 / (m.factorial : ℚ) else 0 := by
  induction n using Nat.strong_induction_on generalizing m with
  | _ n ih' =>
  cases n with
  | zero =>
    rw [bstPge, bstE_zero]
    by_cases h : m = 0
    · subst h; simp
    · simp [h]
  | succ n =>
    have ih : ∀ k ≤ n, ∀ m, bstPge k m = if m ≤ k then 1 / (m.factorial : ℚ) else 0 :=
      fun k hk m => ih' k (by omega) m
    cases m with
    | zero =>
      have := bstE_one (n + 1)
      simp only [bstPge, Nat.zero_le, if_true, Nat.factorial_zero, Nat.cast_one, div_one]
      exact this
    | succ m =>
      rw [bstPge, bstE_succ]
      have hin : ∀ p ∈ antidiagonal n, (∑ l ∈ trees p.1, ∑ r ∈ trees p.2,
          bstW l * bstW r * (fun t : T => if m + 1 ≤ rlen t then (1 : ℚ) else 0) (.node () l r))
            = if p.2 = 0 then bstPge p.1 m else bstPge p.2 (m + 1) := by
        intro p _
        by_cases h0 : p.2 = 0
        · rw [if_pos h0]
          have := dsum_mul p.1 p.2 (fun t => if m ≤ rlen t then 1 else 0) (fun _ => 1)
          rw [bstE_one, mul_one] at this
          rw [bstPge, ← this]
          refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r hr => ?_))
          rw [BinaryTree.mem_treesOfNumNodesEq] at hr
          simp only [rlen_node, hr, h0, if_true, mul_one]
          congr 1
          by_cases hm : m ≤ rlen l
          · rw [if_pos hm, if_pos (by omega)]
          · rw [if_neg hm, if_neg (by omega)]
        · rw [if_neg h0]
          have := dsum_mul p.1 p.2 (fun _ => 1) (fun t => if m + 1 ≤ rlen t then 1 else 0)
          rw [bstE_one, one_mul] at this
          rw [bstPge, ← this]
          refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r hr => ?_))
          rw [BinaryTree.mem_treesOfNumNodesEq] at hr
          simp only [rlen_node, hr, h0, if_false, one_mul]
      rw [Finset.sum_congr rfl hin, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => if j = 0 then bstPge i m else bstPge j (m + 1)), Finset.sum_range_succ]
      simp only [Nat.sub_self, if_true]
      have hk : ∀ k ∈ range n, (if n - k = 0 then bstPge k m else bstPge (n - k) (m + 1))
          = if m + 1 ≤ n - k then 1 / ((m + 1).factorial : ℚ) else 0 := by
        intro k hk
        have := Finset.mem_range.mp hk
        rw [if_neg (by omega), ih _ (by omega)]
      rw [Finset.sum_congr rfl hk, count_ge, ih n le_rfl]
      by_cases h : m ≤ n
      · rw [if_pos h, if_pos (by omega), Nat.cast_sub h, Nat.factorial_succ]
        push_cast
        field_simp
        ring
      · rw [if_neg h, if_neg (by omega), show n - m = 0 by omega]
        simp

/-! ## 3. The moments of `h` by the layer-cake formula -/

/-- `E_n = Σ_{m=1}^n 1/m!`. -/
def Ee (n : ℕ) : ℚ := ∑ m ∈ range n, 1 / ((m + 1).factorial : ℚ)

/-- `F_n = Σ_{m=1}^n (2m-1)/m!`. -/
def Fe (n : ℕ) : ℚ := ∑ m ∈ range n, (2 * m + 1) / ((m + 1).factorial : ℚ)

lemma layer_h (N : ℕ) (t : T) (h : rlen t ≤ N) :
    (rlen t : ℚ) = ∑ m ∈ range N, (if m + 1 ≤ rlen t then 1 else 0) := by
  induction N with
  | zero => simp at h; simp [h]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    by_cases hN : N + 1 ≤ rlen t
    · have : rlen t = N + 1 := by omega
      rw [if_pos hN]
      have hs : ∑ m ∈ range N, (if m + 1 ≤ rlen t then (1 : ℚ) else 0) = N := by
        rw [Finset.sum_congr rfl (fun m hm => if_pos (by have := Finset.mem_range.mp hm; omega))]
        simp
      rw [hs, this]; push_cast; ring
    · rw [if_neg hN, add_zero]; exact ih (by omega)

lemma layer_h2 (N : ℕ) (t : T) (h : rlen t ≤ N) :
    (rlen t : ℚ) ^ 2 = ∑ m ∈ range N, (2 * (m : ℚ) + 1) * (if m + 1 ≤ rlen t then 1 else 0) := by
  induction N with
  | zero => simp at h; simp [h]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    by_cases hN : N + 1 ≤ rlen t
    · have : rlen t = N + 1 := by omega
      rw [if_pos hN]
      have hs : ∑ m ∈ range N, (2 * (m : ℚ) + 1) * (if m + 1 ≤ rlen t then (1 : ℚ) else 0)
          = (N : ℚ) ^ 2 := by
        rw [Finset.sum_congr rfl (fun m hm => by
          rw [if_pos (by have := Finset.mem_range.mp hm; omega), mul_one])]
        clear ih h hN this
        induction N with
        | zero => simp
        | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
      rw [hs, this]; push_cast; ring
    · rw [if_neg hN, mul_zero, add_zero]; exact ih (by omega)

/-- **`E[h] = E_n`** (Rocq: `Eh_closed`). -/
theorem bst_Eh (n : ℕ) : bstE n (fun t => (rlen t : ℚ)) = Ee n := by
  rw [bstE_congr (g := fun t => ∑ m ∈ range n, (if m + 1 ≤ rlen t then (1 : ℚ) else 0))
    (fun t ht => layer_h n t (by have := rlen_le_numNodes t; omega)), bstE_sum, Ee]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have := Finset.mem_range.mp hm
  rw [show bstE n (fun t => if m + 1 ≤ rlen t then (1 : ℚ) else 0) = bstPge n (m + 1) from rfl,
    bst_Pge, if_pos (by omega)]

/-- **`E[h²] = F_n`** (Rocq: `Eh2_closed`). -/
theorem bst_Eh2 (n : ℕ) : bstE n (fun t => (rlen t : ℚ) ^ 2) = Fe n := by
  rw [bstE_congr (g := fun t => ∑ m ∈ range n,
      (2 * (m : ℚ) + 1) * (if m + 1 ≤ rlen t then (1 : ℚ) else 0))
    (fun t ht => layer_h2 n t (by have := rlen_le_numNodes t; omega)), bstE_sum, Fe]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have := Finset.mem_range.mp hm
  rw [bstE_smul,
    show bstE n (fun t => if m + 1 ≤ rlen t then (1 : ℚ) else 0) = bstPge n (m + 1) from rfl,
    bst_Pge, if_pos (by omega)]
  ring

/-! ## 4. Elementary closed forms

Everything the moment recursions of §5 need, as identities between explicit
rational expressions in `n`, `E_n` and `1/n!`, each proved by induction. -/

lemma Ee_succ (n : ℕ) : Ee (n + 1) = Ee n + 1 / ((n + 1).factorial : ℚ) := by
  rw [Ee, Finset.sum_range_succ]; rfl

lemma Fe_succ (n : ℕ) : Fe (n + 1) = Fe n + (2 * n + 1) / ((n + 1).factorial : ℚ) := by
  rw [Fe, Finset.sum_range_succ]; rfl

lemma fact_succ_q (n : ℕ) : ((n + 1).factorial : ℚ) = (n + 1) * n.factorial := by
  rw [Nat.factorial_succ]; push_cast; ring

lemma fact_ne_zero_q (n : ℕ) : (n.factorial : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)

/-- `E[L_n]`: `0`, `1`, then `(n+1)/3` from `n = 2` on. -/
def eC : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | n + 2 => ((n : ℚ) + 3) / 3

lemma sum_anti_fst (n : ℕ) (g : ℕ → ℚ) :
    ∑ p ∈ antidiagonal n, g p.1 = ∑ k ∈ range (n + 1), g k := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

lemma sum_anti_snd (n : ℕ) (g : ℕ → ℚ) :
    ∑ p ∈ antidiagonal n, g p.2 = ∑ k ∈ range (n + 1), g k := by
  rw [← Finset.Nat.sum_antidiagonal_swap, ← sum_anti_fst]
  rfl

lemma sum_eC (n : ℕ) :
    ∑ k ∈ range (n + 2), eC k = ((n : ℚ) + 1) ^ 2 / 6 + ((n : ℚ) + 1) / 2 + 1 / 3 := by
  induction n with
  | zero => simp [Finset.sum_range_succ, eC]; norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    show _ + ((n : ℚ) + 3) / 3 = _
    push_cast; ring

/-- `Σ_{i+j=n} (i+1) g(j)`. -/
def conv1 (n : ℕ) (g : ℕ → ℚ) : ℚ := ∑ p ∈ antidiagonal n, ((p.1 : ℚ) + 1) * g p.2

lemma conv1_succ (n : ℕ) (g : ℕ → ℚ) :
    conv1 (n + 1) g = g (n + 1) + conv1 n g + ∑ k ∈ range (n + 1), g k := by
  rw [conv1, Finset.Nat.sum_antidiagonal_succ, conv1, ← sum_anti_snd]
  have : ∀ p ∈ antidiagonal n, (((p.1 + 1 : ℕ) : ℚ) + 1) * g p.2
      = ((p.1 : ℚ) + 1) * g p.2 + g p.2 := fun p _ => by push_cast; ring
  simp only at this ⊢
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
  push_cast; ring

lemma conv1_eC (n : ℕ) :
    conv1 n eC = (n : ℚ) ^ 3 / 18 + (n : ℚ) ^ 2 / 3 + 11 * (n : ℚ) / 18 := by
  induction n with
  | zero => simp [conv1, eC]
  | succ n ih =>
    rw [conv1_succ, ih]
    cases n with
    | zero => simp [eC]; norm_num
    | succ n =>
      rw [sum_eC]
      show ((n : ℚ) + 3) / 3 + _ + _ = _
      push_cast; ring

lemma eC_add_two (n : ℕ) : eC (n + 2) = ((n : ℚ) + 3) / 3 := rfl

lemma anti_ite0 (n : ℕ) (c : ℕ → ℚ) :
    ∑ p ∈ antidiagonal n, (if p.1 = 0 then c p.2 else 0) = c n := by
  rw [Finset.sum_eq_single (0, n)]
  · simp
  · intro p hp hne
    have := Finset.mem_antidiagonal.mp hp
    rw [if_neg]
    intro h0
    apply hne
    ext <;> simp <;> omega
  · intro h; exact absurd (Finset.mem_antidiagonal.mpr (by simp)) h

lemma anti_ite1 (n : ℕ) (c : ℕ → ℚ) :
    ∑ p ∈ antidiagonal (n + 1), (if p.1 = 1 then c p.2 else 0) = c n := by
  rw [Finset.sum_eq_single (1, n)]
  · simp
  · intro p hp hne
    have := Finset.mem_antidiagonal.mp hp
    rw [if_neg]
    intro h0
    apply hne
    ext <;> simp <;> omega
  · intro h; exact absurd (Finset.mem_antidiagonal.mpr (by simp; omega)) h

/-- `eC` is `(i+1)/3` up to a correction at `i = 0, 1`, which turns any
    convolution with `eC` into one with `i + 1`. -/
lemma conv_eC (n : ℕ) (g : ℕ → ℚ) :
    ∑ p ∈ antidiagonal (n + 1), eC p.1 * g p.2
      = conv1 (n + 1) g / 3 - g (n + 1) / 3 + g n / 3 := by
  have key : ∀ p ∈ antidiagonal (n + 1), eC p.1 * g p.2
      = ((p.1 : ℚ) + 1) * g p.2 / 3
        + ((if p.1 = 0 then -(1 / 3 : ℚ) * g p.2 else 0)
          + (if p.1 = 1 then (1 / 3 : ℚ) * g p.2 else 0)) := by
    rintro ⟨i, j⟩ _
    match i with
    | 0 => simp [eC]; ring
    | 1 => simp [eC]; ring
    | i + 2 => simp [eC]; ring
  have h0 := anti_ite0 (n + 1) (fun j => -(1 / 3 : ℚ) * g j)
  have h1 := anti_ite1 n (fun j => (1 / 3 : ℚ) * g j)
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_add_distrib, h0, h1, conv1,
    Finset.sum_div]
  ring

lemma conv_eC_eC (n : ℕ) (hn : 3 ≤ n) :
    ∑ p ∈ antidiagonal n, eC p.1 * eC p.2
      = (n : ℚ) ^ 3 / 54 + (n : ℚ) ^ 2 / 9 + 11 * (n : ℚ) / 54 - 1 / 9 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 = (m + 2) + 1 by omega, conv_eC, conv1_eC,
    show m + 2 + 1 = (m + 1) + 2 by omega, eC_add_two, eC_add_two]
  push_cast; ring

/-- `E[L_n²]`: `0, 1, 1, 2`, then `(n+1)²/9 + 2(n+1)/45`. -/
def sC : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | n + 4 => ((n : ℚ) + 4) ^ 2 / 9 + 4 * ((n : ℚ) + 4) / 15 + 7 / 45

lemma sC_add_four (n : ℕ) :
    sC (n + 4) = ((n : ℚ) + 4) ^ 2 / 9 + 4 * ((n : ℚ) + 4) / 15 + 7 / 45 := rfl

lemma sum_sC (n : ℕ) :
    ∑ k ∈ range (n + 4), sC k = ((n : ℚ) + 3) ^ 3 / 27 + 17 * ((n : ℚ) + 3) ^ 2 / 90
      + 83 * ((n : ℚ) + 3) / 270 + 17 / 45 := by
  induction n with
  | zero => simp [Finset.sum_range_succ, sC]; norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    show _ + (((n : ℚ) + 4) ^ 2 / 9 + 4 * ((n : ℚ) + 4) / 15 + 7 / 45) = _
    push_cast; ring

lemma sum_Ee (n : ℕ) :
    ∑ k ∈ range (n + 1), Ee k = n * Ee n + 1 / (n.factorial : ℚ) - 1 := by
  induction n with
  | zero => simp [Ee]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Ee_succ, fact_succ_q]
    have := fact_ne_zero_q n
    push_cast
    field_simp
    ring

lemma conv1_Ee (n : ℕ) :
    conv1 n Ee = Ee n * ((n : ℚ) ^ 2 + n + 1) / 2 - n + ((n : ℚ) + 1) / (2 * n.factorial) - 1 / 2 := by
  induction n with
  | zero => simp [conv1, Ee]
  | succ n ih =>
    rw [conv1_succ, ih, sum_Ee, Ee_succ, fact_succ_q]
    have := fact_ne_zero_q n
    push_cast
    field_simp
    ring

/-- The convolution `Σ_{i+j=n} E[L_i] E_j` (`n ≥ 1`). -/
lemma conv_eC_Ee (n : ℕ) :
    ∑ p ∈ antidiagonal (n + 1), eC p.1 * Ee p.2
      = Ee (n + 1) * (((n : ℚ) + 1) ^ 2 + (n + 1) + 1) / 6 - ((n : ℚ) + 1) / 3
        + (n : ℚ) / (6 * (n + 1).factorial) - 1 / 6 := by
  rw [conv_eC, conv1_Ee, Ee_succ, fact_succ_q]
  have := fact_ne_zero_q n
  push_cast
  field_simp
  ring

/-- `E[h_n L_n]`: `0`, `1`, then `((2n-3)E_n + 7)/6 - (n-3)/(6 n!)`. -/
def cC : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | n + 2 => ((2 * ((n : ℚ) + 2) - 3) * Ee (n + 2) + 7) / 6
      - ((n : ℚ) + 2 - 3) / (6 * (n + 2).factorial)

lemma sum_cC (n : ℕ) :
    ∑ k ∈ range (n + 2), cC k = Ee (n + 1) * (n : ℚ) ^ 2 / 6 + 7 * ((n : ℚ) + 1) / 6
      + (n : ℚ) / (6 * (n + 1).factorial) - 1 / 6 := by
  induction n with
  | zero => simp [Finset.sum_range_succ, cC, Ee]; norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    show _ + (((2 * (((n : ℕ) : ℚ) + 2) - 3) * Ee (n + 2) + 7) / 6
      - (((n : ℕ) : ℚ) + 2 - 3) / (6 * (n + 2).factorial)) = _
    rw [Ee_succ (n + 1), fact_succ_q (n + 1)]
    have := fact_ne_zero_q (n + 1)
    push_cast
    field_simp
    ring

/-! ## 5. The leaf count `L` and the joint moment `E[hL]` -/

lemma leaves_node (v : Unit) (l r : T) :
    (leaves (.node v l r) : ℚ)
      = leaves l + leaves r + (if l.numNodes + r.numNodes = 0 then 1 else 0) := by
  cases l <;> cases r <;> simp [leaves, isNode, BinaryTree.numNodes]

lemma dsum_fst (i j : ℕ) (g : T → ℚ) :
    ∑ l ∈ trees i, ∑ r ∈ trees j, bstW l * bstW r * g l = bstE i g := by
  have := dsum_mul i j g (fun _ => 1)
  rw [bstE_one, mul_one] at this
  rw [← this]; simp only [mul_one]

lemma dsum_snd (i j : ℕ) (g : T → ℚ) :
    ∑ l ∈ trees i, ∑ r ∈ trees j, bstW l * bstW r * g r = bstE j g := by
  have := dsum_mul i j (fun _ => 1) g
  rw [bstE_one, one_mul] at this
  rw [← this]; simp only [one_mul]

lemma dsum_add (i j : ℕ) (F G : T → T → ℚ) :
    ∑ l ∈ trees i, ∑ r ∈ trees j, bstW l * bstW r * (F l r + G l r)
      = ∑ l ∈ trees i, ∑ r ∈ trees j, bstW l * bstW r * F l r
        + ∑ l ∈ trees i, ∑ r ∈ trees j, bstW l * bstW r * G l r := by
  simp only [mul_add, Finset.sum_add_distrib]

lemma dsum_congr {i j : ℕ} {F G : T → T → ℚ}
    (h : ∀ l r, l.numNodes = i → r.numNodes = j → F l r = G l r) :
    ∑ l ∈ trees i, ∑ r ∈ trees j, bstW l * bstW r * F l r
      = ∑ l ∈ trees i, ∑ r ∈ trees j, bstW l * bstW r * G l r :=
  Finset.sum_congr rfl (fun l hl => Finset.sum_congr rfl (fun r hr => by
    rw [h l r (BinaryTree.mem_treesOfNumNodesEq.mp hl) (BinaryTree.mem_treesOfNumNodesEq.mp hr)]))

/-- `E[L_n]` -/
def bstEL (n : ℕ) : ℚ := bstE n (fun t => (leaves t : ℚ))

/-- **`E[L_n] = (n+1)/3` for `n ≥ 2`** (Rocq: `EL_closed`). -/
theorem bst_EL (n : ℕ) : bstEL n = eC n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  match n with
  | 0 => simp [bstEL, bstE_zero, eC]
  | 1 => simp [bstEL, bstE_succ, bstW, leaves, isNode, eC]
  | m + 2 =>
    rw [bstEL, bstE_succ]
    have hin : ∀ p ∈ antidiagonal (m + 1), (∑ l ∈ trees p.1, ∑ r ∈ trees p.2,
        bstW l * bstW r * (fun t : T => (leaves t : ℚ)) (.node () l r))
          = bstEL p.1 + bstEL p.2 := by
      intro p hp
      have hp' : p.1 + p.2 = m + 1 := Finset.mem_antidiagonal.mp hp
      rw [dsum_congr (G := fun l r => (leaves l : ℚ) + leaves r) (fun l r hl hr => by
        simp only [leaves_node, hl, hr, hp', add_eq_zero, one_ne_zero, and_false, if_false,
          add_zero]), dsum_add, dsum_fst, dsum_snd]
      rfl
    rw [Finset.sum_congr rfl hin, Finset.sum_add_distrib, sum_anti_fst, sum_anti_snd]
    have hs : ∑ k ∈ range (m + 1 + 1), bstEL k = ∑ k ∈ range (m + 2), eC k :=
      Finset.sum_congr rfl (fun k hk => ih k (by have := Finset.mem_range.mp hk; omega))
    rw [hs, sum_eC]
    show _ = ((m : ℚ) + 3) / 3
    push_cast
    field_simp
    ring

/-- `E[L_n²]` -/
def bstEL2 (n : ℕ) : ℚ := bstE n (fun t => (leaves t : ℚ) ^ 2)

lemma bstEL2_succ (m : ℕ) :
    bstEL2 (m + 2) = (2 * ∑ k ∈ range (m + 2), bstEL2 k
      + 2 * ∑ p ∈ antidiagonal (m + 1), eC p.1 * eC p.2) / (m + 2) := by
  rw [bstEL2, bstE_succ]
  have hin : ∀ p ∈ antidiagonal (m + 1), (∑ l ∈ trees p.1, ∑ r ∈ trees p.2,
      bstW l * bstW r * (fun t : T => (leaves t : ℚ) ^ 2) (.node () l r))
        = bstEL2 p.1 + bstEL2 p.2 + 2 * (eC p.1 * eC p.2) := by
    intro p hp
    have hp' : p.1 + p.2 = m + 1 := Finset.mem_antidiagonal.mp hp
    rw [dsum_congr (G := fun l r => ((leaves l : ℚ) ^ 2 + (leaves r : ℚ) ^ 2)
        + 2 * ((leaves l : ℚ) * (leaves r : ℚ))) (fun l r hl hr => by
      simp only [leaves_node, hl, hr, hp', add_eq_zero, one_ne_zero, and_false, if_false,
        add_zero]; ring), dsum_add, dsum_add, dsum_fst, dsum_snd]
    have := dsum_mul p.1 p.2 (fun t => (leaves t : ℚ)) (fun t => (leaves t : ℚ))
    rw [show (∑ l ∈ trees p.1, ∑ r ∈ trees p.2, bstW l * bstW r * (2 * ((leaves l : ℚ) * leaves r)))
        = 2 * ∑ l ∈ trees p.1, ∑ r ∈ trees p.2, bstW l * bstW r * ((leaves l : ℚ) * leaves r) by
      simp only [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ =>
        Finset.sum_congr rfl (fun _ _ => by ring)), this]
    rw [← bstEL, ← bstEL, bst_EL, bst_EL]
    rfl
  rw [Finset.sum_congr rfl hin, Finset.sum_add_distrib, Finset.sum_add_distrib, sum_anti_fst,
    sum_anti_snd, ← Finset.mul_sum]
  push_cast
  ring

/-- **`E[L_n²] = (n+1)²/9 + 2(n+1)/45` for `n ≥ 4`.** -/
theorem bst_EL2 (n : ℕ) : bstEL2 n = sC n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  match n with
  | 0 => simp [bstEL2, bstE_zero, sC]
  | 1 => simp [bstEL2, bstE_succ, bstW, leaves, isNode, sC]
  | m + 2 =>
    rw [bstEL2_succ]
    have hs : ∑ k ∈ range (m + 2), bstEL2 k = ∑ k ∈ range (m + 2), sC k :=
      Finset.sum_congr rfl (fun k hk => ih k (by have := Finset.mem_range.mp hk; omega))
    rw [hs]
    match m with
    | 0 => norm_num [Finset.sum_range_succ, Finset.Nat.antidiagonal_succ, sC, eC]
    | 1 => norm_num [Finset.sum_range_succ, Finset.Nat.antidiagonal_succ, sC, eC]
    | k + 2 =>
      rw [show k + 2 + 2 = k + 4 by omega, sum_sC, show k + 2 + 1 = k + 3 by omega,
        conv_eC_eC (k + 3) (by omega)]
      rw [sC_add_four]
      push_cast
      field_simp
      ring

/-- **`Var[L_n] = 2(n+1)/45` for `n ≥ 4`** (Rocq: `VarL_closed`). -/
theorem bst_VarL (n : ℕ) (hn : 4 ≤ n) :
    bstEL2 n - bstEL n ^ 2 = 2 * ((n : ℚ) + 1) / 45 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [bst_EL2, bst_EL, sC_add_four, show m + 4 = (m + 2) + 2 by omega, eC_add_two]
  push_cast; ring

/-- `E[h_n L_n]` -/
def bstEhL (n : ℕ) : ℚ := bstE n (fun t => (rlen t : ℚ) * leaves t)

lemma nil_of_numNodes_zero {t : T} (h : t.numNodes = 0) : t = .nil := by
  cases t with
  | nil => rfl
  | node _ _ _ => simp [BinaryTree.numNodes] at h

lemma bstEhL_succ (m : ℕ) :
    bstEhL (m + 2) = (bstEhL (m + 1) + eC (m + 1)
      + ∑ p ∈ antidiagonal (m + 1), eC p.1 * Ee p.2
      + ∑ k ∈ range (m + 2), bstEhL k) / (m + 2) := by
  rw [bstEhL, bstE_succ]
  have hin : ∀ p ∈ antidiagonal (m + 1), (∑ l ∈ trees p.1, ∑ r ∈ trees p.2,
      bstW l * bstW r * (fun t : T => (rlen t : ℚ) * leaves t) (.node () l r))
        = if p.2 = 0 then bstEhL p.1 + eC p.1 else eC p.1 * Ee p.2 + bstEhL p.2 := by
    intro p hp
    have hp' : p.1 + p.2 = m + 1 := Finset.mem_antidiagonal.mp hp
    by_cases h0 : p.2 = 0
    · have hp1 : p.1 ≠ 0 := by omega
      rw [if_pos h0, dsum_congr (G := fun l r => (rlen l : ℚ) * leaves l + leaves l)
        (fun l r hl hr => by
          have hrn := nil_of_numNodes_zero (hr.trans h0)
          subst hrn
          simp only [rlen_node, leaves_node, hl, BinaryTree.numNodes, if_true, hp1, if_false,
            add_zero, leaves_nil, Nat.cast_zero]
          push_cast; ring),
        dsum_add, dsum_fst, dsum_fst, ← bst_EL]
      rfl
    · rw [if_neg h0, dsum_congr (G := fun l r => (leaves l : ℚ) * rlen r + (rlen r : ℚ) * leaves r)
        (fun l r hl hr => by
          simp only [rlen_node, leaves_node, hl, hr, h0, if_false, hp',
            add_eq_zero, one_ne_zero, and_false, add_zero]
          ring),
        dsum_add, dsum_snd, dsum_mul, bst_Eh, ← bstEL, bst_EL]
      rfl
  rw [Finset.sum_congr rfl hin, Finset.Nat.sum_antidiagonal_succ']
  simp only [if_true, Nat.add_one_ne_zero, if_false]
  have hz : ∑ p ∈ antidiagonal (m + 1), (eC p.1 * Ee p.2 + bstEhL p.2)
      = ∑ p ∈ antidiagonal m, (eC p.1 * Ee (p.2 + 1) + bstEhL (p.2 + 1)) := by
    rw [Finset.Nat.sum_antidiagonal_succ']
    simp [Ee, bstEhL, bstE_zero]
  rw [← hz, Finset.sum_add_distrib, sum_anti_snd]
  push_cast
  ring

/-- **`E[h_n L_n] = ((2n-3)E_n + 7)/6 - (n-3)/(6 n!)` for `n ≥ 2`**
    (Rocq: `Ehl_closed`). -/
theorem bst_EhL (n : ℕ) : bstEhL n = cC n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  match n with
  | 0 => simp [bstEhL, bstE_zero, cC]
  | 1 => simp [bstEhL, bstE_succ, bstW, leaves, isNode, rlen, cC]
  | m + 2 =>
    rw [bstEhL_succ, ih (m + 1) (by omega)]
    have hs : ∑ k ∈ range (m + 2), bstEhL k = ∑ k ∈ range (m + 2), cC k :=
      Finset.sum_congr rfl (fun k hk => ih k (by have := Finset.mem_range.mp hk; omega))
    rw [hs, sum_cC, conv_eC_Ee]
    match m with
    | 0 => simp [cC, eC, Ee, Finset.sum_range_succ, Nat.factorial]; norm_num
    | k + 1 =>
      show (cC (k + 2) + eC (k + 2) + _ + _) / _ = cC (k + 1 + 2)
      simp only [cC, eC_add_two]
      rw [show k + 1 + 2 = (k + 2) + 1 by omega, Ee_succ (k + 2), fact_succ_q (k + 2)]
      have := fact_ne_zero_q (k + 2)
      push_cast
      field_simp
      ring

/-- **`Cov(h, L) = 7/6 - (5/6) E_n - (n-3)/(6·n!)` for `n ≥ 2`** (Rocq: `Covq_closed`).
    The closed form stated in A2. -/
theorem bst_CovhL (n : ℕ) (hn : 2 ≤ n) :
    bstEhL n - Ee n * bstEL n = 7 / 6 - 5 / 6 * Ee n - ((n : ℚ) - 3) / (6 * n.factorial) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [bst_EhL, bst_EL, eC_add_two]
  simp only [cC]
  push_cast
  ring

/-- **`Var[h] = F_n - E_n²`** (Rocq: `Varh_closed`). -/
theorem bst_Varh (n : ℕ) :
    bstE n (fun t => (rlen t : ℚ) ^ 2) - bstE n (fun t => (rlen t : ℚ)) ^ 2 = Fe n - Ee n ^ 2 := by
  rw [bst_Eh, bst_Eh2]

/-! ## 6. One identity, two models: the comparison counts under the BST model

`ExecBridge.central_M_exec` and `central_N_exec` are statements about a single
tree: `A_M + h + 1 = 3n` and `A_N + h = 2n + 1 + L`, where `A_M`, `A_N` are the
comparison counters of the runs of the two algorithms on the tree's i-p sequence.
The uniform-model theorems of `ExecBridge` average them over the Catalan trees;
the theorems below average the *same* identities under the BST weight.  Nothing
about the algorithms is re-proved here. -/

/-- The stack height of the codeword side is the residue length used above. -/
lemma finalH_toPop_eq_rlen (t : T) (h : t ≠ .nil) : finalH 1 (toPop t) = rlen t := by
  have h1 := finalH_add_sum_numNodes t h
  have h2 := Srec_add_rlen t
  rw [sum_toPop_eq_Srec] at h1
  omega

lemma ne_nil_of_numNodes {t : T} {n : ℕ} (hn : 1 ≤ n) (ht : t.numNodes = n) : t ≠ .nil := by
  rintro rfl; simp [BinaryTree.numNodes] at ht; omega

/-- `A_M = 3n - 1 - h` on every tree, in `ℚ`. -/
lemma cmpsM_q (t : T) (h : t ≠ .nil) :
    (cmpsM (ip t) : ℚ) = 3 * t.numNodes - 1 - rlen t := by
  have := central_M_exec t h
  rw [finalH_toPop_eq_rlen t h] at this
  have hq : ((cmpsM (ip t) + rlen t + 1 : ℕ) : ℚ) = ((3 * t.numNodes : ℕ) : ℚ) := by rw [this]
  push_cast at hq
  linarith

/-- `A_N = 2n + 1 - h + L` on every tree, in `ℚ`. -/
lemma cmpsN_q (t : T) (h : t ≠ .nil) :
    (cmpsN (ip t) : ℚ) = 2 * t.numNodes + 1 - rlen t + leaves t := by
  have := central_N_exec t h
  rw [finalH_toPop_eq_rlen t h] at this
  have hq : ((cmpsN (ip t) + rlen t : ℕ) : ℚ) = ((2 * t.numNodes + 1 + leaves t : ℕ) : ℚ) := by
    rw [this]
  push_cast at hq
  linarith

lemma bstE_const (n : ℕ) (a : ℚ) : bstE n (fun _ => a) = a := by
  have := bstE_smul n a (fun _ => 1)
  simp only [mul_one] at this
  rw [this, bstE_one, mul_one]

lemma bstE_sub (n : ℕ) (f g : T → ℚ) : bstE n (fun t => f t - g t) = bstE n f - bstE n g := by
  simp only [bstE, mul_sub, Finset.sum_sub_distrib]

/-- **`E[A_M] = 3n - 1 - E_n`** under the BST model (`n ≥ 1`). -/
theorem bst_EAM (n : ℕ) (hn : 1 ≤ n) :
    bstE n (fun t => (cmpsM (ip t) : ℚ)) = 3 * n - 1 - Ee n := by
  rw [bstE_congr (g := fun t => ((3 * n - 1 : ℚ)) - rlen t) (fun t ht => by
    rw [cmpsM_q t (ne_nil_of_numNodes hn ht), ht]), bstE_sub, bstE_const, bst_Eh]

/-- **`E[A_N] = (7n+4)/3 - E_n`** under the BST model (`n ≥ 2`). -/
theorem bst_EAN (n : ℕ) (hn : 2 ≤ n) :
    bstE n (fun t => (cmpsN (ip t) : ℚ)) = (7 * n + 4) / 3 - Ee n := by
  rw [bstE_congr (g := fun t => ((2 * n + 1 : ℚ)) - rlen t + leaves t) (fun t ht => by
    rw [cmpsN_q t (ne_nil_of_numNodes (by omega) ht), ht]), bstE_add, bstE_sub, bstE_const,
    bst_Eh, show bstE n (fun t => (leaves t : ℚ)) = bstEL n from rfl, bst_EL]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [eC_add_two]; push_cast; ring

/-- **`Var[A_N]`** under the BST model, `n ≥ 4` (A2, Theorem 1):
    `2(n+1)/45 + F_n - E_n² - 7/3 + (5/3)E_n + (n-3)/(3·n!)`. -/
theorem bst_VarAN (n : ℕ) (hn : 4 ≤ n) :
    bstE n (fun t => (cmpsN (ip t) : ℚ) ^ 2) - bstE n (fun t => (cmpsN (ip t) : ℚ)) ^ 2
      = 2 * ((n : ℚ) + 1) / 45 + Fe n - Ee n ^ 2 - 7 / 3 + 5 / 3 * Ee n
        + ((n : ℚ) - 3) / (3 * n.factorial) := by
  have hsq : bstE n (fun t => (cmpsN (ip t) : ℚ) ^ 2)
      = bstE n (fun t => ((2 * n + 1 : ℚ)) ^ 2
          + (rlen t : ℚ) ^ 2 + (leaves t : ℚ) ^ 2 - 2 * ((rlen t : ℚ) * leaves t)
          - 2 * (2 * n + 1 : ℚ) * rlen t + 2 * (2 * n + 1 : ℚ) * leaves t) :=
    bstE_congr (fun t ht => by
      rw [cmpsN_q t (ne_nil_of_numNodes (by omega) ht), ht]; ring)
  rw [hsq, bstE_add, bstE_sub, bstE_sub, bstE_add, bstE_add, bstE_const, bstE_smul, bstE_smul,
    bstE_smul, bst_EAN n (by omega), bst_Eh2, bst_Eh,
    show bstE n (fun t => (leaves t : ℚ) ^ 2) = bstEL2 n from rfl,
    show bstE n (fun t => (rlen t : ℚ) * leaves t) = bstEhL n from rfl,
    show bstE n (fun t => (leaves t : ℚ)) = bstEL n from rfl]
  have hv := bst_VarL n hn
  have hc := bst_CovhL n (by omega)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [bst_EL, show m + 4 = (m + 2) + 2 by omega, eC_add_two] at hv hc ⊢
  rw [show m + 2 + 2 = m + 4 by omega] at hv hc ⊢
  push_cast at hv hc ⊢
  linear_combination hv - 2 * hc

/-- **`Cov(A_M, A_N) = Var[h] - Cov(h, L)`** under the BST model (`n ≥ 2`),
    i.e. `F_n - E_n² - 7/6 + (5/6)E_n + (n-3)/(6·n!)`. -/
theorem bst_CovAMAN (n : ℕ) (hn : 2 ≤ n) :
    bstE n (fun t => (cmpsM (ip t) : ℚ) * cmpsN (ip t))
        - bstE n (fun t => (cmpsM (ip t) : ℚ)) * bstE n (fun t => (cmpsN (ip t) : ℚ))
      = Fe n - Ee n ^ 2 - 7 / 6 + 5 / 6 * Ee n + ((n : ℚ) - 3) / (6 * n.factorial) := by
  have hpr : bstE n (fun t => (cmpsM (ip t) : ℚ) * cmpsN (ip t))
      = bstE n (fun t => ((3 * n - 1 : ℚ)) * (2 * n + 1) + (rlen t : ℚ) ^ 2
          - (rlen t : ℚ) * leaves t - (2 * n + 1 : ℚ) * rlen t - (3 * n - 1 : ℚ) * rlen t
          + (3 * n - 1 : ℚ) * leaves t) :=
    bstE_congr (fun t ht => by
      rw [cmpsM_q t (ne_nil_of_numNodes (by omega) ht),
        cmpsN_q t (ne_nil_of_numNodes (by omega) ht), ht]; ring)
  rw [hpr, bstE_add, bstE_sub, bstE_sub, bstE_sub, bstE_add, bstE_const, bstE_smul, bstE_smul,
    bstE_smul, bst_EAM n (by omega), bst_EAN n hn, bst_Eh2, bst_Eh,
    show bstE n (fun t => (rlen t : ℚ) * leaves t) = bstEhL n from rfl,
    show bstE n (fun t => (leaves t : ℚ)) = bstEL n from rfl]
  have hc := bst_CovhL n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [bst_EL, eC_add_two] at hc ⊢
  push_cast at hc ⊢
  linear_combination -hc

/-- **Concentration of `A_M` at the worst case** under the BST model:
    `P(A_M ≥ 3n - 2 - c) = 1 - 1/(c+2)!` for `n ≥ c + 2`. -/
theorem bst_PAM_ge (n c : ℕ) (hn : c + 2 ≤ n) :
    bstE n (fun t => if 3 * n - 2 - c ≤ cmpsM (ip t) then 1 else 0)
      = 1 - 1 / ((c + 2).factorial : ℚ) := by
  rw [bstE_congr (g := fun t => 1 - (if c + 2 ≤ rlen t then (1 : ℚ) else 0)) (fun t ht => by
    have hne := ne_nil_of_numNodes (by omega : 1 ≤ n) ht
    have h1 := central_M_exec t hne
    rw [finalH_toPop_eq_rlen t hne, ht] at h1
    by_cases hc : c + 2 ≤ rlen t
    · rw [if_neg (by omega), if_pos hc]; ring
    · rw [if_pos (by omega), if_neg hc]; ring),
    bstE_sub, bstE_const, show bstE n (fun t => if c + 2 ≤ rlen t then (1 : ℚ) else 0)
      = bstPge n (c + 2) from rfl, bst_Pge, if_pos hn]

end MakinenAnalysis
