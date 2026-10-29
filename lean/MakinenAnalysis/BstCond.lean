import MakinenAnalysis.BstModel

/-!
# The random BST model: moments of `L` conditioned on the final stack height

Ports the conditional-moment results of a separate Rocq development
(`BstStackHeightProof.v`, not included in this artifact) to the Lean system of
`BstModel`, and adds the conditional second moment, which Rocq only checked for
`n ≤ 8` (`EqL2_bounded_upto_8`).

| here | Rocq | claim |
|---|---|---|
| `bst_PgeL_top` | `PgeL_top` | `E[L; h ≥ m] = 1/m!` for `m ≤ n ≤ m+1` |
| `bst_PgeL_bulk` | `PgeL_bulk` | `E[L; h ≥ m] = (1/m!)((n−m+1)/3 + 1/2 − 1/((m+1)(m+2)))`, `n ≥ m+2` |
| `bst_EqL` | `cond_mean`, `EqL_closed` | `E[L | h = m] = (n−m+1)/3 + 1/2 + 1/(3(m+3))`, `n ≥ m+3` |
| `bst_PgeL2_closed` | — | `E[L²; h ≥ m]` in closed form for every `n` |
| `bst_EqL2` | `EqL2_conj` (bounded only) | `E[L² | h = m] = Var + E²` with `Var[L | h = m] = 2(n−m+1)/45 − (3m²+23m+52)/(45(m+3)²(m+5))`, `n ≥ m+5` |

The conditional statements are written without division, as
`E[f; h = m] = P(h = m) · (value)`.  The onsets `n ≥ m+3` and `n ≥ m+5` are
sharp (checked against the exact law for `n ≤ 22`).

The proofs follow the root decomposition of `BstModel`: for `n ≥ 2` and `m ≥ 1`
the right subtree is empty (then `h = 1 + h(left)`) or not (then `h = h(right)`),
so `E[L; h ≥ m]` at `(n, m)` is expressed through `(n−1, m−1)` and through
`(j, m)` for `j < n`.  Writing `n = m + d`, the closed forms `g1 d m`, `g2 d m`
satisfy the resulting recursions (`g1_rec`, `g2_rec`); the partial sums needed
there have closed forms of their own (`sum_g1`, `sum_g2`, `Kc_eq`).
-/

namespace MakinenAnalysis

open Finset

/-! ## 1. Definitions and the root recursion -/

/-- `E[L; h ≥ m]`. -/
def PgeL (n m : ℕ) : ℚ := bstE n (fun t => if m ≤ rlen t then (leaves t : ℚ) else 0)

/-- `E[L²; h ≥ m]`. -/
def PgeL2 (n m : ℕ) : ℚ := bstE n (fun t => if m ≤ rlen t then (leaves t : ℚ) ^ 2 else 0)

lemma PgeL_zero_m (n : ℕ) : PgeL n 0 = eC n := by
  rw [← bst_EL, PgeL, bstEL]; exact bstE_congr (fun t _ => by simp)

lemma PgeL2_zero_m (n : ℕ) : PgeL2 n 0 = sC n := by
  rw [← bst_EL2, PgeL2, bstEL2]; exact bstE_congr (fun t _ => by simp)

lemma PgeL_lt {n m : ℕ} (h : n < m) : PgeL n m = 0 := by
  rw [PgeL, bstE_congr (g := fun _ => 0) (fun t ht => by
    rw [if_neg (by have := rlen_le_numNodes t; omega)])]
  exact bstE_const n 0

lemma PgeL2_lt {n m : ℕ} (h : n < m) : PgeL2 n m = 0 := by
  rw [PgeL2, bstE_congr (g := fun _ => 0) (fun t ht => by
    rw [if_neg (by have := rlen_le_numNodes t; omega)])]
  exact bstE_const n 0

lemma bstPge_lt {n m : ℕ} (h : n < m) : bstPge n m = 0 := by
  rw [bst_Pge, if_neg (by omega)]

/-- **Root recursion for `E[L; h ≥ m+1]`.** -/
lemma PgeL_succ (k m : ℕ) :
    PgeL (k + 2) (m + 1) = (PgeL (k + 1) m
      + ∑ p ∈ antidiagonal k, (eC p.1 * bstPge (p.2 + 1) (m + 1) + PgeL (p.2 + 1) (m + 1)))
        / (k + 2) := by
  rw [PgeL, bstE_succ]
  have hin : ∀ p ∈ antidiagonal (k + 1), (∑ l ∈ trees p.1, ∑ r ∈ trees p.2,
      bstW l * bstW r * (fun t : T => if m + 1 ≤ rlen t then (leaves t : ℚ) else 0)
        (.node () l r))
        = if p.2 = 0 then PgeL p.1 m else eC p.1 * bstPge p.2 (m + 1) + PgeL p.2 (m + 1) := by
    intro p hp
    have hp' : p.1 + p.2 = k + 1 := Finset.mem_antidiagonal.mp hp
    by_cases h0 : p.2 = 0
    · have hp1 : p.1 ≠ 0 := by omega
      rw [if_pos h0, dsum_congr (G := fun l r => if m ≤ rlen l then (leaves l : ℚ) else 0)
        (fun l r hl hr => by
          have hrn := nil_of_numNodes_zero (hr.trans h0)
          subst hrn
          simp only [rlen_node, leaves_node, hl, BinaryTree.numNodes, if_true, hp1, if_false,
            add_zero, leaves_nil, Nat.cast_zero]
          by_cases hm : m ≤ rlen l
          · rw [if_pos (by omega), if_pos hm]
          · rw [if_neg (by omega), if_neg hm]),
        dsum_fst]
      rfl
    · rw [if_neg h0, dsum_congr (G := fun l r => (leaves l : ℚ) * (if m + 1 ≤ rlen r then 1 else 0)
          + (if m + 1 ≤ rlen r then (leaves r : ℚ) else 0))
        (fun l r hl hr => by
          simp only [rlen_node, leaves_node, hl, hr, h0, if_false, hp',
            add_eq_zero, one_ne_zero, and_false, add_zero]
          split_ifs <;> ring),
        dsum_add, dsum_snd, dsum_mul, ← bstEL, bst_EL]
      rfl
  rw [Finset.sum_congr rfl hin, Finset.Nat.sum_antidiagonal_succ']
  simp only [if_true, Nat.add_one_ne_zero, if_false]
  push_cast
  ring

/-- **Root recursion for `E[L²; h ≥ m+1]`.** -/
lemma PgeL2_succ (k m : ℕ) :
    PgeL2 (k + 2) (m + 1) = (PgeL2 (k + 1) m
      + ∑ p ∈ antidiagonal k, (sC p.1 * bstPge (p.2 + 1) (m + 1)
          + 2 * (eC p.1 * PgeL (p.2 + 1) (m + 1)) + PgeL2 (p.2 + 1) (m + 1))) / (k + 2) := by
  rw [PgeL2, bstE_succ]
  have hin : ∀ p ∈ antidiagonal (k + 1), (∑ l ∈ trees p.1, ∑ r ∈ trees p.2,
      bstW l * bstW r * (fun t : T => if m + 1 ≤ rlen t then (leaves t : ℚ) ^ 2 else 0)
        (.node () l r))
        = if p.2 = 0 then PgeL2 p.1 m
          else sC p.1 * bstPge p.2 (m + 1) + 2 * (eC p.1 * PgeL p.2 (m + 1))
            + PgeL2 p.2 (m + 1) := by
    intro p hp
    have hp' : p.1 + p.2 = k + 1 := Finset.mem_antidiagonal.mp hp
    by_cases h0 : p.2 = 0
    · have hp1 : p.1 ≠ 0 := by omega
      rw [if_pos h0, dsum_congr (G := fun l r => if m ≤ rlen l then (leaves l : ℚ) ^ 2 else 0)
        (fun l r hl hr => by
          have hrn := nil_of_numNodes_zero (hr.trans h0)
          subst hrn
          simp only [rlen_node, leaves_node, hl, BinaryTree.numNodes, if_true, hp1, if_false,
            add_zero, leaves_nil, Nat.cast_zero]
          by_cases hm : m ≤ rlen l
          · rw [if_pos (by omega), if_pos hm]
          · rw [if_neg (by omega), if_neg hm]),
        dsum_fst]
      rfl
    · rw [if_neg h0, dsum_congr (G := fun l r =>
          ((leaves l : ℚ) ^ 2 * (if m + 1 ≤ rlen r then 1 else 0)
            + (2 * (leaves l : ℚ)) * (if m + 1 ≤ rlen r then (leaves r : ℚ) else 0))
          + (if m + 1 ≤ rlen r then (leaves r : ℚ) ^ 2 else 0))
        (fun l r hl hr => by
          simp only [rlen_node, leaves_node, hl, hr, h0, if_false, hp',
            add_eq_zero, one_ne_zero, and_false, add_zero]
          split_ifs <;> ring),
        dsum_add, dsum_add, dsum_snd, dsum_mul, dsum_mul, bstE_smul, ← bstEL, bst_EL,
        ← bstEL2, bst_EL2]
      simp only [bstPge, PgeL, PgeL2]
      ring
  rw [Finset.sum_congr rfl hin, Finset.Nat.sum_antidiagonal_succ']
  simp only [if_true, Nat.add_one_ne_zero, if_false]
  push_cast
  ring

/-- Re-indexing a sum over `antidiagonal k` whose terms vanish for `p.2 < m`,
    with `k + 1 = m + d`: only `p.2 = m + e`, `p.1 = d − 1 − e` (`e < d`) remain. -/
lemma sum_shift (k m d : ℕ) (h : k + 1 = m + d) (F : ℕ → ℕ → ℚ)
    (hF : ∀ j, j < m → F (k - j) j = 0) :
    ∑ p ∈ antidiagonal k, F p.1 p.2 = ∑ e ∈ range d, F (d - 1 - e) (m + e) := by
  rw [← Finset.Nat.sum_antidiagonal_swap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => F b a) k]
  rw [show k.succ = m + d by omega, Finset.sum_range_add,
    Finset.sum_eq_zero (fun j hj => hF j (Finset.mem_range.mp hj)), zero_add]
  exact Finset.sum_congr rfl (fun e he => by
    have := Finset.mem_range.mp he
    rw [show k - (m + e) = d - 1 - e by omega])

/-! ## 2. The closed forms -/

/-- `m! · E[L; h ≥ m]` at `n = m + d`. -/
def g1 : ℕ → ℕ → ℚ
  | 0, _ => 1
  | 1, _ => 1
  | e + 2, m => ((e : ℚ) + 3) / 3 + 1 / 2 - 1 / (((m : ℚ) + 1) * ((m : ℚ) + 2))

/-- `m! · E[L²; h ≥ m]` at `n = m + d`. -/
def g2 : ℕ → ℕ → ℚ
  | 0, _ => 1
  | 1, _ => 1
  | 2, m => 5 / 2 + 3 / ((m : ℚ) + 2) - 3 / ((m : ℚ) + 1)
  | 3, m => 7 / 2 + 3 / ((m : ℚ) + 2) - 3 / ((m : ℚ) + 1)
  | e + 4, m => ((e : ℚ) + 4) ^ 2 / 9
      + ((e : ℚ) + 4) * (3 / 5 + 2 / (3 * ((m : ℚ) + 2)) - 2 / (3 * ((m : ℚ) + 1)))
      + 133 / 180 - 1 / (3 * ((m : ℚ) + 4)) + 1 / ((m : ℚ) + 3) + 1 / (3 * ((m : ℚ) + 2))
      - 1 / ((m : ℚ) + 1)

lemma g1_zero (d : ℕ) (hd : 1 ≤ d) : g1 d 0 = eC d := by
  match d with
  | 1 => rfl
  | e + 2 => simp only [g1, eC_add_two]; push_cast; ring

lemma g2_zero (d : ℕ) (hd : 1 ≤ d) : g2 d 0 = sC d := by
  match d with
  | 1 => rfl
  | 2 => simp [g2, sC]; norm_num
  | 3 => simp [g2, sC]; norm_num
  | e + 4 => simp only [g2, sC_add_four]; push_cast; ring

/-- `Σ_{e<D} g1 e m` for `D ≥ 2`. -/
def SG1c (D m : ℕ) : ℚ :=
  (D : ℚ) ^ 2 / 6 + (D : ℚ) * (2 / 3 + 1 / ((m : ℚ) + 2) - 1 / ((m : ℚ) + 1))
    - 2 / ((m : ℚ) + 2) + 2 / ((m : ℚ) + 1)

lemma sum_g1 (m e : ℕ) : ∑ k ∈ range (e + 2), g1 k m = SG1c (e + 2) m := by
  have h1 : (0 : ℚ) < (m : ℚ) + 1 := by positivity
  have h2 : (0 : ℚ) < (m : ℚ) + 2 := by positivity
  induction e with
  | zero => simp [Finset.sum_range_succ, g1, SG1c]; field_simp; ring
  | succ e ih =>
    rw [Finset.sum_range_succ, ih, show e + 2 = e + 2 from rfl]
    simp only [g1, SG1c]
    push_cast
    field_simp
    ring

/-- **The recursion that `g1` satisfies.** -/
lemma g1_rec (m d : ℕ) :
    ((m : ℚ) + 1 + d) * g1 d (m + 1)
      = ((m : ℚ) + 1) * g1 d m + ∑ a ∈ range d, eC a + ∑ e ∈ range d, g1 e (m + 1) := by
  have h1 : (0 : ℚ) < (m : ℚ) + 1 := by positivity
  have h2 : (0 : ℚ) < (m : ℚ) + 2 := by positivity
  have h3 : (0 : ℚ) < (m : ℚ) + 3 := by positivity
  match d with
  | 0 => simp [g1]
  | 1 => simp [g1, eC]
  | e + 2 =>
    rw [sum_eC e, sum_g1 (m + 1) e]
    simp only [g1, SG1c]
    push_cast
    field_simp
    ring

lemma sum_eC_reflect (d : ℕ) (c : ℚ) :
    ∑ e ∈ range d, eC (d - 1 - e) * c = (∑ a ∈ range d, eC a) * c := by
  rw [Finset.sum_mul, ← Finset.sum_range_reflect (fun a => eC a * c) d]

/-- **`m! · E[L; h ≥ m] = g1 (n − m) m`** for every `n ≥ m ≥ 1`. -/
theorem PgeL_closed : ∀ n m d : ℕ, 1 ≤ m → m + d = n → PgeL n m = g1 d m / m.factorial := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro m d hm hn
  match n, ih with
  | 0, _ => omega
  | 1, _ =>
    obtain ⟨rfl, rfl⟩ : m = 1 ∧ d = 0 := by omega
    simp [PgeL, bstE_succ, bstW, leaves, isNode, g1, rlen]
  | k + 2, ih =>
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [PgeL_succ k m']
    have hX : PgeL (k + 1) m' = g1 d m' / m'.factorial := by
      rcases Nat.eq_zero_or_pos m' with rfl | hm'
      · rw [PgeL_zero_m, g1_zero d (by omega), show k + 1 = d by omega]; simp
      · exact ih (k + 1) (by omega) m' d hm' (by omega)
    have hS : ∑ p ∈ antidiagonal k, (eC p.1 * bstPge (p.2 + 1) (m' + 1) + PgeL (p.2 + 1) (m' + 1))
        = (∑ a ∈ range d, eC a + ∑ e ∈ range d, g1 e (m' + 1)) / (m' + 1).factorial := by
      rw [sum_shift k m' d (by omega)
        (fun a b => eC a * bstPge (b + 1) (m' + 1) + PgeL (b + 1) (m' + 1))
        (fun j hj => by
          show eC (k - j) * bstPge (j + 1) (m' + 1) + PgeL (j + 1) (m' + 1) = 0
          rw [bstPge_lt (by omega), PgeL_lt (by omega)]; ring)]
      rw [Finset.sum_congr rfl (fun e he => by
        rw [bst_Pge, if_pos (by omega),
          ih (m' + e + 1) (by have := Finset.mem_range.mp he; omega) (m' + 1) e (by omega)
            (by omega)])]
      rw [Finset.sum_add_distrib, sum_eC_reflect, add_div,
        Finset.sum_div (range d) (fun e => g1 e (m' + 1))]
      ring
    rw [hX, hS]
    have key := g1_rec m' d
    have hk : (k : ℚ) + 2 = (m' : ℚ) + 1 + d := by exact_mod_cast (show k + 2 = m' + 1 + d by omega)
    have hF : (0 : ℚ) < (m'.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos m'
    rw [fact_succ_q, hk]
    field_simp
    linarith [key]

/-! ## 3. The second moment -/

/-- The convolution `Σ_{e<d} E[L_{d−1−e}] · g1 e m` that the cross term produces. -/
def Kconv (d m : ℕ) : ℚ := ∑ e ∈ range d, eC (d - 1 - e) * g1 e m

/-- The first difference of `eC`. -/
def dC (j : ℕ) : ℚ := if j = 0 then 1 else if j = 1 then 0 else 1 / 3

lemma eC_succ_eq (j : ℕ) : eC (j + 1) = eC j + dC j := by
  match j with
  | 0 => simp [eC, dC]
  | 1 => simp [eC, dC]
  | j + 2 =>
    rw [show j + 2 + 1 = (j + 1) + 2 by omega, eC_add_two, eC_add_two]
    simp only [dC, show j + 2 ≠ 0 by omega, show j + 2 ≠ 1 by omega, if_false]
    push_cast; ring

lemma Kconv_succ (f m : ℕ) :
    Kconv (f + 3) m = Kconv (f + 2) m + g1 (f + 1) m + (∑ e ∈ range f, g1 e m) / 3 := by
  rw [Kconv, Finset.sum_range_succ, show f + 3 - 1 - (f + 2) = 0 by omega]
  simp only [show eC 0 = 0 from rfl, zero_mul, add_zero]
  have h1 : ∀ e ∈ range (f + 2), eC (f + 3 - 1 - e) * g1 e m
      = eC (f + 2 - 1 - e) * g1 e m + dC (f + 1 - e) * g1 e m := by
    intro e he
    have := Finset.mem_range.mp he
    rw [show f + 3 - 1 - e = (f + 1 - e) + 1 by omega, eC_succ_eq,
      show f + 2 - 1 - e = f + 1 - e by omega]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Kconv]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, show f + 1 - (f + 1) = 0 by omega,
    show f + 1 - f = 1 by omega]
  have h2 : ∀ e ∈ range f, dC (f + 1 - e) * g1 e m = g1 e m / 3 := by
    intro e he
    have := Finset.mem_range.mp he
    simp only [dC, show f + 1 - e ≠ 0 by omega, show f + 1 - e ≠ 1 by omega, if_false]
    ring
  rw [Finset.sum_congr rfl h2, ← Finset.sum_div]
  simp [dC]
  ring

/-- `Kconv d m` for `d ≥ 4`. -/
def Kc (d m : ℕ) : ℚ :=
  (d : ℚ) ^ 3 / 54 + (d : ℚ) ^ 2 * (5 / 36 + 1 / (6 * ((m : ℚ) + 2)) - 1 / (6 * ((m : ℚ) + 1)))
    + (d : ℚ) * (13 / 108 - 1 / (2 * ((m : ℚ) + 2)) + 1 / (2 * ((m : ℚ) + 1)))
    - 1 / 18 + 1 / (3 * ((m : ℚ) + 2)) - 1 / (3 * ((m : ℚ) + 1))

lemma Kconv_small (m : ℕ) :
    Kconv 0 m = 0 ∧ Kconv 1 m = 0 ∧ Kconv 2 m = 1 ∧ Kconv 3 m = 2 ∧
      Kconv 4 m = 23 / 6 - 1 / (((m : ℚ) + 1) * ((m : ℚ) + 2)) := by
  refine ⟨by simp [Kconv], by simp [Kconv, eC], by simp [Kconv, Finset.sum_range_succ, eC, g1],
    ?_, ?_⟩
  · simp [Kconv, Finset.sum_range_succ, eC, g1]; norm_num
  · simp [Kconv, Finset.sum_range_succ, g1]
    rw [show (3 : ℕ) = 1 + 2 from rfl, eC_add_two]
    simp [eC]
    ring

lemma Kconv_eq (m e : ℕ) : Kconv (e + 4) m = Kc (e + 4) m := by
  have h1 : (0 : ℚ) < (m : ℚ) + 1 := by positivity
  have h2 : (0 : ℚ) < (m : ℚ) + 2 := by positivity
  induction e with
  | zero =>
    rw [(Kconv_small m).2.2.2.2]
    simp only [Kc]; push_cast; field_simp; ring
  | succ e ih =>
    rw [show e + 1 + 4 = (e + 2) + 3 by omega, Kconv_succ, show e + 2 + 2 = e + 4 by omega, ih,
      sum_g1 m e]
    simp only [Kc, g1, SG1c]
    push_cast
    field_simp
    ring

/-- `Σ_{e<D} g2 e m` for `D ≥ 4`. -/
def SG2c (D m : ℕ) : ℚ :=
  (D : ℚ) ^ 3 / 27 + (D : ℚ) ^ 2 * (11 / 45 + 1 / (3 * ((m : ℚ) + 2)) - 1 / (3 * ((m : ℚ) + 1)))
    + (D : ℚ) * (247 / 540 - 1 / (3 * ((m : ℚ) + 4)) + 1 / ((m : ℚ) + 3)
      - 2 / (3 * ((m : ℚ) + 1)))
    - 1 / 9 + 4 / (3 * ((m : ℚ) + 4)) - 4 / ((m : ℚ) + 3) + 2 / (3 * ((m : ℚ) + 2))
    + 2 / ((m : ℚ) + 1)

lemma sum_g2 (m e : ℕ) : ∑ k ∈ range (e + 4), g2 k m = SG2c (e + 4) m := by
  have h1 : (0 : ℚ) < (m : ℚ) + 1 := by positivity
  have h2 : (0 : ℚ) < (m : ℚ) + 2 := by positivity
  have h3 : (0 : ℚ) < (m : ℚ) + 3 := by positivity
  have h4 : (0 : ℚ) < (m : ℚ) + 4 := by positivity
  induction e with
  | zero => simp [Finset.sum_range_succ, g2, SG2c]; field_simp; ring
  | succ e ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [g2, SG2c]
    push_cast
    field_simp
    ring

/-- **The recursion that `g2` satisfies.** -/
lemma g2_rec (m d : ℕ) :
    ((m : ℚ) + 1 + d) * g2 d (m + 1)
      = ((m : ℚ) + 1) * g2 d m + ∑ a ∈ range d, sC a + 2 * Kconv d (m + 1)
        + ∑ e ∈ range d, g2 e (m + 1) := by
  have h1 : (0 : ℚ) < (m : ℚ) + 1 := by positivity
  have h2 : (0 : ℚ) < (m : ℚ) + 2 := by positivity
  have h3 : (0 : ℚ) < (m : ℚ) + 3 := by positivity
  have h4 : (0 : ℚ) < (m : ℚ) + 4 := by positivity
  have h5 : (0 : ℚ) < (m : ℚ) + 5 := by positivity
  obtain ⟨k0, k1, k2, k3, -⟩ := Kconv_small (m + 1)
  match d with
  | 0 => simp [g2, k0]
  | 1 => simp [g2, k1, sC]
  | 2 =>
    rw [k2]; simp [g2, Finset.sum_range_succ, sC]; field_simp; ring
  | 3 =>
    rw [k3]; simp [g2, Finset.sum_range_succ, sC]; field_simp; ring
  | e + 4 =>
    rw [sum_sC e, Kconv_eq (m + 1) e, sum_g2 (m + 1) e]
    simp only [g2, Kc, SG2c]
    push_cast
    field_simp
    ring

lemma sum_reflect_mul (f : ℕ → ℚ) (d : ℕ) (c : ℚ) :
    ∑ e ∈ range d, f (d - 1 - e) * c = (∑ a ∈ range d, f a) * c := by
  rw [Finset.sum_mul, ← Finset.sum_range_reflect (fun a => f a * c) d]

/-- **`m! · E[L²; h ≥ m] = g2 (n − m) m`** for every `n ≥ m ≥ 1`. -/
theorem PgeL2_closed : ∀ n m d : ℕ, 1 ≤ m → m + d = n → PgeL2 n m = g2 d m / m.factorial := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro m d hm hn
  match n, ih with
  | 0, _ => omega
  | 1, _ =>
    obtain ⟨rfl, rfl⟩ : m = 1 ∧ d = 0 := by omega
    simp [PgeL2, bstE_succ, bstW, leaves, isNode, g2, rlen]
  | k + 2, ih =>
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [PgeL2_succ k m']
    have hX : PgeL2 (k + 1) m' = g2 d m' / m'.factorial := by
      rcases Nat.eq_zero_or_pos m' with rfl | hm'
      · rw [PgeL2_zero_m, g2_zero d (by omega), show k + 1 = d by omega]; simp
      · exact ih (k + 1) (by omega) m' d hm' (by omega)
    have hS : ∑ p ∈ antidiagonal k, (sC p.1 * bstPge (p.2 + 1) (m' + 1)
          + 2 * (eC p.1 * PgeL (p.2 + 1) (m' + 1)) + PgeL2 (p.2 + 1) (m' + 1))
        = (∑ a ∈ range d, sC a + 2 * Kconv d (m' + 1) + ∑ e ∈ range d, g2 e (m' + 1))
            / (m' + 1).factorial := by
      rw [sum_shift k m' d (by omega)
        (fun a b => sC a * bstPge (b + 1) (m' + 1) + 2 * (eC a * PgeL (b + 1) (m' + 1))
          + PgeL2 (b + 1) (m' + 1))
        (fun j hj => by
          show sC (k - j) * bstPge (j + 1) (m' + 1) + 2 * (eC (k - j) * PgeL (j + 1) (m' + 1))
            + PgeL2 (j + 1) (m' + 1) = 0
          rw [bstPge_lt (by omega), PgeL_lt (by omega), PgeL2_lt (by omega)]; ring)]
      rw [Finset.sum_congr rfl (fun e he => by
        rw [bst_Pge, if_pos (by omega),
          PgeL_closed (m' + e + 1) (m' + 1) e (by omega) (by omega),
          ih (m' + e + 1) (by have := Finset.mem_range.mp he; omega) (m' + 1) e (by omega)
            (by omega)])]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_reflect_mul, Kconv]
      have e1 : ∑ e ∈ range d, 2 * (eC (d - 1 - e) * (g1 e (m' + 1) / ((m' + 1).factorial : ℚ)))
          = 2 * (∑ e ∈ range d, eC (d - 1 - e) * g1 e (m' + 1)) / ((m' + 1).factorial : ℚ) := by
        rw [Finset.mul_sum, Finset.sum_div]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      have e2 : ∑ e ∈ range d, g2 e (m' + 1) / ((m' + 1).factorial : ℚ)
          = (∑ e ∈ range d, g2 e (m' + 1)) / ((m' + 1).factorial : ℚ) :=
        (Finset.sum_div _ _ _).symm
      rw [e1, e2]
      ring
    rw [hX, hS]
    have key := g2_rec m' d
    have hk : (k : ℚ) + 2 = (m' : ℚ) + 1 + d := by exact_mod_cast (show k + 2 = m' + 1 + d by omega)
    have hF : (0 : ℚ) < (m'.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos m'
    rw [fact_succ_q, hk]
    field_simp
    linarith [key]

/-! ## 4. The headline statements -/

/-- **`E[L; h ≥ m] = 1/m!` for `m ≤ n ≤ m+1`** (Rocq: `PgeL_top`). -/
theorem bst_PgeL_top (n m : ℕ) (hm : 1 ≤ m) (h1 : m ≤ n) (h2 : n ≤ m + 1) :
    PgeL n m = 1 / m.factorial := by
  rw [PgeL_closed n m (n - m) hm (by omega)]
  rcases (show n - m = 0 ∨ n - m = 1 by omega) with h | h <;> rw [h] <;> rfl

/-- **`E[L; h ≥ m] = (1/m!)((n−m+1)/3 + 1/2 − 1/((m+1)(m+2)))` for `n ≥ m+2`**
    (Rocq: `PgeL_bulk`). -/
theorem bst_PgeL_bulk (n m : ℕ) (hm : 1 ≤ m) (h : m + 2 ≤ n) :
    PgeL n m = 1 / m.factorial
      * (((n : ℚ) - m + 1) / 3 + 1 / 2 - 1 / (((m : ℚ) + 1) * ((m : ℚ) + 2))) := by
  obtain ⟨e, rfl⟩ : ∃ e, n = m + (e + 2) := ⟨n - m - 2, by omega⟩
  rw [PgeL_closed _ m (e + 2) hm rfl]
  simp only [g1]
  push_cast
  ring

lemma bstE_eq_sub_L (n m : ℕ) (k : ℕ) :
    bstE n (fun t => if rlen t = m then (leaves t : ℚ) ^ k else 0)
      = bstE n (fun t => if m ≤ rlen t then (leaves t : ℚ) ^ k else 0)
        - bstE n (fun t => if m + 1 ≤ rlen t then (leaves t : ℚ) ^ k else 0) := by
  rw [← bstE_sub]
  refine bstE_congr (fun t _ => ?_)
  by_cases h1 : rlen t = m
  · simp [h1]
  · by_cases h2 : m ≤ rlen t
    · rw [if_neg h1, if_pos h2, if_pos (by omega)]; ring
    · rw [if_neg h1, if_neg h2, if_neg (by omega)]; ring

lemma bstPeq (n m : ℕ) (h : m + 1 ≤ n) :
    bstE n (fun t => if rlen t = m then 1 else 0)
      = 1 / (m.factorial : ℚ) - 1 / ((m + 1).factorial : ℚ) := by
  have := bstE_eq_sub_L n m 0
  simp only [pow_zero] at this
  rw [this, ← bstPge, ← bstPge, bst_Pge, bst_Pge, if_pos (by omega), if_pos h]

/-- **The conditional mean `E[L | h = m] = (n−m+1)/3 + 1/2 + 1/(3(m+3))`** for
    `1 ≤ m`, `n ≥ m+3` (Rocq: `cond_mean`, `EqL_closed`), written as
    `E[L; h = m] = P(h = m) · (…)`. -/
theorem bst_EqL (n m : ℕ) (hm : 1 ≤ m) (h : m + 3 ≤ n) :
    bstE n (fun t => if rlen t = m then (leaves t : ℚ) else 0)
      = bstE n (fun t => if rlen t = m then 1 else 0)
        * (((n : ℚ) - m + 1) / 3 + 1 / 2 + 1 / (3 * ((m : ℚ) + 3))) := by
  have := bstE_eq_sub_L n m 1
  simp only [pow_one] at this
  rw [this, ← PgeL, ← PgeL, bstPeq n m (by omega)]
  obtain ⟨e, rfl⟩ : ∃ e, n = m + (e + 3) := ⟨n - m - 3, by omega⟩
  rw [PgeL_closed _ m (e + 3) hm rfl, PgeL_closed _ (m + 1) (e + 2) (by omega) (by omega)]
  simp only [g1]
  rw [fact_succ_q]
  have hF : (0 : ℚ) < (m.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos m
  push_cast
  field_simp
  ring

/-- **`E[L²; h ≥ m]` in closed form** for every `n = m + d ≥ m ≥ 1`. -/
theorem bst_PgeL2_closed (m d : ℕ) (hm : 1 ≤ m) : PgeL2 (m + d) m = g2 d m / m.factorial :=
  PgeL2_closed _ m d hm rfl

/-- **The conditional second moment**: for `1 ≤ m`, `n ≥ m+5`,
    `E[L²; h = m] = P(h = m) · (V + E²)` with the conditional mean
    `E = (n−m+1)/3 + 1/2 + 1/(3(m+3))` and the conditional variance
    `V = 2(n−m+1)/45 − (3m²+23m+52)/(45(m+3)²(m+5))` (Rocq: `EqL2_conj`, there checked
    for `n ≤ 8` only). -/
theorem bst_EqL2 (n m : ℕ) (hm : 1 ≤ m) (h : m + 5 ≤ n) :
    bstE n (fun t => if rlen t = m then (leaves t : ℚ) ^ 2 else 0)
      = bstE n (fun t => if rlen t = m then 1 else 0)
        * ((2 * ((n : ℚ) - m + 1) / 45
            - (3 * (m : ℚ) ^ 2 + 23 * m + 52) / (45 * ((m : ℚ) + 3) ^ 2 * ((m : ℚ) + 5)))
          + (((n : ℚ) - m + 1) / 3 + 1 / 2 + 1 / (3 * ((m : ℚ) + 3))) ^ 2) := by
  rw [bstE_eq_sub_L n m 2, ← PgeL2, ← PgeL2, bstPeq n m (by omega)]
  obtain ⟨e, rfl⟩ : ∃ e, n = m + (e + 5) := ⟨n - m - 5, by omega⟩
  rw [PgeL2_closed _ m (e + 5) hm rfl, PgeL2_closed _ (m + 1) (e + 4) (by omega) (by omega)]
  rw [show e + 5 = (e + 1) + 4 from rfl]
  simp only [g2]
  rw [fact_succ_q]
  have hF : (0 : ℚ) < (m.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos m
  push_cast
  field_simp
  ring

end MakinenAnalysis
