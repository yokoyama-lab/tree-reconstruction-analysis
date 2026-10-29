import MakinenAnalysis.BstModel

/-!
# The third and fourth cumulants of the leaf count under the random BST model

Ported from a separate Rocq development (not included in this artifact;
`BstCumulant3.v`, `BstCumulant4.v`).  `BstModel` proved `E[L]` and `E[L²]`;
this file adds the third and fourth moments and the cumulants they give.

| here | Rocq | claim |
|---|---|---|
| `bst_EL3` | `EL3_closed` | `E[L³] = −2(n+1)/945 + 2(n+1)²/45 + (n+1)³/27` (`n ≥ 6`) |
| `bst_kappa3` | `KappaL3_closed` | `κ₃(L) = −2(n+1)/945` (`n ≥ 6`) |
| `bst_EL4` | `EL4_closed` | `E[L⁴] = n⁴/81 + 32n³/405 + 2354n²/14175 + 1982n/14175 + 191/4725` (`n ≥ 8`) |
| `bst_kappa4` | `KappaL4_closed` | `κ₄(L) = −22(n+1)/4725` (`n ≥ 8`) |

The proof follows Rocq: the root split gives a recursion for each moment
(`bstEL3_succ`, `bstEL4_succ`) whose cross terms are convolutions of the lower
moments; each convolution is cut into the few small indices where the lower
moments are not yet polynomial and a middle range, whose sum telescopes against
an explicit antiderivative (`tele`; the antiderivatives were found with sympy and
are checked here by `ring`).  The onsets `n ≥ 6`, `n ≥ 8` are sharp (exact
enumeration of the root recursion for `n ≤ 30`).
-/

namespace MakinenAnalysis

open Finset

/-- The closed form of `E[L_n³]` from `n = 6` on (Rocq `cf3`). -/
def cf3 (j : ℕ) : ℚ :=
  -(2 / 945) * ((j : ℚ) + 1) + 2 / 45 * ((j : ℚ) + 1) ^ 2 + 1 / 27 * ((j : ℚ) + 1) ^ 3

/-- The closed form of `E[L_n⁴]` from `n = 8` on (Rocq `cf4`). -/
def cf4 (j : ℕ) : ℚ :=
  (j : ℚ) ^ 4 / 81 + 32 * (j : ℚ) ^ 3 / 405 + 2354 * (j : ℚ) ^ 2 / 14175
    + 1982 * (j : ℚ) / 14175 + 191 / 4725

/-- `E[L_n³]` -/
def bstEL3 (n : ℕ) : ℚ := bstE n (fun t => (leaves t : ℚ) ^ 3)

/-- `E[L_n⁴]` -/
def bstEL4 (n : ℕ) : ℚ := bstE n (fun t => (leaves t : ℚ) ^ 4)

namespace BstCum

/-! ## 1. Tools -/

/-- Telescoping, with the step identity needed only on the range. -/
lemma tele {f F : ℕ → ℚ} : ∀ M : ℕ, (∀ x < M, F (x + 1) - F x = f x) →
    ∑ x ∈ range M, f x = F M - F 0
  | 0, _ => by simp
  | M + 1, h => by
    rw [sum_range_succ, tele M (fun x hx => h x (by omega)), ← h M (by omega)]; ring

lemma eC_ge {j : ℕ} (h : 2 ≤ j) : eC j = ((j : ℚ) + 1) / 3 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
  rw [eC_add_two]; push_cast; ring

lemma sC_ge {j : ℕ} (h : 4 ≤ j) :
    sC j = ((j : ℚ) + 1) ^ 2 / 9 + 2 * ((j : ℚ) + 1) / 45 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 4 := ⟨j - 4, by omega⟩
  rw [sC_add_four]; push_cast; ring

/-- `E[L_n³]` for every `n`: `0, 1, 1, 10/3, 17/3, 48/5`, then `cf3`. -/
def tC : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 10 / 3
  | 4 => 17 / 3
  | 5 => 48 / 5
  | n + 6 => cf3 (n + 6)

lemma tC_ge {j : ℕ} (h : 6 ≤ j) : tC j = cf3 j := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 6 := ⟨j - 6, by omega⟩
  rfl

/-- `E[L_n⁴]` for every `n`: `0, 1, 1, 6, 11, 68/3, 359/9, 1384/21`, then `cf4`. -/
def fC : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 6
  | 4 => 11
  | 5 => 68 / 3
  | 6 => 359 / 9
  | 7 => 1384 / 21
  | n + 8 => cf4 (n + 8)

lemma fC_ge {j : ℕ} (h : 8 ≤ j) : fC j = cf4 j := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 8 := ⟨j - 8, by omega⟩
  rfl

/-- A cross term of the root split. -/
lemma dsum_cmul (i j : ℕ) (c : ℚ) (g k : T → ℚ) :
    ∑ l ∈ trees i, ∑ r ∈ trees j, bstW l * bstW r * (c * (g l * k r))
      = c * (bstE i g * bstE j k) := by
  rw [← dsum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring))

lemma anti_swap (n : ℕ) (f g : ℕ → ℚ) :
    ∑ p ∈ antidiagonal n, f p.1 * g p.2 = ∑ p ∈ antidiagonal n, g p.1 * f p.2 := by
  rw [← Finset.Nat.sum_antidiagonal_swap]
  exact Finset.sum_congr rfl (fun p _ => by simp only [Prod.fst_swap, Prod.snd_swap]; ring)

/-! ## 2. Sums of the moments -/

lemma sum_tC (M : ℕ) :
    ∑ k ∈ range (M + 6), tC k = 103 / 5 + ((1 / 108 : ℚ) * (M : ℚ) ^ 4 + (23 / 90 : ℚ) * (M : ℚ) ^ 3
      + (9943 / 3780 : ℚ) * (M : ℚ) ^ 2 + (419 / 35 : ℚ) * (M : ℚ)) := by
  induction M with
  | zero => norm_num [sum_range_succ, tC]
  | succ M ih =>
    rw [show M + 1 + 6 = (M + 6) + 1 by omega, sum_range_succ, ih, tC_ge (by omega), cf3]
    push_cast; ring

lemma sum_fC (M : ℕ) :
    ∑ k ∈ range (M + 8), fC k = 9290 / 63 + ((1 / 405 : ℚ) * (M : ℚ) ^ 5
      + (91 / 810 : ℚ) * (M : ℚ) ^ 4 + (28843 / 14175 : ℚ) * (M : ℚ) ^ 3
      + (260006 / 14175 : ℚ) * (M : ℚ) ^ 2 + (777899 / 9450 : ℚ) * (M : ℚ)) := by
  induction M with
  | zero => norm_num [sum_range_succ, fC]
  | succ M ih =>
    rw [show M + 1 + 8 = (M + 8) + 1 by omega, sum_range_succ, ih, fC_ge (by omega), cf4]
    push_cast; ring

/-! ## 3. The convolutions -/

/-- `Σ_{i+j=K} E[L_i²] E[L_j]` for `K ≥ 5` (Rocq `conv_21`). -/
lemma conv_sC_eC (M : ℕ) :
    ∑ p ∈ antidiagonal (M + 5), sC p.1 * eC p.2
      = (5 * (M : ℚ) ^ 4 + 144 * (M : ℚ) ^ 3 + 1549 * (M : ℚ) ^ 2 + 7374 * (M : ℚ) + 12960)
        / 1620 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  dsimp only
  rw [show (M + 5).succ = (4 + M) + 1 + 1 by omega, sum_range_succ, sum_range_succ,
    sum_range_add]
  have hmid : ∑ x ∈ range M, sC (4 + x) * eC (M + 5 - (4 + x))
      = (-1/108 : ℚ)*(M:ℚ)^4 + (1/81 : ℚ)*(M:ℚ)^3*(M:ℚ) + (-23/270 : ℚ)*(M:ℚ)^3
        + (47/270 : ℚ)*(M:ℚ)^2*(M:ℚ) + (17/540 : ℚ)*(M:ℚ)^2 + (659/810 : ℚ)*(M:ℚ)*(M:ℚ)
        + (557/270 : ℚ)*(M:ℚ) := by
    rw [tele (F := fun X : ℕ => (-1/108 : ℚ)*(X:ℚ)^4 + (1/81 : ℚ)*(X:ℚ)^3*(M:ℚ)
        + (-23/270 : ℚ)*(X:ℚ)^3 + (47/270 : ℚ)*(X:ℚ)^2*(M:ℚ) + (17/540 : ℚ)*(X:ℚ)^2
        + (659/810 : ℚ)*(X:ℚ)*(M:ℚ) + (557/270 : ℚ)*(X:ℚ)) M (fun x hx => ?_)]
    · push_cast; ring
    · rw [sC_ge (by omega), eC_ge (by omega), Nat.cast_sub (by omega)]
      push_cast; ring
  have hlo : ∑ x ∈ range 4, sC x * eC (M + 5 - x)
      = ∑ x ∈ range 4, sC x * (((M : ℚ) + 5 - x + 1) / 3) :=
    Finset.sum_congr rfl (fun x hx => by
      have := Finset.mem_range.mp hx
      rw [eC_ge (by omega), Nat.cast_sub (by omega)]; push_cast; ring)
  rw [hmid, hlo, show M + 5 - (4 + M) = 1 by omega, show M + 5 - (4 + M + 1) = 0 by omega,
    sC_ge (show 4 ≤ 4 + M by omega)]
  simp only [sum_range_succ, sum_range_zero]
  norm_num [sC, eC]
  ring

/-- `Σ_{i+j=K} E[L_i³] E[L_j]` for `K ≥ 7`. -/
lemma conv_tC_eC (M : ℕ) :
    ∑ p ∈ antidiagonal (M + 7), tC p.1 * eC p.2
      = (M : ℚ) ^ 5 / 1620 + 47 * (M : ℚ) ^ 4 / 1620 + 6161 * (M : ℚ) ^ 3 / 11340
        + 57049 * (M : ℚ) ^ 2 / 11340 + 43571 * (M : ℚ) / 1890 + 1886 / 45 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  dsimp only
  rw [show (M + 7).succ = (6 + M) + 1 + 1 by omega, sum_range_succ, sum_range_succ,
    sum_range_add]
  have hmid : ∑ x ∈ range M, tC (6 + x) * eC (M + 7 - (6 + x))
      = (-1/405 : ℚ)*(M:ℚ)^5 + (1/324 : ℚ)*(M:ℚ)^4*(M:ℚ) + (-91/1620 : ℚ)*(M:ℚ)^4
        + (23/270 : ℚ)*(M:ℚ)^3*(M:ℚ) + (-2101/5670 : ℚ)*(M:ℚ)^3
        + (9943/11340 : ℚ)*(M:ℚ)^2*(M:ℚ) + (2473/11340 : ℚ)*(M:ℚ)^2
        + (419/105 : ℚ)*(M:ℚ)*(M:ℚ) + (911/90 : ℚ)*(M:ℚ) := by
    rw [tele (F := fun X : ℕ => (-1/405 : ℚ)*(X:ℚ)^5 + (1/324 : ℚ)*(X:ℚ)^4*(M:ℚ)
        + (-91/1620 : ℚ)*(X:ℚ)^4 + (23/270 : ℚ)*(X:ℚ)^3*(M:ℚ) + (-2101/5670 : ℚ)*(X:ℚ)^3
        + (9943/11340 : ℚ)*(X:ℚ)^2*(M:ℚ) + (2473/11340 : ℚ)*(X:ℚ)^2
        + (419/105 : ℚ)*(X:ℚ)*(M:ℚ) + (911/90 : ℚ)*(X:ℚ)) M (fun x hx => ?_)]
    · push_cast; ring
    · rw [tC_ge (by omega), cf3, eC_ge (by omega), Nat.cast_sub (by omega)]
      push_cast; ring
  have hlo : ∑ x ∈ range 6, tC x * eC (M + 7 - x)
      = ∑ x ∈ range 6, tC x * (((M : ℚ) + 7 - x + 1) / 3) :=
    Finset.sum_congr rfl (fun x hx => by
      have := Finset.mem_range.mp hx
      rw [eC_ge (by omega), Nat.cast_sub (by omega)]; push_cast; ring)
  rw [hmid, hlo, show M + 7 - (6 + M) = 1 by omega, show M + 7 - (6 + M + 1) = 0 by omega,
    tC_ge (show 6 ≤ 6 + M by omega), cf3]
  simp only [sum_range_succ, sum_range_zero]
  norm_num [tC, eC]
  ring

/-- `Σ_{i+j=K} E[L_i²] E[L_j²]` for `K ≥ 7`. -/
lemma conv_sC_sC (M : ℕ) :
    ∑ p ∈ antidiagonal (M + 7), sC p.1 * sC p.2
      = (M : ℚ) ^ 5 / 2430 + 47 * (M : ℚ) ^ 4 / 2430 + 2207 * (M : ℚ) ^ 3 / 6075
        + 21004 * (M : ℚ) ^ 2 / 6075 + 33668 * (M : ℚ) / 2025 + 1442 / 45 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  dsimp only
  rw [show (M + 7).succ = (4 + M) + 4 by omega, sum_range_add, sum_range_add]
  have hmid : ∑ x ∈ range M, sC (4 + x) * sC (M + 7 - (4 + x))
      = (1/405 : ℚ)*(M:ℚ)^5 + (-1/162 : ℚ)*(M:ℚ)^4*(M:ℚ) + (1/243 : ℚ)*(M:ℚ)^3*(M:ℚ)^2
        + (-47/1215 : ℚ)*(M:ℚ)^3*(M:ℚ) + (-373/2025 : ℚ)*(M:ℚ)^3
        + (47/810 : ℚ)*(M:ℚ)^2*(M:ℚ)^2 + (373/1350 : ℚ)*(M:ℚ)^2*(M:ℚ)
        + (659/2430 : ℚ)*(M:ℚ)*(M:ℚ)^2 + (15604/6075 : ℚ)*(M:ℚ)*(M:ℚ)
        + (12248/2025 : ℚ)*(M:ℚ) := by
    rw [tele (F := fun X : ℕ => (1/405 : ℚ)*(X:ℚ)^5 + (-1/162 : ℚ)*(X:ℚ)^4*(M:ℚ)
        + (1/243 : ℚ)*(X:ℚ)^3*(M:ℚ)^2 + (-47/1215 : ℚ)*(X:ℚ)^3*(M:ℚ) + (-373/2025 : ℚ)*(X:ℚ)^3
        + (47/810 : ℚ)*(X:ℚ)^2*(M:ℚ)^2 + (373/1350 : ℚ)*(X:ℚ)^2*(M:ℚ)
        + (659/2430 : ℚ)*(X:ℚ)*(M:ℚ)^2 + (15604/6075 : ℚ)*(X:ℚ)*(M:ℚ)
        + (12248/2025 : ℚ)*(X:ℚ)) M (fun x hx => ?_)]
    · push_cast; ring
    · rw [sC_ge (show 4 ≤ 4 + x by omega), sC_ge (show 4 ≤ M + 7 - (4 + x) by omega),
        Nat.cast_sub (by omega)]
      push_cast; ring
  have hlo : ∑ x ∈ range 4, sC x * sC (M + 7 - x)
      = ∑ x ∈ range 4, sC x * ((((M : ℚ) + 7 - x) + 1) ^ 2 / 9 + 2 * (((M : ℚ) + 7 - x) + 1) / 45) :=
    Finset.sum_congr rfl (fun x hx => by
      have := Finset.mem_range.mp hx
      rw [sC_ge (show 4 ≤ M + 7 - x by omega), Nat.cast_sub (by omega)]; push_cast; ring)
  have hhi : ∑ x ∈ range 4, sC (4 + M + x) * sC (M + 7 - (4 + M + x))
      = ∑ x ∈ range 4, ((((4 + M + x : ℕ) : ℚ) + 1) ^ 2 / 9
          + 2 * (((4 + M + x : ℕ) : ℚ) + 1) / 45) * sC (3 - x) :=
    Finset.sum_congr rfl (fun x hx => by
      have := Finset.mem_range.mp hx
      rw [sC_ge (show 4 ≤ 4 + M + x by omega), show M + 7 - (4 + M + x) = 3 - x by omega])
  rw [hmid, hlo, hhi]
  simp only [sum_range_succ, sum_range_zero]
  norm_num [sC]
  ring

/-! ## 4. The moment recursions -/

lemma split_node {m : ℕ} {p : ℕ × ℕ} (hp : p ∈ antidiagonal (m + 1)) {l r : T}
    (hl : l.numNodes = p.1) (hr : r.numNodes = p.2) :
    (leaves (.node () l r) : ℚ) = leaves l + leaves r := by
  have hp' : p.1 + p.2 = m + 1 := Finset.mem_antidiagonal.mp hp
  simp only [leaves_node, hl, hr, hp', add_eq_zero, one_ne_zero, and_false, if_false, add_zero]

lemma bstEL3_succ (m : ℕ) :
    bstEL3 (m + 2) = (2 * ∑ k ∈ range (m + 2), bstEL3 k
      + 6 * ∑ p ∈ antidiagonal (m + 1), sC p.1 * eC p.2) / (m + 2) := by
  rw [bstEL3, bstE_succ]
  have hin : ∀ p ∈ antidiagonal (m + 1), (∑ l ∈ trees p.1, ∑ r ∈ trees p.2,
      bstW l * bstW r * (fun t : T => (leaves t : ℚ) ^ 3) (.node () l r))
        = bstEL3 p.1 + bstEL3 p.2 + (3 * (sC p.1 * eC p.2) + 3 * (eC p.1 * sC p.2)) := by
    intro p hp
    rw [dsum_congr (G := fun l r => ((leaves l : ℚ) ^ 3 + (leaves r : ℚ) ^ 3)
        + (3 * ((leaves l : ℚ) ^ 2 * (leaves r : ℚ)) + 3 * ((leaves l : ℚ) * (leaves r : ℚ) ^ 2)))
      (fun l r hl hr => by dsimp only; rw [split_node hp hl hr]; ring),
      dsum_add, dsum_add, dsum_add, dsum_fst, dsum_snd, dsum_cmul, dsum_cmul]
    have h1 := bst_EL p.1
    have h2 := bst_EL p.2
    have h3 := bst_EL2 p.1
    have h4 := bst_EL2 p.2
    rw [bstEL] at h1 h2
    rw [bstEL2] at h3 h4
    rw [h1, h2, h3, h4]
    rfl
  rw [Finset.sum_congr rfl hin, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, sum_anti_fst, sum_anti_snd, ← Finset.mul_sum, ← Finset.mul_sum,
    anti_swap (m + 1) eC sC]
  push_cast
  ring

/-- **`E[L_n³]` for every `n`.** -/
theorem bst_EL3_all (n : ℕ) : bstEL3 n = tC n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  match n with
  | 0 => simp [bstEL3, bstE_zero, tC]
  | 1 => simp [bstEL3, bstE_succ, bstW, leaves, isNode, tC]
  | m + 2 =>
    rw [bstEL3_succ]
    have hs : ∑ k ∈ range (m + 2), bstEL3 k = ∑ k ∈ range (m + 2), tC k :=
      Finset.sum_congr rfl (fun k hk => ih k (by have := Finset.mem_range.mp hk; omega))
    rw [hs]
    match m with
    | 0 => norm_num [Finset.sum_range_succ, Finset.Nat.antidiagonal_succ, sC, eC, tC]
    | 1 => norm_num [Finset.sum_range_succ, Finset.Nat.antidiagonal_succ, sC, eC, tC]
    | 2 => norm_num [Finset.sum_range_succ, Finset.Nat.antidiagonal_succ, sC, eC, tC]
    | 3 => norm_num [Finset.sum_range_succ, Finset.Nat.antidiagonal_succ, sC, eC, tC]
    | k + 4 =>
      rw [show k + 4 + 2 = k + 6 by omega, sum_tC, show k + 4 + 1 = k + 5 by omega,
        conv_sC_eC, tC_ge (by omega), cf3]
      push_cast
      field_simp
      ring

lemma bstEL4_succ (m : ℕ) :
    bstEL4 (m + 2) = (2 * ∑ k ∈ range (m + 2), bstEL4 k
      + 8 * ∑ p ∈ antidiagonal (m + 1), tC p.1 * eC p.2
      + 6 * ∑ p ∈ antidiagonal (m + 1), sC p.1 * sC p.2) / (m + 2) := by
  rw [bstEL4, bstE_succ]
  have hin : ∀ p ∈ antidiagonal (m + 1), (∑ l ∈ trees p.1, ∑ r ∈ trees p.2,
      bstW l * bstW r * (fun t : T => (leaves t : ℚ) ^ 4) (.node () l r))
        = bstEL4 p.1 + bstEL4 p.2 + ((4 * (tC p.1 * eC p.2) + 4 * (eC p.1 * tC p.2))
          + 6 * (sC p.1 * sC p.2)) := by
    intro p hp
    rw [dsum_congr (G := fun l r => ((leaves l : ℚ) ^ 4 + (leaves r : ℚ) ^ 4)
        + ((4 * ((leaves l : ℚ) ^ 3 * (leaves r : ℚ)) + 4 * ((leaves l : ℚ) * (leaves r : ℚ) ^ 3))
          + 6 * ((leaves l : ℚ) ^ 2 * (leaves r : ℚ) ^ 2)))
      (fun l r hl hr => by dsimp only; rw [split_node hp hl hr]; ring),
      dsum_add, dsum_add, dsum_add, dsum_add, dsum_fst, dsum_snd, dsum_cmul, dsum_cmul,
      dsum_cmul]
    have h1 := bst_EL p.1
    have h2 := bst_EL p.2
    have h3 := bst_EL2 p.1
    have h4 := bst_EL2 p.2
    have h5 := bst_EL3_all p.1
    have h6 := bst_EL3_all p.2
    rw [bstEL] at h1 h2
    rw [bstEL2] at h3 h4
    rw [bstEL3] at h5 h6
    rw [h1, h2, h3, h4, h5, h6]
    rfl
  rw [Finset.sum_congr rfl hin, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, sum_anti_fst, sum_anti_snd,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, anti_swap (m + 1) eC tC]
  push_cast
  ring

/-- **`E[L_n⁴]` for every `n`.** -/
theorem bst_EL4_all (n : ℕ) : bstEL4 n = fC n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  match n with
  | 0 => simp [bstEL4, bstE_zero, fC]
  | 1 => simp [bstEL4, bstE_succ, bstW, leaves, isNode, fC]
  | m + 2 =>
    rw [bstEL4_succ]
    have hs : ∑ k ∈ range (m + 2), bstEL4 k = ∑ k ∈ range (m + 2), fC k :=
      Finset.sum_congr rfl (fun k hk => ih k (by have := Finset.mem_range.mp hk; omega))
    rw [hs]
    match m with
    | 0 => norm_num [Finset.sum_range_succ, Finset.Nat.antidiagonal_succ, sC, eC, tC, fC]
    | 1 => norm_num [Finset.sum_range_succ, Finset.Nat.antidiagonal_succ, sC, eC, tC, fC]
    | 2 => norm_num [Finset.sum_range_succ, Finset.Nat.antidiagonal_succ, sC, eC, tC, fC]
    | 3 => norm_num [Finset.sum_range_succ, Finset.Nat.antidiagonal_succ, sC, eC, tC, fC]
    | 4 => norm_num [Finset.sum_range_succ, Finset.Nat.antidiagonal_succ, sC, eC, tC, fC, cf3]
    | 5 => norm_num [Finset.sum_range_succ, Finset.Nat.antidiagonal_succ, sC, eC, tC, fC, cf3]
    | k + 6 =>
      rw [show k + 6 + 2 = k + 8 by omega, sum_fC, show k + 6 + 1 = k + 7 by omega,
        conv_tC_eC, conv_sC_sC, fC_ge (by omega), cf4]
      push_cast
      field_simp
      ring

end BstCum

open BstCum

/-! ## 5. The headline theorems -/

/-- **`E[L_n³]` in closed form for `n ≥ 6`** (Rocq: `EL3_closed`). -/
theorem bst_EL3 (n : ℕ) (hn : 6 ≤ n) : bstEL3 n = cf3 n := by
  rw [bst_EL3_all, tC_ge hn]

/-- **The third cumulant `κ₃(L_n) = −2(n+1)/945` for `n ≥ 6`** (Rocq: `KappaL3_closed`). -/
theorem bst_kappa3 (n : ℕ) (hn : 6 ≤ n) :
    bstEL3 n - 3 * bstEL2 n * bstEL n + 2 * bstEL n ^ 3 = -2 * ((n : ℚ) + 1) / 945 := by
  rw [bst_EL3 n hn, bst_EL2, bst_EL, sC_ge (by omega), eC_ge (by omega), cf3]
  ring

/-- **`E[L_n⁴]` in closed form for `n ≥ 8`** (Rocq: `EL4_closed`). -/
theorem bst_EL4 (n : ℕ) (hn : 8 ≤ n) : bstEL4 n = cf4 n := by
  rw [bst_EL4_all, fC_ge hn]

/-- **The fourth cumulant `κ₄(L_n) = −22(n+1)/4725` for `n ≥ 8`** (Rocq: `KappaL4_closed`). -/
theorem bst_kappa4 (n : ℕ) (hn : 8 ≤ n) :
    bstEL4 n - 4 * bstEL3 n * bstEL n - 3 * bstEL2 n ^ 2 + 12 * bstEL2 n * bstEL n ^ 2
      - 6 * bstEL n ^ 4 = -22 * ((n : ℚ) + 1) / 4725 := by
  rw [bst_EL4 n hn, bst_EL3 n (by omega), bst_EL2, bst_EL, sC_ge (by omega), eC_ge (by omega),
    cf4, cf3]
  ring

end MakinenAnalysis
