import Mathlib
import MakinenAnalysis.Asymptotics

/-!
# The double-pop (two-children-node) count: towards Proposition 12 / Theorem 13

`paper_en.tex`, Proposition 12 (`prop:leafclt`) asserts a CLT for the leaf
count `L` of a uniform binary tree; Theorem 13 (`thm:Nclt`) the CLT for
`A_N = S + P₂ + (n+2)`, where on the codeword side `P₂ = #{i : x_i ≥ 2}` is
the number of double pops (= two-children nodes = `L - 1`, Lemma 3 / Rocq
`P2_identity`).

This file starts the programme laid out in `README.md`:

1. **Exact law infrastructure (proved).**  `P2` on codewords, the refined
   count `U ℓ h k` of valid words with `P2 = k`, and
   `card_filter_P2 : #((suffixes ℓ h).filter (P2 · = k)) = U ℓ h k`.
   Structure lemmas: `U_eq_zero_of_gt` (at most `ℓ` double pops), `U_zero`
   (`U ℓ h 0 = 2^ℓ`, the chains — the `k = 0` case `U_mul_closed_zero` of the
   closed-form target), and `sum_U` / `sum_U_eq_card` (the refined counts
   partition the sample space: `Σ_k U ℓ h k = W (ℓ+1) h 1 = #(suffixes ℓ h)`,
   tying this file to `BallotCount`).
2. **The correct closed form, machine-pinned (proved by `decide`).**
   The number of `n`-node binary trees with `k` two-children nodes is
   `(1/n)·C(n,k)·C(n-k, n-1-2k)·2^(n-1-2k)`   (Lagrange inversion on
   `B = z(1+2B+uB²)`).  *Not* the Narayana numbers — those count leaves of
   *plane* trees.  The instances below verify the multiplicative form for all
   `n ≤ 8` inside the kernel.
3. **The reduction, PROVED (`AN_CLT_of_leafCLT`).**  Theorem 13 is
   machine-reduced to Proposition 12: since `A_N − P₂` differs from a constant
   by `h = n − S` with mean exactly `3n/(n+2)` (`sum_finalH_mul_eq`), the
   characteristic functions differ by at most `24|t|/√n`
   (`norm_charAN_sub_charP2_le`), Slutsky-free.
4. **Precise remaining targets (`proof_wanted`).**  The general closed form
   (`U_mul_closed`, via the cycle lemma `dvoretzky_motzkin`) and the CLT for
   `P₂` at the characteristic-function level (`leafCLT_charFun` — equivalent
   to Proposition 12 by Lévy continuity; `AN_CLT_charFun` = Theorem 13 then
   follows by item 3).

The remaining hard analysis for `leafCLT_charFun` is a local-limit/Laplace
estimate on the explicit law (Stirling is available:
`Mathlib.Analysis.SpecialFunctions.Stirling`) — see `README.md`.
-/


namespace MakinenAnalysis

open Finset Filter Topology

/-- Number of double pops of a codeword: letters `≥ 2`
    (= two-children nodes of the tree = leaves − 1). -/
def P2 : List ℕ → ℕ
  | [] => 0
  | x :: w => (if 2 ≤ x then 1 else 0) + P2 w

/-- Count of valid words of length `ℓ` from height `h` with exactly `k`
    letters `≥ 2`. -/
def U : ℕ → ℕ → ℕ → ℕ
  | 0, _, k => if k = 0 then 1 else 0
  | ℓ + 1, h, k => ∑ x ∈ range (h + 1),
      if 2 ≤ x then (if k = 0 then 0 else U ℓ (h + 1 - x) (k - 1))
      else U ℓ (h + 1 - x) k

/-- The recursive count is the cardinality of the refined codeword set. -/
lemma card_filter_P2 : ∀ (ℓ h k : ℕ),
    ((suffixes ℓ h).filter fun w => P2 w = k).card = U ℓ h k := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro h k
    show (({([] : List ℕ)} : Finset (List ℕ)).filter fun w => P2 w = k).card
      = if k = 0 then 1 else 0
    rw [Finset.filter_singleton]
    by_cases hk : k = 0
    · subst hk
      rw [if_pos (show P2 [] = 0 from rfl), if_pos rfl, Finset.card_singleton]
    · rw [if_neg (show ¬P2 [] = k from by simpa [P2, eq_comm] using hk),
          if_neg hk, Finset.card_empty]
  | succ ℓ ih =>
    intro h k
    show ((((range (h + 1)).biUnion fun x =>
        (suffixes ℓ (h + 1 - x)).image (x :: ·))).filter fun w => P2 w = k).card
      = ∑ x ∈ range (h + 1),
          if 2 ≤ x then (if k = 0 then 0 else U ℓ (h + 1 - x) (k - 1))
          else U ℓ (h + 1 - x) k
    rw [Finset.filter_biUnion]
    have hcong : ((range (h + 1)).biUnion fun x =>
          ((suffixes ℓ (h + 1 - x)).image (x :: ·)).filter fun w => P2 w = k)
        = (range (h + 1)).biUnion fun x =>
          ((suffixes ℓ (h + 1 - x)).filter fun v => P2 (x :: v) = k).image (x :: ·) :=
      Finset.biUnion_congr rfl fun x _ => Finset.filter_image
    rw [hcong, Finset.card_biUnion (consImage_pairwiseDisjoint _ _)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.card_image_of_injective _ List.cons_injective]
    by_cases hx : 2 ≤ x
    · by_cases hk : k = 0
      · subst hk
        rw [if_pos hx, if_pos rfl]
        rw [Finset.filter_false_of_mem fun v _ => by
          show ¬((if 2 ≤ x then 1 else 0) + P2 v = 0)
          rw [if_pos hx]; omega]
        exact Finset.card_empty
      · rw [if_pos hx, if_neg hk, ← ih]
        congr 1
        refine Finset.filter_congr fun v _ => ?_
        show ((if 2 ≤ x then 1 else 0) + P2 v = k) ↔ P2 v = k - 1
        rw [if_pos hx]; omega
    · rw [if_neg hx, ← ih]
      congr 1
      refine Finset.filter_congr fun v _ => ?_
      show ((if 2 ≤ x then 1 else 0) + P2 v = k) ↔ P2 v = k
      rw [if_neg hx]; omega

/-! ### First structure lemmas for `U` -/

/-- A word of length `ℓ` has at most `ℓ` letters `≥ 2`. -/
lemma U_eq_zero_of_gt : ∀ ℓ h k : ℕ, ℓ < k → U ℓ h k = 0 := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro h k hk
    show (if k = 0 then 1 else 0) = 0
    rw [if_neg (by omega)]
  | succ ℓ ih =>
    intro h k hk
    show (∑ x ∈ range (h + 1),
        if 2 ≤ x then (if k = 0 then 0 else U ℓ (h + 1 - x) (k - 1))
        else U ℓ (h + 1 - x) k) = 0
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : 2 ≤ x
    · rw [if_pos hx, if_neg (by omega : ¬k = 0)]
      exact ih _ _ (by omega)
    · rw [if_neg hx]
      exact ih _ _ (by omega)

private lemma sum_ite_two_le (c : ℕ) : ∀ h : ℕ, 1 ≤ h →
    (∑ x ∈ range (h + 1), if 2 ≤ x then 0 else c) = 2 * c := by
  intro h
  induction h with
  | zero => intro h1; exact absurd h1 (by norm_num)
  | succ h ih =>
    intro _
    rw [Finset.sum_range_succ]
    by_cases hh : 1 ≤ h
    · rw [ih hh, if_pos (by omega)]
      omega
    · have h0 : h = 0 := by omega
      subst h0
      rw [Finset.sum_range_one, if_neg (by omega : ¬(2 : ℕ) ≤ 0),
          if_neg (by omega : ¬(2 : ℕ) ≤ 1)]
      omega

/-- With no letter `≥ 2` every step is unconstrained (the height never
    decreases): the words counted by `U ℓ h 0` are the `2^ℓ` chains. -/
lemma U_zero : ∀ ℓ h : ℕ, 1 ≤ h → U ℓ h 0 = 2 ^ ℓ := by
  intro ℓ
  induction ℓ with
  | zero => intro h _; rfl
  | succ ℓ ih =>
    intro h hh
    show (∑ x ∈ range (h + 1),
        if 2 ≤ x then (if (0 : ℕ) = 0 then 0 else U ℓ (h + 1 - x) (0 - 1))
        else U ℓ (h + 1 - x) 0) = 2 ^ (ℓ + 1)
    have hcong : ∀ x ∈ range (h + 1),
        (if 2 ≤ x then (if (0 : ℕ) = 0 then 0 else U ℓ (h + 1 - x) (0 - 1))
         else U ℓ (h + 1 - x) 0)
        = (if 2 ≤ x then 0 else 2 ^ ℓ) := by
      intro x _
      by_cases hx : 2 ≤ x
      · rw [if_pos hx, if_pos hx, if_pos rfl]
      · rw [if_neg hx, if_neg hx, ih _ (by omega)]
    rw [Finset.sum_congr rfl hcong, sum_ite_two_le _ h hh]
    ring

/-- The `k = 0` instance of the closed-form target `U_mul_closed`:
    `n · U(n-1,1,0) = n · 2^(n-1)` — the chains. -/
lemma U_mul_closed_zero (n : ℕ) (hn : 1 ≤ n) :
    n * U (n - 1) 1 0
      = n.choose 0 * (n - 0).choose (n - 1 - 2 * 0) * 2 ^ (n - 1 - 2 * 0) := by
  have h1 : n.choose (n - 1) = n := by
    have h := Nat.choose_symm (show 1 ≤ n from hn)
    rwa [Nat.choose_one_right] at h
  rw [U_zero _ _ le_rfl, Nat.choose_zero_right, Nat.sub_zero,
      show n - 1 - 2 * 0 = n - 1 by omega, h1]
  ring

/-- Marginal consistency: summing the refined counts over `k` recovers the
    total count `W (ℓ+1) h 1` of `MakinenAnalysis.BallotCount`. -/
lemma sum_U : ∀ ℓ h : ℕ, (∑ k ∈ range (ℓ + 1), U ℓ h k) = W (ℓ + 1) h 1 := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro h
    rw [Finset.sum_range_one, ← card_suffixes 0 h]
    show 1 = ({([] : List ℕ)} : Finset (List ℕ)).card
    exact (Finset.card_singleton _).symm
  | succ ℓ ih =>
    intro h
    show (∑ k ∈ range (ℓ + 1 + 1), ∑ x ∈ range (h + 1),
        if 2 ≤ x then (if k = 0 then 0 else U ℓ (h + 1 - x) (k - 1))
        else U ℓ (h + 1 - x) k)
      = W (ℓ + 1 + 1) h 1
    rw [Finset.sum_comm]
    have hx : ∀ x ∈ range (h + 1),
        (∑ k ∈ range (ℓ + 1 + 1),
          if 2 ≤ x then (if k = 0 then 0 else U ℓ (h + 1 - x) (k - 1))
          else U ℓ (h + 1 - x) k)
        = W (ℓ + 1) (h + 1 - x) 1 := by
      intro x _
      by_cases h2x : 2 ≤ x
      · simp only [if_pos h2x]
        rw [Finset.sum_range_succ', if_pos rfl, add_zero]
        rw [Finset.sum_congr rfl fun i (_ : i ∈ range (ℓ + 1)) => by
          rw [if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel]]
        exact ih _
      · simp only [if_neg h2x]
        rw [Finset.sum_range_succ, U_eq_zero_of_gt ℓ _ (ℓ + 1) (by omega), add_zero]
        exact ih _
    rw [Finset.sum_congr rfl hx]
    rfl

/-- The refined counts partition the sample space. -/
lemma sum_U_eq_card (ℓ h : ℕ) :
    (∑ k ∈ range (ℓ + 1), U ℓ h k) = (suffixes ℓ h).card := by
  rw [sum_U, card_suffixes]

/-! ### The exact mean of the final stack height (and of `S`)

`E[h] = 3n/(n+2)` and `E[S] = n(n-1)/(n+2)` (paper, Theorem 5) as *finite-sum
identities* over the codeword space.  The key observation collapsing the mean
to a single `W`-value: `Σ_w h(w) = Σ_{j≥1} #{w : h(w) ≥ j}` (layer cake), and
appending one forced letter is a bijection `{h ≥ j} ≃ {words one longer ending
exactly at j+1}` — applying it twice gives `Σ_w h(w) = W (ℓ+2) h 3`.
Numerically the whole layer cake reduces to one structural induction whose
step is literally `W`'s defining recurrence.  These identities feed the
`AN_CLT_of_leafCLT` reduction (`E[h] ≤ 3`). -/

/-- Conservation: on valid words, `finalH h w + sum w = h + length w`
    (each letter pushes one and pops `x`). -/
lemma finalH_add_sum : ∀ (w : List ℕ) (h : ℕ), Valid h w →
    finalH h w + w.sum = h + w.length := by
  intro w
  induction w with
  | nil => intro h _; simp [finalH]
  | cons x v ih =>
    intro h hv
    obtain ⟨hx, hv'⟩ := hv
    have hrec := ih (h + 1 - x) hv'
    show finalH (h + 1 - x) v + (x + v.sum) = h + (v.length + 1)
    omega

private lemma W_one_three : ∀ h : ℕ, 2 ≤ h → W 1 h 3 = 1 := by
  intro h h2
  show (∑ y ∈ range (h + 1), W 0 (h + 1 - y) 3) = 1
  rw [Finset.sum_eq_single (h - 2)
    (fun y hy hne => by
      simp only [Finset.mem_range] at hy
      show (if (3 : ℕ) = h + 1 - y then 1 else 0) = 0
      rw [if_neg (by omega)])
    (fun habs => absurd (Finset.mem_range.mpr (by omega)) habs)]
  show (if (3 : ℕ) = h + 1 - (h - 2) then 1 else 0) = 1
  rw [if_pos (by omega)]

private lemma W_two_three : ∀ h : ℕ, W 2 h 3 = h := by
  intro h
  induction h with
  | zero =>
    show (∑ x ∈ range 1, W 1 (0 + 1 - x) 3) = 0
    rw [Finset.sum_range_one]
    exact W_eq_zero 1 1 3 (by omega)
  | succ h ih =>
    show (∑ x ∈ range (h + 1 + 1), W 1 (h + 1 + 1 - x) 3) = h + 1
    rw [Finset.sum_range_succ']
    rw [Finset.sum_congr rfl fun i (_ : i ∈ range (h + 1)) => by
      rw [show h + 1 + 1 - (i + 1) = h + 1 - i by omega]]
    have hfst : (∑ i ∈ range (h + 1), W 1 (h + 1 - i) 3) = h := ih
    rw [hfst, show h + 1 + 1 - 0 = h + 2 by omega, W_one_three (h + 2) (by omega)]

/-- **The mean collapses to one `W`-value**:
    `Σ_{w ∈ suffixes ℓ h} finalH h w = W (ℓ+2) h 3`. -/
lemma sum_finalH : ∀ ℓ h : ℕ, (∑ w ∈ suffixes ℓ h, finalH h w) = W (ℓ + 2) h 3 := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro h
    show (∑ w ∈ ({([] : List ℕ)} : Finset (List ℕ)), finalH h w) = W 2 h 3
    rw [Finset.sum_singleton, W_two_three]
    rfl
  | succ ℓ ih =>
    intro h
    show (∑ w ∈ (range (h + 1)).biUnion
        fun x => (suffixes ℓ (h + 1 - x)).image (x :: ·), finalH h w)
      = W (ℓ + 1 + 2) h 3
    rw [Finset.sum_biUnion (consImage_pairwiseDisjoint _ _)]
    have hx : ∀ x ∈ range (h + 1),
        (∑ w ∈ (suffixes ℓ (h + 1 - x)).image (x :: ·), finalH h w)
        = W (ℓ + 2) (h + 1 - x) 3 := by
      intro x _
      rw [Finset.sum_image fun a _ b _ hab => List.cons_injective hab]
      exact (Finset.sum_congr rfl fun v _ => rfl).trans (ih _)
    rw [Finset.sum_congr rfl hx]
    rfl

/-- **`E[h] = 3n/(n+2)` exactly**, as the finite-sum identity
    `(n+2) · Σ_w h(w) = 3n · catalan n`. -/
theorem sum_finalH_mul_eq (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) + 2) * ((∑ w ∈ suffixes (n - 1) 1, finalH 1 w : ℕ) : ℝ)
      = 3 * (n : ℝ) * (catalan n : ℝ) := by
  have hsf := sum_finalH (n - 1) 1
  rw [show n - 1 + 2 = n + 1 by omega] at hsf
  rw [hsf]
  by_cases hn1 : n = 1
  · subst hn1
    have h1 : W 2 1 3 = 1 := W_two_three 1
    rw [h1]
    norm_num [catalan_one]
  · have hn2 : 2 ≤ n := by omega
    -- W (n+1) 1 3 + C(2n-1, n+2) = C(2n-1, n)
    have hW := W_add_choose n 1 3 (by omega) (by omega)
    rw [show 2 * n + 1 + 1 - 3 = 2 * n - 1 by omega,
        show n + 1 + 1 = n + 2 by omega] at hW
    -- one-step ratios and Pascal
    have hR1 := Nat.choose_succ_right_eq (2 * n - 1) n
    rw [show 2 * n - 1 - n = n - 1 by omega] at hR1
    have hR2 := Nat.choose_succ_right_eq (2 * n - 1) (n + 1)
    rw [show 2 * n - 1 - (n + 1) = n - 2 by omega] at hR2
    have hP := Nat.choose_succ_succ' (2 * n - 1) (n - 1)
    rw [show 2 * n - 1 + 1 = 2 * n by omega, show n - 1 + 1 = n by omega] at hP
    have hS := Nat.choose_symm (show n ≤ 2 * n - 1 by omega)
    rw [show 2 * n - 1 - n = n - 1 by omega] at hS
    have hcat := succ_mul_catalan_eq_centralBinom n
    -- ℝ casts
    have hc1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hc2 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hWR : (W (n + 1) 1 3 : ℝ) + ((2 * n - 1).choose (n + 2) : ℝ)
        = ((2 * n - 1).choose n : ℝ) := by exact_mod_cast hW
    have hR1R : ((2 * n - 1).choose (n + 1) : ℝ) * ((n : ℝ) + 1)
        = ((2 * n - 1).choose n : ℝ) * ((n : ℝ) - 1) := by
      rw [← hc1]; exact_mod_cast hR1
    have hR2R : ((2 * n - 1).choose (n + 2) : ℝ) * ((n : ℝ) + 2)
        = ((2 * n - 1).choose (n + 1) : ℝ) * ((n : ℝ) - 2) := by
      rw [← hc2]; exact_mod_cast hR2
    have hPR : ((2 * n).choose n : ℝ)
        = ((2 * n - 1).choose (n - 1) : ℝ) + ((2 * n - 1).choose n : ℝ) := by
      exact_mod_cast hP
    have hSR : ((2 * n - 1).choose (n - 1) : ℝ) = ((2 * n - 1).choose n : ℝ) := by
      exact_mod_cast hS
    have hcatR : ((n : ℝ) + 1) * (catalan n : ℝ)
        = ((2 * n).choose n : ℝ) := by
      rw [show ((2 * n).choose n : ℝ) = (Nat.centralBinom n : ℝ) by
        rw [Nat.centralBinom_eq_two_mul_choose]]
      exact_mod_cast hcat
    have key : ((n : ℝ) + 1) * (((n : ℝ) + 2) * (W (n + 1) 1 3 : ℝ))
        = ((n : ℝ) + 1) * (3 * (n : ℝ) * (catalan n : ℝ)) := by
      linear_combination ((n : ℝ) + 1) * ((n : ℝ) + 2) * hWR - ((n : ℝ) + 1) * hR2R
        - ((n : ℝ) - 2) * hR1R - 3 * (n : ℝ) * hcatR - 3 * (n : ℝ) * hPR
        - 3 * (n : ℝ) * hSR
    have key2 := mul_left_cancel₀ (by positivity : ((n : ℝ) + 1) ≠ 0) key
    linear_combination key2

/-- **`E[S] = n(n-1)/(n+2)` exactly**, as the finite-sum identity
    `(n+2) · Σ_w (sum w) = n(n-1) · catalan n`. -/
theorem sum_listSum_mul_eq (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) + 2) * ((∑ w ∈ suffixes (n - 1) 1, w.sum : ℕ) : ℝ)
      = (n : ℝ) * ((n : ℝ) - 1) * (catalan n : ℝ) := by
  -- pointwise: h(w) + S(w) = n on the sample space
  have hpt : ∀ w ∈ suffixes (n - 1) 1, finalH 1 w + w.sum = n := by
    intro w hw
    obtain ⟨hlen, hval⟩ := (mem_suffixes _ _ w).mp hw
    have := finalH_add_sum w 1 hval
    omega
  have hsum : (∑ w ∈ suffixes (n - 1) 1, (finalH 1 w + w.sum))
      = catalan n * n := by
    rw [Finset.sum_congr rfl hpt, Finset.sum_const,
        card_suffixes_eq_catalan n hn, smul_eq_mul]
  rw [Finset.sum_add_distrib] at hsum
  have hcast : ((∑ w ∈ suffixes (n - 1) 1, finalH 1 w : ℕ) : ℝ)
      + ((∑ w ∈ suffixes (n - 1) 1, w.sum : ℕ) : ℝ)
      = (catalan n : ℝ) * (n : ℝ) := by exact_mod_cast hsum
  have hH := sum_finalH_mul_eq n hn
  linear_combination ((n : ℝ) + 2) * hcast - hH

/-! ### The correct closed form, machine-pinned

The number of `n`-node binary trees with `k` two-children nodes is
`(1/n)·C(n,k)·C(n-k, n-1-2k)·2^(n-1-2k)` (Lagrange inversion on
`B = z(1+2B+uB²)`, extracting `[z^n u^k]`).  The following kernel-checked
instances pin the multiplicative form for every `n ≤ 8`, guarding against a
mis-stated target (the plausible-looking "Narayana" guess `N(n,k+1)` is
*wrong*: it counts plane-tree leaves and already fails at `n = 3`). -/

example : ∀ n < 9, ∀ k < 5, 2 * k + 1 ≤ n →
    n * U (n - 1) 1 k
      = n.choose k * (n - k).choose (n - 1 - 2 * k) * 2 ^ (n - 1 - 2 * k) := by
  decide

/-- **Target (Lagrange-inversion identity).**  The refined count in closed
    form, multiplicative shape. -/
proof_wanted U_mul_closed (n k : ℕ) (hn : 1 ≤ n) (hk : 2 * k + 1 ≤ n) :
    n * U (n - 1) 1 k
      = n.choose k * (n - k).choose (n - 1 - 2 * k) * 2 ^ (n - 1 - 2 * k)

/-! #### The route to `U_mul_closed`: the cycle lemma

Unlike Lemma 2's ballot count, `U ℓ h k` has **no product closed form for
general `h`** (already `U(ℓ,h,1)` is `ℓ2^{ℓ-1}h - c_ℓ` with non-product
constants), so the Pascal-glued double induction of `W_add_choose` does not
transfer.  The natural proof is combinatorial:

1. **Dvoretzky–Motzkin cycle lemma** (stated below): a sequence of integer
   steps `≤ 1` with total sum `1` has exactly one everywhere-positive
   rotation.
2. Apply it to *degree words* (children counts `∈ {0, 1ᴸ, 1ᴿ, 2}` in
   preorder, letter `d` contributing step `d - 1`): the arrangements with `k`
   two-letters number `C(n,k)·C(n-k,k+1)·2^(n-1-2k)` (multinomial), rotations
   partition them into orbits of size `n` (the sum `n-1` is coprime-free), and
   each orbit has exactly one valid tree word — giving the closed form for
   trees, hence for pop-codewords via a `P2`-preserving encoding bridge
   (mirroring the Rocq-side `Codewords.v`). -/

-- The **Dvoretzky–Motzkin cycle lemma** (step 1 of the route above) is now
-- PROVED in `MakinenAnalysis.CycleLemma` (`dvoretzky_motzkin`), including the
-- rotation prefix-sum calculus and the integrality uniqueness argument.

/-! ### CLT targets at the characteristic-function level

By Lévy's continuity theorem (`ProbabilityMeasure.tendsto_iff_tendsto_charFun`,
in Mathlib), pointwise convergence of characteristic functions to
`exp(-t²/2)` is equivalent to the CLT.  Stating the targets on the finite
uniform law as plain `Finset.sum`s keeps them elementary. -/

/-- Exact mean of `P₂` under the uniform law: `(n-1)(n-2)/(2(2n-1))`
    (paper, Theorem 5). -/
noncomputable def EP2 (n : ℕ) : ℝ :=
  ((n : ℝ) - 1) * ((n : ℝ) - 2) / (2 * (2 * (n : ℝ) - 1))

/-- Characteristic function of the standardised double-pop count
    `(P₂ - E[P₂])/(√n/4)` under the uniform law on valid codewords. -/
noncomputable def charP2 (n : ℕ) (t : ℝ) : ℂ :=
  (∑ w ∈ suffixes (n - 1) 1,
      Complex.exp (Complex.I *
        Complex.ofReal (t * (((P2 w : ℝ) - EP2 n) * 4 / Real.sqrt n))))
    / (catalan n : ℂ)

/-- The comparison count of the improved algorithm on a codeword:
    `A_N = S + P₂ + (n+2)` (paper, eq. (4)). -/
def ANw (n : ℕ) (w : List ℕ) : ℕ := w.sum + P2 w + (n + 2)

/-- Characteristic function of the standardised `A_N`. -/
noncomputable def charAN (n : ℕ) (t : ℝ) : ℂ :=
  (∑ w ∈ suffixes (n - 1) 1,
      Complex.exp (Complex.I *
        Complex.ofReal (t * (((ANw n w : ℝ) - EAN n) * 4 / Real.sqrt n))))
    / (catalan n : ℂ)

/-- **Proposition 12 (`prop:leafclt`), charFun form.**  The standardised
    double-pop (leaf) count is asymptotically `N(0,1)`. -/
proof_wanted leafCLT_charFun (t : ℝ) :
    Tendsto (fun n : ℕ => charP2 n t) atTop (nhds (Complex.exp (-(t : ℂ) ^ 2 / 2)))

/-- **Theorem 13 (`thm:Nclt`), charFun form.**  The standardised comparison
    count of `N` is asymptotically `N(0,1)`. -/
proof_wanted AN_CLT_charFun (t : ℝ) :
    Tendsto (fun n : ℕ => charAN n t) atTop (nhds (Complex.exp (-(t : ℂ) ^ 2 / 2)))

/-! ### The reduction: Theorem 13 from Proposition 12 (proved)

`A_N` and `P₂` differ by `n + 2 + S = 2n + 2 - h`, so the standardised
versions differ pointwise by `(E[h] - h)·4t/√n` with `E[h] = 3n/(n+2)`
(exactly the mean identity `sum_finalH_mul_eq`).  Hence, by
`|e^{ix} − e^{iy}| ≤ |x − y|`,
`‖charAN − charP2‖ ≤ (4|t|/√n)·E|E[h] − h| ≤ (4|t|/√n)·2E[h] ≤ 24|t|/√n → 0`
— Slutsky-free, at the characteristic-function level. -/

private lemma norm_exp_I_sub_exp_I (x y : ℝ) :
    ‖Complex.exp (Complex.I * x) - Complex.exp (Complex.I * y)‖ ≤ |x - y| := by
  have harg : Complex.I * (x : ℂ) = Complex.I * (y : ℂ) + Complex.I * ((x - y : ℝ) : ℂ) := by
    push_cast; ring
  have hfact : Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ))
      = Complex.exp (Complex.I * (y : ℂ))
        * (Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add, ← harg]
  rw [hfact, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  simpa using Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y)

private lemma abs_dev_nonneg_bound (n : ℕ) (hn : 1 ≤ n) (w : List ℕ) :
    |3 * (n : ℝ) / ((n : ℝ) + 2) - (finalH 1 w : ℝ)|
      ≤ 3 * (n : ℝ) / ((n : ℝ) + 2) + (finalH 1 w : ℝ) := by
  have h1 : (0 : ℝ) ≤ 3 * (n : ℝ) / ((n : ℝ) + 2) := by positivity
  have h2 : (0 : ℝ) ≤ ((finalH 1 w : ℕ) : ℝ) := Nat.cast_nonneg _
  calc |3 * (n : ℝ) / ((n : ℝ) + 2) - (finalH 1 w : ℝ)|
      ≤ |3 * (n : ℝ) / ((n : ℝ) + 2)| + |(finalH 1 w : ℝ)| := abs_sub _ _
    _ = 3 * (n : ℝ) / ((n : ℝ) + 2) + (finalH 1 w : ℝ) := by
        rw [abs_of_nonneg h1, abs_of_nonneg h2]

/-- The mean absolute deviation of `h` from `3n/(n+2)` is at most `6·catalan n`
    (crude triangle bound, using the exact mean `sum_finalH_mul_eq`). -/
private lemma sum_abs_dev_le (n : ℕ) (hn : 1 ≤ n) :
    (∑ w ∈ suffixes (n - 1) 1,
        |3 * (n : ℝ) / ((n : ℝ) + 2) - (finalH 1 w : ℝ)|)
      ≤ 6 * (catalan n : ℝ) := by
  have h2pos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hcatpos : (0 : ℝ) < (catalan n : ℝ) := by
    have h := Cat_ne_zero n
    simp only [Cat] at h
    exact_mod_cast Nat.pos_of_ne_zero (by exact_mod_cast h)
  have hHle : ((∑ w ∈ suffixes (n - 1) 1, finalH 1 w : ℕ) : ℝ)
      ≤ 3 * (catalan n : ℝ) := by
    have hH := sum_finalH_mul_eq n hn
    nlinarith [hcatpos]
  have hterm : 3 * (n : ℝ) / ((n : ℝ) + 2) ≤ 3 := by
    rw [div_le_iff₀ h2pos]; nlinarith
  have hsplit : (∑ w ∈ suffixes (n - 1) 1,
      (3 * (n : ℝ) / ((n : ℝ) + 2) + (finalH 1 w : ℝ)))
      = (catalan n : ℝ) * (3 * (n : ℝ) / ((n : ℝ) + 2))
        + ((∑ w ∈ suffixes (n - 1) 1, finalH 1 w : ℕ) : ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, card_suffixes_eq_catalan n hn,
        nsmul_eq_mul, Nat.cast_sum]
  have hbound := Finset.sum_le_sum
    (fun w (_ : w ∈ suffixes (n - 1) 1) => abs_dev_nonneg_bound n hn w)
  have hcm : (catalan n : ℝ) * (3 * (n : ℝ) / ((n : ℝ) + 2))
      ≤ (catalan n : ℝ) * 3 :=
    mul_le_mul_of_nonneg_left hterm (le_of_lt hcatpos)
  calc (∑ w ∈ suffixes (n - 1) 1,
        |3 * (n : ℝ) / ((n : ℝ) + 2) - (finalH 1 w : ℝ)|)
      ≤ (∑ w ∈ suffixes (n - 1) 1,
        (3 * (n : ℝ) / ((n : ℝ) + 2) + (finalH 1 w : ℝ))) := hbound
    _ = (catalan n : ℝ) * (3 * (n : ℝ) / ((n : ℝ) + 2))
          + ((∑ w ∈ suffixes (n - 1) 1, finalH 1 w : ℕ) : ℝ) := hsplit
    _ ≤ (catalan n : ℝ) * 3 + 3 * (catalan n : ℝ) := add_le_add hcm hHle
    _ = 6 * (catalan n : ℝ) := by ring

private lemma norm_charAN_sub_charP2_le (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    ‖charAN n t - charP2 n t‖ ≤ 24 * |t| / Real.sqrt n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsq : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have h2pos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hcatpos : (0 : ℝ) < (catalan n : ℝ) := by
    have h := Cat_ne_zero n
    simp only [Cat] at h
    exact_mod_cast Nat.pos_of_ne_zero (by exact_mod_cast h)
  -- pointwise: the standardised arguments differ by `(4t/√n)(E[h] − h_w)`
  have hargs : ∀ w ∈ suffixes (n - 1) 1,
      t * (((ANw n w : ℝ) - EAN n) * 4 / Real.sqrt n)
        - t * (((P2 w : ℝ) - EP2 n) * 4 / Real.sqrt n)
      = 4 * t / Real.sqrt n
          * (3 * (n : ℝ) / ((n : ℝ) + 2) - (finalH 1 w : ℝ)) := by
    intro w hw
    obtain ⟨hlen, hval⟩ := (mem_suffixes _ _ w).mp hw
    have hcons := finalH_add_sum w 1 hval
    have hN : finalH 1 w + w.sum = n := by omega
    have hcast : ((finalH 1 w : ℕ) : ℝ) + ((w.sum : ℕ) : ℝ) = ((n : ℕ) : ℝ) := by
      rw [← Nat.cast_add]
      exact_mod_cast hN
    have hsum : (w.sum : ℝ) = (n : ℝ) - (finalH 1 w : ℝ) := by linarith
    have hAN : (ANw n w : ℝ) = (w.sum : ℝ) + (P2 w : ℝ) + (n : ℝ) + 2 := by
      simp only [ANw]; push_cast; ring
    rw [hAN, hsum]
    simp only [EAN, EP2]
    have h21 : 2 * (2 * (n : ℝ) - 1) ≠ 0 := by
      have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith
    field_simp
    ring
  -- the difference as a single quotient
  have hquot : charAN n t - charP2 n t
      = (∑ w ∈ suffixes (n - 1) 1,
          (Complex.exp (Complex.I *
              Complex.ofReal (t * (((ANw n w : ℝ) - EAN n) * 4 / Real.sqrt n)))
            - Complex.exp (Complex.I *
              Complex.ofReal (t * (((P2 w : ℝ) - EP2 n) * 4 / Real.sqrt n)))))
        / (catalan n : ℂ) := by
    simp only [charAN, charP2, div_sub_div_same, ← Finset.sum_sub_distrib]
  -- pointwise norm bound
  have hpt : ∀ w ∈ suffixes (n - 1) 1,
      ‖Complex.exp (Complex.I *
          Complex.ofReal (t * (((ANw n w : ℝ) - EAN n) * 4 / Real.sqrt n)))
        - Complex.exp (Complex.I *
          Complex.ofReal (t * (((P2 w : ℝ) - EP2 n) * 4 / Real.sqrt n)))‖
      ≤ 4 * |t| / Real.sqrt n
          * |3 * (n : ℝ) / ((n : ℝ) + 2) - (finalH 1 w : ℝ)| := by
    intro w hw
    have h1 := norm_exp_I_sub_exp_I
      (t * (((ANw n w : ℝ) - EAN n) * 4 / Real.sqrt n))
      (t * (((P2 w : ℝ) - EP2 n) * 4 / Real.sqrt n))
    rw [hargs w hw] at h1
    have habs : |4 * t / Real.sqrt n
        * (3 * (n : ℝ) / ((n : ℝ) + 2) - (finalH 1 w : ℝ))|
        = 4 * |t| / Real.sqrt n
          * |3 * (n : ℝ) / ((n : ℝ) + 2) - (finalH 1 w : ℝ)| := by
      rw [abs_mul, abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    rw [habs] at h1
    exact h1
  -- assemble
  rw [hquot, norm_div, Complex.norm_natCast, div_le_iff₀ hcatpos]
  have hstep1 := norm_sum_le (suffixes (n - 1) 1)
    (fun w => Complex.exp (Complex.I *
        Complex.ofReal (t * (((ANw n w : ℝ) - EAN n) * 4 / Real.sqrt n)))
      - Complex.exp (Complex.I *
        Complex.ofReal (t * (((P2 w : ℝ) - EP2 n) * 4 / Real.sqrt n))))
  have hstep2 := Finset.sum_le_sum hpt
  have hstep3 : (∑ w ∈ suffixes (n - 1) 1,
      4 * |t| / Real.sqrt n
        * |3 * (n : ℝ) / ((n : ℝ) + 2) - (finalH 1 w : ℝ)|)
      = 4 * |t| / Real.sqrt n
        * (∑ w ∈ suffixes (n - 1) 1,
          |3 * (n : ℝ) / ((n : ℝ) + 2) - (finalH 1 w : ℝ)|) := by
    rw [Finset.mul_sum]
  have hstep4 : 4 * |t| / Real.sqrt n
      * (∑ w ∈ suffixes (n - 1) 1,
        |3 * (n : ℝ) / ((n : ℝ) + 2) - (finalH 1 w : ℝ)|)
      ≤ 4 * |t| / Real.sqrt n * (6 * (catalan n : ℝ)) :=
    mul_le_mul_of_nonneg_left (sum_abs_dev_le n hn) (by positivity)
  have hfin : 4 * |t| / Real.sqrt n * (6 * (catalan n : ℝ))
      = 24 * |t| / Real.sqrt n * (catalan n : ℝ) := by ring
  linarith [hstep1, hstep2, hstep3 ▸ hstep4]

/-- **The elementary reduction, PROVED (Slutsky-free)**: Theorem 13 follows
    from Proposition 12 at the characteristic-function level, via
    `‖charAN − charP2‖ ≤ 24|t|/√n` (`norm_charAN_sub_charP2_le`), which uses
    only `|e^{ix} − e^{iy}| ≤ |x − y|` and the exact mean
    `E[h] = 3n/(n+2)` (`sum_finalH_mul_eq`). -/
theorem AN_CLT_of_leafCLT
    (hP : ∀ t : ℝ, Tendsto (fun n : ℕ => charP2 n t) atTop
      (nhds (Complex.exp (-(t : ℂ) ^ 2 / 2)))) (t : ℝ) :
    Tendsto (fun n : ℕ => charAN n t) atTop
      (nhds (Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
  have hdiff : Tendsto (fun n : ℕ => charAN n t - charP2 n t) atTop (nhds 0) := by
    refine squeeze_zero_norm' (a := fun n : ℕ => 24 * |t| / Real.sqrt n) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact norm_charAN_sub_charP2_le n hn t
    · have hs : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
      have hinv : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (nhds 0) :=
        tendsto_inv_atTop_zero.comp hs
      have hmul := hinv.const_mul (24 * |t|)
      simpa [div_eq_mul_inv, mul_zero] using hmul
  have hsum := hdiff.add (hP t)
  simpa using hsum

end MakinenAnalysis
