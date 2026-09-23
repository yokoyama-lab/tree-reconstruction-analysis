import MakinenAnalysis.BallotCount
import MakinenAnalysis.Asymptotics
import MakinenAnalysis.LeafCount
import MakinenAnalysis.PopDegreeBridge

/-!
# Exact combinatorial sums on the codeword side (Lean port of the Rocq results)

The Rocq development (`../../coq/`) proves the *exact* and algebraic half of the
paper: the codeword bijection, the closed-form totals of the pop count `S` and
the double-pop count `P₂`, and hence the closed-form averages.  The Lean
development so far took those closed forms as **definitions** (`Asymptotics.EAN`,
`EAM`, `VarS`, `VarP2`, `CovSP2`) and proved only their asymptotics.

This file starts closing that gap on the Lean side: it proves, from the
combinatorial definition of the sample space `suffixes (n-1) 1`, the totals that
Rocq derives from the tree decomposition and the Catalan convolution.

| here | Rocq counterpart |
|---|---|
| `Hsum_add_card` | the recursion behind `rsum_rec` (`ReconstructES.v`) |
| `sum_finalH_add_catalan` | `rsum_closed` (`ReconstructES.v`): `Σ h + C_n = C_{n+1}` |
| `sum_pops` | `pops_sum_closed` (`ReconstructES.v`): `Σ S + C_{n+1} = (n+1) C_n` |
| `ES_rational` | `ES_rational` (`ReconstructES.v`): `(n+2) Σ S = n(n-1) C_n` |

The route differs from the Rocq one on purpose.  Rocq decomposes a tree as
"root, left subtree, right subtree" and needs the Catalan convolution; on the
codeword side the same totals follow from a single induction on the word length,
because extending a valid word on the right by one letter has exactly
`finalH h w + 1` choices.  That is the content of `Hsum_add_card`:

  `Σ_{w : |w| = ℓ} finalH h w  +  #{w : |w| = ℓ}  =  #{w : |w| = ℓ+1}`.

Everything stays in ℕ and additive, so truncated subtraction never has to be
unfolded.  Every result below is fully proved: there are no unproved holes, no
kernel-bypassing evaluation, and no axioms beyond Mathlib's standard three
(`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace MakinenAnalysis

open Finset Polynomial

/-- Total of the final stack heights over all valid words of length `ℓ` read
    from stack height `h`. -/
def Hsum (ℓ h : ℕ) : ℕ := ∑ w ∈ suffixes ℓ h, finalH h w

/-! ### Splitting a sum over `suffixes` along the first letter -/

/-- `suffixes (ℓ+1) h` is the disjoint union over the first letter `x ≤ h` of
    the words `x :: w` with `w` valid from height `h+1-x`; so any sum over it
    splits accordingly.  (Same disjointness argument as `card_suffixes`.) -/
lemma sum_suffixes_succ (ℓ h : ℕ) (f : List ℕ → ℕ) :
    (∑ w ∈ suffixes (ℓ + 1) h, f w)
      = ∑ x ∈ range (h + 1), ∑ w ∈ suffixes ℓ (h + 1 - x), f (x :: w) := by
  show (∑ w ∈ (range (h + 1)).biUnion
      (fun x => (suffixes ℓ (h + 1 - x)).image (x :: ·)), f w) = _
  rw [Finset.sum_biUnion (consImage_pairwiseDisjoint _ _)]
  exact Finset.sum_congr rfl fun x _ =>
    Finset.sum_image fun a _ b _ hab => by injection hab

/-- The same split for the cardinality (unfolding `suffixes` once). -/
lemma card_suffixes_succ (ℓ h : ℕ) :
    (suffixes (ℓ + 1) h).card = ∑ x ∈ range (h + 1), (suffixes ℓ (h + 1 - x)).card := by
  show ((range (h + 1)).biUnion
      (fun x => (suffixes ℓ (h + 1 - x)).image (x :: ·))).card = _
  rw [Finset.card_biUnion (consImage_pairwiseDisjoint _ _)]
  exact Finset.sum_congr rfl fun x _ => by
    rw [Finset.card_image_of_injective _ List.cons_injective]

/-- `Hsum` obeys the same first-letter recursion. -/
lemma Hsum_succ (ℓ h : ℕ) :
    Hsum (ℓ + 1) h = ∑ x ∈ range (h + 1), Hsum ℓ (h + 1 - x) := by
  unfold Hsum
  rw [sum_suffixes_succ]
  rfl

/-! ### The key counting identity -/

/-- **Right-extension count.**  Extending a valid word of length `ℓ` by one
    letter has `finalH h w + 1` choices, so

    `Σ_w finalH h w + #(words of length ℓ) = #(words of length ℓ+1)`.

    This is the codeword-side replacement for the Catalan convolution used in
    the Rocq proof of `rsum_closed`. -/
theorem Hsum_add_card : ∀ (ℓ h : ℕ),
    Hsum ℓ h + (suffixes ℓ h).card = (suffixes (ℓ + 1) h).card := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro h
    have hH : Hsum 0 h = h := by
      show (∑ w ∈ ({([] : List ℕ)} : Finset (List ℕ)), finalH h w) = h
      rw [Finset.sum_singleton]
      rfl
    have hc : (suffixes 0 h).card = 1 := by
      show ({([] : List ℕ)} : Finset (List ℕ)).card = 1
      exact Finset.card_singleton _
    have h1 : (suffixes (0 + 1) h).card = h + 1 := by
      rw [card_suffixes_succ]
      have : ∀ x ∈ range (h + 1), (suffixes 0 (h + 1 - x)).card = 1 := fun x _ =>
        Finset.card_singleton _
      rw [Finset.sum_congr rfl this]
      simp
    omega
  | succ ℓ ih =>
    intro h
    rw [Hsum_succ, card_suffixes_succ, card_suffixes_succ (ℓ + 1) h,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => ih (h + 1 - x)

/-- **Total of the final stack heights** (Rocq: `rsum_closed`).
    Over the `C_n` codewords of size `n`, `Σ h = C_{n+1} - C_n`, stated
    additively to stay inside ℕ. -/
theorem sum_finalH_add_catalan (n : ℕ) (hn : 1 ≤ n) :
    (∑ w ∈ suffixes (n - 1) 1, finalH 1 w) + catalan n = catalan (n + 1) := by
  have key := Hsum_add_card (n - 1) 1
  have hsucc : n - 1 + 1 = n := by omega
  rw [hsucc] at key
  rw [card_suffixes_eq_catalan n hn] at key
  have hn1 : (suffixes n 1).card = catalan (n + 1) := by
    have := card_suffixes_eq_catalan (n + 1) (by omega)
    simpa using this
  rw [hn1] at key
  exact key

/-! ### From heights to pop counts -/

/-! The conservation law `finalH h w + sum w = h + |w|` is already proved in
`MakinenAnalysis.LeafCount` as `finalH_add_sum`; we reuse it here. -/

/-- **Total of the pop counts** (Rocq: `pops_sum_closed`).
    `Σ S + C_{n+1} = (n+1) C_n`. -/
theorem sum_pops (n : ℕ) (hn : 1 ≤ n) :
    (∑ w ∈ suffixes (n - 1) 1, w.sum) + catalan (n + 1) = (n + 1) * catalan n := by
  have hpair : ∀ w ∈ suffixes (n - 1) 1, finalH 1 w + w.sum = n := by
    intro w hw
    obtain ⟨hlen, hval⟩ := (mem_suffixes (n - 1) 1 w).mp hw
    have := finalH_add_sum w 1 hval
    omega
  have hsplit :
      (∑ w ∈ suffixes (n - 1) 1, finalH 1 w) + (∑ w ∈ suffixes (n - 1) 1, w.sum)
        = n * catalan n := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hpair,
      Finset.sum_const, card_suffixes_eq_catalan n hn, smul_eq_mul, mul_comm]
  have hheights := sum_finalH_add_catalan n hn
  have hexp : (n + 1) * catalan n = n * catalan n + catalan n := by ring
  omega

/-- The Catalan one-step ratio in cleared form: `(n+2) C_{n+1} = 2(2n+1) C_n`.
    (Rocq: `catalan_ratio`.)  Derived from Mathlib's
    `succ_mul_catalan_eq_centralBinom` and `Nat.succ_mul_centralBinom_succ`. -/
lemma catalan_ratio (n : ℕ) :
    (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
  have h1 : (n + 1 + 1) * catalan (n + 1) = (n + 1).centralBinom :=
    succ_mul_catalan_eq_centralBinom (n + 1)
  have h2 : (n + 1) * catalan n = n.centralBinom :=
    succ_mul_catalan_eq_centralBinom n
  have h3 : (n + 1) * (n + 1).centralBinom = 2 * (2 * n + 1) * n.centralBinom :=
    Nat.succ_mul_centralBinom_succ n
  have hcancel : (n + 1) * ((n + 2) * catalan (n + 1))
      = (n + 1) * (2 * (2 * n + 1) * catalan n) := by
    calc (n + 1) * ((n + 2) * catalan (n + 1))
        = (n + 1) * ((n + 1 + 1) * catalan (n + 1)) := by ring_nf
      _ = (n + 1) * (n + 1).centralBinom := by rw [h1]
      _ = 2 * (2 * n + 1) * n.centralBinom := h3
      _ = 2 * (2 * n + 1) * ((n + 1) * catalan n) := by rw [h2]
      _ = (n + 1) * (2 * (2 * n + 1) * catalan n) := by ring
  exact Nat.eq_of_mul_eq_mul_left (by omega) hcancel

/-- **The cleared closed form of `E[S]`** (Rocq: `ES_rational`).
    `(n+2) · Σ S = n(n-1) · C_n`, i.e. `E[S] = n(n-1)/(n+2)`.
    Kept subtraction-free by casing on `n = k+1`. -/
theorem ES_rational (n : ℕ) (hn : 1 ≤ n) :
    (n + 2) * (∑ w ∈ suffixes (n - 1) 1, w.sum) = n * (n - 1) * catalan n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hSD := sum_pops (k + 1) (by omega)
  have hD := catalan_ratio (k + 1)
  simp only [Nat.add_sub_cancel] at hSD ⊢
  set S := ∑ w ∈ suffixes k 1, w.sum with hSdef
  set C := catalan (k + 1) with hCdef
  set D := catalan (k + 1 + 1) with hDdef
  have key : (k + 1 + 2) * S + (k + 1 + 2) * D
      = (k + 1) * k * C + (k + 1 + 2) * D := by
    calc (k + 1 + 2) * S + (k + 1 + 2) * D
        = (k + 1 + 2) * (S + D) := by ring
      _ = (k + 1 + 2) * ((k + 1 + 1) * C) := by rw [hSD]
      _ = (k + 1) * k * C + 2 * (2 * (k + 1) + 1) * C := by ring
      _ = (k + 1) * k * C + (k + 1 + 2) * D := by rw [hD]
  exact Nat.add_right_cancel key

/-! ### Towards `Σ P₂` (Rocq: `ReconstructMoments.v`)

`P2 w` counts the letters `≥ 2`, i.e. the strict descents of the height path.
The first-letter recursion below is the exact analogue of `Hsum_succ`, with one
extra term: a first letter `x ≥ 2` contributes `1` to every word it heads.

The closed form `Σ_{w ∈ suffixes (n-1) 1} P2 w = C(2n-2, n-3)` (Rocq:
`EP2_rational`) needs, on top of this recursion, the reflection formula for the
partial sums of the counts — the same machinery as `W_add_choose`.  That step is
**not done here**; the recursion is stated and proved so it can be built on.
Numerically the closed form checks out for `n ≤ 8`. -/

/-- Total of the double-pop counts over all valid words of length `ℓ` read from
    stack height `h`. -/
def Psum (ℓ h : ℕ) : ℕ := ∑ w ∈ suffixes ℓ h, P2 w

/-- First-letter recursion for `Psum`: the words are grouped by their first
    letter `x ≤ h`, and each `x ≥ 2` adds one double pop to every word it
    heads. -/
lemma Psum_succ (ℓ h : ℕ) :
    Psum (ℓ + 1) h
      = ∑ x ∈ range (h + 1),
          (Psum ℓ (h + 1 - x)
            + (if 2 ≤ x then (suffixes ℓ (h + 1 - x)).card else 0)) := by
  unfold Psum
  rw [sum_suffixes_succ]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hP : ∀ w : List ℕ, P2 (x :: w) = (if 2 ≤ x then 1 else 0) + P2 w := fun _ => rfl
  rw [Finset.sum_congr rfl fun w _ => hP w, Finset.sum_add_distrib,
    Finset.sum_const, smul_eq_mul]
  by_cases hx : 2 ≤ x
  · simp [hx, Nat.add_comm]
  · simp [hx]

/-! ### Exact mean comparison count of Mäkinen's algorithm -/

/-- **`E[A_M]` in cleared form** (Rocq: `EAM_rational`).
    `A_M = S + 2n - 1` on every codeword, so
    `(n+2) · Σ A_M = (n(n-1) + (2n-1)(n+2)) · C_n`. -/
theorem EAM_rational (n : ℕ) (hn : 1 ≤ n) :
    (n + 2) * (∑ w ∈ suffixes (n - 1) 1, (w.sum + (2 * n - 1)))
      = (n * (n - 1) + (2 * n - 1) * (n + 2)) * catalan n := by
  have hsplit : (∑ w ∈ suffixes (n - 1) 1, (w.sum + (2 * n - 1)))
      = (∑ w ∈ suffixes (n - 1) 1, w.sum) + (2 * n - 1) * catalan n := by
    rw [Finset.sum_add_distrib, Finset.sum_const,
      card_suffixes_eq_catalan n hn, smul_eq_mul, Nat.mul_comm]
  rw [hsplit, Nat.mul_add, ES_rational n hn, Nat.add_mul]
  ring


/-! ### `Σ P₂`: the closed form (Rocq: `EP2_rational`)

The refined counts `U (n-1) 1 k = #{w : P₂ w = k}` already have a closed form
(`PopDegreeBridge.U_mul_closed`), so `Σ_w P₂ w = Σ_k k·U` becomes a binomial
sum.  Pulling out `k·C(n,k) = n·C(n-1,k-1)` and reindexing turns it into the
trinomial identity `Σ_j C(m,j)·C(m-j,r-2j)·2^(r-2j) = C(2m,r)`, the coefficient
form of `(1+X)^{2m} = (X² + (1+2X))^m`, proved here from Mathlib's polynomial
coefficient lemmas. -/


lemma coeff_one_add_two_X_pow (k s : ℕ) :
    ((1 + C 2 * X : ℕ[X]) ^ k).coeff s = k.choose s * 2 ^ s := by
  have hC : ∀ j : ℕ, ((C 2 * X : ℕ[X]) ^ j).coeff s = if s = j then 2 ^ j else 0 := by
    intro j
    rw [mul_pow, ← C_pow, coeff_C_mul, coeff_X_pow]
    by_cases h : s = j <;> simp [h]
  rw [show (1 + C 2 * X : ℕ[X]) = C 2 * X + 1 by ring, add_pow, Polynomial.finsetSum_coeff]
  have hstep : ∀ j ∈ range (k + 1),
      ((C 2 * X : ℕ[X]) ^ j * 1 ^ (k - j) * (k.choose j : ℕ[X])).coeff s
        = if s = j then k.choose j * 2 ^ j else 0 := by
    intro j _
    rw [one_pow, mul_one, ← Nat.cast_id (k.choose j), ← C_eq_natCast, mul_comm _ (C _),
      coeff_C_mul, hC j]
    by_cases h : s = j <;> simp [h]
  rw [Finset.sum_congr rfl hstep]
  by_cases hs : s ≤ k
  · rw [Finset.sum_ite_eq (range (k + 1)) s (fun j => k.choose j * 2 ^ j)]
    simp [Finset.mem_range, hs]
  · have : k.choose s = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [this, zero_mul]
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hj
    rw [if_neg (by omega)]


/-- **Trinomial identity**: `Σ_j C(m,j)·C(m-j, r-2j)·2^(r-2j) = C(2m, r)`,
    the coefficient form of `(1+X)^{2m} = (X² + (1 + 2X))^m`. -/
lemma trinomial_choose (m r : ℕ) :
    (∑ j ∈ range (r / 2 + 1), m.choose j * ((m - j).choose (r - 2 * j) * 2 ^ (r - 2 * j)))
      = (2 * m).choose r := by
  have hLHS : ((1 + X : ℕ[X]) ^ (2 * m)).coeff r = (2 * m).choose r := by
    simpa using Polynomial.coeff_one_add_X_pow ℕ (2 * m) r
  have hC2 : (C 2 : ℕ[X]) = 2 := by simp
  have h2 : ((1 : ℕ[X]) + X) ^ 2 = X ^ 2 + (1 + C 2 * X) := by rw [hC2]; ring
  have hfac : ((1 + X : ℕ[X]) ^ (2 * m)) = (X ^ 2 + (1 + C 2 * X)) ^ m := by
    rw [pow_mul, h2]
  rw [← hLHS, hfac, add_pow, Polynomial.finsetSum_coeff]
  have hterm : ∀ j ∈ range (m + 1),
      (((X : ℕ[X]) ^ 2) ^ j * (1 + C 2 * X) ^ (m - j) * ((m.choose j : ℕ) : ℕ[X])).coeff r
        = if 2 * j ≤ r then m.choose j * ((m - j).choose (r - 2 * j) * 2 ^ (r - 2 * j))
          else 0 := by
    intro j _
    rw [← pow_mul, ← Nat.cast_id (m.choose j), ← C_eq_natCast, mul_comm _ (C _),
      coeff_C_mul, mul_comm ((X : ℕ[X]) ^ (2 * j)), coeff_mul_X_pow']
    by_cases h : 2 * j ≤ r
    · rw [if_pos h, if_pos h, coeff_one_add_two_X_pow]
      simp
    · rw [if_neg h, if_neg h, mul_zero]
  rw [Finset.sum_congr rfl hterm]
  have hiff : ∀ j : ℕ, (2 * j ≤ r) ↔ (j ∈ range (r / 2 + 1)) := by
    intro j; simp only [Finset.mem_range, Nat.lt_succ_iff]; omega
  have hrew : ∀ j ∈ range (m + 1),
      (if 2 * j ≤ r then m.choose j * ((m - j).choose (r - 2 * j) * 2 ^ (r - 2 * j)) else 0)
      = (if j ∈ range (r / 2 + 1) then
          m.choose j * ((m - j).choose (r - 2 * j) * 2 ^ (r - 2 * j)) else 0) :=
    fun j _ => if_congr (hiff j) rfl rfl
  rw [Finset.sum_congr rfl hrew, Finset.sum_ite_mem]
  refine (Finset.sum_subset Finset.inter_subset_right ?_).symm
  intro j hj hnot
  simp only [Finset.mem_inter, Finset.mem_range, Nat.lt_succ_iff] at hj hnot
  have hjm : m < j := by omega
  rw [Nat.choose_eq_zero_of_lt hjm, zero_mul]


/-- `P2 w` never exceeds the length of `w`. -/
lemma P2_le_length : ∀ w : List ℕ, P2 w ≤ w.length := by
  intro w
  induction w with
  | nil => simp [P2]
  | cons x v ih =>
    simp only [P2, List.length_cons]
    split <;> omega

/-- `Σ_w P2 w` refined by the value of `P2`. -/
lemma Psum_eq_sum_U (l h : ℕ) :
    (∑ w ∈ suffixes l h, P2 w) = ∑ k ∈ range (l + 1), k * U l h k := by
  classical
  have hmaps : ∀ w ∈ suffixes l h, P2 w ∈ range (l + 1) := by
    intro w hw
    obtain ⟨hlen, _⟩ := (mem_suffixes l h w).mp hw
    simp only [Finset.mem_range, Nat.lt_succ_iff]
    have := P2_le_length w
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun w => P2 w)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_congr rfl (fun w hw => (Finset.mem_filter.mp hw).2), Finset.sum_const,
    smul_eq_mul, card_filter_P2, mul_comm]


/-- Each double pop costs at least two pops, so `2·P₂(w) ≤ S(w)`. -/
lemma two_mul_P2_le_sum : ∀ w : List ℕ, 2 * P2 w ≤ w.sum := by
  intro w
  induction w with
  | nil => simp [P2]
  | cons x v ih =>
    simp only [P2, List.sum_cons]
    split <;> omega

/-- On the sample space the support of `P₂` sits in `[0, (n-1)/2]`. -/
lemma Psum_eq_sum_U_bounded (n : ℕ) (_hn : 1 ≤ n) :
    (∑ w ∈ suffixes (n - 1) 1, P2 w)
      = ∑ k ∈ range ((n - 1) / 2 + 1), k * U (n - 1) 1 k := by
  classical
  have hmaps : ∀ w ∈ suffixes (n - 1) 1, P2 w ∈ range ((n - 1) / 2 + 1) := by
    intro w hw
    obtain ⟨hlen, hval⟩ := (mem_suffixes (n - 1) 1 w).mp hw
    have hcons := finalH_add_sum w 1 hval
    have hpos : 1 ≤ finalH 1 w := by
      have gen : ∀ (v : List ℕ) (q : ℕ), Valid q v → 1 ≤ q → 1 ≤ finalH q v := by
        intro v
        induction v with
        | nil => intro q _ hq; simpa [finalH] using hq
        | cons y u ihv =>
          intro q hv hq
          obtain ⟨hy, hv'⟩ := hv
          exact ihv _ hv' (by omega)
      exact gen w 1 hval le_rfl
    have hb := two_mul_P2_le_sum w
    simp only [Finset.mem_range, Nat.lt_succ_iff]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun w => P2 w)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_congr rfl (fun w hw => (Finset.mem_filter.mp hw).2), Finset.sum_const,
    smul_eq_mul, card_filter_P2, mul_comm]


/-- **Total of the double-pop counts** (Rocq: `EP2_rational`).
    `Σ_{w} P₂(w) = C(2n-2, n-3)` over the `C_n` codewords of size `n`. -/
theorem sum_P2 (n : ℕ) (hn : 3 ≤ n) :
    (∑ w ∈ suffixes (n - 1) 1, P2 w) = (2 * n - 2).choose (n - 3) := by
  have hnpos : 0 < n := by omega
  -- multiply by n and use the closed form for the refined counts
  have hmul : n * (∑ w ∈ suffixes (n - 1) 1, P2 w)
      = ∑ k ∈ range ((n - 1) / 2 + 1),
          k * (n.choose k * ((n - k).choose (n - 1 - 2 * k) * 2 ^ (n - 1 - 2 * k))) := by
    rw [Psum_eq_sum_U_bounded n (by omega), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
    have hk' : 2 * k + 1 ≤ n := by omega
    have := U_mul_closed n k (by omega) hk'
    calc n * (k * U (n - 1) 1 k) = k * (n * U (n - 1) 1 k) := by ring
      _ = k * (n.choose k * (n - k).choose (n - 1 - 2 * k) * 2 ^ (n - 1 - 2 * k)) := by rw [this]
      _ = k * (n.choose k * ((n - k).choose (n - 1 - 2 * k) * 2 ^ (n - 1 - 2 * k))) := by ring
  -- pull out the factor n via k·C(n,k) = n·C(n-1,k-1) and reindex k = j+1
  have hshift : (∑ k ∈ range ((n - 1) / 2 + 1),
        k * (n.choose k * ((n - k).choose (n - 1 - 2 * k) * 2 ^ (n - 1 - 2 * k))))
      = n * ∑ j ∈ range ((n - 3) / 2 + 1),
          (n - 1).choose j * (((n - 1) - j).choose (n - 3 - 2 * j) * 2 ^ (n - 3 - 2 * j)) := by
    have hrange : (n - 1) / 2 = (n - 3) / 2 + 1 := by omega
    rw [hrange, Finset.sum_range_succ' _ ((n - 3) / 2 + 1), Finset.mul_sum]
    simp only [Nat.zero_mul, Nat.add_zero, Nat.choose_zero_right, Nat.mul_zero]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hj
    have hkc : (j + 1) * n.choose (j + 1) = n * (n - 1).choose j := by
      have h := Nat.add_one_mul_choose_eq (n - 1) j
      rw [show n - 1 + 1 = n by omega] at h
      rw [h]; ring
    have hi1 : n - (j + 1) = (n - 1) - j := by omega
    have hi2 : n - 1 - 2 * (j + 1) = n - 3 - 2 * j := by omega
    rw [hi1, hi2, ← Nat.mul_assoc, hkc, Nat.mul_assoc]
  have hfinal : n * (∑ w ∈ suffixes (n - 1) 1, P2 w) = n * ((2 * n - 2).choose (n - 3)) := by
    rw [hmul, hshift, trinomial_choose (n - 1) (n - 3),
      show 2 * (n - 1) = 2 * n - 2 by omega]
  exact Nat.eq_of_mul_eq_mul_left hnpos hfinal


/-! ### Second moments

Extending a word by **two** letters (rather than one) counts `(q+1)(q+4)/2`
continuations, where `q` is the final height.  Comparing that with the plain
counts gives `Σ h²` in closed form, and the pointwise `h + S = n` turns it into
`Σ S²`, which is what `Var[S]` needs. -/

/-- Total of the squared final stack heights. -/
def Hsq (l h : ℕ) : ℕ := ∑ w ∈ suffixes l h, (finalH h w) ^ 2

lemma Hsq_succ (l h : ℕ) :
    Hsq (l + 1) h = ∑ x ∈ range (h + 1), Hsq l (h + 1 - x) := by
  unfold Hsq
  rw [sum_suffixes_succ]
  rfl

/-- `#(suffixes 1 h) = h + 1`. -/
lemma card_suffixes_one (h : ℕ) : (suffixes 1 h).card = h + 1 := by
  rw [card_suffixes_succ]
  have : ∀ x ∈ range (h + 1), (suffixes 0 (h + 1 - x)).card = 1 :=
    fun x _ => Finset.card_singleton _
  rw [Finset.sum_congr rfl this]
  simp

/-- `2·#(suffixes 2 h) + 2 = (h+2)(h+3)`. -/
lemma card_suffixes_two (h : ℕ) :
    2 * (suffixes 2 h).card + 2 = (h + 2) * (h + 3) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, card_suffixes_succ]
  have hx : ∀ x ∈ range (h + 1), (suffixes 1 (h + 1 - x)).card = h + 2 - x := by
    intro x hx
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hx
    rw [card_suffixes_one]
    omega
  rw [Finset.sum_congr rfl hx]
  have hrefl : (∑ x ∈ range (h + 1), (h + 2 - x)) = ∑ x ∈ range (h + 1), (x + 2) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [Finset.mem_range] at hx
    omega
  have hg : (∑ i ∈ range (h + 1), i) * 2 = (h + 1) * h := by
    simpa using Finset.sum_range_id_mul_two (h + 1)
  rw [hrefl, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  calc 2 * ((∑ i ∈ range (h + 1), i) + (h + 1) * 2) + 2
      = (∑ i ∈ range (h + 1), i) * 2 + ((h + 1) * 4 + 2) := by ring
    _ = (h + 1) * h + ((h + 1) * 4 + 2) := by rw [hg]
    _ = (h + 2) * (h + 3) := by ring

/-- **Second moment of the final stack height.**  Extending a word of length `ℓ`
    by two letters has `(q+1)(q+4)/2` continuations, where `q` is its final
    height; comparing that with the counts gives, additively over ℕ,

    `Σ_w h(w)² + 5·#{|w|=ℓ+1} = 2·#{|w|=ℓ+2} + #{|w|=ℓ}`. -/
theorem Hsq_add_card : ∀ (l h : ℕ),
    Hsq l h + 5 * (suffixes (l + 1) h).card
      = 2 * (suffixes (l + 2) h).card + (suffixes l h).card := by
  intro l
  induction l with
  | zero =>
    intro h
    have hH : Hsq 0 h = h ^ 2 := by
      show (∑ w ∈ ({([] : List ℕ)} : Finset (List ℕ)), (finalH h w) ^ 2) = h ^ 2
      rw [Finset.sum_singleton]; rfl
    have hc : (suffixes 0 h).card = 1 := Finset.card_singleton _
    have h1 : (suffixes (0 + 1) h).card = h + 1 := card_suffixes_one h
    have h2 := card_suffixes_two h
    rw [show (0 : ℕ) + 2 = 2 from rfl] at *
    rw [hH, hc, h1]
    nlinarith [h2]
  | succ l ih =>
    intro h
    rw [Hsq_succ, card_suffixes_succ (l + 1) h, card_suffixes_succ (l + 2) h,
      card_suffixes_succ l h, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => ih (h + 1 - x)

/-- `Σ h²` in closed form: `Σ_w h(w)² + 5·C_{n+1} = 2·C_{n+2} + C_n`. -/
theorem sum_finalH_sq (n : ℕ) (hn : 1 ≤ n) :
    (∑ w ∈ suffixes (n - 1) 1, (finalH 1 w) ^ 2) + 5 * catalan (n + 1)
      = 2 * catalan (n + 2) + catalan n := by
  have key := Hsq_add_card (n - 1) 1
  rw [show n - 1 + 1 = n by omega, show n - 1 + 2 = n + 1 by omega] at key
  rw [card_suffixes_eq_catalan n hn] at key
  have e1 : (suffixes n 1).card = catalan (n + 1) := by
    simpa using card_suffixes_eq_catalan (n + 1) (by omega)
  have e2 : (suffixes (n + 1) 1).card = catalan (n + 2) := by
    simpa using card_suffixes_eq_catalan (n + 2) (by omega)
  rw [e1, e2] at key
  exact key

/-- **Second moment of the pop count** (feeds `Var[S]`):
    `Σ_w S(w)² + (2n+5)·C_{n+1} = (n+1)²·C_n + 2·C_{n+2}`. -/
theorem sum_pops_sq (n : ℕ) (hn : 1 ≤ n) :
    (∑ w ∈ suffixes (n - 1) 1, (w.sum) ^ 2) + (2 * n + 5) * catalan (n + 1)
      = (n + 1) ^ 2 * catalan n + 2 * catalan (n + 2) := by
  -- pointwise `s² + 2n·h = n² + h²` from `h + s = n`
  have hpt : ∀ w ∈ suffixes (n - 1) 1,
      (w.sum) ^ 2 + 2 * n * finalH 1 w = n ^ 2 + (finalH 1 w) ^ 2 := by
    intro w hw
    obtain ⟨hlen, hval⟩ := (mem_suffixes (n - 1) 1 w).mp hw
    have hc := finalH_add_sum w 1 hval
    have hn' : finalH 1 w + w.sum = n := by omega
    nlinarith [hn']
  have hsum : (∑ w ∈ suffixes (n - 1) 1, (w.sum) ^ 2)
      + 2 * n * (∑ w ∈ suffixes (n - 1) 1, finalH 1 w)
      = n ^ 2 * catalan n + (∑ w ∈ suffixes (n - 1) 1, (finalH 1 w) ^ 2) := by
    have := Finset.sum_congr rfl hpt
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
      card_suffixes_eq_catalan n hn, smul_eq_mul, ← Finset.mul_sum] at this
    linarith [this]
  have h1 := sum_finalH_add_catalan n hn
  have h2 := sum_finalH_sq n hn
  nlinarith [hsum, h1, h2]

/-! ## Corollary 7: the exact mean of `A_N` (Rocq: `EAN_rational`)

`E[A_M]` needed only `Σ S`.  `E[A_N]` needs `Σ P₂` in the paper's *rational*
shape `E[P₂] = (n-1)(n-2)/(2(2n-1))` rather than in the binomial shape
`Σ P₂ = C(2n-2, n-3)` that `sum_P2` delivers.  The bridge is two rungs of the
`choose` ladder (`Nat.choose_succ_right_eq`) plus the Catalan ratio. -/

/-- Two rungs of the `choose` ladder:
    `(m+1)(m+2)·C(2m, m-2) = m(m-1)·C(2m, m)`. -/
lemma choose_ladder_two (m : ℕ) (hm : 2 ≤ m) :
    (m + 1) * (m + 2) * (2 * m).choose (m - 2) = m * (m - 1) * (2 * m).choose m := by
  have h1 : (2 * m).choose (m - 1) * (m - 1) = (2 * m).choose (m - 2) * (m + 2) := by
    have h := Nat.choose_succ_right_eq (2 * m) (m - 2)
    rwa [show m - 2 + 1 = m - 1 by omega, show 2 * m - (m - 2) = m + 2 by omega] at h
  have h2 : (2 * m).choose m * m = (2 * m).choose (m - 1) * (m + 1) := by
    have h := Nat.choose_succ_right_eq (2 * m) (m - 1)
    rwa [show m - 1 + 1 = m by omega, show 2 * m - (m - 1) = m + 1 by omega] at h
  calc (m + 1) * (m + 2) * (2 * m).choose (m - 2)
      = (m + 1) * ((2 * m).choose (m - 2) * (m + 2)) := by ring
    _ = (m + 1) * ((2 * m).choose (m - 1) * (m - 1)) := by rw [h1]
    _ = (m - 1) * ((2 * m).choose m * m) := by rw [h2]; ring
    _ = m * (m - 1) * (2 * m).choose m := by ring

/-- Three rungs of the same ladder:
    `(m+1)(m+2)(m+3)·C(2m, m-3) = m(m-1)(m-2)·C(2m, m)`. -/
lemma choose_ladder_three (m : ℕ) (hm : 3 ≤ m) :
    (m + 1) * (m + 2) * (m + 3) * (2 * m).choose (m - 3)
      = m * (m - 1) * (m - 2) * (2 * m).choose m := by
  have h0 : (2 * m).choose (m - 2) * (m - 2) = (2 * m).choose (m - 3) * (m + 3) := by
    have h := Nat.choose_succ_right_eq (2 * m) (m - 3)
    rwa [show m - 3 + 1 = m - 2 by omega, show 2 * m - (m - 3) = m + 3 by omega] at h
  have h1 : (2 * m).choose (m - 1) * (m - 1) = (2 * m).choose (m - 2) * (m + 2) := by
    have h := Nat.choose_succ_right_eq (2 * m) (m - 2)
    rwa [show m - 2 + 1 = m - 1 by omega, show 2 * m - (m - 2) = m + 2 by omega] at h
  have h2 : (2 * m).choose m * m = (2 * m).choose (m - 1) * (m + 1) := by
    have h := Nat.choose_succ_right_eq (2 * m) (m - 1)
    rwa [show m - 1 + 1 = m by omega, show 2 * m - (m - 1) = m + 1 by omega] at h
  calc (m + 1) * (m + 2) * (m + 3) * (2 * m).choose (m - 3)
      = (m + 1) * (m + 2) * ((2 * m).choose (m - 3) * (m + 3)) := by ring
    _ = (m + 1) * (m + 2) * ((2 * m).choose (m - 2) * (m - 2)) := by rw [h0]
    _ = (m - 2) * ((m + 1) * ((2 * m).choose (m - 2) * (m + 2))) := by ring
    _ = (m - 2) * ((m + 1) * ((2 * m).choose (m - 1) * (m - 1))) := by rw [h1]
    _ = (m - 2) * ((m - 1) * ((2 * m).choose m * m)) := by rw [h2]; ring
    _ = m * (m - 1) * (m - 2) * (2 * m).choose m := by ring

/-- `C(2m, m) = (m+1)·C_m` (Mathlib's `centralBinom`, spelled with `choose`). -/
lemma choose_two_mul_self (m : ℕ) : (2 * m).choose m = (m + 1) * catalan m := by
  rw [succ_mul_catalan_eq_centralBinom m]
  rfl

/-- **`Σ P₂` in the paper's rational form** (Rocq: `EP2_rational`):
    `2(2n-1)·Σ P₂ = (n-1)(n-2)·C_n`, i.e. `E[P₂] = (n-1)(n-2)/(2(2n-1))`. -/
theorem EP2_rational (n : ℕ) (hn : 1 ≤ n) :
    2 * (2 * n - 1) * (∑ w ∈ suffixes (n - 1) 1, P2 w)
      = (n - 1) * (n - 2) * catalan n := by
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn
  · rw [catalan_one]; decide
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · -- `n = 2`: both sides vanish (`Σ P₂ = 0` over the two codewords of size 2).
    -- `catalan` is well-founded recursion, so rewrite the literal first.
    interval_cases n
    rw [catalan_two]; decide
  have hs := sum_P2 n h3
  have hlad := choose_ladder_two (n - 1) (by omega)
  rw [show n - 1 + 1 = n by omega, show n - 1 + 2 = n + 1 by omega,
    show 2 * (n - 1) = 2 * n - 2 by omega, show n - 1 - 2 = n - 3 by omega,
    show n - 1 - 1 = n - 2 by omega] at hlad
  have hcb : n * catalan (n - 1) = (2 * n - 2).choose (n - 1) := by
    have h := choose_two_mul_self (n - 1)
    rw [show 2 * (n - 1) = 2 * n - 2 by omega, show n - 1 + 1 = n by omega] at h
    exact h.symm
  have hratio : (n + 1) * catalan n = 2 * (2 * n - 1) * catalan (n - 1) := by
    have h := catalan_ratio (n - 1)
    rwa [show n - 1 + 2 = n + 1 by omega, show n - 1 + 1 = n by omega,
      show 2 * (n - 1) + 1 = 2 * n - 1 by omega] at h
  refine Nat.eq_of_mul_eq_mul_left (show 0 < n * (n + 1) by
    exact Nat.mul_pos (by omega) (by omega)) ?_
  calc n * (n + 1) * (2 * (2 * n - 1) * (∑ w ∈ suffixes (n - 1) 1, P2 w))
      = 2 * (2 * n - 1) * (n * (n + 1) * (∑ w ∈ suffixes (n - 1) 1, P2 w)) := by ring
    _ = 2 * (2 * n - 1) * (n * (n + 1) * ((2 * n - 2).choose (n - 3))) := by rw [hs]
    _ = 2 * (2 * n - 1) * ((n - 1) * (n - 2) * ((2 * n - 2).choose (n - 1))) := by rw [hlad]
    _ = 2 * (2 * n - 1) * ((n - 1) * (n - 2) * (n * catalan (n - 1))) := by rw [hcb]
    _ = (n - 1) * (n - 2) * (n * (2 * (2 * n - 1) * catalan (n - 1))) := by ring
    _ = (n - 1) * (n - 2) * (n * ((n + 1) * catalan n)) := by rw [hratio]
    _ = n * (n + 1) * ((n - 1) * (n - 2) * catalan n) := by ring

/-- **`E[A_N]` in cleared form** (Rocq: `EAN_rational`).
    By the central identity `A_N = S + P₂ + (n+2)` (Corollary 4),
    `2(n+2)(2n-1)·Σ A_N = (2(2n-1)n(n-1) + 2(n+2)²(2n-1) + (n+2)(n-1)(n-2))·C_n`,
    i.e. `E[A_N] = n(n-1)/(n+2) + (n+2) + (n-1)(n-2)/(2(2n-1))`. -/
theorem EAN_rational (n : ℕ) (hn : 1 ≤ n) :
    2 * (n + 2) * (2 * n - 1)
        * (∑ w ∈ suffixes (n - 1) 1, (w.sum + P2 w + (n + 2)))
      = (2 * (2 * n - 1) * n * (n - 1) + 2 * (n + 2) * (n + 2) * (2 * n - 1)
          + (n + 2) * (n - 1) * (n - 2)) * catalan n := by
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn
  · rw [catalan_one]; decide
  have hsplit : (∑ w ∈ suffixes (n - 1) 1, (w.sum + P2 w + (n + 2)))
      = (∑ w ∈ suffixes (n - 1) 1, w.sum) + (∑ w ∈ suffixes (n - 1) 1, P2 w)
        + (n + 2) * catalan n := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
      card_suffixes_eq_catalan n (by omega), smul_eq_mul, Nat.mul_comm]
  have hES := ES_rational n (by omega)
  have hEP := EP2_rational n (by omega)
  rw [hsplit]
  calc 2 * (n + 2) * (2 * n - 1)
        * ((∑ w ∈ suffixes (n - 1) 1, w.sum) + (∑ w ∈ suffixes (n - 1) 1, P2 w)
            + (n + 2) * catalan n)
      = 2 * (2 * n - 1) * ((n + 2) * (∑ w ∈ suffixes (n - 1) 1, w.sum))
        + (n + 2) * (2 * (2 * n - 1) * (∑ w ∈ suffixes (n - 1) 1, P2 w))
        + 2 * (n + 2) * (2 * n - 1) * ((n + 2) * catalan n) := by ring
    _ = 2 * (2 * n - 1) * (n * (n - 1) * catalan n)
        + (n + 2) * ((n - 1) * (n - 2) * catalan n)
        + 2 * (n + 2) * (2 * n - 1) * ((n + 2) * catalan n) := by rw [hES, hEP]
    _ = _ := by ring

/-! ## Proposition 8: `Var[P₂]` and `Cov[S,P₂]` (Rocq: `VarP2_rational`,
`CovSP2_rational`)

The Rocq route decomposes a tree at the root and solves Catalan convolutions
(`ReconstructES3.v`).  On the codeword side both second moments come out of the
same two machines already used above:

* `Σ P₂²` from the refined counts `U` (`PopDegreeBridge.U_mul_closed`) and the
  trinomial identity, exactly as `Σ P₂` did — only with `k²= k(k-1)+k`, so the
  falling part reindexes by **two** instead of one;
* `Σ h·P₂` (the joint statistic the covariance needs) from a
  **one-letter-extension identity**: a word of final height `q` has `q+1`
  right extensions, of which `q-1` are double pops, so the `P₂`-total over
  words one letter longer already contains `Σ h·P₂`.  No joint generating
  function and no kernel method is needed. -/

/-- On valid words the height never drops below its starting value. -/
lemma one_le_finalH : ∀ (w : List ℕ) (h : ℕ), Valid h w → 1 ≤ h → 1 ≤ finalH h w := by
  intro w
  induction w with
  | nil => intro h _ hh; simpa [finalH] using hh
  | cons y u ih =>
    intro h hv hh
    obtain ⟨hy, hv'⟩ := hv
    exact ih _ hv' (by omega)

/-- `P₂` takes its values in `[0, (n-1)/2]` on the sample space. -/
lemma P2_mem_support (n : ℕ) (_hn : 1 ≤ n) :
    ∀ w ∈ suffixes (n - 1) 1, P2 w ∈ range ((n - 1) / 2 + 1) := by
  intro w hw
  obtain ⟨hlen, hval⟩ := (mem_suffixes (n - 1) 1 w).mp hw
  have hcons := finalH_add_sum w 1 hval
  have hpos : 1 ≤ finalH 1 w := one_le_finalH w 1 hval le_rfl
  have hb := two_mul_P2_le_sum w
  simp only [Finset.mem_range, Nat.lt_succ_iff]
  omega

/-- `Σ P₂²` refined by the value of `P₂` (companion of `Psum_eq_sum_U_bounded`). -/
lemma Psq_eq_sum_U_bounded (n : ℕ) (hn : 1 ≤ n) :
    (∑ w ∈ suffixes (n - 1) 1, P2 w * P2 w)
      = ∑ k ∈ range ((n - 1) / 2 + 1), (k * k) * U (n - 1) 1 k := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (P2_mem_support n hn) (fun w => P2 w * P2 w)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_congr rfl (fun w hw => by rw [(Finset.mem_filter.mp hw).2] :
      ∀ w ∈ (suffixes (n - 1) 1).filter (fun w => P2 w = k), P2 w * P2 w = k * k),
    Finset.sum_const, smul_eq_mul, card_filter_P2, mul_comm]

/-- Two rungs of the `choose` recurrence downwards:
    `(j+2)(j+1)·C(n, j+2) = n(n-1)·C(n-2, j)`. -/
lemma choose_down_two (n j : ℕ) (hn : 2 ≤ n) :
    (j + 2) * (j + 1) * n.choose (j + 2) = n * (n - 1) * ((n - 2).choose j) := by
  have hj : j + 1 + 1 = j + 2 := by omega
  have h1 : n * (n - 1).choose (j + 1) = n.choose (j + 2) * (j + 2) := by
    have h := Nat.add_one_mul_choose_eq (n - 1) (j + 1)
    rw [show n - 1 + 1 = n by omega, hj] at h
    exact h
  have h2 : (n - 1) * (n - 2).choose j = (n - 1).choose (j + 1) * (j + 1) := by
    have h := Nat.add_one_mul_choose_eq (n - 2) j
    rw [show n - 2 + 1 = n - 1 by omega] at h
    exact h
  calc (j + 2) * (j + 1) * n.choose (j + 2)
      = (j + 1) * (n.choose (j + 2) * (j + 2)) := by ring
    _ = (j + 1) * (n * (n - 1).choose (j + 1)) := by rw [h1]
    _ = n * ((n - 1).choose (j + 1) * (j + 1)) := by ring
    _ = n * ((n - 1) * (n - 2).choose j) := by rw [h2]
    _ = n * (n - 1) * (n - 2).choose j := by ring

/-- **Second moment of `P₂`** (`n ≥ 5`; the small cases are not of this shape
    because of truncated subtraction):
    `Σ P₂² = (n-1)·C(2n-4, n-5) + C(2n-2, n-3)`. -/
theorem sum_P2_sq (n : ℕ) (hn : 5 ≤ n) :
    (∑ w ∈ suffixes (n - 1) 1, P2 w * P2 w)
      = (n - 1) * ((2 * n - 4).choose (n - 5)) + (2 * n - 2).choose (n - 3) := by
  have hnpos : 0 < n := by omega
  have hkk : ∀ k : ℕ, k * k = k * (k - 1) + k := by
    intro k
    cases k with
    | zero => rfl
    | succ m =>
      show (m + 1) * (m + 1) = (m + 1) * ((m + 1) - 1) + (m + 1)
      rw [Nat.add_sub_cancel]; ring
  -- move to the refined counts and to their closed form
  have hmul : n * (∑ w ∈ suffixes (n - 1) 1, P2 w * P2 w)
      = ∑ k ∈ range ((n - 1) / 2 + 1),
          (k * k) * (n.choose k * ((n - k).choose (n - 1 - 2 * k) * 2 ^ (n - 1 - 2 * k))) := by
    rw [Psq_eq_sum_U_bounded n (by omega), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
    rw [show n * ((k * k) * U (n - 1) 1 k) = (k * k) * (n * U (n - 1) 1 k) by ring,
      U_mul_closed n k (by omega) (by omega)]
    ring
  -- split `k² = k(k-1) + k`
  have hsplit : (∑ k ∈ range ((n - 1) / 2 + 1),
        (k * k) * (n.choose k * ((n - k).choose (n - 1 - 2 * k) * 2 ^ (n - 1 - 2 * k))))
      = (∑ k ∈ range ((n - 1) / 2 + 1),
          (k * (k - 1)) * (n.choose k * ((n - k).choose (n - 1 - 2 * k) * 2 ^ (n - 1 - 2 * k))))
        + (∑ k ∈ range ((n - 1) / 2 + 1),
          k * (n.choose k * ((n - k).choose (n - 1 - 2 * k) * 2 ^ (n - 1 - 2 * k)))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hkk k]; ring
  -- the linear part is `n · Σ P₂`
  have hlin : (∑ k ∈ range ((n - 1) / 2 + 1),
        k * (n.choose k * ((n - k).choose (n - 1 - 2 * k) * 2 ^ (n - 1 - 2 * k))))
      = n * ((2 * n - 2).choose (n - 3)) := by
    have hstep : (∑ k ∈ range ((n - 1) / 2 + 1),
        k * (n.choose k * ((n - k).choose (n - 1 - 2 * k) * 2 ^ (n - 1 - 2 * k))))
        = n * (∑ w ∈ suffixes (n - 1) 1, P2 w) := by
      rw [Psum_eq_sum_U_bounded n (by omega), Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
      rw [show n * (k * U (n - 1) 1 k) = k * (n * U (n - 1) 1 k) by ring,
        U_mul_closed n k (by omega) (by omega)]
      ring
    rw [hstep, sum_P2 n (by omega)]
  -- the falling part reindexes by two into the trinomial identity
  have hfall : (∑ k ∈ range ((n - 1) / 2 + 1),
        (k * (k - 1)) * (n.choose k * ((n - k).choose (n - 1 - 2 * k) * 2 ^ (n - 1 - 2 * k))))
      = n * (n - 1) * ((2 * n - 4).choose (n - 5)) := by
    obtain ⟨K, hK⟩ : ∃ K, (n - 1) / 2 = K + 2 := ⟨(n - 1) / 2 - 2, by omega⟩
    have hKval : K = (n - 5) / 2 := by omega
    rw [hK, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [Nat.zero_mul, Nat.mul_zero, Nat.zero_add, Nat.add_zero,
      Nat.zero_sub, Nat.sub_self]
    rw [hKval]
    have hterm : ∀ i ∈ range ((n - 5) / 2 + 1),
        ((i + 1 + 1) * ((i + 1 + 1) - 1))
            * (n.choose (i + 1 + 1)
                * ((n - (i + 1 + 1)).choose (n - 1 - 2 * (i + 1 + 1))
                    * 2 ^ (n - 1 - 2 * (i + 1 + 1))))
          = n * (n - 1)
              * ((n - 2).choose i
                  * (((n - 2) - i).choose ((n - 5) - 2 * i) * 2 ^ ((n - 5) - 2 * i))) := by
      intro i _
      rw [show i + 1 + 1 = i + 2 by omega, show n - (i + 2) = (n - 2) - i by omega,
        show n - 1 - 2 * (i + 2) = (n - 5) - 2 * i by omega,
        show i + 2 - 1 = i + 1 by omega]
      calc (i + 2) * (i + 1)
              * (n.choose (i + 2)
                  * (((n - 2) - i).choose ((n - 5) - 2 * i) * 2 ^ ((n - 5) - 2 * i)))
          = ((i + 2) * (i + 1) * n.choose (i + 2))
              * (((n - 2) - i).choose ((n - 5) - 2 * i) * 2 ^ ((n - 5) - 2 * i)) := by ring
        _ = (n * (n - 1) * ((n - 2).choose i))
              * (((n - 2) - i).choose ((n - 5) - 2 * i) * 2 ^ ((n - 5) - 2 * i)) := by
              rw [choose_down_two n i (by omega)]
        _ = n * (n - 1)
              * ((n - 2).choose i
                  * (((n - 2) - i).choose ((n - 5) - 2 * i) * 2 ^ ((n - 5) - 2 * i))) := by ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, trinomial_choose (n - 2) (n - 5),
      show 2 * (n - 2) = 2 * n - 4 by omega]
  have hfinal : n * (∑ w ∈ suffixes (n - 1) 1, P2 w * P2 w)
      = n * ((n - 1) * ((2 * n - 4).choose (n - 5)) + (2 * n - 2).choose (n - 3)) := by
    rw [hmul, hsplit, hfall, hlin]; ring
  exact Nat.eq_of_mul_eq_mul_left hnpos hfinal

/-! ### The joint statistic `Σ h·P₂`

The covariance is the one place where the marginals do not suffice.  The paper
gets the joint law by the kernel method; Rocq gets it by mixing the `rlen` and
`leaves` cell decompositions (`SLR_closed`).  On the codeword side it is a
one-line bookkeeping fact about *appending* a letter: a word with final height
`q` has `q+1` right extensions, of which `q-1` are double pops.  So the
`P₂`-total over words one letter longer already contains `Σ h·P₂`. -/

/-- Total of `h·P₂` over all valid words of length `ℓ` read from stack height `h`. -/
def HPsum (l h : ℕ) : ℕ := ∑ w ∈ suffixes l h, finalH h w * P2 w

/-- First-letter recursion for `HPsum` (the analogue of `Psum_succ`). -/
lemma HPsum_succ (l h : ℕ) :
    HPsum (l + 1) h
      = ∑ x ∈ range (h + 1),
          (HPsum l (h + 1 - x) + (if 2 ≤ x then Hsum l (h + 1 - x) else 0)) := by
  show (∑ w ∈ suffixes (l + 1) h, finalH h w * P2 w) = _
  rw [sum_suffixes_succ]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hterm : ∀ w : List ℕ,
      finalH h (x :: w) * P2 (x :: w)
        = finalH (h + 1 - x) w * P2 w
          + (if 2 ≤ x then finalH (h + 1 - x) w else 0) := by
    intro w
    show finalH (h + 1 - x) w * ((if 2 ≤ x then 1 else 0) + P2 w) = _
    by_cases hx : 2 ≤ x
    · simp only [if_pos hx]; ring
    · simp only [if_neg hx]; ring
  rw [Finset.sum_congr rfl fun w _ => hterm w, Finset.sum_add_distrib]
  by_cases hx : 2 ≤ x
  · simp only [if_pos hx, HPsum, Hsum]
  · simp only [if_neg hx, Finset.sum_const_zero, Nat.add_zero, HPsum]

/-- `#{x ≤ h : x ≥ 2} + 1 = h` for `h ≥ 1`. -/
lemma sum_two_le_indicator : ∀ h : ℕ, 1 ≤ h →
    (∑ x ∈ range (h + 1), (if 2 ≤ x then 1 else 0)) + 1 = h := by
  intro h
  induction h with
  | zero => intro hh; exact absurd hh (by omega)
  | succ k ih =>
    intro _
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; decide
    · rw [Finset.sum_range_succ, if_pos (by omega)]
      have := ih hk
      omega

/-- **One-letter extension identity.**  Appending a letter to a word of final
    height `q` has `q+1` choices, `q-1` of which are double pops, so

    `Σ_{|w|=ℓ+1} P₂ + #{|w|=ℓ} = Σ_{|w|=ℓ} h·P₂ + Σ_{|w|=ℓ} P₂ + Σ_{|w|=ℓ} h`.

    Proved by the same first-letter induction as everything else in this file;
    the inductive step closes on `Hsum_add_card`. -/
theorem Psum_succ_add_card : ∀ (l h : ℕ), 1 ≤ h →
    Psum (l + 1) h + (suffixes l h).card = HPsum l h + Psum l h + Hsum l h := by
  intro l
  induction l with
  | zero =>
    intro h hh
    have hP1 : Psum 1 h = ∑ x ∈ range (h + 1), (if 2 ≤ x then 1 else 0) := by
      rw [Psum_succ]
      refine Finset.sum_congr rfl fun x _ => ?_
      have h0 : Psum 0 (h + 1 - x) = 0 := by
        show (∑ w ∈ ({([] : List ℕ)} : Finset (List ℕ)), P2 w) = 0
        rw [Finset.sum_singleton]; rfl
      have hc1 : (suffixes 0 (h + 1 - x)).card = 1 := Finset.card_singleton _
      rw [h0, hc1]
      by_cases hx : 2 ≤ x <;> simp [hx]
    have hH0 : Hsum 0 h = h := by
      show (∑ w ∈ ({([] : List ℕ)} : Finset (List ℕ)), finalH h w) = h
      rw [Finset.sum_singleton]; rfl
    have hP0 : Psum 0 h = 0 := by
      show (∑ w ∈ ({([] : List ℕ)} : Finset (List ℕ)), P2 w) = 0
      rw [Finset.sum_singleton]; rfl
    have hHP0 : HPsum 0 h = 0 := by
      show (∑ w ∈ ({([] : List ℕ)} : Finset (List ℕ)), finalH h w * P2 w) = 0
      rw [Finset.sum_singleton]; rfl
    have hc0 : (suffixes 0 h).card = 1 := Finset.card_singleton _
    have hind := sum_two_le_indicator h hh
    rw [hP1, hH0, hP0, hHP0, hc0]
    omega
  | succ l ih =>
    intro h hh
    rw [Psum_succ (l + 1) h, card_suffixes_succ l h, HPsum_succ l h, Psum_succ l h,
      Hsum_succ l h, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hx
    have hIH := ih (h + 1 - x) (by omega)
    have hHc := Hsum_add_card l (h + 1 - x)
    by_cases h2 : 2 ≤ x
    · simp only [if_pos h2]; omega
    · simp only [if_neg h2]; omega

/-- **`Σ h·P₂` over the size-`n` population**, subtraction-free:
    `Σ h·P₂ + Σ P₂ + C_{n+1} = Σ_{size n+1} P₂ + 2·C_n`. -/
theorem sum_finalH_mul_P2 (n : ℕ) (hn : 1 ≤ n) :
    (∑ w ∈ suffixes (n - 1) 1, finalH 1 w * P2 w)
        + (∑ w ∈ suffixes (n - 1) 1, P2 w) + catalan (n + 1)
      = (∑ w ∈ suffixes n 1, P2 w) + 2 * catalan n := by
  have key := Psum_succ_add_card (n - 1) 1 le_rfl
  rw [show n - 1 + 1 = n by omega] at key
  simp only [Psum, Hsum, HPsum] at key
  rw [card_suffixes_eq_catalan n hn] at key
  have hH := sum_finalH_add_catalan n hn
  omega

/-- `Σ S·P₂ + Σ h·P₂ = n·Σ P₂`, from the pointwise `S + h = n`. -/
theorem sum_pops_mul_P2_add (n : ℕ) (hn : 1 ≤ n) :
    (∑ w ∈ suffixes (n - 1) 1, w.sum * P2 w)
        + (∑ w ∈ suffixes (n - 1) 1, finalH 1 w * P2 w)
      = n * (∑ w ∈ suffixes (n - 1) 1, P2 w) := by
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  obtain ⟨hlen, hval⟩ := (mem_suffixes (n - 1) 1 w).mp hw
  have hc := finalH_add_sum w 1 hval
  have hsum : finalH 1 w + w.sum = n := by omega
  calc w.sum * P2 w + finalH 1 w * P2 w = (finalH 1 w + w.sum) * P2 w := by ring
    _ = n * P2 w := by rw [hsum]

/-! ### The closed forms of `Σ S·P₂` and `Σ P₂²`

Both are pure ℕ-algebra from the totals above.  The polynomial identities mix
`n` with `n-1`, `n-2`, … , so each is isolated in a helper lemma where `n` is
first written `m + k` and truncated subtraction disappears. -/

private lemma covSP2_alg (n X Pn B C D : ℕ) (hn : 3 ≤ n)
    (hG : X + Pn + 2 * C = n * B + B + D)
    (hB : 2 * (2 * n - 1) * B = (n - 1) * (n - 2) * C)
    (hPnc : (n + 2) * Pn = n * (n - 1) * C)
    (hF : (n + 2) * D = 2 * (2 * n + 1) * C) :
    2 * (2 * n - 1) * (n + 2) * X
      = (n - 1) * (n - 2) * (n * (n - 1) + 4) * C := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [show m + 3 - 1 = m + 2 from by omega, show m + 3 - 2 = m + 1 from by omega,
    show 2 * (m + 3) - 1 = 2 * m + 5 from by omega,
    show m + 3 + 2 = m + 5 from by omega,
    show 2 * (m + 3) + 1 = 2 * m + 7 from by omega] at hB hPnc hF ⊢
  apply Nat.add_right_cancel
    (m := 2 * (2 * m + 5) * ((m + 3) * (m + 2) * C) + 4 * (2 * m + 5) * (m + 5) * C)
  calc 2 * (2 * m + 5) * (m + 5) * X
        + (2 * (2 * m + 5) * ((m + 3) * (m + 2) * C) + 4 * (2 * m + 5) * (m + 5) * C)
      = 2 * (2 * m + 5) * (m + 5) * X + 2 * (2 * m + 5) * ((m + 5) * Pn)
          + 4 * (2 * m + 5) * (m + 5) * C := by rw [hPnc]; ring
    _ = 2 * (2 * m + 5) * (m + 5) * (X + Pn + 2 * C) := by ring
    _ = 2 * (2 * m + 5) * (m + 5) * ((m + 3) * B + B + D) := by rw [hG]
    _ = (m + 5) * (m + 4) * (2 * (2 * m + 5) * B) + 2 * (2 * m + 5) * ((m + 5) * D) := by ring
    _ = (m + 5) * (m + 4) * ((m + 2) * (m + 1) * C)
          + 2 * (2 * m + 5) * (2 * (2 * m + 7) * C) := by rw [hB, hF]
    _ = (m + 2) * (m + 1) * ((m + 3) * (m + 2) + 4) * C
          + (2 * (2 * m + 5) * ((m + 3) * (m + 2) * C)
              + 4 * (2 * m + 5) * (m + 5) * C) := by ring

/-- **`Σ S·P₂` in cleared rational form**:
    `2(2n-1)(n+2)·Σ S·P₂ = (n-1)(n-2)(n(n-1)+4)·C_n`. -/
theorem sum_pops_mul_P2_rational (n : ℕ) (hn : 2 ≤ n) :
    2 * (2 * n - 1) * (n + 2) * (∑ w ∈ suffixes (n - 1) 1, w.sum * P2 w)
      = (n - 1) * (n - 2) * (n * (n - 1) + 4) * catalan n := by
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · -- `n = 2`: `Σ S·P₂ = 0` and the factor `n - 2` vanishes.
    interval_cases n
    rw [catalan_two]; decide
  have hF := catalan_ratio n
  have hPn2 : 2 * (2 * n + 1) * (∑ w ∈ suffixes n 1, P2 w)
      = n * (n - 1) * catalan (n + 1) := by
    have h := EP2_rational (n + 1) (by omega)
    rwa [show n + 1 - 1 = n by omega, show 2 * (n + 1) - 1 = 2 * n + 1 by omega,
      show n + 1 - 2 = n - 1 by omega] at h
  have hPnc : (n + 2) * (∑ w ∈ suffixes n 1, P2 w) = n * (n - 1) * catalan n := by
    refine Nat.eq_of_mul_eq_mul_left (show 0 < 2 * (2 * n + 1) by omega) ?_
    calc 2 * (2 * n + 1) * ((n + 2) * (∑ w ∈ suffixes n 1, P2 w))
        = (n + 2) * (2 * (2 * n + 1) * (∑ w ∈ suffixes n 1, P2 w)) := by ring
      _ = (n + 2) * (n * (n - 1) * catalan (n + 1)) := by rw [hPn2]
      _ = n * (n - 1) * ((n + 2) * catalan (n + 1)) := by ring
      _ = n * (n - 1) * (2 * (2 * n + 1) * catalan n) := by rw [hF]
      _ = 2 * (2 * n + 1) * (n * (n - 1) * catalan n) := by ring
  have hG : (∑ w ∈ suffixes (n - 1) 1, w.sum * P2 w) + (∑ w ∈ suffixes n 1, P2 w)
        + 2 * catalan n
      = n * (∑ w ∈ suffixes (n - 1) 1, P2 w) + (∑ w ∈ suffixes (n - 1) 1, P2 w)
        + catalan (n + 1) := by
    have hA := sum_pops_mul_P2_add n (by omega)
    have hB' := sum_finalH_mul_P2 n (by omega)
    omega
  exact covSP2_alg n _ _ _ _ _ h3 hG (EP2_rational n (by omega)) hPnc hF

private lemma covSP2_final_alg (n X S B C : ℕ)
    (hX : 2 * (2 * n - 1) * (n + 2) * X = (n - 1) * (n - 2) * (n * (n - 1) + 4) * C)
    (hS : (n + 2) * S = n * (n - 1) * C)
    (hB : 2 * (2 * n - 1) * B = (n - 1) * (n - 2) * C) :
    (n + 2) * (2 * n - 1) * (C * X)
      = 2 * (n - 1) * (n - 2) * (C * C) + (n + 2) * (2 * n - 1) * (S * B) := by
  refine Nat.eq_of_mul_eq_mul_left (show (0 : ℕ) < 2 by norm_num) ?_
  calc 2 * ((n + 2) * (2 * n - 1) * (C * X))
      = C * (2 * (2 * n - 1) * (n + 2) * X) := by ring
    _ = C * ((n - 1) * (n - 2) * (n * (n - 1) + 4) * C) := by rw [hX]
    _ = 4 * (n - 1) * (n - 2) * (C * C)
        + (n * (n - 1) * C) * ((n - 1) * (n - 2) * C) := by ring
    _ = 4 * (n - 1) * (n - 2) * (C * C) + ((n + 2) * S) * (2 * (2 * n - 1) * B) := by
        rw [hS, hB]
    _ = 2 * (2 * (n - 1) * (n - 2) * (C * C) + (n + 2) * (2 * n - 1) * (S * B)) := by ring

/-- **`Cov[S,P₂]` in cleared form** (Rocq: `CovSP2_rational`).
    `Cov[S,P₂] = 2(n-1)(n-2) / ((n+2)(2n-1))`. -/
theorem CovSP2_rational (n : ℕ) (hn : 1 ≤ n) :
    (n + 2) * (2 * n - 1)
        * (catalan n * (∑ w ∈ suffixes (n - 1) 1, w.sum * P2 w))
      = 2 * (n - 1) * (n - 2) * (catalan n * catalan n)
        + (n + 2) * (2 * n - 1)
          * ((∑ w ∈ suffixes (n - 1) 1, w.sum) * (∑ w ∈ suffixes (n - 1) 1, P2 w)) := by
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn
  · rw [catalan_one]; decide
  exact covSP2_final_alg n _ _ _ _ (sum_pops_mul_P2_rational n hn) (ES_rational n (by omega))
    (EP2_rational n (by omega))

private lemma varP2_moment_alg (n Y Z C C1 C2 : ℕ) (hn : 5 ≤ n)
    (hY : n * (n + 1) * Y = (n - 2) * (n - 3) * (n - 4) * C2)
    (hZ : 2 * (2 * n - 1) * Z = (n - 1) * (n - 2) * C)
    (r1 : (n + 1) * C = 2 * (2 * n - 1) * C1)
    (r2 : n * C1 = 2 * (2 * n - 3) * C2) :
    4 * (2 * n - 1) * (2 * n - 3) * ((n - 1) * Y + Z)
      = (n - 1) * (n - 2) * ((n - 1) * (n - 2) + 4) * C := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  simp only [show m + 5 - 1 = m + 4 from by omega, show m + 5 - 2 = m + 3 from by omega,
    show m + 5 - 3 = m + 2 from by omega, show m + 5 - 4 = m + 1 from by omega,
    show 2 * (m + 5) - 1 = 2 * m + 9 from by omega,
    show 2 * (m + 5) - 3 = 2 * m + 7 from by omega] at hY hZ r1 r2 ⊢
  refine Nat.eq_of_mul_eq_mul_left
    (show 0 < (m + 5) * (m + 5 + 1) by exact Nat.mul_pos (by omega) (by omega)) ?_
  calc (m + 5) * (m + 5 + 1) * (4 * (2 * m + 9) * (2 * m + 7) * ((m + 4) * Y + Z))
      = 4 * (2 * m + 9) * (2 * m + 7) * (m + 4) * ((m + 5) * (m + 5 + 1) * Y)
        + 2 * ((m + 5) * (m + 5 + 1) * (2 * m + 7))
            * (2 * (2 * m + 9) * Z) := by ring
    _ = 4 * (2 * m + 9) * (2 * m + 7) * (m + 4) * ((m + 3) * (m + 2) * (m + 1) * C2)
        + 2 * ((m + 5) * (m + 5 + 1) * (2 * m + 7))
            * ((m + 4) * (m + 3) * C) := by rw [hY, hZ]
    _ = (m + 4) * (m + 3) * (m + 2) * (m + 1) * (2 * (2 * m + 9) * (2 * (2 * m + 7) * C2))
        + 2 * ((m + 5) * (m + 5 + 1) * (2 * m + 7))
            * ((m + 4) * (m + 3) * C) := by ring
    _ = (m + 4) * (m + 3) * (m + 2) * (m + 1) * (2 * (2 * m + 9) * ((m + 5) * C1))
        + 2 * ((m + 5) * (m + 5 + 1) * (2 * m + 7))
            * ((m + 4) * (m + 3) * C) := by rw [← r2]
    _ = (m + 4) * (m + 3) * (m + 2) * (m + 1) * ((m + 5) * (2 * (2 * m + 9) * C1))
        + 2 * ((m + 5) * (m + 5 + 1) * (2 * m + 7))
            * ((m + 4) * (m + 3) * C) := by ring
    _ = (m + 4) * (m + 3) * (m + 2) * (m + 1) * ((m + 5) * ((m + 5 + 1) * C))
        + 2 * ((m + 5) * (m + 5 + 1) * (2 * m + 7))
            * ((m + 4) * (m + 3) * C) := by rw [← r1]
    _ = (m + 5) * (m + 5 + 1) * ((m + 4) * (m + 3) * ((m + 4) * (m + 3) + 4) * C) := by ring

private lemma varP2_alg (n Q B C : ℕ) (hn : 5 ≤ n)
    (hQ : 4 * (2 * n - 1) * (2 * n - 3) * Q
            = (n - 1) * (n - 2) * ((n - 1) * (n - 2) + 4) * C)
    (hB : 2 * (2 * n - 1) * B = (n - 1) * (n - 2) * C) :
    2 * (2 * n - 1) * (2 * n - 1) * (2 * n - 3) * (C * Q)
      = n * (n + 1) * (n - 1) * (n - 2) * (C * C)
        + 2 * (2 * n - 1) * (2 * n - 1) * (2 * n - 3) * (B * B) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  simp only [show m + 5 - 1 = m + 4 from by omega, show m + 5 - 2 = m + 3 from by omega,
    show 2 * (m + 5) - 1 = 2 * m + 9 from by omega,
    show 2 * (m + 5) - 3 = 2 * m + 7 from by omega] at hQ hB ⊢
  have e2 : 4 * ((2 * m + 9) * (2 * m + 9)) * (2 * m + 7) * (B * B)
      = (2 * m + 7) * ((m + 4) * (m + 3) * ((m + 4) * (m + 3))) * (C * C) := by
    calc 4 * ((2 * m + 9) * (2 * m + 9)) * (2 * m + 7) * (B * B)
        = (2 * m + 7) * ((2 * (2 * m + 9) * B) * (2 * (2 * m + 9) * B)) := by ring
      _ = (2 * m + 7) * (((m + 4) * (m + 3) * C) * ((m + 4) * (m + 3) * C)) := by rw [hB]
      _ = (2 * m + 7) * ((m + 4) * (m + 3) * ((m + 4) * (m + 3))) * (C * C) := by ring
  refine Nat.eq_of_mul_eq_mul_left (show (0 : ℕ) < 2 by norm_num) ?_
  calc 2 * (2 * (2 * m + 9) * (2 * m + 9) * (2 * m + 7) * (C * Q))
      = ((2 * m + 9) * C) * (4 * (2 * m + 9) * (2 * m + 7) * Q) := by ring
    _ = ((2 * m + 9) * C) * ((m + 4) * (m + 3) * ((m + 4) * (m + 3) + 4) * C) := by rw [hQ]
    _ = 2 * ((m + 5) * (m + 5 + 1) * (m + 4) * (m + 3) * (C * C))
        + (2 * m + 7) * ((m + 4) * (m + 3) * ((m + 4) * (m + 3))) * (C * C) := by ring
    _ = 2 * ((m + 5) * (m + 5 + 1) * (m + 4) * (m + 3) * (C * C))
        + 4 * ((2 * m + 9) * (2 * m + 9)) * (2 * m + 7) * (B * B) := by rw [← e2]
    _ = 2 * ((m + 5) * (m + 5 + 1) * (m + 4) * (m + 3) * (C * C)
        + 2 * (2 * m + 9) * (2 * m + 9) * (2 * m + 7) * (B * B)) := by ring

/-- **`Var[P₂]` in cleared form** (Rocq: `VarP2_rational`).
    `Var[P₂] = n(n+1)(n-1)(n-2) / (2(2n-1)²(2n-3))`. -/
theorem VarP2_rational (n : ℕ) (hn : 1 ≤ n) :
    2 * (2 * n - 1) * (2 * n - 1) * (2 * n - 3)
        * (catalan n * (∑ w ∈ suffixes (n - 1) 1, P2 w * P2 w))
      = n * (n + 1) * (n - 1) * (n - 2) * (catalan n * catalan n)
        + 2 * (2 * n - 1) * (2 * n - 1) * (2 * n - 3)
          * ((∑ w ∈ suffixes (n - 1) 1, P2 w) * (∑ w ∈ suffixes (n - 1) 1, P2 w)) := by
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn
  · rw [catalan_one]; decide
  rcases Nat.lt_or_ge n 5 with h5 | h5
  · -- `catalan` is defined by well-founded recursion and does not reduce in the
    -- kernel, so the three small cases get their Catalan numbers by rewriting
    -- first and only then evaluate the (tiny) codeword sums.
    have c4 : catalan 4 = 14 := by
      have h := catalan_ratio 3
      norm_num [catalan_three] at h
      omega
    interval_cases n
    · rw [catalan_two]; decide
    · rw [catalan_three]; decide
    · rw [c4]; decide
  · have hY : n * (n + 1) * ((2 * n - 4).choose (n - 5))
        = (n - 2) * (n - 3) * (n - 4) * catalan (n - 2) := by
      have hlad := choose_ladder_three (n - 2) (by omega)
      rw [show n - 2 + 1 = n - 1 by omega, show n - 2 + 2 = n by omega,
        show n - 2 + 3 = n + 1 by omega, show 2 * (n - 2) = 2 * n - 4 by omega,
        show n - 2 - 3 = n - 5 by omega, show n - 2 - 1 = n - 3 by omega,
        show n - 2 - 2 = n - 4 by omega] at hlad
      have hc := choose_two_mul_self (n - 2)
      rw [show 2 * (n - 2) = 2 * n - 4 by omega, show n - 2 + 1 = n - 1 by omega] at hc
      rw [hc] at hlad
      refine Nat.eq_of_mul_eq_mul_left (show 0 < n - 1 by omega) ?_
      calc (n - 1) * (n * (n + 1) * ((2 * n - 4).choose (n - 5)))
          = (n - 1) * n * (n + 1) * ((2 * n - 4).choose (n - 5)) := by ring
        _ = (n - 2) * (n - 3) * (n - 4) * ((n - 1) * catalan (n - 2)) := hlad
        _ = (n - 1) * ((n - 2) * (n - 3) * (n - 4) * catalan (n - 2)) := by ring
    have r1 : (n + 1) * catalan n = 2 * (2 * n - 1) * catalan (n - 1) := by
      have h := catalan_ratio (n - 1)
      rwa [show n - 1 + 2 = n + 1 by omega, show n - 1 + 1 = n by omega,
        show 2 * (n - 1) + 1 = 2 * n - 1 by omega] at h
    have r2 : n * catalan (n - 1) = 2 * (2 * n - 3) * catalan (n - 2) := by
      have h := catalan_ratio (n - 2)
      rwa [show n - 2 + 2 = n by omega, show n - 2 + 1 = n - 1 by omega,
        show 2 * (n - 2) + 1 = 2 * n - 3 by omega] at h
    have hQ : 4 * (2 * n - 1) * (2 * n - 3)
          * (∑ w ∈ suffixes (n - 1) 1, P2 w * P2 w)
        = (n - 1) * (n - 2) * ((n - 1) * (n - 2) + 4) * catalan n := by
      rw [sum_P2_sq n h5]
      exact varP2_moment_alg n _ _ _ _ _ h5 hY
        (by rw [← sum_P2 n (by omega)]; exact EP2_rational n (by omega)) r1 r2
    exact varP2_alg n _ _ _ h5 hQ (EP2_rational n (by omega))

end MakinenAnalysis
