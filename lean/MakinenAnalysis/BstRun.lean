import MakinenAnalysis.BstLimits
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Fin.Tuple.Sort

/-!
# `H` is the first ascending run of an i.i.d. uniform sequence

WiNF2026 A2 (§3) describes the limit law `H` of the final stack height (`Hpmf`,
`P(H = m) = m/(m+1)!`, `BstLimits`) as the length of the first ascending run of an
infinite sequence of independent uniform random numbers.  Here `U_0, U_1, …` are the
coordinates of `ℕ → ℝ` under the infinite product `Measure.infinitePi` of the uniform
law on `[0, 1]`.

| here | A2 |
|---|---|
| `run_ge` | `P(U_0 < U_1 < ⋯ < U_{m-1}) = 1/m!`, i.e. `P(H ≥ m) = 1/m!` |
| `run_eq` | `P(the first ascending run has length exactly m) = m/(m+1)! = P(H = m)` |

The proof is the symmetry argument: under the product of `m` copies of an atomless
law the `m!` events "`x ∘ σ` is strictly increasing" (`σ` a permutation) are pairwise
disjoint, have the same probability (the product is invariant under permuting the
coordinates), and cover every tuple with distinct entries (`Tuple.sort`); ties have
probability zero.  The infinite product restricted to the first `m` coordinates is that
finite product (`infinitePi_pi`).
-/

namespace MakinenAnalysis

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BstRun

/-- The uniform law on `[0, 1]`. -/
def unif : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure unif := by
  constructor; simp [unif]

instance : NoAtoms unif := by unfold unif; infer_instance

/-- The law of `m` independent uniforms. -/
def P (m : ℕ) : Measure (Fin m → ℝ) := Measure.pi fun _ => unif

instance (m : ℕ) : IsProbabilityMeasure (P m) := by unfold P; infer_instance

/-! ## 1. Finitely many coordinates -/

/-- Permuting the coordinates preserves the product law. -/
lemma perm_preserving (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    MeasurePreserving (fun x : Fin m → ℝ => x ∘ σ) (P m) (P m) := by
  have h := measurePreserving_piCongrLeft (α := fun _ : Fin m => ℝ) (fun _ => unif) σ.symm
  unfold P
  convert h using 1
  funext x; funext i
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]

/-- Ties have probability zero. -/
lemma tie_null (m : ℕ) {i j : Fin m} (hij : i ≠ j) : P m {x | x i = x j} = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by have := i.2; omega⟩
  obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hij)
  have hmp := measurePreserving_piFinSuccAbove (α := fun _ : Fin (k + 1) => ℝ) (fun _ => unif) i
  set S : Set (ℝ × (Fin k → ℝ)) := {p | p.1 = p.2 j'}
  have hS : MeasurableSet S :=
    measurableSet_eq_fun measurable_fst ((measurable_pi_apply j').comp measurable_snd)
  have hpre : {x : Fin (k + 1) → ℝ | x i = x (i.succAbove j')}
      = MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i ⁻¹' S := by
    ext x; simp [S, MeasurableEquiv.piFinSuccAbove_apply, Fin.removeNth_apply]
  rw [P, hpre, hmp.measure_preimage hS.nullMeasurableSet, Measure.prod_apply_symm hS]
  have : ∀ y : Fin k → ℝ, unif ((fun a => (a, y)) ⁻¹' S) = 0 := by
    intro y
    have : (fun a => (a, y)) ⁻¹' S = {y j'} := by ext a; simp [S]
    rw [this, measure_singleton]
  simp [this]

/-- `x ∘ σ` strictly increasing. -/
def sortedBy (m : ℕ) (σ : Equiv.Perm (Fin m)) : Set (Fin m → ℝ) := {x | StrictMono (x ∘ σ)}

lemma measurableSet_sortedBy (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    MeasurableSet (sortedBy m σ) := by
  have : sortedBy m σ = ⋂ a : Fin m, ⋂ b : Fin m, {x | a < b → x (σ a) < x (σ b)} := by
    ext x; simp [sortedBy, StrictMono]
  rw [this]
  refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => ?_
  by_cases hab : a < b
  · simp only [hab, true_implies]
    exact measurableSet_lt (measurable_pi_apply _) (measurable_pi_apply _)
  · simp [hab]

lemma sortedBy_eq_preimage (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    sortedBy m σ = (fun x : Fin m → ℝ => x ∘ σ) ⁻¹' sortedBy m 1 := by
  ext x; simp [sortedBy]

lemma disjoint_sortedBy (m : ℕ) {σ τ : Equiv.Perm (Fin m)} (h : σ ≠ τ) :
    Disjoint (sortedBy m σ) (sortedBy m τ) := by
  rw [Set.disjoint_left]
  intro x hσ hτ
  apply h
  have heq := Tuple.unique_monotone hσ.monotone hτ.monotone
  have hinj : Function.Injective x := by
    have := hσ.injective
    intro a b hab
    have := this (a₁ := σ.symm a) (a₂ := σ.symm b) (by simp [hab])
    simpa using this
  ext i
  have := congrFun heq i
  exact congrArg Fin.val (hinj this)

lemma injective_subset (m : ℕ) :
    {x : Fin m → ℝ | Function.Injective x} ⊆ ⋃ σ : Equiv.Perm (Fin m), sortedBy m σ := by
  intro x hx
  refine Set.mem_iUnion.mpr ⟨Tuple.sort x, ?_⟩
  exact (Tuple.monotone_sort x).strictMono_of_injective (hx.comp (Tuple.sort x).injective)

lemma noninjective_null (m : ℕ) : P m {x : Fin m → ℝ | Function.Injective x}ᶜ = 0 := by
  have : {x : Fin m → ℝ | Function.Injective x}ᶜ
      ⊆ ⋃ i : Fin m, ⋃ j : Fin m, ⋃ (_ : i ≠ j), {x | x i = x j} := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Function.Injective, not_forall] at hx
    obtain ⟨a, b, hab, hne⟩ := hx
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hne, hab⟩⟩⟩
  refine measure_mono_null this ?_
  refine measure_iUnion_null fun i => measure_iUnion_null fun j => measure_iUnion_null fun hij => ?_
  exact tie_null m hij

/-- **`P(x_0 < ⋯ < x_{m-1}) = 1/m!`** for `m` i.i.d. uniforms. -/
theorem prob_sorted (m : ℕ) : P m (sortedBy m 1) = (m.factorial : ℝ≥0∞)⁻¹ := by
  have hsame : ∀ σ, P m (sortedBy m σ) = P m (sortedBy m 1) := fun σ => by
    rw [sortedBy_eq_preimage, (perm_preserving m σ).measure_preimage
      (measurableSet_sortedBy m 1).nullMeasurableSet]
  have hunion : P m (⋃ σ : Equiv.Perm (Fin m), sortedBy m σ) = 1 := by
    refine le_antisymm prob_le_one ?_
    have h1 : P m {x : Fin m → ℝ | Function.Injective x} = 1 := by
      rw [← prob_compl_eq_zero_iff]
      · exact noninjective_null m
      · have : {x : Fin m → ℝ | Function.Injective x}ᶜ
            = ⋃ i : Fin m, ⋃ j : Fin m, ⋃ (_ : i ≠ j), {x | x i = x j} := by
          ext x
          simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Function.Injective, not_forall,
            Set.mem_iUnion]
          constructor
          · rintro ⟨a, b, hab, hne⟩; exact ⟨a, b, hne, hab⟩
          · rintro ⟨a, b, hne, hab⟩; exact ⟨a, b, hab, hne⟩
        rw [← MeasurableSet.compl_iff, this]
        exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j =>
          MeasurableSet.iUnion fun _ => measurableSet_eq_fun (measurable_pi_apply i)
            (measurable_pi_apply j)
    rw [← h1]
    exact measure_mono (injective_subset m)
  rw [measure_iUnion (fun σ τ h => disjoint_sortedBy m h) (measurableSet_sortedBy m),
    tsum_fintype] at hunion
  simp_rw [hsame] at hunion
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul, mul_comm] at hunion
  exact ENNReal.eq_inv_of_mul_eq_one_left hunion

/-! ## 2. The infinite sequence -/

/-- The law of `U_0, U_1, …` i.i.d. uniform on `[0, 1]`. -/
def μ : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => unif

instance : IsProbabilityMeasure μ := by unfold μ; infer_instance

/-- The first `m` coordinates. -/
def firstM (m : ℕ) (ω : ℕ → ℝ) : Fin m → ℝ := fun i => ω i

lemma measurable_firstM (m : ℕ) : Measurable (firstM m) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- The first `m` coordinates of the infinite product are `m` independent uniforms. -/
lemma map_firstM (m : ℕ) : μ.map (firstM m) = P m := by
  classical
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (measurable_firstM m) (MeasurableSet.univ_pi hs)]
  set t : ℕ → Set ℝ := fun i => if h : i < m then s ⟨i, h⟩ else univ
  have hpre : firstM m ⁻¹' Set.univ.pi s = Set.pi (Finset.range m : Set ℕ) t := by
    ext ω
    simp only [Set.mem_preimage, firstM, Set.mem_pi, Finset.coe_range,
      Set.mem_Iio, t, Set.mem_univ, true_implies]
    constructor
    · intro h i hi; rw [dif_pos hi]; exact h ⟨i, hi⟩
    · intro h i; have := h i i.2; rwa [dif_pos i.2] at this
  rw [hpre, μ, Measure.infinitePi_pi]
  · rw [← Fin.prod_univ_eq_prod_range (fun i => unif (t i)) m]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [t]
  · intro i _
    simp only [t]
    split_ifs with h
    · exact hs _
    · exact MeasurableSet.univ

lemma chain_lt (f : ℕ → ℝ) (m : ℕ) (h : ∀ i, i + 1 < m → f i < f (i + 1)) :
    ∀ a b : ℕ, a < b → b < m → f a < f b := by
  intro a b hab hbm
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hab with h' | rfl
    · exact (ih h' (by omega)).trans (h b hbm)
    · exact h a hbm

/-- `U_0 < U_1 < ⋯ < U_{m-1}`. -/
def ascending (m : ℕ) : Set (ℕ → ℝ) := {ω | ∀ i, i + 1 < m → ω i < ω (i + 1)}

lemma ascending_eq (m : ℕ) : ascending m = firstM m ⁻¹' sortedBy m 1 := by
  ext ω
  simp only [ascending, sortedBy, Set.mem_preimage, Set.mem_setOf_eq, Equiv.Perm.coe_one,
    Function.comp_id]
  constructor
  · intro h a b hab
    exact chain_lt ω m h a b hab b.2
  · intro h i hi
    exact h (show (⟨i, by omega⟩ : Fin m) < ⟨i + 1, hi⟩ from Fin.mk_lt_mk.mpr (by omega))

lemma measurableSet_ascending (m : ℕ) : MeasurableSet (ascending m) := by
  rw [ascending_eq]; exact measurable_firstM m (measurableSet_sortedBy m 1)

lemma mu_ascending (m : ℕ) : μ (ascending m) = (m.factorial : ℝ≥0∞)⁻¹ := by
  rw [ascending_eq, ← Measure.map_apply (measurable_firstM m) (measurableSet_sortedBy m 1),
    map_firstM, prob_sorted]

lemma inv_fact_eq_ofReal (m : ℕ) :
    (m.factorial : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / (m.factorial : ℝ)) := by
  rw [one_div, ENNReal.ofReal_inv_of_pos (by exact_mod_cast Nat.factorial_pos m),
    ENNReal.ofReal_natCast]

end BstRun

open BstRun in
/-- **`P(H ≥ m) = 1/m!`**: for `U_0, U_1, …` i.i.d. uniform on `[0, 1]`, the probability
    that the sequence starts with an ascending run of length at least `m` is `1/m!`. -/
theorem run_ge (m : ℕ) :
    BstRun.μ {ω | ∀ i, i + 1 < m → ω i < ω (i + 1)} = (m.factorial : ℝ≥0∞)⁻¹ :=
  mu_ascending m

open BstRun in
/-- **`P(H = m) = m/(m+1)!`**: the first ascending run of an i.i.d. uniform sequence has
    length exactly `m` (`U_0 < ⋯ < U_{m-1}` and `U_{m-1} ≥ U_m`) with probability
    `Hpmf m`, the limit law of the final stack height (`bst_h_tendsto`). -/
theorem run_eq (m : ℕ) (hm : 1 ≤ m) :
    BstRun.μ {ω | (∀ i, i + 1 < m → ω i < ω (i + 1)) ∧ ¬ ω (m - 1) < ω m}
      = ENNReal.ofReal (Hpmf m) := by
  have hset : {ω : ℕ → ℝ | (∀ i, i + 1 < m → ω i < ω (i + 1)) ∧ ¬ ω (m - 1) < ω m}
      = ascending m \ ascending (m + 1) := by
    ext ω
    simp only [ascending, Set.mem_setOf_eq, Set.mem_sdiff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun h => h2 ?_⟩
      have := h (m - 1) (by omega)
      rwa [show m - 1 + 1 = m by omega] at this
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun h => h2 fun i hi => ?_⟩
      rcases (show i + 1 < m ∨ i = m - 1 by omega) with hi' | rfl
      · exact h1 i hi'
      · rwa [show m - 1 + 1 = m by omega]
  have hsub : ascending (m + 1) ⊆ ascending m := fun ω h i hi => h i (by omega)
  rw [hset, measure_sdiff hsub (measurableSet_ascending (m + 1)).nullMeasurableSet
      (measure_ne_top _ _), mu_ascending, mu_ascending, inv_fact_eq_ofReal, inv_fact_eq_ofReal,
    ← ENNReal.ofReal_sub _ (by positivity), Hpmf_eq]

end

end MakinenAnalysis
