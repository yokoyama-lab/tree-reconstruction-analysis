import MakinenAnalysis.PopDegreeBridge

/-!
# A kernel-reducible enumeration of the binary trees

`BinaryTree.treesOfNumNodesEq` is defined by well-founded recursion, so the
kernel cannot unfold it and `decide` cannot see it.  Every bounded exhaustive
check in this development therefore used to be run by `#eval` — outside the
kernel, and outside CI, which means a later change to a definition could make
the recorded results stale without anything going red.

`treesOfSize` is the same finite set built bottom-up by structural recursion on
the size, so it *does* reduce in the kernel.  `mem_treesOfSize` proves the
enumeration is complete, and `forall_numNodes_eq` turns "checked on
`treesOfSize n`" into "holds for every tree with `n` internal nodes" — so a
`decide` over it is a genuine exhaustive theorem, re-checked on every build.

Rocq does the same thing with `Reconstruct.trees_table` / `trees_upto` and
closes its bounded checks by `vm_compute`; the difference is that `vm_compute`
is a trusted-kernel bytecode evaluator whereas `decide` here goes through
ordinary kernel reduction.
-/

namespace MakinenAnalysis

/-- Row `k` of the table is every tree with `k` internal nodes.  Built bottom-up
    so that the recursion is structural in `n` and therefore **reduces in the
    kernel** — unlike `BinaryTree.treesOfNumNodesEq`, which is defined by
    well-founded recursion and cannot be used by `decide`. -/
def treesTable : ℕ → List (List T)
  | 0 => [[.nil]]
  | n + 1 =>
      let tbl := treesTable n
      tbl ++ [(List.range (n + 1)).flatMap (fun i =>
        (tbl.getD i []).flatMap (fun l =>
          (tbl.getD (n - i) []).map (fun r => .node () l r)))]

/-- Every tree with `n` internal nodes, as a kernel-reducible list. -/
def treesOfSize (n : ℕ) : List T := (treesTable n).getD n []

lemma length_treesTable : ∀ n : ℕ, (treesTable n).length = n + 1
  | 0 => rfl
  | n + 1 => by simp [treesTable, length_treesTable n]

/-- The table is stable: earlier rows never change as it grows. -/
lemma getD_treesTable : ∀ {i n : ℕ}, i ≤ n → (treesTable n).getD i [] = treesOfSize i := by
  intro i n
  induction n with
  | zero => intro h; interval_cases i; rfl
  | succ n ih =>
    intro h
    rcases Nat.lt_or_ge i (n + 1) with hlt | hge
    · rw [treesOfSize] at *
      rw [show treesTable (n + 1)
            = treesTable n ++ [(List.range (n + 1)).flatMap (fun i =>
                ((treesTable n).getD i []).flatMap (fun l =>
                  ((treesTable n).getD (n - i) []).map (fun r => .node () l r)))] from rfl,
        List.getD_append _ _ _ _ (by rw [length_treesTable]; omega)]
      exact ih (by omega)
    · have : i = n + 1 := by omega
      subst this
      rfl

/-- **The enumeration is complete.** -/
lemma mem_treesOfSize : ∀ t : T, t ∈ treesOfSize t.numNodes := by
  intro t
  induction t with
  | nil => simp [treesOfSize, treesTable]
  | node v L R ihL ihR =>
    cases v
    have hnum : (BinaryTree.node () L R).numNodes = L.numNodes + R.numNodes + 1 := rfl
    rw [hnum, treesOfSize,
      show treesTable (L.numNodes + R.numNodes + 1)
          = treesTable (L.numNodes + R.numNodes)
            ++ [(List.range (L.numNodes + R.numNodes + 1)).flatMap (fun i =>
                ((treesTable (L.numNodes + R.numNodes)).getD i []).flatMap (fun l =>
                  ((treesTable (L.numNodes + R.numNodes)).getD
                      (L.numNodes + R.numNodes - i) []).map (fun r => .node () l r)))] from rfl]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [length_treesTable]),
      show L.numNodes + R.numNodes + 1 - (treesTable (L.numNodes + R.numNodes)).length = 0 by
        rw [length_treesTable]; omega]
    simp only [List.getElem?_cons_zero, Option.getD_some]
    refine List.mem_flatMap.mpr ⟨L.numNodes, ?_, ?_⟩
    · exact List.mem_range.mpr (by omega)
    · refine List.mem_flatMap.mpr ⟨L, ?_, ?_⟩
      · rw [getD_treesTable (by omega)]; exact ihL
      · refine List.mem_map.mpr ⟨R, ?_, rfl⟩
        rw [getD_treesTable (by omega),
          show L.numNodes + R.numNodes - L.numNodes = R.numNodes from by omega]
        exact ihR

/-- Bounded exhaustive checking: a property checked on `treesOfSize n` holds for
    every tree with `n` internal nodes. -/
theorem forall_numNodes_eq {n : ℕ} {P : T → Prop} (h : ∀ t ∈ treesOfSize n, P t) :
    ∀ t : T, t.numNodes = n → P t := by
  intro t ht
  exact h t (ht ▸ mem_treesOfSize t)

end MakinenAnalysis
