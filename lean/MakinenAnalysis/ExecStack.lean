import MakinenAnalysis.ExecModel

/-!
# The stack invariant: a run's pop count is a structural statistic

This is the heart of the operational half of the development
(`../../coq/ReconstructPops.v`, `../../coq/ReconstructLcount.v`).  Although the
number of stack pops is *run*-dependent -- two trees of the same size can pop a
different number of times -- it satisfies the clean recurrence `Srec` of
`ExecModel`, and the number of index tests is the number of two-children nodes
plus one.

The crux is one generalized invariant, `runN_gen`: processing `ipo off t` from a
stack `low ++ high`, where every element of `low` is `< off` and every element
of `high` is `≥ off + numNodes t`,

* consumes all of `low` at the root,
* leaves a residue `rho` of length `rlen t`, with labels in `t`'s range, on top
  of `high`,
* raises the pop counter by `Srec t + |low|`, and
* raises the index-test counter by `twoNodes t + [2 ≤ |low|]`.

The induction descends left with `low = []` and right with
`low = rho_left ++ [root]`; the right descent is the only one whose `low` can
reach length `2`, and it does so exactly when both subtrees are non-empty,
which is why the index tests count the two-children nodes.

Two deviations from the Rocq development, both recorded here because they are
places where this port does *less* work rather than proving something weaker:

* Rocq proves the pop part (`ppof_gen`) and the index-test part (`lcof_gen`) by
  two separate inductions of the same shape, and then repeats the pop part a
  third time for algorithm `M` (`ppof_genM`).  Here the first two are a single
  induction, and the `M` side comes from a simulation lemma (`runMN_agree`: the
  two machines build the same array, keep the same stack and pop the same number
  of times; `N` merely keeps two extra counters).  Rocq states that conclusion
  too (`pops_M_eq_N`), as a corollary of its two invariants rather than as the
  input to one of them.
* Rocq's inner multi-pop loop carries a fuel argument; `ExecModel.popStack` is
  the same loop with the stack as the decreasing measure, and
  `popLoop_eq_popStack` says the fuel the callers pass never truncates.

| here | Rocq |
|---|---|
| `popStack_consumes` | `ReconstructLcount.popN_consumes` |
| `stepM_root` | `ReconstructPops.stepM_root_pp` |
| `stepN_root` | `ReconstructLcount.stepN_root` + `ReconstructPops.stepN_root_pp` |
| `runN_gen` | `ReconstructPops.ppof_gen` + `ReconstructLcount.lcof_gen` |
| `runN_indep` | `ReconstructBounds.ppof_aec_indep` + `ReconstructLcount.lcof_aec_indep` |
| `runMN_agree` | `ReconstructPops.popof_ac_indep` + `ppof_genM` (replaced) |
| `popsN_eq_Srec` | `ReconstructPops.pops_N_Srec` |
| `popsM_eq_Srec` | `ReconstructPops.pops_M_Srec` |
| `popsM_eq_popsN` | `ReconstructPops.pops_M_eq_N` |
| `lcountN_eq` | `ReconstructLcount.lcount_N_full` |
-/
namespace MakinenAnalysis

@[simp] lemma runM_nil (st : StM) : runM [] st = st := rfl
lemma runM_cons (cur : ℕ) (rest : List ℕ) (st : StM) :
    runM (cur :: rest) st = runM rest (stepM cur st) := rfl
@[simp] lemma runN_nil (st : StN) : runN [] st = st := rfl
lemma runN_cons (cur : ℕ) (rest : List ℕ) (st : StN) :
    runN (cur :: rest) st = runN rest (stepN cur st) := rfl

lemma popStack_consumes : ∀ (low high : List ℕ) (root : ℕ), low ≠ [] →
    (∀ x ∈ low, x ≤ root) → (∀ y ∈ high, root < y) →
    ∃ prev, popStack root (low ++ high) = (prev, high, low.length) := by
  intro low
  induction low with
  | nil => intro high root h; exact absurd rfl h
  | cons x low' ih =>
    intro high root _ hlo hhi
    match low' with
    | [] =>
      match high with
      | [] => exact ⟨x, by simp⟩
      | h :: hs =>
        have hxh : ¬ (h ≤ root) := by have := hhi h (by simp); omega
        exact ⟨x, by simp [popStack_cons2, hxh]⟩
    | y :: rest =>
      have hy : y ≤ root := hlo y (by simp)
      obtain ⟨prev, hp⟩ := ih high root (by simp)
        (fun z hz => hlo z (List.mem_cons_of_mem _ hz)) hhi
      refine ⟨prev, ?_⟩
      rw [List.cons_append] at hp
      show popStack root (x :: y :: (rest ++ high)) = _
      rw [popStack_cons2, if_pos hy, hp]
      simp

lemma stepM_root (root : ℕ) (low high : List ℕ) (st : StM)
    (hst : st.stk = low ++ high) (hhne : high ≠ [])
    (hlo : ∀ x ∈ low, x < root) (hhi : ∀ y ∈ high, root < y) :
    (stepM root st).stk = root :: high ∧
    (stepM root st).pop = st.pop + low.length := by
  obtain ⟨h, hs, rfl⟩ : ∃ h hs, high = h :: hs := by
    cases high with
    | nil => exact absurd rfl hhne
    | cons h hs => exact ⟨h, hs, rfl⟩
  have hrh : root < h := hhi h (by simp)
  obtain ⟨a, s, c, p⟩ := st
  subst hst
  cases low with
  | nil => simp [stepM, hrh]
  | cons x1 low' =>
    have hx1 : ¬ root < x1 := by have := hlo x1 (by simp); omega
    obtain ⟨prev, hp⟩ := popStack_consumes (x1 :: low') (h :: hs) root (by simp)
      (fun z hz => le_of_lt (hlo z hz)) hhi
    rw [List.cons_append] at hp
    simp only [List.cons_append, stepM, hx1, if_false, popLoop_length, hp]
    simp

lemma stepN_root (root : ℕ) (low high : List ℕ) (st : StN)
    (hst : st.stk = low ++ high) (hhne : high ≠ [])
    (hlo : ∀ x ∈ low, x < root) (hhi : ∀ y ∈ high, root < y) :
    (stepN root st).stk = root :: high ∧
    (stepN root st).pcnt = st.pcnt + low.length ∧
    (stepN root st).lcnt = st.lcnt + (if 2 ≤ low.length then 1 else 0) := by
  obtain ⟨h, hs, rfl⟩ : ∃ h hs, high = h :: hs := by
    cases high with
    | nil => exact absurd rfl hhne
    | cons h hs => exact ⟨h, hs, rfl⟩
  have hrh : root < h := hhi h (by simp)
  obtain ⟨a, s, e, l, p⟩ := st
  subst hst
  match low with
  | [] => simp [stepN, hrh]
  | [x1] =>
    have hx1 : ¬ root < x1 := by have := hlo x1 (by simp); omega
    have hhr : ¬ (h ≤ root) := by omega
    simp [stepN, hx1, hhr]
  | x1 :: x2 :: low'' =>
    have hx1 : ¬ root < x1 := by have := hlo x1 (by simp); omega
    have hx2 : x2 ≤ root := le_of_lt (hlo x2 (by simp))
    obtain ⟨prev, hp⟩ := popStack_consumes (x2 :: low'') (h :: hs) root (by simp)
      (fun z hz => le_of_lt (hlo z (List.mem_cons_of_mem _ hz))) hhi
    rw [List.cons_append] at hp
    simp only [List.cons_append, stepN, hx1, if_false, hx2, if_true, popLoop_length, hp]
    have hif : (if 2 ≤ (x1 :: x2 :: low'').length then (1:ℕ) else 0) = 1 := by
      rw [if_pos]
      simp only [List.length_cons]
      omega
    rw [hif]
    simp only [true_and, List.length_cons]
    exact ⟨by omega, trivial⟩

lemma runN_gen : ∀ (t : T) (off : ℕ) (low high : List ℕ) (st : StN),
    t ≠ .nil → high ≠ [] → st.stk = low ++ high →
    (∀ x ∈ low, x < off) → (∀ y ∈ high, off + t.numNodes ≤ y) →
    ∃ rho : List ℕ,
      rho.length = rlen t ∧
      (∀ z ∈ rho, off ≤ z ∧ z < off + t.numNodes) ∧
      (runN (ipo off t) st).stk = rho ++ high ∧
      (runN (ipo off t) st).pcnt = st.pcnt + Srec t + low.length ∧
      (runN (ipo off t) st).lcnt
        = st.lcnt + twoNodes t + (if 2 ≤ low.length then 1 else 0) := by
  intro t
  induction t with
  | nil => intro _ _ _ _ h; exact absurd rfl h
  | node v L R ihL ihR =>
    intro off low high st _ hhne hst hlo hhi
    by_cases hL : L = .nil
    · -- ===== L empty: nothing happens on the left =====
      subst hL
      have hnil : (BinaryTree.nil : T).numNodes = 0 := rfl
      have hnum : (BinaryTree.node v (.nil : T) R).numNodes = R.numNodes + 1 := by
        simp [BinaryTree.numNodes]
      have hipo : ipo off (BinaryTree.node v (.nil : T) R) = off :: ipo (off + 1) R := by
        simp [ipo_node]
      rw [hnum] at hhi
      have hhi' : ∀ y ∈ high, off < y := fun y hy => by have := hhi y hy; omega
      obtain ⟨h1, h2, h3⟩ := stepN_root off low high st hst hhne hlo hhi'
      rw [hipo, runN_cons]
      generalize hgen : stepN off st = st1 at h1 h2 h3 ⊢
      by_cases hR : R = .nil
      · -- a single node
        subst hR
        rw [show ipo (off + 1) (.nil : T) = [] from rfl, runN_nil]
        refine ⟨[off], ?_, ?_, ?_, ?_, ?_⟩
        · rw [rlen_node_nil]; simp
        · intro z hz
          simp only [List.mem_singleton] at hz
          subst hz
          rw [hnum]; omega
        · simpa using h1
        · rw [h2, Srec_node_nil, Srec_nil]; simp
        · rw [h3]
          have htn : twoNodes (BinaryTree.node v (.nil : T) (.nil : T)) = 0 := by
            simp [twoNodes]
          rw [htn]; simp
      · -- right subtree only
        have hst1 : st1.stk = [off] ++ high := by simpa using h1
        have hlor : ∀ x ∈ [off], x < off + 1 := by
          intro x hx; simp only [List.mem_singleton] at hx; omega
        have hhir : ∀ y ∈ high, off + 1 + R.numNodes ≤ y := fun y hy => by
          have := hhi y hy; omega
        obtain ⟨rho, hlen, hmem, hstk, hpc, hlc⟩ :=
          ihR (off + 1) [off] high st1 hR hhne hst1 hlor hhir
        refine ⟨rho, ?_, ?_, hstk, ?_, ?_⟩
        · rw [hlen, rlen_node_node hR]
        · intro z hz; obtain ⟨hA, hB⟩ := hmem z hz; rw [hnum]; omega
        · rw [hpc, h2, Srec_node_node hR, hnil, List.length_singleton]; ring
        · have h0 : (if 2 ≤ ([off] : List ℕ).length then (1:ℕ) else 0) = 0 := by simp
          have htn : twoNodes (BinaryTree.node v (.nil : T) R) = twoNodes R := by
            simp [twoNodes]
          rw [hlc, h3, h0, htn]; ring
    · -- ===== L is a node: descend left with an empty low block =====
      have hnum : (BinaryTree.node v L R).numNodes = L.numNodes + R.numNodes + 1 := rfl
      have hipo : ipo off (BinaryTree.node v L R)
          = (off + L.numNodes) :: (ipo off L ++ ipo (off + L.numNodes + 1) R) := rfl
      rw [hnum] at hhi
      have hlo' : ∀ x ∈ low, x < off + L.numNodes := fun x hx => by
        have := hlo x hx; omega
      have hhi' : ∀ y ∈ high, off + L.numNodes < y := fun y hy => by
        have := hhi y hy; omega
      obtain ⟨h1, h2, h3⟩ := stepN_root (off + L.numNodes) low high st hst hhne hlo' hhi'
      rw [hipo, runN_cons, runN_append]
      generalize hgen : stepN (off + L.numNodes) st = st1 at h1 h2 h3 ⊢
      have hst1 : st1.stk = [] ++ ((off + L.numNodes) :: high) := by simpa using h1
      have hlol : ∀ x ∈ ([] : List ℕ), x < off := by intro x hx; simp at hx
      have hhil : ∀ y ∈ (off + L.numNodes) :: high, off + L.numNodes ≤ y := by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · omega
        · have := hhi y hy'; omega
      obtain ⟨rl0, hlen0, hmem0, hstk0, hpc0, hlc0⟩ :=
        ihL off [] ((off + L.numNodes) :: high) st1 hL (by simp) hst1 hlol hhil
      have hrl0 : 1 ≤ rl0.length := by rw [hlen0]; exact rlen_pos hL
      generalize hgen2 : runN (ipo off L) st1 = st2 at hstk0 hpc0 hlc0 ⊢
      by_cases hR : R = .nil
      · -- left subtree only: the root joins the residue
        subst hR
        have hnil : (BinaryTree.nil : T).numNodes = 0 := rfl
        rw [show ipo (off + L.numNodes + 1) (.nil : T) = [] from rfl, runN_nil]
        refine ⟨rl0 ++ [off + L.numNodes], ?_, ?_, ?_, ?_, ?_⟩
        · rw [rlen_node_nil]
          simp only [List.length_append, List.length_cons, List.length_nil, hlen0]
        · intro z hz
          rcases List.mem_append.mp hz with hz | hz
          · obtain ⟨hA, hB⟩ := hmem0 z hz; rw [hnum, hnil]; omega
          · simp only [List.mem_singleton] at hz; subst hz; rw [hnum, hnil]; omega
        · rw [hstk0]; simp
        · rw [hpc0, h2, Srec_node_nil, List.length_nil]; ring
        · have h0 : (if 2 ≤ ([] : List ℕ).length then (1:ℕ) else 0) = 0 := by simp
          have htn : twoNodes (BinaryTree.node v L (.nil : T)) = twoNodes L := by
            simp [twoNodes]
          rw [hlc0, h3, h0, htn]; ring
      · -- both subtrees: the root is a two-children node, one extra index test
        have hst2 : st2.stk = (rl0 ++ [off + L.numNodes]) ++ high := by
          rw [hstk0]; simp
        have hlor : ∀ x ∈ rl0 ++ [off + L.numNodes], x < off + L.numNodes + 1 := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · obtain ⟨_, hB⟩ := hmem0 x hx; omega
          · simp only [List.mem_singleton] at hx; omega
        have hhir : ∀ y ∈ high, off + L.numNodes + 1 + R.numNodes ≤ y := fun y hy => by
          have := hhi y hy; omega
        obtain ⟨rho, hlen, hmem, hstk, hpc, hlc⟩ :=
          ihR (off + L.numNodes + 1) (rl0 ++ [off + L.numNodes]) high st2 hR hhne
            hst2 hlor hhir
        have hind : (if 2 ≤ (rl0 ++ [off + L.numNodes]).length then (1:ℕ) else 0) = 1 := by
          rw [if_pos]
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        refine ⟨rho, ?_, ?_, hstk, ?_, ?_⟩
        · rw [hlen, rlen_node_node hR]
        · intro z hz; obtain ⟨hA, hB⟩ := hmem z hz; rw [hnum]; omega
        · rw [hpc, hpc0, h2, Srec_node_node hR]
          have hsl := Srec_add_rlen L
          simp only [List.length_append, List.length_cons, List.length_nil, hlen0]
          omega
        · have h0 : (if 2 ≤ ([] : List ℕ).length then (1:ℕ) else 0) = 0 := by simp
          have htn : twoNodes (BinaryTree.node v L R) = 1 + twoNodes L + twoNodes R := by
            simp [twoNodes, isNode_eq_true.mpr hL, isNode_eq_true.mpr hR]
          rw [hlc, hlc0, h3, hind, h0, htn]; ring


/-! ## 4. The stack, the pops and the index tests ignore the array and `ecnt` -/

lemma stepN_indep (cur : ℕ) (st st' : StN) (h : st.stk = st'.stk) :
    (stepN cur st).stk = (stepN cur st').stk ∧
    (stepN cur st).pcnt + st'.pcnt = (stepN cur st').pcnt + st.pcnt ∧
    (stepN cur st).lcnt + st'.lcnt = (stepN cur st').lcnt + st.lcnt := by
  obtain ⟨a, s, e, l, p⟩ := st
  obtain ⟨a', s', e', l', p'⟩ := st'
  subst h
  match s with
  | [] => simp [stepN]; omega
  | [top] => by_cases hc : cur < top <;> simp [stepN, hc] <;> omega
  | top :: top2 :: s'' =>
    simp only [stepN, popLoop_length]
    by_cases hc : cur < top
    · simp only [if_pos hc]; exact ⟨trivial, by omega, by omega⟩
    · by_cases h2 : top2 ≤ cur <;> simp [hc, h2] <;> omega

lemma runN_indep : ∀ (xs : List ℕ) (st st' : StN), st.stk = st'.stk →
    (runN xs st).stk = (runN xs st').stk ∧
    (runN xs st).pcnt + st'.pcnt = (runN xs st').pcnt + st.pcnt ∧
    (runN xs st).lcnt + st'.lcnt = (runN xs st').lcnt + st.lcnt := by
  intro xs
  induction xs with
  | nil => intro st st' h; exact ⟨h, Nat.add_comm _ _, Nat.add_comm _ _⟩
  | cons cur rest ih =>
    intro st st' h
    obtain ⟨k1, k2, k3⟩ := stepN_indep cur st st' h
    obtain ⟨m1, m2, m3⟩ := ih (stepN cur st) (stepN cur st') k1
    rw [runN_cons, runN_cons]
    refine ⟨m1, ?_, ?_⟩ <;> omega

/-! ## 5. `M` and `N` simulate each other

The two machines start from the same stack, build the same array, keep the same
stack and pop the same number of times; `N` merely keeps two extra counters.
Rocq proves the two pop invariants separately and derives this as
`pops_M_eq_N`; here it is the input to the `M` side. -/

lemma stepMN_agree (cur : ℕ) (stM : StM) (stN : StN)
    (ha : stM.arr = stN.arr) (hs : stM.stk = stN.stk) (hp : stM.pop = stN.pcnt) :
    (stepM cur stM).arr = (stepN cur stN).arr ∧
    (stepM cur stM).stk = (stepN cur stN).stk ∧
    (stepM cur stM).pop = (stepN cur stN).pcnt := by
  obtain ⟨a, s, c, p⟩ := stM
  obtain ⟨a', s', e, l, p'⟩ := stN
  subst ha; subst hs; subst hp
  match s with
  | [] => simp [stepM, stepN]
  | [top] =>
    simp only [stepM, stepN, popLoop_length]
    by_cases hc : cur < top <;> simp [hc]
  | top :: top2 :: s'' =>
    simp only [stepM, stepN, popLoop_length]
    by_cases hc : cur < top
    · simp [hc]
    · by_cases h2 : top2 ≤ cur
      · simp [hc, h2, popStack_cons2]; omega
      · simp [hc, h2, popStack_cons2]

lemma runMN_agree : ∀ (xs : List ℕ) (stM : StM) (stN : StN),
    stM.arr = stN.arr → stM.stk = stN.stk → stM.pop = stN.pcnt →
    (runM xs stM).arr = (runN xs stN).arr ∧
    (runM xs stM).stk = (runN xs stN).stk ∧
    (runM xs stM).pop = (runN xs stN).pcnt := by
  intro xs
  induction xs with
  | nil => intro stM stN ha hs hp; exact ⟨ha, hs, hp⟩
  | cons cur rest ih =>
    intro stM stN ha hs hp
    obtain ⟨k1, k2, k3⟩ := stepMN_agree cur stM stN ha hs hp
    rw [runM_cons, runN_cons]
    exact ih (stepM cur stM) (stepN cur stN) k1 k2 k3

/-! ## 6. Top level -/

lemma runMFull_cons (x0 : ℕ) (rest : List ℕ) :
    runMFull (x0 :: rest)
      = runM rest { arr := emptyArr, stk := [x0, rest.length + 1], cmp := 0, pop := 0 } := by
  simp [runMFull]

lemma runNFull_cons (x0 : ℕ) (rest : List ℕ) :
    runNFull (x0 :: rest)
      = runN rest { arr := emptyArr, stk := [x0, rest.length + 1],
                    ecnt := 0, lcnt := 0, pcnt := 0 } := by
  simp [runNFull]

/-- The sentinel iteration that prefixes the `gen`-form run does not change the
    pop count or the index-test count. -/
lemma runN_full_vs_gen (root n : ℕ) (rest : List ℕ) (h : root < n) :
    (runN rest { arr := emptyArr, stk := [root, n], ecnt := 0, lcnt := 0, pcnt := 0 }).pcnt
        = (runN (root :: rest)
            { arr := emptyArr, stk := [n], ecnt := 0, lcnt := 0, pcnt := 0 }).pcnt ∧
    (runN rest { arr := emptyArr, stk := [root, n], ecnt := 0, lcnt := 0, pcnt := 0 }).lcnt
        = (runN (root :: rest)
            { arr := emptyArr, stk := [n], ecnt := 0, lcnt := 0, pcnt := 0 }).lcnt := by
  have hstep : stepN root { arr := emptyArr, stk := [n], ecnt := 0, lcnt := 0, pcnt := 0 }
      = { arr := setL emptyArr n root, stk := [root, n], ecnt := 1, lcnt := 0, pcnt := 0 } := by
    simp [stepN, h]
  rw [runN_cons, hstep]
  obtain ⟨-, i2, i3⟩ := runN_indep rest
    { arr := emptyArr, stk := [root, n], ecnt := 0, lcnt := 0, pcnt := 0 }
    { arr := setL emptyArr n root, stk := [root, n], ecnt := 1, lcnt := 0, pcnt := 0 } rfl
  simp only at i2 i3
  exact ⟨by omega, by omega⟩

lemma runNFull_counts (t : T) (h : t ≠ .nil) :
    (runNFull (ip t)).pcnt = Srec t ∧ (runNFull (ip t)).lcnt = twoNodes t := by
  obtain ⟨x0, rest, hip, hx0⟩ := ip_eq_cons h
  have hlen : rest.length + 1 = t.numNodes := by
    have h1 := ip_length t; rw [hip] at h1; simpa using h1
  obtain ⟨rho, -, -, -, hpc, hlc⟩ :=
    runN_gen t 0 [] [t.numNodes]
      { arr := emptyArr, stk := [t.numNodes], ecnt := 0, lcnt := 0, pcnt := 0 }
      h (by simp) (by simp) (by simp)
      (by intro y hy; simp only [List.mem_singleton] at hy; omega)
  rw [← ip_def, hip] at hpc hlc
  obtain ⟨j2, j3⟩ := runN_full_vs_gen x0 t.numNodes rest hx0
  rw [hip, runNFull_cons, hlen]
  simp only [List.length_nil, Nat.add_zero, Nat.zero_add, Nat.reduceLeDiff,
    if_false] at hpc hlc
  exact ⟨by omega, by omega⟩

/-- **The run's pop count is the structural statistic** (Rocq:
    `ReconstructPops.pops_N_Srec`). -/
theorem popsN_eq_Srec (t : T) : popsN (ip t) = Srec t := by
  by_cases h : t = .nil
  · subst h; rfl
  · exact (runNFull_counts t h).1

/-- **The number of index tests is the number of two-children nodes plus one**
    (Rocq: `ReconstructLcount.lcount_N_full`). -/
theorem lcountN_eq (t : T) (h : t ≠ .nil) : lcountN (ip t) = twoNodes t + 1 := by
  rw [lcountN, (runNFull_counts t h).2]

/-- The two algorithms pop the same number of times (Rocq: `pops_M_eq_N`). -/
theorem popsM_eq_popsN (t : T) : popsM (ip t) = popsN (ip t) := by
  by_cases h : t = .nil
  · subst h; rfl
  · obtain ⟨x0, rest, hip, -⟩ := ip_eq_cons h
    rw [popsM, popsN, hip, runMFull_cons, runNFull_cons]
    exact (runMN_agree _ _ _ rfl rfl rfl).2.2

/-- Rocq: `ReconstructPops.pops_M_Srec`. -/
theorem popsM_eq_Srec (t : T) : popsM (ip t) = Srec t := by
  rw [popsM_eq_popsN, popsN_eq_Srec]

end MakinenAnalysis
