import MakinenAnalysis.PopDegreeBridge

/-!
# The execution semantics of the two reconstruction algorithms

This file ports the *operational* half of the Rocq development: the i-p
sequence, the two stack machines of Figure 1 of `paper_ja.tex`, their
comparison and pop counters, and the counter invariants

* `cmpsM_eq` : `A_M = 2n - 1 + pops_M`  (Rocq `ReconstructM.total_comparisons_M_count`)
* `cmpsN_eq` : `A_N = pops_N + lcount_N + n + 1`  (Rocq `ReconstructN.total_comparisons_N_count`)

together with the *structural* pop count `Srec` and the identification

* `sum_toPop_eq_Srec` : `Srec t = (toPop t).sum`

which is the joint of this operational layer with the codeword statistics of
`ExactMoments`/`TreeIdentities`.

Nothing here needs a program logic: as in Rocq, the two machines are ordinary
structurally recursive folds `List ℕ → σ → σ` and the counter invariants are
one-step deltas plus a list induction.  (The deep-embedded IMP layer of
`../../coq/ImpHoare.v` is about the C array layout and in-place reuse, a
different concern, and is not on the path to these theorems.)

The runs carry the node array as well as the counters, so the objects below are
models of the reconstruction algorithms and not merely of their cost; that the
array really is rebuilt is pinned by the `Regression` section
(`childAssoc`-agreement on explicit trees; Rocq checks all trees of size ≤ 9
by reflection in `Reconstruct.reconstruct_correct_upto_10` and
`ReconstructN.correctN_upto_9`).
-/

namespace MakinenAnalysis

/-! ## 1. The i-p sequence -/

/-- `ipo off t` : the inorder labels of `t` listed in **preorder**, where `off`
    is the number of nodes preceding `t` in the global inorder.  The current
    node's inorder number is `off + numNodes l`.  (Rocq: `Dictionary.ipo`.) -/
def ipo : ℕ → T → List ℕ
  | _, .nil => []
  | off, .node _ l r =>
      (off + l.numNodes) :: (ipo off l ++ ipo (off + l.numNodes + 1) r)

/-- The i-p sequence of a tree (Rocq: `Dictionary.ip`). -/
def ip (t : T) : List ℕ := ipo 0 t

@[simp] lemma ipo_nil (off : ℕ) : ipo off (.nil : T) = [] := rfl

@[simp] lemma ipo_node (off : ℕ) (v : Unit) (l r : T) :
    ipo off (.node v l r)
      = (off + l.numNodes) :: (ipo off l ++ ipo (off + l.numNodes + 1) r) := rfl

/-- Rocq: `Dictionary.ipo_length`. -/
lemma ipo_length : ∀ (t : T) (off : ℕ), (ipo off t).length = t.numNodes := by
  intro t
  induction t with
  | nil => intro off; simp
  | node v l r ihl ihr =>
    intro off
    simp only [ipo_node, List.length_cons, List.length_append, ihl, ihr,
      BinaryTree.numNodes]

lemma ip_length (t : T) : (ip t).length = t.numNodes := ipo_length t 0

/-- A non-empty tree has a non-empty i-p sequence. -/
lemma ipo_ne_nil_of_ne_nil {t : T} (h : t ≠ .nil) : ipo 0 t ≠ [] := by
  cases t with
  | nil => exact absurd rfl h
  | node v l r => simp

/-! ### The i-p sequence determines the tree

Rocq proves this (`IpInjective.ip_injective`) as a corollary of the all-`n`
correctness of the Algorithm-C model (`ReconstructFull.reconstruct_correct_all`):
decoding recovers the tree, so encoding is injective.  Here it is proved
directly from the shape of `ipo`, which needs no reconstruction argument: the
head fixes `numNodes L`, the length fixes `numNodes R`, and `List.append_inj`
splits the tail. -/

lemma numNodes_eq_zero {t : T} (h : t.numNodes = 0) : t = .nil := by
  cases t with
  | nil => rfl
  | node _ _ _ => simp [BinaryTree.numNodes] at h

lemma ipo_inj : ∀ (t₁ t₂ : T) (off : ℕ), ipo off t₁ = ipo off t₂ → t₁ = t₂ := by
  intro t₁
  induction t₁ with
  | nil =>
    intro t₂ off h
    rw [ipo_nil] at h
    have := ipo_length t₂ off
    rw [← h] at this
    exact (numNodes_eq_zero this.symm).symm
  | node v L R ihL ihR =>
    intro t₂ off h
    cases t₂ with
    | nil => rw [ipo_nil] at h; simp at h
    | node w L' R' =>
      cases v; cases w
      rw [ipo_node, ipo_node] at h
      obtain ⟨hhd, htl⟩ := List.cons_eq_cons.mp h
      have hL : L.numNodes = L'.numNodes := by omega
      have hlen : (ipo off L).length = (ipo off L').length := by
        rw [ipo_length, ipo_length, hL]
      obtain ⟨h1, h2⟩ := List.append_inj htl hlen
      rw [hL] at h2
      rw [ihL L' off h1, ihR R' (off + L'.numNodes + 1) h2]

/-- **The i-p sequence determines the tree** (Rocq: `IpInjective.ip_injective`). -/
theorem ip_injective {t₁ t₂ : T} (h : ip t₁ = ip t₂) : t₁ = t₂ :=
  ipo_inj t₁ t₂ 0 h

/-! ### The decoder: the i-p sequence is invertible

Rocq's `IpInjective.ip_roundtrip` states the round trip through algorithm C's
run (`ReconstructFull.reconstruct_correct_all`).  Here the inverse is a
functional decoder: the head of `ipo off t` is `off + numNodes l`, so `x - off`
is the size of the left subtree and splits the tail into the two subtrees'
sequences.  The recursion is on a fuel argument (as in `popLoop`) so that the
decoder is structurally recursive and reduces in the kernel: the regression
`ipDec 0 (ip tree7) = tree7` in `ExecBridge` is closed by `decide`. -/

/-- Fuelled decoder: `f` bounds the recursion depth (`w.length` always
    suffices, `ipDecF_ipo`). -/
def ipDecF : ℕ → ℕ → List ℕ → T
  | 0, _, _ => .nil
  | f + 1, off, w =>
      match w with
      | [] => .nil
      | x :: rest =>
          .node () (ipDecF f off (rest.take (x - off))) (ipDecF f (x + 1) (rest.drop (x - off)))

/-- Decoder for the i-p sequence: the head is the root's inorder label, so
    `x - off` is the size of the left subtree, which splits the tail. -/
def ipDec (off : ℕ) (w : List ℕ) : T := ipDecF w.length off w

@[simp] lemma ipDecF_zero (off : ℕ) (w : List ℕ) : ipDecF 0 off w = .nil := rfl

@[simp] lemma ipDecF_succ_nil (f off : ℕ) : ipDecF (f + 1) off [] = .nil := rfl

@[simp] lemma ipDecF_succ_cons (f off x : ℕ) (rest : List ℕ) :
    ipDecF (f + 1) off (x :: rest)
      = .node () (ipDecF f off (rest.take (x - off))) (ipDecF f (x + 1) (rest.drop (x - off))) :=
  rfl

/-- With enough fuel the decoder inverts `ipo`. -/
lemma ipDecF_ipo : ∀ (t : T) (off f : ℕ), t.numNodes ≤ f → ipDecF f off (ipo off t) = t := by
  intro t
  induction t with
  | nil =>
    intro off f _
    cases f <;> rfl
  | node v L R ihL ihR =>
    intro off f hf
    cases v
    have hf' : L.numNodes + R.numNodes + 1 ≤ f := hf
    cases f with
    | zero => omega
    | succ f =>
      rw [ipo_node, ipDecF_succ_cons, Nat.add_sub_cancel_left,
        List.take_left' (ipo_length L off), List.drop_left' (ipo_length L off),
        ihL off f (by omega), ihR (off + L.numNodes + 1) f (by omega)]

/-- **The decoder inverts the i-p sequence**, for every tree and every offset. -/
theorem ipDec_ipo (t : T) (off : ℕ) : ipDec off (ipo off t) = t :=
  ipDecF_ipo t off (ipo off t).length (le_of_eq (ipo_length t off).symm)

/-- **The i-p round trip** (Rocq: `IpInjective.ip_roundtrip`).  Rocq's first
    conjunct is stated for algorithm C's run (`reconstruct_correct_all`); here
    the inverse is the functional decoder `ipDec`, and the algorithms' runs are
    covered for `n ≤ 8` by `rebuildsN_le_eight` / `rebuildsM_le_eight`
    (`ExecBridge`). -/
theorem ip_roundtrip (t : T) : ipDec 0 (ip t) = t ∧ ∀ u : T, ip u = ip t → u = t :=
  ⟨ipDec_ipo t 0, fun _ h => ip_injective h⟩

/-! ## 2. The node array -/

/-- A node cell: the `(left, right)` child fields; `none` is the C code's
    `TERM`. -/
abbrev Cell := Option ℕ × Option ℕ

/-- The node array, modelled (as in Rocq) as a total function, so the virtual
    cell `a[n]` needs no special case. -/
abbrev Arr := ℕ → Cell

/-- All fields `TERM`. -/
def emptyArr : Arr := fun _ => (none, none)

/-- `a[k].l := v`. -/
def setL (a : Arr) (k v : ℕ) : Arr := fun x => if x = k then (some v, (a x).2) else a x

/-- `a[k].r := v`. -/
def setR (a : Arr) (k v : ℕ) : Arr := fun x => if x = k then ((a x).1, some v) else a x

/-! ## 3. The multi-pop inner loop

`repeat prev := pop() until topLabel() > ip[i]`.  Pops at least once; each pop
is followed by one label comparison, so the number of comparisons equals the
number of pops, which is what is returned.  `fuel` bounds the recursion; the
callers pass the stack length.

Rocq defines this twice (`ReconstructM.popM` and `ReconstructN.popN`) and
proves the two equal (`ReconstructPops.popM_popN`); here the two algorithms
share the single definition, which is the same fact recorded in the definition
instead of in a lemma.  The *call sites* still differ: `stepM` enters the loop
with the whole stack, `stepN` pops once by hand first. -/
def popLoop : ℕ → ℕ → List ℕ → ℕ × List ℕ × ℕ
  | 0, cur, s => (cur, s, 0)
  | _ + 1, cur, [] => (cur, [], 0)
  | _ + 1, _, [top] => (top, [], 1)
  | f + 1, cur, top :: top2 :: s'' =>
      if top2 ≤ cur then
        let r := popLoop f cur (top2 :: s'')
        (r.1, r.2.1, r.2.2 + 1)
      else (top, top2 :: s'', 1)

/-- The same loop with the **stack itself** as the decreasing measure.  Rocq
    carries a fuel argument (and the callers always pass the stack length);
    `popLoop_eq_popStack` below shows the fuel never truncates, so every proof
    can reason with this fuel-free form. -/
def popStack (cur : ℕ) : List ℕ → ℕ × List ℕ × ℕ
  | [] => (cur, [], 0)
  | [top] => (top, [], 1)
  | top :: top2 :: s =>
      if top2 ≤ cur then
        let r := popStack cur (top2 :: s)
        (r.1, r.2.1, r.2.2 + 1)
      else (top, top2 :: s, 1)

@[simp] lemma popStack_nil (cur : ℕ) : popStack cur [] = (cur, [], 0) := rfl
@[simp] lemma popStack_single (cur top : ℕ) : popStack cur [top] = (top, [], 1) := rfl

lemma popStack_cons2 (cur top top2 : ℕ) (s : List ℕ) :
    popStack cur (top :: top2 :: s)
      = if top2 ≤ cur then
          ((popStack cur (top2 :: s)).1, (popStack cur (top2 :: s)).2.1,
            (popStack cur (top2 :: s)).2.2 + 1)
        else (top, top2 :: s, 1) := rfl

/-- **The fuel never truncates.**  As soon as the fuel is at least the stack
    length, the fuelled loop of Rocq and the fuel-free `popStack` agree. -/
lemma popLoop_eq_popStack : ∀ (s : List ℕ) (cur f : ℕ), s.length ≤ f →
    popLoop f cur s = popStack cur s := by
  intro s
  induction s with
  | nil => intro cur f _; cases f <;> rfl
  | cons top s' ih =>
    intro cur f hf
    match s', f with
    | _, 0 => simp at hf
    | [], _ + 1 => rfl
    | top2 :: s'', f' + 1 =>
      have hf' : (top2 :: s'').length ≤ f' := by
        simp only [List.length_cons] at hf ⊢; omega
      show (if top2 ≤ cur then
              ((popLoop f' cur (top2 :: s'')).1, (popLoop f' cur (top2 :: s'')).2.1,
                (popLoop f' cur (top2 :: s'')).2.2 + 1)
            else (top, top2 :: s'', 1)) = _
      rw [ih cur f' hf', popStack_cons2]

/-- The form in which the loop occurs inside `stepM` and `stepN`. -/
@[simp] lemma popLoop_length (cur : ℕ) (s : List ℕ) :
    popLoop s.length cur s = popStack cur s :=
  popLoop_eq_popStack s cur s.length le_rfl

/-! ## 4. Algorithm M (Mäkinen) -/

/-- The state of a run of `M`: node array, stack, label-comparison counter,
    construction-pop counter. -/
structure StM where
  /-- The node array being filled in. -/
  arr : Arr
  /-- The label stack. -/
  stk : List ℕ
  /-- Number of label comparisons (`β`) performed so far. -/
  cmp : ℕ
  /-- Number of construction pops performed so far. -/
  pop : ℕ

/-- One iteration of `M`'s `for` loop on the current element `cur`: one order
    test `ip[i-1] ? ip[i]`, then either a left-child graft and a push, or the
    multi-pop loop followed by a right-child graft and a push. -/
def stepM (cur : ℕ) (st : StM) : StM :=
  match st.stk with
  | [] => { st with cmp := st.cmp + 1 }          -- unreachable (sentinel)
  | top :: s' =>
      if cur < top then
        { arr := setL st.arr top cur, stk := cur :: top :: s',
          cmp := st.cmp + 1, pop := st.pop }
      else
        let r := popLoop (top :: s').length cur (top :: s')
        { arr := setR st.arr r.1 cur, stk := cur :: r.2.1,
          cmp := st.cmp + 1 + r.2.2, pop := st.pop + r.2.2 }

/-- The loop of `M` (Rocq: `runM_aux`). -/
def runM : List ℕ → StM → StM
  | [], st => st
  | cur :: rest, st => runM rest (stepM cur st)

/-- Top level: a sentinel greater than every label at the bottom of the stack,
    `PUSH(ip[0])`, then the loop over `ip[1..n-1]`. -/
def runMFull (w : List ℕ) : StM :=
  match w with
  | [] => { arr := emptyArr, stk := [], cmp := 0, pop := 0 }
  | x0 :: rest => runM rest { arr := emptyArr, stk := [x0, w.length], cmp := 0, pop := 0 }

/-- The (data-dependent) number of construction pops of `M`. -/
def popsM (w : List ℕ) : ℕ := (runMFull w).pop

/-- `M`'s total comparison count: the `n` evaluations of the loop guard `i < n`
    plus the label comparisons. -/
def cmpsM (w : List ℕ) : ℕ := w.length + (runMFull w).cmp

/-! ## 5. Algorithm N (Glück–Yokoyama) -/

/-- The state of a run of `N`: node array, stack, label-comparison counter
    (`β`: the tests A, B and the multi-pop D), index-test counter (`α`: the
    tests C), construction-pop counter. -/
structure StN where
  /-- The node array being filled in. -/
  arr : Arr
  /-- The label stack. -/
  stk : List ℕ
  /-- Number of label comparisons (`β`) performed so far. -/
  ecnt : ℕ
  /-- Number of index tests (`α`) performed so far. -/
  lcnt : ℕ
  /-- Number of construction pops performed so far. -/
  pcnt : ℕ

/-- One iteration of `N`'s `while(1)` loop.  `N` pops once per right child and
    occasionally more; every extra (double) pop is preceded by one index test
    `i ≥ n`. -/
def stepN (cur : ℕ) (st : StN) : StN :=
  match st.stk with
  | [] => { st with ecnt := st.ecnt + 1 }        -- unreachable (sentinel)
  | top :: s' =>
      if cur < top then
        { arr := setL st.arr top cur, stk := cur :: top :: s',
          ecnt := st.ecnt + 1, lcnt := st.lcnt, pcnt := st.pcnt }
      else
        match s' with
        | [] =>
            { arr := setR st.arr top cur, stk := [cur],
              ecnt := st.ecnt + 2, lcnt := st.lcnt, pcnt := st.pcnt + 1 }
        | top2 :: s'' =>
            if top2 ≤ cur then
              let r := popLoop (top2 :: s'').length cur (top2 :: s'')
              { arr := setR st.arr r.1 cur, stk := cur :: r.2.1,
                ecnt := st.ecnt + 2 + r.2.2, lcnt := st.lcnt + 1,
                pcnt := st.pcnt + 1 + r.2.2 }
            else
              { arr := setR st.arr top cur, stk := cur :: top2 :: s'',
                ecnt := st.ecnt + 2, lcnt := st.lcnt, pcnt := st.pcnt + 1 }

/-- The loop of `N` (Rocq: `runN_aux`). -/
def runN : List ℕ → StN → StN
  | [], st => st
  | cur :: rest, st => runN rest (stepN cur st)

/-- Top level, as for `M`. -/
def runNFull (w : List ℕ) : StN :=
  match w with
  | [] => { arr := emptyArr, stk := [], ecnt := 0, lcnt := 0, pcnt := 0 }
  | x0 :: rest =>
      runN rest { arr := emptyArr, stk := [x0, w.length], ecnt := 0, lcnt := 0, pcnt := 0 }

/-- The number of construction pops of `N`. -/
def popsN (w : List ℕ) : ℕ := (runNFull w).pcnt

/-- `N`'s index tests (`α`): the double-pop events plus the one at the
    terminating iteration. -/
def lcountN (w : List ℕ) : ℕ := (runNFull w).lcnt + 1

/-- `N`'s total comparison count.  The terminating iteration adds two label
    comparisons and one index test before the `break`, and no construction
    pop. -/
def cmpsN (w : List ℕ) : ℕ := ((runNFull w).ecnt + 2) + ((runNFull w).lcnt + 1)

/-! ## 6. The counter invariants

Each loop iteration raises the label-comparison counter by exactly one more
than the pop counter, whichever branch it takes: the `if` branch costs one
comparison and no pop, and the `else` branch's extra comparisons are exactly
one plus its pops. -/

/-- Rocq: `ReconstructM.stepM_step`. -/
lemma stepM_delta (cur : ℕ) (st : StM) :
    (stepM cur st).cmp + st.pop = (stepM cur st).pop + st.cmp + 1 := by
  obtain ⟨a, s, c, p⟩ := st
  match s with
  | [] => simp [stepM]; omega
  | top :: s' => by_cases h : cur < top <;> simp [stepM, h] <;> omega

/-- Rocq: `ReconstructM.runM_aux_count`. -/
lemma runM_delta : ∀ (xs : List ℕ) (st : StM),
    (runM xs st).cmp + st.pop = (runM xs st).pop + st.cmp + xs.length := by
  intro xs
  induction xs with
  | nil => intro st; simp [runM]; omega
  | cons cur rest ih =>
    intro st
    have h1 := stepM_delta cur st
    have h2 := ih (stepM cur st)
    simp only [runM, List.length_cons]
    omega

/-- Rocq: `ReconstructN.stepN_delta`. -/
lemma stepN_delta (cur : ℕ) (st : StN) :
    (stepN cur st).ecnt + st.pcnt = (stepN cur st).pcnt + st.ecnt + 1 := by
  obtain ⟨a, s, e, l, p⟩ := st
  match s with
  | [] => simp [stepN]; omega
  | top :: s' =>
    by_cases h : cur < top
    · simp [stepN, h]; omega
    · match s' with
      | [] => simp [stepN, h]; omega
      | top2 :: s'' => by_cases h2 : top2 ≤ cur <;> simp [stepN, h, h2] <;> omega

/-- Rocq: `ReconstructN.runN_aux_count`. -/
lemma runN_delta : ∀ (xs : List ℕ) (st : StN),
    (runN xs st).ecnt + st.pcnt = (runN xs st).pcnt + st.ecnt + xs.length := by
  intro xs
  induction xs with
  | nil => intro st; simp [runN]; omega
  | cons cur rest ih =>
    intro st
    have h1 := stepN_delta cur st
    have h2 := ih (stepN cur st)
    simp only [runN, List.length_cons]
    omega

/-- The fold splits along `++` (Rocq: `runM_aux_app`). -/
lemma runM_append : ∀ (xs ys : List ℕ) (st : StM),
    runM (xs ++ ys) st = runM ys (runM xs st) := by
  intro xs
  induction xs with
  | nil => intro ys st; simp [runM]
  | cons x xs ih => intro ys st; simp only [List.cons_append, runM]; exact ih ys _

/-- The fold splits along `++` (Rocq: `ReconstructLcount.runN_aux_app`). -/
lemma runN_append : ∀ (xs ys : List ℕ) (st : StN),
    runN (xs ++ ys) st = runN ys (runN xs st) := by
  intro xs
  induction xs with
  | nil => intro ys st; simp [runN]
  | cons x xs ih => intro ys st; simp only [List.cons_append, runN]; exact ih ys _

/-- The count identity for `M`, on an arbitrary non-empty input word: the
    loop-guard tests and the label comparisons together come to
    `2n - 1 + pops`. -/
lemma cmpsM_cons (x0 : ℕ) (rest : List ℕ) :
    cmpsM (x0 :: rest) + 1 = 2 * (rest.length + 1) + popsM (x0 :: rest) := by
  have hd := runM_delta rest
    { arr := emptyArr, stk := [x0, rest.length + 1], cmp := 0, pop := 0 }
  simp only [cmpsM, popsM, runMFull, List.length_cons] at *
  omega

/-- The count identity for `N`, on an arbitrary non-empty input word. -/
lemma cmpsN_cons (x0 : ℕ) (rest : List ℕ) :
    cmpsN (x0 :: rest)
      = popsN (x0 :: rest) + lcountN (x0 :: rest) + (rest.length + 1) + 1 := by
  have hd := runN_delta rest
    { arr := emptyArr, stk := [x0, rest.length + 1], ecnt := 0, lcnt := 0, pcnt := 0 }
  simp only [cmpsN, popsN, lcountN, runNFull, List.length_cons] at *
  omega

@[simp] lemma ip_def (t : T) : ip t = ipo 0 t := rfl

/-- The i-p sequence of a non-empty tree starts with the root's inorder number,
    which is smaller than `n` (so the bottom sentinel `n` is never popped). -/
lemma ip_eq_cons {t : T} (h : t ≠ .nil) :
    ∃ x0 rest, ip t = x0 :: rest ∧ x0 < t.numNodes := by
  cases t with
  | nil => exact absurd rfl h
  | node v l r =>
    refine ⟨_, _, rfl, ?_⟩
    simp only [BinaryTree.numNodes]
    omega

/-- **The count identity for `M`** (Rocq: `ReconstructM.total_comparisons_M_count`).
    Running `M` on the i-p sequence of `t` performs exactly `2n - 1 + S`
    comparisons, where `S = popsM (ip t)` is the run's pop count.  This is
    equation `eq:AM` of `paper_ja.tex` before the structural substitution. -/
theorem cmpsM_eq (t : T) (h : t ≠ .nil) :
    cmpsM (ip t) = 2 * t.numNodes - 1 + popsM (ip t) := by
  obtain ⟨x0, rest, hip, -⟩ := ip_eq_cons h
  have hlen : rest.length + 1 = t.numNodes := by
    have h1 := ip_length t; rw [hip] at h1; simpa using h1
  have hc := cmpsM_cons x0 rest
  rw [← hip, hlen] at hc
  omega

/-- **The count identity for `N`** (Rocq: `ReconstructN.total_comparisons_N_count`).
    This is the algorithm-intrinsic form; with `lcountN_eq` it becomes
    equation `eq:AN` of `paper_ja.tex`, `A_N = S + P₂ + (n+2)`. -/
theorem cmpsN_eq (t : T) (h : t ≠ .nil) :
    cmpsN (ip t) = popsN (ip t) + lcountN (ip t) + t.numNodes + 1 := by
  obtain ⟨x0, rest, hip, -⟩ := ip_eq_cons h
  have hlen : rest.length + 1 = t.numNodes := by
    have h1 := ip_length t; rw [hip] at h1; simpa using h1
  have hc := cmpsN_cons x0 rest
  rw [← hip, hlen] at hc
  omega

/-! ## 7. The structural pop count and the codeword total

`Srec` is the Rocq development's structural pop statistic
(`ReconstructPops.Srec`) and `rlen` the length of the residue a run leaves on
the stack.  `sum_toPop_eq_Srec` identifies `Srec` with the sum of the Mäkinen
pop-codeword, which is the statistic `ExactMoments` computes the moments of.
This is the join point of the two halves of the development. -/

/-- The structural pop count (Rocq: `ReconstructPops.Srec`). -/
def Srec : T → ℕ
  | .nil => 0
  | .node _ l r => match r with
      | .nil => Srec l
      | .node _ _ _ => l.numNodes + 1 + Srec r

/-- The length of the residue a run leaves on the stack
    (Rocq: `ReconstructPops.rlen`). -/
def rlen : T → ℕ
  | .nil => 0
  | .node _ l r => match r with
      | .nil => rlen l + 1
      | .node _ _ _ => rlen r

@[simp] lemma Srec_nil : Srec (.nil : T) = 0 := rfl
@[simp] lemma rlen_nil : rlen (.nil : T) = 0 := rfl

lemma Srec_node_nil (v : Unit) (l : T) : Srec (.node v l .nil) = Srec l := rfl
lemma rlen_node_nil (v : Unit) (l : T) : rlen (.node v l .nil) = rlen l + 1 := rfl

lemma Srec_node_node {v : Unit} {l r : T} (hr : r ≠ .nil) :
    Srec (.node v l r) = l.numNodes + 1 + Srec r := by
  cases r with
  | nil => exact absurd rfl hr
  | node _ _ _ => rfl

lemma rlen_node_node {v : Unit} {l r : T} (hr : r ≠ .nil) :
    rlen (.node v l r) = rlen r := by
  cases r with
  | nil => exact absurd rfl hr
  | node _ _ _ => rfl

/-- Rocq: `ReconstructPops.srec_rlen_size`. -/
lemma Srec_add_rlen (t : T) : Srec t + rlen t = t.numNodes := by
  induction t with
  | nil => simp
  | node v l r ihl ihr =>
    by_cases hr : r = .nil
    · subst hr
      simp only [Srec_node_nil, rlen_node_nil, BinaryTree.numNodes] at *
      omega
    · rw [Srec_node_node hr, rlen_node_node hr]
      simp only [BinaryTree.numNodes] at *
      omega

/-- Rocq: `ReconstructPops.rlen_pos`. -/
lemma rlen_pos {t : T} (h : t ≠ .nil) : 1 ≤ rlen t := by
  induction t with
  | nil => exact absurd rfl h
  | node v l r _ ihr =>
    by_cases hr : r = .nil
    · subst hr; simp [rlen_node_nil]
    · rw [rlen_node_node hr]; exact ihr hr

/-- The encoder's bookkeeping value is the residue length.  (`rem` is the
    second component of `enc`, ported from Rocq's `Codewords.v`.) -/
lemma rem_eq_rlen (t : T) : rem t = rlen t := by
  induction t with
  | nil => simp
  | node v L R ihL ihR =>
    by_cases hL : L = .nil <;> by_cases hR : R = .nil
    · subst hL; subst hR; simp [rlen_node_nil]
    · subst hL
      rw [rem_lR hR, rlen_node_node hR, ihR]
    · subst hR
      rw [rem_Ln hL, rlen_node_nil, ihL]
    · rw [rem_Rnn hR, rlen_node_node hR, ihR]

/-- **The structural pop count is the codeword total** (the Lean side of
    Rocq's `Srec`).  `Srec t = Σ toPop t`, so every moment computed in
    `ExactMoments` over the codewords is a moment of `Srec`. -/
theorem sum_toPop_eq_Srec (t : T) : (toPop t).sum = Srec t := by
  induction t with
  | nil => simp
  | node v L R ihL ihR =>
    by_cases hL : L = .nil <;> by_cases hR : R = .nil
    · subst hL; subst hR; simp [Srec_node_nil]
    · subst hL
      rw [toPop_lR hR, Srec_node_node hR]
      simp only [List.sum_cons, ihR, BinaryTree.numNodes]
    · subst hR
      rw [toPop_Ln hL, Srec_node_nil]
      simp only [List.sum_cons, ihL, Nat.zero_add]
    · rw [toPop_LR hL hR, Srec_node_node hR]
      have hrl : (toPop L).sum + rem L = L.numNodes := by
        rw [ihL, rem_eq_rlen]; exact Srec_add_rlen L
      simp only [List.sum_append, List.sum_cons, ihL, ihR, Nat.zero_add] at *
      omega

end MakinenAnalysis
