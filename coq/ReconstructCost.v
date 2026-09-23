(* ReconstructCost.v
   Instrumented cost semantics for Algorithm C (single-pop reconstruction,
   algorithm_c.tex Fig. 1).  We attach a comparison counter to the functional
   model of Reconstruct.v and prove, for ALL n (no size bound, no reflection
   over an enumeration), that the algorithm performs

       data-dependent (label/structural) comparisons : 2n - 2
       loop-guard (index) comparisons                : n
       total                                         : 3n - 2

   on the i-p sequence of any non-empty tree.  Crucially the count depends only
   on the SIZE of the tree, never on its shape: Algorithm C is *oblivious*.
   This discharges the gap flagged in formal_verification.tex (the comparison
   counts of the forthcoming Algorithm C "are not mechanized ... would require a
   cost (instrumented) semantics that counts pairwise order tests").

   We also prove the instrumentation is *faithful*: stripping the counter
   recovers Reconstruct.run exactly, so the counter measures the real algorithm.

   Build:  rocq c Trees.v Dictionary.v Reconstruct.v   (first)
           rocq c ReconstructCost.v
   Rocq Prover 9.1.0.  Standard library only; axiom-free (see Print Assumptions). *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import Trees.
Require Import Dictionary.
Require Import Reconstruct.

(* ================================================================== *)
(* 1. Instrumented step: the same work as [step], plus a counter that  *)
(*    is incremented once at each of the two comparisons performed in   *)
(*    one loop iteration of Fig. 1:                                     *)
(*       (c1) the grafting order test   ip[i] <? ip[i-1]                *)
(*       (c2) the push test             a[ip[i]+1].l == TERM            *)
(* ================================================================== *)

(* State carries the node array, the stack, and the comparison count. *)
Definition cstate := (arr * list nat * nat)%type.

Definition step_c (prev cur : nat) (st : cstate) : cstate :=
  let '(a, s, c) := st in
  let c := S c in                            (* (c1) order test cur <? prev *)
  let '(a1, s1) :=
    if Nat.ltb cur prev
    then (setL a prev cur, s)
    else match s with
         | top :: s' => (setR a top cur, s')
         | []        => (a, s)
         end in
  let c := S c in                            (* (c2) push test a1[cur+1].l *)
  match fst (a1 (cur + 1)) with
  | None   => (a1, cur :: s1, c)
  | Some _ => (a1, s1, c)
  end.

Fixpoint run_aux_c (prev : nat) (xs : list nat) (st : cstate) : cstate :=
  match xs with
  | []          => st
  | cur :: rest => run_aux_c cur rest (step_c prev cur st)
  end.

(* The data-dependent comparison count of the whole loop: PUSH(ip[0]) then the
   loop over ip[1..n-1], starting the counter at 0. *)
Definition data_comparisons (ip : list nat) : nat :=
  match ip with
  | []        => 0
  | x0 :: rest => snd (run_aux_c x0 rest (empty, [x0], 0))
  end.

(* The loop guard  i < n  is evaluated once per element (n-1 continuations and
   one exit): exactly  n  index comparisons. *)
Definition guard_comparisons (ip : list nat) : nat := length ip.

Definition total_comparisons (ip : list nat) : nat :=
  guard_comparisons ip + data_comparisons ip.

(* ================================================================== *)
(* 2. Faithfulness: dropping the counter recovers [run] exactly.       *)
(* ================================================================== *)

Lemma step_c_faithful : forall prev cur a s c,
  fst (step_c prev cur (a, s, c)) = step prev cur (a, s).
Proof.
  intros prev cur a s c. unfold step_c, step.
  destruct (Nat.ltb cur prev);
    [ destruct (fst (setL a prev cur (cur + 1)))
    | destruct s as [|top s'];
        [ destruct (fst (a (cur + 1)))
        | destruct (fst (setR a top cur (cur + 1))) ] ];
    reflexivity.
Qed.

Lemma run_aux_c_faithful : forall xs prev a s c,
  fst (run_aux_c prev xs (a, s, c)) = run_aux prev xs (a, s).
Proof.
  induction xs as [|cur rest IH]; intros prev a s c.
  - reflexivity.
  - cbn [run_aux_c run_aux].
    pose proof (step_c_faithful prev cur a s c) as Hf.
    destruct (step_c prev cur (a, s, c)) as [[a1 s1] c1] eqn:E.
    cbn [fst] in Hf. rewrite <- Hf.
    exact (IH cur a1 s1 c1).
Qed.

(* ================================================================== *)
(* 3. The counter is oblivious: each iteration adds exactly 2.         *)
(* ================================================================== *)

Lemma step_c_count : forall prev cur a s c,
  snd (step_c prev cur (a, s, c)) = S (S c).
Proof.
  intros prev cur a s c. unfold step_c.
  destruct (Nat.ltb cur prev);
    [ destruct (fst (setL a prev cur (cur + 1)))
    | destruct s as [|top s'];
        [ destruct (fst (a (cur + 1)))
        | destruct (fst (setR a top cur (cur + 1))) ] ];
    reflexivity.
Qed.

(* The accumulated count after the loop is the starting count plus 2 per
   listed node -- independent of the node values, hence of the tree shape. *)
Lemma run_aux_c_count : forall xs prev a s c,
  snd (run_aux_c prev xs (a, s, c)) = c + 2 * length xs.
Proof.
  induction xs as [|cur rest IH]; intros prev a s c.
  - simpl. lia.
  - cbn [run_aux_c]. destruct (step_c prev cur (a, s, c)) as [[a1 s1] c1] eqn:E.
    pose proof (step_c_count prev cur a s c) as Hc. rewrite E in Hc. cbn [snd] in Hc.
    rewrite (IH cur a1 s1 c1). cbn [length]. lia.
Qed.

(* ================================================================== *)
(* 4. Main count theorems, for every non-empty tree and all n.         *)
(* ================================================================== *)

(* Data-dependent comparisons: exactly 2n - 2. *)
Theorem data_comparisons_count : forall t, t <> Leaf ->
  data_comparisons (ip t) = 2 * size t - 2.
Proof.
  intros t Hne. unfold data_comparisons, ip.
  destruct (ipo 0 t) as [|x0 rest] eqn:E.
  - (* ip t = [] is impossible for a non-empty tree: length ip t = size t >= 1 *)
    exfalso. pose proof (ip_length t) as HL. unfold ip in HL. rewrite E in HL.
    simpl in HL. destruct t; [congruence|simpl in HL; lia].
  - rewrite run_aux_c_count. simpl.
    (* length (x0 :: rest) = size t, so length rest = size t - 1 *)
    pose proof (ip_length t) as HL. unfold ip in HL. rewrite E in HL.
    simpl in HL. lia.
Qed.

(* Loop-guard comparisons: exactly n. *)
Theorem guard_comparisons_count : forall t,
  guard_comparisons (ip t) = size t.
Proof. intro t. unfold guard_comparisons. apply ip_length. Qed.

(* Total comparisons: exactly 3n - 2. *)
Theorem total_comparisons_count : forall t, t <> Leaf ->
  total_comparisons (ip t) = 3 * size t - 2.
Proof.
  intros t Hne. unfold total_comparisons.
  rewrite guard_comparisons_count, data_comparisons_count by exact Hne.
  (* size t >= 1, so n + (2n-2) = 3n-2 over nat subtraction *)
  destruct t; [congruence|]. simpl size. lia.
Qed.

(* ================================================================== *)
(* 5. Obliviousness: the count is a function of the SIZE alone.        *)
(*    Two trees of the same size cost the same -- the formal content   *)
(*    of the claim that Algorithm C has a constant, data-independent,       *)
(*    oblivious comparison count, on which the lower-bound and hardware      *)
(*    papers hinge.                                                          *)
(* ================================================================== *)

Corollary comparisons_oblivious : forall t u,
  t <> Leaf -> u <> Leaf -> size t = size u ->
  total_comparisons (ip t) = total_comparisons (ip u).
Proof.
  intros t u Ht Hu Hsz.
  rewrite (total_comparisons_count t Ht), (total_comparisons_count u Hu).
  rewrite Hsz. reflexivity.
Qed.

(* Concrete sanity: the 7-node example costs 3*7-2 = 19 (data 12, guard 7). *)
Example total_tree7 : total_comparisons (ip tree7) = 19.
Proof. vm_compute. reflexivity. Qed.
Example data_tree7 : data_comparisons (ip tree7) = 12.
Proof. vm_compute. reflexivity. Qed.

(* The instrumented run computes the same array as the uninstrumented [run]:
   faithfulness in general is [run_aux_c_faithful]; here we exhibit it on the
   7-node example by sampling the array at every node (cf. run_tree7_nodes). *)
Example faithful_tree7 :
  let a := fst (fst (run_aux_c 4 (tl (ip tree7)) (empty, [4], 0))) in
  (a 4, a 1, a 0, a 2, a 3, a 6, a 5) = let b := run (ip tree7) in
  (b 4, b 1, b 0, b 2, b 3, b 6, b 5).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* 6. Reversible comparison cost: entry test + exit assertion.         *)
(*                                                                      *)
(* A reversible conditional charges two label comparisons: an ENTRY     *)
(* test on the forward run and an EXIT assertion on the backward run    *)
(* (the orthogonalising i-test/exit-test of a reversible if).  We       *)
(* thread an entry counter and an exit counter through the same step;   *)
(* each conditional bumps both.  The two counters stay equal (the exit  *)
(* assertion exactly mirrors the entry test), so the reversible total   *)
(* is precisely twice the irreversible 3n-2 -- the factor of two of     *)
(* Glueck-Yokoyama 2019 is the redundant exit assertion, not a price of *)
(* reversibility.  Axiom-free.                                          *)
(* ================================================================== *)

Definition rstate := (arr * list nat * nat * nat)%type.   (* a, s, entry, exit *)

Definition step_rev (prev cur : nat) (st : rstate) : rstate :=
  let '(a, s, e, x) := st in
  let e := S e in let x := S x in            (* (c1) order test: entry + exit *)
  let '(a1, s1) :=
    if Nat.ltb cur prev
    then (setL a prev cur, s)
    else match s with top :: s' => (setR a top cur, s') | [] => (a, s) end in
  let e := S e in let x := S x in            (* (c2) push test: entry + exit *)
  match fst (a1 (cur + 1)) with
  | None   => (a1, cur :: s1, e, x)
  | Some _ => (a1, s1, e, x)
  end.

Fixpoint run_aux_rev (prev : nat) (xs : list nat) (st : rstate) : rstate :=
  match xs with
  | []          => st
  | cur :: rest => run_aux_rev cur rest (step_rev prev cur st)
  end.

Definition entryof (st : rstate) : nat := let '(_, _, e, _) := st in e.
Definition exitof  (st : rstate) : nat := let '(_, _, _, x) := st in x.

Definition data_entry (ip : list nat) : nat :=
  match ip with [] => 0 | x0 :: rest => entryof (run_aux_rev x0 rest (empty, [x0], 0, 0)) end.
Definition data_exit (ip : list nat) : nat :=
  match ip with [] => 0 | x0 :: rest => exitof (run_aux_rev x0 rest (empty, [x0], 0, 0)) end.

(* The reversible label-comparison count: every test (the n guard tests and the
   data tests) is charged at entry and again at exit. *)
Definition total_comparisons_rev (ip : list nat) : nat :=
  2 * guard_comparisons ip + data_entry ip + data_exit ip.

(* Each loop iteration charges two entry and two exit comparisons. *)
Lemma step_rev_count : forall prev cur a s e x,
  entryof (step_rev prev cur (a, s, e, x)) = S (S e)
  /\ exitof (step_rev prev cur (a, s, e, x)) = S (S x).
Proof.
  intros. unfold step_rev, entryof, exitof.
  destruct (Nat.ltb cur prev);
    [ destruct (fst (setL a prev cur (cur + 1)))
    | destruct s as [|top s'];
        [ destruct (fst (a (cur + 1)))
        | destruct (fst (setR a top cur (cur + 1))) ] ];
    split; reflexivity.
Qed.

Lemma run_aux_rev_count : forall xs prev a s e x,
  entryof (run_aux_rev prev xs (a, s, e, x)) = e + 2 * length xs
  /\ exitof (run_aux_rev prev xs (a, s, e, x)) = x + 2 * length xs.
Proof.
  induction xs as [|cur rest IH]; intros prev a s e x.
  - simpl. split; lia.
  - cbn [run_aux_rev].
    destruct (step_rev prev cur (a, s, e, x)) as [[[a1 s1] e1] x1] eqn:E.
    pose proof (step_rev_count prev cur a s e x) as [He Hx].
    rewrite E in He, Hx. cbn [entryof exitof] in He, Hx.
    destruct (IH cur a1 s1 e1 x1) as [IHe IHx].
    cbn [length]. split; lia.
Qed.

(* The exit-assertion count equals the entry-test count: the doubling is exactly
   the redundant exit assertion. *)
Theorem rev_entry_eq_exit : forall t, t <> Leaf ->
  data_entry (ip t) = data_exit (ip t).
Proof.
  intros t Hne. unfold data_entry, data_exit. destruct (ip t) as [|x0 rest] eqn:E.
  - reflexivity.
  - destruct (run_aux_rev_count rest x0 empty [x0] 0 0) as [He Hx].
    rewrite He, Hx. reflexivity.
Qed.

(* Hence the reversible cost is exactly twice the irreversible cost, for all n. *)
Theorem total_comparisons_rev_count : forall t, t <> Leaf ->
  total_comparisons_rev (ip t) = 2 * total_comparisons (ip t).
Proof.
  intros t Hne. unfold total_comparisons_rev, total_comparisons.
  assert (Hde : data_exit (ip t) = data_comparisons (ip t)).
  { unfold data_exit, data_comparisons. destruct (ip t) as [|x0 rest] eqn:E;
      [reflexivity|].
    destruct (run_aux_rev_count rest x0 empty [x0] 0 0) as [_ Hx].
    rewrite Hx, run_aux_c_count. reflexivity. }
  rewrite (rev_entry_eq_exit t Hne), Hde. lia.
Qed.

(* In closed form: 2*(3n-2) = 6n-4. *)
Corollary total_comparisons_rev_value : forall t, t <> Leaf ->
  total_comparisons_rev (ip t) = 6 * size t - 4.
Proof.
  intros t Hne. rewrite (total_comparisons_rev_count t Hne),
    (total_comparisons_count t Hne).
  destruct t; [congruence|]. cbn [size]. lia.
Qed.

(* The reversible run computes the same array as the irreversible one
   (faithfulness on the 7-node example; the array ops are identical to step_c). *)
Example rev_faithful_tree7 :
  let '(a, _, _, _) := run_aux_rev 4 (tl (ip tree7)) (empty, [4], 0, 0) in
  (a 4, a 1, a 0, a 2, a 3, a 6, a 5) = let b := run (ip tree7) in
  (b 4, b 1, b 0, b 2, b 3, b 6, b 5).
Proof. vm_compute. reflexivity. Qed.

(* The 7-node example: reversible cost 2*19 = 38 = 6*7-4. *)
Example total_rev_tree7 : total_comparisons_rev (ip tree7) = 38.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* 7. Axiom-freeness                                                   *)
(* ================================================================== *)

Print Assumptions total_comparisons_count.
Print Assumptions total_comparisons_rev_count.
Print Assumptions comparisons_oblivious.
Print Assumptions run_aux_c_faithful.
