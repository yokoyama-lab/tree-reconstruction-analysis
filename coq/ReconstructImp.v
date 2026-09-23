(* ReconstructImp.v
   An imperative refinement of the single-pass construction (Fig.~1).

   The functional model `run` (Reconstruct.v) carries its stack as an abstract
   list (cons = push, head/tail = pop).  Here we replace that list with an
   in-place ARRAY STACK: a buffer `buf` together with a top pointer `sp`.  Push
   writes `buf[sp] := x` and increments `sp`; pop decrements `sp`; the top is
   `buf[sp-1]`.  Popping leaves stale data in the buffer above `sp`, which a
   later push overwrites -- so this models the actual in-place reuse (the
   "aliasing" the paper flags) rather than a fresh allocation.

   We define `runI` over this representation and prove the refinement

       runI ip = run ip    for all ip,

   axiom-free.  The output array is built by exactly the same setL/setR
   operations in both models, so the array equality is genuine Leibniz
   equality (no functional extensionality).

   Rocq Prover 9.1.  Standard library only.  Axiom-free. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import Trees.
Require Import Dictionary.
Require Import Reconstruct.

(* ------------------------------------------------------------------ *)
(* In-place update of a buffer: overwrite in range, append at the end. *)
(* ------------------------------------------------------------------ *)
Fixpoint set_nth (l : list nat) (i v : nat) : list nat :=
  match l, i with
  | [], 0       => [v]
  | [], S j     => 0 :: set_nth [] j v
  | _ :: t, 0   => v :: t
  | h :: t, S j => h :: set_nth t j v
  end.

(* A general firstn/nth split, specialised to nat lists. *)
Lemma firstn_S_nth : forall (l : list nat) i,
  i < length l -> firstn (S i) l = firstn i l ++ [nth i l 0].
Proof.
  induction l as [|h t IH]; intros i Hi.
  - destruct i; cbn [length] in Hi; lia.
  - destruct i as [|i]; [reflexivity|].
    cbn [length] in Hi. cbn [firstn nth app]. f_equal. apply IH. lia.
Qed.

Lemma firstn_set_nth : forall l i v,
  i <= length l -> firstn i (set_nth l i v) = firstn i l.
Proof.
  induction l as [|h t IH]; intros i v Hi.
  - cbn [length] in Hi. assert (i = 0) by lia. subst. reflexivity.
  - destruct i as [|i]; [reflexivity|].
    cbn [length] in Hi. cbn [set_nth firstn]. f_equal. apply IH. lia.
Qed.

Lemma nth_set_nth : forall l i v,
  i <= length l -> nth i (set_nth l i v) 0 = v.
Proof.
  induction l as [|h t IH]; intros i v Hi.
  - cbn [length] in Hi. assert (i = 0) by lia. subst. reflexivity.
  - destruct i as [|i]; [reflexivity|].
    cbn [length] in Hi. cbn [set_nth nth]. apply IH. lia.
Qed.

Lemma lt_length_set_nth : forall l i v,
  i <= length l -> i < length (set_nth l i v).
Proof.
  induction l as [|h t IH]; intros i v Hi.
  - cbn [length] in Hi. assert (i = 0) by lia. subst. cbn [set_nth length]. lia.
  - destruct i as [|i]; cbn [set_nth length]; [lia|].
    cbn [length] in Hi. specialize (IH i v ltac:(lia)). lia.
Qed.

Lemma firstn_S_set_nth : forall l i v,
  i <= length l -> firstn (S i) (set_nth l i v) = firstn i l ++ [v].
Proof.
  intros l i v Hi.
  rewrite firstn_S_nth by (apply lt_length_set_nth; exact Hi).
  rewrite firstn_set_nth by exact Hi.
  rewrite nth_set_nth by exact Hi. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The array stack: buffer + top pointer.                              *)
(* ------------------------------------------------------------------ *)
Record astack := mkstk { buf : list nat ; sp : nat }.

Definition emptystk : astack := mkstk [] 0.
Definition apush (x : nat) (s : astack) : astack :=
  mkstk (set_nth (buf s) (sp s) x) (S (sp s)).
Definition apop (s : astack) : astack := mkstk (buf s) (pred (sp s)).
Definition atop (s : astack) : nat := nth (pred (sp s)) (buf s) 0.
(* pop k times: drop the top k elements (used by the multi-pop loops of M/N). *)
Definition apopn (k : nat) (s : astack) : astack := mkstk (buf s) (sp s - k).

(* The abstract (top-first) view of the live region. *)
Definition absv (s : astack) : list nat := rev (firstn (sp s) (buf s)).

(* Well-formedness: the top pointer is within the buffer. *)
Definition stkWF (s : astack) : Prop := sp s <= length (buf s).

Lemma length_absv : forall s, stkWF s -> length (absv s) = sp s.
Proof.
  intros s H. unfold absv. rewrite length_rev, length_firstn.
  unfold stkWF in H. lia.
Qed.

Lemma absv_apush : forall x s, stkWF s -> absv (apush x s) = x :: absv s.
Proof.
  intros x s H. unfold stkWF in H. unfold absv, apush. cbn [buf sp].
  rewrite firstn_S_set_nth by exact H.
  rewrite rev_app_distr. reflexivity.
Qed.

Lemma stkWF_apush : forall x s, stkWF s -> stkWF (apush x s).
Proof.
  intros x s H. unfold stkWF in H.
  pose proof (lt_length_set_nth (buf s) (sp s) x H) as H2.
  unfold stkWF, apush. cbn [buf sp]. lia.
Qed.

Lemma stkWF_apop : forall s, stkWF s -> stkWF (apop s).
Proof. intros s H. unfold stkWF, apop in *. cbn [buf sp]. lia. Qed.

Lemma atop_absv : forall s, 1 <= sp s -> stkWF s -> atop s = hd 0 (absv s).
Proof.
  intros s H1 H2. unfold stkWF in H2. unfold atop, absv.
  destruct (sp s) as [|k] eqn:E; [lia|]. cbn [pred].
  rewrite firstn_S_nth by lia. rewrite rev_app_distr. cbn [hd app]. reflexivity.
Qed.

Lemma absv_apop : forall s, 1 <= sp s -> stkWF s -> absv (apop s) = tl (absv s).
Proof.
  intros s H1 H2. unfold stkWF in H2. unfold absv, apop. cbn [buf sp].
  destruct (sp s) as [|k] eqn:E; [lia|]. cbn [pred].
  rewrite (firstn_S_nth (buf s) k) by lia.
  rewrite rev_app_distr. cbn [tl app]. reflexivity.
Qed.

(* sp s = 0 iff the abstract stack is empty. *)
Lemma absv_nil_iff : forall s, stkWF s -> (absv s = [] <-> sp s = 0).
Proof.
  intros s H. split; intro He.
  - apply (f_equal (@length nat)) in He. rewrite length_absv in He by exact H.
    simpl in He. exact He.
  - unfold absv. rewrite He. reflexivity.
Qed.

(* The stack, exposed one element at a time (drives the multi-pop loops). *)
Lemma absv_cons : forall s, 1 <= sp s -> stkWF s -> absv s = atop s :: absv (apop s).
Proof.
  intros s H1 H2. rewrite (atop_absv s H1 H2), (absv_apop s H1 H2).
  destruct (absv s) as [|h t] eqn:E.
  - exfalso. pose proof (absv_nil_iff s H2) as [Hf _]. specialize (Hf E). lia.
  - reflexivity.
Qed.

Lemma stkWF_apopn : forall k s, stkWF s -> stkWF (apopn k s).
Proof. intros k s H. unfold stkWF, apopn in *. cbn [buf sp]. lia. Qed.

Lemma absv_apopn : forall k s,
  k <= sp s -> stkWF s -> absv (apopn k s) = skipn k (absv s).
Proof.
  induction k as [|k IH]; intros s Hk HWF.
  - unfold apopn, absv. cbn [buf sp]. rewrite Nat.sub_0_r. reflexivity.
  - assert (Hsp : 1 <= sp s) by lia.
    assert (Hk' : k <= sp (apop s)) by (unfold apop; cbn [sp]; lia).
    assert (HWF' : stkWF (apop s)) by (apply stkWF_apop; exact HWF).
    replace (apopn (S k) s) with (apopn k (apop s)) by
      (unfold apopn, apop; cbn [buf sp]; f_equal; lia).
    rewrite (IH (apop s) Hk' HWF'), (absv_apop s Hsp HWF).
    destruct (absv s) as [|h tl0] eqn:E.
    + exfalso. pose proof (absv_nil_iff s HWF) as [Hf _]. specialize (Hf E). lia.
    + reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The imperative step, mirroring `step` over the array stack.         *)
(* ------------------------------------------------------------------ *)
Definition stepI (prev cur : nat) (st : arr * astack) : arr * astack :=
  let '(a, s) := st in
  let '(a1, s1) :=
    if Nat.ltb cur prev
    then (setL a prev cur, s)
    else if Nat.ltb 0 (sp s)
         then (setR a (atop s) cur, apop s)
         else (a, s) in
  match fst (a1 (cur + 1)) with
  | None   => (a1, apush cur s1)
  | Some _ => (a1, s1)
  end.

Fixpoint runI_aux (prev : nat) (xs : list nat) (st : arr * astack)
  : arr * astack :=
  match xs with
  | []          => st
  | cur :: rest => runI_aux cur rest (stepI prev cur st)
  end.

Definition runI (ip : list nat) : arr :=
  match ip with
  | []         => empty
  | x0 :: rest => fst (runI_aux x0 rest (empty, apush x0 emptystk))
  end.

(* ------------------------------------------------------------------ *)
(* Refinement of one step.                                             *)
(* ------------------------------------------------------------------ *)
Lemma stepI_step : forall prev cur a st,
  stkWF st ->
  fst (stepI prev cur (a, st)) = fst (step prev cur (a, absv st))
  /\ absv (snd (stepI prev cur (a, st))) = snd (step prev cur (a, absv st))
  /\ stkWF (snd (stepI prev cur (a, st))).
Proof.
  intros prev cur a st HWF. unfold stepI, step.
  (* the inner (a1,s1): match the two models branch by branch *)
  destruct (Nat.ltb cur prev) eqn:Elt.
  - (* left child: stack unchanged *)
    cbn match. destruct (fst (setL a prev cur (cur + 1))) eqn:Eg; cbn [fst snd].
    + split; [reflexivity| split; [reflexivity| exact HWF]].
    + split; [reflexivity|]. split.
      * apply absv_apush; exact HWF.
      * apply stkWF_apush; exact HWF.
  - (* right child or empty *)
    destruct (Nat.ltb 0 (sp st)) eqn:Esp.
    + (* sp st > 0 : pop *)
      apply Nat.ltb_lt in Esp.
      assert (Htop : atop st = hd 0 (absv st)) by (apply atop_absv; [lia|exact HWF]).
      assert (Hpop : absv (apop st) = tl (absv st)) by (apply absv_apop; [lia|exact HWF]).
      assert (Hne : absv st <> []) by
        (rewrite absv_nil_iff by exact HWF; lia).
      destruct (absv st) as [|top s'] eqn:Eabs; [contradiction|].
      cbn [hd tl] in Htop, Hpop. rewrite Htop. cbn match.
      destruct (fst (setR a top cur (cur + 1))) eqn:Eg; cbn [fst snd].
      * (* no push: snd = apop st ~ s' *)
        split; [reflexivity| split; [exact Hpop| apply stkWF_apop; exact HWF]].
      * (* push: snd = apush cur (apop st) ~ cur :: s' *)
        split; [reflexivity|]. split.
        -- rewrite absv_apush by (apply stkWF_apop; exact HWF). rewrite Hpop. reflexivity.
        -- apply stkWF_apush, stkWF_apop; exact HWF.
    + (* sp st = 0 : empty, no-op *)
      apply Nat.ltb_ge in Esp. assert (sp st = 0) by lia.
      assert (Hnil : absv st = []) by (rewrite absv_nil_iff by exact HWF; lia).
      rewrite Hnil. cbn match.
      destruct (fst (a (cur + 1))) eqn:Eg; cbn [fst snd].
      * split; [reflexivity| split; [exact Hnil| exact HWF]].
      * split; [reflexivity|]. split.
        -- rewrite absv_apush by exact HWF. rewrite Hnil. reflexivity.
        -- apply stkWF_apush; exact HWF.
Qed.

(* ------------------------------------------------------------------ *)
(* Refinement of the loop, then the whole run.                         *)
(* ------------------------------------------------------------------ *)
Lemma runI_run_aux : forall xs prev a st,
  stkWF st ->
  fst (runI_aux prev xs (a, st)) = fst (run_aux prev xs (a, absv st))
  /\ stkWF (snd (runI_aux prev xs (a, st))).
Proof.
  induction xs as [|cur rest IH]; intros prev a st HWF.
  - simpl. split; [reflexivity| exact HWF].
  - cbn [runI_aux run_aux].
    destruct (stepI prev cur (a, st)) as [a1 s1] eqn:EI.
    destruct (step prev cur (a, absv st)) as [b1 t1] eqn:EF.
    pose proof (stepI_step prev cur a st HWF) as [Ha [Hs Hw]].
    rewrite EI in Ha, Hs, Hw. rewrite EF in Ha, Hs. cbn [fst snd] in Ha, Hs, Hw.
    subst b1.
    specialize (IH cur a1 s1 Hw). rewrite Hs in IH. exact IH.
Qed.

Theorem runI_eq_run : forall ip, runI ip = run ip.
Proof.
  intro ip. unfold runI, run. destruct ip as [|x0 rest]; [reflexivity|].
  assert (HWF0 : stkWF emptystk) by (unfold stkWF, emptystk; simpl; lia).
  assert (Habs : absv (apush x0 emptystk) = [x0]).
  { rewrite absv_apush by exact HWF0. unfold absv, emptystk; reflexivity. }
  pose proof (runI_run_aux rest x0 empty (apush x0 emptystk)
                (stkWF_apush x0 emptystk HWF0)) as [H _].
  rewrite Habs in H. exact H.
Qed.

Print Assumptions runI_eq_run.

(* ------------------------------------------------------------------ *)
(* Tests: the array stack behaves like a stack, and the imperative      *)
(* construction agrees with the functional one on the running example.  *)
(* ------------------------------------------------------------------ *)
Example absv_push_push : absv (apush 5 (apush 3 emptystk)) = [5; 3].
Proof. reflexivity. Qed.

Example absv_push_pop : absv (apop (apush 5 (apush 3 emptystk))) = [3].
Proof. reflexivity. Qed.

Example runI_tree7 : runI (ip tree7) = run (ip tree7).
Proof. apply runI_eq_run. Qed.
