(* ReconstructImpM.v
   The imperative array-stack refinement of Maekinen's algorithm M.

   M (ReconstructM.v) carries its state as (array, list stack, #comparisons,
   #pops) and uses a multi-pop inner loop `popM` (do prev := pop while
   cur >= top).  Here we replace the list stack with the in-place array stack of
   ReconstructImp.v and mirror the multi-pop loop as `popMI` (repeated `apop`,
   reading the top two cells buf[sp-1], buf[sp-2]).  We prove the refinement

       absM (runMI_full ip) = runM_full ip    for all ip,

   so the imperative run computes the same array, comparison count and pop count
   as the functional model.  Axiom-free.

   Rocq Prover 9.1.  Standard library only. *)

From Stdlib Require Import List Arith Bool Lia.
Import ListNotations.
Require Import Trees.
Require Import Dictionary.
Require Import Reconstruct.
Require Import ReconstructM.
Require Import ReconstructImp.

(* ------------------------------------------------------------------ *)
(* The multi-pop loop on the array stack, mirroring popM.              *)
(* ------------------------------------------------------------------ *)
Fixpoint popMI (fuel cur : nat) (st : astack) : nat * astack * nat :=
  match fuel with
  | 0 => (cur, st, 0)
  | S f =>
    if Nat.ltb 0 (sp st) then
      let top := atop st in
      if Nat.ltb 1 (sp st) then
        let top2 := atop (apop st) in
        if Nat.leb top2 cur
        then let '(p, r, k) := popMI f cur (apop st) in (p, r, S k)
        else (top, apop st, 1)
      else (top, apop st, 1)
    else (cur, st, 0)
  end.

Lemma popMI_popM : forall fuel cur st, stkWF st ->
  let '(p, r, k) := popMI fuel cur st in
  popM fuel cur (absv st) = (p, absv r, k) /\ stkWF r.
Proof.
  induction fuel as [|f IH]; intros cur st HWF; cbn [popMI].
  - cbn [popM]. split; [reflexivity| exact HWF].
  - destruct (Nat.ltb 0 (sp st)) eqn:E0.
    + apply Nat.ltb_lt in E0.
      rewrite (absv_cons st E0 HWF). cbn [popM].
      destruct (Nat.ltb 1 (sp st)) eqn:E1.
      * apply Nat.ltb_lt in E1.
        assert (Hsp1 : 1 <= sp (apop st)) by (unfold apop; cbn [sp]; lia).
        assert (HWF1 : stkWF (apop st)) by (apply stkWF_apop; exact HWF).
        rewrite (absv_cons (apop st) Hsp1 HWF1). cbn [popM].
        rewrite <- (absv_cons (apop st) Hsp1 HWF1).
        destruct (Nat.leb (atop (apop st)) cur) eqn:Ele.
        -- specialize (IH cur (apop st) HWF1).
           destruct (popMI f cur (apop st)) as [[p r] k].
           destruct IH as [IHe IHw]. rewrite IHe. split; [reflexivity| exact IHw].
        -- split; [reflexivity| exact HWF1].
      * apply Nat.ltb_ge in E1.
        assert (Hsp0 : sp (apop st) = 0) by (unfold apop; cbn [sp]; lia).
        assert (Hnil : absv (apop st) = []) by
          (apply (absv_nil_iff (apop st)); [apply stkWF_apop; exact HWF| exact Hsp0]).
        rewrite Hnil. cbn [popM]. rewrite <- Hnil.
        split; [reflexivity| apply stkWF_apop; exact HWF].
    + apply Nat.ltb_ge in E0. assert (sp st = 0) by lia.
      assert (Hnil : absv st = []) by (apply (absv_nil_iff st); [exact HWF| lia]).
      rewrite Hnil. cbn [popM]. rewrite <- Hnil.
      split; [reflexivity| exact HWF].
Qed.

(* ------------------------------------------------------------------ *)
(* The imperative step, mirroring stepM.                               *)
(* ------------------------------------------------------------------ *)
Definition stateMI := (arr * astack * nat * nat)%type.

Definition stepMI (cur : nat) (st : stateMI) : stateMI :=
  let '(a, s, c, p) := st in
  let c := S c in
  if Nat.ltb 0 (sp s) then
    let top := atop s in
    if Nat.ltb cur top
    then (setL a top cur, apush cur s, c, p)
    else let '(prev, s', k) := popMI (sp s) cur s in
         (setR a prev cur, apush cur s', c + k, p + k)
  else (a, s, c, p).

Fixpoint runMI_aux (xs : list nat) (st : stateMI) : stateMI :=
  match xs with
  | []          => st
  | cur :: rest => runMI_aux rest (stepMI cur st)
  end.

Definition runMI_full (ip : list nat) : stateMI :=
  match ip with
  | []        => (empty, emptystk, 0, 0)
  | x0 :: rest => runMI_aux rest (empty, apush x0 (apush (length ip) emptystk), 0, 0)
  end.

(* The abstraction back to stateM and the stack well-formedness predicate. *)
Definition absM (st : stateMI) : stateM :=
  let '(a, s, c, p) := st in (a, absv s, c, p).
Definition stMWF (st : stateMI) : Prop :=
  let '(a, s, c, p) := st in stkWF s.

(* ------------------------------------------------------------------ *)
(* Refinement of one step.                                             *)
(* ------------------------------------------------------------------ *)
Lemma stepMI_stepM : forall cur st,
  stMWF st -> absM (stepMI cur st) = stepM cur (absM st) /\ stMWF (stepMI cur st).
Proof.
  intros cur st HWF. destruct st as [[[a s] c] p].
  unfold stMWF in HWF. unfold stepMI, stepM, absM.
  destruct (Nat.ltb 0 (sp s)) eqn:E0.
  - apply Nat.ltb_lt in E0.
    rewrite (absv_cons s E0 HWF).
    (* stepM matches on (atop s :: absv (apop s)); top0 = atop s *)
    cbn match. rewrite <- (absv_cons s E0 HWF).
    rewrite (atop_absv s E0 HWF) in *.
    destruct (Nat.ltb cur (hd 0 (absv s))) eqn:Elt.
    + (* left child / push *)
      split.
      * rewrite absv_apush by exact HWF. reflexivity.
      * cbn [stMWF]. apply stkWF_apush; exact HWF.
    + (* right child / multi-pop *)
      pose proof (popMI_popM (sp s) cur s HWF) as HP.
      assert (Hlen : length (absv s) = sp s) by (apply length_absv; exact HWF).
      rewrite Hlen.
      destruct (popMI (sp s) cur s) as [[prev s'] k].
      destruct HP as [HPe HPw]. rewrite HPe.
      split.
      * rewrite absv_apush by exact HPw. reflexivity.
      * cbn [stMWF]. apply stkWF_apush; exact HPw.
  - apply Nat.ltb_ge in E0. assert (sp s = 0) by lia.
    assert (Hnil : absv s = []) by (apply (absv_nil_iff s); [exact HWF| lia]).
    rewrite Hnil. cbn match. rewrite <- Hnil.
    split; [reflexivity| exact HWF].
Qed.

(* ------------------------------------------------------------------ *)
(* Refinement of the loop and the whole run.                           *)
(* ------------------------------------------------------------------ *)
Lemma runMI_runM_aux : forall xs st,
  stMWF st -> absM (runMI_aux xs st) = runM_aux xs (absM st) /\ stMWF (runMI_aux xs st).
Proof.
  induction xs as [|cur rest IH]; intros st HWF.
  - split; [reflexivity| exact HWF].
  - cbn [runMI_aux runM_aux].
    pose proof (stepMI_stepM cur st HWF) as [He Hw].
    specialize (IH (stepMI cur st) Hw). rewrite He in IH. exact IH.
Qed.

Theorem runMI_full_eq : forall ip, absM (runMI_full ip) = runM_full ip.
Proof.
  intro ip. unfold runMI_full, runM_full. destruct ip as [|x0 rest]; [reflexivity|].
  assert (HWF0 : stkWF emptystk) by (unfold stkWF, emptystk; simpl; lia).
  assert (HWFs : stkWF (apush x0 (apush (length (x0 :: rest)) emptystk)))
    by (apply stkWF_apush, stkWF_apush; exact HWF0).
  assert (Habs : absv (apush x0 (apush (length (x0 :: rest)) emptystk))
                 = [x0; length (x0 :: rest)]).
  { rewrite absv_apush by (apply stkWF_apush; exact HWF0).
    rewrite absv_apush by exact HWF0. unfold absv, emptystk; reflexivity. }
  pose proof (runMI_runM_aux rest
                (empty, apush x0 (apush (length (x0 :: rest)) emptystk), 0, 0)
                HWFs) as [He _].
  unfold absM in He. rewrite Habs in He. exact He.
Qed.

Print Assumptions runMI_full_eq.

(* ------------------------------------------------------------------ *)
(* Tests: the imperative run reproduces M's array, comparison and pop   *)
(* counts on the running example.                                       *)
(* ------------------------------------------------------------------ *)
Example runMI_tree7 : absM (runMI_full (ip tree7)) = runM_full (ip tree7).
Proof. apply runMI_full_eq. Qed.
