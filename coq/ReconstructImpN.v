(* ReconstructImpN.v
   The imperative array-stack refinement of the improved algorithm N.

   N (ReconstructN.v) carries (array, list stack, ec, lc, pp): the order-test
   counter ec, the index-test counter lc, and the construction-pop counter pp.
   It pops once per right child and occasionally more (the double-pop do-while,
   reusing the same multi-pop loop as M).  We replace the list stack with the
   in-place array stack of ReconstructImp.v, reuse popMI (ReconstructImpM.v) for
   the double pop, and prove the refinement

       absN (runNI0 ip) = runN0 ip    for all ip,

   so the imperative run computes the same array and the same three counters as
   the functional model.  Axiom-free.

   Rocq Prover 9.1.  Standard library only. *)

From Stdlib Require Import List Arith Bool Lia.
Import ListNotations.
Require Import Trees.
Require Import Dictionary.
Require Import Reconstruct.
Require Import ReconstructN.
Require Import ReconstructImp.
Require Import ReconstructImpM.

(* popMI mirrors popN exactly as it mirrors popM (same loop body). *)
Lemma popMI_popN : forall fuel cur st, stkWF st ->
  let '(p, r, k) := popMI fuel cur st in
  popN fuel cur (absv st) = (p, absv r, k) /\ stkWF r.
Proof.
  induction fuel as [|f IH]; intros cur st HWF; cbn [popMI].
  - cbn [popN]. split; [reflexivity| exact HWF].
  - destruct (Nat.ltb 0 (sp st)) eqn:E0.
    + apply Nat.ltb_lt in E0.
      rewrite (absv_cons st E0 HWF). cbn [popN].
      destruct (Nat.ltb 1 (sp st)) eqn:E1.
      * apply Nat.ltb_lt in E1.
        assert (Hsp1 : 1 <= sp (apop st)) by (unfold apop; cbn [sp]; lia).
        assert (HWF1 : stkWF (apop st)) by (apply stkWF_apop; exact HWF).
        rewrite (absv_cons (apop st) Hsp1 HWF1). cbn [popN].
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
        rewrite Hnil. cbn [popN]. rewrite <- Hnil.
        split; [reflexivity| apply stkWF_apop; exact HWF].
    + apply Nat.ltb_ge in E0. assert (sp st = 0) by lia.
      assert (Hnil : absv st = []) by (apply (absv_nil_iff st); [exact HWF| lia]).
      rewrite Hnil. cbn [popN]. rewrite <- Hnil.
      split; [reflexivity| exact HWF].
Qed.

(* ------------------------------------------------------------------ *)
(* The imperative step, mirroring stepN.                               *)
(* ------------------------------------------------------------------ *)
Definition stNI := (arr * astack * nat * nat * nat)%type.

Definition stepNI (cur : nat) (st : stNI) : stNI :=
  let '(a, s, ec, lc, pp) := st in
  let ec := S ec in
  if Nat.ltb 0 (sp s) then
    let top := atop s in
    if Nat.ltb cur top
    then (setL a top cur, apush cur s, ec, lc, pp)
    else
      let pp := S pp in
      let ec := S ec in
      if Nat.ltb 0 (sp (apop s)) then
        let top2 := atop (apop s) in
        if Nat.leb top2 cur
        then let lc := S lc in
             let '(prev, s2, k) := popMI (sp (apop s)) cur (apop s) in
             (setR a prev cur, apush cur s2, ec + k, lc, pp + k)
        else (setR a top cur, apush cur (apop s), ec, lc, pp)
      else (setR a top cur, apush cur (apop s), ec, lc, pp)
  else (a, s, ec, lc, pp).

Fixpoint runNI_aux (xs : list nat) (st : stNI) : stNI :=
  match xs with [] => st | c :: r => runNI_aux r (stepNI c st) end.

Definition runNI0 (ip : list nat) : stNI :=
  match ip with
  | [] => (empty, emptystk, 0, 0, 0)
  | x0 :: rest => runNI_aux rest (empty, apush x0 (apush (length ip) emptystk), 0, 0, 0)
  end.

Definition absN (st : stNI) : stN :=
  let '(a, s, ec, lc, pp) := st in (a, absv s, ec, lc, pp).
Definition stNWF (st : stNI) : Prop :=
  let '(a, s, ec, lc, pp) := st in stkWF s.

(* ------------------------------------------------------------------ *)
(* Refinement of one step.                                             *)
(* ------------------------------------------------------------------ *)
Lemma stepNI_stepN : forall cur st,
  stNWF st -> absN (stepNI cur st) = stepN cur (absN st) /\ stNWF (stepNI cur st).
Proof.
  intros cur st HWF. destruct st as [[[[a s] ec] lc] pp].
  unfold stNWF in HWF. unfold stepNI, stepN, absN.
  destruct (Nat.ltb 0 (sp s)) eqn:E0.
  - apply Nat.ltb_lt in E0.
    rewrite (absv_cons s E0 HWF). cbn match. rewrite <- (absv_cons s E0 HWF).
    rewrite (atop_absv s E0 HWF) in *.
    destruct (Nat.ltb cur (hd 0 (absv s))) eqn:Elt.
    + (* left child / push *)
      split.
      * rewrite absv_apush by exact HWF. reflexivity.
      * cbn [stNWF]. apply stkWF_apush; exact HWF.
    + (* right child *)
      assert (HWF1 : stkWF (apop s)) by (apply stkWF_apop; exact HWF).
      destruct (Nat.ltb 0 (sp (apop s))) eqn:E1.
      * apply Nat.ltb_lt in E1.
        rewrite (absv_cons (apop s) E1 HWF1). cbn match.
        rewrite <- (absv_cons (apop s) E1 HWF1).
        rewrite (atop_absv (apop s) E1 HWF1) in *.
        destruct (Nat.leb (hd 0 (absv (apop s))) cur) eqn:Ele.
        -- (* double pop *)
           pose proof (popMI_popN (sp (apop s)) cur (apop s) HWF1) as HP.
           assert (Hlen : length (absv (apop s)) = sp (apop s))
             by (apply length_absv; exact HWF1).
           rewrite Hlen.
           destruct (popMI (sp (apop s)) cur (apop s)) as [[prev s2] k].
           destruct HP as [HPe HPw]. rewrite HPe.
           split.
           ++ rewrite absv_apush by exact HPw. reflexivity.
           ++ cbn [stNWF]. apply stkWF_apush; exact HPw.
        -- (* single pop, top2 > cur *)
           split.
           ++ rewrite absv_apush by exact HWF1. reflexivity.
           ++ cbn [stNWF]. apply stkWF_apush; exact HWF1.
      * apply Nat.ltb_ge in E1. assert (sp (apop s) = 0) by lia.
        assert (Hnil : absv (apop s) = []) by
          (apply (absv_nil_iff (apop s)); [exact HWF1| lia]).
        rewrite Hnil. cbn match. rewrite <- Hnil.
        split.
        -- rewrite absv_apush by exact HWF1. reflexivity.
        -- cbn [stNWF]. apply stkWF_apush; exact HWF1.
  - apply Nat.ltb_ge in E0. assert (sp s = 0) by lia.
    assert (Hnil : absv s = []) by (apply (absv_nil_iff s); [exact HWF| lia]).
    rewrite Hnil. cbn match. rewrite <- Hnil.
    split; [reflexivity| exact HWF].
Qed.

(* ------------------------------------------------------------------ *)
(* Refinement of the loop and the whole run.                           *)
(* ------------------------------------------------------------------ *)
Lemma runNI_runN_aux : forall xs st,
  stNWF st -> absN (runNI_aux xs st) = runN_aux xs (absN st) /\ stNWF (runNI_aux xs st).
Proof.
  induction xs as [|cur rest IH]; intros st HWF.
  - split; [reflexivity| exact HWF].
  - cbn [runNI_aux runN_aux].
    pose proof (stepNI_stepN cur st HWF) as [He Hw].
    specialize (IH (stepNI cur st) Hw). rewrite He in IH. exact IH.
Qed.

Theorem runNI0_eq : forall ip, absN (runNI0 ip) = runN0 ip.
Proof.
  intro ip. unfold runNI0, runN0. destruct ip as [|x0 rest]; [reflexivity|].
  assert (HWF0 : stkWF emptystk) by (unfold stkWF, emptystk; simpl; lia).
  assert (HWFs : stkWF (apush x0 (apush (length (x0 :: rest)) emptystk)))
    by (apply stkWF_apush, stkWF_apush; exact HWF0).
  assert (Habs : absv (apush x0 (apush (length (x0 :: rest)) emptystk))
                 = [x0; length (x0 :: rest)]).
  { rewrite absv_apush by (apply stkWF_apush; exact HWF0).
    rewrite absv_apush by exact HWF0. unfold absv, emptystk; reflexivity. }
  pose proof (runNI_runN_aux rest
                (empty, apush x0 (apush (length (x0 :: rest)) emptystk), 0, 0, 0)
                HWFs) as [He _].
  unfold absN in He. rewrite Habs in He. exact He.
Qed.

Print Assumptions runNI0_eq.

Example runNI_tree7 : absN (runNI0 (ip tree7)) = runN0 (ip tree7).
Proof. apply runNI0_eq. Qed.
