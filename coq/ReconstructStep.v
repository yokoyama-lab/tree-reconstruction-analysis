(* ReconstructStep.v
   One construction iteration as an imperative program, refining the functional
   `step` of Reconstruct.v under a joint invariant over the shared heap.

   The functional model represents a configuration as a pair (array, list-stack)
   and `step prev cur` first grafts the new node -- as a left child of prev if
   cur < prev, else as the right child of the popped stack top -- and then, by a
   push-test on the (cur+1) link, conditionally pushes cur.  This module realises
   that iteration over the heap layout of ReconstructHeap.v / ReconstructStack.v
   (the output array below address 2N, the label stack in [2N, ..)), tying the
   two together with the joint invariant

       JI N a st s  :=  arr_ok_n N a (heap s)            (the array, nodes < N)
                     /\ stk_abs (N+N) (length st) (heap s) = st   (the stack)
                     /\ DEPTH = length st  /\  Forall (< N) st.

   This first part verifies the GRAFT half -- the branch that either writes the
   left link of prev or pops the stack top and writes its right link -- as a
   Hoare triple refining the functional graft.  The region-separation lemmas of
   ReconstructFrame.v discharge the non-interference (an array write preserves
   the stack view; a stack pop preserves the array).  Axiom-free.

   Rocq Prover 9.1.  Standard library only.  Axiom-free. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import Reconstruct.
Require Import ImpHoare.
Require Import ReconstructHeap.   (* enc, arr_ok, hset, PREV, CUR, iSetL *)
Require Import ReconstructStack.   (* stk_abs, stk_abs_pop, stk_top *)
Require Import ReconstructStackCom. (* DEPTH, popB, topB, topB_ok, snd_hupd *)
Require Import ReconstructFrame.   (* arr_ok_n, arr_ok_n_frame, stk_abs_frame *)

(* A scalar register holding the popped stack top, for the right graft.
   Disjoint from PREV (=0), CUR (=1), DEPTH (=2). *)
Definition TOP : nat := 3.

(* ------------------------------------------------------------------ *)
(* Bounded versions of the graft array-correctness lemmas: setL / setR  *)
(* preserve the array correspondence restricted to nodes < N (the form   *)
(* the joint invariant carries, since the stack occupies the cells >=2N). *)
(* ------------------------------------------------------------------ *)
Lemma arr_ok_n_setL : forall N a h prev cur,
  arr_ok_n N a h ->
  arr_ok_n N (setL a prev cur) (hset h (prev + prev) (S cur)).
Proof.
  intros N a h prev cur Ha k Hk. unfold setL, hset.
  destruct (Ha k Hk) as [HL HR]. split.
  - destruct (Nat.eqb_spec (k + k) (prev + prev)) as [E|E].
    + assert (k = prev) by lia. subst k. rewrite Nat.eqb_refl. reflexivity.
    + assert (k <> prev) by lia.
      rewrite (proj2 (Nat.eqb_neq k prev)) by assumption. exact HL.
  - rewrite (proj2 (Nat.eqb_neq (S (k + k)) (prev + prev))) by lia.
    destruct (Nat.eqb_spec k prev) as [E|E]; [subst k|]; exact HR.
Qed.

Lemma arr_ok_n_setR : forall N a h prev cur,
  arr_ok_n N a h ->
  arr_ok_n N (setR a prev cur) (hset h (S (prev + prev)) (S cur)).
Proof.
  intros N a h prev cur Ha k Hk. unfold setR, hset.
  destruct (Ha k Hk) as [HL HR]. split.
  - rewrite (proj2 (Nat.eqb_neq (k + k) (S (prev + prev)))) by lia.
    destruct (Nat.eqb_spec k prev) as [E|E]; [subst k|]; exact HL.
  - destruct (Nat.eqb_spec (S (k + k)) (S (prev + prev))) as [E|E].
    + assert (k = prev) by lia. subst k. rewrite Nat.eqb_refl. reflexivity.
    + assert (k <> prev) by lia.
      rewrite (proj2 (Nat.eqb_neq k prev)) by assumption. exact HR.
Qed.

(* ------------------------------------------------------------------ *)
(* The joint invariant and the functional graft (the inner let of step). *)
(* ------------------------------------------------------------------ *)
Definition JI (N : nat) (a : arr) (st : list nat) (s : state) : Prop :=
     arr_ok_n N a (snd s)
  /\ stk_abs (N + N) (length st) (snd s) = st
  /\ sget s DEPTH = length st
  /\ Forall (fun x => x < N) st.

Definition graft (prev cur : nat) (a : arr) (st : list nat) : arr * list nat :=
  if Nat.ltb cur prev
  then (setL a prev cur, st)
  else match st with
       | top :: st' => (setR a top cur, st')
       | []         => (a, st)
       end.

(* The imperative graft: scalar PREV, CUR, DEPTH, TOP over the shared heap. *)
Definition iSetR_top : com :=                  (* heap[S(TOP+TOP)] := CUR+1 *)
  CStore (APlus (APlus (AVar TOP) (AVar TOP)) (ANum 1)) (APlus (AVar CUR) (ANum 1)).

Definition iGraft (base : nat) : com :=
  CIf (BLt (AVar CUR) (AVar PREV))
      iSetL                                            (* left child of PREV *)
      (CSeq (CAssign TOP (topB base))                  (* TOP := stack top *)
            (CSeq popB iSetR_top)).                    (* pop; right child of TOP *)

(* ------------------------------------------------------------------ *)
(* The graft half refines the functional graft, preserving the joint    *)
(* invariant and the loop registers PREV / CUR.  In the right branch the *)
(* stack must be nonempty (supplied by the construction's stack          *)
(* invariant at integration); prev, cur, and the stack labels are < N.   *)
(* ------------------------------------------------------------------ *)
Lemma iGraft_spec : forall N prev cur a st,
  prev < N -> cur < N ->
  (Nat.ltb cur prev = false -> st <> []) ->
  hoare (fun s => JI N a st s /\ sget s PREV = prev /\ sget s CUR = cur)
        (iGraft (N + N))
        (fun s => JI N (fst (graft prev cur a st)) (snd (graft prev cur a st)) s
                  /\ sget s PREV = prev /\ sget s CUR = cur).
Proof.
  intros N prev cur a st Hprev Hcur Hne. unfold iGraft.
  destruct (Nat.ltb cur prev) eqn:Hlt.
  - (* cur < prev: left graft; the else branch is unreachable *)
    unfold graft. rewrite Hlt. cbn [fst snd].
    apply hoare_if.
    + (* iSetL refines setL *)
      unfold iSetL.
      eapply hoare_consequence;
        [ | apply (hoare_store
              (fun s => JI N (setL a prev cur) st s
                        /\ sget s PREV = prev /\ sget s CUR = cur))
          | intros s H; exact H ].
      intros s [[[Harr [Hstk [Hdep Hall]]] [HP HC]] _].
      cbn [aeval]. rewrite HP, HC, !Nat.add_1_r.
      unfold JI. rewrite !snd_hupd.
      split;
        [ split;
            [ apply arr_ok_n_setL; exact Harr
            | split;
                [ rewrite stk_abs_frame by lia; exact Hstk
                | split; [ exact Hdep | exact Hall ] ] ]
        | split; [ exact HP | exact HC ] ].
    + (* unreachable: beval false contradicts cur < prev *)
      intros s s' Hev [[_ [HP HC]] Hbf].
      cbn [beval aeval] in Hbf. rewrite HC, HP, Hlt in Hbf. discriminate.
  - (* cur >= prev: pop the top, graft right child *)
    destruct st as [|topv st']; [exfalso; apply (Hne eq_refl); reflexivity|].
    unfold graft. rewrite Hlt. cbn [fst snd].
    apply hoare_if.
    + (* unreachable: beval true contradicts cur >= prev *)
      intros s s' Hev [[_ [HP HC]] Hbt].
      cbn [beval aeval] in Hbt. rewrite HC, HP, Hlt in Hbt. discriminate.
    + (* TOP := stack top ; pop ; right link of TOP *)
      eapply hoare_seq with
        (R := fun s => arr_ok_n N a (snd s)
                    /\ stk_abs (N + N) (S (length st')) (snd s) = topv :: st'
                    /\ sget s DEPTH = S (length st')
                    /\ topv < N /\ Forall (fun x => x < N) st'
                    /\ sget s PREV = prev /\ sget s CUR = cur
                    /\ sget s TOP = topv).
      * (* CAssign TOP (topB) : read the top into register TOP *)
        eapply hoare_consequence;
          [ | apply (hoare_assign _ TOP (topB (N + N))) | intros s H; exact H ].
        intros s [[[Harr [Hstk [Hdep Hall]]] [HP HC]] _].
        cbn [length] in Hstk, Hdep.
        rewrite (topB_ok (N + N) (length st') s Hdep), Hstk. cbn [hd].
        pose proof (Forall_inv Hall) as Htopv.
        pose proof (Forall_inv_tail Hall) as Hall'.
        split; [ exact Harr
        | split; [ exact Hstk
        | split; [ exact Hdep
        | split; [ exact Htopv
        | split; [ exact Hall'
        | split; [ exact HP
        | split; [ exact HC
        | reflexivity ] ] ] ] ] ] ].
      * (* pop ; right link of TOP *)
        eapply hoare_seq with
          (R := fun s => arr_ok_n N a (snd s)
                      /\ stk_abs (N + N) (length st') (snd s) = st'
                      /\ sget s DEPTH = length st'
                      /\ topv < N /\ Forall (fun x => x < N) st'
                      /\ sget s PREV = prev /\ sget s CUR = cur
                      /\ sget s TOP = topv).
        { (* popB : DEPTH := DEPTH - 1 *)
          unfold popB.
          eapply hoare_consequence;
            [ | apply (hoare_assign _ DEPTH (AMinus (AVar DEPTH) (ANum 1)))
              | intros s H; exact H ].
          intros s [Harr [Hstk [Hdep [Htopv [Hall' [HP [HC HT]]]]]]].
          assert (Hpop : stk_abs (N + N) (length st') (snd s) = st').
          { replace (length st') with (pred (S (length st'))) by (cbn [pred]; reflexivity).
            rewrite stk_abs_pop, Hstk. reflexivity. }
          assert (Hval : aeval s (AMinus (AVar DEPTH) (ANum 1)) = length st')
            by (cbn [aeval]; rewrite Hdep; lia).
          rewrite Hval.
          split; [ exact Harr
          | split; [ exact Hpop
          | split; [ reflexivity
          | split; [ exact Htopv
          | split; [ exact Hall'
          | split; [ exact HP
          | split; [ exact HC
          | exact HT ] ] ] ] ] ] ]. }
        { (* iSetR_top : heap[S(TOP+TOP)] := CUR+1 *)
          unfold iSetR_top.
          eapply hoare_consequence;
            [ | apply (hoare_store
                  (fun s => JI N (setR a topv cur) st' s
                            /\ sget s PREV = prev /\ sget s CUR = cur))
              | intros s H; exact H ].
          intros s [Harr [Hstk [Hdep [Htopv [Hall' [HP [HC HT]]]]]]].
          cbn [aeval]. rewrite HT, HC, !Nat.add_1_r.
          unfold JI. rewrite !snd_hupd.
          split;
            [ split;
                [ apply arr_ok_n_setR; exact Harr
                | split;
                    [ rewrite stk_abs_frame by lia; exact Hstk
                    | split; [ exact Hdep | exact Hall' ] ] ]
            | split; [ exact HP | exact HC ] ]. }
Qed.

Print Assumptions iGraft_spec.

(* ================================================================== *)
(* The push-test half, and the full step.                              *)
(* ================================================================== *)

(* Bounded link reads: the heap read at a live node (< N) returns the    *)
(* array link, and the leaf-test reflects whether that link is empty.    *)
Lemma iGetL_n_ok : forall N a s e,
  arr_ok_n N a (snd s) -> aeval s e < N ->
  aeval s (iGetL e) = enc (fst (a (aeval s e))).
Proof.
  intros N a s e Ha Hlt. unfold iGetL; cbn [aeval]; unfold hget.
  destruct (Ha (aeval s e) Hlt) as [HL _]. rewrite <- HL. f_equal; lia.
Qed.

Lemma isLeafL_n_ok : forall N a s e,
  arr_ok_n N a (snd s) -> aeval s e < N ->
  beval s (isLeafL e)
  = match fst (a (aeval s e)) with None => true | Some _ => false end.
Proof.
  intros N a s e Ha Hlt. unfold isLeafL; cbn [beval].
  rewrite (iGetL_n_ok N a s e Ha Hlt).
  destruct (fst (a (aeval s e))) as [v|]; reflexivity.
Qed.

(* The full functional step, factored through graft, and its agreement   *)
(* with Reconstruct.step (definitionally the same expression).           *)
Definition stepF (prev cur : nat) (a : arr) (st : list nat) : arr * list nat :=
  let (a1, s1) := graft prev cur a st in
  match fst (a1 (cur + 1)) with
  | None   => (a1, cur :: s1)
  | Some _ => (a1, s1)
  end.

Lemma step_fst : forall prev cur a st,
  fst (step prev cur (a, st)) = fst (graft prev cur a st).
Proof.
  intros. change (step prev cur (a, st)) with (stepF prev cur a st).
  unfold stepF. destruct (graft prev cur a st) as [a1 s1]. cbn [fst snd].
  destruct (fst (a1 (cur + 1))); reflexivity.
Qed.

Lemma step_snd : forall prev cur a st,
  snd (step prev cur (a, st))
  = match fst (fst (graft prev cur a st) (cur + 1)) with
    | None   => cur :: snd (graft prev cur a st)
    | Some _ => snd (graft prev cur a st)
    end.
Proof.
  intros. change (step prev cur (a, st)) with (stepF prev cur a st).
  unfold stepF. destruct (graft prev cur a st) as [a1 s1]. cbn [fst snd].
  destruct (fst (a1 (cur + 1))); reflexivity.
Qed.

(* The imperative push-test and the whole iteration. *)
Definition iPushTest (base : nat) : com :=
  CIf (isLeafL (APlus (AVar CUR) (ANum 1)))
      (pushB base (AVar CUR))                         (* push CUR *)
      CSkip.

Definition iStep (base : nat) : com :=
  CSeq (iGraft base) (iPushTest base).

(* ------------------------------------------------------------------ *)
(* A push of CUR over the joint invariant: it grows the stack region    *)
(* (a write at base+DEPTH >= 2N, framed away from the array) and the     *)
(* abstraction by cur, preserving everything else.                       *)
(* ------------------------------------------------------------------ *)
Lemma pushB_frame_spec : forall N prev cur a1 s1,
  cur < N ->
  hoare (fun s => arr_ok_n N a1 (snd s)
               /\ stk_abs (N + N) (length s1) (snd s) = s1
               /\ sget s DEPTH = length s1
               /\ Forall (fun x => x < N) s1
               /\ sget s PREV = prev /\ sget s CUR = cur)
        (pushB (N + N) (AVar CUR))
        (fun s => arr_ok_n N a1 (snd s)
               /\ stk_abs (N + N) (S (length s1)) (snd s) = cur :: s1
               /\ sget s DEPTH = S (length s1)
               /\ Forall (fun x => x < N) (cur :: s1)
               /\ sget s PREV = prev /\ sget s CUR = cur).
Proof.
  intros N prev cur a1 s1 Hcur. unfold pushB.
  eapply hoare_seq with
    (R := fun s => arr_ok_n N a1 (snd s)
                /\ stk_abs (N + N) (S (length s1)) (snd s) = cur :: s1
                /\ sget s DEPTH = length s1
                /\ Forall (fun x => x < N) (cur :: s1)
                /\ sget s PREV = prev /\ sget s CUR = cur).
  - (* CStore : heap[(N+N)+DEPTH] := CUR *)
    eapply hoare_consequence;
      [ | apply (hoare_store _) | intros s H; exact H ].
    intros s [Harr [Hstk [Hdep [Hall [HP HC]]]]].
    cbn [aeval]. rewrite Hdep, HC, snd_hupd.
    split; [ apply arr_ok_n_frame; [ lia | exact Harr ]
    | split; [ rewrite stk_abs_push, Hstk; reflexivity
    | split; [ exact Hdep
    | split; [ apply Forall_cons; [ exact Hcur | exact Hall ]
    | split; [ exact HP | exact HC ] ] ] ] ].
  - (* CAssign DEPTH := DEPTH + 1 *)
    eapply hoare_consequence;
      [ | apply (hoare_assign _ DEPTH (APlus (AVar DEPTH) (ANum 1)))
        | intros s H; exact H ].
    intros s [Harr [Hstk [Hdep [Hall' [HP HC]]]]].
    cbn [aeval]. rewrite Hdep, Nat.add_1_r.
    split; [ exact Harr
    | split; [ exact Hstk
    | split; [ reflexivity
    | split; [ exact Hall'
    | split; [ exact HP | exact HC ] ] ] ] ].
Qed.

(* ------------------------------------------------------------------ *)
(* The push-test refines the second half of step: it pushes cur iff the *)
(* (cur+1) link is empty, leaving the array (a1) untouched.              *)
(* ------------------------------------------------------------------ *)
Lemma iPushTest_spec : forall N prev cur a1 s1,
  cur < N -> S cur < N ->
  hoare (fun s => JI N a1 s1 s /\ sget s PREV = prev /\ sget s CUR = cur)
        (iPushTest (N + N))
        (fun s => JI N a1 (match fst (a1 (cur + 1)) with
                           | None => cur :: s1 | Some _ => s1 end) s
                  /\ sget s PREV = prev /\ sget s CUR = cur).
Proof.
  intros N prev cur a1 s1 Hcur HScur. unfold iPushTest.
  destruct (fst (a1 (cur + 1))) as [v|] eqn:Hleaf.
  - (* Some v: not a leaf, do not push *)
    apply hoare_if.
    + (* unreachable: guard would be false *)
      intros s s' Hev [[[Harr [Hstk [Hdep Hall]]] [HP HC]] Hbt].
      assert (Hbnd : aeval s (APlus (AVar CUR) (ANum 1)) < N)
        by (cbn [aeval]; rewrite HC; lia).
      rewrite (isLeafL_n_ok N a1 s (APlus (AVar CUR) (ANum 1)) Harr Hbnd) in Hbt.
      cbn [aeval] in Hbt. rewrite HC, Hleaf in Hbt. discriminate.
    + (* CSkip *)
      intros s s' Hev Hpre. inversion Hev; subst s'.
      destruct Hpre as [[HJI [HP HC]] _].
      split; [ exact HJI | split; [ exact HP | exact HC ] ].
  - (* None: leaf, push cur *)
    apply hoare_if.
    + (* pushB CUR *)
      eapply hoare_consequence;
        [ intros s [[HJI [HP HC]] _];
          destruct HJI as [Harr [Hstk [Hdep Hall]]];
          exact (conj Harr (conj Hstk (conj Hdep (conj Hall (conj HP HC)))))
        | apply (pushB_frame_spec N prev cur a1 s1 Hcur)
        | intros s [Harr [Hstk [Hdep [Hall' [HP HC]]]]];
          unfold JI;
          split; [ split; [ exact Harr
                          | split; [ exact Hstk
                          | split; [ exact Hdep | exact Hall' ] ] ]
                 | split; [ exact HP | exact HC ] ] ].
    + (* unreachable: guard would be true *)
      intros s s' Hev [[[Harr [Hstk [Hdep Hall]]] [HP HC]] Hbf].
      assert (Hbnd : aeval s (APlus (AVar CUR) (ANum 1)) < N)
        by (cbn [aeval]; rewrite HC; lia).
      rewrite (isLeafL_n_ok N a1 s (APlus (AVar CUR) (ANum 1)) Harr Hbnd) in Hbf.
      cbn [aeval] in Hbf. rewrite HC, Hleaf in Hbf. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* The whole iteration refines Reconstruct.step under the joint          *)
(* invariant: graft, then push-test.                                     *)
(* ------------------------------------------------------------------ *)
Lemma iStep_spec : forall N prev cur a st,
  prev < N -> cur < N -> S cur < N ->
  (Nat.ltb cur prev = false -> st <> []) ->
  hoare (fun s => JI N a st s /\ sget s PREV = prev /\ sget s CUR = cur)
        (iStep (N + N))
        (fun s => JI N (fst (step prev cur (a, st))) (snd (step prev cur (a, st))) s
                  /\ sget s PREV = prev /\ sget s CUR = cur).
Proof.
  intros N prev cur a st Hprev Hcur HScur Hne. unfold iStep.
  eapply hoare_seq with
    (R := fun s => JI N (fst (graft prev cur a st)) (snd (graft prev cur a st)) s
                /\ sget s PREV = prev /\ sget s CUR = cur).
  - apply iGraft_spec; assumption.
  - eapply hoare_consequence;
      [ intros s H; exact H
      | apply (iPushTest_spec N prev cur
                 (fst (graft prev cur a st)) (snd (graft prev cur a st)) Hcur HScur)
      | intros s Hpost; rewrite step_fst, step_snd; exact Hpost ].
Qed.

Print Assumptions iStep_spec.

(* ------------------------------------------------------------------ *)
(* Sanity: the bounded graft lemmas on a concrete empty heap, and the    *)
(* register-disjointness that makes the joint invariant compose.         *)
(* ------------------------------------------------------------------ *)
Example arr_ok_n_setL_concrete :
  arr_ok_n 3 (setL empty 1 2) (hset (fun _ => 0) (1 + 1) (S 2)).
Proof. apply arr_ok_n_setL. apply arr_ok_to_n. intro k. split; reflexivity. Qed.

Example top_register_disjoint :
  TOP <> PREV /\ TOP <> CUR /\ TOP <> DEPTH.
Proof. unfold TOP, PREV, CUR, DEPTH. repeat split; discriminate. Qed.
