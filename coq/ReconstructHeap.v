(* ReconstructHeap.v
   The construction's output array at the level of memory cells, verified with
   the program logic of ImpHoare.v.

   The functional model (Reconstruct.v) keeps the reconstructed parent-child
   relation in an array  a : nat -> cell,  cell = (option nat * option nat).  We
   lay it out in the heap (heap : nat -> nat) as two cells per node: node k's
   LEFT link at address k+k and its RIGHT link at S (k+k), with options offset-
   encoded (None as 0, Some v as S v).  The grafting operations setL / setR are
   then single array writes; we encode them as `com` (CStore) and prove the
   Hoare triples

       {arr_ok a} iSetL {arr_ok (setL a prev cur)}
       {arr_ok a} iSetR {arr_ok (setR a prev cur)}

   i.e. the imperative writes refine the functional grafting, with the framing
   that a write to one link leaves every other cell (and the stack region)
   untouched discharged by the disjointness of the addresses.  Axiom-free.

   This is the heap-level building block for an imperative encoding of the whole
   construction loop (the stack push/pop episodes are already verified at the
   cell level in ImpHoare.v).

   Rocq Prover 9.1.  Standard library only.  Axiom-free. *)

From Stdlib Require Import Arith Lia.
Require Import Reconstruct.
Require Import ImpHoare.

(* Offset encoding of an option link. *)
Definition enc (o : option nat) : nat :=
  match o with None => 0 | Some v => S v end.

(* The heap faithfully represents the array a. *)
Definition arr_ok (a : arr) (h : heap) : Prop :=
  forall k, h (k + k) = enc (fst (a k)) /\ h (S (k + k)) = enc (snd (a k)).

(* A pure heap update (the second component of hupd). *)
Definition hset (h : heap) (addr v : nat) : heap :=
  fun x => if Nat.eqb x addr then v else h x.

(* ------------------------------------------------------------------ *)
(* Writing the left / right link preserves the representation of the    *)
(* grafted array -- the disjointness of the addresses does the framing. *)
(* ------------------------------------------------------------------ *)
Lemma arr_ok_setL : forall a h prev cur,
  arr_ok a h -> arr_ok (setL a prev cur) (hset h (prev + prev) (S cur)).
Proof.
  intros a h prev cur Ha k. unfold setL, hset.
  destruct (Ha k) as [HL HR]. split.
  - (* left link of k *)
    destruct (Nat.eqb_spec (k + k) (prev + prev)) as [E|E].
    + assert (k = prev) by lia. subst k. rewrite Nat.eqb_refl. reflexivity.
    + assert (k <> prev) by lia.
      rewrite (proj2 (Nat.eqb_neq k prev)) by assumption. exact HL.
  - (* right link of k is never the written (even) address S (prev+prev) is... *)
    rewrite (proj2 (Nat.eqb_neq (S (k + k)) (prev + prev))) by lia.
    destruct (Nat.eqb_spec k prev) as [E|E]; [subst k|]; exact HR.
Qed.

Lemma arr_ok_setR : forall a h prev cur,
  arr_ok a h -> arr_ok (setR a prev cur) (hset h (S (prev + prev)) (S cur)).
Proof.
  intros a h prev cur Ha k. unfold setR, hset.
  destruct (Ha k) as [HL HR]. split.
  - (* left link of k is at the even address k+k, never S(prev+prev) (odd) *)
    rewrite (proj2 (Nat.eqb_neq (k + k) (S (prev + prev)))) by lia.
    destruct (Nat.eqb_spec k prev) as [E|E]; [subst k|]; exact HL.
  - (* right link of k *)
    destruct (Nat.eqb_spec (S (k + k)) (S (prev + prev))) as [E|E].
    + assert (k = prev) by lia. subst k. rewrite Nat.eqb_refl. reflexivity.
    + assert (k <> prev) by lia.
      rewrite (proj2 (Nat.eqb_neq k prev)) by assumption. exact HR.
Qed.

(* ------------------------------------------------------------------ *)
(* The imperative graft programs and their Hoare triples.              *)
(*   scalar PREV, CUR hold the predecessor and current labels.         *)
(* ------------------------------------------------------------------ *)
Definition PREV : nat := 0.
Definition CUR  : nat := 1.

Definition iSetL : com :=                            (* heap[PREV+PREV] := CUR+1 *)
  CStore (APlus (AVar PREV) (AVar PREV)) (APlus (AVar CUR) (ANum 1)).
Definition iSetR : com :=                            (* heap[S(PREV+PREV)] := CUR+1 *)
  CStore (APlus (APlus (AVar PREV) (AVar PREV)) (ANum 1)) (APlus (AVar CUR) (ANum 1)).

Lemma iSetL_spec : forall a prev cur,
  hoare (fun s => arr_ok a (snd s) /\ sget s PREV = prev /\ sget s CUR = cur)
        iSetL
        (fun s => arr_ok (setL a prev cur) (snd s)).
Proof.
  intros a prev cur. unfold iSetL.
  eapply hoare_consequence;
    [ | apply (hoare_store (fun s => arr_ok (setL a prev cur) (snd s)))
      | intros s H; exact H ].
  intros s [Ha [Hp Hc]].
  (* the store puts heap[prev+prev] := S cur; match arr_ok_setL *)
  cbv [hupd snd aeval].
  rewrite Hp, Hc, !Nat.add_1_r.
  apply (arr_ok_setL a (snd s) prev cur Ha).
Qed.

Lemma iSetR_spec : forall a prev cur,
  hoare (fun s => arr_ok a (snd s) /\ sget s PREV = prev /\ sget s CUR = cur)
        iSetR
        (fun s => arr_ok (setR a prev cur) (snd s)).
Proof.
  intros a prev cur. unfold iSetR.
  eapply hoare_consequence;
    [ | apply (hoare_store (fun s => arr_ok (setR a prev cur) (snd s)))
      | intros s H; exact H ].
  intros s [Ha [Hp Hc]].
  cbv [hupd snd aeval].
  rewrite Hp, Hc, !Nat.add_1_r.
  apply (arr_ok_setR a (snd s) prev cur Ha).
Qed.

Print Assumptions iSetL_spec.
Print Assumptions iSetR_spec.

(* ------------------------------------------------------------------ *)
(* The dual: reading a link.  The construction's push-test inspects      *)
(* a[cur+1].left, so we need a heap READ refining the array, and the     *)
(* boolean ``is this link empty (TERM)?'' that decides the push.         *)
(* ------------------------------------------------------------------ *)
Definition iGetL (e : aexp) : aexp := ALoad (APlus e e).                 (* heap[node+node] *)
Definition iGetR (e : aexp) : aexp := ALoad (APlus (APlus e e) (ANum 1)). (* heap[S(node+node)] *)

Lemma iGetL_ok : forall a s e,
  arr_ok a (snd s) -> aeval s (iGetL e) = enc (fst (a (aeval s e))).
Proof.
  intros a s e Ha. unfold iGetL; cbn [aeval]; unfold hget.
  destruct (Ha (aeval s e)) as [HL _]. rewrite <- HL. f_equal; lia.
Qed.

Lemma iGetR_ok : forall a s e,
  arr_ok a (snd s) -> aeval s (iGetR e) = enc (snd (a (aeval s e))).
Proof.
  intros a s e Ha. unfold iGetR; cbn [aeval]; unfold hget.
  destruct (Ha (aeval s e)) as [_ HR]. rewrite <- HR. f_equal; lia.
Qed.

(* The push-test predicate: node e's left link is empty (None / TERM). *)
Definition isLeafL (e : aexp) : bexp := BEq (iGetL e) (ANum 0).

Lemma isLeafL_ok : forall a s e,
  arr_ok a (snd s) ->
  beval s (isLeafL e)
  = match fst (a (aeval s e)) with None => true | Some _ => false end.
Proof.
  intros a s e Ha. unfold isLeafL; cbn [beval]. rewrite (iGetL_ok a s e Ha).
  destruct (fst (a (aeval s e))) as [v|]; reflexivity.
Qed.

Print Assumptions iGetL_ok.

(* ------------------------------------------------------------------ *)
(* Sanity: the empty array is represented by the all-zero heap; reading  *)
(* back a freshly grafted link returns it; the empty test fires on TERM. *)
(* ------------------------------------------------------------------ *)
Example arr_ok_empty : arr_ok empty (fun _ => 0).
Proof. intro k. split; reflexivity. Qed.

Example enc_roundtrip : enc (Some 4) = 5 /\ enc None = 0.
Proof. split; reflexivity. Qed.

(* After grafting cur as prev's left child, reading prev's left link gives cur. *)
Example read_after_setL : forall a h prev cur,
  arr_ok a h ->
  hset h (prev + prev) (S cur) (prev + prev) = enc (Some cur).
Proof.
  intros a h prev cur _. unfold hset. rewrite Nat.eqb_refl. reflexivity.
Qed.
