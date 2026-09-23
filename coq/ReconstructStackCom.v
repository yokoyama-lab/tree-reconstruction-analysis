(* ReconstructStackCom.v
   The label stack as program-logic operations: push / pop / top realised as
   `com` (resp. `aexp`) of ImpHoare.v over the separate stack region of
   ReconstructStack.v, with Hoare triples proving they refine cons / tl / hd of
   the abstract top-first list stack.

   ReconstructStack.v established, at the pure-heap level, that the region
   [base, base+sp) abstracts to a top-first list stk_abs and that a write at
   base+sp (resp. a shrink) refines cons (resp. tl).  This module lifts those
   facts through the program logic: a scalar register DEPTH holds the live cell
   count sp, and

       pushB base e   = heap[base+DEPTH] := e ; DEPTH := DEPTH+1
       popB           = DEPTH := DEPTH-1
       topB base      = heap[base + (DEPTH-1)]          (an aexp)

   are proved, by the Hoare rules, to refine cons / tl / hd:

       {DEPTH=sp /\ e=v /\ stk_abs=L}  pushB  {DEPTH=S sp /\ stk_abs = v::L}
       {DEPTH=S sp /\ stk_abs=L}       popB   {DEPTH=sp   /\ stk_abs = tl L}
        DEPTH=S k  ->  topB = hd (stk_abs)

   DEPTH (= 2) is disjoint from the graft registers PREV (= 0) / CUR (= 1) of
   ReconstructHeap.v, so the two refinements compose at integration.  Axiom-free.

   Rocq Prover 9.1.  Standard library only.  Axiom-free. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import ImpHoare.
Require Import ReconstructHeap. (* hset *)
Require Import ReconstructStack.

(* The scalar register holding the live cell count (stack depth). *)
Definition DEPTH : nat := 2.

(* snd of a heap update is exactly the pure heap update hset. *)
Lemma snd_hupd : forall s a v, snd (hupd s a v) = hset (snd s) a v.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The stack operations as program-logic terms.                        *)
(* ------------------------------------------------------------------ *)
Definition pushB (base : nat) (e : aexp) : com :=
  CSeq (CStore (APlus (ANum base) (AVar DEPTH)) e)        (* heap[base+DEPTH] := e *)
       (CAssign DEPTH (APlus (AVar DEPTH) (ANum 1))).     (* DEPTH := DEPTH+1 *)

Definition popB : com :=
  CAssign DEPTH (AMinus (AVar DEPTH) (ANum 1)).           (* DEPTH := DEPTH-1 *)

Definition topB (base : nat) : aexp :=                    (* heap[base + (DEPTH-1)] *)
  ALoad (APlus (ANum base) (AMinus (AVar DEPTH) (ANum 1))).

(* ------------------------------------------------------------------ *)
(* push refines cons: it grows DEPTH and the abstraction by the value.  *)
(* ------------------------------------------------------------------ *)
Lemma pushB_spec : forall base e sp v L,
  hoare (fun s => sget s DEPTH = sp /\ aeval s e = v /\ stk_abs base sp (snd s) = L)
        (pushB base e)
        (fun s => sget s DEPTH = S sp /\ stk_abs base (S sp) (snd s) = v :: L).
Proof.
  intros base e sp v L. unfold pushB.
  eapply hoare_seq with
    (R := fun s => sget s DEPTH = sp /\ stk_abs base (S sp) (snd s) = v :: L).
  - (* the store writes the new top cell base+sp := v *)
    eapply hoare_consequence;
      [ | apply (hoare_store
            (fun s => sget s DEPTH = sp /\ stk_abs base (S sp) (snd s) = v :: L))
        | intros s H; exact H ].
    intros s [Hsp [Hv HL]]. rewrite Hv. cbn [aeval].
    rewrite Hsp, snd_hupd. split.
    + (* the store leaves the store component (hence DEPTH) untouched *)
      cbv [sget hupd]; cbn. exact Hsp.
    + (* the new region abstracts to v :: L by stk_abs_push *)
      rewrite stk_abs_push, HL. reflexivity.
  - (* the increment advances DEPTH; the heap (hence stk_abs) is untouched *)
    eapply hoare_consequence;
      [ | apply (hoare_assign
            (fun s => sget s DEPTH = S sp /\ stk_abs base (S sp) (snd s) = v :: L)
            DEPTH (APlus (AVar DEPTH) (ANum 1)))
        | intros s H; exact H ].
    intros s [Hsp HL]. cbv [aeval]. rewrite Hsp. split.
    + cbv [sget supd]; cbn. rewrite Nat.add_1_r. reflexivity.
    + (* supd changes only the store; snd s is preserved *)
      cbv [supd snd] in *. exact HL.
Qed.

(* ------------------------------------------------------------------ *)
(* pop refines tl: it shrinks DEPTH; the abstraction drops the top.     *)
(* ------------------------------------------------------------------ *)
Lemma popB_spec : forall base sp L,
  hoare (fun s => sget s DEPTH = S sp /\ stk_abs base (S sp) (snd s) = L)
        popB
        (fun s => sget s DEPTH = sp /\ stk_abs base sp (snd s) = tl L).
Proof.
  intros base sp L. unfold popB.
  eapply hoare_consequence;
    [ | apply (hoare_assign
          (fun s => sget s DEPTH = sp /\ stk_abs base sp (snd s) = tl L)
          DEPTH (AMinus (AVar DEPTH) (ANum 1)))
      | intros s H; exact H ].
  intros s [Hsp HL]. cbv [aeval]. rewrite Hsp. split.
  + cbv [sget supd]; cbn. lia.
  + (* supd leaves snd s; the top drops by stk_abs_pop *)
    cbv [supd snd] in *. rewrite <- HL. exact (stk_abs_pop base (S sp) (snd s)).
Qed.

(* ------------------------------------------------------------------ *)
(* top refines hd: reading base + (DEPTH-1) returns the head of stk_abs. *)
(* ------------------------------------------------------------------ *)
Lemma topB_ok : forall base k s,
  sget s DEPTH = S k ->
  aeval s (topB base) = hd 0 (stk_abs base (S k) (snd s)).
Proof.
  intros base k s Hsp. unfold topB; cbn [aeval]. rewrite Hsp.
  cbv [hget]. rewrite stk_top. f_equal. lia.
Qed.

Print Assumptions pushB_spec.
Print Assumptions popB_spec.
Print Assumptions topB_ok.

(* ------------------------------------------------------------------ *)
(* Sanity: starting from the empty region, push 7 then push 8 leaves     *)
(* DEPTH = 2 and the top-first stack [8; 7]; popping returns to [7].      *)
(* ------------------------------------------------------------------ *)
Example pushB_cons_concrete :
  hoare (fun s => sget s DEPTH = 0 /\ aeval s (ANum 7) = 7
                  /\ stk_abs 10 0 (snd s) = [])
        (pushB 10 (ANum 7))
        (fun s => sget s DEPTH = 1 /\ stk_abs 10 1 (snd s) = [7]).
Proof. apply (pushB_spec 10 (ANum 7) 0 7 []). Qed.

Example popB_tl_concrete :
  hoare (fun s => sget s DEPTH = 2 /\ stk_abs 10 2 (snd s) = [8; 7])
        popB
        (fun s => sget s DEPTH = 1 /\ stk_abs 10 1 (snd s) = [7]).
Proof. apply (popB_spec 10 1 [8; 7]). Qed.

(* DEPTH is disjoint from the graft registers, so the views compose. *)
Example depth_disjoint_from_graft : DEPTH <> PREV /\ DEPTH <> CUR.
Proof. unfold DEPTH, PREV, CUR. split; discriminate. Qed.
