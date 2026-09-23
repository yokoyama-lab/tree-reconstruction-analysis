(* ImpHoare.v
   A small imperative language with a mutable array memory, its operational
   semantics, and a sound Hoare logic -- the program-logic layer for reasoning
   about the in-place array stack at the level of memory cells (loads/stores and
   a stack pointer), without leaving Rocq 9.1 / the standard library.

   This models the C data layout of the algorithms (the node array and the label
   stack live in one address space `heap : nat -> nat`, with a scalar stack
   pointer in the store).  We prove the Hoare rules sound against the big-step
   semantics -- in particular the while rule -- and verify, purely by the logic,
   a stack episode that exhibits the in-place REUSE the paper flags: pushing,
   popping, then pushing again overwrites the freed cell while the cell below is
   untouched.

   Rocq Prover 9.1.  Standard library only.  Axiom-free. *)

From Stdlib Require Import Arith Lia Bool.

(* ------------------------------------------------------------------ *)
(* State: a scalar store and an array heap, both nat -> nat.           *)
(* ------------------------------------------------------------------ *)
Definition store := nat -> nat.
Definition heap  := nat -> nat.
Definition state : Type := (store * heap)%type.

Definition sget (s : state) (x : nat) : nat := fst s x.
Definition hget (s : state) (a : nat) : nat := snd s a.
Definition supd (s : state) (x v : nat) : state :=
  (fun y => if Nat.eqb y x then v else fst s y, snd s).
Definition hupd (s : state) (a v : nat) : state :=
  (fst s, fun b => if Nat.eqb b a then v else snd s b).

(* ------------------------------------------------------------------ *)
(* Syntax.                                                              *)
(* ------------------------------------------------------------------ *)
Inductive aexp : Type :=
| ANum   (n : nat)
| AVar   (x : nat)
| ALoad  (a : aexp)              (* heap[a] : a pointer dereference *)
| APlus  (a b : aexp)
| AMinus (a b : aexp).

Inductive bexp : Type :=
| BTrue | BFalse
| BLe (a b : aexp)
| BLt (a b : aexp)
| BEq (a b : aexp)
| BNot (p : bexp)
| BAnd (p q : bexp).

Inductive com : Type :=
| CSkip
| CAssign (x : nat) (e : aexp)     (* x := e            (scalar) *)
| CStore  (a e : aexp)             (* heap[a] := e      (array write) *)
| CSeq    (c1 c2 : com)
| CIf     (b : bexp) (c1 c2 : com)
| CWhile  (b : bexp) (c : com).

Fixpoint aeval (s : state) (e : aexp) : nat :=
  match e with
  | ANum n     => n
  | AVar x     => sget s x
  | ALoad a    => hget s (aeval s a)
  | APlus a b  => aeval s a + aeval s b
  | AMinus a b => aeval s a - aeval s b
  end.

Fixpoint beval (s : state) (b : bexp) : bool :=
  match b with
  | BTrue    => true
  | BFalse   => false
  | BLe a b  => Nat.leb (aeval s a) (aeval s b)
  | BLt a b  => Nat.ltb (aeval s a) (aeval s b)
  | BEq a b  => Nat.eqb (aeval s a) (aeval s b)
  | BNot p   => negb (beval s p)
  | BAnd p q => beval s p && beval s q
  end.

(* ------------------------------------------------------------------ *)
(* Big-step operational semantics.                                     *)
(* ------------------------------------------------------------------ *)
Inductive ceval : com -> state -> state -> Prop :=
| E_Skip   : forall s, ceval CSkip s s
| E_Assign : forall s x e, ceval (CAssign x e) s (supd s x (aeval s e))
| E_Store  : forall s a e, ceval (CStore a e) s (hupd s (aeval s a) (aeval s e))
| E_Seq    : forall c1 c2 s s' s'',
    ceval c1 s s' -> ceval c2 s' s'' -> ceval (CSeq c1 c2) s s''
| E_IfTrue : forall b c1 c2 s s',
    beval s b = true  -> ceval c1 s s' -> ceval (CIf b c1 c2) s s'
| E_IfFalse: forall b c1 c2 s s',
    beval s b = false -> ceval c2 s s' -> ceval (CIf b c1 c2) s s'
| E_WhileFalse : forall b c s,
    beval s b = false -> ceval (CWhile b c) s s
| E_WhileTrue  : forall b c s s' s'',
    beval s b = true -> ceval c s s' -> ceval (CWhile b c) s' s'' ->
    ceval (CWhile b c) s s''.

(* ------------------------------------------------------------------ *)
(* Hoare triples and the proof rules (sound by construction).          *)
(* ------------------------------------------------------------------ *)
Definition assertion := state -> Prop.
Definition hoare (P : assertion) (c : com) (Q : assertion) : Prop :=
  forall s s', ceval c s s' -> P s -> Q s'.
Definition implies (P Q : assertion) : Prop := forall s, P s -> Q s.

Lemma hoare_skip : forall P, hoare P CSkip P.
Proof. intros P s s' Hev HP. inversion Hev; subst. exact HP. Qed.

(* Backward assignment rule. *)
Lemma hoare_assign : forall Q x e,
  hoare (fun s => Q (supd s x (aeval s e))) (CAssign x e) Q.
Proof. intros Q x e s s' Hev HP. inversion Hev; subst. exact HP. Qed.

(* Backward store rule (the array-write analogue). *)
Lemma hoare_store : forall Q a e,
  hoare (fun s => Q (hupd s (aeval s a) (aeval s e))) (CStore a e) Q.
Proof. intros Q a e s s' Hev HP. inversion Hev; subst. exact HP. Qed.

Lemma hoare_seq : forall P R Q c1 c2,
  hoare P c1 R -> hoare R c2 Q -> hoare P (CSeq c1 c2) Q.
Proof.
  intros P R Q c1 c2 H1 H2 s s' Hev HP. inversion Hev; subst.
  apply (H2 s'0 s'); [assumption|]. apply (H1 s s'0); assumption.
Qed.

Lemma hoare_if : forall P Q b c1 c2,
  hoare (fun s => P s /\ beval s b = true)  c1 Q ->
  hoare (fun s => P s /\ beval s b = false) c2 Q ->
  hoare P (CIf b c1 c2) Q.
Proof.
  intros P Q b c1 c2 H1 H2 s s' Hev HP. inversion Hev; subst.
  - apply (H1 s s'); [assumption | split; assumption].
  - apply (H2 s s'); [assumption | split; assumption].
Qed.

Lemma hoare_consequence : forall (P P' Q Q' : assertion) c,
  implies P P' -> hoare P' c Q' -> implies Q' Q -> hoare P c Q.
Proof.
  intros P P' Q Q' c HPP H HQQ s s' Hev HP.
  apply HQQ. apply (H s s'); [assumption | apply HPP; assumption].
Qed.

(* The while rule: I is preserved by the body while the guard holds. *)
Lemma hoare_while : forall I b c,
  hoare (fun s => I s /\ beval s b = true) c I ->
  hoare I (CWhile b c) (fun s => I s /\ beval s b = false).
Proof.
  intros I b c Hbody s s' Hev.
  remember (CWhile b c) as cw eqn:Hcw.
  induction Hev; intros HI; inversion Hcw; subst.
  - split; assumption.
  - apply IHHev2; [reflexivity|].
    apply (Hbody s s'); [assumption | split; assumption].
Qed.

(* ------------------------------------------------------------------ *)
(* The array stack at the memory level, and the in-place reuse.        *)
(*   SP is a scalar stack pointer; the buffer is heap[0..SP-1].         *)
(* ------------------------------------------------------------------ *)
Definition SP : nat := 0.
Definition push (v : nat) : com :=
  CSeq (CStore (AVar SP) (ANum v))                 (* heap[SP] := v *)
       (CAssign SP (APlus (AVar SP) (ANum 1))).    (* SP := SP + 1 *)
Definition pop : com :=
  CAssign SP (AMinus (AVar SP) (ANum 1)).          (* SP := SP - 1 *)

(* One push: it advances SP and writes the cell it found at SP. *)
Theorem push_spec : forall k v,
  hoare (fun s => sget s SP = k)
        (push v)
        (fun s => sget s SP = S k /\ hget s k = v).
Proof.
  intros k v. unfold push.
  eapply hoare_seq with (R := fun s => sget s SP = k /\ hget s k = v).
  - (* the store:  {SP = k}  heap[SP] := v  {SP = k /\ heap[k] = v} *)
    eapply hoare_consequence;
      [ | apply (hoare_store (fun s => sget s SP = k /\ hget s k = v))
        | intros s H; exact H ].
    intros s HP. cbv [sget hget supd hupd SP aeval] in *; cbn in *.
    rewrite HP, Nat.eqb_refl. split; reflexivity.
  - (* the increment:  {SP = k /\ heap[k] = v}  SP := SP+1  {SP = S k /\ heap[k] = v} *)
    eapply hoare_consequence;
      [ | apply (hoare_assign
            (fun s => sget s SP = S k /\ hget s k = v) SP (APlus (AVar SP) (ANum 1)))
        | intros s H; exact H ].
    intros s [HP Hh]. cbv [sget hget supd hupd SP aeval] in *; cbn in *.
    rewrite HP, Nat.add_1_r. split; [reflexivity| exact Hh].
Qed.

(* The in-place reuse: push 7, push 8, pop, push 9.  The cell that held 8 is
   overwritten by 9; the cell below (7) is untouched; SP ends at 2.  Proved
   straight from the semantics (straight-line code). *)
Definition stack_episode : com :=
  CSeq (push 7) (CSeq (push 8) (CSeq pop (push 9))).

Theorem stack_episode_reuse :
  hoare (fun s => sget s SP = 0)
        stack_episode
        (fun s => sget s SP = 2 /\ hget s 0 = 7 /\ hget s 1 = 9).
Proof.
  intros s s' Hev HP.
  unfold stack_episode, push, pop in Hev.
  (* peel the eight straight-line steps *)
  repeat match goal with
  | [ H : ceval (CSeq _ _) _ _ |- _ ]    => inversion H; subst; clear H
  | [ H : ceval (CStore _ _) _ _ |- _ ]  => inversion H; subst; clear H
  | [ H : ceval (CAssign _ _) _ _ |- _ ] => inversion H; subst; clear H
  end.
  cbv [sget hget supd hupd SP aeval] in *; cbn in *.
  rewrite HP. cbn. repeat split; reflexivity.
Qed.

Print Assumptions hoare_while.
Print Assumptions stack_episode_reuse.

(* The semantics actually runs the episode (sanity check). *)
Example run_episode_exists :
  exists s', ceval stack_episode (fun _ => 0, fun _ => 0) s'.
Proof.
  eexists. unfold stack_episode, push, pop. repeat econstructor.
Qed.

(* ------------------------------------------------------------------ *)
(* A verified LOOP: summing an array region, exercising the while rule  *)
(* (proved sound above) on a real program with a heap read in the body. *)
(*   IDX := 0; ACC := 0; while IDX < N { ACC += heap[IDX]; IDX += 1 }    *)
(* ------------------------------------------------------------------ *)
Fixpoint hsum (h : heap) (n : nat) : nat :=
  match n with O => 0 | S k => hsum h k + h k end.

Definition IDX  : nat := 1.
Definition ACCv : nat := 2.

Definition sumbody : com :=
  CSeq (CAssign ACCv (APlus (AVar ACCv) (ALoad (AVar IDX))))   (* ACC += heap[IDX] *)
       (CAssign IDX  (APlus (AVar IDX)  (ANum 1))).            (* IDX += 1 *)

Definition sumprog (N : nat) : com :=
  CSeq (CAssign IDX  (ANum 0))
       (CSeq (CAssign ACCv (ANum 0))
             (CWhile (BLt (AVar IDX) (ANum N)) sumbody)).

(* The loop invariant is preserved by one iteration. *)
Lemma sumbody_pres : forall N,
  hoare (fun s => (sget s IDX <= N /\ sget s ACCv = hsum (snd s) (sget s IDX))
                  /\ beval s (BLt (AVar IDX) (ANum N)) = true)
        sumbody
        (fun s => sget s IDX <= N /\ sget s ACCv = hsum (snd s) (sget s IDX)).
Proof.
  intro N. unfold sumbody.
  eapply hoare_seq with
    (R := fun s => sget s IDX < N /\ sget s ACCv = hsum (snd s) (S (sget s IDX))).
  - eapply hoare_consequence;
      [ | apply (hoare_assign _ ACCv (APlus (AVar ACCv) (ALoad (AVar IDX))))
        | intros s H; exact H ].
    intros s [[Hle Hacc] Hg].
    cbv [sget hget supd IDX ACCv aeval beval] in *; cbn in *.
    apply Nat.ltb_lt in Hg. split; [exact Hg|].
    rewrite Hacc. cbn. reflexivity.
  - eapply hoare_consequence;
      [ | apply (hoare_assign _ IDX (APlus (AVar IDX) (ANum 1)))
        | intros s H; exact H ].
    intros s [Hlt Hacc].
    cbv [sget hget supd IDX ACCv aeval] in *; cbn in *.
    rewrite Nat.add_1_r. split; [lia | exact Hacc].
Qed.

Theorem sum_spec : forall N,
  hoare (fun _ => True) (sumprog N) (fun s => sget s ACCv = hsum (snd s) N).
Proof.
  intro N. unfold sumprog.
  eapply hoare_seq with (R := fun s => sget s IDX = 0).
  - eapply hoare_consequence;
      [ | apply (hoare_assign (fun s => sget s IDX = 0) IDX (ANum 0))
        | intros s H; exact H ].
    intros s _. cbv [sget supd IDX aeval]; cbn. reflexivity.
  - eapply hoare_seq with
      (R := fun s => sget s IDX <= N /\ sget s ACCv = hsum (snd s) (sget s IDX)).
    + eapply hoare_consequence;
        [ | apply (hoare_assign _ ACCv (ANum 0))
          | intros s H; exact H ].
      intros s HI. cbv [sget hget supd IDX ACCv aeval] in *; cbn in *.
      rewrite HI. cbn. split; [lia | reflexivity].
    + eapply hoare_consequence;
        [ intros s H; exact H
        | apply hoare_while, sumbody_pres
        | ].
      intros s [[Hle Hacc] Hg].
      cbv [sget ACCv IDX aeval beval] in *; cbn in *.
      apply Nat.ltb_ge in Hg.
      assert (E : fst s 1 = N) by lia.
      rewrite Hacc, E. reflexivity.
Qed.

Print Assumptions sum_spec.

(* sum_spec says the loop computes hsum of the heap; check hsum concretely. *)
Example hsum_three :
  hsum (fun i => match i with 0 => 3 | 1 => 1 | 2 => 4 | _ => 0 end) 3 = 8.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Locality / framing: the separation building blocks.                  *)
(*  - a store touches only its target cell;                             *)
(*  - a store-free program leaves the heap entirely unchanged.          *)
(* These let one reason that the stack region and the output-array      *)
(* region do not interfere -- the heart of the in-place aliasing story. *)
(* ------------------------------------------------------------------ *)
Lemma hget_hupd_same : forall s a v, hget (hupd s a v) a = v.
Proof. intros s a v. unfold hget, hupd; cbn. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma hget_hupd_other : forall s a b v, a <> b -> hget (hupd s a v) b = hget s b.
Proof.
  intros s a b v H. unfold hget, hupd; cbn.
  destruct (Nat.eqb_spec b a); [subst; contradiction | reflexivity].
Qed.

(* A command with no array writes. *)
Fixpoint no_store (c : com) : Prop :=
  match c with
  | CSkip       => True
  | CAssign _ _ => True
  | CStore _ _  => False
  | CSeq c1 c2  => no_store c1 /\ no_store c2
  | CIf _ c1 c2 => no_store c1 /\ no_store c2
  | CWhile _ c1 => no_store c1
  end.

(* Frame: a store-free program preserves the whole heap. *)
Lemma frame_heap : forall c s s', no_store c -> ceval c s s' -> snd s' = snd s.
Proof.
  intros c s s' Hns Hev. revert Hns.
  induction Hev; intros Hns; simpl in Hns; try reflexivity; try contradiction.
  - destruct Hns as [H1 H2]. rewrite (IHHev2 H2), (IHHev1 H1); reflexivity.
  - exact (IHHev (proj1 Hns)).
  - exact (IHHev (proj2 Hns)).
  - rewrite (IHHev2 Hns), (IHHev1 Hns); reflexivity.
Qed.

Print Assumptions frame_heap.

(* End-to-end: on a concrete heap the loop really lands ACC = 8.  The frame
   lemma supplies snd s' = h (the loop is store-free), then sum_spec closes it. *)
Example sum_three :
  forall s',
    ceval (sumprog 3)
          (fun _ => 0, fun i => match i with 0 => 3 | 1 => 1 | 2 => 4 | _ => 0 end) s' ->
    sget s' ACCv = 8.
Proof.
  intros s' Hev.
  assert (Hns : no_store (sumprog 3)) by (repeat split).
  pose proof (frame_heap (sumprog 3) _ s' Hns Hev) as Hh.
  pose proof (sum_spec 3 _ s' Hev I) as Hs. cbv beta in Hs.
  rewrite Hs, Hh. reflexivity.
Qed.
