(* ReconstructExec.v
   An executable interpreter for the deep-embedded imperative language, and the
   genuine CWhile reconstructor run through it.

   The big-step semantics `ceval` of ImpHoare is a relation, not a function, so
   it cannot be run.  Here we give a fuel-driven *functional* interpreter
   `ceval_fun : nat -> com -> state -> option state` and prove it SOUND w.r.t.
   `ceval`: whatever it returns is a genuine big-step evaluation
   (`ceval_fun_sound`).  Composing with `iRun_builds_tree_init` (ReconstructWhile)
   yields the executable headline `exec_builds_tree`: from the explicit initial
   heap configuration, *running* the CWhile program with enough fuel produces
   exactly the tree's `setTree` parent-pointer array.  A concrete `Compute`
   exercises it end-to-end on the left spine ip = [2;1;0].

   Rocq Prover 9.1.0, standard library only, axiom-free. *)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Trees.
Require Import Dictionary.
Require Import Reconstruct.
Require Import ReconstructRight.       (* setTree *)
Require Import ReconstructFull.
Require Import ImpHoare.
Require Import ReconstructHeap.       (* enc, PREV, CUR *)
Require Import ReconstructStack.       (* stk_abs *)
Require Import ReconstructStackCom.    (* DEPTH *)
Require Import ReconstructStep.        (* JI, TOP *)
Require Import ReconstructFrame.       (* arr_ok_n *)
Require Import ReconstructWhile.       (* iRun, INbase, IDX/PREV/DEPTH, iRun_builds_tree_init *)

(* ------------------------------------------------------------------ *)
(* A fuel-driven functional interpreter for `com`.                      *)
(* `None` means "ran out of fuel" (the loop did not finish in `fuel`     *)
(* steps); any `Some s'` is a genuine terminating big-step run.          *)
(* ------------------------------------------------------------------ *)
Fixpoint ceval_fun (fuel : nat) (c : com) (s : state) : option state :=
  match fuel with
  | O => None
  | S fuel' =>
      match c with
      | CSkip        => Some s
      | CAssign x e  => Some (supd s x (aeval s e))
      | CStore a e   => Some (hupd s (aeval s a) (aeval s e))
      | CSeq c1 c2   =>
          match ceval_fun fuel' c1 s with
          | Some s1 => ceval_fun fuel' c2 s1
          | None    => None
          end
      | CIf b c1 c2  =>
          if beval s b then ceval_fun fuel' c1 s else ceval_fun fuel' c2 s
      | CWhile b c1  =>
          if beval s b
          then match ceval_fun fuel' c1 s with
               | Some s1 => ceval_fun fuel' (CWhile b c1) s1
               | None    => None
               end
          else Some s
      end
  end.

(* Soundness: anything the interpreter computes is a real big-step run. *)
Theorem ceval_fun_sound : forall fuel c s s',
  ceval_fun fuel c s = Some s' -> ceval c s s'.
Proof.
  induction fuel as [|fuel IH]; intros c s s' H; simpl in H; [discriminate|].
  destruct c.
  - injection H as H; subst s'; constructor.
  - injection H as H; subst s'; constructor.
  - injection H as H; subst s'; constructor.
  - (* CSeq *)
    destruct (ceval_fun fuel c1 s) as [s1|] eqn:E1; [|discriminate].
    eapply E_Seq; [apply IH; exact E1 | apply IH; exact H].
  - (* CIf *)
    destruct (beval s b) eqn:Eb.
    + apply E_IfTrue;  [exact Eb | apply IH; exact H].
    + apply E_IfFalse; [exact Eb | apply IH; exact H].
  - (* CWhile *)
    destruct (beval s b) eqn:Eb.
    + destruct (ceval_fun fuel c s) as [s1|] eqn:E1; [|discriminate].
      eapply E_WhileTrue; [exact Eb | apply IH; exact E1 | apply IH; exact H].
    + injection H as H; subst s'; apply E_WhileFalse; exact Eb.
Qed.

Print Assumptions ceval_fun_sound.

(* ------------------------------------------------------------------ *)
(* Executable headline: RUNNING the CWhile program (with enough fuel)   *)
(* from the explicit initial configuration builds the tree's setTree.   *)
(* ------------------------------------------------------------------ *)
Corollary exec_builds_tree : forall t x0 rest fuel s s',
  ip t = x0 :: rest ->
  sget s IDX = 0 -> sget s PREV = x0 -> sget s DEPTH = 1 ->
  arr_ok_n (S (size t)) empty (snd s) ->
  stk_abs (S (size t) + S (size t)) 1 (snd s) = [x0] ->
  inp_ok (INbase (S (size t))) rest (snd s) ->
  ceval_fun fuel (iRun (S (size t)) (length rest)) s = Some s' ->
  arr_ok_n (S (size t)) (setTree 0 t empty) (snd s').
Proof.
  intros t x0 rest fuel s s' Hip Hidx Hprev Hdep Harr Hstk Hinp Hexec.
  apply (iRun_builds_tree_init t x0 rest Hip s s').
  - eapply ceval_fun_sound; exact Hexec.
  - split; [exact Hidx | split; [exact Hprev | split; [exact Hdep |
      split; [exact Harr | split; [exact Hstk | exact Hinp]]]]].
Qed.

Print Assumptions exec_builds_tree.

(* ------------------------------------------------------------------ *)
(* Concrete end-to-end run.  Left spine of three internal nodes:        *)
(*   t = Node (Node (Node Leaf Leaf) Leaf) Leaf,  ip t = [2;1;0],        *)
(* N = 4.  Initial config: IDX=0, PREV=2, DEPTH=1, output array zeroed,  *)
(* stack cell 8 = 2, input [1;0] at 12,13.  We *run* the program and     *)
(* read off the eight output cells -- they match the functional model.   *)
(* ------------------------------------------------------------------ *)
Definition store0 : store := fun r => if r =? 0 then 2 else if r =? 2 then 1 else 0.
Definition heap0  : heap  := fun a => if a =? 8 then 2 else if a =? 12 then 1 else 0.
Definition s0     : state := (store0, heap0).

(* 200 units of fuel suffice: the run terminates and lands the eight output
   cells of the left spine (node 2 -> 1 -> 0). *)
Example exec_left_spine_run :
  option_map (fun s => map (snd s) (seq 0 8)) (ceval_fun 200 (iRun 4 2) s0)
  = Some [0; 0; 1; 0; 2; 0; 0; 0].
Proof. reflexivity. Qed.

(* Those eight cells are exactly the functional model run [2;1;0], cell by
   cell (heap[k+k] = enc left-child of k, heap[S(k+k)] = enc right-child). *)
Example exec_matches_model :
  option_map (fun s => map (snd s) (seq 0 8)) (ceval_fun 200 (iRun 4 2) s0)
  = Some (flat_map (fun k => [enc (fst (run [2;1;0] k)); enc (snd (run [2;1;0] k))])
                   (seq 0 4)).
Proof. reflexivity. Qed.

(* And the run does satisfy the verified post-condition for that tree:
   arr_ok_n 4 (setTree 0 t empty), discharged through exec_builds_tree. *)
Example exec_left_spine_correct : forall s',
  ceval_fun 200 (iRun 4 2) s0 = Some s' ->
  arr_ok_n 4 (setTree 0 (Node (Node (Node Leaf Leaf) Leaf) Leaf) empty) (snd s').
Proof.
  intros s' Hexec.
  apply (exec_builds_tree (Node (Node (Node Leaf Leaf) Leaf) Leaf) 2 [1;0] 200 s0 s'
           eq_refl); try reflexivity; [ | | exact Hexec].
  - (* output array zeroed below 8 *)
    intros k Hk. destruct k as [|[|[|[|k]]]]; cbn; try (split; reflexivity).
    exfalso; cbn in Hk; lia.
  - (* input region holds [1;0] *)
    intros j Hj. destruct j as [|[|j]]; cbn; try reflexivity.
    exfalso; cbn [length] in Hj; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* A self-contained, extractable driver.  From an i-p code and the node *)
(* count N it lays out the initial configuration, RUNS the CWhile        *)
(* program, and (read_arr) reads back the 2N output cells.               *)
(* ------------------------------------------------------------------ *)
Definition init_store (x0 : nat) : store :=
  fun r => if r =? PREV then x0 else if r =? DEPTH then 1 else 0.

Definition init_heap (N x0 : nat) (rest : list nat) : heap :=
  fun a => if a =? N + N then x0                                     (* stack base = [x0] *)
           else if (INbase N <=? a) && (a <? INbase N + length rest) (* input region *)
                then nth (a - INbase N) rest 0
                else 0.                                              (* output array zeroed *)

Definition init_state (N x0 : nat) (rest : list nat) : state :=
  (init_store x0, init_heap N x0 rest).

Definition reconstruct_exec (fuel N : nat) (ipc : list nat) : option state :=
  match ipc with
  | []         => None
  | x0 :: rest => ceval_fun fuel (iRun N (length rest)) (init_state N x0 rest)
  end.

(* Read the 2N output cells: [l_0; r_0; l_1; r_1; ...], encoded by enc. *)
Definition read_arr (N : nat) (s : state) : list nat := map (snd s) (seq 0 (N + N)).

(* The laid-out initial configuration meets iRun's precondition. *)
Lemma init_state_pre : forall t x0 rest,
  ip t = x0 :: rest ->
  sget (init_state (S (size t)) x0 rest) IDX = 0
  /\ sget (init_state (S (size t)) x0 rest) PREV = x0
  /\ sget (init_state (S (size t)) x0 rest) DEPTH = 1
  /\ arr_ok_n (S (size t)) empty (snd (init_state (S (size t)) x0 rest))
  /\ stk_abs (S (size t) + S (size t)) 1 (snd (init_state (S (size t)) x0 rest)) = [x0]
  /\ inp_ok (INbase (S (size t))) rest (snd (init_state (S (size t)) x0 rest)).
Proof.
  intros t x0 rest _. set (N := S (size t)).
  assert (HN : 0 < N) by (unfold N; lia).
  unfold init_state, sget, snd, fst.
  split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [|split]]]].
  - (* arr_ok_n: every output cell below 2N is zero = enc None *)
    intros k Hk. unfold empty, enc; cbn [fst snd]. unfold init_heap.
    rewrite (proj2 (Nat.eqb_neq (k + k) (N + N))) by lia.
    rewrite (proj2 (Nat.eqb_neq (S (k + k)) (N + N))) by lia.
    assert (HL : (INbase N <=? k + k) = false)
      by (apply Nat.leb_gt; unfold INbase; lia).
    assert (HR : (INbase N <=? S (k + k)) = false)
      by (apply Nat.leb_gt; unfold INbase; lia).
    rewrite HL, HR; cbn [andb]. split; reflexivity.
  - (* stack base holds [x0] *)
    unfold stk_abs; cbn [seq map rev app]. rewrite Nat.add_0_r.
    unfold init_heap. rewrite Nat.eqb_refl. reflexivity.
  - (* input region holds rest *)
    intros i Hi. unfold init_heap.
    rewrite (proj2 (Nat.eqb_neq (INbase N + i) (N + N))) by (unfold INbase; lia).
    assert (HL : (INbase N <=? INbase N + i) = true) by (apply Nat.leb_le; lia).
    assert (HR : (INbase N + i <? INbase N + length rest) = true)
      by (apply Nat.ltb_lt; lia).
    rewrite HL, HR; cbn [andb].
    rewrite Nat.add_comm, Nat.add_sub. reflexivity.
Qed.

(* Driver correctness: for *every* tree, running the CWhile program on its
   i-p code (with enough fuel to terminate) lands its setTree parent array. *)
Theorem reconstruct_exec_correct : forall t fuel s',
  reconstruct_exec fuel (S (size t)) (ip t) = Some s' ->
  arr_ok_n (S (size t)) (setTree 0 t empty) (snd s').
Proof.
  intros t fuel s' H. unfold reconstruct_exec in H.
  destruct (ip t) as [|x0 rest] eqn:Hip; [discriminate|].
  destruct (init_state_pre t x0 rest Hip)
    as (Hidx & Hprev & Hdep & Harr & Hstk & Hinp).
  exact (exec_builds_tree t x0 rest fuel (init_state (S (size t)) x0 rest) s'
           Hip Hidx Hprev Hdep Harr Hstk Hinp H).
Qed.

Print Assumptions reconstruct_exec_correct.

(* The driver, run concretely on the left spine, reads back the model array. *)
Example reconstruct_exec_left_spine :
  option_map (read_arr 4) (reconstruct_exec 200 4 [2; 1; 0]) = Some [0; 0; 1; 0; 2; 0; 0; 0].
Proof. reflexivity. Qed.
