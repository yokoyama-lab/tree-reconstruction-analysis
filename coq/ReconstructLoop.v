(* ReconstructLoop.v
   The whole construction loop as a sequence of imperative iterations, proved to
   refine the functional fold run_aux of Reconstruct.v under the joint heap
   invariant.

   run_aux threads a predecessor prev through the input list, folding step:

       run_aux prev (cur :: rest) cfg = run_aux cur rest (step prev cur cfg)

   so the predecessor of the next node is the current node.  We realise this as a
   straight-line program iSteps that, for each cur, loads CUR, runs the verified
   iteration iStep (ReconstructStep.v), then sets PREV := cur for the next round:

       iSteps base (cur :: rest)
         = CUR := cur ; iStep base ; PREV := cur ; iSteps base rest

   The refinement is proved by induction on the input list, applying iStep_spec
   at each step.  Its per-iteration preconditions (the labels are < N, and the
   stack is nonempty when a right child is grafted) are collected in a single
   well-formedness predicate RunOK over the run; discharging RunOK from the
   construction's own invariants is left to integration.  Axiom-free.

   Rocq Prover 9.1.  Standard library only.  Axiom-free. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import Reconstruct.
Require Import ImpHoare.
Require Import ReconstructHeap.    (* PREV, CUR *)
Require Import ReconstructFrame.    (* arr_ok_n *)
Require Import ReconstructStep.     (* JI, iStep, iStep_spec *)
Require Import Trees.               (* tree, Node, Leaf *)
Require Import Dictionary.          (* ip, ipo, ipo_cons, root_label *)
Require Import ReconstructInvariant. (* pre, out_stk, rpop, rootedge, blank *)
Require Import ReconstructRight.    (* setTree, setL_neq, setTree_oob, run_aux_app, lastd *)
Require Import ReconstructFull.     (* run_eq_setTree, gen, step_graft, step_push, ... *)

(* The straight-line program for the loop over the input list. *)
Fixpoint iSteps (base : nat) (xs : list nat) : com :=
  match xs with
  | []          => CSkip
  | cur :: rest =>
      CSeq (CAssign CUR (ANum cur))
           (CSeq (iStep base)
                 (CSeq (CAssign PREV (ANum cur)) (iSteps base rest)))
  end.

(* Per-iteration well-formedness along the run: every label is < N (with the
   (cur+1) sentinel still < N), and the stack is nonempty whenever a right child
   is grafted -- exactly the preconditions iStep_spec needs at each step. *)
Fixpoint RunOK (N prev : nat) (xs : list nat) (cfg : arr * list nat) : Prop :=
  match xs with
  | []          => True
  | cur :: rest =>
      prev < N /\ cur < N /\ S cur < N
      /\ (Nat.ltb cur prev = false -> snd cfg <> [])
      /\ RunOK N cur rest (step prev cur cfg)
  end.

(* ------------------------------------------------------------------ *)
(* The loop refines run_aux: starting from any joint configuration       *)
(* (a, st) with PREV = prev, the program ends in the configuration       *)
(* computed by the functional fold.                                      *)
(* ------------------------------------------------------------------ *)
Lemma iSteps_spec : forall N xs prev a st,
  RunOK N prev xs (a, st) ->
  hoare (fun s => JI N a st s /\ sget s PREV = prev)
        (iSteps (N + N) xs)
        (fun s => JI N (fst (run_aux prev xs (a, st)))
                       (snd (run_aux prev xs (a, st))) s).
Proof.
  intros N. induction xs as [|cur rest IH]; intros prev a st Hok.
  - (* [] : CSkip leaves the configuration unchanged *)
    cbn [iSteps run_aux].
    intros s s' Hev Hpre. inversion Hev; subst s'.
    destruct Hpre as [HJI _]. cbn [fst snd]. exact HJI.
  - (* cur :: rest *)
    cbn [iSteps run_aux].
    destruct Hok as [Hprev [Hcur [HScur [Hstk_ne Hrest]]]].
    cbn [snd] in Hstk_ne.
    destruct (step prev cur (a, st)) as [a' st'] eqn:Hstep.
    (* CUR := cur ; iStep ; PREV := cur ; iSteps rest *)
    eapply hoare_seq with
      (R := fun s => JI N a st s /\ sget s PREV = prev /\ sget s CUR = cur).
    + (* CUR := cur *)
      eapply hoare_consequence;
        [ | apply (hoare_assign _ CUR (ANum cur)) | intros s H; exact H ].
      intros s [HJI HP].
      split; [ exact HJI | split; [ exact HP | reflexivity ] ].
    + eapply hoare_seq with
        (R := fun s => JI N a' st' s /\ sget s PREV = prev /\ sget s CUR = cur).
      * (* iStep refines step prev cur (a, st) = (a', st') *)
        eapply hoare_consequence;
          [ intros s H; exact H
          | apply (iStep_spec N prev cur a st Hprev Hcur HScur Hstk_ne)
          | intros s [HJI [HP HC]]; rewrite Hstep in HJI; cbn [fst snd] in HJI;
            exact (conj HJI (conj HP HC)) ].
      * eapply hoare_seq with
          (R := fun s => JI N a' st' s /\ sget s PREV = cur).
        { (* PREV := cur *)
          eapply hoare_consequence;
            [ | apply (hoare_assign _ PREV (ANum cur)) | intros s H; exact H ].
          intros s [HJI [HP HC]].
          split; [ exact HJI | reflexivity ]. }
        { (* iSteps rest, by the induction hypothesis *)
          exact (IH cur a' st' Hrest). }
Qed.

Print Assumptions iSteps_spec.

(* ------------------------------------------------------------------ *)
(* Tie to the top level: starting from the initial configuration of the  *)
(* construction (the empty array and the singleton stack [x0]), the loop  *)
(* over the remaining input builds the heap representation of run.        *)
(* ------------------------------------------------------------------ *)
Corollary iSteps_run : forall N x0 rest,
  RunOK N x0 rest (empty, [x0]) ->
  hoare (fun s => JI N empty [x0] s /\ sget s PREV = x0)
        (iSteps (N + N) rest)
        (fun s => arr_ok_n N (run (x0 :: rest)) (snd s)).
Proof.
  intros N x0 rest Hok.
  eapply hoare_consequence;
    [ intros s H; exact H
    | apply (iSteps_spec N rest x0 empty [x0] Hok)
    | intros s HJI; destruct HJI as [Harr _]; unfold run; exact Harr ].
Qed.

Print Assumptions iSteps_run.

(* ================================================================== *)
(* Discharging the label bounds of RunOK.                              *)
(*                                                                      *)
(* RunOK bundles two kinds of per-iteration conditions: arithmetic      *)
(* label bounds (prev, cur, cur+1 all < N) and the genuine stack        *)
(* invariant (the stack is nonempty when a right child is grafted).     *)
(* The bounds are structural -- they hold for any input whose labels    *)
(* are < n, taking N = S n (the +1 sentinel) -- so we peel them off,    *)
(* leaving only the stack condition StackOK, which holds exactly for    *)
(* valid i-p inputs and is the content of the construction's stack      *)
(* invariant.                                                            *)
(* ================================================================== *)

(* The stack-nonemptiness conditions along the run, on their own. *)
Fixpoint StackOK (prev : nat) (xs : list nat) (cfg : arr * list nat) : Prop :=
  match xs with
  | []          => True
  | cur :: rest =>
      (Nat.ltb cur prev = false -> snd cfg <> [])
      /\ StackOK cur rest (step prev cur cfg)
  end.

(* The label bounds discharge unconditionally for in-range inputs (N = S n). *)
Lemma RunOK_of_StackOK : forall n xs prev cfg,
  prev < n -> Forall (fun x => x < n) xs ->
  StackOK prev xs cfg ->
  RunOK (S n) prev xs cfg.
Proof.
  intros n xs. induction xs as [|cur rest IH]; intros prev cfg Hprev Hall Hstk.
  - exact I.
  - cbn [StackOK] in Hstk. destruct Hstk as [Hne Hrest].
    pose proof (Forall_inv Hall : cur < n) as Hcur.
    pose proof (Forall_inv_tail Hall) as Hall'.
    cbn [RunOK].
    split; [ lia
    | split; [ lia
    | split; [ lia
    | split; [ exact Hne
    | apply IH; [ exact Hcur | exact Hall' | exact Hrest ] ] ] ] ].
Qed.

Print Assumptions RunOK_of_StackOK.

(* Top level with the bounds discharged: for an in-range input whose run never
   underflows the stack, the loop builds the heap form of run. *)
Corollary iSteps_run_bounded : forall n x0 rest,
  x0 < n -> Forall (fun x => x < n) rest ->
  StackOK x0 rest (empty, [x0]) ->
  hoare (fun s => JI (S n) empty [x0] s /\ sget s PREV = x0)
        (iSteps (S n + S n) rest)
        (fun s => arr_ok_n (S n) (run (x0 :: rest)) (snd s)).
Proof.
  intros n x0 rest Hx0 Hall Hstk.
  apply iSteps_run. apply RunOK_of_StackOK; assumption.
Qed.

Print Assumptions iSteps_run_bounded.

(* ------------------------------------------------------------------ *)
(* A nontrivial class for which StackOK discharges outright: strictly    *)
(* decreasing inputs (the inorder-preorder code of a left spine).  There  *)
(* every node grafts a left child (cur < prev), so the right-graft        *)
(* premise Nat.ltb cur prev = false is never met and the stack condition  *)
(* holds vacuously -- the stack never underflows.                         *)
(* ------------------------------------------------------------------ *)
Fixpoint Decreasing (prev : nat) (xs : list nat) : Prop :=
  match xs with
  | []          => True
  | cur :: rest => cur < prev /\ Decreasing cur rest
  end.

Lemma StackOK_decreasing : forall xs prev cfg,
  Decreasing prev xs -> StackOK prev xs cfg.
Proof.
  induction xs as [|cur rest IH]; intros prev cfg Hdec.
  - exact I.
  - cbn [Decreasing] in Hdec. destruct Hdec as [Hlt Hrest].
    cbn [StackOK]. split.
    + (* the right-graft premise cur >= prev is false here *)
      intro Hf. pose proof (proj2 (Nat.ltb_lt cur prev) Hlt) as Hltb.
      rewrite Hltb in Hf. discriminate.
    + apply IH; exact Hrest.
Qed.

Print Assumptions StackOK_decreasing.

(* StackOK distributes over list concatenation, mirroring run_aux_app: the run
   threads the last label of the first part as the predecessor of the second.
   This is the compositional core for discharging StackOK over the append-
   structured inorder-preorder code ipo off (Node l r) = _ :: ipo .. ++ ipo .. *)
Lemma StackOK_app : forall xs ys prev cfg,
  StackOK prev xs cfg ->
  StackOK (lastd prev xs) ys (run_aux prev xs cfg) ->
  StackOK prev (xs ++ ys) cfg.
Proof.
  induction xs as [|cur rest IH]; intros ys prev cfg Hxs Hys.
  - cbn [app lastd run_aux] in *. exact Hys.
  - cbn [app]. cbn [StackOK] in Hxs |- *. destruct Hxs as [Hne Hrest].
    split.
    + exact Hne.
    + apply IH.
      * exact Hrest.
      * cbn [lastd run_aux] in Hys. exact Hys.
Qed.

Print Assumptions StackOK_app.

(* ================================================================== *)
(* The general stack invariant: the run on a tree's inorder-preorder    *)
(* code never underflows.  Proved by induction on the tree, mirroring    *)
(* ReconstructFull.gen: the root step's right-graft (root >= P) forces    *)
(* P < off, where the precondition pre supplies a nonempty stack; the     *)
(* subtree blocks compose by StackOK_app, reusing gen to characterise     *)
(* the stack entering the right block.  This is the invariant the         *)
(* existing development validates only by bounded checking.               *)
(* ================================================================== *)
Lemma StackOK_ipo : forall t P off a s,
  pre P off t a s -> StackOK P (ipo off t) (a, s).
Proof.
  induction t as [|l IHl r IHr]; intros P off a s Hpre.
  - cbn [ipo]. exact I.
  - pose proof Hpre as Hpre0.
    destruct Hpre as [Hblank [Hext Hpop]].
    unfold blank in Hblank. cbn [size] in Hext, Hpop, Hblank.
    rewrite ipo_cons.
    pose proof (step_graft P (off + size l) a s) as Hg.
    pose proof (step_push P (off + size l) a s) as Hp.
    destruct (step P (off + size l) (a, s)) as [a1 s2] eqn:Hstep.
    cbn [fst] in Hg. cbn [snd] in Hp.
    cbn [StackOK]. rewrite Hstep.
    split.
    + (* root step: a right graft (root >= P) forces P < off, so s <> [] *)
      intro Hf. destruct Hext as [HPlt | HPge].
      * destruct (Hpop HPlt) as [Hsne _]. exact Hsne.
      * exfalso. assert (Hlt2 : off + size l < P) by lia.
        rewrite (proj2 (Nat.ltb_lt (off + size l) P) Hlt2) in Hf. discriminate.
    + (* the two subtree blocks *)
      assert (HpreL : pre (off + size l) off l a1 s2).
      { split; [|split].
        - intros y Hy. rewrite Hg.
          rewrite (rootedge_interval P off l r a s y Hpre0 ltac:(cbn [size]; lia)).
          apply Hblank. lia.
        - right. lia.
        - intros Hc; exfalso; lia. }
      apply StackOK_app.
      * exact (IHl (off + size l) off a1 s2 HpreL).
      * destruct r as [|rl rr].
        -- cbn [ipo StackOK]. exact I.
        -- destruct (run_aux (off + size l) (ipo off l) (a1, s2)) as [A_l S_l] eqn:HL.
           pose proof (gen l (off + size l) off a1 s2 HpreL) as [Hgs Hga].
           rewrite HL in Hgs, Hga. cbn [snd] in Hgs. cbn [fst] in Hga.
           rewrite out_stk_left in Hgs. subst S_l.
           assert (HAlhi : forall x, off + size l < x -> A_l x = a1 x).
           { intros x Hx.
             rewrite (Hga x), out_arr_left_eq, setTree_oob by lia.
             destruct l; [reflexivity | apply setL_neq; lia]. }
           pose proof (lastd_ipo_le l off) as HPl.
           assert (Hr : Node rl rr <> Leaf) by discriminate.
           assert (Hpush : s2 = (off + size l) :: rpop P (off + size l) s).
           { rewrite Hp. rewrite (push_interior P off l (Node rl rr) a s Hpre0 Hr).
             reflexivity. }
           apply IHr.
           split; [|split].
           ++ intros y Hy. rewrite HAlhi by lia. rewrite Hg.
              rewrite (rootedge_interval P off l (Node rl rr) a s y Hpre0
                         ltac:(cbn [size] in *; lia)).
              apply Hblank. cbn [size] in *. lia.
           ++ left. lia.
           ++ intros _. rewrite Hpush. split; [discriminate|]. cbn [hd]. left. lia.
Qed.

Print Assumptions StackOK_ipo.

(* Top level: the loop input is the tail of ip t, with the root pre-pushed as
   the singleton stack.  Mirroring the top level of run_eq_setTree, the two
   child blocks compose by StackOK_app and StackOK_ipo. *)
Lemma StackOK_ip : forall t x0 rest,
  ip t = x0 :: rest -> StackOK x0 rest (empty, [x0]).
Proof.
  intros t x0 rest Hip. destruct t as [|l r].
  - unfold ip in Hip; cbn [ipo] in Hip; discriminate.
  - unfold ip in Hip. rewrite ipo_cons in Hip. inversion Hip; subst x0 rest; clear Hip.
    replace (size l) with (0 + size l) by lia.
    assert (HpreL : pre (0 + size l) 0 l empty [0 + size l]).
    { split; [|split].
      - intros y Hy; reflexivity.
      - right; lia.
      - intros Hc; exfalso; lia. }
    apply StackOK_app.
    + apply StackOK_ipo. exact HpreL.
    + destruct r as [|rl rr].
      * cbn [ipo StackOK]. exact I.
      * destruct (run_aux (0 + size l) (ipo 0 l) (empty, [0 + size l]))
          as [A_l S_l] eqn:HL.
        pose proof (gen l (0 + size l) 0 empty [0 + size l] HpreL) as [Hgs Hga].
        rewrite HL in Hgs, Hga. cbn [snd] in Hgs. cbn [fst] in Hga.
        rewrite out_stk_left in Hgs. subst S_l.
        assert (HAlhi : forall y, 0 + size l < y -> A_l y = empty y).
        { intros y Hy.
          rewrite (Hga y), out_arr_left_eq, setTree_oob by lia.
          destruct l; [reflexivity | apply setL_neq; lia]. }
        pose proof (lastd_ipo_le l 0) as HPl.
        apply StackOK_ipo.
        split; [|split].
        -- intros y Hy. rewrite HAlhi by (cbn [size] in *; lia). reflexivity.
        -- left. lia.
        -- intros _. split; [discriminate|]. cbn [hd]. left. lia.
Qed.

Print Assumptions StackOK_ip.

(* End-to-end on a concrete decreasing input: the whole loop refines run,    *)
(* with every well-formedness obligation discharged by computation.          *)
Example iSteps_run_decreasing :
  hoare (fun s => JI 4 empty [2] s /\ sget s PREV = 2)
        (iSteps (4 + 4) [1; 0])
        (fun s => arr_ok_n 4 (run (2 :: [1; 0])) (snd s)).
Proof.
  apply (iSteps_run_bounded 3 2 [1; 0]).
  - lia.
  - repeat constructor; lia.
  - apply StackOK_decreasing. cbn [Decreasing]. repeat split; lia.
Qed.

(* A concrete input that actually exercises the right-graft branch: at the
   second node (cur = 2 >= prev = 0) the loop pops the stack top and writes its
   right link.  StackOK is discharged by computation -- the stack is nonempty at
   that point -- so the whole loop refines run on this input too. *)
Example iSteps_run_right_graft :
  hoare (fun s => JI 4 empty [1] s /\ sget s PREV = 1)
        (iSteps (4 + 4) [0; 2])
        (fun s => arr_ok_n 4 (run (1 :: [0; 2])) (snd s)).
Proof.
  apply (iSteps_run_bounded 3 1 [0; 2]).
  - lia.
  - repeat constructor; lia.
  - cbn. repeat split; intros H; discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* Capstone: when the input is the inorder-preorder code of a tree, the  *)
(* loop builds exactly that tree's parent-pointer array.  This bridges    *)
(* the imperative refinement (iSteps_run) to the verified functional      *)
(* correctness run = setTree (ReconstructFull.run_eq_setTree).            *)
(* ------------------------------------------------------------------ *)
Corollary iSteps_builds_tree : forall N t x0 rest,
  ip t = x0 :: rest ->
  RunOK N x0 rest (empty, [x0]) ->
  hoare (fun s => JI N empty [x0] s /\ sget s PREV = x0)
        (iSteps (N + N) rest)
        (fun s => arr_ok_n N (setTree 0 t empty) (snd s)).
Proof.
  intros N t x0 rest Hip Hok.
  eapply hoare_consequence;
    [ intros s H; exact H
    | apply (iSteps_run N x0 rest Hok)
    | ].
  intros s Harr. rewrite <- Hip in Harr.
  intros k Hk. destruct (Harr k Hk) as [HL HR].
  rewrite (run_eq_setTree t k) in HL, HR.
  split; [ exact HL | exact HR ].
Qed.

Print Assumptions iSteps_builds_tree.

(* ================================================================== *)
(* The unconditional theorem: for EVERY tree, the imperative loop --     *)
(* from the initial configuration (empty array, the root pre-pushed) --   *)
(* builds exactly that tree's parent-pointer array.  Both kinds of        *)
(* RunOK obligation are now discharged: the label bounds by ipo_bounds    *)
(* (with the +1 sentinel N = size t + 1) and the stack invariant by       *)
(* StackOK_ip.  No assumptions remain.                                    *)
(* ================================================================== *)
Corollary iSteps_builds_tree_unconditional : forall t x0 rest,
  ip t = x0 :: rest ->
  hoare (fun s => JI (S (size t)) empty [x0] s /\ sget s PREV = x0)
        (iSteps (S (size t) + S (size t)) rest)
        (fun s => arr_ok_n (S (size t)) (setTree 0 t empty) (snd s)).
Proof.
  intros t x0 rest Hip.
  apply (iSteps_builds_tree (S (size t)) t x0 rest Hip).
  pose proof Hip as Hip0. unfold ip in Hip0.
  apply (RunOK_of_StackOK (size t) rest x0 (empty, [x0])).
  - (* x0 < size t : the head is a label of the tree *)
    assert (Hin : In x0 (ipo 0 t)) by (rewrite Hip0; left; reflexivity).
    apply ipo_bounds in Hin. lia.
  - (* every label in the tail is < size t *)
    apply Forall_forall. intros x Hx.
    assert (Hin : In x (ipo 0 t)) by (rewrite Hip0; right; exact Hx).
    apply ipo_bounds in Hin. lia.
  - (* the stack never underflows *)
    exact (StackOK_ip t x0 rest Hip).
Qed.

Print Assumptions iSteps_builds_tree_unconditional.

(* Concrete instance: the left spine of three internal nodes has the      *)
(* decreasing code ip = [2;1;0], so the loop reconstructs its setTree.    *)
Example iSteps_builds_left_spine :
  hoare (fun s => JI 4 empty [2] s /\ sget s PREV = 2)
        (iSteps (4 + 4) [1; 0])
        (fun s => arr_ok_n 4
                    (setTree 0 (Node (Node (Node Leaf Leaf) Leaf) Leaf) empty)
                    (snd s)).
Proof.
  apply (iSteps_builds_tree 4 (Node (Node (Node Leaf Leaf) Leaf) Leaf) 2 [1; 0]).
  - reflexivity.
  - apply RunOK_of_StackOK.
    + lia.
    + repeat constructor; lia.
    + apply StackOK_decreasing. cbn [Decreasing]. repeat split; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Sanity: the empty loop is a no-op; a single-node run is well-formed   *)
(* when the label fits, and the loop shape for it is exactly one episode. *)
(* ------------------------------------------------------------------ *)
Example iSteps_nil : forall base, iSteps base [] = CSkip.
Proof. reflexivity. Qed.

Example RunOK_nil : forall N prev a st, RunOK N prev [] (a, st).
Proof. intros. exact I. Qed.

Example iSteps_one_shape : forall base cur,
  iSteps base [cur]
  = CSeq (CAssign CUR (ANum cur))
         (CSeq (iStep base) (CSeq (CAssign PREV (ANum cur)) CSkip)).
Proof. reflexivity. Qed.
