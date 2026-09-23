(* ReconstructWhile.v
   The construction loop as a real CWhile, reading the input from a heap region.

   ReconstructLoop.v drove the iteration as a straight-line program with the
   input values baked in (CUR := <literal>).  Here we give the genuine loop: the
   input list lives in a third heap region (disjoint from the output array below
   2N and the label stack in [2N, 3N)), a scalar counter IDX indexes it, and a
   CWhile runs one iStep per input node.  The layout is

       output array : addresses < 2N        (node k's links at k+k, S(k+k))
       label stack  : addresses [2N, 3N)     (depth < N labels, each < N)
       input region : addresses [3N, ..)     (read-only; ip's tail)

   This file builds the foundation: the program, the input-region predicate, the
   functional bound that the stack depth grows by at most one per step (so it
   stays below N), and the locality of iStep (it never writes at or above 3N, so
   it leaves the input region intact).  The loop body and the hoare_while tie-up
   build on these.  Axiom-free.

   Rocq Prover 9.1.  Standard library only.  Axiom-free. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import Reconstruct.
Require Import ImpHoare.
Require Import ReconstructHeap.     (* PREV, CUR, hset *)
Require Import ReconstructStack.     (* stk_abs *)
Require Import ReconstructStackCom.  (* DEPTH, topB, topB_ok *)
Require Import ReconstructFrame.     (* arr_ok_n *)
Require Import ReconstructStep.      (* JI, iStep, TOP, iSetR_top, iGraft, iPushTest, iStep_spec *)
Require Import ReconstructRight.      (* lastd, run_aux_app, setTree *)
Require Import ReconstructLoop.       (* StackOK, StackOK_app, StackOK_ip *)
Require Import Trees.                  (* size *)
Require Import Dictionary.             (* ip, ipo, ipo_bounds, ip_length *)
Require Import ReconstructFull.        (* run_eq_setTree *)

(* The loop counter, disjoint from PREV (0), CUR (1), DEPTH (2), TOP (3). *)
Definition IDX : nat := 4.

(* Base of the input region. *)
Definition INbase (N : nat) : nat := N + N + N.

(* The input region [INbase, INbase + length xs) holds the list xs. *)
Definition inp_ok (base : nat) (xs : list nat) (h : heap) : Prop :=
  forall i, i < length xs -> h (base + i) = nth i xs 0.

(* One loop body: CUR := input[IDX] ; iStep ; PREV := CUR ; IDX := IDX+1. *)
Definition iWhileBody (N : nat) : com :=
  CSeq (CAssign CUR (ALoad (APlus (ANum (INbase N)) (AVar IDX))))
       (CSeq (iStep (N + N))
             (CSeq (CAssign PREV (AVar CUR))
                   (CAssign IDX (APlus (AVar IDX) (ANum 1))))).

(* The loop: run the body while IDX < n (n = number of input nodes to process). *)
Definition iRun (N n : nat) : com :=
  CWhile (BLt (AVar IDX) (ANum n)) (iWhileBody N).

(* ------------------------------------------------------------------ *)
(* The stack depth grows by at most one per step: one push, at most.    *)
(* With the depth a step before bounded, it stays below N.              *)
(* ------------------------------------------------------------------ *)
Lemma step_len_le : forall prev cur a st,
  length (snd (step prev cur (a, st))) <= S (length st).
Proof.
  intros prev cur a st. unfold step.
  destruct (Nat.ltb cur prev) eqn:E.
  - destruct (fst (setL a prev cur (cur + 1))); cbn [snd length]; lia.
  - destruct st as [|top s'].
    + destruct (fst (a (cur + 1))); cbn [snd length]; lia.
    + destruct (fst (setR a top cur (cur + 1))); cbn [snd length]; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Locality of iStep: under the joint invariant (with prev, cur < N) it  *)
(* writes only the output array (< 2N) and one stack cell (< 2N+DEPTH),  *)
(* so it leaves every cell at or above 2N+DEPTH -- in particular the      *)
(* input region [3N, ..) -- untouched.                                   *)
(* ------------------------------------------------------------------ *)
(* A scalar assignment never touches the heap; a heap write never touches the
   store; the obvious store read-back lemmas. *)
Lemma hget_supd : forall s x v addr, hget (supd s x v) addr = hget s addr.
Proof. reflexivity. Qed.
Lemma sget_hupd : forall s a v x, sget (hupd s a v) x = sget s x.
Proof. reflexivity. Qed.
Lemma sget_supd_same : forall s x v, sget (supd s x v) x = v.
Proof. intros. cbv [sget supd]; cbn. rewrite Nat.eqb_refl. reflexivity. Qed.
Lemma sget_supd_other : forall s x y v, y <> x -> sget (supd s x v) y = sget s y.
Proof.
  intros s x y v H. cbv [sget supd]; cbn.
  rewrite (proj2 (Nat.eqb_neq y x) H). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Locality of iStep: under the joint invariant (with prev, cur < N) it  *)
(* writes only the output array (< 2N) and one stack cell (< 2N+DEPTH),  *)
(* so it leaves every cell at or above 2N+DEPTH -- in particular the      *)
(* input region [3N, ..) -- untouched.                                   *)
(* ------------------------------------------------------------------ *)
Lemma iStep_local : forall N a st s s' addr,
  JI N a st s ->
  sget s PREV < N ->
  (Nat.ltb (sget s CUR) (sget s PREV) = false -> st <> []) ->
  ceval (iStep (N + N)) s s' ->
  N + N + sget s DEPTH < addr ->
  hget s' addr = hget s addr.
Proof.
  intros N a st s s' addr [Harr [Hstk [Hdep Hall]]] HPrev Hne Hev Haddr.
  unfold iStep in Hev.
  inversion Hev as [| | | ? ? ? s1 ? Hgraft Hpush | | | |]; subst.
  (* (A) the graft preserves addr and does not raise DEPTH *)
  assert (Hgr : hget s1 addr = hget s addr /\ sget s1 DEPTH <= sget s DEPTH).
  { unfold iGraft in Hgraft.
    inversion Hgraft as [| | | | ? ? ? ? ? Hbt Hset | ? ? ? ? ? Hbf Helse | |]; subst.
    - (* left graft: iSetL, a write at PREV+PREV < 2N *)
      inversion Hset; subst. split.
      + rewrite hget_hupd_other by (cbn [aeval]; lia). reflexivity.
      + rewrite sget_hupd. lia.
    - (* right graft: TOP := top ; pop ; iSetR_top, a write at S(top+top) < 2N *)
      cbn [beval aeval] in Hbf.
      inversion Helse as [| | | ? ? ? sa ? Htop Hrest | | | |]; subst.
      inversion Hrest as [| | | ? ? ? sb ? Hpop Hsetr | | | |]; subst.
      inversion Htop; subst. inversion Hpop; subst.
      unfold iSetR_top in Hsetr. inversion Hsetr; subst.
      assert (Hstne : st <> []) by (apply Hne; exact Hbf).
      destruct st as [|top0 st0]; [contradiction|].
      cbn [length] in Hdep, Hstk.
      assert (Htop0 : top0 < N) by exact (Forall_inv Hall).
      assert (Htv : aeval s (topB (N + N)) = top0).
      { rewrite (topB_ok (N + N) (length st0) s Hdep), Hstk. reflexivity. }
      split.
      + rewrite hget_hupd_other.
        * rewrite !hget_supd. reflexivity.
        * cbn [aeval].
          rewrite sget_supd_other by (unfold DEPTH, TOP; discriminate).
          rewrite sget_supd_same, Htv. lia.
      + rewrite sget_hupd, sget_supd_same. cbn [aeval].
        rewrite sget_supd_other by (unfold DEPTH, TOP; discriminate). lia. }
  destruct Hgr as [Hgrh Hgrd].
  (* (B) the push-test preserves addr: a push lands at 2N+DEPTH(s1) < addr *)
  rewrite <- Hgrh. unfold iPushTest in Hpush.
  inversion Hpush as [| | | | ? ? ? ? ? Hbt Hpb | ? ? ? ? ? Hbf Hsk | |]; subst.
  - (* pushB CUR *)
    unfold pushB in Hpb.
    inversion Hpb as [| | | ? ? ? sc ? Hstore Hinc | | | |]; subst.
    inversion Hstore; subst. inversion Hinc; subst.
    rewrite hget_supd. rewrite hget_hupd_other by (cbn [aeval]; lia).
    reflexivity.
  - (* CSkip *)
    inversion Hsk; subst. reflexivity.
Qed.

Print Assumptions iStep_local.

(* iStep leaves the whole input region intact (every cell is >= 3N > 2N+DEPTH). *)
Lemma iStep_inp : forall N a st xs s s',
  JI N a st s ->
  sget s PREV < N ->
  (Nat.ltb (sget s CUR) (sget s PREV) = false -> st <> []) ->
  sget s DEPTH < N ->
  ceval (iStep (N + N)) s s' ->
  inp_ok (INbase N) xs (snd s) ->
  inp_ok (INbase N) xs (snd s').
Proof.
  intros N a st xs s s' HJI HPrev Hne Hdep Hev Hinp i Hi.
  assert (Hpres : hget s' (INbase N + i) = hget s (INbase N + i)).
  { apply (iStep_local N a st s s' (INbase N + i) HJI HPrev Hne Hev).
    unfold INbase. lia. }
  unfold hget in Hpres. rewrite Hpres. apply Hinp. exact Hi.
Qed.

Print Assumptions iStep_inp.

(* iStep assigns only DEPTH and TOP, so any other register (e.g. IDX) is kept. *)
Lemma iStep_sget_other : forall b x s s',
  x <> DEPTH -> x <> TOP -> ceval (iStep b) s s' -> sget s' x = sget s x.
Proof.
  intros b x s s' HxD HxT Hev. unfold iStep in Hev.
  inversion Hev as [| | | ? ? ? s1 ? Hgraft Hpush | | | |]; subst.
  transitivity (sget s1 x).
  - (* iPushTest: sget s' x = sget s1 x *)
    unfold iPushTest in Hpush.
    inversion Hpush as [| | | | ? ? ? ? ? Hbt Hpb | ? ? ? ? ? Hbf Hsk | |]; subst.
    + unfold pushB in Hpb.
      inversion Hpb as [| | | ? ? ? sc ? Hstore Hinc | | | |]; subst.
      inversion Hstore; subst. inversion Hinc; subst.
      rewrite sget_supd_other by exact HxD. rewrite sget_hupd. reflexivity.
    + inversion Hsk; subst. reflexivity.
  - (* iGraft: sget s1 x = sget s x *)
    unfold iGraft in Hgraft.
    inversion Hgraft as [| | | | ? ? ? ? ? Hbt Hset | ? ? ? ? ? Hbf Helse | |]; subst.
    + inversion Hset; subst. rewrite sget_hupd. reflexivity.
    + inversion Helse as [| | | ? ? ? sa ? Htop Hrest | | | |]; subst.
      inversion Hrest as [| | | ? ? ? sb ? Hpop Hsetr | | | |]; subst.
      inversion Htop; subst. inversion Hpop; subst. inversion Hsetr; subst.
      rewrite sget_hupd, sget_supd_other by exact HxD.
      rewrite sget_supd_other by exact HxT. reflexivity.
Qed.

Print Assumptions iStep_sget_other.

(* ================================================================== *)
(* Scaffolding for the loop invariant: how processing one more input    *)
(* node advances the functional fold, and the per-step well-formedness  *)
(* read off from StackOK / the label bounds.                            *)
(* ================================================================== *)

Lemma firstn_S_app : forall (l : list nat) i,
  i < length l -> firstn (S i) l = firstn i l ++ [nth i l 0].
Proof.
  induction l as [|x l IH]; intros i Hi; [cbn [length] in Hi; lia|].
  destruct i as [|i]; [reflexivity|].
  cbn [firstn nth app]. f_equal. apply IH. cbn [length] in Hi; lia.
Qed.

Lemma lastd_app1 : forall l d x, lastd d (l ++ [x]) = x.
Proof. induction l as [|y l IH]; intros d x; [reflexivity | cbn [app lastd]; apply IH]. Qed.

Lemma lastd_firstn_S : forall x0 rest i,
  i < length rest -> lastd x0 (firstn (S i) rest) = nth i rest 0.
Proof. intros. rewrite firstn_S_app by assumption. apply lastd_app1. Qed.

Lemma run_aux_firstn_S : forall x0 rest i cfg,
  i < length rest ->
  run_aux x0 (firstn (S i) rest) cfg
  = step (lastd x0 (firstn i rest)) (nth i rest 0) (run_aux x0 (firstn i rest) cfg).
Proof.
  intros x0 rest i cfg Hi. rewrite firstn_S_app by assumption.
  rewrite run_aux_app. cbn [run_aux]. reflexivity.
Qed.

Lemma Forall_firstn : forall (P : nat -> Prop) l n,
  Forall P l -> Forall P (firstn n l).
Proof.
  intros P l n. revert n. induction l as [|x l IH]; intros n HF.
  - rewrite firstn_nil. constructor.
  - destruct n as [|n]; [constructor|].
    cbn [firstn]. inversion HF; subst. constructor; [assumption | apply IH; assumption].
Qed.

Lemma lastd_lt : forall l x0 N,
  x0 < N -> Forall (fun x => x < N) l -> lastd x0 l < N.
Proof.
  induction l as [|a l IH]; intros x0 N H0 HF; [exact H0|].
  cbn [lastd]. apply IH; [exact (Forall_inv HF) | exact (Forall_inv_tail HF)].
Qed.

Lemma skipn_S_nth : forall (l : list nat) i,
  i < length l -> skipn i l = nth i l 0 :: skipn (S i) l.
Proof.
  induction l as [|x l IH]; intros i Hi; [cbn [length] in Hi; lia|].
  destruct i as [|i]; [reflexivity|].
  cbn [skipn nth]. apply IH. cbn [length] in Hi; lia.
Qed.

(* The stack entering the i-th step is nonempty whenever that step grafts a
   right child -- read off from StackOK by splitting the run at i. *)
Lemma StackOK_at : forall rest x0 cfg i,
  StackOK x0 rest cfg -> i < length rest ->
  StackOK (lastd x0 (firstn i rest)) (skipn i rest) (run_aux x0 (firstn i rest) cfg).
Proof.
  induction rest as [|c rest IH]; intros x0 cfg i Hok Hi; [cbn [length] in Hi; lia|].
  destruct i as [|i].
  - cbn [firstn skipn lastd run_aux]. exact Hok.
  - cbn [StackOK] in Hok. destruct Hok as [_ Htail].
    cbn [firstn skipn lastd run_aux length] in *.
    apply IH; [exact Htail | lia].
Qed.

Lemma StackOK_step_cond : forall rest x0 cfg i,
  StackOK x0 rest cfg -> i < length rest ->
  Nat.ltb (nth i rest 0) (lastd x0 (firstn i rest)) = false ->
  snd (run_aux x0 (firstn i rest) cfg) <> [].
Proof.
  intros rest x0 cfg i Hok Hi Hlt.
  pose proof (StackOK_at rest x0 cfg i Hok Hi) as Hat.
  rewrite (skipn_S_nth rest i Hi) in Hat. cbn [StackOK] in Hat.
  destruct Hat as [Hh _]. apply Hh. exact Hlt.
Qed.

(* One iStep, carrying both the joint invariant (via iStep_spec) and the input
   region (via iStep_inp). *)
Lemma iStep_full : forall N prev cur a st xs,
  prev < N -> cur < N -> S cur < N ->
  (Nat.ltb cur prev = false -> st <> []) ->
  length st < N ->
  hoare (fun s => JI N a st s /\ sget s PREV = prev /\ sget s CUR = cur
                  /\ inp_ok (INbase N) xs (snd s))
        (iStep (N + N))
        (fun s => JI N (fst (step prev cur (a, st))) (snd (step prev cur (a, st))) s
                  /\ sget s PREV = prev /\ sget s CUR = cur
                  /\ inp_ok (INbase N) xs (snd s)).
Proof.
  intros N prev cur a st xs Hp Hc Hsc Hne Hlen s s' Hev [HJI [HP [HC Hinp]]].
  pose proof HJI as HJIf. destruct HJI as [Harr [Hstk [Hd Hall]]].
  pose proof (iStep_spec N prev cur a st Hp Hc Hsc Hne s s' Hev
                (conj HJIf (conj HP HC))) as [HJI' [HP' HC']].
  split; [exact HJI' | split; [exact HP' | split; [exact HC' |]]].
  refine (iStep_inp N a st xs s s' HJIf _ _ _ Hev Hinp).
  - rewrite HP; exact Hp.
  - rewrite HC, HP; exact Hne.
  - rewrite Hd; exact Hlen.
Qed.

(* The loop invariant: at counter i, the i-node prefix of the input has been
   folded, the predecessor register holds its last node, the input region is
   intact, and the depth has not outgrown S i. *)
Definition LoopInv (N x0 : nat) (rest : list nat) (s : state) : Prop :=
  sget s IDX <= length rest
  /\ JI N (fst (run_aux x0 (firstn (sget s IDX) rest) (empty, [x0])))
          (snd (run_aux x0 (firstn (sget s IDX) rest) (empty, [x0]))) s
  /\ sget s PREV = lastd x0 (firstn (sget s IDX) rest)
  /\ inp_ok (INbase N) rest (snd s)
  /\ sget s DEPTH <= S (sget s IDX).

(* The loop body preserves the invariant: read the next node, run one iStep,
   advance PREV and IDX. *)
Lemma body_spec : forall N x0 rest,
  S (length rest) <= N -> x0 < N -> Forall (fun x => S x < N) rest ->
  StackOK x0 rest (empty, [x0]) ->
  hoare (fun s => LoopInv N x0 rest s
                  /\ beval s (BLt (AVar IDX) (ANum (length rest))) = true)
        (iWhileBody N)
        (LoopInv N x0 rest).
Proof.
  intros N x0 rest Hn Hx0 HF Hstk s s' Hev [HInv Hg].
  destruct HInv as [Hidx [HJI [HPREV [Hinp Hdepb]]]].
  cbn [beval aeval] in Hg. apply Nat.ltb_lt in Hg.
  set (i := sget s IDX) in *.
  destruct (run_aux x0 (firstn i rest) (empty, [x0])) as [a_i st_i] eqn:Hcfg.
  cbn [fst snd] in HJI.
  pose proof HJI as HJIf. destruct HJI as [Harr [Hstk_i [Hd Hall]]].
  assert (HprevN : lastd x0 (firstn i rest) < N).
  { apply lastd_lt; [exact Hx0|]. apply Forall_firstn.
    eapply Forall_impl; [|exact HF]. intros y Hy; cbv beta in Hy; lia. }
  assert (HScurN : S (nth i rest 0) < N).
  { rewrite Forall_forall in HF. apply HF, nth_In, Hg. }
  assert (Hnonempty : Nat.ltb (nth i rest 0) (lastd x0 (firstn i rest)) = false ->
                      st_i <> []).
  { intro Hlt. pose proof (StackOK_step_cond rest x0 (empty, [x0]) i Hstk Hg Hlt) as H0.
    rewrite Hcfg in H0. cbn [snd] in H0. exact H0. }
  assert (Hlen : length st_i < N) by (rewrite <- Hd; lia).
  (* peel the four commands of the body, keeping the intermediate states named *)
  inversion Hev as [| | | ? ? ? s1 ? Hass1 Hr1 | | | |]; subst.
  inversion Hr1 as [| | | ? ? ? s2 ? Histep Hr2 | | | |]; subst.
  inversion Hr2 as [| | | ? ? ? s3 ? Hass3 Hass4 | | | |]; subst.
  assert (Hs1 : s1 = supd s CUR (nth i rest 0)).
  { inversion Hass1; subst. f_equal. cbn [aeval]. unfold hget.
    apply Hinp; exact Hg. }
  assert (Hs3 : s3 = supd s2 PREV (sget s2 CUR)) by (inversion Hass3; subst; reflexivity).
  assert (Hs' : s' = supd s3 IDX (S (sget s3 IDX))).
  { inversion Hass4; subst. f_equal. cbn [aeval]. lia. }
  (* the iStep step, via iStep_full *)
  assert (Hpre1 : JI N a_i st_i s1
                  /\ sget s1 PREV = lastd x0 (firstn i rest)
                  /\ sget s1 CUR = nth i rest 0
                  /\ inp_ok (INbase N) rest (snd s1)).
  { rewrite Hs1. split; [|split; [|split]].
    - exact HJIf.
    - rewrite sget_supd_other by discriminate. exact HPREV.
    - apply sget_supd_same.
    - exact Hinp. }
  pose proof (iStep_full N (lastd x0 (firstn i rest)) (nth i rest 0) a_i st_i rest
                HprevN ltac:(lia) HScurN Hnonempty Hlen s1 s2 Histep Hpre1)
    as [HJI2 [HP2 [HC2 Hinp2]]].
  (* IDX is untouched by iStep *)
  assert (HidxS2 : sget s2 IDX = i).
  { rewrite (iStep_sget_other (N + N) IDX s1 s2 ltac:(discriminate) ltac:(discriminate) Histep).
    rewrite Hs1, sget_supd_other by discriminate. reflexivity. }
  (* assemble LoopInv at s' *)
  assert (Hidx' : sget s' IDX = S i).
  { rewrite Hs'. rewrite sget_supd_same. rewrite Hs3.
    rewrite sget_supd_other by discriminate. rewrite HidxS2; reflexivity. }
  unfold LoopInv. rewrite Hidx'.
  (* common: snd s' = snd s2, sget s' DEPTH = sget s2 DEPTH *)
  assert (Hsnd' : snd s' = snd s2) by (rewrite Hs', Hs3; reflexivity).
  assert (Hdep' : sget s' DEPTH = sget s2 DEPTH).
  { rewrite Hs'. rewrite sget_supd_other by discriminate.
    rewrite Hs3. rewrite sget_supd_other by discriminate. reflexivity. }
  rewrite (run_aux_firstn_S x0 rest i (empty, [x0]) Hg), Hcfg. cbn [fst snd].
  split; [lia | split; [|split; [|split]]].
  - (* JI for the advanced config *)
    revert HJI2. unfold JI. rewrite Hsnd', Hdep'. intro HJI2. exact HJI2.
  - (* PREV = last node = nth i rest 0 *)
    rewrite (lastd_firstn_S x0 rest i Hg).
    rewrite Hs'. rewrite sget_supd_other by discriminate.
    rewrite Hs3. rewrite sget_supd_same. exact HC2.
  - (* input region intact *)
    rewrite Hsnd'. exact Hinp2.
  - (* depth bound: S length(step) <= S (S i) *)
    rewrite Hdep'. destruct HJI2 as [_ [_ [Hd2 _]]]. rewrite Hd2.
    pose proof (step_len_le (lastd x0 (firstn i rest)) (nth i rest 0) a_i st_i) as Hsl.
    cbn [snd] in Hsl. lia.
Qed.

Print Assumptions body_spec.

(* The whole CWhile loop: from the loop invariant it ends having folded the
   entire input, building run_aux x0 rest in the heap. *)
Lemma iRun_spec : forall N x0 rest,
  S (length rest) <= N -> x0 < N -> Forall (fun x => S x < N) rest ->
  StackOK x0 rest (empty, [x0]) ->
  hoare (LoopInv N x0 rest)
        (iRun N (length rest))
        (fun s => JI N (fst (run_aux x0 rest (empty, [x0])))
                       (snd (run_aux x0 rest (empty, [x0]))) s
                  /\ inp_ok (INbase N) rest (snd s)).
Proof.
  intros N x0 rest Hn Hx0 HF Hstk.
  eapply hoare_consequence;
    [ intros s H; exact H
    | apply (hoare_while (LoopInv N x0 rest)
               (BLt (AVar IDX) (ANum (length rest))) (iWhileBody N)
               (body_spec N x0 rest Hn Hx0 HF Hstk))
    | ].
  intros s [HInv Hg].
  cbn [beval aeval] in Hg. apply Nat.ltb_ge in Hg.
  destruct HInv as [Hle [HJI [_ [Hinp _]]]].
  assert (Heq : sget s IDX = length rest) by lia.
  rewrite Heq, firstn_all in HJI.
  split; [exact HJI | exact Hinp].
Qed.

Print Assumptions iRun_spec.

(* Capstone: from its loop invariant, the genuine CWhile loop on a tree's i-p
   code builds exactly that tree's parent-pointer array -- the well-formedness
   discharged by StackOK_ip and the label bounds, just as for the straight-line
   form.  (A caller establishes the invariant at IDX = 0, i.e. the empty array,
   the singleton stack [x0], the input laid out, and PREV = x0.) *)
Corollary iRun_builds_tree : forall t x0 rest,
  ip t = x0 :: rest ->
  hoare (LoopInv (S (size t)) x0 rest)
        (iRun (S (size t)) (length rest))
        (fun s => arr_ok_n (S (size t)) (setTree 0 t empty) (snd s)).
Proof.
  intros t x0 rest Hip.
  assert (HF : Forall (fun x => S x < S (size t)) rest).
  { apply Forall_forall. intros x Hx.
    assert (Hin : In x (ipo 0 t)) by (unfold ip in Hip; rewrite Hip; right; exact Hx).
    apply ipo_bounds in Hin. lia. }
  assert (Hx0 : x0 < S (size t)).
  { assert (Hin : In x0 (ipo 0 t)) by (unfold ip in Hip; rewrite Hip; left; reflexivity).
    apply ipo_bounds in Hin. lia. }
  assert (Hn : S (length rest) <= S (size t)).
  { pose proof (ip_length t) as Hl. rewrite Hip in Hl. cbn [length] in Hl. lia. }
  eapply hoare_consequence;
    [ intros s H; exact H
    | apply (iRun_spec (S (size t)) x0 rest Hn Hx0 HF (StackOK_ip t x0 rest Hip))
    | ].
  intros s [HJI _]. destruct HJI as [Harr _].
  assert (Hak : forall k, fst (run_aux x0 rest (empty, [x0])) k = setTree 0 t empty k).
  { intro k. change (fst (run_aux x0 rest (empty, [x0])) k) with (run (x0 :: rest) k).
    rewrite <- Hip. apply run_eq_setTree. }
  intros k Hk. destruct (Harr k Hk) as [HL HR].
  rewrite (Hak k) in HL, HR. split; [exact HL | exact HR].
Qed.

Print Assumptions iRun_builds_tree.

(* The loop invariant holds at the start (IDX = 0) for the concrete initial
   configuration: the output array zeroed, the singleton stack [x0], the input
   laid out, PREV = x0. *)
Lemma LoopInv_init : forall N x0 rest s,
  x0 < N ->
  sget s IDX = 0 -> sget s PREV = x0 -> sget s DEPTH = 1 ->
  arr_ok_n N empty (snd s) ->
  stk_abs (N + N) 1 (snd s) = [x0] ->
  inp_ok (INbase N) rest (snd s) ->
  LoopInv N x0 rest s.
Proof.
  intros N x0 rest s Hx0 Hidx Hprev Hdep Harr Hstk Hinp.
  unfold LoopInv. rewrite Hidx. cbn [firstn run_aux fst snd lastd].
  split; [lia | split; [|split; [|split]]].
  - unfold JI. cbn [length].
    split; [exact Harr | split; [exact Hstk | split; [exact Hdep|]]].
    constructor; [exact Hx0 | constructor].
  - exact Hprev.
  - exact Hinp.
  - rewrite Hdep. lia.
Qed.

(* Self-contained capstone: from the explicit initial heap/store configuration,
   the genuine CWhile program builds the tree's parent-pointer array. *)
Corollary iRun_builds_tree_init : forall t x0 rest,
  ip t = x0 :: rest ->
  hoare (fun s => sget s IDX = 0 /\ sget s PREV = x0 /\ sget s DEPTH = 1
                  /\ arr_ok_n (S (size t)) empty (snd s)
                  /\ stk_abs (S (size t) + S (size t)) 1 (snd s) = [x0]
                  /\ inp_ok (INbase (S (size t))) rest (snd s))
        (iRun (S (size t)) (length rest))
        (fun s => arr_ok_n (S (size t)) (setTree 0 t empty) (snd s)).
Proof.
  intros t x0 rest Hip.
  assert (Hx0 : x0 < S (size t)).
  { assert (Hin : In x0 (ipo 0 t)) by (unfold ip in Hip; rewrite Hip; left; reflexivity).
    apply ipo_bounds in Hin. lia. }
  eapply hoare_consequence;
    [ | apply (iRun_builds_tree t x0 rest Hip) | intros s H; exact H ].
  intros s [Hidx [Hprev [Hdep [Harr [Hstk Hinp]]]]].
  apply LoopInv_init; assumption.
Qed.

Print Assumptions iRun_builds_tree_init.

(* ------------------------------------------------------------------ *)
(* Sanity: register disjointness and the program shapes.                *)
(* ------------------------------------------------------------------ *)
Example idx_register_disjoint :
  IDX <> PREV /\ IDX <> CUR /\ IDX <> DEPTH /\ IDX <> TOP.
Proof. unfold IDX, PREV, CUR, DEPTH, TOP. repeat split; discriminate. Qed.

Example input_above_stack : forall N, N + N + N = INbase N.
Proof. reflexivity. Qed.

Example iRun_unfold : forall N n,
  iRun N n = CWhile (BLt (AVar IDX) (ANum n)) (iWhileBody N).
Proof. reflexivity. Qed.

(* End-to-end on a concrete initial heap: the left spine of three internal nodes
   has code ip = [2;1;0].  Lay it out -- IDX=0, PREV=2, DEPTH=1, the output array
   (addresses < 8) zeroed, the stack cell at 8 holding 2, the input [1;0] at
   12,13 -- and any run of the CWhile program ends with that tree's setTree. *)
Example iRun_builds_left_spine : forall s',
  ceval (iRun 4 2)
        (fun r => if r =? 0 then 2 else if r =? 2 then 1 else 0,
         fun a => if a =? 8 then 2 else if a =? 12 then 1 else 0)
        s' ->
  arr_ok_n 4 (setTree 0 (Node (Node (Node Leaf Leaf) Leaf) Leaf) empty) (snd s').
Proof.
  intros s' Hev.
  apply (iRun_builds_tree_init (Node (Node (Node Leaf Leaf) Leaf) Leaf) 2 [1; 0]
            eq_refl _ s' Hev).
  split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [|split]]]].
  - (* output array zeroed below 8 *)
    intros k Hk. destruct k as [|[|[|[|k]]]].
    + cbn; split; reflexivity.
    + cbn; split; reflexivity.
    + cbn; split; reflexivity.
    + cbn; split; reflexivity.
    + exfalso; cbn in Hk; lia.
  - (* the stack holds [2] *)
    reflexivity.
  - (* the input region holds [1;0] *)
    intros j Hj. destruct j as [|[|j]].
    + cbn; reflexivity.
    + cbn; reflexivity.
    + exfalso; cbn [length] in Hj; lia.
Qed.
