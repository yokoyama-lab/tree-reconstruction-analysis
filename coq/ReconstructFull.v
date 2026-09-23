(* ReconstructFull.v
   Closes the bridge run = setTree, hence unbounded (forall n) correctness of
   the FULL parent-child relation of the Fig. 1 reconstruction model.

   We prove the generalized loop invariant [gen] validated in
   ReconstructInvariant.v, by induction on the tree, then derive
   run (ip t) = setTree 0 t empty (pointwise) and, with ReconstructRight's
   setTree_correct, the per-node correctness for ALL n.

   The node array is a function nat -> cell, so we state every array equality
   POINTWISE to avoid functional extensionality (no axioms).  The key fact is
   that setTree's value at x depends only on the base array at x (setTree_local).

   Build:  rocq c Trees.v Dictionary.v Reconstruct.v ReconstructRight.v
           rocq c ReconstructInvariant.v ReconstructFull.v
   Rocq Prover 9.1.0.  Standard library only; axiom-free. *)

From Stdlib Require Import List Arith Bool Lia.
Import ListNotations.
Require Import Trees.
Require Import Dictionary.
Require Import Reconstruct.
Require Import ReconstructRight.
Require Import ReconstructInvariant.

(* ================================================================== *)
(* 1. Locality of the setters and of setTree.                          *)
(* ================================================================== *)

Lemma setL_local : forall a b k v x, a x = b x -> setL a k v x = setL b k v x.
Proof.
  intros a b k v x H. unfold setL.
  destruct (Nat.eqb x k); [rewrite H | exact H]; reflexivity.
Qed.

Lemma setR_local : forall a b k v x, a x = b x -> setR a k v x = setR b k v x.
Proof.
  intros a b k v x H. unfold setR.
  destruct (Nat.eqb x k); [rewrite H | exact H]; reflexivity.
Qed.

(* setTree off t a x depends on the base array only at the point x. *)
Lemma setTree_local : forall t off a b x, a x = b x -> setTree off t a x = setTree off t b x.
Proof.
  induction t as [|l IHl r IHr]; intros off a b x H; [exact H|].
  cbn [setTree size].
  apply IHr. apply IHl.
  (* the root edges agree at x because their base values at x agree *)
  destruct l; destruct r;
    repeat (apply setR_local || apply setL_local); exact H.
Qed.

(* ================================================================== *)
(* 2. One step: the graft is rootedge/rpop; only the push needs the     *)
(*    array value at k+1.                                                *)
(* ================================================================== *)

Lemma step_graft : forall P k a s, fst (step P k (a, s)) = rootedge P k a s.
Proof.
  intros P k a s. unfold step, rootedge.
  destruct (Nat.ltb k P);
    [ destruct (fst (setL a P k (k + 1)))
    | destruct s as [|top s'];
        [ destruct (fst (a (k + 1)))
        | destruct (fst (setR a top k (k + 1))) ] ];
    reflexivity.
Qed.

Lemma step_push : forall P k a s,
  snd (step P k (a, s)) =
    (if match fst (rootedge P k a s (k + 1)) with None => true | _ => false end
     then k :: rpop P k s else rpop P k s).
Proof.
  intros P k a s. unfold step, rootedge, rpop.
  destruct (Nat.ltb k P).
  - destruct (fst (setL a P k (k + 1))); reflexivity.
  - destruct s as [|top s'];
      [ destruct (fst (a (k + 1)))
      | destruct (fst (setR a top k (k + 1))) ]; reflexivity.
Qed.

(* ================================================================== *)
(* 3. Small geometric helpers.                                          *)
(* ================================================================== *)

Lemma lastd_in : forall xs d, In (lastd d xs) (d :: xs).
Proof.
  induction xs as [|x xs IH]; intros d; [left; reflexivity|].
  cbn [lastd]. specialize (IH x). destruct IH as [H | H].
  - right. left. exact H.
  - right. right. exact H.
Qed.

(* The predecessor after the left block stays within l's interval. *)
Lemma lastd_ipo_le : forall l off, lastd (off + size l) (ipo off l) <= off + size l.
Proof.
  intros l off. pose proof (lastd_in (ipo off l) (off + size l)) as H.
  destruct H as [H | H].
  - lia.
  - apply ipo_bounds in H. lia.
Qed.

(* rootedge writes only outside t's interval, so it is inert on the interval. *)
Lemma rootedge_interval : forall P off l r a s y,
  pre P off (Node l r) a s ->
  off <= y < off + size (Node l r) ->
  rootedge P (off + size l) a s y = a y.
Proof.
  intros P off l r a s y [Hblank [Hext Hpop]] Hy.
  unfold rootedge. cbn [size] in *.
  destruct (Nat.ltb (off + size l) P) eqn:Hlt.
  - (* left graft: setL a P (off+size l) ; P external, y in interval => y<>P *)
    apply Nat.ltb_lt in Hlt. apply setL_neq. lia.
  - (* pop: setR a (hd s) (off+size l) ; hd s external *)
    apply Nat.ltb_ge in Hlt.
    (* here off+size l >= P, and P external forces P < off, so the pop branch *)
    assert (HPlt : P < off) by lia.
    destruct Hpop as [Hne Hhd]; [exact HPlt|].
    destruct s as [|top s']; [congruence|].
    cbn [hd] in Hhd. apply setR_neq. lia.
Qed.

(* When r is non-empty, the root's push test reads an interior blank cell, so the
   root is pushed. *)
Lemma push_interior : forall P off l r a s,
  pre P off (Node l r) a s -> r <> Leaf ->
  fst (rootedge P (off + size l) a s (off + size l + 1)) = None.
Proof.
  intros P off l r a s Hpre Hr.
  assert (Hrange : off <= off + size l + 1 < off + size (Node l r)).
  { cbn [size]. destruct r; [congruence | cbn [size]; lia]. }
  rewrite (rootedge_interval P off l r a s (off + size l + 1) Hpre Hrange).
  destruct Hpre as [Hblank _]. rewrite (Hblank (off + size l + 1) Hrange). reflexivity.
Qed.

(* The root's push test read at the boundary node off+size(Node l r) yields
   exactly [maxstay] -- in both graft directions.  (When r is empty the boundary
   is k+1, the root's own push test; when r is non-empty this governs the
   maximum of t instead.) *)
Lemma rootedge_boundary_maxstay : forall P off l r a s,
  pre P off (Node l r) a s ->
  match fst (rootedge P (off + size l) a s (off + size (Node l r))) with
  | None => true | _ => false end
  = maxstay P off (Node l r) a.
Proof.
  intros P off l r a s [Hblank [Hext Hpop]].
  cbn [size] in Hext, Hpop.
  unfold rootedge, maxstay. cbn [size].
  set (B := off + (1 + size l + size r)).
  destruct (Nat.ltb (off + size l) P) eqn:Hlt.
  - apply Nat.ltb_lt in Hlt. unfold setL.
    destruct (Nat.eqb B P) eqn:He.
    + apply Nat.eqb_eq in He. subst P. cbn [fst].
      rewrite Nat.eqb_refl. reflexivity.
    + apply Nat.eqb_neq in He. cbn [fst].
      assert (HPne : Nat.eqb P B = false) by (apply Nat.eqb_neq; unfold B in *; lia).
      rewrite HPne. reflexivity.
  - apply Nat.ltb_ge in Hlt.
    assert (HP : P < off) by (unfold B in *; lia).
    assert (HPne : Nat.eqb P B = false) by (apply Nat.eqb_neq; unfold B in *; lia).
    rewrite HPne. cbn [andb].
    destruct s as [|top s']; [reflexivity|].
    unfold setR. destruct (Nat.eqb B top); reflexivity.
Qed.

(* ================================================================== *)
(* 4. The left block: stack unchanged, array is l's structural write.   *)
(* ================================================================== *)

Lemma out_stk_left : forall l off a s, out_stk (off + size l) off l a s = s.
Proof.
  intros l off a s. destruct l as [|ll lr]; [reflexivity|].
  unfold out_stk, maxstay, rpop.
  rewrite Nat.eqb_refl. cbn [negb andb].
  replace (Nat.ltb (off + size ll) (off + size (Node ll lr))) with true
    by (symmetry; apply Nat.ltb_lt; cbn [size]; lia).
  reflexivity.
Qed.

Lemma out_arr_left_eq : forall l off a s x,
  out_arr (off + size l) off l a s x
  = setTree off l (match l with Leaf => a
                   | _ => setL a (off + size l) (root_label off l) end) x.
Proof.
  intros l off a s x. destruct l as [|ll lr]; [reflexivity|].
  unfold out_arr, rootedge. cbn [root_label].
  replace (Nat.ltb (off + size ll) (off + size (Node ll lr))) with true
    by (symmetry; apply Nat.ltb_lt; cbn [size]; lia).
  reflexivity.
Qed.

(* Pushing a right-write at k (outside l's interval) inside setTree off l. *)
Lemma setR_pushin : forall l off a k v x, off + size l <= k ->
  setR (setTree off l a) k v x = setTree off l (setR a k v) x.
Proof.
  intros l off a k v x Hk.
  destruct (Nat.eqb x k) eqn:Hx.
  - apply Nat.eqb_eq in Hx. subst x. unfold setR.
    rewrite (setTree_oob l off a k (or_intror Hk)).
    rewrite (setTree_oob l off (fun y => if Nat.eqb y k then (fst (a y), Some v) else a y)
                          k (or_intror Hk)).
    rewrite Nat.eqb_refl. reflexivity.
  - apply Nat.eqb_neq in Hx.
    rewrite (setR_neq (setTree off l a) k v x Hx).
    apply setTree_local. rewrite (setR_neq a k v x Hx). reflexivity.
Qed.

(* ================================================================== *)
(* 5. The generalized loop invariant, for all n.                       *)
(* ================================================================== *)

Lemma gen : forall t P off a s, pre P off t a s ->
  snd (run_aux P (ipo off t) (a, s)) = out_stk P off t a s
  /\ (forall x, fst (run_aux P (ipo off t) (a, s)) x = out_arr P off t a s x).
Proof.
  induction t as [|l IHl r IHr]; intros P off a s Hpre.
  - split; [reflexivity | intro x; reflexivity].
  - pose proof Hpre as Hpre0.
    destruct Hpre as [Hblank [Hext Hpop]].
    unfold blank in Hblank. cbn [size] in Hext, Hpop, Hblank.
    rewrite ipo_cons. cbn [run_aux].
    pose proof (step_graft P (off + size l) a s) as Hg.
    pose proof (step_push P (off + size l) a s) as Hp.
    destruct (step P (off + size l) (a, s)) as [a1 s2] eqn:Hstep.
    cbn [fst] in Hg. cbn [snd] in Hp.
    rewrite run_aux_app.
    destruct (run_aux (off + size l) (ipo off l) (a1, s2)) as [A_l S_l] eqn:HL.
    assert (HpreL : pre (off + size l) off l a1 s2).
    { split; [|split].
      - intros y Hy. rewrite Hg.
        rewrite (rootedge_interval P off l r a s y Hpre0 ltac:(cbn [size]; lia)).
        apply Hblank. lia.
      - right. lia.
      - intros Hc; exfalso; lia. }
    destruct (IHl (off + size l) off a1 s2 HpreL) as [IHLs IHLa].
    rewrite HL in IHLs, IHLa. cbn [snd] in IHLs. cbn [fst] in IHLa.
    rewrite out_stk_left in IHLs.
    assert (HAl : forall x, A_l x = setTree off l
                  (match l with Leaf => a1
                   | _ => setL a1 (off + size l) (root_label off l) end) x).
    { intro x. rewrite (IHLa x). apply out_arr_left_eq. }
    assert (HAlhi : forall x, off + size l < x -> A_l x = a1 x).
    { intros x Hx. rewrite HAl. rewrite setTree_oob by lia.
      destruct l; [reflexivity | apply setL_neq; lia]. }
    subst S_l.
    destruct r as [|rl rr].
    + (* r = Leaf : no right block *)
      cbn [ipo run_aux].
      split.
      * cbn [snd]. rewrite Hp.
        replace (off + size l + 1) with (off + size (Node l Leaf)) by (cbn [size]; lia).
        rewrite (rootedge_boundary_maxstay P off l Leaf a s Hpre0).
        unfold out_stk. cbn [size].
        replace (off + (1 + size l + 0) - 1) with (off + size l) by lia.
        destruct (maxstay P off (Node l Leaf) a); reflexivity.
      * intro x. cbn [fst]. rewrite HAl.
        unfold out_arr. rewrite <- Hg. cbn [setTree]. reflexivity.
    + (* r = Node rl rr *)
      assert (Hr : Node rl rr <> Leaf) by discriminate.
      assert (Hpush : s2 = (off + size l) :: rpop P (off + size l) s).
      { rewrite Hp. rewrite (push_interior P off l (Node rl rr) a s Hpre0 Hr). reflexivity. }
      pose proof (lastd_ipo_le l off) as HPl.
      destruct (IHr (lastd (off + size l) (ipo off l)) (off + size l + 1) A_l s2)
        as [IHRs IHRa].
      { split; [|split].
        - intros y Hy. rewrite HAlhi by lia. rewrite Hg.
          rewrite (rootedge_interval P off l (Node rl rr) a s y Hpre0
                     ltac:(cbn [size] in *; lia)).
          apply Hblank. cbn [size] in *. lia.
        - left. lia.
        - intros _. rewrite Hpush. split; [discriminate|]. cbn [hd]. left. lia. }
      split.
      * (* stack *)
        rewrite IHRs. unfold out_stk. cbn [size].
        (* boundary index and maxstay coincide; the tail pops the root *)
        assert (Hmax : maxstay (lastd (off + size l) (ipo off l)) (off + size l + 1)
                         (Node rl rr) A_l = maxstay P off (Node l (Node rl rr)) a).
        { unfold maxstay. cbn [size].
          replace (off + size l + 1 + (1 + size rl + size rr))
            with (off + (1 + size l + (1 + size rl + size rr))) by lia.
          rewrite HAlhi by lia. rewrite Hg.
          replace (Nat.eqb (lastd (off + size l) (ipo off l))
                    (off + (1 + size l + (1 + size rl + size rr)))) with false
            by (symmetry; apply Nat.eqb_neq; lia).
          assert (HB := rootedge_boundary_maxstay P off l (Node rl rr) a s Hpre0).
          unfold maxstay in HB. cbn [size] in HB.
          rewrite <- HB. cbn [negb andb]. reflexivity. }
        rewrite Hmax.
        replace (off + size l + 1 + (1 + size rl + size rr) - 1)
          with (off + (1 + size l + (1 + size rl + size rr)) - 1) by lia.
        f_equal.
        (* the pop: rpop Pl root_r s2 = rpop P (off+size l) s *)
        unfold rpop.
        replace (Nat.ltb (off + size l + 1 + size rl)
                  (lastd (off + size l) (ipo off l))) with false
          by (symmetry; apply Nat.ltb_ge; lia).
        rewrite Hpush. cbn [tl]. reflexivity.
      * (* array *)
        intro x. rewrite IHRa.
        assert (Hout : out_arr (lastd (off + size l) (ipo off l)) (off + size l + 1)
                         (Node rl rr) A_l s2 x
                       = setTree (off + size l + 1) (Node rl rr)
                           (setR A_l (off + size l)
                             (root_label (off + size l + 1) (Node rl rr))) x).
        { unfold out_arr, rootedge.
          replace (Nat.ltb (off + size l + 1 + size rl)
                    (lastd (off + size l) (ipo off l))) with false
            by (symmetry; apply Nat.ltb_ge; cbn [root_label]; lia).
          rewrite Hpush. reflexivity. }
        rewrite Hout. clear Hout.
        unfold out_arr. rewrite <- Hg.
        change (setTree off (Node l (Node rl rr)) a1 x)
          with (setTree (off + size l + 1) (Node rl rr)
                 (setTree off l (setR (match l with Leaf => a1
                                       | _ => setL a1 (off + size l) (root_label off l) end)
                                  (off + size l) (root_label (off + size l + 1) (Node rl rr)))) x).
        apply setTree_local.
        rewrite <- (setR_pushin l off
                  (match l with Leaf => a1
                   | _ => setL a1 (off + size l) (root_label off l) end)
                  (off + size l) (root_label (off + size l + 1) (Node rl rr)) x (le_n _)).
        apply setR_local. exact (HAl x).
Qed.

(* ================================================================== *)
(* 6. The bridge run = setTree, and full correctness for all n.        *)
(* ================================================================== *)

(* The top level pre-pushes the root (no incoming edge); we apply [gen] to the
   two children blocks.  Only the array (fst) is needed. *)
Theorem run_eq_setTree : forall t x, run (ip t) x = setTree 0 t empty x.
Proof.
  intros t x. destruct t as [|l r]; [reflexivity|].
  unfold run, ip. rewrite ipo_cons. cbn [run_aux].
  set (k := 0 + size l) in *.
  rewrite run_aux_app.
  destruct (run_aux k (ipo 0 l) (empty, [k])) as [A_l S_l] eqn:HL.
  assert (HpreL : pre k 0 l empty [k]).
  { split; [|split].
    - intros y Hy. reflexivity.
    - right. unfold k; lia.
    - intros Hc; exfalso; unfold k in Hc; lia. }
  destruct (gen l k 0 empty [k] HpreL) as [GLs GLa].
  rewrite HL in GLs, GLa. cbn [snd] in GLs. cbn [fst] in GLa.
  assert (HSl : S_l = [k]) by (rewrite GLs; apply out_stk_left).
  rewrite HSl. clear GLs HSl.
  assert (HAl : forall y, A_l y = setTree 0 l (match l with Leaf => empty
                 | _ => setL empty k (root_label 0 l) end) y).
  { intro y. rewrite (GLa y). apply out_arr_left_eq. }
  assert (HAlhi : forall y, k < y -> A_l y = empty y).
  { intros y Hy. rewrite HAl. rewrite setTree_oob by (unfold k in *; lia).
    destruct l; [reflexivity | apply setL_neq; unfold k in *; lia]. }
  destruct r as [|rl rr].
  - (* r = Leaf *)
    cbn [ipo run_aux fst]. rewrite HAl.
    change (setTree 0 (Node l Leaf) empty x)
      with (setTree (0 + size l + 1) Leaf
             (setTree 0 l (match l with Leaf => empty
                           | _ => setL empty (0 + size l) (root_label 0 l) end)) x).
    reflexivity.
  - (* r = Node rl rr *)
    destruct (gen (Node rl rr) (lastd k (ipo 0 l)) (k + 1) A_l [k]) as [GRs GRa].
    { split; [|split].
      - intros y Hy. rewrite HAlhi by (unfold k in *; cbn [size] in *; lia). reflexivity.
      - left. pose proof (lastd_ipo_le l 0). unfold k in *; lia.
      - intros _. split; [discriminate|]. cbn [hd]. left.
        pose proof (lastd_ipo_le l 0). unfold k in *; lia. }
    cbn [fst]. rewrite (GRa x).
    assert (Hout : out_arr (lastd k (ipo 0 l)) (k + 1) (Node rl rr) A_l [k] x
                   = setTree (k + 1) (Node rl rr)
                       (setR A_l k (root_label (k + 1) (Node rl rr))) x).
    { unfold out_arr, rootedge.
      replace (Nat.ltb (k + 1 + size rl) (lastd k (ipo 0 l))) with false
        by (symmetry; apply Nat.ltb_ge; cbn [root_label];
            pose proof (lastd_ipo_le l 0); unfold k in *; lia).
      reflexivity. }
    rewrite Hout. clear Hout.
    change (setTree 0 (Node l (Node rl rr)) empty x)
      with (setTree (k + 1) (Node rl rr)
             (setTree 0 l (setR (match l with Leaf => empty
                                 | _ => setL empty k (root_label 0 l) end)
                            k (root_label (k + 1) (Node rl rr)))) x).
    apply setTree_local.
    rewrite <- (setR_pushin l 0 (match l with Leaf => empty
                | _ => setL empty k (root_label 0 l) end)
              k (root_label (k + 1) (Node rl rr)) x ltac:(unfold k; lia)).
    apply setR_local. exact (HAl x).
Qed.

(* Per-node correctness of the reconstruction, for ALL n: the model rebuilds the
   tree's child relation at every node. *)
Theorem reconstruct_correct_all : forall t p,
  In p (child_assoc 0 t) -> run (ip t) (fst p) = snd p.
Proof.
  intros t p Hin. rewrite (run_eq_setTree t (fst p)).
  apply setTree_correct. exact Hin.
Qed.

(* The boolean check of Reconstruct.v holds for every tree, unbounded. *)
Theorem reconstruct_correct : forall t, correct t = true.
Proof.
  intro t. unfold correct. apply forallb_forall. intros p Hin.
  rewrite (reconstruct_correct_all t p Hin).
  destruct (snd p) as [u v]. unfold cell_eqb.
  destruct u, v; cbn [oeqb fst snd]; rewrite ?Nat.eqb_refl; reflexivity.
Qed.

Print Assumptions run_eq_setTree.
Print Assumptions reconstruct_correct.

(* ------------------------------------------------------------------ *)
(* Regression on the running 7-node example (ip = [4;1;0;2;3;6;5]):      *)
(* the reconstruction is correct, and run o ip agrees with setTree       *)
(* pointwise (run_eq_setTree) at a representative node.                  *)
(* ------------------------------------------------------------------ *)
Example correct_tree7 : correct tree7 = true.
Proof. vm_compute. reflexivity. Qed.

Example run_eq_setTree_tree7_node4 : run (ip tree7) 4 = setTree 0 tree7 empty 4.
Proof. vm_compute. reflexivity. Qed.
