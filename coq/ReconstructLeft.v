(* ReconstructLeft.v
   Unbounded (forall n) correctness of the LEFT-child relation produced by the
   Fig. 1 reconstruction model of Reconstruct.v.

   The left field of a node is written only by setL, in the [cur < prev] branch
   of [step]; the pop/push and the right-field writes never touch it.  Hence the
   left field of node k after the whole run is determined by the single adjacent
   pair (k, successor) in the i-p sequence: it is Some(successor) exactly when
   the successor is smaller than k.  That local fact is bridged to the tree by
   the already-proved grafting criterion [dictionary_left_child], giving, for
   ALL n, a full characterization of the reconstructed left-child relation.

   Build:  rocq c Trees.v Dictionary.v Reconstruct.v  (first)
           rocq c ReconstructLeft.v
   Rocq Prover 9.1.0.  Standard library only; axiom-free. *)

From Stdlib Require Import List Arith Bool Lia.
Import ListNotations.
Require Import Trees.
Require Import Dictionary.
Require Import Reconstruct.

(* ================================================================== *)
(* 1. The array [step] produces, and its left field.                   *)
(* ================================================================== *)

Definition getL (a : arr) (k : nat) : option nat := fst (a k).

(* The push test returns the same array in both branches, so the array after
   one step is just the grafting update. *)
Lemma step_arr : forall prev cur a s,
  fst (step prev cur (a, s)) =
    if Nat.ltb cur prev then setL a prev cur
    else match s with top :: _ => setR a top cur | [] => a end.
Proof.
  intros prev cur a s. unfold step.
  destruct (Nat.ltb cur prev);
    [ destruct (fst (setL a prev cur (cur + 1)))
    | destruct s as [|top s'];
        [ destruct (fst (a (cur + 1)))
        | destruct (fst (setR a top cur (cur + 1))) ] ];
    reflexivity.
Qed.

(* One step changes the left field of node k iff k is the current [prev] and a
   strictly smaller [cur] is grafted there. *)
Lemma getL_step : forall prev cur a s k,
  getL (fst (step prev cur (a, s))) k
  = if Nat.ltb cur prev && Nat.eqb k prev then Some cur else getL a k.
Proof.
  intros prev cur a s k. unfold getL. rewrite step_arr.
  destruct (Nat.ltb cur prev) eqn:Hlt; cbn [andb].
  - unfold setL. destruct (Nat.eqb k prev); reflexivity.
  - destruct s as [|top s'].
    + reflexivity.
    + unfold setR. cbn [fst]. destruct (Nat.eqb k top); reflexivity.
Qed.

(* ================================================================== *)
(* 2. The left field after the whole loop, as a pure scan of the list. *)
(* ================================================================== *)

(* [lpick prev xs d k]: scan the consecutive pairs of (prev :: xs); whenever a
   pair (prev', cur) has prev' = k and cur < prev', record Some cur.  [d] is the
   left field of k on entry. *)
Fixpoint lpick (prev : nat) (xs : list nat) (d : option nat) (k : nat) : option nat :=
  match xs with
  | []          => d
  | cur :: rest =>
      lpick cur rest (if Nat.ltb cur prev && Nat.eqb k prev then Some cur else d) k
  end.

Lemma run_aux_getL : forall xs prev a s k,
  getL (fst (run_aux prev xs (a, s))) k = lpick prev xs (getL a k) k.
Proof.
  induction xs as [|cur rest IH]; intros prev a s k.
  - reflexivity.
  - cbn [run_aux lpick].
    pose proof (getL_step prev cur a s k) as Hg.
    destruct (step prev cur (a, s)) as [a1 s1] eqn:E.
    cbn [fst] in Hg.
    rewrite (IH cur a1 s1 k), Hg. reflexivity.
Qed.

(* Specialized to a full run from the empty array (left field None everywhere). *)
Lemma run_getL : forall x0 rest k,
  getL (run (x0 :: rest)) k = lpick x0 rest None k.
Proof.
  intros x0 rest k. unfold run.
  pose proof (run_aux_getL rest x0 empty [x0] k) as H.
  unfold getL in H |- *. rewrite H. reflexivity.
Qed.

(* ================================================================== *)
(* 3. [lpick] as adjacency: it returns Some b iff k is immediately followed by  *)
(*    a strictly smaller b somewhere in the scanned list.                       *)
(* ================================================================== *)

(* Forward: a recorded value is justified by a concrete adjacent pair. *)
Lemma lpick_some_Adj : forall xs prev d k b,
  lpick prev xs d k = Some b ->
  (d = Some b) \/ (Adj k b (prev :: xs) /\ b < k).
Proof.
  induction xs as [|cur rest IH]; intros prev d k b H.
  - left. exact H.
  - cbn [lpick] in H.
    destruct (Nat.ltb cur prev && Nat.eqb k prev) eqn:Hc.
    + apply IH in H. destruct H as [H | [HA Hlt]].
      * (* the recorded value is Some cur, from this very pair *)
        apply andb_true_iff in Hc as [Hlt' Heq].
        apply Nat.ltb_lt in Hlt'. apply Nat.eqb_eq in Heq. subst.
        injection H as ->. right. split; [apply Adj_head | exact Hlt'].
      * right. split; [apply Adj_cons; exact HA | exact Hlt].
    + apply IH in H. destruct H as [H | [HA Hlt]].
      * left. exact H.
      * right. split; [apply Adj_cons; exact HA | exact Hlt].
Qed.

(* If k never appears as a first component of a scanned pair, [lpick] leaves the
   accumulator untouched. *)
Lemma lpick_no_prev : forall xs prev d k,
  k <> prev -> ~ In k xs -> lpick prev xs d k = d.
Proof.
  induction xs as [|cur rest IH]; intros prev d k Hne Hnin.
  - reflexivity.
  - cbn [lpick].
    replace (Nat.ltb cur prev && Nat.eqb k prev) with false.
    2:{ symmetry. apply andb_false_iff. right. apply Nat.eqb_neq. exact Hne. }
    apply IH.
    + intro Hc. apply Hnin. left. exact (eq_sym Hc).
    + intro Hi. apply Hnin. right. exact Hi.
Qed.

(* Backward: in a duplicate-free list, an adjacent strictly-smaller successor of
   k is exactly the value [lpick] ends on.  [NoDup] makes the single occurrence
   of k as a first component decisive.  This is the form supplied by the i-p
   sequence, whose entries are distinct ([ip_NoDup]). *)
Lemma lpick_Adj_some : forall xs prev d k b,
  NoDup (prev :: xs) -> Adj k b (prev :: xs) -> b < k ->
  lpick prev xs d k = Some b.
Proof.
  induction xs as [|cur rest IH]; intros prev d k b Hnd HA Hlt.
  - (* (prev::[]) has no adjacent pair *)
    destruct HA as [pre [suf Hpre]].
    destruct pre as [|p0 pre']; simpl in Hpre.
    + inversion Hpre.
    + injection Hpre as _ Htl. destruct pre'; simpl in Htl; inversion Htl.
  - cbn [lpick].
    apply NoDup_cons_iff in Hnd as [Hnin Hnd'].
    destruct (Nat.eqb prev k) eqn:Hpk.
    + apply Nat.eqb_eq in Hpk. subst prev.
      (* head pair is (k,cur); the adjacency (k,b) forces cur=b (k is unique) *)
      assert (cur = b) as ->.
      { destruct HA as [pre [suf Hpre]]. destruct pre as [|p0 pre']; simpl in Hpre.
        - injection Hpre as Hb _. exact Hb.
        - injection Hpre as Hp0 Htl. subst p0.
          exfalso. apply Hnin. rewrite Htl. apply in_or_app. right. left. reflexivity. }
      assert (Hg : Nat.ltb b k && Nat.eqb k k = true).
      { apply andb_true_iff. split; [apply Nat.ltb_lt; exact Hlt | apply Nat.eqb_eq; reflexivity]. }
      rewrite Hg.
      apply lpick_no_prev.
      * lia.
      * intro Hi. apply Hnin. right. exact Hi.
    + apply Nat.eqb_neq in Hpk.
      assert (Nat.ltb cur prev && Nat.eqb k prev = false) as ->.
      { apply andb_false_iff. right. apply Nat.eqb_neq. intro Hc. apply Hpk. exact (eq_sym Hc). }
      destruct HA as [pre [suf Hpre]].
      destruct pre as [|p0 pre']; simpl in Hpre.
      * injection Hpre as Hk _. subst. exfalso. apply Hpk. reflexivity.
      * injection Hpre as _ Htl.
        apply IH with (b := b).
        -- exact Hnd'.
        -- exists pre', suf. exact Htl.
        -- exact Hlt.
Qed.

(* ================================================================== *)
(* 4. Main theorem: the reconstructed left-child relation is correct    *)
(*    for ALL n, bridging the run-level scan to the grafting criterion. *)
(* ================================================================== *)

(* For ALL n: node [a] has left child [b] in [t] iff the reconstruction writes
   [b] into [a]'s left field.  Soundness and completeness of the left relation. *)
Theorem run_left_iff : forall t a b,
  lchild 0 t a b <-> getL (run (ip t)) a = Some b.
Proof.
  intros t a b. split.
  - (* completeness: a real left child is reconstructed *)
    intro Hlc.
    pose proof (lchild_Adj 0 t a b Hlc) as HA. unfold ip in HA.
    pose proof (lchild_lt 0 t a b Hlc) as Hlt.
    pose proof (ip_NoDup t) as Hnd. unfold ip in Hnd.
    destruct (ipo 0 t) as [|x0 rest] eqn:E.
    + destruct HA as [pre [suf Hpre]]. destruct pre; simpl in Hpre; discriminate.
    + assert (Hip : ip t = x0 :: rest) by (unfold ip; exact E).
      rewrite Hip, (run_getL x0 rest a).
      apply (lpick_Adj_some rest x0 None a b); assumption.
  - (* soundness: a reconstructed left field is a real left child *)
    intro Hrun.
    destruct (ipo 0 t) as [|x0 rest] eqn:E.
    + (* empty i-p: run is the empty array, left field None, contradiction *)
      assert (Hip : ip t = []) by (unfold ip; exact E).
      unfold getL in Hrun. rewrite Hip in Hrun. cbn in Hrun. discriminate.
    + assert (Hip : ip t = x0 :: rest) by (unfold ip; exact E).
      rewrite Hip, (run_getL x0 rest a) in Hrun.
      apply lpick_some_Adj in Hrun. destruct Hrun as [Hd | [HA Hlt]].
      * discriminate.
      * rewrite <- Hip in HA.
        apply (proj1 (dictionary_left_child t a b HA)). lia.
Qed.

Definition tree7 : tree :=
  Node (Node (Node Leaf Leaf) (Node Leaf (Node Leaf Leaf)))
       (Node (Node Leaf Leaf) Leaf).

Example getL_tree7_4 : getL (run (ip tree7)) 4 = Some 1.
Proof. vm_compute. reflexivity. Qed.
Example getL_tree7_0 : getL (run (ip tree7)) 0 = None.
Proof. vm_compute. reflexivity. Qed.

(* a=4 really has left child 1 in tree7, and the theorem certifies the run. *)
Example lchild_tree7_4 : getL (run (ip tree7)) 4 = Some 1.
Proof. apply run_left_iff. apply lchild_here. discriminate. Qed.

(* ================================================================== *)
(* 5. Axiom-freeness                                                   *)
(* ================================================================== *)

Print Assumptions run_left_iff.
