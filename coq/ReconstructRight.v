(* ReconstructRight.v
   Toward unbounded (forall n) correctness of the FULL parent-child relation of
   the Fig. 1 reconstruction model (Reconstruct.v).

   A computational discovery, then partial proof.  The companion ReconstructLeft.v
   already proves the left-child relation correct for all n.  Here we identify the
   exact structural target for the whole array: the run equals a direct recursive
   write of every node's child pointers,

        run (ip t)  =  setTree 0 t empty          (validated below, n <= 10),

   and the run terminates with exactly the maximum label on its stack,

        run_stack (ip t) = [size t - 1].

   We prove (i) the reusable append law for run_aux, for all n; (ii) that the
   structural target setTree is itself correct against child_assoc, for all n;
   and (iii) the equality run = setTree by reflection over all trees of size
   <= 10.  Promoting (iii) to all n requires a generalized run_aux-over-ipo
   invariant whose only delicate point is a single boundary left-field
   (a[off+size t].l, deciding whether the maximum of t is pushed); this is stated
   as the remaining obligation.  All proofs below are axiom-free.

   Build:  rocq c Trees.v Dictionary.v Reconstruct.v  (first)
           rocq c ReconstructRight.v
   Rocq Prover 9.1.0.  Standard library only. *)

From Stdlib Require Import List Arith Bool Lia.
Import ListNotations.
Require Import Trees.
Require Import Dictionary.
Require Import Reconstruct.

(* ================================================================== *)
(* 1. The append law for run_aux (reusable, all n).                    *)
(* ================================================================== *)

(* The predecessor threaded into the second part of a concatenation: the last
   element of the first part (or the incoming [d] if it is empty).  This folds
   exactly like run_aux's predecessor, so no auxiliary [last] lemmas are needed. *)
Fixpoint lastd (d : nat) (xs : list nat) : nat :=
  match xs with [] => d | x :: xs' => lastd x xs' end.

(* Processing a concatenation is processing the parts in turn, threading the
   last element of the first part as the predecessor of the second. *)
Lemma run_aux_app : forall xs ys prev st,
  run_aux prev (xs ++ ys) st = run_aux (lastd prev xs) ys (run_aux prev xs st).
Proof.
  induction xs as [|cur rest IH]; intros ys prev st.
  - reflexivity.
  - cbn [app run_aux lastd]. apply IH.
Qed.

(* ================================================================== *)
(* 2. The structural target and its correctness (all n).               *)
(* ================================================================== *)

Definition run_full (ip : list nat) : arr * list nat :=
  match ip with
  | []        => (empty, [])
  | x0 :: rest => run_aux x0 rest (empty, [x0])
  end.
Definition run_stack (ip : list nat) : list nat := snd (run_full ip).

(* Direct recursive write of all of t's child pointers (labels from off). *)
Fixpoint setTree (off : nat) (t : tree) (a : arr) : arr :=
  match t with
  | Leaf => a
  | Node l r =>
      let k := off + size l in
      let a1 := match l with Leaf => a | _ => setL a k (root_label off l) end in
      let a2 := match r with Leaf => a1 | _ => setR a1 k (root_label (off + size l + 1) r) end in
      setTree (off + size l + 1) r (setTree off l a2)
  end.

(* ================================================================== *)
(* 3. Computational evidence: run = setTree, and the final stack.       *)
(* ================================================================== *)

Definition agree (t : tree) : bool :=
  forallb (fun p => cell_eqb (run (ip t) (fst p)) (setTree 0 t empty (fst p)))
          (child_assoc 0 t).

(* MAIN (bounded): the run equals the structural write setTree on every tree of
   size <= 10 -- all 23,714 of them; closed by reflection, axiom-free.  This is
   a sharper statement than reconstruct_correct_upto_10: it pins the run to an
   explicit recursive array, the target for an all-n proof. *)
Theorem run_eq_setTree_upto_10 :
  forallb agree (trees_upto 10) = true.
Proof. vm_compute. reflexivity. Qed.

(* The run terminates with exactly the maximum label on its stack. *)
Definition stack_is_max (t : tree) : bool :=
  match t with
  | Leaf => Nat.eqb (length (run_stack (ip t))) 0
  | _    => Nat.eqb (length (run_stack (ip t))) 1
           && Nat.eqb (hd 0 (run_stack (ip t))) (size t - 1)
  end.

Theorem stack_is_max_upto_10 :
  forallb stack_is_max (trees_upto 10) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* 4. The structural target is correct against child_assoc, ALL n.     *)
(*    This factors the remaining problem: the left relation is already  *)
(*    proved for all n (ReconstructLeft.run_left_iff); setTree is proved *)
(*    correct for all n here; so the sole all-n gap is run = setTree,    *)
(*    machine-checked above for n <= 10.                                 *)
(* ================================================================== *)

(* setL / setR do not touch a cell other than their own. *)
Lemma setL_neq : forall a k v x, x <> k -> setL a k v x = a x.
Proof. intros a k v x H. unfold setL. rewrite (proj2 (Nat.eqb_neq x k) H). reflexivity. Qed.
Lemma setR_neq : forall a k v x, x <> k -> setR a k v x = a x.
Proof. intros a k v x H. unfold setR. rewrite (proj2 (Nat.eqb_neq x k) H). reflexivity. Qed.

(* The "root edges" written for a Node, evaluated off the root, are inert. *)
Lemma roots_neq : forall l r off a x, x <> off + size l ->
  (match r with Leaf => match l with Leaf => a | _ => setL a (off + size l) (root_label off l) end
   | _ => setR (match l with Leaf => a | _ => setL a (off + size l) (root_label off l) end)
                (off + size l) (root_label (off + size l + 1) r) end) x = a x.
Proof.
  intros l r off a x Hx.
  destruct r; destruct l; rewrite ?setR_neq, ?setL_neq by exact Hx; reflexivity.
Qed.

(* setTree writes only inside t's label interval [off, off+size t). *)
Lemma setTree_oob : forall t off a x,
  x < off \/ off + size t <= x -> setTree off t a x = a x.
Proof.
  induction t as [|l IHl r IHr]; intros off a x Hx; [reflexivity|].
  cbn [setTree size] in *.
  rewrite IHr by lia. rewrite IHl by lia.
  apply roots_neq. lia.
Qed.

(* The cell setTree assigns to the root k, from a base array that is empty on
   t's interval, is exactly child_assoc's entry for k. *)
Lemma setTree_root : forall l r off a,
  a (off + size l) = (None, None) ->
  setTree off (Node l r) a (off + size l)
  = (root_opt off l, root_opt (off + size l + 1) r).
Proof.
  intros l r off a Ha. cbn [setTree size].
  rewrite setTree_oob by lia. rewrite setTree_oob by lia.
  destruct l; destruct r; unfold setL, setR; cbn [root_opt];
    rewrite ?Nat.eqb_refl; cbn [fst snd]; rewrite ?Ha; reflexivity.
Qed.

(* Every label listed by child_assoc off t lies in t's interval. *)
Lemma child_assoc_range : forall t off p,
  In p (child_assoc off t) -> off <= fst p < off + size t.
Proof.
  induction t as [|l IHl r IHr]; intros off p Hin; [contradiction|].
  cbn [child_assoc size] in *.
  destruct Hin as [Heq | Hin].
  - subst p. cbn [fst]. lia.
  - apply in_app_or in Hin. destruct Hin as [Hl | Hr].
    + specialize (IHl off p Hl). lia.
    + specialize (IHr (off + size l + 1) p Hr). lia.
Qed.

(* Main structural correctness, generalized over the offset and a base array
   that is blank on the subtree's interval. *)
Lemma setTree_correct_gen : forall t off a,
  (forall x, off <= x < off + size t -> a x = (None, None)) ->
  forall p, In p (child_assoc off t) -> setTree off t a (fst p) = snd p.
Proof.
  induction t as [|l IHl r IHr]; intros off a Hblank p Hin; [contradiction|].
  cbn [child_assoc] in Hin. cbn [size] in Hblank.
  destruct Hin as [Heq | Hin].
  - (* p is the root entry *)
    subst p. cbn [fst snd].
    apply setTree_root. apply Hblank. lia.
  - apply in_app_or in Hin. destruct Hin as [Hl | Hr].
    + (* p is in the left subtree: the outer r-write is out of range *)
      cbn [setTree size]. rewrite setTree_oob by
        (pose proof (child_assoc_range l off p Hl); lia).
      apply IHl; [| exact Hl].
      intros x Hx. rewrite roots_neq by lia. apply Hblank. lia.
    + (* p is in the right subtree *)
      cbn [setTree size].
      apply IHr; [| exact Hr].
      intros x Hx. rewrite setTree_oob by lia. rewrite roots_neq by lia.
      apply Hblank. lia.
Qed.

Theorem setTree_correct : forall t p,
  In p (child_assoc 0 t) -> setTree 0 t empty (fst p) = snd p.
Proof.
  intros t p Hin. apply (setTree_correct_gen t 0 empty); [| exact Hin].
  intros x _. reflexivity.
Qed.

(* ================================================================== *)
(* 5. Axiom-freeness                                                   *)
(* ================================================================== *)

Print Assumptions run_aux_app.
Print Assumptions setTree_correct.
Print Assumptions run_eq_setTree_upto_10.

(* ------------------------------------------------------------------ *)
(* Regression: setTree builds the running 7-node example's child cells   *)
(* (ip = [4;1;0;2;3;6;5]): node 1 has children (0,2), node 4 has (1,6).  *)
(* ------------------------------------------------------------------ *)
Example setTree_tree7_node1 : setTree 0 tree7 empty 1 = (Some 0, Some 2).
Proof. vm_compute. reflexivity. Qed.

Example setTree_tree7_node4 : setTree 0 tree7 empty 4 = (Some 1, Some 6).
Proof. vm_compute. reflexivity. Qed.
