(* ReconstructLowerBound.v
   The information-theoretic lower bound for reconstruction.

   Any comparison-based algorithm that reconstructs a binary tree from its
   inorder-preorder sequence can be modelled as a binary decision tree: each
   internal node is one comparison with two possible outcomes, and each leaf is
   labelled with the tree the algorithm outputs along that branch.  The number
   of comparisons performed on a given input is the depth of the leaf it
   reaches, so the WORST-CASE comparison count is the height of the decision
   tree.

   Since reconstruction must be able to produce every one of the  C_n  trees of
   size n, a correct decision tree has at least  C_n  distinct leaves.  A binary
   tree of height h has at most  2^h  leaves, hence

        C_n <= 2 ^ (worst-case comparisons),   i.e.   worst case >= log2 C_n.

   With  log2 C_n = 2n - O(log n)  this matches the linear upper bounds
   A_M <= 3n-2 and A_N <= 3n (ReconstructBounds): both algorithms are within a
   constant factor of information-theoretically optimal.

   Rocq Prover 9.1.  Standard library only.  Axiom-free. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import Trees.
Require Import ReconstructCatalan.
Require Import ReconstructDyck.   (* allt_nodup *)

(* ------------------------------------------------------------------ *)
(* Decision trees: internal node = a binary-outcome comparison,        *)
(* leaf = the algorithm's output on that branch.                       *)
(* ------------------------------------------------------------------ *)
Inductive dtree (A : Type) : Type :=
| DLeaf : A -> dtree A
| DNode : dtree A -> dtree A -> dtree A.
Arguments DLeaf {A} _.
Arguments DNode {A} _ _.

(* worst-case number of comparisons = height of the decision tree *)
Fixpoint dheight {A} (d : dtree A) : nat :=
  match d with
  | DLeaf _   => 0
  | DNode l r => S (Nat.max (dheight l) (dheight r))
  end.

(* the multiset of leaf labels (the outputs the algorithm can produce) *)
Fixpoint dleaflist {A} (d : dtree A) : list A :=
  match d with
  | DLeaf a   => [a]
  | DNode l r => dleaflist l ++ dleaflist r
  end.

Definition dleaves {A} (d : dtree A) : nat := length (dleaflist d).

(* ------------------------------------------------------------------ *)
(* The fundamental counting bound: a height-h binary tree has at most  *)
(* 2^h leaves.                                                          *)
(* ------------------------------------------------------------------ *)
Lemma dleaves_le_pow2 : forall {A} (d : dtree A), dleaves d <= 2 ^ dheight d.
Proof.
  intros A d. unfold dleaves. induction d as [a | l IHl r IHr]; simpl.
  - lia.
  - rewrite length_app.
    assert (Hl : 2 ^ dheight l <= 2 ^ Nat.max (dheight l) (dheight r))
      by (apply Nat.pow_le_mono_r; lia).
    assert (Hr : 2 ^ dheight r <= 2 ^ Nat.max (dheight l) (dheight r))
      by (apply Nat.pow_le_mono_r; lia).
    lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Correctness for size n: the decision tree can output every size-n   *)
(* tree (every tree of size n appears as some leaf).                   *)
(* ------------------------------------------------------------------ *)
Definition reconstructs (d : dtree tree) (n : nat) : Prop :=
  incl (allt n) (dleaflist d).

(* A correct decision tree has at least C_n leaves (the C_n distinct    *)
(* size-n trees are pairwise distinct leaves, by allt_nodup).           *)
Theorem catalan_le_leaves : forall d n,
  reconstructs d n -> catalan n <= dleaves d.
Proof.
  intros d n H. unfold catalan, dleaves, reconstructs in *.
  apply NoDup_incl_length; [ apply allt_nodup | exact H ].
Qed.

(* Main bound:  C_n <= 2 ^ (worst-case comparisons). *)
Theorem catalan_le_pow2_height : forall d n,
  reconstructs d n -> catalan n <= 2 ^ dheight d.
Proof.
  intros d n H.
  apply Nat.le_trans with (m := dleaves d).
  - apply catalan_le_leaves, H.
  - apply dleaves_le_pow2.
Qed.

(* The information-theoretic lower bound, in logarithmic form:           *)
(*   worst-case comparisons  >=  ceil(log2 C_n).                         *)
Theorem info_lower_bound : forall d n,
  reconstructs d n -> Nat.log2_up (catalan n) <= dheight d.
Proof.
  intros d n H.
  pose proof (catalan_le_pow2_height d n H) as Hle.
  apply Nat.log2_up_le_mono in Hle.
  rewrite Nat.log2_up_pow2 in Hle by lia.
  exact Hle.
Qed.

Print Assumptions info_lower_bound.

(* ------------------------------------------------------------------ *)
(* An explicit linear form of the bound, with no logarithm.            *)
(* Since C_{n+1} >= 2 C_n for n>=1 (from catalan_ratio: the factor      *)
(* 2(2n+1)/(n+2) exceeds 2 once n>=1) and C_1 = 1, we have              *)
(* C_n >= 2^{n-1}, hence the worst case is at least n-1.                *)
(* ------------------------------------------------------------------ *)
Lemma catalan_double : forall n, 1 <= n -> 2 * catalan n <= catalan (S n).
Proof.
  intros n Hn. pose proof (catalan_ratio n) as Hr. nia.
Qed.

Lemma catalan_ge_pow2 : forall n, 1 <= n -> 2 ^ (n - 1) <= catalan n.
Proof.
  induction n as [|n IH]; intro Hn; [lia|].
  destruct n as [|m].
  - (* n = 1 *) assert (catalan 1 = 1) by reflexivity. simpl. lia.
  - replace (S (S m) - 1) with (S (S m - 1)) by lia.
    rewrite Nat.pow_succ_r'.
    pose proof (IH ltac:(lia)) as IHm.
    pose proof (catalan_double (S m) ltac:(lia)) as Hd.
    nia.
Qed.

(* worst-case comparisons >= n - 1, log-free *)
Theorem info_lower_bound_linear : forall d n,
  1 <= n -> reconstructs d n -> n - 1 <= dheight d.
Proof.
  intros d n Hn H.
  pose proof (info_lower_bound d n H) as Hlog.
  pose proof (catalan_ge_pow2 n Hn) as Hge.
  apply Nat.log2_up_le_mono in Hge.
  rewrite Nat.log2_up_pow2 in Hge by lia.
  lia.
Qed.

Print Assumptions info_lower_bound_linear.

Example catalan_ge_pow2_small :
  map (fun n => Nat.leb (2 ^ (n - 1)) (catalan n)) (seq 1 7) = repeat true 7.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The bound is non-trivial: ceil(log2 C_n) grows linearly in n.        *)
(* C_n = [1;1;2;5;14;42;132;429];  ceil(log2 .) = [0;0;1;3;4;6;8;9].    *)
(* So distinguishing the 14 trees of size 4 already forces >= 4         *)
(* comparisons in the worst case, the 429 trees of size 7 force >= 9.   *)
(* ------------------------------------------------------------------ *)
Example log2_up_catalan_small :
  map (fun n => Nat.log2_up (catalan n)) (seq 0 8) = [0;0;1;3;4;6;8;9].
Proof. reflexivity. Qed.
