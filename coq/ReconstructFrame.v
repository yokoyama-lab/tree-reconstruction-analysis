(* ReconstructFrame.v
   Region separation between the output array and the label stack.

   For the integrated construction the two structures share one heap, in the
   chosen separate-region layout (ReconstructStack.v): node labels are < n, so
   the output array occupies addresses < 2n, and the stack lives in [2n, ..).
   This module proves that the two regions do not interfere -- the concrete
   ``frame'' between them:

     * a write in the stack region (address >= 2N) preserves the (bounded)
       array correspondence  arr_ok_n N;
     * a write in the array region (address < base) preserves the stack view
       stk_abs base.

   These are the lemmas that, with base = 2n, let one step of the construction
   update the array and the stack independently.  Axiom-free.

   Rocq Prover 9.1.  Standard library only.  Axiom-free. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import Reconstruct.
Require Import ImpHoare.
Require Import ReconstructHeap.
Require Import ReconstructStack.

(* The array correspondence restricted to the live nodes (labels < N): the only
   form preserved by a write in the disjoint stack region. *)
Definition arr_ok_n (N : nat) (a : arr) (h : heap) : Prop :=
  forall k, k < N -> h (k + k) = enc (fst (a k)) /\ h (S (k + k)) = enc (snd (a k)).

(* The full (unbounded) correspondence implies every bounded one. *)
Lemma arr_ok_to_n : forall N a h, arr_ok a h -> arr_ok_n N a h.
Proof. intros N a h Ha k _. exact (Ha k). Qed.

(* A write in the stack region (addr >= 2N) leaves the array region intact. *)
Lemma arr_ok_n_frame : forall N a h addr v,
  N + N <= addr -> arr_ok_n N a h -> arr_ok_n N a (hset h addr v).
Proof.
  intros N a h addr v Hge Ha k Hk. unfold hset.
  destruct (Ha k Hk) as [HL HR].
  rewrite (proj2 (Nat.eqb_neq (k + k) addr)) by lia.
  rewrite (proj2 (Nat.eqb_neq (S (k + k)) addr)) by lia.
  split; assumption.
Qed.

(* A write in the array region (addr < base) leaves the stack view intact. *)
Lemma stk_abs_frame : forall base sp h addr v,
  addr < base -> stk_abs base sp (hset h addr v) = stk_abs base sp h.
Proof.
  intros base sp h addr v Hlt. unfold stk_abs. f_equal.
  apply map_ext_in. intros j Hj. unfold hset.
  rewrite (proj2 (Nat.eqb_neq (base + j) addr)) by lia. reflexivity.
Qed.

Print Assumptions arr_ok_n_frame.
Print Assumptions stk_abs_frame.

(* ------------------------------------------------------------------ *)
(* Sanity: with base = 2N the output array (addresses < 2N) and the     *)
(* stack region (addresses >= 2N) are disjoint, so each frame applies.  *)
(* ------------------------------------------------------------------ *)
Example array_below_2N : forall N k, k < N -> S (k + k) < N + N.
Proof. intros N k Hk. lia. Qed.

Example stack_at_or_above_2N : forall N j, N + N <= N + N + j.
Proof. intros N j. lia. Qed.

(* A graft write (array region, addr < 2N) preserves the stack at base 2N. *)
Example graft_preserves_stack : forall N h prev cur sp,
  prev < N ->
  stk_abs (N + N) sp (hset h (prev + prev) (S cur)) = stk_abs (N + N) sp h.
Proof. intros N h prev cur sp Hp. apply stk_abs_frame. lia. Qed.
