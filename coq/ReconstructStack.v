(* ReconstructStack.v
   The construction's label stack as a separate heap region, verified against
   the abstract (top-first) list stack of the functional model.

   We chose a separate-region layout (rather than the C trick of threading the
   stack through the nodes' unused right-child links): the output array occupies
   the heap addresses below 2n (ReconstructHeap.v: node k's links at k+k and
   S(k+k), with labels k < n), so the stack lives in the disjoint region
   [base, ..) with base = 2n.  A stack pointer SP counts the live cells; push
   writes heap[base+SP] and increments SP, pop decrements SP, and the top is
   heap[base+SP-1] -- exactly the array-stack discipline of ImpHoare.v, here over
   the construction's heap region.

   This module proves the region refines the abstract list stack:

       stk_abs (push)  = v :: stk_abs        (push refines cons)
       stk_abs (pop)   = tl (stk_abs)        (pop  refines tl)
       hd  (stk_abs)   = heap[base+SP-1]     (top  refines hd)

   the disjointness from the output array (base = 2n) being a side condition
   discharged at integration.  Axiom-free.

   Rocq Prover 9.1.  Standard library only.  Axiom-free. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import ImpHoare.        (* heap *)
Require Import ReconstructHeap. (* hset *)

(* The top-first abstract view of the stack region [base, base+sp). *)
Definition stk_abs (base sp : nat) (h : heap) : list nat :=
  rev (map (fun j => h (base + j)) (seq 0 sp)).

(* Push: write heap[base+sp] := v and grow the region by one cell. *)
Lemma stk_abs_push : forall base sp v h,
  stk_abs base (S sp) (hset h (base + sp) v) = v :: stk_abs base sp h.
Proof.
  intros base sp v h. unfold stk_abs.
  rewrite (seq_S sp 0), map_app, rev_app_distr. cbn [map rev app].
  f_equal.
  - (* the new top cell reads back v *)
    unfold hset. rewrite Nat.add_0_l, Nat.eqb_refl. reflexivity.
  - (* the cells below are untouched by the write at base+sp *)
    apply f_equal. apply map_ext_in. intros j Hj. rewrite in_seq in Hj.
    unfold hset. rewrite (proj2 (Nat.eqb_neq (base + j) (base + sp))) by lia.
    reflexivity.
Qed.

(* Pop: shrink the region; the abstraction drops the top. *)
Lemma stk_abs_pop : forall base sp h,
  stk_abs base (pred sp) h = tl (stk_abs base sp h).
Proof.
  intros base sp h. destruct sp as [|k]; [reflexivity|]. cbn [pred].
  unfold stk_abs.
  rewrite (seq_S k 0), map_app, rev_app_distr. cbn [map rev app tl]. reflexivity.
Qed.

(* Top: the head of the abstraction is the cell just below SP. *)
Lemma stk_top : forall base k h,
  hd 0 (stk_abs base (S k) h) = h (base + k).
Proof.
  intros base k h. unfold stk_abs.
  rewrite (seq_S k 0), map_app, rev_app_distr. cbn [map rev app hd].
  rewrite Nat.add_0_l. reflexivity.
Qed.

(* Length of the abstraction is exactly the live cell count. *)
Lemma stk_abs_length : forall base sp h, length (stk_abs base sp h) = sp.
Proof.
  intros base sp h. unfold stk_abs.
  rewrite length_rev, length_map, length_seq. reflexivity.
Qed.

Print Assumptions stk_abs_push.
Print Assumptions stk_abs_pop.

(* ------------------------------------------------------------------ *)
(* Sanity: an empty region is the empty stack; pushing 7 then 8 onto    *)
(* the region at base 10 yields the top-first stack [8; 7].             *)
(* ------------------------------------------------------------------ *)
Example stk_abs_empty : forall base h, stk_abs base 0 h = [].
Proof. reflexivity. Qed.

Example stk_push_push :
  stk_abs 10 2 (hset (hset (fun _ => 0) 10 7) 11 8) = [8; 7].
Proof. reflexivity. Qed.

(* Push refines cons on a concrete region (instance of stk_abs_push). *)
Example stk_push_cons :
  stk_abs 10 3 (hset (hset (hset (fun _ => 0) 10 7) 11 8) 12 9) = [9; 8; 7].
Proof. reflexivity. Qed.
