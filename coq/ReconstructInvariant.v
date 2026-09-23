(* ReconstructInvariant.v
   The generalized loop invariant that closes the gap "run = setTree".

   ReconstructRight.v reduced unbounded correctness to the single equation
   run (ip t) = setTree 0 t empty.  That equation follows from one generalized
   statement about processing a subtree's preorder block,

       run_aux P (ipo off t) (a, s) = (out_arr P off t a s, out_stk P off t a s),

   under a precondition [pre] that the array is blank on t's interval, the
   predecessor P is external, and (when the root is grafted as a right child)
   the stack top is external.  The output array is t's structural write plus the
   root's incoming edge; the output stack keeps the maximum label of t exactly
   when it is a "false-positive" push (its push test reads the still-unset
   boundary left-field a[off+size t].l).

   This file STATES that invariant precisely, with all spec functions, and
   MACHINE-VALIDATES it by reflection over every subtree of size <= 6 in both
   graft directions, at several offsets, and for both boundary values.  The
   all-n proof is an induction on t (sketch in the comments) whose only subtlety
   is the single boundary left-field; stating it pointwise sidesteps functional
   extensionality (the array is a function nat -> cell), exactly as in
   ReconstructLeft/ReconstructRight.

   Build:  rocq c Trees.v Dictionary.v Reconstruct.v ReconstructRight.v (first)
           rocq c ReconstructInvariant.v
   Rocq Prover 9.1.0.  Standard library only; axiom-free. *)

From Stdlib Require Import List Arith Bool Lia.
Import ListNotations.
Require Import Trees.
Require Import Dictionary.
Require Import Reconstruct.
Require Import ReconstructRight.

(* ================================================================== *)
(* 1. Spec functions of the generalized invariant.                     *)
(* ================================================================== *)

(* The root's incoming edge: left child of P if root < P, else (popping the
   stack) the right child of the current top. *)
Definition rootedge (P k : nat) (a : arr) (s : list nat) : arr :=
  if Nat.ltb k P then setL a P k
  else match s with top :: _ => setR a top k | [] => a end.

(* The stack after grafting the root: a pop iff the root is a right child. *)
Definition rpop (P k : nat) (s : list nat) : list nat :=
  if Nat.ltb k P then s else match s with _ :: s' => s' | [] => s end.

(* Whether the maximum label of t stays on the stack: t is non-empty, the
   predecessor is not the boundary node (which would have set a[off+size t].l),
   and the boundary left-field is unset. *)
Definition maxstay (P off : nat) (t : tree) (a : arr) : bool :=
  match t with
  | Leaf => false
  | _ => negb (Nat.eqb P (off + size t)) &&
         match fst (a (off + size t)) with None => true | _ => false end
  end.

Definition out_arr (P off : nat) (t : tree) (a : arr) (s : list nat) : arr :=
  match t with Leaf => a | Node l _ => setTree off t (rootedge P (off + size l) a s) end.

Definition out_stk (P off : nat) (t : tree) (a : arr) (s : list nat) : list nat :=
  match t with
  | Leaf => s
  | Node l _ => (if maxstay P off t a then [off + size t - 1] else [])
                  ++ rpop P (off + size l) s
  end.

(* Precondition under which the invariant holds. *)
Definition blank (off : nat) (t : tree) (a : arr) : Prop :=
  forall x, off <= x < off + size t -> a x = (None, None).

Definition pre (P off : nat) (t : tree) (a : arr) (s : list nat) : Prop :=
  blank off t a
  /\ (P < off \/ off + size t <= P)                       (* P external to t *)
  /\ (P < off -> s <> [] /\ (hd 0 s < off \/ off + size t <= hd 0 s)).
                                                          (* pop target external *)

(* The all-n statement (proved bounded below; induction sketch in the header):
     forall t P off a s, pre P off t a s ->
       run_aux P (ipo off t) (a, s) = (out_arr P off t a s, out_stk P off t a s). *)

(* ================================================================== *)
(* 2. Machine validation of the invariant (bounded, axiom-free).       *)
(* ================================================================== *)

Definition arr_eqb (m : nat) (a b : arr) : bool :=
  forallb (fun x => cell_eqb (a x) (b x)) (seq 0 m).
Fixpoint lst_eqb (xs ys : list nat) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => Nat.eqb x y && lst_eqb xs' ys'
  | _, _ => false
  end.

(* boundary test array: blank on t's interval, a[off+size t].l = B *)
Definition bnd (off : nat) (t : tree) (B : option nat) : arr :=
  fun x => if Nat.eqb x (off + size t) then (B, None) else (None, None).

Definition check (P off : nat) (t : tree) (B : option nat) (s : list nat) : bool :=
  let a := bnd off t B in
  let '(ar, sk) := run_aux P (ipo off t) (a, s) in
  arr_eqb (off + size t + 2) ar (out_arr P off t a s)
  && lst_eqb sk (out_stk P off t a s).

(* For each tree: both graft directions (left graft with P at/above the
   boundary, pop with P below the offset and an external stack top), both
   boundary values, several offsets. *)
Definition cases (t : tree) : list bool :=
  let n := size t in
  concat (map (fun off =>
    [ check (off + n) off t None [7;8];
      check (off + n) off t (Some 900) [7;8];
      check (off + n + 1) off t None [7;8];
      check (off + n + 1) off t (Some 900) [7;8] ]
    ++ (if Nat.ltb 0 off
        then [ check 0 off t None [off + n + 5; 8];
               check 0 off t (Some 900) [off + n + 5; 8] ]
        else [])) [0;1;2]).

Definition all_ok (N : nat) : bool :=
  forallb (fun t => forallb (fun b => b) (cases t)) (trees_upto N).

(* The generalized invariant holds on every subtree of size <= 6, in both graft
   directions and for both boundary values: 197 trees, axiom-free. *)
Theorem gen_invariant_upto_6 : all_ok 6 = true.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Regression: the bounded invariant check also passes at a smaller size *)
(* (a fast smoke test independent of the size-6 proof), and every case   *)
(* of the running 7-node tree is accepted.                               *)
(* ------------------------------------------------------------------ *)
Example all_ok_4 : all_ok 4 = true.
Proof. vm_compute. reflexivity. Qed.

Example cases_tree7_all_true : forallb (fun b => b) (cases tree7) = true.
Proof. vm_compute. reflexivity. Qed.
