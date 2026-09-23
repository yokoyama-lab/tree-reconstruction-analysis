(* Trees.v
   Theme 7 (formal verification), mechanization part A.
   Basic definitions of binary trees and the P2 structural identity.

   Build:  coqc Trees.v
   Rocq Prover 9.1.1.  Standard library only.
*)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* 1. Basic definitions                                                *)
(* ------------------------------------------------------------------ *)

(* Leaf = empty tree, Node = internal node with two children. *)
Inductive tree : Type :=
| Leaf : tree
| Node : tree -> tree -> tree.

(* size = number of nodes (internal Node constructors). *)
Fixpoint size (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l r => 1 + size l + size r
  end.

(* leaves = number of leaf nodes, i.e. Nodes whose both children are Leaf. *)
Fixpoint leaves (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node Leaf Leaf => 1
  | Node l r => leaves l + leaves r
  end.

(* full = number of nodes with two (non-empty) children. *)
Fixpoint full (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node Leaf Leaf => 0
  | Node Leaf r => full r
  | Node l Leaf => full l
  | Node l r => 1 + full l + full r
  end.

(* unary = number of nodes with exactly one (non-empty) child. *)
Fixpoint unary (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node Leaf Leaf => 0
  | Node Leaf r => 1 + unary r
  | Node l Leaf => 1 + unary l
  | Node l r => unary l + unary r
  end.

(* edges = number of edges = number of non-empty children links. *)
Fixpoint edges (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l r =>
      (match l with Leaf => 0 | _ => 1 end) +
      (match r with Leaf => 0 | _ => 1 end) +
      edges l + edges r
  end.

(* ------------------------------------------------------------------ *)
(* Sanity examples                                                     *)
(* ------------------------------------------------------------------ *)

(* A single node:    o            *)
Definition t1 : tree := Node Leaf Leaf.
(* A small tree:
        o
       / \
      o   o
     /
    o
*)
Definition t4 : tree :=
  Node (Node (Node Leaf Leaf) Leaf) (Node Leaf Leaf).

Example size_t4 : size t4 = 4. Proof. reflexivity. Qed.
Example leaves_t4 : leaves t4 = 2. Proof. reflexivity. Qed.
Example full_t4 : full t4 = 1. Proof. reflexivity. Qed.
Example unary_t4 : unary t4 = 1. Proof. reflexivity. Qed.
Example edges_t4 : edges t4 = 3. Proof. reflexivity. Qed.

(* Every node is exactly one of: leaf node, unary node, full node. *)
Lemma classify_size : forall t, size t = leaves t + unary t + full t.
Proof.
  induction t as [| l IHl r IHr]; [reflexivity|].
  destruct l; destruct r; simpl in *; lia.
Qed.

(* edges = size - 1 for a non-empty tree (number of links). *)
Lemma edges_size : forall t, t <> Leaf -> edges t + 1 = size t.
Proof.
  induction t as [| l IHl r IHr]; [congruence|].
  intros _.
  destruct l as [|ll lr]; destruct r as [|rl rr]; simpl in *.
  - reflexivity.
  - specialize (IHr ltac:(discriminate)). simpl in IHr. lia.
  - specialize (IHl ltac:(discriminate)). simpl in IHl. lia.
  - specialize (IHl ltac:(discriminate)).
    specialize (IHr ltac:(discriminate)). simpl in *. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. P2 identity:  for a non-empty tree,  full t + 1 = leaves t.      *)
(*    ("Two children = leaves - 1")                                    *)
(* ------------------------------------------------------------------ *)

Lemma P2_identity : forall t, t <> Leaf -> full t + 1 = leaves t.
Proof.
  induction t as [| l IHl r IHr]; [congruence|].
  intros _.
  destruct l as [|ll lr]; destruct r as [|rl rr]; simpl in *.
  - (* both children empty: leaf node *) reflexivity.
  - (* only right child non-empty: unary node *)
    specialize (IHr ltac:(discriminate)). simpl in IHr. lia.
  - (* only left child non-empty *)
    specialize (IHl ltac:(discriminate)). simpl in IHl. lia.
  - (* both children non-empty: full node *)
    specialize (IHl ltac:(discriminate)).
    specialize (IHr ltac:(discriminate)). simpl in *. lia.
Qed.
