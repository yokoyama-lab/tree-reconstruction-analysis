(** * Stack reconstruction invariant

    Theme 7 / draft A2 (reversible_construction.tex), mechanisation on top of
    [Codewords.v] (Rocq 9.1).

    The iterative constructor keeps a stack of the nodes still eligible to
    receive a right child.  The paper's stack-reconstruction invariant
    (Lemma "Stack reconstruction invariant") states that this stack is, at
    every step boundary, a *function of the partially built tree*: it is the
    chain

        u_1 = bottom of the right spine of the root,
        u_{j+1} = bottom of the right spine of u_j's left subtree,

    stopping at the first node whose left subtree is empty.  Consequently the
    stack carries no information of its own -- it is recomputable from the
    output tree -- which is the garbage-freeness of the reversible round trip,
    and its length is exactly the final stack height [rem t = n - S].

    The development of [Codewords.v] is functional (a structural encoder/
    decoder, no explicit stack), so we mechanise the *tree-intrinsic* content
    of the invariant: we define the chain structurally as [chain t], prove it
    obeys the geometric right-spine-bottom recursion ([chain_rsb]), and prove
    its length equals [rem t] ([chain_length_rem]), the final stack height
    ([chain_length_final_h]), and [n - S] ([chain_length_n_minus_S]).

    Closed with Qed, no Admitted / Axiom (see [Print Assumptions] at the end). *)

Require Import List Arith Lia.
Import ListNotations.
Require Import Codewords.

(* ===================================================================== *)
(** ** The chain of nested right-spine bottoms *)
(* ===================================================================== *)

(** Left-subtree projection. *)
Definition leftsub (t : tree) : tree :=
  match t with Leaf => Leaf | Node l _ => l end.

(** Bottom node of the right spine of [t], returned as the subtree rooted
    there.  Identity on [Leaf], where it is never used.  The recursion is
    structural on the right child [r]. *)
Fixpoint rsb (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l r =>
      match r with
      | Leaf => Node l Leaf
      | Node _ _ => rsb r
      end
  end.

(** The reconstruction stack as the list of still-open subtrees, from bottom
    (the root's right-spine bottom) to top: the nested-right-spine-bottom
    chain of [t].  The three cases mirror the stack semantics directly --
    a node with an empty right subtree is open and we descend into its left
    subtree; a node with a right subtree was popped, so we skip to it. *)
Fixpoint chain (t : tree) : list tree :=
  match t with
  | Leaf => []
  | Node L r =>
      match r with
      | Leaf => Node L Leaf :: chain L
      | Node _ _ => chain r
      end
  end.

Lemma chain_NodeLeaf : forall L, chain (Node L Leaf) = Node L Leaf :: chain L.
Proof. reflexivity. Qed.

Lemma chain_NodeRight : forall L RL RR,
  chain (Node L (Node RL RR)) = chain (Node RL RR).
Proof. reflexivity. Qed.

(* ===================================================================== *)
(** ** [rem] on the two relevant tree shapes *)
(* ===================================================================== *)

(** From the encoder equations of [Codewords.v]: a node with an empty right
    subtree adds one to the count, a node with a right subtree inherits the
    count of that subtree. *)

Lemma rem_NodeLeaf : forall L, rem (Node L Leaf) = S (rem L).
Proof.
  intro L. destruct L as [|LL LR].
  - destruct encode_LL as [_ Hr]. rewrite Hr. reflexivity.
  - destruct (encode_NL (Node LL LR) ltac:(discriminate)) as [_ Hr].
    rewrite Hr. lia.
Qed.

Lemma rem_NodeRight : forall L R, R <> Leaf -> rem (Node L R) = rem R.
Proof.
  intros L R HR. destruct L as [|LL LR].
  - destruct (encode_LN R HR) as [_ Hr]. exact Hr.
  - destruct (encode_NN (Node LL LR) R ltac:(discriminate) HR) as [_ Hr]. exact Hr.
Qed.

(* ===================================================================== *)
(** ** Main invariant: the stack length is [rem t] *)
(* ===================================================================== *)

(** Tree-intrinsic form of the stack-reconstruction invariant: the length of
    the open-node chain equals [rem t], the number of nodes left on the stack.
    Since [chain] is a function of the tree, the stack is a function of the
    tree. *)
Theorem chain_length_rem : forall t, length (chain t) = rem t.
Proof.
  induction t as [|L IHL R IHR].
  - reflexivity.
  - destruct R as [|RL RR].
    + rewrite chain_NodeLeaf. simpl length.
      rewrite rem_NodeLeaf, IHL. reflexivity.
    + rewrite chain_NodeRight. rewrite rem_NodeRight by discriminate. exact IHR.
Qed.

(** The chain length is the final stack height [final_h 1 (encode t)]. *)
Corollary chain_length_final_h : forall t, t <> Leaf ->
  length (chain t) = final_h 1 (encode t).
Proof.
  intros t Hne. rewrite chain_length_rem. symmetry. apply final_h_encode. exact Hne.
Qed.

(** Conservation law in chain form: (open nodes) + (total pops S) = n.
    Here [sumw (encode t)] is [S] and [size t] is [n]. *)
Corollary chain_length_n_minus_S : forall t, t <> Leaf ->
  length (chain t) + sumw (encode t) = size t.
Proof.
  intros t Hne.
  pose proof (height_eq_n_minus_S (encode t) (valid_encode t Hne)) as H.
  pose proof (length_encode t Hne) as HL.
  rewrite chain_length_final_h by exact Hne.
  lia.
Qed.

(* ===================================================================== *)
(** ** Bridge to the geometric definition (right-spine bottoms) *)
(* ===================================================================== *)

(** [rsb] of a node is a node. *)
Lemma rsb_not_leaf : forall r l, rsb (Node l r) <> Leaf.
Proof.
  induction r as [|rl IHrl rr IHrr]; intro l; simpl.
  - discriminate.
  - apply IHrr.
Qed.

(** The structurally-defined [chain] obeys exactly the paper's geometric
    recursion: the head is the bottom of the right spine of [t], and the rest
    is the chain of the left subtree of that bottom node, terminating when
    that left subtree is empty.  This certifies that [chain] *is* the
    nested-right-spine-bottom chain. *)
Lemma chain_rsb : forall t, t <> Leaf ->
  chain t = rsb t :: chain (leftsub (rsb t)).
Proof.
  induction t as [|L IHL R IHR]; intro Hne.
  - congruence.
  - destruct R as [|RL RR].
    + rewrite chain_NodeLeaf. reflexivity.
    + rewrite chain_NodeRight.
      change (rsb (Node L (Node RL RR))) with (rsb (Node RL RR)).
      apply IHR. discriminate.
Qed.

(* ===================================================================== *)
(** ** Examples (the worked trees of reversible_construction.tex) *)
(* ===================================================================== *)

(** The left chain of 3 nodes keeps all 3 on the stack: chain length 3. *)
Example chain_len_00 : length (chain (decode [0;0])) = 3.
Proof. reflexivity. Qed.

(** decode [0;2] = Node (Node Leaf Leaf) (Node Leaf Leaf): after the double
    pop only the right child remains, so chain length 1. *)
Example chain_len_02 : length (chain (decode [0;2])) = 1.
Proof. reflexivity. Qed.

(** The chain of [decode [0;2]] is the single node that is the output's
    right child, recomputed from the tree alone. *)
Example chain_02 : chain (decode [0;2]) = [Node Leaf Leaf].
Proof. reflexivity. Qed.

(* ===================================================================== *)
(** ** Axiom-freeness *)
(* ===================================================================== *)

Print Assumptions chain_length_rem.
Print Assumptions chain_length_n_minus_S.
Print Assumptions chain_rsb.
