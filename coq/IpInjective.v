(* IpInjective.v
   The inorder-preorder encoding is injective, for all n: distinct trees have
   distinct i-p sequences.  With ReconstructFull.reconstruct_correct_all (the
   reconstruction rebuilds a tree's child relation, for all n) this gives the
   i-p <-> tree correspondence as a genuine bijection -- the mathematical core
   of the construction's reversibility -- for every n, axiom-free.

   This complements the codeword bijection of Codewords.v (decode_encode /
   encode_decode / bijection_decode_encode), which is the height-recurrence
   encoding; here it is the i-p sequence itself.  The reversible-construction
   note had this for the i-p side only by exhaustion (n <= 9, via an external
   interpreter); the injectivity is now proved for all n.

   Build:  rocq c Trees.v Dictionary.v Reconstruct.v ReconstructRight.v
                  ReconstructInvariant.v ReconstructFull.v   (first)
           rocq c IpInjective.v
   Rocq Prover 9.1.0.  Standard library only; axiom-free. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import Trees.
Require Import Dictionary.
Require Import Reconstruct.
Require Import ReconstructFull.

(* Two concatenations with equal-length first parts split the same way. *)
Lemma app_eq_len : forall (a c b d : list nat),
  length a = length c -> a ++ b = c ++ d -> a = c /\ b = d.
Proof.
  induction a as [|x a IH]; intros c b d Hlen Happ.
  - destruct c as [|y c]; simpl in Hlen; [ simpl in Happ; auto | discriminate ].
  - destruct c as [|y c]; simpl in Hlen; [ discriminate |].
    simpl in Happ. injection Happ as Hxy Happ'. injection Hlen as Hlen'.
    destruct (IH c b d Hlen' Happ') as [Hac Hbd]. subst. auto.
Qed.

(* The preorder listing of inorder ranks is injective at every offset:
   the first label fixes the size of the left subtree, which splits the rest. *)
Lemma ipo_inj : forall t1 t2 off, ipo off t1 = ipo off t2 -> t1 = t2.
Proof.
  induction t1 as [|l1 IHl1 r1 IHr1]; intros t2 off H.
  - destruct t2 as [|l2 r2]; [reflexivity|]. rewrite ipo_cons in H. discriminate.
  - destruct t2 as [|l2 r2].
    + rewrite ipo_cons in H. discriminate.
    + rewrite !ipo_cons in H. injection H as Hhd Htl.
      assert (Hsz : size l1 = size l2) by lia.
      assert (Hlen : length (ipo off l1) = length (ipo off l2))
        by (rewrite !ipo_length; exact Hsz).
      rewrite Hsz in Htl.
      destruct (app_eq_len _ _ _ _ Hlen Htl) as [Hl Hr].
      apply IHl1 in Hl. apply IHr1 in Hr. subst. reflexivity.
Qed.

(* For all n: distinct trees have distinct i-p sequences. *)
Theorem ip_injective : forall t1 t2, ip t1 = ip t2 -> t1 = t2.
Proof. intros t1 t2 H. apply (ipo_inj t1 t2 0). exact H. Qed.

(* The i-p sequence determines the tree: ip t1 = ip t2 <-> t1 = t2. *)
Corollary ip_iff : forall t1 t2, ip t1 = ip t2 <-> t1 = t2.
Proof. intros t1 t2. split; [apply ip_injective | intro; subst; reflexivity]. Qed.

(* The reversible round trip, for all n.  Encoding (ip) is injective, and the
   reconstruction (run) inverts it: run (ip t) rebuilds t's whole child relation
   (ReconstructFull.reconstruct_correct_all).  So tree |-> ip t |-> run (ip t)
   recovers t for every tree, and distinct trees never collide. *)
Theorem ip_roundtrip : forall t,
  (forall p, In p (child_assoc 0 t) -> run (ip t) (fst p) = snd p)   (* run inverts ip *)
  /\ (forall u, ip u = ip t -> u = t).                              (* ip is injective *)
Proof.
  intro t. split.
  - intros p Hin. exact (reconstruct_correct_all t p Hin).
  - intros u Hu. apply ip_injective. exact Hu.
Qed.

Print Assumptions ip_injective.
Print Assumptions ip_roundtrip.

(* ------------------------------------------------------------------ *)
(* Regression: distinct trees get distinct codes (a concrete instance   *)
(* of ip_injective's contrapositive), and run inverts ip on the running  *)
(* 7-node example, recovering node 4's children (1,6).                   *)
(* ------------------------------------------------------------------ *)
Example ip_distinct_t4_tree7 : ip t4 <> ip tree7.
Proof. vm_compute. discriminate. Qed.

Example run_inverts_ip_tree7_node4 : run (ip tree7) 4 = (Some 1, Some 6).
Proof. vm_compute. reflexivity. Qed.
