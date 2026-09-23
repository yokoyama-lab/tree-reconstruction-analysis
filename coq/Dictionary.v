(* Dictionary.v
   Theme 7 (formal verification), mechanization part A.
   The i-p sequence (inorder labels listed in preorder) and the
   "dictionary" / grafting-criterion theorems.

   Build:  coqc Trees.v   (first)
           coqc Dictionary.v
   Rocq Prover 9.1.1.  Standard library only.
*)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Permutation.
Import ListNotations.

Require Import Trees.

(* ------------------------------------------------------------------ *)
(* 3. The i-p sequence                                                 *)
(* ------------------------------------------------------------------ *)

(* ipo off t : inorder labels of t, listed in PREORDER, where [off] is
   the number of nodes that precede t in the global inorder.
   The current node's inorder number is  off + size l. *)
Fixpoint ipo (off : nat) (t : tree) : list nat :=
  match t with
  | Leaf => []
  | Node l r =>
      (off + size l)
        :: ipo off l
        ++ ipo (off + size l + 1) r
  end.

Definition ip (t : tree) : list nat := ipo 0 t.

(* small examples *)
(*  t4:
         o (label 2)
        / \
 (l) o     o (label 3)
    /
   o (label 0)   -- wait, recompute below
*)
Example ip_t1 : ip t1 = [0]. Proof. reflexivity. Qed.
Example ip_t4 : ip t4 = [2;1;0;3].
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Basic facts about ipo                                               *)
(* ------------------------------------------------------------------ *)

Lemma ipo_length : forall t off, length (ipo off t) = size t.
Proof.
  induction t as [| l IHl r IHr]; intro off; [reflexivity|].
  simpl. rewrite length_app, IHl, IHr. lia.
Qed.

Lemma ip_length : forall t, length (ip t) = size t.
Proof. intro t. apply ipo_length. Qed.

(* Shifting the offset shifts every label by the same amount. *)
Lemma ipo_shift : forall t off k,
  ipo (off + k) t = map (fun x => x + k) (ipo off t).
Proof.
  induction t as [| l IHl r IHr]; intros off k; [reflexivity|].
  simpl. rewrite map_app. f_equal.
  - lia.
  - f_equal.
    + (* left subtree *)
      apply IHl.
    + (* right subtree: offset (off+k) + size l + 1 *)
      replace (off + k + size l + 1) with ((off + size l + 1) + k) by lia.
      apply IHr.
Qed.

(* Every label produced by ipo off t lies in [off, off + size t). *)
Lemma ipo_bounds : forall t off x,
  In x (ipo off t) -> off <= x < off + size t.
Proof.
  induction t as [| l IHl r IHr]; intros off x H; [destruct H|].
  simpl in H. destruct H as [H | H].
  - subst. simpl. lia.
  - apply in_app_or in H. destruct H as [H | H].
    + apply IHl in H. simpl. lia.
    + apply IHr in H. simpl. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* NoDup and permutation of seq                                        *)
(* ------------------------------------------------------------------ *)

Lemma ipo_NoDup : forall t off, NoDup (ipo off t).
Proof.
  induction t as [| l IHl r IHr]; intro off.
  - constructor.
  - simpl. constructor.
    + (* off + size l not in the two subtree lists *)
      intro Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * apply ipo_bounds in Hin. lia.
      * apply ipo_bounds in Hin. lia.
    + (* NoDup of the concatenation: ranges disjoint *)
      apply NoDup_app.
      * apply IHl.
      * apply IHr.
      * intros x Hl Hr.
        apply ipo_bounds in Hl. apply ipo_bounds in Hr. lia.
        (* NoDup_app expects: forall a, In a l1 -> ~ In a l2 *)
Qed.

(* The set of labels of ipo off t is exactly { off, ..., off+size t-1 }. *)
Lemma ipo_in_iff : forall t off x,
  In x (ipo off t) <-> off <= x < off + size t.
Proof.
  induction t as [| l IHl r IHr]; intros off x.
  - simpl. split; [intro H; destruct H | lia].
  - simpl. split.
    + intro H. destruct H as [H | H].
      * subst. lia.
      * apply in_app_or in H. destruct H as [H | H].
        -- apply IHl in H. lia.
        -- apply IHr in H. lia.
    + intro H.
      (* decide whether x is the root label, in left, or in right range *)
      destruct (Nat.eq_dec x (off + size l)) as [Heq | Hne].
      * left. lia.
      * right. apply in_or_app.
        destruct (lt_dec x (off + size l)) as [Hlt | Hge].
        -- left. apply IHl. lia.
        -- right. apply IHr. lia.
Qed.

(* ip t is a permutation of seq 0 (size t). *)
Lemma ipo_Permutation_seq : forall t off,
  Permutation (ipo off t) (seq off (size t)).
Proof.
  intros t off.
  apply NoDup_Permutation.
  - apply ipo_NoDup.
  - apply seq_NoDup.
  - intro x. rewrite ipo_in_iff. rewrite in_seq. lia.
Qed.

Theorem ip_Permutation_seq : forall t,
  Permutation (ip t) (seq 0 (size t)).
Proof. intro t. apply ipo_Permutation_seq. Qed.

Theorem ip_NoDup : forall t, NoDup (ip t).
Proof. intro t. apply ipo_NoDup. Qed.

(* ================================================================== *)
(* 4. Dictionary / grafting-criterion theorems                        *)
(* ================================================================== *)

(* root_label off t = inorder label of the root of a non-empty t. *)
Definition root_label (off : nat) (t : tree) : nat :=
  match t with
  | Leaf => 0          (* unused for Leaf *)
  | Node l _ => off + size l
  end.

(* The head of ipo off t (for non-empty t) is the root label. *)
Lemma ipo_hd_error : forall t off,
  t <> Leaf -> hd_error (ipo off t) = Some (root_label off t).
Proof.
  intros t off Hne. destruct t as [|l r]; [congruence|]. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* (4a)  Left-child criterion.                                         *)
(*                                                                     *)
(* We formalise the published Thm 3.1(1): looking at the preorder      *)
(* listing, the node immediately following node a (i.e. the preorder   *)
(* successor) is the LEFT child of a  iff  a's label is greater than    *)
(* the successor's label.                                              *)
(*                                                                     *)
(* "lchild off t a b": in the tree t (labelled from offset off) there  *)
(* is an internal node with label a whose non-empty left subtree has   *)
(* root label b (so b is the left child of a, and b is also the        *)
(* preorder successor of a).                                           *)
(* ------------------------------------------------------------------ *)

Inductive lchild (off : nat) : tree -> nat -> nat -> Prop :=
| lchild_here : forall l r,
    l <> Leaf ->
    lchild off (Node l r) (off + size l) (root_label off l)
| lchild_left : forall l r a b,
    lchild off l a b ->
    lchild off (Node l r) a b
| lchild_right : forall l r a b,
    lchild (off + size l + 1) r a b ->
    lchild off (Node l r) a b.

(* For lchild, b < a always (the left child's inorder label is smaller). *)
Lemma lchild_lt : forall off t a b, lchild off t a b -> b < a.
Proof.
  intros off t a b H. induction H.
  - (* here: root_label off l < off + size l *)
    destruct l as [|ll lr]; [congruence|]. simpl. simpl size. lia.
  - assumption.
  - assumption.
Qed.

(* Adjacency in a list: a is immediately followed by b. *)
Definition Adj (a b : nat) (xs : list nat) : Prop :=
  exists pre suf, xs = pre ++ a :: b :: suf.

Lemma Adj_cons : forall a b x xs,
  Adj a b xs -> Adj a b (x :: xs).
Proof.
  intros a b x xs [pre [suf H]]. exists (x :: pre), suf. simpl. f_equal. exact H.
Qed.

Lemma Adj_head : forall a b suf, Adj a b (a :: b :: suf).
Proof. intros. exists [], suf. reflexivity. Qed.

(* Adjacency across an append boundary: last of l1 then first of l2. *)
Lemma Adj_app_boundary : forall a b l1 l2,
  Adj a b (l1 ++ l2) ->
  Adj a b l1 \/ Adj a b l2 \/
  (exists p, l1 = p ++ [a] /\ exists s, l2 = b :: s).
Proof.
  intros a b l1.
  induction l1 as [| x l1 IH]; intros l2 H.
  - right. left. simpl in H. exact H.
  - simpl in H. destruct H as [pre [suf Heq]].
    destruct pre as [| y pre].
    + (* a = x, and b :: suf = l1 ++ l2 *)
      simpl in Heq. injection Heq as Hax Hrest. subst x.
      destruct l1 as [| z l1].
      * (* l1 empty: a at boundary, l2 = b :: suf *)
        right. right. exists []. split; [reflexivity|].
        exists suf. simpl in Hrest. subst l2. reflexivity.
      * (* l1 = z :: l1; then b = z and l1 ++ l2 = suf *)
        simpl in Hrest. injection Hrest as Hbz Hsuf. subst z.
        left. exists [], l1. reflexivity.
    + (* prefix nonempty *)
      simpl in Heq. injection Heq as Hxy Hrest. subst y.
      assert (Hsub : Adj a b (l1 ++ l2)) by (exists pre, suf; exact Hrest).
      apply IH in Hsub. destruct Hsub as [H1 | [H2 | H3]].
      * left. apply Adj_cons. exact H1.
      * right. left. exact H2.
      * right. right. destruct H3 as [p [Hp Hs]].
        exists (x :: p). split; [simpl; f_equal; exact Hp | exact Hs].
Qed.

(* The head of a non-empty ipo equals root_label, expressed as a cons. *)
Lemma ipo_cons : forall l r off,
  ipo off (Node l r) = (off + size l) :: ipo off l ++ ipo (off + size l + 1) r.
Proof. reflexivity. Qed.

Lemma ipo_nonempty : forall t off, t <> Leaf -> exists x s, ipo off t = x :: s.
Proof.
  intros t off Hne. destruct t as [|l r]; [congruence|].
  simpl. eexists. eexists. reflexivity.
Qed.

(* Direction 1:  lchild  ->  Adj (with a > b). *)
Lemma lchild_Adj : forall off t a b,
  lchild off t a b -> Adj a b (ipo off t).
Proof.
  intros off t a b H. induction H.
  - (* here *)
    rewrite ipo_cons.
    (* root_label off l is head of ipo off l *)
    assert (Hh := ipo_hd_error l off H).
    destruct (ipo_nonempty l off H) as [x [s Hs]].
    rewrite Hs in Hh. simpl in Hh. injection Hh as Hx. subst x.
    rewrite Hs. simpl. exists [], (s ++ ipo (off + size l + 1) r). reflexivity.
  - (* in left subtree *)
    rewrite ipo_cons. apply Adj_cons.
    (* Adj a b (ipo off l ++ ...) *)
    destruct IHlchild as [pre [suf Hpre]].
    exists pre, (suf ++ ipo (off + size l + 1) r).
    rewrite Hpre. rewrite <- !app_assoc. reflexivity.
  - (* in right subtree *)
    rewrite ipo_cons. apply Adj_cons.
    destruct IHlchild as [pre [suf Hpre]].
    exists (ipo off l ++ pre), suf.
    rewrite Hpre. rewrite <- !app_assoc. reflexivity.
Qed.

(* Adjacency in a cons: either it is the head pair, or it is in the tail. *)
Lemma Adj_inv_cons : forall a b x xs,
  Adj a b (x :: xs) ->
  (x = a /\ exists s, xs = b :: s) \/ Adj a b xs.
Proof.
  intros a b x xs [pre [suf Heq]].
  destruct pre as [| y pre].
  - simpl in Heq. injection Heq as Hx Hxs. subst x.
    left. split; [reflexivity|]. exists suf. exact Hxs.
  - simpl in Heq. injection Heq as Hxy Hrest. subst y.
    right. exists pre, suf. exact Hrest.
Qed.

(* Direction 2:  Adj a b (ipo off t)  /\  a > b  ->  lchild off t a b. *)
Lemma Adj_lchild : forall t off a b,
  Adj a b (ipo off t) -> a > b -> lchild off t a b.
Proof.
  induction t as [| l IHl r IHr]; intros off a b Hadj Hgt.
  - (* Leaf: ipo = [], no adjacency *)
    destruct Hadj as [pre [suf Heq]].
    destruct pre; simpl in Heq; discriminate.
  - rewrite ipo_cons in Hadj.
    apply Adj_inv_cons in Hadj.
    destruct Hadj as [[Hxa [s Hs]] | Hadj].
    + (* head pair: a = off + size l, b = head of (ipo off l ++ ipo r) *)
      subst a.
      (* Determine whether l is empty. *)
      destruct l as [|ll lr] eqn:El.
      * (* l = Leaf: head comes from ipo (off+0+1) r, all >= off+1 > a=off *)
        simpl in Hs.
        (* Hs : ipo (off + 0 + 1) r = b :: s *)
        assert (Hin : In b (ipo (off + 0 + 1) r)).
        { rewrite Hs. apply in_eq. }
        apply ipo_bounds in Hin. simpl size in Hgt. lia.
      * (* l nonempty: head of ipo off l ++ ... is head of ipo off l = root_label *)
        assert (Hlne : Node ll lr <> Leaf) by discriminate.
        destruct (ipo_nonempty (Node ll lr) off Hlne) as [x [s' Hs']].
        rewrite Hs' in Hs. simpl in Hs. injection Hs as Hb _. subst b.
        (* x = head of ipo off (Node ll lr) = root_label *)
        assert (Hh := ipo_hd_error (Node ll lr) off Hlne).
        rewrite Hs' in Hh. simpl in Hh. injection Hh as Hx. subst x.
        apply lchild_here. exact Hlne.
    + (* adjacency inside ipo off l ++ ipo (off+size l+1) r *)
      apply Adj_app_boundary in Hadj.
      destruct Hadj as [H1 | [H2 | H3]].
      * apply lchild_left. apply IHl; assumption.
      * apply lchild_right. apply IHr; assumption.
      * (* boundary: last of l is a, first of r is b -> a < b, contradiction *)
        destruct H3 as [p [Hp [s Hs]]].
        assert (HaIn : In a (ipo off l)).
        { rewrite Hp. apply in_or_app. right. apply in_eq. }
        assert (HbIn : In b (ipo (off + size l + 1) r)).
        { rewrite Hs. apply in_eq. }
        apply ipo_bounds in HaIn. apply ipo_bounds in HbIn. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* (4a) MAIN: the left-child / grafting criterion.                     *)
(*                                                                     *)
(* For any two preorder-adjacent labels a, b in ip t:                  *)
(*    a > b   <->   b is the left child of a   (lchild 0 t a b).        *)
(* ------------------------------------------------------------------ *)
Theorem dictionary_left_child : forall t a b,
  Adj a b (ip t) ->
  (a > b <-> lchild 0 t a b).
Proof.
  intros t a b Hadj. unfold ip in *. split.
  - intro Hgt. apply Adj_lchild; assumption.
  - intro Hlc. apply lchild_lt in Hlc. lia.
Qed.

(* Convenience corollary phrased with nth_error positions i, i+1. *)
Theorem dictionary_left_child_nth : forall t i a b,
  nth_error (ip t) i = Some a ->
  nth_error (ip t) (S i) = Some b ->
  (a > b <-> lchild 0 t a b).
Proof.
  intros t i a b Hi Hsi.
  apply dictionary_left_child.
  (* build Adj from the two nth_error facts *)
  unfold Adj. unfold ip in *.
  revert i Hi Hsi.
  generalize (ipo 0 t) as xs. clear t.
  induction xs as [| x xs IH]; intros i Hi Hsi.
  - destruct i; simpl in Hi; discriminate.
  - destruct i as [| i].
    + (* a is head, b is head of xs *)
      simpl in Hi. injection Hi as Ha. subst x.
      simpl in Hsi. destruct xs as [| y ys]; [discriminate|].
      simpl in Hsi. injection Hsi as Hb. subst y.
      exists [], ys. reflexivity.
    + simpl in Hi, Hsi.
      destruct (IH i Hi Hsi) as [pre [suf Heq]].
      exists (x :: pre), suf. simpl. f_equal. exact Heq.
Qed.

(* ------------------------------------------------------------------ *)
(* (4b)  Right-child precedence (theme-4 dictionary (b)).              *)
(*                                                                     *)
(* "has_right_child off t a": tree t (labelled from off) has an        *)
(* internal node with label a whose right subtree is non-empty.        *)
(* ------------------------------------------------------------------ *)

Inductive has_right_child (off : nat) : tree -> nat -> Prop :=
| hrc_here : forall l r,
    r <> Leaf ->
    has_right_child off (Node l r) (off + size l)
| hrc_left : forall l r a,
    has_right_child off l a ->
    has_right_child off (Node l r) a
| hrc_right : forall l r a,
    has_right_child (off + size l + 1) r a ->
    has_right_child off (Node l r) a.

(* "Before x y xs": x occurs in xs strictly before some later y. *)
Definition Before (x y : nat) (xs : list nat) : Prop :=
  exists p m s, xs = p ++ x :: m ++ y :: s.

Lemma Before_cons : forall x y z xs,
  Before x y xs -> Before x y (z :: xs).
Proof.
  intros x y z xs [p [m [s H]]]. exists (z :: p), m, s. simpl. f_equal. exact H.
Qed.

(* If x is in l1 and y is in l2 (the later part), then Before x y (l1++l2). *)
Lemma Before_app_split : forall x y l1 l2,
  In x l1 -> In y l2 -> Before x y (l1 ++ l2).
Proof.
  intros x y l1 l2 Hx Hy.
  apply in_split in Hx. destruct Hx as [p1 [s1 H1]].
  apply in_split in Hy. destruct Hy as [p2 [s2 H2]].
  exists p1, (s1 ++ p2), s2. subst.
  rewrite <- app_assoc. simpl. f_equal. f_equal.
  rewrite <- app_assoc. reflexivity.
Qed.

(* head element case: x is the very first element, y somewhere later. *)
Lemma Before_head : forall x y m s, Before x y (x :: m ++ y :: s).
Proof. intros. exists [], m, s. reflexivity. Qed.

(* The offset itself is a label of any non-empty subtree (its minimum). *)
Lemma off_In_ipo : forall t off, t <> Leaf -> In off (ipo off t).
Proof.
  intros t off Hne. apply ipo_in_iff. destruct t; [congruence|]. simpl. lia.
Qed.

(* Before with x as head and y later in the tail. *)
Lemma Before_head_in : forall x y tl,
  In y tl -> Before x y (x :: tl).
Proof.
  intros x y tl Hy. apply in_split in Hy. destruct Hy as [m [s Htl]].
  exists [], m, s. simpl. f_equal. exact Htl.
Qed.

(* Before inside the left operand of an append. *)
Lemma Before_app_left : forall x y l1 l2,
  Before x y l1 -> Before x y (l1 ++ l2).
Proof.
  intros x y l1 l2 [p [m [s H]]]. exists p, m, (s ++ l2).
  rewrite H. rewrite <- !app_assoc. simpl. f_equal. f_equal.
  rewrite <- !app_assoc. reflexivity.
Qed.

(* Before inside the right operand of an append. *)
Lemma Before_app_right : forall x y l1 l2,
  Before x y l2 -> Before x y (l1 ++ l2).
Proof.
  intros x y l1 l2 [p [m [s H]]]. exists (l1 ++ p), m, s.
  rewrite H. rewrite <- !app_assoc. reflexivity.
Qed.

(* Forward (b):  has_right_child off t a  ->  Before a (a+1) (ipo off t). *)
Lemma hrc_Before : forall t off a,
  has_right_child off t a -> Before a (a + 1) (ipo off t).
Proof.
  intros t off a H. induction H.
  - (* here: a = off+size l, right subtree r nonempty.
       a+1 = off+size l+1 is in ipo (off+size l+1) r (its offset). *)
    rewrite ipo_cons. apply Before_head_in.
    apply in_or_app. right.
    replace (off + size l + 1) with ((off + size l) + 1) by lia.
    apply off_In_ipo. assumption.
  - (* left subtree *)
    rewrite ipo_cons. apply Before_cons.
    apply Before_app_left. exact IHhas_right_child.
  - (* right subtree *)
    rewrite ipo_cons. apply Before_cons.
    apply Before_app_right. exact IHhas_right_child.
Qed.

(* ------------------------------------------------------------------ *)
(* Converse of (b): we prove the complementary "no right child"        *)
(* implies a+1 occurs before a, then combine via NoDup exclusivity.    *)
(* ------------------------------------------------------------------ *)

(* In a list, Before x y implies x is a member. *)
Lemma Before_In_l : forall x y xs, Before x y xs -> In x xs.
Proof.
  intros x y xs [p [m [s H]]]. subst. apply in_or_app. right. apply in_eq.
Qed.

Lemma Before_In_r : forall x y xs, Before x y xs -> In y xs.
Proof.
  intros x y xs [p [m [s H]]]. subst.
  apply in_or_app. right. right. apply in_or_app. right. apply in_eq.
Qed.

(* Inversion of Before on a cons. *)
Lemma Before_cons_inv : forall x y c xs,
  Before x y (c :: xs) ->
  (c = x /\ In y xs) \/ Before x y xs.
Proof.
  intros x y c xs [p [m [s H]]].
  destruct p as [| d p].
  - simpl in H. injection H as Hcx Hrest. subst c.
    left. split; [reflexivity|]. rewrite Hrest.
    apply in_or_app. right. apply in_eq.
  - simpl in H. injection H as Hcd Hrest. subst d.
    right. exists p, m, s. exact Hrest.
Qed.

(* Exclusivity: a NoDup list cannot witness both orders. *)
Lemma Before_NoDup_excl : forall xs x y,
  NoDup xs -> Before x y xs -> ~ Before y x xs.
Proof.
  induction xs as [| c xs IH]; intros x y Hnd Hxy Hyx.
  - destruct Hxy as [p [m [s H]]]. destruct p; discriminate.
  - inversion Hnd as [| c' xs' Hnotin Hnd' [Hc Hxs]]; subst.
    (* Analyse the heads of the two Before witnesses. *)
    apply Before_cons_inv in Hxy.
    apply Before_cons_inv in Hyx.
    destruct Hxy as [[Hcx Hyin] | Hxy]; destruct Hyx as [[Hcy Hxin] | Hyx].
    + (* c = x and c = y : then x = y; Before y x gives In x xs and In y xs;
         but x=c=y =>  c in xs contradicts Hnotin (In y xs). *)
      subst c. (* x = y *)
      (* Hxin : In x xs (from y::... ) but with c=y=x; Hnotin: ~In c xs *)
      rewrite <- Hcy in *. (* keep *) 
      apply Hnotin. exact Hxin.
    + (* c = x, Hyin: In y xs ; Hyx: Before y x xs. Then x = c in xs via Before_In_r Hyx *)
      subst c.
      apply Before_In_r in Hyx. (* In x xs *)
      apply Hnotin. exact Hyx.
    + (* c = y, Hxy: Before x y xs ; then y = c in xs via Before_In_r Hxy *)
      subst c.
      apply Before_In_r in Hxy. (* In y xs *)
      apply Hnotin. exact Hxy.
    + (* both in tail *)
      apply (IH x y Hnd' Hxy Hyx).
Qed.

(* If a has NO right child, then a+1 appears before a (its inorder
   successor is an ancestor, listed earlier in preorder). *)
Lemma no_hrc_Before : forall t off a,
  ~ has_right_child off t a ->
  off <= a ->
  a + 1 < off + size t ->
  Before (a + 1) a (ipo off t).
Proof.
  induction t as [| l IHl r IHr]; intros off a Hnhrc Hlo Hhi.
  - (* Leaf: size 0, a+1 < off impossible *)
    simpl in Hhi. lia.
  - rewrite ipo_cons.
    simpl size in Hhi.
    set (m := off + size l) in *.
    destruct (lt_eq_lt_dec a m) as [[Hlt | Heq] | Hgt].
    + (* a < m : a in left part *)
      destruct (Nat.eq_dec (a + 1) m) as [Hp1 | Hp1].
      * (* a+1 = m = head : Before m a, a in left list *)
        rewrite Hp1. apply Before_head_in.
        apply in_or_app. left. apply ipo_in_iff. unfold m in *. lia.
      * (* a+1 < m : both in left list, recurse *)
        apply Before_cons. apply Before_app_left.
        apply IHl.
        -- intro Hl. apply Hnhrc. apply hrc_left. exact Hl.
        -- exact Hlo.
        -- unfold m in *. lia.
    + (* a = m : root. Since no right child here, r = Leaf, so size r = 0,
         making a+1 = m+1 = off+size t, contradicting Hhi. *)
      exfalso. subst a.
      destruct r as [|rl rr] eqn:Er.
      * unfold m in Hhi. simpl size in Hhi. lia.
      * apply Hnhrc. unfold m. apply hrc_here. discriminate.
    + (* a > m : a in right part *)
      apply Before_cons. apply Before_app_right.
      replace m with (off + size l) in * by reflexivity.
      apply IHr.
      * intro Hr. apply Hnhrc. apply hrc_right. exact Hr.
      * unfold m in Hgt. lia.
      * unfold m in *. lia.
Qed.

(* has_right_child is decidable (constructive, no axioms). *)
Lemma hrc_dec : forall t off a,
  {has_right_child off t a} + {~ has_right_child off t a}.
Proof.
  induction t as [| l IHl r IHr]; intros off a.
  - (* Leaf: never *)
    right. intro H. inversion H.
  - destruct (IHl off a) as [Hl | Hl].
    { left. apply hrc_left. exact Hl. }
    destruct (IHr (off + size l + 1) a) as [Hr | Hr].
    { left. apply hrc_right. exact Hr. }
    (* check the "here" case: a = off+size l and r <> Leaf *)
    destruct (Nat.eq_dec a (off + size l)) as [Heq | Hne].
    + destruct r as [|rl rr] eqn:Er.
      * (* r = Leaf: no here, no left, no right *)
        right. intro H. inversion H; subst.
        -- congruence.
        -- apply Hl. assumption.
        -- apply Hr. assumption.
      * left. subst a. apply hrc_here. discriminate.
    + right. intro H. inversion H; subst.
      * congruence.
      * apply Hl. assumption.
      * apply Hr. assumption.
Qed.

(* Converse of (b):  Before a (a+1) (ipo off t) -> has_right_child off t a. *)
Lemma Before_hrc : forall t off a,
  off <= a ->
  a + 1 < off + size t ->
  Before a (a + 1) (ipo off t) ->
  has_right_child off t a.
Proof.
  intros t off a Hlo Hhi HB.
  destruct (hrc_dec t off a) as [Hyes | Hno].
  - exact Hyes.
  - exfalso.
    assert (HB' : Before (a + 1) a (ipo off t))
      by (apply no_hrc_Before; assumption).
    apply (Before_NoDup_excl (ipo off t) a (a + 1)).
    + apply ipo_NoDup.
    + exact HB.
    + exact HB'.
Qed.

(* ------------------------------------------------------------------ *)
(* (4b) MAIN: right-child precedence.                                  *)
(*                                                                     *)
(* For a label a with a+1 <= size t - 1 (i.e. a+1 < size t):           *)
(*    node a has a right child  <->  a precedes a+1 in ip t.           *)
(* ------------------------------------------------------------------ *)
Theorem dictionary_right_child : forall t a,
  a + 1 < size t ->
  (has_right_child 0 t a <-> Before a (a + 1) (ip t)).
Proof.
  intros t a Hsz. unfold ip. split.
  - intro H. apply hrc_Before. exact H.
  - intro H. apply Before_hrc; [lia | lia | exact H].
Qed.

(* ------------------------------------------------------------------ *)
(* (4c)  Left-child EXISTENCE condition (dual of (4b)).                *)
(*                                                                     *)
(* The mirror image of the right-child condition: node a has a LEFT    *)
(* child iff a precedes its inorder predecessor a-1 in ip t; equiv-    *)
(* alently (the dual of the paper's right-child condition) a has a     *)
(* left child iff a-1 has NO right child.  Proved from scratch by      *)
(* mirroring the has_right_child development; axiom-free.              *)
(* ------------------------------------------------------------------ *)

(* "has_left_child off t a": tree t (labelled from off) has an         *)
(* internal node with label a whose left subtree is non-empty.         *)
Inductive has_left_child (off : nat) : tree -> nat -> Prop :=
| hlc_here : forall l r,
    l <> Leaf ->
    has_left_child off (Node l r) (off + size l)
| hlc_left : forall l r a,
    has_left_child off l a ->
    has_left_child off (Node l r) a
| hlc_right : forall l r a,
    has_left_child (off + size l + 1) r a ->
    has_left_child off (Node l r) a.

(* Forward:  has_left_child off t a  ->  Before a (a-1) (ipo off t). *)
Lemma hlc_Before : forall t off a,
  has_left_child off t a -> Before a (a - 1) (ipo off t).
Proof.
  intros t off a H. induction H.
  - (* here: a = off+size l, left subtree l nonempty.
       a-1 = off+size l-1 is the maximum label of ipo off l. *)
    rewrite ipo_cons. apply Before_head_in.
    apply in_or_app. left. apply ipo_in_iff.
    destruct l as [|ll lr]; [congruence|]. simpl size. lia.
  - (* left subtree *)
    rewrite ipo_cons. apply Before_cons.
    apply Before_app_left. exact IHhas_left_child.
  - (* right subtree *)
    rewrite ipo_cons. apply Before_cons.
    apply Before_app_right. exact IHhas_left_child.
Qed.

(* If a has NO left child, then a-1 appears before a (its inorder
   predecessor is an ancestor, listed earlier in preorder). *)
Lemma no_hlc_Before : forall t off a,
  ~ has_left_child off t a ->
  off + 1 <= a ->
  a < off + size t ->
  Before (a - 1) a (ipo off t).
Proof.
  induction t as [| l IHl r IHr]; intros off a Hnhlc Hlo Hhi.
  - simpl in Hhi. lia.
  - rewrite ipo_cons.
    simpl size in Hhi.
    set (m := off + size l) in *.
    destruct (lt_eq_lt_dec a m) as [[Hlt | Heq] | Hgt].
    + (* a < m : a (and a-1) in left part, recurse *)
      apply Before_cons. apply Before_app_left.
      apply IHl.
      * intro Hl. apply Hnhlc. apply hlc_left. exact Hl.
      * exact Hlo.
      * unfold m in Hlt. lia.
    + (* a = m : root.  No left child here => l = Leaf => size l = 0
         => a = off, contradicting off+1 <= a. *)
      exfalso. subst a.
      destruct l as [|ll lr] eqn:El.
      * unfold m in Hlo. simpl size in Hlo. lia.
      * apply Hnhlc. unfold m. apply hlc_here. discriminate.
    + (* a > m : a in right part *)
      destruct (Nat.eq_dec (a - 1) m) as [Hp1 | Hp1].
      * (* a-1 = m = head : Before m a, a in right list *)
        rewrite Hp1. apply Before_head_in.
        apply in_or_app. right.
        apply ipo_in_iff. unfold m in *. lia.
      * (* a-1 > m : both in right list, recurse *)
        apply Before_cons. apply Before_app_right.
        apply IHr.
        -- intro Hr. apply Hnhlc. apply hlc_right. exact Hr.
        -- unfold m in *. lia.
        -- unfold m in *. lia.
Qed.

(* has_left_child is decidable (constructive, no axioms). *)
Lemma hlc_dec : forall t off a,
  {has_left_child off t a} + {~ has_left_child off t a}.
Proof.
  induction t as [| l IHl r IHr]; intros off a.
  - right. intro H. inversion H.
  - destruct (IHl off a) as [Hl | Hl].
    { left. apply hlc_left. exact Hl. }
    destruct (IHr (off + size l + 1) a) as [Hr | Hr].
    { left. apply hlc_right. exact Hr. }
    destruct (Nat.eq_dec a (off + size l)) as [Heq | Hne].
    + destruct l as [|ll lr] eqn:El.
      * (* l = Leaf: no here, no left, no right *)
        right. intro H. inversion H; subst.
        -- congruence.
        -- apply Hl. assumption.
        -- apply Hr. assumption.
      * left. subst a. apply hlc_here. discriminate.
    + right. intro H. inversion H; subst.
      * congruence.
      * apply Hl. assumption.
      * apply Hr. assumption.
Qed.

(* Converse:  Before a (a-1) (ipo off t)  ->  has_left_child off t a. *)
Lemma Before_hlc : forall t off a,
  off + 1 <= a ->
  a < off + size t ->
  Before a (a - 1) (ipo off t) ->
  has_left_child off t a.
Proof.
  intros t off a Hlo Hhi HB.
  destruct (hlc_dec t off a) as [Hyes | Hno].
  - exact Hyes.
  - exfalso.
    assert (HB' : Before (a - 1) a (ipo off t))
      by (apply no_hlc_Before; assumption).
    apply (Before_NoDup_excl (ipo off t) a (a - 1)).
    + apply ipo_NoDup.
    + exact HB.
    + exact HB'.
Qed.

(* In a NoDup list, of two distinct members one precedes the other. *)
Lemma Before_total : forall xs x y,
  In x xs -> In y xs -> x <> y -> Before x y xs \/ Before y x xs.
Proof.
  induction xs as [| c xs IH]; intros x y Hx Hy Hneq.
  - destruct Hx.
  - simpl in Hx, Hy.
    destruct Hx as [Hcx | Hx].
    + subst c. destruct Hy as [Hcy | Hy]; [subst; congruence|].
      left. apply Before_head_in. exact Hy.
    + destruct Hy as [Hcy | Hy].
      * subst c. right. apply Before_head_in. exact Hx.
      * destruct (IH x y Hx Hy Hneq) as [H | H]; [left | right];
          apply Before_cons; exact H.
Qed.

(* ------------------------------------------------------------------ *)
(* (4c) MAIN: left-child existence, precedence form.                   *)
(*                                                                     *)
(* For a label a with 1 <= a < size t:                                 *)
(*    node a has a left child  <->  a precedes a-1 in ip t.            *)
(* ------------------------------------------------------------------ *)
Theorem dictionary_left_child_exist : forall t a,
  1 <= a ->
  a < size t ->
  (has_left_child 0 t a <-> Before a (a - 1) (ip t)).
Proof.
  intros t a Hge Hsz. unfold ip. split.
  - intro H. apply hlc_Before. exact H.
  - intro H. apply Before_hlc; [lia | lia | exact H].
Qed.

(* ------------------------------------------------------------------ *)
(* (4c') The paper's dual: a has a left child  <->  a-1 has no right   *)
(* child.  Obtained by combining (4c) and (4b) via NoDup totality.     *)
(* ------------------------------------------------------------------ *)
Corollary left_child_iff_no_right : forall t a,
  1 <= a -> a < size t ->
  (has_left_child 0 t a <-> ~ has_right_child 0 t (a - 1)).
Proof.
  intros t a Hge Hsz.
  assert (Hlc : has_left_child 0 t a <-> Before a (a - 1) (ip t))
    by (apply dictionary_left_child_exist; lia).
  assert (Hrc : has_right_child 0 t (a - 1) <-> Before (a - 1) a (ip t)).
  { assert (Htmp := dictionary_right_child t (a - 1) ltac:(lia)).
    replace (a - 1 + 1) with a in Htmp by lia. exact Htmp. }
  split.
  - intros Hl Hr.
    apply Hlc in Hl. apply Hrc in Hr.
    apply (Before_NoDup_excl (ip t) a (a - 1)).
    + unfold ip. apply ipo_NoDup.
    + exact Hl.
    + exact Hr.
  - intro Hnr. apply Hlc.
    assert (Hina : In a (ip t)) by (unfold ip; apply ipo_in_iff; lia).
    assert (Hinb : In (a - 1) (ip t)) by (unfold ip; apply ipo_in_iff; lia).
    destruct (Before_total (ip t) a (a - 1) Hina Hinb ltac:(lia)) as [H | H].
    + exact H.
    + exfalso. apply Hnr. apply Hrc. exact H.
Qed.

(* ================================================================== *)
(* 5. Worked examples / sanity checks                                  *)
(* ================================================================== *)

(* t4 = Node (Node (Node Leaf Leaf) Leaf) (Node Leaf Leaf)
   ip t4 = [2;1;0;3].  Inorder labels:
     root = 2, its left subtree {0,1}, right subtree {3}. *)
Compute (ip t4).                       (* = [2;1;0;3] *)
Compute (size t4).                     (* = 4 *)

(* (4a): 2 > 1 and node 1 is the left child of node 2. *)
Example ex_left_child_2_1 : lchild 0 t4 2 1.
Proof.
  apply (dictionary_left_child t4 2 1).
  - exists [], [0;3]. reflexivity.   (* Adj 2 1 (ip t4) *)
  - lia.
Qed.

(* 1 > 0 and node 0 is the left child of node 1. *)
Example ex_left_child_1_0 : lchild 0 t4 1 0.
Proof.
  apply (dictionary_left_child t4 1 0).
  - exists [2], [3]. reflexivity.
  - lia.
Qed.

(* (4b): node 2 has a right child (node 3), and 2 precedes 3 in ip t4. *)
Example ex_right_child_2 : has_right_child 0 t4 2.
Proof.
  apply (dictionary_right_child t4 2).
  - simpl. lia.
  - exists [], [1;0], []. reflexivity.   (* Before 2 3 (ip t4) = [2;1;0;3] *)
Qed.

(* Node 0 has NO right child: 0 does NOT precede 1 in ip t4 = [2;1;0;3]
   (1 comes before 0). *)
Example ex_no_right_child_0 : ~ has_right_child 0 t4 0.
Proof.
  intro H.
  apply (dictionary_right_child t4 0) in H; [| simpl; lia].
  (* H : Before 0 1 (ip t4); but 1 precedes 0, so excluded *)
  apply (Before_NoDup_excl (ip t4) 0 1).
  - apply ip_NoDup.
  - exact H.
  - exists [2], [], [3]. reflexivity.   (* Before 1 0 (ip t4) = [2;1;0;3] *)
Qed.

(* (4c): node 2 has a LEFT child (node 1), and 2 precedes 2-1=1 in ip t4. *)
Example ex_has_left_child_2 : has_left_child 0 t4 2.
Proof.
  apply (dictionary_left_child_exist t4 2).
  - lia.
  - simpl. lia.
  - exists [], [], [0;3]. reflexivity.   (* Before 2 1 (ip t4) = [2;1;0;3] *)
Qed.

(* node 1 has a left child (node 0). *)
Example ex_has_left_child_1 : has_left_child 0 t4 1.
Proof.
  apply (dictionary_left_child_exist t4 1).
  - lia.
  - simpl. lia.
  - exists [2], [], [3]. reflexivity.   (* Before 1 0 (ip t4) = [2;1;0;3] *)
Qed.

(* (4c') the paper's dual instantiated: node 1 has a left child iff node
   0 (= 1-1) has no right child.  (Both hold: see ex_no_right_child_0.) *)
Example ex_dual_1 :
  has_left_child 0 t4 1 <-> ~ has_right_child 0 t4 0.
Proof. apply (left_child_iff_no_right t4 1); [lia | simpl; lia]. Qed.

(* node 3 has NO left child: 3 does NOT precede 3-1=2 in ip t4 (2 is first). *)
Example ex_no_left_child_3 : ~ has_left_child 0 t4 3.
Proof.
  intro H.
  apply (dictionary_left_child_exist t4 3) in H; [| lia | simpl; lia].
  apply (Before_NoDup_excl (ip t4) 3 2).
  - apply ip_NoDup.
  - exact H.
  - exists [], [1;0], []. reflexivity.   (* Before 2 3 (ip t4) = [2;1;0;3] *)
Qed.

(* Axiom-freeness of the new left-child results (expect:
   "Closed under the global context"). *)
Print Assumptions dictionary_left_child_exist.
Print Assumptions left_child_iff_no_right.
