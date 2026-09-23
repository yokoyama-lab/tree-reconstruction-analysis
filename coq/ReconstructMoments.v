(* ReconstructMoments.v
   Closed forms for the first-moment sums of tree statistics over the Catalan
   family allt n (the size-n trees, ReconstructCatalan).  These are the
   numerators of the average-case expectations; dividing by catalan n recovers
   the published rational forms.

   Structural (this file), axiom-free, for ALL n:
       sum of leaves over allt n  =  n * catalan (n-1)
       sum of full   over allt n  +  catalan n  =  n * catalan (n-1)
   The second is E[P_2] cleared of its denominator: with E[P_2] = (sum full)/C_n
   and C_{n-1}/C_n = (n+1)/(2(2n-1)) this is exactly (n-1)(n-2)/(2(2n-1)).

   The engine is one weighted Catalan-convolution identity
       2 * sum_{j=0}^{m} (j+1) * C_j * C_{m-j} = (m+2) * C_{m+1},
   itself a reflection of catalan_recurrence (the plain convolution
   sum C_j C_{m-j} = C_{m+1}).

   Build:  rocq c Trees.v Dictionary.v Reconstruct.v ReconstructCatalan.v (first)
           rocq c ReconstructMoments.v
   Rocq Prover 9.1.0.  Standard library only.  Axiom-free. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import Trees.
Require Import Dictionary.
Require Import Reconstruct.
Require Import ReconstructCatalan.

(* ================================================================== *)
(* 0. list_sum toolkit                                                 *)
(* ================================================================== *)

Lemma list_sum_map_add : forall {A} (a b : A -> nat) (l : list A),
  list_sum (map (fun x => a x + b x) l) = list_sum (map a l) + list_sum (map b l).
Proof.
  intros A a b l. induction l as [|x l IH]; [reflexivity|].
  simpl. rewrite IH. lia.
Qed.

Lemma list_sum_map_scal : forall {A} (c : nat) (h : A -> nat) (l : list A),
  list_sum (map (fun x => c * h x) l) = c * list_sum (map h l).
Proof.
  intros A c h l. induction l as [|x l IH]; simpl; [lia|].
  rewrite IH. nia.
Qed.

Lemma list_sum_const : forall {A} (c : nat) (l : list A),
  list_sum (map (fun _ => c) l) = length l * c.
Proof.
  intros A c l. induction l as [|x l IH]; simpl; [lia|].
  rewrite IH. nia.
Qed.

Lemma list_sum_map_zero' : forall {A} (g : A -> nat) (l : list A),
  (forall x, In x l -> g x = 0) -> list_sum (map g l) = 0.
Proof.
  intros A g l. induction l as [|x l IH]; intros H; [reflexivity|].
  simpl. rewrite (H x (or_introl eq_refl)).
  rewrite IH by (intros y Hy; apply H; right; exact Hy). reflexivity.
Qed.

Lemma list_sum_rev : forall l, list_sum (rev l) = list_sum l.
Proof.
  induction l as [|x l IH]; [reflexivity|].
  simpl. rewrite list_sum_app, IH. simpl. lia.
Qed.

(* ================================================================== *)
(* 1. Reflection of a sum over an initial segment                      *)
(* ================================================================== *)

Lemma rev_seq_0 : forall m, rev (seq 0 (S m)) = map (fun j => m - j) (seq 0 (S m)).
Proof.
  intro m. apply (nth_ext _ _ 0 0).
  - rewrite length_rev, length_map. reflexivity.
  - intros i Hi. rewrite length_rev, length_seq in Hi.
    (* LHS = m - i *)
    rewrite rev_nth by (rewrite length_seq; lia).
    rewrite length_seq, seq_nth by lia.
    (* RHS = m - i *)
    rewrite (nth_indep (map (fun j => m - j) (seq 0 (S m))) 0 ((fun j => m - j) 0))
      by (rewrite length_map, length_seq; lia).
    rewrite map_nth, seq_nth by lia.
    lia.
Qed.

Lemma list_sum_seq_reflect : forall (g : nat -> nat) m,
  list_sum (map g (seq 0 (S m))) = list_sum (map (fun j => g (m - j)) (seq 0 (S m))).
Proof.
  intros g m.
  transitivity (list_sum (map g (rev (seq 0 (S m))))).
  - rewrite map_rev, list_sum_rev. reflexivity.
  - rewrite rev_seq_0, map_map. reflexivity.
Qed.

(* peel the head 0 and reindex i = S j *)
Lemma sum_seq_shift1 : forall (F : nat -> nat) n,
  list_sum (map F (seq 0 (S n))) = F 0 + list_sum (map (fun j => F (S j)) (seq 0 n)).
Proof.
  intros F n.
  change (seq 0 (S n)) with (0 :: seq 1 n).
  rewrite map_cons. cbn [list_sum].
  rewrite <- (seq_shift n 0), map_map. reflexivity.
Qed.

(* ================================================================== *)
(* 2. The weighted Catalan-convolution identity                        *)
(* ================================================================== *)

(* plain convolution, just catalan_recurrence reread *)
Lemma catalan_conv : forall m,
  list_sum (map (fun i => catalan i * catalan (m - i)) (seq 0 (S m))) = catalan (S m).
Proof. intro m. symmetry. apply catalan_recurrence. Qed.

Lemma weighted_conv : forall m,
  2 * list_sum (map (fun j => (j + 1) * catalan j * catalan (m - j)) (seq 0 (S m)))
  = (m + 2) * catalan (S m).
Proof.
  intro m.
  set (g := fun j => (j + 1) * catalan j * catalan (m - j)).
  (* 2W = W + (reflected W) = sum of (g j + g (m-j)) = (m+2) * sum C_j C_{m-j} *)
  assert (Href : list_sum (map g (seq 0 (S m)))
               = list_sum (map (fun j => g (m - j)) (seq 0 (S m))))
    by apply list_sum_seq_reflect.
  replace (2 * list_sum (map g (seq 0 (S m))))
    with (list_sum (map g (seq 0 (S m))) + list_sum (map (fun j => g (m - j)) (seq 0 (S m))))
    by (rewrite <- Href; lia).
  rewrite <- list_sum_map_add.
  (* g j + g (m-j) = (m+2) * (catalan j * catalan (m-j))  for j in seq 0 (S m) *)
  transitivity (list_sum (map (fun j => (m + 2) * (catalan j * catalan (m - j))) (seq 0 (S m)))).
  - f_equal. apply map_ext_in. intros j Hj. rewrite in_seq in Hj. unfold g.
    replace (m - (m - j)) with j by lia.
    (* (j+1)*Cj*C(m-j) + (m-j+1)*C(m-j)*Cj = (m+2)*(Cj*C(m-j)) *)
    remember (m - j) as w eqn:Hw.
    assert (Hm : m = j + w) by lia. subst m. nia.
  - rewrite list_sum_map_scal. rewrite catalan_conv. reflexivity.
Qed.

(* ================================================================== *)
(* 3. Row decomposition of a sum over allt (S k)                       *)
(* ================================================================== *)

Definition node (lr : tree * tree) : tree := Node (fst lr) (snd lr).

Lemma allt_S_rows : forall k,
  allt (S k)
  = concat (map (fun i => map node (list_prod (allt i) (allt (k - i)))) (seq 0 (S k))).
Proof.
  intro k. rewrite allt_S. unfold build_row.
  f_equal. apply map_ext_in. intros i Hi. rewrite in_seq in Hi.
  unfold node.
  rewrite (row_eq_le k i) by lia.
  replace (S k - 1 - i) with (k - i) by lia.
  rewrite (row_eq_le k (k - i)) by lia.
  reflexivity.
Qed.

Lemma list_sum_map_concat : forall {A} (f : A -> nat) (L : list (list A)),
  list_sum (map f (concat L)) = list_sum (map (fun x => list_sum (map f x)) L).
Proof.
  intros A f L. induction L as [|x L IH]; [reflexivity|].
  cbn [concat map]. rewrite map_app, list_sum_app, IH. cbn [list_sum]. reflexivity.
Qed.

(* The cell sum: sum of f over the trees built from rows i and j. *)
Definition cell (f : tree -> nat) (i j : nat) : nat :=
  list_sum (map (fun lr => f (Node (fst lr) (snd lr))) (list_prod (allt i) (allt j))).

Lemma sum_allt_S : forall (f : tree -> nat) k,
  list_sum (map f (allt (S k)))
  = list_sum (map (fun i => cell f i (k - i)) (seq 0 (S k))).
Proof.
  intros f k. rewrite allt_S_rows. rewrite list_sum_map_concat, map_map.
  f_equal. apply map_ext_in. intros i _. unfold cell, node.
  rewrite map_map. reflexivity.
Qed.

(* ================================================================== *)
(* 4. Product-sum lemmas for the cell                                  *)
(* ================================================================== *)

Lemma list_prod_cons : forall (a : tree) (A B : list tree),
  list_prod (a :: A) B = map (fun y => (a, y)) B ++ list_prod A B.
Proof. reflexivity. Qed.

Lemma list_sum_prod_fst : forall (p : tree -> nat) (A B : list tree),
  list_sum (map (fun lr => p (fst lr)) (list_prod A B)) = length B * list_sum (map p A).
Proof.
  intros p A B. induction A as [|a A IH]; [cbn; lia|].
  rewrite list_prod_cons, map_app, list_sum_app, IH.
  rewrite map_map. cbn [fst]. rewrite (list_sum_const (p a) B).
  change (list_sum (map p (a :: A))) with (p a + list_sum (map p A)). nia.
Qed.

Lemma list_sum_prod_snd : forall (q : tree -> nat) (A B : list tree),
  list_sum (map (fun lr => q (snd lr)) (list_prod A B)) = length A * list_sum (map q B).
Proof.
  intros q A B. induction A as [|a A IH]; [cbn; lia|].
  rewrite list_prod_cons, map_app, list_sum_app, IH.
  rewrite map_map. cbn [snd].
  change (map (fun y => q y) B) with (map q B).
  cbn [length]. nia.
Qed.

Lemma list_sum_prod_mul : forall (p q : tree -> nat) (A B : list tree),
  list_sum (map (fun lr => p (fst lr) * q (snd lr)) (list_prod A B))
  = list_sum (map p A) * list_sum (map q B).
Proof.
  intros p q A B. induction A as [|a A IH]; [cbn; lia|].
  rewrite list_prod_cons, map_app, list_sum_app, IH.
  rewrite map_map. cbn [fst snd]. rewrite (list_sum_map_scal (p a) q B).
  change (list_sum (map p (a :: A))) with (p a + list_sum (map p A)). nia.
Qed.

(* ================================================================== *)
(* 5. leaves: the cell, and the closed form                            *)
(* ================================================================== *)

Definition isleaf (t : tree) : nat := match t with Leaf => 1 | _ => 0 end.

Lemma leaves_node : forall l r,
  leaves (Node l r) = leaves l + leaves r + isleaf l * isleaf r.
Proof. intros l r. destruct l; destruct r; cbn; lia. Qed.

(* count of Leaf in allt i = 1 if i = 0 else 0 *)
Lemma sum_isleaf_allt : forall i,
  list_sum (map isleaf (allt i)) = (if Nat.eqb i 0 then 1 else 0).
Proof.
  intro i. destruct i as [|i].
  - reflexivity.
  - cbn [Nat.eqb]. apply list_sum_map_zero'. intros t Hin.
    pose proof (allt_size (S i) (S i) t (Nat.le_refl _) Hin) as Hsz.
    destruct t; [cbn in Hsz; lia | reflexivity].
Qed.

Definition SL (n : nat) : nat := list_sum (map leaves (allt n)).

Lemma cell_leaves : forall i j,
  cell leaves i j
  = catalan j * SL i + catalan i * SL j
    + (if Nat.eqb i 0 then 1 else 0) * (if Nat.eqb j 0 then 1 else 0).
Proof.
  intros i j. unfold cell.
  erewrite map_ext; [|intro lr; rewrite leaves_node; reflexivity].
  (* split the three summands *)
  rewrite (list_sum_map_add (fun lr => leaves (fst lr) + leaves (snd lr))
                            (fun lr => isleaf (fst lr) * isleaf (snd lr))).
  rewrite (list_sum_map_add (fun lr => leaves (fst lr)) (fun lr => leaves (snd lr))).
  rewrite list_sum_prod_fst, list_sum_prod_snd, list_sum_prod_mul.
  rewrite sum_isleaf_allt, sum_isleaf_allt.
  unfold SL, catalan. reflexivity.
Qed.

Lemma SL_0 : SL 0 = 0.
Proof. reflexivity. Qed.

(* The recurrence for SL (S k), corner term folded in. *)
Lemma SL_rec : forall k,
  SL (S k)
  = list_sum (map (fun i => catalan (k - i) * SL i + catalan i * SL (k - i)) (seq 0 (S k)))
    + (if Nat.eqb k 0 then 1 else 0).
Proof.
  intro k. unfold SL at 1. rewrite sum_allt_S.
  erewrite map_ext; [|intro i; rewrite cell_leaves; reflexivity].
  (* separate the corner indicators into their own sum *)
  rewrite (list_sum_map_add
             (fun i => catalan (k - i) * SL i + catalan i * SL (k - i))
             (fun i => (if Nat.eqb i 0 then 1 else 0) * (if Nat.eqb (k - i) 0 then 1 else 0))).
  f_equal.
  (* the corner sum equals (if k=0 then 1 else 0) *)
  destruct (Nat.eqb_spec k 0) as [Hk|Hk].
  - subst k. reflexivity.
  - apply list_sum_map_zero'. intros i Hi. rewrite in_seq in Hi.
    destruct (Nat.eqb_spec i 0) as [Hi0|Hi0]; [|reflexivity].
    subst i. rewrite Nat.sub_0_r.
    destruct (Nat.eqb_spec k 0) as [|]; [contradiction|]. lia.
Qed.

(* The closed form, by strong induction. *)
Theorem SL_closed : forall n, SL n = n * catalan (n - 1).
Proof.
  intro n. induction n as [n IH] using lt_wf_ind.
  destruct n as [|k].
  - reflexivity.
  - rewrite SL_rec.
    (* rewrite every SL i (i <= k) and SL (k-i) by the IH *)
    erewrite map_ext_in;
      [|intros i Hi; rewrite in_seq in Hi;
        rewrite (IH i) by lia; rewrite (IH (k - i)) by lia; reflexivity].
    (* now an arithmetic identity over catalan; reduce the two halves to one *)
    (* sum_i [ C_{k-i} * (i * C_{i-1}) + C_i * ((k-i) * C_{k-i-1}) ] *)
    rewrite (list_sum_map_add
               (fun i => catalan (k - i) * (i * catalan (i - 1)))
               (fun i => catalan i * ((k - i) * catalan (k - i - 1)))).
    (* second sum is the reflection of the first -> equal *)
    assert (Hrefl :
      list_sum (map (fun i => catalan i * ((k - i) * catalan (k - i - 1))) (seq 0 (S k)))
      = list_sum (map (fun i => catalan (k - i) * (i * catalan (i - 1))) (seq 0 (S k)))).
    { rewrite (list_sum_seq_reflect
                 (fun i => catalan i * ((k - i) * catalan (k - i - 1)))).
      f_equal. apply map_ext_in. intros i Hi. rewrite in_seq in Hi.
      replace (k - (k - i)) with i by lia. reflexivity. }
    rewrite Hrefl.
    destruct (Nat.eqb_spec k 0) as [Hk|Hk].
    + subst k. cbn. reflexivity.
    + (* corner term 0; main = 2 * sum C_{k-i} i C_{i-1} = (k+1) C_k via weighted_conv *)
      rewrite Nat.add_0_r.
      replace (list_sum (map (fun i => catalan (k - i) * (i * catalan (i - 1))) (seq 0 (S k)))
               + list_sum (map (fun i => catalan (k - i) * (i * catalan (i - 1))) (seq 0 (S k))))
        with (2 * list_sum (map (fun i => catalan (k - i) * (i * catalan (i - 1))) (seq 0 (S k))))
        by lia.
      (* re-express the body as the weighted_conv body shifted by one *)
      (* sum_{i=0}^{k} C_{k-i} * i * C_{i-1} = sum_{j=0}^{k-1} (j+1) C_j C_{k-1-j} *)
      destruct k as [|k']; [lia|].
      transitivity (2 * list_sum
        (map (fun j => (j + 1) * catalan j * catalan (k' - j)) (seq 0 (S k')))).
      * f_equal.
        (* drop the i=0 term, reindex i = S j *)
        rewrite (sum_seq_shift1 (fun i => catalan (S k' - i) * (i * catalan (i - 1))) (S k')).
        cbv beta. rewrite Nat.mul_0_l, Nat.mul_0_r, Nat.add_0_l.
        f_equal. apply map_ext_in. intros j Hj. rewrite in_seq in Hj.
        replace (S k' - S j) with (k' - j) by lia.
        replace (S j - 1) with j by lia.
        replace (S j) with (j + 1) by lia. ring.
      * rewrite weighted_conv.
        replace (S (S k') - 1) with (S k') by lia.
        replace (k' + 2) with (S (S k')) by lia. reflexivity.
Qed.

Print Assumptions SL_closed.

(* ================================================================== *)
(* 6. full: full = leaves - 1 on non-leaves -> closed form             *)
(* ================================================================== *)

Definition isnonleaf (t : tree) : nat := match t with Leaf => 0 | _ => 1 end.

Lemma full_node : forall l r,
  full (Node l r) = full l + full r + isnonleaf l * isnonleaf r.
Proof. intros l r; destruct l; destruct r; cbn; lia. Qed.

Lemma full_leaves : forall t, t <> Leaf -> full t + 1 = leaves t.
Proof.
  induction t as [|l IHl r IHr]; [congruence|]. intros _.
  rewrite full_node, leaves_node.
  destruct l as [|la lb]; destruct r as [|ra rb]; cbn [isleaf isnonleaf].
  - change (full Leaf) with 0. change (leaves Leaf) with 0. lia.
  - pose proof (IHr ltac:(discriminate)).
    change (full Leaf) with 0. change (leaves Leaf) with 0. lia.
  - pose proof (IHl ltac:(discriminate)).
    change (full Leaf) with 0. change (leaves Leaf) with 0. lia.
  - pose proof (IHl ltac:(discriminate)). pose proof (IHr ltac:(discriminate)). lia.
Qed.

Definition SF (n : nat) : nat := list_sum (map full (allt n)).

(* For n >= 1 every tree in allt n is a non-leaf, so leaves = full + 1 pointwise. *)
Theorem SF_closed : forall n, 1 <= n -> SF n + catalan n = n * catalan (n - 1).
Proof.
  intros n Hn. unfold SF.
  assert (Hadd : forall (h : tree -> nat) l,
    list_sum (map (fun x => h x + 1) l) = list_sum (map h l) + length l).
  { intros h l; induction l as [|x l IHl]; simpl; [lia | rewrite IHl; lia]. }
  assert (Hpw : forall t, In t (allt n) -> leaves t = full t + 1).
  { intros t Hin. symmetry. apply full_leaves.
    intro Ht; subst t.
    pose proof (allt_size n n Leaf (Nat.le_refl _) Hin) as Hsz; cbn in Hsz; lia. }
  assert (Hpt : list_sum (map leaves (allt n)) = list_sum (map full (allt n)) + catalan n).
  { rewrite (map_ext_in leaves (fun t => full t + 1) (allt n) Hpw).
    rewrite (Hadd full (allt n)). unfold catalan. reflexivity. }
  change (list_sum (map leaves (allt n))) with (SL n) in Hpt.
  rewrite SL_closed in Hpt. lia.
Qed.

Print Assumptions SF_closed.

(* ================================================================== *)
(* 7. Bridge: the size-n filter of trees_upto B is exactly row n        *)
(* ================================================================== *)

Lemma concat_all_nil : forall {A} (F : nat -> list A) l,
  (forall k, In k l -> F k = []) -> concat (map F l) = [].
Proof.
  intros A F l H. induction l as [|x l IH]; [reflexivity|].
  cbn [map]. rewrite concat_cons, (H x (or_introl eq_refl)).
  cbn [app]. apply IH. intros y Hy; apply H; right; exact Hy.
Qed.

Lemma concat_map_app_single : forall {A B} (F : A -> list B) l a,
  concat (map F (l ++ [a])) = concat (map F l) ++ F a.
Proof.
  intros A B F l a. rewrite map_app, concat_app.
  cbn [map concat]. rewrite app_nil_r. reflexivity.
Qed.

Lemma concat_seg : forall (h : nat -> list tree) n m, n < m ->
  concat (map (fun k => if Nat.eqb k n then h k else []) (seq 0 m)) = h n.
Proof.
  intros h n. induction m as [|m IH]; intros Hn; [lia|].
  rewrite seq_S, Nat.add_0_l, concat_map_app_single. cbv beta.
  destruct (Nat.eqb_spec m n) as [->|Hne].
  - rewrite (concat_all_nil (fun k => if Nat.eqb k n then h k else []) (seq 0 n)).
    + reflexivity.
    + intros k Hk. rewrite in_seq in Hk.
      destruct (Nat.eqb_spec k n); [lia | reflexivity].
  - change (if false then h m else (@nil tree)) with (@nil tree).
    rewrite app_nil_r. apply IH. lia.
Qed.

Lemma filter_size_row : forall k n,
  filter (fun t => Nat.eqb (size t) n) (allt k) = (if Nat.eqb k n then allt k else []).
Proof.
  intros k n. destruct (Nat.eqb_spec k n) as [->|Hne].
  - apply filter_all_true. intros t Hin. apply Nat.eqb_eq.
    apply (allt_size n n t (Nat.le_refl n) Hin).
  - apply filter_all_false. intros t Hin. apply Nat.eqb_neq.
    rewrite (allt_size k k t (Nat.le_refl k) Hin). exact Hne.
Qed.

Lemma trees_of_size_eq_allt : forall n B, n <= B -> trees_of_size n B = allt n.
Proof.
  intros n B Hn. unfold trees_of_size, trees_upto.
  rewrite filter_concat, trees_table_eq_map, map_map.
  erewrite map_ext; [| intro k; rewrite filter_size_row; reflexivity ].
  apply (concat_seg allt n (S B)). lia.
Qed.

(* ================================================================== *)
(* 8. Sanity                                                           *)
(* ================================================================== *)

Example SL_values : map SL (seq 1 6) = [1; 2; 6; 20; 70; 252].
Proof. vm_compute. reflexivity. Qed.

Example SF_values : map SF (seq 1 6) = [0; 0; 1; 6; 28; 120].
Proof. vm_compute. reflexivity. Qed.
