(* ReconstructCatalan.v
   The verified Catalan enumeration: the size-indexed tree table of Reconstruct.v
   has, in row n, exactly the Catalan-number-many trees of size n.  We prove for
   ALL n (no size bound) that the row count

       catalan n := length (row n)

   starts at 1 and satisfies the Catalan convolution recurrence
       catalan (S k) = sum_{i=0}^{k} catalan i * catalan (k - i),
   and that the rows are size-homogeneous and complete: row n is exactly the set
   of trees of size n.  Hence  trees_of_size n B  (the size-n filter of
   trees_upto B, used in ReconstructAverage.v) has exactly  catalan n  trees for
   every B >= n -- the denominator of the average-case expectations, mechanized.

   This is the verified-enumeration foundation flagged in the roadmap as the
   precondition for the analytic (average-case) statements.  Axiom-free.

   Build:  rocq c Trees.v Dictionary.v Reconstruct.v   (first)
           rocq c ReconstructCatalan.v
   Rocq Prover 9.1.0.  Standard library only. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import Trees.
Require Import Dictionary.
Require Import Reconstruct.

(* row n of the size table = all trees the table assigns size n. *)
Definition allt (n : nat) : list tree := nth n (trees_table n) [].

(* ------------------------------------------------------------------ *)
(* 1. The table is built one row at a time (the fold, unrolled).       *)
(* ------------------------------------------------------------------ *)
Lemma trees_table_S : forall N,
  trees_table (S N) = trees_table N ++ [build_row (trees_table N) (S N)].
Proof.
  intro N. unfold trees_table.
  replace (seq 0 (S (S N))) with (seq 0 (S N) ++ [S N]).
  2:{ rewrite (seq_S (S N) 0). reflexivity. }
  rewrite fold_left_app. reflexivity.
Qed.

Lemma trees_table_0 : trees_table 0 = [[Leaf]].
Proof. reflexivity. Qed.

Lemma trees_table_len : forall N, length (trees_table N) = S N.
Proof.
  induction N as [|N IH]; [reflexivity|].
  rewrite trees_table_S, length_app, IH. cbn [length]. lia.
Qed.

(* Rows already built never change as the table grows. *)
Lemma row_stable_step : forall N i, i <= N ->
  nth i (trees_table (S N)) [] = nth i (trees_table N) [].
Proof.
  intros N i Hi. rewrite trees_table_S. rewrite app_nth1.
  - reflexivity.
  - rewrite trees_table_len. lia.
Qed.

Lemma row_eq : forall d i, nth i (trees_table (i + d)) [] = allt i.
Proof.
  induction d as [|d IH]; intro i.
  - rewrite Nat.add_0_r. reflexivity.
  - replace (i + S d) with (S (i + d)) by lia.
    rewrite row_stable_step by lia. apply IH.
Qed.

Lemma row_eq_le : forall N i, i <= N -> nth i (trees_table N) [] = allt i.
Proof.
  intros N i Hle. replace N with (i + (N - i)) by lia. apply row_eq.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The count of row n, and its Catalan convolution recurrence.      *)
(* ------------------------------------------------------------------ *)
Definition catalan (n : nat) : nat := length (allt n).

Lemma catalan_0 : catalan 0 = 1.
Proof. reflexivity. Qed.

(* allt (S k) is exactly build_row of the size-k table. *)
Lemma allt_S : forall k,
  allt (S k) = build_row (trees_table k) (S k).
Proof.
  intro k. unfold allt. rewrite trees_table_S.
  rewrite app_nth2; rewrite trees_table_len.
  - rewrite Nat.sub_diag. reflexivity.
  - lia.
Qed.

Theorem catalan_recurrence : forall k,
  catalan (S k) = list_sum (map (fun i => catalan i * catalan (k - i)) (seq 0 (S k))).
Proof.
  intro k. unfold catalan at 1. rewrite allt_S.
  unfold build_row. cbn [length] in *.
  (* length (concat (map g (seq 0 (S k)))) = sum of lengths *)
  rewrite length_concat, map_map.
  (* now rewrite each summand using length_map, length_prod, row_eq_le *)
  f_equal. apply map_ext_in. intros i Hi. rewrite in_seq in Hi.
  rewrite length_map, length_prod.
  replace (S k - 1 - i) with (k - i) by lia.
  rewrite (row_eq_le k i) by lia.
  rewrite (row_eq_le k (k - i)) by lia.
  reflexivity.
Qed.

(* Sanity: the counts are 1,1,2,5,14,42,132,429,1430. *)
Example catalan_values :
  map catalan (seq 0 9) = [1; 1; 2; 5; 14; 42; 132; 429; 1430].
Proof. vm_compute. reflexivity. Qed.

Print Assumptions catalan_recurrence.

(* ------------------------------------------------------------------ *)
(* 3. Row n is exactly the set of trees of size n (sound + complete).  *)
(* ------------------------------------------------------------------ *)

(* Soundness: every tree in row m has size m. *)
Lemma allt_size : forall n m t, m <= n -> In t (allt m) -> size t = m.
Proof.
  induction n as [|n IH]; intros m t Hm Hin.
  - assert (m = 0) by lia. subst m.
    unfold allt in Hin. rewrite trees_table_0 in Hin. cbn [nth] in Hin.
    destruct Hin as [<-|[]]. reflexivity.
  - destruct (Nat.eq_dec m (S n)) as [Heq|Hne].
    + subst m. rewrite allt_S in Hin. unfold build_row in Hin.
      apply in_concat in Hin. destruct Hin as [row' [Hrow Hin]].
      apply in_map_iff in Hrow. destruct Hrow as [i [Hgi Hi]].
      rewrite in_seq in Hi.
      subst row'. apply in_map_iff in Hin. destruct Hin as [[l r] [Hnode Hpair]].
      apply in_prod_iff in Hpair. destruct Hpair as [Hl Hr].
      replace (S n - 1 - i) with (n - i) in Hr by lia.
      rewrite (row_eq_le n i) in Hl by lia.
      rewrite (row_eq_le n (n - i)) in Hr by lia.
      apply (IH i) in Hl; [|lia]. apply (IH (n - i)) in Hr; [|lia].
      subst t. cbn [size fst snd]. lia.
    + apply (IH m); [lia | exact Hin].
Qed.

(* Completeness: every tree is in the row of its own size. *)
Lemma allt_complete : forall t, In t (allt (size t)).
Proof.
  induction t as [|l IHl r IHr].
  - cbn [size]. unfold allt. rewrite trees_table_0. cbn [nth]. left. reflexivity.
  - change (allt (size (Node l r))) with (allt (S (size l + size r))).
    rewrite allt_S. unfold build_row.
    set (k := size l + size r).
    apply in_concat.
    exists (map (fun lr => Node (fst lr) (snd lr))
            (list_prod (nth (size l) (trees_table k) [])
                       (nth (S k - 1 - size l) (trees_table k) []))).
    split.
    + apply in_map_iff. exists (size l). split; [reflexivity|].
      rewrite in_seq. unfold k. lia.
    + apply in_map_iff. exists (l, r). split; [reflexivity|].
      apply in_prod_iff.
      replace (S k - 1 - size l) with (size r) by (unfold k; lia).
      rewrite (row_eq_le k (size l)) by (unfold k; lia).
      rewrite (row_eq_le k (size r)) by (unfold k; lia).
      split; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The size-n filter has exactly catalan n trees, for every B >= n. *)
(* ------------------------------------------------------------------ *)
Definition trees_of_size (n B : nat) : list tree :=
  filter (fun t => Nat.eqb (size t) n) (trees_upto B).

Lemma filter_concat : forall (f : tree -> bool) (l : list (list tree)),
  filter f (concat l) = concat (map (filter f) l).
Proof.
  induction l as [|x l IH]; [reflexivity|].
  cbn [concat map]. rewrite filter_app, IH. reflexivity.
Qed.

Lemma filter_all_true : forall (f : tree -> bool) l,
  (forall x, In x l -> f x = true) -> filter f l = l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|].
  cbn [filter]. rewrite (H x (or_introl eq_refl)).
  rewrite IH by (intros y Hy; apply H; right; exact Hy). reflexivity.
Qed.

Lemma filter_all_false : forall (f : tree -> bool) l,
  (forall x, In x l -> f x = false) -> filter f l = [].
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|].
  cbn [filter]. rewrite (H x (or_introl eq_refl)).
  apply IH. intros y Hy; apply H; right; exact Hy.
Qed.

(* Filtering row k by "size = n" keeps the whole row if k = n, else nothing. *)
Lemma filter_row : forall k n,
  length (filter (fun t => Nat.eqb (size t) n) (allt k))
  = (if Nat.eqb k n then catalan n else 0).
Proof.
  intros k n. destruct (Nat.eqb_spec k n) as [Heq|Hne].
  - subst n. unfold catalan.
    rewrite filter_all_true; [reflexivity|].
    intros t Hin. apply Nat.eqb_eq. apply (allt_size k k t (Nat.le_refl k) Hin).
  - rewrite filter_all_false; [reflexivity|].
    intros t Hin. apply Nat.eqb_neq.
    rewrite (allt_size k k t (Nat.le_refl k) Hin). exact Hne.
Qed.

(* The whole table is the list of rows allt 0, ..., allt B. *)
Lemma trees_table_eq_map : forall B,
  trees_table B = map allt (seq 0 (S B)).
Proof.
  induction B as [|B IH]; [reflexivity|].
  rewrite trees_table_S, <- allt_S, IH.
  rewrite (seq_S (S B) 0), map_app. reflexivity.
Qed.

Lemma list_sum_map_zero : forall (g : nat -> nat) l,
  (forall x, In x l -> g x = 0) -> list_sum (map g l) = 0.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|].
  simpl. rewrite (H x (or_introl eq_refl)).
  rewrite IH by (intros y Hy; apply H; right; exact Hy). reflexivity.
Qed.

Lemma list_sum_app_single : forall l a, list_sum (l ++ [a]) = list_sum l + a.
Proof. intros l a. rewrite list_sum_app. simpl. lia. Qed.

(* A single indicator term survives a sum over an initial segment. *)
Lemma sum_indicator : forall m n v, n < m ->
  list_sum (map (fun k => if Nat.eqb k n then v else 0) (seq 0 m)) = v.
Proof.
  induction m as [|m IH]; intros n v Hn; [lia|].
  rewrite seq_S, Nat.add_0_l, map_app.
  change (map (fun k => if Nat.eqb k n then v else 0) [m])
    with ([if Nat.eqb m n then v else 0]).
  rewrite list_sum_app_single.
  destruct (Nat.eqb m n) eqn:Em.
  - apply Nat.eqb_eq in Em. subst n.
    assert (Hz : list_sum (map (fun k => if Nat.eqb k m then v else 0) (seq 0 m)) = 0).
    { apply list_sum_map_zero. intros k Hk. rewrite in_seq in Hk.
      destruct (Nat.eqb_spec k m); [lia | reflexivity]. }
    rewrite Hz. cbn; lia.
  - apply Nat.eqb_neq in Em. rewrite IH by lia. cbn; lia.
Qed.

Theorem length_trees_of_size : forall n B, n <= B ->
  length (trees_of_size n B) = catalan n.
Proof.
  intros n B Hn. unfold trees_of_size, trees_upto.
  rewrite filter_concat, length_concat, trees_table_eq_map, !map_map.
  erewrite map_ext; [|intro k; rewrite filter_row; reflexivity].
  apply sum_indicator. lia.
Qed.

Print Assumptions allt_complete.
Print Assumptions length_trees_of_size.
