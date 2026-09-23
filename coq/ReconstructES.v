(* ReconstructES.v
   The average data-dependent count.  Summing the structural statistic Srec
   (= pops_N (ip t), ReconstructPops) over the Catalan family gives the cleared
   rational closed form

       E[S] = n(n-1)/(n+2),    i.e.  (n+2) * sum_{|t|=n} S = n(n-1) * C_n,

   axiom-free, for all n.  Engine: the residue-length sum
       sum_{|t|=n} rlen t + C_n = C_{n+1},
   proved from the row convolution and catalan_recurrence; with
   Srec t = size t - rlen t this gives  sum S = (n+1) C_n - C_{n+1}, and
   catalan_ratio clears the denominator.

   Rocq Prover 9.1.0.  Standard library only.  Axiom-free. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import Trees.
Require Import Dictionary.
Require Import Reconstruct.
Require Import ReconstructM.
Require Import ReconstructN.
Require Import ReconstructLcount.
Require Import ReconstructCatalan.
Require Import ReconstructMoments.
Require Import ReconstructPops.
Require Import ReconstructBinomial.
Require Import ReconstructDyck.
Require Import ReconstructAverage.

(* ------------------------------------------------------------------ *)
(* helpers                                                             *)
(* ------------------------------------------------------------------ *)
Lemma list_prod_single_r : forall {A B} (l : list A) (x : B),
  list_prod l [x] = map (fun a => (a, x)) l.
Proof.
  intros A B l x. induction l as [|a l IH]; [reflexivity|].
  cbn [list_prod map]. rewrite IH. reflexivity.
Qed.

Lemma list_sum_single : forall a, list_sum [a] = a.
Proof. intro a. cbn. lia. Qed.

Lemma list_sum_map_S : forall {A} (f : A -> nat) (l : list A),
  list_sum (map (fun x => S (f x)) l) = list_sum (map f l) + length l.
Proof.
  intros A f l. induction l as [|x l IH]; [reflexivity|].
  simpl. rewrite IH. lia.
Qed.

Definition rsum (n : nat) : nat := list_sum (map rlen (allt n)).

(* ------------------------------------------------------------------ *)
(* the cell sum for rlen                                              *)
(* ------------------------------------------------------------------ *)
Lemma cell_rlen_pos : forall i j, 1 <= j -> cell rlen i j = catalan i * rsum j.
Proof.
  intros i j Hj. unfold cell, rsum.
  erewrite (map_ext_in _ (fun lr => rlen (snd lr))).
  2:{ intros lr Hlr. destruct lr as [ll rr]. apply in_prod_iff in Hlr.
      destruct Hlr as [_ Hr]. cbn [fst snd].
      pose proof (allt_size j j rr (Nat.le_refl j) Hr) as Hsz.
      destruct rr as [|rrl rrr]; [cbn in Hsz; lia | reflexivity]. }
  rewrite (list_sum_prod_snd rlen (allt i) (allt j)). unfold catalan. reflexivity.
Qed.

Lemma cell_rlen_0 : forall i, cell rlen i 0 = rsum i + catalan i.
Proof.
  intro i. unfold cell, rsum, catalan.
  unfold allt at 2. rewrite trees_table_0. cbn [nth].
  rewrite list_prod_single_r, map_map.
  erewrite (map_ext _ (fun l => S (rlen l))); [| intro l; cbn [fst snd]; reflexivity].
  rewrite list_sum_map_S. reflexivity.
Qed.

Lemma cell_rlen : forall i j,
  cell rlen i j = catalan i * rsum j + (if Nat.eqb j 0 then rsum i + catalan i else 0).
Proof.
  intros i j. destruct j as [|j].
  - rewrite cell_rlen_0. cbn [Nat.eqb]. change (rsum 0) with 0. lia.
  - rewrite cell_rlen_pos by lia. cbn [Nat.eqb]. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* the rlen-sum recurrence                                            *)
(* ------------------------------------------------------------------ *)
Lemma rsum_rec : forall k,
  rsum (S k)
  = list_sum (map (fun i => catalan i * rsum (k - i)) (seq 0 (S k)))
    + (rsum k + catalan k).
Proof.
  intro k. unfold rsum at 1. rewrite sum_allt_S.
  erewrite map_ext; [| intro i; rewrite cell_rlen; reflexivity].
  rewrite (list_sum_map_add
             (fun i => catalan i * rsum (k - i))
             (fun i => if Nat.eqb (k - i) 0 then rsum i + catalan i else 0)).
  f_equal.
  rewrite (seq_S k 0), map_app, list_sum_app.
  rewrite Nat.add_0_l.
  rewrite (list_sum_map_zero' (fun i => if Nat.eqb (k - i) 0 then rsum i + catalan i else 0)
             (seq 0 k)).
  - cbn [map].
    replace (if Nat.eqb (k - k) 0 then rsum k + catalan k else 0)
      with (rsum k + catalan k) by (rewrite Nat.sub_diag; reflexivity).
    rewrite list_sum_single. lia.
  - intros i Hi. rewrite in_seq in Hi.
    destruct (Nat.eqb_spec (k - i) 0); [lia | reflexivity].
Qed.

(* ------------------------------------------------------------------ *)
(* closed form: sum rlen + C_n = C_{n+1}                               *)
(* ------------------------------------------------------------------ *)
Theorem rsum_closed : forall n, rsum n + catalan n = catalan (S n).
Proof.
  induction n as [n IH] using lt_wf_ind.
  destruct n as [|k]; [reflexivity|].
  rewrite rsum_rec.
  set (CONV := list_sum (map (fun i => catalan i * rsum (k - i)) (seq 0 (S k)))).
  set (SCONV := list_sum (map (fun i => catalan i * catalan (S (k - i))) (seq 0 (S k)))).
  pose proof (IH k ltac:(lia)) as IHk.
  (* convA: CONV + catalan (S k) = SCONV *)
  assert (HA : CONV + catalan (S k) = SCONV).
  { unfold CONV, SCONV.
    replace (catalan (S k))
      with (list_sum (map (fun i => catalan i * catalan (k - i)) (seq 0 (S k))))
      by (apply catalan_conv).
    rewrite <- list_sum_map_add. f_equal. apply map_ext_in.
    intros i Hi. rewrite in_seq in Hi.
    rewrite <- Nat.mul_add_distr_l, (IH (k - i)) by lia. reflexivity. }
  (* convB: SCONV + catalan (S k) = catalan (S (S k)) *)
  assert (HB : SCONV + catalan (S k) = catalan (S (S k))).
  { unfold SCONV. rewrite <- (catalan_conv (S k)).
    rewrite (seq_S (S k) 0), map_app, list_sum_app, Nat.add_0_l.
    f_equal.
    - f_equal. apply map_ext_in. intros i Hi. rewrite in_seq in Hi.
      replace (S k - i) with (S (k - i)) by lia. reflexivity.
    - cbn [map]. rewrite list_sum_single, Nat.sub_diag.
      change (catalan 0) with 1. lia. }
  lia.
Qed.

(* ------------------------------------------------------------------ *)
(* sum of Srec / pops_N over the size-n trees                          *)
(* ------------------------------------------------------------------ *)
Definition ssum (n : nat) : nat := list_sum (map Srec (allt n)).

(* sum size over allt n = n * C_n (every size-n tree has size n) *)
Lemma sum_size_allt : forall n, list_sum (map size (allt n)) = n * catalan n.
Proof.
  intro n. unfold catalan.
  erewrite map_ext_in; [| intros t Ht; rewrite (allt_size n n t (Nat.le_refl _) Ht); reflexivity].
  rewrite list_sum_const. lia.
Qed.

(* sum Srec + sum rlen = sum size, pointwise Srec+rlen=size *)
Lemma ssum_rsum_size : forall n, ssum n + rsum n = n * catalan n.
Proof.
  intro n. unfold ssum, rsum. rewrite <- (sum_size_allt n).
  rewrite <- list_sum_map_add. f_equal. apply map_ext.
  intro t. apply srec_rlen_size.
Qed.

Theorem ssum_closed : forall n, ssum n + catalan (S n) = S n * catalan n.
Proof.
  intro n. pose proof (ssum_rsum_size n) as H1. pose proof (rsum_closed n) as H2. lia.
Qed.

(* pops_N (ip t) = Srec t, so the sum of pops over the population is ssum *)
Theorem pops_sum_closed : forall n,
  tsum (fun t => pops_N (ip t)) (trees_of_size n n) + catalan (S n) = S n * catalan n.
Proof.
  intro n. rewrite (tsum_trees_of_size_allt (fun t => pops_N (ip t)) n).
  erewrite map_ext; [| intro t; rewrite pops_N_Srec; reflexivity].
  change (list_sum (map Srec (allt n))) with (ssum n). apply ssum_closed.
Qed.

(* ------------------------------------------------------------------ *)
(* the rational closed form  E[S] = n(n-1)/(n+2)  (cleared)             *)
(* ------------------------------------------------------------------ *)
Theorem ES_rational : forall n,
  (n + 2) * tsum (fun t => pops_N (ip t)) (trees_of_size n n) = n * (n - 1) * catalan n.
Proof.
  intro n. pose proof (pops_sum_closed n) as Hp.
  (* tsum pops = S n * catalan n - catalan (S n) ; and (n+2) catalan(S n) = 2(2n+1) catalan n *)
  pose proof (catalan_ratio n) as Hr.
  (* (n+2) * (S n * C_n - C_{n+1}) = n(n-1) C_n  using  (n+2) C_{n+1} = 2(2n+1) C_n *)
  set (T := tsum (fun t => pops_N (ip t)) (trees_of_size n n)) in *.
  assert (HT : T + catalan (S n) = S n * catalan n) by exact Hp.
  nia.
Qed.

Print Assumptions ES_rational.

(* ------------------------------------------------------------------ *)
(* The full average comparison counts E[A_M] and E[A_N], cleared.       *)
(*   E[A_M] = n(n-1)/(n+2) + (2n-1)                                      *)
(*   E[A_N] = n(n-1)/(n+2) + (n+2) + (n-1)(n-2)/(2(2n-1))                *)
(* ------------------------------------------------------------------ *)
Lemma tsum_pops_M_N : forall n,
  tsum (fun t => pops_M (ip t)) (trees_of_size n n)
  = tsum (fun t => pops_N (ip t)) (trees_of_size n n).
Proof.
  intro n. rewrite !tsum_trees_of_size_allt. f_equal. apply map_ext.
  intro t. apply pops_M_eq_N.
Qed.

Theorem EAM_rational : forall n, 1 <= n ->
  (n + 2) * tsum (fun t => total_comparisons_M (ip t)) (trees_of_size n n)
  = (n * (n - 1) + (2 * n - 1) * (n + 2)) * catalan n.
Proof.
  intros n Hn. rewrite (avg_decomp_M_catalan n Hn), tsum_pops_M_N.
  pose proof (ES_rational n) as Hs.
  set (T := tsum (fun t => pops_N (ip t)) (trees_of_size n n)) in *. nia.
Qed.

Theorem EAN_rational : forall n, 2 <= n ->
  2 * (n + 2) * (2 * n - 1)
    * tsum (fun t => total_comparisons_N (ip t)) (trees_of_size n n)
  = (2 * (2 * n - 1) * n * (n - 1)
     + 2 * (n + 2) * (n + 2) * (2 * n - 1)
     + (n + 2) * (n - 1) * (n - 2)) * catalan n.
Proof.
  intros n Hn. rewrite (avg_decomp_N_catalan n ltac:(lia)).
  pose proof (ES_rational n) as Hs. pose proof (EP2_rational n Hn) as Hp.
  set (TS := tsum (fun t => pops_N (ip t)) (trees_of_size n n)) in *.
  set (TF := tsum full (trees_of_size n n)) in *. nia.
Qed.

Print Assumptions EAM_rational.
Print Assumptions EAN_rational.

(* ------------------------------------------------------------------ *)
(* Regression: the population-sum identities at n = 3.  Over the five    *)
(* size-3 trees (catalan 3 = 5), the residue lengths sum to rsum 3 = 9   *)
(* and the pop counts to ssum 3 = 6, satisfying rsum_closed and          *)
(* ssum_closed concretely (catalan 4 = 14).                              *)
(* ------------------------------------------------------------------ *)
Example rsum_3 : rsum 3 = 9.
Proof. vm_compute. reflexivity. Qed.

Example ssum_3 : ssum 3 = 6.
Proof. vm_compute. reflexivity. Qed.

Example rsum_closed_3 : rsum 3 + catalan 3 = catalan 4.
Proof. vm_compute. reflexivity. Qed.

Example ssum_closed_3 : ssum 3 + catalan 4 = 4 * catalan 3.
Proof. vm_compute. reflexivity. Qed.

