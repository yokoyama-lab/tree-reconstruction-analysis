(* ReconstructES2.v
   The SECOND moment of the data-dependent count S (= pops_N(ip t) = Srec t).
   Since S is a structural statistic, E[S^2] is an exact rational in n.

   Engine: the residue-square sum, an exact Catalan-number closed form
       sum_{|t|=n} (rlen t)^2 + 5 C_{n+1} = 2 C_{n+2} + C_n,
   proved from the row convolution and catalan_recurrence; with
   Srec t = size t - rlen t and size = n on allt n,
       sum_{|t|=n} S^2 + (2n+5) C_{n+1} = (n+1)^2 C_n + 2 C_{n+2}.
   catalan_ratio then clears E[S^2] (and the variance) to a rational in n.

   Rocq Prover 9.1.0.  Standard library only.  Axiom-free. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import Trees Dictionary Reconstruct ReconstructM ReconstructN ReconstructLcount.
Require Import ReconstructCatalan ReconstructMoments ReconstructPops.
Require Import ReconstructBinomial ReconstructDyck ReconstructAverage ReconstructES.

Lemma sum_Ssq : forall {A} (f : A -> nat) (l : list A),
  list_sum (map (fun x => S (f x) * S (f x)) l)
  = list_sum (map (fun x => f x * f x) l) + 2 * list_sum (map f l) + length l.
Proof.
  intros A f l.
  erewrite (map_ext (fun x => S (f x) * S (f x)) (fun x => f x * f x + S (2 * f x)))
    by (intro x; nia).
  rewrite (list_sum_map_add (fun x => f x * f x) (fun x => S (2 * f x))).
  rewrite (list_sum_map_S (fun x => 2 * f x) l).
  rewrite (list_sum_map_scal 2 f l). lia.
Qed.

Definition rsum2 (n : nat) : nat := list_sum (map (fun t => rlen t * rlen t) (allt n)).

(* ------------------------------------------------------------------ *)
(* cell sum for rlen^2                                                 *)
(* ------------------------------------------------------------------ *)
Lemma cell_rlen2_pos : forall i j, 1 <= j ->
  cell (fun t => rlen t * rlen t) i j = catalan i * rsum2 j.
Proof.
  intros i j Hj. unfold cell, rsum2.
  erewrite (map_ext_in _ (fun lr => rlen (snd lr) * rlen (snd lr))).
  2:{ intros lr Hlr. destruct lr as [ll rr]. apply in_prod_iff in Hlr.
      destruct Hlr as [_ Hr]. cbn [fst snd].
      pose proof (allt_size j j rr (Nat.le_refl j) Hr) as Hsz.
      destruct rr as [|rrl rrr]; [cbn in Hsz; lia | reflexivity]. }
  rewrite (list_sum_prod_snd (fun t => rlen t * rlen t) (allt i) (allt j)).
  unfold catalan. reflexivity.
Qed.

Lemma cell_rlen2_0 : forall i,
  cell (fun t => rlen t * rlen t) i 0 = rsum2 i + 2 * rsum i + catalan i.
Proof.
  intro i. unfold cell, rsum2, rsum, catalan.
  unfold allt at 2. rewrite trees_table_0. cbn [nth].
  rewrite list_prod_single_r, map_map.
  erewrite (map_ext _ (fun l => S (rlen l) * S (rlen l)));
    [| intro l; cbn [fst snd]; reflexivity].
  rewrite (sum_Ssq rlen (allt i)). reflexivity.
Qed.

Lemma cell_rlen2 : forall i j,
  cell (fun t => rlen t * rlen t) i j
  = catalan i * rsum2 j + (if Nat.eqb j 0 then rsum2 i + 2 * rsum i + catalan i else 0).
Proof.
  intros i j. destruct j as [|j].
  - rewrite cell_rlen2_0. cbn [Nat.eqb]. change (rsum2 0) with 0. lia.
  - rewrite cell_rlen2_pos by lia. cbn [Nat.eqb]. lia.
Qed.

Lemma rsum2_rec : forall k,
  rsum2 (S k)
  = list_sum (map (fun i => catalan i * rsum2 (k - i)) (seq 0 (S k)))
    + (rsum2 k + 2 * rsum k + catalan k).
Proof.
  intro k. unfold rsum2 at 1. rewrite sum_allt_S.
  erewrite map_ext; [| intro i; rewrite cell_rlen2; reflexivity].
  rewrite (list_sum_map_add
             (fun i => catalan i * rsum2 (k - i))
             (fun i => if Nat.eqb (k - i) 0 then rsum2 i + 2 * rsum i + catalan i else 0)).
  f_equal.
  rewrite (seq_S k 0), map_app, list_sum_app, Nat.add_0_l.
  rewrite (list_sum_map_zero'
             (fun i => if Nat.eqb (k - i) 0 then rsum2 i + 2 * rsum i + catalan i else 0)
             (seq 0 k)).
  - cbn [map].
    replace (if Nat.eqb (k - k) 0 then rsum2 k + 2 * rsum k + catalan k else 0)
      with (rsum2 k + 2 * rsum k + catalan k) by (rewrite Nat.sub_diag; reflexivity).
    rewrite list_sum_single. lia.
  - intros i Hi. rewrite in_seq in Hi.
    destruct (Nat.eqb_spec (k - i) 0); [lia | reflexivity].
Qed.

(* ------------------------------------------------------------------ *)
(* shifted Catalan convolutions                                        *)
(* ------------------------------------------------------------------ *)
Lemma conv_shift1 : forall k,
  list_sum (map (fun i => catalan i * catalan (S k - i)) (seq 0 (S k))) + catalan (S k)
  = catalan (S (S k)).
Proof.
  intro k. rewrite <- (catalan_conv (S k)).
  rewrite (seq_S (S k) 0), map_app, list_sum_app, Nat.add_0_l. f_equal.
  cbn [map]. rewrite list_sum_single, Nat.sub_diag. change (catalan 0) with 1. lia.
Qed.

Lemma conv_shift2 : forall k,
  list_sum (map (fun i => catalan i * catalan (S (S k) - i)) (seq 0 (S k)))
    + catalan (S k) + catalan (S (S k))
  = catalan (S (S (S k))).
Proof.
  intro k. rewrite <- (catalan_conv (S (S k))).
  rewrite (seq_S (S (S k)) 0), (seq_S (S k) 0), map_app, map_app,
          list_sum_app, list_sum_app, !Nat.add_0_l.
  (* last two terms: i = S k and i = S (S k) *)
  cbn [map]. rewrite !list_sum_single.
  replace (S (S k) - S k) with 1 by lia. rewrite Nat.sub_diag.
  change (catalan 0) with 1. change (catalan 1) with 1. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* closed form:  sum rlen^2 + 5 C_{n+1} = 2 C_{n+2} + C_n              *)
(* ------------------------------------------------------------------ *)
Theorem rsum2_closed : forall n,
  rsum2 n + 5 * catalan (S n) = 2 * catalan (S (S n)) + catalan n.
Proof.
  induction n as [n IH] using lt_wf_ind.
  destruct n as [|k]; [reflexivity|].
  rewrite rsum2_rec.
  (* substitute rsum2 (k-i) = 2 C(k-i+2) - 5 C(k-i+1) + C(k-i) via IH (additive),
     turning the convolution into shifted catalan convolutions *)
  set (CV := list_sum (map (fun i => catalan i * rsum2 (k - i)) (seq 0 (S k)))).
  set (S0 := list_sum (map (fun i => catalan i * catalan (k - i)) (seq 0 (S k)))).
  set (S1 := list_sum (map (fun i => catalan i * catalan (S k - i)) (seq 0 (S k)))).
  set (S2 := list_sum (map (fun i => catalan i * catalan (S (S k) - i)) (seq 0 (S k)))).
  pose proof (IH k ltac:(lia)) as IHk.
  pose proof (rsum_closed k) as Hr.
  (* CV + 5*S1 = 2*S2 + S0   (term-wise, via IH:  rsum2 j + 5 C(j+1) = 2 C(j+2) + C j) *)
  assert (HCV : CV + 5 * S1 = 2 * S2 + S0).
  { unfold CV, S0, S1, S2.
    rewrite <- (list_sum_map_scal 5 (fun i => catalan i * catalan (S k - i))).
    rewrite <- (list_sum_map_scal 2 (fun i => catalan i * catalan (S (S k) - i))).
    rewrite <- list_sum_map_add, <- list_sum_map_add.
    f_equal. apply map_ext_in. intros i Hi. rewrite in_seq in Hi.
    replace (S k - i) with (S (k - i)) by lia.
    replace (S (S k) - i) with (S (S (k - i))) by lia.
    pose proof (IH (k - i) ltac:(lia)) as Hi'. nia. }
  pose proof (catalan_conv k) as H0. fold S0 in H0.
  pose proof (conv_shift1 k) as H1. fold S1 in H1.
  pose proof (conv_shift2 k) as H2. fold S2 in H2.
  nia.
Qed.

Print Assumptions rsum2_closed.

(* ------------------------------------------------------------------ *)
(* second moment of S:  sum Srec^2 over allt n                          *)
(* ------------------------------------------------------------------ *)
Definition ssum2 (n : nat) : nat := list_sum (map (fun t => Srec t * Srec t) (allt n)).

Lemma srec_sq_id : forall t,
  Srec t * Srec t + 2 * size t * rlen t = size t * size t + rlen t * rlen t.
Proof. intro t. pose proof (srec_rlen_size t). nia. Qed.

(* ssum2 n + 2 n (sum rlen) = n^2 C_n + (sum rlen^2) *)
Lemma ssum2_via_rsum2 : forall n,
  ssum2 n + 2 * n * rsum n = n * n * catalan n + rsum2 n.
Proof.
  intro n.
  assert (H : list_sum (map (fun t => Srec t * Srec t + 2 * size t * rlen t) (allt n))
            = list_sum (map (fun t => size t * size t + rlen t * rlen t) (allt n))).
  { f_equal. apply map_ext. intro t. apply srec_sq_id. }
  rewrite (list_sum_map_add (fun t => Srec t * Srec t) (fun t => 2 * size t * rlen t)) in H.
  rewrite (list_sum_map_add (fun t => size t * size t) (fun t => rlen t * rlen t)) in H.
  (* size t = n on allt n, so the two size-dependent sums collapse *)
  erewrite (map_ext_in (fun t => 2 * size t * rlen t) (fun t => 2 * n * rlen t)) in H;
    [| intros t Ht; rewrite (allt_size n n t (Nat.le_refl _) Ht); reflexivity].
  erewrite (map_ext_in (fun t => size t * size t) (fun t => n * n)) in H;
    [| intros t Ht; rewrite (allt_size n n t (Nat.le_refl _) Ht); reflexivity].
  rewrite (list_sum_map_scal (2 * n) rlen) in H.
  rewrite list_sum_const in H.
  change (list_sum (map (fun t => Srec t * Srec t) (allt n))) with (ssum2 n) in H.
  change (list_sum (map (fun t => rlen t * rlen t) (allt n))) with (rsum2 n) in H.
  change (list_sum (map rlen (allt n))) with (rsum n) in H.
  unfold catalan. nia.
Qed.

(* exact closed form:  sum S^2 + (2n+5) C_{n+1} = (n+1)^2 C_n + 2 C_{n+2} *)
Theorem ssum2_closed : forall n,
  ssum2 n + (2 * n + 5) * catalan (S n)
  = (n + 1) * (n + 1) * catalan n + 2 * catalan (S (S n)).
Proof.
  intro n.
  pose proof (ssum2_via_rsum2 n) as Hsq.
  pose proof (rsum_closed n) as Hr.
  pose proof (rsum2_closed n) as Hr2.
  nia.
Qed.

(* the population sum of pops_N^2 (= pops_M^2) over the size-n trees *)
Theorem pops_sq_sum_closed : forall n,
  tsum (fun t => pops_N (ip t) * pops_N (ip t)) (trees_of_size n n)
    + (2 * n + 5) * catalan (S n)
  = (n + 1) * (n + 1) * catalan n + 2 * catalan (S (S n)).
Proof.
  intro n. rewrite (tsum_trees_of_size_allt (fun t => pops_N (ip t) * pops_N (ip t)) n).
  erewrite map_ext; [| intro t; rewrite pops_N_Srec; reflexivity].
  change (list_sum (map (fun t => Srec t * Srec t) (allt n))) with (ssum2 n).
  apply ssum2_closed.
Qed.

Print Assumptions pops_sq_sum_closed.

(* ------------------------------------------------------------------ *)
(* E[S^2] cleared, and the variance Var[S] = E[S^2] - E[S]^2.           *)
(* ------------------------------------------------------------------ *)

(* (n+2)(n+3) E[S^2] is a polynomial in n: clearing C_{n+1}, C_{n+2}
   against C_n with catalan_ratio (at n and at n+1). *)
Theorem ESQ_rational : forall n,
  (n + 2) * (n + 3) * tsum (fun t => pops_N (ip t) * pops_N (ip t)) (trees_of_size n n)
    + 2 * (n + 3) * (2 * n + 5) * (2 * n + 1) * catalan n
  = ((n + 1) * (n + 1) * (n + 2) * (n + 3) + 8 * (2 * n + 3) * (2 * n + 1)) * catalan n.
Proof.
  intro n. pose proof (pops_sq_sum_closed n) as Hsq.
  pose proof (catalan_ratio n) as Hr0.
  pose proof (catalan_ratio (S n)) as Hr1.
  replace (S n + 2) with (n + 3) in Hr1 by lia.
  replace (2 * S n + 1) with (2 * n + 3) in Hr1 by lia.
  nia.
Qed.

(* The variance, cleared of its C_n^2 denominator and expressed purely in
   Catalan numbers (no ratio needed):  C_n^2 * Var[S] = 2 C_{n+2} C_n
   - 3 C_{n+1} C_n - C_{n+1}^2, stated as the corresponding additive identity. *)
Theorem VarS_catalan : forall n,
  tsum (fun t => pops_N (ip t) * pops_N (ip t)) (trees_of_size n n) * catalan n
    + 3 * catalan (S n) * catalan n + catalan (S n) * catalan (S n)
  = 2 * catalan (S (S n)) * catalan n
    + tsum (fun t => pops_N (ip t)) (trees_of_size n n)
      * tsum (fun t => pops_N (ip t)) (trees_of_size n n).
Proof.
  intro n. pose proof (pops_sq_sum_closed n) as Hsq.
  pose proof (pops_sum_closed n) as Hs.
  set (T2 := tsum (fun t => pops_N (ip t) * pops_N (ip t)) (trees_of_size n n)) in *.
  set (T := tsum (fun t => pops_N (ip t)) (trees_of_size n n)) in *.
  nia.
Qed.

Print Assumptions ESQ_rational.
Print Assumptions VarS_catalan.

(* Sanity: C_n^2 * Var[S] = 1,14,168,1980 for n=2..5, i.e. Var[S] =
   1/4, 14/25, 6/7, 55/49 (over C_n^2 = 4,25,196,1764). *)
Example varS_small :
  map (fun n => 2 * catalan (S (S n)) * catalan n
                - 3 * catalan (S n) * catalan n - catalan (S n) * catalan (S n))
      [2;3;4;5] = [1; 14; 168; 1980].
Proof. vm_compute. reflexivity. Qed.
