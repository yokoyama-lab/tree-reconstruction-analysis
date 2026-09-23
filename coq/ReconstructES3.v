(* ReconstructES3.v
   Exact closed forms for Var[P2] and Cov[S,P2] (Proposition 8 of paper_ja.tex).

   Engine (same as ReconstructES / ReconstructES2): sums over the row allt n of
   all size-n trees, decomposed at the root into cells, then strong induction
   with Catalan convolutions.  Two new ingredients appear here.

   (1) The "central" sequence Dc m := (m+1) C_m  (= binom(2m,m)), whose
       self-convolution is 4^m and whose Catalan-weighted convolutions are
       obtained from the ratio  (m+1) Dc (m+1) = 2 (2m+1) Dc m  by the
       reflection trick of weighted_conv.

   (2) For the covariance the joint statistic  rlen t * leaves t  is summed;
       its cell decomposition mixes the rlen cell (right subtree only) with the
       leaves cell (both subtrees), which is why both engines are needed.

   Closed forms proved (Dc m = (m+1) C_m, all n >= 1):
       sum_{|t|=n} leaves^2        = (n-2) Dc(n-2) + Dc(n-1)
       4 sum_{|t|=n} rlen*leaves   + 12 Dc(n+1) + 2 C_{n-1} = 2 Dc(n+2) + 19 Dc n
   from which the paper's rational forms of Var[P2] and Cov[S,P2] follow
   (VarP2_rational, CovSP2_rational), stated with all denominators cleared.

   Rocq Prover 9.1.  Standard library only.  Axiom-free. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import Trees Dictionary Reconstruct ReconstructM ReconstructN ReconstructLcount.
Require Import ReconstructCatalan ReconstructMoments ReconstructPops.
Require Import ReconstructBinomial ReconstructDyck ReconstructAverage.
Require Import ReconstructES ReconstructES2.

(* ================================================================== *)
(* 1. The central sequence Dc and its convolutions                     *)
(* ================================================================== *)

Definition Dc (m : nat) : nat := (m + 1) * catalan m.

Lemma Dc_ratio : forall m, (m + 1) * Dc (S m) = 2 * (2 * m + 1) * Dc m.
Proof.
  intro m. unfold Dc. pose proof (catalan_ratio m) as H.
  replace (S m + 1) with (m + 2) by lia. nia.
Qed.

Lemma Dc_0 : Dc 0 = 1.
Proof. reflexivity. Qed.

Lemma Dc_1 : Dc 1 = 2.
Proof. reflexivity. Qed.

(* generic reflection: 2 * sum_i i X_i X_{m-i} = m * sum_i X_i X_{m-i} *)
Lemma sym_weight : forall (X : nat -> nat) m,
  2 * list_sum (map (fun i => i * (X i * X (m - i))) (seq 0 (S m)))
  = m * list_sum (map (fun i => X i * X (m - i)) (seq 0 (S m))).
Proof.
  intros X m.
  set (g := fun i => i * (X i * X (m - i))).
  assert (Href : list_sum (map g (seq 0 (S m)))
               = list_sum (map (fun j => g (m - j)) (seq 0 (S m))))
    by apply list_sum_seq_reflect.
  replace (2 * list_sum (map g (seq 0 (S m))))
    with (list_sum (map g (seq 0 (S m))) + list_sum (map (fun j => g (m - j)) (seq 0 (S m))))
    by (rewrite <- Href; lia).
  rewrite <- list_sum_map_add.
  rewrite <- (list_sum_map_scal m (fun i => X i * X (m - i))).
  f_equal. apply map_ext_in. intros j Hj. rewrite in_seq in Hj. unfold g.
  replace (m - (m - j)) with j by lia.
  remember (m - j) as w eqn:Hw.
  assert (Hm : m = j + w) by lia. subst m. nia.
Qed.

(* reflection of a two-sequence convolution *)
Lemma conv_reflect : forall (X Y : nat -> nat) m,
  list_sum (map (fun i => X i * Y (m - i)) (seq 0 (S m)))
  = list_sum (map (fun i => Y i * X (m - i)) (seq 0 (S m))).
Proof.
  intros X Y m.
  rewrite (list_sum_seq_reflect (fun i => X i * Y (m - i)) m).
  f_equal. apply map_ext_in. intros j Hj. rewrite in_seq in Hj.
  replace (m - (m - j)) with j by lia. lia.
Qed.

(* self-convolution of Dc *)
Definition aconv (m : nat) : nat :=
  list_sum (map (fun i => Dc i * Dc (m - i)) (seq 0 (S m))).

(* weighted self-convolution, weight on the first index *)
Definition awconv (m : nat) : nat :=
  list_sum (map (fun i => i * (Dc i * Dc (m - i))) (seq 0 (S m))).

Lemma awconv_sym : forall m, 2 * awconv m = m * aconv m.
Proof. intro m. unfold awconv, aconv. apply sym_weight. Qed.

(* the shift: drop i = 0, reindex i = S j, and use the ratio *)
Lemma awconv_S : forall m,
  awconv (S m) = 4 * awconv m + 2 * aconv m.
Proof.
  intro m. unfold awconv, aconv.
  rewrite (sum_seq_shift1 (fun i => i * (Dc i * Dc (S m - i))) (S m)).
  cbv beta. rewrite Nat.mul_0_l, Nat.add_0_l.
  rewrite <- (list_sum_map_scal 4 (fun i => i * (Dc i * Dc (m - i)))).
  rewrite <- (list_sum_map_scal 2 (fun i => Dc i * Dc (m - i))).
  rewrite <- list_sum_map_add.
  f_equal. apply map_ext_in. intros j Hj. rewrite in_seq in Hj.
  replace (S m - S j) with (m - j) by lia.
  pose proof (Dc_ratio j) as Hr. nia.
Qed.

Theorem aconv_pow : forall m, aconv m = 4 ^ m.
Proof.
  induction m as [|m IH].
  - reflexivity.
  - pose proof (awconv_sym (S m)) as H1.
    pose proof (awconv_S m) as H2.
    pose proof (awconv_sym m) as H3.
    (* (S m) aconv (S m) = 2 awconv (S m) = 8 awconv m + 4 aconv m
                        = 4 m aconv m + 4 aconv m = 4 (S m) aconv m *)
    assert (Hk : S m * aconv (S m) = S m * (4 * aconv m)) by nia.
    apply Nat.mul_cancel_l in Hk; [| lia].
    rewrite Hk, IH. cbn [Nat.pow]. lia.
Qed.

(* Catalan-Dc convolution, Dc on the first index *)
Definition bconv (m : nat) : nat :=
  list_sum (map (fun i => Dc i * catalan (m - i)) (seq 0 (S m))).

Lemma bconv_closed : forall m, 2 * bconv m = Dc (S m).
Proof.
  intro m. unfold bconv, Dc.
  replace (S m + 1) with (m + 2) by lia.
  rewrite <- (weighted_conv m). reflexivity.
Qed.

(* weighted Catalan-Dc convolution, weight on the Dc index *)
Definition gconv (m : nat) : nat :=
  list_sum (map (fun i => i * (Dc i * catalan (m - i))) (seq 0 (S m))).

Lemma gconv_S : forall m, gconv (S m) = 4 * gconv m + 2 * bconv m.
Proof.
  intro m. unfold gconv, bconv.
  rewrite (sum_seq_shift1 (fun i => i * (Dc i * catalan (S m - i))) (S m)).
  cbv beta. rewrite Nat.mul_0_l, Nat.add_0_l.
  rewrite <- (list_sum_map_scal 4 (fun i => i * (Dc i * catalan (m - i)))).
  rewrite <- (list_sum_map_scal 2 (fun i => Dc i * catalan (m - i))).
  rewrite <- list_sum_map_add.
  f_equal. apply map_ext_in. intros j Hj. rewrite in_seq in Hj.
  replace (S m - S j) with (m - j) by lia.
  pose proof (Dc_ratio j) as Hr. nia.
Qed.

Theorem gconv_closed : forall m, gconv m + 4 ^ m = (2 * m + 1) * Dc m.
Proof.
  induction m as [|m IH].
  - reflexivity.
  - rewrite gconv_S.
    pose proof (bconv_closed m) as Hb.
    pose proof (Dc_ratio m) as Hr.
    cbn [Nat.pow]. nia.
Qed.

Print Assumptions aconv_pow.
Print Assumptions gconv_closed.

(* ================================================================== *)
(* 2. Second moment of the leaf count                                  *)
(* ================================================================== *)

Definition SL2 (n : nat) : nat := list_sum (map (fun t => leaves t * leaves t) (allt n)).

Lemma isleaf_leaves : forall t, isleaf t * leaves t = 0.
Proof. intro t; destruct t; reflexivity. Qed.

Lemma isleaf_rlen : forall t, isleaf t * rlen t = 0.
Proof. intro t; destruct t; reflexivity. Qed.

Lemma isleaf_sq : forall t, isleaf t * isleaf t = isleaf t.
Proof. intro t; destruct t; reflexivity. Qed.

Lemma leaves_sq_node : forall l r,
  leaves (Node l r) * leaves (Node l r)
  = leaves l * leaves l + leaves r * leaves r + 2 * (leaves l * leaves r)
    + isleaf l * isleaf r.
Proof.
  intros l r. rewrite leaves_node.
  pose proof (isleaf_leaves l). pose proof (isleaf_leaves r).
  pose proof (isleaf_sq l). pose proof (isleaf_sq r). nia.
Qed.

Lemma cell_leaves_sq : forall i j,
  cell (fun t => leaves t * leaves t) i j
  = catalan j * SL2 i + catalan i * SL2 j + 2 * (SL i * SL j)
    + (if Nat.eqb i 0 then 1 else 0) * (if Nat.eqb j 0 then 1 else 0).
Proof.
  intros i j. unfold cell.
  erewrite map_ext; [| intro lr; rewrite leaves_sq_node; reflexivity].
  rewrite (list_sum_map_add
             (fun lr => leaves (fst lr) * leaves (fst lr) + leaves (snd lr) * leaves (snd lr)
                        + 2 * (leaves (fst lr) * leaves (snd lr)))
             (fun lr => isleaf (fst lr) * isleaf (snd lr))).
  rewrite (list_sum_map_add
             (fun lr => leaves (fst lr) * leaves (fst lr) + leaves (snd lr) * leaves (snd lr))
             (fun lr => 2 * (leaves (fst lr) * leaves (snd lr)))).
  rewrite (list_sum_map_add
             (fun lr => leaves (fst lr) * leaves (fst lr))
             (fun lr => leaves (snd lr) * leaves (snd lr))).
  rewrite (list_sum_prod_fst (fun t => leaves t * leaves t) (allt i) (allt j)).
  rewrite (list_sum_prod_snd (fun t => leaves t * leaves t) (allt i) (allt j)).
  rewrite (list_sum_map_scal 2 (fun lr => leaves (fst lr) * leaves (snd lr))).
  rewrite (list_sum_prod_mul leaves leaves (allt i) (allt j)).
  rewrite (list_sum_prod_mul isleaf isleaf (allt i) (allt j)).
  rewrite sum_isleaf_allt, sum_isleaf_allt.
  unfold SL2, SL, catalan. reflexivity.
Qed.

Lemma SL2_rec : forall k,
  SL2 (S k)
  = list_sum (map (fun i => catalan (k - i) * SL2 i + catalan i * SL2 (k - i)
                            + 2 * (SL i * SL (k - i))) (seq 0 (S k)))
    + (if Nat.eqb k 0 then 1 else 0).
Proof.
  intro k. unfold SL2 at 1. rewrite sum_allt_S.
  erewrite map_ext; [|intro i; rewrite cell_leaves_sq; reflexivity].
  rewrite (list_sum_map_add
             (fun i => catalan (k - i) * SL2 i + catalan i * SL2 (k - i) + 2 * (SL i * SL (k - i)))
             (fun i => (if Nat.eqb i 0 then 1 else 0) * (if Nat.eqb (k - i) 0 then 1 else 0))).
  f_equal.
  destruct (Nat.eqb_spec k 0) as [Hk|Hk].
  - subst k. reflexivity.
  - apply list_sum_map_zero'. intros i Hi. rewrite in_seq in Hi.
    destruct (Nat.eqb_spec i 0) as [Hi0|Hi0]; [|reflexivity].
    subst i. rewrite Nat.sub_0_r.
    destruct (Nat.eqb_spec k 0) as [|]; [contradiction|]. lia.
Qed.

Example SL2_values : map SL2 (seq 0 6) = [0; 1; 2; 8; 32; 130].
Proof. vm_compute. reflexivity. Qed.

(* index bookkeeping *)
Lemma sum_drop0 : forall (F : nat -> nat) n, F 0 = 0 ->
  list_sum (map F (seq 0 (S n))) = list_sum (map (fun j => F (S j)) (seq 0 n)).
Proof. intros F n H0. rewrite (sum_seq_shift1 F n), H0. reflexivity. Qed.

Lemma sum_drop_last : forall (F : nat -> nat) n, F n = 0 ->
  list_sum (map F (seq 0 (S n))) = list_sum (map F (seq 0 n)).
Proof.
  intros F n Hn. rewrite (seq_S n 0), map_app, list_sum_app, Nat.add_0_l.
  cbn [map]. rewrite list_sum_single, Hn. lia.
Qed.

Lemma SL_S_Dc : forall a, SL (S a) = Dc a.
Proof.
  intro a. rewrite SL_closed. unfold Dc.
  replace (S a - 1) with a by lia. lia.
Qed.

(* sum_i C_{k-i} SL2 i over i <= k, k = S (S k'), under the inductive hypothesis *)
Lemma SL2_conv_eval : forall k',
  (forall j, 1 <= j -> j <= S (S k') -> SL2 j = (j - 2) * Dc (j - 2) + Dc (j - 1)) ->
  list_sum (map (fun i => catalan (S (S k') - i) * SL2 i) (seq 0 (S (S (S k')))))
  = bconv (S k') + gconv k'.
Proof.
  intros k' IH.
  rewrite sum_drop0 by (cbn [SL2]; rewrite Nat.mul_0_r; reflexivity).
  erewrite map_ext_in;
    [| intros j Hj; rewrite in_seq in Hj;
       rewrite (IH (S j)) by lia;
       replace (S (S k') - S j) with (S k' - j) by lia;
       replace (S j - 2) with (j - 1) by lia;
       replace (S j - 1) with j by lia;
       rewrite Nat.mul_add_distr_l; reflexivity].
  rewrite (list_sum_map_add
             (fun j => catalan (S k' - j) * ((j - 1) * Dc (j - 1)))
             (fun j => catalan (S k' - j) * Dc j)).
  (* second summand is bconv (S k') *)
  replace (list_sum (map (fun j => catalan (S k' - j) * Dc j) (seq 0 (S (S k')))))
    with (bconv (S k'))
    by (unfold bconv; f_equal; apply map_ext; intro j; lia).
  (* first summand: drop j = 0, shift, is gconv k' *)
  rewrite (sum_drop0 (fun j => catalan (S k' - j) * ((j - 1) * Dc (j - 1))))
    by (cbn [Nat.sub]; rewrite Nat.mul_0_l, Nat.mul_0_r; reflexivity).
  replace (list_sum (map (fun j => catalan (S k' - S j) * ((S j - 1) * Dc (S j - 1))) (seq 0 (S k'))))
    with (gconv k').
  - lia.
  - unfold gconv. f_equal. apply map_ext_in. intros j Hj. rewrite in_seq in Hj.
    replace (S k' - S j) with (k' - j) by lia.
    replace (S j - 1) with j by lia. lia.
Qed.

(* sum_i SL i SL (k-i) over i <= k, k = S (S k') *)
Lemma SL_selfconv_eval : forall k',
  list_sum (map (fun i => SL i * SL (S (S k') - i)) (seq 0 (S (S (S k'))))) = aconv k'.
Proof.
  intro k'.
  rewrite sum_drop0 by reflexivity.
  rewrite (sum_drop_last (fun j => SL (S j) * SL (S (S k') - S j)) (S k'))
    by (rewrite Nat.sub_diag; cbn [SL]; rewrite Nat.mul_0_r; reflexivity).
  unfold aconv. f_equal. apply map_ext_in. intros a Ha. rewrite in_seq in Ha.
  replace (S (S k') - S a) with (S (k' - a)) by lia.
  rewrite !SL_S_Dc. reflexivity.
Qed.

Theorem SL2_closed : forall n, 1 <= n -> SL2 n = (n - 2) * Dc (n - 2) + Dc (n - 1).
Proof.
  intro n. induction n as [n IH] using lt_wf_ind. intro Hn.
  destruct n as [|[|[|k']]]; [lia | reflexivity | reflexivity |].
  rewrite SL2_rec. cbn [Nat.eqb]. rewrite Nat.add_0_r.
  rewrite (list_sum_map_add
             (fun i => catalan (S (S k') - i) * SL2 i + catalan i * SL2 (S (S k') - i))
             (fun i => 2 * (SL i * SL (S (S k') - i)))).
  rewrite (list_sum_map_add
             (fun i => catalan (S (S k') - i) * SL2 i)
             (fun i => catalan i * SL2 (S (S k') - i))).
  rewrite (list_sum_map_scal 2 (fun i => SL i * SL (S (S k') - i))).
  (* the two SL2 convolutions are reflections of each other *)
  replace (list_sum (map (fun i => catalan i * SL2 (S (S k') - i)) (seq 0 (S (S (S k'))))))
    with (list_sum (map (fun i => catalan (S (S k') - i) * SL2 i) (seq 0 (S (S (S k'))))))
    by (rewrite (conv_reflect catalan SL2 (S (S k'))); f_equal; apply map_ext; intro i; lia).
  rewrite (SL2_conv_eval k') by (intros j Hj1 Hj2; apply IH; lia).
  rewrite SL_selfconv_eval.
  replace (S (S (S k')) - 2) with (S k') by lia.
  replace (S (S (S k')) - 1) with (S (S k')) by lia.
  pose proof (bconv_closed (S k')) as Hb.
  pose proof (gconv_closed k') as Hg.
  pose proof (aconv_pow k') as Ha.
  pose proof (Dc_ratio k') as Hr.
  nia.
Qed.

Print Assumptions SL2_closed.

(* ================================================================== *)
(* 3. The joint sum  sum rlen * leaves  (final stack height x leaves)  *)
(* ================================================================== *)

Definition SLR (n : nat) : nat := list_sum (map (fun t => rlen t * leaves t) (allt n)).

(* right subtree non-empty: rlen is inherited from the right subtree *)
Lemma rl_node_pos : forall l ra rb,
  rlen (Node l (Node ra rb)) * leaves (Node l (Node ra rb))
  = leaves l * rlen (Node ra rb) + rlen (Node ra rb) * leaves (Node ra rb).
Proof.
  intros l ra rb.
  change (rlen (Node l (Node ra rb))) with (rlen (Node ra rb)).
  rewrite leaves_node. change (isleaf (Node ra rb)) with 0. nia.
Qed.

(* right subtree empty: the height grows by one *)
Lemma rl_node_0 : forall l,
  rlen (Node l Leaf) * leaves (Node l Leaf) = rlen l * leaves l + leaves l + isleaf l.
Proof.
  intro l.
  change (rlen (Node l Leaf)) with (S (rlen l)).
  rewrite leaves_node. change (isleaf Leaf) with 1. change (leaves Leaf) with 0.
  pose proof (isleaf_leaves l). pose proof (isleaf_rlen l). pose proof (isleaf_sq l). nia.
Qed.

Lemma cell_rl_pos : forall i j, 1 <= j ->
  cell (fun t => rlen t * leaves t) i j = SL i * rsum j + catalan i * SLR j.
Proof.
  intros i j Hj. unfold cell.
  erewrite (map_ext_in _ (fun lr => leaves (fst lr) * rlen (snd lr)
                                    + rlen (snd lr) * leaves (snd lr))).
  2:{ intros lr Hlr. destruct lr as [ll rr]. apply in_prod_iff in Hlr.
      destruct Hlr as [_ Hr]. cbn [fst snd].
      pose proof (allt_size j j rr (Nat.le_refl j) Hr) as Hsz.
      destruct rr as [|ra rb]; [cbn in Hsz; lia | apply rl_node_pos]. }
  rewrite (list_sum_map_add (fun lr => leaves (fst lr) * rlen (snd lr))
                            (fun lr => rlen (snd lr) * leaves (snd lr))).
  rewrite (list_sum_prod_mul leaves rlen (allt i) (allt j)).
  rewrite (list_sum_prod_snd (fun t => rlen t * leaves t) (allt i) (allt j)).
  unfold SL, rsum, SLR, catalan. reflexivity.
Qed.

Lemma cell_rl_0 : forall i,
  cell (fun t => rlen t * leaves t) i 0 = SLR i + SL i + (if Nat.eqb i 0 then 1 else 0).
Proof.
  intro i. unfold cell.
  unfold allt at 2. rewrite trees_table_0. cbn [nth].
  rewrite list_prod_single_r, map_map.
  erewrite (map_ext _ (fun l => rlen l * leaves l + leaves l + isleaf l));
    [| intro l; cbn [fst snd]; apply rl_node_0].
  rewrite (list_sum_map_add (fun l => rlen l * leaves l + leaves l) isleaf).
  rewrite (list_sum_map_add (fun l => rlen l * leaves l) leaves).
  rewrite sum_isleaf_allt. unfold SLR, SL. reflexivity.
Qed.

Lemma cell_rl : forall i j,
  cell (fun t => rlen t * leaves t) i j
  = SL i * rsum j + catalan i * SLR j
    + (if Nat.eqb j 0 then SLR i + SL i + (if Nat.eqb i 0 then 1 else 0) else 0).
Proof.
  intros i j. destruct j as [|j].
  - rewrite cell_rl_0. cbn [Nat.eqb].
    change (rsum 0) with 0. change (SLR 0) with 0. lia.
  - rewrite cell_rl_pos by lia. cbn [Nat.eqb]. lia.
Qed.

Lemma SLR_rec : forall k,
  SLR (S k)
  = list_sum (map (fun i => SL i * rsum (k - i) + catalan i * SLR (k - i)) (seq 0 (S k)))
    + (SLR k + SL k + (if Nat.eqb k 0 then 1 else 0)).
Proof.
  intro k. unfold SLR at 1. rewrite sum_allt_S.
  erewrite map_ext; [| intro i; rewrite cell_rl; reflexivity].
  rewrite (list_sum_map_add
             (fun i => SL i * rsum (k - i) + catalan i * SLR (k - i))
             (fun i => if Nat.eqb (k - i) 0 then SLR i + SL i + (if Nat.eqb i 0 then 1 else 0) else 0)).
  f_equal.
  rewrite (seq_S k 0), map_app, list_sum_app, Nat.add_0_l.
  rewrite (list_sum_map_zero'
             (fun i => if Nat.eqb (k - i) 0 then SLR i + SL i + (if Nat.eqb i 0 then 1 else 0) else 0)
             (seq 0 k)).
  - cbn [map]. rewrite list_sum_single, Nat.sub_diag. cbn [Nat.eqb]. lia.
  - intros i Hi. rewrite in_seq in Hi.
    destruct (Nat.eqb_spec (k - i) 0); [lia | reflexivity].
Qed.

Example SLR_values : map SLR (seq 0 6) = [0; 1; 3; 10; 36; 134].
Proof. vm_compute. reflexivity. Qed.

(* the SL-rsum convolution, k = S k'':  A + bconv k'' + Dc (S k'') = bconv (S k'') *)
Lemma SL_rsum_conv_eval : forall k'',
  list_sum (map (fun i => SL i * rsum (S k'' - i)) (seq 0 (S (S k''))))
    + bconv k'' + Dc (S k'')
  = bconv (S k'').
Proof.
  intro k''.
  (* add sum SL i C(k-i) to both sides via rsum_closed, termwise *)
  assert (Hsplit :
    list_sum (map (fun i => SL i * rsum (S k'' - i)) (seq 0 (S (S k''))))
    + list_sum (map (fun i => SL i * catalan (S k'' - i)) (seq 0 (S (S k''))))
    = list_sum (map (fun i => SL i * catalan (S (S k'' - i))) (seq 0 (S (S k''))))).
  { rewrite <- list_sum_map_add. f_equal. apply map_ext. intro i.
    pose proof (rsum_closed (S k'' - i)). nia. }
  (* sum SL i C(k-i) = bconv k'' *)
  assert (H1 : list_sum (map (fun i => SL i * catalan (S k'' - i)) (seq 0 (S (S k''))))
             = bconv k'').
  { rewrite sum_drop0 by reflexivity. unfold bconv. f_equal.
    apply map_ext_in. intros a Ha. rewrite in_seq in Ha.
    rewrite SL_S_Dc. replace (S k'' - S a) with (k'' - a) by lia. reflexivity. }
  (* sum SL i C(S(k-i)) = bconv (S k'') - Dc (S k'') *)
  assert (H2 : list_sum (map (fun i => SL i * catalan (S (S k'' - i))) (seq 0 (S (S k''))))
             + Dc (S k'') = bconv (S k'')).
  { rewrite sum_drop0 by reflexivity. unfold bconv.
    rewrite (seq_S (S k'') 0), map_app, list_sum_app, Nat.add_0_l.
    cbn [map]. rewrite list_sum_single, Nat.sub_diag. change (catalan 0) with 1.
    rewrite Nat.mul_1_r. f_equal. f_equal.
    apply map_ext_in. intros a Ha. rewrite in_seq in Ha.
    rewrite SL_S_Dc. replace (S (S k'' - S a)) with (S k'' - a) by lia. reflexivity. }
  lia.
Qed.

(* the bconv shifts by 1, 2, 3 *)
Lemma bconv_shift1 : forall m,
  bconv (S m) = catalan (S m) + list_sum (map (fun j => Dc (S j) * catalan (m - j)) (seq 0 (S m))).
Proof.
  intro m. unfold bconv. rewrite (sum_seq_shift1 (fun i => Dc i * catalan (S m - i)) (S m)).
  cbv beta. rewrite Nat.sub_0_r, Dc_0, Nat.mul_1_l. reflexivity.
Qed.

Lemma bconv_shift2 : forall m,
  bconv (S (S m))
  = catalan (S (S m)) + 2 * catalan (S m)
    + list_sum (map (fun j => Dc (S (S j)) * catalan (m - j)) (seq 0 (S m))).
Proof.
  intro m. rewrite bconv_shift1.
  rewrite (sum_seq_shift1 (fun j => Dc (S j) * catalan (S m - j)) (S m)).
  cbv beta. rewrite Nat.sub_0_r, Dc_1.
  replace (list_sum (map (fun j => Dc (S (S j)) * catalan (S m - S j)) (seq 0 (S m))))
    with (list_sum (map (fun j => Dc (S (S j)) * catalan (m - j)) (seq 0 (S m)))).
  - lia.
  - reflexivity.
Qed.

Lemma bconv_shift3 : forall m,
  bconv (S (S (S m)))
  = catalan (S (S (S m))) + 2 * catalan (S (S m)) + 6 * catalan (S m)
    + list_sum (map (fun j => Dc (S (S (S j))) * catalan (m - j)) (seq 0 (S m))).
Proof.
  intro m. rewrite bconv_shift2.
  rewrite (sum_seq_shift1 (fun j => Dc (S (S j)) * catalan (S m - j)) (S m)).
  cbv beta. rewrite Nat.sub_0_r. change (Dc 2) with 6.
  replace (list_sum (map (fun j => Dc (S (S (S j))) * catalan (S m - S j)) (seq 0 (S m))))
    with (list_sum (map (fun j => Dc (S (S (S j))) * catalan (m - j)) (seq 0 (S m)))).
  - lia.
  - reflexivity.
Qed.

(* the C-SLR convolution under the inductive hypothesis, k = S k'' *)
Lemma SLR_conv_eval : forall k'',
  (forall j, 1 <= j -> j <= S k'' ->
     4 * SLR j + 12 * Dc (j + 1) + 2 * catalan (j - 1) = 2 * Dc (j + 2) + 19 * Dc j) ->
  4 * list_sum (map (fun i => catalan i * SLR (S k'' - i)) (seq 0 (S (S k''))))
    + 12 * bconv (S (S k'')) + 2 * catalan (S (S (S k'')))
    + 4 * catalan (S (S k'')) + 9 * catalan (S k'')
  = 2 * bconv (S (S (S k''))) + 19 * bconv (S k'') + 12 * catalan (S (S k'')).
Proof.
  intros k'' IH.
  (* reflect, drop j = 0, so the sum runs over SLR (S j) C(k'' - j) *)
  replace (list_sum (map (fun i => catalan i * SLR (S k'' - i)) (seq 0 (S (S k'')))))
    with (list_sum (map (fun j => SLR (S j) * catalan (k'' - j)) (seq 0 (S k'')))).
  2:{ rewrite (conv_reflect catalan SLR (S k'')).
      rewrite (sum_drop0 (fun i => SLR i * catalan (S k'' - i)) (S k'')) by reflexivity.
      reflexivity. }
  (* termwise IH, multiplied through by catalan (k'' - j) *)
  set (s1 := list_sum (map (fun j => Dc (S j) * catalan (k'' - j)) (seq 0 (S k'')))).
  set (s2 := list_sum (map (fun j => Dc (S (S j)) * catalan (k'' - j)) (seq 0 (S k'')))).
  set (s3 := list_sum (map (fun j => Dc (S (S (S j))) * catalan (k'' - j)) (seq 0 (S k'')))).
  set (c0 := list_sum (map (fun j => catalan j * catalan (k'' - j)) (seq 0 (S k'')))).
  assert (Hterm :
    4 * list_sum (map (fun j => SLR (S j) * catalan (k'' - j)) (seq 0 (S k'')))
      + 12 * s2 + 2 * c0
    = 2 * s3 + 19 * s1).
  { unfold s1, s2, s3, c0.
    rewrite <- (list_sum_map_scal 4 (fun j => SLR (S j) * catalan (k'' - j))).
    rewrite <- (list_sum_map_scal 12 (fun j => Dc (S (S j)) * catalan (k'' - j))).
    rewrite <- (list_sum_map_scal 2 (fun j => catalan j * catalan (k'' - j))).
    rewrite <- (list_sum_map_scal 2 (fun j => Dc (S (S (S j))) * catalan (k'' - j))).
    rewrite <- (list_sum_map_scal 19 (fun j => Dc (S j) * catalan (k'' - j))).
    rewrite <- !list_sum_map_add. f_equal. apply map_ext_in.
    intros j Hj. rewrite in_seq in Hj.
    pose proof (IH (S j) ltac:(lia) ltac:(lia)) as H.
    replace (S j + 1) with (S (S j)) in H by lia.
    replace (S j + 2) with (S (S (S j))) in H by lia.
    replace (S j - 1) with j in H by lia. nia. }
  pose proof (bconv_shift1 (S k'')) as B1.
  pose proof (bconv_shift2 k'') as B2.
  pose proof (bconv_shift3 k'') as B3.
  pose proof (catalan_conv k'') as C0.
  fold s1 in B1. fold s2 in B2. fold s3 in B3. fold c0 in C0.
  (* B1 is stated at S k'': its sum runs over seq 0 (S (S k'')) with m = S k''; realign *)
  clear B1.
  assert (B1' : bconv (S k'') = catalan (S k'') + s1).
  { unfold s1. rewrite bconv_shift1. reflexivity. }
  nia.
Qed.

Theorem SLR_closed : forall n, 1 <= n ->
  4 * SLR n + 12 * Dc (n + 1) + 2 * catalan (n - 1) = 2 * Dc (n + 2) + 19 * Dc n.
Proof.
  intro n. induction n as [n IH] using lt_wf_ind. intro Hn.
  destruct n as [|[|k'']]; [lia | vm_compute; reflexivity |].
  rewrite SLR_rec. cbn [Nat.eqb]. rewrite Nat.add_0_r.
  rewrite (list_sum_map_add
             (fun i => SL i * rsum (S k'' - i))
             (fun i => catalan i * SLR (S k'' - i))).
  pose proof (SL_rsum_conv_eval k'') as HA.
  pose proof (SLR_conv_eval k'' (fun j H1 H2 => IH j ltac:(lia) H1)) as HB.
  pose proof (IH (S k'') ltac:(lia) ltac:(lia)) as HI.
  rewrite SL_S_Dc.
  pose proof (bconv_closed k'') as Hb0.
  pose proof (bconv_closed (S k'')) as Hb1.
  pose proof (bconv_closed (S (S k''))) as Hb2.
  pose proof (bconv_closed (S (S (S k'')))) as Hb3.
  replace (S k'' + 1) with (S (S k'')) in HI by lia.
  replace (S k'' + 2) with (S (S (S k''))) in HI by lia.
  replace (S k'' - 1) with k'' in HI by lia.
  replace (S (S k'') + 1) with (S (S (S k''))) by lia.
  replace (S (S k'') + 2) with (S (S (S (S k'')))) by lia.
  replace (S (S k'') - 1) with (S k'') by lia.
  unfold Dc in *.
  pose proof (catalan_ratio k'') as R0.
  pose proof (catalan_ratio (S k'')) as R1.
  pose proof (catalan_ratio (S (S k''))) as R2.
  pose proof (catalan_ratio (S (S (S k'')))) as R3.
  nia.
Qed.

Print Assumptions SLR_closed.

(* ================================================================== *)
(* 4. Translation to the paper's statistics and the rational forms     *)
(* ================================================================== *)

(* second moment of P2 = full, and the mixed moment S * P2, over allt n *)
Definition SF2 (n : nat) : nat := list_sum (map (fun t => full t * full t) (allt n)).
Definition SSP2 (n : nat) : nat := list_sum (map (fun t => Srec t * full t) (allt n)).

Lemma allt_nonleaf : forall n t, 1 <= n -> In t (allt n) -> t <> Leaf.
Proof.
  intros n t Hn Hin Ht. subst t.
  pose proof (allt_size n n Leaf (Nat.le_refl _) Hin) as Hsz. cbn in Hsz. lia.
Qed.

(* full^2 + 2 leaves = leaves^2 + 1 on non-leaves *)
Lemma SF2_via_SL2 : forall n, 1 <= n -> SF2 n + 2 * SL n = SL2 n + catalan n.
Proof.
  intros n Hn. unfold SF2, SL, SL2, catalan.
  assert (H : list_sum (map (fun t => full t * full t + 2 * leaves t) (allt n))
            = list_sum (map (fun t => leaves t * leaves t + 1) (allt n))).
  { f_equal. apply map_ext_in. intros t Ht.
    pose proof (full_leaves t (allt_nonleaf n t Hn Ht)). nia. }
  rewrite (list_sum_map_add (fun t => full t * full t) (fun t => 2 * leaves t)) in H.
  rewrite (list_sum_map_scal 2 leaves) in H.
  rewrite (list_sum_map_add (fun t => leaves t * leaves t) (fun _ => 1)) in H.
  rewrite (list_sum_const 1) in H. lia.
Qed.

(* Srec * full + rlen * leaves = n * full + rlen on size-n non-leaves *)
Lemma SSP2_via_SLR : forall n, 1 <= n -> SSP2 n + SLR n = n * SF n + rsum n.
Proof.
  intros n Hn. unfold SSP2, SLR, SF, rsum.
  assert (H : list_sum (map (fun t => Srec t * full t + rlen t * leaves t) (allt n))
            = list_sum (map (fun t => n * full t + rlen t) (allt n))).
  { f_equal. apply map_ext_in. intros t Ht.
    pose proof (full_leaves t (allt_nonleaf n t Hn Ht)) as H.
    pose proof (srec_rlen_size t) as Hs.
    pose proof (allt_size n n t (Nat.le_refl _) Ht) as Hsz. nia. }
  rewrite (list_sum_map_add (fun t => Srec t * full t) (fun t => rlen t * leaves t)) in H.
  rewrite (list_sum_map_add (fun t => n * full t) rlen) in H.
  rewrite (list_sum_map_scal n full) in H. lia.
Qed.

Example SF2_values : map SF2 (seq 1 6) = [0; 0; 1; 6; 32; 160].
Proof. vm_compute. reflexivity. Qed.

Example SSP2_values : map SSP2 (seq 1 6) = [0; 0; 2; 16; 96; 510].
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The purely algebraic steps, isolated so that lia sees a small context. *)
(* Each is a linear certificate: the identity is a Z-linear combination   *)
(* of the hypotheses scaled by explicit polynomial multipliers (computed  *)
(* offline; the multipliers appear literally in the E/F/G equations).      *)
(* ------------------------------------------------------------------ *)

Lemma varP2_alg : forall m c0 c1 c2 F2 F,
  F2 + (m + 2) * c1 = m * ((m + 1) * c0) + c2 ->
  F + c2 = (m + 2) * c1 ->
  (m + 2) * c1 = 2 * (2 * m + 1) * c0 ->
  (m + 3) * c2 = 2 * (2 * m + 3) * c1 ->
  2 * (2 * m + 3) * (2 * m + 3) * (2 * m + 1) * (c2 * F2)
  = (m + 2) * (m + 3) * (m + 1) * m * (c2 * c2)
    + 2 * (2 * m + 3) * (2 * m + 3) * (2 * m + 1) * (F * F).
Proof.
  intros m c0 c1 c2 F2 F HF2 HF R0 R1.
  set (K := 2 * (2 * m + 3) * (2 * m + 3) * (2 * m + 1)).
  assert (E1 : K * (c2 * (F2 + (m + 2) * c1)) = K * (c2 * (m * ((m + 1) * c0) + c2)))
    by (rewrite HF2; reflexivity).
  assert (E2 : K * ((F + c2) * (F + c2)) = K * (((m + 2) * c1) * ((m + 2) * c1)))
    by (rewrite HF; reflexivity).
  assert (E3 : K * (c2 * (F + c2)) = K * (c2 * ((m + 2) * c1)))
    by (rewrite HF; reflexivity).
  (* certificate: G = A R0 + B R1,
       A = - c2 m (m+1) (2m+3)^2,
       B = (m+2) c1 (4m^3+16m^2+19m+6) - (m+2) c2 (m^2+m) *)
  assert (E4 : (c2 * m * (m + 1) * (2 * m + 3) * (2 * m + 3)) * ((m + 2) * c1)
             = (c2 * m * (m + 1) * (2 * m + 3) * (2 * m + 3)) * (2 * (2 * m + 1) * c0))
    by (rewrite R0; reflexivity).
  assert (E5 : ((m + 2) * c1 * (4 * m * m * m + 16 * m * m + 19 * m + 6)) * ((m + 3) * c2)
             = ((m + 2) * c1 * (4 * m * m * m + 16 * m * m + 19 * m + 6)) * (2 * (2 * m + 3) * c1))
    by (rewrite R1; reflexivity).
  assert (E6 : ((m + 2) * c2 * (m * m + m)) * ((m + 3) * c2)
             = ((m + 2) * c2 * (m * m + m)) * (2 * (2 * m + 3) * c1))
    by (rewrite R1; reflexivity).
  unfold K in *. clear HF2 HF R0 R1. lia.
Qed.

Lemma covSP2_alg : forall m c1 c2 c3 c4 P F L Rs SS,
  SS + c3 = (m + 3) * c2 ->
  F + c2 = (m + 2) * c1 ->
  P + L = (m + 2) * F + Rs ->
  4 * L + 12 * ((m + 4) * c3) + 2 * c1 = 2 * ((m + 5) * c4) + 19 * ((m + 3) * c2) ->
  Rs + c2 = c3 ->
  (m + 3) * c2 = 2 * (2 * m + 3) * c1 ->
  (m + 4) * c3 = 2 * (2 * m + 5) * c2 ->
  (m + 5) * c4 = 2 * (2 * m + 7) * c3 ->
  4 * ((m + 4) * (2 * m + 3) * (c2 * P))
  = 4 * (2 * (m + 1) * m * (c2 * c2) + (m + 4) * (2 * m + 3) * (SS * F)).
Proof.
  intros m c1 c2 c3 c4 P F L Rs SS HSS HF HP HR Hrs R1 R2 R3.
  set (Kc := (m + 4) * (2 * m + 3)).
  assert (F1 : Kc * (c2 * (4 * (P + L))) = Kc * (c2 * (4 * ((m + 2) * F + Rs))))
    by (rewrite HP; reflexivity).
  assert (F2 : Kc * (c2 * (4 * L + 12 * ((m + 4) * c3) + 2 * c1))
             = Kc * (c2 * (2 * ((m + 5) * c4) + 19 * ((m + 3) * c2))))
    by (rewrite HR; reflexivity).
  assert (F3 : Kc * (c2 * (4 * (Rs + c2))) = Kc * (c2 * (4 * c3)))
    by (rewrite Hrs; reflexivity).
  assert (F4 : Kc * (c2 * (4 * ((m + 2) * (F + c2)))) = Kc * (c2 * (4 * ((m + 2) * ((m + 2) * c1)))))
    by (rewrite HF; reflexivity).
  assert (F5 : 4 * Kc * ((SS + c3) * (F + c2)) = 4 * Kc * (((m + 3) * c2) * ((m + 2) * c1)))
    by (rewrite HSS, HF; reflexivity).
  assert (F6 : 4 * Kc * (c2 * (SS + c3)) = 4 * Kc * (c2 * ((m + 3) * c2)))
    by (rewrite HSS; reflexivity).
  assert (F7 : 4 * Kc * (c3 * (F + c2)) = 4 * Kc * (c3 * ((m + 2) * c1)))
    by (rewrite HF; reflexivity).
  (* certificate: 4 G = A3 R3 + A2 R2 + A1 R1,
       A3 = -2 c2 (m+4)(2m+3),  A2 = 4 (2m+3) ((m+2) c1 + (m+5) c2),
       A1 = - c2 (6m^2 + 25m + 28) *)
  assert (G3 : (2 * c2 * (m + 4) * (2 * m + 3)) * ((m + 5) * c4)
             = (2 * c2 * (m + 4) * (2 * m + 3)) * (2 * (2 * m + 7) * c3))
    by (rewrite R3; reflexivity).
  assert (G2 : (4 * (2 * m + 3) * ((m + 2) * c1 + (m + 5) * c2)) * ((m + 4) * c3)
             = (4 * (2 * m + 3) * ((m + 2) * c1 + (m + 5) * c2)) * (2 * (2 * m + 5) * c2))
    by (rewrite R2; reflexivity).
  assert (G1 : (c2 * (6 * m * m + 25 * m + 28)) * ((m + 3) * c2)
             = (c2 * (6 * m * m + 25 * m + 28)) * (2 * (2 * m + 3) * c1))
    by (rewrite R1; reflexivity).
  unfold Kc in *. clear HSS HF HP HR Hrs R1 R2 R3. lia.
Qed.

(* --- the paper's rational closed form of Var[P2], denominators cleared ---
     Var[P2] = n(n+1)(n-1)(n-2) / (2 (2n-1)^2 (2n-3)),  i.e.
     2(2n-1)^2(2n-3) * (C_n * sum P2^2) = n(n+1)(n-1)(n-2) C_n^2 + 2(2n-1)^2(2n-3) (sum P2)^2 *)
Theorem VarP2_rational : forall n, 2 <= n ->
  2 * (2 * n - 1) * (2 * n - 1) * (2 * n - 3)
    * (catalan n * tsum (fun t => full t * full t) (trees_of_size n n))
  = n * (n + 1) * (n - 1) * (n - 2) * (catalan n * catalan n)
    + 2 * (2 * n - 1) * (2 * n - 1) * (2 * n - 3)
      * (tsum full (trees_of_size n n) * tsum full (trees_of_size n n)).
Proof.
  intros n Hn. destruct n as [|[|m]]; [lia | lia |].
  rewrite !tsum_trees_of_size_allt.
  change (list_sum (map (fun t => full t * full t) (allt (S (S m))))) with (SF2 (S (S m))).
  change (list_sum (map full (allt (S (S m))))) with (SF (S (S m))).
  pose proof (SF2_via_SL2 (S (S m)) ltac:(lia)) as H2.
  pose proof (SL2_closed (S (S m)) ltac:(lia)) as HL2.
  pose proof (SF_closed (S (S m)) ltac:(lia)) as HF.
  pose proof (SL_closed (S (S m))) as HL.
  pose proof (catalan_ratio m) as R0.
  pose proof (catalan_ratio (S m)) as R1.
  replace (S (S m) - 2) with m in * by lia.
  replace (S (S m) - 1) with (S m) in * by lia.
  unfold Dc in *.
  assert (HF2 : SF2 (S (S m)) + (m + 2) * catalan (S m)
                = m * ((m + 1) * catalan m) + catalan (S (S m))) by nia.
  assert (HF' : SF (S (S m)) + catalan (S (S m)) = (m + 2) * catalan (S m)) by lia.
  assert (R0' : (m + 2) * catalan (S m) = 2 * (2 * m + 1) * catalan m) by lia.
  assert (R1' : (m + 3) * catalan (S (S m)) = 2 * (2 * m + 3) * catalan (S m)) by lia.
  pose proof (varP2_alg m (catalan m) (catalan (S m)) (catalan (S (S m)))
                (SF2 (S (S m))) (SF (S (S m))) HF2 HF' R0' R1') as HA.
  clear - HA.
  replace (2 * S (S m) - 1) with (2 * m + 3) by lia.
  replace (2 * S (S m) - 3) with (2 * m + 1) by lia.
  replace (S (S m) - 1) with (S m) by lia.
  replace (S (S m) - 2) with m by lia.
  lia.
Qed.

(* --- the paper's rational closed form of Cov[S,P2], denominators cleared ---
     Cov[S,P2] = 2(n-1)(n-2) / ((n+2)(2n-1)),  i.e.
     (n+2)(2n-1) * (C_n * sum S P2) = 2(n-1)(n-2) C_n^2 + (n+2)(2n-1) (sum S)(sum P2) *)
Theorem CovSP2_rational : forall n, 2 <= n ->
  (n + 2) * (2 * n - 1)
    * (catalan n * tsum (fun t => pops_N (ip t) * full t) (trees_of_size n n))
  = 2 * (n - 1) * (n - 2) * (catalan n * catalan n)
    + (n + 2) * (2 * n - 1)
      * (tsum (fun t => pops_N (ip t)) (trees_of_size n n) * tsum full (trees_of_size n n)).
Proof.
  intros n Hn. destruct n as [|[|m]]; [lia | lia |].
  pose proof (pops_sum_closed (S (S m))) as HSS.
  pose proof (SF_closed (S (S m)) ltac:(lia)) as HF.
  pose proof (SSP2_via_SLR (S (S m)) ltac:(lia)) as HP.
  pose proof (SLR_closed (S (S m)) ltac:(lia)) as HR.
  pose proof (rsum_closed (S (S m))) as Hrs.
  pose proof (catalan_ratio (S m)) as R1.
  pose proof (catalan_ratio (S (S m))) as R2.
  pose proof (catalan_ratio (S (S (S m)))) as R3.
  rewrite (tsum_trees_of_size_allt (fun t => pops_N (ip t) * full t)).
  rewrite (tsum_trees_of_size_allt full).
  erewrite (map_ext (fun t => pops_N (ip t) * full t) (fun t => Srec t * full t))
    by (intro t; rewrite pops_N_Srec; reflexivity).
  change (list_sum (map (fun t => Srec t * full t) (allt (S (S m))))) with (SSP2 (S (S m))).
  change (list_sum (map full (allt (S (S m))))) with (SF (S (S m))).
  replace (S (S m) - 1) with (S m) in * by lia.
  replace (S (S m) + 1) with (S (S (S m))) in * by lia.
  replace (S (S m) + 2) with (S (S (S (S m)))) in * by lia.
  unfold Dc in *.
  assert (HSS' : tsum (fun t => pops_N (ip t)) (trees_of_size (S (S m)) (S (S m)))
                 + catalan (S (S (S m))) = (m + 3) * catalan (S (S m))) by lia.
  assert (HF' : SF (S (S m)) + catalan (S (S m)) = (m + 2) * catalan (S m)) by lia.
  assert (HP' : SSP2 (S (S m)) + SLR (S (S m)) = (m + 2) * SF (S (S m)) + rsum (S (S m))) by lia.
  assert (HR' : 4 * SLR (S (S m)) + 12 * ((m + 4) * catalan (S (S (S m)))) + 2 * catalan (S m)
                = 2 * ((m + 5) * catalan (S (S (S (S m))))) + 19 * ((m + 3) * catalan (S (S m))))
    by lia.
  assert (Hrs' : rsum (S (S m)) + catalan (S (S m)) = catalan (S (S (S m)))) by lia.
  assert (R1' : (m + 3) * catalan (S (S m)) = 2 * (2 * m + 3) * catalan (S m)) by lia.
  assert (R2' : (m + 4) * catalan (S (S (S m))) = 2 * (2 * m + 5) * catalan (S (S m))) by lia.
  assert (R3' : (m + 5) * catalan (S (S (S (S m)))) = 2 * (2 * m + 7) * catalan (S (S (S m)))) by lia.
  pose proof (covSP2_alg m (catalan (S m)) (catalan (S (S m))) (catalan (S (S (S m))))
                (catalan (S (S (S (S m))))) (SSP2 (S (S m))) (SF (S (S m))) (SLR (S (S m)))
                (rsum (S (S m))) (tsum (fun t => pops_N (ip t)) (trees_of_size (S (S m)) (S (S m))))
                HSS' HF' HP' HR' Hrs' R1' R2' R3') as HA.
  clear - HA.
  replace (2 * S (S m) - 1) with (2 * m + 3) by lia.
  replace (S (S m) - 1) with (S m) by lia.
  replace (S (S m) - 2) with m by lia.
  apply (Nat.mul_cancel_l _ _ 4); [lia |]. lia.
Qed.

Print Assumptions VarP2_rational.
Print Assumptions CovSP2_rational.
