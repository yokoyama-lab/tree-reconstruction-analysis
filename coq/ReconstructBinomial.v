(* ReconstructBinomial.v
   Binomial coefficients (Pascal) and the closed-form Catalan number
       cb n := binom (2n) n - binom (2n) (n+1).
   We prove, purely from Pascal's rule and the adjacent-column ("absorption")
   identity, that cb obeys the classical Catalan product-formula recurrence
       (n+2) * cb (n+1) = 2 * (2n+1) * cb n          (cb_ratio)
   with cb 0 = 1.  This is the number-theoretic content of the Catalan ratio;
   the bridge catalan = cb (combinatorics) is established separately.

   Build:  rocq c ReconstructBinomial.v       (Standard library only)
   Rocq Prover 9.1.0.  Axiom-free. *)

From Stdlib Require Import Arith Lia List.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* 1. binom and Pascal                                                 *)
(* ------------------------------------------------------------------ *)
Fixpoint binom (n : nat) : nat -> nat :=
  match n with
  | 0    => fun k => match k with 0 => 1 | S _ => 0 end
  | S n' => fun k => match k with 0 => 1 | S k' => binom n' k' + binom n' (S k') end
  end.

Lemma binom_0r : forall n, binom n 0 = 1.
Proof. destruct n; reflexivity. Qed.

Lemma binom_pascal : forall n k, binom (S n) (S k) = binom n k + binom n (S k).
Proof. reflexivity. Qed.

Lemma binom_0Sk : forall k, binom 0 (S k) = 0.
Proof. reflexivity. Qed.

Lemma binom_gt : forall n k, n < k -> binom n k = 0.
Proof.
  induction n as [|n IH]; intros k Hk.
  - destruct k; [lia | reflexivity].
  - destruct k as [|k]; [lia|].
    rewrite binom_pascal, IH, IH by lia. reflexivity.
Qed.

Lemma binom_diag : forall n, binom n n = 1.
Proof.
  induction n as [|n IH]; [reflexivity|].
  rewrite binom_pascal, IH, (binom_gt n (S n)) by lia. reflexivity.
Qed.

Lemma binom_sym : forall n k, k <= n -> binom n k = binom n (n - k).
Proof.
  induction n as [|n IH]; intros k Hk.
  - assert (k = 0) by lia. subst. reflexivity.
  - destruct k as [|k].
    + rewrite binom_0r, Nat.sub_0_r, binom_diag. reflexivity.
    + (* binom (S n) (S k) = binom (S n) (S n - S k) = binom (S n) (n - k) *)
      replace (S n - S k) with (n - k) by lia.
      destruct (Nat.eq_dec (n - k) 0) as [Hnk|Hnk].
      * (* k = n: binom (S n)(S n) = 1 = binom (S n) 0 *)
        assert (k = n) by lia. subst k.
        rewrite binom_pascal, binom_diag, (binom_gt n (S n)) by lia.
        rewrite Hnk, binom_0r. reflexivity.
      * rewrite binom_pascal.
        (* RHS: binom (S n)(n-k) = binom n (n-k-1) + binom n (n-k) *)
        destruct (n - k) as [|m] eqn:Hm; [lia|].
        rewrite binom_pascal.
        rewrite (IH k) by lia. rewrite (IH (S k)) by lia.
        replace (n - k) with (S m) by lia.
        replace (n - S k) with m by lia.
        cbn [Nat.sub]. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. Adjacent-column (absorption) identity                            *)
(*       binom m (k+1) * (k+1) = binom m k * (m - k)                    *)
(* ------------------------------------------------------------------ *)
Lemma binom_adj : forall m k, binom m (S k) * S k = binom m k * (m - k).
Proof.
  induction m as [|m IH]; intros k.
  - cbn. lia.
  - destruct k as [|k].
    + (* binom (S m) 1 * 1 = binom (S m) 0 * (S m - 0) = 1 * (S m) *)
      rewrite binom_0r, Nat.sub_0_r.
      (* binom (S m) 1 = binom m 0 + binom m 1 = 1 + binom m 1 *)
      rewrite binom_pascal, binom_0r.
      (* IH at k = 0 : binom m 1 * 1 = binom m 0 * (m - 0) = m *)
      pose proof (IH 0) as H0. rewrite binom_0r, Nat.sub_0_r in H0.
      lia.
    + (* general *)
      rewrite (binom_pascal m (S k)).
      rewrite (binom_pascal m k).
      (* LHS = (binom m k + binom m (S k)) * (S (S k))
         RHS = (binom m (S k) + binom m (S (S k))) * (S m - S k) *)
      pose proof (IH k) as Hk.        (* binom m (S k) * S k = binom m k * (m - k) *)
      pose proof (IH (S k)) as HSk.   (* binom m (S (S k)) * S (S k) = binom m (S k) * (m - S k) *)
      replace (S m - S k) with (m - k) by lia.
      nia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2b. Unimodality of a binomial row (needed to discharge subtraction   *)
(*     clamps in the ballot reflection count)                           *)
(* ------------------------------------------------------------------ *)

(* one increasing step on the left half: 2k+1 <= N -> binom N k <= binom N (S k) *)
Lemma binom_step_le : forall N k, S (k + k) <= N -> binom N k <= binom N (S k).
Proof.
  intros N k Hk. pose proof (binom_adj N k) as H.  (* binom N (S k)*S k = binom N k*(N-k) *)
  (* N - k >= S k, and binom N k * (N-k) = binom N (S k) * S k *)
  nia.
Qed.

(* monotone on the left half: i <= j and 2j <= N+1 -> binom N i <= binom N j *)
Lemma binom_mono_left : forall N j i, i <= j -> S j + j <= S N -> binom N i <= binom N j.
Proof.
  intros N j. induction j as [|j IHj]; intros i Hi Hj.
  - assert (i = 0) by lia. subst. apply Nat.le_refl.
  - destruct (Nat.eq_dec i (S j)) as [->|Hne]; [apply Nat.le_refl|].
    apply Nat.le_trans with (binom N j).
    + apply IHj; lia.
    + apply binom_step_le. lia.
Qed.

(* decreasing on the right half: N <= 2k -> binom N (S k) <= binom N k *)
Lemma binom_step_ge : forall N k, S k <= N -> N <= k + k -> binom N (S k) <= binom N k.
Proof.
  intros N k Hk1 Hk2. pose proof (binom_adj N k) as H. nia.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The closed-form Catalan number and its ratio                     *)
(* ------------------------------------------------------------------ *)
Definition cb (n : nat) : nat := binom (2 * n) n - binom (2 * n) (S n).

Lemma cb_0 : cb 0 = 1.
Proof. reflexivity. Qed.

(* binom (2n) (n+1) <= binom (2n) n, and (n+1) binom(2n)(n+1) = n binom(2n)n. *)
Lemma binom_2n_adj : forall n,
  binom (2 * n) (S n) * S n = binom (2 * n) n * n.
Proof.
  intro n. pose proof (binom_adj (2 * n) n) as H.
  replace (2 * n - n) with n in H by lia. exact H.
Qed.

Lemma binom_2n_le : forall n, binom (2 * n) (S n) <= binom (2 * n) n.
Proof.
  intro n. pose proof (binom_2n_adj n) as H. nia.
Qed.

(* (n+1) * cb n = binom (2n) n. *)
Lemma cb_central : forall n, S n * cb n = binom (2 * n) n.
Proof.
  intro n. unfold cb.
  pose proof (binom_2n_adj n) as Hadj.
  pose proof (binom_2n_le n) as Hle.
  (* S n * (binom(2n)n - binom(2n)(Sn)) = binom(2n)n *)
  rewrite Nat.mul_sub_distr_l. nia.
Qed.

(* (n+1) binom(2n+1)n = (2n+1) binom(2n)n. *)
Lemma binom_2n1_n : forall n,
  S n * binom (S (2 * n)) n = (2 * n + 1) * binom (2 * n) n.
Proof.
  destruct n as [|n].
  - reflexivity.
  - (* binom (S (2*S n)) (S n) = binom (2*S n) n + binom (2*S n) (S n) *)
    rewrite binom_pascal.
    set (m := 2 * S n).
    pose proof (binom_adj m n) as Hb.   (* binom m (S n) * S n = binom m n * (m - n) *)
    replace (m - n) with (S (S n)) in Hb by (unfold m; lia).
    nia.
Qed.

(* binom(2n+2)(n+1) = 2 binom(2n+1)n. *)
Lemma binom_2n2 : forall n,
  binom (S (S (2 * n))) (S n) = 2 * binom (S (2 * n)) n.
Proof.
  intro n. rewrite binom_pascal.
  assert (Hs : binom (S (2 * n)) (S n) = binom (S (2 * n)) n).
  { rewrite (binom_sym (S (2 * n)) (S n)) by lia.
    replace (S (2 * n) - S n) with n by lia. reflexivity. }
  rewrite Hs. lia.
Qed.

(* The central-binomial doubling: (n+1) binom(2n+2)(n+1) = 2(2n+1) binom(2n)n. *)
Lemma central_step : forall n,
  S n * binom (2 * S n) (S n) = 2 * (2 * n + 1) * binom (2 * n) n.
Proof.
  intro n. replace (2 * S n) with (S (S (2 * n))) by lia.
  rewrite binom_2n2.
  pose proof (binom_2n1_n n) as H1.
  nia.
Qed.

Theorem cb_ratio : forall n, (n + 2) * cb (S n) = 2 * (2 * n + 1) * cb n.
Proof.
  intro n.
  (* (S n) * (n+2) * cb (S n) = (S n) * binom(2(Sn))(Sn) ... use cb_central *)
  pose proof (cb_central (S n)) as HcS.   (* S (S n) * cb (S n) = binom (2(Sn)) (Sn) *)
  pose proof (cb_central n) as Hc.        (* S n * cb n = binom (2n) n *)
  pose proof (central_step n) as Hstep.   (* S n * binom(2(Sn))(Sn) = 2(2n+1) binom(2n)n *)
  (* From HcS: binom(2(Sn))(Sn) = (n+2) cb(Sn).  Substitute into Hstep:
       S n * (n+2) cb(Sn) = 2(2n+1) * (S n * cb n)
     cancel S n. *)
  assert (Hkey : S n * ((n + 2) * cb (S n)) = S n * (2 * (2 * n + 1) * cb n)).
  { replace (n + 2) with (S (S n)) by lia.
    rewrite HcS, Hstep. nia. }
  apply Nat.mul_cancel_l in Hkey; [exact Hkey | lia].
Qed.

(* Sanity: cb n = 1,1,2,5,14,42,132. *)
Example cb_values : map cb (List.seq 0 7) = [1;1;2;5;14;42;132]%list.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions cb_ratio.
