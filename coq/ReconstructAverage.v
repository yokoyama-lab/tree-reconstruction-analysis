(* ReconstructAverage.v
   First milestone of the average-case mechanization (the analytic direction
   flagged in the roadmap of formal_verification.tex): the average-case
   DECOMPOSITION of the comparison counts over the uniform Catalan model, and a
   validation of the published closed forms over the verified tree enumeration.

   The pointwise counts are already mechanized for all n:
       A_M (ip t) = 2*size t - 1 + pops_M             (ReconstructM)
       A_N (ip t) = pops_N + full t + size t + 2      (ReconstructN + ReconstructLcount,
                                                        using lcount_N = full + 1)
   Summing over any population of non-empty trees and dividing by its size gives
       E[A_N] = E[S] + E[P_2] + E[size + 2],
   and over a size-n population (every tree has the same size) the last term is
   exactly n+2:   E[A_N] = E[S] + E[P_2] + n + 2.   This is the analytically
   load-bearing structural step of the average-case analysis (Paper I), here
   machine-checked for ALL n and axiom-free.

   The remaining ingredient -- the rational closed forms E[S] = n(n-1)/(n+2) and
   E[P_2] = (#leaves - 1 averaged) -- needs the Catalan-convolution recurrence on
   the enumeration count; pending that, we VALIDATE the published closed forms
       E[A_M] = n(n-1)/(n+2) + 2n-1,
       E[A_N] = n(n-1)/(n+2) + (n+2) + (n-1)(n-2)/(2(2n-1))
   exactly over the verified Catalan enumeration for every n <= 9 (cleared of
   denominators, so the checks are integer identities).

   Build:  rocq c Trees.v Dictionary.v Reconstruct.v ReconstructM.v
                  ReconstructN.v ReconstructLcount.v   (first)
           rocq c ReconstructAverage.v
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
Require Import ReconstructDyck.

(* Sum of a statistic over a list of trees. *)
Fixpoint tsum (f : tree -> nat) (ts : list tree) : nat :=
  match ts with
  | []        => 0
  | t :: ts'  => f t + tsum f ts'
  end.

(* ------------------------------------------------------------------ *)
(* 1. The pointwise counts, in sum-ready additive form.                *)
(* ------------------------------------------------------------------ *)
Lemma AN_pointwise : forall t, t <> Leaf ->
  total_comparisons_N (ip t) = pops_N (ip t) + full t + size t + 2.
Proof.
  intros t Hne. rewrite (total_comparisons_N_count t Hne), (lcount_N_full t Hne). lia.
Qed.

Lemma AM_pointwise : forall t, t <> Leaf ->
  total_comparisons_M (ip t) = pops_M (ip t) + (2 * size t - 1).
Proof.
  intros t Hne. rewrite (total_comparisons_M_count t Hne).
  assert (1 <= size t) by (destruct t; [congruence | cbn [size]; lia]). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The average-case decomposition over any non-empty-tree list.     *)
(* ------------------------------------------------------------------ *)
Lemma tsum_AN_decomp : forall ts, (forall t, In t ts -> t <> Leaf) ->
  tsum (fun t => total_comparisons_N (ip t)) ts
  = tsum (fun t => pops_N (ip t)) ts + tsum full ts
    + tsum (fun t => size t + 2) ts.
Proof.
  induction ts as [|t ts IH]; intros Hne; [reflexivity|].
  cbn [tsum]. rewrite (AN_pointwise t (Hne t (or_introl eq_refl))).
  rewrite IH by (intros u Hu; apply Hne; right; exact Hu). lia.
Qed.

Lemma tsum_AM_decomp : forall ts, (forall t, In t ts -> t <> Leaf) ->
  tsum (fun t => total_comparisons_M (ip t)) ts
  = tsum (fun t => pops_M (ip t)) ts + tsum (fun t => 2 * size t - 1) ts.
Proof.
  induction ts as [|t ts IH]; intros Hne; [reflexivity|].
  cbn [tsum]. rewrite (AM_pointwise t (Hne t (or_introl eq_refl))).
  rewrite IH by (intros u Hu; apply Hne; right; exact Hu). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The size-n population: every tree has size n, so the size term    *)
(*    factors out as (n+2) * (number of size-n trees) = (n+2) * C_n.    *)
(* ------------------------------------------------------------------ *)
(* trees_of_size is defined in ReconstructCatalan, where its count is proved to
   be exactly catalan n (length_trees_of_size). *)

Lemma trees_of_size_size : forall n bound t,
  In t (trees_of_size n bound) -> size t = n.
Proof.
  intros n bound t. unfold trees_of_size. rewrite filter_In.
  intros [_ H]. apply Nat.eqb_eq in H. exact H.
Qed.

Lemma trees_of_size_nonleaf : forall n bound t,
  1 <= n -> In t (trees_of_size n bound) -> t <> Leaf.
Proof.
  intros n bound t Hn Ht. pose proof (trees_of_size_size n bound t Ht) as Hsz.
  destruct t; [cbn [size] in Hsz; lia | discriminate].
Qed.

Lemma tsum_size_plus2 : forall n ts, (forall t, In t ts -> size t = n) ->
  tsum (fun t => size t + 2) ts = (n + 2) * length ts.
Proof.
  induction ts as [|t ts IH]; intros Hsz; [cbn [tsum length]; lia|].
  cbn [tsum length]. rewrite (Hsz t (or_introl eq_refl)).
  rewrite IH by (intros u Hu; apply Hsz; right; exact Hu). lia.
Qed.

(* E[A_N] = E[S] + E[P_2] + n + 2, mechanized as a sum identity over the
   size-n population, for every n >= 1 and axiom-free.  (Divide by
   length = C_n to read it as the expectation decomposition.) *)
Theorem avg_decomp_N : forall n bound, 1 <= n ->
  tsum (fun t => total_comparisons_N (ip t)) (trees_of_size n bound)
  = tsum (fun t => pops_N (ip t)) (trees_of_size n bound)
    + tsum full (trees_of_size n bound)
    + (n + 2) * length (trees_of_size n bound).
Proof.
  intros n bound Hn.
  rewrite (tsum_AN_decomp _ (fun t => trees_of_size_nonleaf n bound t Hn)).
  rewrite (tsum_size_plus2 n _ (trees_of_size_size n bound)). reflexivity.
Qed.

(* E[A_M] = E[S] + (2n - 1), likewise. *)
Theorem avg_decomp_M : forall n bound, 1 <= n ->
  tsum (fun t => total_comparisons_M (ip t)) (trees_of_size n bound)
  = tsum (fun t => pops_M (ip t)) (trees_of_size n bound)
    + (2 * n - 1) * length (trees_of_size n bound).
Proof.
  intros n bound Hn.
  rewrite (tsum_AM_decomp _ (fun t => trees_of_size_nonleaf n bound t Hn)).
  f_equal.
  (* tsum (fun t => 2*size t - 1) = (2n-1) * length, since size t = n *)
  assert (H : forall ts, (forall t, In t ts -> size t = n) ->
            tsum (fun t => 2 * size t - 1) ts = (2 * n - 1) * length ts).
  { induction ts as [|t ts IH]; intros Hsz; [cbn [tsum length]; lia|].
    cbn [tsum length]. rewrite (Hsz t (or_introl eq_refl)).
    rewrite IH by (intros u Hu; apply Hsz; right; exact Hu). lia. }
  apply H, trees_of_size_size.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. Early validation of the published closed forms over the verified  *)
(*    Catalan enumeration (n <= 9), as integer identities.              *)
(*    These finite checks are now SUPERSEDED by the unconditional, all-n *)
(*    theorems EAM_rational and EAN_rational (ReconstructES.v); they are *)
(*    retained only as fast sanity checks corroborating those proofs.    *)
(* ------------------------------------------------------------------ *)

(* E[A_M] = n(n-1)/(n+2) + 2n-1  <=>  (n+2)*sum A_M = (n(n-1)+(2n-1)(n+2))*C_n. *)
Theorem EAM_closed_form_upto_9 :
  forallb (fun n => Nat.eqb
     ((n + 2) * tsum (fun t => total_comparisons_M (ip t)) (trees_of_size n 9))
     ((n * (n - 1) + (2 * n - 1) * (n + 2)) * length (trees_of_size n 9)))
   (seq 1 9) = true.
Proof. vm_compute. reflexivity. Qed.

(* E[A_N] = n(n-1)/(n+2) + (n+2) + (n-1)(n-2)/(2(2n-1));  clearing the common
   denominator 2(n+2)(2n-1):
     2(n+2)(2n-1) * sum A_N
       = [ 2(2n-1)n(n-1) + 2(n+2)^2(2n-1) + (n+2)(n-1)(n-2) ] * C_n. *)
Theorem EAN_closed_form_upto_9 :
  forallb (fun n => Nat.eqb
     (2 * (n + 2) * (2 * n - 1)
        * tsum (fun t => total_comparisons_N (ip t)) (trees_of_size n 9))
     (( 2 * (2 * n - 1) * n * (n - 1)
        + 2 * (n + 2) * (n + 2) * (2 * n - 1)
        + (n + 2) * (n - 1) * (n - 2) ) * length (trees_of_size n 9)))
   (seq 1 9) = true.
Proof. vm_compute. reflexivity. Qed.

(* The enumeration counts are the Catalan numbers, e.g. n=1..6: 1,1,2,5,14,42. *)
Example catalan_counts :
  map (fun n => length (trees_of_size n 6)) (seq 0 7) = [1; 1; 2; 5; 14; 42; 132].
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* 5. The decomposition with the verified Catalan denominator C_n.      *)
(*    Dividing by length = catalan n (ReconstructCatalan) reads these    *)
(*    as the average-case expectation decompositions over the uniform    *)
(*    Catalan model on the C_n size-n trees.                             *)
(* ------------------------------------------------------------------ *)
Theorem avg_decomp_N_catalan : forall n, 1 <= n ->
  tsum (fun t => total_comparisons_N (ip t)) (trees_of_size n n)
  = tsum (fun t => pops_N (ip t)) (trees_of_size n n)
    + tsum full (trees_of_size n n)
    + (n + 2) * catalan n.
Proof.
  intros n Hn. rewrite <- (length_trees_of_size n n (Nat.le_refl n)).
  apply avg_decomp_N; exact Hn.
Qed.

Theorem avg_decomp_M_catalan : forall n, 1 <= n ->
  tsum (fun t => total_comparisons_M (ip t)) (trees_of_size n n)
  = tsum (fun t => pops_M (ip t)) (trees_of_size n n)
    + (2 * n - 1) * catalan n.
Proof.
  intros n Hn. rewrite <- (length_trees_of_size n n (Nat.le_refl n)).
  apply avg_decomp_M; exact Hn.
Qed.

Print Assumptions avg_decomp_N.
Print Assumptions avg_decomp_M.
Print Assumptions avg_decomp_N_catalan.

(* ================================================================== *)
(* 6. Exact closed forms for the moment sums over the size-n model.    *)
(*    These are the numerators of the average-case expectations; over  *)
(*    the uniform Catalan model (denominator catalan n) they give      *)
(*       E[full] = E[P_2] = (n*C_{n-1} - C_n) / C_n,                    *)
(*       E[leaves]        = n*C_{n-1} / C_n.                            *)
(*    Proved for ALL n, axiom-free (ReconstructMoments).               *)
(* ================================================================== *)

Lemma tsum_as_listsum : forall f ts, tsum f ts = list_sum (map f ts).
Proof. intros f ts. induction ts as [|t ts IH]; cbn [tsum map list_sum]; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma tsum_trees_of_size_allt : forall f n,
  tsum f (trees_of_size n n) = list_sum (map f (allt n)).
Proof.
  intros f n. rewrite tsum_as_listsum, (trees_of_size_eq_allt n n (Nat.le_refl n)).
  reflexivity.
Qed.

(* E[P_2] numerator: sum of full over the C_n size-n trees = n*C_{n-1} - C_n. *)
Theorem EP2_numerator : forall n, 1 <= n ->
  tsum full (trees_of_size n n) + catalan n = n * catalan (n - 1).
Proof. intros n Hn. rewrite tsum_trees_of_size_allt. exact (SF_closed n Hn). Qed.

(* E[leaves] numerator. *)
Theorem Eleaves_numerator : forall n, 1 <= n ->
  tsum leaves (trees_of_size n n) = n * catalan (n - 1).
Proof. intros n Hn. rewrite tsum_trees_of_size_allt. exact (SL_closed n). Qed.

Print Assumptions EP2_numerator.

(* ------------------------------------------------------------------ *)
(* The literal rational form E[P_2] = (n-1)(n-2)/(2(2n-1)), cleared of   *)
(* its denominator, follows from EP2_numerator and the classical        *)
(* Catalan product-formula recurrence (ratio).  We state the ratio as    *)
(* an explicit hypothesis catalan_ratio: (n+2) C_{n+1} = 2(2n+1) C_n      *)
(* (validated numerically below for all n <= 12); the implication is      *)
(* mechanized unconditionally.                                            *)
(* ------------------------------------------------------------------ *)

(* The Catalan product-formula recurrence is now a PROVED theorem, axiom-free,
   for all n (ReconstructDyck.catalan_ratio), so E[P_2] = (n-1)(n-2)/(2(2n-1))
   holds unconditionally, cleared of denominators. *)
Theorem EP2_rational : forall n, 2 <= n ->
  2 * (2 * n - 1) * tsum full (trees_of_size n n) = (n - 1) * (n - 2) * catalan n.
Proof.
  intros n Hn.
  pose proof (EP2_numerator n ltac:(lia)) as H.
  (* ratio at n-1 : (n+1) C_n = 2(2n-1) C_{n-1} *)
  pose proof (catalan_ratio (n - 1)) as Hr1.
  replace (S (n - 1)) with n in Hr1 by lia.
  replace (n - 1 + 2) with (n + 1) in Hr1 by lia.
  replace (2 * (n - 1) + 1) with (2 * n - 1) in Hr1 by lia.
  (* atoms: full-sum s, C_{n-1} = a, C_n = b ; H: s + b = n*a ; Hr1: (n+1)*b = 2(2n-1)*a *)
  nia.
Qed.

Print Assumptions EP2_rational.
