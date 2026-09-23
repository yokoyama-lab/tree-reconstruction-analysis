(* ReconstructDyck.v  (part 1: bool-list enumeration and the column count)
   Towards catalan = cb (ReconstructBinomial), via lattice paths encoded as
   list bool (true = up/+1, false = down/-1).

   This file builds the counting foundation: an enumeration of all length-m
   bool-lists, and the fact that exactly binom m k of them have k trues.
   Later parts add the Dyck (nonnegative-prefix) predicate, the reflection
   count, and the tree<->Dyck bijection.

   Build:  rocq c ReconstructBinomial.v   (first)
           rocq c ReconstructDyck.v
   Rocq Prover 9.1.0.  Standard library only.  Axiom-free. *)

From Stdlib Require Import List Arith Lia Permutation Bool.
Import ListNotations.
Local Open Scope bool_scope.
Require Import ReconstructBinomial.
Require Import Trees.
Require Import Dictionary.
Require Import Reconstruct.
Require Import ReconstructCatalan.
Require Import ReconstructMoments.

(* ------------------------------------------------------------------ *)
(* list helpers                                                        *)
(* ------------------------------------------------------------------ *)
Lemma length_filter_map : forall {A B} (p : B -> bool) (f : A -> B) (l : list A),
  length (filter p (map f l)) = length (filter (fun x => p (f x)) l).
Proof.
  intros A B p f l. induction l as [|x l IH]; [reflexivity|].
  cbn [map filter]. destruct (p (f x)); cbn [length]; rewrite IH; reflexivity.
Qed.

Lemma filter_none : forall {A} (p : A -> bool) (l : list A),
  (forall x, p x = false) -> filter p l = [].
Proof.
  intros A p l H. induction l as [|x l IH]; [reflexivity|].
  cbn [filter]. rewrite H. exact IH.
Qed.

(* ------------------------------------------------------------------ *)
(* number of trues, and the enumeration of all length-m bool lists     *)
(* ------------------------------------------------------------------ *)
Fixpoint ntrue (w : list bool) : nat :=
  match w with
  | [] => 0
  | true :: w' => S (ntrue w')
  | false :: w' => ntrue w'
  end.

Fixpoint all_lists (m : nat) : list (list bool) :=
  match m with
  | 0 => [[]]
  | S m' => let r := all_lists m' in
            map (cons true) r ++ map (cons false) r
  end.

Lemma all_lists_length : forall m w, In w (all_lists m) -> length w = m.
Proof.
  induction m as [|m IH]; intros w Hin.
  - destruct Hin as [<-|[]]. reflexivity.
  - cbn [all_lists] in Hin. rewrite in_app_iff in Hin.
    destruct Hin as [Hin|Hin]; apply in_map_iff in Hin;
      destruct Hin as [w' [<- Hw']]; cbn [length]; rewrite (IH w' Hw'); reflexivity.
Qed.

(* exactly binom m k of the length-m lists have k trues *)
Theorem count_ntrue : forall m k,
  length (filter (fun w => Nat.eqb (ntrue w) k) (all_lists m)) = binom m k.
Proof.
  induction m as [|m IH]; intros k.
  - destruct k; reflexivity.
  - cbn [all_lists]. rewrite filter_app, length_app, !length_filter_map.
    destruct k as [|k].
    + (* k = 0: the "true" half is empty, the "false" half counts ntrue = 0 *)
      rewrite (filter_none (fun w' => Nat.eqb (ntrue (true :: w')) 0))
        by (intro w'; reflexivity).
      cbn [length].
      change (fun w' => Nat.eqb (ntrue (false :: w')) 0)
        with (fun w' => Nat.eqb (ntrue w') 0).
      rewrite IH, binom_0r. reflexivity.
    + change (fun w' => Nat.eqb (ntrue (true :: w')) (S k))
        with (fun w' => Nat.eqb (ntrue w') k).
      change (fun w' => Nat.eqb (ntrue (false :: w')) (S k))
        with (fun w' => Nat.eqb (ntrue w') (S k)).
      rewrite !IH, binom_pascal. reflexivity.
Qed.

(* Sanity: C(4,2) = 6 length-4 lists have 2 trues. *)
Example count_ntrue_4_2 :
  length (filter (fun w => Nat.eqb (ntrue w) 2) (all_lists 4)) = 6.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The Andre reflection: flip the suffix after the path (from height h) *)
(* first drops below 0 (a false read at height 0).                      *)
(* ------------------------------------------------------------------ *)
Fixpoint reflh (h : nat) (w : list bool) : list bool :=
  match w with
  | [] => []
  | true :: w'  => true  :: reflh (S h) w'
  | false :: w' => match h with
                   | 0    => false :: map negb w'
                   | S h' => false :: reflh h' w'
                   end
  end.
Definition refl (w : list bool) : list bool := reflh 0 w.

(* the path from height h goes below 0 at some prefix *)
Fixpoint badh (h : nat) (w : list bool) : bool :=
  match w with
  | [] => false
  | true :: w'  => badh (S h) w'
  | false :: w' => match h with 0 => true | S h' => badh h' w' end
  end.
Definition bad (w : list bool) : bool := badh 0 w.

Lemma map_negb_invol : forall w, map negb (map negb w) = w.
Proof.
  induction w as [|x w IH]; [reflexivity|].
  cbn [map]. rewrite IH, Bool.negb_involutive. reflexivity.
Qed.

(* refl is an involution (at every starting height) *)
Lemma reflh_invol : forall w h, reflh h (reflh h w) = w.
Proof.
  induction w as [|x w IH]; intros h; [reflexivity|].
  destruct x; cbn [reflh].
  - rewrite IH. reflexivity.
  - destruct h as [|h'].
    + cbn [reflh]. rewrite map_negb_invol. reflexivity.
    + cbn [reflh]. rewrite IH. reflexivity.
Qed.

Lemma refl_invol : forall w, refl (refl w) = w.
Proof. intro w. apply reflh_invol. Qed.

Lemma reflh_length : forall w h, length (reflh h w) = length w.
Proof.
  induction w as [|x w IH]; intros h; [reflexivity|].
  destruct x; cbn [reflh length].
  - rewrite IH. reflexivity.
  - destruct h; cbn [length]; [rewrite length_map | rewrite IH]; reflexivity.
Qed.

Lemma refl_length : forall w, length (refl w) = length w.
Proof. intro w. apply reflh_length. Qed.

Print Assumptions refl_invol.

(* on non-bad paths refl is the identity *)
Lemma reflh_id : forall w h, badh h w = false -> reflh h w = w.
Proof.
  induction w as [|x w IH]; intros h Hb; [reflexivity|].
  destruct x; cbn [reflh badh] in *.
  - rewrite IH by exact Hb. reflexivity.
  - destruct h as [|h']; [discriminate|].
    rewrite IH by exact Hb. reflexivity.
Qed.

Lemma refl_id : forall w, bad w = false -> refl w = w.
Proof. intros w. apply reflh_id. Qed.

(* ntrue (map negb w) + ntrue w = length w *)
Lemma ntrue_map_negb : forall w, ntrue (map negb w) + ntrue w = length w.
Proof.
  induction w as [|x w IH]; [reflexivity|].
  destruct x; cbn [map ntrue length negb]; lia.
Qed.

(* on a bad path the reflection trades trues for falses: ntrue + ntrue(refl) + 1 + h = length *)
Lemma ntrue_reflh : forall w h, badh h w = true ->
  ntrue (reflh h w) + ntrue w + 1 + h = length w.
Proof.
  induction w as [|x w IH]; intros h Hb; [discriminate|].
  destruct x; cbn [reflh badh ntrue length] in *.
  - apply IH in Hb. lia.
  - destruct h as [|h']; cbn [reflh badh ntrue length] in *.
    + rewrite ntrue_map_negb. lia.
    + apply IH in Hb. lia.
Qed.

(* completeness and no-duplication of the enumeration *)
Lemma all_lists_complete : forall w, In w (all_lists (length w)).
Proof.
  induction w as [|x w IH]; [left; reflexivity|].
  cbn [length all_lists]. rewrite in_app_iff.
  destruct x; [left | right]; apply in_map_iff; exists w; split; auto.
Qed.

Lemma nodup_map_cons : forall (x : bool) l, NoDup l -> NoDup (map (cons x) l).
Proof.
  intros x l H. induction H as [|a l Ha Hl IH]; cbn [map]; constructor.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as [y [Hy Hiny]].
    injection Hy as ->. contradiction.
  - exact IH.
Qed.

Lemma all_lists_nodup : forall m, NoDup (all_lists m).
Proof.
  induction m as [|m IH]; [repeat constructor; auto|].
  cbn [all_lists]. apply NoDup_app.
  - apply nodup_map_cons, IH.
  - apply nodup_map_cons, IH.
  - intros x Hx Hy. apply in_map_iff in Hx. destruct Hx as [a [<- _]].
    apply in_map_iff in Hy. destruct Hy as [b [Hb _]]. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* The reflection bijection counts the bad paths; hence #Dyck = cb.     *)
(* ------------------------------------------------------------------ *)

(* a non-bad path (from height 0) has at least half trues *)
Lemma badh_false_count : forall w h, badh h w = false -> length w <= h + 2 * ntrue w.
Proof.
  induction w as [|x w IH]; intros h Hb; [cbn; lia|].
  destruct x; cbn [badh ntrue length] in *.
  - apply IH in Hb. lia.
  - destruct h as [|h']; [discriminate|]. apply IH in Hb. lia.
Qed.

Lemma refl_inj : forall a b, refl a = refl b -> a = b.
Proof. intros a b H. rewrite <- (refl_invol a), <- (refl_invol b), H. reflexivity. Qed.

Lemma perm_refl : forall m, Permutation (all_lists m) (map refl (all_lists m)).
Proof.
  intro m. apply NoDup_Permutation_bis.
  - apply all_lists_nodup.
  - rewrite length_map. apply Nat.le_refl.
  - intros x Hx. apply in_map_iff. exists (refl x). split; [apply refl_invol|].
    pose proof (all_lists_complete (refl x)) as Hc.
    rewrite refl_length, (all_lists_length m x Hx) in Hc. exact Hc.
Qed.

Lemma perm_filter_length : forall {A} (P : A -> bool) l l',
  Permutation l l' -> length (filter P l) = length (filter P l').
Proof.
  intros A P l l' H. induction H.
  - reflexivity.
  - simpl; destruct (P x); simpl; rewrite IHPermutation; reflexivity.
  - simpl; destruct (P x); destruct (P y); reflexivity.
  - rewrite IHPermutation1, IHPermutation2; reflexivity.
Qed.

Lemma filt_refl : forall (P : list bool -> bool) m,
  length (filter P (all_lists m)) = length (filter (fun w => P (refl w)) (all_lists m)).
Proof.
  intros P m. rewrite (perm_filter_length P _ _ (perm_refl m)).
  rewrite length_filter_map. reflexivity.
Qed.

Lemma filter_partition : forall {A} (P b : A -> bool) l,
  length (filter (fun x => P x && b x) l) + length (filter (fun x => P x && negb (b x)) l)
  = length (filter P l).
Proof.
  intros A P b l. induction l as [|x l IH]; [reflexivity|].
  simpl. destruct (P x); destruct (b x); simpl; lia.
Qed.

Lemma filter_ext_eq : forall {A} (f g : A -> bool) l,
  (forall x, In x l -> f x = g x) -> filter f l = filter g l.
Proof.
  intros A f g l H. induction l as [|x l IH]; [reflexivity|].
  simpl. rewrite (H x (or_introl eq_refl)),
                 (IH (fun y Hy => H y (or_intror Hy))). reflexivity.
Qed.

(* the load-bearing pointwise equivalence on length-2(n'+1) lists *)
Lemma refl_pointwise : forall n' w, length w = 2 * S n' ->
  Nat.eqb (ntrue (refl w)) n' = (Nat.eqb (ntrue w) (S n') && bad w).
Proof.
  intros n' w Hlen. unfold bad in *. destruct (badh 0 w) eqn:Hb.
  - (* bad: ntrue(refl w) + ntrue w + 1 + 0 = length w *)
    pose proof (ntrue_reflh w 0 Hb) as Hr.
    rewrite Bool.andb_true_r.
    destruct (Nat.eqb_spec (ntrue w) (S n')) as [He|He].
    + apply Nat.eqb_eq. unfold refl. lia.
    + apply Nat.eqb_neq. unfold refl. lia.
  - (* non-bad: refl w = w, and ntrue w >= n'+1 *)
    rewrite refl_id by (unfold bad; exact Hb).
    rewrite Bool.andb_false_r.
    pose proof (badh_false_count w 0 Hb) as Hc.
    apply Nat.eqb_neq. lia.
Qed.

Definition dyck_count (n : nat) : nat :=
  length (filter (fun w => Nat.eqb (ntrue w) n && negb (bad w)) (all_lists (2 * n))).

Theorem dyck_count_cb : forall n, dyck_count n = cb n.
Proof.
  destruct n as [|n']; [vm_compute; reflexivity|].
  unfold dyck_count, cb.
  set (N := 2 * S n').
  (* partition the ntrue = S n' lists into bad and non-bad *)
  pose proof (filter_partition (fun w => Nat.eqb (ntrue w) (S n')) bad (all_lists N)) as Hpart.
  (* the whole ntrue = S n' count *)
  rewrite (count_ntrue N (S n')) in Hpart.
  (* bad count = binom N n' via the reflection *)
  assert (Hbad : length (filter (fun w => Nat.eqb (ntrue w) (S n') && bad w) (all_lists N))
                 = binom N n').
  { rewrite <- (count_ntrue N n').
    rewrite (filt_refl (fun w => Nat.eqb (ntrue w) n') N).
    f_equal. apply filter_ext_eq. intros w Hw.
    symmetry. apply refl_pointwise.
    exact (all_lists_length N w Hw). }
  rewrite Hbad in Hpart.
  (* so dyck_count (S n') = binom N (S n') - binom N n' = cb (S n') *)
  assert (Hsym : binom N (S (S n')) = binom N n').
  { rewrite (binom_sym N (S (S n'))) by (unfold N; lia).
    f_equal. unfold N; lia. }
  unfold N in *. rewrite Hsym. lia.
Qed.

Print Assumptions dyck_count_cb.

(* ================================================================== *)
(* The tree <-> Dyck-word bijection: catalan n = dyck_count n.          *)
(* ================================================================== *)

Lemma ntrue_app : forall p q, ntrue (p ++ q) = ntrue p + ntrue q.
Proof. induction p as [|x p IH]; [reflexivity|]. intro q. destruct x; cbn [app ntrue]; rewrite IH; lia. Qed.

(* final height of a path walked from height h (clamped at 0 on under-runs) *)
Fixpoint finalh (h : nat) (w : list bool) : nat :=
  match w with
  | [] => h
  | true :: w'  => finalh (S h) w'
  | false :: w' => match h with 0 => finalh 0 w' | S h' => finalh h' w' end
  end.

Lemma finalh_app : forall p h q, finalh h (p ++ q) = finalh (finalh h p) q.
Proof.
  induction p as [|x p IH]; intros h q; [reflexivity|].
  destruct x; cbn [app finalh].
  - apply IH.
  - destruct h; apply IH.
Qed.

Lemma badh_app : forall p h q, badh h p = false ->
  badh h (p ++ q) = badh (finalh h p) q.
Proof.
  induction p as [|x p IH]; intros h q Hp; [reflexivity|].
  destruct x; cbn [app badh finalh] in *.
  - apply IH, Hp.
  - destruct h as [|h']; [discriminate|]. apply IH, Hp.
Qed.

(* the encoder *)
Fixpoint word (t : tree) : list bool :=
  match t with
  | Leaf => []
  | Node l r => true :: word l ++ false :: word r
  end.

Lemma word_length : forall t, length (word t) = 2 * size t.
Proof.
  induction t as [|l IHl r IHr]; [reflexivity|].
  cbn [word size length]. rewrite length_app. cbn [length]. rewrite IHl, IHr. lia.
Qed.

Lemma word_ntrue : forall t, ntrue (word t) = size t.
Proof.
  induction t as [|l IHl r IHr]; [reflexivity|].
  cbn [word size ntrue]. rewrite ntrue_app. cbn [ntrue]. rewrite IHl, IHr. lia.
Qed.

Lemma finalh_word : forall t h, finalh h (word t) = h.
Proof.
  induction t as [|l IHl r IHr]; intros h; [reflexivity|].
  cbn [word finalh]. rewrite finalh_app, IHl. cbn [finalh]. rewrite IHr. reflexivity.
Qed.

Lemma word_nobad : forall t h, badh h (word t) = false.
Proof.
  induction t as [|l IHl r IHr]; intros h; [reflexivity|].
  cbn [word badh]. rewrite badh_app by apply IHl. rewrite finalh_word.
  cbn [badh]. apply IHr.
Qed.

Lemma word_dyckpred : forall t,
  Nat.eqb (ntrue (word t)) (size t) && negb (bad (word t)) = true.
Proof.
  intro t. rewrite word_ntrue, Nat.eqb_refl. unfold bad. rewrite word_nobad. reflexivity.
Qed.

(* split off the prefix that returns (relative) height to 0, dropping the
   separating false; this inverts the  word l ++ false :: word r  shape *)
Fixpoint findsplit (h : nat) (w : list bool) : list bool * list bool :=
  match w with
  | [] => ([], [])
  | true :: w'  => let (a, b) := findsplit (S h) w' in (true :: a, b)
  | false :: w' => match h with
                   | 0    => ([], w')
                   | S h' => let (a, b) := findsplit h' w' in (false :: a, b)
                   end
  end.

Fixpoint decode (fuel : nat) (w : list bool) : tree :=
  match fuel with
  | 0 => Leaf
  | S f => match w with
           | [] => Leaf
           | true :: rest => let (a, b) := findsplit 0 rest in
                             Node (decode f a) (decode f b)
           | false :: _ => Leaf
           end
  end.

(* word t, walked from any height h, never triggers the relative-0 separator,
   so it is consumed wholesale into the prefix *)
Lemma findsplit_word_app : forall t h rest,
  findsplit h (word t ++ rest) =
  (let (a, b) := findsplit h rest in (word t ++ a, b)).
Proof.
  induction t as [|l IHl r IHr]; intros h rest.
  - cbn [word app]. destruct (findsplit h rest); reflexivity.
  - cbn [word]. rewrite <- app_comm_cons, <- app_assoc.
    cbn [findsplit]. rewrite IHl.
    rewrite <- app_comm_cons. cbn [findsplit]. rewrite IHr.
    destruct (findsplit h rest) as [a b].
    cbn [word]. rewrite <- app_comm_cons, <- app_assoc. reflexivity.
Qed.

Lemma findsplit_sep : forall t rest, findsplit 0 (word t ++ false :: rest) = (word t, rest).
Proof.
  intros t rest. rewrite findsplit_word_app. cbn [findsplit].
  rewrite app_nil_r. reflexivity.
Qed.

Lemma decode_word : forall t fuel, length (word t) <= fuel -> decode fuel (word t) = t.
Proof.
  induction t as [|l IHl r IHr]; intros fuel Hf.
  - destruct fuel; reflexivity.
  - destruct fuel as [|f]; [rewrite word_length in Hf; cbn [size] in Hf; lia|].
    cbn [word decode]. rewrite findsplit_sep.
    rewrite word_length in Hf. cbn [size] in Hf.
    rewrite IHl by (rewrite word_length; lia).
    rewrite IHr by (rewrite word_length; lia). reflexivity.
Qed.

Print Assumptions decode_word.

(* ---- surjectivity: word (decode w) = w for Dyck words ---- *)

Lemma badh_mono : forall w h, badh h w = false -> badh (S h) w = false.
Proof.
  induction w as [|x w IH]; intros h Hb; [reflexivity|].
  destruct x; cbn [badh] in *.
  - apply IH, Hb.
  - destruct h; [discriminate | apply IH, Hb].
Qed.

Lemma finalh_nobad : forall w h, badh h w = false -> finalh h w + length w = h + 2 * ntrue w.
Proof.
  induction w as [|x w IH]; intros h Hb; [cbn; lia|].
  destruct x; cbn [badh finalh ntrue length] in *.
  - apply IH in Hb. lia.
  - destruct h as [|h']; [discriminate|]. apply IH in Hb. lia.
Qed.

Lemma nobad_le : forall w, badh 0 w = false -> length w <= 2 * ntrue w.
Proof. intros w H. pose proof (finalh_nobad w 0 H). lia. Qed.

Lemma findsplit_prefix : forall w h a b, findsplit h w = (a, b) ->
  badh h a = false /\ (badh h w = true -> w = a ++ false :: b /\ finalh h a = 0).
Proof.
  induction w as [|x w IH]; intros h a b Hfs.
  - cbn [findsplit] in Hfs. injection Hfs as <- <-. split; [reflexivity|]. discriminate.
  - destruct x; cbn [findsplit] in Hfs.
    + destruct (findsplit (S h) w) as [a' b'] eqn:E. injection Hfs as <- <-.
      destruct (IH (S h) a' b' E) as [Hba Himp].
      cbn [badh]. split; [exact Hba|]. intro Hbw.
      cbn [badh] in Hbw. destruct (Himp Hbw) as [Hw Hf].
      split; [cbn [app]; rewrite Hw; reflexivity | cbn [finalh]; exact Hf].
    + destruct h as [|h'].
      * injection Hfs as <- <-. split; [reflexivity|]. intros _. split; reflexivity.
      * destruct (findsplit h' w) as [a' b'] eqn:E. injection Hfs as <- <-.
        destruct (IH h' a' b' E) as [Hba Himp].
        cbn [badh]. split; [exact Hba|]. intro Hbw.
        cbn [badh] in Hbw. destruct (Himp Hbw) as [Hw Hf].
        split; [cbn [app]; rewrite Hw; reflexivity | cbn [finalh]; exact Hf].
Qed.

Lemma word_decode : forall fuel w,
  length w <= fuel -> bad w = false -> 2 * ntrue w = length w -> word (decode fuel w) = w.
Proof.
  induction fuel as [|f IH]; intros w Hlen Hbad Hbal.
  - assert (w = []) by (destruct w; [reflexivity | cbn in Hlen; lia]). subst. reflexivity.
  - destruct w as [|x rest]; [reflexivity|].
    destruct x.
    + (* true :: rest *)
      cbn [decode].
      (* badh 0 rest = true since rest has one more false than true *)
      assert (Hbr : badh 0 rest = true).
      { destruct (badh 0 rest) eqn:Hb; [reflexivity|].
        pose proof (nobad_le rest Hb). cbn [ntrue length] in Hbal. lia. }
      destruct (findsplit 0 rest) as [a b] eqn:Efs.
      destruct (findsplit_prefix rest 0 a b Efs) as [Hba Himp].
      destruct (Himp Hbr) as [Hrec Hfa].
      (* a balanced *)
      assert (Hbala : 2 * ntrue a = length a).
      { pose proof (finalh_nobad a 0 Hba). lia. }
      (* badh 1 rest = false (from bad (true::rest) = false) *)
      assert (Hb1 : badh 1 rest = false) by (unfold bad in Hbad; cbn [badh] in Hbad; exact Hbad).
      (* b balanced and non-bad *)
      assert (Hlenrec : length rest = length a + S (length b))
        by (rewrite Hrec, length_app; cbn [length]; lia).
      assert (Hntrec : ntrue rest = ntrue a + ntrue b)
        by (rewrite Hrec, ntrue_app; cbn [ntrue]; lia).
      assert (Hbalb : 2 * ntrue b = length b).
      { cbn [ntrue length] in Hbal. lia. }
      assert (Hbadb : bad b = false).
      { unfold bad. rewrite Hrec in Hb1.
        rewrite badh_app in Hb1 by (apply badh_mono; exact Hba).
        pose proof (finalh_nobad a 1 (badh_mono a 0 Hba)) as Hf1.
        replace (finalh 1 a) with 1 in Hb1 by lia.
        cbn [badh] in Hb1. exact Hb1. }
      cbn [length] in Hlen.
      assert (Hlena : length a <= f) by lia.
      assert (Hlenb : length b <= f) by lia.
      cbn [word]. rewrite (IH a Hlena Hba Hbala), (IH b Hlenb Hbadb Hbalb).
      rewrite Hrec. reflexivity.
    + (* false :: rest : impossible, bad *)
      unfold bad in Hbad. cbn [badh] in Hbad. discriminate.
Qed.

Lemma size_decode : forall fuel w,
  length w <= fuel -> bad w = false -> 2 * ntrue w = length w -> size (decode fuel w) = ntrue w.
Proof.
  intros fuel w Hlen Hbad Hbal.
  rewrite <- (word_ntrue (decode fuel w)), (word_decode fuel w Hlen Hbad Hbal). reflexivity.
Qed.

Print Assumptions word_decode.

(* ================================================================== *)
(* catalan n = dyck_count n, hence catalan_ratio.                       *)
(* ================================================================== *)

Lemma nodup_map_inj : forall {A B} (f : A -> B) l,
  (forall a b, f a = f b -> a = b) -> NoDup l -> NoDup (map f l).
Proof.
  intros A B f l Hinj H. induction H as [|x l Hx Hl IH]; cbn [map]; constructor.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as [y [Hy Hiny]].
    apply Hinj in Hy. subst y. contradiction.
  - exact IH.
Qed.

Lemma NoDup_list_prod : forall {A B} (l1 : list A) (l2 : list B),
  NoDup l1 -> NoDup l2 -> NoDup (list_prod l1 l2).
Proof.
  intros A B l1 l2 H1 H2. induction H1 as [|a l1 Ha Hl1 IH]; [constructor|].
  cbn [list_prod]. apply NoDup_app.
  - apply nodup_map_inj; [intros b c Hbc; injection Hbc; auto | exact H2].
  - exact IH.
  - intros x Hx Hy. apply in_map_iff in Hx. destruct Hx as [b [<- _]].
    apply in_prod_iff in Hy. destruct Hy as [Hin _]. contradiction.
Qed.

Lemma node_inj : forall lr1 lr2, node lr1 = node lr2 -> lr1 = lr2.
Proof.
  intros [l1 r1] [l2 r2]. unfold node. cbn [fst snd]. intro H.
  injection H as -> ->. reflexivity.
Qed.

Definition lsize (t : tree) : nat := match t with Leaf => 0 | Node l _ => size l end.

Lemma FOP_map_seq_key : forall {E} (key : E -> nat) (f : nat -> list E) start m,
  (forall i, In i (seq start m) -> forall t, In t (f i) -> key t = i) ->
  ForallOrdPairs (fun l1 l2 => forall t, In t l1 -> ~ In t l2) (map f (seq start m)).
Proof.
  intros A key f start m. revert start. induction m as [|m IH]; intros start Hk.
  - constructor.
  - cbn [seq map]. constructor.
    + apply Forall_forall. intros piece Hpiece. apply in_map_iff in Hpiece.
      destruct Hpiece as [j [<- Hj]]. rewrite in_seq in Hj.
      intros t Ht Htj.
      assert (key t = start) by (apply (Hk start); [rewrite in_seq; lia | exact Ht]).
      assert (key t = j) by (apply (Hk j); [rewrite in_seq; lia | exact Htj]).
      lia.
    + apply IH. intros i Hi. apply Hk. rewrite in_seq in Hi |- *. lia.
Qed.

Lemma allt_nodup : forall n, NoDup (allt n).
Proof.
  induction n as [n IH] using lt_wf_ind.
  destruct n as [|k].
  - unfold allt. rewrite trees_table_0. cbn [nth]. repeat constructor; auto.
  - rewrite allt_S_rows. apply NoDup_concat.
    + apply Forall_forall. intros piece Hpiece. apply in_map_iff in Hpiece.
      destruct Hpiece as [i [<- Hi]]. rewrite in_seq in Hi.
      apply nodup_map_inj; [exact node_inj|].
      apply NoDup_list_prod; apply IH; lia.
    + apply (FOP_map_seq_key lsize).
      intros i Hi t Ht. rewrite in_seq in Hi.
      apply in_map_iff in Ht. destruct Ht as [[l r] [Hnode Hpair]].
      apply in_prod_iff in Hpair. destruct Hpair as [Hl _].
      subst t. unfold node, lsize. cbn [fst snd].
      apply (allt_size i i l); [apply Nat.le_refl | exact Hl].
Qed.

(* word is injective (the encoder has a left inverse) *)
Lemma word_inj : forall t1 t2, word t1 = word t2 -> t1 = t2.
Proof.
  intros t1 t2 H.
  rewrite <- (decode_word t1 (length (word t1)) (Nat.le_refl _)).
  rewrite <- (decode_word t2 (length (word t2)) (Nat.le_refl _)).
  rewrite H. reflexivity.
Qed.

(* the size-n trees and the semilength-n Dyck paths are equinumerous *)
Theorem catalan_dyck : forall n, catalan n = dyck_count n.
Proof.
  intro n. unfold catalan, dyck_count.
  rewrite <- (length_map word (allt n)).
  apply Permutation_length, NoDup_Permutation.
  - apply nodup_map_inj; [exact word_inj | apply allt_nodup].
  - apply NoDup_filter, all_lists_nodup.
  - intro w. split.
    + (* word t, t in allt n  ->  w in dyck_list n *)
      intro Hin. apply in_map_iff in Hin. destruct Hin as [t [<- Ht]].
      pose proof (allt_size n n t (Nat.le_refl _) Ht) as Hsz.
      apply filter_In. split.
      * rewrite <- Hsz, <- (word_length t). apply all_lists_complete.
      * pose proof (word_dyckpred t) as Hd. rewrite Hsz in Hd. exact Hd.
    + (* w Dyck  ->  w = word (decode w), decode w in allt n *)
      intro Hin. apply filter_In in Hin. destruct Hin as [Hall Hd].
      apply andb_true_iff in Hd. destruct Hd as [Hnt Hnb].
      apply Nat.eqb_eq in Hnt. apply Bool.negb_true_iff in Hnb.
      pose proof (all_lists_length _ w Hall) as Hlen.
      assert (Hbal : 2 * ntrue w = length w) by lia.
      apply in_map_iff. exists (decode (length w) w). split.
      * apply word_decode; [apply Nat.le_refl | exact Hnb | exact Hbal].
      * pose proof (size_decode (length w) w (Nat.le_refl _) Hnb Hbal) as Hs.
        rewrite Hnt in Hs.
        rewrite <- Hs. apply allt_complete.
Qed.

Theorem catalan_ratio : forall n,
  (n + 2) * catalan (S n) = 2 * (2 * n + 1) * catalan n.
Proof.
  intro n. rewrite !catalan_dyck, !dyck_count_cb. apply cb_ratio.
Qed.

Print Assumptions catalan_ratio.
