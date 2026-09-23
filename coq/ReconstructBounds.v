(* ReconstructBounds.v
   Best-case (and exact-case) comparison bounds for the three algorithms, as
   corollaries of the mechanized counts.  For all n:

     C : total = 3n - 2            (constant -- best = average = worst)
     M : total >= 2n - 1           (best case, attained when there are no pops)
     N : total >= n + 2            (best case, attained when there are no pops
                                    and no double pops)

   These match the best-case column of the average-case analysis.  The matching
   worst-case upper bounds need the structural bound S <= n-1 on the pop count
   (a stack-size invariant), noted at the end as the next increment.
   Axiom-free.

   Build:  rocq c Trees.v Dictionary.v Reconstruct.v ReconstructCost.v
                  ReconstructM.v ReconstructN.v   (first)
           rocq c ReconstructBounds.v
   Rocq Prover 9.1.0.  Standard library only. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import Trees.
Require Import Dictionary.
Require Import Reconstruct.
Require Import ReconstructCost.
Require Import ReconstructM.
Require Import ReconstructN.
Require Import ReconstructLcount.

(* Algorithm C: the count is constant, so best = average = worst = 3n - 2.
   (This is total_comparisons_count; we restate it as the degenerate range.) *)
Corollary C_exact : forall t, t <> Leaf ->
  total_comparisons (ip t) = 3 * size t - 2.
Proof. exact total_comparisons_count. Qed.

(* Makinen's algorithm M: at least 2n - 1, with equality exactly when no pops. *)
Corollary M_best : forall t, t <> Leaf ->
  2 * size t - 1 <= total_comparisons_M (ip t).
Proof.
  intros t Hne. rewrite (total_comparisons_M_count t Hne). lia.
Qed.

Corollary M_best_attained : forall t, t <> Leaf ->
  pops_M (ip t) = 0 -> total_comparisons_M (ip t) = 2 * size t - 1.
Proof.
  intros t Hne H0. rewrite (total_comparisons_M_count t Hne), H0. lia.
Qed.

(* The improved algorithm N: at least n + 2 (the index-test count lcount_N is at
   least 1 -- the sentinel break -- and the pop count is non-negative). *)
Corollary N_best : forall t, t <> Leaf ->
  size t + 2 <= total_comparisons_N (ip t).
Proof.
  intros t Hne. rewrite (total_comparisons_N_count t Hne).
  unfold lcount_N. lia.
Qed.

Corollary N_best_attained : forall t, t <> Leaf ->
  pops_N (ip t) = 0 -> lcount_N (ip t) = 1 ->
  total_comparisons_N (ip t) = size t + 2.
Proof.
  intros t Hne Hp Hl. rewrite (total_comparisons_N_count t Hne), Hp, Hl. lia.
Qed.

(* ================================================================== *)
(* Worst-case upper bound for M:  A_M <= 3n - 2, for all n.            *)
(*                                                                      *)
(* The pop count obeys S <= n-1.  This is a stack-size invariant: the   *)
(* sentinel (= length ip = n, strictly above every label) is never      *)
(* popped, and every step pushes the current label, so the final stack  *)
(* keeps at least two elements (the sentinel and the last push).  With   *)
(* conservation (stack length + pops = pushes + 2) this caps S at n-1,   *)
(* hence A_M = 2n-1 + S <= 3n-2: M never beats the oblivious 3n-2 of C.  *)
(* Axiom-free.                                                          *)
(* ================================================================== *)

Definition stkM (st : stateM) : list nat := let '(_, s, _, _) := st in s.

(* Test first: S <= n-1 on every tree of size <= 9 (independent check). *)
Definition popbound_M (t : tree) : bool :=
  match t with
  | Leaf => true
  | _ => Nat.leb (pops_M (ip t)) (size t - 1)
  end.

Theorem popbound_M_upto_9 : forallb popbound_M (trees_upto 9) = true.
Proof. vm_compute. reflexivity. Qed.

(* And the bound is attained (a right spine of size 3 costs 3*3-2 = 7). *)
Example M_worst_right3 :
  total_comparisons_M (ip (Node Leaf (Node Leaf (Node Leaf Leaf)))) = 7.
Proof. vm_compute. reflexivity. Qed.

(* The inner multi-pop removes exactly k elements from the stack. *)
Lemma popM_length : forall fuel cur s prev r k,
  popM fuel cur s = (prev, r, k) -> length s = length r + k.
Proof.
  induction fuel as [|f IH]; intros cur s prev r k H.
  - cbn [popM] in H. inversion H; subst. lia.
  - destruct s as [|top s'].
    + cbn [popM] in H. inversion H; subst. reflexivity.
    + destruct s' as [|top2 rest2].
      * cbn [popM] in H. inversion H; subst. reflexivity.
      * cbn [popM] in H. destruct (Nat.leb top2 cur) eqn:E.
        -- destruct (popM f cur (top2 :: rest2)) as [[p r0] k0] eqn:Ef.
           inversion H; subst. apply IH in Ef. cbn [length] in Ef |- *. lia.
        -- inversion H; subst. cbn [length]. lia.
Qed.

(* One step conserves "stack length + pops" up by exactly one push. *)
Lemma stepM_conserve : forall cur a s c p,
  s <> [] ->
  length (stkM (stepM cur (a, s, c, p))) + popof (stepM cur (a, s, c, p))
    = length s + p + 1.
Proof.
  intros cur a s c p Hne. unfold stepM, stkM, popof.
  destruct s as [|top s']; [contradiction|].
  destruct (Nat.ltb cur top).
  - cbn [length]. lia.
  - destruct (popM (length (top :: s')) cur (top :: s')) as [[prev r] k] eqn:E.
    apply popM_length in E. cbn [length]. cbn [length] in E. lia.
Qed.

(* Conservation over the whole loop. *)
Lemma runM_aux_conserve : forall xs a s c p,
  s <> [] ->
  length (stkM (runM_aux xs (a, s, c, p))) + popof (runM_aux xs (a, s, c, p))
    = length s + p + length xs.
Proof.
  induction xs as [|cur rest IH]; intros a s c p Hne.
  - cbn [runM_aux length]. unfold stkM, popof. lia.
  - cbn [runM_aux length].
    destruct (stepM cur (a, s, c, p)) as [[[a1 s1] c1] p1] eqn:E.
    assert (Hs1 : s1 <> []).
    { unfold stepM in E. destruct s as [|top s']; [contradiction|].
      destruct (Nat.ltb cur top).
      - inversion E. intro Hc; discriminate.
      - destruct (popM (length (top :: s')) cur (top :: s')) as [[prev r] k].
        inversion E. intro Hc; discriminate. }
    pose proof (stepM_conserve cur a s c p Hne) as Hstep.
    rewrite E in Hstep. unfold stkM, popof in Hstep.
    specialize (IH a1 s1 c1 p1 Hs1). lia.
Qed.

(* The sentinel V (above every label) is never popped. *)
Lemma popM_keeps_V : forall fuel cur s V prev r k,
  cur < V ->
  (match s with [] => True | h :: _ => h <= cur end) ->
  popM fuel cur s = (prev, r, k) ->
  In V s -> In V r.
Proof.
  induction fuel as [|f IH]; intros cur s V prev r k Hcv Hhd H Hin.
  - cbn [popM] in H. inversion H; subst. exact Hin.
  - destruct s as [|top s'].
    + inversion Hin.
    + destruct s' as [|top2 rest2].
      * cbn [popM] in H. inversion H; subst.
        destruct Hin as [Heq | HF]; [exfalso; subst; lia | destruct HF].
      * cbn [popM] in H. destruct (Nat.leb top2 cur) eqn:E.
        -- destruct (popM f cur (top2 :: rest2)) as [[p r0] k0] eqn:Ef.
           inversion H; subst. apply Nat.leb_le in E.
           assert (HinV' : In V (top2 :: rest2)).
           { destruct Hin as [Heq | Hrest]; [exfalso; subst; lia | exact Hrest]. }
           exact (IH cur (top2 :: rest2) V prev r k0 Hcv E Ef HinV').
        -- inversion H; subst.
           destruct Hin as [Heq | Hrest]; [exfalso; subst; lia | exact Hrest].
Qed.

(* One step keeps the sentinel in the stack. *)
Lemma stepM_keepsV : forall cur a s c p V,
  cur < V -> In V s ->
  In V (stkM (stepM cur (a, s, c, p))).
Proof.
  intros cur a s c p V Hcv Hin. unfold stepM, stkM.
  destruct s as [|top s']; [inversion Hin|].
  destruct (Nat.ltb cur top) eqn:E.
  - cbn [List.In]. right. exact Hin.
  - destruct (popM (length (top :: s')) cur (top :: s')) as [[prev r] k] eqn:Ef.
    cbn [List.In]. right.
    apply Nat.ltb_ge in E.
    exact (popM_keeps_V (length (top :: s')) cur (top :: s') V prev r k Hcv E Ef Hin).
Qed.

(* Loop invariant: the sentinel stays, and the head stays below it. *)
Lemma runM_aux_inv : forall xs a s c p V,
  (forall x, In x xs -> x < V) ->
  In V s ->
  (forall h t, s = h :: t -> h < V) ->
  In V (stkM (runM_aux xs (a, s, c, p))) /\
  (forall h t, stkM (runM_aux xs (a, s, c, p)) = h :: t -> h < V).
Proof.
  induction xs as [|cur rest IH]; intros a s c p V Hall Hin Hhd.
  - cbn [runM_aux]. unfold stkM. split; [exact Hin | exact Hhd].
  - cbn [runM_aux].
    destruct (stepM cur (a, s, c, p)) as [[[a1 s1] c1] p1] eqn:E.
    assert (Hcv : cur < V) by (apply Hall; left; reflexivity).
    assert (Hin1 : In V s1).
    { pose proof (stepM_keepsV cur a s c p V Hcv Hin) as Hk.
      rewrite E in Hk. unfold stkM in Hk. exact Hk. }
    assert (Hcons : exists tl, s1 = cur :: tl).
    { unfold stepM in E. destruct s as [|top s']; [inversion Hin|].
      destruct (Nat.ltb cur top).
      - inversion E. eexists; reflexivity.
      - destruct (popM (length (top :: s')) cur (top :: s')) as [[prev r] k].
        inversion E. eexists; reflexivity. }
    assert (Hhd1 : forall h t, s1 = h :: t -> h < V).
    { intros h t Hs1. destruct Hcons as [tl Htl]. rewrite Htl in Hs1.
      inversion Hs1; subst. exact Hcv. }
    apply (IH a1 s1 c1 p1 V).
    + intros x Hx. apply Hall. right. exact Hx.
    + exact Hin1.
    + exact Hhd1.
Qed.

(* Hence S <= n-1, for all n. *)
Lemma pops_M_le : forall t, t <> Leaf -> pops_M (ip t) <= size t - 1.
Proof.
  intros t Hne. unfold pops_M, runM_full.
  destruct (ip t) as [|x0 rest] eqn:Eip.
  - exfalso. pose proof (ip_length t) as HL. rewrite Eip in HL.
    cbn [length] in HL. destruct t; [congruence | cbn [size] in HL; lia].
  - set (V := length (x0 :: rest)).
    assert (HLrest : S (length rest) = size t).
    { pose proof (ip_length t) as HL. rewrite Eip in HL. cbn [length] in HL. exact HL. }
    assert (Hlab : forall x, In x (x0 :: rest) -> x < V).
    { intros x Hx. unfold V. rewrite <- Eip in Hx |- *.
      pose proof (ipo_bounds t 0 x) as Hb. unfold ip in Hx, Hb.
      rewrite ip_length. apply Hb in Hx. lia. }
    assert (Hall : forall x, In x rest -> x < V) by
      (intros x Hx; apply Hlab; right; exact Hx).
    assert (HinV0 : In V [x0; V]) by (right; left; reflexivity).
    assert (Hhd0 : forall h tl, [x0; V] = h :: tl -> h < V).
    { intros h tl Hs. inversion Hs; subst. apply Hlab; left; reflexivity. }
    set (final := runM_aux rest (empty, [x0; V], 0, 0)) in *.
    assert (Hne2 : [x0; V] <> []) by (intro Hc; discriminate).
    pose proof (runM_aux_conserve rest empty [x0; V] 0 0 Hne2) as Hcons.
    fold final in Hcons.
    destruct (runM_aux_inv rest empty [x0; V] 0 0 V Hall HinV0 Hhd0)
      as [HinVfs Hhdfs].
    fold final in HinVfs, Hhdfs.
    assert (Hlen2 : 2 <= length (stkM final)).
    { destruct (stkM final) as [|f0 ft] eqn:Efs.
      - destruct HinVfs.
      - assert (Hf0 : f0 < V) by (apply (Hhdfs f0 ft); reflexivity).
        destruct ft as [|f1 ft'].
        + cbn [List.In] in HinVfs.
          destruct HinVfs as [Hc | HF]; [subst; lia | destruct HF].
        + cbn [length]. lia. }
    cbn [length] in Hcons.
    (* Hcons : length (stkM final) + popof final = 2 + 0 + length rest *)
    lia.
Qed.

(* Worst case: M makes at most 3n-2 comparisons, for all n. *)
Theorem M_worst : forall t, t <> Leaf ->
  total_comparisons_M (ip t) <= 3 * size t - 2.
Proof.
  intros t Hne. rewrite (total_comparisons_M_count t Hne).
  pose proof (pops_M_le t Hne) as Hp.
  assert (Hs : 1 <= size t) by (destruct t; [congruence | cbn [size]; lia]).
  lia.
Qed.

Corollary M_worst_attained : forall t, t <> Leaf ->
  pops_M (ip t) = size t - 1 -> total_comparisons_M (ip t) = 3 * size t - 2.
Proof.
  intros t Hne H. rewrite (total_comparisons_M_count t Hne), H.
  assert (1 <= size t) by (destruct t; [congruence | cbn [size]; lia]). lia.
Qed.

(* ================================================================== *)
(* Worst-case upper bound for N.                                       *)
(*                                                                      *)
(* A_N = S + P_2 + n + 2 (P_2 = full t).  Two INDEPENDENT structural    *)
(* bounds cap it -- the same sentinel stack invariant gives S <= n-1    *)
(* (pops_N_le), and a tree identity gives 2*full t + 1 <= n            *)
(* (full_bound, i.e. full <= floor((n-1)/2)).  No S--P_2 correlation is  *)
(* needed: by computation the two maxima are attained on the same tree, *)
(* so max (S + P_2) = (n-1) + floor((n-1)/2) = floor(3(n-1)/2).         *)
(*                                                                      *)
(* From lcount_N <= S + 1 (each double pop costs a pop) this yields the *)
(* clean A_N <= 3n for all n (N_worst).  The SHARP A_N <= 2n + ceil(n/2)*)
(* -- equivalently 2*A_N <= 5n+1 -- follows once lcount_N = full t + 1   *)
(* for all n (currently a bounded check, check_N_upto_9); we record it   *)
(* as the conditional N_worst_sharp_if, leaving that single identity as  *)
(* the remaining all-n obligation.  Axiom-free.                         *)
(* ================================================================== *)

(* (0) A pure tree identity: at most floor((n-1)/2) full nodes. *)
Lemma full_bound : forall t, t <> Leaf -> 2 * full t + 1 <= size t.
Proof.
  intros t Hne. rewrite (classify_size t), <- (P2_identity t Hne). lia.
Qed.

Definition stkN (st : stN) : list nat := let '(_, s, _, _, _) := st in s.

(* Test first: S <= n-1 on every tree of size <= 9. *)
Definition popbound_N (t : tree) : bool :=
  match t with
  | Leaf => true
  | _ => Nat.leb (pops_N (ip t)) (size t - 1)
  end.

Theorem popbound_N_upto_9 : forallb popbound_N (trees_upto 9) = true.
Proof. vm_compute. reflexivity. Qed.

(* And the sharp worst case 2*A_N <= 5n+1 holds on every tree of size <= 9. *)
Definition sharpbound_N (t : tree) : bool :=
  match t with
  | Leaf => true
  | _ => Nat.leb (2 * total_comparisons_N (ip t)) (5 * size t + 1)
  end.

Theorem sharpbound_N_upto_9 : forallb sharpbound_N (trees_upto 9) = true.
Proof. vm_compute. reflexivity. Qed.

(* (1) The inner multi-pop removes exactly k elements (popN = popM in shape). *)
Lemma popN_length : forall fuel cur s prev r k,
  popN fuel cur s = (prev, r, k) -> length s = length r + k.
Proof.
  induction fuel as [|f IH]; intros cur s prev r k H.
  - cbn [popN] in H. inversion H; subst. lia.
  - destruct s as [|top s'].
    + cbn [popN] in H. inversion H; subst. reflexivity.
    + destruct s' as [|top2 rest2].
      * cbn [popN] in H. inversion H; subst. reflexivity.
      * cbn [popN] in H. destruct (Nat.leb top2 cur) eqn:E.
        -- destruct (popN f cur (top2 :: rest2)) as [[p r0] k0] eqn:Ef.
           inversion H; subst. apply IH in Ef. cbn [length] in Ef |- *. lia.
        -- inversion H; subst. cbn [length]. lia.
Qed.

(* (2) Conservation: stack length + pops rises by one push per step. *)
Lemma stepN_conserve : forall cur a s ec lc pp,
  s <> [] ->
  length (stkN (stepN cur (a, s, ec, lc, pp))) + ppof (stepN cur (a, s, ec, lc, pp))
    = length s + pp + 1.
Proof.
  intros cur a s ec lc pp Hne. unfold stepN, stkN, ppof.
  destruct s as [|top s']; [contradiction|].
  destruct (Nat.ltb cur top).
  - cbn [length]. lia.
  - destruct s' as [|top2 s''].
    + cbn [length]. lia.
    + destruct (Nat.leb top2 cur).
      * destruct (popN (length (top2 :: s'')) cur (top2 :: s'')) as [[prev s2] k] eqn:Ep.
        apply popN_length in Ep. cbn [length]. cbn [length] in Ep. lia.
      * cbn [length]. lia.
Qed.

Lemma stepN_pushes : forall cur a s ec lc pp, s <> [] ->
  exists tl, stkN (stepN cur (a, s, ec, lc, pp)) = cur :: tl.
Proof.
  intros cur a s ec lc pp Hne. unfold stepN, stkN.
  destruct s as [|top s']; [contradiction|].
  destruct (Nat.ltb cur top).
  - eexists; reflexivity.
  - destruct s' as [|top2 s''].
    + eexists; reflexivity.
    + destruct (Nat.leb top2 cur).
      * destruct (popN (length (top2 :: s'')) cur (top2 :: s'')) as [[prev s2] k].
        eexists; reflexivity.
      * eexists; reflexivity.
Qed.

Lemma runN_aux_conserve : forall xs a s ec lc pp,
  s <> [] ->
  length (stkN (runN_aux xs (a, s, ec, lc, pp)))
    + ppof (runN_aux xs (a, s, ec, lc, pp))
    = length s + pp + length xs.
Proof.
  induction xs as [|cur rest IH]; intros a s ec lc pp Hne.
  - cbn [runN_aux length]. unfold stkN, ppof. lia.
  - cbn [runN_aux length].
    destruct (stepN cur (a, s, ec, lc, pp)) as [[[[a1 s1] ec1] lc1] pp1] eqn:E.
    destruct (stepN_pushes cur a s ec lc pp Hne) as [tl Htl].
    rewrite E in Htl. unfold stkN in Htl.
    assert (Hs1 : s1 <> []) by (rewrite Htl; discriminate).
    pose proof (stepN_conserve cur a s ec lc pp Hne) as Hstep.
    rewrite E in Hstep. unfold stkN, ppof in Hstep.
    specialize (IH a1 s1 ec1 lc1 pp1 Hs1). lia.
Qed.

(* (3) The sentinel V (above every label) is never popped. *)
Lemma popN_keeps_V : forall fuel cur s V prev r k,
  cur < V ->
  (match s with [] => True | h :: _ => h <= cur end) ->
  popN fuel cur s = (prev, r, k) ->
  In V s -> In V r.
Proof.
  induction fuel as [|f IH]; intros cur s V prev r k Hcv Hhd H Hin.
  - cbn [popN] in H. inversion H; subst. exact Hin.
  - destruct s as [|top s'].
    + inversion Hin.
    + destruct s' as [|top2 rest2].
      * cbn [popN] in H. inversion H; subst.
        destruct Hin as [Heq | HF]; [exfalso; subst; lia | destruct HF].
      * cbn [popN] in H. destruct (Nat.leb top2 cur) eqn:E.
        -- destruct (popN f cur (top2 :: rest2)) as [[p r0] k0] eqn:Ef.
           inversion H; subst. apply Nat.leb_le in E.
           assert (HinV' : In V (top2 :: rest2)).
           { destruct Hin as [Heq | Hrest]; [exfalso; subst; lia | exact Hrest]. }
           exact (IH cur (top2 :: rest2) V prev r k0 Hcv E Ef HinV').
        -- inversion H; subst.
           destruct Hin as [Heq | Hrest]; [exfalso; subst; lia | exact Hrest].
Qed.

Lemma stepN_keepsV : forall cur a s ec lc pp V,
  cur < V -> In V s ->
  In V (stkN (stepN cur (a, s, ec, lc, pp))).
Proof.
  intros cur a s ec lc pp V Hcv Hin. unfold stepN, stkN.
  destruct s as [|top s']; [inversion Hin|].
  destruct (Nat.ltb cur top) eqn:E.
  - cbn [List.In]. right. exact Hin.
  - apply Nat.ltb_ge in E.
    assert (Htop : In V s').
    { cbn [List.In] in Hin.
      destruct Hin as [Heq | Hrest]; [exfalso; subst; lia | exact Hrest]. }
    destruct s' as [|top2 s''].
    + inversion Htop.
    + destruct (Nat.leb top2 cur) eqn:E2.
      * destruct (popN (length (top2 :: s'')) cur (top2 :: s'')) as [[prev s2] k] eqn:Ep.
        cbn [List.In]. right. apply Nat.leb_le in E2.
        exact (popN_keeps_V (length (top2 :: s'')) cur (top2 :: s'') V prev s2 k
                 Hcv E2 Ep Htop).
      * cbn [List.In]. right. exact Htop.
Qed.

Lemma runN_aux_inv : forall xs a s ec lc pp V,
  (forall x, In x xs -> x < V) ->
  In V s ->
  (forall h t, s = h :: t -> h < V) ->
  In V (stkN (runN_aux xs (a, s, ec, lc, pp))) /\
  (forall h t, stkN (runN_aux xs (a, s, ec, lc, pp)) = h :: t -> h < V).
Proof.
  induction xs as [|cur rest IH]; intros a s ec lc pp V Hall Hin Hhd.
  - cbn [runN_aux]. unfold stkN. split; [exact Hin | exact Hhd].
  - cbn [runN_aux].
    destruct (stepN cur (a, s, ec, lc, pp)) as [[[[a1 s1] ec1] lc1] pp1] eqn:E.
    assert (Hcv : cur < V) by (apply Hall; left; reflexivity).
    assert (Hin1 : In V s1).
    { pose proof (stepN_keepsV cur a s ec lc pp V Hcv Hin) as Hk.
      rewrite E in Hk. unfold stkN in Hk. exact Hk. }
    assert (Hsne : s <> []) by (destruct s; [inversion Hin | discriminate]).
    destruct (stepN_pushes cur a s ec lc pp Hsne) as [tl Htl].
    rewrite E in Htl. unfold stkN in Htl.
    assert (Hhd1 : forall h t, s1 = h :: t -> h < V).
    { intros h t Hs1. rewrite Htl in Hs1. inversion Hs1; subst. exact Hcv. }
    apply (IH a1 s1 ec1 lc1 pp1 V).
    + intros x Hx. apply Hall. right. exact Hx.
    + exact Hin1.
    + exact Hhd1.
Qed.

(* (4) Hence S <= n-1, for all n. *)
Lemma pops_N_le : forall t, t <> Leaf -> pops_N (ip t) <= size t - 1.
Proof.
  intros t Hne. unfold pops_N, runN0.
  destruct (ip t) as [|x0 rest] eqn:Eip.
  - exfalso. pose proof (ip_length t) as HL. rewrite Eip in HL.
    cbn [length] in HL. destruct t; [congruence | cbn [size] in HL; lia].
  - set (V := length (x0 :: rest)).
    assert (HLrest : S (length rest) = size t).
    { pose proof (ip_length t) as HL. rewrite Eip in HL. cbn [length] in HL. exact HL. }
    assert (Hlab : forall x, In x (x0 :: rest) -> x < V).
    { intros x Hx. unfold V. rewrite <- Eip in Hx |- *.
      pose proof (ipo_bounds t 0 x) as Hb. unfold ip in Hx, Hb.
      rewrite ip_length. apply Hb in Hx. lia. }
    assert (Hall : forall x, In x rest -> x < V) by
      (intros x Hx; apply Hlab; right; exact Hx).
    assert (HinV0 : In V [x0; V]) by (right; left; reflexivity).
    assert (Hhd0 : forall h tl, [x0; V] = h :: tl -> h < V).
    { intros h tl Hs. inversion Hs; subst. apply Hlab; left; reflexivity. }
    set (final := runN_aux rest (empty, [x0; V], 0, 0, 0)) in *.
    assert (Hne2 : [x0; V] <> []) by (intro Hc; discriminate).
    pose proof (runN_aux_conserve rest empty [x0; V] 0 0 0 Hne2) as Hcons.
    fold final in Hcons.
    destruct (runN_aux_inv rest empty [x0; V] 0 0 0 V Hall HinV0 Hhd0)
      as [HinVfs Hhdfs].
    fold final in HinVfs, Hhdfs.
    assert (Hlen2 : 2 <= length (stkN final)).
    { destruct (stkN final) as [|f0 ft] eqn:Efs.
      - destruct HinVfs.
      - assert (Hf0 : f0 < V) by (apply (Hhdfs f0 ft); reflexivity).
        destruct ft as [|f1 ft'].
        + cbn [List.In] in HinVfs.
          destruct HinVfs as [Hc | HF]; [subst; lia | destruct HF].
        + cbn [length]. lia. }
    cbn [length] in Hcons.
    lia.
Qed.

(* (5) Each double pop costs a pop, so lcount_N <= S + 1, for all n. *)
Lemma stepN_lc_le : forall cur st,
  lcof (stepN cur st) + ppof st <= ppof (stepN cur st) + lcof st.
Proof.
  intros cur [[[[a s] ec] lc] pp]. unfold stepN, lcof, ppof.
  destruct s as [|top s']; [lia|].
  destruct (Nat.ltb cur top); [lia|].
  destruct s' as [|top2 s'']; [lia|].
  destruct (Nat.leb top2 cur).
  - destruct (popN (length (top2 :: s'')) cur (top2 :: s'')) as [[prev s2] k].
    cbn [lcof ppof]. lia.
  - lia.
Qed.

Lemma runN_aux_lc_pp : forall xs st,
  lcof (runN_aux xs st) + ppof st <= ppof (runN_aux xs st) + lcof st.
Proof.
  induction xs as [|cur rest IH]; intros st.
  - simpl. lia.
  - cbn [runN_aux].
    pose proof (stepN_lc_le cur st) as Hs.
    specialize (IH (stepN cur st)). lia.
Qed.

Lemma lcount_le_pops : forall t, lcount_N (ip t) <= pops_N (ip t) + 1.
Proof.
  intros t. unfold lcount_N, pops_N, runN0.
  destruct (ip t) as [|x0 rest] eqn:E.
  - simpl. lia.
  - pose proof (runN_aux_lc_pp rest (empty, [x0; length (x0 :: rest)], 0, 0, 0)) as H.
    cbn [lcof ppof] in H. lia.
Qed.

(* Clean worst case: N makes at most 3n comparisons, for all n. *)
Theorem N_worst : forall t, t <> Leaf ->
  total_comparisons_N (ip t) <= 3 * size t.
Proof.
  intros t Hne. rewrite (total_comparisons_N_count t Hne).
  pose proof (pops_N_le t Hne) as Hp.
  pose proof (lcount_le_pops t) as Hl.
  assert (Hs : 1 <= size t) by (destruct t; [congruence | cbn [size]; lia]).
  lia.
Qed.

(* Sharp worst case, modulo the all-n identity lcount_N = full t + 1: then
   2*A_N <= 5n+1, i.e. A_N <= 2n + ceil(n/2), the published figure.  Combines
   pops_N_le (S <= n-1) with full_bound (2*full + 1 <= n). *)
Theorem N_worst_sharp_if : forall t, t <> Leaf ->
  lcount_N (ip t) = full t + 1 ->
  2 * total_comparisons_N (ip t) <= 5 * size t + 1.
Proof.
  intros t Hne Hlc. rewrite (total_comparisons_N_count t Hne), Hlc.
  pose proof (pops_N_le t Hne) as Hp.
  pose proof (full_bound t Hne) as Hf.
  assert (1 <= size t) by (destruct t; [congruence | cbn [size]; lia]).
  lia.
Qed.

(* The all-n identity lcount_N = full t + 1 is now proved (ReconstructLcount),
   so the sharp worst case is UNCONDITIONAL. *)
Theorem N_worst_sharp : forall t, t <> Leaf ->
  2 * total_comparisons_N (ip t) <= 5 * size t + 1.
Proof.
  intros t Hne. apply N_worst_sharp_if; [exact Hne | apply lcount_N_full; exact Hne].
Qed.

(* ================================================================== *)
(* M's worst case is ATTAINED for all n: the right spine, whose i-p     *)
(* sequence is the ascending 0,1,...,n-1, makes exactly 3n-2 compares   *)
(* (every loop step pops exactly once, so S = n-1).  Hence M's range    *)
(* [2n-1, 3n-2] is realized at the top end for every n, not just <=9.   *)
(* ================================================================== *)

Fixpoint rspine (k : nat) : tree :=
  match k with 0 => Node Leaf Leaf | S k' => Node Leaf (rspine k') end.

Lemma size_rspine : forall k, size (rspine k) = S k.
Proof.
  induction k as [|k' IH]; [reflexivity|].
  cbn [rspine size]. rewrite IH. lia.
Qed.

Lemma ip_rspine : forall k, ip (rspine k) = seq 0 (S k).
Proof.
  induction k as [|k' IH]; [reflexivity|].
  unfold ip in *. cbn [rspine ipo size app].
  replace (0 + 0) with 0 by lia.
  replace (0 + 0 + 1) with (0 + 1) by lia.
  rewrite ipo_shift, IH.
  replace (map (fun x : nat => x + 1) (seq 0 (S k')))
    with (map S (seq 0 (S k'))) by (apply map_ext; intros; lia).
  rewrite seq_shift. reflexivity.
Qed.

(* On a strictly ascending block seq (S top) len sitting on a stack
   [top; sentinel] (top below it, sentinel above all), every step pops
   exactly once, so the run performs len pops. *)
Lemma runM_seq : forall len top sentinel a c p,
  top + len < sentinel ->
  popof (runM_aux (seq (S top) len) (a, [top; sentinel], c, p)) = p + len.
Proof.
  induction len as [|m IH]; intros top sentinel a c p Hlt.
  - cbn [seq runM_aux]. unfold popof. lia.
  - cbn [seq runM_aux]. unfold stepM.
    replace (Nat.ltb (S top) top) with false by (symmetry; apply Nat.ltb_ge; lia).
    cbn [length popM].
    replace (Nat.leb sentinel (S top)) with false by (symmetry; apply Nat.leb_gt; lia).
    rewrite IH by lia. lia.
Qed.

Theorem M_worst_attained_all : forall k,
  total_comparisons_M (ip (rspine k)) = 3 * size (rspine k) - 2.
Proof.
  intro k.
  assert (Hne : rspine k <> Leaf) by (destruct k; discriminate).
  rewrite (total_comparisons_M_count (rspine k) Hne).
  assert (Hp : pops_M (ip (rspine k)) = k).
  { unfold pops_M, runM_full. rewrite ip_rspine. cbn [seq].
    replace (length (0 :: seq 1 k)) with (S k)
      by (cbn [length]; rewrite length_seq; reflexivity).
    exact (runM_seq k 0 (S k) empty 0 0 ltac:(lia)). }
  rewrite Hp, size_rspine. lia.
Qed.

(* ================================================================== *)
(* The best cases are likewise attained for all n: the left spine,      *)
(* whose i-p sequence descends k,k-1,...,0, never pops (every step is a  *)
(* push) and has no full node, so M costs 2n-1 and N costs n+2.          *)
(* ================================================================== *)

Fixpoint lspine (k : nat) : tree :=
  match k with 0 => Node Leaf Leaf | S k' => Node (lspine k') Leaf end.

Fixpoint descseq (k : nat) : list nat :=
  match k with 0 => [] | S k' => k' :: descseq k' end.

Lemma size_lspine : forall k, size (lspine k) = S k.
Proof.
  induction k as [|k' IH]; [reflexivity|]. cbn [lspine size]. rewrite IH. lia.
Qed.

Lemma full_lspine : forall k, full (lspine k) = 0.
Proof.
  induction k as [|k' IH]; [reflexivity|].
  destruct k' as [|k'']; [reflexivity|]. cbn [lspine full] in *. exact IH.
Qed.

Lemma ip_lspine : forall k, ip (lspine k) = k :: descseq k.
Proof.
  induction k as [|k' IH]; [reflexivity|].
  unfold ip in *. cbn [lspine ipo size].
  rewrite app_nil_r, size_lspine.
  replace (0 + S k') with (S k') by lia.
  rewrite IH. reflexivity.
Qed.

(* A descending block descseq k (all < top) only pushes: no construction pop. *)
Lemma runM_nopop_desc : forall k top rest a c p,
  k <= top ->
  popof (runM_aux (descseq k) (a, top :: rest, c, p)) = p.
Proof.
  induction k as [|k' IH]; intros top rest a c p Hle.
  - cbn [descseq runM_aux]. unfold popof. reflexivity.
  - cbn [descseq runM_aux]. unfold stepM.
    replace (Nat.ltb k' top) with true by (symmetry; apply Nat.ltb_lt; lia).
    apply (IH k' (top :: rest)). lia.
Qed.

Lemma runN_nopop_desc : forall k top rest a ec lc pp,
  k <= top ->
  ppof (runN_aux (descseq k) (a, top :: rest, ec, lc, pp)) = pp.
Proof.
  induction k as [|k' IH]; intros top rest a ec lc pp Hle.
  - cbn [descseq runN_aux]. unfold ppof. reflexivity.
  - cbn [descseq runN_aux]. unfold stepN.
    replace (Nat.ltb k' top) with true by (symmetry; apply Nat.ltb_lt; lia).
    apply (IH k' (top :: rest)). lia.
Qed.

Theorem M_best_attained_all : forall k,
  total_comparisons_M (ip (lspine k)) = 2 * size (lspine k) - 1.
Proof.
  intro k. assert (Hne : lspine k <> Leaf) by (destruct k; discriminate).
  apply total_comparisons_M_best; [exact Hne|].
  unfold pops_M, runM_full. rewrite ip_lspine.
  replace (length (k :: descseq k)) with (S k)
    by (rewrite <- ip_lspine; rewrite ip_length, size_lspine; reflexivity).
  exact (runM_nopop_desc k k [S k] empty 0 0 ltac:(lia)).
Qed.

Theorem N_best_attained_all : forall k,
  total_comparisons_N (ip (lspine k)) = size (lspine k) + 2.
Proof.
  intro k. assert (Hne : lspine k <> Leaf) by (destruct k; discriminate).
  rewrite (total_comparisons_N_count (lspine k) Hne).
  rewrite (lcount_N_full (lspine k) Hne), full_lspine.
  assert (Hp : pops_N (ip (lspine k)) = 0).
  { unfold pops_N, runN0. rewrite ip_lspine.
    replace (length (k :: descseq k)) with (S k)
      by (rewrite <- ip_lspine; rewrite ip_length, size_lspine; reflexivity).
    exact (runN_nopop_desc k k [S k] empty 0 0 0 ltac:(lia)). }
  rewrite Hp. lia.
Qed.

(* ================================================================== *)
(* N's sharp worst case is ATTAINED at odd n by the "zig-zag" family     *)
(* zigA: a right spine of cherries, whose i-p sequence is 1,0,3,2,...     *)
(* For zigA k (size 2k+1): full = k (full_zigA) and pops_N = 2k           *)
(* (pops_N_zigA, via the stack invariant zigA_stk and conservation),      *)
(* whence 2 * A_N = 5n+1 for all k (N_worst_attained_all) -- the published*)
(* worst case attained, axiom-free.  So N's worst case is now two-sided   *)
(* sharp (bound + attainment) for all odd n, like C and M.                *)
(* ================================================================== *)

Fixpoint zigA (k : nat) : tree :=
  match k with 0 => Node Leaf Leaf | S k' => Node (Node Leaf Leaf) (zigA k') end.

Lemma zigA_Node : forall k, exists a b, zigA k = Node a b.
Proof. destruct k as [|k']; [exists Leaf, Leaf | eexists; eexists]; reflexivity. Qed.

Lemma size_zigA : forall k, size (zigA k) = S (2 * k).
Proof.
  induction k as [|k' IH]; [reflexivity|]. cbn [zigA size]. rewrite IH. lia.
Qed.

Lemma full_Node_nonleaf : forall l r,
  l <> Leaf -> r <> Leaf -> full (Node l r) = 1 + full l + full r.
Proof. intros [|ll lr] [|rl rr] Hl Hr; try congruence. reflexivity. Qed.

Lemma full_zigA : forall k, full (zigA k) = k.
Proof.
  induction k as [|k' IH]; [reflexivity|].
  cbn [zigA].
  rewrite (full_Node_nonleaf (Node Leaf Leaf) (zigA k') ltac:(discriminate)
            ltac:(destruct (zigA_Node k') as [a [b H]]; rewrite H; discriminate)).
  cbn [full]. rewrite IH. lia.
Qed.

(* Bounded evidence: zigA k attains 2*A_N = 5n+1 (= 2n+ceil(n/2)) for k<=4. *)
Theorem zigA_attains_upto_4 :
  forallb (fun k => Nat.eqb (2 * total_comparisons_N (ip (zigA k)))
                            (5 * size (zigA k) + 1)) (seq 0 5) = true.
Proof. vm_compute. reflexivity. Qed.

(* The attainment, reduced to the single remaining run identity pops_N = 2k.
   (full_zigA is discharged; with lcount_N = full+1 this is purely arithmetic.) *)
Theorem N_worst_attained_if : forall k,
  pops_N (ip (zigA k)) = 2 * k ->
  2 * total_comparisons_N (ip (zigA k)) = 5 * size (zigA k) + 1.
Proof.
  intros k Hpop.
  assert (Hne : zigA k <> Leaf) by (destruct (zigA_Node k) as [a [b H]]; rewrite H; discriminate).
  rewrite (total_comparisons_N_count (zigA k) Hne).
  rewrite (lcount_N_full (zigA k) Hne), full_zigA, Hpop, size_zigA. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The remaining run identity pops_N (ip (zigA k)) = 2k, closed.        *)
(* ------------------------------------------------------------------ *)

(* i-p of a cherry and of a zigA successor (unfolding the preorder). *)
Lemma ipo_cherry : forall off, ipo off (Node Leaf Leaf) = [off].
Proof. intro off. cbn [ipo size app]. rewrite !Nat.add_0_r. reflexivity. Qed.

Lemma ipo_zigA_S : forall off k',
  ipo off (zigA (S k')) = (off + 1) :: off :: ipo (off + 2) (zigA k').
Proof.
  intros off k'. cbn [zigA ipo size app]. rewrite !Nat.add_0_r.
  replace (off + 1 + 1) with (off + 2) by lia. reflexivity.
Qed.

(* The stack/pp of the N-run do not depend on the array, ec, lc. *)
Lemma stepN_stk_pp : forall cur a a' s ec ec' lc lc' pp,
  stkNl (stepN cur (a, s, ec, lc, pp)) = stkNl (stepN cur (a', s, ec', lc', pp))
  /\ ppof (stepN cur (a, s, ec, lc, pp)) = ppof (stepN cur (a', s, ec', lc', pp)).
Proof.
  intros cur a a' s ec ec' lc lc' pp. unfold stepN, stkNl, ppof.
  destruct s as [|top s']; [split; reflexivity|].
  destruct (Nat.ltb cur top); [split; reflexivity|].
  destruct s' as [|top2 s'']; [split; reflexivity|].
  destruct (Nat.leb top2 cur).
  - destruct (popN (length (top2 :: s'')) cur (top2 :: s'')) as [[prev r] k].
    split; reflexivity.
  - split; reflexivity.
Qed.

Lemma stepN_stk_indep : forall cur a a' s ec ec' lc lc' pp pp',
  stkNl (stepN cur (a, s, ec, lc, pp)) = stkNl (stepN cur (a', s, ec', lc', pp')).
Proof.
  intros cur a a' s ec ec' lc lc' pp pp'. unfold stepN, stkNl.
  destruct s as [|top s']; [reflexivity|].
  destruct (Nat.ltb cur top); [reflexivity|].
  destruct s' as [|top2 s'']; [reflexivity|].
  destruct (Nat.leb top2 cur).
  - destruct (popN (length (top2 :: s'')) cur (top2 :: s'')) as [[prev r] k].
    reflexivity.
  - reflexivity.
Qed.

Lemma stkN_aec_indep : forall xs a a' s ec ec' lc lc' pp pp',
  stkNl (runN_aux xs (a, s, ec, lc, pp)) = stkNl (runN_aux xs (a', s, ec', lc', pp')).
Proof.
  induction xs as [|cur rest IH]; intros a a' s ec ec' lc lc' pp pp'.
  - reflexivity.
  - cbn [runN_aux].
    destruct (stepN cur (a, s, ec, lc, pp)) as [[[[a1 s1] ec1] lc1] pp1] eqn:E1.
    destruct (stepN cur (a', s, ec', lc', pp')) as [[[[a2 s2] ec2] lc2] pp2] eqn:E2.
    assert (Hs : s1 = s2).
    { pose proof (stepN_stk_indep cur a a' s ec ec' lc lc' pp pp') as H.
      rewrite E1, E2 in H. cbn [stkNl] in H. exact H. }
    subst s2. apply IH.
Qed.

Lemma ppof_aec_indep : forall xs a a' s ec ec' lc lc' pp,
  ppof (runN_aux xs (a, s, ec, lc, pp)) = ppof (runN_aux xs (a', s, ec', lc', pp)).
Proof.
  induction xs as [|cur rest IH]; intros a a' s ec ec' lc lc' pp.
  - reflexivity.
  - cbn [runN_aux].
    destruct (stepN cur (a, s, ec, lc, pp)) as [[[[a1 s1] ec1] lc1] pp1] eqn:E1.
    destruct (stepN cur (a', s, ec', lc', pp)) as [[[[a2 s2] ec2] lc2] pp2] eqn:E2.
    pose proof (stepN_stk_pp cur a a' s ec ec' lc lc' pp) as [Hs Hp].
    rewrite E1, E2 in Hs, Hp. cbn [stkNl ppof] in Hs, Hp. subst s2 pp2.
    apply IH.
Qed.

(* runN0 (ip t) agrees with running ipo 0 t from the bare sentinel stack. *)
Lemma runN0_stk_pp : forall t, t <> Leaf ->
  stkNl (runN0 (ip t)) = stkNl (runN_aux (ipo 0 t) (empty, [size t], 0, 0, 0))
  /\ ppof (runN0 (ip t)) = ppof (runN_aux (ipo 0 t) (empty, [size t], 0, 0, 0)).
Proof.
  intros t Hne. destruct t as [|l r]; [congruence|].
  unfold ip. cbn [ipo]. unfold runN0. cbn [runN_aux].
  set (rest := ipo 0 l ++ ipo (0 + size l + 1) r).
  replace (length (0 + size l :: rest)) with (size (Node l r)).
  2:{ cbn [length size]. unfold rest. rewrite length_app, ipo_length, ipo_length. lia. }
  set (n := size (Node l r)).
  assert (Hlt : Nat.ltb (0 + size l) n = true)
    by (apply Nat.ltb_lt; unfold n; cbn [size]; lia).
  unfold stepN. rewrite Hlt. cbn [stkNl ppof].
  split; [apply stkN_aec_indep | apply ppof_aec_indep].
Qed.

(* The zigA stack invariant: processing ipo off (zigA k) from low ++ high
   leaves exactly (off + 2k) :: high.  Hence the final stack has height 2. *)
Lemma zigA_stk : forall k off low high a ec lc pp,
  (forall x, In x low -> x < off) ->
  (forall y, In y high -> off + size (zigA k) <= y) ->
  high <> [] ->
  stkNl (runN_aux (ipo off (zigA k)) (a, low ++ high, ec, lc, pp))
    = (off + 2 * k) :: high.
Proof.
  induction k as [|k' IH]; intros off low high a ec lc pp Hlo Hhi Hhne.
  - rewrite ipo_cherry. cbn [runN_aux].
    destruct (stepN_root off low high a ec lc pp Hhne Hlo
                ltac:(intros y Hy; pose proof (Hhi y Hy) as Hb; cbn [zigA size] in Hb; lia))
      as [Hs _].
    rewrite Hs. f_equal. lia.
  - rewrite ipo_zigA_S. cbn [runN_aux].
    (* step 1: process off+1 (pops low, pushes off+1) *)
    destruct (stepN (off + 1) (a, low ++ high, ec, lc, pp))
      as [[[[a1 s1] ec1] lc1] pp1] eqn:E1.
    assert (Hs1 : s1 = (off + 1) :: high).
    { destruct (stepN_root (off + 1) low high a ec lc pp Hhne
                  ltac:(intros x Hx; pose proof (Hlo x Hx); lia)
                  ltac:(intros y Hy; pose proof (Hhi y Hy) as Hb; cbn [zigA size] in Hb; lia))
        as [Hs _].
      rewrite E1 in Hs. cbn [stkNl] in Hs. exact Hs. }
    subst s1. cbn [runN_aux].
    (* step 2: process off (push onto (off+1)::high) *)
    destruct (stepN off (a1, (off + 1) :: high, ec1, lc1, pp1))
      as [[[[a2 s2] ec2] lc2] pp2] eqn:E2.
    assert (Hs2 : s2 = off :: (off + 1) :: high).
    { destruct (stepN_root off [] ((off + 1) :: high) a1 ec1 lc1 pp1
                  ltac:(discriminate) ltac:(intros x [])
                  ltac:(intros y [Hy|Hy];
                        [lia | pose proof (Hhi y Hy) as Hb; cbn [zigA size] in Hb; lia]))
        as [Hs _].
      cbn [app] in Hs. rewrite E2 in Hs. cbn [stkNl] in Hs. exact Hs. }
    subst s2.
    change (off :: (off + 1) :: high) with ([off; off + 1] ++ high).
    rewrite (IH (off + 2) [off; off + 1] high a2 ec2 lc2 pp2
               ltac:(intros x [<-|[<-|[]]]; lia)
               ltac:(intros y Hy; pose proof (Hhi y Hy) as Hb; cbn [zigA size] in Hb; lia)
               Hhne).
    f_equal. lia.
Qed.

Theorem pops_N_zigA : forall k, pops_N (ip (zigA k)) = 2 * k.
Proof.
  intro k. assert (Hne : zigA k <> Leaf)
    by (destruct (zigA_Node k) as [a [b H]]; rewrite H; discriminate).
  unfold pops_N. rewrite (proj2 (runN0_stk_pp (zigA k) Hne)).
  (* conservation: length(final stack) + ppof = length [size] + length (ipo 0 (zigA k)) *)
  pose proof (runN_aux_conserve (ipo 0 (zigA k)) empty [size (zigA k)] 0 0 0
                ltac:(discriminate)) as Hcons.
  (* final stack = (0 + 2k) :: [size] via zigA_stk (low=[], high=[size]) *)
  assert (Hstk : stkN (runN_aux (ipo 0 (zigA k)) (empty, [size (zigA k)], 0, 0, 0))
                 = (0 + 2 * k) :: [size (zigA k)]).
  { change (stkN (runN_aux (ipo 0 (zigA k)) (empty, [size (zigA k)], 0, 0, 0)))
      with (stkNl (runN_aux (ipo 0 (zigA k)) (empty, [] ++ [size (zigA k)], 0, 0, 0))).
    apply zigA_stk; [intros x [] | intros y [Hy|[]]; lia | discriminate]. }
  rewrite Hstk in Hcons.
  assert (HL : length (ipo 0 (zigA k)) = S (2 * k))
    by (rewrite ipo_length; apply size_zigA).
  rewrite HL in Hcons. cbn [length] in Hcons. lia.
Qed.

(* Hence N's sharp worst case is ATTAINED at every odd n = 2k+1. *)
Theorem N_worst_attained_all : forall k,
  2 * total_comparisons_N (ip (zigA k)) = 5 * size (zigA k) + 1.
Proof. intro k. apply N_worst_attained_if, pops_N_zigA. Qed.

(* So, for every n, axiom-free: best cases M >= 2n-1, N >= n+2, C exactly 3n-2;
   worst cases C and M exactly 3n-2 (M never beats the oblivious C); and N's sharp
   worst case 2*A_N <= 5n+1, i.e. A_N <= 2n + ceil(n/2) -- the published figure --
   now unconditional via lcount_N = full t + 1 (ReconstructLcount). *)

Print Assumptions M_best.
Print Assumptions N_best.
Print Assumptions M_worst.
Print Assumptions N_worst.
Print Assumptions N_worst_sharp.
Print Assumptions M_worst_attained_all.
Print Assumptions M_best_attained_all.
Print Assumptions N_best_attained_all.
Print Assumptions full_zigA.
Print Assumptions pops_N_zigA.
Print Assumptions N_worst_attained_all.

(* ------------------------------------------------------------------ *)
(* Concrete worst-case witnesses on the 7-node zigzag tree zigA 3       *)
(* (size 7).  A named, human-readable instance of the bounded checks:   *)
(* N attains its sharp worst case 2*A_N = 5n+1 (A_N = 18 = 2*7+ceil(7/2)) *)
(* and M attains the oblivious 3n-2 = 19 on the same tree.              *)
(* ------------------------------------------------------------------ *)
Example total_comparisons_N_zigA3 : total_comparisons_N (ip (zigA 3)) = 18.
Proof. vm_compute. reflexivity. Qed.

Example N_worst_sharp_zigA3 :
  2 * total_comparisons_N (ip (zigA 3)) = 5 * size (zigA 3) + 1.
Proof. vm_compute. reflexivity. Qed.

Example M_worst_zigA3 :
  total_comparisons_M (ip (zigA 3)) = 3 * size (zigA 3) - 2.
Proof. vm_compute. reflexivity. Qed.
