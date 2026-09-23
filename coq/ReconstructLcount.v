(* ReconstructLcount.v
   The remaining all-n identity for the improved algorithm N:

       lcount_N (ip t) = full t + 1            (for every non-empty tree)

   i.e. the number of index tests (= double-pop events + the sentinel break)
   is exactly the number of full nodes plus one.  Equivalently the run's
   double-pop count equals  full t.  This was previously only a computational
   check (check_N_upto_9); here it is proved for ALL n.

   With pops_N_le (S <= n-1) and full_bound (2*full + 1 <= n) this closes N's
   SHARP worst case  A_N <= 2n + ceil(n/2)  unconditionally (ReconstructBounds).

   The crux is a generalized stack invariant (lcof_gen): processing  ipo off t
   from a stack  low ++ high  -- where every element of low is < off and every
   element of high is >= off + size t -- consumes all of low at the root, leaves
   a non-empty residue rho (in t's label range) on top of high, and raises the
   double-pop counter by  full t + [2 <= length low].  The whole-tree root is
   pushed with no residue below it, so the increment is exactly  full t.
   Axiom-free.

   Build:  rocq c Trees.v Dictionary.v Reconstruct.v ReconstructN.v  (first)
           rocq c ReconstructLcount.v
   Rocq Prover 9.1.0.  Standard library only. *)

From Stdlib Require Import List Arith Bool Lia.
Import ListNotations.
Require Import Trees.
Require Import Dictionary.
Require Import Reconstruct.
Require Import ReconstructN.

Definition stkNl (st : stN) : list nat := let '(_, s, _, _, _) := st in s.

(* ------------------------------------------------------------------ *)
(* 1. The loop folds over a concatenation in two stages.               *)
(* ------------------------------------------------------------------ *)
Lemma runN_aux_app : forall xs ys st,
  runN_aux (xs ++ ys) st = runN_aux ys (runN_aux xs st).
Proof.
  induction xs as [|x xs IH]; intros ys st; [reflexivity|].
  cbn [app runN_aux]. apply IH.
Qed.

Lemma ipo_Leaf : forall off, ipo off Leaf = [].
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* 3. The inner do-while consumes a top block of small elements.       *)
(* ------------------------------------------------------------------ *)
Lemma popN_consumes : forall low high root f,
  low <> [] -> length low <= f ->
  (forall x, In x low -> x <= root) ->
  (forall y, In y high -> root < y) ->
  exists prev, popN f root (low ++ high) = (prev, high, length low).
Proof.
  induction low as [|x low' IH]; intros high root f Hne Hf Hlo Hhi.
  - contradiction.
  - destruct f as [|f']; [cbn [length] in Hf; lia|].
    destruct low' as [|y rest].
    + cbn [app length]. cbn [popN].
      destruct high as [|h hs].
      * exists x. reflexivity.
      * assert (Hh : root < h) by (apply Hhi; left; reflexivity).
        replace (Nat.leb h root) with false
          by (symmetry; apply Nat.leb_gt; lia).
        exists x. reflexivity.
    + cbn [app popN].
      assert (Hyle : Nat.leb y root = true)
        by (apply Nat.leb_le; apply Hlo; right; left; reflexivity).
      rewrite Hyle.
      assert (Hyr : (y :: rest) <> []) by discriminate.
      assert (Hf' : length (y :: rest) <= f') by (cbn [length] in Hf |- *; lia).
      assert (Hyle2 : forall z, In z (y :: rest) -> z <= root)
        by (intros z Hz; apply Hlo; right; exact Hz).
      destruct (IH high root f' Hyr Hf' Hyle2 Hhi) as [prev Hpop].
      cbn [app] in Hpop |- *. rewrite Hpop.
      exists prev. cbn [length]. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. One root step: pop the whole low block, push the root.           *)
(* ------------------------------------------------------------------ *)
Lemma stepN_root : forall root low high a ec lc pp,
  high <> [] ->
  (forall x, In x low -> x < root) ->
  (forall y, In y high -> root < y) ->
  stkNl (stepN root (a, low ++ high, ec, lc, pp)) = root :: high
  /\ lcof (stepN root (a, low ++ high, ec, lc, pp))
       = lc + (if Nat.leb 2 (length low) then 1 else 0).
Proof.
  intros root low high a ec lc pp Hhne Hlo Hhi.
  destruct high as [|h hs]; [contradiction|].
  assert (Hh : root < h) by (apply Hhi; left; reflexivity).
  unfold stepN, stkNl, lcof.
  destruct low as [|x1 low'].
  - cbn [app length].
    replace (Nat.ltb root h) with true by (symmetry; apply Nat.ltb_lt; lia).
    split; [reflexivity | cbn [length Nat.leb]; lia].
  - assert (Hx1 : x1 < root) by (apply Hlo; left; reflexivity).
    cbn [app].
    replace (Nat.ltb root x1) with false by (symmetry; apply Nat.ltb_ge; lia).
    destruct low' as [|x2 low''].
    + cbn [app length].
      replace (Nat.leb h root) with false by (symmetry; apply Nat.leb_gt; lia).
      split; [reflexivity | cbn [length Nat.leb]; lia].
    + assert (Hx2 : Nat.leb x2 root = true)
        by (apply Nat.leb_le; assert (x2 < root) by (apply Hlo; right; left; reflexivity); lia).
      cbn [app]. rewrite Hx2.
      assert (Hne2 : (x2 :: low'') <> []) by discriminate.
      assert (Hf2 : length (x2 :: low'') <= length ((x2 :: low'') ++ (h :: hs)))
        by (rewrite length_app; lia).
      assert (Hle2 : forall z, In z (x2 :: low'') -> z <= root)
        by (intros z Hz; assert (z < root) by (apply Hlo; right; exact Hz); lia).
      destruct (popN_consumes (x2 :: low'') (h :: hs) root
                  (length ((x2 :: low'') ++ h :: hs)) Hne2 Hf2 Hle2 Hhi)
        as [prev Hpop].
      cbn [app] in Hpop |- *. rewrite Hpop.
      split; [reflexivity | cbn [length Nat.leb]; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The generalized stack/double-pop invariant.                      *)
(* ------------------------------------------------------------------ *)
Lemma lcof_gen : forall t off low high a ec lc pp,
  t <> Leaf -> high <> [] ->
  (forall x, In x low -> x < off) ->
  (forall y, In y high -> off + size t <= y) ->
  exists rho,
    rho <> [] /\
    (forall z, In z rho -> off <= z /\ z < off + size t) /\
    stkNl (runN_aux (ipo off t) (a, low ++ high, ec, lc, pp)) = rho ++ high /\
    lcof (runN_aux (ipo off t) (a, low ++ high, ec, lc, pp))
      = lc + full t + (if Nat.leb 2 (length low) then 1 else 0).
Proof.
  induction t as [| l IHl r IHr]; intros off low high a ec lc pp Hne Hhne Hlo Hhi.
  - congruence.
  - clear Hne.
    assert (Hlo' : forall x, In x low -> x < off + size l)
      by (intros x Hx; pose proof (Hlo x Hx); lia).
    assert (Hhi' : forall y, In y high -> off + size l < y)
      by (intros y Hy; pose proof (Hhi y Hy) as Hb; cbn [size] in Hb; lia).
    destruct (stepN_root (off + size l) low high a ec lc pp Hhne Hlo' Hhi')
      as [Hstk1 Hlc1].
    cbn [ipo runN_aux].
    destruct (stepN (off + size l) (a, low ++ high, ec, lc, pp))
      as [[[[a1 s1] ec1] lc1] pp1] eqn:E1.
    cbn [stkNl lcof] in Hstk1, Hlc1. subst s1. clear E1.
    rewrite runN_aux_app.
    destruct l as [|ll lr] eqn:El.
    + (* l = Leaf *)
      rewrite (ipo_Leaf off). cbn [runN_aux].
      destruct r as [|rl rr] eqn:Er.
      * (* r = Leaf : single node *)
        rewrite (ipo_Leaf (off + size Leaf + 1)). cbn [runN_aux].
        exists [off + size Leaf]. split; [discriminate|]. split.
        { intros z [<-|[]]. cbn [size]. lia. }
        split.
        -- cbn [stkNl]. reflexivity.
        -- cbn [lcof full]. rewrite Hlc1. lia.
      * (* r = Node *)
        assert (HrNe : Node rl rr <> Leaf) by discriminate.
        assert (Hlor : forall x, In x [off + size Leaf] -> x < off + size Leaf + 1)
          by (intros x [<-|[]]; lia).
        assert (Hhir : forall y, In y high -> (off + size Leaf + 1) + size (Node rl rr) <= y).
        { intros y Hy. pose proof (Hhi y Hy) as Hb. cbn [size] in Hb |- *. lia. }
        change ((off + size Leaf) :: high) with ([off + size Leaf] ++ high).
        destruct (IHr (off + size Leaf + 1) [off + size Leaf] high a1 ec1 lc1 pp1
                    HrNe Hhne Hlor Hhir) as [rr0 [Hne0 [Hin0 [Hstk0 Hlc0]]]].
        exists rr0. split; [exact Hne0|]. split.
        { intros z Hz. destruct (Hin0 z Hz). cbn [size] in *. lia. }
        split.
        -- rewrite Hstk0. reflexivity.
        -- rewrite Hlc0, Hlc1. cbn [full size length Nat.leb]. lia.
    + (* l = Node ll lr *)
      assert (HlNe : Node ll lr <> Leaf) by discriminate.
      assert (HhneR : (off + size (Node ll lr)) :: high <> []) by discriminate.
      assert (Hlol : forall x, In x ([]:list nat) -> x < off) by (intros x []).
      assert (Hhil : forall y, In y ((off + size (Node ll lr)) :: high) ->
                       off + size (Node ll lr) <= y).
      { intros y [Hy|Hy]; [lia| pose proof (Hhi y Hy) as Hb; cbn [size] in Hb |- *; lia]. }
      destruct (IHl off [] ((off + size (Node ll lr)) :: high) a1 ec1 lc1 pp1
                  HlNe HhneR Hlol Hhil) as [rl0 [Hrl0ne [Hrl0in [Hrl0stk Hrl0lc]]]].
      cbn [app] in Hrl0stk, Hrl0lc. cbn [length Nat.leb] in Hrl0lc.
      destruct (runN_aux (ipo off (Node ll lr))
                  (a1, (off + size (Node ll lr)) :: high, ec1, lc1, pp1))
        as [[[[a2 s2] ec2] lc2] pp2] eqn:Einner.
      cbn [stkNl lcof] in Hrl0stk, Hrl0lc. subst s2.
      destruct r as [|rl rr] eqn:Er.
      * (* r = Leaf *)
        rewrite (ipo_Leaf (off + size (Node ll lr) + 1)). cbn [runN_aux].
        exists (rl0 ++ [off + size (Node ll lr)]). split.
        { intro Hc. apply app_eq_nil in Hc. destruct Hc as [_ Hc]. discriminate. }
        split.
        { intros z Hz. apply in_app_or in Hz. destruct Hz as [Hz|[<-|[]]].
          - destruct (Hrl0in z Hz) as [HA HB]. cbn [size] in HB |- *. lia.
          - cbn [size]. lia. }
        split.
        -- cbn [stkNl]. rewrite <- app_assoc. reflexivity.
        -- cbn [lcof]. rewrite Hrl0lc, Hlc1. cbn [full]. lia.
      * (* r = Node rl rr *)
        assert (HrNe : Node rl rr <> Leaf) by discriminate.
        assert (Hlor : forall x, In x (rl0 ++ [off + size (Node ll lr)]) ->
                         x < off + size (Node ll lr) + 1).
        { intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx|[<-|[]]].
          - destruct (Hrl0in x Hx). lia.
          - lia. }
        assert (Hhir : forall y, In y high ->
                  (off + size (Node ll lr) + 1) + size (Node rl rr) <= y).
        { intros y Hy. pose proof (Hhi y Hy) as Hb. cbn [size] in Hb |- *. lia. }
        replace (rl0 ++ (off + size (Node ll lr)) :: high)
          with ((rl0 ++ [off + size (Node ll lr)]) ++ high)
          by (rewrite <- app_assoc; reflexivity).
        destruct (IHr (off + size (Node ll lr) + 1) (rl0 ++ [off + size (Node ll lr)])
                    high a2 ec2 lc2 pp2 HrNe Hhne Hlor Hhir)
          as [rr0 [Hrr0ne [Hrr0in [Hrr0stk Hrr0lc]]]].
        exists rr0. split; [exact Hrr0ne|]. split.
        { intros z Hz. destruct (Hrr0in z Hz). cbn [size] in *. lia. }
        split.
        -- rewrite Hrr0stk. reflexivity.
        -- rewrite Hrr0lc, Hrl0lc, Hlc1.
           assert (Hlen : Nat.leb 2 (length (rl0 ++ [off + size (Node ll lr)])) = true).
           { apply Nat.leb_le. rewrite length_app. cbn [length].
             destruct rl0; [contradiction Hrl0ne; reflexivity | cbn [length]; lia]. }
           rewrite Hlen. cbn [full size]. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2'. The stack and lc-counter ignore the array / ec / pp.            *)
(* ------------------------------------------------------------------ *)
Lemma stepN_stk_lc : forall cur a a' s ec ec' lc pp pp',
  stkNl (stepN cur (a, s, ec, lc, pp)) = stkNl (stepN cur (a', s, ec', lc, pp'))
  /\ lcof (stepN cur (a, s, ec, lc, pp)) = lcof (stepN cur (a', s, ec', lc, pp')).
Proof.
  intros cur a a' s ec ec' lc pp pp'. unfold stepN, stkNl, lcof.
  destruct s as [|top s']; [split; reflexivity|].
  destruct (Nat.ltb cur top); [split; reflexivity|].
  destruct s' as [|top2 s'']; [split; reflexivity|].
  destruct (Nat.leb top2 cur).
  - destruct (popN (length (top2 :: s'')) cur (top2 :: s'')) as [[prev r] k].
    split; reflexivity.
  - split; reflexivity.
Qed.

Lemma lcof_aec_indep : forall xs a a' s ec ec' lc pp pp',
  lcof (runN_aux xs (a, s, ec, lc, pp)) = lcof (runN_aux xs (a', s, ec', lc, pp')).
Proof.
  induction xs as [|cur rest IH]; intros a a' s ec ec' lc pp pp'.
  - reflexivity.
  - cbn [runN_aux].
    destruct (stepN cur (a, s, ec, lc, pp)) as [[[[a1 s1] ec1] lc1] pp1] eqn:E1.
    destruct (stepN cur (a', s, ec', lc, pp')) as [[[[a2 s2] ec2] lc2] pp2] eqn:E2.
    pose proof (stepN_stk_lc cur a a' s ec ec' lc pp pp') as [Hs Hl].
    rewrite E1, E2 in Hs, Hl. unfold stkNl, lcof in Hs, Hl. subst s2 lc2.
    apply IH.
Qed.

(* ------------------------------------------------------------------ *)
(* 6. Top level: the whole-tree root is pushed with empty residue, so  *)
(*    the double-pop count is exactly full t, and lcount_N = full t+1. *)
(* ------------------------------------------------------------------ *)
Lemma runN0_as_gen : forall t, t <> Leaf ->
  lcof (runN0 (ip t)) = lcof (runN_aux (ipo 0 t) (empty, [size t], 0, 0, 0)).
Proof.
  intros t Hne. destruct t as [|l r]; [congruence|].
  unfold ip. cbn [ipo]. unfold runN0. cbn [runN_aux].
  set (rest := ipo 0 l ++ ipo (0 + size l + 1) r).
  replace (length (0 + size l :: rest)) with (size (Node l r)).
  2:{ cbn [length size]. unfold rest. rewrite length_app, ipo_length, ipo_length. lia. }
  set (n := size (Node l r)).
  assert (Hlt : Nat.ltb (0 + size l) n = true)
    by (apply Nat.ltb_lt; unfold n; cbn [size]; lia).
  unfold stepN. rewrite Hlt.
  apply lcof_aec_indep.
Qed.

Lemma lcof_full : forall t, t <> Leaf -> lcof (runN0 (ip t)) = full t.
Proof.
  intros t Hne. rewrite (runN0_as_gen t Hne).
  destruct (lcof_gen t 0 [] [size t] empty 0 0 0 Hne ltac:(discriminate)
              ltac:(intros x []) ltac:(intros y [<-|[]]; lia))
    as [rho [_ [_ [_ Hlc]]]].
  cbn [app] in Hlc. rewrite Hlc. cbn [length Nat.leb]. lia.
Qed.

Theorem lcount_N_full : forall t, t <> Leaf -> lcount_N (ip t) = full t + 1.
Proof.
  intros t Hne. unfold lcount_N. rewrite (lcof_full t Hne). reflexivity.
Qed.

Print Assumptions lcount_N_full.

(* ------------------------------------------------------------------ *)
(* Regression: lcount_N = full + 1 on the running 7-node example,        *)
(* with full tree7 = 2 (so lcount_N (ip tree7) = 3).                     *)
(* ------------------------------------------------------------------ *)
Example full_tree7 : full tree7 = 2.
Proof. vm_compute. reflexivity. Qed.

Example lcount_N_full_tree7 : lcount_N (ip tree7) = full tree7 + 1.
Proof. vm_compute. reflexivity. Qed.
