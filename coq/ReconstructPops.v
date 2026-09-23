(* ReconstructPops.v
   The pop count of the i-p reconstruction is a STRUCTURAL tree statistic:

       pops_N (ip t) = pops_M (ip t) = Srec t                (for all t)

   where  Srec(Leaf)=0,  Srec(Node l Leaf)=Srec l,  Srec(Node l r)=size l+1+Srec r
   (r<>Leaf).  Although pops is run-dependent (two same-size trees can have
   different pops), it satisfies this clean recurrence, proved here from the
   algorithm by a generalized stack invariant (ppof_gen) mirroring lcof_gen.

   The key algebraic fact is  Srec t + rlen t = size t,  where rlen t is the
   length of the residue the run leaves on the stack after processing t.

   Build:  rocq c Trees.v Dictionary.v Reconstruct.v ReconstructN.v
                  ReconstructLcount.v   (first)
           rocq c ReconstructPops.v
   Rocq Prover 9.1.0.  Standard library only.  Axiom-free. *)

From Stdlib Require Import List Arith Bool Lia.
Import ListNotations.
Require Import Trees.
Require Import Dictionary.
Require Import Reconstruct.
Require Import ReconstructM.
Require Import ReconstructN.
Require Import ReconstructLcount.
Require Import ReconstructBounds.

(* ------------------------------------------------------------------ *)
(* The structural statistic and the residue length                    *)
(* ------------------------------------------------------------------ *)
Fixpoint Srec (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l r => match r with Leaf => Srec l | _ => size l + 1 + Srec r end
  end.

Fixpoint rlen (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l r => match r with Leaf => S (rlen l) | _ => rlen r end
  end.

Lemma srec_rlen_size : forall t, Srec t + rlen t = size t.
Proof.
  induction t as [|l IHl r IHr]; [reflexivity|].
  destruct r as [|rl rr]; cbn [Srec rlen size] in *; lia.
Qed.

Lemma rlen_pos : forall t, t <> Leaf -> 1 <= rlen t.
Proof.
  induction t as [|l IHl r IHr]; [congruence|]. intros _.
  destruct r as [|rl rr]; cbn [rlen]; [lia | apply IHr; discriminate].
Qed.

(* ------------------------------------------------------------------ *)
(* One root step raises the pop counter by  length low.                *)
(* ------------------------------------------------------------------ *)
Lemma stepN_root_pp : forall root low high a ec lc pp,
  high <> [] ->
  (forall x, In x low -> x < root) ->
  (forall y, In y high -> root < y) ->
  stkNl (stepN root (a, low ++ high, ec, lc, pp)) = root :: high
  /\ ppof (stepN root (a, low ++ high, ec, lc, pp)) = pp + length low.
Proof.
  intros root low high a ec lc pp Hhne Hlo Hhi.
  destruct high as [|h hs]; [contradiction|].
  assert (Hh : root < h) by (apply Hhi; left; reflexivity).
  unfold stepN, stkNl, ppof.
  destruct low as [|x1 low'].
  - cbn [app length].
    replace (Nat.ltb root h) with true by (symmetry; apply Nat.ltb_lt; lia).
    split; [reflexivity | lia].
  - assert (Hx1 : x1 < root) by (apply Hlo; left; reflexivity).
    cbn [app].
    replace (Nat.ltb root x1) with false by (symmetry; apply Nat.ltb_ge; lia).
    destruct low' as [|x2 low''].
    + cbn [app length].
      replace (Nat.leb h root) with false by (symmetry; apply Nat.leb_gt; lia).
      split; [reflexivity | lia].
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
      split; [reflexivity | cbn [length]; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* The generalized stack / pop invariant (mirrors lcof_gen).           *)
(* The residue has length rlen t and the pop counter rises by          *)
(*   Srec t + length low.                                              *)
(* ------------------------------------------------------------------ *)
Lemma ppof_gen : forall t off low high a ec lc pp,
  t <> Leaf -> high <> [] ->
  (forall x, In x low -> x < off) ->
  (forall y, In y high -> off + size t <= y) ->
  exists rho,
    rho <> [] /\ length rho = rlen t /\
    (forall z, In z rho -> off <= z /\ z < off + size t) /\
    stkNl (runN_aux (ipo off t) (a, low ++ high, ec, lc, pp)) = rho ++ high /\
    ppof (runN_aux (ipo off t) (a, low ++ high, ec, lc, pp))
      = pp + Srec t + length low.
Proof.
  induction t as [| l IHl r IHr]; intros off low high a ec lc pp Hne Hhne Hlo Hhi.
  - congruence.
  - clear Hne.
    assert (Hlo' : forall x, In x low -> x < off + size l)
      by (intros x Hx; pose proof (Hlo x Hx); lia).
    assert (Hhi' : forall y, In y high -> off + size l < y)
      by (intros y Hy; pose proof (Hhi y Hy) as Hb; cbn [size] in Hb; lia).
    destruct (stepN_root_pp (off + size l) low high a ec lc pp Hhne Hlo' Hhi')
      as [Hstk1 Hpp1].
    cbn [ipo runN_aux].
    destruct (stepN (off + size l) (a, low ++ high, ec, lc, pp))
      as [[[[a1 s1] ec1] lc1] pp1] eqn:E1.
    cbn [stkNl ppof] in Hstk1, Hpp1. subst s1. subst pp1. clear E1.
    rewrite runN_aux_app.
    destruct l as [|ll lr] eqn:El.
    + (* l = Leaf *)
      rewrite (ipo_Leaf off). cbn [runN_aux].
      destruct r as [|rl rr] eqn:Er.
      * (* r = Leaf : single node *)
        rewrite (ipo_Leaf (off + size Leaf + 1)). cbn [runN_aux].
        exists [off + size Leaf]. split; [discriminate|]. split; [reflexivity|]. split.
        { intros z [<-|[]]. cbn [size]. lia. }
        split.
        -- cbn [stkNl]. reflexivity.
        -- cbn [ppof Srec size]. lia.
      * (* r = Node *)
        assert (HrNe : Node rl rr <> Leaf) by discriminate.
        assert (Hlor : forall x, In x [off + size Leaf] -> x < off + size Leaf + 1)
          by (intros x [<-|[]]; lia).
        assert (Hhir : forall y, In y high -> (off + size Leaf + 1) + size (Node rl rr) <= y).
        { intros y Hy. pose proof (Hhi y Hy) as Hb. cbn [size] in Hb |- *. lia. }
        change ((off + size Leaf) :: high) with ([off + size Leaf] ++ high).
        destruct (IHr (off + size Leaf + 1) [off + size Leaf] high a1 ec1 lc1 (pp + length low)
                    HrNe Hhne Hlor Hhir)
          as [rr0 [Hne0 [Hlen0 [Hin0 [Hstk0 Hpp0]]]]].
        exists rr0. split; [exact Hne0|]. split.
        { cbn [rlen]. exact Hlen0. }
        split.
        { intros z Hz. destruct (Hin0 z Hz). cbn [size] in *. lia. }
        split.
        -- rewrite Hstk0. reflexivity.
        -- rewrite Hpp0. cbn [Srec size length]. lia.
    + (* l = Node ll lr *)
      assert (HlNe : Node ll lr <> Leaf) by discriminate.
      assert (HhneR : (off + size (Node ll lr)) :: high <> []) by discriminate.
      assert (Hlol : forall x, In x ([]:list nat) -> x < off) by (intros x []).
      assert (Hhil : forall y, In y ((off + size (Node ll lr)) :: high) ->
                       off + size (Node ll lr) <= y).
      { intros y [Hy|Hy]; [lia| pose proof (Hhi y Hy) as Hb; cbn [size] in Hb |- *; lia]. }
      destruct (IHl off [] ((off + size (Node ll lr)) :: high) a1 ec1 lc1 (pp + length low)
                  HlNe HhneR Hlol Hhil)
        as [rl0 [Hrl0ne [Hrl0len [Hrl0in [Hrl0stk Hrl0pp]]]]].
      cbn [app] in Hrl0stk, Hrl0pp. cbn [length] in Hrl0pp.
      destruct (runN_aux (ipo off (Node ll lr))
                  (a1, (off + size (Node ll lr)) :: high, ec1, lc1, pp + length low))
        as [[[[a2 s2] ec2] lc2] pp2] eqn:Einner.
      cbn [stkNl ppof] in Hrl0stk, Hrl0pp. subst s2.
      destruct r as [|rl rr] eqn:Er.
      * (* r = Leaf *)
        rewrite (ipo_Leaf (off + size (Node ll lr) + 1)). cbn [runN_aux].
        exists (rl0 ++ [off + size (Node ll lr)]). split.
        { intro Hc. apply app_eq_nil in Hc. destruct Hc as [_ Hc]. discriminate. }
        split.
        { change (rlen (Node (Node ll lr) Leaf)) with (S (rlen (Node ll lr))).
          rewrite length_app, Hrl0len. cbn [length]. lia. }
        split.
        { intros z Hz. apply in_app_or in Hz. destruct Hz as [Hz|[<-|[]]].
          - destruct (Hrl0in z Hz) as [HA HB]. cbn [size] in HB |- *. lia.
          - cbn [size]. lia. }
        split.
        -- cbn [stkNl]. rewrite <- app_assoc. reflexivity.
        -- cbn [ppof].
           change (Srec (Node (Node ll lr) Leaf)) with (Srec (Node ll lr)).
           rewrite Hrl0pp. cbn [length]. lia.
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
          as [rr0 [Hrr0ne [Hrr0len [Hrr0in [Hrr0stk Hrr0pp]]]]].
        exists rr0. split; [exact Hrr0ne|]. split.
        { cbn [rlen]. exact Hrr0len. }
        split.
        { intros z Hz. destruct (Hrr0in z Hz). cbn [size] in *. lia. }
        split.
        -- rewrite Hrr0stk. reflexivity.
        -- change (Srec (Node (Node ll lr) (Node rl rr)))
             with (size (Node ll lr) + 1 + Srec (Node rl rr)).
           rewrite Hrr0pp, Hrl0pp, length_app, Hrl0len. cbn [length].
           pose proof (srec_rlen_size (Node ll lr)) as Hsz. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Top level: pops_N (ip t) = Srec t.                                  *)
(* ------------------------------------------------------------------ *)
Lemma ppof_runN0_gen : forall t, t <> Leaf ->
  ppof (runN0 (ip t)) = ppof (runN_aux (ipo 0 t) (empty, [size t], 0, 0, 0)).
Proof.
  intros t Hne. destruct t as [|l r]; [congruence|].
  unfold ip. cbn [ipo]. unfold runN0. cbn [runN_aux].
  set (rest := ipo 0 l ++ ipo (0 + size l + 1) r).
  replace (length (0 + size l :: rest)) with (size (Node l r)).
  2:{ cbn [length size]. unfold rest. rewrite length_app, ipo_length, ipo_length. lia. }
  set (n := size (Node l r)).
  assert (Hlt : Nat.ltb (0 + size l) n = true)
    by (apply Nat.ltb_lt; unfold n; cbn [size]; lia).
  unfold stepN. rewrite Hlt. cbn [ppof].
  apply ppof_aec_indep.
Qed.

Theorem pops_N_Srec : forall t, pops_N (ip t) = Srec t.
Proof.
  intros t. destruct t as [|l r].
  - reflexivity.
  - assert (Hne : Node l r <> Leaf) by discriminate.
    unfold pops_N. rewrite (ppof_runN0_gen (Node l r) Hne).
    destruct (ppof_gen (Node l r) 0 [] [size (Node l r)] empty 0 0 0 Hne ltac:(discriminate)
                ltac:(intros x []) ltac:(intros y [<-|[]]; lia))
      as [rho [_ [_ [_ [_ Hpp]]]]].
    cbn [app length] in Hpp. rewrite Hpp. lia.
Qed.

Print Assumptions pops_N_Srec.

(* ------------------------------------------------------------------ *)
(* Makinen's pop count agrees with the improved algorithm's, so it is  *)
(* the same structural statistic: pops_M (ip t) = Srec t.              *)
(* The two runs evolve the stack identically and pop the same number   *)
(* of elements per step (N only keeps extra counters).                 *)
(* ------------------------------------------------------------------ *)
Definition stkM (st : stateM) : list nat := let '(_, s, _, _) := st in s.

Lemma popM_popN : forall f cur s, popM f cur s = popN f cur s.
Proof.
  induction f as [|f IH]; intros cur s; [reflexivity|].
  destruct s as [|top s']; [reflexivity|].
  destruct s' as [|top2 s'']; [reflexivity|].
  cbn [popM popN]. destruct (Nat.leb top2 cur); [rewrite IH | reflexivity]; reflexivity.
Qed.

Lemma runM_aux_app : forall xs ys st,
  runM_aux (xs ++ ys) st = runM_aux ys (runM_aux xs st).
Proof.
  induction xs as [|x xs IH]; intros ys st; [reflexivity|].
  cbn [app runM_aux]. apply IH.
Qed.

Lemma stepM_root_pp : forall root low high a c p,
  high <> [] ->
  (forall x, In x low -> x < root) ->
  (forall y, In y high -> root < y) ->
  stkM (stepM root (a, low ++ high, c, p)) = root :: high
  /\ popof (stepM root (a, low ++ high, c, p)) = p + length low.
Proof.
  intros root low high a c p Hhne Hlo Hhi.
  destruct high as [|h hs]; [contradiction|].
  assert (Hh : root < h) by (apply Hhi; left; reflexivity).
  unfold stepM, stkM, popof.
  destruct low as [|x1 low'].
  - cbn [app].
    replace (Nat.ltb root h) with true by (symmetry; apply Nat.ltb_lt; lia).
    cbn [length]. split; [reflexivity | lia].
  - assert (Hx1 : x1 < root) by (apply Hlo; left; reflexivity).
    cbn [app].
    replace (Nat.ltb root x1) with false by (symmetry; apply Nat.ltb_ge; lia).
    rewrite popM_popN.
    assert (Hne1 : (x1 :: low') <> []) by discriminate.
    assert (Hf1 : length (x1 :: low') <= length ((x1 :: low') ++ (h :: hs)))
      by (rewrite length_app; lia).
    assert (Hle1 : forall z, In z (x1 :: low') -> z <= root)
      by (intros z Hz; assert (z < root) by (apply Hlo; exact Hz); lia).
    destruct (popN_consumes (x1 :: low') (h :: hs) root
                (length ((x1 :: low') ++ h :: hs)) Hne1 Hf1 Hle1 Hhi) as [prev Hpop].
    cbn [app] in Hpop |- *. rewrite Hpop.
    split; [reflexivity | cbn [length]; lia].
Qed.

(* The M-version of ppof_gen: same stack dynamics, same pop count. *)
Lemma ppof_genM : forall t off low high a c p,
  t <> Leaf -> high <> [] ->
  (forall x, In x low -> x < off) ->
  (forall y, In y high -> off + size t <= y) ->
  exists rho,
    rho <> [] /\ length rho = rlen t /\
    (forall z, In z rho -> off <= z /\ z < off + size t) /\
    stkM (runM_aux (ipo off t) (a, low ++ high, c, p)) = rho ++ high /\
    popof (runM_aux (ipo off t) (a, low ++ high, c, p)) = p + Srec t + length low.
Proof.
  induction t as [| l IHl r IHr]; intros off low high a c p Hne Hhne Hlo Hhi.
  - congruence.
  - clear Hne.
    assert (Hlo' : forall x, In x low -> x < off + size l)
      by (intros x Hx; pose proof (Hlo x Hx); lia).
    assert (Hhi' : forall y, In y high -> off + size l < y)
      by (intros y Hy; pose proof (Hhi y Hy) as Hb; cbn [size] in Hb; lia).
    destruct (stepM_root_pp (off + size l) low high a c p Hhne Hlo' Hhi')
      as [Hstk1 Hpp1].
    cbn [ipo runM_aux].
    destruct (stepM (off + size l) (a, low ++ high, c, p))
      as [[[a1 s1] c1] p1] eqn:E1.
    cbn [stkM popof] in Hstk1, Hpp1. subst s1. subst p1. clear E1.
    rewrite runM_aux_app.
    destruct l as [|ll lr] eqn:El.
    + (* l = Leaf *)
      rewrite (ipo_Leaf off). cbn [runM_aux].
      destruct r as [|rl rr] eqn:Er.
      * rewrite (ipo_Leaf (off + size Leaf + 1)). cbn [runM_aux].
        exists [off + size Leaf]. split; [discriminate|]. split; [reflexivity|]. split.
        { intros z [<-|[]]. cbn [size]. lia. }
        split.
        -- cbn [stkM]. reflexivity.
        -- cbn [popof Srec size]. lia.
      * assert (HrNe : Node rl rr <> Leaf) by discriminate.
        assert (Hlor : forall x, In x [off + size Leaf] -> x < off + size Leaf + 1)
          by (intros x [<-|[]]; lia).
        assert (Hhir : forall y, In y high -> (off + size Leaf + 1) + size (Node rl rr) <= y).
        { intros y Hy. pose proof (Hhi y Hy) as Hb. cbn [size] in Hb |- *. lia. }
        change ((off + size Leaf) :: high) with ([off + size Leaf] ++ high).
        destruct (IHr (off + size Leaf + 1) [off + size Leaf] high a1 c1 (p + length low)
                    HrNe Hhne Hlor Hhir)
          as [rr0 [Hne0 [Hlen0 [Hin0 [Hstk0 Hpp0]]]]].
        exists rr0. split; [exact Hne0|]. split.
        { cbn [rlen]. exact Hlen0. }
        split.
        { intros z Hz. destruct (Hin0 z Hz). cbn [size] in *. lia. }
        split.
        -- rewrite Hstk0. reflexivity.
        -- rewrite Hpp0. cbn [Srec size length]. lia.
    + (* l = Node ll lr *)
      assert (HlNe : Node ll lr <> Leaf) by discriminate.
      assert (HhneR : (off + size (Node ll lr)) :: high <> []) by discriminate.
      assert (Hlol : forall x, In x ([]:list nat) -> x < off) by (intros x []).
      assert (Hhil : forall y, In y ((off + size (Node ll lr)) :: high) ->
                       off + size (Node ll lr) <= y).
      { intros y [Hy|Hy]; [lia| pose proof (Hhi y Hy) as Hb; cbn [size] in Hb |- *; lia]. }
      destruct (IHl off [] ((off + size (Node ll lr)) :: high) a1 c1 (p + length low)
                  HlNe HhneR Hlol Hhil)
        as [rl0 [Hrl0ne [Hrl0len [Hrl0in [Hrl0stk Hrl0pp]]]]].
      cbn [app] in Hrl0stk, Hrl0pp. cbn [length] in Hrl0pp.
      destruct (runM_aux (ipo off (Node ll lr))
                  (a1, (off + size (Node ll lr)) :: high, c1, p + length low))
        as [[[a2 s2] c2] p2] eqn:Einner.
      cbn [stkM popof] in Hrl0stk, Hrl0pp. subst s2.
      destruct r as [|rl rr] eqn:Er.
      * rewrite (ipo_Leaf (off + size (Node ll lr) + 1)). cbn [runM_aux].
        exists (rl0 ++ [off + size (Node ll lr)]). split.
        { intro Hc. apply app_eq_nil in Hc. destruct Hc as [_ Hc]. discriminate. }
        split.
        { change (rlen (Node (Node ll lr) Leaf)) with (S (rlen (Node ll lr))).
          rewrite length_app, Hrl0len. cbn [length]. lia. }
        split.
        { intros z Hz. apply in_app_or in Hz. destruct Hz as [Hz|[<-|[]]].
          - destruct (Hrl0in z Hz) as [HA HB]. cbn [size] in HB |- *. lia.
          - cbn [size]. lia. }
        split.
        -- cbn [stkM]. rewrite <- app_assoc. reflexivity.
        -- cbn [popof].
           change (Srec (Node (Node ll lr) Leaf)) with (Srec (Node ll lr)).
           rewrite Hrl0pp. cbn [length]. lia.
      * assert (HrNe : Node rl rr <> Leaf) by discriminate.
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
                    high a2 c2 p2 HrNe Hhne Hlor Hhir)
          as [rr0 [Hrr0ne [Hrr0len [Hrr0in [Hrr0stk Hrr0pp]]]]].
        exists rr0. split; [exact Hrr0ne|]. split.
        { cbn [rlen]. exact Hrr0len. }
        split.
        { intros z Hz. destruct (Hrr0in z Hz). cbn [size] in *. lia. }
        split.
        -- rewrite Hrr0stk. reflexivity.
        -- change (Srec (Node (Node ll lr) (Node rl rr)))
             with (size (Node ll lr) + 1 + Srec (Node rl rr)).
           rewrite Hrr0pp, Hrl0pp, length_app, Hrl0len. cbn [length].
           pose proof (srec_rlen_size (Node ll lr)) as Hsz. lia.
Qed.

Lemma stepM_stk_pop : forall cur a a' s c c' p,
  stkM (stepM cur (a, s, c, p)) = stkM (stepM cur (a', s, c', p))
  /\ popof (stepM cur (a, s, c, p)) = popof (stepM cur (a', s, c', p)).
Proof.
  intros cur a a' s c c' p. unfold stepM, stkM, popof.
  destruct s as [|top s']; [split; reflexivity|].
  destruct (Nat.ltb cur top); [split; reflexivity|].
  destruct (popM (length (top :: s')) cur (top :: s')) as [[prev r] k].
  split; reflexivity.
Qed.

Lemma popof_ac_indep : forall xs a a' s c c' p,
  stkM (runM_aux xs (a, s, c, p)) = stkM (runM_aux xs (a', s, c', p))
  /\ popof (runM_aux xs (a, s, c, p)) = popof (runM_aux xs (a', s, c', p)).
Proof.
  induction xs as [|cur rest IH]; intros a a' s c c' p.
  - split; reflexivity.
  - cbn [runM_aux].
    destruct (stepM cur (a, s, c, p)) as [[[a1 s1] c1] p1] eqn:E1.
    destruct (stepM cur (a', s, c', p)) as [[[a2 s2] c2] p2] eqn:E2.
    pose proof (stepM_stk_pop cur a a' s c c' p) as [Hs Hp].
    rewrite E1, E2 in Hs, Hp. unfold stkM, popof in Hs, Hp. subst s2 p2.
    exact (IH a1 a2 s1 c1 c2 p1).
Qed.

Lemma popof_runM0_gen : forall t, t <> Leaf ->
  popof (runM_full (ip t)) = popof (runM_aux (ipo 0 t) (empty, [size t], 0, 0)).
Proof.
  intros t Hne. destruct t as [|l r]; [congruence|].
  unfold ip. cbn [ipo]. unfold runM_full. cbn [runM_aux].
  set (rest := ipo 0 l ++ ipo (0 + size l + 1) r).
  replace (length (0 + size l :: rest)) with (size (Node l r)).
  2:{ cbn [length size]. unfold rest. rewrite length_app, ipo_length, ipo_length. lia. }
  set (n := size (Node l r)).
  assert (Hlt : Nat.ltb (0 + size l) n = true)
    by (apply Nat.ltb_lt; unfold n; cbn [size]; lia).
  unfold stepM. rewrite Hlt. cbn [popof].
  apply (proj2 (popof_ac_indep rest _ _ _ _ _ _)).
Qed.

Theorem pops_M_Srec : forall t, pops_M (ip t) = Srec t.
Proof.
  intros t. destruct t as [|l r].
  - reflexivity.
  - assert (Hne : Node l r <> Leaf) by discriminate.
    unfold pops_M. rewrite (popof_runM0_gen (Node l r) Hne).
    destruct (ppof_genM (Node l r) 0 [] [size (Node l r)] empty 0 0 Hne ltac:(discriminate)
                ltac:(intros x []) ltac:(intros y [<-|[]]; lia))
      as [rho [_ [_ [_ [_ Hpp]]]]].
    cbn [app length] in Hpp. rewrite Hpp. lia.
Qed.

Theorem pops_M_eq_N : forall t, pops_M (ip t) = pops_N (ip t).
Proof. intro t. rewrite pops_M_Srec, pops_N_Srec. reflexivity. Qed.

Print Assumptions pops_M_Srec.

(* ------------------------------------------------------------------ *)
(* Regression: S is structural on the paper's running 7-node example   *)
(* (ip = [4;1;0;2;3;6;5]).  Both the M and the N run pop exactly         *)
(* Srec tree7 = 5 times.                                                *)
(* ------------------------------------------------------------------ *)
Example Srec_tree7 : Srec tree7 = 5.
Proof. vm_compute. reflexivity. Qed.

Example pops_N_Srec_tree7 : pops_N (ip tree7) = Srec tree7.
Proof. vm_compute. reflexivity. Qed.

Example pops_M_Srec_tree7 : pops_M (ip tree7) = Srec tree7.
Proof. vm_compute. reflexivity. Qed.
