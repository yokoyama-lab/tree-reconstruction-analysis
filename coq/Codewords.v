(** * Codewords <-> binary trees: bijection and stack semantics

    Theme 7, mechanisation part B (Rocq 9.1).

    A codeword is a list of naturals  (x_1, ..., x_{n-1})  encoding an
    unlabelled binary tree on  n  internal nodes  (n = size of the tree, and
    [length codeword = n - 1]).  Validity is the height recurrence

        h_0 = 1,    h_i = h_{i-1} + 1 - x_i,    x_i <= h_{i-1}.

    Decoder (Maekinen's [buildA]): start with the root on the stack; for each
    x_i, if x_i = 0 the new node is the LEFT child of the stack top, otherwise
    pop x_i nodes and the new node is the RIGHT child of the last popped node;
    push the new node in both cases.  S = sum of x_i, and the final stack
    height is h = n - S.

    Design note.  The eager assignment of left children in [buildA] makes a
    naive [list tree] stack fold non-functional (the head's subtree depends on
    nodes pushed later).  We therefore model the decoder as a structurally
    recursive *recursive-descent parser* [decode_node] over the codeword,
    which is the exact inverse of a structural *encoder* [enc] on trees.  Both
    are total.  This formulation yields the bijection cleanly while remaining
    faithful to the stack semantics, which we connect through the height
    function and the [sum]/[size] identities.

    Everything below is closed with Qed (no Admitted / Axiom). *)

Require Import List Arith Lia.
Import ListNotations.

(* ===================================================================== *)
(** ** Binary trees *)
(* ===================================================================== *)

Inductive tree : Type :=
| Leaf : tree                         (* the empty tree *)
| Node : tree -> tree -> tree.        (* Node l r *)

Fixpoint size (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l r => 1 + size l + size r
  end.

(* ===================================================================== *)
(** ** Validity via the height recurrence *)
(* ===================================================================== *)

Fixpoint valid_from (h : nat) (w : list nat) : Prop :=
  match w with
  | [] => True
  | x :: w' => x <= h /\ valid_from (h + 1 - x) w'
  end.

Definition valid (w : list nat) : Prop := valid_from 1 w.

Fixpoint valid_fromb (h : nat) (w : list nat) : bool :=
  match w with
  | [] => true
  | x :: w' => (x <=? h) && valid_fromb (h + 1 - x) w'
  end.

Definition validb (w : list nat) : bool := valid_fromb 1 w.

Lemma valid_fromb_correct : forall w h,
  valid_fromb h w = true <-> valid_from h w.
Proof.
  induction w as [|x w IH]; intros h; simpl.
  - split; auto.
  - rewrite Bool.andb_true_iff, Nat.leb_le, IH. tauto.
Qed.

(** Final stack height after running [buildA] from height [h]. *)
Fixpoint final_h (h : nat) (w : list nat) : nat :=
  match w with
  | [] => h
  | x :: w' => final_h (h + 1 - x) w'
  end.

(** S = total number of pops. *)
Definition sumw (w : list nat) : nat := fold_right Nat.add 0 w.

(* ===================================================================== *)
(** ** The encoder (structural recursion on the tree) *)
(* ===================================================================== *)

(** [enc t] returns the codeword of [t] together with [remaining t], the
    number of nodes of [t] that stay on the stack when [t] is built: the
    length of the chain of nested right-spine bottoms (u_{j+1} = bottom of
    the right spine of u_j's left subtree; see the stack-reconstruction
    invariant in reversible_construction.tex).  This second component is
    exactly the bookkeeping that drives the decoder's right-child decision. *)

Fixpoint enc (t : tree) : list nat * nat :=
  match t with
  | Leaf => ([], 0)
  | Node L R =>
      let codeL := match L with Leaf => [] | _ => 0 :: fst (enc L) end in
      let reml  := match L with Leaf => 0 | _ => snd (enc L) end in
      match R with
      | Leaf => (codeL, reml + 1)
      | _ => (codeL ++ (reml + 1) :: fst (enc R), snd (enc R))
      end
  end.

Definition encode (t : tree) : list nat := fst (enc t).
Definition rem (t : tree) : nat := snd (enc t).

(* ===================================================================== *)
(** ** The decoder (recursive-descent parser, structural on the codeword) *)
(* ===================================================================== *)

(** [decode_node w] parses the encoding of a single subtree from the front of
    [w], returning the parsed tree, the unconsumed suffix, and that subtree's
    [remaining] value.  The recursion is structural: every recursive call is on
    a strict suffix [w']. *)

(** We use a fuel argument because the suffix returned by a recursive call is
    not a structural subterm of the input.  Fuel [= length w] always suffices
    (each successful node consumes at least one symbol, except the final
    childless node which consumes none -- handled by the explicit base).  We
    prove that, with enough fuel, the result is independent of the exact fuel
    value, so [decode] below is well defined. *)

Fixpoint decode_node (fuel : nat) (w : list nat) : tree * list nat * nat :=
  match fuel with
  | 0 => (Node Leaf Leaf, w, 1)   (* out of fuel: childless node *)
  | S fuel' =>
      match w with
      | 0 :: w' =>
          (* a left child is present *)
          let '(L, w1, reml) := decode_node fuel' w' in
          match w1 with
          | x :: w2 =>
              if Nat.eqb x (reml + 1)
              then let '(R, w3, remr) := decode_node fuel' w2 in (Node L R, w3, remr)
              else (Node L Leaf, w1, reml + 1)
          | [] => (Node L Leaf, w1, reml + 1)
          end
      | x :: w' =>
          (* no left child; [reml = 0], so a right child needs marker [1] *)
          if Nat.eqb x 1
          then let '(R, w3, remr) := decode_node fuel' w' in (Node Leaf R, w3, remr)
          else (Node Leaf Leaf, w, 1)
      | [] => (Node Leaf Leaf, [], 1)
      end
  end.

(** Top-level decoder.  Fuel [= length w] always suffices on the encodings we
    care about (see [decode_node_enc]). *)
Definition decode (w : list nat) : tree := fst (fst (decode_node (S (length w)) w)).

(* ===================================================================== *)
(** ** Key composition lemma: decode_node (encode t ++ rest) *)
(* ===================================================================== *)

(** The decoder, applied to [encode t] followed by any continuation [rest]
    whose head exceeds [rem t] (or is empty), consumes exactly [encode t] and
    returns [t].  The guard [hd > rem t] is what a valid completing context
    always provides, and it is preserved by the recursion (a right child's
    marker [reml + 1] is strictly above the left subtree's [reml]). *)

Definition guard (rest : list nat) (r : nat) : Prop :=
  match rest with [] => True | y :: _ => y > r end.

(** Small helpers about [enc] on non-Leaf children.  These let us rewrite the
    codeword of a [Node] without unfolding the recursive calls. *)

Lemma encode_LN : forall R, R <> Leaf ->
  encode (Node Leaf R) = 1 :: encode R /\ rem (Node Leaf R) = rem R.
Proof.
  intros R HR. unfold encode, rem; destruct R; [congruence|]; simpl; auto.
Qed.

Lemma encode_NL : forall L, L <> Leaf ->
  encode (Node L Leaf) = 0 :: encode L /\ rem (Node L Leaf) = rem L + 1.
Proof.
  intros L HL. unfold encode, rem; destruct L; [congruence|]; simpl; auto.
Qed.

Lemma encode_NN : forall L R, L <> Leaf -> R <> Leaf ->
  encode (Node L R) = 0 :: encode L ++ (rem L + 1) :: encode R
  /\ rem (Node L R) = rem R.
Proof.
  intros L R HL HR. unfold encode, rem; destruct L; [congruence|];
  destruct R; [congruence|]; simpl; auto.
Qed.

Lemma encode_LL : encode (Node Leaf Leaf) = [] /\ rem (Node Leaf Leaf) = 1.
Proof. unfold encode, rem; simpl; auto. Qed.

Lemma rem_pos : forall t, t <> Leaf -> rem t >= 1.
Proof.
  induction t as [|L IHL R IHR]; intros Hne.
  - congruence.
  - unfold rem in *; simpl.
    destruct R as [|RL RR] eqn:ER.
    + destruct L; simpl; lia.
    + apply IHR. congruence.
Qed.

(** The composition lemma, phrased so the Leaf case is vacuous.
    Any fuel above [size t] works. *)
Lemma decode_node_enc : forall t fuel rest,
  t <> Leaf ->
  size t <= fuel ->
  guard rest (rem t) ->
  decode_node fuel (encode t ++ rest) = (t, rest, rem t).
Proof.
  induction t as [| L IHL R IHR]; intros fuel rest Hne Hf Hg.
  - congruence.
  - clear Hne.
    destruct fuel as [|fuel']; [ simpl in Hf; lia | ].
    assert (Hf' : size L + size R <= fuel') by (simpl in Hf; lia).
    destruct L as [|LL LR] eqn:EL.
    + (* L = Leaf *)
      destruct R as [|RL RR] eqn:ER.
      * (* L = Leaf, R = Leaf : code = [], rem = 1 *)
        destruct encode_LL as [Hc Hr]. rewrite Hc, Hr; simpl app.
        destruct rest as [|y rest']; cbn [decode_node].
        -- reflexivity.
        -- rewrite Hr in Hg; unfold guard in Hg.
           destruct y as [|[|y']]; [lia|lia|]. reflexivity.
      * (* L = Leaf, R = Node : code = 1 :: encode R, rem = rem R *)
        assert (HRsz : size (Node RL RR) <= fuel') by (simpl in Hf' |- *; lia).
        set (R' := Node RL RR) in *.
        assert (HRne : R' <> Leaf) by (unfold R'; congruence).
        destruct (encode_LN R' HRne) as [Hc Hr].
        rewrite Hc, Hr in *. cbn [app decode_node]. cbn [Nat.eqb].
        rewrite IHR with (fuel := fuel') (rest := rest);
          [ reflexivity | exact HRne | exact HRsz | exact Hg].
    + (* L = Node *)
      assert (HLsz0 : size (Node LL LR) <= fuel') by (simpl in Hf' |- *; lia).
      assert (HRsz0 : size R <= fuel') by (simpl in Hf' |- *; lia).
      set (L' := Node LL LR) in *.
      assert (HLne : L' <> Leaf) by (unfold L'; congruence).
      assert (HLrem : rem L' >= 1) by (apply rem_pos; exact HLne).
      assert (HLsz : size L' <= fuel') by exact HLsz0.
      destruct R as [|RL RR] eqn:ER.
      * (* L = Node, R = Leaf : code = 0 :: encode L, rem = rem L + 1 *)
        destruct (encode_NL L' HLne) as [Hc Hr].
        rewrite Hc, Hr in *. cbn [app decode_node].
        assert (HgL : guard rest (rem L')).
        { destruct rest as [|y rest']; unfold guard in *; [exact I| lia]. }
        rewrite IHL with (fuel := fuel') (rest := rest);
          [| exact HLne | exact HLsz | exact HgL].
        destruct rest as [|y rest'].
        -- reflexivity.
        -- assert (Hy : y <> rem L' + 1) by (unfold guard in Hg; lia).
           apply Nat.eqb_neq in Hy. rewrite Hy. reflexivity.
      * (* L = Node, R = Node *)
        assert (HRsz : size (Node RL RR) <= fuel') by exact HRsz0.
        set (R' := Node RL RR) in *.
        assert (HRne : R' <> Leaf) by (unfold R'; congruence).
        destruct (encode_NN L' R' HLne HRne) as [Hc Hr].
        rewrite Hc, Hr in *.
        cbn [app decode_node].
        rewrite <- app_assoc. simpl app.
        assert (HgL : guard ((rem L' + 1) :: (encode R' ++ rest)) (rem L')).
        { unfold guard; lia. }
        rewrite IHL with (fuel := fuel')
                         (rest := (rem L' + 1) :: (encode R' ++ rest));
          [| exact HLne | exact HLsz | exact HgL ].
        rewrite Nat.eqb_refl.
        assert (HgR : guard rest (rem R')).
        { destruct rest as [|y rest']; unfold guard in *; [exact I | lia]. }
        rewrite IHR with (fuel := fuel') (rest := rest);
          [ reflexivity | exact HRne | exact HRsz | exact HgR ].
Qed.

(* ===================================================================== *)
(** ** [valid_from] and [final_h] distribute over concatenation *)
(* ===================================================================== *)

Lemma final_h_app : forall w1 w2 h,
  final_h h (w1 ++ w2) = final_h (final_h h w1) w2.
Proof.
  induction w1 as [|x w1 IH]; intros w2 h; simpl; [reflexivity | apply IH].
Qed.

Lemma valid_from_app : forall w1 w2 h,
  valid_from h (w1 ++ w2) <-> (valid_from h w1 /\ valid_from (final_h h w1) w2).
Proof.
  induction w1 as [|x w1 IH]; intros w2 h; simpl.
  - tauto.
  - rewrite IH. tauto.
Qed.

(* ===================================================================== *)
(** ** Length / size relation *)
(* ===================================================================== *)

Lemma length_encode : forall t, t <> Leaf -> S (length (encode t)) = size t.
Proof.
  induction t as [|L IHL R IHR]; intros Hne.
  - congruence.
  - clear Hne. destruct L as [|LL LR] eqn:EL.
    + destruct R as [|RL RR] eqn:ER.
      * destruct encode_LL as [Hc _]. rewrite Hc. reflexivity.
      * remember (Node RL RR) as R' eqn:HR'.
        assert (HRne : R' <> Leaf) by (rewrite HR'; congruence).
        destruct (encode_LN R' HRne) as [Hc _].
        rewrite Hc. cbn [length size]. rewrite <- (IHR HRne). lia.
    + remember (Node LL LR) as L' eqn:HL'.
      assert (HLne : L' <> Leaf) by (rewrite HL'; congruence).
      destruct R as [|RL RR] eqn:ER.
      * destruct (encode_NL L' HLne) as [Hc _].
        rewrite Hc. cbn [length size]. rewrite <- (IHL HLne). lia.
      * remember (Node RL RR) as R' eqn:HR'.
        assert (HRne : R' <> Leaf) by (rewrite HR'; congruence).
        destruct (encode_NN L' R' HLne HRne) as [Hc _].
        rewrite Hc. cbn [length size]. rewrite length_app. cbn [length].
        rewrite <- (IHL HLne), <- (IHR HRne). lia.
Qed.

(* ===================================================================== *)
(** ** Round-trip: decode (encode t) = t  (Theorem (c), surjectivity) *)
(* ===================================================================== *)

(** Surjectivity of [decode] onto trees: every nonempty tree is decoded from
    its own codeword.  Combined with [valid_encode] below this gives that
    [decode] restricted to valid codewords is onto. *)
Theorem decode_encode : forall t, t <> Leaf -> decode (encode t) = t.
Proof.
  intros t Hne. unfold decode.
  rewrite (length_encode t Hne).
  rewrite <- (app_nil_r (encode t)).
  rewrite (decode_node_enc t (size t) []); auto.
  exact I.
Qed.

(* ===================================================================== *)
(** ** Validity of encodings *)
(* ===================================================================== *)

(** The codeword produced by [enc] satisfies the height recurrence.
    We prove a generalized statement about [valid_from] at the height that the
    surrounding context provides.  [enc_valid_from] says: building [t] from any
    starting height [h >= 1] keeps the recurrence valid and ends at height
    [h - 1 + rem t]. *)
Lemma enc_valid_from : forall t h, t <> Leaf -> 1 <= h ->
  valid_from h (encode t) /\ final_h h (encode t) = h - 1 + rem t.
Proof.
  induction t as [|L IHL R IHR]; intros h Hne Hh.
  - congruence.
  - clear Hne. destruct L as [|LL LR] eqn:EL.
    + destruct R as [|RL RR] eqn:ER.
      * destruct encode_LL as [Hc Hr]. rewrite Hc, Hr. simpl. lia.
      * set (R' := Node RL RR) in *.
        assert (HRne : R' <> Leaf) by (unfold R'; congruence).
        destruct (encode_LN R' HRne) as [Hc Hr].
        rewrite Hc, Hr.
        (* marker 1 at height h: 1 <= h ok; new height h+1-1 = h *)
        simpl valid_from. simpl final_h.
        replace (h + 1 - 1) with h by lia.
        destruct (IHR h HRne Hh) as [Hv Hf].
        split; [split; [lia | exact Hv] | rewrite Hf; lia].
    + set (L' := Node LL LR) in *.
      assert (HLne : L' <> Leaf) by (unfold L'; congruence).
      assert (HLrem : rem L' >= 1) by (apply rem_pos; exact HLne).
      destruct R as [|RL RR] eqn:ER.
      * destruct (encode_NL L' HLne) as [Hc Hr].
        rewrite Hc, Hr.
        simpl valid_from. simpl final_h.
        replace (h + 1 - 0) with (h + 1) by lia.
        destruct (IHL (h+1) HLne ltac:(lia)) as [Hv Hf].
        split.
        -- split; [lia | exact Hv].
        -- rewrite Hf. lia.
      * set (R' := Node RL RR) in *.
        assert (HRne : R' <> Leaf) by (unfold R'; congruence).
        destruct (encode_NN L' R' HLne HRne) as [Hc Hr].
        rewrite Hc, Hr.
        (* code = 0 :: encode L' ++ (rem L'+1) :: encode R' *)
        simpl valid_from. simpl final_h.
        replace (h + 1 - 0) with (h + 1) by lia.
        destruct (IHL (h+1) HLne ltac:(lia)) as [HvL HfL].
        (* after L': height = (h+1) - 1 + rem L' = h + rem L' *)
        rewrite valid_from_app. rewrite HfL.
        rewrite final_h_app. rewrite HfL.
        replace (h + 1 - 1 + rem L') with (h + rem L') by lia.
        (* now process marker (rem L' + 1) at height (h + rem L') *)
        simpl valid_from. simpl final_h.
        replace (h + rem L' + 1 - (rem L' + 1)) with h by lia.
        destruct (IHR h HRne Hh) as [HvR HfR].
        split.
        -- split; [lia | split; [exact HvL | split; [lia | exact HvR]]].
        -- rewrite HfR. lia.
Qed.

(** Corollary at the decoder's starting height [h = 1]:
    every nonempty tree encodes to a VALID codeword, and the final stack height
    equals [rem t]. *)
Theorem valid_encode : forall t, t <> Leaf -> valid (encode t).
Proof.
  intros t Hne. unfold valid.
  apply (enc_valid_from t 1 Hne (le_n 1)).
Qed.

Theorem final_h_encode : forall t, t <> Leaf -> final_h 1 (encode t) = rem t.
Proof.
  intros t Hne. destruct (enc_valid_from t 1 Hne (le_n 1)) as [_ Hf].
  rewrite Hf. lia.
Qed.

(* ===================================================================== *)
(** ** Theorem (b): injectivity of [decode] on valid codewords *)
(* ===================================================================== *)

(** [decode_node fuel] is monotone in fuel: once fuel is large enough the
    result is fixed.  We only need: extra fuel does not change a successful
    [encode]-driven parse, which we already have via [decode_node_enc]. *)

(** Existence of a decomposition for valid codewords.  A valid codeword at
    height [h >= 1] begins with the encoding of a nonempty tree [t]; the tail
    [rest] is again valid, now at height [h - 1 + rem t].  Proved by strong
    induction on the length of the codeword: the encoded prefix has positive
    length unless the tree is a single node, and in all cases [rest] is a
    strict suffix or empty, so the (informal) iteration terminates.  Here we
    only need the single-step existence. *)
Lemma valid_decompose : forall n w h,
  length w <= n -> 1 <= h -> valid_from h w ->
  exists t, t <> Leaf /\ exists rest,
    encode t ++ rest = w /\
    valid_from (h - 1 + rem t) rest /\
    length rest <= length w /\
    guard rest (rem t).
Proof.
  induction n as [|n IHn]; intros w h Hlen Hh Hv.
  - destruct w as [|x w']; simpl in Hlen; [|lia].
    exists (Node Leaf Leaf). split; [discriminate|].
    exists []. destruct encode_LL as [Hc Hr].
    rewrite Hc, Hr. simpl. repeat split; auto.
  - destruct w as [|x w'].
    + exists (Node Leaf Leaf). split; [discriminate|].
      exists []. destruct encode_LL as [Hc Hr].
      rewrite Hc, Hr. simpl. repeat split; auto.
    + simpl in Hv. destruct Hv as [Hx Hv'].
      destruct x as [|x'].
      * (* x = 0 : left child present *)
        replace (h + 1 - 0) with (h + 1) in Hv' by lia.
        assert (Hlen' : length w' <= n) by (simpl in Hlen; lia).
        destruct (IHn w' (h+1) Hlen' ltac:(lia) Hv') as
          [tL [HtLne [restL [Hcat [HvL [HleL HgL]]]]]].
        destruct restL as [|y restL'].
        -- (* no right child *)
           exists (Node tL Leaf). split; [discriminate|].
           exists []. destruct (encode_NL tL HtLne) as [Hc Hr].
           rewrite Hc, Hr. rewrite app_nil_r in Hcat. rewrite app_nil_r.
           split; [simpl; rewrite Hcat; reflexivity|].
           simpl in HvL.
           split; [replace (h - 1 + (rem tL + 1)) with (h + 1 - 1 + rem tL) by lia;
                   exact HvL |].
           split; [simpl; lia | exact I].
        -- simpl in HvL. destruct HvL as [Hy HvL'].
           (* from HgL : y > rem tL ; so y = rem tL + 1 or y > rem tL + 1 *)
           unfold guard in HgL.
           destruct (Nat.eq_dec y (rem tL + 1)) as [Hyeq | Hyneq].
           ++ (* right child present *)
              subst y.
              replace (h + 1 - 1 + rem tL + 1 - (rem tL + 1)) with h in HvL' by lia.
              assert (HlenR : length restL' <= n).
              { simpl in HleL. lia. }
              destruct (IHn restL' h HlenR Hh HvL') as
                [tR [HtRne [restR [HcatR [HvR [HleR HgR]]]]]].
              exists (Node tL tR). split; [discriminate|].
              exists restR.
              destruct (encode_NN tL tR HtLne HtRne) as [Hc Hr].
              rewrite Hc, Hr.
              split.
              { simpl. rewrite <- app_assoc. simpl.
                rewrite HcatR. f_equal. exact Hcat. }
              split; [exact HvR|].
              assert (HwL : length restL' < length w').
              { rewrite <- Hcat. rewrite length_app. simpl. lia. }
              split; [simpl; lia | exact HgR].
           ++ (* no right child: marker y > rem tL + 1 *)
              exists (Node tL Leaf). split; [discriminate|].
              exists (y :: restL').
              destruct (encode_NL tL HtLne) as [Hc Hr].
              rewrite Hc, Hr.
              split; [simpl; rewrite Hcat; reflexivity|].
              split.
              { simpl. split; [lia|].
                replace (h - 1 + (rem tL + 1)) with (h + 1 - 1 + rem tL) by lia.
                exact HvL'. }
              split.
              { simpl. rewrite <- Hcat. rewrite length_app. simpl. lia. }
              { unfold guard. lia. }
      * (* x = S x' : no left child *)
        destruct x' as [|x''].
        -- (* x = 1 : right child present *)
           replace (h + 1 - 1) with h in Hv' by lia.
           assert (Hlen' : length w' <= n) by (simpl in Hlen; lia).
           destruct (IHn w' h Hlen' Hh Hv') as
             [tR [HtRne [restR [HcatR [HvR [HleR HgR]]]]]].
           exists (Node Leaf tR). split; [discriminate|].
           exists restR. destruct (encode_LN tR HtRne) as [Hc Hr].
           rewrite Hc, Hr.
           split; [simpl; rewrite HcatR; reflexivity|].
           split; [exact HvR|].
           split; [| exact HgR].
           simpl. rewrite <- HcatR. rewrite length_app. simpl in *. lia.
        -- (* x >= 2 : childless node, rest = whole word *)
           exists (Node Leaf Leaf). split; [discriminate|].
           exists (S (S x'') :: w').
           destruct encode_LL as [Hc Hr].
           rewrite Hc, Hr. simpl app.
           split; [reflexivity|].
           split.
           { replace (h - 1 + 1) with h by lia. simpl. split; [exact Hx | exact Hv']. }
           split; [simpl; lia |].
           (* guard: S (S x'') > rem (Node Leaf Leaf) = 1 *)
           unfold guard. lia.
Qed.

(** A valid codeword (at the decoder's starting height 1) is exactly the
    encoding of its decoding: [encode] is a left inverse of [decode] on valid
    codewords. *)
Theorem encode_decode : forall w, valid w -> encode (decode w) = w.
Proof.
  intros w Hv. unfold valid in Hv.
  destruct (valid_decompose (length w) w 1 (le_n _) (le_n _) Hv) as
    [t [Htne [rest [Hcat [Hvr [Hle Hg]]]]]].
  (* rest must be empty: it is valid at height [rem t] yet [guard rest (rem t)]
     forces its head (if any) to exceed [rem t] -- contradiction. *)
  assert (Hrest : rest = []).
  { destruct rest as [|y rest']; [reflexivity|].
    simpl in Hvr. destruct Hvr as [Hy _]. unfold guard in Hg.
    replace (1 - 1 + rem t) with (rem t) in Hy by lia. lia. }
  subst rest. rewrite app_nil_r in Hcat. subst w.
  rewrite (decode_encode t Htne). reflexivity.
Qed.

(** Theorem (b): [decode] is injective on valid codewords. *)
Theorem decode_injective : forall w1 w2,
  valid w1 -> valid w2 -> decode w1 = decode w2 -> w1 = w2.
Proof.
  intros w1 w2 Hv1 Hv2 Heq.
  rewrite <- (encode_decode w1 Hv1), <- (encode_decode w2 Hv2), Heq.
  reflexivity.
Qed.

(* ===================================================================== *)
(** ** Theorem (a): [decode] returns a tree of the right size; and the
       bijection between valid codewords and (nonempty) trees *)
(* ===================================================================== *)

(** Size of the decoded tree: [size (decode w) = length w + 1]. *)
Theorem size_decode : forall w, valid w -> size (decode w) = length w + 1.
Proof.
  intros w Hv.
  assert (Hne : decode w <> Leaf).
  { intro Hd. assert (Hw := encode_decode w Hv). rewrite Hd in Hw.
    unfold encode in Hw. simpl in Hw.
    (* encode Leaf = [], so w = []; but then decode [] = Node Leaf Leaf <> Leaf *)
    subst w. unfold decode in Hd. simpl in Hd. discriminate. }
  pose proof (length_encode (decode w) Hne) as HL.
  rewrite (encode_decode w Hv) in HL. lia.
Qed.

(** The two maps are mutually inverse: [decode] is a bijection from valid
    codewords to nonempty trees, with inverse [encode]. *)
Theorem bijection_decode_encode :
  (forall t, t <> Leaf -> decode (encode t) = t) /\
  (forall w, valid w -> encode (decode w) = w) /\
  (forall t, t <> Leaf -> valid (encode t)).
Proof.
  repeat split.
  - apply decode_encode.
  - apply encode_decode.
  - apply valid_encode.
Qed.

(* ===================================================================== *)
(** ** Theorem (d): final stack height  h = n - S *)
(* ===================================================================== *)

(** Conservation law for the height recurrence on VALID input.  Validity
    guarantees [x_i <= h_{i-1}], so the truncated subtraction [h + 1 - x] is
    exact at every step and the law holds with no correction term.

    With [n = length w + 1] (the number of nodes) and [S = sumw w] (the total
    number of pops), this is exactly [final_h 1 w = n - S], the paper's
    [h = n - S]. *)
Lemma final_h_sum_valid : forall w h,
  valid_from h w -> final_h h w + sumw w = h + length w.
Proof.
  induction w as [|x w IH]; intros h Hv.
  - simpl. unfold sumw; simpl. lia.
  - simpl in Hv. destruct Hv as [Hx Hv']. simpl final_h.
    pose proof (IH (h + 1 - x) Hv') as HIH.
    assert (Hs : sumw (x :: w) = x + sumw w) by reflexivity.
    rewrite Hs. simpl length. lia.
Qed.

Theorem height_eq_n_minus_S : forall w,
  valid w -> final_h 1 w + sumw w = length w + 1.
Proof.
  intros w Hv. unfold valid in Hv.
  rewrite (final_h_sum_valid w 1 Hv). lia.
Qed.

(* ===================================================================== *)
(** ** Examples: the five trees of size 3 (n=3, codewords of length 2) *)
(* ===================================================================== *)

(** All five valid codewords of length 2, their decodings, and round-trips. *)

Example valid_codewords_n3 :
  validb [0;0] = true /\ validb [0;1] = true /\ validb [0;2] = true /\
  validb [1;0] = true /\ validb [1;1] = true.
Proof. repeat split; reflexivity. Qed.

Example invalid_codewords_n3 :
  validb [1;2] = false /\ validb [2;0] = false.
Proof. split; reflexivity. Qed.

Example decode_00 : decode [0;0] = Node (Node (Node Leaf Leaf) Leaf) Leaf.
Proof. reflexivity. Qed.

Example decode_01 : decode [0;1] = Node (Node Leaf (Node Leaf Leaf)) Leaf.
Proof. reflexivity. Qed.

Example decode_02 : decode [0;2] = Node (Node Leaf Leaf) (Node Leaf Leaf).
Proof. reflexivity. Qed.

Example decode_10 : decode [1;0] = Node Leaf (Node (Node Leaf Leaf) Leaf).
Proof. reflexivity. Qed.

Example decode_11 : decode [1;1] = Node Leaf (Node Leaf (Node Leaf Leaf)).
Proof. reflexivity. Qed.

(** The five decodings are pairwise distinct (the 5 distinct shapes). *)
Example five_distinct_shapes :
  NoDup [ decode [0;0]; decode [0;1]; decode [0;2]; decode [1;0]; decode [1;1] ].
Proof.
  repeat constructor; simpl; intuition discriminate.
Qed.

(** Round-trip on each codeword. *)
Example roundtrip_n3 :
  encode (decode [0;0]) = [0;0] /\ encode (decode [0;1]) = [0;1] /\
  encode (decode [0;2]) = [0;2] /\ encode (decode [1;0]) = [1;0] /\
  encode (decode [1;1]) = [1;1].
Proof. repeat split; reflexivity. Qed.

(** h = n - S on examples: [0;2] has S = 2, n = 3, so h = 1. *)
Example height_02 : final_h 1 [0;2] = 1 /\ sumw [0;2] = 2.
Proof. split; reflexivity. Qed.

Example height_00 : final_h 1 [0;0] = 3 /\ sumw [0;0] = 0.
Proof. split; reflexivity. Qed.
