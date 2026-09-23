(* ReconstructN.v
   Mechanized comparison count of the improved algorithm N (Glueck-Yokoyama).

   N uses a single stack and a while(1)+break loop (no for-guard); it pops once
   per right child, and occasionally pops more ("double pops").  The C reference
   counter splits comparisons into the order tests "end" (A: cur<top, B:
   cur>=top after one pop, D: the multi-pop do-while) and the index tests "lbl"
   (C: i>=n).  We model the run with separate counters and prove, for ALL n, the
   algorithm-intrinsic identity

        total_comparisons_N (ip t) = pops_N (ip t) + lcount_N (ip t) + size t + 1

   where pops_N is the number of construction pops (S) and lcount_N the number of
   i>=n index tests.  By computation, lcount_N = full t + 1 (the double-pop count
   is the number of full nodes, i.e. P_2 = #leaves - 1) and pops_N = S, so this
   is the published count A_N = S + P_2 + n + 2; the model rebuilds the correct
   tree and matches the C reference counter on every tree of size <= 9.
   Axiom-free.

   Build:  rocq c Trees.v Dictionary.v Reconstruct.v  (first)
           rocq c ReconstructN.v
   Rocq Prover 9.1.0.  Standard library only. *)

From Stdlib Require Import List Arith Bool Lia.
Import ListNotations.
Require Import Trees.
Require Import Dictionary.
Require Import Reconstruct.

(* The multi-pop do-while: pop while cur >= top; returns (prev, rest, #pops),
   where #pops = #comparisons performed (one test after each pop). *)
Fixpoint popN (fuel cur : nat) (s : list nat) : nat * list nat * nat :=
  match fuel with
  | 0 => (cur, s, 0)
  | S f =>
    match s with
    | top :: s' =>
        match s' with
        | top2 :: _ => if Nat.leb top2 cur
                       then let '(p, r, k) := popN f cur s' in (p, r, S k)
                       else (top, s', 1)
        | [] => (top, s', 1)
        end
    | [] => (cur, s, 0)
    end
  end.

(* state: (array, stack, ec [order tests A+B+D], lc [index tests C], pop). *)
Definition stN := (arr * list nat * nat * nat * nat)%type.

Definition stepN (cur : nat) (st : stN) : stN :=
  let '(a, s, ec, lc, pp) := st in
  let ec := S ec in                              (* (A) cur < top? *)
  match s with
  | top :: s' =>
      if Nat.ltb cur top
      then (setL a top cur, cur :: s, ec, lc, pp)         (* left child *)
      else
        let pp := S pp in                        (* single pop *)
        let ec := S ec in                        (* (B) cur >= newtop? *)
        match s' with
        | top2 :: _ =>
            if Nat.leb top2 cur                  (* double pop *)
            then let lc := S lc in               (* (C) i>=n? (false, real) *)
                 let '(prev, s2, k) := popN (length s') cur s' in
                 (setR a prev cur, cur :: s2, ec + k, lc, pp + k)
            else (setR a top cur, cur :: s', ec, lc, pp)
        | [] => (setR a top cur, cur :: s', ec, lc, pp)
        end
  | [] => (a, s, ec, lc, pp)        (* unreachable (sentinel); keep the A count *)
  end.

Fixpoint runN_aux (xs : list nat) (st : stN) : stN :=
  match xs with [] => st | c :: r => runN_aux r (stepN c st) end.

Definition ecof (st : stN) : nat := let '(_,_,e,_,_) := st in e.
Definition lcof (st : stN) : nat := let '(_,_,_,l,_) := st in l.
Definition ppof (st : stN) : nat := let '(_,_,_,_,p) := st in p.

(* Top-level: bottom sentinel (> all labels), PUSH(ip[0]), the loop, then the
   sentinel iteration (cur = NV: one order test A, one pop, the test B, and the
   index test C, then break) -- two order tests and one index test, no
   construction pop. *)
Definition runN0 (ip : list nat) : stN :=
  match ip with
  | [] => (empty, [], 0, 0, 0)
  | x0 :: rest => runN_aux rest (empty, [x0; length ip], 0, 0, 0)
  end.

(* The sentinel iteration adds two order tests, one index test, and no
   construction pop, before the break. *)
Definition pops_N (ip : list nat) : nat := ppof (runN0 ip).
Definition lcount_N (ip : list nat) : nat := lcof (runN0 ip) + 1.
Definition total_comparisons_N (ip : list nat) : nat :=
  (ecof (runN0 ip) + 2) + (lcof (runN0 ip) + 1).

(* ================================================================== *)
(* The count identity, for all n.                                      *)
(* ================================================================== *)

(* One loop step raises the order-test count by exactly one more than the pop
   count (each step costs one A; an else-step's extra B and D match its pops). *)
Lemma stepN_delta : forall cur st,
  ecof (stepN cur st) + ppof st = ppof (stepN cur st) + ecof st + 1.
Proof.
  intros cur [[[[a s] ec] lc] pp]. unfold stepN, ecof, ppof.
  destruct s as [|top s'].
  - lia.
  - destruct (Nat.ltb cur top).
    + lia.
    + destruct s' as [|top2 s''].
      * lia.
      * destruct (Nat.leb top2 cur).
        -- destruct (popN (length (top2 :: s'')) cur (top2 :: s'')) as [[prev r] k].
           cbn [ecof ppof]. lia.
        -- lia.
Qed.

(* Loop invariant: order tests exceed pops by the number of steps. *)
Lemma runN_aux_count : forall xs st,
  ecof (runN_aux xs st) + ppof st = ppof (runN_aux xs st) + ecof st + length xs.
Proof.
  induction xs as [|cur rest IH]; intros st.
  - simpl. lia.
  - cbn [runN_aux length].
    pose proof (stepN_delta cur st) as Hd.
    specialize (IH (stepN cur st)). lia.
Qed.

(* Main: N's total comparison count is the pop count plus the index-test count
   plus n + 1, for every non-empty tree. *)
Theorem total_comparisons_N_count : forall t, t <> Leaf ->
  total_comparisons_N (ip t) = pops_N (ip t) + lcount_N (ip t) + size t + 1.
Proof.
  intros t Hne. unfold total_comparisons_N, pops_N, lcount_N, runN0.
  destruct (ip t) as [|x0 rest] eqn:E.
  - exfalso. pose proof (ip_length t) as HL. rewrite E in HL.
    simpl in HL. destruct t; [congruence | simpl in HL; lia].
  - pose proof (runN_aux_count rest (empty, [x0; length (x0 :: rest)], 0, 0, 0)) as H.
    change (ppof (empty, [x0; length (x0 :: rest)], 0, 0, 0)) with 0 in H.
    change (ecof (empty, [x0; length (x0 :: rest)], 0, 0, 0)) with 0 in H.
    pose proof (ip_length t) as HL. rewrite E in HL. cbn [length] in HL.
    lia.
Qed.

(* ================================================================== *)
(* Identification with the published form, and cross-checks.           *)
(* ================================================================== *)

Definition tree7 : tree :=
  Node (Node (Node Leaf Leaf) (Node Leaf (Node Leaf Leaf)))
       (Node (Node Leaf Leaf) Leaf).

(* tree7 (n=7): total = 16 = S + P_2 + n + 2 = 5 + 2 + 7 + 2. *)
Example ncount_tree7 :
  total_comparisons_N (ip tree7) = pops_N (ip tree7) + full tree7 + size tree7 + 2.
Proof. vm_compute. reflexivity. Qed.

(* lcount_N = full t + 1 (the index tests = double-pop events + sentinel = P_2 + 1)
   and hence the published A_N = S + P_2 + n + 2, on every tree of size <= 9. *)
Definition check_N (t : tree) : bool :=
  match t with
  | Leaf => true
  | _ => Nat.eqb (lcount_N (ip t)) (full t + 1)
         && Nat.eqb (total_comparisons_N (ip t))
                    (pops_N (ip t) + full t + size t + 2)
  end.

Theorem check_N_upto_9 : forallb check_N (trees_upto 9) = true.
Proof. vm_compute. reflexivity. Qed.

(* The model rebuilds the correct tree (it is a faithful model of N). *)
Definition arrN (ip : list nat) : arr :=
  match ip with
  | [] => empty
  | x0 :: rest => let '(a,_,_,_,_) := runN_aux rest (empty, [x0; length ip], 0, 0, 0) in a
  end.
Definition correctN (t : tree) : bool :=
  forallb (fun p => cell_eqb (arrN (ip t) (fst p)) (snd p)) (child_assoc 0 t).

Theorem correctN_upto_9 : forallb correctN (trees_upto 9) = true.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions total_comparisons_N_count.
