(* ExtractWhile.v
   Extract the *executable* CWhile reconstructor to OCaml.

   ReconstructExec gives a fuel-driven interpreter `ceval_fun` proved sound
   against the big-step semantics (`ceval_fun_sound`), and a self-contained
   driver `reconstruct_exec` proved correct for every tree
   (`reconstruct_exec_correct`): laying out the initial heap, running the genuine
   `CWhile` program `iRun`, and reading back the 2N output cells builds exactly
   the tree's `setTree` parent array.  Here we extract that driver -- the
   deep-embedded program term `iRun`, the interpreter `ceval_fun`, the heap
   layout `init_state`, and the reader `read_arr` -- to native OCaml, so the
   *certified* imperative program can actually be run.

   Build (after `make`):
       rocq c ExtractWhile.v      (* writes reconstruct_while.ml / .mli *)
   Rocq Prover 9.1.0. *)

From Stdlib Require Import Extraction.
From Stdlib Require Import List Arith Bool.
Require Import ImpHoare.
Require Import ReconstructWhile.
Require Import ReconstructExec.

Extraction Language OCaml.

(* Map Coq's unary nat onto OCaml's native int (as in Extract.v). *)
Extract Inductive nat => "int" [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n -> if n=0 then zero () else succ (n-1))".
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "( * )" [ "(,)" ].
Extract Inductive option => "option" [ "Some" "None" ].

Extract Inlined Constant Nat.eqb => "(=)".
Extract Inlined Constant Nat.ltb => "(<)".
Extract Inlined Constant Nat.leb => "(<=)".
Extract Inlined Constant Nat.add => "(+)".
Extract Inlined Constant Nat.mul => "( * )".
Extract Inlined Constant Nat.sub => "(fun a b -> max 0 (a - b))".
Extract Inlined Constant length  => "List.length".
Extract Inlined Constant app     => "List.append".
Extract Inlined Constant andb    => "(&&)".

(* The executable CWhile reconstructor and the pieces to drive / read it. *)
Extraction "reconstruct_while.ml"
  reconstruct_exec read_arr ceval_fun iRun init_state.
