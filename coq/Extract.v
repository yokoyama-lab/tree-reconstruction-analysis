(* Extract.v
   Extract the verified reconstructor to OCaml.

   run (ip t) is proved equal to setTree 0 t empty (ReconstructFull.run_eq_setTree)
   and correct against the tree's child relation, for all n.  Here we extract the
   functional model itself to native OCaml, so the *certified* code can be run --
   and the proved identity run = setTree exercised -- on inputs far larger than
   vm_compute reaches inside the prover.

   Build:  rocq c Trees.v Dictionary.v Reconstruct.v ReconstructRight.v
                  ReconstructInvariant.v ReconstructFull.v   (first)
           rocq c Extract.v      (* writes reconstruct.ml / reconstruct.mli *)
   Rocq Prover 9.1.0. *)

From Stdlib Require Import Extraction.
From Stdlib Require Import List Arith.
Require Import Trees.
Require Import Dictionary.
Require Import Reconstruct.
Require Import ReconstructRight.

Extraction Language OCaml.

(* Map Coq's unary nat onto OCaml's native int. *)
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
Extract Inlined Constant length => "List.length".
Extract Inlined Constant app => "List.append".

(* The certified reconstructor and its structural spec, plus helpers to build
   trees and read off the node array in OCaml. *)
Extraction "reconstruct.ml"
  run ip size setTree empty child_assoc.
