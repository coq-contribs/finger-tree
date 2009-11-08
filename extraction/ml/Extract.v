(* -*- coq-prog-args: ("-emacs-U" "-R" "../.." "FingerTree" "-R" "../../../../safe" "Safe" "-R" "../../../../monads" "Monad") -*- *)
Require Import FingerTree.DependentFingerTreeModule.
Require Import FingerTree.FingerTreeModule.
Require Import FingerTree.RopeModule.
Require Import Coq.Program.Program.

(* Unboxing of tuples. *) 
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive sigT => "(*)" [ " " ].

(* sumbools are bools *)
Require Import Sumbool.
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extraction Inline sumbool_of_bool.
Extraction Inline bool_of_sumbool.

(* Fine tune inlining *)
Extraction Inline eq_rect.
Unset Extraction AutoInline.

Recursive Extraction Library FingerTreeModule.
Recursive Extraction Library RopeModule.
