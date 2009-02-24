(* -*- coq-prog-args: ("-emacs-U" "-R" "../.." "FingerTree" "-R" "../../../safe" "Safe" "-R" "../../../monads" "Monad") -*- *)
Require Import FingerTree.DependentSequence.
Require Import FingerTree.FingerTree.
Require Import Coq.Program.Program.
(* Extract Constant pair "'a" "'b" => " 'a * 'b ". *)
Extract Inductive prod => "(,)" [ "(,)" ].
Extract Inductive sigT => "(,)" [ "(,)" ].
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive sumbool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extraction Inline eq_rect.
Extraction Language Haskell.
Recursive Extraction Library DependentSequence.
Recursive Extraction Library FingerTree.
