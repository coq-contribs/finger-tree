(* -*- coq-prog-args: ("-emacs-U" "-R" "." "FingerTree" "-R" "../safe" " "-R" "../monads" " "-debug"); compile-command: "./makedoc.sh" -*- *)
(* begin hide *)
Require Import Monoid.
(* end hide *)
(** Suppose we want to define the monoid $(0, +)$ on naturals. We have to apply the [mkMonoid]
   constructor to [0], [plus] and proofs of identity and associativity. Fortunately, those can be filled
   automatically by Coq.
   The $\coqdockw{Program}$ modifier simply indicates we want to call the Russell type-checker,
   the '@' symbol is used to bypass the implicit argument mechanism and the underscores are 
   holes which will be automatically turned into obligations by the type-checker.
   *)  

Program Definition plus_monoid := @mkMonoid nat 0 plus _ _ _.
