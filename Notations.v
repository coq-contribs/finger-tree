(* begin hide *)
Require Import FingerTree.Reduce.
Require Import Coq.Program.Utils.
Set Implicit Arguments.
(* end hide *)

Notation " { ( x , y , z ) : A | P } " := { t : A | 
  let (u, z) := t in let (x, y) := u in P } (x ident, y ident, z ident, at level 10).
