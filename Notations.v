(* begin hide *)
Require Import FingerTree.Reduce.
Require Import Coq.Program.Utils.
Set Implicit Arguments.
(* end hide *)

Notation "'λ'  x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity).

Notation "'Π'  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.

Notation " { ( x , y , z ) : A | P } " := { t : A | 
  let (u, z) := t in let (x, y) := u in P } (x ident, y ident, z ident, at level 10).
