(* -*- coq-prog-args: ("-emacs-U" "-R" "." "FingerTree" "-R" "../safe" " "-R" "../monads" ") -*- *)
Require Import Coq.subtac.Utils.
Require Import Coq.Lists.List.
Require Import Monoid.
Set Implicit Arguments.

Section ListMonoid.
  Variable A : Type.  

  Program Definition listMonoid := @mkMonoid (list A) nil (@app A) _ _ _. 

  Next Obligation.
  Proof.
    intros.
    red ; intros.
    rewrite app_nil_end ; reflexivity.
  Qed.

  Next Obligation.
  Proof.
    intros.
    red ; intros. 
    apply app_ass.
  Qed.

End ListMonoid.

