(* -*- coq-prog-args: ("-emacs-U" "-R" "." "FingerTree" "-R" "../safe" " "-R" "../monads" " "-debug") -*- *)
Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Export Coq.Structures.OrderedType.
(* beware: exports SetoidList too *)

Set Implicit Arguments.

Module OrderedTypeFacts2(O : OrderedType).
  Import O.
  Module OFacts := OrderedTypeFacts O.
  Import OFacts.

  Definition ltb x y : bool := if lt_dec x y then true else false.
  Definition gtb x y := ltb y x.

  Lemma ltb_alt : 
     forall x y, ltb x y = match compare x y with LT _ => true | _ => false end.
   Proof.
     unfold ltb; intros; destruct (lt_dec x y); program_simpl ; elim_comp; auto.
   Qed.

  Definition geb x y := negb (ltb x y).

  Lemma geb_alt : 
     forall x y, geb x y = match compare x y with LT _ => false | _ => true end.
   Proof.
     unfold geb, negb, ltb; intros. 
     destruct (lt_dec x y); program_simpl ; elim_comp; auto.
   Qed.
End OrderedTypeFacts2.
