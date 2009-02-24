Set Implicit Arguments.

Section Reduce.
  Variable f : Type -> Type.
  Definition reducer_t := forall A B : Type, (A -> B -> B) -> (f A -> B -> B).
  Definition reducel_t := forall A B : Type, (B -> A -> B) -> (B -> f A -> B).
End Reduce.
  
Record Reduce (f : Type -> Type) : Type :=
  mkReduce {
    reducer : reducer_t f;
    reducel : reducel_t f
  }.

Definition idReduce := mkReduce (fun a b op => op) (fun a b op => op).

Require Import Coq.Lists.List.

Definition listReduce := mkReduce (fun a b op fa b => fold_right op b fa)
  (fun a b op b fa => fold_left op fa b).

Section toList.

  Variable f : Type -> Type.
  Variable r : Reduce f.
  Variable A : Type.

  Definition toList (x : f A) : list A :=
    (reducer r (cons (A:=A))) x nil.
End toList.






