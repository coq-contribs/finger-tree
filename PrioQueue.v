Require Import List.
Require Import Monoid.
Require Import FingerTree.Notations.
Require Import FingerTree.DependentFingerTree.
Require Import FingerTree.FingerTree.
Require Import Coq.Program.Program.
Require Import Arith.
Require FingerTree.

Require Import Coq.Structures.OrderedType.

Set Implicit Arguments.

Module PrioMonoid(O : OrderedType).
  Module OFacts := OrderedTypeFacts(O).
  Import OFacts.

  Definition ltb x y : bool := if lt_dec x y then true else false.
 
  Definition A : Type := O.t.

  Definition max (x y : A) := if ltb x y then x else y.
  Infix "maxi" := max (at level 20). 

  Lemma max_assoc : forall x y z, (x maxi y) maxi z = x maxi (y maxi z).
  Proof.
    intros.
    unfold max.
    unfold ltb.
    destruct (lt_dec x y) ; destruct (lt_dec y z) ; simpl ; program_simpl ; auto.
    destruct (lt_dec x z) ; destruct (lt_dec x y) ; simpl ; program_simpl ; auto ; try contradiction.
    order.
    destruct (lt_dec x y) ; program_simpl ; try contradiction ; auto.
    destruct (lt_dec x z).
    program_simpl ; pose (le_lt_trans n l) ; contradiction.
    auto.
  Qed.

  Inductive Priority : Type := 
  | Infinity : Priority 
  | Prio : A -> Priority.

  Definition v := Priority.

  Notation epsilon := Infinity.

  Definition op (x y : Priority) : Priority :=
    match x, y with
      | Infinity, x => x
      | x, Infinity => x
      | Prio x, Prio y => Prio (max x y)
    end.

  Definition prio_ltb (x y : Priority) : bool := 
    match x, y with
      | Infinity, x => true
      | x, Infinity => false
      | Prio x, Prio y => ltb x y
    end.

  Program Instance priomon : Monoid v :=
    { mempty := Infinity ; mappend := op }.

    Next Obligation.
    Proof. red.
      unfold op ; intros.
      destruct x ; reflexivity.
    Defined.
    
    Next Obligation.
    Proof. red.
      destruct x ; simpl ; auto.
      destruct y ; simpl ; auto.
      destruct z ; simpl ; auto.
      rewrite max_assoc.
      auto.
    Defined.

End PrioMonoid.

Module PrioQueue(A : OrderedType).
  Module PrioM := PrioMonoid A.
  Import PrioM.

  Definition A : Type := A.t.
  
  Instance prio_measure : Measured Priority A :=
    { measure := Prio }.

  Definition PQueue := FingerTree prio_measure.

  Import FingerTree.

  Program Definition extractMax (x : PQueue) : option A * PQueue := 
      if is_empty_dec x then (None, x)
      else 
        match split (prio_ltb (tree_measure x)) epsilon x with
          | mkSplit l x r => 
            (Some x, cat l r)
        end.

  Definition add (x : A) (q : PQueue) : PQueue := cons x q.

End PrioQueue.



