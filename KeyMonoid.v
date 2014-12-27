Require Import FingerTree.Monoid.
Require Import Coq.Program.Program.
Require Import FingerTree.OrderedType.
Require Coq.Bool.Bool.

Module KeyMonoid(O : OrderedType).
  Module OFacts := OrderedTypeFacts2 O.
  Import OFacts.

  Definition key : Type := option O.t.
  
  Definition monop (x y : key) := 
    match x, y with
      | k, None => k
      | _, k => k
    end.
  
  Program Instance key_monoid : Monoid key := 
    { mempty := None ; mappend := monop }.

    Next Obligation.
    Proof. red.
      destruct x ; reflexivity.
    Defined.
    
    Next Obligation.
    Proof. red.
      destruct x ; destruct y ; destruct z ; reflexivity.
    Defined.
    
  Definition key_ltb (x y : key) :=
    match x, y with
      | _, None => false
      | None, _ => true
      | Some x, Some y => ltb x y
    end.
  
  Import Coq.Bool.Bool.
  Definition key_ge x y := negb (key_ltb x y).
  Definition key_gt x y := key_ltb y x.

  Definition v := key.
  Definition m := key_monoid.
End KeyMonoid.
