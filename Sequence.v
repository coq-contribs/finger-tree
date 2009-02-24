Require Import FingerTree.Monoid.
Require Import FingerTree.Notations.
Require Import FingerTree.DependentFingerTree.
Require Import FingerTree.FingerTree.
Require Import Coq.Program.Program.
Require Import Arith.

Set Implicit Arguments.

Program Instance SizeMonoid : Monoid nat := 
  { mempty := 0 ; mappend := plus }.

  Next Obligation. red. auto with arith. Qed.

Section Sequence.
  Variable A : Type.

  Instance trivial_measure : Measured (m:=SizeMonoid) nat A :=
    { measure x := 1 }.

  Definition Seq := FingerTree trivial_measure.

  Definition length (x : Seq) := let (s, seq) := x in s.
  
  Definition lt (x y : nat) := leb (S x) y.

  Definition splitAt (i : nat) (x : Seq) := 
    split_with (fun x => lt i x) x.
    
  Program Definition nth (x : Seq) (i : nat | i < length x) : A := 
    let 'existT s t := x in
    let 'mkTreeSplit _ _ x _ _ := split_tree (lt i) 0 t in x.
    
  Require Import Omega.

  Next Obligation.
  Proof.
    unfold length in * ; simpl in *.
    assert(s > 0).
    omega.
    
    destruct t ; simpl in * ; auto.
    inversion H.
    apply (not_isEmpty_Deep l t r).
  Qed.

End Sequence.


      
