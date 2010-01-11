(* begin hide *)
Require Import FingerTree.Modules.
Require Import FingerTree.StringInterface.
Require Import FingerTree.FingerTreeModule.
Require Import Coq.Program.Program.

Set Implicit Arguments.

Module Type ROPE.

  Declare Module Str : String.
  Import Str.Nats.

  Definition string := Str.t.
  Definition N := Str.NAxioms.t.

  Parameter t : Type.
  
  Parameter empty : t.
  Parameter add : { s : string | Str.length s > 0 } -> t -> t.
  Parameter length : t -> N.
  Parameter get : forall rope : t, below (length rope) -> Str.char.
  Parameter sub : forall rope : t, 
    { n : N | n < length rope } -> { n' : N | n' < length rope } -> t.
End ROPE.

Require Import Coq.Numbers.Natural.Abstract.NBase.
Require Import Coq.Numbers.Natural.Abstract.NAxioms.
Require Import Coq.Numbers.Natural.Abstract.NSub.
Require Import Coq.Numbers.Natural.Abstract.NProperties.
Require Import Coq.Numbers.Natural.Abstract.NDefOps.

Require Import Coq.Numbers.NatInt.NZAxioms.
    
Module Rope(Export NAxioms : NAxiomsSig' with 
  Definition t := nat
    with Definition eq := @eq nat)
  (S : String with Module NAxioms := NAxioms) : ROPE.

  Module Str := S.
  Import S.
  Module Sub := SubString S.
  Import Sub.
  Module Props := NPropFunct NAxioms.
  Export Props.
  Import S.Nats.
  Import S.Nats.Props.
  Module Ops :=  NdefOpsPropFunct NAxioms.

  Definition string := Str.t.
  Definition N := NAxioms.t.
  
  Lemma not_below_0 : below 0 -> False.
  Proof.
    intros. destruct X.
    apply (nlt_0_r _ l).
  Qed.

  Ltac mysimpl := simpl ; intros ; destruct_pairs ; simpl in * ; try subst ; 
    try (solve [ red ; intros ; discriminate ]) ; auto with *.  
  
  Obligation Tactic := unfold below in * ; intros ; mysimpl.

  Hint Resolve not_below_0 : ft.
  Hint Unfold below.

  Module PlusMonoid <: Monoid.

    Definition m := N.
    Definition mempty := zero.
    Definition mappend := add.

    Definition monoid_id_l := add_0_l.
    Definition monoid_id_r := add_0_r.
    Lemma monoid_assoc : Monoid.monoid_assoc_t _ add.
    Proof.
      red ; intros. symmetry.
      apply add_assoc.
    Qed.

  End PlusMonoid.

  Module RopeMeasure <: Measured.

    Definition A : Type := substring.

    Module Mon := PlusMonoid.
    Program Definition measure x : N := length x.

  End RopeMeasure.

  Module RopeFT := FingerTree PlusMonoid RopeMeasure.
  
  Import RopeMeasure.
  Import RopeFT.
  
  Notation rope := finger_tree.

  Definition t := finger_tree.

  Definition length := tree_measure.

  Definition empty := empty.

  Definition add (s : S.t | S.length s > 0) (r : rope) : rope := 
    cons (new s) r.

  Hypothesis sub : forall (r : rope) (i : below (length r)) (j : below (length r)), rope.

  Program Definition get (r : rope) (i : below (length r)) : char :=
    let 'rs :| rt := r in
    let '(ls, str) := FT.get_tree (fun x => Ops.ltb i x) rt tt 0 in
    let 'mkSubStr s start len := str in
      S.get s (start + (i - ls)).

  Ltac forward t := 
    let H := fresh "H" in assert(H:=t).

  Next Obligation.
  Proof.
    intros.
    destruct exist i Hi.
    forward (lt_lt_0 _ _ Hi).
    simpl in *.
    red ; intros.
    forward (FT.isEmpty_epsilon _ H0).
    rewrite H1 in H.
    apply (nlt_0_r _ H).
  Qed.

  Next Obligation.
  Proof with trivial.
    intros.
    destruct exist i Hi.
    forward (lt_lt_0 _ _ Hi).
    simpl in *.
    split. apply Ops.ltb_0.
    unfold PlusMonoid.mappend. rewrite add_0_l.
    rewrite Ops.ltb_lt. assumption.
  Qed.

  Next Obligation.
  Proof with simpl in *.
    intros.
    destruct exist i Hi...
    destruct exist start Hstart.
    destruct exist len Hlen...
    destruct_call FT.get_tree.
    destruct x... injection Heq_anonymous. intros.
    clear Heq_anonymous. subst.
    unfold PlusMonoid.mappend in *. unfold measure in y. simpl in y.
    destruct y. rewrite Ops.ltb_lt in *.
    assert(start + len <= S.length s). red. admit.
    assert(i - v0 < len). admit.
    admit.
  Qed.

  Definition app := cat.

End Rope.
