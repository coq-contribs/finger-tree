(* begin hide *)
Require Import FingerTree.Modules.
Require Import FingerTree.StringInterface.
Require Import FingerTree.FingerTreeModule.
Require Import Coq.Program.Program.

Set Implicit Arguments.

Module Type ROPE.

  Declare Module Str : String.
  Import Str.Nats.

  Open Scope NatScope.

  Definition string := Str.t.

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

Require Import Coq.Numbers.NatInt.NZAxioms.
    
Module Rope(NZA : NZAxiomsSig with Definition NZ := nat with
  Definition NZeq := @eq nat)
  (S : String with Module NAxioms.NZOrdAxiomsMod.NZAxiomsMod := NZA) : ROPE.

  Module Str := S.
  Import S.
  Module Sub := SubString S.
  Import Sub.
  Module Props := NBasePropFunct NAxioms.
  Export Props.
  Import S.Nats.
  Import S.Nats.Props.

  Open Scope NatScope.

  Definition string := Str.t.
  Definition nat := N.
  
  Lemma not_below_0 : below 0 -> False.
  Proof.
    intros.
    inversion X.
    apply (NSub.NMulOrderPropMod.NAddOrderPropMod.NOrderPropMod.nlt_0_r _ H).
  Qed.

  Ltac mysimpl := simpl ; intros ; destruct_pairs ; simpl in * ; try subst ; 
    try (solve [ red ; intros ; discriminate ]) ; auto with *.  
  
  Obligation Tactic := unfold below in * ; intros ; mysimpl.

  Hint Resolve not_below_0 : ft.
  Hint Unfold below.

  Module PlusMonoid <: Monoid.

    Definition m := N.
    Definition mempty := N0.
    Definition mappend := add.

    Definition monoid_id_l := NZadd_0_l.
    Definition monoid_id_r := NZadd_0_r.
    Lemma monoid_assoc : Monoid.monoid_assoc_t _ NZadd.
    Proof.
      red ; intros.
      symmetry.
      apply NZadd_assoc.
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

  Hypothesis less_than : forall x y : N, bool.

  Program Definition get (r : rope) (i : below (length r)) : char :=
    let 'rs :| rt := r in
    let '(ls, str) := FT.get_tree (fun x => less_than i x) rt tt 0 in
    let 'mkSubStr s start len := str in
      S.get s (start + (i - ls)).

  Ltac forward t := 
    let H := fresh "H" in assert(H:=t).

  (* Works, but Naturals has changed once more ... *)
  Admit Obligations.
  (*
  Next Obligation.
  Proof.
    intros.
    destruct exist i Hi.
    forward (lt_positive _ _ Hi).
    simpl in *.
    red ; intros.
    forward (FT.isEmpty_epsilon _ H0).
    rewrite H1 in H.
    apply (lt_0 _ H).
  Qed.

  Next Obligation.
  Proof with trivial.
    intros.
    destruct exist i Hi.
    forward (lt_positive _ _ Hi).
    simpl in *.
    split.
    apply not_true_is_false.
    red ; intros.
    pose (lt_0 i).
    rewrite H0 in n ; destruct n ; constructor.
    rewrite plus_0_l.
    destruct Hi...
  Qed.

  Next Obligation.
  Proof with simpl in *.
    intros.
    destruct exist i Hi...
    destruct exist start Hstart.
    destruct exist len Hlen...
    destruct_call FT.get_tree.
    destruct x...
    autoinjection...
    subst a.
    destruct y...
    unfold measure in H0...
    assert(start + len <= S.length s).
    unfold PlusMonoid.mappend in H0.
    rewrite <- lt_S in Hlen.
    forward (plus_lt_compat_r _ _ start Hlen).
    rewrite plus_S_l in H1.
    rewrite minus_plus in H1.
    rewrite plus_comm in H1.
    apply -> lt_S.
    assumption.
    subst l.
    rewrite lt_le_S_l in Hstart.
    apply le_S_l_le.
    assumption.

    cut(i - v0 < len) ; intros.
    apply lt_le_trans with (start + len) ; auto.
    apply <- (plus_lt_cancel_l start).
    assumption.
    
    unfold PlusMonoid.mappend in H0.
    apply -> (plus_lt_cancel_r v0).
    rewrite plus_comm in H0.
    rewrite minus_plus.
    rewrite <- eq_true_unfold_neg in H.
    rewrite <- (not_lt i v0).
    assumption.
    rewrite (eq_true_unfold_pos).
    auto.
  Qed.
  *)

  Definition app := cat.

End Rope.

