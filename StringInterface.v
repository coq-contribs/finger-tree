Set Implicit Arguments.
Require Import Coq.Program.Program.
Require Import Coq.Numbers.Natural.Abstract.NBase.
Require Import Coq.Numbers.Natural.Abstract.NSub.
Require Import Coq.Numbers.Natural.Abstract.NAxioms.

Module NatPack(Export NAxioms : NAxiomsMiniSig').

  Module Props := NBaseProp NAxioms.
  Export Props.

  Definition below i := { x : t | x < i }.
  Definition upto i := { x : t | x <= i }.

End NatPack.

Module Type String.
  Declare Module NAxioms : NAxiomsMiniSig'.

  Module Nats := NatPack NAxioms.
  Import Nats.

  Parameter char : Type.

  Parameter t : Type.

  Parameter length : t -> NAxioms.t.

  Parameter sub : forall (str : t) (offset : below (length str))
    (len : below (length str - `offset)), t.

  Arguments sub : clear implicits.

  Parameter get : forall (str : t) (idx : below (length str)), char.

  Arguments get : clear implicits.

End String.

Module SubString(S : String).
  Import S.
  Import Nats.
  Import Props.

  Module Import NSub.
   Include NSubProp NAxioms.
  End NSub.

  Record substring : Type := mkSubStr
    { string : S.t;
      offset : below (length string);
      length : upto (length string - `offset) }.

  Program Definition new (s : {s:S.t | S.length s > 0}) :=
    @mkSubStr s 0 (S.length s).

  Next Obligation.
  Proof.
    rewrite sub_0_r.
    apply le_refl.
  Qed.

End SubString.
