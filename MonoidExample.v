(* -*- coq-prog-args: ("-emacs-U" "-R" "../monads" "); compile-command: "./makedoc.sh" -*- *)
(* begin hide *)
Set Implicit Arguments.
Unset Strict Implicit.

Require Export MyPrelude.
(* end hide *)
(** printing epsilon $\varepsilon$ *)(** printing cdot $\cdot$ *)
(** We first introduce the monoid laws we just described. 
   We will use the section mechanism of Coq extensively in the following. 
   Sections permit to write a bunch of definitions which are parameterized by some variables,
   e.g. for types and operations.
   When closing a section, every definition inside it is quantified over the variables it used.
   *)

Section Monoid_Laws.

  (** The carrier [m] type may be any type. *)

  Variable m : Type.

  (** The identity element [mempty] and the operation [mappend]. *)

  Variables (mempty : m) (mappend : m -> m -> m).

  (** We define fancy notations for the element and operation. *)

  Notation epsilon := mempty.
  Infix "cdot" := mappend (right associativity, at level 20).

  (** We now state the properties. *)

  Definition monoid_id_l_t : Prop := forall x, epsilon cdot x = x.
  Definition monoid_id_r_t := forall x, x cdot epsilon = x.
  Definition monoid_assoc_t := forall x y z, (x cdot y) cdot z = x cdot y cdot z.
End Monoid_Laws.

(** Every variable in [Monoid_Laws] has been discharged by now, so we must apply each definition 
   to particular [mempty] and [mappend] objects.
   We can finally define the dependent record which represents monoids on [m]:
   %\label{def:monoid}%
*)

Record monoid (m : Type) : Type := mkMonoid 
  { mempty : m ; mappend : m -> m -> m
  ; monoid_id_l : monoid_id_l_t mempty mappend
  ; monoid_id_r : monoid_id_r_t mempty mappend
  ; monoid_assoc : monoid_assoc_t mappend }.

(* begin hide *)
(* Notation " x 'cdot' y " := (monoid_append _ x y) (right associativity, at level 20). *)
(* Notation " 'varepsilon' " := (monoid_empty _) (no associativity, at level 20). *)
Hint Unfold  monoid_id_l_t  monoid_id_r_t  monoid_assoc_t.

Require Import Plus.

Ltac monoid_tac_in H := repeat rewrite monoid_id_r in H ; repeat rewrite monoid_id_l in H ; repeat rewrite monoid_assoc in H.

Ltac monoid_tac := repeat rewrite monoid_id_r ; repeat rewrite monoid_id_l ; repeat rewrite monoid_assoc.
(* end hide *)
