(* begin hide *)
Require Export Coq.Program.Basics Program Notations.
(* end hide *)
(** printing measure %\coqmethodref{FingerTree.Monoid.measure}{measure}% *)(** printing lparr $\coqdoublebar$ *)(** printing rparr $\coqdoublebar$ *)
(** *** Monoïdes
   %\label{sec:fts:monoids}%
   On va implémenter la classe des monoïdes en %\Coq% par un enregistrement 
   (ou %\eng{record}%) paramétré. On définit tout d'abord les lois du monoïde.
   On va utiliser le mécanisme de %\emph{sections}% de %\Coq% intensivement dans la suite.
   Les sections permettent d'écrire un ensemble de définitions paramétrées par un ensemble de variables 
   de section (généralement des types, mais parfois aussi des opérations). Lorsqu'on clôt une section, 
   toutes les définitions à l'intérieur de celle-ci sont automatiquement généralisées par rapport 
   aux variables de section qu'elles utilisent. *)

Global Generalizable Variables m v A.

Section Monoid_Laws.

  (** Le support du monoïde [m] peut être n'importe quel type. *)

  Variable m : Type.

  (** On suppose donnés l'élément neutre [mempty] et l'opération du monoïde [mappend]. *)

  Variables (mempty : m) (mappend : m -> m -> m).

  (** On peut définir des notations appropriées pour ces deux variables. *)

  Notation "'ε'" := mempty.
  Infix "∙" := mappend (right associativity, at level 20).

  (** Finalement, on définit les trois lois du monoïde. *)

  Definition monoid_id_l_t : Prop := forall x, ε ∙ x = x.
  Definition monoid_id_r_t := forall x, x ∙ ε = x.
  Definition monoid_assoc_t := forall x y z, (x ∙ y) ∙ z = x ∙ y ∙ z.

End Monoid_Laws.

(** Toutes les variables dans la section [Monoid_Laws] sont maintenant %\emph{déchargées}%,
   on doit donc appliquer chaque définition de loi à des objets [mempty] et [mappend] particuliers.
   On définit la classe de type représentant un monoïde sur un type [m]:
   %\label{def:monoid}%
*)

Class Monoid (m : Type) : Type := {
  mempty : m ; 
  mappend : m -> m -> m ;
  monoid_id_l : monoid_id_l_t m mempty mappend ;
  monoid_id_r : monoid_id_r_t m mempty mappend ;
  monoid_assoc : monoid_assoc_t m mappend }.

Infix "∙" := mappend (right associativity, at level 20).
Notation ε := mempty.
(* begin hide *)
Hint Unfold monoid_id_l_t monoid_id_r_t monoid_assoc_t.

Require Import Plus.

Lemma monoid_id_left `{Monoid m} : Π x, ε ∙ x = x.
Proof. intros. apply (monoid_id_l x). Qed.

Lemma monoid_id_right `{Monoid m} : Π x, x ∙ ε = x.
Proof. intros. apply (monoid_id_r x). Qed.

Lemma monoid_append_ass `{Monoid m} : Π x y z, (x ∙ y) ∙ z = x ∙ (y ∙ z).
Proof. intros. apply (monoid_assoc x). Qed.

Ltac monoid_tac_in H := repeat rewrite @monoid_id_right in H ; repeat rewrite @monoid_id_left in H ; repeat rewrite @monoid_append_ass in H.

Hint Rewrite @monoid_id_right @monoid_id_left @monoid_append_ass : monoid.

Ltac monoid_tac := repeat rewrite @monoid_id_right ; repeat rewrite @monoid_id_left ; repeat rewrite @monoid_append_ass.
(* end hide *)

(** On peut maintenant créer des instances de [Monoid]. Par exemple on peut déclarer
   le monoïde %$(\nil, \app)$% sur les listes. 
   On peut utiliser %\Program% pour créer des monoïdes en ne mentionnant explicitement 
   que les parties informatives et en faisant de chaque preuve    
   une obligation. Celles-ci peuvent être résolues automatiquement. *)

Require Import Coq.Lists.List.

Program Instance list_monoid A : Monoid (list A) :=
  { mempty := [] ; mappend:= @app A }.

  Solve Obligations using red ; auto with datatypes.

(** On définit aussi la classe [Measured] tout comme en %\Haskell% qui va
   permettre de faire référence indifférement à la mesure d'un doigt, un nœud ou
   un %\FT% à l'aide de la fonction surchargée %\coqprojection{FingerTree.Monoid.measure}{measure}%. *)

Class Measured v {m : Monoid v} (A : Type) := { measure : A -> v }.

(** Par défaut, tout les arguments n'apparaissant pas à gauche de la flèche
   sont implicites. On veut ici que seule l'implémentation du monoïde le soit. *)

Implicit Arguments Measured [[m]].

(* begin hide *)
Notation " 'lparr' x 'rparr' " := (measure x) (x ident, no associativity).
(* end hide *)
(** On peut utiliser la notation %\eng{mixfix}% [lparr _ rparr] pour se référer à
   la fonction [measure]. D'ores et déjà on peut déclarer une instance paramétrique pour prendre
   la mesure d'un objet de type [option A] si [A] est mesurable *)

Instance option_measure `(Measured v A) : Measured v (option A) := 
  { measure x := match x with Some x => lparr x rparr | None => ε end }.
