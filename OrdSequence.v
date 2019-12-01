(* begin hide *)
Require Import FingerTree.Monoid.
Require Import FingerTree.Notations.
Require Import Coq.Program.Program.
Require Import FingerTree.OrderedType.
Require Import FingerTree.FingerTree.
Require Import FingerTree.KeyMonoid.
Require Import Omega.
Require DependentFingerTree.

Require Import Arith.

Set Implicit Arguments.
(* end hide *)

(** ** Séquences ordonnées
   %\label{fts:inst:seqord}%
   
   Un exemple d'utilisation de l'interface simplement typée est la construction de séquences ordonnées
   suivante. L'idée principale est d'utiliser comme mesure d'un élément l'élément lui-même et faire que le monoïde
   calcule l'élément le plus à droite de l'arbre. Alors, si les opérations maintiennent l'invariant que 
   la séquence des éléments de l'arbre est ordonnée on a une séquence ordonnée ou l'élément maximal peut
   être récupéré en temps constant.
   *)

Module OrdSequence(AO : OrderedType).
  
  (** On utilise des modules plutôt que des sections puisque cela nous 
     permet d'instancier à %\eng{compile-time}% ce qui est exactement ce dont
     nous avons besoin ici. Le système de modules de %\Coq% est un surensemble de celui 
     d'%\Ocaml% et l'extraction supporte la traduction de l'un à l'autre. 
     On suppose donnée une implémentation d'un type ordonné [AO].
     *)

  Definition A : Type := AO.t.

  (** On mesure un élément par lui même. On utilise un type option et l'arbre vide aura
     pour mesure %\constr{None}%. *)
  
  Module KM := KeyMonoid AO. Import KM.

  Instance ord_measure : Measured key A :=
    { measure := Some }.
  
  (** Le module [KeyMonoid] implémente le monoïde %(\constr{None}, \cst{keyop})% sur le type
     %\ind{option} \id{A}%, où l'opération %\cst{keyop}% est définie par:
     
     %\[\begin{array}{lcl}
     \cst{keyop}~\id{x}~\constr{None} & = & \id{x} \\
     \cst{keyop}~\id{\_}~(\constr{Some}~\_~\kw{as}~\id{y}) & = & \id{y}
     \end{array}\]%
     
     Clairement, cela va donner l'élément le plus à droite de la structure s'il existe.
     Le module définit aussi une fonction %\cst{key\_gt}% qui "lifte" l'ordre sur le type
     ordonné vers le type du monoïde. On peut déclarer le type des séquences ordonnées
     comme spécialisation de [FingerTree] sur le monoïde et la mesure qu'on vient de 
     présenter. *)
  
  Definition OrdSeq := FingerTree ord_measure.

  (** On peut prendre l'élément maximum en temps constant en récupérant la mesure à la
     racine du %\FT%. *)
     
  Definition max (x : OrdSeq) := tree_measure x.

  (* begin hide *)
  Definition singleton (x : A) : OrdSeq := singleton ord_measure x.

  (* end hide *)
  Program Definition partition (k:A) (xs:OrdSeq) : OrdSeq * OrdSeq :=
    split_with (key_ltb (Some k)) xs.

  (* begin hide *)
  Program Definition insert (x:A) (xs:OrdSeq) : OrdSeq :=
    let (l, r) := partition x xs in
      cat l (cons x r).

  Program Definition deleteAll (x : A) (xs : OrdSeq) : OrdSeq :=
    let (l, r) := partition x xs in
    let (_, r') := split_with (fun y => key_gt y (Some x)) r in
      cat l r'.
  Definition size (x : OrdSeq) := tree_size x.
  (* end hide *)
  (** On ne présente pas en détail les autres opérations définies dans l'article original qui 
     permettent de partitionner une séquence ([partition]) ou d'insérer/supprimer un élément,
     elles ne sont pas plus compliquées à programmer.
     On se penche plus précisément sur la seule difficulté liée à la terminaison de ce développement
     qui apparaît lorsqu'on veut coder la fonction [merge] qui mélange deux séquences ordonnées.
     Cette fonction utilise [view_left] sur les séquences et fonctionne donc par récurrence sur
     la vue. Il est à noter que l'argument de terminaison est de plus compliqué par le fait
     qu'on interchange les arguments pour rendre la fonction adaptative. Elle dégénere à une
     concaténation dès que possible, donnant une complexité très bonne en pratique.
     On peut utiliser la mesure [pair_size] définie ci-dessous pour définir la fonction par récursion
     bien fondée sur la paire des séquences. Les obligations générées peuvent être résolues en utilisant
     le lemme [view_left_size] défini plus haut. %\label{fig:merge}% *) 

  Program Fixpoint merge (xs ys : OrdSeq) {measure (tree_size xs + tree_size ys)} : OrdSeq :=
    match view_left xs with
      | nil_left => ys
      | cons_left x xs' =>
        let '(l, r) := split_with (fun y => key_gt y (measure x)) ys 
        in cat l (cons x (merge r xs'))
    end.

  (** On obtient donc une implémentation des séquences ordonnées bâtie sur le code 
     des [fingertree] qu'on peut extraire vers %\Ocaml%. Seulement, on s'appuie ici
     sur des invariants implicites de la structure et rien n'empêche de créer des
     objets de type [OrdSeq] non ordonnés. On pourrait bien sûr faire un raffinement
     du type forçant l'arbre à être ordonné, mais l'on aurait besoin pour cela de
     raisonner sur le code de [fingertree] pour montrer la préservation de cette propriété 
     pour les différentes opérations que nous utilisons. On va plutôt profiter du pouvoir
     de spécification qui nous est donné par le monoïde et l'indexation des %\FTs% dépendants
     pour obtenir une structure certifiée modulairement, sans avoir à raisonner sur le code. *)
  (* begin hide *)

  Import DependentFingerTree.
 

  Next Obligation.
  Proof.
    simpl.
    cut (FingerTree.tree_size ys >= FingerTree.tree_size r) ; intros.
    pose (view_left_size _ (sym_eq Heq_anonymous0)) ; omega.
    rewrite (split_size _ _ (sym_eq Heq_anonymous)). simpl. omega.
  Qed.

End OrdSequence.

(** Tests *)

(*Require Coq.FSets.OrderedTypeEx.

Module NatOrdSeq := OrdSequence Coq.FSets.OrderedTypeEx.Nat_as_OT.
Import NatOrdSeq.

Definition a := 7.
Definition b := 6.
Definition c := 4.

(* This can be checked in the extracted code *)

Definition sample := 
  insert a (insert c (singleton b)).

(* end hide *) *)
