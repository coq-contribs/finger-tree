(* begin hide *)
Require Import List.
Require Import FingerTree.Monoid.
Require Import FingerTree.DependentFingerTree.
Require Import Coq.Program.Program Coq.Program.Equality.
Require Import Omega.
Implicit Type v A : Type.
Set Implicit Arguments.

Arguments fingertree _ {mono} _ {ma}.
(* end hide *)
(** printing lparr $\coqdoublebar$ *)(** printing rparr $\coqdoublebar$ *)(** printing cdot $\cdot$ *)(** printing epsilon $\varepsilon$ *)(** printing +:+ $\treeapp$ *)(** printing ++ $\app$ *)(** printing := $\coloneqq$ *)(** printing :> $\Yright$ *)(** printing < $<$ *)(** printing > $>$ *)
(** ** Une interface non dépendante
   %\label{fts:inst:fingertree}%
   
   Comme décrit précédemment, on peut agréger la mesure et le [fingertree] dans une paire dépendante pour
   donner une interface simplifiée aux %\FTs% dépendants. *)

Section FingerTree.
  Context `(ma : Measured v A).
  Definition FingerTree := { m : v & fingertree v A m }.
  Notation " ts :| t " := (existT _ ts t) (at level 20).
  
  (** Cela nous donne un type [FingerTree v {mono} A {ma}], qu'on peut comparer au type 
     original %\ind{FingerTree} \id{v} \id{a}% dans %\Haskell%. On a ajouté l'implémentation [monoid] et la
     fonction de mesure [ma] comme paramètres explicites alors qu'en %\Haskell% ils sont passés
     implicitement à l'aide des classes de type à chaque fonction les manipulant. 
     
     *)
  (* begin hide *)
  (** Now we can wrap all the operations on [fingertree] objects. *)
  Program Definition empty : FingerTree := ε :| Empty.

  Program Definition is_empty (s : FingerTree) : Prop := 
    let 'ts :| t := s in isEmpty t.
  
  Program Definition is_empty_dec (s : FingerTree) 
    : {is_empty s} + {~is_empty s} :=
    let 'ts :| t := s in 
    if isEmpty_dec t then left _ else right _.
  
  Program Definition singleton (x : A) : FingerTree := 
    _ :| Single x.

  Program Definition cons (x : A) (s : FingerTree) : FingerTree := 
    let 'ts :| t := s in _ :| add_left x t.

  Program Definition snoc (s : FingerTree) (x : A) : FingerTree := 
    let '_ :| t := s in _ :| add_right t x.
  
  Program Definition head (s : FingerTree | ~ is_empty s) : A := 
    let '_ :| t := s in head t.

  Program Definition last (s : FingerTree | ~ is_empty s) : A := 
    let '_ :| t := s in last t.

  Program Definition tail (s : FingerTree | ~ is_empty s) : FingerTree := 
    let '_ :| t := s in tail t.
 
  Program Definition liat (s : FingerTree | ~ is_empty s) : FingerTree := 
    let '_ :| t := s in liat t.
 	
  Definition tree_measure (s : FingerTree) : v := 
    let 'ts :| _ := s in ts.

  Require Import JMeq.

  (* end hide *)
  (** On ne décrit pas le "repackaging" en détail, il s'agit just de décomposer un objet de type 
     [FingerTree], appeler la fonction appropriée sur les [fingertree] et recomposer la paire dépendante.
     En revanche un point important est que l'on peut exporter les vues sur les [fingertree] et retrouver
     la mesure associée: *)

  Program Definition tree_size (s : FingerTree) : nat := 
    let '_ :| t := s in tree_size t.

  Inductive left_view : Type :=
  | nil_left : left_view | cons_left : A -> FingerTree -> left_view.
  (* begin hide *)
  Program Definition view_left (s : FingerTree) : left_view :=
    let '_ :| t := s in
    match view_L t with
      | nil_L => nil_left
      | cons_L x ts t => cons_left x (ts :| t)
    end.
  (* end hide *)

  Lemma view_left_size : forall t x t', view_left t = cons_left x t' -> 
    tree_size t' < tree_size t.
  Proof.
    intros.
    destruct t ; destruct t' ; simpl in *.
    generalize H ; clear H.
    remember (view_L f) as vf.
    destruct vf ; simpl in * ; intros ; try discriminate.
    symmetry in Heqvf.
    pose (view_L_size_measure f Heqvf).
    inversion H.
    subst.
    assert(Hi:=inj_pairT2 H3).
    subst f0.
    simpl.
    omega.
  Qed. 
  (* begin hide *)
  Inductive right_view : Type :=
  | nil_right : right_view
  | cons_right : FingerTree -> A -> right_view.

  Program Definition view_right (s : FingerTree) : right_view :=
    let '_ :| t := s in
    match view_R t with
      | nil_R => nil_right
      | cons_R ts t x => cons_right (ts :| t) x
    end.

  Lemma view_right_size : forall t t' x, view_right t = cons_right t' x -> tree_size t > tree_size t'.
  Proof.
    intros.
    destruct t ; destruct t' ; simpl in *.
    generalize H ; clear H.
    remember (view_R f) as vf.
    destruct vf ; simpl in * ; intros ; try discriminate.
    symmetry in Heqvf.
    inversion H ; subst.
    assert (eq:=inj_pairT2 H2) ; subst*.
    simpl.  
    (*pose (view_R_size_measure f Heqvf). *)
(*     inversion H. *)
(*     simpl. *)
(*     omega. *)
  Admitted.

  (** We wrap concatenation using a simple type but we export the split invariants in an inductive. *)

  Program Definition cat (s s' : FingerTree) : FingerTree :=
    let 's :| ss := s in
    let 'ts' :| ss' := s' in
      _ :| app ss ss'.

  Obligation Tactic := program_simpl.

  Section Splits.
    
  (**     
     The [Split] inductive is is a direct wrapper of the [tree_split] datatype. *)
   
    Inductive Split (p : v -> bool) (i : v) : Type :=
    mkSplit : forall (l : { l : FingerTree | is_empty l \/
      p (i ∙ tree_measure l) = false }) (x : A) (r : FingerTree | is_empty r \/ 
      p (i ∙ tree_measure (`l) ∙ measure x) = true), Split p i.
    
    (** Correspondingly, the function [split] just wraps the original [split_tree] definition. *)

    Program Definition split (p : v -> bool)(i : v) (x : FingerTree | ~ is_empty x)
      : Split p i :=
      let 's :| t := x in
      let (ls, l, x, rs, r) := split_tree p i t in
        mkSplit p i (ls :| ` l) x (rs :| ` r).
    
  (* end hide *)

    (** %\label{def:split_with}%
       On peut aussi refaire le découpage par rapport à un prédicat sur les [FingerTree].
       On offre la même interface simplement typée qu'en %\Haskell% en définissant la 
       fonction [split_with p x]. Cette fonction découpe n'importe quel arbre en regardant
       tout d'abord s'il est vide et sinon en appelant la fonction fortement spécifiée [split]
       avec un accumulateur vide [ε]. On crée alors une paire avec l'arbre à gauche et l'arbre droit 
       auquel on ajoute l'élément qui fait changer le prédicat de valeur. On oublie complètement
       les propriétés données par la fonction [split] sur le résultat. *)
    
    Program Definition split_with (p : v -> bool) 
      (x : FingerTree) : FingerTree * FingerTree := 
      if is_empty_dec x then (empty, empty)
      else let (l, x, r) := split p ε x in (l, cons x r).
    
    (* begin hide *)
    Program Definition takeUntil (p : v -> bool) (x : FingerTree) : FingerTree := 
      fst (split_with p x).
    
    Program Definition dropUntil (p : v -> bool) (x : FingerTree) : FingerTree :=
      snd (split_with p x).
  
    Program Definition size_split (x : FingerTree * FingerTree) : nat :=
      let (x,y) := x in tree_size x + tree_size y.

    Require Import Coq.Program.Equality.

(*     Program Definition coerce_tree_split_v (v : Type) (mono : monoid v) (p : v -> bool)  *)
(*       (A : Type) (measure : A -> v) (i : v) (s : v) (t : tree_split mono p measure i s) *)
(*       (s' : v) (H : s = s') : tree_split mono p measure i s' := *)
(*       match t in tree_split _ _ _ _ s return s = s' -> tree_split mono p measure i s' with *)
(*         mkTreeSplit xsm xs x ysm ys => fun H => mkTreeSplit p i xs x ys *)
(*       end H. *)

(*     Lemma cut_tree_split : forall (v : Type) (mono : monoid v) (p : v -> bool)  *)
(*       (A : Type) (measure : A -> v) (i : v) (s : v) *)
(*       (P :  *)
(*         forall xsm, *)
(*           forall {xs : fingertree mono measure xsm | *)
(*             isEmpty xs \/ p (Monoid.mappend mono i xsm) = false}, *)
(*           forall (x : A) (ysm : v), *)
(*             forall {ys : fingertree mono measure ysm | *)
(*               isEmpty ys \/ *)
(*                 p *)
(*                 (Monoid.mappend mono i *)
(*                   (Monoid.mappend mono xsm (measure x))) = true}, *)
              
(*             tree_split mono p measure i (Monoid.mappend mono xsm (Monoid.mappend mono (measure x) ysm)) ->  *)
(*             Type), *)
(*       forall xsm, *)
(*         forall {xs : fingertree mono measure xsm | *)
(*           isEmpty xs \/ p (Monoid.mappend mono i xsm) = false}, *)
(*         forall (x : A) (ysm : v), *)
(*           forall {ys : fingertree mono measure ysm | *)
(*             isEmpty ys \/ *)
(*             p *)
(*             (Monoid.mappend mono i *)
(*               (Monoid.mappend mono xsm (measure x))) = true}, *)
(*       forall  *)
            
(*         (b :       forall xsm, *)
(*         forall {xs : fingertree mono measure xsm | *)
(*           isEmpty xs \/ p (Monoid.mappend mono i xsm) = false}, *)
(*         forall (x : A) (ysm : v), *)
(*           forall {ys : fingertree mono measure ysm | *)
(*             isEmpty ys \/ *)
(*             p *)
(*             (Monoid.mappend mono i *)
(*               (Monoid.mappend mono xsm (measure x))) = true}, P xsm xs x ysm ys (mkTreeSplit p i xs x ys)) *)
(*         , *)

(*       forall s' (H : (Monoid.mappend mono xsm (Monoid.mappend mono (measure x) ysm)) = s'), *)


(*             match *)
(*               eq_rect (fun s : v => tree_split mono p measure i s) *)
(*               (mkTreeSplit p i xs x ys) s' H as x0 in (tree_split _ _ _ _ v0) *)
(*                 return P x0 *)
(*               with mkTreeSplit xsm xs x ysm ys =>  *)
(*                 b xsm xs x ysm ys *)
(*             end. *)

                

        
    Lemma split_size : forall (p : v -> bool) (t : FingerTree) s, 
      split_with p t = s -> tree_size t = size_split s.
    Proof.
      intros.
      induction t.
      unfold split_with.
      unfold split_with in H.
      destruct (is_empty_dec (x :| p0)) ; simpl in * ; auto.
      subst s.
      unfold tree_size, DependentFingerTree.tree_size.
      simpl ; auto.
      assert (He:=isEmpty_ε _ i) ; subst x.
      assert (He:=isEmpty_Empty p0 i).
      subst p0 ; simpl ; auto.
    Admitted.

  End Splits.
  (* end hide *)
End FingerTree.
