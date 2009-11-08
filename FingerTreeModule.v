(* -*- compile-command: "cd .. && ./makedoc.sh" -*- *)
(* begin hide *)
Require Import FingerTree.Modules.
Require Import FingerTree.DependentFingerTreeModule.
Require Import Coq.Program.Program Coq.Program.Equality.
Implicit Type v A : Type.
Set Implicit Arguments.
(* end hide *)
(** printing lparr $\coqdoublebar$ *)(** printing rparr $\coqdoublebar$ *)(** printing cdot $\cdot$ *)(** printing epsilon $\varepsilon$ *)(** printing +:+ $\treeapp$ *)(** printing ++ $\app$ *)(** printing := $\coloneqq$ *)(** printing :> $\Yright$ *)(** printing < $<$ *)(** printing > $>$ *)
(** ** FingerTree: a non-dependent interface
   
   As shown before, we can wrap the measure and the tree in a dependent pair to offer a simpler
   interface to Finger Trees. 
   %\def\coqdocindent#1{\noindent\kern#1}%
   *)

Module FingerTree(M : Monoid) (Ms : Measured with Module Mon := M).
  Import M.
  Import Ms.
  Module FT := DependentFingerTree M.
  Import FT.
  Definition v := M.m.

  Definition finger_tree :=
    { m : v & fingertree measure m }.

  Notation " ts :| t " := (existT _ ts t) (at level 20).

  (** This gives us a type [finger_tree v mono A measure], which can be compared with 
     the original [finger_tree v a] datatype in Haskell. It adds the [monoid] implementation 
     and [measure] function as explicit parameters whereas in Haskell they are passed implicitely 
     using the typeclass mechanism. Morally, the parameterization we did using the section
     mechanism correspond to the systematic prefixing of functions on [FingerTree] objects by a
     [Measured v a] constraint in Haskell ([Measured v a] is a class with a single function 
     [measure] of type [a -> v] where [v] must have a [Monoid] instance). We 
     think this equivalence indicates an interesting field of investigations 
     on how to integrate overloading in a language like Russell, or a section system in Haskell.
     *)
  (* begin hide *)
  (** Now we can wrap all the operations on [fingertree] objects. *)
  Program Definition empty : finger_tree := epsilon :| Empty.
  
  Program Definition is_empty (s : finger_tree) : Prop := 
    let 'ts :| t := s in isEmpty t.
  
  Program Definition is_empty_dec (s : finger_tree) 
    : {is_empty s} + {~is_empty s} :=
    let 'ts :| t := s in 
    if isEmpty_dec t then left _ else right _.
  
  Program Definition singleton (x : A) : finger_tree := 
    _ :| Single x.

  Program Definition cons (x : A) (s : finger_tree) : finger_tree := 
    let 'ts :| t := s in _ :| add_left x t.
  
  Program Definition snoc (s : finger_tree) (x : A) : finger_tree := 
    let '_ :| t := s in _ :| add_right t x.
  
  Program Definition head (s : finger_tree | ~ is_empty s) : A := 
    let '_ :| t := s in head t.

  Program Definition last (s : finger_tree | ~ is_empty s) : A := 
    let '_ :| t := s in last t.

  Program Definition tail (s : finger_tree | ~ is_empty s) : finger_tree := 
    let '_ :| t := s in tail t.
 
  Program Definition liat (s : finger_tree | ~ is_empty s) : finger_tree := 
    let '_ :| t := s in liat t.
 	
  Definition tree_measure (s : finger_tree) : v := 
    let 'ts :| _ := s in ts.

  Require Import JMeq.

  Program Definition tree_size (s : finger_tree) : nat := 
    let '_ :| t := s in tree_size t.

  (* end hide *)
  (** 
     We do not describe the wrapping in detail, it is just destructuring a [finger_tree] object,
     calling the appropriate function on [fingertree]s and packing back the measure and the tree.     
     However, an important point is that we can wrap views too
     and obviously recover the associated measure: *)

  Inductive left_view : Type :=
  | nil_left : left_view | cons_left : A -> finger_tree -> left_view.
  (* begin hide *)
  Program Definition view_left (s : finger_tree) : left_view :=
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
    assert(Hi:=inj_pair2 H3).
    subst f0.
    simpl.
    omega.
  Qed. 
  (* begin hide *)
  Inductive right_view : Type :=
  | nil_right : right_view
  | cons_right : finger_tree -> A -> right_view.

  Program Definition view_right (s : finger_tree) : right_view :=
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
    (*pose (view_R_size_measure f Heqvf).
    inversion H.
    simpl.
    omega.*)
  Admitted.

  (** We wrap concatenation using a simple type but we export the split invariants in an inductive. *)

  Program Definition cat (s s' : finger_tree) : finger_tree :=
    let 's :| ss := s in
    let 'ts' :| ss' := s' in
      _ :| app ss ss'.

  Obligation Tactic := program_simpl.

  Section Splits.

    Program Definition get (p : v -> bool) (x : finger_tree | ~ is_empty x) 
      (i : v | p i = false /\ p (i cdot tree_measure x) = true) : v * A :=
      let 's :| t := x in
        get_tree p t tt i.
    
  (**     
     The [Split] inductive is is a direct wrapper of the [tree_split] datatype. *)
   
    Inductive Split (p : v -> bool) (i : v) : Type :=
    mkSplit : forall (l : { l : finger_tree | is_empty l \/
      p (i cdot tree_measure l) = false }) (x : A) (r : finger_tree | is_empty r \/ 
      p (i cdot tree_measure (`l) cdot measure x) = true), Split p i.
    
    (** Correspondingly, the function [split] just wraps the original [split_tree] definition. *)

    Program Definition split (p : v -> bool)(i : v) (x : finger_tree | ~ is_empty x)
      : Split p i :=
      let 's :| t := x in
      let 'mkTreeSplit ls l x rs r := split_tree p i t in
        mkSplit p i (ls :| l : finger_tree) x (rs :| r : finger_tree).
  (* end hide *)

    (** %\def\coqdocindent#1{\noindent\kern#1\hskip-1em}\label{def:split_with}%We can finally wrap splitting
       on [finger_tree]s along a predicate. We offer the same
       simply-typed interface as Haskell by definining the function [split_with p x].
       It splits any tree [x] by first checking if [x] is empty and if
       not calls the [split] function on it using the predicate [p] with an empty accumulator.
       %\extended{Its first and second projections give the [takeUntil] and [dropUntil] functions 
       which return respectively the prefix of the tree for which the predicate was [false]
       and the rest of the tree.}% *)

    Program Definition split_with (p : v -> bool) 
      (x : finger_tree) : finger_tree * finger_tree := 
      if is_empty_dec x then (empty, empty)
      else let (l, x, r) := split p epsilon x in (l, cons x r).
    
    (* begin hide *)
    Program Definition takeUntil (p : v -> bool) (x : finger_tree) : finger_tree := 
      fst (split_with p x).
    
    Program Definition dropUntil (p : v -> bool) (x : finger_tree) : finger_tree :=
      snd (split_with p x).

    Program Definition size_split (x : finger_tree * finger_tree) : nat :=
      let (x,y) := x in tree_size x + tree_size y.

    Require Import Coq.Program.Equality.

    Print mkTreeSplit.

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

                

        
    Lemma split_size : forall (p : v -> bool) (t : finger_tree) s, 
      split_with p t = s -> tree_size t = size_split s.
    Proof.
      intros.
      induction t.
      unfold split_with.
      unfold split_with in H.
      destruct (is_empty_dec (x :| p0)) ; simpl in * ; auto.
      subst s.
      unfold tree_size.
      simpl ; auto.
      assert (He:=isEmpty_epsilon _ i) ; subst x.
      assert (He:=isEmpty_Empty p0 i).
      subst p0 ; simpl ; auto.

      subst s.
      destruct p0.
      unfold isEmpty in n ; simpl in n.
      elim n ;  auto.

    Admitted.

(*       unfold split ; simpl. *)
(*       unfold split_tree ; simpl. *)
(*       on_coerce_proof_gl ltac:(fun p => set(H:=p)). *)
      
(*       Set Printing Implicit. *)
(*       Unset Printing Notations. *)
(*       intros. *)
(*       match goal with *)
(*         | |- ?T =>  *)

(*       pattern H. *)
(*       generalize dependent H. *)
(*       pattern (mappend mempty (mappend (measure x) mempty)) at 1 2. *)

(*       generalize *)
(*       (eq_rect (epsilon cdot measure x cdot epsilon) *)
(*               (fun H0 : Digits.v => tree_split p measure epsilon H0) *)
(*               (mkTreeSplit p epsilon (Empty )%subset x (Empty &?)%subset) *)
(*               (measure x) H). *)
(*       generalize dependent H. *)
(*       rewrite H in H. *)
(*       clearbody H. *)
(*     Admitted. *)

  End Splits.
  (* end hide *)
End FingerTree.
