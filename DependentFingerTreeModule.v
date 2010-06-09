(* begin hide *)
Require Import FingerTree.Monoid.
Require Import FingerTree.Reduce.
Require Import FingerTree.Notations.

Require Import FingerTree.Modules.
Require Import FingerTree.DigitModule.

Require Import Coq.Program.Program Coq.Program.Equality.
Require Import Omega JMeq.

Unset Dependent Propositions Elimination.
Set Implicit Arguments.
(** Useful when working with existT equalities. *)
Implicit Arguments inj_pair2 [U P p x y].
(* end hide *)
(** printing lparr $\coqdoublebar$ *)(** printing rparr $\coqdoublebar$ *)(** printing cdot $\cdot$ *)(** printing epsilon $\varepsilon$ *)(** printing +:+ $\treeapp$ *)(** printing ++ $\app$ *)(** printing := $\coloneqq$ *)(** printing ::> $\Yright$ *)(** printing < $<$ *)
(** We shall now define the Finger Trees over some monoid and measure. 
   We will see in section %\ref{sec:Instances}% how particular instantiations of these
   will give different structures.
*)

Ltac program_simpl ::= program_simplify ; auto with *.

Module DependentFingerTree (M : Monoid).
  Import M.
  
  Module Digits := DigitMeasure M.
  Import Digits.

  Hint Unfold digit_measure option_digit_measure option_measure.

  (* Digits are defined in [FingerTree.Digit], we define 2-3 nodes parameterized by a measure. *)  

  (** ** Nodes

     Finger Trees are implemented using 2-3 nodes as in 2-3 trees, with the addition
     of a cached value that stores the combined measure of the subobjects.
     *)

  Section Nodes.    
    Variables (A : Type) (measure : A -> v).
    Notation " 'lparr' x 'rparr' " := (measure x).

    (** Intuitively, the measure represents an
       abstraction of the sequence of objects in the node (later, in the tree) considered from left to right.
       Taking the list monoid previously defined and the singleton measure $\tip$ gives
       the most concrete abstraction of this sequence of elements: the sequence itself.
       The [measure] function is denoted by $\measure{\_}$ in the following, when possible
       (notations local to a function are not supported). We now define 2-3 nodes with cached measures:
       *)
    
    Inductive node : Type :=
    | Node2 : forall x y, { s : v | s = lparr x rparr cdot lparr y rparr } -> node
    | Node3 : forall x y z, { s : v | s = lparr x rparr cdot lparr y rparr cdot lparr z rparr } -> node.

    (**
       We use a subset type here to specify the invariant on the cached value. This invariant
       could not be checked using simple types, because it is dependent
       on the values carried by the node. Moreover, it uses the measure %\emph{function}%
       as a %\emph{datatype parameter}% so it would require an additional abstraction mechanism like type
       classes or functors to achieve it in a regular ML-based functional language.  
       A regular dependent product is used here instead.
       *)

    (** We have smart constructors [node2] and [node3] which compute the measure, e.g: *)

    Program Definition node2 (x y : A) : node := 
      @Node2 x y (lparr x rparr cdot lparr y rparr).
    (* begin hide *)
    Program Definition node3 (x y z : A) : node := 
      @Node3 x y z (lparr x rparr cdot lparr y rparr cdot lparr z rparr).

    Definition node_to_digit (n : node) : digit A :=
      match n with | Node2 x y _ => Two x y | Node3 x y z _ => Three x y z end.
    (** [node_to_digit n] converts a node to a digit. *)
    (* end hide *)

    (** The generated obligations are trivially true as they are of the form $x = x$.
       Correspondingly, [node_measure] pulls the cached measure. *)

    Program Definition node_measure (n : node) : v :=
      match n with Node2 _ _ s => s | Node3 _ _ _ s => s end.   
  End Nodes.

  (** Although it may seem that the [node_measure] function is independent of the [measure] function,
     it is not. Witness its type after we closed the section: 
     %\[\forall (A : \Type) (\ident{measure}: A "->" v),
     \coqdocind{node}~\ident{measure} "->" v\]%
     The [node] datatype itself is parameterized by the measure function, hence all operations on
     nodes take it as an implicit parameter.
     Had we not added the invariant, we would not need this parameter,
     but we could not prove much about node measures either, because they might be
     any element of type [v]. We could define an inductive invariant on nodes asserting 
     that their measures were built using the measure function coherently, but we would need to show
     that this invariant is preserved in each of the functions, while in our case we get it 
     for free by typing.
     *)
  
  (* begin hide *)
  Implicit Arguments node_measure [A].

  (** We define this abbreviation for partial applications, where the [measure] parameter
     will get instantiated automatically. *)

  Implicit Arguments Node2 [A measure].
  Implicit Arguments Node3 [A measure].
  
  Hint Unfold option_digit_measure option_measure digit_measure : ft.
  
  Lemma nodeMeasure_digits : forall A (measure : A -> v) n, 
    (node_measure measure n) = digit_measure measure (node_to_digit n).
  Proof.
    intros.
    destruct n ; program_simpl ; monoid_tac ; auto.
  Qed.
  (* end hide *)

  (** ** The [fingertree] datatype
     
     Before presenting the definition of [fingertree] in Coq, we introduce the original 
     Haskell datatype and justify why the direct translation would be unsatisfactory.
     In Haskell, the [FingerTree] algebraic datatype is defined as:

     %\kw{data} \ind{FingerTree} \id{v} \id{a} = \constr{Empty} | \constr{Single} \id{a}\coqdoceol{}
     \coqdocindent{2.00em}| \constr{Deep} \id{v} (\ind{Digit} \id{a}) (\ind{FingerTree} \id{v} (\ind{Node} \id{v} \id{a})) (\ind{Digit} \id{a})
     %

     %\noindent{}%The [Empty] constructor represents the empty tree, the [Single] constructor builds a singleton tree
     from an element of [a] and the [Deep] constructor is the branching node. 
     It builds a [FingerTree v a] from a cached measure of type [v], two digits of [a]
     and a middle [FingerTree v (Node v a)] of %\emph{2-3 nodes}% of [a] with measures of type [v].
     This is where the nesting occurs; it is best described by a picture
     (figure %\ref{fig:FingerTree}%).
     
     %\begin{figure}[h]\begin{center}\tikfingertree\end{center}%
     %\caption{A sample FingerTree.\small{%
     At the first level we have a [Deep] node with a 
     2-digit of [a] at the left and a 3-digit at the right. The middle tree is a [FingerTree v (Node v a)] consisting
     of a [Deep] node with an [Empty] middle tree. It has a 2-digit of [Node v a] at its left and
     a 1-digit at its right. The circled nodes represent elements of type [a] and the shaded ones
     indicate loci where cached measures are stored%}}\label{fig:FingerTree}\end{figure}%
     
     We could directly define the Finger Tree data structure in Coq by translating 
     the Haskell definition. However doing so would cause a rather subtle problem: 
     the cached measures in two Finger Trees could be computed by two %\emph{different}%
     measure functions but these trees would still have the same type because the [FingerTree] datatype is 
     parameterized only by the type of the computed measures and not by the measure function.
     Again, we could live with it and have a predicate formalizing the fact
     that the measures appearing in a [FingerTree] were built coherently with some measure function, but 
     preservation of this invariant would have to be proved for each new definition on
     Finger Trees. We prefer to view the measure function as an additional parameter of the Finger Tree
     datatype. In this case coherence is ensured by the type system because two Finger Trees 
     will have different types if they are built from different measure functions. Hence the following 
     definition:

     A [fingertree] inductive is parameterized by a type [A] and a measure function [measure : A -> v] on this type.
     Each [fingertree] object is also indexed by its corresponding measure:
     
     - [Empty] builds the empty tree of measure $\varepsilon$;
     - [Single x] builds the tree with sole element [x] of measure $\measure{x}$;
     - [Deep pr ms m sf] builds the tree of prefix [pr], subtree [m] of measure [ms] and suffix [sf]. 
     Its measure is given by combining the measures of its subtrees. The argument [ms] will be 
     implicit when constructing [Deep] nodes, as it can be infered from the type of [m]. We place 
     this argument [ms] just before the middle Finger Tree contrary to the original datatype in which
     the cached measure is the first field and stores the measure of the %\emph{whole}% tree whereas
     for us the latter is given by the index.

     We present the definition using inference rules for enhanced readability, omitting [A] and [measure] in the
     premises:
     
     %\fingertreeFig%
    *)
  (* begin hide *)
  Inductive fingertree A (measure : A -> v) : v -> Type :=
  | Empty : fingertree measure epsilon
  | Single : forall x : A, fingertree measure (measure x)
  | Deep : forall (l : digit A) (ms : v), 
    fingertree (A:=node measure) (node_measure measure) ms
    -> forall r : digit A, fingertree measure
      (digit_measure measure l cdot ms cdot digit_measure measure r).
  (* end hide *)
  (** This inductive family is indexed by values of type [v]. 
     Why we need a dependent type follows from a simple observation. If we want
     the cached measure on the [Deep] node and the invariant that the measure is
     really the one of the middle tree, we must have a way to refer
     to the measure of the middle tree, but we are actually defining trees, 
     so we cannot recurse on them at this time. 
     Note also that we need %\emph{polymorphic}% recursion to go into the middle subtrees of [Deep] nodes.     
     *)
  (* begin hide *)
  Implicit Arguments Single [A measure].
  Implicit Arguments Empty [A measure].
  Implicit Arguments Deep [A measure ms].

  Section add.   
  (* end hide *)    

  (** **** Adding elements
     %\label{def:addleft}% We can add an element [a] to the left of a tree [t] of measure [s] to get a tree with measure 
     $\measure{a} \cdot s$. Due to polymorphic recursion, our functions will now always have [A] and [measure] arguments
     as they are %\emph{real}% arguments which will change during recursive calls. If [t] is empty, a singleton or a tree with
     a left prefix which is not full, then we simply put [a] at the leftmost position of the tree. Otherwise, we need to
     reorganize the tree to make space at the left for [a], and this requires recursing polymorphically to add a [node a] to the 
     left of the middle subtree in the [Deep] node.
     *) 

    Program Fixpoint add_left (A : Type) (measure : A -> v)
      (a : A) (s : v) (t : fingertree measure s) {struct t} : 
      fingertree measure (measure a cdot s) :=
      match t in fingertree _ s 
      return @fingertree A measure (measure a cdot s) with
        | Empty => Single a
        | Single b => Deep (One a) Empty (One b)
        | Deep pr st' t' sf =>
          match pr with
            | Four b c d e => 
              let sub := add_left (node3 measure c d e) t' in
                Deep (Two a b) sub sf
            | x => Deep (add_digit_left a pr) t' sf
          end
      end.
    
    (** The first match expression uses dependent elimination. Its meaning is that 
       from a particular [fingertree] of measure [s] each branch will build a [fingertree] of measure [measure a cdot s]
       where [s] has been substituted by the measure of the matched pattern. 
       For example in the first branch we must build an object of type 
       [fingertree measure (measure a cdot epsilon)].
       However, the right hand side [Single a] has type 
       [fingertree measure (measure a)], hence we must use the inductive equivalence rule %(figure \ref{fig:russell:indequiv})%,
       which generates an obligation $\vdash \ident{measure} a \cdot \varepsilon = \ident{measure} a$, 
       easily solved using the right identity of the monoid. The [in] and [return] clauses
       are mandatory in Coq due to undecidability of higher-order unification, but they can be
       dropped in Russell, in which case substitution is replaced by equational reasoning.
       Had we dropped the clauses, we would have the equation [s = epsilon] in the context of the first branch hence
       the generated obligation $s = \varepsilon \vdash \ident{measure} a \cdot s = \ident{measure} a$. 
       This one would be solved by first substituting [s] by $\varepsilon$ in the goal then
       applying the right identity ; we just postponed the substitution.

       The nested match expression uses an alias [x] for capturing prefixes which are not [Four] and applies the partial function
       [add_digit_left] defined earlier. There is an application of the subset equivalence rule here, which
       generates an obligation to show that [pr] is not full. It can be solved because we have 
       $`A b~c~d~e, pr \neq \ident{Four}~b~c~d~e$ in the context.

       It is an essential property of this function that the measure is preserved. To see that, let us instantiate 
       the Finger Tree by the list monoid $(\nil, \app)$ and measure $\tip$ defined earlier.
       You can check here that adding to the left is prepending the measure of the element to
       the measure of the Finger Tree, hence consing to the sequence of elements of the tree with 
       the list monoid interpretation.
       For each of the following operations, this correspondence with
       the list instanciation of the measure will hold. *)
    (* begin hide *)
    Solve Obligations using program_simpl ; try unfold digit_measure ; simpl ; monoid_tac ; auto with *.

    Next Obligation.
    Proof.
      destruct pr ; simpl in H0 ; try discriminate ; auto.
      elim (H a0 a1 a2 a3) ; auto.
    Qed.

    Next Obligation.
    Proof.
      intros.
      destruct pr ; simpl ; auto ;
      try subst x ; try clear Heq_t ; try subst s ; monoid_tac ; auto ;
        simpl ; monoid_tac ; auto.
      elim H with a0 a1 a2 a3 ; auto.
    Qed.
    
    Program Fixpoint add_right A (measure : A -> v) (s : v) (t : fingertree measure s) (a : A) {struct t} : 
      fingertree measure (s cdot measure a) :=
      match t in fingertree _ s return fingertree measure (s cdot measure a) with
        | Empty => Single a
        | Single b => Deep (One b) Empty (One a)
        | Deep pr st' t' sf =>
          match sf with
            | Four b c d e => Deep pr (add_right t' (node3 measure b c d)) (Two e a)
            | _ => Deep pr t' (add_digit_right sf a)
          end
      end.

    Solve Obligations using program_simpl ; simpl ; monoid_tac ; auto.

    Next Obligation.
    Proof.
      destruct sf ; simpl in H0 ; try discriminate ; auto.
      elim (H a0 a1 a2 a3) ; auto.
    Qed.

    Next Obligation.
    Proof.
      intros.
      destruct sf ; simpl ; monoid_tac ; auto.
      elim H with a0 a1 a2 a3 ; auto.
    Qed.
    
  End add.  
  (** A simpler example of dependent elimination is given by [digit_to_tree], 
     which turns a digit into a tree with the same measure. Note that we
     did no keep the type annotations. *)
     
  Program Fixpoint digit_to_tree (A : Type) (measure : A -> v) 
    (d : digit A) {struct d} : 
    fingertree measure (digit_measure measure d) :=
    match d with
      | One x => Single x
      | Two x y => Deep (One x) Empty (One y)
      | Three x y z => Deep (Two x y) Empty (One z)
      | Four x y z w => Deep (Two x y) Empty (Two z w)
    end.
  
  (** *** Computing the size of a tree
     In this section we build recursive functions for computing the number of elements of a tree.
     It will be used as a measure for recursion on the various views of Finger Trees. *)

  Section Size.
    Definition digit_size (A : Type) (size : A -> nat) (d : digit A) := 
      match d with
        | One x => size x
        | Two x y => size x + size y
        | Three x y z => size x + size y + size z
        | Four x y z w => size x + size y + size z + size w
      end.

    Definition node_size (A : Type) (measure : A -> v) (size : A -> nat) (d : node measure) := 
      match d with
        | Node2 x y _ => size x + size y
        | Node3 x y z _ => size x + size y + size z
      end.

    Fixpoint tree_size' (A : Type) (measure : A -> v) (size : A -> nat) (s : v) 
      (t : fingertree measure s) : nat :=
      match t with
        | Empty => 0
        | Single x => size x
        | Deep xs _ x ys => digit_size size xs + tree_size' (node_size size) x + digit_size size ys
      end.
    
    Definition tree_size (A : Type) (measure : A -> v) (s : v) (t : fingertree measure s) : nat :=
      tree_size' (fun _ => 1) t.

  End Size.

  Section view_L.
  (* end hide *)

  (** ** The view from the left... of a [fingertree]
     %\def\coqdocindent#1{\noindent\kern#1\hskip-1em}%
     We will now construct views on the Finger Trees which decompose a tree into its leftmost element and a remaining 
     Finger Tree ([View_L]) (or dually, the rightmost one and the "preceding" Finger Tree). 
     It serves to abstract from the implementation and give a list-like view of [fingertree], 
     which is used to write functions which recurse on fingertrees without having to deal 
     with the intricacies of the structure (c.f. figure %\ref{fig:merge}%).
     The [View_L] inductive is a little less polymorphic, as it does not need
     carry the measure function which views ignore. 
     However [View_L] still stores the measure [s] of the rest of the tree in the [cons_L] constructor ([s] will be implicit),
     hence we need to abstract by the sequence's type [seq] which is indexed by [v]. 
     It will be instanciated by [fingertree measure]. *)

    Inductive View_L (A : Type) (seq : v -> Type) : Type := 
    | nil_L : View_L A seq
    | cons_L : A -> forall s, seq s -> View_L A seq.
    
    (* begin hide *)
    Implicit Arguments nil_L [A seq].
    Implicit Arguments cons_L [A seq s].
    (* end hide *)

    (** Such a view will be constructed by the [view_L] function, by structural (polymorphic)
       recursion on the [fingertree]. We can seamlessly use the [digit_tail] function which is partial (it accepts
       only digits which are not [One]) and need not add any type annotations when calling [view_L] recursively on [t']. 
       Note that we use a partial type application [(fingertree measure)] in the return type, which is perfectly legal.
       %\label{def:viewL}%*)

    Program Fixpoint view_L A (measure : A -> v)
      (s : v) (t : fingertree measure s) {struct t} : 
      View_L A (fingertree measure) := 
      match t with
        | Empty => nil_L 
        | Single x => cons_L x Empty
        | Deep pr st' t' sf => 
          match pr with
            | One x => 
              match view_L t' with
                | nil_L => cons_L x (digit_to_tree _ sf)
                | cons_L a st' t' => 
                  cons_L x (Deep (node_to_digit a) t' sf)
              end
            | y => cons_L (digit_head y) (Deep (digit_tail y) t' sf)
          end
      end.

    (* begin hide *)
    Next Obligation.
    Proof.
      intros.
      destruct pr ; simpl in * ; auto.
      apply H with a ; auto.
    Qed.

    (** We prove some lemmas that will come in handy later. 
       First, we can do case analysis on [view_L]. *)

    Lemma view_L_case : forall A (measure : A -> v) (s : v) (t : fingertree measure s), 
      view_L t = nil_L \/ exists x, exists st', exists t',  view_L t = cons_L x (s:=st') t'.
    (* begin hide *)
    Proof.
      intros.
      destruct (view_L t) ; simpl ; intuition ; auto.
      right.
      exists a ; exists s0 ; exists f ; auto.
    Qed.
    (* end hide *)

    (** We can show that [view_L] preserves the measure of the input tree;
       had we indexed [View_L] by the measure of the input tree,
       these generation lemmas would have appeared as obligations. 
       *)

    Lemma view_L_nil : forall A (measure : A -> v) s
      (t : fingertree measure s), view_L t = nil_L -> s = epsilon.
    (* begin hide *)
    Proof.
      intros.
      induction t ; simpl in * ; try discriminate ; auto.
      destruct l ; simpl  in * ; try discriminate ; auto.
      
      monoid_tac.
match type of IHt with
      context [ ?x = _ -> _ ] => set (y :=x)
      end.

      program_simpl.
      destruct (view_L t) ; try destruct (digit_to_tree measure r) ; simpl  in * ; try discriminate ; auto.
    Qed.
    (* end hide *)

    Lemma view_L_cons : forall A (measure : A -> v) s
      (t : fingertree measure s) x st' t',
      view_L t = cons_L x (s:=st') t' -> s = measure x cdot st'.
    (* begin hide *)
    Proof.
      induction t ; program_simpl ; intros ; simpl in * ; try discriminate ; auto.
      simpl ; monoid_tac ; auto.
      destruct l ; simpl  in * ; try discriminate ; monoid_tac ; auto ; try (inversion H ; subst ; simpl ; monoid_tac ; auto).

      destruct (view_L_case t).
      rewrite H0 in H.
      inversion H ; subst ; simpl ; monoid_tac ; auto.
      rewrite (view_L_nil _ H0) ; monoid_tac ; auto.

      destruct_exists.
      rewrite H4 in H ; simpl.
      inversion H ; simpl ; subst.
      f_equal.
      rewrite (IHt _ _ _ H4).
      monoid_tac ; f_equal.
      unfold digit_measure ; rewrite nodeMeasure_digits ; auto.
    Qed.
    (* end hide *)
    (** *** Dependence hell
       %\label{sec:DependenceHell}%
       Our views are useful to give an high-level interfaces to Finger Trees, but in their current state 
       they are very limited as we can write only non-recursive definitions on views. That is, we will not 
       be able to convince Coq that functions defined by recursion on the view of a tree are just as valid
       as those defined by recursion on the tree itself. To do that, we must have a measure on our Finger Trees, e.g. their number
       of elements (named [tree_size]), from which we can trivially build a measure on the views [View_L_size]. Then it is only
       a matter of showing that for all [t], [view_L t] returns a view of size [tree_size t] to prove that a recursive
       call on the tail of a view is correct (c.f. %\S\ref{fig:merge}%).
       
       However, doing such a thing is not as easy as it looks because [view_L] manipulates objects of dependent types
       and reasoning about them is somewhat tricky. An essential difficulty is that the usual Leibniz equality is not 
       large enough to compare objects in dependent types as they may be comparable but in different types. A simple example
       is that the proposition [vnil = vcons x n v] is not well-typed because [vnil] is of type [vector 0] and [vcons x n v]
       of type [vector (S n)] which are not convertible.

       In our case, we want to say that an arbitrary tree [t] of measure [s] with view [nil_L] must 
       be the [Empty] tree, but those two trees do not have the same type. We apply the usual
       trick of heterogeneous equality %\cite{mcbride00dependently}% : prove they must be in the same type. The inductive
       [JMeq] defines an heterogeneous equality (previously denoted by $"~="$) in Coq. It is used to compare objects which are not 
       of the same type. Its sole constructor is [JMeq_refl] of type $\forall~A~a, \coqdocind{JMeq}~A~a~A~a$.
       The point of this admittedly strange notion of equality is to postpone the moment at which
       we need to prove that the types of the compared objects are equal. When we arrive at this point, 
       we can apply the [JMeq_eq] axiom of type $\forall~A~x~y, \coqdocind{JMeq}~A~x~A~y "->" x = y$ to
       get back a regular equality between the objects.
    
       In the first lemma, we compare [t] of measure [s] with [Empty] of measure $\varepsilon$; 
       clearly, replacing [JMeq] by regular equality would yield a type error here.
    *)

    Lemma view_L_nil_JMeq_Empty : forall A (measure : A -> v) s
      (t : fingertree measure s), view_L t = nil_L -> 
      JMeq t (Empty (measure:=measure)).
    (* begin hide *)
    Proof.
      intros.
      induction t ; simpl in * ; try discriminate ; auto.
      destruct l ; simpl  in * ; try discriminate ; auto.
      program_simpl ; destruct (view_L t) ; try destruct (digit_to_tree measure r) ; simpl  in * ; try discriminate ; auto.
    Qed.
    (* end hide *)

    (** Now that we have shown the equality for a general [s] index, we can instantiate it 
       with a particular one, i.e. $\varepsilon$. Given that $t$ is now of measure $\varepsilon$, 
       we can use the regular equality with [Empty].
       *)

    Lemma view_L_nil_Empty : forall A (measure : A -> v) 
      (t : fingertree measure epsilon), view_L t = nil_L -> t = Empty.
    Proof.
      intros ; apply JMeq_eq.
      apply (view_L_nil_JMeq_Empty _ H).
    Qed.

    (* begin hide *)
    Section view_L_measure.
    
      Definition View_L_size' A (measure : A -> v) (size : A -> nat) 
        (view : View_L A (fingertree measure)) :=
        match view with
          | nil_L => 0
          | cons_L x st' t' => size x + tree_size' size t'
        end.

      Definition View_L_size A (measure : A -> v) 
        (view : View_L A (fingertree measure)) :=
        View_L_size' (fun _ => 1) view.

      Lemma digit_to_tree_size : forall A (measure : A -> v) (f : A -> nat) d, tree_size' f (digit_to_tree measure d) = digit_size f d.
      Proof.
        intros.
        induction d ; program_simpl ; simpl ;
          elim_eq_rect ; simpl ; auto with arith.
        omega.
      Qed.
      
      Lemma node_to_digit_size : forall A (measure : A -> v) (f : A -> nat) n, digit_size f (node_to_digit n) = (node_size (measure:=measure) f) n.
      Proof.
        intros.
        destruct n ; simpl ; auto.
      Qed.

      Lemma view_L_size_gen : forall A (measure : A -> v) (s : v)
        (t : fingertree measure s) (f : A -> nat),
        View_L_size' f (view_L t) = tree_size' f t.
      Proof.
        induction t ; simpl ; intros ; auto.
        destruct l ; program_simpl ; simpl in IHt ; subst ; simpl ; auto with arith ; try omega.
        program_simpl ; destruct (view_L_case t).
        rewrite H ; simpl.
        rewrite H in IHt.
        simpl in IHt.
        assert (Heq:=view_L_nil _ H).
        subst ms.
        rewrite (view_L_nil_Empty _ H).
        simpl.
        rewrite digit_to_tree_size ; auto with arith.

        destruct H as [x [st' [t' Hview]]].
        rewrite Hview in IHt.
        simpl in IHt.
        rewrite Hview ; simpl.
        pose (IHt (node_size (measure:=measure) f)).
        rewrite <- e.
        rewrite node_to_digit_size.
        auto with arith.
      Qed.
      (* end hide *)
    (** %\def\coqdocindent#1{\noindent\kern#1\hskip-2em}%These technical lemmas about [nil_L] and [Empty] will help us 
       build our measure. Indeed, they are needed to prove the following: *)

      Lemma view_L_size : forall A (measure : A -> v) (s : v)
      (t : fingertree measure s), View_L_size (view_L t) = tree_size t.
      Proof.
        intros.
        unfold View_L_size, tree_size ; apply view_L_size_gen.
      Qed.

      (** This gives us a decreasing measure on [view_L] results. We will use it when building
         the instances. *)

      Lemma view_L_size_measure : forall A (measure : A -> v) (s : v)
        (t : fingertree measure s) x st' (t' : fingertree measure st'), 
        view_L t = cons_L x t' -> tree_size t' < tree_size t.
      (* begin hide *)
      Proof.
        intros ; unfold tree_size. 
        pose (view_L_size t).
        rewrite H in e ; simpl in e.
        unfold tree_size in e.
        omega.
      Qed.
    End view_L_measure.
    (* end hide *)
    
    (** %\def\coqdocindent#1{\noindent\kern#1\hskip-1em}%We can also define [deep_L], the smart constructor
       which rearranges a tree given a potentially empty digit
       for the prefix. It is a dependent version of the internal function for the [Deep] case of [view_L],
       which is used when splitting Finger Trees.
       The code has not changed at all from the non-dependent version hence we do not show it.
       However, the specification would greatly benefit from an overloading mechanism to factor the different [measure] specializations.

       %\deepLfig%
       *)
    (* begin hide *)
    Program Definition deep_L (A : Type) (measure : A -> v) 
      (d : option (digit A)) (s : v) 
      (mid : fingertree (node_measure measure) s)
      (sf : digit A) : fingertree measure (option_digit_measure 
        measure d cdot s cdot digit_measure measure sf) := 
      match d with
        | Some pr => Deep pr mid sf
        | None =>  
          match view_L mid with
            | nil_L => digit_to_tree _ sf
            | cons_L a sm' m' => Deep (node_to_digit a) m' sf
          end
      end.

    Local Obligation Tactic := program_simpl ; monoid_tac ; auto.
    Solve Obligations.
    
    Next Obligation.
    Proof.
      intros.
      unfold option_digit_measure ; simpl.
      monoid_tac ; auto.
      induction mid ; simpl in * ; monoid_tac ; auto ; try discriminate.
      destruct l ; simpl ; try discriminate.
      program_simpl ; destruct (view_L mid) ; simpl ; try discriminate.
    Qed.

    Next Obligation.
    Proof. 
      intros.
      unfold option_digit_measure, option_measure.
      monoid_tac.
      destruct mid ; simpl in * ; try discriminate.
      inversion Heq_anonymous ; subst ; simpl ; monoid_tac ; auto.
      f_equal.
      destruct x ; simpl ; monoid_tac ; auto.
      program_simpl ; auto.
      program_simpl ; auto.
      rewrite <- monoid_assoc.
      f_equal.
      monoid_tac.

      repeat rewrite <- nodeMeasure_digits ; simpl ; monoid_tac ; auto.

      destruct l ; simpl ; monoid_tac ; auto.
      destruct (view_L_case mid).
      rewrite H in Heq_anonymous ; simpl in * ; auto.

      inversion Heq_anonymous ; subst ; simpl ; auto ; clear Heq_anonymous.
      f_equal ; auto.
      rewrite (view_L_nil _ H).
      monoid_tac ; auto.

      destruct H as [x [st' [t' H]]].
      rewrite H in Heq_anonymous ; simpl.
      inversion Heq_anonymous.
      subst.
      f_equal.
      repeat rewrite nodeMeasure_digits ; simpl ; monoid_tac ; auto.

      rewrite <- monoid_assoc.
      f_equal.
      rewrite (view_L_cons _ H) ; rewrite <- nodeMeasure_digits ; auto.

      inversion Heq_anonymous ; simpl ; subst ; monoid_tac ; repeat rewrite nodeMeasure_digits ; auto.
      inversion Heq_anonymous ; simpl ; subst ; monoid_tac ; repeat rewrite nodeMeasure_digits ; auto.
      inversion Heq_anonymous ; simpl ; subst ; monoid_tac ; repeat rewrite nodeMeasure_digits ; auto.
    Qed.

  End view_L.
  (* end hide *)
  (* begin hide *)
  Section view_R.

    Inductive View_R (A : Type) (measure : A -> v) (seq : forall (A : Type) (measure : A -> v), v -> Type)  : Type := 
    | nil_R : View_R measure seq
    | cons_R : forall s : v, seq A measure s -> A -> View_R measure seq.
    
    Implicit Arguments nil_R [A measure seq].
    Implicit Arguments cons_R [A measure seq s].

    Program Fixpoint view_R (A : Type) (measure : A -> v) (s : v) (t : fingertree measure s) {struct t} : 
      View_R measure fingertree := 
      match t with
        | Empty => nil_R 
        | Single x => cons_R Empty x
        | Deep pr st' t' sf => 
          match sf with
            | One x => match view_R t' with
                         | nil_R => cons_R (digit_to_tree _ pr) x
                         | cons_R st' t' a => cons_R (Deep pr t' (node_to_digit a)) x
                       end
            | y => cons_R (Deep pr t' (digit_liat y)) (digit_last y)
          end
      end.

    Next Obligation of view_R.
    Proof.
      intros.
      destruct sf ; simpl in * ; auto.
      apply (H a). auto.
    Defined.

    Lemma view_R_case : forall A (measure : A -> v) (s : v) (t : fingertree measure s), view_R t = nil_R \/ 
      exists st', exists t' : fingertree measure st', exists x,  view_R t = cons_R t' x.
    Proof.
      intros.
      destruct (view_R t) ; simpl ; intuition ; auto.
      right.
      exists s0 ; exists f ; exists a ; auto.
    Qed.

    Lemma view_R_nil : forall A (measure : A -> v) (s : v) (t : fingertree measure s), 
      view_R t = nil_R -> s = epsilon.
    Proof.
      intros.
      induction t ; simpl in * ; try discriminate ; auto.
      destruct r ; simpl  in * ; try discriminate ; auto.
      program_simpl ; destruct (view_R t) ; simpl  in * ; try discriminate ; auto.
    Qed.

    Lemma view_R_cons : forall A (measure : A -> v) (s : v) (t : fingertree measure s), 
      forall st' (t' : fingertree measure st') x, view_R t = cons_R t' x -> s = st' cdot measure x.
    Proof.
      induction t ; program_simpl ; intros ; simpl in * ; try discriminate ; auto.
      simpl ; monoid_tac ; auto.
      program_simpl ; destruct r ; simpl  in * ; try discriminate ; monoid_tac ; auto ; 
        try (inversion H ; subst ; simpl ; monoid_tac ; auto).

      destruct (view_R_case t).
      rewrite H0 in H.
      inversion H ; subst ; simpl ; monoid_tac ; auto. 
      rewrite (view_R_nil _ H0) ; monoid_tac ; auto.

      destruct H0 as [st [t'' [x'' H0]]].
      rewrite H0 in H ; simpl.
      inversion H ; simpl ; subst.
      rewrite (IHt _ _ _ H0).
      monoid_tac ; f_equal.
      rewrite <- nodeMeasure_digits ; auto.
    Qed.

    Program Definition deep_R (A : Type) (measure : A -> v) (pr : digit A) (s : v) (mid : fingertree (node_measure measure) s) (d : option (digit A))
      : fingertree measure (digit_measure measure pr cdot s cdot option_digit_measure measure d) :=
      match d with
        | Some sf => Deep pr mid sf
        | None =>  
          match view_R mid with
            | nil_R => digit_to_tree _ pr
            | cons_R sm' m' a => Deep pr m' (node_to_digit a)
          end
      end.

    Obligation Tactic := program_simpl ; monoid_tac ; auto.
    
    Next Obligation.
    Proof.
      intros.
      unfold option_digit_measure ; simpl.
      cut(s = epsilon) ; intros ; subst.
      monoid_tac ; auto.
      apply (view_R_nil mid) ; auto.
    Qed.

    Next Obligation.
    Proof.
      intros.
      unfold option_digit_measure, option_measure.
      monoid_tac.
      destruct mid ; simpl in Heq_anonymous ; try discriminate.
      inversion Heq_anonymous ; subst ; simpl ; monoid_tac ; auto.
      f_equal.
      destruct x ; simpl ; monoid_tac ; auto.
      program_simpl ; auto.
      program_simpl ; auto.
      f_equal.
      monoid_tac.

      repeat rewrite <- nodeMeasure_digits ; simpl ; monoid_tac ; auto.

      destruct r ; simpl ; monoid_tac ; auto.
      destruct (view_R_case mid).
      rewrite H in Heq_anonymous ; simpl in * ; auto.

      inversion Heq_anonymous ; subst ; simpl ; auto ; clear Heq_anonymous.
      f_equal ; auto.
      rewrite (view_R_nil _ H).
      monoid_tac ; rewrite nodeMeasure_digits ; auto.

      destruct H as [st' [t' [x H]]].
      rewrite H in Heq_anonymous ; simpl.
      inversion Heq_anonymous.
      subst.
      rewrite monoid_assoc.
      f_equal.
      repeat rewrite <- nodeMeasure_digits ; simpl ; monoid_tac ; auto.
      rewrite <- monoid_assoc.
      f_equal.
      rewrite (view_R_cons _ H) ; auto.

      inversion Heq_anonymous ; simpl ; subst ; monoid_tac ; repeat rewrite nodeMeasure_digits ; auto.
      inversion Heq_anonymous ; simpl ; subst ; monoid_tac ; repeat rewrite nodeMeasure_digits ; auto.
      inversion Heq_anonymous ; simpl ; subst ; monoid_tac ; repeat rewrite nodeMeasure_digits ; auto.
    Qed.
  
  End view_R.
  (* end hide *)
  
  (** *** Back to normal
     %\def\coqdocindent#1{\noindent\kern#1\hskip-1em}\label{sec:Back_To_Normal}%
     We are now ready to implement regular deque viewing operations on our Finger Trees. 
     We do not need recursion on the trees here, so we can define the operations for
     a fixed element type, measure function and measure index.
     *)
  
  Section View.
    Variables (A : Type) (measure : A -> v) (s : v).

    (** We define an [isEmpty] predicate for some operations will be partial, 
       i.e. defined only for non-empty [fingertree] objects. We do not match directly on the 
       object to maintain the abstraction from the implementation. *)

    Definition isEmpty (t : fingertree measure s) := 
      match view_L t with nil_L => True | _ => False end.
    
    (** Emptiness is decidable. *)
    
    Definition isEmpty_dec (t : fingertree measure s) :
      { isEmpty t } + { ~ isEmpty t }.
    (* begin hide *)
      intros.
      unfold isEmpty.
      destruct (view_L t) ; simpl ; 
        intuition.
    Defined.
    
    (* end hide *)

    (** The obvious operations are definable, we show the [liat] operation dual to [tail]. 
       Here we return the index along with the fingertree in a dependent pair of type 
       [{s : v & fingertree measure s}], which corresponds
       more closely to the view that the cached measure is really data, not only an index used to refine a datatype.
       The pairing of a tree [t] with its measure [m] is denoted [m :| t] and reads 
       "[m] measures [t]".
       *)  
    (* begin hide *)
    Obligation Tactic := idtac.

    Program Definition head (t : fingertree measure s | ~ isEmpty t) : A :=
      match view_L t with
        | cons_L hd _ _ => hd
        | nil_L => !
      end.
    Next Obligation.
    Proof.
      intros.
      destruct t ; unfold isEmpty in * ;  simpl in *.
      subst.
      destruct (view_L x) ; simpl in * ; auto ; program_simpl ; try discriminate.
    Qed.
    
    Notation " x :| t " := (existT _ x t) (at level 20).
    Program Definition tail (t : fingertree measure s | ~ isEmpty t) : { s' : v & fingertree measure s' } :=
      match view_L t with
        | cons_L _ st' t' => st' :| t'
        | nil_L => !
      end.

    Next Obligation.
    Proof.
      intros.
      unfold isEmpty in * ; program_simpl.
      rewrite <- Heq_anonymous in H ; simpl in H ; auto.
    Qed.

    Program Definition last (t : fingertree measure s | ~ isEmpty t) : A :=
      match view_R t with
        | cons_R _ _ x => x
        | nil_R => !
      end.

    Next Obligation.
    Proof.
      intros.
      unfold isEmpty in * ; program_simpl.
      destruct t ; simpl in * ; try discriminate ; auto.
      destruct r ; simpl in * ; try discriminate ; auto.
      destruct (view_R t) ; simpl in * ; try discriminate.
    Qed.
    (* end hide *)

    Program Definition liat (t : fingertree measure s |
      ~ isEmpty t) : { s' : v & fingertree measure s' } := 
      match view_R t with
        | nil_R => ! | cons_R st' t' last => st' :| t' 
      end.
    (* begin hide *)
    Next Obligation.
    Proof.
      intros.
      unfold isEmpty in * ; program_simpl.
      destruct t ; simpl in * ; try discriminate ; auto.
      destruct r ; simpl in * ; try discriminate ; auto.
      destruct (view_R t) ; simpl in * ; try discriminate.
    Qed.
    (* end hide *)
  End View.  

  (* begin hide *)
  Section isEmpty_Facts.

   Lemma isEmpty_epsilon : forall (A : Type) (measure : A -> v) (s : v) (t : fingertree measure s), 
      isEmpty t -> s = epsilon.
    Proof.
      intros; induction t; simpl; auto with exfalso.
      unfold isEmpty in H ; simpl in H ; auto.
      destruct l ; simpl ; auto ; try contradiction.
      program_simpl ; destruct (view_L t) ; simpl ; try contradiction.
    Qed.
    
    Lemma not_isEmpty_Deep : forall (A : Type) (measure : A -> v) pr sm 
      (m : fingertree (node_measure measure) sm) sf, 
      ~ isEmpty (Deep pr m sf).
    Proof.
      intros.
      unfold isEmpty.
      destruct pr ; simpl in * ; auto ; try discriminate.
      destruct (view_L m0) ; simpl in * ; auto ; try discriminate.
    Qed.
    
    Lemma isEmpty_JMeq_Empty : forall (A : Type) (measure : A -> v) (s : v) (t : fingertree measure s), 
      isEmpty t -> JMeq t (Empty (measure:=measure)).
    Proof.
      intros.
      induction t.
      apply JMeq_refl.
      simpl in H ; try contradiction.
      program_simpl ; pose (not_isEmpty_Deep l t r). 
      elim n.
      assumption.
    Qed.
    
    Lemma isEmpty_Empty : forall (A : Type) (measure : A -> v) (t : fingertree measure epsilon), 
      isEmpty t -> t = Empty.
    Proof.
      intros.
      pose (isEmpty_JMeq_Empty t H).
      apply JMeq_eq ; auto.
    Qed.
  End isEmpty_Facts.

  Section Cat.
  (** Concatenation still using digits. *)
    
  (* Too long to check interactively (2min) *)
    Program Fixpoint appendTree0 (A : Type) (measure : A -> v) (xsm : v) (xs : fingertree measure xsm)
      (ysm : v) (ys : fingertree measure ysm) {struct xs} : fingertree measure (xsm cdot ysm) :=
      match xs in fingertree _ xsm, ys in fingertree _ ysm return fingertree measure (xsm cdot ysm) with
        | Empty, ys => ys
        | xs, Empty => xs
        | Single x, ys => add_left x ys
        | xs, Single y => add_right xs y
        | Deep pr xsm xs sf, Deep pr' ysm ys sf' => 
          let f := 
            match sf return fingertree (node_measure measure) (xsm cdot digit_measure measure sf cdot digit_measure measure pr' cdot ysm) with
              | One a => 
                match pr' return fingertree (node_measure measure) (xsm cdot digit_measure measure (One a) cdot digit_measure measure pr' cdot ysm) with
                  | One b => appendTree1 xs (node2 measure a b) ys
                  | Two b c => appendTree1 xs (node3 measure a b c) ys
                  | Three b c d => appendTree2 xs (node2 measure a b) (node2 measure c d) ys
                  | Four b c d e => appendTree2 xs (node3 measure a b c) (node2 measure d e) ys
                end
              | Two a b =>
                match pr' return fingertree (node_measure measure) (xsm cdot digit_measure measure (Two a b) cdot digit_measure measure pr' cdot ysm) with
                  | One c => appendTree1 xs (node3 measure a b c) ys
                  | Two c d => appendTree2 xs (node2 measure a b) (node2 measure c d) ys
                  | Three c d e => appendTree2 xs (node3 measure a b c) (node2 measure d e) ys
                  | Four c d e f => appendTree2 xs (node3 measure a b c) (node3 measure d e f) ys
                end
              | Three a b c =>
                match pr' return fingertree (node_measure measure) (xsm cdot digit_measure measure (Three a b c) cdot digit_measure measure pr' cdot ysm) with
                  | One d => appendTree2 xs (node2 measure a b) (node2 measure c d) ys
                  | Two d e => appendTree2 xs (node3 measure a b c) (node2 measure d e) ys
                  | Three d e f => appendTree2 xs (node3 measure a b c) (node3 measure d e f) ys
                  | Four d e f g => appendTree3 xs (node3 measure a b c) (node2 measure d e) (node2 measure f g) ys
                end
              | Four a b c d =>
                match pr' return fingertree (node_measure measure) (xsm cdot digit_measure measure (Four a b c d) cdot digit_measure measure pr' cdot ysm) with
                  | One e => appendTree2 xs (node3 measure a b c) (node2 measure d e) ys
                  | Two e f => appendTree2 xs (node3 measure a b c) (node3 measure d e f) ys
                  | Three e f g => appendTree3 xs (node3 measure a b c) (node2 measure d e) (node2 measure f g) ys
                  | Four e f g h => appendTree3 xs (node3 measure a b c) (node3 measure d e f) (node2 measure g h) ys
                end
            end
            in
            Deep pr f sf'
      end

    with appendTree1 (A : Type) (measure : A -> v) (xsm : v) (xs : fingertree measure xsm) (x : A)
      (ysm : v) (ys : fingertree measure ysm) {struct xs} : fingertree measure (xsm cdot measure x cdot ysm) :=
      match  xs in fingertree _ xsm, ys in fingertree _ ysm return fingertree measure (xsm cdot measure x cdot ysm) with
        | Empty, ys => add_left x ys
        | xs, Empty => add_right xs x
        | Single x', ys => add_left x' (add_left x ys)
        | xs, Single y' => add_right (add_right xs x) y'
        | Deep pr xsm xs dl, Deep dr ysm ys sf' => 
          let addDigits1 := 
            match dl return fingertree (node_measure measure) (xsm cdot digit_measure measure dl cdot measure x cdot digit_measure measure dr cdot ysm) with
              | One a => 
                match dr return fingertree (node_measure measure) (xsm cdot digit_measure measure (One a) cdot measure x cdot digit_measure measure dr cdot ysm) with 
                  | One b => appendTree1 xs (node3 measure a x b) ys
                  | Two b c => appendTree2 xs (node2 measure a x) (node2 measure b c) ys
                  | Three b c d => appendTree2 xs (node3 measure a x b) (node2 measure c d) ys
                  | Four b c d e => appendTree2 xs (node3 measure a x b) (node3 measure c d e) ys
                end
              | Two a b =>
                match dr return fingertree (node_measure measure) (xsm cdot digit_measure measure (Two a b) cdot measure x cdot digit_measure measure dr cdot ysm) with 
                  | One c => appendTree2 xs (node2 measure a b) (node2 measure x c) ys
                  | Two c d => appendTree2 xs (node3 measure a b x) (node2 measure c d) ys
                  | Three c d e => appendTree2 xs (node3 measure a b x) (node3 measure c d e) ys
                  | Four c d e f => appendTree3 xs (node3 measure a b x) (node2 measure c d) (node2 measure e f) ys
                end
              | Three a b c =>
                match dr return fingertree (node_measure measure) (xsm cdot digit_measure measure (Three a b c) cdot measure x cdot digit_measure measure dr cdot ysm) with 
                  | One d => appendTree2 xs (node3 measure a b c) (node2 measure x d) ys
                  | Two d e => appendTree2 xs (node3 measure a b c) (node3 measure x d e) ys
                  | Three d e f => appendTree3 xs (node3 measure a b c) (node2 measure x d) (node2 measure e f) ys
                  | Four d e f g => appendTree3 xs (node3 measure a b c) (node3 measure x d e) (node2 measure f g) ys
                end
              | Four a b c d =>
                match dr return fingertree (node_measure measure) (xsm cdot digit_measure measure (Four a b c d) cdot measure x cdot digit_measure measure dr cdot ysm) with 
                  | One e => appendTree2 xs (node3 measure a b c) (node3 measure d x e) ys
                  | Two e f => appendTree3 xs (node3 measure a b c) (node2 measure d x) (node2 measure e f) ys
                  | Three e f g => appendTree3 xs (node3 measure a b c) (node3 measure d x e) (node2 measure f g) ys
                  | Four e f g h => appendTree3 xs (node3 measure a b c) (node3 measure d x e) (node3 measure f g h) ys
                end
            end
            in Deep pr addDigits1 sf'
      end
      
    with appendTree2 (A : Type) (measure : A -> v) (xsm : v) (xs : fingertree measure xsm) (x y : A) (ysm : v) (ys : fingertree measure ysm) {struct xs} 
      : fingertree measure (xsm cdot measure x cdot measure y cdot ysm) :=
      match xs in fingertree _ xsm, ys in fingertree _ ysm return fingertree measure (xsm cdot measure x cdot measure y cdot ysm) with
        | Empty, ys => add_left x (add_left y ys)
        | xs, Empty => add_right (add_right xs x) y
        | Single x', ys => add_left x' (add_left x (add_left y ys))
        | xs, Single y' => add_right (add_right (add_right xs x) y) y'
        | Deep pr xsm xs dl, Deep dr ysm ys sf' => 
          let addDigits2 :=
            match dl return fingertree (node_measure measure) (xsm cdot digit_measure measure dl cdot measure x cdot measure y cdot digit_measure measure dr cdot ysm) with 
              | One a => 
                match dr return fingertree (node_measure measure) (xsm cdot digit_measure measure (One a) cdot measure x cdot measure y cdot digit_measure measure dr cdot ysm) with 
                  | One b => appendTree2 xs (node2 measure a x) (node2 measure y b) ys
                  | Two b c => appendTree2 xs (node3 measure a x y) (node2 measure b c) ys
                  | Three b c d => appendTree2 xs (node3 measure a x y) (node3 measure b c d) ys
                  | Four b c d e => appendTree3 xs (node3 measure a x y) (node2 measure b c) (node2 measure d e) ys
                end
              | Two a b =>
                match dr return fingertree (node_measure measure) (xsm cdot digit_measure measure (Two a b) cdot measure x cdot measure y cdot digit_measure measure dr cdot ysm) with 

                  | One c => appendTree2 xs (node3 measure a b x) (node2 measure y c) ys
                  | Two c d => appendTree2 xs (node3 measure a b x) (node3 measure y c d) ys
                  | Three c d e => appendTree3 xs (node3 measure a b x) (node2 measure y c) (node2 measure d e) ys
                  | Four c d e f => appendTree3 xs (node3 measure a b x) (node3 measure y c d) (node2 measure e f) ys
                end
              | Three a b c =>
                match dr return fingertree (node_measure measure) (xsm cdot digit_measure measure (Three a b c) cdot measure x cdot measure y cdot digit_measure measure dr cdot ysm) with 

                  | One d => appendTree2 xs (node3 measure a b c) (node3 measure x y d) ys
                  | Two d e => appendTree3 xs (node3 measure a b c) (node2 measure x y) (node2 measure d e) ys
                  | Three d e f => appendTree3 xs (node3 measure a b c) (node3 measure x y d) (node2 measure e f) ys
                  | Four d e f g => appendTree3 xs (node3 measure a b c) (node3 measure x y d) (node3 measure e f g) ys
                end
              | Four a b c d =>
                match dr return fingertree (node_measure measure) (xsm cdot digit_measure measure (Four a b c d) cdot measure x cdot measure y cdot digit_measure measure dr cdot ysm) with 

                  | One e => appendTree3 xs (node3 measure a b c) (node2 measure d x) (node2 measure y e) ys
                  | Two e f => appendTree3 xs (node3 measure a b c) (node3 measure d x y) (node2 measure e f) ys
                  | Three e f g => appendTree3 xs (node3 measure a b c) (node3 measure d x y) (node3 measure e f g) ys
                  | Four e f g h => appendTree4 xs (node3 measure a b c) (node3 measure d x y) (node2 measure e f) (node2 measure g h) ys
                end
            end
            in Deep pr addDigits2 sf'
      end


    with appendTree3 (A : Type) (measure : A -> v) (xsm : v) (xs : fingertree measure xsm) (x y z : A) (ysm : v) (ys : fingertree measure ysm) {struct xs}
      : fingertree measure (xsm cdot measure x cdot measure y cdot measure z cdot ysm) :=
      match xs in fingertree _ xsm, ys in fingertree _ ysm return fingertree measure (xsm cdot measure x cdot measure y cdot measure z cdot ysm) with
        | Empty, ys => add_left x (add_left y (add_left z ys))
        | xs, Empty => add_right (add_right (add_right xs x) y) z
        | Single x', ys => add_left x' (add_left x (add_left y (add_left z ys)))
        | xs, Single y' => add_right (add_right (add_right (add_right xs x) y) z) y'
        | Deep pr xsm xs dl, Deep dr ysm ys sf' =>
          let addDigits3 := 
            match dl return fingertree (node_measure measure) (xsm cdot digit_measure measure dl cdot measure x cdot measure y cdot measure z cdot digit_measure measure dr cdot ysm) with 
              | One a => 
                match dr return fingertree (node_measure measure) (xsm cdot digit_measure measure (One a) cdot measure x cdot measure y cdot measure z cdot digit_measure measure dr cdot ysm) with 
                  | One b => appendTree2 xs (node3 measure a x y) (node2 measure z b) ys
                  | Two b c => appendTree2 xs (node3 measure a x y) (node3 measure z b c) ys
                  | Three b c d => appendTree3 xs (node3 measure a x y) (node2 measure z b) (node2 measure c d) ys
                  | Four b c d e => appendTree3 xs (node3 measure a x y) (node3 measure z b c) (node2 measure d e) ys
                end
              | Two a b =>
                match dr return fingertree (node_measure measure) (xsm cdot digit_measure measure (Two a b) cdot measure x cdot measure y cdot measure z cdot digit_measure measure dr cdot ysm) with 
                  | One c => appendTree2 xs (node3 measure a b x) (node3 measure y z c) ys
                  | Two c d => appendTree3 xs (node3 measure a b x) (node2 measure y z) (node2 measure c d) ys
                  | Three c d e => appendTree3 xs (node3 measure a b x) (node3 measure y z c) (node2 measure d e) ys
                  | Four c d e f => appendTree3 xs (node3 measure a b x) (node3 measure y z c) (node3 measure d e f) ys
                end
              | Three a b c =>
                match dr return fingertree (node_measure measure) (xsm cdot digit_measure measure (Three a b c) cdot measure x cdot measure y cdot measure z cdot digit_measure measure dr cdot ysm) with 
                  | One d => appendTree3 xs (node3 measure a b c) (node2 measure x y) (node2 measure z d) ys
                  | Two d e => appendTree3 xs (node3 measure a b c) (node3 measure x y z) (node2 measure d e) ys
                  | Three d e f => appendTree3 xs (node3 measure a b c) (node3 measure x y z) (node3 measure d e f) ys
                  | Four d e f g => appendTree4 xs (node3 measure a b c) (node3 measure x y z) (node2 measure d e) (node2 measure f g) ys
                end
              | Four a b c d =>
                match dr return fingertree (node_measure measure) (xsm cdot digit_measure measure (Four a b c d) cdot measure x cdot measure y cdot measure z cdot digit_measure measure dr cdot ysm) with 
                  | One e => appendTree3 xs (node3 measure a b c) (node3 measure d x y) (node2 measure z e) ys
                  | Two e f => appendTree3 xs (node3 measure a b c) (node3 measure d x y) (node3 measure z e f) ys
                  | Three e f g => appendTree4 xs (node3 measure a b c) (node3 measure d x y) (node2 measure z e) (node2 measure f g) ys
                  | Four e f g h => appendTree4 xs (node3 measure a b c) (node3 measure d x y) (node3 measure z e f) (node2 measure g h) ys
                end
            end
            in Deep pr addDigits3 sf'
      end

    with appendTree4 (A : Type) (measure : A -> v) (xsm : v) (xs : fingertree measure xsm) (x y z w : A) (ysm : v) (ys : fingertree measure ysm) {struct xs} 
      : fingertree measure (xsm cdot measure x cdot measure y cdot measure z cdot measure w cdot ysm) :=
      match xs in fingertree _ xsm, ys in fingertree _ ysm return fingertree measure (xsm cdot measure x cdot measure y cdot measure z cdot measure w cdot ysm) with
        | Empty, ys => add_left x (add_left y (add_left z (add_left w ys)))
        | xs, Empty => add_right (add_right (add_right (add_right xs x) y) z) w 
        | Single x', ys => add_left x' (add_left x (add_left y (add_left z (add_left w ys))))
        | xs, Single y' => add_right (add_right (add_right (add_right (add_right xs x) y) z) w) y'
        | Deep pr xsm xs dl, Deep dr ysm ys sf' =>
          let addDigits4 := 
            match dl return fingertree (node_measure measure) (xsm cdot digit_measure measure dl cdot measure x cdot measure y cdot measure z cdot measure w cdot digit_measure measure dr cdot ysm) with 
              | One a => 
                match dr return fingertree (node_measure measure) (xsm cdot digit_measure measure (One a) cdot measure x cdot measure y cdot measure z cdot measure w cdot digit_measure measure dr cdot ysm) with 

                  | One b => appendTree2 xs (node3 measure a x y) (node3 measure z w b) ys
                  | Two b c => appendTree3 xs (node3 measure a x y) (node2 measure z w) (node2 measure b c) ys
                  | Three b c d => appendTree3 xs (node3 measure a x y) (node3 measure z w b) (node2 measure c d) ys
                  | Four b c d e => appendTree3 xs (node3 measure a x y) (node3 measure z w b) (node3 measure c d e) ys
                end
              | Two a b =>
                match dr return fingertree (node_measure measure) (xsm cdot digit_measure measure (Two a b) cdot measure x cdot measure y cdot measure z cdot measure w cdot digit_measure measure dr cdot ysm) with 

                  | One c => appendTree3 xs (node3 measure a b x) (node2 measure y z) (node2 measure w c) ys
                  | Two c d => appendTree3 xs (node3 measure a b x) (node3 measure y z w) (node2 measure c d) ys
                  | Three c d e => appendTree3 xs (node3 measure a b x) (node3 measure y z w) (node3 measure c d e) ys
                  | Four c d e f => appendTree4 xs (node3 measure a b x) (node3 measure y z w) (node2 measure c d) (node2 measure e f) ys
                end
              | Three a b c =>
                match dr return fingertree (node_measure measure) (xsm cdot digit_measure measure (Three a b c) cdot measure x cdot measure y cdot measure z cdot measure w cdot digit_measure measure dr cdot ysm) with 

                  | One d => appendTree3 xs (node3 measure a b c) (node3 measure x y z) (node2 measure w d) ys
                  | Two d e => appendTree3 xs (node3 measure a b c) (node3 measure x y z) (node3 measure w d e) ys
                  | Three d e f => appendTree4 xs (node3 measure a b c) (node3 measure x y z) (node2 measure w d) (node2 measure e f) ys
                  | Four d e f g => appendTree4 xs (node3 measure a b c) (node3 measure x y z) (node3 measure w d e) (node2 measure f g) ys
                end
              | Four a b c d =>
                match dr return fingertree (node_measure measure) (xsm cdot digit_measure measure (Four a b c d) cdot measure x cdot measure y cdot measure z cdot measure w cdot digit_measure measure dr cdot ysm) with 

                  | One e => appendTree3 xs (node3 measure a b c) (node3 measure d x y) (node3 measure z w e) ys
                  | Two e f => appendTree4 xs (node3 measure a b c) (node3 measure d x y) (node2 measure z w) (node2 measure e f) ys
                  | Three e f g => appendTree4 xs (node3 measure a b c) (node3 measure d x y) (node3 measure z w e) (node2 measure f g) ys
                  | Four e f g h => appendTree4 xs (node3 measure a b c) (node3 measure d x y) (node3 measure z w e) (node3 measure f g h) ys
                end
            end in Deep pr addDigits4 sf'
      end.
  End Cat.
  (* end hide *)
  (** ** Catenation & splitting, dependently
     We can also define catenation using a dependent type which clearly
     states the function's specification. The implementation is the same as the one of Hinze & Paterson, 
     except we proved the 100 obligations generated by %\Program% concerning measures.
     The five mutually recursive functions hidden here which define [app] have
     the particularity of being quite big because they
     implement a specialization of concatenation for each combination of the digits at the 
     right of the left tree and the left of the right tree.
     Hinze & Paterson even recommend to produce the 200 lines long definition automatically to prevent
     mistakes. Here the definition is checked directly: the type itself expresses
     that we did not mess up the obvious property of [app] on measures.
     %\def\coqdocindent#1{\noindent\kern#1}\label{def:app}%
     *)
  
  Definition app : forall (A : Type) (measure : A -> v)
    (xs : v) (x : fingertree measure xs) 
    (ys : v) (y : fingertree measure ys),
    fingertree measure (xs cdot ys).
  (* begin hide *)
    exact appendTree0.
  Defined.
  (* end hide *)  
  Notation " x +:+ y " := (app x y) (at level 20).
  (* begin hide *)
  Section Get.

    Section Nodes.
      Variables (A : Type) (measure : A -> v).
      Variables (p : v -> bool).

      Notation " 'lparr' x 'rparr' " := (measure x) (x ident, no associativity).
      
      Program Definition get_node (n : node measure)
        (i : v | p i = false /\ p (i cdot node_measure measure n) = true) : 
        { (s, x) : v * A | p s = false /\ p (s cdot lparr x rparr) = true } :=
        match n with
          | Node2 x y _ => 
            let i' := i cdot lparr x rparr in
              if dec (p i') then (i, x) else (i', y)
          | Node3 x y z _ =>
            let i' := i cdot lparr x rparr in
              if dec (p i') then (i, x)
              else 
                let i'' := i' cdot lparr y rparr in
                  if dec (p i'') then (i', y)
                  else (i'', z)
        end.

    End Nodes.

    Section Trees.
      
      Program Fixpoint get_tree (A : Type) (measure : A -> v) (p : v -> bool)
        (s : v) (t : fingertree measure s) (pr : unit | ~ isEmpty t)
        (i : v | p i = false /\ p (i cdot s) = true)
        {struct t} : 
        { (s, x) : v * A | p s = false /\ p (s cdot measure x) = true } :=
        match t with
          | Empty => !
          | Single x => (i, x)
          | Deep pr smid mid sf => 
            let vpr := i cdot (digit_measure measure pr) in
            if dec (p vpr) then get_digit measure p pr i
            else let vpm := vpr cdot smid in
              if dec (p vpm) then 
                let '(mls, x) := get_tree p mid tt vpr in
                  get_node p x mls
              else
                let vsf := vpm cdot (digit_measure measure sf) in
                  get_digit measure p sf vpm
        end.

      Solve Obligations using  program_simpl ; intuition ; simpl in * ; subst ; simpl_monoid ; auto.
    
      Next Obligation.
      Proof.
        intros.
        simpl_monoid.
        rewrite H0 in H ; discriminate.
      Qed.

      Lemma isEmpty_empty : forall (A : Type) (measure : A -> v), isEmpty (@Empty A measure).
      Proof.
        intros.
        unfold isEmpty ; simpl ; intros.
        auto.
      Qed.

      Hint Resolve isEmpty_empty.

      Next Obligation.
      Proof.
        intros.
        simpl_JMeq.
        subst.
        destruct mid ; unfold isEmpty in H4 ; simpl in H4 ; try elim H4; program_simpl ; auto.
        rewrite monoid_id_r in H0.
        rewrite H0 in H ; discriminate.
        destruct l ; simpl ; auto.
        destruct (view_L mid) ; simpl ; auto.
      Qed.

    End Trees.

  End Get.

  Section Split.
  (* end hide *)

  (** %\def\coqdocindent#1{\noindent\kern#1\hskip-2em}%The last and most interesting operation from the specifier's point of view, is
       splitting a tree by a predicate on its measure. We begin by splitting a node.
    *)
    
    Section Nodes.
      Variables (A : Type) (measure : A -> v).
      Variables (p : v -> bool) (i : v).
      (* begin hide *)
      Notation " 'lparr' x 'rparr' " := (measure x) (x ident, no associativity).

      (* end hide *)
      
      (** We split a node [n] by finding where some predicate [p] on measures turns to [true], 
         starting with an initial measure [i] and accumulating the measures of subtrees from left to right.
         We simply copy the invariant given by %\citet*{hinze:FingerTrees}% here, there is nothing to change, 
         we only add the corresponding property on the measure which clearly generalizes 
         the [to_list] equation. The code is also a direct translation from Haskell to Russell except 
         we use a regular tuple instead of a custom [split] datatype.
         We have also defined a [split_digit] function with the same specification.

         %\splitnodefig%
         *)
      (* begin hide *)
      Program Definition split_node (n : node measure) : 
      { (l, x, r) : option (digit A) * A * option (digit A) | 
        let ls := option_digit_measure measure l in
        let rs := option_digit_measure measure r in
        node_measure measure n = ls cdot lparr x rparr cdot rs /\
        (l = None \/ p (i cdot ls) = false) /\
        (r = None \/ p (i cdot ls cdot lparr x rparr) = true)} :=
      match n with
        | Node2 x y _ => 
          let i' := i cdot lparr x rparr in
          if dec (p i') then (None, x, Some (One y))
          else (Some (One x), y, None)
        | Node3 x y z _ =>
          let i' := i cdot lparr x rparr in
          let i'' := i' cdot lparr y rparr in
          if dec (p i') then (None, x, Some (Two y z))
          else 
            if dec (p i'') then
              (Some (One x), y, Some (One z))
            else 
              (Some (Two x y), z, None)
      end.

      (* end hide *)
    End Nodes.

    (** The interesting case is for trees, as usual. Instead of returning a tuple,
       we use a dependent [tree_split] inductive which directly captures 
       the invariant that a split is a decomposition of a [fingertree] preserving measures. We also put
       the invariants on the left and right trees, which can be used by clients to prove properties about
       their code. 
       This is one of the most distinctive parts of this work: we derive not only reusable code but
       also reusable proofs using rich types. Indeed, [split_tree] can be seen as a proof combinator, 
       turning a property on a measure and monoid to a property on words on this monoid.
       *)

    Section Trees.
      (* begin hide *)
      Obligation Tactic := splitTac.
      (* end hide *)
      Variable p : v -> bool.
      
      Inductive tree_split (A : Type) (measure : A -> v) 
        (i : v) : v -> Type :=
        mkTreeSplit : forall (xsm : v) (xs : fingertree measure xsm |
          isEmpty xs \/ p (i cdot xsm) = false)
        (x : A) (ysm : v) (ys : fingertree measure ysm |
          isEmpty ys \/ p (i cdot xsm cdot measure x) = true),
        tree_split measure i (xsm cdot measure x cdot ysm).
      
      (** This inductive combines both subsets and dependent inductive types, but we can still
         write our code as usual.
         %\extended{In the definition below, we use a [pr] argument of [unit] type to carry a proposition on [t] to
         work around the structural recursion criterion of Coq which does not work ``up-to subsets''
         whereas a type-based criterion would accept the more natural definition.}%
         Approximately 100 lines of proof are necessary to discharge the generated obligations.

         %\label{def:split_tree}\splittreefig{}% *)
      (* begin hide *)
      (*
         We can of course define a wrapper to get rid of the [unit] argument.}%
         *)

      Program Definition option_digit_to_tree (A : Type) (measure : A -> v) (d : option (digit A)) :
        fingertree measure (option_digit_measure measure d) :=
        match d with Some x => digit_to_tree measure x | None => Empty end.

      Obligation Tactic := program_simpl ; intros ; try splitTac ; simpl ; monoid_tac ; auto.

      Program Fixpoint split_tree' (A : Type) (measure : A -> v)
        (i s : v) (t : fingertree measure s) (pr : unit | ~ isEmpty t)
        {struct t} : tree_split measure i s :=
        match t with
        | Empty => !
        | Single x => mkTreeSplit Empty x Empty
        | Deep pr smid mid sf => 
          let vpr := i cdot (digit_measure measure pr) in
          if dec (p vpr) then
            let '(l, x, r) := split_digit measure p i pr in
              mkTreeSplit (option_digit_to_tree measure l)
                x (deep_L r mid sf)
          else let vpm := vpr cdot smid in
            if dec (p vpm) then
              let 'mkTreeSplit mls ml x mrs mr := split_tree' vpr mid tt in
              let '(l, x, r) := split_node p (vpr cdot mls) x in
                mkTreeSplit (deep_R pr ml l) x (deep_L r mr sf)
            else
              let vsf := vpm cdot (digit_measure measure sf) in
              let '(l, x, r) := split_digit measure p vpm sf in
                mkTreeSplit (deep_R pr mid l) x
                  (option_digit_to_tree measure r)
        end.

      Next Obligation.
      Proof.
        intros.
        program_simpl.
        inversion Heq_t.
        rewrite <- (inj_pair2 H1) in H.
        simpl in * ; elim H.
        compute ; auto.
      Qed.

      Obligation Tactic := program_simpl.
      Next Obligation.
      Proof.
        inversion Heq_t.
        rewrite <- (inj_pair2 H0) in H.
        left.
        compute ; auto.
      Qed.
      
      Next Obligation.
      Proof.
        left ; compute ; auto.
      Qed.

      Next Obligation.
      Proof.
        destruct (split_digit measure p i pr0) ; program_simpl.
        destruct_conjs. simpl_JMeq. autoinjections.
        destruct H2 ; [left | right] ; auto.
        rewrite H1 ; simpl. split.
      Qed.

      Next Obligation.
      Proof.
        destruct (split_digit measure p i pr0). program_simpl.
        reverse ; simplify_dep_elim.
        rewrite H1 in H.
        destruct H2. subst. simpl in *.
        unfold option_digit_measure in *.
        simpl in H ; monoid_tac_in H ; auto.
        destruct H3; auto. subst. monoid_tac_in H. right. now monoid_tac.
        destruct H3; auto. subst. monoid_tac_in H. right. now monoid_tac.
      Qed.

      Next Obligation.
      Proof.
        destruct (split_digit measure p i pr0) ; program_simpl. 
        rewrite H1. monoid_tac. reflexivity.
      Qed.

      Next Obligation.
      Proof.
        destruct (isEmpty_dec mid).
        destruct mid ; unfold isEmpty in i0 ; simpl in i0 ; program_simpl ; auto.
        red ; intros.
        rewrite monoid_id_r in H0.
        rewrite H0 in H ; discriminate.
        destruct l ; simpl ; auto.
        destruct (view_L mid) ; simpl ; auto.
        program_simpl ; assumption.
      Qed.

      Obligation Tactic := idtac.

      Next Obligation.
      Proof.
        intros. subst filtered_var. 
        clear Heq_anonymous split_tree'. subst filtered_var0 vpr vpm. program_simpl.
        right.
        destruct (split_node p ((i cdot digit_measure measure pr0) cdot mls) x).
        simpl in *.
        destruct x1 ; program_simpl.
        destruct_pairs.
        destruct_nondep H2 ; monoid_tac_in H2 ;auto.
        assert (He:=isEmpty_epsilon _ H7).
        subst mls.
        destruct H5 ; monoid_tac_in H5 ; monoid_tac ; auto.
        subst o0.
        simpl in * ; monoid_tac ; auto.
        
        destruct H5 ; monoid_tac_in H7 ; monoid_tac ; auto.
        subst o0.
        simpl in * ; monoid_tac ; auto.
        
        monoid_tac_in H5 ; auto.
      Defined.

      Next Obligation.
      Proof.
        intros. subst filtered_var.
        clear Heq_anonymous split_tree'. subst filtered_var0 vpr vpm. program_simpl.
        right.
        destruct (split_node p ((i cdot digit_measure measure pr0) cdot mls) x).
        simpl in *.
        destruct x1 ; program_simpl.
        monoid_tac.
        destruct_pairs.
        destruct H6 ; monoid_tac_in H6 ;auto.
        subst o.
        simpl in * ; monoid_tac_in H4.
        rewrite <- H4.
        destruct_nondep H1.
        assert (He:=isEmpty_epsilon _ H6).
        subst mrs ; clear H6.
        monoid_tac_in H0 ; auto.
        rewrite <- H6 ; monoid_tac ; auto.
      Defined.

      Next Obligation.
      Proof.
        intros. subst filtered_var.
        clear split_tree' Heq_anonymous. subst filtered_var0 vpr vpm. program_simpl.
        destruct (split_node p ((i cdot digit_measure measure pr0) cdot mls) x).
        simpl in *.
        destruct x1 as [[l' x'] r'].
        inversion Heq_anonymous0 ; subst l x0 r ; clear Heq_anonymous0.
        monoid_tac.
        program_simpl ; destruct_pairs.
        rewrite H4.
        monoid_tac ; reflexivity.
      Defined.

      Obligation Tactic := program_simpl.

      Next Obligation.
      Proof.
        destruct (split_digit measure p
          ((i cdot digit_measure measure pr0) cdot smid) sf).
        destruct x0 ; simpl in * ; program_simpl.
        right.
        destruct_pairs.
        unfold option_digit_measure in *.
        destruct H3 as [H3|H3] ; subst ; try monoid_tac_in H3 ; auto.
        simpl in H2; monoid_tac_in H2.
        simpl ; monoid_tac.
        monoid_tac_in H0 ; auto.
      Qed.
      
      Next Obligation.
      Proof.
        destruct (split_digit measure p
          ((i cdot digit_measure measure pr0) cdot smid) sf).
        destruct x0 ; simpl in * ; program_simpl.
        monoid_tac.
        destruct_pairs.
        destruct H4 as [H4|H4] ; subst ; try monoid_tac_in H4 ; auto.
        left ; simpl. split.
      Qed.

      Next Obligation.
      Proof.
        destruct (split_digit measure p
          ((i cdot digit_measure measure pr0) cdot smid) sf).
        destruct x0 ; simpl in * ; program_simpl.
        monoid_tac.
        do 2 f_equal.
        rewrite <- H2.
        auto.
      Qed.

      Program Definition split_tree (A : Type) (measure : A -> v)
        (i s : v) (t : fingertree measure s | ~ isEmpty t) :
        tree_split measure i s := split_tree' i t tt.
      (* end hide *)
    End Trees.
  (* begin hide *)
  End Split.
  (* end hide *)

  (** This concludes our implementation of (dependent) Finger Trees with %\Program%. 
     To sum up, we have proven that:
     - All functions are total, once properly annotated with their preconditions.
     - All functions respect the measure semantics and use them coherently.
     - All functions respect the invariants given in the paper by Hinze & Paterson. *)
(* begin hide *)
End DependentFingerTree.
(* end hide *)
