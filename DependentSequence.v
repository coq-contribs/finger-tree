(** printing cdot $\cdot$ *)(** printing circ $\circ$ *)(** printing +:+ $\treeapp$ *)(** printing epsilon $\varepsilon$ *)(** printing :> $\Yright$ *)(** printing ::> $\Yright$ *)(** printing < $<$ *)
(* begin hide *)
Require Import FingerTree.Monoid.
Require Import Coq.Program.Program Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.
(* Require Import Reflect.Tactics. *)
Require Import Arith.
Require Import Omega.

Set Implicit Arguments.

Lemma inj_pairT1 : forall (A : Type) (P : A -> Type) x Px y Py, existT P x Px = existT P y Py -> x = y.
Proof.
  intros.
  inversion H ; reflexivity.
Qed.

Axiom subsetT_eq_compat :
  forall (U:Type) (P:U->U->Prop) (x y: U) (A : Type) 
    (Heq : x = y)
    (f : sig (fun z => P x z) -> A)
    (g : sig (fun z => P y z) -> A),
    let eq : forall z (p : P x z), P y z := 
      fun z p => @eq_ind _ _ (fun w => P w z) p _ (Heq) 
    in
      forall (Hf : forall (z : U) (p : P x z),
        f (exist (fun y => P x y) z p) =
        g (exist (fun z => P y z) z (eq z p))),
      existT (fun i : U => sig (fun z : U => P i z) -> A) x f =
      existT (fun i : U => sig (fun z : U => P i z) -> A) y g.
(** This axiom is necessary for the following to go through. 
   It looks like [ProofIrrelevanceFacts.subsetT_eq_compat] and seems validated
   by proof-irrelevance + functional extensionality.
*)

(** We first state some useful definitions. *)

Obligation Tactic := program_simplify ; auto with *.

(** We define an almost boolean less-than definition. *)
Program Definition less_than (x y : nat) : { lt x y } + { ~ lt x y }
  := if le_lt_dec y x then right _ else left _.

Definition ltb (x y : nat) : bool := leb (S x) y.

Lemma lt_complete : forall {x y}, ltb x y = true -> lt x y.
Proof. 
  intros ; unfold ltb in *. apply leb_complete. auto.
Qed.

Lemma lt_complete_conv : forall {x y}, ltb x y = false -> ~ lt x y.
Proof. 
  intros ; unfold ltb in *. pose (leb_complete_conv y (S x) H). omega.
Qed.

Ltac absurd_arith := elimtype False ; omega.
(* end hide *)
(** ** Séquences dépendantes
   %\label{fts:inst:depseq}%
   
   On va maintenant définir des séquences à accès aléatoire comme spécialisation des [fingertree].
   Cette structure permet d'ajouter un élément à n'importe quel bout d'une séquence en temps constant
   amorti, de concaténer ([app]) et découper ([split]) des séquences en temps logarithmique et d'accéder
   ([get]) ou modifier (%\cst{set}%) un élément de la séquence en temps logarithmique en la taille de la séquence aussi.
   On va créer une implémentation certifiée de cette structure en montrant que ces opérations respectent une
   spécification fonctionnelle très forte. Cette méthode diffère significativement de l'habituelle séparation
   entre opérations et preuve des invariants sur ces opérations. Ici, la préservation des propriétés va être
   prouvée simultanément à la définition des opérations elles-même. 

   *** Structure

   On définit les séquences indexées par des naturels sur un type d'éléments [A].
   On pourrait généraliser à d'autres représentations des indices, mais pour plus de
   simplicité on utilise ici les entiers de Peano. 
   *)

Section DependentSequence.
  Variable A : Type.

  (** Tout d'abord, une définition utile: le type [below i] (isomorphe au type bien 
     connu [Fin] des ensembles finis) représente les entiers naturels plus petits
     que [i], donc [below 0] est un type vide. *)

  Definition below i := { x : nat | x < i }.
  Lemma not_below_0 : below 0 -> False.
  Proof.
    intros.
    inversion H.
    inversion H0.
  Qed.
  (* begin hide *)
  Ltac mysimpl := simpl ; intros ; destruct_pairs ; simpl in * ; try subst ; 
  try (solve [ red ; intros ; discriminate ]) ; auto with *.  
  
  Obligation Tactic := unfold below in * ; intros ; mysimpl.
  
  Hint Resolve not_below_0 : ft.
  Hint Unfold below.
  (* end hide *)
   
  (** On utilise les entiers pour mesurer les séquences par leur longueur.
     Notre mesure est un peu particulière puisqu'elle contient aussi une fonction donnant
     la map %\emph{réalisée}% par le %\FT%. Cette fonction totale associe à toute position de la
     séquence une valeur de type [A]. Elle est utilisée seulement pour la spécification et pourrait
     être éliminée du code généré en utilisant une analyse de code mort ou même effacée à l'extraction
     en utilisant un système de type plus fin (c.f. %\S \ref{fts:Extraction}%). *)
  
  Definition v := { i : nat & (below i -> A) }.
  Notation " x ::> f " := (existT (fun i => below i -> A) x f : v) (at level 80, no associativity).
    
  (** On définit une notation pour nos mesures: un objet [i ::> m] est une paire dépendante
     composée d'une taille [i] et une %\eng{map}% des naturels plus petits que [i] vers [A].
     L'élément neutre ε représente la mesure d'une séquence vide. Comme elle ne contient
     aucun élément, aucune valeur n'est retournée par la fonction. On a une obligation de montrer
     que dans un contexte avec l'hypothèse [below 0], on peut prouver %\ind{False}%: on utilise juste le 
     lemme [not_below_0]. *)
  
  Program Definition epsilon : v := 0 ::> (fun _ => !).    
  
  (** Concaténer deux séquences requiert un peu de réindexation: la nouvelle map est formée par
     la projection du nouvel index sur l'une ou l'autre des maps. *)
  
  Program Definition append (xs ys : v) : v := 
    let (n, fx) := xs in let (m, fy) := ys in
    (n + m) ::> (fun i => if less_than i n then fx i else fy (i - n)).

  (* begin hide *)
  Solve Obligations with unfold below in * ; program_simplify ; auto with *.
  (* end hide *)
  (** On peut construire le monoïde [seqMonoid] à partir de ces opérations. 
     On saute les preuves qui sont relativement faciles. Il est juste à noter 
     qu'on utilise l'axiome d'extensionalité des fonctions lorsqu'on a à comparer 
     les fonctions de représentation des séquences ainsi que l'indifférence aux preuves
     pour montrer que deux objets de type [below i] sont égaux si et seulement si
     leurs premières projections sont égales. *)
  
  Program Instance seqMonoid : Monoid v := 
    { mempty := epsilon ; mappend := append }.

  (* begin hide *)
  Next Obligation.
  Proof. red.
    unfold epsilon, append ; intros.
    destruct x ; simpl ; intros.
    f_equal.
    extensionality y.
    simpl ; intros.
    destruct y ; simpl.
    f_equal.
    apply <- subset_eq. simpl.
    rewrite <- minus_n_O.
    reflexivity.
  Qed.
  
  Next Obligation.
  Proof. red.
    unfold epsilon, append ; intros.
    destruct x ; simpl ; intros.
    unfold below in *.
    assert (x + 0 = x) by auto with arith.
    pose (@subsetT_eq_compat _ (fun i => fun n => n < i)
      (x + 0) x A H).
    simpl in e ; eapply e ; eauto.
    simpl ; intros.
    elim (less_than z x) ; simpl ; intros ; auto.
    f_equal ; intros ; auto. 
    apply <- subset_eq ; try reflexivity.
    assert(z < x) by omega.
    assert(~ z < x) by omega.
    contradiction.
  Qed.
  
  Notation " ( x &) " := (@exist _ _ x _).

  Next Obligation.
  Proof. red.
    destruct x ; destruct y ; destruct z ; subst ; simpl ; auto. 
    unfold below in *.
    assert (x + x0 + x1 = x + (x0 + x1)) ; auto with arith.
    pose (@subsetT_eq_compat _ (fun i => fun n => n < i)
      (x + x0 + x1) (x + (x0 + x1)) A H).
    simpl in e.
    eapply e.
    intros ; simpl.
    elim (less_than z (x + x0)) ; simpl ; intros.
    elim (less_than z x) ; simpl ; intros; try pi.
    elim (less_than (z - x) x0) ; simpl ; intros.
    pi.

    assert(x0 = 0) by omega.
    assert(~ z < x) by omega.
    subst x0.
    assert(z < x) by omega.
    contradiction.

    elim (less_than z x) ; simpl ; intros.
    assert(x0 = 0) by omega.
    assert(~ z < x) by omega.
    contradiction.

    elim (less_than (z - x) x0) ; simpl ; intros.
    assert(x0 = 0) by omega ; subst x0.
    inversion a2.

    f_equal ; simpl ; intros ; auto.
    apply <- subset_eq ; simpl ; omega.
  Qed.

  Require Import FingerTree.Notations.
  Require Import FingerTree.DependentFingerTree.
  Notation " x ::> f " := (existT _ x f) (at level 80).
  (* end hide *)
  (** La mesure d'un singleton [x] est la map constante renvoyant [x]. *)

  Definition single (x : A) : v := 1 ::> const x.
  Instance seq_measure : Measured v A := { measure := single }.

  (** On définit l'abbréviation [seq] pour notre type de séquences. C'est une spécialisation de 
     [fingertree] avec le monoïde [seqMonoid] et la mesure [single] définie ci-dessus. *)

  Definition seq (x : v) := fingertree (v:=v) (A:=A) x.

  (** Un objet de type [seq (i ::> m)] est donc un %\FT% représentant une séquence d'objets de 
     longueur [i] donnée par la fonction [m]. On obtient trivialement la séquence vide et la séquence 
     singleton. *)
  
  Definition empty : seq epsilon := Empty.
  Definition singleton x : seq (single x) := Single x.

  (** *** Opérations

     On peut prendre la longueur de la séquence en temps constant puisqu'elle fait partie
     de la mesure. *)

  Program Definition length (s : v) (x : seq s) : nat := 
    let 'size ::> _ := s in size.

  (** Le constructeur [make n x] crée une séquence de longueur [n] avec la valeur [x] dans chaque cellule.
     Les obligations générées nous demandent de prouver par exemple que si 
     [make n x] est de type [seq (n ::> fun _ => x)] alors [add_left x (make n x)] est de type
     [seq (S n ::> fun _ => x)]. On a la préservation de la sémantique de [make] directement par typage
     ici: tous les éléments de la séquence de longueur [i] contiennent [x]. *)

  Program Fixpoint make (i : nat) (x : A) { struct i } : 
    seq (i ::> (fun _ => x)) := 
    match i with
      | 0 => empty
      | S n => add_left x (make n x)
    end.
  (* begin hide *)
  Next Obligation.
  Proof.
    intros.
    unfold epsilon, below ; simpl ; auto.
    f_equal.
    extensionality y. bang.
  Qed.

  Next Obligation.
  Proof.
    intros.
    unfold below.
    f_equal.
    extensionality y.
    elim (less_than (`y) 1) ; simpl ; reflexivity.
  Qed.

  Notation " x +:+ y " := (@app _ _ _ _ _ x _ y) (at level 20).

  Program Definition lt_idx (i : nat) (x : v) : bool := 
    let (idx, _) := x in ltb i idx.

  Notation " x =n y " := (eq_nat_dec x y) (at level 88).

  Ltac isEmpty_tac H := let He := fresh in 
    let He' := fresh in
      pose (He:=isEmpty_ε _ H) ; clearbody He ; simpl in He ; unfold epsilon in He ; 
        pose (He':=inj_pairT1 He) ; clearbody He' ;
        subst ; clear He.
  (* end hide *)     

  (** On définit maintenant la fonction fortement spécifiée [get] qui retourne le [j]ème élément
     d'une séquence [x] de longueur [i]. On assure qu'aucun accès en dehors des bornes n'est possible
     puisque [j] est de type [below i] et on assure que l'élément retourné est bien [m j].
     Le prédicat booléen [lt_idx i x] teste si un index [i] est inférieur ou égal à la première
     composante d'une mesure [x]. Pour récupérer un élément, on découpe donc l'arbre au [j]ème
     élément puisque chaque élément a pour mesure 1 et que l'accumulation additionne les mesures. *)

  Program Definition get i m (x : seq (i ::> m)) (j : below i)
    : { value : A | value = m j } :=
    let 'mkTreeSplit ls l x rs r := split_tree (lt_idx j) epsilon x in x.
  
  (** Notons qu'on n'utilise pas [m] dans le code, seulement dans le type, on aurait sinon une implémentation
     triviale. Encore une fois, on génère des obligations pour montrer que le code respecte bien 
     la spécification. Il est crucial que la fonction [split_tree] renvoie un objet de type
     [tree_split] incluant des preuves reliant l'arbre donné en entrée aux résultats pour 
     pouvoir résoudre ces obligations. Comme toujours, le code reste simple et compact. 
     En revanche, on passe près de 50 lignes de preuves nécessaires pour décharger les obligations. *)
  (* begin hide *)
  Next Obligation.
  Proof.
    red ; intros.
    isEmpty_tac H.
    apply (not_below_0 j).
  Qed.

  Next Obligation.
  Proof.
    intros.
    destruct exist rs rf ; simpl.
    destruct exist ls lf ; simpl.
    destruct exist j Hj ; simpl in *.

    assert(ls + S rs = i). 
    inversion Heq_anonymous.
    auto.
    program_simpl.
    clear Heq_anonymous0.
    
    assert (He:=inj_pairT2 Heq_anonymous).
    rewrite <- He.
    simpl.
    clear Heq_anonymous He.

    cut (j = ls).
    intros ; subst j.
    elim (less_than ls ls) ; simpl ; intros ; auto.
    elim (lt_irrefl _ a).

    elim (less_than (ls - ls) 1) ; simpl ; intros ; auto.
    contradiction by (ls - ls < 1).

    destruct or H0 ; [ isEmpty_tac H0 | idtac ];
      (destruct or H1 ; [ isEmpty_tac H1 | idtac ]) ; try omega.

    pose (lt_complete_conv H1). omega.
    pose (leb_complete _ _ H0). omega.
    destruct ls. 
    simpl in *;  pose (leb_complete _ _ H0) ; omega.
    pose (leb_complete_conv _ _ H1).  
    pose (lt_complete H0). omega.
  Qed.
  (* end hide *)

  Ltac poses H t := assert(H:=t).

  (** Le compagnon naturel de [get] est la fonction %\cst{set}% qui étant donnée une séquence [x] de longueur [i] 
     met sa [j]ème cellule à [value]. On a pour précondition que [j] est dans les bornes et comme postcondition
     que la "map" représentée par la séquence résultat est partout égale à l'ancienne séquence excepté en [j] où
     elle vaut désormais [value]. La fonction dénotée par [=n] décide l'égalité sur les naturels. 
     Ici on découpe toujours l'arbre en [j] mais on ignore l'élément associé et on reconstruit un arbre en utilisant
     la nouvelle valeur. *)
  
  Program Definition set i (m : below i -> A) (x : seq (i ::> m)) 
    (j : below i) (value : A) :  
    seq (i ::> (fun idx => if idx =n j then value else m idx)) :=
    let 'mkTreeSplit ls l _ rs r := split_tree (lt_idx j) epsilon x in
      add_right l value +:+ r.

  (* begin hide *)
  Next Obligation.
  Proof. 
    red ; intros.
    isEmpty_tac H.
    destruct exist j Hj ; inversion Hj.
  Qed.

  Obligation Tactic := mysimpl.
  Next Obligation.
  Proof.
    intros.
    destruct exist rs rf.
    destruct exist ls lf.
    destruct exist l Hl ; destruct exist r Hr.
    mysimpl.
    assert(ls + S rs = i) by (inversion Heq_anonymous ; auto).
    mysimpl.

    destruct exist j Hj. simpl in *.
    poses H' (inj_pairT2 Heq_anonymous) ; clear Heq_anonymous.
    clear Heq_anonymous0.

    assert (ls + 1 + rs = ls + S rs) by omega.
    poses e (@subsetT_eq_compat _ (fun i => fun n => n < i) _ _ A H).
    simpl in e ; apply e ; simpl ; intros ; clear e.
  
    clear x.

    assert(z < ls + S rs) by (rewrite <- H ; auto).
    subst m ; simpl in *.
    clear H0.
    destruct (eq_nat_dec z j) ; subst ; simpl in *.
    destruct (less_than j (ls + 1)) ; simpl ; auto.
    destruct (less_than j ls) ; simpl ; auto.
    
    destruct or Hl ; [ isEmpty_tac Hl ; inversion l1 | poses Hl' (lt_complete_conv Hl) ].
    absurd_arith.

    destruct or Hr ; [ isEmpty_tac Hr ; contradiction | poses Hr' (leb_complete (S j) _ Hr)].
    contradiction.
    
    destruct (less_than z (ls + 1)).
    destruct (less_than z ls) ; simpl ; auto.
    assert(z = ls) by omega ; subst z.
    destruct (less_than (ls - ls) 1) ; simpl ; auto.
    
    destruct or Hl ; [ isEmpty_tac Hl | poses Hl' (leb_complete_conv _ (S j) Hl) ; clear Hl ; simpl in *] ;
      (destruct or Hr ; [ isEmpty_tac Hr  | poses Hr' (lt_complete Hr) ; clear Hr ; simpl in *]) ;
      try contradiction by (0 = j).
    
    assert(j > ls) by omega.
    contradiction by (~ j < ls + 1).
    assert(j = ls) by omega ; subst j.
    discriminates.
   contradiction by (ls - ls < 1).

    
    destruct or Hl ; [ isEmpty_tac Hl | poses Hl' (lt_complete_conv Hl) ; clear Hl ; simpl in *] ;
      (destruct or Hr ; [ isEmpty_tac Hr  | poses Hr' (lt_complete Hr) ; clear Hr ; simpl in *]) ;
      try contradiction by (0 = j).

    destruct (less_than (z - 0) 1).
    contradiction by (z < 1).
    f_equal; apply subset_eq_compat; omega.
    
    assert(j = ls) by omega ; subst j.
    contradiction by (z < ls + 1).

    assert(j = ls) by omega ; subst j.
    destruct (less_than z ls).
    contradiction by (~ z < ls).
    destruct (less_than (z - ls) 1).
    contradiction by (z < ls).
    f_equal ; apply subset_eq_compat ; omega.
  Qed.

  Lemma eq_nat_refl : forall A x (l r : A), (if (x =n x) then l else r) = l.
  Proof.
    intros ; destruct (x =n x) ; auto with *. 
  Qed.
  Notation " j `<> k " := ((j :> ) <> (k :> )) (at level 20).
(* In the following definition we use the quoted operators [`<>] and [`=] which are wrappers around *)
(*      inequality and equality respectively, which first coerce the arguments to their base type  *)
(*      using the operator [:>]. More formally, [:>] coerces an object to its least non-subset equivalent type  *)
(*      where the number of nested subsets define the order. *)
       
  Lemma empty_any_map : forall (m m' : below 0 -> A), 
    (0 ::> m : v) = (0 ::> m' : v).
  Proof.
    intros. apply f_equal.
    extensionality x.
    elim (not_below_0 x).
  Qed.

  Obligation Tactic := unfold below in * ; intros ; program_simpl ; auto with *.
  (* end hide *)  
  (** Finalement, on définit le découpage d'une séquence en deux. Cela requiert deux projections
     dans les %\eng{map}% correspondantes qui font une réindexation, d'où: *)
    
  Program Definition split_l i (j : below i) (idx : below j) : below i := idx.
  Program Definition split_r i (j : below i) (idx : below (i - j)) : below i := j + idx.

  (** On peut découper une séquence [x] à un index [j] en renvoyant deux séquences dont la deuxième contient
     l'élément à l'index [j]. Il faut approximativement une centaine de lignes de preuve pour décharger les
     trois obligations générées par %\Program%, essentiellement sur l'arithmétique de la réindexation.
     %\label{def:split}% *)
  
  Program Definition split i m (x : seq (i ::> m)) (j : below i) :
    seq (j ::> (m ∘ split_l j)) * seq ((i - j) ::> (m ∘ split_r j)) :=
    let 'mkTreeSplit ls l x rs r := split_tree (lt_idx j) epsilon x in
      (l, add_left x r).
  (* begin hide *)
  Obligation Tactic := unfold below in * ; intros ; mysimpl.
  
  Next Obligation.
  Proof.
    intros.
    destruct exist j Hj.
    red ; intro He ; isEmpty_tac He ; inversion Hj.
  Qed.

Hint Extern 4 => contradiction : exfalso.

  Next Obligation.
  Proof.
    clear Heq_anonymous0.
    intros.
    destruct exist j Hj.
    destruct exist ls lf.
    destruct exist rs rf.
    destruct exist l Hl ; destruct exist r Hr.
    simpl in *.
    inversion Heq_anonymous ; clear Heq_anonymous.
    subst i.
    assert (Hproj:=inj_pairT2 H1).
    subst m ; clear H1 x0.

    unfold apply ; simpl.

    cut (j = ls) ; intros.
    subst j.

    apply (@subsetT_eq_compat _ (fun i => fun n => n < i) _ _ A (@eq_refl _ ls)).
    simpl ; intros. 
    unfold compose ; simpl.
    elim (less_than z ls) ; intros ; simpl ; auto with exfalso.
    f_equal ; simpl ; auto. 
    apply <- subset_eq ; auto.

    destruct or Hl ; [ isEmpty_tac Hl | poses Hl'' (lt_complete_conv Hl) ; clear Hl] ;
      (destruct or Hr ; [ isEmpty_tac Hr | poses Hr'' (lt_complete Hr) ; clear Hr]) ; omega.
  Qed.

  Next Obligation.
  Proof.
    unfold const.
    clear  Heq_anonymous0.
    intros ; unfold compose.
    destruct exist j Hj.
    destruct exist ls lf.
    destruct exist rs rf.
    destruct exist l Hl ; destruct exist r Hr.
    simpl in *.
    inversion Heq_anonymous ; clear Heq_anonymous.
    subst i.
    assert (Hproj:=inj_pairT2 H1).
    subst m ; clear H1 x0.

    unfold apply ; simpl.

    cut (j = ls) ; intros.
    subst j.
    assert(S rs = ls + S rs - ls) by (rewrite minus_plus ; auto).
    
    pose (@subsetT_eq_compat _ (fun i => fun n => n < i)
     _ _ A H).
    simpl in e.
    apply e ; simpl ; intros ; clear e.

    destruct (less_than (ls + z) ls).
    contradiction by (~ ls + z < ls).

    elim (less_than z 1) ; intros ; auto.
    assert(z = 0) by omega ; subst z.
    assert(ls + 0 - ls = 0) by (rewrite minus_plus ; auto).
    destruct (less_than (ls + 0 - ls) 1) ; auto.
    pattern 0 at 1 in a.
    rewrite <- H0 in a.
    contradiction.

    destruct (less_than (ls + z - ls) 1) ; intros ; auto.
    
    unfold const. 
    rewrite minus_plus in l0.
    contradiction.

    f_equal ; apply subset_eq_compat ; auto.
    rewrite minus_plus ; reflexivity.
    
    destruct or Hl ; [ isEmpty_tac Hl | poses Hl'' (lt_complete_conv Hl) ; clear Hl] ;
      (destruct or Hr ; [ isEmpty_tac Hr | poses Hr'' (lt_complete Hr) ; clear Hr]) ; omega.
  Qed.

  (* end hide *)

  (** *** Propriétés

     Maintenant que nous avons défini nos opérations avec leurs invariants, il suffit d'utiliser
     l'information donnée par les types pour les relier. Ici on formalise comment [get] et %\cst{set}% 
     se comportent l'un vis-à-vis de l'autre. Les preuves utilisent uniquement les types et pas le code
     des deux opérations. On montre que nos séquences vérifient les deux axiomes des tableaux fonctionnels:
     si l'on récupère la valeur à l'index [j] qu'on vient de modifier on récupère la nouvelle valeur ([get_set]),
     sinon l'ancienne ([get_set_diff]). *)
  
  Program Lemma get_set : forall i m (x : seq (i ::> m)) 
    (j : below i) (value : A), value = get (set x j value) j.
  Proof.
    intros.
    destruct_call get. 
    subst x0.
    destruct exist j Hj ; simpl in *.
    rewrite eq_nat_refl ; reflexivity.
  Qed.

  (** Nous avons pu écrire ce lemme seulement parce qu'on a utilisé le %\eng{type-checker}% de %\Russell%, 
     qui a automatiquement inséré une coercion à la droite de l'égalité pour aller d'un sous-ensemble sur
     [A] à [A] (le type implicite d'une égalité est fixé par son premier argument explicite, ici [value]).
     L'intégration transparente de %\Program% dans %\Coq% en tant qu'assistant de preuve et pas seulement 
     langage de programmation est une amélioration par rapport aux systèmes antérieurs qui tentaient de faire 
     de %\Coq% un langage de programmation, comme la tactique %\texttt{Program}% de %\citet{conf/mpc/Parent95}%.
     Il reste cependant du chemin à faire pour supporter les énoncés les plus naturels dans %\Russell%.
     Dans la prochaine définition par exemple, on coerce explicitement les objets [j] et [k] du type [below i] vers 
     leurs composantes de type [nat] et le résultat de [get] vers [A]. C'est dû au fait que l'égalité de Leibniz
     sur les objets de type sous-ensemble ne fait du sens que sur leurs premières composantes, les témoins, tandis
     que la comparaison des preuves n'a pas vraiment de sens. Notre solution pragmatique est de laisser les
     utilisateurs insérer des %\eng{casts}% pour obtenir le comportement souhaité, mais dans une théorie 
     des types avec indifférence aux preuves on pourrait vraiment résoudre ce problème puisque la comparaison
     des preuves deviendrait triviale. On détaillera cette solution dans la section %\ref{fts:sec:PI}%.
     *)
  
  Program Lemma get_set_diff : forall i m (x : seq (i ::> m)) 
    (j : below i) (value : A) (k : below i),
    (j : nat) <> k -> (get x k : A) = get (set x j value) k.
  Proof.
    unfold below in * ; intros ; program_simpl.
    destruct_call get. 
    destruct_call get.
    simpl in *.
    subst x0 x1.
    
    elim (eq_nat_dec k j) ; simpl ; intros.
    subst k ; discriminates.
    f_equal.
  Qed.

End DependentSequence.

(** On a développé une implémentation certifiée des séquences à accès aléatoire de façon modulaire
   en moins de 400 lignes dont l'interface dépendante peut être utilisée pour écrire des programmes 
   et prouver des propriétés sur ceux-ci en même temps. *)
