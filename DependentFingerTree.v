(* begin hide *)
Require Import FingerTree.Monoid.
Require Import FingerTree.Reduce.
Require Import FingerTree.Notations.
Require Import FingerTree.Digit.
Require Import Coq.Lists.List Coq.Program.Program JMeq Coq.Program.Equality.

Set Implicit Arguments.
(** Useful when working with existT equalities. *)
Implicit Arguments inj_pair2 [U P p x y].
(* end hide *)
(** printing measure %\coqdefinitionref{FingerTree.Monoid.measure}{measure}% *)(** printing lparr $\coqdoublebar$ *)(** printing rparr $\coqdoublebar$ *)(** printing ∙ $\cdot$ *)(** printing epsilon $\varepsilon$ *)(** printing +:+ $\treeapp$ *)(** printing ++ $\app$ *)(** printing := $\coloneqq$ *)(** printing ::> $\Yright$ *)(** printing < $<$ *)
(** On va maintenant définir la structure de %\FT% sur un monoïde et une mesure donnée.
   On verra dans la section %\ref{fts:Instances}% comment diverses instantiations de ces 
   paramètres permettent de dériver différentes structures.
   *)

Section DependentFingerTree.  
  Context `{mono : Monoid v}.

  (** La variable [v] représente le support du monoïde et [mono] est l'implémentation 
     du monoide elle-même. Bien sûr, on a toujours accès au notations ε et ∙ pour se référer aux
     méthodes de la classe [Monoid]. *)

  (** ** Nodes

     On a déjà défini les doigts, on définit maintenant les nœuds 2-3 paramétrés par une
     mesure. Les [node] cachent aussi une mesure qui contient la combinaison des mesures des sous-objets. *)

  Section Nodes.
    Context `{ms :! Measured v A}.

    (** On dénote encore une fois la fonction [measure] par $\measure{\_}$ dans la suite. *)
    
    Inductive node : Type :=
    | Node2 : forall x y, { s : v | s = lparr x rparr ∙ lparr y rparr } -> node
    | Node3 : forall x y z, { s : v | s = lparr x rparr ∙ lparr y rparr ∙ lparr z rparr } -> node.

    (** On utilise un type sous-ensemble ici pour spécifier l'invariant sur la valeur cachée.
       Cet invariant ne peut pas être vérifié à l'aide de types simples puisqu'il dépend évidemment
       des valeurs portées par le constructeur de [node]. De plus, l'invariant fait référence à la 
       %\emph{fonction}% de mesure, qui va donc devenir un %\emph{paramètre}% du type de donnée, ce qui
       requiert un mécanisme d'abstraction supplémentaire dans les langages fonctionnels courants, comme 
       les classes de type de %\Haskell% ou un système de module avec foncteurs à la %\ML%. Ici, on utilise
       simplement le produit dépendant.
       *)

    (** On peut aussi définir les %\eng{smart constructors}% [node2] et [node3] qui calculent les 
       mesures à la volée. On caste les expressions avec le type [v] pour désambiguer la surcharge
       qui sinon chercherait une instance de [Monoid] sur le type sous-ensemble 
       [{s : v | s = lparr x rparr ∙ lparr y rparr }]. *)

    Program Definition node2 (x y : A) : node := 
      Node2 x y (lparr x rparr ∙ lparr y rparr : v).
    Program Definition node3 (x y z : A) : node := 
      Node3 x y z (lparr x rparr ∙ lparr y rparr ∙ lparr z rparr : v).

    (** Les obligations générées sont trivialement vraies, elles sont de la forme $x = x$.
       De façon correspondante, [node_measure] projette la mesure cachée.
       On a ici une projection implicite. *)
    
    Program Definition node_measure n : v :=
      match n with Node2 _ _ s => s | Node3 _ _ _ s => s end.
    
    (** On peut déclarer une instance globale (généralisée à la sortie de la section) pour
       la mesure d'un nœud. *)
    
    Global Instance nodeMeasured : Measured v node := { measure := node_measure }.

    (** On peut toujours convertir un [node] en [digit] en oubliant la mesure. *)
    
    Definition node_to_digit (n : node) : digit A :=
      match n with Node2 x y _ => Two x y | Node3 x y z _ => Three x y z end.
  End Nodes.

  (** Bien qu'il puisse sembler que la fonction [node_measure] est indépendante de la fonction [measure],
     elle ne l'est pas. En effet le type de cette fonction après la clôture de la section devient:
     [Π (m : Monoid v) (A : Type) (ms : Measured A), node -> v]
     
     L'inductif [node] lui-même est paramétré par la fonction de mesure, donc toutes les opérations sur les 
     nœuds la prennent comme argument implicite (à la manière d'une contrainte de classe sur un type de donnée 
     en %\Haskell%). On a donc gratuitement la propriété qu'on ne peut pas confondre deux objets de type [node]
     construits avec des mesures différentes sur le même type d'éléments puisque la mesure fait partie
     du type.

     Si nous n'avions pas ajouté l'invariant au sein des constructeurs, nous n'aurions pas
     besoin de ce paramètre, mais nous ne pourrions pas prouver grand chose sur les mesures qui seraient des
     objets arbitraires de type [v]. On pourrait définir un prédicat inductif sur les [node] assurant
     que la mesure d'un nœud a bien été construite en utilisant la mesure de façon cohérente, mais on 
     aurait à montrer la préservation de ce prédicat pour toutes les fonctions manipulant directement ou 
     indirectement des nœuds. Ici, on garantit cette propriété par le typage et le système nous donnera
     automatiquement les obligations à montrer lorsque l'invariant pourrait être cassé. 
     *)
  
  (* begin hide *)  
  Hint Unfold measure option_measure digit_measure : ft.

  Implicit Arguments node [[ms]].

  Lemma nodeMeasure_digits : forall `{ms :! Measured v A} (n : node A), 
    (measure n) = digit_reducel (fun i a => i ∙ measure a) ε (node_to_digit n).
  Proof.
    intros.
    destruct n ; program_simpl ; monoid_tac ; auto. 
  Qed.
  (* end hide *)

  (** ** Finger Trees
     
     Avant de présenter la définition de [fingertree] en %\Coq%, on rappelle le type %\Haskell% 
     original et on va justifier pourquoi une traduction directe serait insatisfaisante.
     Le type des %\FTs% mesurés est défini comme suit:

     %\begin{code}
     \kw{data} \ind{FingerTree} \id{v} \id{a} = \constr{Empty} | \constr{Single} \id{a}\coqdoceol{}
     \coqdocindent{2.00em}| \constr{Deep} \id{v} (\ind{Digit} \id{a}) (\ind{FingerTree} \id{v} (\ind{Node} \id{v} \id{a})) (\ind{Digit} \id{a})
     \end{code}%
     
     La figure %\ref{fig:FingerTree}% représente un exemple de %\ind{FingerTree}% mesuré.
     
     %\begin{figure}[h]\begin{center}\tikfingertree\end{center}%
     %\caption[Un exemple de \FT]{Un exemple de \FT. \fingertreecaption}\label{fig:FingerTree}\end{figure}%
     
     On pourrait directement définir la structure de %\FT% en %\Coq% en traduisant la définition
     %\Haskell%. Seulement, en faisant cela on pourrait causer un certain nombre de difficultés. 
     Premièrement, on aurait le même problème décrit auparavant d'identification de structures 
     qui ont été construites par des mesures différentes si l'on ne paramétrait pas le type par celle-ci.
     Bien sûr, le fait de paramétrer par la mesure force à réinstancier celle-ci au nœud [Deep]
     puisque le %\ind{FingerTree} \id{v} (\ind{Node} \id{v} \id{α})% sous-jacent attend une mesure sur des 
     objets de type %\ind{Node} \id{v} \id{α}% plutôt que [α].
     
     Un %\coqinductive{FingerTree.DependentFingerTree.fingertree}{fingertree}%
     est donc paramétré par un type [A] et une fonction de mesure sur ce type.
     Chaque objet de type [fingertree] est aussi indexé par sa propre mesure:
     
     - [Empty] construit l'arbre vide de mesure ε;
     - [Single x] construit l'arbre singleton de mesure $\measure{x}$;
     - [Deep pr ms m sf] construit un arbre de préfixe [pr], sous-arbre [m] de mesure [ms] et suffixe [sf]. 
     Sa mesure est calculée en combinant les mesures de ses sous-structures de gauche à droite.
     L'argument [ms] sera implicite lorsqu'on construira des nœuds [Deep] puisqu'on peut l'inférer à partir 
     du type de [m]. On place cette mesure cachée juste avant l'arbre du milieu contrairement à la version originale
     où la mesure est le premier composant et stocke la mesure de l'%\emph{ensemble}% de l'arbre.
     Pour nous, la mesure de l'arbre complet est donnée par l'index.
     On présente la définition sous forme de règles d'inférence pour une meilleure lisibilité, en omettant
     les paramètres [A] et [measure] dans les prémisses:
     
     %\fingertreeFig%
    *)
  (* begin hide *)
  Inductive fingertree {A} {ma : Measured v A} : v -> Type :=
  | Empty : fingertree ε
  | Single : forall x : A, fingertree (measure x)
  | Deep : forall (l : digit A) {ms : v}, 
    @fingertree (node A) _ ms
    -> forall r : digit A, fingertree (measure l ∙ ms ∙ measure r).

  Implicit Arguments fingertree [[ma]].
  (* end hide *)
  
  (** Cette famille inductive est indexée par des valeurs de type [v].
     Une simple observation nous a conduit à ce type dépendant:
     nous voulons avoir l'invariant que la mesure cachée sur le nœud [Deep] 
     est bien celle du sous-arbre. Pour cela on doit avoir une façon de référer à cette
     mesure au moment même de la définition de l'arbre, alors qu'on ne peut 
     pas écrire une fonction récursive (polymorphe) sur l'arbre, à moins de se placer dans le 
     cadre des définitions inductives-récursives %\cite{DBLP:journals/jsyml/Dybjer00}%.
     La mesure de l'arbre fait ici partie de son type. On va donc faire apparaître les
     invariants sur les mesures contenues dans nos arbres directement dans les types des 
     fonctions sur les [fingertree].
     *)

  (* begin hide *)
  Section add.   
  (* end hide *)
  (** **** Ajouter un élément
     %\label{def:addleft}% On peut ajouter un élément [a] à gauche d'un arbre [t] de mesure [s] pour obtenir
     un arbre de mesure [measure a ∙ s]. 
     Du fait de la récursion polymorphe, toutes nos fonctions récursives vont maintenant avoir des arguments
     [A] et [measure] puisqu'ils sont de %\emph{vrais}% arguments qui changent lors des appels récursifs.
     Si [t] est vide, un singleton ou un arbre avec un préfixe gauche non plein, on pousse simplement
     [a] à la position la plus à gauche de l'arbre. Sinon, on doit réorganiser l'arbre pour faire de l'espace
     à gauche pour [a]. Cela requiert une récursion polymorphe pour ajouter un élément [node3 measure c d e]
     à gauche de [t' : fingertree v (node_measure measure) st'].
     *) 

    Program Fixpoint add_left `{m :! Measured v A} (a : A) (s : v)
      (t : fingertree A s) {struct t} : fingertree A (measure a ∙ s) :=
      match t in fingertree _ s return @fingertree A m (measure a ∙ s) with
        | Empty => Single a
        | Single b => Deep (One a) Empty (One b)
        | Deep pr st' t' sf =>
          match pr with
            | Four b c d e => let sub := add_left (node3 c d e) t' in
              Deep (Two a b) sub sf
            | x => Deep (add_digit_left a x) t' sf
          end
      end.
    
    (** La première expression [match] utilise l'élimination dépendante. Le sens des annotations est qu'à partir
       d'un [fingertree] d'une mesure [s] particulière, chaque branche doit construire un 
       [fingertree] de mesure [measure a ∙ s] ou [s] sera substitué par la mesure correspondant au motif
       de la branche. Par example, dans la première branche on doit construire un objet de type
       [fingertree measure (measure a ∙ ε)].
       Seulement, la branche droite [Single a] a le type [fingertree measure (measure a)], 
       on utilise donc la règle d'équivalence sur les familles inductives présentée figure
       %\ref{fig:russell:indequiv}% pour coercer l'objet dans le type attendu. L'application 
       de cette règle génère une obligation $\vdash \coqmeasure{}~\id{a} ∙ \varepsilon = \coqmeasure{}~\id{a}$, 
       facilement résolue en utilisant la loi d'identité à droite du monoïde. 
       Les clauses [in] et [return] sont en général obligatoires en %\Coq% à cause de 
       l'indécidabilité de l'unification d'ordre-supérieur (il faudrait trouver le type le plus général 
       unifiant les types des branches, en inférant les dépendances avec l'objet filtré).
       On peut cependant les omettre dans %\Russell%, auquel cas la substitution utilisée par 
       l'élimination dépendante est remplacée par du raisonnement équationnel.
       Si nous avions omis ces clauses, on aurait eu l'équation [s = ε] dans le 
       contexte de la première branche et donc l'obligation 
       $\id{H} : \id{s} = ε \vdash \coqmeasure{}~\id{a} ∙ s = \coqmeasure{}~\id{a}$.
       Celle-ci serait résolue par substitution de [s] par ε dans le but puis application 
       de l'identité à droite ; on a juste retardé la substitution.

       Le filtrage imbriqué sur le préfixe de l'arbre utilise un %\emph{alias}% [x] pour capturer
       les préfixes qui ne sont pas [Four] et applique la fonction "partielle" 
       [add_digit_left] définie précédemment. On a une application de la règle d'équivalence 
       sur les sous-ensembles ici, qui génère une obligation de montrer que [x] n'est pas plein.
       Celle ci peut être résolue parce que l'algorithme de compilation du filtrage ajoute une 
       hypothèse $`A b~c~d~e, x \neq \ident{Four}~b~c~d~e$ dans le contexte. On enrichit les contextes
       de typage des branches par ce genre d'inégalités lorsque leurs motifs sont en intersection avec
       des motifs précédents.

       La préservation de la mesure est une propriété essentielle de cette fonction. Pour le voir,
       prenons l'instantiation des %\FTs% par le monoïde des listes avec la concaténation. On peut 
       vérifier ici qu'ajouter un élément à gauche de l'arbre insère bien la mesure de l'élément devant
       la mesure de l'arbre. Cela revient donc à ajouter un élément en tête de la liste des éléments
       de l'arbre original avec ce monoïde des listes. Pour chacune des définitions
       suivantes, cette correspondance avec l'interprétation des listes aura toujours un sens évident.
       On définit la fonction %\coqdefinition{FingerTree.DependentFingerTree.addright}{add\_right}% de la même
       façon.
     
       *)
    (* begin hide *)

    Solve Obligations using program_simpl ; try unfold measure, digit_measure ; simpl ; monoid_tac ; auto.

    Next Obligation.
    Proof.
      destruct pr ; simpl in H ; try discriminate ; auto.
      elim (H a0 a1 a2 a3) ; auto.
    Qed.

    Next Obligation.
    Proof.
      clear_subset_proofs. 
      destruct pr ; simpl ; auto ;
      try subst x ; try clear Heq_t ; try subst s ; monoid_tac ; auto ;
      unfold measure, digit_measure, Digit.digit_measure ; simpl ; monoid_tac ; auto.
      elim H with a0 a1 a2 a3 ; auto.
    Qed.

    Program Fixpoint add_right `{ma :! Measured v A} (s : v) (t : fingertree A s) (a : A) :
      fingertree A (s ∙ measure a) :=
      match t in fingertree _ s return fingertree A (s ∙ measure a) with
        | Empty => Single a
        | Single b => Deep (One b) Empty (One a)
        | Deep pr st' t' sf =>
          match sf with
            | Four b c d e => Deep pr (add_right t' (node3 b c d)) (Two e a)
            | _ => Deep pr t' (add_digit_right sf a)
          end
      end.

    Solve Obligations using program_simpl ; try unfold measure, digit_measure ; simpl ; monoid_tac ; auto.

    Next Obligation.
    Proof.
      intros.
      red ; intros.
      destruct sf ; simpl in H0 ; try discriminate ; auto.
      elim (H a0 a1 a2 a3) ; auto.
    Defined.

    Next Obligation.
    Proof.
      intros.
      unfold measure, digit_measure ; simpl.
      destruct sf ; simpl ; monoid_tac ; auto.
      elim H with a0 a1 a2 a3 ; auto.
    Defined.
    
  End add.  
  (* end hide *)

  (** Un exemple plus simple d'élimination dépendante nous est donné par 
     la fonction de conversion [digit_to_tree], qui transforme un "doigt" en
     un arbre de même mesure. Notons qu'ici on omet les annotations. 
     Les versions récentes de %\Coq% sont capables dans le cas où l'on filtre une
     variable qui apparaît dans le type de retour d'inférer automatiquement le
     prédicat d'élimination dépendante. On utilise aussi cette optimisation dans 
     %\Program%, qui permet d'utiliser la substitution le plus possible mais
     toujours en conservant les équations dans chaque branche. *)
  
  Program Fixpoint digit_to_tree `{ma :! Measured v A} (d : digit A) {struct d} : 
    fingertree A (measure d) :=
    match d with
      | One x => Single x
      | Two x y => Deep (One x) Empty (One y)
      | Three x y z => Deep (Two x y) Empty (One z)
      | Four x y z w => Deep (Two x y) Empty (Two z w)
    end.
  (* begin hide *)
  Solve Obligations using program_simpl ; simpl in * ; program_simpl ; unfold measure ; simpl ; monoid_tac ; auto.

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

    Definition node_size `{mv :! Measured v A} (size : A -> nat) (d : node A) := 
      match d with
        | Node2 x y _ => size x + size y
        | Node3 x y z _ => size x + size y + size z
      end.

    Fixpoint tree_size' `{mv :! Measured v A} (size : A -> nat) {s : v}
      (t : fingertree A s) : nat :=
      match t with
        | Empty => 0
        | Single x => size x
        | Deep xs _ x ys => digit_size size xs + tree_size' (node_size size) x + digit_size size ys
      end.
    
    Definition tree_size `{mv :! Measured v A} (s : v) (t : fingertree A s) : nat :=
      tree_size' (fun _ => 1) t.

  End Size.

  Section view_L.
  (* end hide *)

  (** ** La vue à gauche d'un %\FT%
     On va maintenant construire des vues %\cite{wadler85,DBLP:journals/jfp/McBrideM04}%
     sur les %\FTs% qui permettent de décomposer un arbre en son premier élément 
     (à gauche ou à droite) puis le reste de l'arbre.
     Cela permet de s'abstraire de l'implémentation et donner une interface similaire 
     aux listes au type de donnée [fingertree]. On peut ainsi écrire des fonctions récursives
     sur les %\FTs% sans avoir à s'occuper des détails compliqués de la structure 
     (voir par exemple la définition de [merge]).
     
     Le type inductif de la vue à gauche [View_L] est un peu moins polymorphe que les autres,
     puisqu'il n'a pas besoin de contenir la fonction de mesure que les vues ignorent.
     En revanche on stocke la mesure [s] du reste de l'arbre dans le constructeur
     [cons_L] ([s] sera implicite). On abstrait donc [View_L] par le type de la séquence
     [seq] indexé par un objet de type [v]. On l'instanciera par [fingertree A]. *)
    
    Inductive View_L {A : Type} {seq : v -> Type} : Type := 
    | nil_L : View_L
    | cons_L : A -> forall {s}, seq s -> View_L.
    
    Implicit Arguments View_L [ ].

    (** Une telle vue sera produite par la fonction [view_L], par récursion structurelle (polymorphe)
       sur le [fingertree]. On peut facilement utiliser la fonction partielle [digit_tail] qui n'accepte
       que les [digit] non-singleton et l'on n'a besoin d'aucune annotation de type à l'appel récursif de
       [view_L]. Notons qu'on utilise une %\emph{application partielle}% de type [(fingertree A)] 
       dans le type de retour, ce qui est parfaitement légal en %\Coq%.
       %\label{def:viewL}%*)

    Program Fixpoint view_L `{ma :! Measured v A} (s : v) (t : fingertree A s) :
      View_L A (fingertree A) := 
      match t with
        | Empty => nil_L 
        | Single x => cons_L x Empty
        | Deep pr st' t' sf => 
          match pr with
            | One x => 
              match view_L t' with
                | nil_L => cons_L x (digit_to_tree sf)
                | cons_L a st' t' => cons_L x (Deep (node_to_digit a) t' sf)
              end
            | y => cons_L (digit_head y) (Deep (digit_tail y) t' sf)
          end
      end.

    (* begin hide *)
    Next Obligation.
    Proof.
      destruct pr ; simpl in * ; auto.
      intro ; apply (H a) ; auto.
    Defined.

    Lemma view_L_case : forall `{ma :! Measured v A} (s : v) (t : fingertree A s), 
      view_L t = nil_L \/ exists x, exists st', exists t',  view_L t = cons_L x (s:=st') t'.
    Proof.
      intros.
      destruct (view_L t) ; simpl ; intuition ; auto.
      right.
      exists a ; exists s0 ; exists f ; auto.
    Qed.
    (* end hide *)
    (** On peut montrer que [view_L] préserve la mesure de l'arbre. Si nous avions indexé
       [View_L] par la mesure de l'arbre en entrée, ces lemmes de génération seraient apparus
       comme obligations dans la définition de [view_L].
       *)

    Lemma view_L_nil : Π `{ma :! Measured v A} s (t : fingertree A s),
      view_L t = nil_L -> s = ε.
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

    Lemma view_L_cons : Π `{ma :! Measured v A} s (t : fingertree A s) x st' t',
      view_L t = cons_L x (s:=st') t' -> s = measure x ∙ st'.
    Proof.
      induction t ; program_simpl ; intros ; simpl in * ; try discriminate ; auto.
      monoid_tac ; auto.
      destruct l ; simpl  in * ; try discriminate ; simpl ; monoid_tac ; 
        auto ; try (inversion H ; subst ; simpl ; simpl ; monoid_tac ; auto).
      clear H1.
      destruct (view_L_case t).
      rewrite H0 in H.
      inversion H ; subst ; simpl ; monoid_tac ; auto.
      rewrite (view_L_nil _ H0) ; monoid_tac ; auto.
      program_simpl.
      rewrite H3 in H ; simpl.
      inversion H ; simpl ; subst.
      f_equal.
      rewrite (IHt _ _ _ H3).
      monoid_tac ; f_equal.
      rewrite <- nodeMeasure_digits. reflexivity.
    Qed.

    (** *** Problèmes de dépendance
       %\label{sec:DependenceHell}%
       Nos vues sont utiles pour construire une interface de haut-niveau sur les %\FTs%, mais dans leur état
       courant elles sont très limitées puisqu'on ne peut écrire que des fonctions non-récursives sur ces vues.
       En effet, on ne peut pas convaincre %\Coq% qu'une fonction définie par récursion sur la 
       vue d'un arbre est aussi valide que par récursion sur l'arbre lui-même, à cause de la
       condition de garde. Pour ce faire, nous avons besoin d'une mesure
       sur le type [fingertree], par exemple leur nombre d'éléments donné par la fonction [tree_size]. 
       On peut dès lors créer une mesure trivialement sur les vues [View_L_size]. Les définitions de 
       [tree_size] et donc [View_L_size] sont généralisées pour toute fonction de taille à cause de la 
       récursion polymorphe. *)

    Definition View_L_size' `{ma :! Measured v A} (size : A -> nat)
      (view : View_L A (fingertree A)) :=
      match view with
        | nil_L => 0
        | cons_L x st' t' => size x + tree_size' size t'
      end.

    Definition View_L_size `{ma :! Measured v A} (v : View_L A (fingertree A)) :=
      View_L_size' (λ _, 1) v.
       
    (** Il n'y a plus qu'à montrer que pour tout arbre [t], [view_L t] retourne une vue de taille
       [tree_size t] pour prouver qu'un appel récursif sur la queue d'une vue est correct
       (c.f. %\S\ref{fig:merge}%).
       
       Seulement, faire cette preuve n'est pas si facile parce que [view_L] manipule des objets à type
       dépendant et raisonner sur ceux-ci est assez délicat. Une difficulté essentielle est que l'égalité
       de Leibniz n'est pas adaptée pour comparer des objets dans des types dépendants puisqu'ils peuvent 
       être comparables mais dans des types différents. Par exemple la
       proposition sur les vecteurs [vnil = vcons x n v]
       n'est pas bien typée puisque [vnil] est de type [vector 0] 
       et [vcons x n v] de type [vector (S n)].
       Ces deux types n'étant pas convertibles, on ne peut même pas typer cet énoncé.
       
       Dans notre cas, on veut montrer qu'un arbre [t] arbitraire de mesure [s] ayant pour 
       vue [nil_L] est forcément l'arbre vide [Empty], mais ces deux termes n'ont pas le 
       même type. On applique la solution proposée par %\cite{mcbride00dependently}% en utilisant 
       une égalité hétérogène: on va alors pouvoir prouver que les termes doivent être dans le même type
       et retrouver l'égalité de Leibniz ensuite. L'inductif [JMeq] definit l'égalité hétérogène
       (denotée par $"~="$) en %\Coq%, de type: [∀ A (a : A) B (b : B), Type].
       Cette égalité permet de comparer des objets qui ne sont pas du même type (ou pas encore, 
       avant simplifications dues à des réécritures, des éliminations%\ldots%).
       Son unique constructeur est [JMeq_refl], de type [Π A a, JMeq A a A a].
       L'intérêt de cette notion d'égalité est de retarder le moment où l'on doit montrer que deux 
       types sont égaux et donc que deux objets sont comparables. Lorsqu'on arrive à raffiner une 
       hypothèse d'égalité dépendante pour que les deux types coincident, on peut appliquer l'axiome
       [JMeq_eq] de type [Π A x y, JMeq A x A y -> x = y] pour récupérer une égalité
       de Leibniz usuelle entre les deux objets. L'axiome [JMeq_eq] est équivalent à l'axiome 
       %\textsf{K}% de %\people{Streicher} \cite{Hofmann98thegroupoid}%.
       
       Dans le premier lemme, on compare [t] de mesure [s] avec [Empty] de mesure ε;
       clairement, si l'on remplace [JMeq] par l'égalité de Leibniz on aura une erreur de typage. *)

    Lemma view_L_nil_JMeq_Empty : forall `{ma :! Measured v A} s
      (t : fingertree A s), view_L t = nil_L -> JMeq t Empty.
    Proof.
      intros.
      induction t ; simpl in * ; try discriminate ; auto.
      destruct l ; simpl  in * ; try discriminate ; auto.
      program_simpl ; destruct (view_L t) ; try destruct (digit_to_tree measure r) ; simpl  in * ; try discriminate ; auto.
    Qed.

    (** Une fois qu'on a montré l'égalité pour un index général [s], on peut l'instancier sur 
       un index particulier, ici ε. Sachant que [t] est maintenant de mesure ε, on peut utiliser
       l'égalité de Leibniz entre [t] et [Empty]. *)

    Lemma view_L_nil_Empty : forall `{ma :! Measured v A}
      (t : fingertree A ε), view_L t = nil_L -> t = Empty.
    Proof.
      intros ; apply JMeq_eq.
      apply (view_L_nil_JMeq_Empty _ H).
    Qed.

    (** Ces lemmes auxiliaires sur [nil_L] et [Empty] vont nous permettre de
       construire la mesure. En effet, ils sont nécessaires pour prouver le 
       lemme suivant: *)

    Section view_L_measure.
      (* begin hide *)
      Require Import Omega.

      Lemma digit_to_tree_size : forall `{ma :! Measured v A} (f : A -> nat) d, tree_size' f (digit_to_tree d) = digit_size f d.
      Proof.
        intros.
        induction d ; program_simpl ; simpl ;
          elim_eq_rect ; simpl ; auto with arith.
        omega.
      Qed.
      
      Lemma node_to_digit_size : forall `{ma :! Measured v A} (f : A -> nat) n, digit_size f (node_to_digit n) = (node_size f) n.
      Proof.
        intros.
        destruct n ; simpl ; auto.
      Qed.

      Lemma view_L_size_gen : forall `{ma :! Measured v A} (s : v)
        (t : fingertree A s) (f : A -> nat),
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
        rewrite <- digit_to_tree_size ; auto with arith.

        destruct H as [x [st' [t' Hview]]].
        rewrite Hview in IHt.
        simpl in IHt.
        rewrite Hview ; simpl.
        pose (IHt (node_size f)).
        rewrite <- e.
        rewrite node_to_digit_size.
        auto with arith.
      Qed.
      (* end hide *)
      Lemma view_L_size : forall `{ma :! Measured v A} (s : v) (t : fingertree A s),
        View_L_size (view_L t) = tree_size t.
      Proof.
        intros.
        unfold View_L_size, tree_size ; apply view_L_size_gen.
      Qed.

      (** Cela nous donne une mesure décroissante sur les résultats de [view_L].
         On l'utilisera plus tard, lorsqu'on programmera des instances. *)

      Lemma view_L_size_measure : forall `{ma :! Measured v A} (s : v)
        (t : fingertree A s) x st' (t' : fingertree A st'), 
        view_L t = cons_L x t' -> tree_size t' < tree_size t.
      Proof.
        intros ; unfold tree_size. 
        pose (view_L_size t).
        rewrite H in e ; simpl in e.
        unfold tree_size in e.
        omega.
      Qed.
    End view_L_measure.

    (** On peut aussi définir le %\eng{smart constructor}% [deep_L], qui réarrange un arbre
       lorsqu'on lui donne un [digit] de préfixe potentiel et inversement pour [deep_R].
       C'est une version dépendante de la fonction interne pour le cas [Deep] de [view_L],
       qui est utilisée lorsqu'on découpe des %\FTs%. On peut noter que la spécification bénéficie
       de la surcharge qui permet de factoriser toutes les instances de [measure] sur les arbres,
       les doigts et les doigts optionnels dans ce cas. *)

    Program Definition deep_L  `{ma :! Measured v A}
      (d : option (digit A)) (s : v) (mid : fingertree (node A) s)
      (sf : digit A) : fingertree A (measure d ∙ s ∙ measure sf) := 
      match d with
        | Some pr => Deep pr mid sf
        | None =>  
          match view_L mid with
            | nil_L => digit_to_tree sf
            | cons_L a sm' m' => Deep (node_to_digit a) m' sf
          end
      end.

    (* begin hide *)
    Next Obligation.
    Proof.
      intros.
      unfold measure ; simpl.
      monoid_tac ; auto.
      induction mid ; simpl in * ; monoid_tac ; auto ; try discriminate.
      destruct l ; simpl ; try discriminate.
      program_simpl ; destruct (view_L mid) ; simpl ; try discriminate.
    Qed.

    Next Obligation.
    Proof.
      intros. monoid_tac. rewrite <- monoid_append_ass. f_equal.
      symmetry in Heq_anonymous.
      apply view_L_cons in Heq_anonymous.
      subst. rewrite nodeMeasure_digits. reflexivity.
    Qed.

  End view_L.
  (* end hide *)
  (* begin hide *)
  Section view_R.

    Inductive View_R `{ma :! Measured v A} (seq : forall A (ma : Measured v A), v -> Type)  : Type := 
    | nil_R : View_R seq
    | cons_R : forall s : v, seq A ma s -> A -> View_R seq.
    
    Implicit Arguments nil_R [A ma seq].
    Implicit Arguments cons_R [A ma seq s].

    Program Fixpoint view_R `{ma :! Measured v A} (s : v) (t : fingertree A s) {struct t} : 
      View_R fingertree := 
      match t with
        | Empty => nil_R 
        | Single x => cons_R Empty x
        | Deep pr st' t' sf => 
          match sf with
            | One x => match view_R t' with
                         | nil_R => cons_R (digit_to_tree pr) x
                         | cons_R st' t' a => cons_R (Deep pr t' (node_to_digit a)) x
                       end
            | y => cons_R (Deep pr t' (digit_liat y)) (digit_last y)
          end
      end.

    Next Obligation of view_R.
    Proof.
      intros.
      destruct sf ; simpl in * ; auto.
      intro ; apply (H a) ; auto.
    Defined.

    Lemma view_R_case : forall `{ma :! Measured v A} (s : v) (t : fingertree A s), view_R t = nil_R \/ 
      exists st', exists t' : fingertree A st', exists x,  view_R t = cons_R t' x.
    Proof.
      intros.
      destruct (view_R t) ; simpl ; intuition ; auto.
      right.
      exists s0 ; exists f ; exists a ; auto.
    Qed.

    Lemma view_R_nil : forall `{ma :! Measured v A} (s : v) (t : fingertree A s), 
      view_R t = nil_R -> s = ε.
    Proof.
      intros.
      induction t ; simpl in * ; try discriminate ; auto.
      destruct r ; simpl  in * ; try discriminate ; auto.
      program_simpl ; destruct (view_R t) ; simpl  in * ; try discriminate ; auto.
    Qed.

    Lemma view_R_cons : forall `{ma :! Measured v A} (s : v) (t : fingertree A s), 
      forall st' (t' : fingertree A st') x, view_R t = cons_R t' x -> s = st' ∙ measure x.
    Proof.
      induction t ; program_simpl ; intros ; simpl in * ; try discriminate ; auto.
      unfold measure ; simpl ; monoid_tac ; auto.

      program_simpl ; destruct r ; simpl  in * ; try discriminate ; monoid_tac ; auto ; 
        try (inversion H ; subst ; simpl ; unfold measure ; simpl ; monoid_tac ; auto).

      destruct (view_R_case t).
      rewrite H0 in H.
      inversion H ; subst ; simpl ; unfold measure ; simpl ; monoid_tac ; auto. 
      rewrite (view_R_nil _ H0) ; unfold measure ; simpl ; monoid_tac ; auto.

      destruct H0 as [st [t'' [x'' H0]]].
      rewrite H0 in H ; simpl.
      inversion H ; simpl ; subst.
      rewrite (IHt _ _ _ H0).
      monoid_tac. repeat f_equal. rewrite <- nodeMeasure_digits ; auto.
    Qed.

    Program Definition deep_R `{ma :! Measured v A} (pr : digit A) (s : v) (mid : fingertree (node A) s) (d : option (digit A))
      : fingertree A (measure pr ∙ s ∙ measure d) :=
      match d with
        | Some sf => Deep pr mid sf
        | None =>  
          match view_R mid with
            | nil_R => digit_to_tree pr
            | cons_R sm' m' a => Deep pr m' (node_to_digit a)
          end
      end.
    
   Next Obligation.
    Proof.
      intros.
      unfold measure ; simpl.
      cut(s = ε) ; intros ; subst.
      monoid_tac ; auto.
      apply (view_R_nil mid) ; auto.
    Qed.

    Next Obligation.
    Proof.
      intros. f_equal. monoid_tac. symmetry in Heq_anonymous. apply view_R_cons in Heq_anonymous. subst.
      rewrite nodeMeasure_digits. reflexivity.
    Qed.
  
  End view_R.
  (* end hide *)
  (** *** De retour à la normale
     %\label{sec:Back_To_Normal}%
     À l'aide de ces vues, on peut maintenant implémenter facilement les opérations de
     %\eng{deque}% sur le type [fingertree]. On n'a pas besoin de récursion ici, on peut
     donc définir ces opérations sur un type [A], une mesure [measure] et un index [s] fixés
     dans une section.

     *)
  
  Section View.
    Context `{ma :! Measured v A} (s : v).

    (** On définit un prédicat [isEmpty] pour les fonctions définies seulement sur les arbres non vides.
       Cette fois-ci, on ne filtre pas directement sur l'objet mais sur la vue pour maintenir l'abstraction
       vis-à-vis de l'implémentation. *)

    Definition isEmpty (t : fingertree A s) := 
      match view_L t with nil_L => True | _ => False end.
    
    (** On peut évidemment décider si un arbre est vide ou non. *)
    
    Definition isEmpty_dec (t : fingertree A s) : { isEmpty t } + { ~ isEmpty t }.
    Proof.
      intros.
      unfold isEmpty.
      destruct (view_L t) ; simpl ; 
        intuition.
    Defined.

    (** Les opérations évidentes sont définissables, on montre la fonction [liat] duale de [tail].
       Ici on retourne une mesure accompagnée d'un [fingertree] dans une paire dépendante de type
       [{s : v & fingertree A s}], qui correspond bien à la vue de la mesure comme une donnée et
       pas seulement un indice qui raffine le type de données.
       On note la construction d'une telle paire d'un arbre [t] avec sa mesure [m] par [m :| t], qui
       se lit "[m] mesure [t]". *)  
    (* begin hide *)

    Obligation Tactic := idtac.

    Program Definition head (t : fingertree A s | ~ isEmpty t) : A :=
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
    Program Definition tail (t : fingertree A s | ~ isEmpty t) : { s' : v & fingertree A s' } :=
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

    Program Definition last (t : fingertree A s | ~ isEmpty t) : A :=
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

    Program Definition liat (t : fingertree A s | ~ isEmpty t) 
      : { s' : v & fingertree A s' } := 
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

    Lemma isEmpty_ε : forall `{ma :! Measured v A} (s : v) (t : fingertree A s), 
      isEmpty t -> s = ε.
    Proof.
      intros; induction t ; simpl in * ; auto with exfalso.
      unfold isEmpty in H ; simpl in H.
      destruct l ; simpl ; auto ; try contradiction. 
      program_simpl ; destruct (view_L t) ; simpl in * ; try contradiction.
    Qed.
    
    Lemma not_isEmpty_Deep : forall `{ma :! Measured v A} pr sm 
      (m : fingertree (node A) sm) sf, ~ isEmpty (Deep pr m sf).
    Proof.
      intros.
      unfold isEmpty.
      destruct pr ; simpl in * ; auto ; try discriminate.
      destruct (view_L m) ; simpl in * ; auto ; try discriminate.
    Qed.
    
    Lemma isEmpty_JMeq_Empty : forall `{ma :! Measured v A} (s : v) (t : fingertree A s), 
      isEmpty t -> JMeq t Empty.
    Proof.
      intros.
      induction t.
      apply JMeq_refl.
      simpl in H ; try contradiction.
      program_simpl ; pose (not_isEmpty_Deep l t r). 
      elim n.
      assumption.
    Qed.
    
    Lemma isEmpty_Empty : forall `{ma :! Measured v A} (t : fingertree A ε), 
      isEmpty t -> t = Empty.
    Proof.
      intros.
      pose (isEmpty_JMeq_Empty t H).
      apply JMeq_eq ; auto.
    Qed.
  End isEmpty_Facts.

  Section Cat.
  (** Concatenation still using digits. *)
    Obligation Tactic := 
      intros ; monoid_tac ; auto ;
        program_simpl ; unfold measure ; simpl ; program_simpl ; monoid_tac ; auto.

    (* Too long to check interactively (2min) *)

    Time Program Fixpoint appendTree0 `{ma :! Measured v A} (xsm : v) (xs : fingertree A xsm)
      (ysm : v) (ys : fingertree A ysm) {struct xs} : fingertree A (xsm ∙ ysm) :=
      match xs in fingertree _ xsm, ys in fingertree _ ysm return fingertree A (xsm ∙ ysm) with
        | Empty, ys => ys
        | xs, Empty => xs
        | Single x, ys => add_left x ys
        | xs, Single y => add_right xs y
        | Deep pr xsm xs sf, Deep pr' ysm ys sf' => 
          let f :=
            match sf return fingertree (node A) (xsm ∙ measure sf ∙ measure pr' ∙ ysm) with
              | One a =>
                match pr' return fingertree (node A) (xsm ∙ measure (One a) ∙ measure pr' ∙ ysm) with
                  | One b => appendTree1 xs (node2 a b) ys
                  | Two b c => appendTree1 xs (node3 a b c) ys
                  | Three b c d => appendTree2 xs (node2 a b) (node2 c d) ys
                  | Four b c d e => appendTree2 xs (node3 a b c) (node2 d e) ys
                end
              | Two a b =>
                match pr' return fingertree (node A) (xsm ∙ measure (Two a b) ∙ measure pr' ∙ ysm) with
                  | One c => appendTree1 xs (node3 a b c) ys
                  | Two c d => appendTree2 xs (node2 a b) (node2 c d) ys
                  | Three c d e => appendTree2 xs (node3 a b c) (node2 d e) ys
                  | Four c d e f => appendTree2 xs (node3 a b c) (node3 d e f) ys
                end
              | Three a b c =>
                match pr' return fingertree (node A) (xsm ∙ measure (Three a b c) ∙ measure pr' ∙ ysm) with
                  | One d => appendTree2 xs (node2 a b) (node2 c d) ys
                  | Two d e => appendTree2 xs (node3 a b c) (node2 d e) ys
                  | Three d e f => appendTree2 xs (node3 a b c) (node3 d e f) ys
                  | Four d e f g => appendTree3 xs (node3 a b c) (node2 d e) (node2 f g) ys
                end
              | Four a b c d =>
                match pr' return fingertree (node A) (xsm ∙ measure (Four a b c d) ∙ measure pr' ∙ ysm) with
                  | One e => appendTree2 xs (node3 a b c) (node2 d e) ys
                  | Two e f => appendTree2 xs (node3 a b c) (node3 d e f) ys
                  | Three e f g => appendTree3 xs (node3 a b c) (node2 d e) (node2 f g) ys
                  | Four e f g h => appendTree3 xs (node3 a b c) (node3 d e f) (node2 g h) ys
                end
            end
            in
            Deep pr f sf'
      end

    with appendTree1 `{ma :! Measured v A} (xsm : v) (xs : fingertree A xsm) (x : A)
      (ysm : v) (ys : fingertree A ysm) {struct xs} : fingertree A (xsm ∙ measure x ∙ ysm) :=
      match  xs in fingertree _ xsm, ys in fingertree _ ysm return fingertree A (xsm ∙ measure x ∙ ysm) with
        | Empty, ys => add_left x ys
        | xs, Empty => add_right xs x
        | Single x', ys => add_left x' (add_left x ys)
        | xs, Single y' => add_right (add_right xs x) y'
        | Deep pr xsm xs dl, Deep dr ysm ys sf' => 
          let addDigits1 := 
            match dl return fingertree (node A) (xsm ∙ measure dl ∙ measure x ∙ measure dr ∙ ysm) with
              | One a => 
                match dr return fingertree (node A) (xsm ∙ measure (One a) ∙ measure x ∙ measure dr ∙ ysm) with 
                  | One b => appendTree1 xs (node3 a x b) ys
                  | Two b c => appendTree2 xs (node2 a x) (node2 b c) ys
                  | Three b c d => appendTree2 xs (node3 a x b) (node2 c d) ys
                  | Four b c d e => appendTree2 xs (node3 a x b) (node3 c d e) ys
                end
              | Two a b =>
                match dr return fingertree (node A) (xsm ∙ measure (Two a b) ∙ measure x ∙ measure dr ∙ ysm) with 
                  | One c => appendTree2 xs (node2 a b) (node2 x c) ys
                  | Two c d => appendTree2 xs (node3 a b x) (node2 c d) ys
                  | Three c d e => appendTree2 xs (node3 a b x) (node3 c d e) ys
                  | Four c d e f => appendTree3 xs (node3 a b x) (node2 c d) (node2 e f) ys
                end
              | Three a b c =>
                match dr return fingertree (node A) (xsm ∙ measure (Three a b c) ∙ measure x ∙ measure dr ∙ ysm) with 
                  | One d => appendTree2 xs (node3 a b c) (node2 x d) ys
                  | Two d e => appendTree2 xs (node3 a b c) (node3 x d e) ys
                  | Three d e f => appendTree3 xs (node3 a b c) (node2 x d) (node2 e f) ys
                  | Four d e f g => appendTree3 xs (node3 a b c) (node3 x d e) (node2 f g) ys
                end
              | Four a b c d =>
                match dr return fingertree (node A) (xsm ∙ measure (Four a b c d) ∙ measure x ∙ measure dr ∙ ysm) with 
                  | One e => appendTree2 xs (node3 a b c) (node3 d x e) ys
                  | Two e f => appendTree3 xs (node3 a b c) (node2 d x) (node2 e f) ys
                  | Three e f g => appendTree3 xs (node3 a b c) (node3 d x e) (node2 f g) ys
                  | Four e f g h => appendTree3 xs (node3 a b c) (node3 d x e) (node3 f g h) ys
                end
            end
            in Deep pr addDigits1 sf'
      end
      
    with appendTree2 `{ma :! Measured v A} (xsm : v) (xs : fingertree A xsm) (x y : A) (ysm : v) (ys : fingertree A ysm) {struct xs} 
      : fingertree A (xsm ∙ measure x ∙ measure y ∙ ysm) :=
      match xs in fingertree _ xsm, ys in fingertree _ ysm return fingertree A (xsm ∙ measure x ∙ measure y ∙ ysm) with
        | Empty, ys => add_left x (add_left y ys)
        | xs, Empty => add_right (add_right xs x) y
        | Single x', ys => add_left x' (add_left x (add_left y ys))
        | xs, Single y' => add_right (add_right (add_right xs x) y) y'
        | Deep pr xsm xs dl, Deep dr ysm ys sf' => 
          let addDigits2 :=
            match dl return fingertree (node A) (xsm ∙ measure dl ∙ measure x ∙ measure y ∙ measure dr ∙ ysm) with 
              | One a => 
                match dr return fingertree (node A) (xsm ∙ measure (One a) ∙ measure x ∙ measure y ∙ measure dr ∙ ysm) with 
                  | One b => appendTree2 xs (node2 a x) (node2 y b) ys
                  | Two b c => appendTree2 xs (node3 a x y) (node2 b c) ys
                  | Three b c d => appendTree2 xs (node3 a x y) (node3 b c d) ys
                  | Four b c d e => appendTree3 xs (node3 a x y) (node2 b c) (node2 d e) ys
                end
              | Two a b =>
                match dr return fingertree (node A) (xsm ∙ measure (Two a b) ∙ measure x ∙ measure y ∙ measure dr ∙ ysm) with 

                  | One c => appendTree2 xs (node3 a b x) (node2 y c) ys
                  | Two c d => appendTree2 xs (node3 a b x) (node3 y c d) ys
                  | Three c d e => appendTree3 xs (node3 a b x) (node2 y c) (node2 d e) ys
                  | Four c d e f => appendTree3 xs (node3 a b x) (node3 y c d) (node2 e f) ys
                end
              | Three a b c =>
                match dr return fingertree (node A) (xsm ∙ measure (Three a b c) ∙ measure x ∙ measure y ∙ measure dr ∙ ysm) with 

                  | One d => appendTree2 xs (node3 a b c) (node3 x y d) ys
                  | Two d e => appendTree3 xs (node3 a b c) (node2 x y) (node2 d e) ys
                  | Three d e f => appendTree3 xs (node3 a b c) (node3 x y d) (node2 e f) ys
                  | Four d e f g => appendTree3 xs (node3 a b c) (node3 x y d) (node3 e f g) ys
                end
              | Four a b c d =>
                match dr return fingertree (node A) (xsm ∙ measure (Four a b c d) ∙ measure x ∙ measure y ∙ measure dr ∙ ysm) with 

                  | One e => appendTree3 xs (node3 a b c) (node2 d x) (node2 y e) ys
                  | Two e f => appendTree3 xs (node3 a b c) (node3 d x y) (node2 e f) ys
                  | Three e f g => appendTree3 xs (node3 a b c) (node3 d x y) (node3 e f g) ys
                  | Four e f g h => appendTree4 xs (node3 a b c) (node3 d x y) (node2 e f) (node2 g h) ys
                end
            end
            in Deep pr addDigits2 sf'
      end


    with appendTree3 `{ma :! Measured v A} (xsm : v) (xs : fingertree A xsm) (x y z : A) (ysm : v) (ys : fingertree A ysm) {struct xs}
      : fingertree A (xsm ∙ measure x ∙ measure y ∙ measure z ∙ ysm) :=
      match xs in fingertree _ xsm, ys in fingertree _ ysm return fingertree A (xsm ∙ measure x ∙ measure y ∙ measure z ∙ ysm) with
        | Empty, ys => add_left x (add_left y (add_left z ys))
        | xs, Empty => add_right (add_right (add_right xs x) y) z
        | Single x', ys => add_left x' (add_left x (add_left y (add_left z ys)))
        | xs, Single y' => add_right (add_right (add_right (add_right xs x) y) z) y'
        | Deep pr xsm xs dl, Deep dr ysm ys sf' =>
          let addDigits3 := 
            match dl return fingertree (node A) (xsm ∙ measure dl ∙ measure x ∙ measure y ∙ measure z ∙ measure dr ∙ ysm) with 
              | One a => 
                match dr return fingertree (node A) (xsm ∙ measure (One a) ∙ measure x ∙ measure y ∙ measure z ∙ measure dr ∙ ysm) with 
                  | One b => appendTree2 xs (node3 a x y) (node2 z b) ys
                  | Two b c => appendTree2 xs (node3 a x y) (node3 z b c) ys
                  | Three b c d => appendTree3 xs (node3 a x y) (node2 z b) (node2 c d) ys
                  | Four b c d e => appendTree3 xs (node3 a x y) (node3 z b c) (node2 d e) ys
                end
              | Two a b =>
                match dr return fingertree (node A) (xsm ∙ measure (Two a b) ∙ measure x ∙ measure y ∙ measure z ∙ measure dr ∙ ysm) with 
                  | One c => appendTree2 xs (node3 a b x) (node3 y z c) ys
                  | Two c d => appendTree3 xs (node3 a b x) (node2 y z) (node2 c d) ys
                  | Three c d e => appendTree3 xs (node3 a b x) (node3 y z c) (node2 d e) ys
                  | Four c d e f => appendTree3 xs (node3 a b x) (node3 y z c) (node3 d e f) ys
                end
              | Three a b c =>
                match dr return fingertree (node A) (xsm ∙ measure (Three a b c) ∙ measure x ∙ measure y ∙ measure z ∙ measure dr ∙ ysm) with 
                  | One d => appendTree3 xs (node3 a b c) (node2 x y) (node2 z d) ys
                  | Two d e => appendTree3 xs (node3 a b c) (node3 x y z) (node2 d e) ys
                  | Three d e f => appendTree3 xs (node3 a b c) (node3 x y z) (node3 d e f) ys
                  | Four d e f g => appendTree4 xs (node3 a b c) (node3 x y z) (node2 d e) (node2 f g) ys
                end
              | Four a b c d =>
                match dr return fingertree (node A) (xsm ∙ measure (Four a b c d) ∙ measure x ∙ measure y ∙ measure z ∙ measure dr ∙ ysm) with 
                  | One e => appendTree3 xs (node3 a b c) (node3 d x y) (node2 z e) ys
                  | Two e f => appendTree3 xs (node3 a b c) (node3 d x y) (node3 z e f) ys
                  | Three e f g => appendTree4 xs (node3 a b c) (node3 d x y) (node2 z e) (node2 f g) ys
                  | Four e f g h => appendTree4 xs (node3 a b c) (node3 d x y) (node3 z e f) (node2 g h) ys
                end
            end
            in Deep pr addDigits3 sf'
      end

    with appendTree4 `{ma :! Measured v A} (xsm : v) (xs : fingertree A xsm) (x y z w : A) (ysm : v) (ys : fingertree A ysm) {struct xs} 
      : fingertree A (xsm ∙ measure x ∙ measure y ∙ measure z ∙ measure w ∙ ysm) :=
      match xs in fingertree _ xsm, ys in fingertree _ ysm return fingertree A (xsm ∙ measure x ∙ measure y ∙ measure z ∙ measure w ∙ ysm) with
        | Empty, ys => add_left x (add_left y (add_left z (add_left w ys)))
        | xs, Empty => add_right (add_right (add_right (add_right xs x) y) z) w 
        | Single x', ys => add_left x' (add_left x (add_left y (add_left z (add_left w ys))))
        | xs, Single y' => add_right (add_right (add_right (add_right (add_right xs x) y) z) w) y'
        | Deep pr xsm xs dl, Deep dr ysm ys sf' =>
          let addDigits4 := 
            match dl return fingertree (node A) (xsm ∙ measure dl ∙ measure x ∙ measure y ∙ measure z ∙ measure w ∙ measure dr ∙ ysm) with 
              | One a => 
                match dr return fingertree (node A) (xsm ∙ measure (One a) ∙ measure x ∙ measure y ∙ measure z ∙ measure w ∙ measure dr ∙ ysm) with 

                  | One b => appendTree2 xs (node3 a x y) (node3 z w b) ys
                  | Two b c => appendTree3 xs (node3 a x y) (node2 z w) (node2 b c) ys
                  | Three b c d => appendTree3 xs (node3 a x y) (node3 z w b) (node2 c d) ys
                  | Four b c d e => appendTree3 xs (node3 a x y) (node3 z w b) (node3 c d e) ys
                end
              | Two a b =>
                match dr return fingertree (node A) (xsm ∙ measure (Two a b) ∙ measure x ∙ measure y ∙ measure z ∙ measure w ∙ measure dr ∙ ysm) with 

                  | One c => appendTree3 xs (node3 a b x) (node2 y z) (node2 w c) ys
                  | Two c d => appendTree3 xs (node3 a b x) (node3 y z w) (node2 c d) ys
                  | Three c d e => appendTree3 xs (node3 a b x) (node3 y z w) (node3 c d e) ys
                  | Four c d e f => appendTree4 xs (node3 a b x) (node3 y z w) (node2 c d) (node2 e f) ys
                end
              | Three a b c =>
                match dr return fingertree (node A) (xsm ∙ measure (Three a b c) ∙ measure x ∙ measure y ∙ measure z ∙ measure w ∙ measure dr ∙ ysm) with 

                  | One d => appendTree3 xs (node3 a b c) (node3 x y z) (node2 w d) ys
                  | Two d e => appendTree3 xs (node3 a b c) (node3 x y z) (node3 w d e) ys
                  | Three d e f => appendTree4 xs (node3 a b c) (node3 x y z) (node2 w d) (node2 e f) ys
                  | Four d e f g => appendTree4 xs (node3 a b c) (node3 x y z) (node3 w d e) (node2 f g) ys
                end
              | Four a b c d =>
                match dr return fingertree (node A) (xsm ∙ measure (Four a b c d) ∙ measure x ∙ measure y ∙ measure z ∙ measure w ∙ measure dr ∙ ysm) with 

                  | One e => appendTree3 xs (node3 a b c) (node3 d x y) (node3 z w e) ys
                  | Two e f => appendTree4 xs (node3 a b c) (node3 d x y) (node2 z w) (node2 e f) ys
                  | Three e f g => appendTree4 xs (node3 a b c) (node3 d x y) (node3 z w e) (node2 f g) ys
                  | Four e f g h => appendTree4 xs (node3 a b c) (node3 d x y) (node3 z w e) (node3 f g h) ys
                end
            end in Deep pr addDigits4 sf'
      end.

  End Cat.
  (* end hide *)
  (** ** Concaténation et découpage dépendants.
     On peut aussi définir la concaténation avec un type dépendant exprimant clairement sa spécification.
     L'implémentation est la même que celle d'Hinze & Paterson, excepté qu'on a prouvé les 100 obligations
     générées par %\Program% concernant les mesures.
     Les cinq fonctions mutuellement récursives cachées ici qui définissent [app] ont la particularité d'être
     assez longues (près de 200 lignes au complet) puisqu'elles implémentent une spécialisation de la 
     concaténation comme nous l'avons décrit plus haut %(\S \ref{fts:sec:implem})%.
     On vérifie ici statiquement que la définition est correcte: le type indique qu'on a 
     bien la propriété évidente sur les %\FTs% que la concaténation de deux arbres donne
     un arbre dont la mesure est la concaténation des mesures des deux arbres.
     %\label{def:app}% *)

  Program Definition app `{ma :! Measured v A}
    (xs : v) (x : fingertree A xs) (ys : v) (y : fingertree A ys) : 
    fingertree A (xs ∙ ys) := appendTree0 x y.

  Notation " x +:+ y " := (app x y) (at level 20).
  (* begin hide *)
  Section Split.
  (* end hide *)

  (** La dernière opération, qui a certainement la plus intéressante spéficication
     du développement, est le découpage
     d'un arbre par un prédicat sur sa mesure. On commence par découper un nœud. *)
    
    Section Nodes.
      Context `{ma :! Measured v A}.
      Variables (p : v -> bool) (i : v).

      (* begin hide *)
      Definition node_to_list (n : node A) := digit_to_list (node_to_digit n).
      (* end hide *)
      (** On découpe un nœud [n] par un prédicat [p] en cherchant où celui-ci s'évalue à [true], 
         en commencant par la mesure initiale [i] et en accumulant les mesures des sous-objets de
         gauche à droite. On a simplement copié l'invariant donné dans %\citet*{hinze:FingerTrees}% 
         sans rien y changer. On a simplement ajouté une propriété sur les mesures qui généralise l'équation
         sur [to_list]. Le code est aussi une traduction directe du code %\Haskell% en %\Russell%, on utilise
         juste un produit cartésien au lieu d'un nouveau type inductif [split].
         On a aussi défini une opération [split_digit] avec une spécification similaire.
         *)

      Program Definition split_node (n : node A) : 
      { (l, x, r) : option (digit A) * A * option (digit A) | 
        let ls := measure l in let rs := measure r in 
        measure n = ls ∙ lparr x rparr ∙ rs /\
        node_to_list n = option_digit_to_list l ++ [x] ++ option_digit_to_list r /\
        (l = None \/ p (i ∙ ls) = false) /\
        (r = None \/ p (i ∙ ls ∙ lparr x rparr) = true)} :=
      match n with
        | Node2 x y _ => 
          let i' := i ∙ lparr x rparr in
          if dec (p i') then (None, x, Some (One y))
          else (Some (One x), y, None)
        | Node3 x y z _ =>
          let i' := i ∙ lparr x rparr in
          if dec (p i') then (None, x, Some (Two y z))
          else 
            let i'' := i' ∙ lparr y rparr in
            if dec (p i'') then
              (Some (One x), y, Some (One z))
            else 
              (Some (Two x y), z, None)
      end.
      (* begin hide *)
      Solve Obligations using program_simpl ; intros ;
        try subst l x r ; try subst l x0 r ;
          split ; unfold node_to_list, digit_to_list, node_to_digit ; try splitTac ; auto ;
            destruct n ; program_simpl ;
              inversion Heq_n ; clear Heq_n H ; try subst ; simpl ; monoid_tac ; auto.
      (* end hide *)
    End Nodes.

    (** Le cas le plus intéressant est celui des arbres. Plutôt que de retourner un tuple
       raffiné dans un type sous-ensemble, on définit cette fois une famille inductive [tree_split]
       qui capture l'invariant qu'un découpage est une décomposition d'un [fingertree] préservant sa
       mesure. On ajoute aussi les invariants sur les arbres de gauche et droite vis-à-vis du prédicat. Ils 
       pourront être utilisés par les clients pour prouver des propriétés sur leur code.
       L'inductif [tree_split] est en fait une %\emph{vue}% dépendante d'un arbre. 
       C'est une particularité de la programmation avec types dépendants et de ce développement en particulier:
       on dérive non seulement du code réutilisable mais aussi des preuves réutilisables en utilisant 
       des types riches. En effet, la fonction de découpage peut être vue comme un combinateur de preuves,
       relevant une propriété sur une mesure et un monoïde en une propriété sur les mots de ce monoïde
       représentés par les [fingertree]. *)

    Section Trees.
      (* begin hide *)
      Obligation Tactic := splitTac.
      (* end hide *)
      Variable p : v -> bool.
      
      Inductive tree_split `{ma :! Measured v A} (i : v) : v -> Type :=
        mkTreeSplit : forall (xsm : v) 
          (xs : fingertree A xsm | isEmpty xs \/ p (i ∙ xsm) = false)
          (x : A) (ysm : v) 
          (ys : fingertree A ysm | isEmpty ys \/ p (i ∙ xsm ∙ measure x) = true),
          tree_split i (xsm ∙ measure x ∙ ysm).
      
      (** Ce type inductif combine des types sous-ensemble et dépendants, mais nous pouvons toujours 
         écrire notre code comme d'habitude. Approximativement 100 lignes de preuves sont nécessaires 
         pour décharger les obligations générées par cette définition.

         
         %\label{def:split_tree}\splittreefig{}% *)
      (* begin hide *)
      Program Definition option_digit_to_tree `{ma :! Measured v A} (d : option (digit A)) :
        fingertree A (measure d) :=
        match d with Some x => digit_to_tree x | None => Empty end.

      Obligation Tactic := idtac. (*program_simpl ; intros ; try splitTac ; simpl ; monoid_tac ; auto.*)

      Program Fixpoint split_tree' `{ma :! Measured v A} (i s : v) 
        (t : fingertree A s) (pr : unit | ~ isEmpty t) {struct t} : tree_split i s :=
        match t with
        | Empty => !
        | Single x => mkTreeSplit i Empty x Empty
        | Deep pr smid mid sf => 
          let vpr := i ∙ measure pr in
          if dec (p vpr) then
            let '(l, x, r) := split_digit p i pr in
              mkTreeSplit i (option_digit_to_tree l)
                x (deep_L r mid sf)
          else let vpm := vpr ∙ smid in
            if dec (p vpm) then
              let 'mkTreeSplit mls ml x mrs mr := split_tree' vpr mid tt in
              let '(l, x, r) := split_node p (vpr ∙ mls) x in
                mkTreeSplit i (deep_R pr ml l) x (deep_L r mr sf)
            else
              let vsf := vpm ∙ measure sf in
              let '(l, x, r) := split_digit p vpm sf in
                mkTreeSplit i (deep_R pr mid l) x
                  (option_digit_to_tree r)
        end.

      Obligation Tactic := program_simpl ; intros ; try splitTac ; simpl ; monoid_tac ; auto.
      Solve Obligations.

      Next Obligation.
      Proof. subst t. apply H; constructor. Qed.

      Obligation Tactic := program_simpl.
      Next Obligation.
      Proof. subst t. left; constructor. Qed.
      
      Next Obligation.
      Proof.
        left ; compute ; auto.
      Qed.

      Unset Dependent Propositions Elimination.

      Ltac monoid_tac_in H := autorewrite with monoid in H.

      Next Obligation.
      Proof.
        destruct_call split_digit. program_simpl.
        destruct_conjs.
        simpl_JMeq. subst t.
        destruct H3 ; [left | right] ; auto.
        rewrite H3 ; constructor.
      Qed.
      
      Hint Extern 4 => discriminate : exfalso.

      Next Obligation.
      Proof.
        change (p (i ∙ lparr pr0 rparr) = true) in H. right.
        destruct_call split_digit ; program_simpl.
        destruct_conjs ; simpl_JMeq ; autoinjections.
        destruct o0. destruct H3 ; auto with exfalso. 
        destruct o. destruct H4 ; auto with exfalso. 
        rewrite H1 in H. 
        simpl in H. autorewrite with monoid in H ; auto.

        destruct o. destruct H4; auto with exfalso.
        rewrite H1 in H. monoid_tac_in H. monoid_tac. assumption.
      Qed.
      
      Next Obligation.
      Proof.
        destruct_call split_digit ; program_simpl.
        destruct_conjs ; simpl_JMeq ; autoinjections.
        change (digit_reducel (λ (i : v) (a : A), i ∙ lparr a rparr) ε pr0) with (lparr pr0 rparr) in *.
        rewrite H1 in H. rewrite <- monoid_assoc. rewrite <- monoid_assoc. f_equal.
        rewrite H1. rewrite monoid_assoc. reflexivity.
      Qed.

      Next Obligation.
      Proof.
        destruct (isEmpty_dec mid).
        destruct mid ; unfold isEmpty in i0 ; simpl in i0 ; program_simpl ; auto.
        red ; intros.
        monoid_tac_in H0.
        rewrite H0 in H ; discriminate.

        destruct l ; simpl ; auto.
        destruct (view_L mid) ; simpl ; auto.
        program_simpl ; assumption.
      Qed.

      (** The program simpl tactic is too dangerous, calling subst and autoinjection transforms the goal to much 
         and easily make the guardness criterion checker fail if there are some recursive calls in the context. *)

      Ltac my_simplify :=
        simpl ; intros ; destruct_conjs ; simpl proj1_sig in * ; try discriminates ;
          try (solve [ red ; intros ; destruct_conjs ; autoinjections ; discriminates ]).

      Obligation Tactic := my_simplify.

      Opaque measure.

      Next Obligation.
      Proof.
        clear split_tree' Heq_anonymous.
        right.
        destruct_call split_node in Heq_anonymous0. simpl in *. subst.
        program_simpl.
        destruct_nondep H2 ; monoid_tac_in H2 ;auto.
        assert (He:=isEmpty_ε _ H8).
        subst mls.
        destruct H6 ; monoid_tac_in H6 ; monoid_tac ; auto.
        subst l.
        simpl in * ; monoid_tac ; auto.
        
        destruct H6 ; monoid_tac_in H8 ; monoid_tac ; auto.
        subst l.
        simpl in * ; monoid_tac ; auto.
        
        monoid_tac_in H6 ; auto.
      Defined.

      Next Obligation.
      Proof.
        clear Heq_anonymous split_tree'.
        right.
        destruct_call split_node.
        simpl in *. subst x1 ; program_simpl.
        simpl_JMeq ; subst ; monoid_tac.
        destruct H7 ; monoid_tac_in H7 ; auto.
        rewrite H7 in * ; clear H7.
        simpl in * ; monoid_tac_in H4.
        rewrite <- H4.
        destruct H1.
        assert (He:=isEmpty_ε _ H1).
        subst mrs.
        monoid_tac_in H0 ; auto.
        rewrite <- H1 ; monoid_tac ; auto.
      Defined.
      
      Next Obligation.
      Proof.
        clear Heq_anonymous.
        destruct_call split_node.
        simpl in * ; subst x1.
        monoid_tac.
        program_simpl ; destruct_pairs.
        rewrite H4.
        monoid_tac ; reflexivity.
      Defined.

      Next Obligation.
      Proof.
        destruct_call split_digit.
        simpl in *. subst x0 ; program_simpl.
        right.
        destruct H4 as [H4|H4] ; subst ; try monoid_tac_in H4 ; auto.
        simpl in H2; monoid_tac_in H2.
        simpl ; monoid_tac.
        monoid_tac_in H0 ; auto.
      Qed.

      Next Obligation.
      Proof.
        destruct_call split_digit as [ [[l' x'] r'] ].
        simpl in *. program_simpl.
        monoid_tac.
        destruct_pairs.
        destruct H5 as [H5|H5] ; subst ; try monoid_tac_in H5 ; auto.
        left ; simpl. split.
      Qed.

      Next Obligation.
      Proof.
        destruct_call split_digit as [ [ [ l' x' ] r' ] ]. 
        simpl in * ; program_simpl.
        monoid_tac. rewrite H2. auto.
      Qed.
      
      Transparent measure.
      Obligation Tactic := program_simpl.
      Program Definition split_tree `{ma :! Measured v A}
        (i s : v) (t : fingertree A s | ~ isEmpty t) :
        tree_split i s := split_tree' i t tt.
    End Trees.
  End Split.
  (* end hide *)

  (** Ceci conclut notre implémentation des %\FTs% dépendants avec %\Program%. Pour résumer,
     nous avons prouvé que:
     - Toutes les fonctions sont totales une fois annotées par leurs préconditions.
     - Toutes les fonctions respectent la sémantique des mesures qui est rendue explicite dans les types
     alors qu'elle était auparavant implicite dans le code.
     - Toutes les fonctions respectent les invariants donnés dans le papier original
     par Hinze & Paterson. *)
(* begin hide *)
End DependentFingerTree.
(* end hide *)
