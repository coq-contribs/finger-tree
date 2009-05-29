(* begin hide *)
Require Import FingerTree.Monoid.
Require Import FingerTree.Reduce.
Require Import FingerTree.Notations.
Require Import Coq.Lists.List Coq.Program.Program.
Set Implicit Arguments.
Unset Strict Implicit.
(* end hide *)

(** ** "Doigts"

   Les doigts de nos arbres sont simplement des buffers d'une à quatre valeurs d'un type 
   polymorphe [A].
   *)

Section Digit.
  Variable A : Type.
  Inductive digit : Type := 
  | One : A -> digit
  | Two : A -> A -> digit
  | Three : A -> A -> A -> digit
  | Four : A -> A -> A -> A -> digit.
  
  (** On construit des prédicats simples sur les doigts qu'on va utiliser pour
     spécifier les fonctions partielles. Un [digit] est plein ([full]) lorsqu'il contient 
     déjà quatre valeurs, et [single] lorsqu'il n'en contient qu'une. Notez qu'on utilise
     ici les constructueurs de propositions %\ind{True}% et %\ind{False}% et non pas les constructeurs 
     du type booléen %\constr{true}% et %\constr{false}%.
     *)
  
  Definition full (x : digit) := 
    match x with Four _ _ _ _ => True | _ => False end.
  Definition single (x : digit) := 
    match x with One _ => True | _ => False end.
  
  (** On définit l'addition d'un élément à gauche d'un [digit]. *)

  Program Definition add_digit_left (a : A) (d : digit | ~ full d) : digit :=
    match d with
      | One x => Two a x
      | Two x y => Three a x y
      | Three x y z => Four a x y z
      | Four _ _ _ _ => !
    end.
  (* begin hide *)
  Next Obligation.
    intros ; simpl in H ; auto. 
  Qed.
  (* end hide *)

  (** C'est la première fonction %\emph{partielle}% que l'on définit avec %\Program%. 
     On peut ajouter un élément à un doigt seulement si celui-ci n'est pas déjà plein.
     On requiert donc que l'argument [d] soit accompagné d'une preuve qu'il n'est pas plein.
     On utilise cette preuve pour montrer que le dernier cas est inaccessible, ce qu'on dénote 
     par ! ('bang'). On peut toujours filtrer sur [d] comme sur n'importe quel autre 
     [digit]: les propriétés n'ont aucune influence sur le code, uniquement dans les preuves.
     Au moment du filtrage, une projection est insérée implicitement au typage par l'algorithme 
     de coercion. Ici, la compilation du filtrage de %\Program% fait que l'obligation générée
     (figure %\ref{fig:adddigitleftobl}%) est facilement déchargée.
     
     %\adddigitleftobl%

     On définit de façon similaire l'addition à droite d'un digit et les divers accesseurs sur les
     digits: [digit_head], [digit_last], [digit_tail], [digit_liat]. Ces deux dernières fonctions 
     sont rendues totales en spécifiant que les [digit] en entrée ne doivent pas être des singletons
     ([single]). On définit aussi une instance paramétrique [digit_measure] qui calcule la mesure
     d'un doigt en fonction d'une mesure sur ses éléments. 
     *)
  
  (* begin hide *)  
  Program Definition add_digit_right (d : digit | ~ full d ) (a : A) : digit :=
    match d with
      | One x => Two x a
      | Two x y => Three x y a
      | Three x y z => Four x y z a
      | Four _ _ _ _ => !
    end.
  
  Next Obligation.
  Proof.
    intros ; simpl in H ; elim H ; auto.
  Qed.

  Definition digit_head (d : digit) : A :=
    match d with
      | One x => x
      | Two x _ => x
      | Three x _ _ => x
      | Four x _ _ _ => x
    end.
  
  Program Definition digit_tail (d : digit | ~ single d) : digit :=
    match d with
      | One _ => !
      | Two x y => One y
      | Three x y z => Two y z
      | Four x y z w => Three y z w
    end.

  Next Obligation.
  Proof.
    intros ; simpl in H ; auto.
  Qed.

  Definition digit_last (d : digit) : A :=
    match d with
      | One x => x
      | Two _ x => x
      | Three _ _ x => x
      | Four _ _ _ x => x
    end.
  
  Program Definition digit_liat (d : digit | ~ single d) : digit :=
    match d with
      | One _ => !
      | Two x y => One x
      | Three x y z => Two x y
      | Four x y z w => Three x y z
    end.

  Next Obligation.
  Proof.
    intros ; elim H ; simpl ; auto.
  Qed.

End Digit.

Section DigitReduce.
  Program Definition digit_reducer (X Y : Type) (redr : X -> Y -> Y) (d : digit X) (w : Y) : Y :=
  match d with
  | One x => redr x w
  | Two x y => redr x (redr y w)
  | Three x y z => redr x (redr y (redr z w))
  | Four x y z w' => redr x (redr y (redr z (redr w' w)))
  end.
    
  Program Definition digit_reducel (X Y : Type) (redl : Y -> X -> Y) (w : Y) (d : digit X) : Y :=
    match d with
    | One x => redl w x
    | Two x y => redl (redl w x) y
    | Three x y z => redl (redl (redl w x) y) z
    | Four x y z w' => redl (redl (redl (redl w x) y) z) w'
    end.
    
  Definition digitReduce := mkReduce digit_reducer digit_reducel.

  Context {A:Type}.
  Definition digit_to_list (x : digit A) : list A := toList digitReduce _ x.
  
  Definition option_digit_to_list (x : option (digit A)) : list A := match x with None => [] | Some x => digit_to_list x end.

End DigitReduce.

Ltac monoid_tac := autorewrite with monoid.

(* begin hide *)
Section Notations.
  Context `{m : Monoid v}.

  Global Instance digit_measure `(Measured v A) : Measured v (digit A) :=
    { measure := digit_reducel (fun i a => i ∙ lparr a rparr) ε }.

  Ltac splitTac := 
    unfold measure ; program_simpl ; intuition ; try right ; unfold measure, option_measure, digit_measure ; simpl ; 
      monoid_tac ; auto ; repeat rewrite <- monoid_append_ass ; auto.
  
  Obligation Tactic := splitTac.

  Section Digits.
    Context `{ms : !Measured v A}.

    Program Definition split_digit (p : v -> bool) (i : v) (d : digit A) : 
      { (l, x, r) : option (digit A) * A * option (digit A) | 
        measure d = measure l ∙ measure x ∙ measure r /\
        digit_to_list d = option_digit_to_list l ++ [x] ++ option_digit_to_list r /\
        (l = None \/ p (i ∙ measure l) = false) /\
        (r = None \/ p (i ∙ measure l ∙ measure x) = true) } :=
      match d with
        | One x => (None, x, None)
        | Two x y => 
          let i' := i ∙ lparr x rparr in
            if dec (p i') then (None, x, Some (One y))
            else (Some (One x), y, None)
        | Three x y z =>
          let i' := i ∙ lparr x rparr in
          let i'' := i' ∙ lparr y rparr in
            if dec (p i') then
              (None, x, Some (Two y z))
            else if dec (p i'') then
              (Some (One x), y, Some (One z))
            else 
              (Some (Two x y), z, None)
        | Four x y z w =>
          let i' := i ∙ lparr x rparr in
            if dec (p i') then
              (None, x, Some (Three y z w))
            else let i'' := i' ∙ lparr y rparr in
              if dec (p i'') then
                (Some (One x), y, Some (Two z w))
              else let i''' := i'' ∙ lparr z rparr in
                if dec (p i''') then
                  (Some (Two x y), z, Some (One w))
                else 
                  (Some (Three x y z), w, None)
      end.
  
  End Digits.
End Notations.

Ltac splitTac := 
  unfold measure ; program_simpl ; intuition ; try right ; unfold measure, option_measure, digit_measure ; simpl ; 
    monoid_tac ; auto ; repeat rewrite <- monoid_append_ass ; auto.
(* end hide *)
