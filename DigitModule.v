(* -*- coq-prog-name: "~/research/coq/trunk/bin/coqtop.byte"; coq-prog-args: ("-emacs-U" "-R" "." "FingerTree" "-R" "../../safe" "Safe" "-R" "../../monads" "Monad") -*- *)
(* begin hide *)
Require Import FingerTree.Monoid.
Require Import FingerTree.Notations.
Require Import Coq.Program.Program.
Set Implicit Arguments.
(* end hide *)
(** ** Digits *)
Section Digit.
  Variable A : Type.

  (** A digit is simply a buffer of one to four values. *)

  Inductive digit : Type := 
  | One : A -> digit
  | Two : A -> A -> digit
  | Three : A -> A -> A -> digit
  | Four : A -> A -> A -> A -> digit.
  
  (** We build simple functional predicates on digits for use in specifications. *)

  Definition full (x : digit) := 
    match x with Four _ _ _ _ => True | _ => False  end.

  (* begin hide *)
  Definition single (x : digit) := 
    match x with One _ => True | _ => False end.
  (* end hide *)
  (** We now define addition of an element to the left of a digit. *)

  Program Definition add_digit_left (a : A)
    (d : digit | ~ full d) : digit :=
    match d with
      | One x => Two a x
      | Two x y => Three a x y
      | Three x y z => Four a x y z
      | Four _ _ _ _ => !
    end.

  (** It has become a little more interesting here, as we define our first %\emph{partial}%
     function. We can add to a digit if and only if it is not already full. 
     So, we require the argument digit to be accompanied by a proof that it is not full.
     We will use it to prove that the last branch is inaccessible ; 
     we use the notation ! ('bang') to denote inaccessible program points, which are
     points where [False] can be proved.
     Note that we can pattern-match on 
     [d] as if it was just a digit: properties have no influence on code, only on proofs.
     
     The generated obligation (figure \ref{fig:}) is easily solved, as we have a contradiction in the context: 
     both [~ full d] and [d = Four _ _ _ _] are present.
     We can define in a similar fashion addition on the right and the various 
     accessors on digits ([head], [tail], [last] and [liat]). 
     From now on we will omit the proof scripts used to solve obligations.
     *)


  Next Obligation.
    intros ; simpl in H ; auto.
  Qed.
  
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

Require Import Modules.

(* begin hide *)
Module DigitMeasure(M : Monoid).
  Import M.
  Definition v := M.m.
  
  Section Measure.
    Variable A : Type.
    Variable measure : A -> v.
    Notation " 'lparr' x 'rparr' " := (measure x) (x ident, no associativity).
    
    Definition digit_measure (d : digit A) : v :=
      match d with
        | One x => measure x
        | Two x y => measure x cdot measure y
        | Three x y z => measure x cdot measure y cdot measure z
        | Four x y z w => measure x cdot measure y cdot measure z cdot measure w
      end.
    
    Definition option_measure (A:Type) (measure : A -> v) (x : option A) := 
      match x with Some x => measure x | None => epsilon end.
  End Measure.

  Definition option_digit_measure (A : Type) (measure : A -> v) := 
     option_measure (digit_measure measure).

  Ltac splitTac := 
    program_simpl ; auto with * ; intuition ; try right ; unfold option_measure ; unfold digit_measure ; simpl ; 
      monoid_tac ; auto ; repeat rewrite <- monoid_assoc ; auto.
  
  Obligation Tactic := splitTac.

  Section Digits.
    Variable A : Type.
    Variable measure : A -> v.
    Notation " 'lparr' x 'rparr' " := (measure x) (x ident, no associativity).

    Program Definition get_digit (p : v -> bool) (d : digit A) 
      (i : v | p i = false /\ p (i cdot digit_measure measure d) = true) : 
      { (s, x) : v * A | p s = false /\ p (s cdot lparr x rparr) = true } :=
      match d with
        | One x => (i, x)
        | Two x y => 
          let i' := i cdot lparr x rparr in
            if dec (p i') then (i, x) else (i', y)
        | Three x y z =>
          let i' := i cdot lparr x rparr in
            if dec (p i') then (i, x)
            else
              let i'' := i' cdot lparr y rparr in
              if dec (p i'') then (i', y) else (i'', z)
        | Four x y z w =>
          let i' := i cdot lparr x rparr in
            if dec (p i') then (i, x)
            else
              let i'' := i' cdot lparr y rparr in
              if dec (p i'') then (i', y)
              else
                let i''' := i'' cdot lparr z rparr in
                if dec (p i''') then (i'', z) else  (i''', w)
      end.

    Program Definition split_digit (p : v -> bool) (i : v) (d : digit A) : 
      { (l, x, r) : option (digit A) * A * option (digit A) | 
        digit_measure measure d = option_digit_measure measure l cdot measure x cdot option_digit_measure measure r /\
        (l = None \/ p (i cdot (option_measure (digit_measure measure) l)) = false) /\
        (r = None \/ p (i cdot (option_measure (digit_measure measure) l) cdot (measure x)) = true) } :=
      match d with
        | One x => (None, x, None)
        | Two x y => 
          let i' := i cdot lparr x rparr in
            if dec (p i') then (None, x, Some (One y))
            else (Some (One x), y, None)
        | Three x y z =>
          let i' := i cdot lparr x rparr in
          let i'' := i' cdot lparr y rparr in
            if dec (p i') then
              (None, x, Some (Two y z))
            else if dec (p i'') then
              (Some (One x), y, Some (One z))
            else 
              (Some (Two x y), z, None)
        | Four x y z w =>
          let i' := i cdot lparr x rparr in
            if dec (p i') then
              (None, x, Some (Three y z w))
            else let i'' := i' cdot lparr y rparr in
              if dec (p i'') then
                (Some (One x), y, Some (Two z w))
              else let i''' := i'' cdot lparr z rparr in
                if dec (p i''') then
                  (Some (Two x y), z, Some (One w))
                else 
                  (Some (Three x y z), w, None)
      end.

  End Digits.
End DigitMeasure.

(* end hide *)
