Set Implicit Arguments.
Require Import Coq.subtac.Utils.
Require Import Omega.

Program Fixpoint div2 (n : nat) : 
  { n' : nat | n = 2 * n' \/ n = 2 * n' + 1 } :=
  match n with
    | S (S p) => S (div2 p)
    | x => 0
  end.

Next Obligation.
Proof.
  intros.
  destruct_call div2.
  clear div2.
  simpl ; destruct o as [o|o] ; subst p ; simpl ; intuition.
Defined.

Next Obligation.
  destruct n ; simpl in * ; intuition.
  destruct n ; simpl in * ; intuition.
  elim (H n) ; auto.
Qed.
  
Print div2.
    

Inductive sig (A : Set) (P : A -> Prop) : Set :=
| exist : forall (a : A), P a -> sig P.

Require Import List.
Definition vector A n := { x : list A | length x = n }.

Inductive vector (A : Set) : nat -> Set :=
| vnil : vector A 0
| vcons : A -> forall n, vector A n -> vector A (S n).


Inductive pow_list (A : Set) : Set :=
| pow_nil : pow_list A
| pow_cons : A -> pow_list (A * A) -> pow_list A.

Notation "'pow_nil'" := (@pow_nil _).

Fixpoint pow_map (A B : Set) (f : A -> B) 
  (l : pow_list A) { struct l } : pow_list B := 
  match l with
    | pow_nil => pow_nil
    | pow_cons hd tl => pow_cons (f hd) 
      (pow_map (fun x => (f (fst x), f (snd x))) tl)
  end.

Inductive list (A : Set) : Set :=
| nil : list A
| cons : A -> list A -> list A.
Notation "'nil'" := (@nil _).
 

Fixpoint map (A B : Set) (f : A -> B) (l : list A) : list B :=
  match l with
    | cons hd tl => cons (f hd) (map f tl)
    | nil => nil
  end.

Notation " g 'o' f " := (fun x => g (f x)) (at level 20, left associativity).

Lemma map_cons : forall (A B C : Set) (f : A -> B) (g : B -> C) x l, 
  map g (map f (cons x l)) = map (g o f) l.







(* Fixpoint pow_map (A B : Set) (f : A -> B)  *)
(*   (l : pow_list A) { struct l } : pow_list B :=  *)
(*   match l with *)
(*     | pow_nil => pow_nil B *)
(*     | pow_cons hd tl => pow_cons B (f hd)  *)
(*       (pow_map (A * A) (B * B)  *)
(*         (fun x : A * A => (f (fst x), f (snd x))) tl) *)
(*   end. *)

