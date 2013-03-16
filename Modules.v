Module Type Monoid.
  
  Parameter m : Type.
  
  Parameter mempty : m.
  Parameter mappend : m -> m -> m.

  Notation " x 'cdot' y " := (mappend x y) (right associativity, at level 20).
  Notation epsilon := mempty.
  
  Axiom monoid_id_l : forall x, epsilon cdot x = x.
  Axiom monoid_id_r : forall x, x cdot epsilon = x.
  Axiom monoid_assoc : forall x y z, (x cdot y) cdot z = x cdot y cdot z.

  Hint Rewrite monoid_id_r monoid_id_l monoid_assoc : monoid.

  Ltac monoid_tac_in H := repeat rewrite monoid_id_r in H ; repeat rewrite monoid_id_l in H ; repeat rewrite monoid_assoc in H.

  Ltac simpl_monoid := autorewrite with monoid in *.

  Ltac monoid_tac := repeat rewrite monoid_id_r ; repeat rewrite monoid_id_l ; repeat rewrite monoid_assoc.

End Monoid.

Module Type Measured.
  Parameter A : Type.
  Declare Module Mon : Monoid.

  Parameter measure : A -> Mon.m.

End Measured.
