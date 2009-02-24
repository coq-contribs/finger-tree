Definition add_digit_right : (A : Type) (d : digit A | ~ full d) (a : A) : digit A.
Definition digit_head : (A : Type) (d : digit A) : A.
Definition digit_tail : (A : Type) (d : digit A | ~ single d) : digit A.
Definition digit_measure : (A : Type) (measure : A -> v) (d : digit A) : v.
Definition tree_size (A : Type) (measure : A -> v) (s : v) (t : fingertree measure s) -> nat.
Definition View_L_size A (measure : A -> v) (view : View_L A (fingertree measure)) -> nat.
