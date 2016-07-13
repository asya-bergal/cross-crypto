Set Implicit Arguments.
Unset Strict Implicit.

Inductive tuple (T : Type) : nat -> Type :=
| tuple_nil : tuple T 0
| tuple_cons : forall n, T -> tuple T n -> tuple T (S n).

Notation " t[] " := (tuple_nil _).
Infix "t::" := tuple_cons (at level 60, right associativity).

Fixpoint tuple_fold n A B (f : A -> B -> B) (t : tuple A n) (b : B) : B :=
  match t with
    | t[] => b
    | x t:: xs => f x (tuple_fold f xs b)
  end.

Fixpoint tuple_map n A B (f : A -> B) (t : tuple A n) : tuple B n :=
  match t with
    | t[] => tuple_nil B
    | x t:: xs => (f x) t:: (tuple_map f xs)
  end.

Fixpoint tuple_append n m T (t : tuple T n) (t' : tuple T m) :
  tuple T (n + m) :=
  match t with
    | t[] => t'
    | x t:: xs => x t:: (tuple_append xs t')
  end.

Inductive htuple : forall n : nat, tuple Type n -> Type :=
| htuple_nil : htuple t[]
| htuple_cons : forall n T (TS : tuple Type n),
                  T -> htuple TS -> htuple (T t:: TS).

Notation " ht[] " := (htuple_nil _).
Infix "ht::" := htuple_cons (at level 60, right associativity).
