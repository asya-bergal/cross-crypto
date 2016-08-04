Set Implicit Arguments.
Unset Strict Implicit.

Require Import Coq.Lists.List.
Import ListNotations.

Require Import CrossCrypto.FrapTactics.

Inductive tuple (T : Type) : nat -> Type :=
| tuple_nil : tuple T 0
| tuple_cons : forall {n}, T -> tuple T n -> tuple T (S n).

Notation " t[] " := (tuple_nil _).
Infix "t::" := tuple_cons (at level 60, right associativity).

Fixpoint tnth n A (t : tuple A n) i (H : i < n) : A.
  cases i; cases n; try linear_arithmetic.
  inversion t.
  exact X.
  inversion t.
  refine (tnth n A X0 i _).
  linear_arithmetic.
Defined.

Fixpoint tfirstn n A (t : tuple A n) (i : nat) (H : i <= n) : tuple A i.
  cases i.
  exact (t[]).
  cases n.
  linear_arithmetic.
  inversion t.
  refine (X t:: (tfirstn n A X0 i _)).
  linear_arithmetic.
Defined.

Fixpoint tskipn n A (t : tuple A n) (i : nat) : tuple A (n - i)%nat.
  cases i.
  assert (n - 0 = n).
  linear_arithmetic.
  rewrite H.
  exact t.
  cases n.
  exact t.
  inversion t.
  exact (tskipn n A X0 i).
Defined.

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

Fixpoint list2tuple T (l : list T) : tuple T (length l):=
  match l with
    | [] => t[]
    | x :: xs => x t:: list2tuple xs
  end.

Fixpoint tuple2list T n (t : tuple T n) : list T :=
  match t with
  | t[] => []
  | x t:: xs => x :: tuple2list xs
  end.

Lemma tuple2list_len : forall T n (t : tuple T n), length (tuple2list t) = n.
Proof.
  induct t; simplify; equality.
Qed.

Inductive htuple : forall n : nat, tuple Type n -> Type :=
| htuple_nil : htuple t[]
| htuple_cons : forall {n} T (TS : tuple Type n),
                  T -> htuple TS -> htuple (T t:: TS).

Notation " ht[] " := (htuple_nil _).
Infix "ht::" := htuple_cons (at level 60, right associativity).
