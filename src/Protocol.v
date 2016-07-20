Set Implicit Arguments.
Unset Strict Implicit.

Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import Coq.Structures.OrderedType.
Import ListNotations.

Require Import CrossCrypto.FirstOrder.
Require Import CrossCrypto.Tuple.
Require Import CrossCrypto.HList.

Definition head T (l : list T) (H : l <> []) : T.
  destruct l.
  destruct (H eq_refl).
  exact t.
Defined.

Fixpoint repeat A (a : A) n :=
  match n with
    | 0 => []
    | S n => a :: repeat a n
  end.

Fixpoint tuple_to_hlist A (T : A) P n (t : tuple (P T) n)
: hlist P (repeat T n).
  induction t; constructor; assumption.
Defined.

Inductive In_with_tail A : A -> list A -> list A -> Type :=
| Here : forall hd tl, In_with_tail hd tl (hd :: tl)
| Next : forall hd tl x xs, In_with_tail hd tl xs ->
                            In_with_tail hd tl (x :: xs).

Section Protocol.

  Context (sort : Type)
          (func : list sort -> sort -> Type)
          (predicate : list sort -> Type)
          (sbool : sort)
          (message : sort)
          (ite : func (sbool :: message :: message :: []) message)
          (ftrue : func [] sbool)
          (ffalse : func [] sbool)
          (empty_message : func [] message)
          (eq_test : func (message :: message :: []) sbool)
          (equiv : forall (ss : list sort), predicate (ss ++ ss)).

  Notation "'term'" := (term func).
  Notation "'model'" := (model func predicate).

  Variable Q : nat -> Type.
  Variable q0 : Q 0.

  Record transition n := mkTransition {
      from : Q n;
      to : Q (S n);
      output : tuple (term message) n -> term message -> term message;
      guard : tuple (term message) n -> term message -> term sbool
  }.

  Variable transitions : forall n (q : Q n), list (transition n).
  Variable transitions_from : forall n (q : Q n) t,
                                In t (transitions q) -> t.(from) = q.

  Definition final n (q : Q n) : Prop := transitions q = [].

  Definition maximal n (t : transition n) : Prop :=
    forall (is : tuple (term message) n) (i : term message),
      t.(guard) is i = App ftrue h[].

  Definition has_max_transition n (q : Q n) (H : ~final q) : Prop :=
    maximal (head H).

  Variable max_transition : forall n (q : Q n) (H : ~final q),
                              has_max_transition H.

  Variable initial_knowledge : list (term message).

  Variable handles : forall n : nat,
                       func (repeat message (n + length initial_knowledge))
                            message.

  Inductive execution (m : model)
  : forall n, Q n -> tuple (term message) n ->
              tuple (term message) (n + length initial_knowledge)
              -> Type :=
  | Initial : execution m q0 t[] (list_to_tuple initial_knowledge)
  | Transition :
      forall n (q : Q n) (inputs : tuple (term message) n)
             (knowledge : tuple (term message)
                                (n + length initial_knowledge))
             (t : transition n) (l : list (transition n)) q',
        In_with_tail t l (transitions q) ->
        t.(to) = q' ->
        execution m q inputs knowledge ->
        let new_input := (App (handles n)
                              (tuple_to_hlist knowledge)) in
        let new_inputs := new_input t:: inputs in
        let new_knowledge :=
            t.(output) inputs new_input t:: knowledge in
        m.(interp_term) (t.(guard) inputs new_input) =
        m.(interp_term) (App ftrue h[]) ->
        (forall (t' : transition n),
           In t' l ->
           m.(interp_term) (t.(guard) inputs new_input) <>
           m.(interp_term) (App ftrue h[])) ->
        execution m q' new_inputs new_knowledge.

End Protocol.
