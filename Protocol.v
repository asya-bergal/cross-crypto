Set Implicit Arguments.
Unset Strict Implicit.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import Coq.Structures.OrderedType.
Import ListNotations.

Load FirstOrder.
Load Tuple.

Definition head T (l : list T) (H : l <> []) : T.
  destruct l.
  destruct (H eq_refl).
  exact t.
Defined.

Parameter sbool : sort.
Parameter message : sort.
Parameter ite : func (sbool :: message :: message :: []) message.
Parameter ftrue : func [] sbool.
Parameter ffalse : func [] sbool.
Parameter empty_message : func [] message.
Parameter eq_test : func (message :: message :: []) sbool.
Parameter equiv : forall (ss : list sort), predicate (ss ++ ss).

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

(*
s is a function from variables to term
theta is a function from variables to Formula
control state with transition such that ordering is reasonable
gg
set of states

*)
Section Protocol.

  Variable Q : Type.
  Variable Q_gt : Q -> Q -> Prop.
  Infix "Q>" := Q_gt (at level 70).

  Variable q0 : Q.

  Record transition := mkTransition {
      from : Q;
      to : Q;
      transition_order : from Q> to;
      t_n : nat;
      output : tuple (term message) t_n -> term message -> term message;
      guard : tuple (term message) t_n -> term message -> term sbool
  }.

  Variable transitions : forall q : Q, list transition.
  Variable transitions_from : forall q, forall t, In t (transitions q) ->
                                                  t.(from) = q.

  Definition final q : Prop := transitions q = [].

  Definition maximal (t : transition) : Prop :=
    forall (is : tuple (term message) t.(t_n)) (i : term message),
      guard is i = App ftrue h[].

  Definition has_max_transition (q : Q) (H : ~final q) : Prop :=
    maximal (head H).

  Variable max_transition : forall q (H : ~final q), has_max_transition H.

  Variable initial_knowledge : list (term message).

  Variable handles : forall n : nat,
                       func (repeat message (n + length initial_knowledge))
                            message.

  Axiom TODO : forall {T : Type}, T.

  Check eq_rect.

  Inductive execution (m : model)
  : forall n, Q -> tuple (term message) n ->
              tuple (term message) (n + length initial_knowledge)
              -> Type :=
  | Initial : execution m q0 t[] (list_to_tuple initial_knowledge)
  | Transition :
      forall n q (inputs : tuple (term message) n)
             (knowledge : tuple (term message)
                                (n + length initial_knowledge))
             (t : transition) (l : list transition) q',
                   In_with_tail t l (transitions q) ->
                   t.(to) = q' ->
                   forall H : n = t.(t_n),
                     execution m q inputs knowledge ->
                     let new_input := (App (handles n)
                                           (tuple_to_hlist knowledge)) in
                     let new_inputs := new_input t:: inputs in
                     let inputs' :=
                         eq_rect n (tuple (term message)) inputs t.(t_n) H in
                     let new_knowledge :=
                         output inputs' new_input t:: knowledge in
                     m.(interp_term) (guard inputs' new_input) =
                     m.(interp_term) (App ftrue h[]) ->
                     (forall (t' : transition) (H' : n = t'.(t_n)),
                        let inputs' :=
                            eq_rect n (tuple (term message))
                                    inputs t'.(t_n) H' in
                        In t' l ->
                        m.(interp_term) (guard inputs' new_input) <>
                        m.(interp_term) (App ftrue h[])) ->
                     execution m q' new_inputs new_knowledge.

End Protocol.
