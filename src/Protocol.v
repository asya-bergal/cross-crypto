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

Inductive In_with_tail A : A -> list A -> list A -> Prop :=
| Here : forall hd tl, In_with_tail hd tl (hd :: tl)
| Next : forall hd tl x xs, In_with_tail hd tl xs ->
                            In_with_tail hd tl (x :: xs).

Section Protocols.

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

  Section Protocol.

    Variable Q : nat -> Type.
    Variable q0 : Q 0.

    Record transition_ n (from : Q n) (to : Q (S n)) :=
      mkTransition {
          output : tuple (term message) n -> term message -> term message;
          guard : tuple (term message) n -> term message -> term sbool
        }.

    Variable transitions : forall n (q : Q n),
                             list {q' : Q (S n) & transition_ q q'}.

    Definition final_ n (q : Q n) : Prop := transitions q = [].

    Definition maximal_transition n q q' (t : transition_ q q') : Prop :=
      forall (is : tuple (term message) n) (i : term message),
        t.(guard) is i = App ftrue h[].

    Definition has_max_transition n (q : Q n) (H : ~final_ q) : Prop :=
      maximal_transition (projT2 (head H)).

  End Protocol.

  Record protocol :=
    mkProtocol {
        Q : nat -> Type;
        q0 : Q 0;
        transition : forall n, Q n -> Q (S n) -> Type := @transition_ Q;
        transitions : forall n (q : Q n),
                        list {q' : Q (S n) & transition q q'};
        final : forall n, Q n -> Prop := @final_ Q transitions;
        max_transition : forall n (q : Q n) (H : ~final q),
                           has_max_transition H;
        initial_knowledge : list (term message);
        handles : forall n : nat,
                    func (repeat message (n + length initial_knowledge))
                         message
      }.

  Inductive execution (p : protocol)
  : forall n, p.(Q) n -> tuple (term message) n ->
              tuple (term message) (n + length p.(initial_knowledge))
              -> Type :=
  | Initial : execution p.(q0) t[] (list_to_tuple p.(initial_knowledge))
  | Transition :
      forall n (q : p.(Q) n) inputs knowledge q' (t : transition q q'),
        execution q inputs knowledge ->
        let new_input := (App (p.(handles) n)
                              (tuple_to_hlist knowledge)) in
        let new_inputs := new_input t:: inputs in
        let new_knowledge :=
            t.(output) inputs new_input t:: knowledge in
        execution q' new_inputs new_knowledge.

  Inductive Execution (p : protocol) : Type :=
  | exec : forall n (q : p.(Q) n) inputs knowledge
                  (e : execution q inputs knowledge), Execution p.

  Definition valid_exec (m : model) (p : protocol) (e : Execution p) : Prop.
    destruct e as [n q inputs knowledge e].
    induction e.
    exact True.
    exact (exists t_ l,
             In_with_tail t_ l (transitions q) /\
             (exists H : q' = projT1 t_,
                projT2 t_ = eq_rect q' (transition _) t (projT1 t_) H) /\
             m.(interp_term) (t.(guard) inputs new_input) =
             m.(interp_term) (App ftrue h[]) /\
             (forall t'_, In t'_ l ->
                          let t' := projT2 t'_ in
                          m.(interp_term) (t'.(guard) inputs new_input) <>
                          m.(interp_term) (App ftrue h[]))).
  Defined.

  Definition final_exec (p : protocol) (e : Execution p) : Prop :=
    match e with
      | @exec _ _ q _ _ _ => final q
    end.

  Theorem exec_final_valid_unique :
    forall (m : model) (p : protocol) (e e' : Execution p),
      final_exec e -> final_exec e' -> valid_exec m e -> valid_exec m e' ->
      e = e'.
    intros m p e e' Hfe Hfe' Hve Hve'.
  Admitted.  (* TODO *)

  (* Existence of a final valid execution requires at least decidability
  over domain bool *)

End Protocols.
