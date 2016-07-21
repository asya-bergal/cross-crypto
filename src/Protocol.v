Set Implicit Arguments.
Unset Strict Implicit.

Require Import Coq.Lists.List.
Require Import Coq.Structures.OrderedType.
Import ListNotations.

Require Import CrossCrypto.FirstOrder.
Require Import CrossCrypto.Tuple.
Require Import CrossCrypto.HList.
Require Import CrossCrypto.Tail.

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

Inductive eq_2 (A : Type) (P : A -> Type) (a a' : A) (p : P a) (p' : P a')
: Prop :=
| eq_refl2 : forall (H : a = a'),
               eq_rect a P p a' H = p' -> eq_2 p p'.

Definition eq_rect2 (A : Type) (P : A -> Type) (a a' : A)
           (p : P a) (p' : P a') (Q : forall a : A, P a -> Type)
           (H : eq_2 p p') (q : Q a p) : Q a' p'.
  assert ({H : a = a' | eq_rect a P p a' H = p'}) as H'.
  destruct H as [H H'].
  refine (exist _ H H').
  clear H.
  destruct H'.
  subst a.
  subst p'.
  assumption.
Defined.

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

  Definition valid_exec (m : model) (p : protocol)
             n (q : p.(Q) n) inputs knowledge
             (e : execution q inputs knowledge) : Prop.
    induction e.
    exact True.
    set (guard_condition := (fun t_ : {q' : Q p (S n) & transition q q' } =>
                              let t := projT2 t_ in
                              m.(interp_term) (t.(guard) inputs new_input) =
                              m.(interp_term) (App ftrue h[]))).
    exact (exists t_ l,
             In_with_tail t_ l (transitions q) /\
             (eq_2 (projT2 t_) t) /\
             guard_condition t_ /\
             (forall t'_, In t'_ l -> ~guard_condition t'_)).
  Defined.

  Lemma valid_exec_extension_unique :
    forall (m : model) (p : protocol) n (q : p.(Q) n) inputs knowledge
           (e : execution q inputs knowledge)
           q' (t : transition q q') q'1 (t1 : transition q q'1),
      valid_exec m (Transition t e) -> valid_exec m (Transition t1 e) ->
      (eq_2 t t1).
    intros m p n q inputs knowledge e q' t q'1 t1 Hv Hv1.
    simpl in Hv.
    destruct Hv as [t_ [l [Iwt [[eq' et] [Hguard Hguardrest]]]]].
    subst q'.
    subst t.
    simpl in Hv1.
    destruct Hv1 as [t_1 [l1 [Iwt1 [[eq'1 et1] [Hguard1 Hguardrest1]]]]].
    subst q'1.
    subst t1.
    simpl.

    assert (t_ = t_1) as Heqt_.

    set (new_input := (App (p.(handles) n)
                              (tuple_to_hlist knowledge))).
    set (guard_condition := (fun t_ : {q' : Q p (S n) & transition q q' } =>
                              let t := projT2 t_ in
                              m.(interp_term) (t.(guard) inputs new_input) =
                              m.(interp_term) (App ftrue h[]))).
    eapply head_unique_prop with (P := guard_condition); eassumption.
    subst t_1.
    refine (eq_refl2 (H:=eq_refl) _).
    reflexivity.
  Qed.

  Inductive Execution (p : protocol) : Type :=
  | exec : forall n (q : p.(Q) n) inputs knowledge
                  (e : execution q inputs knowledge), Execution p.

  Definition valid_Exec (m : model) (p : protocol) (e : Execution p) : Prop :=
    match e with
      | exec e => valid_exec m e
    end.

  Definition final_exec (p : protocol) (e : Execution p) : Prop :=
    match e with
      | @exec _ _ q _ _ _ => final q
    end.

  Theorem exec_final_valid_unique :
    forall (m : model) (p : protocol) (e e' : Execution p),
      final_exec e -> final_exec e' -> valid_Exec m e -> valid_Exec m e' ->
      e = e'.
    intros m p e e'' Hfe Hfe'' Hve Hve''.
    destruct e as [n q inputs knowledge e].
    destruct e'' as [n' q' inputs' knowledge' e''].
    generalize e'' Hfe'' Hve''.
    induction e.
    intros e' Hfe' Hve'.
  Admitted.  (* TODO *)

  (* Existence of a final valid execution requires at least decidability
  over domain bool *)

End Protocols.
