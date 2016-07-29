Set Implicit Arguments.
Unset Strict Implicit.

Require Import Coq.Lists.List.
Require Import Coq.Structures.OrderedType.
Import ListNotations.

Require Import CrossCrypto.FirstOrder.
Require Import CrossCrypto.Tuple.
Require Import CrossCrypto.HList.
Require Import CrossCrypto.Tail.
Require Import CrossCrypto.Execution.
Require Import Omega.

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
        N_cap : nat;
        fin_Q : forall n : nat, Q n -> n < N_cap;
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

  Definition initial_knowledge_t p := list_to_tuple p.(initial_knowledge).

  Definition machine_state p :=
    {n : nat & p.(Q) n * tuple (term message) n *
               tuple (term message) (n + length p.(initial_knowledge))}%type.
  Definition machine_initial p : machine_state p :=
    existT _ 0 (q0 p, t[], initial_knowledge_t p).

  Inductive transition_valid (m : model) (p : protocol) n :
    p.(Q) n -> tuple (term message) n ->
    tuple (term message) (n + length p.(initial_knowledge)) ->
    p.(Q) (S n) -> tuple (term message) (S n) ->
    tuple (term message) (S n + length p.(initial_knowledge)) -> Prop :=
  | TransValid q inputs knowledge t_ l :
      let q' := projT1 t_ in
      let t := projT2 t_ in
      let new_input := (App (p.(handles) n)
                            (tuple_to_hlist knowledge)) in
      let new_inputs := new_input t:: inputs in
      let new_knowledge :=
          t.(output) inputs new_input t:: knowledge in
      let guard_condition := (fun t_ : {q' : Q p (S n) & transition q q'} =>
                                let t := projT2 t_ in
                                m.(interp_term) (t.(guard) inputs new_input) =
                                m.(interp_term) (App ftrue h[])) in
      In_with_tail t_ l (transitions q) ->
      guard_condition t_ ->
      (forall t'_, In t'_ l -> ~guard_condition t'_) ->
      transition_valid m q inputs knowledge q' new_inputs new_knowledge.

  Lemma valid_transition_unique (m : model) (p : protocol) n
        (q : p.(Q) n) inputs knowledge
        q'1 inputs'1 knowledge'1
        q'2 inputs'2 knowledge'2 :
    transition_valid m q inputs knowledge q'1 inputs'1 knowledge'1 ->
    transition_valid m q inputs knowledge q'2 inputs'2 knowledge'2 ->
    q'1 = q'2 /\ inputs'1 = inputs'2 /\ knowledge'1 = knowledge'2.
    intros V1 V2.
    inversion_clear V1 as [? ? knowledge1 t_1 l1 q'1_ t1 new_input1
                             inputs'1_ knowledge'1_ guard1 ? HG1 HNG1].
    inversion_clear V2 as [? ? knowledge2 t_2 l2 q'2_ t2 new_input2
                             inputs'2_ knowledge'2_ guard2 ? HG2 HNG2].
    subst.
    replace guard2 with guard1 in * by reflexivity; clear guard2.

    assert (t_1 = t_2) by
        (eapply head_unique_prop with (P := guard1); eassumption).
    subst t_2.
    split; [|split]; reflexivity.
  Qed.

  Definition machine_lt (m : model) p (to from : machine_state p) : Prop.
    destruct from as [n [[q i] k]].
    destruct to as [n' [[q' i'] k']].
    refine (exists H : n' = S n, _).
    subst n'.
    exact (transition_valid m q i k q' i' k').
  Defined.

  Definition nat_gt_max_wf (N : nat) (A : nat -> Type)
          (cap : forall n, A n -> n < N)
          (A_lt : sigT A -> sigT A -> Prop)
          (A_lt_gt : forall a a' : sigT A, A_lt a' a -> projT1 a' > projT1 a) :
    well_founded A_lt.
    assert (forall n (a : A n), exists b, n = N - b) as HcN.
    {
      intros n a.
      exists (N - n).
      specialize (cap n a).
      omega.
    }
    intros [n a].
    destruct (HcN n a) as [b].
    subst n.
    refine ((Fix lt_wf (fun n => forall a : A (N - n),
                                   Acc A_lt (existT _ _ a)) _) b a); clear a b.
    intros b H a.
    constructor.
    intros a' l.
    destruct a' as [n' a'].
    destruct (HcN n' a') as [b'].
    subst n'.
    apply H.
    specialize (A_lt_gt (existT _ _ a) (existT _ _ a') l).
    simpl in A_lt_gt.
    omega.
  Defined.

  Definition machine_lt_wf (m : model) p : well_founded (@machine_lt m p).
    eapply nat_gt_max_wf.
    - intros n [[q _] _].
      apply fin_Q; eassumption.
    - intros [n [[q i] k]] [n' [[q' i'] k']] [H _].
      simpl.
      omega.
  Defined.

  Definition model_protocol_machine m p :=
    @mkMachine (machine_state p) (machine_initial p)
               (@machine_lt m p) (@machine_lt_wf m p).

  Theorem machine_unique m p : unique_transition (model_protocol_machine m p).
    intros x x'1 x'2 t1 t2.
    simpl in t1, t2.
    unfold machine_lt in t1, t2.
    destruct x as [n [[q i] k]].
    destruct x'1 as [n'1 [[q'1 i'1] k'1]].
    destruct x'2 as [n'2 [[q'2 i'2] k'2]].
    destruct t1 as [H1 tv1], t2 as [H2 tv2].
    subst n'1.
    subst n'2.
    unfold eq_rect_r in tv1; simpl in tv1.
    unfold eq_rect_r in tv2; simpl in tv2.
    destruct (valid_transition_unique tv1 tv2) as [qe [ie ke]].
    rewrite qe, ie, ke; reflexivity.
  Qed.

  (* Existence of a final valid execution requires at least decidability
  over domain bool *)

End Protocols.
