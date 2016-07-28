Set Implicit Arguments.
Unset Strict Implicit.

Require Import Coq.Lists.List.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Arith.Arith.
Require Import Omega.
Import ListNotations.

Require Import CrossCrypto.Tail.

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

  Variable input : Type.

  Record protocol :=
    mkProtocol {
        state : Type;
        initial : state;
        state_lt : state -> state -> Prop;
        state_wf : well_founded state_lt;
      }.

  Definition final p (q : p.(state)) :=
    forall q', ~state_lt q' q.

  Definition unique_transition p :=
    forall q q' q'': p.(state),
      state_lt q' q -> state_lt q'' q -> q' = q''.

  Definition transition_dec p :=
    forall q : p.(state), {q' : p.(state) & state_lt q' q} + {final q}.

  (* TODO use more traditional semantics style than these traces *)

  Inductive reaches p : p.(state) -> Type :=
  | RInitial : reaches p.(initial)
  | RTransition : forall q q' (t : state_lt q' q),
                    reaches q -> reaches q'.

  Fixpoint reaches_n p (q : p.(state)) (R : reaches q) : nat :=
    match R with
      | RInitial _ => O
      | @RTransition _ q' _ _ R => S (@reaches_n p q' R)
    end.

  Lemma root_unique p (q : p.(state)) (R : reaches q) :
    reaches_n R = 0 -> q = p.(initial).
    intro H.
    induction R.
    reflexivity.
    simpl in H; discriminate.
  Qed.

  Lemma reaches_n_inv p (q : p.(state)) (R : reaches q) n :
    reaches_n R = S n ->
    exists q' (t : state_lt q q') (R' : reaches q'),
      R = (RTransition t R') /\ reaches_n R' = n.
    intro H.
    revert n H.
    remember R as r.
    destruct r as [| q' q H0 r]; intros n H.
    inversion H.

    exists q'.
    exists H0.
    exists r.
    split.
    reflexivity.

    inversion H.
    reflexivity.
  Qed.

  Lemma reaches_unique_n p (U : unique_transition p) (q q' : p.(state))
        (R : reaches q) (R' : reaches q') :
    reaches_n R = reaches_n R' -> q = q'.
    remember (reaches_n R) as n eqn:HnR.
    intro HnR'.
    symmetry in HnR, HnR'.
    revert q q' R R' HnR HnR'.
    induction n; intros q q' R R' HnR HnR'.
    assert (q = p.(initial)) by (eapply root_unique; eassumption); subst q.
    assert (q' = p.(initial)) by (eapply root_unique; eassumption); subst q'.
    reflexivity.
    pose proof (reaches_n_inv HnR) as H.
    pose proof (reaches_n_inv HnR') as H'.
    clear HnR HnR'.
    destruct H as [q0 [? [? [? ?]]]].
    subst R.

    destruct H' as [q0' [? [? [? ?]]]].
    subst R'.

    assert (q0 = q0') by (eapply IHn; eassumption).
    subst q0'.

    eapply U; eassumption.
  Qed.

  Lemma no_final_greater p (U : unique_transition p) (q q' : p.(state))
        (R : reaches q) (R' : reaches q') :
    final q -> reaches_n R < reaches_n R' -> False.
    intros Fq l.

    assert (exists n, reaches_n R' = S (n + reaches_n R)) as l' by
          (exists (reaches_n R' - reaches_n R - 1); omega); clear l.
    destruct l' as [n H].
    destruct (reaches_n_inv H) as [q'0 [t'0 [R'0 [_ HnR'0]]]]; clear H R'.

    revert q' q'0 t'0 R'0 HnR'0.
    induction n; intros q' q'0 t'0 R'0 HnR'0.

    simpl in HnR'0.
    assert (q = q'0) by
        (symmetry in HnR'0; eapply reaches_unique_n; eassumption).
    subst q'0.
    eapply Fq; eassumption.

    destruct (reaches_n_inv HnR'0) as [q'1 [t'1 [R'1 [_ HnR'1]]]].
    clear HnR'0 R'0.

    eapply IHn; swap 1 2; eassumption.
  Qed.

  Lemma reaches_unique_final_n p (U : unique_transition p)
        (q q' : p.(state)) (R : reaches q)
        (R' : reaches q') :
    final q -> final q' -> reaches_n R = reaches_n R'.
    intros Fq Fq'.
    destruct (lt_eq_lt_dec (reaches_n R) (reaches_n R')) as [[l | e] | l];
      [exfalso | assumption | exfalso];
      eapply no_final_greater; swap 2 3; eassumption.
  Qed.

  Theorem reaches_unique_final p (U : unique_transition p) (q q' : p.(state))
          (R : reaches q) (R' : reaches q') :
    final q -> final q' -> q = q'.
    intros Fq Fq'.
    eapply reaches_unique_n with (R := R) (R' := R');
      [assumption | eapply reaches_unique_final_n; eassumption].
  Qed.


  Definition extend_reach p (E : transition_dec p) (q : p.(state))
             (R : reaches q) :
    {q' : p.(state) & (reaches q') * state_lt q' q}%type + {final q}.
    destruct (E q) as [[q' t] | Fq].
    left; exists q'; split; [econstructor|]; eassumption.
    right; assumption.
  Defined.

  Definition finalize_reach p (E : transition_dec p) (q : p.(state))
             (R : reaches q) :
    {q' : p.(state) & (reaches q') * (final q')}%type.
    revert q R.
    refine
      (Fix p.(@state_wf)
               (fun q : p.(state) =>
                  reaches (p:=p) q ->
                  {q' : state p &
                        (reaches (p:=p) q' * final (p:=p) q')%type}) _).
    intros q IHq R.
    destruct (E q) as [[q' t] | Fq].
    eapply IHq; [|econstructor]; eassumption.

    exists q.
    split; assumption.
  Defined.

  Definition exists_reaches p (E : transition_dec p) :
    {q : p.(state) & (reaches q) * (final q)}%type.
    eapply finalize_reach; [assumption | constructor].
  Defined.

End Protocols.
