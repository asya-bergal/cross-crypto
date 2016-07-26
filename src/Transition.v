Set Implicit Arguments.
Unset Strict Implicit.

Require Import Coq.Lists.List.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Arith.Arith.
Require Import Omega.
Import ListNotations.

Require Import CrossCrypto.Tail.

Definition head T (l : list T) (H : l <> []) : T.
  destruct l.
  destruct (H eq_refl).
  exact t.
Defined.

Inductive rosetree (T : Type) : Type :=
| RLeaf : rosetree T
| RNode : T -> list (rosetree T) -> rosetree T.

Arguments RLeaf {T}.

Definition rosetree_list_rect (T : Type)
           (P : rosetree T -> Type)
           (Q : list (rosetree T) -> Type)
           (p_leaf : P RLeaf)
           (p_node : forall x l, Q l -> P (RNode x l))
           (q_nil : Q [])
           (q_cons : forall r l, P r -> Q l -> Q (r :: l)) :
  forall r : rosetree T, P r :=
  fix F (r : rosetree T) : P r :=
  match r with
    | RLeaf => p_leaf
    | RNode x l =>
      p_node x l
             ((fix G (l : list (rosetree T)) : Q l :=
                 match l with
                   | [] => q_nil
                   | r :: l => q_cons r l (F r) (G l)
                 end) l)
  end.

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

  Section Protocol.

    Variable state : Type.
    Variable initial : state.
    Variable state_lt : state -> state -> Prop.
    Variable state_wf : well_founded state_lt.

    Variable transition : state -> Type.
    Variable transition_guard : forall q, transition q -> input -> Prop.
    Variable transition_update : forall q (t : transition q), input -> state.
    Variable transition_next_lt : forall q (t : transition q) i,
                                    state_lt (@transition_update _ t i) q.

    Variable transition_lt : forall q, transition q -> transition q -> Prop.

    Variable transition_lt_total :
      forall q (t t' : transition q),
         t = t' \/ transition_lt t t' \/ transition_lt t' t.

    Definition final_ q := transition q -> False.

    Definition maximal_transition q (t : transition q) :=
      forall i, transition_guard t i.

    Definition has_max_transition q (H : ~final_ q) : Prop :=
      exists t : transition q, maximal_transition t.

  End Protocol.

  Record protocol :=
    mkProtocol {
        state : Type;
        initial : state;
        state_lt : state -> state -> Prop;
        state_wf : well_founded state_lt;
        transition : state -> Type;
        transition_guard : forall q, transition q -> input -> Prop;
        transition_update : forall q (t : transition q), input -> state;
        transition_next_lt : forall q (t : transition q) i,
                               state_lt (@transition_update _ t i) q;

        transition_lt : forall q, transition q -> transition q -> Prop;
        transition_lt_total :
          forall q (t t' : transition q),
            t = t' \/ transition_lt t t' \/ transition_lt t' t;
        final : state -> Prop := final_ transition;
        max_transition : forall q (H : ~final q),
                           has_max_transition transition_guard H;
      }.

  Definition valid_transition p (q : p.(state))
             (t : transition q) (i : input) :=
    transition_guard t i /\
    forall t', transition_lt t t' -> ~transition_guard t' i.

  Lemma valid_transition_unique p (q : p.(state))
        (t t' : transition q) (i : input) :
    valid_transition t i -> valid_transition t' i -> t = t'.
    intros Vt Vt'.
    destruct (transition_lt_total t t') as [e | [lt | lt]];
      [assumption | ..];
      destruct Vt as [Vt nVt'];
      destruct Vt' as [Vt' nVt];
      [destruct (nVt' t' lt Vt') | destruct (nVt t lt Vt)].
  Qed.

  Definition client p := p.(state) -> input.

  Definition valid_transition_client p (c : p.(client)) q (t : transition q) :=
    valid_transition t (c q).

  Definition valid_transition_unique_client p (c : p.(client)) q
             (t t' : transition q)
             (Vt : valid_transition_client c t)
             (Vt' : valid_transition_client c t') : t = t' :=
    valid_transition_unique Vt Vt'.


  Definition transition_update_client p (c : p.(client)) q
             (t : transition q) :=
    transition_update t (c q).

  (* TODO use more traditional semantics style than these traces *)

  Inductive reaches p (c : client p) : p.(state) -> Type :=
  | RInitial : reaches c p.(initial)
  | RTransition : forall q (t : transition q)
                         (Hv : valid_transition_client c t),
                    reaches c q -> reaches c (transition_update_client c t).

  Fixpoint reaches_n p (c : client p) q (R : reaches c q) : nat :=
    match R with
      | RInitial _ => O
      | @RTransition _ _ q' _ _ R => S (@reaches_n p c q' R)
    end.

  Lemma root_unique p (c : client p) q (R : reaches c q) :
    reaches_n R = 0 -> q = p.(initial).
    intro H.
    induction R.
    reflexivity.
    simpl in H; congruence.
  Qed.

  Lemma reaches_n_inv p (c : client p) q (R : reaches c q) n :
    reaches_n R = S n ->
    exists q' (t : transition q') (Hv : valid_transition_client c t)
           (R' : reaches c q'),
      (eq_2 R (RTransition Hv R')) /\ reaches_n R' = n.
    intro H.
    revert n H.
    remember R as r.
    destruct r as [| q t Hv r]; intros n H.
    inversion H.
    exists q.
    exists t.
    exists Hv.
    exists r.
    split.
    apply eq_refl2 with (H := eq_refl).
    simpl.
    reflexivity.
    simpl in H.
    inversion H.
    reflexivity.
  Qed.

  Lemma reaches_unique_n p (c : client p) q q'
        (R : reaches c q) (R' : reaches c q') :
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
    destruct H as [q0 [t0 [Hv0 [R0 [[? eR] HnR0]]]]].
    subst q.
    simpl in eR.
    subst R.

    destruct H' as [q0' [t0' [Hv0' [R0' [[? eR'] HnR0']]]]].
    subst q'.
    simpl in eR'.
    subst R'.

    assert (q0 = q0') by (eapply IHn; eassumption).
    subst q0'.
    assert (t0 = t0') by (eapply valid_transition_unique_client; eassumption).
    subst t0'.
    reflexivity.
  Qed.

  Lemma no_final_extension p (c : client p) q q'
        (R : reaches c q) (R' : reaches c q') :
    final q -> reaches_n R < reaches_n R' -> False.
    intros Fq l.

    assert (exists n, reaches_n R' = S (n + reaches_n R)) as l' by
          (exists (reaches_n R' - reaches_n R - 1); omega); clear l.
    destruct l' as [n H].
    destruct (reaches_n_inv H) as [q'0 [t [Hv [R'0 [[? _] HnR'0]]]]];
      clear H.
    subst q'.
    clear R'.

    revert q R Fq q'0 t Hv R'0 HnR'0.
    induction n; intros q R Fq q'0 t Hv R'0 HnR'0.

    simpl in HnR'0.
    assert (q = q'0) by
        (symmetry in HnR'0; eapply reaches_unique_n; eassumption).
    subst q'0.
    exact (Fq t).

    destruct (reaches_n_inv HnR'0) as [q'1 [t0 [Hv0 [R'1 [[? _] HnR'1]]]]];
      clear HnR'0.
    subst q'0.
    clear R'0.

    eapply IHn with (t:=t0); eassumption.
  Qed.

  Lemma reaches_unique_final_n p (c : client p) q q' (R : reaches c q)
        (R' : reaches c q') :
    final q -> final q' -> reaches_n R = reaches_n R'.
    intros Fq Fq'.
    destruct (lt_eq_lt_dec (reaches_n R) (reaches_n R')) as [[l | e] | l];
      [exfalso | assumption | exfalso];
      eapply no_final_extension; swap 1 2; eassumption.
  Qed.

  Theorem reaches_unique_final p (c : client p) q q'
          (R : reaches c q) (R' : reaches c q') :
    final q -> final q' -> q = q'.
    intros Fq Fq'.
    apply reaches_unique_n with (c:=c) (R:=R) (R':=R');
    apply reaches_unique_final_n; assumption.
  Qed.

End Protocols.
