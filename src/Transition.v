Set Implicit Arguments.
Unset Strict Implicit.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Arith.Arith.
Require Import Omega.

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

Inductive trace p : Type :=
| TInitial : p.(state) -> trace p
| TTransition : p.(state) -> trace p -> trace p.

Definition head p (tr : trace p) := match tr with
                                      | TInitial q => q
                                      | TTransition q _ => q
                                    end.

Fixpoint tr_len p (tr : trace p) :=
  match tr with
    | TInitial _ => 0
    | TTransition _ tr => S (tr_len tr)
  end.

Inductive valid p : trace p -> Prop :=
| VInitial : valid (TInitial p.(initial))
| VTransition : forall q' (tr : trace p) (t : state_lt q' (head tr)),
                  valid tr -> valid (TTransition q' tr).

Definition complete p (tr : trace p) := final (head tr).

Lemma trace_root_unique p (R : trace p) (vR : valid R) :
  tr_len R = 0 -> R = (TInitial p.(initial)).
  intro H.
  induction vR.
  reflexivity.
  inversion H.
Qed.

Definition tr_len_inv p (R : trace p) n :
  tr_len R = S n ->
  {q' : p.(state) &
        {R' : trace p | R = (TTransition q' R') /\ tr_len R' = n}}.
  revert n.
  remember R as r.
  destruct r as [| q' r]; intros n H.
  inversion H.

  exists q'.
  exists r.
  split.
  reflexivity.

  inversion H.
  reflexivity.
Defined.

Lemma valid_inv p (q' : p.(state)) (R : trace p)
      (vRt : valid (TTransition q' R)) : valid R.
  inversion vRt.
  assumption.
Qed.

Definition valid_len_inv p (R : trace p) (vR : valid R) n :
  tr_len R = S n ->
  {q : p.(state) &
       {R' : trace p | R = (TTransition q R') /\ tr_len R' = n /\ valid R'}}.
  intro H.
  destruct (tr_len_inv H) as [q' [R' [eR' en]]].
  exists q'.
  exists R'.
  split; [|split]; [assumption ..|].
  subst R.
  eapply valid_inv; eassumption.
Defined.

Lemma unique_valid_extension p (U : unique_transition p)
      (R : trace p) (q q' : p.(state))
      (vRq : valid (TTransition q R)) (vRq' : valid (TTransition q' R)) :
  q = q'.
  inversion vRq.
  inversion vRq'.
  eapply U.
  eassumption.
  eassumption.
Qed.

Lemma trace_unique_n p (U : unique_transition p)
      (R R' : trace p) (vR : valid R) (vR' : valid R') :
  tr_len R = tr_len R' -> R = R'.
  remember (tr_len R) as n eqn:HnR.
  intro HnR'.
  symmetry in HnR, HnR'.
  revert R R' vR vR' HnR HnR'.
  induction n; intros R R' vR vR' HnR HnR'.
  assert (R = TInitial p.(initial)) by
      (eapply trace_root_unique; eassumption); subst R.
  assert (R' = TInitial p.(initial)) by
      (eapply trace_root_unique; eassumption); subst R'.
  reflexivity.

  pose proof (valid_len_inv vR HnR) as H.
  pose proof (valid_len_inv vR' HnR') as H'.
  clear HnR HnR'.
  destruct H as [q0 [R0 [? [? ?]]]].
  subst R.

  destruct H' as [q'0 [R'0 [? [? ?]]]].
  subst R'.

  assert (R0 = R'0) by (eapply IHn; eassumption); subst R'0.

  assert (q0 = q'0) by (eapply unique_valid_extension; eassumption);
    subst q'0.

  reflexivity.
Qed.

Lemma complete_no_extension p (q : p.(state)) (R : trace p) :
  (complete R) -> valid (TTransition q R) -> False.
  intros cR vRq.
  inversion vRq.
  eapply cR; eassumption.
Qed.

Lemma complete_no_greater p (U : unique_transition p)
      (R R' : trace p) (vR : valid R) (vR' : valid R') :
  complete R -> tr_len R < tr_len R' -> False.
  intros cR l.

  assert (exists n, tr_len R' = S (n + tr_len R)) as l' by
        (exists (tr_len R' - tr_len R - 1); omega); clear l.
  destruct l' as [n H].
  destruct (valid_len_inv vR' H) as [q'0 [R'0 [? [HnR'0 vR'0]]]];
    clear H; subst R'.

  revert q'0 R'0 HnR'0 vR' vR'0.
  induction n; intros q'0 R'0 HnR'0 vR' vR'0.

  simpl in HnR'0.
  assert (R = R'0) by
      (symmetry in HnR'0; eapply trace_unique_n; eassumption); subst R'0.
  eapply complete_no_extension; eassumption.

  destruct (valid_len_inv vR'0 HnR'0) as [q'1 [R'1 [? [HnR'1 vR'1]]]];
    clear HnR'0; subst R'0.

  eapply IHn; swap 1 2; eassumption.
Qed.

Lemma complete_same_len p (U : unique_transition p)
      (R : trace p) (R' : trace p) :
  valid R -> valid R' -> complete R -> complete R' -> tr_len R = tr_len R'.
  intros.
  destruct (lt_eq_lt_dec (tr_len R) (tr_len R')) as [[l | e] | l];
    [exfalso | assumption | exfalso];
    [ > eapply complete_no_greater; swap 1 5 .. ]; eassumption.
Qed.

Theorem complete_unique p (U : unique_transition p)
        (R : trace p) (R' : trace p) :
  valid R -> valid R' -> complete R -> complete R' -> R = R'.
  intros.
  eapply trace_unique_n with (R := R) (R' := R');
    try eapply complete_same_len; eassumption.
Qed.

Definition extend_trace p (E : transition_dec p)
           (R : trace p) (vR : valid R) :
  {R' : trace p | valid R' /\ state_lt (head R') (head R)}%type +
  {complete R}.
  destruct (E (head R)) as [[q' t] | Fq].
  left; eexists; split; [econstructor|]; eassumption.
  right; assumption.
Defined.

Definition tr_lt p (R R' : trace p) : Prop := state_lt (head R) (head R').

Fixpoint tr_with_head_tail p (q : p.(state)) qs :=
  match qs with
    | [] => TInitial q
    | q' :: qs' => TTransition q (tr_with_head_tail q' qs')
  end.

Fixpoint tail p (R : trace p) : list p.(state) :=
  match R with
    | TInitial _ => []
    | TTransition _ R => head R :: tail R
  end.

Lemma head_tail_inv p (R : trace p) :
  R = tr_with_head_tail (head R) (tail R).
  induction R.
  reflexivity.
  simpl.
  rewrite IHR at 1.
  reflexivity.
Qed.

Lemma head_inv p (q : p.(state)) qs :
  q = head (tr_with_head_tail (p:=p) q qs).
  induction qs; reflexivity.
Qed.

Definition tr_wf p : well_founded (@tr_lt p).
  unfold well_founded.
  intro R.
  rewrite head_tail_inv.

  refine ((Fix p.(@state_wf)
                   (fun q => forall R, Acc (tr_lt (p:=p))
                                           (tr_with_head_tail q (tail R)))
                   _ _) R); clear R.

  intros q IHq Rtl.
  constructor.
  intros R' H.
  unfold tr_lt in H.
  rewrite <- head_inv in H.
  specialize (IHq (head R') H R').
  rewrite <- head_tail_inv in IHq.
  assumption.
Defined.

Definition finalize_trace p (E : transition_dec p)
           (R : trace p) (vR : valid R) :
  {R' : trace p | valid R' /\ complete R'}%type.
  revert R vR.
  refine
    (Fix (@tr_wf p)
         (fun R : trace p =>
            valid R ->
            {R' : trace p | valid R' /\ complete R'}) _).
  intros R IHR vR.
  destruct (extend_trace E vR) as [[R' [vR' t]] | cR].

  eapply IHR; eassumption.

  exists R; split; assumption.
Defined.

Definition exists_trace p (E : transition_dec p) :
  {R : trace p | valid R /\ complete R}%type.
  eapply finalize_trace; [assumption | constructor].
Defined.
