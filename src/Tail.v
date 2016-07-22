Set Implicit Arguments.
Unset Strict Implicit.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Omega.

Inductive sublist A : list A -> list A -> Prop :=
| Here : forall l, sublist l l
| Next : forall a l l', sublist l l' -> sublist l (a :: l').

Lemma sublist_in A (l l' : list A) :
  sublist l l' -> forall a, In a l -> In a l'.
  intro S; induction S; [auto | constructor; solve [auto]].
Qed.

Lemma head_prop A (P : A -> Prop) a a' l :
  (forall x, In x l -> ~P x) -> P a -> P a' -> In a' (a :: l) -> a = a'.
  intros H pa pa' H'.
  destruct H'.
  assumption.
  exfalso; apply (H a'); assumption.
Qed.

Lemma sub_nil A (l : list A) : sublist l [] -> l = [].
  intro H; inversion H; reflexivity.
Qed.

Corollary cons_not_sub_nil A (a : A) l : ~sublist (a :: l) [].
  intro H.
  assert (a :: l = []) by (apply sub_nil; assumption).
  congruence.
Qed.

Lemma nil_sub A (l : list A) : sublist [] l.
  induction l; constructor; trivial.
Qed.

Lemma sub_app A (l l' : list A) : sublist l l' <-> exists L, L ++ l = l'.
  split.
  intro S.
  induction S as [| a l l' S IHS].
  exists [].
  reflexivity.
  destruct IHS as [x H].
  subst l'.
  exists (a :: x).
  reflexivity.

  intros [L H].
  subst l'.
  induction L; constructor; assumption.
Defined.

Lemma sub_trans A (l l' l'' : list A) :
  sublist l l' -> sublist l' l'' -> sublist l l''.
  intros S S'.
  apply sub_app in S.
  apply sub_app in S'.
  apply sub_app.
  destruct S as [L H].
  destruct S' as [L' H'].
  subst l'.
  exists (L' ++ L).
  subst l''.
  symmetry; apply app_assoc.
Qed.

Lemma app_l_sub A (l l' l'' : list A) :
  sublist (l ++ l') l'' -> sublist l' l''.
  intro S.
  apply sub_app in S.
  apply sub_app.
  destruct S as [L H].
  exists (L ++ l).
  subst l''.
  symmetry; apply app_assoc.
Qed.

Lemma sub_cons A (a : A) l l' : sublist (a :: l) l' -> sublist l l'.
  intro S.
  apply app_l_sub with (l:=[a]).
  assumption.
Qed.

Lemma head_prop_sub A (P : A -> Prop) a a' l l' :
  (forall x, In x l -> ~P x) -> P a -> P a' -> In a' l' ->
  sublist l' (a :: l) -> l' = a :: l.
  intros H pa pa' H' S.
  inversion_clear S as [| ? ? ? H''].
  reflexivity.
  exfalso.
  eapply H.
  eapply sublist_in.
  eassumption.
  eassumption.
  assumption.
Qed.

(* Lemma head_prop_sub' A (P : A -> Prop) a l l' : *)
(*   (forall x, In x l -> ~P x) *)

Lemma sub_length_inverted A (l l' : list A) :
  length l' <= length l -> sublist l l' -> l = l'.
  intros H S.
  apply sub_app in S.
  destruct S as [L e].
  subst l'.
  rewrite app_length in H.
  assert (length L = 0) as H0 by omega.
  assert (L = []) by (apply length_zero_iff_nil; assumption).
  subst L.
  reflexivity.
Qed.

Lemma subs_length_sub A (l l1 l2 : list A) :
  sublist l1 l -> sublist l2 l -> length l1 <= length l2 ->
  sublist l1 l2.
  intros S1 S2 H.
  apply sub_app in S1.
  apply sub_app in S2.
  apply sub_app.
  destruct S1 as [L1 e1].
  destruct S2 as [L2 e2].
  generalize l1 l2 L1 L2 e1 e2 H.
  clear l1 l2 L1 L2 e1 e2 H.
  induction l.
  intros.
  apply app_eq_nil in e1.
  apply app_eq_nil in e2.
  destruct e1, e2.
  subst l1.
  subst l2.
  exists [].
  reflexivity.

  intros.
  destruct L1 as [| x1 L1];
  destruct L2 as [| x2 L2].
  simpl in e1, e2.
  rewrite -> e1; rewrite <- e2.
  exists []; reflexivity.

  simpl in e1.
  exists []; simpl.
  symmetry; apply sub_length_inverted.
  assumption.
  apply sub_app.
  exists (x2 :: L2).
  rewrite e2; rewrite e1; reflexivity.

  exists (x1 :: L1).
  rewrite e1.
  rewrite <- e2.
  reflexivity.

  assert (L1 ++ l1 = l) as H0 by (inversion e1; reflexivity).
  assert (L2 ++ l2 = l) as H1 by (inversion e2; reflexivity).
  exact (IHl l1 l2 L1 L2 H0 H1 H).
Qed.

Corollary subs_sub A (l l1 l2 : list A) :
  sublist l1 l -> sublist l2 l ->
  {sublist l1 l2} + {sublist l2 l1}.
  intros S1 S2.
  destruct (le_ge_dec (length l1) (length l2)) as [L | G];
  [left | right]; eapply subs_length_sub; eassumption.
Defined.

Definition In_with_tail A a l l' := @sublist A (a :: l) l'.

(* Inductive In_with_tail A : A -> list A -> list A -> Prop := *)
(* | Here : forall hd tl, In_with_tail hd tl (hd :: tl) *)
(* | Next : forall hd tl x xs, In_with_tail hd tl xs -> *)
(*                             In_with_tail hd tl (x :: xs). *)

Lemma sub_length A (l l' : list A) :
  sublist l l' -> length l <= length l'.
  intro S.
  apply sub_app in S.
  destruct S as [L H].
  assert (length L + length l = length l') by
      (subst l'; symmetry; apply app_length).
  omega.
Qed.

Lemma sub_antisymmetry A (l l' : list A) :
  sublist l l' -> sublist l' l -> l = l'.
  intros S S'.
  apply sub_app in S.
  apply sub_app in S'.
  destruct S as [L H].
  destruct S' as [L' H'].
  subst l.
  assert (L ++ L' = []) as H0.
  rewrite app_assoc in H.
  apply app_inv_tail with (l2 := []) in H.
  assumption.
  assert (L' = []).
  apply app_eq_nil in H0.
  destruct H0; assumption.
  subst L'.
  reflexivity.
Qed.

Lemma subs_equal_length A (l l1 l2 : list A) :
  sublist l1 l -> sublist l2 l -> length l1 = length l2 -> l1 = l2.
  intros S1 S2 H.
  apply sub_antisymmetry; eapply subs_length_sub; (eassumption || omega).
Qed.

Corollary subs_compare A a1 a2 (l l1 l2 : list A) :
  sublist (a1 :: l1) l -> sublist (a2 :: l2) l ->
  {l1 = l2} + {sublist (a1 :: l1) l2} + {sublist (a2 :: l2) l1}.
  intros S1 S2.
  pose proof sub_cons S1 as S1'.
  pose proof sub_cons S2 as S2'.
  destruct (lt_eq_lt_dec (length l1) (length l2)) as [[le | e] | ge].

  left; right.
  assert (length (a1 :: l1) <= length l2) by (simpl; omega).
  eapply subs_length_sub; eassumption.

  left; left; eapply subs_equal_length; eassumption.

  right.
  assert (length (a2 :: l2) <= length l1) by (simpl; omega).
  eapply subs_length_sub; eassumption.
Qed.

Lemma tail_unique_prop (A : Type) (P : A -> Prop) (a1 a2 : A)
      (l l1 l2 : list A)
: In_with_tail a1 l1 l -> In_with_tail a2 l2 l ->
  P a1 -> P a2 ->
  (forall a1', In a1' l1 -> ~P a1') ->
  (forall a2', In a2' l2 -> ~P a2') ->
  l1 = l2.
  unfold In_with_tail.
  intros S1 S2 P1 P2 nP1 nP2.
  pose proof sub_cons S2 as S2'.
  destruct (subs_compare S1 S2) as [[e | s] | s].
  assumption.

  exfalso.
  pose proof sub_cons s as s'.
  apply (nP2 a1).
  eapply sublist_in.
  apply s.
  left; reflexivity.
  assumption.

  exfalso.
  pose proof sub_cons s as s'.
  apply (nP1 a2).
  eapply sublist_in.
  apply s.
  left; reflexivity.
  assumption.
Qed.

Lemma head_unique_prop (A : Type) (P : A -> Prop) (a1 a2 : A)
      (l l1 l2 : list A)
: In_with_tail a1 l1 l -> In_with_tail a2 l2 l ->
  P a1 -> P a2 ->
  (forall a1', In a1' l1 -> ~P a1') ->
  (forall a2', In a2' l2 -> ~P a2') ->
  a1 = a2.
  unfold In_with_tail.
  intros S1 S2 P1 P2 nP1 nP2.
  assert (l1 = l2) by (eapply tail_unique_prop; eassumption).
  subst l2.
  assert (a1 :: l1 = a2 :: l1).
  eapply subs_equal_length.
  eassumption.
  assumption.
  reflexivity.
  inversion H; reflexivity.
Qed.
