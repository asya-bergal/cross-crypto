Require Import FCF.FCF.
Require Import FCF.Asymptotic.
Require Import RatUtil.
Require Import Coq.Lists.SetoidList.

Global Instance Proper_negligible :
  Proper (pointwise_relation nat eqRat ==> iff) negligible.
Proof.
  cbv [pointwise_relation Proper respectful].
  split; eauto 10 using negligible_eq, (@symmetry _ eqRat _).
Qed.

Global Instance Proper_negligible_le :
  Proper (pointwise_relation nat leRat ==> Basics.flip Basics.impl) negligible.
Proof.
  cbv [pointwise_relation Proper respectful].
  intros ? ? ? ?; eauto using negligible_le.
Qed.

Lemma negligible_0 : negligible (fun _ => 0).
  eapply negligible_le with (f1 := fun n => 0 / expnat 2 n).
  { reflexivity. }
  { apply negligible_const_num. }
Qed.

Definition image_relation {T} (R:T->T->Prop) {A} (f:A->T) := fun x y => R (f x) (f y).
Global Instance Equivalence_image_relation {T R} {Equivalence_R:Equivalence R} {A} (f:A->T) :
  Equivalence (image_relation R f).
Proof. destruct Equivalence_R; split; cbv; eauto. Qed.
Definition Distribution_eq {A} := pointwise_relation A eqRat.

Global Instance Equivalence_Distribution_eq {A} : Equivalence (@Distribution_eq A).
Proof.
  split; repeat intro; eauto using (@symmetry _ eqRat _), (@transitivity _ eqRat _) with rat.
Qed.

Definition Comp_eq {A} := image_relation Distribution_eq (@evalDist A).
Global Instance Equivalence_Comp_eq {A} : Equivalence (@Comp_eq A) := _.

Global Instance Proper_evalDist {A} : Proper (Comp_eq ==> Distribution_eq) (@evalDist A).
Proof. exact (fun _ _ => id). Qed.

Global Instance Proper_getSupport {A} : Proper (Comp_eq ==> (@Permutation.Permutation _)) (@getSupport A).
Proof. intros ???; eapply evalDist_getSupport_perm_id; assumption. Qed.

Global Instance Proper_sumList {A:Set} {R:A->A->Prop} : Proper (eqlistA R  ==> (R ==> eqRat) ==> eqRat) (@sumList A).
Proof.
  repeat intro. cbv [sumList].
  rewrite <-!fold_left_rev_right.
  eapply eqlistA_rev in H.
  generalize dependent (rev x); generalize dependent (rev y).
  intros ? ?; induction 1; [reflexivity|].
  simpl; f_equiv; eauto.
Qed.

Global Instance Proper_sumList_permutation {A:Set} : Proper ((@Permutation.Permutation A) ==> (Logic.eq ==> eqRat) ==> eqRat) (@sumList A).
Proof.
  intros ? ? H; induction H; repeat intro; cbv [respectful] in *; rewrite ?sumList_cons.
  { eauto with rat. }
  { f_equiv; eauto. }
  { repeat rewrite H by reflexivity.
    repeat rewrite <-ratAdd_assoc.
    rewrite (ratAdd_comm (y0 y)).
    f_equiv.
    eapply (Proper_sumList(R:=Logic.eq)); eauto; reflexivity. }
  { etransitivity; [eapply IHPermutation1 | eapply IHPermutation2];
      intros; subst; (try match goal with H1:_ |- _ => eapply H1 end;reflexivity). }
Qed.

Global Instance Proper_Bind {A B} : Proper (Comp_eq ==> (Logic.eq==>Comp_eq) ==> Comp_eq) (@Bind A B).
Proof.
  intros ?? H ?? G ?. simpl evalDist.

  (* TODO: find out why setoid rewrite does not do this *)
  etransitivity; [|reflexivity].
  eapply Proper_sumList_permutation.
  eapply Proper_getSupport.
  eassumption.
  intros ? ? ?; subst.
  f_equiv.
  { eapply Proper_evalDist. assumption. }
  { eapply Proper_evalDist. eapply G. reflexivity. }
Qed.

Lemma eq_impl_negligible : forall A (x y : nat -> Comp A), pointwise_relation _ Comp_eq x y -> forall t, negligible (fun eta : nat => | evalDist (x eta) t - evalDist (y eta) t|).
Admitted.

Lemma Comp_eq_bool (x y:Comp bool) :
  well_formed_comp x
  -> well_formed_comp y
  -> Pr [x] == Pr[y]
  -> Comp_eq x y.
  intros.
  intro b.
  destruct b; trivial.
  rewrite !evalDist_complement; trivial.
  f_equiv; trivial.
Qed.

Lemma Comp_eq_evalDist A (x y:Comp A) :
  (forall c, evalDist x c == evalDist y c)
  <-> Comp_eq x y.
  split; intro.
  { cbv [Comp_eq Distribution_eq pointwise_relation image_relation]; assumption. }
  { cbv [Comp_eq Distribution_eq pointwise_relation image_relation] in H; assumption. }
Qed.

Lemma Bind_unused A B (a:Comp A) (b:Comp B) :
  Comp_eq (_ <-$ a; b) b.
Admitted. (* TODO: does FCF have something like this? *)

Lemma Comp_eq_left_ident (A B: Set) (H: EqDec A) (H': EqDec B) (x: A) (f: A -> Comp B):
  Comp_eq (x' <-$ ret x; f x') (f x).
Proof.
  apply Comp_eq_evalDist.
  intros.
  apply evalDist_left_ident_eq.
Qed.

Lemma Comp_eq_right_ident (A : Set) (H: EqDec A) (cA : Comp A) :
  Comp_eq (x <-$ cA; ret x) cA.
Proof.
  apply Comp_eq_evalDist.
  intros.
  apply evalDist_right_ident.
Qed.

Lemma Comp_eq_associativity (A B C: Set) (H : EqDec A) (cA : Comp A)
      (f : A -> Comp B) (g : B -> Comp C) :
  Comp_eq (x <-$ cA; y <-$ f x; g y) (y <-$ (x <-$ cA; f x); g y).
Proof.
  intros.
  apply Comp_eq_evalDist.
  intros.
  fcf_inline_first.
  reflexivity.
Qed.

Lemma Comp_eq_swap : forall (A B : Set)(c1 : Comp A)(c2 : Comp B)(C : Set)(c3 : A -> B -> Comp C),
  Comp_eq (a <-$ c1; b <-$ c2; (c3 a b)) (b <-$ c2; a <-$ c1; (c3 a b)). 
Proof.
  intros.
  apply Comp_eq_evalDist.
  intros.
  apply evalDist_commute_eq.
Qed.
