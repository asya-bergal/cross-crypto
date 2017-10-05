Require Import FCF.FCF.
Require Import FCF.Asymptotic.
Require Import FCF.Admissibility.
Require Import Tactics.
Require Import FrapTactics.
Require Import FCF.Encryption.
Require Import FCF.SplitVector.
Require Import FCF.TwoWorldsEquiv.
Require Import FCF.OTP.
Require Import RatUtil.
Require Import RewriteUtil.
Require Import Util.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.SetoidList.
Require Import Coq.Lists.ListSet.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.MSets.MSetProperties.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.FSets.FSetFacts.
Require Import Coq.PArith.BinPosDef.
Module PositiveMapFacts := FMapFacts.WFacts_fun PositiveMap.E PositiveMap.
Module PositiveMapProperties := FMapFacts.WProperties_fun PositiveMap.E PositiveMap.
Print PositiveSet.E.
Module PositiveSetProperties := MSetProperties.WPropertiesOn PositiveSet.E MSetPositive.PositiveSet.

Ltac solve_Proper_eqs :=
  idtac;
  lazymatch goal with
  | [ |- Proper _ _ ] => apply @reflexive_proper; solve_Proper_eqs
  | [ |- Reflexive (_ ==> _)%signature ]
    => apply @reflexive_eq_dom_reflexive; solve_Proper_eqs
  | [ |- Reflexive _ ] => try apply eq_Reflexive
  end.
Ltac is_evar_or_eq e :=
  first [ is_evar e
        | match e with
          | eq => idtac
          end ].
Ltac is_evar_or_eq_or_evar_free e :=
  first [ is_evar_or_eq e
        | try (has_evar e; fail 1) ].
Hint Extern 1 (Proper ?e _) =>
is_evar_or_eq e; solve_Proper_eqs : typeclass_instances.
Hint Extern 1 (Proper (?e1 ==> ?e2) _) =>
is_evar_or_eq e1; is_evar_or_eq_or_evar_free e2; solve_Proper_eqs : typeclass_instances.
Hint Extern 1 (Proper (?e1 ==> ?e2 ==> ?e3) _) =>
is_evar_or_eq e1; is_evar_or_eq e2; is_evar_or_eq_or_evar_free e3; solve_Proper_eqs : typeclass_instances.
Hint Extern 1 (Proper (?e1 ==> ?e2 ==> ?e3 ==> ?e4) _) =>
is_evar_or_eq e1; is_evar_or_eq e2; is_evar_or_eq e3; is_evar_or_eq_or_evar_free e4; solve_Proper_eqs : typeclass_instances.
Hint Extern 1 (Proper (?e1 ==> ?e2 ==> ?e3 ==> ?e4 ==> ?e5) _) =>
is_evar_or_eq e1; is_evar_or_eq e2; is_evar_or_eq e3; is_evar_or_eq e4; is_evar_or_eq_or_evar_free e5; solve_Proper_eqs : typeclass_instances.
Hint Extern 1 (Proper (?e1 ==> ?e2 ==> ?e3 ==> ?e4 ==> ?e5 ==> ?e6) _) =>
is_evar_or_eq e1; is_evar_or_eq e2; is_evar_or_eq e3; is_evar_or_eq e4; is_evar_or_eq e5; is_evar_or_eq_or_evar_free e6; solve_Proper_eqs : typeclass_instances.

Section FMapTODO.
  Lemma PosMap_add_commutes {A} x y (m : PositiveMap.t A) a b :
    (x <> y \/ a = b) ->
    PositiveMap.Equal (PositiveMap.add x a (PositiveMap.add y b m))
                      (PositiveMap.add y b (PositiveMap.add x a m)).
  Proof.
    cbv [PositiveMap.Equal]; destruct 1; intros;
      repeat match goal with
             | _ => rewrite PositiveMapFacts.add_o
             | |- context [if ?x then _ else _] =>
               destruct x; subst; try congruence
             end.
  Qed.

  Lemma subset_inter s1 s2 s3:
    PositiveSet.Subset s1 s3 ->
    PositiveSet.Subset s2 s3 ->
    PositiveSet.Subset (PositiveSet.inter s1 s2) s3.
  Admitted.
  
  Lemma subset_union s1 s2 s3 :
    PositiveSet.Subset (PositiveSet.union s2 s3) s1
    -> PositiveSet.Subset s2 s1 /\ PositiveSet.Subset s3 s1.
  Admitted.

  Lemma find_update_in {A} k (m1 m2 : PositiveMap.t A) :
    PositiveMap.In k m2 ->
    PositiveMap.find k (PositiveMapProperties.update m1 m2) =
    PositiveMap.find k m2.
  Admitted.

  Lemma find_update_not_in {A} k (m1 m2 : PositiveMap.t A) :
    ~PositiveMap.In k m2 ->
    PositiveMap.find k (PositiveMapProperties.update m1 m2) =
    PositiveMap.find k m1.
  Admitted.

  Lemma update_assoc {A} (m0 m1 m2 : PositiveMap.t A):
    PositiveMapProperties.update m0 (PositiveMapProperties.update m1 m2) =
    PositiveMapProperties.update (PositiveMapProperties.update m0 m1) m2.
  Admitted.

  Lemma update_add {A} (m0 m1:PositiveMap.t A) i a :
    PositiveMap.Equal
      (PositiveMapProperties.update m0 (PositiveMap.add i a m1))
      (PositiveMap.add i a (PositiveMapProperties.update m0 m1)).
  Proof.
  Admitted.
  
  Lemma union_remove_equal x s s' s1 s2
        (Hadd: PositiveSetProperties.Add x s s') :
    ~PositiveSet.In x s ->
    PositiveSet.Equal (PositiveSet.union s1 s2) s' ->
    PositiveSet.Equal (PositiveSet.union (PositiveSet.remove x s1)
                                         (PositiveSet.remove x s2)) s.
  Proof.
    cbv [PositiveSet.Equal PositiveSetProperties.Add] in *; intros.
    match goal with H: forall _, PositiveSet.In _ _ <-> PositiveSet.In _ _
                                 |- context [PositiveSet.In ?x] =>
                    specialize (H x) end.
    rewrite Hadd in *.
    rewrite PositiveSet.union_spec in *.
    rewrite !PositiveSet.remove_spec in *.
    (* asserts because tauto is bad at substituting *)
    assert (x = a <-> a = x) by (split; congruence).
    assert (x = a -> ~ PositiveSet.In a s) by congruence.
    repeat match goal with
           | _ => progress intros
           | H: _ /\ _ |- _ => destruct H
           | H: _ \/ _ |- _ => destruct H
           | _ => split
           | _ => tauto
           end.
  Qed.

  Lemma add_add_eq {A} x y (a b : A) m (H:x = y) :
    PositiveMap.Equal
      (PositiveMap.add x a (PositiveMap.add y b m))
      (PositiveMap.add x a m).
  Admitted.

  Lemma update_overwrite {A} x (m1 m2 : PositiveMap.t A) :
    PositiveMap.In x m2 ->
    PositiveMap.Equal 
      (PositiveMapProperties.update m1 m2)
      (PositiveMapProperties.update (PositiveMap.remove x m1) m2).
  Admitted.


  Lemma union_remove s1 s2 x :
    PositiveSet.Equal (PositiveSet.union s1 s2)
                      (PositiveSet.union s1 (PositiveSet.remove x s2)).
  Admitted.

  Lemma empty_not_in {A} m :
    @PositiveMap.Empty A m <-> forall x, ~PositiveMap.In x m.
  Proof.
    cbv [PositiveMap.Empty PositiveMap.MapsTo PositiveMap.In not neq].
    split; repeat match goal with
                  | _ => progress intro
                  | H: exists _, _ |- _ => destruct H
                  | _ => solve [eauto]
                  end.
  Qed.

  Lemma update_empty_r {A} (m1 m2: PositiveMap.t A) :
    PositiveMap.Empty m2 ->
    PositiveMap.Equal (PositiveMapProperties.update m1 m2) m1.
  Admitted.

  Lemma update_subset {A} (m1 m2 : PositiveMap.t A) :
    (forall k, PositiveMap.In k m1 -> PositiveMap.In k m2) ->
    PositiveMap.Equal (PositiveMapProperties.update m1 m2) m2.
  Admitted.

  Lemma empty_inter: forall s : PositiveSet.t, PositiveSet.eq (PositiveSet.inter s PositiveSet.empty) PositiveSet.empty.
    intros.
    apply PositiveSetProperties.empty_is_empty_1.
    apply PositiveSetProperties.empty_inter_2.
    apply PositiveSet.empty_spec.
  Qed.
End FMapTODO.

Section Language.
  Context {type  : Set} {eqdec_type : EqDec type}
          {interp_type : type -> nat -> Set} {eqdec_interp_type : forall {t eta}, EqDec (interp_type t eta)}
          {tbool trand tmessage : type} {tlist : type -> type} {tprod : type -> type -> type}.
  Context {func : type -> type -> Set}.

  Inductive expr : type -> Type :=
  | expr_const {t} (_:forall eta, interp_type t eta) : expr t
  | expr_random (idx:positive) : expr trand
  | expr_adversarial (_:expr (tlist tmessage)) : expr tmessage
  | expr_func {t1 t2} (_:func t1 t2) (_:expr t1) : expr t2
  | expr_pair {t1 t2} (_:expr t1) (_:expr t2) : expr (tprod t1 t2).

  Bind Scope expr_scope with expr.
  Delimit Scope expr_scope with expr.
  Notation "A @ B" := (expr_func A B) (at level 99) : expr_scope.
  Local Open Scope expr_scope.

  Fixpoint randomness_indices {t:type} (e:expr t) : PositiveSet.t :=
    match e with
    | expr_const _ => PositiveSet.empty
    | expr_random idx => PositiveSet.singleton idx
    | expr_adversarial x => randomness_indices x
    | expr_func f x => randomness_indices x
    | expr_pair a b => PositiveSet.union (randomness_indices a) (randomness_indices b)
    end.

  (* TODO: use a map with a canonical representation *)
  Global Instance randomness_map_eq_dec {eta} : EqDec (PositiveMap.t (interp_type trand eta)). Admitted.

  Context (cast_rand : forall eta, Bvector eta -> interp_type trand eta).
  Section GenerateRandomness. 
    Context (eta:nat).

    Definition genrand : Comp _ := (r <-$ {0,1}^eta; ret (cast_rand eta r)).
    (* TODO: use [genrand] in the remainder of this section *)

    Definition generate_randomness_single i rndC := 
      rnds' <-$ rndC;
        ri <-$ {0,1}^eta;
        ret (PositiveMap.add i (cast_rand eta ri) rnds').

    Definition generate_randomness idxs
      : Comp (PositiveMap.t (interp_type trand eta))
      := PositiveSet.fold generate_randomness_single
                          idxs
                          (ret (PositiveMap.empty _)).

    Lemma empty_randomness : 
      Comp_eq (generate_randomness PositiveSet.empty)
              (ret (PositiveMap.empty _)).
    Proof.
      intros; cbv [generate_randomness].
      rewrite PositiveSetProperties.fold_empty.
      reflexivity.
    Qed.

    Global Instance Proper_generate_randomness_single :
      Proper (eq ==> Comp_eq ==> Comp_eq) generate_randomness_single.
    Proof.
      cbv [Proper respectful generate_randomness_single]; intros; subst.
      match goal with H: Comp_eq _ _ |- _ => rewrite H; reflexivity end.
    Qed.


    (* TODO: This is unprovable; it is true if programs only use the
    map interface functions and never modify the map structurally. To
    prove this you need a canonical map.*)
    Lemma generate_randomness_single_transpose :
      transpose Comp_eq generate_randomness_single.
    Proof.
      cbv [transpose generate_randomness_single]; intros.
      repeat setoid_rewrite <-Bind_assoc.
      repeat setoid_rewrite Bind_Ret_l.

      destruct (Pos.eq_dec x y).
      {
        etransitivity.
        { 
          do 3 (eapply Proper_Bind; [reflexivity|];
                cbv [pointwise_relation]; intros).

    (* Line below fails because Ret is not proper over
          PositiveMap.eq *)
          (* rewrite add_add_eq. *)
          
    Admitted.

    Lemma add_generate_randomness {A} (f:_->Comp A) x s s' :
      PositiveSetProperties.Add x s s' ->
      ~PositiveSet.In x s ->
      Comp_eq (a <-$ generate_randomness s'; f a)
              (a <-$ {0,1}^eta;
                 b <-$ generate_randomness s;
                 f (PositiveMap.add x (cast_rand eta a) b)).
    Proof.
      cbv [generate_randomness]; intros.
      rewrite PositiveSetProperties.fold_2 by
          (try eassumption; try (exact _);
           auto using generate_randomness_single_transpose).
      cbv [generate_randomness_single].
      repeat setoid_rewrite <-Bind_assoc;
        repeat setoid_rewrite Bind_Ret_l;
        rewrite Bind_comm with (c2 := {0,1}^_).
      reflexivity.
    Qed.

    Lemma generate_single i idxs:
      forall {A} (f:_->Comp A),
        PositiveSet.In i idxs ->
        Comp_eq
          (t <-$ generate_randomness idxs;
             f (PositiveMap.find i t))
          (r <-$ { 0 , 1 }^ eta; f (Some (cast_rand eta r))).
    Proof.
      intros.
      apply PositiveSetProperties.Add_remove in H.
      rewrite add_generate_randomness
        by eauto using PositiveSetProperties.Dec.F.remove_1.

      (* TODO: this should work but doesn't:  
         setoid_rewrite PositiveMapProperties.F.add_eq_o *)
      f_equiv; cbv [pointwise_relation]; intros.
      etransitivity. {
        apply Proper_Bind; [reflexivity|].
        cbv [pointwise_relation]; intros.
        rewrite PositiveMapProperties.F.add_eq_o by reflexivity.
        eapply reflexivity. }
      rewrite Bind_unused; reflexivity.
    Qed. 

    Lemma Proper_Bind_generate_randomness {A: Set} idxs :
      Proper (
          (fun f g =>
             forall m,
               (forall i, PositiveMap.In i m <-> PositiveSet.In i idxs) ->
               Comp_eq (f m) (g m))
            ==> Comp_eq)
             (Bind (A:=A) (generate_randomness idxs)).
    Proof.
      cbv [Proper respectful generate_randomness].
      match goal with |- context [PositiveSet.fold ?f _] =>
                      set (F:=f) end.
      apply PositiveSetProperties.fold_rec; [|subst F; simpl];
        repeat match goal with
               | _ => progress intros
               | _ => setoid_rewrite Bind_Ret_l
               | _ => setoid_rewrite <-Bind_assoc
               | _ => rewrite PositiveMapProperties.F.empty_in_iff
               | H: forall m, _ -> Comp_eq (_ m) (_ m) |- _ => apply H; intros
               | H: PositiveSet.Empty _ |- context[PositiveSet.In ?x _] =>
                 specialize (H x)
               | H: forall _ _, _ -> Comp_eq (Bind _ _) (Bind _ _)
                                |- _ => apply H; intros
               | H: forall m, _ -> Comp_eq (_ m) (_ m)
                              |- _ => apply H; intros
               | _ => rewrite PositiveMapFacts.add_in_iff
               | H: PositiveSetProperties.Add _ _ _ |- context [PositiveSet.In ?x] =>
                 cbv [PositiveSetProperties.Add] in H; specialize (H x)
               | |- Comp_eq (Bind ?x _) (Bind ?x _) =>
                 apply Proper_Bind;[reflexivity|];
                   cbv [pointwise_relation]; intros
               | H: _ |- _ => rewrite H; tauto
               | _ => tauto
               end.
    Qed.

    Global Instance Proper_generate_randomness :
      Proper (PositiveSet.Equal ==> Comp_eq) generate_randomness.
    Proof.
      cbv [Proper respectful generate_randomness].
      intros.
      cbv [PositiveSet.Equal] in H.
      apply PositiveSetProperties.fold_equal;
        auto using generate_randomness_single_transpose; try exact _.
    Qed.

    Lemma generate_twice idxs1 :
      forall idxs2 {A} (f:_->Comp A),
        Proper (PositiveMap.Equal ==> Comp_eq) f ->
        Comp_eq
          (a <-$ generate_randomness idxs1;
             b <-$ generate_randomness idxs2;
             f (PositiveMapProperties.update b a))
          (a <-$ generate_randomness (PositiveSet.union idxs1 idxs2);
             f a).
    Proof.
      apply PositiveSetProperties.set_induction with (s:=idxs1).
      {
        intros.
        etransitivity. {
          do 2 (eapply Proper_Bind_generate_randomness; intros).
          rewrite update_empty_r; [eapply reflexivity|].
          apply empty_not_in; intros; cbv [PositiveSet.Empty] in *.
          repeat match goal with
                 | H: forall _, _ |- context[PositiveMap.In ?x] =>
                   specialize (H x) end; tauto. }
        rewrite Bind_unused.
        rewrite PositiveSetProperties.empty_union_1 by assumption.
        reflexivity. }
      { intros until 1. intro new_elt; intros.
        rewrite add_generate_randomness with (s'0:=s') by eassumption.
        rewrite add_generate_randomness with
            (s0:=PositiveSet.union s (PositiveSet.remove new_elt idxs2))
            (s'0:=PositiveSet.union s' idxs2) (x:=new_elt).
        Focus 2. {
          cbv [PositiveSetProperties.Add]; intros.
          rewrite (union_remove s' idxs2 new_elt).
          eapply PositiveSetProperties.union_Add.
          assumption. } Unfocus.
        Focus 2. {
          rewrite !PositiveSet.union_spec, PositiveSet.remove_spec.
          assert (new_elt = new_elt) by reflexivity.
          tauto. } Unfocus.

        setoid_rewrite update_add.
        f_equiv; cbv [pointwise_relation]; intros.
        match goal with H: _ |- context [PositiveMap.add ?i ?x] =>
                        rewrite H with (f:=fun m => f (PositiveMap.add i x m)) end.
        rewrite <-union_remove; try reflexivity.
        cbv [Proper respectful]; intros;
          match goal with H: PositiveMap.Equal _ _ |- _ => rewrite H end;
          reflexivity. }
    Qed.

  End GenerateRandomness.

  Context (interp_func : forall {t1 t2} (f:func t1 t2) {eta}, interp_type t1 eta -> interp_type t2 eta).
  Context (interp_pair : forall {t1 t2 eta}, interp_type t1 eta -> interp_type t2 eta -> interp_type (tprod t1 t2) eta).
  Arguments interp_func {_ _} _ {_}.
  Arguments interp_pair {_ _ _}.

  Fixpoint interp_fixed {t} (e:expr t) (eta : nat)
           (adv: interp_type (tlist tmessage) eta -> interp_type tmessage eta)
           (rands: PositiveMap.t (interp_type trand eta))
    : interp_type t eta :=
    match e with
    | expr_const c => c eta
    | expr_random i => match PositiveMap.find i rands with Some r => r | _ => cast_rand eta (Bvector_exists _) end
    | expr_adversarial inputs => adv (interp_fixed inputs eta adv rands)
    | expr_func f inputs => interp_func f (interp_fixed inputs eta adv rands)
    | expr_pair a b => interp_pair (interp_fixed a eta adv rands) (interp_fixed b eta adv rands)
    end.
  Definition interp {t} (e:expr t) (eta:nat)
             (adv: interp_type (tlist tmessage) eta -> interp_type tmessage eta)
    : Comp (interp_type t eta)
    := rands <-$ generate_randomness eta (randomness_indices e); ret (interp_fixed e eta adv rands).

  Global Instance Proper_interp_term_fixed {t} (e:expr t) eta adv :
    Proper (PositiveMap.Equal ==> Logic.eq) (interp_fixed e eta adv).
  Proof.
    cbv [Proper respectful]; induction e; intros; simpl; try reflexivity.
    { cbv [PositiveMap.Equal] in *. rewrite H. reflexivity. }
    { erewrite IHe; eauto. }
    { erewrite IHe; eauto. }
    { erewrite IHe1, IHe2; eauto. }
  Qed.

  Section Security.
    (* the adversary is split into three parts for no particular reason. It first decides how much randomness it will need, then interacts with the protocol (repeated calls to [adverary] with all messages up to now as input), and then tries to claim victory ([distinguisher]). There is no explicit sharing of state between these procedures, but all of them get the same random inputs in the security game. The handling of state is a major difference between FCF [OracleComp] and this framework *)
    Definition universal_security_game
               (evil_rand_indices: forall eta:nat, PositiveSet.t)
               (adversary:forall (eta:nat) (rands: PositiveMap.t (interp_type trand eta)), interp_type (tlist tmessage) eta -> interp_type tmessage eta)
               (distinguisher: forall {t} (eta:nat) (rands: PositiveMap.t (interp_type trand eta)), interp_type t eta -> Datatypes.bool)
               (eta:nat) {t:type} (e:expr t) : Comp Datatypes.bool :=
      evil_rands <-$ generate_randomness eta (evil_rand_indices eta);
        out <-$ interp e eta (adversary eta (evil_rands));
        ret (distinguisher eta evil_rands out).

    Definition indist {t:type} (a b:expr t) : Prop :=  forall adl adv dst,
        (* TODO: insert bounds on coputational complexity of [adv] and [dst] here *)
        let game eta e := universal_security_game adl adv dst eta e in
        negligible (fun eta => | Pr[game eta a] -  Pr[game eta b] | ).

    Global Instance Equivalence_indist {t} : Equivalence (@indist t) := _.
    Proof.
      split; cbv [Reflexive Symmetric Transitive indist]; intros;
        [ setoid_rewrite ratDistance_same (* Reflexive *)
        | setoid_rewrite ratDistance_comm (* Symmetric *)
        | setoid_rewrite ratTriangleInequality ]; (* Transitive *)
        eauto using negligible_0, negligible_plus.
    Qed.
  End Security.
  Infix "≈" := indist (at level 70).

  Lemma interp_term_const {t} e eta a : Comp_eq (interp (@expr_const t e) eta a) (ret (e eta)).
  Proof. cbv -[Comp_eq]; setoid_rewrite Bind_unused; reflexivity. Qed.

  Lemma interp_term_rand i eta a : Comp_eq (interp (@expr_random i) eta a) (genrand eta).
  Admitted.

  Context (vtrue vfalse : forall eta, interp_type tbool eta)
          (inspect_vbool : forall eta, interp_type tbool eta -> bool)
          (case_tbool : forall eta (b:interp_type tbool eta), b = if inspect_vbool eta b then vtrue eta else vfalse eta).
  Arguments inspect_vbool {eta}.

  Definition whp (e:expr tbool) := e ≈ (expr_const vtrue).

  Local Existing Instance eq_subrelation | 5.
  (* Local Instance subrelation_eq_Comp_eq {A} : subrelation eq (Comp_eq(A:=A)) | 2 := eq_subrelation _. *)

  Context (feqb : forall t, func (tprod t t) tbool).
  Arguments feqb {_}.
  Context (interp_feqb : forall t eta (v1 v2:interp_type t eta),
              interp_func feqb (interp_pair v1 v2) = if eqb v1 v2 then vtrue eta else vfalse eta).

  Section Equality.
    Definition eqwhp {t} (e1 e2:expr t) : Prop := whp (expr_func feqb (expr_pair e1 e2)).

    Global Instance Reflexive_eqwhp {t} : Reflexive (@eqwhp t).
    Proof.
      cbv [Reflexive indist universal_security_game eqwhp whp interp]; intros.
      cbn [interp_fixed].
      (* TODO: report inlined setoid rewrite *)
      eapply Proper_negligible. 
      {
        intro eta.
        setoid_rewrite interp_feqb.
        setoid_rewrite eqb_refl.
        setoid_rewrite Bind_unused.
        eapply reflexivity.
      }
      setoid_rewrite ratDistance_same.
      eapply negligible_0.
    Qed.

    Global Instance Symmetric_eqwhp {t} : Symmetric (@eqwhp t).
    Proof.
      cbv [Symmetric indist universal_security_game eqwhp whp interp]; intros.
      cbn [interp_fixed] in *.
      (* TODO: report inlined setoid rewrite *)
      eapply Proper_negligible. 
      {
        intro eta.

        setoid_rewrite interp_feqb.
        setoid_rewrite eqb_symm.
        setoid_rewrite <-interp_feqb.

        cbn [randomness_indices].
        setoid_rewrite PositiveSetProperties.union_sym.
        
        eapply reflexivity.
      }
      eapply H.
    Qed.

    Global Instance Transitive_eqwhp {t} : Transitive (@eqwhp t). Admitted.

    Global Instance Proper_eqwhp_pair {t1 t2} : Proper (eqwhp ==> eqwhp ==> eqwhp) (@expr_pair t1 t2).
    Admitted.

    Global Instance Proper_eqwhp_adversarial : Proper (eqwhp ==> eqwhp) expr_adversarial.
    Admitted.
  End Equality.

  Section LateInterp.
    Fixpoint interp_late
             {t} (e:expr t) (eta : nat)
             (adv: interp_type (tlist tmessage) eta -> interp_type tmessage eta)
             (fixed_rand: PositiveMap.t (interp_type trand eta))
    : Comp (interp_type t eta) :=
      match e with
      | expr_const c => ret (c eta)
      | expr_random i =>
        match PositiveMap.find i fixed_rand with
        | Some r => ret r
        | _ => r <-$ {0,1}^eta; ret (cast_rand eta r)
        end
      | expr_adversarial ctx =>
        ctx <-$ interp_late ctx eta adv fixed_rand; ret (adv ctx)
      | expr_func f x => 
        x <-$ interp_late x eta adv fixed_rand; ret (interp_func f x)
      | expr_pair a b =>
        common_rand <-$ generate_randomness eta (PositiveSet.inter (randomness_indices b) (randomness_indices a));
          let rands := PositiveMapProperties.update common_rand fixed_rand in
          b <-$ interp_late b eta adv rands;
            a <-$ interp_late a eta adv rands;
            ret (interp_pair a b)
      end.

    Lemma interp_late_correct' {t} (e:expr t) eta adv :
      forall univ (H:PositiveSet.Subset (randomness_indices e) univ) fixed,
        Comp_eq (interp_late e eta adv fixed)
                (rands <-$ generate_randomness eta univ;
                   ret (interp_fixed e eta adv
                                     (PositiveMapProperties.update rands fixed))).
    Proof.
      induction e; intros;
        simpl interp_late; simpl interp_fixed.
      { rewrite Bind_unused. reflexivity. }
      {
        simpl randomness_indices in *.
        match goal with |- context[match ?x with | _ => _ end] =>
                        case_eq x; intros end.
        {
          etransitivity.
          Focus 2. {
            apply Proper_Bind_generate_randomness.
            intros.
            rewrite find_update_in
              by (apply PositiveMapProperties.F.in_find_iff; congruence).
            eapply reflexivity. } Unfocus.
          rewrite Bind_unused.
          rewrite H0; reflexivity. }
        {  
          etransitivity.
          Focus 2. {
            apply Proper_Bind_generate_randomness.
            intros.
            rewrite find_update_not_in
              by (apply PositiveMapProperties.F.not_find_in_iff; congruence).
            eapply reflexivity. } Unfocus.

          remember (fun m => ret (match m with | Some r => r | None => cast_rand eta (Bvector_exists eta) end)) as G.
          transitivity (Bind (generate_randomness eta univ)
                             (fun t => G (PositiveMap.find idx t)));
            [|subst G; reflexivity].
          rewrite generate_single.
          subst G; reflexivity.
          cbv [PositiveSet.Subset] in H.
          apply H; apply PositiveSet.singleton_spec; reflexivity.
      } }
      { simpl randomness_indices in *.
        rewrite IHe by eassumption.
        repeat setoid_rewrite <-Bind_assoc.
        repeat setoid_rewrite Bind_Ret_l.
        reflexivity. }
      { simpl randomness_indices in *.
        rewrite IHe by eassumption.
        repeat setoid_rewrite <-Bind_assoc.
        repeat setoid_rewrite Bind_Ret_l.
        reflexivity. }
      { 
        match goal with H : _ |- _ =>
                        simpl randomness_indices in H;
                          apply subset_union in H; destruct H end.
        
        setoid_rewrite IHe2; [|eassumption].
        setoid_rewrite IHe1; [|eassumption].
        repeat setoid_rewrite <-Bind_assoc.
        repeat setoid_rewrite Bind_Ret_l.

        (* FIXME: this might be false ~ andreser *)
        assert (bind_twice : forall {A B:Set} (x: Comp B) (f : B -> B -> Comp A),
                   Comp_eq (Bind x (fun y => Bind x (f y)))
                           (Bind x (fun y => f y y))) by admit.
        repeat setoid_rewrite bind_twice.
        clear bind_twice.

        repeat setoid_rewrite update_assoc.

        match goal with
          |- Comp_eq (Bind ?y (fun a => Bind ?x _)) (Bind ?x ?g) =>
          rewrite generate_twice with (f:=g) end.
        { f_equiv; apply Proper_generate_randomness.
          auto using PositiveSetProperties.union_subset_equal, subset_inter. }
        { cbv [Proper respectful]; intros;
            match goal with H: PositiveMap.Equal _ _ |- _ => rewrite H end;
            reflexivity. } }
    Admitted.
    
    Lemma interp_late_correct {t} (e:expr t) eta adv:
      Comp_eq
        (interp_late e eta adv (PositiveMap.empty _))
        (interp e eta adv).
    Proof.
      rewrite interp_late_correct'; cbv [interp]; reflexivity.
    Qed.
  End LateInterp.

  Lemma indist_rand x y : expr_random x ≈ expr_random y.
  Proof.
    cbv [indist universal_security_game]; intros.
    setoid_rewrite <-interp_late_correct.
    cbv [interp_late].
    setoid_rewrite PositiveMap.gempty.
    setoid_rewrite ratDistance_same.
    trivial using negligible_0.
  Qed.

  Definition independent {T} {U} (x : expr T) (y : expr U) :=
    PositiveSet.eq (PositiveSet.inter (randomness_indices x) (randomness_indices y))
                   PositiveSet.empty.

  (* TODO: do we need explicit substitution to define [interact]? *)

  Context (ite : forall t, func (tprod tbool (tprod t t)) t).
  Arguments ite {_}.
  Context (interp_ite : forall t eta b (v1 v2:interp_type t eta), interp_func ite (interp_pair b (interp_pair v1 v2)) = if inspect_vbool b then v1 else v2).
  Arguments interp_ite {_ _}.

  Lemma if_same b t (e:expr t) : eqwhp (expr_func ite (expr_pair b (expr_pair e e))) e.
  Proof.
    cbv [eqwhp whp indist universal_security_game interp]; intros.
    cbn [interp_fixed].
    eapply Proper_negligible; [intro eta|].
    {
      setoid_rewrite interp_feqb.
      setoid_rewrite interp_ite.
      assert (if_same : forall (x:bool) {T} (Y:T), (if x then Y else Y) = Y) by (destruct x; reflexivity).
      setoid_rewrite if_same at 1.
      setoid_rewrite eqb_refl.
      setoid_rewrite Bind_unused.
      eapply reflexivity.
    }
    setoid_rewrite ratDistance_same.
    eapply negligible_0.
  Qed.

  Context (inspect_vtrue : forall eta, inspect_vbool (vtrue eta) = true).
  Context (inspect_vfalse : forall eta, inspect_vbool (vfalse eta) = false).

  Lemma if_true t (e1 e2:expr t) : eqwhp (expr_func ite (expr_pair (expr_const vtrue) (expr_pair e1 e2))) e1.
  Proof.
    cbv [eqwhp whp indist universal_security_game interp]; intros.
    cbn [interp_fixed].
    eapply Proper_negligible; [intro eta|].
    {
      setoid_rewrite interp_ite.
      setoid_rewrite inspect_vtrue.
      setoid_rewrite interp_feqb.
      setoid_rewrite eqb_refl.
      setoid_rewrite Bind_unused.
      eapply reflexivity.
    }
    setoid_rewrite ratDistance_same.
    eapply negligible_0.
  Qed.

  Lemma if_false t (e1 e2:expr t) : eqwhp (expr_func ite (expr_pair (expr_const vfalse) (expr_pair e1 e2))) e2.
  Proof.
    cbv [eqwhp whp indist universal_security_game interp]; intros.
    cbn [interp_fixed].
    eapply Proper_negligible; [intro eta|].
    {
      setoid_rewrite interp_ite.
      setoid_rewrite inspect_vfalse.
      setoid_rewrite interp_feqb.
      setoid_rewrite eqb_refl.
      setoid_rewrite Bind_unused.
      eapply reflexivity.
    }
    setoid_rewrite ratDistance_same.
    eapply negligible_0.
  Qed.

End Language.
