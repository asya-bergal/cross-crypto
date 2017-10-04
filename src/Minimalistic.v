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
  Context {base_type : Set}
          {interp_base_type:base_type->nat->Set}
          {eqdec_base_type : forall {t eta}, EqDec (interp_base_type t eta)}.

  Inductive type := Type_base (t:base_type) | Type_arrow (dom:type) (cod:type).
  Global Coercion Type_base : base_type >-> type.
  Fixpoint interp_type (t:type) (eta:nat) : Set :=
    match t with
    | Type_base t => interp_base_type t eta
    | Type_arrow dom cod => interp_type dom eta -> interp_type cod eta
    end.
  Delimit Scope term_scope with term.
  Bind Scope term_scope with type.
  Notation "A -> B" := (Type_arrow A B) : term_scope.

  Context {sbool message list_message rand : base_type}
          {strue sfalse:forall eta, interp_type sbool eta}.
  (* we would need a dependently typed map data structure for dependently typed randomness *)

  (* A term is parametrized by its type, which can either be one of the base_types *)
  (* listed above, or an arrow type consisting of multiple interpreted base_types. *)
  Inductive term : type -> Type :=
  | Term_const {t} (_:forall eta, interp_type t eta) : term t
  | Term_random (idx:positive) : term rand
  | Term_adversarial (_:term list_message) : term message
  | Term_app {dom cod} (_:term (Type_arrow dom cod)) (_:term dom) : term cod.

  (* Term with one or more holes in it *)
  Inductive term_wh (holetype : type) : type -> Type :=
  | Term_wh_const {t} (_:forall eta, interp_type t eta) : term_wh holetype t
  | Term_wh_random (idx:positive) : term_wh holetype rand
  | Term_wh_adversarial (_:term_wh holetype list_message) : term_wh holetype message
  | Term_wh_app {dom cod} (_:term_wh holetype (Type_arrow dom cod)) (_:term_wh holetype dom) :
      term_wh holetype cod
  | Term_wh_hole : term_wh holetype holetype.

  Bind Scope term_scope with term.
  Notation "A @ B" := (Term_app A B) (at level 99) : term_scope.
  Notation "'rnd' n" := (Term_random n) (at level 35) : term_scope.
  Notation "'const' c" := (Term_const c) (at level 35) : term_scope.

  Notation "A h@ B" := (Term_wh_app A B) (at level 99) : term_scope.
  Notation "'hrnd' n" := (Term_wh_random n) (at level 35) : term_scope.
  Notation "'hconst' c" := (Term_wh_const c) (at level 35) : term_scope.
  Notation "'hole'" := (Term_wh_hole) (at level 35) : term_scope.


  Fixpoint fill {holetype t} (twh : term_wh holetype t) (filler : term holetype) : term t :=
    match twh with
    | Term_wh_const _ c => Term_const c
    | Term_wh_random _ r => Term_random r
    | Term_wh_adversarial _ ctx => Term_adversarial (fill ctx filler)
    | Term_wh_app _ f x => Term_app (fill f filler) (fill x filler)
    | Term_wh_hole _ => filler
    end.

  Fixpoint randomness_indices {t:type} (e:term t) : PositiveSet.t :=
    match e with
    | Term_random idx => PositiveSet.singleton idx
    | Term_app f x => PositiveSet.union (randomness_indices f) (randomness_indices x)
    | Term_adversarial x => randomness_indices x
    | _ => PositiveSet.empty
    end.
  Scheme Equality for PositiveMap.tree.
  Global Instance randomness_map_eq_dec {eta} : EqDec (PositiveMap.t (interp_type rand eta)).
  Proof.
    Print EqDec.
    eapply Build_EqDec.
    constructor.
  Admitted.

  Context (cast_rand : forall eta, Bvector eta -> interp_type rand eta).
  Section GenerateRandomness. 
    Context (eta:nat).

    Definition generate_randomness_single i rndC := 
      rnds' <-$ rndC;
        ri <-$ {0,1}^eta;
        ret (PositiveMap.add i (cast_rand eta ri) rnds').

    Definition generate_randomness idxs
      : Comp (PositiveMap.t (interp_type rand eta))
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


  Context (unreachable:forall {i}, Bvector i).
  Global Instance EqDec_interp_type : forall t eta, EqDec (interp_type t eta). Admitted. (* TODO: functional extensionality? *)
  Fixpoint interp_term_fixed {t} (e:term t) (eta : nat)
           (adv: interp_type list_message eta -> interp_type message eta)
           (rands: PositiveMap.t (interp_type rand eta))
    : interp_type t eta :=
    match e with
    | Term_const c => c eta
    | Term_random i => match PositiveMap.find i rands with Some r => r | _ => cast_rand eta (unreachable _) end
    | Term_adversarial ctx => adv (interp_term_fixed ctx eta adv rands)
    | Term_app f x => (interp_term_fixed f eta adv rands) (interp_term_fixed x eta adv rands)
    end.
  Definition interp_term {t} (e:term t) (eta:nat)
             (adv: interp_type list_message eta -> interp_type message eta)
    : Comp (interp_type t eta)
    := rands <-$ generate_randomness eta (randomness_indices e); ret (interp_term_fixed e eta adv rands).

  Global Instance Proper_interp_term_fixed {t} (e:term t) eta adv :
    Proper (PositiveMap.Equal ==> Logic.eq) (interp_term_fixed e eta adv).
  Proof.
    cbv [Proper respectful]; induction e; intros; simpl; try reflexivity.
    { cbv [PositiveMap.Equal] in *. rewrite H. reflexivity. }
    { erewrite IHe; eauto. }
    { erewrite IHe1, IHe2; eauto. }
  Qed.

  Section Security.
    (* the adversary is split into three parts for no particular reason. It first decides how much randomness it will need, then interacts with the protocol (repeated calls to [adverary] with all messages up to now as input), and then tries to claim victory ([distinguisher]). There is no explicit sharing of state between these procedures, but all of them get the same random inputs in the security game. The handling of state is a major difference between FCF [OracleComp] and this framework *)
(* TODO: Change adl to be function that goes from eta -> keys of randomness we need, change this definitoin approrpiately *)
    Definition universal_security_game
               (evil_rand_indices: forall eta:nat, PositiveSet.t)
               (adversary:forall (eta:nat) (rands: PositiveMap.t (interp_type rand eta)), interp_type list_message eta -> interp_type message eta)
               (distinguisher: forall {t} (eta:nat) (rands: PositiveMap.t (interp_type rand eta)), interp_type t eta -> Datatypes.bool)
               (eta:nat) {t:type} (e:term t) : Comp Datatypes.bool :=
        evil_rands <-$ generate_randomness eta (evil_rand_indices eta);
        out <-$ interp_term e eta (adversary eta (evil_rands));
        ret (distinguisher eta evil_rands out).

    Definition indist {t:type} (a b:term t) : Prop :=  forall adl adv dst,
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

  Definition whp (e:term sbool) := indist e (const strue).

  Local Existing Instance eq_subrelation | 5.
  (* Local Instance subrelation_eq_Comp_eq {A} : subrelation eq (Comp_eq(A:=A)) | 2 := eq_subrelation _. *)

  Section Equality.
    Definition const_eqb t : term (t -> t -> sbool) :=
      @Term_const
        (Type_arrow t (Type_arrow t (Type_base sbool)))
        (fun eta x1 x2 => if eqb x1 x2 then strue eta else sfalse eta).
    Definition eqwhp {t:type} (e1 e2:term t) : Prop := whp (const_eqb t @ e1 @ e2)%term.

    Global Instance Reflexive_eqwhp {t} : Reflexive (@eqwhp t).
    Proof.
      cbv [Reflexive indist universal_security_game eqwhp whp interp_term]; intros.
      cbn [interp_term_fixed const_eqb].
      (* TODO:debug setoid_rewrite here:
      Existing Instance eq_Reflexive | 0.
      Existing Instance eq_equivalence | 0.
      Local Opaque negligible.
      Local Opaque eqRat.
      Set Typeclasses Debug.
      pose proof Proper_negligible.
      Fail timeout 1 setoid_rewrite (eqb_refl _ (interp_term_fixed _ _ (adv _ _) _)). *)
      eapply Proper_negligible.
      {
        intro eta.
        setoid_rewrite (eqb_refl _ (interp_term_fixed _ _ (adv _ _) _)).
        setoid_rewrite Bind_unused.
        eapply reflexivity.
      }
      setoid_rewrite ratDistance_same.
      eapply negligible_0.
    Qed.

  End Equality.

  Section LateInterp.
    Fixpoint interp_term_late
             {t} (e:term t) (eta : nat)
             (adv: interp_type list_message eta -> interp_type message eta)
             (fixed_rand: PositiveMap.t (interp_type rand eta))
    : Comp (interp_type t eta) :=
      match e with
      | Term_const c => ret (c eta)
      | Term_random i =>
        match PositiveMap.find i fixed_rand with
        | Some r => ret r
        | _ => r <-$ {0,1}^eta; ret (cast_rand eta r)
        end
      | Term_adversarial ctx =>
        ctx <-$ interp_term_late ctx eta adv fixed_rand; ret (adv ctx)
      | Term_app f x =>
        common_rand <-$ generate_randomness eta (PositiveSet.inter (randomness_indices x) (randomness_indices f));
          let rands := PositiveMapProperties.update common_rand fixed_rand in
          x <-$ interp_term_late x eta adv rands;
            f <-$ interp_term_late f eta adv rands;
            ret (f x)
      end.

    Lemma interp_term_late_correct' {t} (e:term t) eta adv :
      forall univ (H:PositiveSet.Subset (randomness_indices e) univ) fixed,
        Comp_eq (interp_term_late e eta adv fixed)
                (rands <-$ generate_randomness eta univ;
                   ret (interp_term_fixed e eta adv
                                          (PositiveMapProperties.update rands fixed))).
    Proof.
      induction e; intros;
        simpl interp_term_late; simpl interp_term_fixed.
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

          remember (fun m => ret (match m with | Some r => r | None => cast_rand eta (unreachable eta) end)) as G.
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
    
    Lemma interp_term_late_correct {t} (e:term t) eta adv:
      Comp_eq
        (interp_term_late e eta adv (PositiveMap.empty _))
        (interp_term e eta adv).
    Proof.
      rewrite interp_term_late_correct'; cbv [interp_term]; reflexivity.
    Qed.
  End LateInterp.

  Lemma indist_rand (x y:positive) : indist (rnd x) (rnd y).
  Proof.
    cbv [indist universal_security_game]; intros.
    setoid_rewrite <-interp_term_late_correct.
    cbv [interp_term_late].
    setoid_rewrite PositiveMap.gempty.
    setoid_rewrite ratDistance_same.
    trivial using negligible_0.
  Qed.

  Fixpoint randomness_indices_wh {holetype t} (twh: term_wh holetype t) : PositiveSet.t :=
    match twh with
    | Term_wh_random _ idx => PositiveSet.singleton idx
    | Term_wh_app _ f x => PositiveSet.union (randomness_indices_wh f) (randomness_indices_wh x)
    | Term_wh_adversarial _ x => randomness_indices_wh x
    | _ => PositiveSet.empty
    end.

  (* One term is fresh in another if they don't share randomness. *)
  Definition fresh {T} {U} (x : term T) (y : term U) :=
    PositiveSet.eq (PositiveSet.inter (randomness_indices x) (randomness_indices y))
                   PositiveSet.empty.

  Lemma indist_no_shared_randomness: forall {t u} (x: term t) (y: term t) (z: term u) (ctx: term_wh t u),
      PositiveSet.Equal (PositiveSet.inter (randomness_indices_wh ctx) (randomness_indices x)) PositiveSet.empty ->
      PositiveSet.Equal (PositiveSet.inter (randomness_indices_wh ctx) (randomness_indices y)) PositiveSet.empty ->
      indist y x ->
      indist (fill ctx y) (fill ctx x).
  Proof.
    cbv [indist universal_security_game] in *;
      intros t u x y z ctx eqx eqy indistxy adl adv dst.
  Abort.

  Context {state state_list_message:base_type}.
  Context (proj_state : forall eta, interp_type (state_list_message -> state) eta).
  Context (proj_list_message : forall eta, interp_type (state_list_message -> list_message) eta).
  Context (list_message_nil : forall eta, interp_type list_message eta).
  Context (join_state_list_message : forall eta, interp_type (state -> list_message -> state_list_message) eta).
  Context (app_list_message : forall eta, interp_type (list_message -> list_message -> list_message) eta).
  Section Interact.
    Context
      (start:term state)
      (step:term (state -> message -> state_list_message)).
    Fixpoint interact (n:nat) : term (state_list_message) :=
      match n with
      | O => const join_state_list_message @ start @ const list_message_nil
      | S n' =>
        let s'o' := interact n' in
        let old_state := const proj_state @ s'o' in
        let old_outputs := const proj_list_message @ s'o' in
        let so := step @ old_state @ (Term_adversarial old_outputs) in
        let new_state := const proj_state @ so in
        let new_outputs := const proj_list_message @ so in
        let cumulative_outputs := const app_list_message @ old_outputs @ new_outputs in
        const join_state_list_message @ new_state @ cumulative_outputs
      end%term.
  End Interact.

End Language.
Arguments type _ : clear implicits.
