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

Section TODO.

  Global Instance Proper_Ret {A} {R} : Proper (R ==> pointwise_relation _ Comp_eq) (@Ret A).
  Proof.
    intros eq1 eq2 ? x1 x2.
    cbv [Comp_eq image_relation pointwise_relation evalDist].
    destruct (eq1 x1 x2), (eq2 x1 x2); (congruence||reflexivity).
  Qed. 
    (* Goal Comp_eq (a <-$ ret 0; b <-$ ret 1; ret ((a*a) + (b-b)))%nat (ret 0)%nat. *)
    (* Goal Comp_eq (a <-$ ret 0; b <-$ ret 1; ret ((a*a)))%nat (ret 0)%nat. *)
    (* Goal Comp_eq (a <-$ ret 0; ret ((a*a)))%nat (ret 0)%nat. *)
    (* Proof. *)
    (*   assert (eq_dec nat) as eq_dec_nat by admit. *)
    (*   pose proof @Proper_Ret. *)
    (*   pose proof @Proper_Bind. *)
    (*   pose proof @Equivalence_Comp_eq. *)
    (*   pose proof (fun a => Comp_eq_left_ident nat nat _ _ (a*a) (@Ret nat (@EqDec_dec nat nat_EqDec)))%nat. *)
    (*   setoid_rewrite <- H2. *)

      (* SearchAbout Bind. *)
      (* Set Typeclasses Debug. *)
      (* setoid_rewrite <- H. *)
      (* simpl in H. *)
      (*
      etransitivity.
      eapply Proper_Bind.
      reflexivity.
      intros ???. subst.
      match goal with
        |- ?R ?LHS (?e ?v) =>
        let LHS'v := (eval pattern v in LHS) in
        match LHS'v with ?f ?v =>
                         instantiate (1:=f)
        end
      end; reflexivity.
      *)

  Lemma eq_impl_negligible : forall A (x y : nat -> Comp A), pointwise_relation _ Comp_eq x y -> forall t, negligible (fun eta : nat => | evalDist (x eta) t - evalDist (y eta) t|).
  Admitted.

  (* TODO: This should be a two-way lemma *)
  Lemma comp_spec_impl_Comp_eq A (H: EqDec A) (x y: Comp A) :
    comp_spec eq x y
    -> Comp_eq x y.
  Proof.
    intro.
    apply Comp_eq_evalDist.
    intro.
    fcf_to_prhl.
    cbv [comp_spec] in *.
    destruct H0.
    exists x0.
    destruct H0.
    destruct H1.
    split; try split; try assumption.
    intros.
    specialize (H2 p H3).
    rewrite H2.
    reflexivity.
  Qed.


  Lemma Bind_unused A B (a:Comp A) (b:Comp B) :
    Comp_eq (_ <-$ a; b) b.
  Admitted. (* TODO: does FCF have something like this? *)

  Lemma PosMap_add_commutes : forall (x y : positive) (elt : Type) (m : PositiveMap.t elt) (A B : elt),
      PositiveMap.add x A (PositiveMap.add y B m) = PositiveMap.add y B (PositiveMap.add x A m).
  Admitted.

End TODO.

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

  Context (len_rand : forall eta:nat, nat)
          (cast_rand : forall eta, Bvector (len_rand eta) -> interp_type rand eta).

  Definition generate_randomness_single eta i rndC := 
    rnds' <-$ rndC;
      ri <-$ {0,1}^(len_rand eta);
      ret (PositiveMap.add i (cast_rand eta ri) rnds').
  Definition generate_randomness (eta:nat) idxs
    : Comp (PositiveMap.t (interp_type rand eta))
    := PositiveSet.fold (generate_randomness_single eta)
                        idxs
                        (ret (PositiveMap.empty _)).

  Lemma empty_randomness : forall (eta : nat),
      Comp_eq (generate_randomness eta PositiveSet.empty)
      (ret (PositiveMap.empty _)).
  Proof.
    intros.
    cbv [generate_randomness].
    rewrite PositiveSetProperties.fold_empty.
    reflexivity.
  Qed.

  Lemma singleton_randomness : forall (eta : nat) (n : positive),
      Comp_eq (generate_randomness eta (PositiveSet.singleton n))
              (ri <-$ {0,1}^(len_rand eta);
                 ret (PositiveMap.add n (cast_rand eta ri) (PositiveMap.empty _))).
  Proof.
    intros.
    cbv [generate_randomness generate_randomness_single PositiveSet.singleton].
    rewrite PositiveSetProperties.fold_add.
    {
      rewrite PositiveSetProperties.fold_empty.
      rewrite Bind_Ret_l.
      { reflexivity. }
    (* } *)
    (* { admit. } *)
    (* { *)
    (*   cbv [Proper respectful pointwise_relation RelCompFun]. *)
    (*   intros. *)
    (*   rewrite H. *)
    (*   assert (Comp_eq x0 y0). *)
    (*   apply Comp_eq_evalDist. *)
    (*   intros. *)
    (*   setoid_rewrite H0. *)
    (*   reflexivity. *)
    (* } *)
    (* { *)
    (*   cbv [transpose pointwise_relation RelCompFun]. *)
    (*   intros. (* *)
    (*   (* TODO: Make these all tactics you can perform on Comp_eqs + ask andres about this *) *)
    (*   apply Comp_eq_evalDist. *)
    (*   intros. *)
    (*   fcf_inline_first. *)
    (*   fcf_skip. *)
    (*   fcf_inline_first. *)
    (*   fcf_at fcf_swap fcf_left 1%nat. *)
    (*   fcf_at fcf_swap fcf_right 1%nat. *)
    (*   fcf_at fcf_ret fcf_left 2%nat. *)
    (*   fcf_at fcf_ret fcf_right 2%nat. *)
    (*   apply Comp_eq_evalDist. *)
    (*   destruct (Pos.eq_dec x y). *)
    (*   { rewrite e; reflexivity. } *)
    (*   { admit. } *)

    (*   (* { *) *)
    (*   (*   remember (PosMap_add_commutes x y n0 (interp_type rand eta) x0) as comm. *) *)
    (*   (*   assert (evalDist *) *)
    (*   (*     (a0 <-$ { 0 , 1 }^ len_rand eta; *) *)
    (*   (*        a1 <-$ { 0 , 1 }^ len_rand eta; *) *)
    (*   (*        ret PositiveMap.add y (cast_rand eta a0) (PositiveMap.add x (cast_rand eta a1) x0)) a == *) *)
    (*   (*           evalDist *) *)
    (*   (*     (a0 <-$ { 0 , 1 }^ len_rand eta; *) *)
    (*   (*        a1 <-$ { 0 , 1 }^ len_rand eta; *) *)
    (*   (*        ret PositiveMap.add y (cast_rand eta a1) (PositiveMap.add x (cast_rand eta a0) x0)) a). *) *)
    (*   (*   { *) *)
    (*   (*     fcf_at fcf_swap fcf_right 0%nat. *) *)
    (*   (*     reflexivity. *) *)
    (*   (*   } *) *)
    (*     (* TODO: Do this rewrite under a bind. *) *)
    (*   } *)
    (* { cbv [not]; apply (PositiveSetProperties.Dec.F.empty_iff n). } *) *)
  Admitted.

  Context (unreachable:forall {i}, Bvector (len_rand i)).
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
    Admitted.

    Global Instance Transitive_indist {t} : Transitive (@indist t).
    Admitted.

    Global Instance Reflexive_indist {t} : Reflexive (@indist t).
    Proof.
      cbv [Reflexive indist]; setoid_rewrite ratDistance_same; eauto using negligible_0.
    Qed.

    Global Instance Symmetric_indist {t} : Symmetric (@indist t).
    Proof.
      cbv [Symmetric indist]; intros; setoid_rewrite ratDistance_comm; eauto.
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

    Existing Instance eq_Reflexive | 0.
    Existing Instance eq_equivalence | 0.
    Global Instance Reflexive_eqwhp {t} : Reflexive (@eqwhp t).
    Proof.
      cbv [Reflexive indist universal_security_game eqwhp whp interp_term]; intros.
      cbn [interp_term_fixed const_eqb].
      Local Opaque negligible.
      Local Opaque eqRat.
      (* Set Typeclasses Debug. *)
      pose proof Proper_negligible.
      
      Fail timeout 1 setoid_rewrite (eqb_refl _ (interp_term_fixed _ _ (adv _ _) _)).
      eapply Proper_negligible. intro eta.
      timeout 1 setoid_rewrite (eqb_refl _ (interp_term_fixed _ _ (adv _ _) _)).
      timeout 1 setoid_rewrite Bind_unused.
      eapply (reflexivity _).
      eapply (@eq_impl_negligible _ _ _ (reflexivity _)).
    Qed.
  End Equality.

  (* Forall message, Generate key. *)
  (* Encrypt message under key *)
  (* Generate 2nd key, encrypt 1st key under 2nd key *)
  (* Reveal both ciphertexts to adversary *)
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
        | _ => r <-$ {0,1}^(len_rand eta); ret (cast_rand eta r)
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

    Local Ltac peel_level :=
      apply Proper_Bind; [reflexivity|]; cbv [pointwise_relation]; intros.

    Local Ltac rewrite_in_bind H t :=
      apply Proper_Bind; [rewrite H by t; reflexivity|]; cbv [pointwise_relation]; intros.

    Local Ltac resolve_left :=
          match goal with |- Comp_eq ?lhs (_ ?a) =>
                          match (eval pattern a in lhs) with
                            ?f _ => set (F :=f); transitivity (F a);
                                    [subst F; reflexivity | reflexivity]
                          end end.
    Local Ltac resolve_right := symmetry; resolve_left.

    Lemma update_subset {A} (m1 m2 : PositiveMap.t A) :
      (forall k, PositiveMap.In k m1 -> PositiveMap.In k m2) ->
      PositiveMap.Equal (PositiveMapProperties.update m1 m2) m2.
    Admitted.

    Global Instance Proper_generate_randomness eta :
      Proper (PositiveSet.Equal ==> Comp_eq) (generate_randomness eta).
    Proof.
      cbv [Proper respectful generate_randomness].
      match goal with |- context [PositiveSet.fold ?f _] =>
                      set (F:=f) end.
      intros.
      cbv [PositiveSet.Equal] in H.
      apply PositiveSetProperties.fold_equal; auto; try exact _.
      { subst F. cbv [Proper respectful]; intros.
        apply Proper_Bind; subst; (congruence || reflexivity). }
      { subst F; cbv [transpose]; intros.
        repeat setoid_rewrite <-Bind_assoc.
        repeat setoid_rewrite Bind_Ret_l.
        do 1 peel_level.
        (* if we generate two random numbers, swapping the order preserves indist *)
     Admitted.

    Lemma Proper_Bind_generate_randomness {A: Set} eta idxs :
      Proper (
          (fun f g =>
                 forall m,
                   (forall i, PositiveMap.In i m <-> PositiveSet.In i idxs) ->
                   Comp_eq (f m) (g m))
                ==> Comp_eq)
             (Bind (A:=A) (generate_randomness eta idxs)).
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
               | |- Comp_eq (Bind ?x _) (Bind ?x _) => peel_level
               | H: _ |- _ => rewrite H; tauto
               | _ => tauto
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

    Lemma bind_twice {A B:Set} (x: Comp B) (f : B -> B -> Comp A) :
      Comp_eq (Bind x (fun y => Bind x (f y)))
              (Bind x (fun y => f y y)).
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


    Global Instance Proper_generate_randomness_single eta :
      Proper (eq ==> Comp_eq ==> Comp_eq) (generate_randomness_single eta).
    Proof.
      cbv [Proper respectful generate_randomness_single]; intros; subst.
      rewrite H0. reflexivity.
    Qed.

    Lemma generate_randomness_single_transpose eta :
      transpose Comp_eq (generate_randomness_single eta).
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

    Lemma update_overwrite {A} x (m1 m2 : PositiveMap.t A) :
      PositiveMap.In x m2 ->
      PositiveMap.Equal 
        (PositiveMapProperties.update m1 m2)
        (PositiveMapProperties.update (PositiveMap.remove x m1) m2).
    Admitted.
      
    Lemma add_generate_randomness {A} eta (f:_->Comp A) x s s' :
      PositiveSetProperties.Add x s s' ->
      ~PositiveSet.In x s ->
      Comp_eq (a <-$ generate_randomness eta s'; f a)
              (a <-$ generate_randomness_single eta x
                 (generate_randomness eta s); f a).
    Proof.
      cbv [generate_randomness]; intros.
      rewrite PositiveSetProperties.fold_2 by
          (try eassumption; try (exact _);
           auto using generate_randomness_single_transpose).
      reflexivity.
    Qed.

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

    Local Ltac move_rand_to_top := 
      cbv [generate_randomness_single];
      repeat setoid_rewrite <-Bind_assoc;
      repeat setoid_rewrite Bind_Ret_l;
      rewrite Bind_comm with (c2 := {0,1}^len_rand _).

    Lemma generate_single eta i idxs:
      forall {A} (f:_->Comp A),
        PositiveSet.In i idxs ->
        Comp_eq
          (t <-$ generate_randomness eta idxs;
             f (PositiveMap.find i t))
          (r <-$ { 0 , 1 }^ len_rand eta; f (Some (cast_rand eta r))).
    Proof.
      intros.
      apply PositiveSetProperties.Add_remove in H.
      rewrite add_generate_randomness
        by eauto using PositiveSetProperties.Dec.F.remove_1.
      move_rand_to_top.
      etransitivity. {
        do 2 peel_level.
        rewrite PositiveMapProperties.F.add_eq_o by reflexivity.
        eapply reflexivity. }
      setoid_rewrite Bind_unused; reflexivity.
    Qed. 

    Lemma generate_twice eta idxs1 :
      forall idxs2 {A} (f:_->Comp A),
        Proper (PositiveMap.Equal ==> Comp_eq) f ->
      Comp_eq
        (a <-$ generate_randomness eta idxs1;
           b <-$ generate_randomness eta idxs2;
           f (PositiveMapProperties.update b a))
        (a <-$ generate_randomness eta (PositiveSet.union idxs1 idxs2);
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
        rewrite Bind_unused, PositiveSetProperties.empty_union_1 by assumption.
        reflexivity. }
      { intros until 1. intro new_elt; intros.
        
        (* move the new elt to the top on the LHS *)
        rewrite add_generate_randomness with (s'0:=s') by eassumption.
        move_rand_to_top.

        (* and on the RHS *)
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
        move_rand_to_top.

        (* apply inductive hypothesis *)
        setoid_rewrite update_add.
        peel_level.
        match goal with H: _ |- context [PositiveMap.add ?i ?x] =>
                        rewrite H with (f:=fun m => f (PositiveMap.add i x m)) end.
        rewrite <-union_remove; try reflexivity.
        cbv [Proper respectful]; intros;
          match goal with H: PositiveMap.Equal _ _ |- _ => rewrite H end;
        reflexivity. }
    Qed.

    Global Instance Proper_interp_term_fixed {t} (e:term t) eta adv :
      Proper (PositiveMap.Equal ==> Logic.eq) (interp_term_fixed e eta adv).
    Proof.
      cbv [Proper respectful]; induction e; intros; simpl; try reflexivity.
      { cbv [PositiveMap.Equal] in *. rewrite H. reflexivity. }
      { erewrite IHe; eauto. }
      { erewrite IHe1, IHe2; eauto. }
    Qed.

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
        repeat setoid_rewrite bind_twice.

        repeat setoid_rewrite update_assoc.

        match goal with
          |- Comp_eq (Bind ?y (fun a => Bind ?x _)) (Bind ?x ?g) =>
          rewrite generate_twice with (f:=g) end.
        { f_equiv; apply Proper_generate_randomness.
          auto using PositiveSetProperties.union_subset_equal, subset_inter. }
        { cbv [Proper respectful]; intros;
            match goal with H: PositiveMap.Equal _ _ |- _ => rewrite H end;
            reflexivity. } }
    Qed.
    
    Lemma interp_term_late_correct_full {t} (e:term t) eta adv fixed:
      (PositiveSet.Subset fixed (randomness_indices e)) ->
      Comp_eq
        (rands <-$ generate_randomness eta fixed;
           interp_term_late e eta adv rands)
        (interp_term e eta adv).
    Proof.
    Admitted.

    Lemma interp_term_late_correct {t} (e:term t) eta adv:
      Comp_eq
        (interp_term_late e eta adv (PositiveMap.empty _))
        (interp_term e eta adv).
    Proof.
      rewrite interp_term_late_correct'; cbv [interp_term]; reflexivity.
    Qed.
  End LateInterp.

Section FillInterp.
  Fixpoint interp_term_fill_fixed {holetype t eta}
           (twh : term_wh holetype t)
           (filler_const : forall eta, interp_type holetype eta)
           (adv: interp_type list_message eta -> interp_type message eta)
           (rands: PositiveMap.t (interp_type rand eta))
    : interp_type t eta :=
    match twh with
    | Term_wh_const _ c =>  c eta
    | Term_wh_random _ i => match PositiveMap.find i rands with Some r => r | _ => cast_rand eta (unreachable _) end
    | Term_wh_adversarial _ ctx => adv (interp_term_fill_fixed ctx filler_const adv rands)
    | Term_wh_app _ f x => (interp_term_fill_fixed f filler_const adv rands) (interp_term_fill_fixed x filler_const adv rands)
    | Term_wh_hole _ => interp_term_fixed (Term_const filler_const) eta adv rands
    end.

  Fixpoint randomness_indices_wh {holetype t} (twh: term_wh holetype t) : PositiveSet.t :=
    match twh with
    | Term_wh_random _ idx => PositiveSet.singleton idx
    | Term_wh_app _ f x => PositiveSet.union (randomness_indices_wh f) (randomness_indices_wh x)
    | Term_wh_adversarial _ x => randomness_indices_wh x
    | _ => PositiveSet.empty
    end.

  Definition interp_term_fill {holetype t eta}
           (twh : term_wh holetype t) (filler : forall eta, interp_type holetype eta)
           (adv: interp_type list_message eta -> interp_type message eta)
    : Comp (interp_type t eta)
    := rands <-$ generate_randomness eta (randomness_indices_wh twh);
         ret (interp_term_fill_fixed twh filler adv rands).

  Global Instance Proper_interp_term_late t x eta adv:
    Proper (PositiveMap.Equal ==> Comp_eq) (@interp_term_late t x eta adv).
  Admitted.
  
  Lemma union_empty s1 s2 s3 :
    PositiveSet.Equal (PositiveSet.inter (PositiveSet.union s1 s2) s3) PositiveSet.empty ->
    PositiveSet.Equal (PositiveSet.inter s1 s3) PositiveSet.empty /\
    PositiveSet.Equal (PositiveSet.inter s2 s3) PositiveSet.empty.
  Admitted.

  Lemma interp_term_fill_correct {holetype t} (twh : term_wh holetype t) 
        (x: term holetype) (filler_const : forall eta, interp_type holetype eta)
        eta adv :
    (Comp_eq (interp_term (Term_const filler_const) eta adv)
             (interp_term x eta adv)) ->
    PositiveSet.Equal (PositiveSet.inter (randomness_indices_wh twh) (randomness_indices x)) PositiveSet.empty ->
    Comp_eq (interp_term_fill twh filler_const adv)
            (interp_term (fill twh x) eta adv).
  Proof.
    intro.
    induction twh; intros.
    { reflexivity. }
    { reflexivity. }
    {
      repeat match goal with
             | _ => progress simpl randomness_indices_wh in *
             | _ => progress simpl randomness_indices in *
             | _ => progress cbv [interp_term_fill] in *
             | _ => progress simpl interp_term_late in *
             | _ => progress simpl interp_term_fill_fixed in *
             | _ => rewrite <-IHtwh by assumption
             | _ => rewrite <-interp_term_late_correct
             | _ => rewrite <-interp_term_late_correct in IHtwh
             | _ => rewrite <-Bind_assoc
             | _ => rewrite Bind_Ret_l
             end.
      apply Proper_Bind; cbv [pointwise_relation]; intros;
        rewrite ?Bind_Ret_l; try reflexivity. }
    {
      rewrite <-interp_term_late_correct_full in IHtwh1.
      rewrite <-interp_term_late_correct_full in IHtwh2.
      repeat match goal with
             | _ => progress simpl randomness_indices_wh in *
             | _ => progress simpl randomness_indices in *
             | _ => progress cbv [interp_term_fill] in *
             | _ => rewrite <-interp_term_late_correct in * by reflexivity
             | _ => progress simpl interp_term_late in *
             | _ => progress simpl fill in *
             | _ => progress simpl interp_term_fill_fixed in *
             | _ => rewrite <-IHtwh1 by assumption
             | _ => rewrite <-IHtwh2 by assumption
             | _ => rewrite <-Bind_assoc
             | _ => rewrite Bind_Ret_l
             end.

      Local Notation "x & y" := (PositiveSet.inter x y) (at level 70, only printing).
      Local Notation "x | y" := (PositiveSet.union x y) (at level 70, only printing).
      Local Notation "#idx x" := (randomness_indices x) (at level 70, only printing).
      Local Notation "&idx x" := (randomness_indices_wh x) (at level 70, only printing).

      etransitivity.
      Focus 2. {
        apply Proper_Bind; [reflexivity|].
        cbv [pointwise_relation]; intros.
        apply Proper_Bind.
        rewrite update_empty_r by apply PositiveMap.empty_1; reflexivity.
        cbv [pointwise_relation]; intros.
        apply Proper_Bind.
        rewrite update_empty_r by apply PositiveMap.empty_1; reflexivity.
        cbv [pointwise_relation]; intros.
        change (ret a1 a0) with ((fun y => ret y a0) a1); reflexivity. }
      Unfocus.

      match goal with
        |- Comp_eq (r <-$ generate_randomness ?e (PositiveSet.union ?a ?b);
                    ret (?f r (?g r))) _ =>
        transitivity (x <-$ (r1 <-$ generate_randomness e b;
                             ret g r1);
                      y <-$ (r2 <-$ generate_randomness e a;
                             ret f r2);
                      ret y x) end.
      { 
        repeat setoid_rewrite <-Bind_assoc.
        repeat setoid_rewrite Bind_Ret_l.
        rewrite <-generate_twice.
        rewrite Bind_comm.
        apply Proper_Bind_generate_randomness; intros.
        apply Proper_Bind_generate_randomness; intros.
        (* TODO *)
        admit. admit.
      }
      {
        match goal with H:_ |- _ => apply union_empty in H; destruct H end.
        setoid_rewrite IHtwh1; [|assumption].
        setoid_rewrite IHtwh2; [|assumption].
        repeat setoid_rewrite <-Bind_assoc.
        
        match goal with
          |- Comp_eq _ (x0 <-$ ?a; x1 <-$ ?f x0; x2 <-$ ?g x0; ret x2 x1) =>
          setoid_rewrite
            <-(bind_twice a (fun y0 y1 => x1 <-$ f y0; x2 <-$ g y1; ret x2 x1));
            apply Proper_Bind; [reflexivity|]; cbv [pointwise_relation]; intros;
              setoid_rewrite Bind_comm with (c1:=a)
        end.
        reflexivity. }
      { auto using PositiveSetProperties.inter_subset_1. }
      { auto using PositiveSetProperties.inter_subset_2. }
  Admitted.

End FillInterp.
  (* One term is fresh in another if they don't share randomness. *)
  Definition fresh {T} {U} (x : term T) (y : term U) :=
    PositiveSet.eq (PositiveSet.inter (randomness_indices x) (randomness_indices y))
                  PositiveSet.empty.

  Lemma empty_inter: forall s : PositiveSet.t, PositiveSet.eq (PositiveSet.inter s PositiveSet.empty) PositiveSet.empty.
    intros.
    apply PositiveSetProperties.empty_is_empty_1.
    apply PositiveSetProperties.empty_inter_2.
    apply PositiveSet.empty_spec.
  Qed.

  Ltac indistify :=
    intros;
    cbv [indist universal_security_game]; intros;
    apply eq_impl_negligible; cbv [pointwise_relation]; intros eta;
    eapply Proper_Bind;
    try reflexivity;
    cbv [respectful]; intros;
    subst.


  Context (pair_eta : forall (eta : nat), interp_type (message -> message -> list_message) eta).

  Fixpoint replace_individual_randomness {t} (x: term t) (idx p : positive) : term t :=
    match x with
    | Term_const c => Term_const c
    | Term_random n => if PositiveSet.E.eqb idx n then Term_random p else Term_random n
    | Term_adversarial l => Term_adversarial l
    | Term_app f x => Term_app (replace_individual_randomness f idx p)
                              (replace_individual_randomness x idx p)
    end.

  Fixpoint replace_randomness {t} (x: term t) (from : list positive) (to : list positive) : term t :=
    match from with
    | nil => x
    | hd :: tl => match to with
                 | nil => x
                 | hd' :: tl' => replace_randomness
                                  (replace_individual_randomness x hd hd') tl tl'
                 end
    end.

  (* TODO: Provetp for syntactic randomness *)

  (* TODO: Make this a bijective map. *)
  (* 2016 paper encryption formalization *)
  (*look into substitution into ctx inside the encryption lemma *)
  (* E_k{x} ~ r *)
  Definition no_randomness_leaked {t u} (x: term t) (ctx : term (Type_arrow t u)) : Prop :=
    forall new_idxs: list positive,
      indist (ctx @ (replace_randomness x
                                      (PositiveSet.elements (randomness_indices x))
                                      new_idxs))
             (ctx @ x).

  Lemma eqdec_type : forall (t u : type), {t = u} + {t <> u}.
  Admitted.

  Definition shift_up_set_indices (m : PositiveSet.t) (shift : positive) : PositiveSet.t :=
    PositiveSet.fold
      (fun (p : positive) (t : PositiveSet.t) => PositiveSet.add (p + shift) t) m PositiveSet.empty.

  Definition shift_down_map_indices {T : Type} (m : PositiveMap.t T) (shift : positive) : PositiveMap.t T :=
    PositiveMap.fold
      (fun (p : positive) (t : T) (m : PositiveMap.t T) => PositiveMap.add (BinPosDef.Pos.sub p shift) t m)
      m (PositiveMap.empty T).

  Definition defaulted_option {T U : Type} (f : T -> U) (o : option T) (default : U) : U :=
    match o with
    | Some r => f r
    | None => default
    end.

  Fixpoint pmap_diff' {T : Type} (m : PositiveMap.t T) (sub : list positive) : PositiveMap.t T :=
    match sub with
    | nil => m
    | hd :: tl => pmap_diff' (PositiveMap.remove hd m) tl
    end.

  Definition pmap_diff {T : Type} (m : PositiveMap.t T) (sub : PositiveSet.t) : PositiveMap.t T :=
    pmap_diff' m (PositiveSet.elements sub).

  Lemma pmap_diff_disjoint : forall (T : Type) (m : PositiveMap.t T) (sub : PositiveSet.t),
      (forall x, PositiveSet.In x sub -> ~PositiveMap.In x m) ->
      PositiveMap.Equal (pmap_diff m sub) m.
  Admitted.

  Lemma generate_randomness_map : forall (s1 s2 : PositiveSet.t) (eta : nat),
    PositiveSet.Equal (PositiveSet.inter s1 s2) PositiveSet.empty ->
    Comp_eq (rands <-$ generate_randomness eta (PositiveSet.union s1 s2);
               ret pmap_diff rands s2)
            (rands <-$ generate_randomness eta s1;
               ret rands).
  Admitted.

  (* About evalDet_equiv. *)
  Lemma Comp_eq_split : forall (A B C D : Set) (H : EqDec D) (f f1 f2 : Comp A) (g1 : A -> Comp B) (g2 : A -> Comp C) (h : B -> C -> D),
      Comp_eq (x <-$ f;
               y1 <-$ g1 x;
               y2 <-$ g2 x;
               ret h y1 y2)
            (x1 <-$ f1;
               x2 <-$ f2;
               y1 <-$ g1 x1;
               y2 <-$ g2 x2;
               ret h y1 y2).

    Admitted.
  (* Lemma interp_term_fill_fixed_randomness : forall (t u : type) (ctx : term_wh t u), *)
  (*     Comp_eq (rands <-$ generate_randomness eta (PositiveSet.union s1 (randomness_indices_wh ctx))); *)
  (*       ret interp_term_fill_fixed ctx x1  *)

  Check interp_term_fill_fixed.
  (*         (filler_const : forall eta, interp_type holetype eta) *)
   (* Rewrite as Xa <-$ A, Xb <-$ B, concatenate anytime x is passed in *)
  (* 1. How to structure this proof? *)
  (* 2. How to, in general, say something about generate_randomness? *)
  Lemma Comp_eq_split_map : forall (t u : type) (ctx : term_wh t u) (x : forall eta, interp_type t eta) (eta : nat) (s1 : PositiveSet.t)
                              (adv : forall eta : nat, PositiveMap.t (interp_type rand eta) -> interp_type list_message eta -> interp_type message eta)
                              (dst : forall (t : type) (eta : nat), PositiveMap.t (interp_type rand eta) -> interp_type t eta -> bool)
                              (H : PositiveSet.Equal (PositiveSet.inter s1 (randomness_indices_wh ctx)) PositiveSet.empty)
    T (C:_->Comp T),
      (* TODO : Disjointness of s1, randomness_indices, ctx randomness and x1 randomness *)

      Comp_eq (rands <-$ generate_randomness eta (PositiveSet.union s1 (randomness_indices_wh ctx));
                 C (dst u eta (pmap_diff rands (randomness_indices_wh ctx)) (interp_term_fill_fixed ctx x (adv eta (pmap_diff rands (randomness_indices_wh ctx))) rands)))
              (evil_rands <-$ generate_randomness eta s1;
                 rands <-$ generate_randomness eta (randomness_indices_wh ctx);
                 C (dst u eta (pmap_diff evil_rands (randomness_indices_wh ctx)) (interp_term_fill_fixed ctx x (adv eta (pmap_diff evil_rands (randomness_indices_wh ctx))) rands))).
    (* intros. *)
    (* pose proof (generate_randomness_map s1 (randomness_indices_wh ctx) eta). *)
    Admitted.



  Lemma Comp_eq_shift_pmap_diff (s1 s2 : PositiveSet.t) (eta : nat) {T} (C:_->Comp T):

    Comp_eq (rands <-$ generate_randomness eta (defaulted_option (shift_up_set_indices s1)
                                                                 (PositiveSet.max_elt s2) s1);
               C (pmap_diff rands s2))
            (rands <-$ generate_randomness eta (defaulted_option (shift_up_set_indices s1)
                                                                 (PositiveSet.max_elt s2) s1);
               C rands).
  Admitted.
  Lemma Comp_eq_shift_up_shift_down' (shift : positive) eta (indices : PositiveSet.t) (elements: list positive) (H : elements = PositiveSet.elements indices):
    Comp_eq (rands <-$ generate_randomness eta (shift_up_set_indices indices shift);
               ret (shift_down_map_indices rands shift))
            (rands <-$ generate_randomness eta indices;
               ret rands).
    Admitted.
    (* induction elements. *)
    (* { cbv [shift_up_set_indices shift_down_map_indices]. *)
    (*   rewrite PositiveSet.fold_spec. *)
    (*   (* rewrite <- H. *) *)


    (*   (* setoid_rewrite PositiveMap.fold_1. *) *)

    (*   (* Proper (eq ==> Comp_eq) Ret @ *) *)

    (*   transitivity  *)
    (* (rands <-$ *)
    (*  generate_randomness eta *)
    (*    (fold_left (fun (a : PositiveSet.t) (e : PositiveSet.elt) => PositiveSet.add (e + shift) a) nil *)
    (*       PositiveSet.empty); *)
    (*  ret fold_left (fun (a : PositiveMap.t (interp_type rand eta)) (p : PositiveMap.key * interp_type rand eta) => (fun (p : positive) (t : interp_type rand eta) (m : PositiveMap.t (interp_type rand eta)) => *)
    (*         PositiveMap.add (p - shift)%positive t m) (fst p) (snd p) a) (PositiveMap.elements rands) (PositiveMap.empty (interp_type rand eta))). *)
    (*   apply Proper_Bind. *)
    (*   reflexivity. *)
    (*   cbv [respectful]; intros; subst. *)
    (*   apply Comp_eq_evalDist; intros. *)
    (*   apply evalDist_ret_eq. *)
    (*   apply PositiveMap.fold_1. *)
    (*   cbv [fold_left]. *)
    (*   rewrite empty_randomness. *)
    (*   rewrite Comp_eq_left_ident. *)
    (*   rewrite PositiveMapProperties.elements_empty. *)
    (*   assert (PositiveSet.Empty indices). *)
    (*   apply PositiveSetProperties.elements_Empty. *)
    (*   symmetry; assumption. *)
    (*   assert (PositiveSet.Equal indices PositiveSet.empty). *)
    (*   apply PositiveSetProperties.empty_is_empty_1; assumption. *)
    (*   symmetry. *)
    (*   transitivity (rands <-$ generate_randomness eta PositiveSet.empty; ret rands). *)
    (*   admit. (* Ugh rewrites *) *)
    (*   rewrite empty_randomness. *)
    (*   rewrite Comp_eq_left_ident. *)
    (*   reflexivity. *)
    (*   apply randomness_map_eq_dec. *)
    (*   apply randomness_map_eq_dec. } *)
    (* { cbv [shift_up_set_indices shift_down_map_indices] in IHelements. *)
    (*   rewrite PositiveSet.fold_spec in IHelements. *)

    (*   assert (elements = PositiveSet.elements indices -> *)
    (*            Comp_eq *)
    (*              (rands <-$ *)
    (*               generate_randomness eta *)
    (*                 (fold_left *)
    (*                    (fun (a : PositiveSet.t) (e : PositiveSet.elt) => PositiveSet.add (e + shift) a) *)
    (*                    (PositiveSet.elements indices) PositiveSet.empty); *)
    (*               ret fold_left (fun (a : PositiveMap.t (interp_type rand eta)) (p : PositiveMap.key * interp_type rand eta) => (fun (p : positive) (t : interp_type rand eta) (m : PositiveMap.t (interp_type rand eta)) => *)
    (*                                                                                                                             PositiveMap.add (p - shift)%positive t m) (fst p) (snd p) a) (PositiveMap.elements rands) (PositiveMap.empty (interp_type rand eta))) *)
    (*              (rands <-$ generate_randomness eta indices; ret rands)). *)
    (*   admit. (* rewrite troubles *) *)
    (*   clear IHelements. *)
    (* { cbv [shift_up_set_indices shift_down_map_indices]. *)
    (*   rewrite PositiveSet.fold_spec. *)
    (*   assert (Comp_eq *)
    (*              (rands <-$ *)
    (*               generate_randomness eta *)
    (*                 (fold_left *)
    (*                    (fun (a : PositiveSet.t) (e : PositiveSet.elt) => PositiveSet.add (e + shift) a) *)
    (*                    (PositiveSet.elements indices) PositiveSet.empty); *)
    (*               ret fold_left (fun (a : PositiveMap.t (interp_type rand eta)) (p : PositiveMap.key * interp_type rand eta) => (fun (p : positive) (t : interp_type rand eta) (m : PositiveMap.t (interp_type rand eta)) => *)
    (*                                                                                                                             PositiveMap.add (p - shift)%positive t m) (fst p) (snd p) a) (PositiveMap.elements rands) (PositiveMap.empty (interp_type rand eta))) *)
    (*              (rands <-$ generate_randomness eta indices; ret rands)). *)
    (*   cbv [fold_left]. *)
    (*   rewrite <- H. *)
    (*   Admitted. *)

 Lemma Comp_eq_shift_up_shift_down (indices : PositiveSet.t) (shift : positive) eta {T} (C:_->Comp T):
    Comp_eq (rands <-$ generate_randomness eta (shift_up_set_indices indices shift);
               C (shift_down_map_indices rands shift))
            (rands <-$ generate_randomness eta indices;
               C rands).
  Admitted.

 Lemma inter_with_max_empty: forall s1 s2 : PositiveSet.t,
 PositiveSet.Equal
   (PositiveSet.inter
      (defaulted_option (shift_up_set_indices s1)
         (PositiveSet.max_elt s2) s1) s2)
   PositiveSet.empty.
 Admitted.
   Ltac compeqify f1 f2 :=
     lazymatch goal with
       | [ H : negligible (fun (eta : nat) => | Pr [ ?X ] - Pr [ ?Y ] | ) |- _ ] =>
         cut (forall (n : nat), (fun (eta : nat) => | Pr [ X ] - Pr [ Y ] | ) n ==
                         (fun (eta : nat) => | Pr [ f1 eta ] - Pr [ f2 eta ] | ) n); [
         let E := fresh "E" in intro E;
         let negeq := fresh "negeq" in

         pose proof (@negligible_eq (fun (eta : nat) => | Pr [ X ] - Pr [ Y  ] | )
                                    (fun (eta : nat) => | Pr [ f1 eta ] - Pr [ f2 eta ] | ) H) as negeq;
         specialize (@negeq E) | cbv beta; intro eta]
                                    (* H H') *)
       end.

  Global Instance Reflexive_negligible_ratDistance :
    Reflexive (fun f g => negligible (fun eta => | f eta - g eta |)).
  Proof.
    intros ?; setoid_rewrite ratDistance_same; eapply negligible_0.
  Qed.

  Global Instance Symmetric_negligible_ratDistance :
    Symmetric (fun f g => negligible (fun eta => | f eta - g eta |)).
  Proof.
    intros ???; setoid_rewrite ratDistance_comm; assumption.
  Qed.

  Global Instance Transitive_negligible_ratDistance :
    Transitive (fun f g => negligible (fun eta => | f eta - g eta |)).
  Proof.
    intros ?????; setoid_rewrite ratTriangleInequality; eauto using negligible_plus.
  Qed.

  Lemma Transitive2_negligible_ratDistance {f1 g1 f2 g2} :
    negligible (fun eta => | f1 eta - g1 eta |) -> 
    negligible (fun eta => | f1 eta - f2 eta |) -> 
    negligible (fun eta => | g1 eta - g2 eta |) -> 
    negligible (fun eta => | f2 eta - g2 eta |).
  Proof.
    intros f1g1 f1f2 g1g2.
    eapply Transitive_negligible_ratDistance.
    eapply Transitive_negligible_ratDistance.
    2:exact f1g1.
    eapply Symmetric_negligible_ratDistance; assumption.
    assumption.
  Qed.

  (* Pattern example *)
  (* Goal forall (a:nat), False. *)
  (*   intros. *)
  (*   let x := eval pattern a in (a + a)%nat in *)
  (*       pose x. *)


  Require Import Coq.Logic.Eqdep.
  Local Opaque interp_term.
  (* TODO: Use this lemma somewhere, fill in lemmas it depends on *)
  (* Will need to pull out fill manually, *)
  (* or write an ltac to do it for you (potentially using eval pattern) *)
  (* Master TODO: *)
    (* - Lemma admits *)
    (* - Toy use case of this lemma *)
    (* - Rewrite OTP proof using setoid_rewrite *)
    (* - otcpa one day *)
  Lemma indist_no_shared_randomness: forall {t u} (x: term t) (y: term t) (z: term u) (ctx: term_wh t u),
      PositiveSet.Equal (PositiveSet.inter (randomness_indices_wh ctx) (randomness_indices x)) PositiveSet.empty ->
      PositiveSet.Equal (PositiveSet.inter (randomness_indices_wh ctx) (randomness_indices y)) PositiveSet.empty ->
      indist y x ->
      indist (fill ctx y) (fill ctx x).
  Proof.
    cbv [indist universal_security_game] in *;
      intros t u x y z ctx eqx eqy indistxy adl adv dst.

    (*
    let dst' := constr:(
                  fun t t' u
                      (evil_rand_indices : nat -> PositiveSet.t)
                      (dst : forall (t: type) (eta : nat), PositiveMap.t (interp_type rand eta) -> interp_type t eta -> bool)
                      (eta : nat)
                      (adv: interp_type list_message eta -> interp_type message eta)
                      (rands : PositiveMap.t (interp_type rand eta))
                      (evil_rands : PositiveMap.t (interp_type rand eta))
                      (ctx : term_wh t u) =>
                    match eqdec_type t t' with
                    | left H =>
                      eq_rect
                        t
                        (fun t0 : type => interp_type t0 eta -> bool)
                        (fun x : interp_type t eta => dst u eta evil_rands (interp_term_fill_fixed ctx x adv rands))
                        t' H
                    | right _ => fun _ : forall eta, interp_type t' eta => false
                    end) in
    let adl' := constr:(
                  fun (eta : nat) =>
                    PositiveSet.union
                      (defaulted_option
                         (shift_up_set_indices (adl eta))
                         (PositiveSet.max_elt (randomness_indices_wh ctx))
                         (adl eta))
                      (randomness_indices_wh ctx)) in
    let adv' := constr:(
                  fun (eta : nat) (m : PositiveMap.t (interp_type rand eta)) =>
                    adv eta (defaulted_option
                               (shift_down_map_indices (pmap_diff m (randomness_indices_wh ctx)))
                               (PositiveSet.max_elt (randomness_indices_wh ctx))
                               (pmap_diff m (randomness_indices_wh ctx)))) in
    eapply (Transitive2_negligible_ratDistance (indistxy adl' adv' (fun (t : type) (eta : nat) (evil_rands: PositiveMap.t (interp_type rand eta)) (filler : interp_type t eta) => (dst' _ _ _) adl' dst eta (adv' eta evil_rands) evil_rands (defaulted_option (shift_down_map_indices (pmap_diff evil_rands (randomness_indices_wh ctx))) (PositiveSet.max_elt (randomness_indices_wh ctx)) (pmap_diff evil_rands (randomness_indices_wh ctx))) ctx filler))); clear indistxy;

    eapply eq_impl_negligible; intro eta;

    (destruct (eqdec_type t t); [|contradiction]; cbv [eq_rect]; rewrite (UIP_refl type t e));
        
    setoid_rewrite (Comp_eq_split_map t u ctx _ _ _
        (fun (eta : nat) (p : PositiveMap.t (interp_type rand eta)) => adv eta (defaulted_option (shift_down_map_indices p) _ p))
        (fun (t : type) (eta : nat) (p : PositiveMap.t (interp_type rand eta)) => dst t eta (defaulted_option (shift_down_map_indices p) _ p)) (inter_with_max_empty (adl _) (randomness_indices_wh ctx)));


    (etransitivity; [| (* TODO: setoid_rewrite <-interp_term_fill_correct *)
      (eapply Proper_Bind; [reflexivity|intro]);
      (setoid_rewrite <-interp_term_fill_correct; [|assumption]);
      eapply (reflexivity _)]);

    (* Context is like pattern, but context allows wildcards inside (?s) *)
    (* context G [ ], G is the thing around the matched thing, G [ ] to substitute back in *)
    (* eval cbv beta if on variable, cbv beta on goals or hypotheses *)
    repeat match goal with
             |- context [ r <-$ ?R ; @?C r ] => (* shift_pmap *)
             let T := match type of R with Comp ?T => T end in
             (* You can't do a lambda in ltac land *)
             (* Constr gives you an ltac variable with Galina term value *)
             (* Ltac uses ltac to generate a Galina term *)
             let Ct := constr:(
                         (fun (r:T) =>
                            ltac:(
                              let Cr := (eval cbv beta in (C r)) in
                              let Cp := (eval pattern (pmap_diff r (randomness_indices_wh ctx)) in Cr) in
                              let C' := match Cp with ?C _ => C end in
                              let Ct := (eval cbv beta in (C' r)) in
                              exact Ct
                       ))) in
             setoid_rewrite (@Comp_eq_shift_pmap_diff (adl _) (randomness_indices_wh ctx) _ _ Ct)
           | _ => setoid_rewrite <-Bind_assoc
           | _ => setoid_rewrite Bind_Ret_l
           | _  => progress (cbv [defaulted_option]);
                     progress (destruct (PositiveSet.max_elt (randomness_indices_wh ctx)) as [m|])
           | _ => setoid_rewrite <-(@Comp_eq_shift_up_shift_down (adl _) m)
           | _ => reflexivity
           | _ => repeat f_equiv; setoid_rewrite Bind_comm at 1; reflexivity
           | _ => repeat f_equiv; setoid_rewrite Bind_comm at 2; reflexivity
           | _ => repeat f_equiv; setoid_rewrite Bind_comm at 3; reflexivity
           end
    .
    *)
Admitted.
  Lemma indist_rand (x y:positive) : indist (rnd x) (rnd y).
  Proof.
    cbv [indist universal_security_game]; intros.
    setoid_rewrite <-interp_term_late_correct.
    cbv [interp_term_late].
    setoid_rewrite PositiveMap.gempty.
    setoid_rewrite ratDistance_same.
    trivial using negligible_0.
  Qed.

  Section OTP.
    Definition T' := interp_type message.
    Hypothesis T'_EqDec : forall (eta : nat), EqDec (T' eta).
    Variable RndT'_symbolic : forall (eta : nat), interp_type (rand -> message) eta.
    Definition RndT' := fun (eta : nat) => x <-$ {0,1}^(len_rand eta);
                                        ret (RndT'_symbolic eta (cast_rand eta x)).
    Variable T_op' : forall (eta : nat), interp_type (message -> message -> message)%term eta.
    Hypothesis op_assoc' : forall (eta : nat), forall x y z, T_op' eta (T_op' eta x y) z = T_op' eta x (T_op' eta y z).
    Variable T_inverse' : forall (eta : nat), interp_type(message -> message)%term eta.
    Variable T_ident' : forall (eta : nat), T' eta.
    Hypothesis inverse_l_ident' : forall (eta : nat), forall x, T_op' eta (T_inverse' eta x) x = T_ident' eta.
    Hypothesis inverse_r_ident' : forall (eta : nat), forall x, T_op' eta x (T_inverse' eta x) = T_ident' eta.
    Hypothesis ident_l : forall (eta : nat), forall x, (T_op' eta) (T_ident' eta) x = x.
    Hypothesis ident_r : forall (eta : nat), forall x, (T_op' eta) x (T_ident' eta) = x.
    Hypothesis RndT_uniform : forall (eta : nat), forall x y, comp_spec (fun a b => a = x <-> b = y) (RndT' eta) (RndT' eta).

    Let comp_spec_otp_l eta
      : forall (x : T' eta), comp_spec eq (RndT' eta) (r <-$ RndT' eta; ret T_op' eta x r)
      := @OTP_inf_th_sec_l (T' eta) _ (RndT' eta) (T_op' eta) (op_assoc' eta) (T_inverse' eta) (T_ident' eta) (inverse_l_ident' eta) (inverse_r_ident' eta) (ident_l eta) (RndT_uniform eta).

    (* forall x y, A x y ==> B (f x) (f y) *)
    (* Proper PositiveSetEq CompEq generate_randomness *)

    (* Definition weird_eq := fun (A : Set) (c1 c2 : Comp A) => Comp_eq c1 c2. *)
    Global Instance Proper_PosSetEq (eta : nat) :
      Proper (PositiveSet.Equal ==> Comp_eq) (generate_randomness eta).
    Admitted.

    About Proper_Bind.
    Lemma empty_update_1 : forall (elt : Type) (m : PositiveMap.t elt),
        PositiveMap.Equal (PositiveMapProperties.update m (PositiveMap.empty elt)) m.
    Proof.
      intros.
      cbv [PositiveMapProperties.update].
      apply PositiveMapProperties.fold_Empty.
      { apply PositiveMapProperties.F.Equal_ST. }
      { apply PositiveMap.empty_1. }
    Qed.

    Lemma empty_update_2 : forall (elt : Type) (m : PositiveMap.t elt),
      PositiveMap.Equal (PositiveMapProperties.update (PositiveMap.empty elt) m) m.
    Proof.
      intros.
      cbv [PositiveMapProperties.update].
      cbv [PositiveMap.fold PositiveMap.xfoldi].
    Admitted.
    (*   apply PositiveMapProperties.fold_Empty. *)
    (*   { apply PositiveMapProperties.F.Equal_ST. } *)
    (*   { apply PositiveMap.empty_1. } *)
    (* Qed. *)

    (* Theorem symbolic_OTP : forall (n : positive) (x : forall (eta : nat), T' eta), indist (const RndT'_symbolic @ (rnd n)) (const T_op' @ const x @ (const RndT'_symbolic @ (rnd n)))%term. *)

    About interp_term_late.
    (* Global Instance Proper_interp_term_late {t} (x : term t) eta : (Proper (pointwise_relation _ PositiveMap.Equal ==> Comp_eq) (interp_term_late x eta)). *)
    (* Admitted. *)

    Global Instance Proper_map eta: Proper (pointwise_relation (PositiveMap.t (interp_base_type rand eta)) (comp_spec (@eq (T' eta))) ==> Comp_eq) (Bind (ret PositiveMap.empty (interp_type rand eta))).
    Admitted.

    Global Instance Proper_map' eta: Proper (PositiveMap.Equal ==> Comp_eq) (Ret (EqDec_dec (@randomness_map_eq_dec eta))).
    Admitted.
    (* Admitted. *)
    Theorem symbolic_OTP : forall (n : positive) (x: term message),
        fresh (rnd n) x ->
        indist (const RndT'_symbolic @ (rnd n)) (const T_op' @ x @ (const RndT'_symbolic @ (rnd n)))%term.
      indistify.
      subst.
      setoid_rewrite <-interp_term_late_correct.
      simpl interp_term_late.
      cbv [fresh] in H.
      simpl in H.
      (* rewrite H. *)

      setoid_rewrite empty_inter.
      setoid_rewrite empty_randomness.
      About empty_update_1.
      Opaque PositiveMap.empty.
      Opaque PositiveMapProperties.update.
      Admitted.
      (* setoid_rewrite empty_update_1. *)
      (* setoid_rewrite Comp_eq_left_ident. *)
      (* setoid_rewrite empty_update_1. *)
      (* setoid_rewrite Comp_eq_left_ident. *)
      (* rewrite PositiveMap.gempty. *)
      (* apply Comp_eq_evalDist. *)
      (* intros. *)
      (* fcf_at fcf_inline fcf_right 0%nat. *)
      (* fcf_at fcf_inline fcf_right 1%nat. *)
      (* fcf_at fcf_inline fcf_right 1%nat. *)
      (* fcf_at fcf_inline fcf_right 1%nat. *)
      (* fcf_at fcf_swap fcf_right 0%nat. *)
      (* fcf_at fcf_swap fcf_right 1%nat. *)
      (* fcf_at fcf_inline fcf_right 1%nat. *)
      (* fcf_irr_r. *)
      (* { admit. } *)
      (* { *)
      (*   cbv [RndT'] in comp_spec_otp_l. *)
      (*   specialize (comp_spec_otp_l eta x0). *)
      (*   assert (Comp_eq *)
      (*             (x <-$ { 0 , 1 }^ len_rand eta; ret RndT'_symbolic eta (cast_rand eta x)) *)
      (*             (r <-$ (x <-$ { 0 , 1 }^ len_rand eta; ret RndT'_symbolic eta (cast_rand eta x)); *)
      (*              ret T_op' eta x0 r)). *)
      (*   { apply comp_spec_impl_Comp_eq in comp_spec_otp_l; assumption. } *)
      (*   { *)
      (*     apply Comp_eq_evalDist. *)
      (*     setoid_rewrite Comp_eq_associativity. *)
      (*     apply Proper_Bind. *)
      (*     Admitted. *)
    (*       etransitivity. *)
    (*       instantiate (1 := (x <-$ { 0 , 1 }^ len_rand eta; ret RndT'_symbolic eta (cast_rand eta x))). *)
    (*       Unset Printing Notations. *)
    (*       idtac. *)

    (*       setoid_rewrite <- Comp_eq_associativity. *)
    (*       rewrite <- Comp_eq_associativity in H1. *)
    (*       setoid_rewrite <- Comp_eq_associativity. *)
    (*       apply Comp_eq_evalDist; intros. *)

    (*       fcf_at fcf_ret fcf_left 1%nat. *)
    (*       fcf_at fcf_inline fcf_right 2%nat. *)
    (*       apply Comp_eq_evalDist. *)
    (*       (* This rewrite should work, but it doesn't. :< *) *)
    (*       (* setoid_rewrite Comp_eq_left_ident in H1. *) *)
    (*       simpl. *)
    (*       simpl in H1. *)
    (*       About EqDec_interp_type. *)
    (*       etransitivity. *)
    (*       { *)
    (*         etransitivity. *)
    (*         { *)
    (*           instantiate (1 := x <-$ { 0 , 1 }^ len_rand eta; ret RndT'_symbolic eta (cast_rand eta x)). *)
    (*           reflexivity. *)

    (*       with (y := (x <-$ { 0 , 1 }^ len_rand eta; y <-$ ret RndT'_symbolic eta (cast_rand eta x); ret T_op' eta x0 y)). *)
    (*       { apply H1. } *)

    (*       setoid_rewrite Comp_eq_left_ident. *)
    (*       setoid_rewrite Comp_eq_left_ident in H1. *)

    (*       Focus 2. apply Bvector_EqDec. *)
    (*       assert ( *)
    (*           evalDist *)
    (*             (x <-$ ( *)
    (*                   a <-$ { 0 , 1 }^ len_rand eta; *)
    (*                   ret RndT'_symbolic eta (cast_rand eta a)); *)
    (*               ret dst message eta y x) c == *)
    (*           evalDist *)
    (*             (x <-$ ( *)
    (*                   a <-$ { 0 , 1 }^ len_rand eta; *)
    (*                   b <-$ ret RndT'_symbolic eta (cast_rand eta a); *)
    (*                   ret T_op' eta x0 b); *)
    (*               ret dst message eta y x) c). *)
    (*       { *)
    (*         apply Comp_eq_evalDist. *)
    (*         apply Proper_Bind. *)
    (*         assumption. *)
    (*         cbv [respectful]; intros; subst; reflexivity. *)
    (*       } *)
    (*       { *)
    (*         transitivity (evalDist (x <-$ (a <-$ { 0 , 1 }^ len_rand eta; *)
    (*                                        ret RndT'_symbolic eta (cast_rand eta a)); *)
    (*                                 ret dst message eta y x) c). *)
    (*         { *)
    (*           fcf_inline_first. *)
    (*           fcf_at fcf_ret fcf_right 1%nat. *)
    (*           reflexivity. *)
    (*         } *)
    (*         { *)
    (*           transitivity (evalDist (x <-$ (a <-$ { 0 , 1 }^ len_rand eta; *)
    (*                                          b <-$ ret RndT'_symbolic eta (cast_rand eta a); *)
    (*                                          ret T_op' eta x0 b); *)
    (*                                   ret dst message eta y x) c). *)
    (*           { assumption. } *)
    (*           { *)
    (*             fcf_inline_first. *)
    (*             fcf_at fcf_inline fcf_left 1%nat. *)
    (*             fcf_at fcf_ret fcf_right 1%nat. *)
    (*             reflexivity. *)
    (*           } *)
    (*         } *)
    (*       } *)
    (*     } *)
    (*   } *)
    (*   } *)
    (* { admit. } *)

    (* Admitted. *)

      (* When is it okay to rewrite ctx, Ek'x ~ ctx, rnd? *)
      (* Answer: Two conditions if you're rewriting x to y in indist expression z. *)
         (* Condition 1: y is fresh in z *)
          (* Condition 2: For all randomness that appears in x, the statement is true for all *)
      (*                                                        indices of that randomness *)
      (* Examples: *)
      (*   1. f r1 r1 ~ ? cannot be rewritten to f r1 r2 *)
      (*   2. f r1 r2 ~ ? cannot be rewritten to f r1 r1 *)
           (* 3. ctx, E_k'{x} ~ ctx, rnd can be freely rewritten with OTP *)
    Theorem temp_name: forall (x k k': term message) (n n' : positive),
        fresh x k ->
        fresh k k' ->
        fresh x k' ->
        indist (const pair_eta @ ((const T_op' @ x) @ k) @ ((const T_op' @ k) @ k'))
               (const pair_eta @ (const RndT'_symbolic @ rnd n) @ (const RndT'_symbolic @ rnd n')).
    Proof.
      intros.
      About symbolic_OTP.
      cbv [indist universal_security_game]; intros.
      apply eq_impl_negligible; cbv [pointwise_relation]; intros eta.
      eapply Proper_Bind.
      reflexivity.
      cbv [respectful]; intros.
      subst.
      setoid_rewrite <-interp_term_late_correct.
      simpl interp_term_late.
      cbv [fresh] in H, H0.
      (* When is it okay to rewrite ctx, Ek'x ~ ctx, rnd? *)
      (* Answer: Two conditions if you're rewriting x to y in indist expression z. *)
         (* Condition 1: y is fresh in z *)
          (* Condition 2: For all randomness that appears in x, the statement is true for all *)
      (*                                                        indices of that randomness *)
      (* Examples: *)
      (*   1. f r1 r1 ~ ? cannot be rewritten to f r1 r2 *)
      (*   2. f r1 r2 ~ ? cannot be rewritten to f r1 r1 *)
           (* 3. ctx, E_k'{x} ~ ctx, rnd can be freely rewritten with OTP *)


   Admitted.

(*       simpl in H. *)
(*       rewrite H. *)

(*       About symbolic_OTP. *)



(* encryption of x under k, encryption of k under k' ~~ randomness, randomness *)
  End OTP.
End Language.
Arguments type _ : clear implicits.
