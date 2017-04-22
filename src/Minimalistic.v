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

Section TODO.

Lemma PosMap_add_commutes : forall (x y : positive) (H : x <> y) (elt : Type) (m : PositiveMap.t elt) (A B : elt),
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
  Definition generate_randomness (eta:nat) idxs
    : Comp (PositiveMap.t (interp_type rand eta))
    := PositiveSet.fold (fun i rndC => (
                             rnds' <-$ rndC;
                               ri <-$ {0,1}^(len_rand eta);
                               ret (PositiveMap.add i (cast_rand eta ri) rnds')
                           )%comp)
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
    cbv [generate_randomness PositiveSet.singleton].
    rewrite PositiveSetProperties.fold_add.
    {
      rewrite PositiveSetProperties.fold_empty.
      rewrite Comp_eq_left_ident.
      { reflexivity. }
      { admit. }
    }
    { admit. }
    {
      cbv [Proper respectful Distribution_eq pointwise_relation RelCompFun].
      intros.
      rewrite H.
      assert (Comp_eq x0 y0).
      apply Comp_eq_evalDist.
      assumption.
      setoid_rewrite H0.
      reflexivity.
    }
    {
      cbv [transpose Distribution_eq pointwise_relation RelCompFun].
      intros.
      (* TODO: Make these all tactics you can perform on Comp_eqs + ask andres about this *)
      apply Comp_eq_evalDist.
      intros.
      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      fcf_at fcf_swap fcf_left 1%nat.
      fcf_at fcf_swap fcf_right 1%nat.
      fcf_at fcf_ret fcf_left 2%nat.
      fcf_at fcf_ret fcf_right 2%nat.
      apply Comp_eq_evalDist.
      destruct (Pos.eq_dec x y).
      { rewrite e; reflexivity. }
      { admit. }

      (* { *)
      (*   remember (PosMap_add_commutes x y n0 (interp_type rand eta) x0) as comm. *)
      (*   assert (evalDist *)
      (*     (a0 <-$ { 0 , 1 }^ len_rand eta; *)
      (*        a1 <-$ { 0 , 1 }^ len_rand eta; *)
      (*        ret PositiveMap.add y (cast_rand eta a0) (PositiveMap.add x (cast_rand eta a1) x0)) a == *)
      (*           evalDist *)
      (*     (a0 <-$ { 0 , 1 }^ len_rand eta; *)
      (*        a1 <-$ { 0 , 1 }^ len_rand eta; *)
      (*        ret PositiveMap.add y (cast_rand eta a1) (PositiveMap.add x (cast_rand eta a0) x0)) a). *)
      (*   { *)
      (*     fcf_at fcf_swap fcf_right 0%nat. *)
      (*     reflexivity. *)
      (*   } *)
        (* TODO: Do this rewrite under a bind. *)
      }
    { cbv [not]; apply (PositiveSetProperties.Dec.F.empty_iff n). }
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

  Section Equality.
    Definition const_eqb t : term (t -> t -> sbool) :=
      @Term_const
        (Type_arrow t (Type_arrow t (Type_base sbool)))
        (fun eta x1 x2 => if eqb x1 x2 then strue eta else sfalse eta).
    Definition eqwhp {t:type} (e1 e2:term t) : Prop := whp (const_eqb t @ e1 @ e2)%term.

    Global Instance Reflexive_eqwhp {t} : Reflexive (@eqwhp t).
    Proof.
      cbv [Reflexive indist universal_security_game eqwhp whp interp_term]; intros.
      apply eq_impl_negligible; intro eta.
      eapply Proper_Bind; [reflexivity|]; intros ? ? ?; subst.
      eapply Proper_Bind; [|intros ? ? ?; subst; reflexivity]. 
      simpl interp_term_fixed.
      etransitivity.
      { eapply Proper_Bind; [reflexivity|]; intros ? ? ?; subst.
        (* TODO: why can't we do this earlier (under binders) using setoid_rewrite? *)
        rewrite eqb_refl.
        instantiate (1:=fun _ => ret strue eta); cbv beta.
        reflexivity. }
      rewrite 2Bind_unused.
      reflexivity.
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

    Lemma interp_term_late_correct' {t} (e:term t) eta :
      forall adv univ (H:PositiveSet.Subset (randomness_indices e) univ) fixed,
      Comp_eq (interp_term_late e eta adv fixed)
              (rands <-$ generate_randomness eta univ;
                 ret (interp_term_fixed e eta adv (PositiveMapProperties.update rands fixed))).
    Proof.
      induction e; intros;
        simpl interp_term_late; simpl interp_term_fixed.
      { rewrite Bind_unused. reflexivity. }
      { admit. }
      { admit. }
      { 
    Admitted.
    Lemma interp_term_late_correct {t} (e:term t) eta adv :
      Comp_eq (interp_term_late e eta adv (PositiveMap.empty _))
              (interp_term e eta adv).
      induction e; intros. admit. admit. admit.
      simpl.
      cbv [interp_term].
      simpl.
      eapply Proper_Bind.
      (* this form is not strong enough for induction? *)
    Admitted.
  End LateInterp.

Section FillInterp.
  Fixpoint interp_term_fill_fixed {holetype t eta}
           (twh : term_wh holetype t) (filler : interp_type holetype eta)
           (adv: interp_type list_message eta -> interp_type message eta)
           (rands: PositiveMap.t (interp_type rand eta))
    : interp_type t eta :=
    match twh with
    | Term_wh_const _ c =>  c eta
    | Term_wh_random _ i => match PositiveMap.find i rands with Some r => r | _ => cast_rand eta (unreachable _) end
    | Term_wh_adversarial _ ctx => adv (interp_term_fill_fixed ctx filler adv rands)
    | Term_wh_app _ f x => (interp_term_fill_fixed f filler adv rands) (interp_term_fill_fixed x filler adv rands)
    | Term_wh_hole _ => filler
    end.

  Fixpoint randomness_indices_wh {holetype t} (twh: term_wh holetype t) : PositiveSet.t :=
    match twh with
    | Term_wh_random _ idx => PositiveSet.singleton idx
    | Term_wh_app _ f x => PositiveSet.union (randomness_indices_wh f) (randomness_indices_wh x)
    | _ => PositiveSet.empty
    end.

  Definition interp_term_fill {holetype t eta}
           (twh : term_wh holetype t) (filler : interp_type holetype eta)
           (adv: interp_type list_message eta -> interp_type message eta)
    : Comp (interp_type t eta)
    := rands <-$ generate_randomness eta (randomness_indices_wh twh); ret (interp_term_fill_fixed twh filler adv rands).

  Lemma interp_term_fill_correct {holetype t} (twh : term_wh holetype t) (x: term holetype) eta adv:
    Comp_eq (filler <-$ interp_term x eta adv;
               interp_term_fill twh filler adv)
            (interp_term (fill twh x) eta adv).
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

  (* TODO: I'm sorry this definition is in proof mode. *)
  Definition dst' {t t' u}
             (evil_rand_indices : nat -> PositiveSet.t)
             (dst : forall (t: type) (eta : nat), PositiveMap.t (interp_type rand eta) -> interp_type t eta -> bool)
             (eta : nat)
             (adv: interp_type list_message eta -> interp_type message eta)
             (evil_rands : PositiveMap.t (interp_type rand eta))
             (ctx : term_wh t u)
             (x : interp_type t' eta)
             : bool.
    destruct (eqdec_type t t').
    subst.
    exact (dst u eta evil_rands (interp_term_fill_fixed ctx x adv evil_rands)).
    exact false.
  Defined.

  Definition shift_up_set_indices (m : PositiveSet.t) (shift : positive) : PositiveSet.t :=
    PositiveSet.fold
      (fun (p : positive) (t : PositiveSet.t) => PositiveSet.add (p + shift) t) m PositiveSet.empty.


  Print BinPosDef.Pos.sub.

  Definition shift_down_map_indices {T : Type} (m : PositiveMap.t T) (shift : positive) : PositiveMap.t T :=
    PositiveMap.fold
      (fun (p : positive) (t : T) (m : PositiveMap.t T) => PositiveMap.add (BinPosDef.Pos.sub p shift) t m)
      m (PositiveMap.empty T).

  Definition defaulted_option {T U : Type} (f : T -> U) (o : option T) (default : U) : U :=
    match o with
    | Some r => f r
    | None => default
    end.

  Lemma indist_no_shared_randomness: forall {t u} (x: term t) (y: term t) (z: term u) (ctx: term_wh t u),
      indist (fill ctx x) z ->
      indist x y ->
      indist (fill ctx y) z.
  Proof.
    intros.
    transitivity (fill ctx x).
    cbv [indist universal_security_game].
    intros.
    cbv [indist universal_security_game] in H0.
    unfold interp_term.
    pose (adl' := fun (eta : nat) =>
                    PositiveSet.union
                      (defaulted_option (shift_up_set_indices (adl eta))
                                        (PositiveSet.max_elt (randomness_indices_wh ctx))
                                        (adl eta))
                      (randomness_indices_wh ctx)).

    pose (adv' := fun (eta : nat) (m : PositiveMap.t (interp_type rand eta)) =>
                    adv eta (defaulted_option (shift_down_map_indices m)
                                              (PositiveSet.max_elt (randomness_indices_wh ctx))
                                              m)).

    specialize (H0 adl' adv' (fun (t : type) (eta : nat) (evil_rands: PositiveMap.t (interp_type rand eta)) (filler : interp_type t eta) => dst' adl' dst eta (adv' eta evil_rands) evil_rands ctx filler)).
    cbv [dst' adl' adv'] in H0.
    Require Import Coq.Logic.Eqdep.

    destruct (eqdec_type t t) in H0.
    cbv [eq_rec_r eq_rec eq_rect] in H0.
    rewrite (UIP_refl type t e) in H0.
    cbv [eq_sym] in H0.

    pose proof (@interp_term_fill_correct t).
    cbv [interp_term_fill] in H1.
    specialize (H1 u ctx x).
    pose proof (fun (eta : nat) (evil_rands : PositiveMap.t (interp_type rand eta))
                => H1 eta (adv' eta evil_rands)).
    (* Dumb monad rewrites *)
    assert (negligible
         (fun eta : nat =>
          |
          Pr [evil_rands <-$
              generate_randomness eta
                (PositiveSet.union
                   (defaulted_option (shift_up_set_indices (adl eta))
                      (PositiveSet.max_elt (randomness_indices_wh ctx)) (adl eta))
                   (randomness_indices_wh ctx));
              out <-$ interp_term x eta
                  (adv eta
                       (defaulted_option (shift_down_map_indices evil_rands)
                                         (PositiveSet.max_elt (randomness_indices_wh ctx)) evil_rands));
              res <-$ ret (interp_term_fill_fixed ctx out
                       (adv eta
                          (defaulted_option (shift_down_map_indices evil_rands)
                             (PositiveSet.max_elt (randomness_indices_wh ctx)) evil_rands)) evil_rands);
              ret dst u eta evil_rands res] -
          Pr [evil_rands <-$
              generate_randomness eta
                (PositiveSet.union
                   (defaulted_option (shift_up_set_indices (adl eta))
                      (PositiveSet.max_elt (randomness_indices_wh ctx)) (adl eta))
                   (randomness_indices_wh ctx));
              out <-$ interp_term y eta
                  (adv eta
                       (defaulted_option (shift_down_map_indices evil_rands)
                                         (PositiveSet.max_elt (randomness_indices_wh ctx)) evil_rands));
              res <-$ ret (interp_term_fill_fixed ctx out
                       (adv eta
                          (defaulted_option (shift_down_map_indices evil_rands)
                             (PositiveSet.max_elt (randomness_indices_wh ctx)) evil_rands)) evil_rands);
              ret dst u eta evil_rands res] |)).
    admit.
    clear H0.
    (* can split into two: *)
    (*   evil_rands, used for the randomness of the adversary, evil_rands in h2 initialized using randomness generated from adl eta *)
    (*   rands, used only for interpreting ctx *)

    (* Needed lemma: *)
    (*   if you have a map, and one function uses only one part of the map, and the other uses only the other, you can split it up *)
                                                                                                            
    (* First problem: how to talk about adversary "using" randomness in this lemma.
       Right now this is the only way to do it. *)
    Lemma Comp_eq_split_map : forall (t u : type) (ctx : term_wh t u) (x : term t) (s1 s2 : PositiveSet.t)
                                (adv : forall eta : nat, PositiveMap.t (interp_type rand eta) -> interp_type list_message eta -> interp_type message eta) (eta : nat), 
      Comp_eq (rands <-$ generate_randomness eta (PositiveSet.union s1 (randomness_indices_wh ctx));
               x1 <-$ interp_term x eta (adv eta rands);
               ret interp_term_fill_fixed ctx x1 (adv eta rands) rands)
              (evil_rands <-$ generate_randomness eta s1;
               rands <-$ generate_randomness eta (randomness_indices_wh ctx);
               x1 <-$ interp_term x eta (adv eta evil_rands);
               ret interp_term_fill_fixed ctx x1 (adv eta evil_rands) rands).




    split up into two randomnesses
    
    (* Calculate max randomness of randomness_indices_wh ctx, then take the adl eta randomness and shift it up by that amount for each index *)
    (*                                                                                                         then in that second function, use an adv that takes in the new remapped randomnesses and fills the min for the new one *)
    (*                                                                                                         gotta prove that adv equal *)
    
    
    (* This should be true for some reason *)
    (* OTP *)
    (* "Nonuniform cracks in the concrete" (appendix) *) 
    (* Decision Diffie-Hellman assumption *)
    (* IND-CPA encryption *)
    (* IND-CCA encryption - curve-CP *)
    (* Hash Functions *)
    (* Symmetric-key that's not OTP *)
    (* Some assymetric-key primitive *)
    (* """Kerberos (encryption with two keys) """ *)
    (* Diffie Hellman key exchange, sigma-i, Hugo <something> , curve-CP*)

    Print interp_term.
 Abort.

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

    Global Instance Proper_Bind' {A B} : Proper (Comp_eq ==> pointwise_relation _ Comp_eq ==> Comp_eq) (@Bind A B).
    Admitted.

    Global Instance Proper_interp_term_late {t} (x : term t) eta : (Proper (eq ==> PositiveMap.Equal ==> Comp_eq) (interp_term_late x eta)).
    Admitted.

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
      rewrite H.

      setoid_rewrite empty_inter.
      setoid_rewrite empty_randomness.
      About empty_update_1.
      Opaque PositiveMap.empty.
      Opaque PositiveMapProperties.update.
      setoid_rewrite empty_update_1.
      setoid_rewrite Comp_eq_left_ident.
      setoid_rewrite empty_update_1.
      setoid_rewrite Comp_eq_left_ident.
      rewrite PositiveMap.gempty.
      apply Comp_eq_evalDist.
      intros.
      fcf_at fcf_inline fcf_right 0%nat.
      fcf_at fcf_inline fcf_right 1%nat.
      fcf_at fcf_inline fcf_right 1%nat.
      fcf_at fcf_inline fcf_right 1%nat.
      fcf_at fcf_swap fcf_right 0%nat.
      fcf_at fcf_swap fcf_right 1%nat.
      fcf_at fcf_inline fcf_right 1%nat.
      fcf_irr_r.
      { admit. }
      {
        cbv [RndT'] in comp_spec_otp_l.
        specialize (comp_spec_otp_l eta x0).
        assert (Comp_eq
                  (x <-$ { 0 , 1 }^ len_rand eta; ret RndT'_symbolic eta (cast_rand eta x))
                  (r <-$ (x <-$ { 0 , 1 }^ len_rand eta; ret RndT'_symbolic eta (cast_rand eta x));
                   ret T_op' eta x0 r)).
        { apply comp_spec_impl_Comp_eq in comp_spec_otp_l; assumption. }
        {
          apply Comp_eq_evalDist.
          setoid_rewrite Comp_eq_associativity.
          apply Proper_Bind.
          Admitted.
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


  Lemma indist_rand (x y:positive) : indist (rnd x) (rnd y).
  Proof.
    cbv [indist]; intros.
    apply eq_impl_negligible; cbv [pointwise_relation]; intros eta.
    cbv [universal_security_game].
    (* setoid_rewrite <-interp_term_late_correct. WHY does it not work? *)
    eapply Proper_Bind; [reflexivity|]; intros ? ? ?; subst.
    setoid_rewrite <-interp_term_late_correct.
    simpl interp_term_late.
    rewrite 2PositiveMap.gempty.
    reflexivity.
  Qed.
End Language.
Arguments type _ : clear implicits.