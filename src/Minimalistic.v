Require Import FCF.
Require Import Asymptotic.
Require Import Admissibility.
Require Import Tactics.
Require Import FrapTactics.
Require Import Encryption.
Require Import SplitVector.
Require Import TwoWorldsEquiv.
Require Import RatUtil.
Require Import RewriteUtil.
Require Import Util.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.SetoidList.
Require Import Coq.Lists.ListSet.

Section Language.
  Context {base_type : Set} {interp_base_type:base_type->Set}.

  Inductive type := Type_base (t:base_type) | Type_arrow (dom:type) (cod:type).
  Global Coercion Type_base : base_type >-> type.
  Fixpoint interp_type (t:type) : Set :=
    match t with
    | Type_base t => interp_base_type t
    | Type_arrow dom cod => interp_type dom -> interp_type cod
    end.

  Context {message list_message rand : base_type}.

  (* A term is parametrized by its type, which can either be one of the base_types *)
  (* listed above, or an arrow type consisting of multiple interpreted base_types. *)
  Inductive term : type -> Type :=
  | Term_const {t} (_: nat -> interp_type t) : term t
  | Term_random (_:nat) : term rand
  | Term_adversarial (_:term list_message) : term message
  | Term_app {dom cod} (_:term (Type_arrow dom cod)) (_:term dom) : term cod.

  (* the first natural number that is not a valid randomness index *)
  Fixpoint rand_end {t:type} (e:term t) : nat :=
    match e with
    | Term_random n => S n
    | Term_app f x => max (rand_end f) (rand_end x)
    | _ => 0
    end.

  Context (interp_random : nat -> interp_type rand).
  Context (interp_adversarial : interp_type list_message -> interp_type message).
  Fixpoint interp_term
           {t} (e:term t) (eta : nat) : interp_type t :=
    match e with
    | Term_const c => c eta
    | Term_random n => interp_random n
    | Term_adversarial ctx => interp_adversarial (interp_term ctx eta)
    | Term_app f x => (interp_term f eta) (interp_term x eta)
    end.
End Language.

Arguments type : clear implicits.
Arguments interp_type {_} _ _.
Arguments term {_} _ _ _ _ _.
Arguments rand_end [_ _ _ _ _ _] _.

Section CompInterp.
  (* We explicitly distinguish between randomness and a message type *)
  Inductive base_type := BaseType_bool | BaseType_message | BaseType_list_message | BaseType_rand.
  Definition interp_base_type t :=
    match t with
    | BaseType_bool => bool
    | BaseType_message => list bool
    | BaseType_list_message => list (list bool)
    | BaseType_rand => list bool
    end.

  Let term := (term interp_base_type BaseType_message BaseType_list_message BaseType_rand).
  
  (* TODO: we aither need to only allow computing base types OR require all types to be finite *)
  Global Instance interp_eqdec : forall {t}, EqDec (interp_type interp_base_type t).
  Admitted.

  (* different protocols may use different amounts of randomness at the same security level. this is an awkward and boring parameter *)

  (* TODO: each term rnd should have it's own size as a function of eta, then the max would be adding together bits that everything needs (this will eliminate multiplication) *)
  Context (rand_size : nat -> nat).

  Section WithAdversary.
    (* the adversary is split into three parts for no particular reason. It first decides how much randomness it will need, then interacts with the protocol (repeated calls to [adverary] with all messages up to now as input), and then tries to claim victory ([distinguisher]). There is no explicit sharing of state between these procedures, but all of them get the same random inputs in the security game. The handling of state is a major difference between FCF [OracleComp] and this framework *)
    Context (evil_rand_tape_len : nat -> nat).
    Context (adversary:nat -> list bool -> list (list bool) -> list bool).
    Context (distinguisher: forall {t}, nat -> list bool -> interp_type interp_base_type t -> bool).

    Definition comp_interp_term_fixed (good_rand_tape evil_rand_tape:list bool) eta {t} (e:term t) :=
      let interp_random (n:nat) : interp_type interp_base_type (Type_base BaseType_rand)
          := List.firstn (rand_size eta) (List.skipn (n * rand_size eta) good_rand_tape) in
      let interp_adversarial : interp_type interp_base_type (Type_arrow (Type_base BaseType_list_message) (Type_base BaseType_message))
          := adversary eta evil_rand_tape in
      interp_term interp_random interp_adversarial e eta.

    Definition comp_interp_term eta {t:type base_type} (e:term t)  : Comp (interp_type interp_base_type t) :=
      good_rand_tape' <-$ {0,1}^(rand_end e * rand_size eta);
        evil_rand_tape' <-$ {0,1}^(evil_rand_tape_len eta);
        let good_rand_tape := Vector.to_list good_rand_tape' in
        let evil_rand_tape := Vector.to_list evil_rand_tape' in
        ret (comp_interp_term_fixed good_rand_tape evil_rand_tape eta e).
            
    Definition universal_security_game eta {t:type base_type} (e:term t) : Comp bool :=
      good_rand_tape' <-$ {0,1}^(rand_end e * rand_size eta);
        evil_rand_tape' <-$ {0,1}^(evil_rand_tape_len eta);
        let good_rand_tape := Vector.to_list good_rand_tape' in
        let evil_rand_tape := Vector.to_list evil_rand_tape' in
        let out := comp_interp_term_fixed good_rand_tape evil_rand_tape eta e in
        ret (distinguisher _ eta evil_rand_tape out).

  End WithAdversary.

  Definition indist {t:type base_type} (a b:term t) : Prop :=  forall l adv dst,
      (* TODO: insert bounds on coputational complexity of [adv] and [dst] here *)
      let game eta e := universal_security_game l adv dst eta e in
      negligible (fun eta => | Pr[game eta a] -  Pr[game eta b] | ).
  Global Instance Reflexive_indist {t} : Reflexive (@indist t).
  Proof.
    cbv [Reflexive indist]; setoid_rewrite ratDistance_same; eauto using negligible_0.
  Qed.

  Global Instance Symmetric_indist {t} : Symmetric (@indist t).
  Proof.
    cbv [Symmetric indist]; intros; setoid_rewrite ratDistance_comm; eauto.
  Qed.

  Delimit Scope term_scope with term.

  Notation "A -> B" := (Type_arrow A B) : term_scope.
  Notation "A @ B" := (Term_app A B) (at level 99) : term_scope.

  Notation "'rnd' n" := (Term_random n) (at level 35) : term_scope.
  Notation "'const' c" := (Term_const c) (at level 35) : term_scope.

  Notation s_message := (Type_base BaseType_message).
  Notation s_rand := (Type_base BaseType_rand).
  Notation s_bool := (Type_base BaseType_bool).

  Section Eqwhp.
    Definition s_true : nat -> interp_type interp_base_type s_bool := fun _ => true.
    Definition s_eqb : nat -> interp_type interp_base_type (s_bool -> s_bool -> s_bool)%term := fun _ => eqb.

    Definition eqwhp (b0 b1 : forall _ : nat, interp_type interp_base_type s_bool) : Prop :=
      indist (const s_eqb @ (const b0) @ (const b1))%term (const s_true)%term.

    Global Instance Reflexive_eqwhp : Reflexive eqwhp.
    Proof.
      simpl.
      intros.
      cbv [Reflexive indist universal_security_game eqwhp s_eqb rand_end].
      intros.
      pose proof negligible_const_num 1.
      apply eq_impl_negligible.
      intros eta.
      apply Comp_eq_bool.
      fcf_well_formed.
      fcf_well_formed.
      rewrite Nat.max_0_l.
      fcf_skip.
      fcf_skip.
      apply evalDist_ret_eq.
      apply f_equal.
      cbv [comp_interp_term_fixed interp_term s_true].
      apply eqb_refl.
    Qed.

    Global Instance Symmetric_eqwhp : Symmetric eqwhp.
    Proof.
      simpl.
      intros.
      cbv [Symmetric indist universal_security_game eqwhp s_eqb rand_end].
      intros.
      pose proof negligible_const_num 1.
      apply eq_impl_negligible.
      intros eta.
      apply Comp_eq_bool.
      fcf_well_formed.
      fcf_well_formed.
      rewrite Nat.max_0_l.
      fcf_skip.
      fcf_skip.
      apply evalDist_ret_eq.
      apply f_equal.
      cbv [comp_interp_term_fixed interp_term s_true].

    Admitted.
  End Eqwhp.

  (* randomness -> key *)
  Context (KeyGen : nat -> interp_type interp_base_type (s_rand -> s_message)%term).
  (* key -> randomness -> plaintext -> ciphertext *)
  Context (Encrypt : nat -> interp_type interp_base_type (s_message -> s_rand -> s_message -> s_message)%term).
  (* key -> ciphertext -> plaintext *)
  Context (Decrypt : nat -> interp_type interp_base_type (s_message -> (s_message -> s_message))%term).

  Context (admissible_A1: pred_oc_fam).
  Context (admissible_A2: pred_oc_func_2_fam).

  Fixpoint disjoint A (xl yl : list A) :=
    match xl with
    | nil => True
    | x :: xl => ~ In x yl /\ disjoint A xl yl
    end.

  Fixpoint rands_in {t} (x : term t) : list nat :=
    match x with
      | Term_random n => n :: nil
      | Term_app func arg => rands_in func ++ rands_in arg
      | _ => nil
    end.

  (* Lemma rand_split : forall {dom cod} (func : term (Type_arrow dom cod)) (arg : term dom), *)
  (*     exists (lfunc larg lshare : list nat), *)
  (*       NoDup lfunc -> *)
  (*       NoDup larg -> *)
  (*       NoDup lshare -> *)
  (*       disjoint lfunc larg -> *)
  (*       disjoint larg lshare -> *)
  (*       disjoint lfunc lshare -> *)
  (*       length lfunc + length larg + length lshare = rand_end (Term_app func arg) -> *)


  (*       Comp_eq  (r <-$ {0, 1} ^ rand_end (Term_app func arg); *)
  (*                ) *)




    (* Term_app {dom cod} (_:term (Type_arrow dom cod)) (_:term dom) : term cod *)
    (* If functions take different randomness as direct arguments, you can split up into + *)
    (* forall (t : term), partition into three sets of randomness, used in a, used in b, used in a + b *)
(* exists (a, b, c : list nat), (a b c are disjoint, elements are unique, sum of lengths = rand_end t), comp_eq ({0, 1} ^ rand_end t) ( *)

  (* TODO: split good_rand_tape into two separate binds *)
  (* TODO: p0, p1 are arbitrary terms that cannot include (rnd r) or (rnd n0) *)
  Lemma indist_encrypt
  (p0 p1 : forall _ : nat, interp_type interp_base_type (s_message))
  (r n0 n1: nat)
  (HNoDup:NoDup (r::n0::n1::nil))
  : indist (const Encrypt @ (const KeyGen @ (rnd r)) @ (rnd n0) @ (const p0))%term
           (const Encrypt @ (const KeyGen @ (rnd r)) @ (rnd n1) @ (const p1))%term.
  Proof.
    cbv [indist universal_security_game comp_interp_term interp_term].
    intros.
                                                                                                        (* coq positive map, randomness is map from index to slot *)
    (* forall (t : term), if two subterms are disjoint, you can partition into two randomnesses *)

    (* , comp_eq ({0, 1} ^ rand_end t) (you can partition rand_end t into n sections/ loop from 0 to n and sum to get the distribution) *)
    (* [ecut] ? *)
    evar (T1:Type); evar (e1:T1); subst T1.
    evar (T2:Type); evar (e2:T2); subst T2.
    evar (T3:Type); evar (e3:T3); subst T3.
    evar (T4:Type); evar (e4:T4); subst T4.
    evar (T5:Type); evar (e5:T5); subst T5.
    evar (T6:Type); evar (e6:T6); subst T6.
    evar (T7:Type); evar (e7:T7); subst T7.
    evar (T8:Type); evar (e8:T8); subst T8.
    evar (eIND:@IND_CPA_SecretKey e1 e2 e3 e4 e5 e6 e7 e8); clearbody eIND.
    subst e1 e2 e3 e4 e5 e6 e7 e8.
    cbv[IND_CPA_SecretKey IND_CPA_SecretKey_Advantage] in eIND.
    eapply TwoWorlds_equiv'.
    admit.
    admit.
    cbv [StandardDef_G'].
    cbv [IND_CPA_SecretKey_G] in eIND.
    cbv [EncryptOracle] in eIND.

    (* map from randomness index to option randomness *)
    (* rewrite interpretation function to push randomness down as low as possible by keeping around map with either already generated or not yet generated randomness *)
    (* prove that two interpretation functions are equal *)
    (* Lemma rand_split : forall adv evil_rand_tape' eta *)
    (*                      {dom cod} (func : term (Type_arrow dom cod)) (arg : term dom), *)
    (*   exists (lfunc larg lshare : list nat), *)
    (*     NoDup lfunc -> *)
    (*     NoDup larg -> *)
    (*     NoDup lshare -> *)
    (*     disjoint lfunc larg -> *)
    (*     disjoint larg lshare -> *)
    (*     disjoint lfunc lshare -> *)
    (*     length lfunc + length larg + length lshare = rand_end (Term_app func arg) -> *)


    (*     Comp_eq (good_rand_tape <-$ {0, 1} ^ rand_end (Term_app func arg); *)
    (*                ret (comp_interp_term_fixed adv *)
    (*                                            (Vector.to_list good_rand_tape') *)
    (*                                            (Vector.to_list evil_rand_tape') *)
    (*                                            eta *)
    (*                                            cod *)
    (*                                            (Term_app func arg))) *)
    (*             (rshare <-$ {0, 1} ^ length lshare; *)
    (*                rarg <-$ {0, 1} ^ length larg; *)
    (*                comp_interp_term_fixed adv *)


    (*                arg' <-$ comp_interp_term_fixed adv *)
    (*                                            (Vector.to_list good_rand_tape') *)
    (*                                            (Vector.to_list evil_rand_tape') *)



    (* (* split it, move good_rand_tape generation down as much as possible *) *)
    (* (* group good_rand_tape + encrypt, good_rand_tape + keygen *) *)
    (* (* instantiate (e6 := (thing that generates comp, bind in goal with good_rand_tape)) *) *)
    (* (* A1 -- generate constant *) *)
    (* (* A2 - everything else *) *)


    (* instantiate (e7 := fun _ _ _ _ => True). *)
    (* instantiate (e8 := fun _ _ _ _ _ _ => True). *)
    (* cbv beta in eIND. *)

    (* eapply IND_CPA_SecretKey_equiv in eIND. *)

    (* eapply TwoWorlds_equiv in eIND. *)

  (* generalize (random_size eta) as D; intro D. *)
    Admitted.

(** proving soundness of symbolic axioms *)
  End CompInterp.

Section SymbolicProof.
  Context {base_type : Set} {interp_base_type : base_type -> Set}.
  Local Coercion type_base (t:base_type) : type base_type := Type_base t.
  Context {message list_message rand bool : base_type}.

  Local Notation term := (term interp_base_type message list_message rand).
  Context (indist : forall {t : type base_type}, term t -> term t -> Prop). Arguments indist {_} _ _.

  Context (if_then_else : forall {t}, term (Type_arrow bool (Type_arrow t (Type_arrow t t)))). Arguments if_then_else {_}.
  Context (indist_rand: forall x y, indist (Term_random x) (Term_random y)).
  Context (indist_if_then_else_irrelevant_l : forall t (x y:term t),
              indist x y -> forall b:term bool, indist (Term_app (Term_app (Term_app if_then_else b) x) y) x).

  Lemma indist_if_then_else_rand_l (b:term bool) (x y:nat) :
    indist (Term_app (Term_app (Term_app if_then_else b) (Term_random x)) (Term_random y)) (Term_random x).
  Proof. exact (indist_if_then_else_irrelevant_l _ _ _ (indist_rand x y) _). Qed.
End SymbolicProof.

Definition if_then_else {t : type base_type}
  : interp_type interp_base_type (Type_arrow (type_base BaseType_bool) (Type_arrow t (Type_arrow t t)))
  := fun (b : bool) (x y : interp_type interp_base_type t) => if b then x else y.

Axiom random_size : nat -> nat.

Lemma indist_rand: forall x y : nat, indist random_size (Term_random x) (Term_random y).
Proof.
  cbv [rand_end indist universal_security_game comp_interp_term interp_term]. (* to monadic probability notation *)
  intros.
  pose proof negligible_const_num 1.
  apply eq_impl_negligible.
  intros eta.
  apply Comp_eq_bool.
  fcf_well_formed.
  fcf_well_formed.
  dist_swap_l.
  dist_swap_r.
  fcf_skip.

  assert (Pr [c <-$ (d <-$ (a <-$ { 0 , 1 }^ x * random_size eta + random_size eta; ret (splitVector (x * random_size eta) (random_size eta) a)); ret snd d);
              ret dst (Type_base BaseType_rand) eta (Vector.to_list x0) (Vector.to_list c) ] ==
          Pr [c <-$ (d <-$ (a <-$ { 0 , 1 }^ y * random_size eta + random_size eta; ret (splitVector (y * random_size eta) (random_size eta) a)); ret snd d);
              ret dst (Type_base BaseType_rand) eta (Vector.to_list x0) (Vector.to_list c) ] ).
  {
    fcf_skip.
    match goal with |- evalDist ?C1 ?x == evalDist ?C2 ?x => generalize x; change (Comp_eq C1 C2) end.
    setoid_rewrite Rnd_split_eq.
    apply Comp_eq_evalDist.
    {
      fcf_well_formed.
    }
    {
      fcf_well_formed.
    }
    {
      intros.
      fcf_inline_first.
      fcf_at fcf_inline fcf_left 1%nat.
      fcf_at fcf_inline fcf_right 1%nat.
      fcf_swap fcf_left.
      fcf_swap fcf_right.
      fcf_skip.
      fcf_at fcf_ret fcf_left 1%nat.
      fcf_at fcf_ret fcf_right 1%nat.
      cbv [snd].
      fcf_irr_l.
      {
        fcf_well_formed.
      }
      fcf_irr_r.
      {
        fcf_well_formed.
      }
    }
  }
  etransitivity.
  etransitivity.
  2: apply H1.

  fcf_inline_first.
  replace (S x * random_size eta)%nat with (x * random_size eta + random_size eta)%nat by ring.
  fcf_skip.
  fcf_simp.
  apply evalDist_ret_eq.
  repeat f_equal.
  cbv [comp_interp_term_fixed interp_term].
  rewrite list_vector_split.
  eapply firstn_ge_all.
  rewrite to_list_length.
  auto.

  fcf_inline_first.
  replace (S y * random_size eta)%nat with (y * random_size eta + random_size eta)%nat by ring.
  fcf_skip.
  fcf_simp.
  apply evalDist_ret_eq.
  repeat f_equal.
  cbv [comp_interp_term_fixed interp_term].
  rewrite list_vector_split.
  symmetry.
  eapply firstn_ge_all.
  rewrite to_list_length.
  auto.
Qed.
