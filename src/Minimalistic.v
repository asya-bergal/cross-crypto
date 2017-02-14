Require Import FCF.
Require Import Asymptotic.
Require Import Admissibility.
Require Import Tactics.
Require Import FrapTactics.
Require Import Encryption.
Require Import SplitVector.
Require Import TwoWorldsEquiv.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.SetoidList.

(* TODO: move these *)
Create HintDb rat discriminated.
Create HintDb ratsimpl discriminated.

Hint Immediate (@reflexivity Rat eqRat _) : rat.
Hint Immediate (@reflexivity Rat leRat _) : rat.

Lemma maxRat_same r : maxRat r r = r.
Proof. intros; cbv [maxRat]; destruct (bleRat r r) eqn:?; trivial. Qed.
Lemma minRat_same r : minRat r r = r.
Proof. intros; cbv [minRat]; destruct (bleRat r r) eqn:?; trivial. Qed.

Hint Rewrite ratSubtract_0 minRat_same maxRat_same : ratsimpl.

Lemma ratDistance_same r : ratDistance r r == 0.
Proof. cbv [ratDistance]; autorewrite with ratsimpl; auto with rat. Qed.

Hint Rewrite ratDistance_same : ratsimpl.






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

Lemma Rnd_split_equiv n1 n2 : Comp_eq
                                (x <-$ { 0 , 1 }^ n1 + n2; ret splitVector n1 n2 x)
                                (x1 <-$ { 0 , 1 }^ n1; x2 <-$ { 0 , 1 }^ n2; ret (x1, x2)).
Proof. intro z. eapply Rnd_split_equiv. Qed.

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
  well_formed_comp x
  -> well_formed_comp y
  -> (forall c, evalDist x c == evalDist y c)
  -> Comp_eq x y.
  intros.
  intro b.
  apply H1.
Qed.

Lemma list_vector_split a b (T : Set) (x : Vector.t T _) : skipn (b) (Vector.to_list x) = Vector.to_list (snd (splitVector (b) a x)).
  induction b; simpl; intuition.
  destruct (splitVector b a (Vector.tl x)) eqn:?.
  specialize (IHb (Vector.tl x)).
  rewrite Heqp in IHb.
  simpl in *.
  rewrite <- IHb.
  SearchAbout Vector.hd Vector.tl.
  rewrite (Vector.eta x).
  reflexivity.
Qed.

Section Language.
  Context {base_type : Set} {interp_base_type:base_type->Set}.

  Inductive type := Type_base (t:base_type) | Type_arrow (dom:type) (cod:type).
  Global Coercion Type_base : base_type >-> type.
  Fixpoint interp_type (t:type) : Set :=
    match t with
    | Type_base t => interp_base_type t
    | Type_arrow dom cod => interp_type dom -> interp_type cod
    end.

  (* interp term takes in eta, comp_interp_term passes in eta , term should include nat -> *)

  Context {message list_message rand : base_type}.
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
  Inductive base_type := BaseType_bool | BaseType_message | BaseType_list_message.
  Definition interp_base_type t :=
    match t with
    | BaseType_bool => bool
    | BaseType_message => list bool
    | BaseType_list_message => list (list bool)
    end.
  Let term := (term interp_base_type BaseType_message BaseType_list_message BaseType_message).
  
  (* TODO: we aither need to only allow computing base types OR require all types to be finite *)
  Global Instance interp_eqdec : forall {t}, EqDec (interp_type interp_base_type t).
  Admitted.

  (* different protocols may use different amounts of randomness at the same security level. this is an awkward and boring parameter *)
  Context (rand_size : nat -> nat).

  Section WithAdversary.
    (* the adversary is split into three parts for no particular reason. It first decides how much randomness it will need, then interacts with the protocol (repeated calls to [adverary] with all messages up to now as input), and then tries to claim victory ([distinguisher]). There is no explicit sharing of state between these procedures, but all of them get the same random inputs in the security game. The handling of state is a major difference between FCF [OracleComp] and this framework *)
    Context (evil_rand_tape_len : nat -> nat).
    Context (adversary:nat -> list bool -> list (list bool) -> list bool).
    Context (distinguisher: forall {t}, nat -> list bool -> interp_type interp_base_type t -> bool).

    Definition comp_interp_term_fixed (good_rand_tape evil_rand_tape:list bool) eta {t} (e:term t) :=
      let interp_random (n:nat) : interp_type interp_base_type (Type_base BaseType_message)
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
  Notation s_bool := (Type_base BaseType_bool).

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
  (*   specialize (H l adv dst). *)
  (*   Print eq_impl_negligible. *)
  (*   apply eq_impl_negligible in H. *)
  (*   intros eta. *)
  (*   apply Comp_eq_bool. *)

  (* Qed. *)


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
  generalize (random_size eta) as D; intro D.


  Context (Encrypt : nat -> interp_type interp_base_type (s_message -> s_message -> s_message -> s_message)%term).
  Definition eqwhp (a b :  ) : indist (
  Lemma indist_encrypt
  (p0 p1 : forall _ : nat, interp_type interp_base_type (Type_base BaseType_message))
  (r n0 n1: nat)
  (HNoDup:NoDup (r::n0::n1::nil))
  : indist (const Encrypt @ (const KeyGen @ (rnd r)) @ (rnd n0) @ (const p0))%term
           (const Encrypt @ (const KeyGen @ (rnd r)) @ (rnd n1) @ (const p1))%term.

  (* Definition eqwhp (a b : term *)
(* thing you might wanna do: define [eqwhp] as [indist (decide_eq_bool a b) true], try to prove some lemma like Cong in the latest paper *)

  (*   destruct (typeDec t t) in X; [|congruence]. *)
  (*   cbv [eq_rec_r eq_rec eq_rect eq_sym] in X. *)
  (*   replace e with (eq_refl:t=t) in X by admit. *)

  (*   destruct (tEqDec x x) in X; [|congruence]. *)
  (*   destruct (tEqDec x y) in X; [congruence|]. *)
  (*   cbv[negligible] in X. *)
  (*   specialize (X 1%nat). *)
  (*   destruct X as [n' X]. *)
  (*   specialize (X (1+n')%nat). *)
  (*   assert (nz (1+n')) by (constructor; omega). *)
  (*   specialize (X H0). *)
  (*   assert (1 + n' > n') by omega. *)
  (*   specialize (X H1). *)
  (*   apply X; clear X. *)

  (*   lazymatch goal with *)
  (*     |- context [ Pr [?C] ] => *)
  (*     let H := fresh "H" in *)
  (*     assert (Pr [C] == 1) as H; *)
  (*       [|rewrite H; clear H] *)
  (*   end. *)
  (*   { *)
  (*     fcf_irr_l; fcf_well_formed; fcf_irr_l; fcf_well_formed; fcf_compute. *)
  (*   } *)

  (* lazymatch goal with *)
  (*   |- context [ Pr [?C] ] => *)
  (*   let H := fresh "H" in *)
  (*   assert (Pr [C] == 0) as H; *)
  (*   [|rewrite H; clear H] *)
  (* end. *)
  (*   { *)
  (*     fcf_irr_l; fcf_well_formed; fcf_irr_l; fcf_well_formed; fcf_compute. *)
  (*   } *)
  (*   { *)
  (*     lazymatch goal with |- ?a <= ?b => change (a <= 1) end. *)
  (*     apply rat_le_1. *)
  (*     apply expnat_ge_1. *)
  (*     omega. *)
  (*   } *)
  (* Admitted. *)

  (* randomness -> key *)
  Context (KeyGen : nat -> interp_type interp_base_type (s_message -> s_message)%term).
  (* key -> plaintext -> randomness -> ciphertext *)
  Context (Encrypt : nat -> interp_type interp_base_type (s_message -> s_message -> s_message -> s_message)%term).
  (* key -> ciphertext -> plaintext *)
  Context (Decrypt : nat -> interp_type interp_base_type (s_message -> (s_message -> s_message))%term).

  Context (admissible_A1: pred_oc_fam).
  Context (admissible_A2: pred_oc_func_2_fam).


(* Goal Type. *)
(*   Print IND_CPA_SecretKey. *)
(*   refine (@IND_CPA_SecretKey (fun n : nat => interp_type interp_base_type (Type_base BaseType_message)) (fun n : nat => interp_type interp_base_type (Type_base BaseType_message)) (fun n : nat => interp_type interp_base_type (Type_base BaseType_message)) _ _ _ admissible_A1 admissible_A2). *)
(*   pose proof KeyGen. *)
(*   cbv [interp_type] in H. *)
(*   simpl. *)
(*   simpl in H. *)
(*   pose @comp_interp_term. *)
  

  Lemma indist_encrypt
  (p0 p1 : forall _ : nat, interp_type interp_base_type (s_message))
  (r n0 n1: nat)
  (HNoDup:NoDup (r::n0::n1::nil))
  : indist (const Encrypt @ (const KeyGen @ (rnd r)) @ (rnd n0) @ (const p0))%term
           (const Encrypt @ (const KeyGen @ (rnd r)) @ (rnd n1) @ (const p1))%term.
  Proof.
    cbv [rand_end indist universal_security_game comp_interp_term interp_term].
    intros.
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
    (* eapply IND_CPA_SecretKey_equiv in eIND. *)

    (* eapply TwoWorlds_equiv in eIND. *)

  (* generalize (random_size eta) as D; intro D. *)
    Admitted.
  (* pose proof negligible_const_num 1. *)
  (* apply eq_impl_negligible. *)

  (* intros eta. *)
  (* apply Comp_eq_bool. *)
  (* fcf_well_formed. *)
  (* fcf_well_formed. *)
  (* dist_swap_l. *)
  (*   cbv [rand_end indist universal_security_game comp_interp_term interp_term]. (* to monadic probability notation *) *)
  (* Context {message list_message rand : base_type}. *)

  (* Context (Plaintext Ciphertext Key : DataTypeFamily). *)
  (* Context {base_type : Set} {interp_base_type:base_type->Set}. *)
  (* Inductive type := Type_base (t:base_type) | Type_arrow (dom:type) (cod:type). *)
  (* Context {base_type : Set} {interp_base_type:base_type->Set}. *)

  (* Check term rand. *)



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

  (* Context (Plaintext Ciphertext Key : message). *)

  (* Lemma indist_refl {t} (x:term t) : indist x x. *)
End SymbolicProof.

Definition if_then_else {t : type base_type}
  : interp_type interp_base_type (Type_arrow (type_base BaseType_bool) (Type_arrow t (Type_arrow t t)))
  := fun (b : bool) (x y : interp_type interp_base_type t) => if b then x else y.
(* Lemma Comp_eq_impl_evalDist A (x y : Comp A): *)
(*   Comp_eq x y -> *)
(*   evalDist *)
Print Distribution.

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
  generalize (random_size eta) as D; intro D.

  assert (Pr [c <-$ (d <-$ (a <-$ { 0 , 1 }^ x * D + D; ret (splitVector (x * D) D a)); ret snd d);
              ret dst (Type_base BaseType_message) eta (Vector.to_list x0) (Vector.to_list c) ] ==
          Pr [c <-$ (d <-$ (a <-$ { 0 , 1 }^ y * D + D; ret (splitVector (y * D) D a)); ret snd d);
              ret dst (Type_base BaseType_message) eta (Vector.to_list x0) (Vector.to_list c) ] ).
  {
    fcf_skip.
    match goal with |- evalDist ?C1 ?x == evalDist ?C2 ?x => generalize x; change (Comp_eq C1 C2) end.
    setoid_rewrite Rnd_split_equiv.
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
  2: apply H2.

  fcf_inline_first.
    (*   |- context [ Pr [?C] ] => *)
    (*   let H := fresh "H" in *)
    (*   assert (Pr [C] == 1) as H; *)
    (*     [|rewrite H; clear H] *)
    (* end. *)
  (* match goal with |- context [S ?x * D] => replace (S x * D)%nat with (x * D + D)%nat by ring end. *)
  replace (S x * D)%nat with (x * D + D)%nat by ring.
  fcf_skip.
  fcf_simp.
  apply evalDist_ret_eq.
  repeat f_equal.
  rewrite list_vector_split.
  eapply firstn_ge_all.
  rewrite to_list_length.
  auto.

  fcf_inline_first.
  replace (S y * D)%nat with (y * D + D)%nat by ring.
  fcf_skip.
  fcf_simp.
  apply evalDist_ret_eq.
  repeat f_equal.
  rewrite list_vector_split.
  symmetry.
  eapply firstn_ge_all.
  rewrite to_list_length.
  auto.
Qed.