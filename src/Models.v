Set Implicit Arguments.

Require Import CrossCrypto.FirstOrder.
Require Import Coq.Lists.List.
Import ListNotations.

Section Models.

  (* Finite bound on the number of random values you and the attacker will need. *)
  Context (rand_bound : nat).
  Context (arand_bound : nat).

Section SymbolicModel.

  Inductive SymbolicSort :=
  | Message : SymbolicSort
  | Bool : SymbolicSort.

  Inductive SymbolicFunc : list SymbolicSort -> SymbolicSort -> Type :=
  | STrue : SymbolicFunc [] Bool
  | SFalse : SymbolicFunc [] Bool
  | IfThenElse : SymbolicFunc (Bool :: Message :: Message :: []) Message
  | EmptyMsg : SymbolicFunc [] Message
  | Eq : SymbolicFunc (Message :: Message :: []) Bool
  | EqL : SymbolicFunc (Message :: Message :: []) Bool

  | Name : forall (n : nat), n < rand_bound -> (SymbolicFunc [] Message)
  | AName : forall (n : nat), n < arand_bound -> (SymbolicFunc [] Message)
  | Handle : forall (n : nat) (dom : list SymbolicSort) (cod : SymbolicSort), SymbolicFunc dom cod.

  (* Indistinguishability is defined on both messages and booleans *)
  Inductive SymbolicPredicate : list SymbolicSort -> Type :=
    | Indist : forall (l1 l2 : list SymbolicSort) (H: length l1 = length l2), SymbolicPredicate (l1 ++ l2).

End SymbolicModel.

Require Import WC_PolyTime.
Require Import Admissibility.
Require Import Asymptotic.
Require Import FCF.

Require Import CrossCrypto.CompUtil.
Require Import CrossCrypto.FrapTactics.
Require Import CrossCrypto.HList.
Require Import CrossCrypto.Tuple.

Section CompInterp.

  Context `{function_cost_model}.
  (* TODO: actual definition of reasonable *)
  Definition reasonable (cost : FunctionCostModel) := True.

  Context `{reasonable cost}.

  Definition message := {n : nat & Bvector n}.
  Definition rands (eta : nat) := tuple (Bvector eta) rand_bound.
  Definition arands (eta : nat) := tuple (Bvector eta) arand_bound.
  Definition comp (S : Set) := forall (eta : nat), rands eta -> arands eta -> Comp S.

  Definition curry_rands_func T eta (c : rands eta -> arands eta -> Comp T) : tuple (Bvector eta) (rand_bound + arand_bound) -> Comp T.
    intros.
    remember (tskipn H0 rand_bound) as arand.
    assert (rand_bound + arand_bound - rand_bound = arand_bound).
    linear_arithmetic.
    clear Heqarand.
    rewrite H1 in arand.
    refine (c (tfirstn H0 _) arand).
    linear_arithmetic.
  Defined.

  Definition bind_rands T eta (c : rands eta -> arands eta -> Comp T) : Comp T :=
    bind_tuple (curry_rands_func c).

  Lemma message_eq_dec : forall (m n : message), {m = n} + {m <> n}.
    intros.
    destruct m; destruct n.
    cases (x ==n x0).
    subst x.
    cases (Bvector_eq_dec b b0).
    subst b.
    left.
    congruence.
    right.
    intuition.
    right.
    congruence.
  Defined.

  (* TODO : Probably shouldn't need to explicitly set and unset here *)
  Unset Implicit Arguments.
  Record MessageComp :=
    mkMessageComp {
        message_comp : comp message;
        message_poly : admissible_oc cost (fun _ => unit) (fun _ => unit) (fun _ => message) (fun (eta : nat) =>
                                                                                                OC_Ret unit unit (bind_rands (message_comp eta)))
      }.

  Record BoolComp :=
    mkBoolComp {
        bool_comp : comp bool;
        bool_poly : admissible_oc cost (fun _ => unit) (fun _ => unit) (fun _ => bool) (fun (eta : nat) => OC_Ret unit unit (bind_rands (bool_comp eta)))
      }.
  Set Implicit Arguments.

  Definition CompDomain (s : SymbolicSort) : Type :=
    match s with
    | Message => MessageComp
    | Bool => BoolComp
    end.

  Ltac trivial_polynomial :=
    unfold polynomial; exists 0%nat; exists 0%nat; exists 0%nat; unfold expnat; simpl; intros; omega.

  Lemma constant_polytime : forall T (eq : eq_dec T) (b : T),
      admissible_oc cost (fun _ => unit) (fun _ => unit) (fun _ => T) (fun (eta : nat) => OC_Ret unit unit (bind_rands (fun _ : rands eta => fun _ : arands eta => Ret eq b))).
  Admitted.

  Definition constant_boolcomp (b : bool) : BoolComp :=
    mkBoolComp (fun _ _ _ => Ret bool_dec b) (constant_polytime bool_dec b).

  Definition constant_messagecomp (m : message) : MessageComp :=
    mkMessageComp (fun _ _ _ => Ret message_eq_dec m) (constant_polytime message_eq_dec m).

  Definition if_then_else_comp (b : comp bool) (m1 m2 : comp message) : comp message :=
    fun (eta : nat) =>
      fun (r : rands eta) =>
        fun (ar : arands eta) =>
      b' <-$ (b eta r ar);
        (if b' then m1 else m2) eta r ar.

  Definition if_then_else_poly: forall (b : BoolComp) (m1 m2 : MessageComp),
      admissible_oc cost (fun _ : nat => unit) (fun _ : nat => unit) (fun _ : nat => message)
                    (fun (eta : nat) => $ (bind_rands ((if_then_else_comp (bool_comp b) (message_comp m1) (message_comp m2)) eta))).
  Admitted.

  Definition if_then_else_messagecomp (b : BoolComp) (m1 m2 : MessageComp) : MessageComp :=
    mkMessageComp (if_then_else_comp b.(bool_comp) m1.(message_comp) m2.(message_comp)) (if_then_else_poly b m1 m2).

  Definition message_eq (m1 m2 : message) : bool.
    cases (message_eq_dec m1 m2).
    exact true.
    exact false.
  Defined.

  Definition EqDec_message : EqDec message.
    refine (Build_EqDec _ _).
    intros.
    cases (message_eq_dec x y).
    instantiate (1 := fun m1 m2 => message_eq m1 m2).
    split; simplify; try assumption.
    unfold message_eq.
    cases (message_eq_dec x y).
    trivial.
    contradiction.
    split; simplify; try assumption.
    unfold message_eq in H0.
    cases (message_eq_dec x y); try equality.
    equality.
  Defined.

  Definition eq_comp (m1 m2 : comp message) : comp bool.
    refine (fun (eta : nat) =>
              fun (r : rands eta) =>
                fun (ar : arands eta) =>
              m1' <-$ m1 eta r ar;
              m2' <-$ m2 eta r ar;
              ret (m1' ?= m2')).
    apply EqDec_message.
  Defined.

  Definition eq_poly: forall (m1 m2 : MessageComp),
      admissible_oc cost (fun _ : nat => unit) (fun _ : nat => unit) (fun _ : nat => bool)
                    (fun eta : nat => $ (bind_rands ((eq_comp (message_comp m1) (message_comp m2)) eta))).
  Admitted.

  Definition eq_boolcomp (m1 m2 : MessageComp) : BoolComp :=
    mkBoolComp (eq_comp m1.(message_comp) m2.(message_comp)) (eq_poly m1 m2).

  Definition eql_comp (m1 m2 : comp message) : comp bool.
    refine (fun (eta : nat) =>
              fun (r : rands eta) =>
                fun (ar : arands eta) =>
              m1' <-$ m1 eta r ar;
              m2' <-$ m2 eta r ar;
              ret _).
    destruct m1'; destruct m2'.
    exact (x ?= x0).
  Defined.

  Definition eql_poly: forall (m1 m2 : MessageComp),
      admissible_oc cost (fun _ : nat => unit) (fun _ : nat => unit) (fun _ : nat => bool)
                    (fun eta : nat => $ (bind_rands ((eql_comp (message_comp m1) (message_comp m2)) eta))).
  Admitted.

  Definition eql_boolcomp (m1 m2 : MessageComp) : BoolComp :=
    mkBoolComp (eql_comp m1.(message_comp) m2.(message_comp)) (eql_poly m1 m2).

  Definition name_comp (n : nat) (H' : n < rand_bound) : comp message.
    refine (fun (eta : nat) =>
              fun (r : rands eta) =>
                fun (ar : arands eta) =>
                ret (existT Bvector eta (tnth r H'))).
    exact EqDec_message.
  Defined.

  Definition name_poly: forall (n : nat) (H' : n < rand_bound),
      admissible_oc cost (fun _ : nat => unit) (fun _ : nat => unit) (fun _ : nat => message)
                    (fun eta : nat => $ (bind_rands ((name_comp H') eta))).
  Admitted.

  Definition name_messagecomp (n : nat) (H' : n < rand_bound) : MessageComp :=
    mkMessageComp (name_comp H') (name_poly H').

  (* Axiom TODO : forall {T : Type}, T. *)

  (* Definition interp_handles := forall (n : nat) (dom : list SymbolicSort) (cod : SymbolicSort) (h : hlist CompDomain dom), CompDomain cod. *)

  (* Definition CompInterpFunc dom cod (s : SymbolicFunc dom cod) (h : hlist CompDomain dom) (ih : interp_handles) : (CompDomain cod). *)
  (*   induction s. *)
  (*   (* STrue *) *)
  (*   - exact (constant_boolcomp true). *)
  (*   (* SFalse *) *)
  (*   - exact (constant_boolcomp false). *)
  (*   (* IfThenElse *) *)
  (*   - refine (if_then_else_messagecomp _ _ _). *)
  (*     inversion h. *)
  (*     exact X. *)
  (*     inversion h. *)
  (*     inversion X0. *)
  (*     exact X1. *)
  (*     inversion h. *)
  (*     inversion X0. *)
  (*     inversion X2. *)
  (*     exact X3. *)
  (*   (* EmptyMsg *) *)
  (*   - exact (constant_messagecomp (existT Bvector 0 Bnil)%nat). *)
  (*   (* Eq *) *)
  (*   - refine (eq_boolcomp _ _). *)
  (*     inversion h. *)
  (*     exact X. *)
  (*     inversion h. *)
  (*     inversion X0. *)
  (*     exact X1. *)
  (*   (* EqL *) *)
  (*   - refine (eql_boolcomp _ _). *)
  (*     inversion h. *)
  (*     exact X. *)
  (*     inversion h. *)
  (*     inversion X0. *)
  (*     exact X1. *)
  (*   (* Name *) *)
  (*   - exact (name_messagecomp l). *)
  (*   (* Handle *) *)
  (*   - exact (ih n dom cod h). *)
  (* Defined. *)


(* Definition indist_comp : bool. *)
(* Definition indist dom (l1 l2 : hlist CompDomain dom) : Prop. *)

(* Definition CompInterpPredicate dom (s : SymbolicPredicate dom) (h : hlist CompDomain dom) : Prop. *)
(*   induction s. *)
(* About model. *)
(* (* Definition CompModel := Model SymbolicSort SymbolicFunc SymbolicState *) *)

End CompInterp.

End Models.
