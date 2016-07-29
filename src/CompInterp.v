Set Implicit Arguments.

Require Import WC_PolyTime.
Require Import Admissibility.
Require Import FCF.
Require Import Asymptotic.
Require Import CrossCrypto.FrapTactics.
Require Import CrossCrypto.FirstOrder.
Require Import CrossCrypto.SymbolicModel.
Require Import CrossCrypto.HList.
Require Import Coq.Lists.List.
Import ListNotations.

Section CompInterp.

  Context `{function_cost_model}.
  (* TODO: actual definition of reasonable *)
  Definition reasonable (cost : FunctionCostModel) := True.
  
  Context `{reasonable cost}.

  Definition message := {n : nat & Bvector n}.

  Record MessageComp :=
    mkMessageComp {
        message_comp : nat -> Comp message;
        message_poly : admissible_oc cost (fun _ => unit) (fun _ => unit) (fun _ => message) (fun (eta : nat) => OC_Ret unit unit (message_comp eta))
      }.

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

  Record BoolComp :=
    mkBoolComp {
        bool_comp : nat -> Comp bool;
        bool_poly : admissible_oc cost (fun _ => unit) (fun _ => unit) (fun _ => bool) (fun (eta : nat) => OC_Ret unit unit (bool_comp eta))
      }.

  Definition CompDomain (s : SymbolicSort) : Type :=
    match s with
    | Message => MessageComp
    | Bool => BoolComp
    end.

  Ltac trivial_polynomial :=
    unfold polynomial; exists 0%nat; exists 0%nat; exists 0%nat; unfold expnat; simpl; intros; omega.
  
  Lemma constant_polytime : forall T (eq : eq_dec T) (b : T),
      admissible_oc cost (fun _ => unit) (fun _ => unit) (fun _ => T) (fun (eta : nat) => OC_Ret unit unit (Ret eq b)).
  Proof.
    intros.
    unfold admissible_oc.
    split.
    - intros; try repeat constructor.
    - unfold poly_time_nonuniform_oc.
      split.
      exists (fun _ => fun _ => 0%nat).
      + split; intros; simpl.
        trivial_polynomial.
        repeat constructor.
      + unfold polynomial_queries_oc.
        exists (fun _ => 0%nat).
        split.
        trivial_polynomial.
        intros.
        constructor.
  Qed.

  Definition constant_boolcomp (b : bool) : BoolComp :=
    mkBoolComp (fun _ => Ret bool_dec b) (constant_polytime bool_dec b).

  Definition constant_messagecomp (m : message) : MessageComp :=
    mkMessageComp (fun _ => Ret message_eq_dec m) (constant_polytime message_eq_dec m).

  Definition if_then_else_comp (b : nat -> Comp bool) (m1 m2 : nat -> Comp message) : nat -> Comp message :=
    fun (eta : nat) =>
      b' <-$ b eta;
        (if b' then m1 else m2) eta.

  Definition if_then_else_poly: forall (b : BoolComp) (m1 m2 : MessageComp), 
      admissible_oc cost (fun _ : nat => unit) (fun _ : nat => unit) (fun _ : nat => message)
                    (fun eta : nat => $ if_then_else_comp (bool_comp b) (message_comp m1) (message_comp m2) eta).
  Admitted.

  Definition if_then_else_messagecomp (b : BoolComp) (m1 m2 : MessageComp) : MessageComp :=
    mkMessageComp (if_then_else_comp b.(bool_comp) m1.(message_comp) m2.(message_comp)) (if_then_else_poly b m1 m2).

  Definition message_eq (m1 m2 : message) : bool.
    cases (message_eq_dec m1 m2).
    exact true.
    exact false.
  Defined.

  Definition EqDec_message : EqDec message.
    Print EqDec.
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

  Definition eq_comp (m1 m2 : nat -> Comp message) : nat -> Comp bool.
    refine (fun (eta : nat) =>
              m1' <-$ m1 eta;
              m2' <-$ m2 eta;
              ret (m1' ?= m2')).
    apply EqDec_message.
  Defined.

  Definition eq_poly: forall (m1 m2 : MessageComp), 
      admissible_oc cost (fun _ : nat => unit) (fun _ : nat => unit) (fun _ : nat => bool)
                    (fun eta : nat => $ eq_comp (message_comp m1) (message_comp m2) eta).
  Admitted.

  Definition eq_boolcomp (m1 m2 : MessageComp) : BoolComp :=
    mkBoolComp (eq_comp m1.(message_comp) m2.(message_comp)) (eq_poly m1 m2).

  Definition eql_comp (m1 m2 : nat -> Comp message) : nat -> Comp bool.
    refine (fun (eta : nat) =>
              m1' <-$ m1 eta;
              m2' <-$ m2 eta;
              ret _).
    destruct m1'; destruct m2'.
    exact (x ?= x0).
  Defined.

  Definition eql_poly: forall (m1 m2 : MessageComp), 
      admissible_oc cost (fun _ : nat => unit) (fun _ : nat => unit) (fun _ : nat => bool)
                    (fun eta : nat => $ eql_comp (message_comp m1) (message_comp m2) eta).
  Admitted.

  Definition eql_boolcomp (m1 m2 : MessageComp) : BoolComp :=
    mkBoolComp (eql_comp m1.(message_comp) m2.(message_comp)) (eql_poly m1 m2).

  Definition names (n : nat) := fun (eta : nat) => Rnd eta.
  Definition anames (n : nat) := fun (eta : nat) => Rnd eta.

  Axiom TODO : forall {T : Type}, T.

  Definition CompInterpFunc dom cod (s : SymbolicFunc dom cod) (h : hlist CompDomain dom) : (CompDomain cod).
    induction s.
    (* STrue *)
    - exact (constant_boolcomp true).
    (* SFalse *)
    - exact (constant_boolcomp false).
    (* IfThenElse *)
    - refine (if_then_else_messagecomp _ _ _).
      inversion h.
      exact X.
      inversion h.
      inversion X0.
      exact X1.
      inversion h.
      inversion X0.
      inversion X2.
      exact X3.
    (* EmptyMsg *)
    - exact (constant_messagecomp (existT Bvector 0 Bnil)%nat).
    (* Eq *)
    - refine (eq_boolcomp _ _).
      inversion h.
      exact X.
      inversion h.
      inversion X0.
      exact X1.
    (* EqL *)
    - refine (eql_boolcomp _ _).
      inversion h.
      exact X.
      inversion h.
      inversion X0.
      exact X1.
    - exact TODO.
    - exact TODO.
  Defined.

(* About Model. *)
(* Definition CompModel := Model SymbolicSort SymbolicFunc SymbolicState *)

End CompInterp. 
