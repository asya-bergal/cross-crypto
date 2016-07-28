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

  Record MessageComp :=
    mkMessageComp {
        message_comp : nat -> Comp ({n : nat & Bvector n});
        message_poly : admissible_oc cost (fun _ => unit) (fun _ => unit) (fun _ => {n : nat & (Bvector n)}) (fun (eta : nat) => OC_Ret unit unit (message_comp eta))
      }.

  Lemma message_eq_dec : forall (m n : {n : nat & Bvector n}), {m = n} + {m <> n}.
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

  Definition names (n : nat) := fun (eta : nat) => Rnd eta.
  Definition anames (n : nat) := fun (eta : nat) => Rnd eta.

  Axiom TODO : forall {T : Type}, T.

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

    Definition constant_messagecomp (m : {n : nat & Bvector n}) : MessageComp :=
      mkMessageComp (fun _ => Ret message_eq_dec m) (constant_polytime message_eq_dec m).

  Definition CompInterpFunc dom cod (s : SymbolicFunc dom cod) (h : hlist CompDomain dom) : (CompDomain cod) :=
    match s with
      | STrue => constant_boolcomp true
      | SFalse => constant_boolcomp false
      | IfThenElse => TODO
      | EmptyMsg => constant_messagecomp (existT Bvector 0 Bnil)%nat
      | Eq => TODO
      | EqL => TODO
      | Name n => TODO
      | AttackerName n => TODO
    end.
          
  (* About Model. *)
  (* Definition CompModel := Model SymbolicSort SymbolicFunc SymbolicState *)

End CompInterp. 
