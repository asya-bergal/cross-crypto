Set Implicit Arguments.

Add LoadPath "../fcf/src/FCF".
Require Import WC_PolyTime.
Require Import Admissibility.
Require Import FCF.
Require Import Asymptotic.
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

  Record PolyComp (n : nat) :=
    mkPolyComp {
        comp : nat -> Comp (Bvector n);
        poly : admissible_oc cost (fun _ => unit) (fun _ => unit) (fun _ => (Bvector n)) (fun (eta : nat) => OC_Ret unit unit (comp eta))
      }.

  Definition CompDomain (s : SymbolicSort) : Type :=
    match s with
    | Message => {n : nat & PolyComp n}
    | Bool => PolyComp 1
    end.

  Definition names (n : nat) := fun (eta : nat) => Rnd eta.
  Definition anames (n : nat) := fun (eta : nat) => Rnd eta.

  Axiom TODO : forall {T : Type}, T.

  (* Definition true_comp := Ret (@Bvector_eq_dec 1) (Bvect_true 1). *)
  (* Definition false_comp := Ret (@Bvector_eq_dec 1) (Bvect_false 1). *)

  Ltac trivial_polynomial :=
    unfold polynomial; exists 0%nat; exists 0%nat; exists 0%nat; unfold expnat; simpl; intros; omega.
    
  (* All computations that are simply constants are polytime *)
  Lemma constant_polytime : forall n (b : Bvector n),
      admissible_oc cost (fun _ => unit) (fun _ => unit) (fun _ => (Bvector n)) (fun (eta : nat) => OC_Ret unit unit (Ret (@Bvector_eq_dec n) b)).
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

    Definition mk_constant_polycomp {n} (b : Bvector n) : PolyComp n.
      refine (mkPolyComp (fun _ => Ret (@Bvector_eq_dec n) b) _ ).
      apply constant_polytime.
    Defined.

  Definition CompInterpFunc dom cod (s : SymbolicFunc dom cod) (h : hlist CompDomain dom) : (CompDomain cod) :=
    match s with
      | STrue => mk_constant_polycomp (Bvect_true 1)
      | SFalse => mk_constant_polycomp (Bvect_false 1)
      | IfThenElse => TODO
      | EmptyMsg => TODO
      | Eq => TODO
      | EqL => TODO
      | Name n => TODO
      | AttackerName n => TODO
    end.
          
  (* About Model. *)
  (* Definition CompModel := Model SymbolicSort SymbolicFunc SymbolicState *)

End CompInterp. 
