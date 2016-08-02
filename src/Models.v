Set Implicit Arguments.

Require Import CrossCrypto.FirstOrder.
Require Import Coq.Lists.List.
Import ListNotations.

Section Models.

  (* Finite bound on the number of random values you will need. *)
  Context (rand_bound : nat).

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
  | Name : forall (n : nat), n < rand_bound -> (SymbolicFunc [] Message).

  (* Indistinguishability is defined on both messages and booleans *)
  Inductive SymbolicPredicate : list SymbolicSort -> Type :=
    | Indist : forall (s : SymbolicSort), SymbolicPredicate (s :: s :: []).

End SymbolicModel.

Require Import WC_PolyTime.
Require Import Admissibility.
Require Import Asymptotic.
Require Import FCF.

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
  Definition comp (S : Set) := forall (eta : nat), rands eta -> Comp S.

  (* TODO : Clean up the following two definitions *)
  Fixpoint rand_tuple' T {eta : nat} {n : nat} (f : tuple (Bvector eta) n -> Comp T) (i : nat) (_: i < n) {struct i} : tuple (Bvector eta) (n - i) -> Comp T.
    cases i.
    assert (n - 0 = n).
    intuition.
    rewrite H1.
    exact f.
    refine (fun (t : tuple (Bvector eta) (n - S i)) => Bind (Rnd eta) (fun (b : Bvector eta) => (rand_tuple' T eta n f i _ _))).
    omega.
    assert (n - i = S (n - S i)).
    omega.
    rewrite H1.
    exact (b t:: t).
  Defined.

  Definition rand_tuple T {eta : nat} {n : nat} (f : tuple (Bvector eta) n -> Comp T) : Comp T.
    cases n.
    exact (f t[]).
    refine (Bind (Rnd eta) (fun (b : Bvector eta) => rand_tuple' f _ _)).
    instantiate (1 := n).
    omega.
    assert (S n - n = 1%nat).
    omega.
    rewrite H0.
    exact (b t:: t[]).
  Defined.

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
                                                                                                OC_Ret unit unit (rand_tuple (message_comp eta)))
      }.

  Record BoolComp :=
    mkBoolComp {
        bool_comp : comp bool;
        bool_poly : admissible_oc cost (fun _ => unit) (fun _ => unit) (fun _ => bool) (fun (eta : nat) => OC_Ret unit unit (rand_tuple (bool_comp eta)))
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
      admissible_oc cost (fun _ => unit) (fun _ => unit) (fun _ => T) (fun (eta : nat) => OC_Ret unit unit (rand_tuple (fun _ : rands eta => Ret eq b))).
  Admitted.

  Definition constant_boolcomp (b : bool) : BoolComp :=
    mkBoolComp (fun _ => fun _ => Ret bool_dec b) (constant_polytime bool_dec b).

  Definition constant_messagecomp (m : message) : MessageComp :=
    mkMessageComp (fun _ => fun _ => Ret message_eq_dec m) (constant_polytime message_eq_dec m).

  Definition if_then_else_comp (b : comp bool) (m1 m2 : comp message) : comp message :=
    fun (eta : nat) =>
      fun (r : rands eta) =>
      b' <-$ (b eta r);
        (if b' then m1 else m2) eta r.

  Definition if_then_else_poly: forall (b : BoolComp) (m1 m2 : MessageComp),
      admissible_oc cost (fun _ : nat => unit) (fun _ : nat => unit) (fun _ : nat => message)
                    (fun (eta : nat) => $ (rand_tuple ((if_then_else_comp (bool_comp b) (message_comp m1) (message_comp m2)) eta))).
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
              m1' <-$ m1 eta r;
              m2' <-$ m2 eta r;
              ret (m1' ?= m2')).
    apply EqDec_message.
  Defined.

  Definition eq_poly: forall (m1 m2 : MessageComp),
      admissible_oc cost (fun _ : nat => unit) (fun _ : nat => unit) (fun _ : nat => bool)
                    (fun eta : nat => $ (rand_tuple ((eq_comp (message_comp m1) (message_comp m2)) eta))).
  Admitted.

  Definition eq_boolcomp (m1 m2 : MessageComp) : BoolComp :=
    mkBoolComp (eq_comp m1.(message_comp) m2.(message_comp)) (eq_poly m1 m2).

  Definition eql_comp (m1 m2 : comp message) : comp bool.
    refine (fun (eta : nat) =>
              fun (r : rands eta) =>
              m1' <-$ m1 eta r;
              m2' <-$ m2 eta r;
              ret _).
    destruct m1'; destruct m2'.
    exact (x ?= x0).
  Defined.

  Definition eql_poly: forall (m1 m2 : MessageComp),
      admissible_oc cost (fun _ : nat => unit) (fun _ : nat => unit) (fun _ : nat => bool)
                    (fun eta : nat => $ (rand_tuple ((eql_comp (message_comp m1) (message_comp m2)) eta))).
  Admitted.

  Definition eql_boolcomp (m1 m2 : MessageComp) : BoolComp :=
    mkBoolComp (eql_comp m1.(message_comp) m2.(message_comp)) (eql_poly m1 m2).

  Definition name_comp (n : nat) (H' : n < rand_bound) : comp message.
    refine (fun (eta : nat) =>
              fun (r : rands eta) =>
                ret (existT Bvector eta (tnth r H'))).
    exact EqDec_message.
  Defined.

  Definition name_poly: forall (n : nat) (H' : n < rand_bound),
      admissible_oc cost (fun _ : nat => unit) (fun _ : nat => unit) (fun _ : nat => message)
                    (fun eta : nat => $ (rand_tuple ((name_comp H') eta))).
  Admitted.

  Definition name_messagecomp (n : nat) (H' : n < rand_bound) : MessageComp :=
    mkMessageComp (name_comp H') (name_poly H').

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
    - exact (name_messagecomp l).
  Defined.

(* About Model. *)
(* Definition CompModel := Model SymbolicSort SymbolicFunc SymbolicState *)

End CompInterp.

End Models.
