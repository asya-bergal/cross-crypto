Set Implicit Arguments.

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
  | Handle : forall (n : nat) (dom : list SymbolicSort) (cod : SymbolicSort), SymbolicFunc dom cod.

  (* Indistinguishability is defined on both messages and booleans *)
  Inductive SymbolicPredicate : list SymbolicSort -> Type :=
    | Indist : forall (l : list SymbolicSort), SymbolicPredicate (l ++ l).

End SymbolicModel.

Require Import WC_PolyTime.
Require Import Admissibility.
Require Import Asymptotic.
Require Import FCF.

Require Import CrossCrypto.CompUtil.
Require Import CrossCrypto.FirstOrder.
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

  Definition poly_time T (c : comp T) :=
    admissible_oc cost (fun _ : nat => unit) (fun _ : nat => unit) (fun _ : nat => T)
                  (fun eta : nat => $ (bind_rands (c eta))).

  Ltac trivial_polynomial :=
    unfold polynomial; exists 0%nat; exists 0%nat; exists 0%nat; unfold expnat; simpl; intros; omega.

  Lemma constant_polytime : forall T (eq : eq_dec T) (b : T),
      poly_time (fun eta => (fun _ : rands eta => fun _ : arands eta => Ret eq b)).
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
      poly_time (if_then_else_comp (bool_comp b) (message_comp m1) (message_comp m2)).
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
      poly_time (eq_comp (message_comp m1) (message_comp m2)).
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
      poly_time (eql_comp (message_comp m1) (message_comp m2)).
  Admitted.

  Definition eql_boolcomp (m1 m2 : MessageComp) : BoolComp :=
    mkBoolComp (eql_comp m1.(message_comp) m2.(message_comp)) (eql_poly m1 m2).

  Definition name_comp (n : nat) (H' : n < rand_bound) : comp message.
    refine (fun (eta : nat) =>
              fun (r : rands eta) =>
                fun (_ : arands eta) =>
                ret (existT Bvector eta (tnth r H'))).
    exact EqDec_message.
  Defined.

  Definition name_poly: forall (n : nat) (H' : n < rand_bound),
      poly_time (fun eta => ((name_comp H') eta)).
  Admitted.

  Definition name_messagecomp (n : nat) (H' : n < rand_bound) : MessageComp :=
    mkMessageComp (name_comp H') (name_poly H').

  Definition arands_only T (c : comp T) :=
    exists c' : Comp T, c = fun (eta : nat) => fun (_ : rands eta) => fun (ar : arands eta) => c'.

  (* Attackers are a generator of computations that are polynomial time and only access attacker randomness. *)
  Definition attacker := forall (n : nat) T dom (args : hlist CompDomain dom),
      {c : comp T | poly_time c & arands_only c}.

  Definition interp_handle dom cod (att : attacker) (n : nat) (args : hlist CompDomain dom) : CompDomain cod :=
  match cod as s return (CompDomain s) with
  | Message => let attacker_sig := (sig_of_sig2 (att n message dom args)) in
      mkMessageComp (proj1_sig attacker_sig) (proj2_sig attacker_sig)
  | Bool => let attacker_sig := (sig_of_sig2 (att n bool dom args)) in
      mkBoolComp (proj1_sig attacker_sig) (proj2_sig attacker_sig)
  end.

  Definition CompInterpFunc (att : attacker) dom cod (f : SymbolicFunc dom cod) (args : hlist CompDomain dom) : (CompDomain cod).
    induction f.
    (* STrue *)
    - exact (constant_boolcomp true).
    (* SFalse *)
    - exact (constant_boolcomp false).
    (* IfThenElse *)
    - refine (if_then_else_messagecomp _ _ _).
      inversion args.
      exact X.
      inversion args.
      inversion X0.
      exact X1.
      inversion args.
      inversion X0.
      inversion X2.
      exact X3.
    (* EmptyMsg *)
    - exact (constant_messagecomp (existT Bvector 0 Bnil)%nat).
    (* Eq *)
    - refine (eq_boolcomp _ _).
      inversion args.
      exact X.
      inversion args.
      inversion X0.
      exact X1.
    (* EqL *)
    - refine (eql_boolcomp _ _).
      inversion args.
      exact X.
      inversion args.
      inversion X0.
      exact X1.
    (* Name *)
    - exact (name_messagecomp l).
    (* Handle *)
    - exact (interp_handle cod att n args).
  Defined.

Definition indist_comp := forall dom, hlist CompDomain dom -> comp bool.

(* TODO: Do we need to somehow bind_rands outside of the probability statement? I don't think so... *)
Definition indist dom (l1 l2 : hlist CompDomain dom) : Prop :=
  forall (f : indist_comp), poly_time (f dom l1) 
                       -> poly_time (f dom l2)
                       -> arands_only (f dom l1)
                       -> arands_only (f dom l2)
                       -> negligible (fun (eta : nat) => (| Pr[bind_rands (f dom l1 eta)] - Pr[bind_rands (f dom l2 eta)]|)).

Lemma firstn_concat : forall A (l : list A) (l' : list A), firstn (length l) (l ++ l') = l.
  induction l; intros; simplify; equality.
Qed.

Lemma skipn_concat : forall A (l : list A) (l' : list A), skipn (length l) (l ++ l') = l'.
  induction l; intros; simplify; equality.
Qed.

Lemma listdup_split : forall A (l : list A), firstn (length l) (l ++ l) = skipn (length l) (l ++ l).
  repeat intros.
  rewrite (firstn_concat l l).
  rewrite (skipn_concat l l).
  equality.
Qed.

Definition CompInterpPredicate dom (p : SymbolicPredicate dom) (args : hlist CompDomain dom) : Prop.
  induction p.
  (* assert (firstn (length l) (l ++ l) = skipn (length l) (l ++ l)). *)
  refine (indist (hfirstn (length l) args) _).
  rewrite listdup_split.
  exact (hskipn (length l) args).
Defined.

Definition CompModel (att : attacker) : model SymbolicFunc SymbolicPredicate :=
  Model (CompInterpFunc att) CompInterpPredicate.

End CompInterp.

End Models.
