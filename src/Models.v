Set Implicit Arguments.

Require Import Coq.Lists.List.
Import ListNotations.

Section Models.

  (* Finite bound on the number of random values
     you and the attacker will need. *)
  Context (rand_bound : nat).
  Context (arand_bound : nat).

  Section SymbolicModel.

    Inductive SymbolicSort :=
    | Message : SymbolicSort
    | Bool : SymbolicSort.

    (* Functions that we are required to define. *)
    (* Names are random values that are indexed by a nat *)
    (* Handles are functions of the attacker, also indexed by a nat *)
    Inductive SymbolicFunc : list SymbolicSort -> SymbolicSort -> Type :=
    | STrue : SymbolicFunc [] Bool
    | SFalse : SymbolicFunc [] Bool
    | IfThenElse : SymbolicFunc (Bool :: Message :: Message :: []) Message
    | EmptyMsg : SymbolicFunc [] Message
    | Eq : SymbolicFunc (Message :: Message :: []) Bool
    | EqL : SymbolicFunc (Message :: Message :: []) Bool
    | Name : forall (n : nat), n < rand_bound -> (SymbolicFunc [] Message)
    | Handle : forall (n : nat) (dom : list SymbolicSort) (cod : SymbolicSort),
        SymbolicFunc dom cod.

    (* Indistinguishability is defined on both messages and booleans *)
    Inductive SymbolicPredicate : list SymbolicSort -> Type :=
    | Indist : forall (l : list SymbolicSort), SymbolicPredicate (l ++ l).

  End SymbolicModel.

  Require Import Admissibility.
  Require Import Asymptotic.
  Require Import FCF.
  Require Import WC_PolyTime.

  Require Import CrossCrypto.CompUtil.
  Require Import CrossCrypto.FirstOrder.
  Require Import CrossCrypto.FrapTactics.
  Require Import CrossCrypto.HList.
  Require Import CrossCrypto.ListUtil.
  Require Import CrossCrypto.Tuple.

  Section CompInterp.

    (* Our cost function should follow certain guidelines. Certain of those guidelines are encoded in the class function_cost_model (e.g. composing functions). Certain guidelines are given by the predicate "reasonable", which still needs to be filled in. "Reasonable" should encode that breaking a specified set of hard problems should not be possible in poly-time given our cost model. *)
    Context `{function_cost_model}.

    (* TODO: actual definition of reasonable *)
    Definition reasonable (cost : FunctionCostModel) := True.

    Context `{reasonable cost}.

    (* A message is a bitvector of any length *)
    Definition message := {n : nat & Bvector n}.

    (* rands and arands are the types of the randomness that the protocol and attacker have access to. They are tuples of exactly the length of the predeclared randomness bound*)
    Definition rands (eta : nat) := tuple (Bvector eta) rand_bound.
    Definition arands (eta : nat) := tuple (Bvector eta) arand_bound.

    (* In the paper, Turing machines take as inputs the security parameter, and two tapes containing randomness for the protocol and attacker, and output some value. Accordingly, our "comp" is a function from a security parameter and two sets of randomness to a distribution on some value. *)
    Definition comp (S : Set) := forall (eta : nat), rands eta -> arands eta -> Comp S.

    (* Utility function *)
    Definition curry_rands_func T eta (c : rands eta -> arands eta -> Comp T)
      : tuple (Bvector eta) (rand_bound + arand_bound) -> Comp T.
      intros t.
      pose proof (tskipn t rand_bound) as arand.
      replace (rand_bound + arand_bound - rand_bound) with arand_bound
        in arand by linear_arithmetic.
      refine (c (tfirstn t _) arand); linear_arithmetic.
    Defined.

    (* In order to use random values, we have to bind them in a function that produces a Comp. bind_rands generates random values and binds them to such a funcion and returns a Comp. *)
    Definition bind_rands T eta (c : rands eta -> arands eta -> Comp T)
      : Comp T :=
      bind_tuple (curry_rands_func c).

    (* Equality on messages is decideable *)
    Lemma message_eq_dec : forall (m n : message), {m = n} + {m <> n}.
      intros m m'.
      destruct m as [n m]; destruct m' as [n' m'].
      cases (n ==n n').
      - subst n'.
        cases (Bvector_eq_dec m m').
        + subst m'.
          left; congruence.
        + right; intuition.
      - right; congruence.
    Defined.

    Definition poly_time T (c : comp T) :=
      admissible_oc cost
                    (fun _ : nat => unit)
                    (fun _ : nat => unit)
                    (fun _ : nat => T)
                    (fun eta : nat => $ (bind_rands (c eta))).

    (* Both domain-types are computations along with proofs that the computations are poly-time. *)
    Definition MessageComp := {c : comp message | poly_time c}.
    Definition BoolComp := {c : comp bool | poly_time c}.

    Definition CompDomain (s : SymbolicSort) : Type :=
      match s with
      | Message => MessageComp
      | Bool => BoolComp
      end.

    (* Defining constant functions that just return a constant and their poly_time proofs. *)
    Lemma constant_polytime : forall T (eq : eq_dec T) (b : T),
        poly_time (fun eta => (fun _ : rands eta => fun _ : arands eta => Ret eq b)).
    Admitted.

    Definition constant_boolcomp (b : bool) : BoolComp :=
      exist (fun c : comp bool => poly_time c)
            (fun (eta : nat) (_ : rands eta) (_ : arands eta) => Ret bool_dec b)
            (constant_polytime bool_dec b).

    Definition constant_messagecomp (m : message) : MessageComp :=
      exist (fun c : comp message => poly_time c)
            (fun (eta : nat) (_ : rands eta) (_ : arands eta) => Ret message_eq_dec m)
            (constant_polytime message_eq_dec m).

    (* Defining several functions and their poly_time proofs. *)

    (* If then else *)
    Definition if_then_else_comp (b : comp bool) (m1 m2 : comp message)
      : comp message :=
      fun (eta : nat) (r : rands eta) (ar : arands eta) =>
        b' <-$ (b eta r ar);
          (if b' then m1 else m2) eta r ar.

    Definition if_then_else_poly: forall (b : BoolComp) (m1 m2 : MessageComp),
        poly_time (if_then_else_comp (proj1_sig b) (proj1_sig m1) (proj1_sig m2)).
    Admitted.

    Definition if_then_else_messagecomp (b : BoolComp) (m1 m2 : MessageComp) : MessageComp :=
      exist (fun c : comp message => poly_time c)
            (if_then_else_comp (proj1_sig b) (proj1_sig m1) (proj1_sig m2))
            (if_then_else_poly b m1 m2).

    (* Message equality proofs *)
    Definition message_eq (m1 m2 : message) : bool :=
      if message_eq_dec m1 m2 then true else false.

    Definition EqDec_message : EqDec message.
      refine (Build_EqDec message_eq _).
      unfold message_eq.
      intros x y.
      destruct (message_eq_dec x y); intuition.
    Defined.

    (* Equality of two messages *)
    Definition eq_comp (m1 m2 : comp message) : comp bool.
      refine (fun (eta : nat) (r : rands eta) (ar : arands eta) =>
                m1' <-$ m1 eta r ar;
                m2' <-$ m2 eta r ar;
                ret (m1' ?= m2')).
      apply EqDec_message.
    Defined.
    Definition eq_poly: forall (m1 m2 : MessageComp),
        poly_time (eq_comp (proj1_sig m1) (proj1_sig m2)).
    Admitted.

    Definition eq_boolcomp (m1 m2 : MessageComp) : BoolComp :=
      exist (fun c : comp bool => poly_time c)
            (eq_comp (proj1_sig m1) (proj1_sig m2))
            (eq_poly m1 m2).

    (* Equal length between two messages *)
    Definition eql_comp (m1 m2 : comp message) : comp bool.
      refine (fun (eta : nat) (r : rands eta) (ar : arands eta) =>
                m1' <-$ m1 eta r ar;
                m2' <-$ m2 eta r ar;
                ret _).

      destruct m1' as [x1 _]; destruct m2' as [x2 _].
      exact (x1 ?= x2).
    Defined.

    Definition eql_poly: forall (m1 m2 : MessageComp),
        poly_time (eql_comp (proj1_sig m1) (proj1_sig m2)).
    Admitted.

    Definition eql_boolcomp (m1 m2 : MessageComp) : BoolComp :=
      exist (fun c : comp bool => poly_time c)
            (eql_comp (proj1_sig m1) (proj1_sig m2))
            (eql_poly m1 m2).

    (* We interpret a name by pulling out the nth value from the list of names that we pass around *)
    Definition name_comp (n : nat) (H' : n < rand_bound) : comp message.
      refine (fun (eta : nat) (r : rands eta) (_ : arands eta) =>
                ret (existT Bvector eta (tnth r H'))).
      exact EqDec_message.
    Defined.

    Definition name_poly: forall (n : nat) (H' : n < rand_bound),
        poly_time (fun eta => ((name_comp H') eta)).
    Admitted.

    Definition name_messagecomp (n : nat) (H' : n < rand_bound) : MessageComp :=
      exist (fun c : comp message => poly_time c)
            (name_comp H')
            (name_poly H').

    (* Predicate that says a function uses only the attacker randomness passed to it *)
    Definition arands_only T (c : comp T) :=
      exists c' : forall eta : nat, arands eta -> Comp T,
        c = fun eta _ ar => c' eta ar.

    (* Attackers are a generator of computations that are polynomial time and only access attacker randomness. *)
    Definition attacker := forall (n : nat) T dom
                             (args : hlist CompDomain dom),
        {c : comp T | poly_time c & arands_only c}.

    (* To interpet a handle we simply pass the relevant arguments to the attacker *)
    Definition interp_handle dom cod (att : attacker) (n : nat)
               (args : hlist CompDomain dom) : CompDomain cod :=
      match cod as s return (CompDomain s) with
      | Message => let attacker_sig := sig_of_sig2 (att n message dom args) in
                  exist (fun c : comp message => poly_time c) (proj1_sig attacker_sig) (proj2_sig attacker_sig)
      | Bool => let attacker_sig := (sig_of_sig2 (att n bool dom args)) in
               exist (fun c : comp bool => poly_time c) (proj1_sig attacker_sig) (proj2_sig attacker_sig)
      end.

    (* Definition of interpreting a function in our Computational Model, parametrized over an attacker who interprets attacker functions. The definition is written in proof mode because dependent matches are too icky *)
    Definition CompInterpFunc (att : attacker) dom cod
               (f : SymbolicFunc dom cod) (args : hlist CompDomain dom)
      : (CompDomain cod).
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

    (* The type of a computation which takes arguments and returns some bool *)
    Definition bool_comp := forall dom, hlist CompDomain dom -> comp bool.

    (* Two hlists are indistinguishable if for any poly-time attacker computation which takes in arguments and returns a bool, there is a negligible probability that the attacker gets different bools. *)
    Definition indist dom (l1 l2 : hlist CompDomain dom) : Prop :=
      forall (f : bool_comp),
        poly_time (f dom l1)
        -> poly_time (f dom l2)
        -> arands_only (f dom l1)
        -> arands_only (f dom l2)
        -> negligible (fun (eta : nat) =>
                        (| Pr[bind_rands (f dom l1 eta)] -
                           Pr[bind_rands (f dom l2 eta)]|)).

    (* Define the computational interpretation of predicates, which right now is only indistinguishability *)
    Definition CompInterpPredicate dom (p : SymbolicPredicate dom)
               (args : hlist CompDomain dom) : Prop.
      induction p.
      refine (indist (hfirstn (length l) args) _).
      rewrite listdup_split.
      exact (hskipn (length l) args).
    Defined.

    (* Finally, define our computational model, which is parametrized by our attacker. *)
    Definition CompModel (att : attacker)
      : model SymbolicFunc SymbolicPredicate :=
      Model (CompInterpFunc att) CompInterpPredicate.

  End CompInterp.

End Models.
