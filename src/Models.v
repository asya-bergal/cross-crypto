Set Implicit Arguments.
Unset Strict Implicit.

Require Import Coq.Lists.List.

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
Require Import CrossCrypto.Protocol.
Require Import CrossCrypto.Execution.

Import ListNotations.
Open Scope list_scope.

Section Models.

  Context (rand_bound : nat).
  Context (arand_bound : nat).

  Inductive SymbolicSort :=
  | Message : SymbolicSort
  | Bool : SymbolicSort.

  (* Finite bound on the number of random values
     you and the attacker will need. *)

  Context (handle_bound : nat).
  Context (handles : tuple (list SymbolicSort * SymbolicSort) handle_bound).

  (* Functions that we are required to define. *)
  (* Names are random values that are indexed by a nat *)
  (* Handles are functions of the attacker, also indexed by a nat *)

  Inductive SymbolicFunc : list SymbolicSort -> SymbolicSort -> Type :=
  | STrue : SymbolicFunc nil Bool
  | SFalse : SymbolicFunc nil Bool
  | IfThenElse : SymbolicFunc (Bool :: Message :: Message :: nil) Message
  | EmptyMsg : SymbolicFunc nil Message
  | Eq : SymbolicFunc (Message :: Message :: nil) Bool
  | EqL : SymbolicFunc (Message :: Message :: nil) Bool
  | Name : forall (n : nat), n < rand_bound -> (SymbolicFunc nil Message)
  | Handle : forall (n : nat) (H : n < handle_bound),
      SymbolicFunc (fst (tnth handles H)) (snd (tnth handles H)).

  (* Indistinguishability is defined on both messages and booleans *)
  Inductive SymbolicPredicate : list SymbolicSort -> Type :=
  | Indist : forall (l : list SymbolicSort), SymbolicPredicate (l ++ l).

  Section CompInterp.

    (* Our cost function should follow certain guidelines.  Certain of
       those guidelines are encoded in the class function_cost_model
       (e.g. composing functions).  Certain guidelines are given by the
       predicate "reasonable", which still needs to be filled in.
       "Reasonable" should encode that breaking a specified set of hard
       problems should not be possible in poly-time given our cost
       model. *)
    Context `{function_cost_model}.

    (* TODO: actual definition of reasonable *)
    Definition reasonable (cost : FunctionCostModel) := True.

    Context `{reasonable cost}.

    (* A message is a bitvector of any length *)
    Definition message := {n : nat & Bvector n}.

    (* Equality on messages is decidable *)
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

    Definition message_eq (m1 m2 : message) : bool :=
      if message_eq_dec m1 m2 then true else false.

    Hint Resolve message_eq_dec.
    Hint Resolve bool_dec.

    (* rands and arands are the types of the randomness that the *)
    (*    protocol and attacker have access to. They are tuples of exactly *)
    (*    the length of the predeclared randomness bound *)
    Definition rands (eta : nat) := tuple (Bvector eta) rand_bound.
    Definition arands (eta : nat) := tuple (Bvector eta) arand_bound.

    (* Utility function *)
    Definition curry_rands_func T eta
               (c : rands eta -> arands eta -> T)
      : tuple (Bvector eta) (rand_bound + arand_bound) -> T.
      intros t.
      pose proof (tskipn t rand_bound) as arand.
      replace (rand_bound + arand_bound - rand_bound) with arand_bound
        in arand by linear_arithmetic.
      refine (c (tfirstn t _) arand); linear_arithmetic.
    Defined.

    Definition bind_rands (T : Set) (T_dec : eq_dec T) eta
               (c : rands eta -> arands eta -> T) : Comp T :=
      bind_tuple T_dec (curry_rands_func c).

    Definition CompDomain (s : SymbolicSort) : Type :=
      match s with
      | Message => message
      | Bool => bool
      end.

    Definition bool_handle_poly A
               (handle : forall eta, arands eta -> hlist CompDomain A -> bool) : Prop.
    Admitted.

    (*   forall args : hlist CompDomain A, *)
    (*     poly_time (mk_comp_bool (wrap_handle handle args)). *)

    Definition message_handle_poly A
               (handle : forall eta, arands eta -> hlist CompDomain A -> message) : Prop.
    Admitted.
    (*   : Prop := *)
    (*   forall args : hlist CompDomain A, *)
    (*     poly_time (mk_comp_message (wrap_handle handle args)). *)

    (* Attackers are a generator of computations that are polynomial *)
    (*    time and only access attacker randomness. *)
    Definition bool_handle (dom : list SymbolicSort) :=
      { f : forall eta, arands eta -> hlist CompDomain dom -> bool |
        bool_handle_poly f }.

    Definition message_handle (dom : list SymbolicSort) :=
      { f : forall eta, arands eta -> hlist CompDomain dom -> message |
        message_handle_poly f }.

    Definition attacker := forall (n : nat) (H : n < handle_bound),
        match (snd (tnth handles H)) with
        | Message => message_handle (fst (tnth handles H))
        | Bool => bool_handle (fst (tnth handles H))
        end.

    (* TODO : Rewrite this prettier, split out cases *)
    Definition CompInterpFunc eta (r : rands eta) (ar : arands eta)
               (att : attacker) dom cod (f : SymbolicFunc dom cod)
               (args : hlist CompDomain dom) : CompDomain cod.
      induction f; simplify.
      (* True *)
      exact true.
      (* False *)
      exact false.
      (* If Then Else *)
      exact (if (hhead args) then (hhead (htail args)) else (hhead (htail (htail args)))).
      (* Empty Msg *)
      exact (existT Bvector 0 Bnil)%nat.
      (* Equal messages *)
      exact (message_eq (hhead args) (hhead (htail args))).
      (* Equal length messages *)
      exact (projT1 (hhead args) ?= projT1 (hhead (htail args))).
      (* Names *)
      exact (existT _ eta (tnth r l)).
      (* Handles *)
      cases (snd (tnth handles (i:=n) H0));
        simplify;
        refine ((proj1_sig _) _ _ _);
        pose proof (att n H0) as attack;
        rewrite Heq in attack.
      exact attack.
      exact args.
      exact attack.
      exact args.
      Unshelve.
      exact eta.
      exact ar.
      exact eta.
      exact ar.
    Defined.

    Definition CompInterpPredicate dom (p : SymbolicPredicate dom)
               (args : hlist CompDomain dom) : Prop :=
      match p with
      | Indist _ => False
      end.

    Definition CompProtocol := protocol Message STrue.

    (* Definition machine_outputs : forall (cp : CompProtocol) (m : model SymbolicFunc SymbolicPredicate), tuple (Message).  *)
    Definition indist (att : attacker) (attack : forall (trace : list SymbolicSort), bool_handle trace) (p1 p2 : CompProtocol): Prop.
      Admitted.

      (* refine (negligible (fun (eta : nat) => (|Pr[bind_rands bool_dec _] - Pr[bind_rands bool_dec _]|))). *)
      (* refine (fun (r : rands eta) (ar : arands eta) => _). *)
      (* refine (proj1_sig (attack _) _ _ _). *)
      (* exact ar. *)
      (* assert (model SymbolicFunc SymbolicPredicate) as fixed_model. *)
      (* refine (Model _ _). *)
      (* refine (CompInterpFunc r ar att). *)
      (* refine (CompInterpPredicate). *)
      (* pose proof (model_protocol_machine fixed_model p1) as fixed_machine. *)
      (* assert (transition_dec fixed_machine) as fixed_machine_dec. *)
      (* admit. *)
      (* pose proof (proj1_sig (exists_trace fixed_machine_dec)) as trace. *)


  End CompInterp.

End Models.
