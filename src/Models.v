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

    Hint Resolve message_eq_dec.
    Hint Resolve bool_dec.
    (* rands and arands are the types of the randomness that the
       protocol and attacker have access to. They are tuples of exactly
       the length of the predeclared randomness bound*)
    Definition rands (eta : nat) := tuple (Bvector eta) rand_bound.
    Definition arands (eta : nat) := tuple (Bvector eta) arand_bound.

    (* In the paper, Turing machines take as inputs the security
       parameter, and two tapes containing randomness for the protocol
       and attacker, and output some value. Accordingly, our "comp" is a
       function from a security parameter and two sets of randomness to
       a value. *)
    Record comp (S : Set) :=
      mk_comp {S_dec : eq_dec S;
               comp_fun :> forall eta, rands eta -> arands eta -> S
              }.

    Definition mk_comp_message f := mk_comp message_eq_dec f.
    Definition mk_comp_bool f := mk_comp bool_dec f.

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

    (* In order to use random values, we have to bind them in a function
       that produces a Comp. bind_rands generates random values and
       binds them to such a funcion and returns a Comp. *)
    Definition bind_rands (T : Set) (T_dec : eq_dec T) eta
               (c : rands eta -> arands eta -> T) : Comp T :=
      bind_tuple T_dec (curry_rands_func c).

    (* Both domain-types are computations along with proofs that the
       computations are poly-time. *)

    (* Definition poly_time (A B : nat -> Type) (f : forall (eta : nat), A eta -> B eta) := *)
    (*   exists (f' : nat -> nat), *)
    (*     polynomial f' /\ *)
    (*     forall n, cost (f n) (f' n). *)
                
    Definition poly_time T (c : comp T) :=
      exists (f : nat -> nat), 
          polynomial f /\
        forall n, comp_cost cost (bind_rands c.(S_dec) (c n)) (f n).

    Record MessageComp :=
      mkMessageComp {
          message_comp : comp message;
          message_poly : poly_time message_comp
        }.

    Record BoolComp :=
      mkBoolComp {
          bool_comp : comp bool;
          bool_poly : poly_time bool_comp
        }.

    Arguments mkBoolComp {bool_comp} bool_poly.

    Definition CompDomain (s : SymbolicSort) : Type :=
      match s with
      | Message => MessageComp
      | Bool => BoolComp
      end.

    Definition dom2type (s : SymbolicSort) :=
      match s with
      | Message => message
      | Bool => bool
      end.

    (* Defining constant functions that just return a constant and their
       poly_time proofs. *)
    Lemma constant_polytime : forall T (T_dec : eq_dec T) (b : T),
        @poly_time T (mk_comp T_dec (fun _ _ _ => b)).
    Admitted.

    Definition constant_boolcomp (b : bool) : BoolComp :=
      mkBoolComp (constant_polytime bool_dec b).

    Definition constant_messagecomp (m : message) : MessageComp :=
      mkMessageComp (constant_polytime message_eq_dec m).

    (* Defining several functions and their poly_time proofs. *)

    (* If then else *)
    Definition if_then_else_comp (b : comp bool)
               (m1 m2 : comp message)
      : comp message :=
      mk_comp_message (fun (eta : nat) (r : rands eta) (ar : arands eta) =>
                         let b' := (b eta r ar) in
                         (if b' then m1 else m2) eta r ar).

    Definition if_then_else_poly : forall (b : BoolComp) (m1 m2 : MessageComp),
        poly_time (if_then_else_comp (bool_comp b)
                                     (message_comp m1)
                                     (message_comp m2)).
    Admitted.

    Definition if_then_else_messagecomp (b : BoolComp) (m1 m2 : MessageComp)
      : MessageComp :=
      mkMessageComp (if_then_else_poly b m1 m2).

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
      refine (mk_comp_bool
                (fun (eta : nat) (r : rands eta) (ar : arands eta) =>
                   let m1' := m1 eta r ar in
                   let m2' := m2 eta r ar in
                   m1' ?= m2')).
      apply EqDec_message.
    Defined.

    Definition eq_poly: forall (m1 m2 : MessageComp),
        poly_time (eq_comp (message_comp m1) (message_comp m2)).
    Admitted.

    Definition eq_boolcomp (m1 m2 : MessageComp) : BoolComp :=
      mkBoolComp (eq_poly m1 m2).

    (* Equal length between two messages *)
    Definition eql_comp (m1 m2 : comp message) : comp bool.
      refine (mk_comp_bool
                (fun (eta : nat) (r : rands eta) (ar : arands eta) =>
                   let m1' := m1 eta r ar in
                   let m2' := m2 eta r ar in
                   _)).

      destruct m1' as [x1 _]; destruct m2' as [x2 _].
      exact (x1 ?= x2).
    Defined.

    Definition eql_poly: forall (m1 m2 : MessageComp),
        poly_time (eql_comp (message_comp m1) (message_comp m2)).
    Admitted.

    Definition eql_boolcomp (m1 m2 : MessageComp) : BoolComp :=
      mkBoolComp (eql_poly m1 m2).

    (* We interpret a name by pulling out the nth value from the list of
       names that we pass around *)
    Definition name_comp (n : nat) (H' : n < rand_bound) : comp message :=
      mk_comp_message
        (fun (eta : nat) (r : rands eta) (_ : arands eta) =>
           existT _ eta (tnth r H')).

    Definition name_poly : forall (n : nat) (H' : n < rand_bound),
        poly_time (name_comp H').
    Admitted.

    Definition name_messagecomp (n : nat) (H' : n < rand_bound)
      : MessageComp :=
      mkMessageComp (name_poly H').

    Definition apply_comp eta (r : rands eta) (ar : arands eta)
               (a : SymbolicSort) (c : CompDomain a) : dom2type a :=
      match a as s return (CompDomain s -> dom2type s) with
      | Message => fun c0 : CompDomain Message => (message_comp c0) eta r ar
      | Bool => fun c0 : CompDomain Bool => (bool_comp c0) eta r ar
      end c.

    Definition apply_comps eta dom (r : rands eta) (ar : arands eta)
               (args : hlist CompDomain dom) := hmap' (apply_comp r ar) args.

    Definition wrap_handle T A (handle : forall eta, arands eta ->
                                                     hlist dom2type A -> T)
               (args : hlist CompDomain A) :=
      (fun (eta : nat) (r : rands eta) (ar : arands eta) =>
         handle eta ar (apply_comps r ar args)).

    (* Attackers w/ inputs are polynomial time if they're polynomial
       time in eta for any inputs that are computed in polynomial time *)
    Definition bool_handle_poly A
               (handle : forall eta, arands eta -> hlist dom2type A -> bool)
      : Prop :=
      forall args : hlist CompDomain A,
        poly_time (mk_comp_bool (wrap_handle handle args)).

    Definition message_handle_poly A
               (handle : forall eta, arands eta -> hlist dom2type A -> message)
      : Prop :=
      forall args : hlist CompDomain A,
        poly_time (mk_comp_message (wrap_handle handle args)).

    (* Attackers are a generator of computations that are polynomial
       time and only access attacker randomness. *)
    Definition bool_handle (dom : list SymbolicSort) :=
      { f : forall eta, arands eta -> hlist dom2type dom -> bool |
        bool_handle_poly f }.

    Definition message_handle (dom : list SymbolicSort) :=
      { f : forall eta, arands eta -> hlist dom2type dom -> message |
        message_handle_poly f }.

    Definition attacker := forall (n : nat) (H : n < handle_bound),
        match (snd (tnth handles H)) with
        | Message => message_handle (fst (tnth handles H))
        | Bool => bool_handle (fst (tnth handles H))
        end.

    (* Given an attacker and a list of inputs in the domain, *)
    (* compute the output of the attacker *)
    Definition interp_handle (att : attacker) (n : nat) (H' : n < handle_bound)
               (args : hlist CompDomain (fst (tnth handles H')))
      : CompDomain (snd (tnth handles H')).
      hnf in att.
      specialize (att n H').
      destruct (snd (tnth handles H')).
      - destruct att as [c p].
        simple refine (@mkMessageComp _ _).
        + econstructor.
          * exact message_eq_dec.
          * intros; eapply c.
            -- eassumption.
            -- eapply apply_comps; eassumption.
        + apply p.
      - destruct att as [c p].
        simple refine (@mkBoolComp _ _).
        + econstructor.
          * exact bool_dec.
          * intros; eapply c.
            -- eassumption.
            -- eapply apply_comps; eassumption.
        + apply p.
    Defined.

    (* Definition of interpreting a function in our Computational Model,
       parametrized over an attacker who interprets attacker
       functions. The definition is written in proof mode because
       dependent matches are too icky *)
    Definition CompInterpFunc :
      forall (att : attacker) dom cod
             (f : SymbolicFunc dom cod) (args : hlist CompDomain dom),
        (CompDomain cod) :=
      fun (att :attacker) dom cod (f : SymbolicFunc dom cod) =>
        match f in (SymbolicFunc dom cod) return
              (hlist CompDomain dom -> CompDomain cod) with
        | STrue => fun _ => constant_boolcomp true
        | SFalse => fun _ => constant_boolcomp false
        | IfThenElse =>
          fun args =>
            if_then_else_messagecomp (hhead args)
                                     (hhead (htail args))
                                     (hhead (htail (htail args)))
        | EmptyMsg =>
          fun _ => constant_messagecomp (existT Bvector 0 Bnil)%nat
        | Eq => fun args =>
                  eq_boolcomp (hhead args) (hhead (htail args))
        | EqL => fun args =>
                   eql_boolcomp (hhead args) (hhead (htail args))
        | Name H => fun _ => name_messagecomp H
        | Handle H => fun args => interp_handle att args
        end.

    Definition indist dom (l1 l2 : hlist CompDomain dom) : Prop :=
      forall (f : bool_handle dom),
        negligible
          (fun (eta : nat) =>
             (| Pr[bind_rands
                     bool_dec
                     (fun (r : rands eta) (ar : arands eta) =>
                        proj1_sig f eta ar (apply_comps r ar l1))] -
                Pr[bind_rands
                     bool_dec
                     (fun (r : rands eta) (ar : arands eta) =>
                        proj1_sig f eta ar (apply_comps r ar l2))] |)).

    (* Define the computational interpretation of predicates, which
       right now is only indistinguishability *)
    Definition CompInterpPredicate dom (p : SymbolicPredicate dom)
               (args : hlist CompDomain dom) : Prop.
      induction p.
      refine (indist (hfirstn (length l) args) _).
      rewrite listdup_split.
      exact (hskipn (length l) args).
    Defined.

    (* Finally, define our computational model, which is parametrized by
       our attacker. *)
    Definition CompModel (att : attacker)
      : model SymbolicFunc SymbolicPredicate :=
      Model (CompInterpFunc att) CompInterpPredicate.

  End CompInterp.

End Models.
