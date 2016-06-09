(* Require Import Coq.Relations.Relation_Definitions. *)
(* Require Import Coq.Strings.String. *)
(* Require Import Map. *)

Inductive typecode :=
| Base (T : Type)
| Arrow (dom : typecode) (ran : typecode).

Fixpoint interp_typecode (tc:typecode) : Type :=
  match tc with
    | Base x => x
    | Arrow x y => interp_typecode x -> interp_typecode y
  end.
  
Inductive term : typecode -> Type :=
| Const : forall {tc} (x:interp_typecode tc), term tc
| App : forall {tc1 tc2} (f: term (Arrow tc1 tc2)) (x:term tc1), term tc2
| Random : forall tc (random_index : nat), term tc.

Inductive atomic :=
| Deducible {tc1 : typecode} {tc2 : typecode} (context : list (term tc1)) (target: term tc2)
| AtomicUnary {tc : typecode} (t : term tc) (P: interp_typecode tc -> Prop)
| AtomicBinary {tc1 : typecode} {tc2 : typecode} (t1 : term tc1) (t2: term tc2) (P: interp_typecode tc1 -> interp_typecode tc2 -> Prop).

Inductive formula :=
| Atomic (a : atomic)
| And (f1 f2 : formula)
| Or (f1 f2 : formula)
| Not (f : formula)
| Implies (f1 f2 : formula)
| Forall {T : Type} (body : T -> formula)
| Exists {T : Type} (body : T -> formula).

Coercion Atomic : atomic >-> formula.

Section Formulas.
  Context (interp_atomic : atomic -> Prop).
  Fixpoint interp_formula  (f : formula) : Prop :=
    match f with
      | Atomic p => interp_atomic p
      | And f1 f2 => interp_formula f1 /\ interp_formula f2
      | Or f1 f2 => interp_formula f1 \/ interp_formula f2
      | Not f => ~(interp_formula f)
      | Implies f1 f2 => interp_formula f1 -> interp_formula f2
      | Forall _ body => forall x, interp_formula (body x)
      | Exists _ body => exists x, interp_formula (body x)
    end.
End Formulas.

Section Example.
  Context (interp_atomic : atomic -> Prop).
  Context (no_telepathy : forall i U T, ~(interp_atomic (Deducible (nil : list (term T)) (Random U i)))).
  Context (independent_randomness: forall j i T l, i <> j -> interp_atomic (Deducible (Random T j :: l) (Random T i)) -> interp_atomic (Deducible l (Random T i))).

  Theorem no_telepathy_for_reals : forall i j T, i <> j -> ~interp_atomic (Deducible (Random T j :: nil) (Random T i)).
  Proof.
    intros.
    intro.
    apply independent_randomness in H0; trivial.
    apply no_telepathy in H0; trivial.
  Qed.
End Example.

Section FormulaExample.
  (* i and j are not present at runtime, so it doesn't make sense to make them terms. Random U i and Random U j represent different calls to the random number generator, they're used to distinguish random values. It's still possible with negligible probability that Random U i = Random U j *)
  Context (interp_atomic : atomic -> Prop).
  Context (no_telepathy : interp_formula interp_atomic (Forall (fun i => Forall (fun U => Forall (fun T => Not (Deducible (nil : list (term T)) (Random U i))))))).
  Context (independent_randomness: forall i j, i <> j -> interp_formula interp_atomic (Forall (fun T => Forall (fun l => Implies (Deducible (Random T j :: l) (Random T i)) (Deducible l (Random T i)))))).

  Theorem formula_no_telepathy_for_reals : forall i j, i <> j -> interp_formula interp_atomic (Forall (fun T =>  Not (Deducible (Random T j :: nil) (Random T i)))).
  Proof.
    simpl.
    intros.
    intro.
    apply independent_randomness in H0; trivial.
    apply no_telepathy in H0; trivial.
  Qed.
End FormulaExample.