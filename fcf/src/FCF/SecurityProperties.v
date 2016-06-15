(* Require Import Coq.Relations.Relation_Definitions. *)
(* Require Import Coq.Strings.String. *)
(* Require Import Map. *)

Require Import FCF.
Require Import Bvector.
Require Import Asymptotic.

(* Inductive typecode := *)
(* | Base (T : Type) *)
(* | Arrow (dom : typecode) (ran : typecode) *)
(* | Bits (eta : nat). *)

(* Fixpoint interp_typecode (tc:typecode) : Type := *)
(*   match tc with *)
(*     | Base x => x *)
(*     | Arrow x y => interp_typecode x -> interp_typecode y *)
(*     | Bits eta => Bvector eta *)
(*   end. *)
  
Inductive unary_func : Type -> Type -> Type :=
| Increment : unary_func nat nat.

Inductive binary_func : Type -> Type -> Type -> Type :=
| Add : binary_func nat nat nat.
(* f in App will be initialized with, per se, f = the computational definition of encryption for convenience. This will denote to the symbolic model that this is encryption, and f will be ranged over *)

(* Inductive term : typecode -> Type := *)
(* | Const : forall {tc} (x:interp_typecode tc), term tc *)
(* | App1 : forall {T1 T2} (f: unary_func T1 T2) (x:term(Base T1)), term(Base T2) *)
(* | App2 : forall {T1 T2 T3} (f: binary_func T1 T2 T3) (x:term(Base T1)) (y:term(Base T2)), term(Base T3) *)
(* | Random : forall tc (random_index : nat), term tc. *)

Inductive term : Type -> Type :=
| Const : forall {T} (x: T), term T
| App1 : forall {T1 T2} (f: unary_func T1 T2) (x:term T1), term T2
| App2 : forall {T1 T2 T3} (f: binary_func T1 T2 T3) (x:term T1) (y:term T2), term T3
| Random : forall (eta: nat) (random_index : nat), term (Bvector eta).

Inductive unary : Type -> Type :=
| IsTrue : unary bool.

Inductive binary : Type -> Type -> Type :=
| Equal : forall (T1: Type) (T2: Type), binary T1 T2.

(* TODO: list of not just all the same type for deducible *)
Inductive atomic :=
| Deducible {T1 : Type} {T2 : Type} (context : list (term T1)) (target: term T2)
| AtomicUnary {T : Type} (t : term T) (P: unary T)
| AtomicBinary {T1 : Type} {T2 : Type} (t1 : term T1) (t2: term T2) (P: binary T1 T2).

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

(* TODO: This definition is wrong, maybe we can fix it when we decide to go back to props *)
Definition cinterp_unary {T: Type} (u : unary T) : (T -> bool) :=
  match u with
    | IsTrue => fun t => true
  end.
                   
Print cinterp_unary.
(* TODO: Write this better *)
(* TODO: P needs to be a function defined on random values of any length if it is to work correctly *)
(* TODO: P also has to be decideable, how awkward. *)
Definition random_unary_comp (eta: nat) (P: Bvector eta -> bool): Comp bool :=
  r <-$ Rnd eta;
  ret P r.

Definition cinterp_atomic_unary {T: Type} (t: term T) : unary T -> Prop :=
  match t with
    | Const _ c => fun P => if (cinterp_unary P) c then True else False
    | App1 _ _ f x => fun _ => True
    | App2 _ _ _ f x y => fun _ => True
    | Random eta i => fun P => negligible (fun n => Pr[random_unary_comp eta (cinterp_unary P)])
  end.

Definition cinterp_atomic (a : atomic) : Prop :=
  match a with
   | Deducible _ _ context target => True
   | AtomicUnary _ t P => cinterp_atomic_unary  t P
   | AtomicBinary _ _ t1 t2 P => True
  end.

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