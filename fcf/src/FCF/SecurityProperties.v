(* Require Import Coq.Relations.Relation_Definitions. *)
(* Require Import Coq.Strings.String. *)
(* Require Import Map. *)

Require Import FCF.
Require Import Bvector.
Require Import Asymptotic.
  
Inductive typecode :=
| Base (T : Type)
| Bits.
  
(* | Arrow x y => interp_typecode x -> interp_typecode y *)
(* | Arrow (dom : typecode) (ran : typecode) *)

(* f in App will be initialized with, per se, f = the computational definition of encryption for convenience. This will denote to the symbolic model that this is encryption, and f will be ranged over *)

(* Inductive term : typecode -> Type := *)
(* | Const : forall {tc} (x:interp_typecode tc), term tc *)
(* | App1 : forall {T1 T2} (f: unary_func T1 T2) (x:term(Base T1)), term(Base T2) *)
(* | App2 : forall {T1 T2 T3} (f: binary_func T1 T2 T3) (x:term(Base T1)) (y:term(Base T2)), term(Base T3) *)
(* | Random : forall tc (random_index : nat), term tc. *)

Inductive unary_func : typecode -> Type -> Type :=
| Increment : unary_func (Base nat) nat.

Inductive binary_func : Type -> Type -> Type -> Type :=
| Add : binary_func nat nat nat.


Inductive term : typecode  -> Type :=
| Const : forall {T} (x: T), term (Base T)
(* | App1 : forall {tc1 T2} (f: unary_func tc1 T2) (x:term tc1), term (Base T2) *)
(* | App2 : forall {T1 T2 T3} (f: binary_func T1 T2 T3) (x:term T1) (y:term T2), term (Base T2) *)
| Random : forall (random_index : nat), term Bits.

Inductive unary : typecode -> Type :=
| IsTrue : unary (Base bool)
| AllZeros : unary Bits.

Inductive binary : typecode -> typecode -> Type :=
| Equal : forall (tc1: typecode) (tc2: typecode), binary tc1 tc2.

(* TODO: list of not just all the same type for deducible *)
Inductive atomic :=
| Deducible {tc1 : typecode} {tc2 : typecode} (context : list (term tc1)) (target: term tc2)
| AtomicUnary {tc : typecode} (t : term tc) (P: unary tc)
| AtomicBinary {tc1 : typecode} {tc2 : typecode} (t1 : term tc1) (t2: term tc2) (P: binary tc1 tc2).

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

(* Problem 2: Apps *)
                                                                        
(* AND ID(n) ID(n) *)

Definition cinterp_unary_base {T: Type} (u : unary (Base T)) : (T -> Prop) :=
  match u with
    | IsTrue => eq true
  end.

Definition eval_base {T : Type} (t: term (Base T)) : T :=
  match t with
    | Const _ c => c
  end.
           
Definition cinterp_unary_bits (eta : nat) (u : unary Bits) : Bvector eta -> bool :=
  match u with
    | AllZeros => fun b => b ?= Bvect_false eta
  end.
                   
(* Given an eta and a function P on bitvectors of length eta, return True only if P r is false. *)
Definition unary_comp {eta: nat} (Comp (P: Bvector eta -> bool): Comp bool :=
  r <-$ Rnd eta;
  ret negb (P r).

Definition cinterp_atomic_unary {tc: typecode} : term tc -> unary tc -> Prop :=
  match tc with
    | Base _ => fun t => fun P => cinterp_unary_base P (eval_base t)
    | Bits => fun _ => fun P => negligible (fun n => Pr[unary_comp n (cinterp_unary_bits n P)])
  end.

(* Either function evaluates a constant to produce a constant (easy game, easy life) *)
(* Or function evaluates Bits. Then function must be decideable,  *)

  
  (* match t with *)
  (*   | Const _ c => fun P => (cinterp_unary P) c  *)
  (*   (* | App1 _ _ f x => fun _ => True *) *)
  (*   (* | App2 _ _ _ f x y => fun _ => True *) *)
  (*   | Random i => fun P => negligible (fun n => Pr[random_unary_comp n (cinterp_unary P)]) *)
  (* end. *)

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