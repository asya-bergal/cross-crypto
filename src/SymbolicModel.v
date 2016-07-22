Require Import CrossCrypto.FirstOrder.
Require Import Coq.Lists.List.
Import ListNotations.

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
  | Name : nat -> SymbolicFunc [] Message
  | AttackerName : nat -> SymbolicFunc [] Message.

  (* Indistinguishability is defined on both messages and booleans *)
  Inductive SymbolicPredicate : list SymbolicSort -> Type :=
    | Indist : forall (s : SymbolicSort), SymbolicPredicate (s :: s :: []).

End SymbolicModel.
