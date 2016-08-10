Set Implicit Arguments.

Require Import Coq.Lists.List.
Import ListNotations.

Require Import FCF.

Require Import CrossCrypto.FrapTactics.
Require Import CrossCrypto.HList.
Require Import CrossCrypto.Tuple.

(* This is a weird way of doing things but I couldn't figure out a good
   workaround *)
Definition set2type (A : Set) : Type := A.

Fixpoint bind_comps (comp_types : list Set) (h : hlist Comp comp_types) T
         (f : hlist set2type comp_types -> Comp T) {struct comp_types} :
  Comp T.
  cases comp_types.
  exact (f h[]).
  refine (bind_comps comp_types (htail h) T
                     (fun (f' : hlist set2type comp_types) =>
                        Bind _ (fun x => f (_ h:: f')))).
  refine (hhead h).
  equality.
Defined.

Definition bind_tuple (T : Set) (T_dec : eq_dec T) {eta : nat} n
           (f : tuple (Bvector eta) n -> T) : Comp T.
  refine (bind_comps (list2hlist (repeat (Rnd eta) n)) _).
  refine (fun h => Ret T_dec (f (hlist2tuple h _ ))).
  assert (length (repeat (Rnd eta) n) = n) by apply repeat_length.
  rewrite H.
  equality.
Defined.
