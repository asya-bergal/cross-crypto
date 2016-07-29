Set Implicit Arguments.
Unset Strict Implicit.

Require Import Omega.
Require Import CrossCrypto.FrapTactics.
Require Import CrossCrypto.ListUtil.
Require Import Coq.Lists.List.
Import ListNotations.

Inductive hlist A (f : A -> Type) : list A -> Type :=
| hnil : hlist f []
| hcons : forall x l, f x -> hlist f l -> hlist f (x :: l).

Notation " h[] " := (hnil _).
Infix "h::" := hcons (at level 60, right associativity).

Definition hhead A f (l : list A) (hl : hlist f l) (H : l <> []) : f (head_with_proof H).
  inversion hl.
  congruence.
  subst l.
  simpl.
  exact X.
Defined.

Fixpoint hnth (n : nat) A f (l : list A) (hl : hlist f l) (H : length(l) > n) {struct l}: f (nth_with_proof l H).
  cases n; cases l; simpl in H; try omega.
  inversion hl.
  exact X.
  inversion hl.
  refine (hnth n A f l X0 _).
Defined.

Definition hmap A (f : A -> Type) B (g : B -> Type)
           (F : A -> B) (F' : forall a, f a -> g (F a))
           (l : list A) (h : hlist f l) : hlist g (map F l).
  induction h; constructor; auto.
Defined.

Definition hmap' A (f : A -> Type) (g : A -> Type)
           (F' : forall a, f a -> g a)
           (l : list A) (h : hlist f l) : hlist g l.
  replace l with (map id l).
  apply hmap with (f := f); assumption.
  clear f g F' h.
  induction l as [| x xs IHl]; [| simpl; rewrite IHl]; reflexivity.
Defined.
