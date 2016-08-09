Set Implicit Arguments.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Omega.

Require Import CrossCrypto.FrapTactics.

Definition head_with_proof T (l : list T) (H : l <> []) : T.
  destruct l.
  destruct (H eq_refl).
  exact t.
Defined.

Fixpoint nth_with_proof T (n:nat) (l:list T) {struct l} :
  length(l) > n -> T.
  intro H.
  FrapTactics.cases n; FrapTactics.cases l; FrapTactics.simplify; try omega.
  exact t.
  refine (nth_with_proof T n l _).
  omega.
Defined.

Lemma firstn_concat : forall A (l : list A) (l' : list A),
    firstn (length l) (l ++ l') = l.
  induction l; intros; simplify; equality.
Qed.

Lemma skipn_concat : forall A (l : list A) (l' : list A),
    skipn (length l) (l ++ l') = l'.
  induction l; intros; simplify; equality.
Qed.

Lemma listdup_split : forall A (l : list A),
    firstn (length l) (l ++ l) = skipn (length l) (l ++ l).
  repeat intros.
  rewrite (firstn_concat l l).
  rewrite (skipn_concat l l).
  equality.
Qed.
