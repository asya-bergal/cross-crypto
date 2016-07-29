Set Implicit Arguments.

Require Import Omega.
Require CrossCrypto.FrapTactics.
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint repeat A (a : A) n :=
  match n with
    | 0 => []
    | S n => a :: repeat a n
  end.

Definition head_with_proof T (l : list T) (H : l <> []) : T.
  destruct l.
  destruct (H eq_refl).
  exact t.
Defined.

Fixpoint nth_with_proof T (n:nat) (l:list T) (H : length(l) > n) {struct l} : T.
  FrapTactics.cases n; FrapTactics.cases l; FrapTactics.simplify; try omega.
  exact t.
  refine (nth_with_proof T n l _).
  omega.
Defined.
