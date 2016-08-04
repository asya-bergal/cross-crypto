Set Implicit Arguments.

Require Import Omega.
Require Import CrossCrypto.FrapTactics.
Require Import Coq.Lists.List.
Import ListNotations.

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
