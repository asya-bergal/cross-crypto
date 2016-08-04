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
