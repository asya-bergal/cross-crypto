(* 1. Specify lemma so there's only one place to apply it.
   2. Apply tactic. *)

(* Specific tactics I want: *)
(* -  Swap two lines *)
(*  -  make ret x (y z) into a <-$ ret y z; ret x a (left_ident)
   -  make (x <-$ cA; ret x) into cA (right_ident)
   -  make (x <-$ cA; y <-$ f x; g y) into (y <-$ (x <-$ cA; f x); g y) (associativty)
   - rewrite a thing with another thing (look into this more)

   Do this with recursive Proper_Binds, reflexivity + check if this applies) *)

(* Things to do: *)
(* Try to use my tactic *)

Require Import FCF.FCF.
Require Import RewriteUtil.

Lemma swap_test : Comp_eq (x <-$ {0,1}; y <-$ {0,1}; ret x && y) (y <-$ {0,1}; x <-$ {0,1}; ret x && y).
  rewrite Comp_eq_swap.
  rewrite Comp_eq_swap.
  reflexivity.
Qed.

(* General lemma that helps do what I want *)
Ltac brewrite lemma :=
  first [ rewrite lemma; reflexivity | etransitivity; [ eapply Proper_Bind; [ reflexivity | do 3 intro; brewrite lemma] | ] ].
  
(* Ltac cswap subexpr := *)
(*   match goal with *)
(*     | [ |- Comp_eq ( context[_ <-$ ?c1; _ <-$ ?c2;  *)
Lemma harder_swap_test : Comp_eq (z <-$ {0,1}; x <-$ {0,1}; y <-$ {0,1}; ret x && y) (y <-$ {0,1}; z <-$ {0,1}; x <-$ {0,1}; ret x && y).

  (* eapply Proper_Bind. *)
  (* reflexivity. *)
  (* do 3 intro. *)
  (* rewrite (Comp_eq_swap _ _ (m <-$ { 0 , 1 }^ 1; ret Vector.hd m) (m <-$ { 0 , 1 }^ 1; ret Vector.hd m) _ (fun (x : bool) (y : bool) => ret x && y)). *)
  (* apply Comp_eq_symmetry. *)
  (* etransitivity. *)
  (* (* Set Printing All. *) *)
  (* (* Show. *) *)
  (* rewrite (Comp_eq_swap _ _ (m <-$ { 0 , 1 }^ 1; ret Vector.hd m) (m <-$ { 0 , 1 }^ 1; ret Vector.hd m) _ (fun (_ : bool) (x0 : bool) => ret x0 && y)). *)

  apply Comp_eq_symmetry.
  (* rewrite (Comp_eq_swap _ _ (m <-$ { 0 , 1 }^ 1; ret Vector.hd m) (m <-$ { 0 , 1 }^ 1; ret Vector.hd m) _ (fun (_ : bool) (x : bool) => ret x && y)). *)
  etransitivity.
  eapply Proper_Bind.
  reflexivity.
  do 3 intro.
  etransitivity.
  rewrite (Comp_eq_swap _ _ (m <-$ { 0 , 1 }^ 1; ret Vector.hd m) (m <-$ { 0 , 1 }^ 1; ret Vector.hd m) _ (fun (_ : bool) (x0 : bool) => ret x0 && _)).
  reflexivity.
  subst.
  lazymatch goal with |- ?R ?LHS (?e ?x) =>
                      let LHS' := eval pattern x in LHS in
                          lazymatch LHS' with ?f x =>
                                              instantiate (1:=f)
                          end
  end; reflexivity.
  Admitted.


  



(*   etransitivity. *)
(*   eapply Proper_Bind. *)
(*   reflexivity. *)
(*   do 3 intro. *)
(*   rewrite (Comp_eq_swap _ _ (m <-$ { 0 , 1 }^ 1; ret Vector.hd m) (m <-$ { 0 , 1 }^ 1; ret Vector.hd m) _ (fun (_ : bool) (x0 : bool) => ret x0 && x)). *)

(*   assert (Comp_eq *)
(*     (_ <-$ (m <-$ { 0 , 1 }^ 1; ret Vector.hd m); *)
(*      x0 <-$ (m <-$ { 0 , 1 }^ 1; ret Vector.hd m); ret x0 && x) (ret y)). *)
(*   Set Printing All. *)
(*   Show. *)
(* Admitted. *)
 (*  rewrite (Comp_eq_swap _ _ (m <-$ { 0 , 1 }^ 1; ret Vector.hd m) (m <-$ { 0 , 1 }^ 1; ret Vector.hd m) _ (fun (x : bool) (y : bool) => ret x && y)). *)
 (*  rewrite (Comp_eq_swap _ _ (m <-$ { 0 , 1 }^ 1; ret Vector.hd m) (m <-$ { 0 , 1 }^ 1; ret Vector.hd m) _ (fun (x : bool) (y : bool) => ret x && y)). *)

 (*  About Comp_eq_swap. *)

 (*  brewrite (Comp_eq_swap _ _ (m <-$ { 0 , 1 }^ 1; ret Vector.hd m) (m <-$ { 0 , 1 }^ 1; ret Vector.hd m) _ (fun (x : bool) (y : bool) => ret x && y)). *)

 (* try timeout 2 setoid_rewrite andb_comm. *)
 (*  apply Proper_Bind. *)
 (*  reflexivity. *)
 (*  do 3 intro. *)
 (*  apply Proper_Bind. *)
 (*  reflexivity. *)
 (*  do 3 intro. *)
 (*  apply Proper_Bind. *)
 (*  reflexivity. *)
 (*  do 3 intro. *)
 (*  subst. *)
 (*  rewrite andb_comm. *)

 (*  etransitivity. *)
 (*  rewrite (Comp_eq_swap _ _ (m <-$ { 0 , 1 }^ 1; ret Vector.hd m) (m <-$ { 0 , 1 }^ 1; ret Vector.hd m) *)
 (*                        _ (fun (y : bool) (z : bool) => x <-$ (m <-$ { 0 , 1 }^ 1; ret Vector.hd m); ret x && y)). *)
 (*  apply Comp_eq_swap. *)
  
