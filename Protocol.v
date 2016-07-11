Set Implicit Arguments.
Unset Strict Implicit.
Require Import Coq.Lists.List.
Import ListNotations.

Load FirstOrder.

Section Protocol.
  Variable Q : Set.
  Variable D : Type.

  Record transition := mkTransition {
      from : Q * list name;
      to : Q * list name;
      inputs : list var;
      input : var;
      guard : formula;
      output : term
  }.


  Definition protocol := transition -> Prop.

  Record sym_state := mkState {
      start: Q * list name;
      attacker_inputs: list handle;
      frame: list term;
      guards: list formula
  }.

  Definition trans_seq := list sym_state.

  (* Inductive formula_ctx := *)
  (* | forall (f : formula), f -> forall v: var, free_formula v f -> D -> formula_ctx *)

  (* Fixpoint satisfies_formulas (m : model) (l : list {(f : formula) * forall v: var, free_formula v f -> D)) : Prop := *)
  (*   match l with *)
  (*     | [] => True *)
  (*     | f :: fs => interp_formula D m f ctx *)
  (*   end. *)
                                                                        
                                                                   
             
  Definition valid (m : model) (tr : trans_seq) : Prop :=
    match trans_seq with
      | [] => True
      | x :: xs =>
        match x.(guards) with
          | [] => True
          | f :: fs => interp_formula D m f  
      

  

  
  
      
                      
End Section.