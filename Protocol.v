Set Implicit Arguments.
Unset Strict Implicit.
Require Import Coq.Lists.List.
Import ListNotations.

Load FirstOrder.

Section Protocol.
  Variable Q : Set.

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
      agent_inputs: list handle;
      attacker_outputs: list term;
      guards: list closed_formula
  }.

  Definition trans_seq := list sym_state.
 
  (* Why don't I need a formula as an argument here? *)
  Definition satisfies_formulas (m : model) (l : list closed_formula) : Prop :=
    fold_left (fun P => fun f => interp_closed_formula m (projT2 f) /\ P) l True. 

  Definition valid (m : model) (tr : trans_seq) : Prop :=
    match tr with
      | [] => True
      | x :: _ => satisfies_formulas m x.(guards)
    end.

End Protocol.