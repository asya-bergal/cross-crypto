Set Implicit Arguments.
Unset Strict Implicit.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
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
      attacker_inputs: list handle;
      agent_outputs: list term;
      guards: set closed_formula
  }.

  Definition valid_transition (from to : sym_state) : Prop := True.
  (* Definition valid_transition (from to : sym_state) : Prop := *)
  (*   to.(guards) = set_add from.(guards) *)

  Definition sym_trans_seq (pi : protocol) (l : list sym_state) : Prop :=
    match l with
      | to :: from :: xs => exists (t : transition), pi t /\ valid_transition from to
      | _ => True
    end.
 
  (* Why don't I need a formula as an argument here? *)
  Definition satisfies_formulas (m : model) (l : set closed_formula) : Prop :=
    fold_left (fun P => fun f => interp_closed_formula m (projT2 f) /\ P) l True. 

  (* Lists have last state at the head *)
  (* Is it more reasonable to have this look like H -> content? *)
  Definition valid (m : model) (pi : protocol) (tr : list sym_state) (H : sym_trans_seq pi tr) : Prop :=
    match tr with
      | [] => True
      | x :: _ => satisfies_formulas m x.(guards)
    end.

End Protocol.