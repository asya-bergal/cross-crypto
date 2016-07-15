Set Implicit Arguments.
Unset Strict Implicit.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import Coq.Structures.OrderedType.
Import ListNotations.

Load FirstOrder.

Definition head T (l : list T) (H : l <> []) : T.
  destruct l.
  destruct (H eq_refl).
  exact t.
Defined.

Parameter sbool : sort.
Parameter message : sort.
Parameter ite : func (sbool :: message :: message :: []) message.
Parameter ftrue : func [] sbool.
Parameter ffalse : func [] sbool.
Parameter empty_message : func [] message.
Parameter eq_test : func (message :: message :: []) sbool.
Parameter equiv : forall (ss : list sort), predicate (ss ++ ss).

(*
s is a function from variables to term
theta is a function from variables to Formula
control state with transition such that ordering is reasonable
gg
set of states

*)
Section Protocol.

  Variable Q : Type.
  Variable Q_gt : Q -> Q -> Prop.
  Infix "Q>" := Q_gt (at level 70).

  Variable q0 : Q.

  Record transition := mkTransition {
      from : Q;
      to : Q;
      transition_order : from Q> to;
      inputs : list sort;
      input : sort;
      output_type : sort;
      output : hlist term (input :: inputs) -> term output_type;
      guard : hlist term (input :: inputs) -> term sbool
  }.

  Definition transition_from q := {t : transition | t.(from) = q}.

  Variable transitions : forall q, list (transition_from q).

  Definition final q : Prop := transitions q = [].

  Definition maximal (t : transition) : Prop :=
    forall ts : hlist term (t.(input) :: t.(inputs)),
      guard ts = App ftrue h[].

  Definition has_max_transition (q : Q) (H : ~final q) : Prop :=
    maximal (proj1_sig (head H)).

  Variable max_transition : forall q (H : ~final q), has_max_transition H.

  (* Variable transitions : list transition. *)

  (* Definition protocol := list transition -> Prop. *)

  (* Record sym_state := mkState { *)
  (*     start : Q * list name; *)
  (*     attacker_inputs : list handle; *)
  (*     agent_outputs : list term *)
  (* }. *)

  (* Definition valid_transition (from to : sym_state) : Prop := True. *)
  (* (* Definition valid_transition (from to : sym_state) : Prop := *) *)
  (* (*   to.(guards) = set_add from.(guards) *) *)

  (* Definition sym_trans_seq (pi : protocol) (l : list sym_state) : Prop := *)
  (*   match l with *)
  (*     | to :: from :: xs => *)
  (*       exists (t : transition), pi t /\ valid_transition from to *)
  (*     | _ => True *)
  (*   end. *)

  (* Definition satisfies_formulas (m : model) (l : set closed_formula) : Prop := *)
  (*   fold_left (fun P => fun f => interp_closed_formula m f /\ P) l True. *)

  (* (* Lists have last state at the head *) *)
  (* (* Is it more reasonable to have this look like H -> content? *) *)
  (* Definition valid (m : model) (pi : protocol) (tr : list sym_state) *)
  (*            (H : sym_trans_seq pi tr) : Prop := *)
  (*   match tr with *)
  (*     | [] => True *)
  (*     | x :: _ => satisfies_formulas m x.(guards) *)
  (*   end. *)

End Protocol.