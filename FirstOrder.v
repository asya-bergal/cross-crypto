Set Implicit Arguments.
Unset Strict Implicit.

Require Import Coq.Lists.List.
Import ListNotations.

Require Import CrossCrypto.HList.

Section FirstOrder.

  Context (sort : Type)
          (func : list sort -> sort -> Type)
          (predicate : list sort -> Type).

  Inductive term : sort -> Type :=
    App : forall {dom cod},
            (func dom cod) -> hlist term dom -> term cod.

  Definition term_terms_rect
             (P : forall s, term s -> Type)
             (Q : forall ss, hlist term ss -> Type)
             (c_app : forall {dom} {cod} (f : func dom cod)
                             (ts : hlist term dom),
                        Q dom ts -> P cod (App f ts))
             (c_nil : Q [] h[])
             (c_cons : forall {s} (t : term s) {ss} (ts : hlist term ss),
                         P s t -> Q ss ts -> Q (s :: ss) (t h:: ts)) :
    forall {s} (t : term s), P s t :=
    fix F {s} (t : term s) : P s t :=
    match t with
      | App f ts =>
        c_app f ts
              ((fix G {ss} (ts : hlist term ss) : Q ss ts :=
                  match ts with
                    | h[] => c_nil
                    | t h:: ts => c_cons t ts (F t) (G ts)
                  end) _ ts)
    end.

  Record model :=
    Model
      {domain :> sort -> Type;
       interp_func : forall dom cod,
                       func dom cod ->
                       hlist domain dom ->
                       domain cod;
       interp_predicate : forall dom,
                            predicate dom ->
                            hlist domain dom -> Prop}.

  Definition interp_term (m : model) s (t : term s) : m s.
    apply term_terms_rect with
    (P := (fun s t => m s))
      (Q := fun ss ts => hlist m ss)
      (t := t); clear s t.
    (* app *)
    intros dom cod f x IHts.
    apply (interp_func f); assumption.
    (* nil *)
    constructor.
    (* cons *)
    constructor; assumption.
  Defined.

  Definition interp_terms (m : model) ss (ts : hlist term ss)
  : hlist m ss :=
    hmap' (interp_term _) ts.

  Section formulas.

    Variable d : sort -> Type.

    Inductive formula : Type :=
    | Predicate : forall ss, predicate ss -> hlist term ss -> formula
    | And : formula -> formula -> formula
    | Or : formula -> formula -> formula
    | Not : formula -> formula
    | Forall : forall s, (d s -> formula) -> formula
    | Exists : forall s, (d s -> formula) -> formula
    | FTrue : formula
    | FFalse : formula.

  End formulas.

  Arguments FTrue {d}.
  Arguments FFalse {d}.

  Definition Formula := forall d : sort -> Type, formula d.

  Fixpoint interp_formula (m : model) (f : formula m) : Prop :=
    match f with
      | Predicate _ p ts => interp_predicate p (interp_terms m ts)
      | And f1 f2 => interp_formula f1 /\ interp_formula f2
      | Or f1 f2 => interp_formula f1 \/ interp_formula f2
      | Not f => ~interp_formula f
      | @Forall _ s f => forall x : m s, interp_formula (f x)
      | @Exists _ s f => exists x : m s, interp_formula (f x)
      | FTrue => True
      | FFalse => False
    end.

  Definition interp_Formula (m : model) (f : Formula) :=
    interp_formula (f m).

End FirstOrder.
