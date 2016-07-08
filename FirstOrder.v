Set Implicit Arguments.
Unset Strict Implicit.

Axiom TODO : forall {t : Type}, t.

Inductive tuple (T : Type) : nat -> Type :=
| tuple_nil : tuple T 0
| tuple_cons : forall n, T -> tuple T n -> tuple T (S n).

Fixpoint tuple_map n A B (f : A -> B) (t : tuple A n) : tuple B n :=
  match t with
    | tuple_nil => tuple_nil B
    | tuple_cons _ x xs => tuple_cons (f x) (tuple_map f xs)
  end.

Fixpoint tuple_fold n A B (f : A -> B -> B) (t : tuple A n) (b : B) : B :=
  match t with
    | tuple_nil => b
    | tuple_cons _ x xs => f x (tuple_fold f xs b)
  end.

(*
Eval cbv [tuple_map nat_rect] in tuple_map.

Fixpoint tuple_map n A B (f : A -> B) (t : tuple n A) {struct n} : tuple n B
 :=
  match n with
    | 0 => tt
    | S n => let (hd, tl) := t in (f hd, tuple_map n A B f tl)
  end.
*)

Axiom identifier : Set.
Axiom identifier_dec_eq : forall i i' : identifier, {i = i'} + {i <> i'}.

Definition func (n : nat) := identifier.
Definition name := identifier.
Definition handle := identifier.
Definition var := identifier.
Definition var_dec_eq := identifier_dec_eq.

Inductive term : Type :=
| Name : name -> term
| Handle : handle -> term
| Var : var -> term
| App : forall n : nat, (func n) -> tuple term n -> term.

Inductive predicate : forall n : nat, Type :=
| Equal : predicate 2
| Deducible : forall n, predicate (S n).

Inductive formula : Type :=
| Predicate : forall n, predicate n -> tuple term n -> formula
| And : formula -> formula -> formula
| Or : formula -> formula -> formula
| Not : formula -> formula
| Forall : var -> formula -> formula
| Exists : var -> formula -> formula.

Record model (D : Type) := Model
                             {interp_func : forall n, func n -> tuple D n -> D;
                              interp_name : name -> D;
                              interp_handle : handle -> D;
                              interp_predicate : forall n, predicate n ->
                                                           tuple D n -> Prop}.

(*
Inductive model (D : Type) :=
| Model : (forall n, func n -> tuple n D -> D) ->
          (name -> D) ->
          (handle -> D) ->
          (forall n, predicate n -> tuple n D -> Prop) ->
          model D.
*)

Fixpoint free_term (v : var) (t : term) {struct t} : Prop :=
  match t with
    | Var v' => v = v'
    | App n f ts => free_terms v ts
    | _ => False
  end

with free_terms (v : var) n (ts : tuple term n) {struct ts} :=
       match ts with
         | tuple_nil => False
         | tuple_cons n t ts => free_term v t \/ free_terms v ts
       end.
  tuple_fold (fun t p => free_term v t \/ p) ts False.

(*
Fixpoint free_terms (v : var) n (ts : tuple term n) {struct ts} :=
       match ts with
         | tuple_nil => False
         | tuple_cons n t ts =>
           match t with
             | Var v' => v = v'
             | App n f ts => free_terms v ts
             | _ => False
           end \/ free_terms v ts
       end.
*)

Definition interp_term (D : Type) (m : model D) (t : term)
           (ctx : forall v : var, free_term v t -> D) : D.
  induction t as [n | h | v].
  exact (m.(interp_name) n).
  exact (m.(interp_handle) h).
  apply (ctx v).
  simpl; reflexivity.
Defined.


Fixpoint free_formula (v : var) (f : formula) : Prop :=
  match f with
    | Predicate n p ts => free_terms v ts
    | And f1 f2 => free_formula v f1 \/ free_formula v f2
    | Or f1 f2 => free_formula v f1 \/ free_formula v f2
    | Not f => free_formula v f
    | Forall v' f => v <> v' /\ free_formula v f
    | Exists v' f => v <> v' /\ free_formula v f
  end.

Definition interp_terms (D : Type) (m : model D) n (ts : tuple term n)
           (ctx : forall v : var, free_terms v ts -> D) : tuple D n.
  induction ts as [| n hd tl IHts].
  exact (tuple_nil D).
  simpl in ctx.
  refine (tuple_cons _ _).
  clear IHts.
  induction hd as [nm | h | v].
  refine (interp_term m (t:=Name nm) _).
  intros v H; destruct H.
  refine (interp_term m (t:=Handle h) _).
  intros v H; destruct H.
  apply (ctx v).
  left.
  simpl; reflexivity.

  apply IHts.
  intros v H.
  apply (ctx v).
  right.
  assumption.
Defined.

Fixpoint interp_formula (D : Type) (m : model D) (f : formula) {struct f}
         : (forall v : var, free_formula v f -> D) -> Prop :=
  match f as f' return ((forall v : var, free_formula v f' -> D) -> _) with
    | Predicate n p ts => fun ctx => m.(interp_predicate)
                                         p (interp_terms m (ts:=ts) ctx)
    | And f1 f2 => fun ctx =>
                     and (interp_formula m (f:=f1)
                                         (fun v H => ctx v (or_introl H)))
                         (interp_formula m (f:=f2)
                                         (fun v H => ctx v (or_intror H)))
    | Or f1 f2 => fun ctx =>
                     or (interp_formula m (f:=f1)
                                         (fun v H => ctx v (or_introl H)))
                         (interp_formula m (f:=f2)
                                         (fun v H => ctx v (or_intror H)))
    | Not f => fun ctx => ~(interp_formula m (f:=f) ctx)
    | Forall v f =>
      fun ctx =>
        forall d : D,
          interp_formula m (f:=f)
                         (fun v' H =>
                            match var_dec_eq v' v with
                              | left veqv' => d
                              | right vneqv' => ctx v' (conj vneqv' H)
                            end)
    | Exists v f =>
      fun ctx =>
        exists d : D,
          interp_formula m (f:=f)
                         (fun v' H =>
                            match var_dec_eq v' v with
                              | left veqv' => d
                              | right vneqv' => ctx v' (conj vneqv' H)
                            end)
  end.

(*
Definition interp_formula (D : Type) (m : model D) (f : formula)
         (ctx : forall v : var, free_formula v f -> D) : Prop.
  induction f as [n p ts | f1 IHf1 f2 IHf2 | f1 IHf1 f2 IHf2 | f IHf | v' f | v' f].
  apply (m.(interp_predicate) p).
  refine (interp_terms m (ts:=ts) _).
  intro v.
  exact (ctx v).

  refine (IHf1 _ /\ IHf2 _); intros v H; apply (ctx v);
  [left | right]; assumption.

  refine (IHf1 _ \/ IHf2 _); intros v H; apply (ctx v);
  [left | right]; assumption.

  refine (~IHf _); exact ctx.

  refine (forall d : D, IHf _). (* error I don't understand *)
*)

Definition closed f := forall v, ~free_formula v f.

Definition interp_closed_formula (D : Type) (m : model D) (f : formula)
           (H : closed f) : Prop.
  refine (interp_formula m (f:=f) _).
  intros v H'.
  destruct (H v H').
Defined.
