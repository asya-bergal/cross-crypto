Set Implicit Arguments.
Unset Strict Implicit.

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

Axiom identifier : Set.
Axiom identifier_dec_eq : forall i i' : identifier, {i = i'} + {i <> i'}.

Definition func (n : nat) := identifier.
Definition predicate (n : nat) := identifier.
Definition name := identifier.
Definition handle := identifier.
Definition var := identifier.
Definition var_dec_eq := identifier_dec_eq.

Inductive term : Type :=
| Name : name -> term
| Handle : handle -> term
| Var : var -> term
| App : forall n : nat, (func n) -> tuple term n -> term.

(* Inductive predicate : forall n : nat, Type := *)
(* | Equal : predicate 2 *)
(* | Deducible : forall n, predicate (S n). *)

Inductive formula : Type :=
| Predicate : forall n, predicate n -> tuple term n -> formula
| And : formula -> formula -> formula
| Or : formula -> formula -> formula
| Not : formula -> formula
| Forall : var -> formula -> formula
| Exists : var -> formula -> formula
| FTrue : formula
| FFalse : formula.

Record model := Model
                  {domain : Type;
                   interp_func : forall n, func n -> tuple domain n -> domain;
                   interp_name : name -> domain;
                   interp_handle : handle -> domain;
                   interp_predicate : forall n, predicate n ->
                                                tuple domain n -> Prop}.

Definition term_terms_rect
         (P : term -> Type)
         (Q : forall n, tuple term n -> Type)
         (c_name : forall n : name, P (Name n))
         (c_handle : forall h : handle, P (Handle h))
         (c_var : forall v : var, P (Var v))
         (c_app : forall (n : nat) (f : func n) (ts : tuple term n),
                    Q n ts -> P (App f ts))
         (c_nil : Q 0 (tuple_nil term))
         (c_cons : forall (n : nat) (t : term) (ts : tuple term n),
                     P t -> Q n ts -> Q (S n) (tuple_cons t ts)) :
  forall t : term, P t :=
  fix F (t : term) : P t :=
  match t with
    | Name n => c_name n
    | Handle h => c_handle h
    | Var v => c_var v
    | App n f ts =>
      c_app n f ts
            ((fix G n (ts : tuple term n) : Q n ts :=
                match ts with
                  | tuple_nil => c_nil
                  | tuple_cons n t ts => c_cons n t ts (F t) (G n ts)
                end) n ts)
  end.

Definition free_term (v : var) : forall t : term, Prop :=
  term_terms_rect (fun _ => False) (* name *)
                  (fun _ => False) (* handle *)
                  (fun v' => v = v') (* var *)
                  (fun _ _ _ (IHts : Prop) => IHts) (* app *)
                  False (* nil *)
                  (fun _ _ _ IHt IHts => IHt \/ IHts). (* cons *)

(* (* Equivalent definition in terms of nested fixpoints. *)
Fixpoint free_term (v : var) (t : term) {struct t} : Prop :=
  match t with
    | Var v' => v = v'
    | App n f ts =>
      (fix free_terms (v : var) n (ts : tuple term n) {struct ts} :=
         match ts with
           | tuple_nil => False
           | tuple_cons n t ts => free_term v t \/ free_terms v n ts
         end) v ts
    | _ => False
  end.
*)

Definition free_terms v n (ts : tuple term n) :=
  tuple_fold (fun t p => free_term v t \/ p) ts False.

Lemma free_terms_app v n (ts : tuple term n) : forall f,
  free_terms v ts -> free_term v (App f ts).
  intros f H.
  simpl.
  clear f.
  induction ts.
  destruct H.
  induction H.
  left; assumption.
  right.
  apply IHts.
  assumption.
Qed.

Definition interp_term (m : model) (t : term) :
  (forall v : var, free_term v t -> m.(domain)) -> m.(domain).
  set (D := m.(domain)).
  apply term_terms_rect with
  (P := (fun t => (forall v : var, free_term v t -> D) -> D))
    (Q := fun n ts => (forall v : var, free_terms v ts -> D) -> tuple D n);
  clear t.
  (* name *)
  intros n ctx.
  exact (m.(interp_name) n).
  (* handle *)
  intros h ctx.
  exact (m.(interp_handle) h).
  (* var *)
  intros v ctx.
  apply (ctx v).
  simpl; reflexivity.
  (* app *)
  intros n f ts IHts ctx.
  apply (interp_func f).
  apply IHts.
  intros v H.
  apply (ctx v).
  apply free_terms_app.
  assumption.
  (* nil *)
  intro; exact (tuple_nil _).
  (* cons *)
  intros n t ts IHt IHts ctx.
  apply tuple_cons.
  apply IHt.
  intros v H.
  apply (ctx v).
  left; assumption.
  apply IHts.
  intros v H.
  apply (ctx v).
  right; assumption.
Defined.

Fixpoint free_formula (v : var) (f : formula) : Prop :=
  match f with
    | Predicate n p ts => free_terms v ts
    | And f1 f2 => free_formula v f1 \/ free_formula v f2
    | Or f1 f2 => free_formula v f1 \/ free_formula v f2
    | Not f => free_formula v f
    | Forall v' f => v <> v' /\ free_formula v f
    | Exists v' f => v <> v' /\ free_formula v f
    | _ => False
  end.

Definition interp_terms (m : model) n (ts : tuple term n)
           (ctx : forall v : var, free_terms v ts -> m.(domain))
: tuple m.(domain) n.
  induction ts as [| n t ts IHts].
  exact (tuple_nil _).
  apply tuple_cons.
  refine (interp_term (t:=t) _).
  intros v H.
  apply (ctx v).
  left; assumption.
  apply IHts.
  intros v H.
  apply (ctx v).
  right; assumption.
Defined.

Fixpoint interp_formula (m : model) (f : formula) {struct f}
         : (forall v : var, free_formula v f -> m.(domain)) -> Prop :=
  match f as f' return ((forall v : var, free_formula v f' -> _) -> _) with
    | Predicate n p ts => fun ctx =>
                            interp_predicate p (interp_terms (ts:=ts) ctx)
    | And f1 f2 => fun ctx =>
                     and (interp_formula (f:=f1)
                                         (fun v H => ctx v (or_introl H)))
                         (interp_formula (f:=f2)
                                         (fun v H => ctx v (or_intror H)))
    | Or f1 f2 => fun ctx =>
                    or (interp_formula (f:=f1)
                                       (fun v H => ctx v (or_introl H)))
                       (interp_formula (f:=f2)
                                       (fun v H => ctx v (or_intror H)))
    | Not f => fun ctx => ~(interp_formula (f:=f) ctx)
    | Forall v f =>
      fun ctx =>
        forall d : m.(domain),
          interp_formula (f:=f)
                         (fun v' H =>
                            match var_dec_eq v' v with
                              | left veqv' => d
                              | right vneqv' => ctx v' (conj vneqv' H)
                            end)
    | Exists v f =>
      fun ctx =>
        exists d : m.(domain),
          interp_formula (f:=f)
                         (fun v' H =>
                            match var_dec_eq v' v with
                              | left veqv' => d
                              | right vneqv' => ctx v' (conj vneqv' H)
                            end)
    | FTrue => fun _ => True
    | FFalse => fun _ => False
  end.

Definition closed f := forall v, ~free_formula v f.

Definition closed_formula := {f : formula & closed f}.

Definition interp_closed_formula (m : model) (f : formula)
           (H : closed f) : Prop.
  refine (interp_formula (m:=m) (f:=f) _).
  intros v H'.
  destruct (H v H').
Defined.
