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
| Exists : var -> formula -> formula
| FTrue : formula
| FFalse : formula.

Record model (D : Type) := Model
                             {interp_func : forall n, func n -> tuple D n -> D;
                              interp_name : name -> D;
                              interp_handle : handle -> D;
                              interp_predicate : forall n, predicate n ->
                                                           tuple D n -> Prop}.

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
  term_terms_rect (fun _ => False)
                  (fun _ => False)
                  (fun v' => v = v')
                  (fun _ _ _ (IHts : Prop) => IHts)
                  False
                  (fun _ _ _ IHt IHts => IHt \/ IHts).

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

Definition interp_term (D : Type) (m : model D) (t : term) :
  (forall v : var, free_term v t -> D) -> D.
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
  apply (m.(interp_func) f).
  apply IHts.
  intros v H.
  apply (ctx v).
  apply free_terms_app.
  assumption.
  (* nil *)
  intro; exact (tuple_nil D).
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

Definition interp_terms (D : Type) (m : model D) n (ts : tuple term n)
           (ctx : forall v : var, free_terms v ts -> D) : tuple D n.
  induction ts as [| n t ts IHts].
  exact (tuple_nil D).
  apply tuple_cons.
  refine (interp_term m (t:=t) _).
  intros v H.
  apply (ctx v).
  left; assumption.
  apply IHts.
  intros v H.
  apply (ctx v).
  right; assumption.
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
    | FTrue => fun _ => True
    | FFalse => fun _ => False
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
