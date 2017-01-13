Require Import FCF.
Require Import Asymptotic.
Require Import Tactics.

Section Language.
  Context {base_type : Set} {interp_base_type:base_type->Set}.

  Inductive type := Type_base (t:base_type) | Type_arrow (dom:type) (cod:type).
  Global Coercion Type_base : base_type >-> type.
  Fixpoint interp_type (t:type) : Set :=
    match t with
    | Type_base t => interp_base_type t
    | Type_arrow dom cod => interp_type dom -> interp_type cod
    end.

  Context {message list_message rand : base_type}.
  Inductive term : type -> Type :=
  | Term_const {t} (_:interp_type t) : term t
  | Term_random (_:nat) : term rand
  | Term_adversarial (_:term list_message) : term message
  | Term_app {dom cod} (_:term (Type_arrow dom cod)) (_:term dom) : term cod.

  (* the first natural number that is not a valid randomness index *)
  Fixpoint rand_end {t:type} (e:term t) : nat :=
    match e with
    | Term_random n => S n
    | Term_app f x => max (rand_end f) (rand_end x)
    | _ => 0
    end.

  Context (interp_random : nat -> interp_type rand).
  Context (interp_adversarial : interp_type list_message -> interp_type message).
  Fixpoint interp_term
           {t} (e:term t) : interp_type t :=
    match e with
    | Term_const c => c
    | Term_random n => interp_random n
    | Term_adversarial ctx => interp_adversarial (interp_term ctx)
    | Term_app f x => (interp_term f) (interp_term x)
    end.
End Language.
Arguments type : clear implicits.
Arguments interp_type {_} _ _.
Arguments term {_} _ _ _ _ _.
Arguments rand_end [_ _ _ _ _ _] _.

Section CompInterp.
  Inductive base_type := BaseType_bool | BaseType_message | BaseType_list_message.
  Definition interp_base_type t :=
    match t with
    | BaseType_bool => bool
    | BaseType_message => list bool
    | BaseType_list_message => list (list bool)
    end.
  Let term := (term interp_base_type BaseType_message BaseType_list_message BaseType_message).

  (* different protocols may use different amounts of randomness at the same security level. this is an awkward and boring parameter *)
  Context (rand_size : nat -> nat).

  Section WithAdversary.
    (* the adversary is split into three parts for no particular reason. It first decides how much randomness it will need, then interacts with the protocol (repeated calls to [adverary] with all messages up to now as input), and then tries to claim victory ([distinguisher]). There is no explicit sharing of state between these procedures, but all of them get the same random inputs in the security game. The handling of state is a major difference between FCF [OracleComp] and this framework *)
    Context (evil_rand_tape_len : nat -> nat).
    Context (adversary:nat -> list bool -> list (list bool) -> list bool).
    Context (distinguisher: forall {t}, nat -> list bool -> interp_type interp_base_type t -> bool).

    Definition comp_interp_term (good_rand_tape evil_rand_tape:list bool) eta {t} (e:term t) :=
      let interp_random (n:nat) : interp_type interp_base_type (Type_base BaseType_message)
          := List.firstn (rand_size eta) (List.skipn (n * rand_size eta) good_rand_tape) in
      let interp_adversarial : interp_type interp_base_type (Type_arrow (Type_base BaseType_list_message) (Type_base BaseType_message))
          := adversary eta evil_rand_tape in
      interp_term interp_random interp_adversarial e.

    Definition universal_security_game eta {t:type base_type} (e:term t) : Comp bool :=
      good_rand_tape' <-$ {0,1}^(rand_end e * rand_size eta);
        evil_rand_tape' <-$ {0,1}^(evil_rand_tape_len eta);
        let good_rand_tape := Vector.to_list good_rand_tape' in
        let evil_rand_tape := Vector.to_list evil_rand_tape' in
        let out := comp_interp_term good_rand_tape evil_rand_tape eta e in
        ret (distinguisher _ eta evil_rand_tape out).
  End WithAdversary.

  Definition indist {t:type base_type} (a b:term t) : Prop :=  forall l adv dst,
      (* TODO: insert bounds on coputational complexity of [adv] and [dst] here *)
      let game eta e := universal_security_game l adv dst eta e in
      negligible (fun eta => | Pr[game eta a] -  Pr[game eta b] | ).
End CompInterp.

Section SymbolicProof.
  Context {base_type : Set} {interp_base_type : base_type -> Set}.
  Local Coercion type_base (t:base_type) : type base_type := Type_base t.
  Context {message list_message rand bool : base_type}.
  Local Notation term := (term interp_base_type message list_message rand).
  Context (indist : forall {t : type base_type}, term t -> term t -> Prop). Arguments indist {_} _ _.

  Context (if_then_else : forall {t}, term (Type_arrow bool (Type_arrow t (Type_arrow t t)))). Arguments if_then_else {_}.
  Context (indist_rand: forall x y, indist (Term_random x) (Term_random y)).
  Context (indist_if_then_else_irrelevant_l : forall t (x y:term t),
              indist x y -> forall b:term bool, indist (Term_app (Term_app (Term_app if_then_else b) x) y) x).

  Lemma indist_if_then_else_rand_l (b:term bool) (x y:nat) :
    indist (Term_app (Term_app (Term_app if_then_else b) (Term_random x)) (Term_random y)) (Term_random x).
  Proof. exact (indist_if_then_else_irrelevant_l _ _ _ (indist_rand x y) _). Qed.
End SymbolicProof.

Definition if_then_else {t : type base_type}
  : interp_type interp_base_type (Type_arrow (type_base BaseType_bool) (Type_arrow t (Type_arrow t t)))
  := fun (b : bool) (x y : interp_type interp_base_type t) => if b then x else y.

(** proving soundness of symbolic axioms *)

Axiom random_size : nat -> nat.
Goal False.
  pose proof (fun A B => indist_if_then_else_rand_l (bool:=BaseType_bool) (@indist random_size) (fun _ => Term_const if_then_else) A B) as H.
  match type of H with ?A -> ?C => assert A as HA; [clear H|specialize(H HA);clear HA] end.

(* 2 subgoals, subgoal 1 (ID 30) *)
  
(*   ============================ *)
(*   forall x y : nat, x <> y -> indist id (Term_random x) (Term_random y) *)

  cbv [rand_end indist universal_security_game comp_interp_term interp_term]. (* to monadic probability notation *)
  intros.
  pose proof negligible_const_num 1.
  eapply negligible_le; [intro eta;etransitivity|..]. {
    setoid_rewrite evalDist_commute.
    rewrite !mult_succ_l.
    generalize (random_size eta) as D; intro D.
    eapply evalDist_bind_distance.
    { eapply well_formed_Rnd. }
    { intros. reflexivity. }
    { intros evil_rand_tape probe Hevil_rand_tape.
      set (dst (Type_base BaseType_message) eta (Vector.to_list evil_rand_tape)) as attack.
      SearchAbout (Rnd (_ + _)).
      SearchAbout (Bind (Ret _ _) _).
      SearchAbout Bind Ret.
      SearchAbout evalDist Bind.



(* 2 subgoals, subgoal 1 (ID 34) *)
  
(*   ============================ *)
(*   forall x y : nat, *)
(*   x <> y -> *)
(*   forall (l : nat -> nat) (adv : nat -> list bool -> list (list bool) -> list bool) *)
(*     (dst : forall t : type base_type, nat -> list bool -> interp_type interp_base_type t -> bool), *)
(*   negligible *)
(*     (fun eta : nat => *)
(*      | *)
(*      Pr [good_rand_tape' <-$ { 0 , 1 }^ S x * id eta; *)
(*          evil_rand_tape' <-$ { 0 , 1 }^ l eta; *)
(*          ret dst (Type_base BaseType_message) eta (Vector.to_list evil_rand_tape') *)
(*                (interp_term *)
(*                   (fun n : nat => firstn (id eta) (skipn (n * id eta) (Vector.to_list good_rand_tape'))) *)
(*                   (adv eta (Vector.to_list evil_rand_tape')) (Term_random x)) ] - *)
(*      Pr [good_rand_tape' <-$ { 0 , 1 }^ S y * id eta; *)
(*          evil_rand_tape' <-$ { 0 , 1 }^ l eta; *)
(*          ret dst (Type_base BaseType_message) eta (Vector.to_list evil_rand_tape') *)
(*                (interp_term *)
(*                   (fun n : nat => firstn (id eta) (skipn (n * id eta) (Vector.to_list good_rand_tape'))) *)
(*                   (adv eta (Vector.to_list evil_rand_tape')) (Term_random y)) ] |) *)

  (* This probably could be proven in this form -- the argument is that the two subsequences of the good random tape that are given to [dst] are non-overlapping. *)

  
  simpl. (* to raw probability equations *)
  
(* 2 subgoals, subgoal 1 (ID 141) *)
  
(*   ============================ *)
(*   forall x y : nat, *)
(*   x <> y -> *)
(*   forall l : nat -> nat, *)
(*   (nat -> list bool -> list (list bool) -> list bool) -> *)
(*   forall dst : forall t : type base_type, nat -> list bool -> interp_type interp_base_type t -> bool, *)
(*   negligible *)
(*     (fun eta : nat => *)
(*      | *)
(*      sumList (getAllBvectors (id eta + x * id eta)) *)
(*        (fun b : Bvector (id eta + x * id eta) => *)
(*         1 / expnat 2 (id eta + x * id eta) * *)
(*         sumList (getAllBvectors (l eta)) *)
(*           (fun b0 : Bvector (l eta) => *)
(*            1 / expnat 2 (l eta) * *)
(*            (if *)
(*              EqDec_dec bool_EqDec *)
(*                (dst (Type_base BaseType_message) eta (Vector.to_list b0) *)
(*                   (firstn (id eta) (skipn (x * id eta) (Vector.to_list b)))) true *)
(*             then 1 *)
(*             else 0))) - *)
(*      sumList (getAllBvectors (id eta + y * id eta)) *)
(*        (fun b : Bvector (id eta + y * id eta) => *)
(*         1 / expnat 2 (id eta + y * id eta) * *)
(*         sumList (getAllBvectors (l eta)) *)
(*           (fun b0 : Bvector (l eta) => *)
(*            1 / expnat 2 (l eta) * *)
(*            (if *)
(*              EqDec_dec bool_EqDec *)
(*                (dst (Type_base BaseType_message) eta (Vector.to_list b0) *)
(*                   (firstn (id eta) (skipn (y * id eta) (Vector.to_list b)))) true *)
(*             then 1 *)
(*             else 0))) |) *)