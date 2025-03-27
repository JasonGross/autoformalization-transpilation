(** * LibSepReference: Appendix - The Full Construction *)

(** This file provides an end-to-end construction of a weakest-precondition
    style characteristic formula generator (the function named [wpgen] in
    chapter [WPgen]), for a core programming language with programs assumed
    to be in A-normal form, including support for records with up to 3 fields. *)

Set Implicit Arguments.
From SLF Require Export LibCore.
From SLF Require Export LibSepTLCbuffer LibSepVar LibSepFmap.
From SLF Require LibSepSimpl.
Module Fmap := LibSepFmap. (* Short name for Fmap module. *)

(* ################################################################# *)
(** * Imports *)

(* ================================================================= *)
(** ** Extensionality Axioms *)

(** These standard extensionality axioms may also be found in
    the [LibAxiom.v] file associated with the TLC library. *)

Axiom functional_extensionality : forall A B (f g:A->B),
  (forall x, f x = g x) ->
  f = g.

Axiom propositional_extensionality : forall (P Q:Prop),
  (P <-> Q) ->
  P = Q.

(* ================================================================= *)
(** ** Variables *)

(** The file [LibSepVar.v], whoses definitions are imported in the header to
    the present file, defines the type [var] as an alias for [string].
    It also provides the boolean function [var_eq x y] to compare two variables,
    and the tactic [case_var] to perform case analysis on expressions of the
    form [if var_eq x y then .. else ..] that appear in the goal. *)

(* ================================================================= *)
(** ** Finite Maps *)

(** The file [LibSepFmap.v], which is bound by the short name [Fmap] in the
    header, provides a formalization of finite maps. These maps are used to
    represent heaps in the semantics. The library provides a tactic called
    [fmap_disjoint] to automate disjointness proofs, and a tactic called
    [fmap_eq] for proving equalities between heaps modulo associativity and
    commutativity. Without these two tactics, proofs involving finite maps
    would be much more tedious and fragile. *)

(* ################################################################# *)
(** * Source Language *)

(* ================================================================= *)
(** ** Syntax *)

(** The grammar of primitive operations includes a number of operations. *)

Inductive prim : Type :=
  | val_ref : prim
  | val_get : prim
  | val_set : prim
  | val_free : prim
  | val_neg : prim
  | val_opp : prim
  | val_eq : prim
  | val_add : prim
  | val_neq : prim
  | val_sub : prim
  | val_mul : prim
  | val_div : prim
  | val_mod : prim
  | val_rand : prim
  | val_le : prim
  | val_lt : prim
  | val_ge : prim
  | val_gt : prim
  | val_ptr_add : prim.

(** Locations are defined as natural numbers. *)

Definition loc : Type := nat.

(** The null location corresponds to address zero. *)

Definition null : loc := 0%nat.

(** The grammar of closed values includes includes basic values such as [int]
    and [bool], but also locations, closures. It also includes two special
    values, [val_uninit] used in the formalization of arrays, and [val_error]
    used for stating semantics featuring error-propagation. *)

Inductive val : Type :=
  | val_unit : val
  | val_bool : bool -> val
  | val_int : int -> val
  | val_loc : loc -> val
  | val_prim : prim -> val
  | val_fun : var -> trm -> val
  | val_fix : var -> var -> trm -> val
  | val_uninit : val
  | val_error : val

(** The grammar of terms includes values, variables, functions, applications,
    sequence, let-bindings, and conditions. Sequences are redundant with
    let-bindings, but are useful in practice to avoid binding dummy names,
    and serve on numerous occasion as a warm-up before proving results on
    let-bindings. *)

with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_fun : var -> trm -> trm
  | trm_fix : var -> var -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_seq : trm -> trm -> trm
  | trm_let : var -> trm -> trm -> trm
  | trm_if : trm -> trm -> trm -> trm.

(** A state, a.k.a. [heap], consists of a finite map from location to values.
    Records and arrays are represented as sets of consecutive cells, preceeded
    by a header field describing the length of the block. *)

Definition heap : Type := fmap loc val.

(* ================================================================= *)
(** ** Coq Tweaks *)

(** [h1 \u h2] is a notation for union of two heaps. *)

Notation "h1 \u h2" := (Fmap.union h1 h2)
  (at level 37, right associativity).

(** Implicit types associated with meta-variables. *)

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types p : loc.
Implicit Types n : int.
Implicit Types v w r vf vx : val.
Implicit Types t : trm.
Implicit Types h s : heap.

(** The types of values and terms are inhabited. *)

Global Instance Inhab_val : Inhab val.
Proof using. apply (Inhab_of_val val_unit). Qed.

Global Instance Inhab_trm : Inhab trm.
Proof using. apply (Inhab_of_val (trm_val val_unit)). Qed.

(** Coercions to improve conciseness in the statment of evaluation rules. *)

Coercion val_bool : bool >-> val.
Coercion val_int : Z >-> val.
Coercion val_loc : loc >-> val.
Coercion val_prim : prim >-> val.

Coercion trm_val : val >-> trm.
Coercion trm_var : var >-> trm.
Coercion trm_app : trm >-> Funclass.

(* ================================================================= *)
(** ** Values and Substitutions *)

(** The predicate [trm_is_val t] asserts that [t] is a value. *)

Definition trm_is_val (t:trm) : Prop :=
  match t with trm_val v => True | _ => False end.

(** The standard capture-avoiding substitution, written [subst x v t]. *)

Fixpoint subst (y:var) (v':val) (t:trm) : trm :=
  let aux t := subst y v' t in
  let if_y_eq x t1 t2 := if var_eq x y then t1 else t2 in
  match t with
  | trm_val v => trm_val v
  | trm_var x => if_y_eq x (trm_val v') t
  | trm_fun x t1 => trm_fun x (if_y_eq x t1 (aux t1))
  | trm_fix f x t1 => trm_fix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1)))
  | trm_app t1 t2 => trm_app (aux t1) (aux t2)
  | trm_seq t1 t2 => trm_seq  (aux t1) (aux t2)
  | trm_let x t1 t2 => trm_let x (aux t1) (if_y_eq x t2 (aux t2))
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  end.

(* ================================================================= *)
(** ** Small-Step Semantics *)

(** The judgment [step s t s' t'] asserts that the configuration [(s,t)]
    can take one reduction step towards the program configuration [(s',t')]. *)

Inductive step : heap -> trm -> heap -> trm -> Prop :=

  (* Context rules *)
  | step_seq_ctx : forall s1 s2 t1 t1' t2,
      step s1 t1 s2 t1' ->
      step s1 (trm_seq t1 t2) s2 (trm_seq t1' t2)
  | step_let_ctx : forall s1 s2 x t1 t1' t2,
      step s1 t1 s2 t1' ->
      step s1 (trm_let x t1 t2) s2 (trm_let x t1' t2)
  | step_app_arg1 : forall s1 s2 t1 t1' t2,
      step s1 t1 s2 t1' ->
      step s1 (trm_app t1 t2) s2 (trm_app t1' t2)
  | step_app_arg2 : forall s1 s2 v1 t2 t2',
      step s1 t2 s2 t2' ->
      step s1 (trm_app v1 t2) s2 (trm_app v1 t2')

  (* Reductions *)
  | step_fun : forall s x t1,
      step s (trm_fun x t1) s (val_fun x t1)
  | step_fix : forall s f x t1,
      step s (trm_fix f x t1) s (val_fix f x t1)
  | step_app_fun : forall s v1 v2 x t1,
      v1 = val_fun x t1 ->
      step s (trm_app v1 v2) s (subst x v2 t1)
  | step_app_fix : forall s v1 v2 f x t1,
      v1 = val_fix f x t1 ->
      step s (trm_app v1 v2) s (subst x v2 (subst f v1 t1))
  | step_if : forall s b t1 t2,
      step s (trm_if (val_bool b) t1 t2) s (if b then t1 else t2)
  | step_seq : forall s t2 v1,
      step s (trm_seq v1 t2) s t2
  | step_let : forall s x t2 v1,
      step s (trm_let x v1 t2) s (subst x v1 t2)

  (* Unary operations *)
  | step_neg : forall s b,
      step s (val_neg (val_bool b)) s (val_bool (neg b))
  | step_opp : forall s n,
      step s (val_opp (val_int n)) s (val_int (- n))
  | step_rand : forall s n n1,
      0 <= n1 < n ->
      step s (val_rand (val_int n)) s (val_int n1)

  (* Binary operations *)
  | step_eq : forall s v1 v2,
      step s (val_eq v1 v2) s (val_bool (isTrue (v1 = v2)))
  | step_neq : forall s v1 v2,
      step s (val_neq v1 v2) s (val_bool (isTrue (v1 <> v2)))
  | step_add : forall s n1 n2,
      step s (val_add (val_int n1) (val_int n2)) s (val_int (n1 + n2))
  | step_sub : forall s n1 n2,
      step s (val_sub (val_int n1) (val_int n2)) s (val_int (n1 - n2))
  | step_mul : forall s n1 n2,
      step s (val_mul (val_int n1) (val_int n2)) s (val_int (n1 * n2))
  | step_div : forall s n1 n2,
      n2 <> 0 ->
      step s (val_div (val_int n1) (val_int n2)) s (Z.quot n1 n2)
  | step_mod : forall s n1 n2,
      n2 <> 0 ->
      step s (val_mod (val_int n1) (val_int n2)) s (Z.rem n1 n2)
  | step_le : forall s n1 n2,
      step s (val_le (val_int n1) (val_int n2)) s (val_bool (isTrue (n1 <= n2)))
  | step_lt : forall s n1 n2,
      step s (val_lt (val_int n1) (val_int n2)) s (val_bool (isTrue (n1 < n2)))
  | step_ge : forall s n1 n2,
      step s (val_ge (val_int n1) (val_int n2)) s (val_bool (isTrue (n1 >= n2)))
  | step_gt : forall s n1 n2,
      step s (val_gt (val_int n1) (val_int n2)) s (val_bool (isTrue (n1 > n2)))
  | step_ptr_add : forall s p1 p2 n,
      (p2:int) = p1 + n ->
      step s (val_ptr_add (val_loc p1) (val_int n)) s (val_loc p2)

  (* Heap operations *)
  | step_ref : forall s v p,
      ~ Fmap.indom s p ->
      step s (val_ref v) (Fmap.update s p v) (val_loc p)
  | step_get : forall s p,
      Fmap.indom s p ->
      step s (val_get (val_loc p)) s (Fmap.read s p)
  | step_set : forall s p v,
      Fmap.indom s p ->
      step s (val_set (val_loc p) v) (Fmap.update s p v) val_unit
  | step_free : forall s p,
      Fmap.indom s p ->
      step s (val_free (val_loc p)) (Fmap.remove s p) val_unit.

(** The judgment [steps s t s' t'] corresponds to the reflexive-transitive
  closure of [step]. Concretely, this judgment asserts that the configuration
  [(s,t)] can reduce in zero, one, or several steps to [(s',t')]. *)

Inductive steps : heap -> trm -> heap -> trm -> Prop :=
  | steps_refl : forall s t,
      steps s t s t
  | steps_step : forall s1 s2 s3 t1 t2 t3,
      step s1 t1 s2 t2 ->
      steps s2 t2 s3 t3 ->
      steps s1 t1 s3 t3.

Lemma steps_of_step : forall s1 s2 t1 t2,
  step s1 t1 s2 t2 ->
  steps s1 t1 s2 t2.
Proof using. introv M. applys steps_step M. applys steps_refl. Qed.

Lemma steps_trans : forall s1 s2 s3 t1 t2 t3,
  steps s1 t1 s2 t2 ->
  steps s2 t2 s3 t3 ->
  steps s1 t1 s3 t3.
Proof using. introv M1. induction M1; introv M2. { auto. } { constructors*. } Qed.

(** The predicate [reducible s t] asserts that the configuration [(s,t)]
    can take a step. *)

Definition reducible (s:heap) (t:trm) : Prop :=
  exists s' t', step s t s' t'.

(** The predicate [notstuck s t] asserts that [t] is a value or is reducible. *)

Definition notstuck (s:heap) (t:trm) : Prop :=
  trm_is_val t \/ reducible s t.

(* ================================================================= *)
(** ** Omni-Big-Step Semantics of primitive operations *)

(** Evaluation rules for unary operations are captured by the predicate
    [evalunop op v1 P], which asserts that [op v1] evaluates to a value
    [v2] satisfying [P]. *)

Inductive evalunop : prim -> val -> (val->Prop) -> Prop :=
  | evalunop_neg : forall b1,
      evalunop val_neg (val_bool b1) (= val_bool (neg b1))
  | evalunop_opp : forall n1,
      evalunop val_opp (val_int n1) (= val_int (- n1))
  | evalunop_rand : forall n,
      n > 0 ->
      evalunop val_rand (val_int n) (fun r => exists n1, r = val_int n1 /\ 0 <= n1 < n).

(** Evaluation rules for binary operations are captured by the predicate
    [redupop op v1 v2 P], which asserts that [op v1 v2] evaluates to a
    value [v3] satisfying [P]. *)

Inductive evalbinop : val -> val -> val -> (val->Prop) -> Prop :=
  | evalbinop_eq : forall v1 v2,
      evalbinop val_eq v1 v2 (= val_bool (isTrue (v1 = v2)))
  | evalbinop_neq : forall v1 v2,
      evalbinop val_neq v1 v2 (= val_bool (isTrue (v1 <> v2)))
  | evalbinop_add : forall n1 n2,
      evalbinop val_add (val_int n1) (val_int n2) (= val_int (n1 + n2))
  | evalbinop_sub : forall n1 n2,
      evalbinop val_sub (val_int n1) (val_int n2) (= val_int (n1 - n2))
  | evalbinop_mul : forall n1 n2,
      evalbinop val_mul (val_int n1) (val_int n2) (= val_int (n1 * n2))
  | evalbinop_div : forall n1 n2,
      n2 <> 0 ->
      evalbinop val_div (val_int n1) (val_int n2) (= val_int (Z.quot n1 n2))
  | evalbinop_mod : forall n1 n2,
      n2 <> 0 ->
      evalbinop val_mod (val_int n1) (val_int n2) (= val_int (Z.rem n1 n2))
  | evalbinop_le : forall n1 n2,
      evalbinop val_le (val_int n1) (val_int n2) (= val_bool (isTrue (n1 <= n2)))
  | evalbinop_lt : forall n1 n2,
      evalbinop val_lt (val_int n1) (val_int n2) (= val_bool (isTrue (n1 < n2)))
  | evalbinop_ge : forall n1 n2,
      evalbinop val_ge (val_int n1) (val_int n2) (= val_bool (isTrue (n1 >= n2)))
  | evalbinop_gt : forall n1 n2,
      evalbinop val_gt (val_int n1) (val_int n2) (= val_bool (isTrue (n1 > n2)))
  | evalbinop_ptr_add : forall p1 p2 n,
      (p2:int) = p1 + n ->
      evalbinop val_ptr_add (val_loc p1) (val_int n) (= val_loc p2).

(* ================================================================= *)
(** ** Omni-Big-Step Semantics *)

Section Eval.

(** The predicate [purepost s P] converts a predicate [P:val->Prop] into
    a postcondition of type [val->heap->Prop] that holds in the state [s]. *)

Definition purepost (s:heap) (P:val->Prop) : val->heap->Prop :=
  fun v s' => P v /\ s' = s.

Definition purepostin (s:heap) (P:val->Prop) (Q:val->heap->Prop) : Prop :=
  (* equivalent to [purepost S P ===> Q] *)
  forall v, P v -> Q v s.

(** Omni-Big-step evaluation judgement, written [eval s t Q]. *)

Implicit Types Q : val->heap->Prop.

Inductive eval : heap -> trm -> (val->heap->Prop) -> Prop :=
  | eval_val : forall s v Q,
      Q v s ->
      eval s (trm_val v) Q
  | eval_fun : forall s x t1 Q,
      Q (val_fun x t1) s ->
      eval s (trm_fun x t1) Q
  | eval_fix : forall s f x t1 Q,
      Q (val_fix f x t1) s ->
      eval s (trm_fix f x t1) Q
  | eval_app_arg1 : forall s1 t1 t2 Q1 Q,
      ~ trm_is_val t1 ->
      eval s1 t1 Q1 ->
      (forall v1 s2, Q1 v1 s2 -> eval s2 (trm_app v1 t2) Q) ->
      eval s1 (trm_app t1 t2) Q
  | eval_app_arg2 : forall s1 v1 t2 Q1 Q,
      ~ trm_is_val t2 ->
      eval s1 t2 Q1 ->
      (forall v2 s2, Q1 v2 s2 -> eval s2 (trm_app v1 v2) Q) ->
      eval s1 (trm_app v1 t2) Q
  | eval_app_fun : forall s1 v1 v2 x t1 Q,
      v1 = val_fun x t1 ->
      eval s1 (subst x v2 t1) Q ->
      eval s1 (trm_app v1 v2) Q
  | eval_app_fix : forall s v1 v2 f x t1 Q,
      v1 = val_fix f x t1 ->
      eval s (subst x v2 (subst f v1 t1)) Q ->
      eval s (trm_app v1 v2) Q
  | eval_seq : forall Q1 s t1 t2 Q,
      eval s t1 Q1 ->
      (forall v1 s2, Q1 v1 s2 -> eval s2 t2 Q) ->
      eval s (trm_seq t1 t2) Q
  | eval_let : forall Q1 s x t1 t2 Q,
      eval s t1 Q1 ->
      (forall v1 s2, Q1 v1 s2 -> eval s2 (subst x v1 t2) Q) ->
      eval s (trm_let x t1 t2) Q
  | eval_if : forall s (b:bool) t1 t2 Q,
      eval s (if b then t1 else t2) Q ->
      eval s (trm_if (val_bool b) t1 t2) Q
  | eval_unop : forall op s v1 P Q,
      evalunop op v1 P ->
      purepostin s P Q ->
      eval s (op v1) Q
  | eval_binop : forall op s v1 v2 P Q,
      evalbinop op v1 v2 P ->
      purepostin s P Q ->
      eval s (op v1 v2) Q
  | eval_ref : forall s v Q,
      (forall p, ~ Fmap.indom s p ->
          Q (val_loc p) (Fmap.update s p v)) ->
      eval s (val_ref v) Q
  | eval_get : forall s p Q,
      Fmap.indom s p ->
      Q (Fmap.read s p) s ->
      eval s (val_get (val_loc p)) Q
  | eval_set : forall s p v Q,
      Fmap.indom s p ->
      Q val_unit (Fmap.update s p v) ->
      eval s (val_set (val_loc p) v) Q
  | eval_free : forall s p Q,
      Fmap.indom s p ->
      Q val_unit (Fmap.remove s p) ->
      eval s (val_free (val_loc p)) Q.

(** Specialized rule for values, to instantiate the postcondition *)

Lemma eval_val_minimal : forall s v,
  eval s (trm_val v) (fun v' s' => (v' = v) /\ (s' = s)).
Proof using. intros. applys* eval_val. Qed.

(** Specialized evaluation rules for selected operations, to avoid the
    indirection via [eval_unop] and [eval_binop] in the course. *)

Lemma eval_add : forall s n1 n2 Q,
  Q (val_int (n1 + n2)) s ->
  eval s (val_add (val_int n1) (val_int n2)) Q.
Proof using.
  intros. applys* eval_binop.
  { applys* evalbinop_add. }
  { intros ? ->. auto. }
Qed.

Lemma eval_div : forall s n1 n2 Q,
  n2 <> 0 ->
  Q (val_int (Z.quot n1 n2)) s ->
  eval s (val_div (val_int n1) (val_int n2)) Q.
Proof using.
  intros. applys* eval_binop.
  { applys* evalbinop_div. }
  { intros ? ->. auto. }
Qed.

Lemma eval_rand : forall s n Q,
  n > 0 ->
  (forall n1, 0 <= n1 < n -> Q n1 s) ->
  eval s (val_rand (val_int n)) Q.
Proof using.
  intros. applys* eval_unop.
  { applys* evalunop_rand. }
  { intros ? (?&->&?). auto. }
Qed.

(** Derived rule for reasoning about an applications, without need to
    perform a case analysis on whether the entities are already values. *)

Lemma eval_app_arg1' : forall s1 t1 t2 Q1 Q,
  eval s1 t1 Q1 ->
  (forall v1 s2, Q1 v1 s2 -> eval s2 (trm_app v1 t2) Q) ->
  eval s1 (trm_app t1 t2) Q.
Proof using.
  introv M1 M2. tests C1: (trm_is_val t1).
  { destruct t1; tryfalse. inverts M1. applys* M2. }
  { applys* eval_app_arg1. }
Qed.

Lemma eval_app_arg2' : forall s1 v1 t2 Q1 Q,
  eval s1 t2 Q1 ->
  (forall v2 s2, eval s2 (trm_app v1 v2) Q) ->
  eval s1 (trm_app v1 t2) Q.
Proof using.
  introv M1 M2. tests C1: (trm_is_val t2).
  { destruct t2; tryfalse. inverts M1. applys* M2. }
  { applys* eval_app_arg2. }
Qed.

(** [eval_like t1 t2] asserts that [t2] evaluates like [t1]. In particular,
    this relation hold whenever [t2] reduces in small-step to [t1]. *)

Definition eval_like (t1 t2:trm) : Prop :=
  forall s Q, eval s t1 Q -> eval s t2 Q.

End Eval.

(* ################################################################# *)
(** * Heap Predicates *)

(** We next define heap predicates and establish their properties. All this
    material is wrapped in a module, allowing us to instantiate the functor from
    chapter [LibSepSimpl] that defines the tactic [xsimpl]. *)
Module SepSimplArgs.

(* ================================================================= *)
(** ** Hprop and Entailment *)

Declare Scope hprop_scope.
Open Scope hprop_scope.

(** The type of heap predicates is named [hprop]. *)

Definition hprop := heap -> Prop.

(** Implicit types for meta-variables. *)

Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.

(** Entailment for heap predicates, written [H1 ==> H2]. This entailment
    is linear. *)

Definition himpl (H1 H2:hprop) : Prop :=
  forall h, H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55) : hprop_scope.

(** Entailment between postconditions, written [Q1 ===> Q2]. *)

Definition qimpl A (Q1 Q2:A->hprop) : Prop :=
  forall (v:A), Q1 v ==> Q2 v.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2) (at level 55) : hprop_scope.

(* ================================================================= *)
(** ** Definition of Heap Predicates *)

(** The core heap predicates are defined next, together with the
    associated notation:

    - [\[]] denotes the empty heap predicate
    - [\[P]] denotes a pure fact
    - [\Top] denotes the true heap predicate (affine)
    - [p ~~> v] denotes a singleton heap
    - [H1 \* H2] denotes the separating conjunction
    - [Q1 \*+ H2] denotes the separating conjunction extending a postcondition
    - [\exists x, H] denotes an existential quantifier
    - [\forall x, H] denotes a universal quantifier
    - [H1 \-* H2] denotes a magic wand between heap predicates
    - [Q1 \--* Q2] denotes a magic wand between postconditions. *)

Definition hempty : hprop :=
  fun h => (h = Fmap.empty).

Definition hsingle (p:loc) (v:val) : hprop :=
  fun h => (h = Fmap.single p v).

Definition hstar (H1 H2 : hprop) : hprop :=
  fun h => exists h1 h2, H1 h1
                              /\ H2 h2
                              /\ Fmap.disjoint h1 h2
                              /\ h = Fmap.union h1 h2.

Definition hexists A (J:A->hprop) : hprop :=
  fun h => exists x, J x h.

Definition hforall (A : Type) (J : A -> hprop) : hprop :=
  fun h => forall x, J x h.

Notation "\[]" := (hempty)
  (at level 0) : hprop_scope.

Notation "p '~~>' v" := (hsingle p v) (at level 32) : hprop_scope.

Notation "H1 '\*' H2" := (hstar H1 H2)
  (at level 41, right associativity) : hprop_scope.

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.

Notation "'\forall' x1 .. xn , H" :=
  (hforall (fun x1 => .. (hforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\forall' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.

(** The remaining operators are defined in terms of the preivous above,
    rather than directly as functions over heaps. Doing so reduces the
    amount of proofs, by allowing to better leverage the tactic [xsimpl]. *)

Definition hpure (P:Prop) : hprop :=
  \exists (p:P), \[].

Definition htop : hprop :=
  \exists (H:hprop), H.

Definition hwand (H1 H2 : hprop) : hprop :=
  \exists H0, H0 \* hpure ((H1 \* H0) ==> H2).

Definition qwand A (Q1 Q2:A->hprop) : hprop :=
  \forall x, hwand (Q1 x) (Q2 x).

Notation "\[ P ]" := (hpure P)
  (at level 0, format "\[ P ]") : hprop_scope.

Notation "\Top" := (htop) : hprop_scope.

Notation "Q \*+ H" := (fun x => hstar (Q x) H)
  (at level 40) : hprop_scope.

Notation "H1 \-* H2" := (hwand H1 H2)
  (at level 43, right associativity) : hprop_scope.

Notation "Q1 \--* Q2" := (qwand Q1 Q2)
  (at level 43) : hprop_scope.

(* ================================================================= *)
(** ** Basic Properties of Separation Logic Operators *)

(* ----------------------------------------------------------------- *)
(** *** Tactic for Automation *)

(** We set up [auto] to process goals of the form [h1 = h2] by calling
    [fmap_eq], which proves equality modulo associativity and commutativity. *)

#[global] Hint Extern 1 (_ = _ :> heap) => fmap_eq.

(** We also set up [auto] to process goals of the form [Fmap.disjoint h1 h2]
    by calling the tactic [fmap_disjoint], which essentially normalizes all
    disjointness goals and hypotheses, split all conjunctions, and invokes
    proof search with a base of hints specified in [LibSepFmap.v]. *)

Import Fmap.DisjointHints.

Tactic Notation "fmap_disjoint_pre" :=
  subst; rew_disjoint; jauto_set.

#[global] Hint Extern 1 (Fmap.disjoint _ _) => fmap_disjoint_pre.

(* ----------------------------------------------------------------- *)
(** *** Properties of [himpl] and [qimpl] *)

Lemma himpl_refl : forall H,
  H ==> H.
Proof using. introv M. auto. Qed.

#[global] Hint Resolve himpl_refl.

Lemma himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).
Proof using. introv M1 M2. unfolds* himpl. Qed.

Lemma himpl_trans_r : forall H2 H1 H3,
   H2 ==> H3 ->
   H1 ==> H2 ->
   H1 ==> H3.
Proof using. introv M1 M2. applys* himpl_trans M2 M1. Qed.

Lemma himpl_antisym : forall H1 H2,
  (H1 ==> H2) ->
  (H2 ==> H1) ->
  (H1 = H2).
Proof using. introv M1 M2. applys pred_ext_1. intros h. iff*. Qed.

Lemma hprop_op_comm : forall (op:hprop->hprop->hprop),
  (forall H1 H2, op H1 H2 ==> op H2 H1) ->
  (forall H1 H2, op H1 H2 = op H2 H1).
Proof using. introv M. intros. applys himpl_antisym; applys M. Qed.

Lemma qimpl_refl : forall A (Q:A->hprop),
  Q ===> Q.
Proof using. intros. unfolds*. Qed.

#[global] Hint Resolve qimpl_refl.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hempty] *)

Lemma hempty_intro :
  \[] Fmap.empty.
Proof using. unfolds*. Qed.

Lemma hempty_inv : forall h,
  \[] h ->
  h = Fmap.empty.
Proof using. auto. Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hstar] *)

Lemma hstar_intro : forall H1 H2 h1 h2,
  H1 h1 ->
  H2 h2 ->
  Fmap.disjoint h1 h2 ->
  (H1 \* H2) (Fmap.union h1 h2).
Proof using. intros. exists~ h1 h2. Qed.

Lemma hstar_inv : forall H1 H2 h,
  (H1 \* H2) h ->
  exists h1 h2, H1 h1 /\ H2 h2 /\ Fmap.disjoint h1 h2 /\ h = Fmap.union h1 h2.
Proof using. introv M. applys M. Qed.

Lemma hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.
Proof using.
  applys hprop_op_comm. unfold hprop, hstar. intros H1 H2.
  intros h (h1&h2&M1&M2&D&U). rewrite~ Fmap.union_comm_of_disjoint in U.
  exists* h2 h1.
Qed.

Lemma hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
Proof using.
  intros H1 H2 H3. applys himpl_antisym; intros h.
  { intros (h'&h3&(h1&h2&M3&M4&D'&U')&M2&D&U). subst h'.
    exists h1 (h2 \+ h3). splits~. { applys* hstar_intro. } }
  { intros (h1&h'&M1&(h2&h3&M3&M4&D'&U')&D&U). subst h'.
    exists (h1 \+ h2) h3. splits~. { applys* hstar_intro. } }
Qed.

Lemma hstar_hempty_l : forall H,
  \[] \* H = H.
Proof using.
  intros. applys himpl_antisym; intros h.
  { intros (h1&h2&M1&M2&D&U). forwards E: hempty_inv M1. subst.
    rewrite~ Fmap.union_empty_l. }
  { intros M. exists (Fmap.empty:heap) h. splits~. { applys hempty_intro. } }
Qed.

Lemma hstar_hempty_r : forall H,
  H \* \[] = H.
Proof using.
  applys neutral_r_of_comm_neutral_l. applys~ hstar_comm. applys~ hstar_hempty_l.
Qed.

Lemma hstar_hexists : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (fun x => (J x) \* H).
Proof using.
  intros. applys himpl_antisym; intros h.
  { intros (h1&h2&(x&M1)&M2&D&U). exists~ x h1 h2. }
  { intros (x&(h1&h2&M1&M2&D&U)). exists h1 h2. splits~. { exists~ x. } }
Qed.

Lemma hstar_hforall : forall H A (J:A->hprop),
  (hforall J) \* H ==> hforall (J \*+ H).
Proof using.
  intros. intros h M. destruct M as (h1&h2&M1&M2&D&U). intros x. exists~ h1 h2.
Qed.

Lemma himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).
Proof using. introv W (h1&h2&?). exists* h1 h2. Qed.

Lemma himpl_frame_r : forall H1 H2 H2',
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1 \* H2').
Proof using.
  introv M. do 2 rewrite (@hstar_comm H1). applys~ himpl_frame_l.
Qed.

Lemma himpl_frame_lr : forall H1 H1' H2 H2',
  H1 ==> H1' ->
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1' \* H2').
Proof using.
  introv M1 M2. applys himpl_trans. applys~ himpl_frame_l M1. applys~ himpl_frame_r.
Qed.

Lemma himpl_hstar_trans_l : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H2 \* H3 ==> H4 ->
  H1 \* H3 ==> H4.
Proof using.
  introv M1 M2. applys himpl_trans_r M2. applys himpl_frame_l M1.
Qed.

Lemma himpl_hstar_trans_r : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H3 \* H2 ==> H4 ->
  H3 \* H1 ==> H4.
Proof using.
  introv M1 M2. applys himpl_trans_r M2. applys himpl_frame_r M1.
Qed.

(* ----------------------------------------------------------------- *)
(** ***  Properties of [hpure] *)

Lemma hpure_intro : forall P,
  P ->
  \[P] Fmap.empty.
Proof using. introv M. exists M. unfolds*. Qed.

Lemma hpure_inv : forall P h,
  \[P] h ->
  P /\ h = Fmap.empty.
Proof using. introv (p&M). split~. Qed.

Lemma hstar_hpure_l : forall P H h,
  (\[P] \* H) h = (P /\ H h).
Proof using.
  intros. apply prop_ext. unfold hpure.
  rewrite hstar_hexists. rewrite* hstar_hempty_l.
  iff (p&M) (p&M). { split~. } { exists~ p. }
Qed.

Lemma hstar_hpure_r : forall P H h,
  (H \* \[P]) h = (H h /\ P).
Proof using.
  intros. rewrite hstar_comm. rewrite hstar_hpure_l. apply* prop_ext.
Qed.

Lemma himpl_hstar_hpure_r : forall P H H',
  P ->
  (H ==> H') ->
  H ==> (\[P] \* H').
Proof using. introv HP W. intros h K. rewrite* hstar_hpure_l. Qed.

Lemma hpure_inv_hempty : forall P h,
  \[P] h ->
  P /\ \[] h.
Proof using.
  introv M. rewrite <- hstar_hpure_l. rewrite~ hstar_hempty_r.
Qed.

Lemma hpure_intro_hempty : forall P h,
  \[] h ->
  P ->
  \[P] h.
Proof using.
  introv M N. rewrite <- (hstar_hempty_l \[P]). rewrite~ hstar_hpure_r.
Qed.

Lemma himpl_hempty_hpure : forall P,
  P ->
  \[] ==> \[P].
Proof using. introv HP. intros h Hh. applys* hpure_intro_hempty. Qed.

Lemma himpl_hstar_hpure_l : forall P H H',
  (P -> H ==> H') ->
  (\[P] \* H) ==> H'.
Proof using.
  introv W Hh. rewrite hstar_hpure_l in Hh. applys* W.
Qed.

Lemma hempty_eq_hpure_true :
  \[] = \[True].
Proof using.
  applys himpl_antisym; intros h M.
  { applys* hpure_intro_hempty. }
  { forwards*: hpure_inv_hempty M. }
Qed.

Lemma hfalse_hstar_any : forall H,
  \[False] \* H = \[False].
Proof using.
  intros. applys himpl_antisym; intros h; rewrite hstar_hpure_l; intros M.
  { false*. } { lets: hpure_inv_hempty M. false*. }
Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hexists] *)

Lemma hexists_intro : forall A (x:A) (J:A->hprop) h,
  J x h ->
  (hexists J) h.
Proof using. intros. exists~ x. Qed.

Lemma hexists_inv : forall A (J:A->hprop) h,
  (hexists J) h ->
  exists x, J x h.
Proof using. intros. destruct H as [x H]. exists~ x. Qed.

Lemma himpl_hexists_l : forall A H (J:A->hprop),
  (forall x, J x ==> H) ->
  (hexists J) ==> H.
Proof using. introv W. intros h (x&Hh). applys* W. Qed.

Lemma himpl_hexists_r : forall A (x:A) H J,
  (H ==> J x) ->
  H ==> (hexists J).
Proof using. introv W. intros h. exists x. apply~ W. Qed.

Lemma himpl_hexists : forall A (J1 J2:A->hprop),
  J1 ===> J2 ->
  hexists J1 ==> hexists J2.
Proof using.
  introv W. applys himpl_hexists_l. intros x. applys himpl_hexists_r W.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hforall] *)

Lemma hforall_intro : forall A (J:A->hprop) h,
  (forall x, J x h) ->
  (hforall J) h.
Proof using. introv M. applys* M. Qed.

Lemma hforall_inv : forall A (J:A->hprop) h,
  (hforall J) h ->
  forall x, J x h.
Proof using. introv M. applys* M. Qed.

Lemma himpl_hforall_r : forall A (J:A->hprop) H,
  (forall x, H ==> J x) ->
  H ==> (hforall J).
Proof using. introv M. intros h Hh x. apply~ M. Qed.

Lemma himpl_hforall_l : forall A x (J:A->hprop) H,
  (J x ==> H) ->
  (hforall J) ==> H.
Proof using. introv M. intros h Hh. apply~ M. Qed.

Lemma hforall_specialize : forall A (x:A) (J:A->hprop),
  (hforall J) ==> (J x).
Proof using. intros. applys* himpl_hforall_l x. Qed.

Lemma himpl_hforall : forall A (J1 J2:A->hprop),
  J1 ===> J2 ->
  hforall J1 ==> hforall J2.
Proof using.
  introv W. applys himpl_hforall_r. intros x. applys himpl_hforall_l W.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hwand] *)

Lemma hwand_equiv : forall H0 H1 H2,
  (H0 ==> H1 \-* H2) <-> (H1 \* H0 ==> H2).
Proof using.
  unfold hwand. iff M.
  { rewrite hstar_comm. applys himpl_hstar_trans_l (rm M).
    rewrite hstar_hexists. applys himpl_hexists_l. intros H.
    rewrite (hstar_comm H). rewrite hstar_assoc.
    rewrite (hstar_comm H H1). applys~ himpl_hstar_hpure_l. }
  { applys himpl_hexists_r H0.
    rewrite <- (hstar_hempty_r H0) at 1.
    applys himpl_frame_r. applys himpl_hempty_hpure M. }
Qed.

Lemma himpl_hwand_r : forall H1 H2 H3,
  H2 \* H1 ==> H3 ->
  H1 ==> (H2 \-* H3).
Proof using. introv M. rewrite~ hwand_equiv. Qed.

Lemma himpl_hwand_r_inv : forall H1 H2 H3,
  H1 ==> (H2 \-* H3) ->
  H2 \* H1 ==> H3.
Proof using. introv M. rewrite~ <- hwand_equiv. Qed.

Lemma hwand_cancel : forall H1 H2,
  H1 \* (H1 \-* H2) ==> H2.
Proof using. intros. applys himpl_hwand_r_inv. applys himpl_refl. Qed.

Arguments hwand_cancel : clear implicits.

Lemma himpl_hempty_hwand_same : forall H,
  \[] ==> (H \-* H).
Proof using. intros. apply himpl_hwand_r. rewrite~ hstar_hempty_r. Qed.

Lemma hwand_hempty_l : forall H,
  (\[] \-* H) = H.
Proof using.
  intros. applys himpl_antisym.
  { rewrite <- hstar_hempty_l at 1. applys hwand_cancel. }
  { rewrite hwand_equiv. rewrite~ hstar_hempty_l. }
Qed.

Lemma hwand_hpure_l : forall P H,
  P ->
  (\[P] \-* H) = H.
Proof using.
  introv HP. applys himpl_antisym.
  { lets K: hwand_cancel \[P] H. applys himpl_trans_r K.
    applys* himpl_hstar_hpure_r. }
  { rewrite hwand_equiv. applys* himpl_hstar_hpure_l. }
Qed.

Lemma hwand_curry : forall H1 H2 H3,
  (H1 \* H2) \-* H3 ==> H1 \-* (H2 \-* H3).
Proof using.
  intros. apply himpl_hwand_r. apply himpl_hwand_r.
  rewrite <- hstar_assoc. rewrite (hstar_comm H1 H2).
  applys hwand_cancel.
Qed.

Lemma hwand_uncurry : forall H1 H2 H3,
  H1 \-* (H2 \-* H3) ==> (H1 \* H2) \-* H3.
Proof using.
  intros. rewrite hwand_equiv. rewrite (hstar_comm H1 H2).
  rewrite hstar_assoc. applys himpl_hstar_trans_r.
  { applys hwand_cancel. } { applys hwand_cancel. }
Qed.

Lemma hwand_curry_eq : forall H1 H2 H3,
  (H1 \* H2) \-* H3 = H1 \-* (H2 \-* H3).
Proof using.
  intros. applys himpl_antisym.
  { applys hwand_curry. }
  { applys hwand_uncurry. }
Qed.

Lemma hwand_inv : forall h1 h2 H1 H2,
  (H1 \-* H2) h2 ->
  H1 h1 ->
  Fmap.disjoint h1 h2 ->
  H2 (h1 \u h2).
Proof using.
  introv M2 M1 D. unfolds hwand. lets (H0&M3): hexists_inv M2.
  lets (h0&h3&P1&P3&D'&U): hstar_inv M3. lets (P4&E3): hpure_inv P3.
  subst h2 h3. rewrite union_empty_r in *. applys P4. applys* hstar_intro.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of qwand *)

Lemma qwand_equiv : forall H A (Q1 Q2:A->hprop),
  H ==> (Q1 \--* Q2) <-> (Q1 \*+ H) ===> Q2.
Proof using.
  unfold qwand. iff M.
  { intros x. rewrite hstar_comm. applys himpl_hstar_trans_l (rm M).
    applys himpl_trans. applys hstar_hforall. simpl.
    applys himpl_hforall_l x. rewrite hstar_comm. applys hwand_cancel. }
  { applys himpl_hforall_r. intros x. rewrite* hwand_equiv. }
Qed.

Lemma qwand_cancel : forall A (Q1 Q2:A->hprop),
  Q1 \*+ (Q1 \--* Q2) ===> Q2.
Proof using. intros. rewrite <- qwand_equiv. applys qimpl_refl. Qed.

Lemma himpl_qwand_r : forall A (Q1 Q2:A->hprop) H,
  Q1 \*+ H ===> Q2 ->
  H ==> (Q1 \--* Q2).
Proof using. introv M. rewrite~ qwand_equiv. Qed.

Arguments himpl_qwand_r [A].

Lemma qwand_specialize : forall A (x:A) (Q1 Q2:A->hprop),
  (Q1 \--* Q2) ==> (Q1 x \-* Q2 x).
Proof using. intros. applys* himpl_hforall_l x. Qed.

Arguments qwand_specialize [ A ].

(* ----------------------------------------------------------------- *)
(** *** Properties of [htop] *)

Lemma htop_intro : forall h,
  \Top h.
Proof using. intros. exists~ (=h). Qed.

Lemma himpl_htop_r : forall H,
  H ==> \Top.
Proof using. intros. intros h Hh. applys* htop_intro. Qed.

Lemma htop_eq :
  \Top = (\exists H, H).
Proof using. auto. Qed.

Lemma hstar_htop_htop :
  \Top \* \Top = \Top.
Proof using.
  applys himpl_antisym.
  { applys himpl_htop_r. }
  { rewrite <- hstar_hempty_r at 1. applys himpl_frame_r. applys himpl_htop_r. }
Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hsingle] *)

Lemma hsingle_intro : forall p v,
  (p ~~> v) (Fmap.single p v).
Proof using. intros. hnfs*. Qed.

Lemma hsingle_inv: forall p v h,
  (p ~~> v) h ->
  h = Fmap.single p v.
Proof using. auto. Qed.

Lemma hstar_hsingle_same_loc : forall p w1 w2,
  (p ~~> w1) \* (p ~~> w2) ==> \[False].
Proof using.
  intros. unfold hsingle. intros h (h1&h2&E1&E2&D&E). false.
  subst. applys* Fmap.disjoint_single_single_same_inv.
Qed.

Arguments hstar_hsingle_same_loc : clear implicits.

(* ----------------------------------------------------------------- *)
(** *** Definition and Properties of [haffine] and [hgc] *)

Definition haffine (H:hprop) :=
  True.

Lemma haffine_hany : forall (H:hprop),
  haffine H.
Proof using. unfold haffine. auto. Qed.

Lemma haffine_hempty :
  haffine \[].
Proof using. applys haffine_hany. Qed.

Definition hgc := (* equivalent to [\exists H, \[haffine H] \* H] *)
  htop.

Notation "\GC" := (hgc) : hprop_scope.

Lemma haffine_hgc :
  haffine \GC.
Proof using. applys haffine_hany. Qed.

Lemma himpl_hgc_r : forall H,
  haffine H ->
  H ==> \GC.
Proof using. introv M. applys himpl_htop_r. Qed.

Lemma hstar_hgc_hgc :
  \GC \* \GC = \GC.
Proof using. applys hstar_htop_htop. Qed.

(* ----------------------------------------------------------------- *)
(** *** Functor Instantiation to Obtain [xsimpl] *)

End SepSimplArgs.

(** We are now ready to instantiate the functor that defines [xsimpl].
    Demos of [xsimpl] are presented in chapter [Himpl.v]. *)

Module Export HS := LibSepSimpl.XsimplSetup(SepSimplArgs).

Export SepSimplArgs.

(** From now on, all operators have opaque definitions. *)

Global Opaque hempty hpure hstar hsingle hexists hforall
              hwand qwand htop hgc haffine.

(** At this point, the tactic [xsimpl] is defined. There remains to customize
    the tactic so that it recognizes the predicate [p ~~> v] in a special way
    when performing simplifications. *)

(** The tactic [xsimpl_hook_hsingle p v] operates as part of [xsimpl].
    The specification that follows makes sense only in the context of the
    presentation of the invariants of [xsimpl] described in [LibSepSimpl.v].
    This tactic is invoked on goals of the form [Xsimpl (Hla, Hlw, Hlt) HR],
    where [Hla] is of the form [H1 \* .. \* Hn \* \[]]. The tactic
    [xsimpl_hook_hsingle p v] searches among the [Hi] for a heap predicate
    of the form [p ~~> v']. If it finds one, it moves this [Hi] to the front,
    just before [H1]. Then, it cancels it out with the [p ~~> v] that occurs
    in [HR]. Otherwise, the tactic fails. *)

Ltac xsimpl_hook_hsingle p :=
  xsimpl_pick_st ltac:(fun H' =>
    match H' with (hsingle p ?v') =>
      constr:(true) end);
  apply xsimpl_lr_cancel_eq;
  [ xsimpl_lr_cancel_eq_repr_post tt | ].

(** The tactic [xsimpl_hook] handles cancellation of heap predicates of the
    form [p ~~> v]. It forces their cancellation against heap predicates of
    the form [p ~~> w], by asserting the equality [v = w]. Note: this tactic
    is later refined to also handle records. *)

Ltac xsimpl_hook H ::=
  match H with
  | hsingle ?p ?v => xsimpl_hook_hsingle p
  end.

(** One last hack is to improve the [math] tactic so that it is able
    to handle the [val_int] coercion in goals and hypotheses of the
    form [val_int ?n = val_int ?m], and so that it is able to process
    the well-founded relations [dowto] and [upto] for induction on
    integers. *)

Ltac math_0 ::=
  unfolds downto, upto;
  repeat match goal with
  | |- val_int _ = val_int _ => fequal
  | H: val_int _ = val_int _ |- _ => inverts H
  end.

(* ================================================================= *)
(** ** Properties of [haffine] *)

(** The lemma [haffine_any] asserts
    that [haffine H] holds for any [H]. Nevertheless, let us state corollaries
    of [haffine_any] for specific heap predicates, to illustrate how the
    [xaffine] tactic works in chapter [Affine]. *)

Lemma haffine_hempty :
  haffine \[].
Proof using. intros. applys haffine_hany. Qed.

Lemma haffine_hpure : forall P,
  haffine \[P].
Proof using. intros. applys haffine_hany. Qed.

Lemma haffine_hstar : forall H1 H2,
  haffine H1 ->
  haffine H2 ->
  haffine (H1 \* H2).
Proof using. intros. applys haffine_hany. Qed.

Lemma haffine_hexists : forall A (J:A->hprop),
  (forall x, haffine (J x)) ->
  haffine (\exists x, (J x)).
Proof using. intros. applys haffine_hany. Qed.

Lemma haffine_hforall : forall A `{Inhab A} (J:A->hprop),
  (forall x, haffine (J x)) ->
  haffine (\forall x, (J x)).
Proof using. intros. applys haffine_hany. Qed.

Lemma haffine_hstar_hpure : forall (P:Prop) H,
  (P -> haffine H) ->
  haffine (\[P] \* H).
Proof using. intros. applys haffine_hany. Qed.

Lemma haffine_hgc :
  haffine \GC.
Proof using. intros. applys haffine_hany. Qed.

(** Using these lemmas, we are able to configure the [xaffine] tactic. *)

Ltac xaffine_core tt ::=
  repeat match goal with |- haffine ?H =>
    match H with
    | (hempty) => apply haffine_hempty
    | (hpure _) => apply haffine_hpure
    | (hstar _ _) => apply haffine_hstar
    | (hexists _) => apply haffine_hexists
    | (hforall _) => apply haffine_hforall
    | (hgc) => apply haffine_hgc
    | _ => eauto with haffine
    end
  end.

(* ################################################################# *)
(** * Reasoning Rules *)

Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.

(* ================================================================= *)
(** ** Definition of Separation Logic Triples. *)

(** The Separation Logic triple [triple t H Q] is defined in terms of
    the omni-big-step semantics predicate [eval s t Q]. *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall s, H s -> eval s t Q.

(** We introduce a handy notation for postconditions of functions
    that return a pointer:  [funloc p => H] is short for
    [fun (r:val) => \exists (p:loc), \[r = val_loc p] \* H)]. *)

Notation "'funloc' p '=>' H" :=
  (fun (r:val) => \exists p, \[r = val_loc p] \* H)
  (at level 200, p name, format "'funloc'  p  '=>'  H") : hprop_scope.

(* ================================================================= *)
(** ** Soundness of Triples w.r.t. the Small-Step Semantics *)

(** If one considers the omni-big-step semantics to be the starting point
    of a development, then the definition of [triple] is obviously sound
    with respect to that semantics, as it concludes [eval s t Q].
    If, however, one considers the small-step semantics to be the starting
    point, then to establish soundness it is required to prove that
    [triple t H Q] ensures that all possible evaluations of [t] in a
    heap satisfy [H] are: (1) terminating, (2) always reaching a value,
    and (3) this value and the final state obtained satisfy the postconditon [Q]. *)

(** The judgment [terminates s t] is defined inductively. The execution
    starting from [(s,t)] terminates if, for any possible step leads to
    a configuration that terminates. Note that a configuration that has
    reached a value cannot take a step, hence is considered terminating. *)

Inductive terminates : heap->trm->Prop :=
  | terminates_step : forall s t,
      (forall s' t', step s t s' t' -> terminates s' t') ->
      terminates s t.

(** The judgment [safe s t] asserts that no execution may reach a stuck
    term. In other words, for any configuration [(s',t')] reachable from
    [(s,t)], it is the case that the configuration [(s',t')] is either
    a value or is reducible. *)

Definition safe (s:heap) (t:trm) : Prop :=
  forall s' t', steps s t s' t' -> notstuck s' t'.

(** The judgment [correct s t Q] asserts that if the execution of [(s,t)] reaches
    a final configuration, then this final configuration satisfies [Q]. *)

Definition correct (s:heap) (t:trm) (Q:val->hprop) : Prop :=
  forall s' v, steps s t s' v -> Q v s'.

(** The aim is to show that [triple t H Q] entails that, for any [s] satisfying [H],
   [terminates s t] and [safe s t] and [correct s t Q] holds. *)

(** The judgment [seval s t Q] asserts that any execution of [(s,t)]
    terminates and reaches a configuration satisfying [Q]. In the "base" case,
    [seval s v Q] holds if the terminal configuration [(s,v)] satisfies [Q].
    In the "step" case, [seval s t Q] holds if (1) the configuration [(s,t)]
    is reducible, and (2) if for any step that [(s,t)] may take to [(s',t')],
    the predicate [seval s' t' Q] holds. *)

Inductive seval : heap->trm->(val->hprop)->Prop :=
  | seval_val : forall s v Q,
      Q v s ->
      seval s v Q
  | seval_step : forall s t Q,
      reducible s t -> (* (exists s' t', step s t s' t') *)
      (forall s' t', step s t s' t' -> seval s' t' Q) ->
      seval s t Q.

(** The judgment [seval s t Q] satisfies the 3 targeted soundness properties. *)

Lemma seval_terminates : forall s t Q,
  seval s t Q ->
  terminates s t.
Proof using.
  introv M. induction M; constructors; introv R.
  { inverts R. }
  { eauto. }
Qed.

Lemma seval_safe : forall s t Q,
  seval s t Q ->
  safe s t.
Proof using.
  introv M R. gen Q. induction R; intros.
  { inverts M. { left. hnfs*. } { right*. } }
  { rename H into S. inverts M. { inverts S. } { applys* IHR. } }
Qed.

Lemma seval_correct : forall s t Q,
  seval s t Q ->
  correct s t Q.
Proof using.
  introv M. induction M; introv R.
  { inverts R as. { auto. } { introv S. inverts S. } }
  { rename H1 into IH. inverts R. { lets (?&?&R): H. inverts R. } applys* IH. }
Qed.

(** [false_step] is a handy tactic to get rid of goals with assumptions
    of the form [step s v s' t'] or [step s (op v) s' t'] for a binary operator [op]. *)

Ltac false_step :=
  solve [ match goal with
  | K: step _ (trm_app (trm_val (val_prim _)) (trm_val _)) _ _ |- _ =>
      inversion K; clear K; subst; false_step
  | K: step _ (trm_val _) _ _ |- _ =>
      inversion K; clear K; subst
  | _ => false
  end ].

(** The proof that [eval s t Q] entails [seval s t Q] begins with a bunch
    of auxiliary lemmas. *)

Lemma seval_fun : forall s x t1 Q,
  Q (val_fun x t1) s ->
  seval s (trm_fun x t1) Q.
Proof using.
  introv M. applys seval_step.
  { do 2 esplit. constructor. }
  { introv R. inverts R. { applys seval_val. applys M. } }
Qed.

Lemma seval_fix : forall s f x t1 Q,
  Q (val_fix f x t1) s ->
  seval s (trm_fix f x t1) Q.
Proof using.
  introv M. applys seval_step.
  { do 2 esplit. constructor. }
  { introv R. inverts R. { applys seval_val. applys M. } }
Qed.

Lemma seval_app_fun : forall s x v1 v2 t1 Q,
  v1 = val_fun x t1 ->
  seval s (subst x v2 t1) Q ->
  seval s (trm_app v1 v2) Q.
Proof using.
  introv E M. applys seval_step.
  { do 2 esplit. applys* step_app_fun. }
  { introv R. invert R; try solve [intros; false | introv R; inverts R].     introv -> -> -> -> -> R. inverts E. applys M. }
Qed.

Lemma seval_app_fix : forall s f x v1 v2 t1 Q,
  v1 = val_fix f x t1 ->
  seval s (subst x v2 (subst f v1 t1)) Q ->
  seval s (trm_app v1 v2) Q.
Proof using.
  introv E M. applys seval_step.
  { do 2 esplit. applys* step_app_fix. }
  { introv R. invert R; try solve [intros; false | introv R; inverts R].     introv -> -> -> -> -> R. inverts E. applys M. }
Qed.

Lemma seval_seq : forall s t1 t2 Q1 Q,
  seval s t1 Q1 ->
  (forall s1 v1, Q1 v1 s1 -> seval s1 t2 Q) ->
  seval s (trm_seq t1 t2) Q.
Proof using.
  introv M1 M2. gen_eq Q1': Q1.
  induction M1; intros; subst.
  { apply seval_step.
    { do 2 esplit. applys step_seq. }
    { introv R. inverts R as R'. { inverts R'. } applys* M2. } }
  { rename t into t1, H1 into IH.
    destruct H as (s'&t'&RE). applys seval_step.
    { do 2 esplit. constructors. applys RE. }
    { introv R. inverts R as R'.
      { applys* IH R' M2. }
      { false. inverts RE. } } }
Qed.

Lemma seval_let : forall s x t1 t2 Q1 Q,
  seval s t1 Q1 ->
  (forall s1 v1, Q1 v1 s1 -> seval s1 (subst x v1 t2) Q) ->
  seval s (trm_let x t1 t2) Q.
Proof using.
  introv M1 M2. gen_eq Q1': Q1.
  induction M1; intros; subst.
  { apply seval_step.
    { do 2 esplit. applys step_let. }
    { introv R. inverts R as R'. { inverts R'. } applys* M2. } }
  { rename t into t1, H1 into IH.
    destruct H as (s'&t'&RE). applys seval_step.
    { do 2 esplit. constructors. applys RE. }
    { introv R. inverts R as R'.
      { applys* IH R' M2. }
      { false. inverts RE. } } }
Qed.

Lemma seval_app_arg1 : forall t1 t2 Q1 s1 Q,
  seval s1 t1 Q1 ->
  (forall v1 s2, Q1 v1 s2 -> seval s2 (v1 t2) Q) ->
  seval s1 (t1 t2) Q.
Proof using.
  introv M1 M2. gen_eq Q1': Q1.
  induction M1; intros; subst.
  { applys* M2. }
  { rename t into t1, H1 into IH.
    destruct H as (s'&t'&RE). applys seval_step.
    { do 2 esplit. applys step_app_arg1. applys RE. }
    { introv R. inverts R as R'; try solve [inverts RE]; try false_step.
      { applys* IH R'. } } }
Qed.

Lemma seval_app_arg2 : forall v1 t2 Q1 s1 Q,
  seval s1 t2 Q1 ->
  (forall v2 s2, Q1 v2 s2 -> seval s2 (v1 v2) Q) ->
  seval s1 (v1 t2) Q.
Proof using.
  introv M1 M2. gen_eq Q1': Q1.
  induction M1; intros; subst.
  { applys* M2. }
  { rename t into t1, H1 into IH.
    destruct H as (s'&t'&RE). applys seval_step.
    { do 2 esplit. applys step_app_arg2. applys RE. }
    { introv R. inverts R as R'; try solve [inverts RE]; try false_step.
      { applys* IH R'. } } }
Qed.

Lemma seval_if : forall s b t1 t2 Q,
  seval s (if b then t1 else t2) Q ->
  seval s (trm_if b t1 t2) Q.
Proof using.
  introv M. applys seval_step.
  { do 2 esplit. constructors*. }
  { introv R. inverts R; tryfalse. { applys M. } }
Qed.

Lemma seval_of_eval : forall s t Q,
  eval s t Q ->
  seval s t Q.
Proof using.
  introv M. induction M.
  { applys* seval_val. }
  { applys* seval_fun. }
  { applys* seval_fix. }
  { applys* seval_app_arg1. }
  { applys* seval_app_arg2. }
  { applys* seval_app_fun. }
  { applys* seval_app_fix. }
  { applys* seval_seq. }
  { applys* seval_let. }
  { applys* seval_if. }
  { rename H into HE, H0 into K. unfolds purepostin.
    applys seval_step.
    { inverts HE; try solve [do 2 esplit; constructor; eauto].
      { exists s 0. applys step_rand. math. } }
    { introv R. inverts R; try false_step; inverts HE; applys* seval_val. } }
   { rename H into HE, H0 into K. unfolds purepostin.
    applys seval_step.
    { inverts HE; try solve [do 2 esplit; constructor; eauto]. }
    { introv R. inverts R; do 2 (try inverts_if_head step); inverts HE; applys* seval_val.
      (* alternative: inverts HE; inverts R; try false_step; applys* seval_val. *)
      { math_rewrite (p2 = p3). { applys eq_nat_of_eq_int. math. } eauto. } } }
  { applys seval_step.
    { forwards~ (p&D&N): (exists_fresh null s).
      do 2 esplit. applys* step_ref. }
    { introv R. do 2 (try inverts_if_head step). applys* seval_val. } }
  { applys seval_step.
    { do 2 esplit. applys* step_get. }
    { introv R. do 2 (try inverts_if_head step). applys* seval_val. } }
  { applys seval_step.
    { do 2 esplit. applys* step_set. }
    { introv R. do 3 (try inverts_if_head step). applys* seval_val. } }
  { applys seval_step.
    { do 2 esplit. applys* step_free. }
    { introv R. do 2 (try inverts_if_head step). applys* seval_val. } }
Qed.

(** Final soundness theorem with respect to the small-step semantics. *)

Lemma triple_sound : forall t H Q,
  triple t H Q ->
  forall s, H s -> terminates s t /\ safe s t /\ correct s t Q.
Proof using.
  introv M Hs. specializes M Hs. lets M': seval_of_eval M. splits.
  { applys* seval_terminates. }
  { applys* seval_safe. }
  { applys* seval_correct. }
Qed.

(* ================================================================= *)
(** ** Structural Properties of the [eval] Predicate *)

Section EvalProp.
Hint Constructors eval.

(** Covariance property *)

Lemma eval_conseq : forall s t Q1 Q2,
  eval s t Q1 ->
  Q1 ===> Q2 ->
  eval s t Q2.
Proof using.
  introv M W.
  asserts W': (forall v h, Q1 v h -> Q2 v h). { auto. } clear W.
  induction M; try solve [ constructors* ].
  { applys* eval_unop. unfolds* purepostin. }
  { applys* eval_binop. unfolds* purepostin. }
Qed.

(** Frame property *)

Lemma eval_frame : forall h1 h2 t Q,
  eval h1 t Q ->
  Fmap.disjoint h1 h2 ->
  eval (h1 \u h2) t (Q \*+ (= h2)).
Proof using.
  introv M HD. gen h2. induction M; intros;
    try solve [ hint hstar_intro; constructors* ].
  { rename M into M1, H into M2, IHM into IH1, H1 into IH2.
    specializes IH1 HD. applys* eval_app_arg1 IH1. introv HK.
    lets (h1'&h2'&K1'&K2'&KD&KU): hstar_inv HK. subst. applys* IH2. }
  { rename M into M1, H into M2, IHM into IH1, H1 into IH2.
    specializes IH1 HD. applys* eval_app_arg2 IH1. introv HK.
    lets (h1'&h2'&K1'&K2'&KD&KU): hstar_inv HK. subst. applys* IH2. }
  { rename M into M1, H into M2, IHM into IH1, H0 into IH2.
    specializes IH1 HD. applys eval_seq IH1. introv HK.
    lets (h1'&h2'&K1'&K2'&KD&KU): hstar_inv HK. subst. applys* IH2. }
  { rename M into M1, H into M2, IHM into IH1, H0 into IH2.
    specializes IH1 HD. applys eval_let IH1. introv HK.
    lets (h1'&h2'&K1'&K2'&KD&KU): hstar_inv HK. subst. applys* IH2. }
  { applys* eval_unop. unfolds* purepostin. introv Hv. applys* hstar_intro. }
  { applys* eval_binop. unfolds* purepostin. introv Hv. applys* hstar_intro. }
  { rename H into M. applys eval_ref. intros p Hp.
    rewrite Fmap.indom_union_eq in Hp. rew_logic in Hp. destruct Hp as [Hp1 Hp2].
    rewrite* Fmap.update_union_not_r. applys hstar_intro.
    { applys* M. } { auto. } { applys* Fmap.disjoint_update_not_r. } }
  { applys eval_get. { rewrite* Fmap.indom_union_eq. }
    { rewrite* Fmap.read_union_l. applys* hstar_intro. } }
  { applys eval_set. { rewrite* Fmap.indom_union_eq. }
    { rewrite* Fmap.update_union_l. applys hstar_intro.
      { auto. } { auto. } { applys* Fmap.disjoint_update_l. } } }
  { applys eval_free. { rewrite* Fmap.indom_union_eq. }
    { rewrite* Fmap.remove_disjoint_union_l. applys hstar_intro.
      { auto. } { auto. } { applys* Fmap.disjoint_remove_l. } } }
Qed.

End EvalProp.

(* ================================================================= *)
(** ** Structural Rules *)

(** Consequence and frame rule. *)

Lemma triple_conseq : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof using. unfolds triple. introv M MH MQ HF. applys* eval_conseq. Qed.

Lemma triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof.
  introv M. intros h HF. lets (h1&h2&M1&M2&MD&MU): hstar_inv (rm HF).
  subst. specializes M M1. applys eval_conseq.
  { applys eval_frame M MD. } { xsimpl. intros h' ->. applys M2. }
Qed.

(** Extraction Rules *)

Lemma triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using.
  introv M. intros h (h1&h2&M1&M2&D&U). destruct M1 as (M1&HP).
  lets E: hempty_inv HP. subst. rewrite Fmap.union_empty_l. applys~ M.
Qed.

Lemma triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall (x:A), triple t (J x) Q) ->
  triple t (hexists J) Q.
Proof using. introv M. intros h (x&Hh). applys M Hh. Qed.

Lemma triple_hforall : forall t (A:Type) (x:A) (J:A->hprop) Q,
  triple t (J x) Q ->
  triple t (hforall J) Q.
Proof using. introv M. applys* triple_conseq M. applys hforall_specialize. Qed.

Lemma triple_hwand_hpure_l : forall t (P:Prop) H Q,
  P ->
  triple t H Q ->
  triple t (\[P] \-* H) Q.
Proof using. introv HP M. applys* triple_conseq M. rewrite* hwand_hpure_l. Qed.

(** A corollary of [triple_hpure] useful for the course *)

Parameter triple_hpure' : forall t (P:Prop) Q,
  (P -> triple t \[] Q) ->
  triple t \[P] Q.

(** Heap-naming rule *)

Lemma triple_named_heap : forall t H Q,
  (forall h, H h -> triple t (= h) Q) ->
  triple t H Q.
Proof using. introv M Hs. applys M Hs. auto. Qed.

(** Combined and ramified rules. *)

Lemma triple_conseq_frame : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.
Proof using.
  introv M WH WQ. applys triple_conseq WH WQ. applys triple_frame M.
Qed.

Lemma triple_ramified_frame : forall H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  triple t H Q.
Proof using.
  introv M W. applys triple_conseq_frame (Q1 \--* Q) M W.
  { rewrite~ <- qwand_equiv. }
Qed.

(* ================================================================= *)
(** ** Rules for Terms *)

Lemma triple_eval_like : forall t1 t2 H Q,
  eval_like t1 t2 ->
  triple t1 H Q ->
  triple t2 H Q.
Proof using. introv E M1 Hv. applys* E. Qed.

Lemma triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using. introv M Hs. applys* eval_val. Qed.

Lemma triple_val_minimal : forall v,
  triple (trm_val v) \[] (fun r => \[r = v]).
Proof using. intros. applys triple_val. xsimpl*. Qed.

Lemma triple_fun : forall x t1 H Q,
  H ==> Q (val_fun x t1) ->
  triple (trm_fun x t1) H Q.
Proof using. introv M Hs. applys* eval_fun. Qed.

Lemma triple_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  triple (trm_fix f x t1) H Q.
Proof using. introv M Hs. applys* eval_fix. Qed.

Lemma triple_seq : forall t1 t2 H Q H1,
  triple t1 H (fun v => H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.
Proof using. introv M1 M2 Hs. applys* eval_seq. Qed.

Lemma triple_let : forall x t1 t2 Q1 H Q,
  triple t1 H Q1 ->
  (forall v1, triple (subst x v1 t2) (Q1 v1) Q) ->
  triple (trm_let x t1 t2) H Q.
Proof using. introv M1 M2 Hs. applys* eval_let. Qed.

Lemma triple_let_val : forall x v1 t2 H Q,
  triple (subst x v1 t2) H Q ->
  triple (trm_let x v1 t2) H Q.
Proof using.
  introv M. applys triple_let (fun v => \[v = v1] \* H).
  { applys triple_val. xsimpl*. }
  { intros v. applys triple_hpure. intros ->. applys M. }
Qed.

Lemma triple_if : forall (b:bool) t1 t2 H Q,
  triple (if b then t1 else t2) H Q ->
  triple (trm_if b t1 t2) H Q.
Proof using. introv M Hs. applys* eval_if. Qed.

Lemma triple_app_fun : forall x v1 v2 t1 H Q,
  v1 = val_fun x t1 ->
  triple (subst x v2 t1) H Q ->
  triple (trm_app v1 v2) H Q.
Proof using. introv E M Hs. applys* eval_app_fun. Qed.

Lemma triple_app_fun_direct : forall x v2 t1 H Q,
  triple (subst x v2 t1) H Q ->
  triple (trm_app (val_fun x t1) v2) H Q.
Proof using. introv M. applys* triple_app_fun. Qed.

Lemma triple_app_fix : forall v1 v2 f x t1 H Q,
  v1 = val_fix f x t1 ->
  triple (subst x v2 (subst f v1 t1)) H Q ->
  triple (trm_app v1 v2) H Q.
Proof using. introv E M Hs. applys* eval_app_fix. Qed.

Lemma triple_app_fix_direct : forall v2 f x t1 H Q,
  f <> x ->
  triple (subst x v2 (subst f (val_fix f x t1) t1)) H Q ->
  triple (trm_app (val_fix f x t1) v2) H Q.
Proof using. introv N M. applys* triple_app_fix. Qed.

(* ================================================================= *)
(** ** Rules for Heap-Manipulating Primitive Operations *)

Lemma triple_ref : forall v,
  triple (val_ref v)
    \[]
    (fun r => \exists p, \[r = val_loc p] \* p ~~> v).
Proof using.
  intros. intros s1 K. applys eval_ref. intros p D.
  lets ->: hempty_inv K. rewrite Fmap.update_empty.
  applys hexists_intro p. rewrite hstar_hpure_l. split*.
  applys hsingle_intro.
Qed.

Lemma triple_get : forall v p,
  triple (val_get p)
    (p ~~> v)
    (fun r => \[r = v] \* (p ~~> v)).
Proof using.
  intros. intros s K. lets ->: hsingle_inv K.
  applys eval_get.
  { applys* Fmap.indom_single. }
  { rewrite hstar_hpure_l. split*. rewrite* Fmap.read_single. }
Qed.

Lemma triple_set : forall w p v,
  triple (val_set (val_loc p) v)
    (p ~~> w)
    (fun r => \[r = val_unit] \* (p ~~> v)).
Proof using.
  intros. intros s1 K. lets ->: hsingle_inv K. lets Hp: indom_single p v.
  applys eval_set.
  { applys* Fmap.indom_single. }
  { rewrite hstar_hpure_l. split*. rewrite Fmap.update_single. applys hsingle_intro. }
Qed.

Lemma triple_free' : forall p v,
  triple (val_free (val_loc p))
    (p ~~> v)
    (fun r => \[r = val_unit]).
Proof using.
  intros. intros s1 K. lets ->: hsingle_inv K. lets Hp: indom_single p v.
  applys eval_free.
  { applys* Fmap.indom_single. }
  { rewrite* Fmap.remove_single. applys* hpure_intro. }
Qed.

Lemma triple_free : forall p v,
  triple (val_free (val_loc p))
    (p ~~> v)
    (fun r => \[]).
Proof using. intros. applys triple_conseq triple_free'; xsimpl*. Qed.

(* ================================================================= *)
(** ** Rules for Other Primitive Operations *)

Lemma triple_unop' : forall op v1 (P:val->Prop) Q, (* DEPRECATED? *)
  evalunop op v1 P ->
  (forall v, P v -> Q v Fmap.empty) -> (* purepostin heap_empty P Q ->*)
  triple (op v1) \[] Q.
Proof using.
  introv M R Hs. lets ->: hempty_inv Hs. applys eval_unop M. hnfs*.
Qed.

Lemma triple_binop' : forall op v1 v2 (P:val->Prop) Q, (* DEPRECATED? *)
  evalbinop op v1 v2 P ->
  (forall v, P v -> Q v Fmap.empty) ->
  triple (op v1 v2) \[] Q.
Proof using.
  introv M R Hs. lets ->: hempty_inv Hs. applys eval_binop M. hnfs*.
Qed.

Lemma triple_unop : forall op v1 (P:val->Prop),
  evalunop op v1 P ->
  triple (op v1) \[] (fun r => \[P r]).
Proof using.
  introv M Hs. lets ->: hempty_inv Hs.
  applys eval_conseq (fun v s => P v /\ s = Fmap.empty).
  { applys* eval_unop M. hnfs*. }
  { intros v s (?&->). applys* hpure_intro. }
Qed.

Lemma triple_binop : forall op v1 v2 (P:val->Prop),
  evalbinop op v1 v2 P ->
  triple (op v1 v2) \[] (fun r => \[P r]).
Proof using.
  introv M Hs. lets ->: hempty_inv Hs.
  applys eval_conseq (fun v s => P v /\ s = Fmap.empty).
  { applys* eval_binop M. hnfs*. }
  { intros v s (?&->). applys* hpure_intro. }
Qed.

Lemma triple_add : forall n1 n2,
  triple (val_add n1 n2)
    \[]
    (fun r => \[r = val_int (n1 + n2)]).
Proof using. intros. applys* triple_binop. applys* evalbinop_add. Qed.

Lemma triple_div : forall n1 n2,
  n2 <> 0 ->
  triple (val_div n1 n2)
    \[]
    (fun r => \[r = val_int (Z.quot n1 n2)]).
Proof using. intros. applys* triple_binop. applys* evalbinop_div. Qed.

Lemma triple_rand : forall n,
  n > 0 ->
  triple (val_rand n)
    \[]
    (fun r => \[exists n1, r = val_int n1 /\ 0 <= n1 < n]).
Proof using. intros. applys* triple_unop. applys* evalunop_rand. Qed.

Lemma triple_neg : forall (b1:bool),
  triple (val_neg b1)
    \[]
    (fun r => \[r = val_bool (neg b1)]).
Proof using. intros. applys* triple_unop. applys* evalunop_neg. Qed.

Lemma triple_opp : forall n1,
  triple (val_opp n1)
    \[]
    (fun r => \[r = val_int (- n1)]).
Proof using. intros. applys* triple_unop. applys* evalunop_opp. Qed.

Lemma triple_eq : forall v1 v2,
  triple (val_eq v1 v2)
    \[]
    (fun r => \[r = isTrue (v1 = v2)]).
Proof using. intros. applys* triple_binop. applys evalbinop_eq. Qed.

Lemma triple_neq : forall v1 v2,
  triple (val_neq v1 v2)
    \[]
    (fun r => \[r = isTrue (v1 <> v2)]).
Proof using. intros. applys* triple_binop. applys evalbinop_neq. Qed.

Lemma triple_sub : forall n1 n2,
  triple (val_sub n1 n2)
    \[]
    (fun r => \[r = val_int (n1 - n2)]).
Proof using. intros. applys* triple_binop. applys* evalbinop_sub. Qed.

Lemma triple_mul : forall n1 n2,
  triple (val_mul n1 n2)
    \[]
    (fun r => \[r = val_int (n1 * n2)]).
Proof using. intros. applys* triple_binop. applys* evalbinop_mul. Qed.

Lemma triple_mod : forall n1 n2,
  n2 <> 0 ->
  triple (val_mod n1 n2)
    \[]
    (fun r => \[r = val_int (Z.rem n1 n2)]).
Proof using. intros. applys* triple_binop. applys* evalbinop_mod. Qed.

Lemma triple_le : forall n1 n2,
  triple (val_le n1 n2)
    \[]
    (fun r => \[r = isTrue (n1 <= n2)]).
Proof using. intros. applys* triple_binop. applys* evalbinop_le. Qed.

Lemma triple_lt : forall n1 n2,
  triple (val_lt n1 n2)
    \[]
    (fun r => \[r = isTrue (n1 < n2)]).
Proof using. intros. applys* triple_binop. applys* evalbinop_lt. Qed.

Lemma triple_ge : forall n1 n2,
  triple (val_ge n1 n2)
    \[]
    (fun r => \[r = isTrue (n1 >= n2)]).
Proof using. intros. applys* triple_binop. applys* evalbinop_ge. Qed.

Lemma triple_gt : forall n1 n2,
  triple (val_gt n1 n2)
    \[]
    (fun r => \[r = isTrue (n1 > n2)]).
Proof using. intros. applys* triple_binop. applys* evalbinop_gt. Qed.

Lemma triple_ptr_add : forall p n,
  p + n >= 0 ->
  triple (val_ptr_add p n)
    \[]
    (fun r => \[r = val_loc (abs (p + n))]).
Proof using.
  intros. applys* triple_binop. applys* evalbinop_ptr_add.
  { rewrite~ abs_nonneg. }
Qed.

Lemma triple_ptr_add_nat : forall p (f:nat),
  triple (val_ptr_add p f)
    \[]
    (fun r => \[r = val_loc (p+f)%nat]).
Proof using.
  intros. applys triple_conseq triple_ptr_add. { math. } { xsimpl. }
  { xsimpl. intros. subst. fequals.
    applys eq_nat_of_eq_int. rewrite abs_nonneg; math. }
Qed.

(* ----------------------------------------------------------------- *)
(** *** Structural Rule for [wp] *)

(** Definition of [wp] *)

Definition wp (t:trm) (Q:val->hprop) : hprop :=
  fun s => eval s t Q.

(** Equivalence between [wp] and [triple] *)

Lemma wp_equiv : forall t H Q,
  (H ==> wp t Q) <-> (triple t H Q).
Proof using. intros. unfold wp, triple. iff*. Qed.

(** Consequence rule for [wp]. *)

Lemma wp_conseq : forall t Q1 Q2,
  Q1 ===> Q2 ->
  wp t Q1 ==> wp t Q2.
Proof using. unfold wp. introv M. intros s Hs. applys* eval_conseq. Qed.

(** Frame rule for [wp]. *)

Lemma wp_frame : forall t H Q,
  (wp t Q) \* H ==> wp t (Q \*+ H).
Proof using.
  intros. unfold wp. intros h HF.
  lets (h1&h2&M1&M2&MD&MU): hstar_inv (rm HF).
  subst. applys eval_conseq.
  { applys eval_frame M1 MD. }
  { xsimpl. intros h' ->. applys M2. }
Qed.

(** Corollaries, including ramified frame rule. *)

Lemma wp_ramified : forall t Q1 Q2,
  (wp t Q1) \* (Q1 \--* Q2) ==> (wp t Q2).
Proof using.
  intros. applys himpl_trans.
  { applys wp_frame. }
  { applys wp_conseq. xsimpl. }
Qed.

Lemma wp_conseq_frame : forall t H Q1 Q2,
  Q1 \*+ H ===> Q2 ->
  (wp t Q1) \* H ==> (wp t Q2).
Proof using.
  introv M. rewrite <- qwand_equiv in M. xchange M. applys wp_ramified.
Qed.

Lemma wp_ramified_trans : forall t H Q1 Q2,
  H ==> (wp t Q1) \* (Q1 \--* Q2) ->
  H ==> (wp t Q2).
Proof using. introv M. xchange M. applys wp_ramified. Qed.

(* ----------------------------------------------------------------- *)
(** *** Weakest-Precondition Style Reasoning Rules for Terms. *)

Lemma wp_eval_like : forall t1 t2 Q,
  eval_like t1 t2 ->
  wp t1 Q ==> wp t2 Q.
Proof using. introv E Hs. applys* E Hs. Qed.

Lemma wp_val : forall v Q,
  Q v ==> wp (trm_val v) Q.
Proof using. unfold wp. intros. intros h K. applys* eval_val. Qed.

Lemma wp_fun : forall x t Q,
  Q (val_fun x t) ==> wp (trm_fun x t) Q.
Proof using. unfold wp. intros. intros h K. applys* eval_fun. Qed.

Lemma wp_fix : forall f x t Q,
  Q (val_fix f x t) ==> wp (trm_fix f x t) Q.
Proof using. unfold wp. intros. intros h K. applys* eval_fix. Qed.

Lemma wp_app_fun : forall x v1 v2 t1 Q,
  v1 = val_fun x t1 ->
  wp (subst x v2 t1) Q ==> wp (trm_app v1 v2) Q.
Proof using. unfold wp. intros. intros h K. applys* eval_app_fun. Qed.

Lemma wp_app_fix : forall f x v1 v2 t1 Q,
  v1 = val_fix f x t1 ->
  wp (subst x v2 (subst f v1 t1)) Q ==> wp (trm_app v1 v2) Q.
Proof using. unfold wp. intros. intros h K. applys* eval_app_fix. Qed.

Lemma wp_seq : forall t1 t2 Q,
  wp t1 (fun r => wp t2 Q) ==> wp (trm_seq t1 t2) Q.
Proof using. unfold wp. intros. intros h K. applys* eval_seq. Qed.

Lemma wp_let : forall x t1 t2 Q,
  wp t1 (fun v => wp (subst x v t2) Q) ==> wp (trm_let x t1 t2) Q.
Proof using. unfold wp. intros. intros h K. applys* eval_let. Qed.

Lemma wp_if : forall b t1 t2 Q,
  wp (if b then t1 else t2) Q ==> wp (trm_if b t1 t2) Q.
Proof using. unfold wp. intros. intros h K. applys* eval_if. Qed.

Lemma wp_if_case : forall b t1 t2 Q,
  (if b then wp t1 Q else wp t2 Q) ==> wp (trm_if b t1 t2) Q.
Proof using. intros. applys himpl_trans_r wp_if. case_if~. Qed.

(* ################################################################# *)
(** * WP Generator *)

(** This section defines a "weakest-precondition style characteristic
     formula generator". This technology adapts the technique of
     "characteristic formulae" (originally developed in CFML 1.0)
     to produce weakest preconditions. (The formulae, their manipulation,
     and their correctness proofs are simpler in wp-style.)

    The goal of the section is to define a function [wpgen t], recursively
    over the structure of [t], such that [wpgen t Q] entails [wp t Q].
    Unlike [wp t Q], which is defined semantically, [wpgen t Q] is defined
    following the syntax of [t].

    Technically, we define [wpgen E t], where [E] is a list of bindings,
    to compute a formula that entails [wp (isubst E t)], where [isubst E t]
    denotes the iterated substitution of bindings from [E] inside [t]. *)

(* ================================================================= *)
(** ** Definition of Context as List of Bindings *)

(** In order to define a structurally recursive and relatively
    efficient characteristic formula generator, we need to introduce
    contexts, that essentially serve to apply substitutions lazily. *)

Open Scope liblist_scope.

(** A context is an association list from variables to values. *)

Definition ctx : Type := list (var*val).

(** [lookup x E] returns [Some v] if [x] is bound to a value [v],
    and [None] otherwise. *)

Fixpoint lookup (x:var) (E:ctx) : option val :=
  match E with
  | nil => None
  | (y,v)::E1 => if var_eq x y
                   then Some v
                   else lookup x E1
  end.

(** [rem x E] denotes the removal of bindings on [x] from [E]. *)

Fixpoint rem (x:var) (E:ctx) : ctx :=
  match E with
  | nil => nil
  | (y,v)::E1 =>
      let E1' := rem x E1 in
      if var_eq x y then E1' else (y,v)::E1'
  end.

(** [ctx_disjoint E1 E2] asserts that the two contexts have disjoint
    domains. *)

Definition ctx_disjoint (E1 E2:ctx) : Prop :=
  forall x v1 v2, lookup x E1 = Some v1 -> lookup x E2 = Some v2 -> False.

(** [ctx_equiv E1 E2] asserts that the two contexts bind same
    keys to same values. *)

Definition ctx_equiv (E1 E2:ctx) : Prop :=
  forall x, lookup x E1 = lookup x E2.

(** Basic properties of context operations follow. *)

Section CtxOps.

Lemma lookup_app : forall E1 E2 x,
  lookup x (E1 ++ E2) = match lookup x E1 with
                         | None => lookup x E2
                         | Some v => Some v
                         end.
Proof using.
  introv. induction E1 as [|(y,w) E1']; rew_list; simpl; intros.
  { auto. } { case_var~. }
Qed.

Lemma lookup_rem : forall x y E,
  lookup x (rem y E) = If x = y then None else lookup x E.
Proof using.
  intros. induction E as [|(z,v) E'].
  { simpl. case_var~. }
  { simpl. case_var~; simpl; case_var~. }
Qed.

Lemma rem_app : forall x E1 E2,
  rem x (E1 ++ E2) = rem x E1 ++ rem x E2.
Proof using.
  intros. induction E1 as [|(y,w) E1']; rew_list; simpl. { auto. }
  { case_var~. { rew_list. fequals. } }
Qed.

Lemma ctx_equiv_rem : forall x E1 E2,
  ctx_equiv E1 E2 ->
  ctx_equiv (rem x E1) (rem x E2).
Proof using.
  introv M. unfolds ctx_equiv. intros y.
  do 2 rewrite lookup_rem. case_var~.
Qed.

Lemma ctx_disjoint_rem : forall x E1 E2,
  ctx_disjoint E1 E2 ->
  ctx_disjoint (rem x E1) (rem x E2).
Proof using.
  introv D. intros y v1 v2 K1 K2. rewrite lookup_rem in *.
  case_var~. applys* D K1 K2.
Qed.

Lemma ctx_disjoint_equiv_app : forall E1 E2,
  ctx_disjoint E1 E2 ->
  ctx_equiv (E1 ++ E2) (E2 ++ E1).
Proof using.
  introv D. intros x. do 2 rewrite~ lookup_app.
  case_eq (lookup x E1); case_eq (lookup x E2); auto.
  { intros v2 K2 v1 K1. false* D. }
Qed.

End CtxOps.

(* ================================================================= *)
(** ** Multi-Substitution *)

(* ----------------------------------------------------------------- *)
(** *** Definition of Multi-Substitution *)

(** The specification of the characteristic formula generator is expressed
    using the multi-substitution function, which substitutes a list of
    bindings inside a term. *)

Fixpoint isubst (E:ctx) (t:trm) : trm :=
  match t with
  | trm_val v =>
       v
  | trm_var x =>
       match lookup x E with
       | None => t
       | Some v => v
       end
  | trm_fun x t1 =>
       trm_fun x (isubst (rem x E) t1)
  | trm_fix f x t1 =>
       trm_fix f x (isubst (rem x (rem f E)) t1)
  | trm_if t0 t1 t2 =>
       trm_if (isubst E t0) (isubst E t1) (isubst E t2)
  | trm_seq t1 t2 =>
       trm_seq (isubst E t1) (isubst E t2)
  | trm_let x t1 t2 =>
       trm_let x (isubst E t1) (isubst (rem x E) t2)
  | trm_app t1 t2 =>
       trm_app (isubst E t1) (isubst E t2)
  end.

(* ----------------------------------------------------------------- *)
(** *** Properties of Multi-Substitution *)

(** The goal of this entire section is only to establish [isubst_nil]
    and [isubst_rem], which assert:

        isubst nil t = t
    and
        isubst ((x,v)::E) t = subst x v (isubst (rem x E) t)
*)

(** [isubst_nil] explains that the empty substitution is the identity. *)

Lemma isubst_nil : forall t,
  isubst nil t = t.
Proof using. intros t. induction t; simpl; fequals. Qed.

(** [subst_eq_isubst_one] relates [subst] and [isubst]. *)

Lemma subst_eq_isubst_one : forall x v t,
  subst x v t = isubst ((x,v)::nil) t.
Proof using.
  intros. induction t; simpl.
  { fequals. }
  { case_var~. }
  { fequals. case_var~. { rewrite~ isubst_nil. } }
  { fequals. case_var; try case_var; simpl; try case_var; try rewrite isubst_nil; auto. }
  { fequals*. }
  { fequals*. }
  { fequals*. case_var~. { rewrite~ isubst_nil. } }
  { fequals*. }
Qed.

(** The next lemma shows that equivalent contexts produce equal
    results for [isubst]. *)

Lemma isubst_ctx_equiv : forall t E1 E2,
  ctx_equiv E1 E2 ->
  isubst E1 t = isubst E2 t.
Proof using.
  hint ctx_equiv_rem.
  intros t. induction t; introv EQ; simpl; fequals~.
  { rewrite~ EQ. }
Qed.

(** [isubst_app] asserts that [isubst] distribute over concatenation. *)

Lemma isubst_app : forall t E1 E2,
  isubst (E1 ++ E2) t = isubst E2 (isubst E1 t).
Proof using.
  hint ctx_disjoint_rem.
  intros t. induction t; simpl; intros.
  { fequals. }
  { rename v into x. rewrite~ lookup_app.
    case_eq (lookup x E1); introv K1; case_eq (lookup x E2); introv K2; auto.
    { simpl. rewrite~ K2. }
    { simpl. rewrite~ K2. } }
  { fequals. rewrite* rem_app. }
  { fequals. do 2 rewrite* rem_app. }
  { fequals*. }
  { fequals*. }
  { fequals*. { rewrite* rem_app. } }
  { fequals*. }
Qed.

(** [isubst_cons] is a corollary *)

Lemma isubst_cons : forall x v xvs t,
  isubst ((x,v)::xvs) t = isubst xvs (subst x v t).
Proof using.
  intros. rewrite <- app_cons_one_r. rewrite isubst_app.
  rewrite* <- subst_eq_isubst_one.
Qed.

(** The next lemma asserts that the concatenation order is irrelevant
    in a substitution if the contexts have disjoint domains. *)

Lemma isubst_app_swap : forall t E1 E2,
  ctx_disjoint E1 E2 ->
  isubst (E1 ++ E2) t = isubst (E2 ++ E1) t.
Proof using.
  introv D. applys isubst_ctx_equiv. applys~ ctx_disjoint_equiv_app.
Qed.

(** We are ready to derive the second targeted property of [isubst]. *)

Lemma isubst_rem : forall x v E t,
  isubst ((x, v)::E) t = subst x v (isubst (rem x E) t).
Proof using.
  intros. rewrite subst_eq_isubst_one. rewrite <- isubst_app.
  rewrite isubst_app_swap.
  { applys isubst_ctx_equiv. intros y. rew_list. simpl. rewrite lookup_rem. case_var~. }
  { intros y v1 v2 K1 K2. simpls. rewrite lookup_rem in K1. case_var. }
Qed.

(** A variant useful for [trm_fix] is proved next. *)

Lemma isubst_rem_2 : forall f x vf vx E t,
  isubst ((f,vf)::(x,vx)::E) t = subst x vx (subst f vf (isubst (rem x (rem f E)) t)).
Proof using.
  intros. do 2 rewrite subst_eq_isubst_one. do 2 rewrite <- isubst_app.
  rewrite isubst_app_swap.
  { applys isubst_ctx_equiv. intros y. rew_list. simpl. do 2 rewrite lookup_rem. case_var~. }
  { intros y v1 v2 K1 K2. rew_listx in *. simpls. do 2 rewrite lookup_rem in K1. case_var. }
Qed.

(* ================================================================= *)
(** ** Definition of [wpgen] *)

(** The definition of [wpgen E t] comes next. It depends on a predicate
    called [mkstruct] for handling structural rules, and on one auxiliary
    definition for each term rule. *)

(* ----------------------------------------------------------------- *)
(** *** Definition of [mkstruct] *)

(** Let [formula] denote the type of [wp t] and [wpgen t]. *)

Definition formula := (val -> hprop) -> hprop.

Implicit Type F : formula.

(** [mkstruct F] transforms a formula [F] into one that satisfies structural
    rules of Separation Logic. This predicate transformer enables integrating
    support for the frame rule (and other structural rules), in characteristic
    formulae. *)

Definition mkstruct (F:formula) : formula :=
  fun Q => \exists Q', F Q' \* (Q' \--* Q).

Lemma mkstruct_ramified : forall Q1 Q2 F,
  (mkstruct F Q1) \* (Q1 \--* Q2) ==> (mkstruct F Q2).
Proof using. unfold mkstruct. xsimpl. Qed.

Arguments mkstruct_ramified : clear implicits.

Lemma mkstruct_erase : forall Q F,
  F Q ==> mkstruct F Q.
Proof using. unfolds mkstruct. xsimpl. Qed.

Arguments mkstruct_erase : clear implicits.

Lemma mkstruct_conseq : forall F Q1 Q2,
  Q1 ===> Q2 ->
  mkstruct F Q1 ==> mkstruct F Q2.
Proof using.
  introv WQ. unfolds mkstruct. xpull. intros Q. xsimpl Q. xchanges WQ.
Qed.

Lemma mkstruct_frame : forall F H Q,
  (mkstruct F Q) \* H ==> mkstruct F (Q \*+ H).
Proof using.
  intros. unfold mkstruct. xpull. intros Q'. xsimpl Q'.
Qed.

Lemma mkstruct_monotone : forall F1 F2 Q,
  (forall Q, F1 Q ==> F2 Q) ->
  mkstruct F1 Q ==> mkstruct F2 Q.
Proof using.
  introv WF. unfolds mkstruct. xpull. intros Q'. xchange WF. xsimpl Q'.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Definition of Auxiliary Definition for [wpgen] *)

(** we state auxiliary definitions for [wpgen], one per term construct.
    For simplicity, we here assume the term [t] to be in A-normal form.
    If it is not, the formula generated will be incomplete, that is,
    useless to prove triples about the term [t]. Note that the actual
    generator in CFML2 does support terms that are not in A-normal form. *)

Definition wpgen_fail : formula := fun Q =>
  \[False].

Definition wpgen_val (v:val) : formula := fun Q =>
  Q v.

Definition wpgen_fun (Fof:val->formula) : formula := fun Q =>
  \forall vf, \[forall vx Q', Fof vx Q' ==> wp (trm_app vf vx) Q'] \-* Q vf.

Definition wpgen_fix (Fof:val->val->formula) : formula := fun Q =>
  \forall vf, \[forall vx Q', Fof vf vx Q' ==> wp (trm_app vf vx) Q'] \-* Q vf.

Definition wpgen_var (E:ctx) (x:var) : formula :=
  match lookup x E with
  | None => wpgen_fail
  | Some v => wpgen_val v
  end.

Definition wpgen_seq (F1 F2:formula) : formula := fun Q =>
  F1 (fun v => F2 Q).

Definition wpgen_let (F1:formula) (F2of:val->formula) : formula := fun Q =>
  F1 (fun v => F2of v Q).

Definition wpgen_if (t:trm) (F1 F2:formula) : formula := fun Q =>
  \exists (b:bool), \[t = trm_val (val_bool b)] \* (if b then F1 Q else F2 Q).

Definition wpgen_if_trm (F0 F1 F2:formula) : formula :=
  wpgen_let F0 (fun v => mkstruct (wpgen_if v F1 F2)).

Definition wpgen_app (t:trm) : formula := fun Q =>
  \exists H, H \* \[triple t H Q].

(* ----------------------------------------------------------------- *)
(** *** Recursive Definition of [wpgen] *)

(** [wpgen E t] is structurally recursive on [t]. Note that this function does
    not recurse through values. Note also that the context [E] gets extended
    when traversing bindings, in the let-binding and the function cases. *)

Fixpoint wpgen (E:ctx) (t:trm) : formula :=
  mkstruct match t with
  | trm_val v => wpgen_val v
  | trm_var x => wpgen_var E x
  | trm_fun x t1 => wpgen_fun (fun v => wpgen ((x,v)::E) t1)
  | trm_fix f x t1 => wpgen_fix (fun vf v => wpgen ((f,vf)::(x,v)::E) t1)
  | trm_if t0 t1 t2 => wpgen_if (isubst E t0) (wpgen E t1) (wpgen E t2)
  | trm_seq t1 t2 => wpgen_seq (wpgen E t1) (wpgen E t2)
  | trm_let x t1 t2 => wpgen_let (wpgen E t1) (fun v => wpgen ((x,v)::E) t2)
  | trm_app t1 t2 => wpgen_app (isubst E t)
  end.

(* ----------------------------------------------------------------- *)
(** *** Soundness of [wpgen] *)

(** [formula_sound t F] asserts that, for any [Q], the Separation Logic
    judgment [triple (F Q) t Q] is valid. In other words, it states that
    [F] is a stronger formula than [wp t].

    The soundness theorem that we are ultimately interested in asserts that
    [formula_sound (isubst E t) (wpgen E t)] holds for any [E] and [t]. *)

Definition formula_sound (t:trm) (F:formula) : Prop :=
  forall Q, F Q ==> wp t Q.

Lemma wp_sound : forall t,
  formula_sound t (wp t).
Proof using. intros. intros Q. applys himpl_refl. Qed.

(** One soundness lemma for [mkstruct]. *)

Lemma mkstruct_wp : forall t,
  mkstruct (wp t) = (wp t).
Proof using.
  intros. applys fun_ext_1. intros Q. applys himpl_antisym.
  { unfold mkstruct. xpull. intros Q'. applys wp_ramified. }
  { applys mkstruct_erase. }
Qed.

Lemma mkstruct_sound : forall t F,
  formula_sound t F ->
  formula_sound t (mkstruct F).
Proof using.
  introv M. unfolds formula_sound. intros Q'.
  rewrite <- mkstruct_wp. applys* mkstruct_monotone M.
Qed.

(** One soundness lemma for each term construct. *)

Lemma wpgen_fail_sound : forall t,
  formula_sound t wpgen_fail.
Proof using. intros. intros Q. unfold wpgen_fail. xpull. Qed.

Lemma wpgen_val_sound : forall v,
  formula_sound (trm_val v) (wpgen_val v).
Proof using. intros. intros Q. unfolds wpgen_val. applys wp_val. Qed.

Lemma wpgen_fun_sound : forall x t1 Fof,
  (forall vx, formula_sound (subst x vx t1) (Fof vx)) ->
  formula_sound (trm_fun x t1) (wpgen_fun Fof).
Proof using.
  introv M. intros Q. unfolds wpgen_fun. applys himpl_hforall_l (val_fun x t1).
  xchange hwand_hpure_l.
  { intros. applys himpl_trans_r. { applys* wp_app_fun. } { applys* M. } }
  { applys wp_fun. }
Qed.

Lemma wpgen_fix_sound : forall f x t1 Fof,
  (forall vf vx, formula_sound (subst x vx (subst f vf t1)) (Fof vf vx)) ->
  formula_sound (trm_fix f x t1) (wpgen_fix Fof).
Proof using.
  introv M. intros Q. unfolds wpgen_fix.
  applys himpl_hforall_l (val_fix f x t1). xchange hwand_hpure_l.
  { intros. applys himpl_trans_r. { applys* wp_app_fix. } { applys* M. } }
  { applys wp_fix. }
Qed.

Lemma wpgen_seq_sound : forall F1 F2 t1 t2,
  formula_sound t1 F1 ->
  formula_sound t2 F2 ->
  formula_sound (trm_seq t1 t2) (wpgen_seq F1 F2).
Proof using.
  introv S1 S2. intros Q. unfolds wpgen_seq. applys himpl_trans_r wp_seq.
  applys himpl_trans S1. applys wp_conseq. intros v. applys S2.
Qed.

Lemma wpgen_let_sound : forall F1 F2of x t1 t2,
  formula_sound t1 F1 ->
  (forall v, formula_sound (subst x v t2) (F2of v)) ->
  formula_sound (trm_let x t1 t2) (wpgen_let F1 F2of).
Proof using.
  introv S1 S2. intros Q. unfolds wpgen_let. applys himpl_trans_r wp_let.
  applys himpl_trans S1. applys wp_conseq. intros v. applys S2.
Qed.

Lemma wpgen_if_sound : forall F1 F2 t0 t1 t2,
  formula_sound t1 F1 ->
  formula_sound t2 F2 ->
  formula_sound (trm_if t0 t1 t2) (wpgen_if t0 F1 F2).
Proof using.
  introv S1 S2. intros Q. unfold wpgen_if. xpull. intros b ->.
  applys himpl_trans_r wp_if. case_if. { applys S1. } { applys S2. }
Qed.

Lemma wpgen_app_sound : forall t,
  formula_sound t (wpgen_app t).
Proof using.
  intros t Q. unfold wpgen_app. xpull. intros H M. rewrite wp_equiv. apply M.
Qed.

(** The main inductive proof for the soundness theorem. *)

Lemma wpgen_sound : forall E t,
  formula_sound (isubst E t) (wpgen E t).
Proof using.
  intros. gen E. induction t; intros; simpl;
   try applys mkstruct_sound.
  { applys wpgen_val_sound. }
  { rename v into x. unfold wpgen_var. case_eq (lookup x E).
    { intros v EQ. applys wpgen_val_sound. }
    { intros N. applys wpgen_fail_sound. } }
  { applys wpgen_fun_sound.
    { intros vx. rewrite* <- isubst_rem. } }
  { applys* wpgen_fix_sound.
    { fold isubst. intros vf vx. rewrite* <- isubst_rem_2. } }
  { applys wpgen_app_sound. }
  { applys* wpgen_seq_sound. }
  { rename v into x. applys* wpgen_let_sound.
    { intros v. rewrite* <- isubst_rem. } }
  { applys* wpgen_if_sound. }
Qed.

Lemma himpl_wpgen_wp : forall t Q,
  wpgen nil t Q ==> wp t Q.
Proof using.
  introv M. lets N: (wpgen_sound nil t). rewrite isubst_nil in N. applys* N.
Qed.

(** The final theorem for closed terms. *)

Lemma triple_of_wpgen : forall t H Q,
  H ==> wpgen nil t Q ->
  triple t H Q.
Proof using.
  introv M. rewrite <- wp_equiv. xchange M. applys himpl_wpgen_wp.
Qed.

(* ################################################################# *)
(** * Practical Proofs *)

(** This last section shows the techniques involved in setting up the lemmas
    and tactics required to carry out verification in practice, through
    concise proof scripts. *)

(* ================================================================= *)
(** ** Lemmas for Tactics to Manipulate [wpgen] Formulae *)

Lemma xstruct_lemma : forall F H Q,
  H ==> F Q ->
  H ==> mkstruct F Q.
Proof using. introv M. xchange M. applys mkstruct_erase. Qed.

Lemma xval_lemma : forall v H Q,
  H ==> Q v ->
  H ==> wpgen_val v Q.
Proof using. introv M. applys M. Qed.

Lemma xlet_lemma : forall H F1 F2of Q,
  H ==> F1 (fun v => F2of v Q) ->
  H ==> wpgen_let F1 F2of Q.
Proof using. introv M. xchange M. Qed.

Lemma xseq_lemma : forall H F1 F2 Q,
  H ==> F1 (fun v => F2 Q) ->
  H ==> wpgen_seq F1 F2 Q.
Proof using. introv M. xchange M. Qed.

Lemma xif_lemma : forall b H F1 F2 Q,
  (b = true -> H ==> F1 Q) ->
  (b = false -> H ==> F2 Q) ->
  H ==> wpgen_if b F1 F2 Q.
Proof using. introv M1 M2. unfold wpgen_if. xsimpl* b. case_if*. Qed.

Lemma xapp_lemma : forall t Q1 H1 H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* protect Q) ->
  H ==> wpgen_app t Q.
Proof using.
  introv M W. unfold wpgen_app. xsimpl.
  applys triple_ramified_frame M. applys W.
Qed.

Lemma xfun_spec_lemma : forall (S:val->Prop) H Q Fof,
  (forall vf,
    (forall vx H' Q', (H' ==> Fof vx Q') -> triple (trm_app vf vx) H' Q') ->
    S vf) ->
  (forall vf, S vf -> (H ==> Q vf)) ->
  H ==> wpgen_fun Fof Q.
Proof using.
  introv M1 M2. unfold wpgen_fun. xsimpl. intros vf N.
  applys M2. applys M1. introv K. rewrite <- wp_equiv. xchange K. applys N.
Qed.

Lemma xfun_nospec_lemma : forall H Q Fof,
  (forall vf,
     (forall vx H' Q', (H' ==> Fof vx Q') -> triple (trm_app vf vx) H' Q') ->
     (H ==> Q vf)) ->
  H ==> wpgen_fun Fof Q.
Proof using.
  introv M. unfold wpgen_fun. xsimpl. intros vf N. applys M.
  introv K. rewrite <- wp_equiv. xchange K. applys N.
Qed.

Lemma xfix_spec_lemma : forall (S:val->Prop) H Q Fof,
  (forall vf,
    (forall vx H' Q', (H' ==> Fof vf vx Q') -> triple (trm_app vf vx) H' Q') ->
    S vf) ->
  (forall vf, S vf -> (H ==> Q vf)) ->
  H ==> wpgen_fix Fof Q.
Proof using.
  introv M1 M2. unfold wpgen_fix. xsimpl. intros vf N.
  applys M2. applys M1. introv K. rewrite <- wp_equiv. xchange K. applys N.
Qed.

Lemma xfix_nospec_lemma : forall H Q Fof,
  (forall vf,
     (forall vx H' Q', (H' ==> Fof vf vx Q') -> triple (trm_app vf vx) H' Q') ->
     (H ==> Q vf)) ->
  H ==> wpgen_fix Fof Q.
Proof using.
  introv M. unfold wpgen_fix. xsimpl. intros vf N. applys M.
  introv K. rewrite <- wp_equiv. xchange K. applys N.
Qed.

Lemma xwp_lemma_fun : forall v1 v2 x t H Q,
  v1 = val_fun x t ->
  H ==> wpgen ((x,v2)::nil) t Q ->
  triple (trm_app v1 v2) H Q.
Proof using.
  introv M1 M2. rewrite <- wp_equiv. xchange M2.
  xchange (>> wpgen_sound ((x,v2)::nil) t Q).
  rewrite <- subst_eq_isubst_one. applys* wp_app_fun.
Qed.

Lemma xwp_lemma_fix : forall v1 v2 f x t H Q,
  v1 = val_fix f x t ->
  f <> x ->
  H ==> wpgen ((f,v1)::(x,v2)::nil) t Q ->
  triple (trm_app v1 v2) H Q.
Proof using.
  introv M1 N M2. rewrite <- wp_equiv. xchange M2.
  xchange (>> wpgen_sound (((f,v1)::nil) ++ (x,v2)::nil) t Q).
  rewrite isubst_app. do 2 rewrite <- subst_eq_isubst_one.
  applys* wp_app_fix.
Qed.

Lemma xtriple_lemma : forall t H (Q:val->hprop),
  H ==> mkstruct (wpgen_app t) Q ->
  triple t H Q.
Proof using.
  introv M. rewrite <- wp_equiv. xchange M. unfold mkstruct, wpgen_app.
  xpull. intros Q' H' N. rewrite <- wp_equiv in N. xchange N.
  applys wp_ramified.
Qed.

(* ================================================================= *)
(** ** Tactics to Manipulate [wpgen] Formulae *)

(** The tactic are presented in chapter [WPgen]. *)

(** Database of hints for [xapp]. *)

#[global] Hint Resolve triple_get triple_set triple_ref triple_free : triple.

#[global] Hint Resolve triple_add triple_div triple_neg triple_opp triple_eq
   triple_neq triple_sub triple_mul triple_mod triple_le triple_lt
   triple_ge triple_gt triple_ptr_add triple_ptr_add_nat : triple.

(** [xstruct] removes the leading [mkstruct]. *)

Tactic Notation "xstruct" :=
  applys xstruct_lemma.

(** [xstruct_if_needed] removes the leading [mkstruct] if there is one. *)

Tactic Notation "xstruct_if_needed" :=
  try match goal with |- ?H ==> mkstruct ?F ?Q => xstruct end.

Tactic Notation "xval" :=
  xstruct_if_needed; applys xval_lemma.

Tactic Notation "xlet" :=
  xstruct_if_needed; applys xlet_lemma.

Tactic Notation "xseq" :=
  xstruct_if_needed; applys xseq_lemma.

Tactic Notation "xseq_xlet_if_needed" :=
  try match goal with |- ?H ==> mkstruct ?F ?Q =>
  match F with
  | wpgen_seq ?F1 ?F2 => xseq
  | wpgen_let ?F1 ?F2of => xlet
  end end.

Tactic Notation "xif" :=
  xseq_xlet_if_needed; xstruct_if_needed;
  applys xif_lemma; rew_bool_eq.

(** [xapp_try_clear_unit_result] implements some post-processing for
    cleaning up unused variables. *)

Tactic Notation "xapp_try_clear_unit_result" :=
  try match goal with |- val -> _ => intros _ end.

Tactic Notation "xtriple" :=
  intros; applys xtriple_lemma.

Tactic Notation "xtriple_if_needed" :=
  try match goal with |- triple ?t ?H ?Q => applys xtriple_lemma end.

(** [xapp_simpl] performs the final step of the tactic [xapp].
    It leverages [xsimpl_no_cancel_wand tt] which is a restricted version of
    [xsimpl] that does not attempt to cancel out magic wands. *)

Lemma xapp_simpl_lemma : forall F H Q,
  H ==> F Q ->
  H ==> F Q \* (Q \--* protect Q).
Proof using. introv M. xchange M. unfold protect. xsimpl. Qed.

Tactic Notation "xapp_simpl" :=
  first [ eapply xapp_simpl_lemma (* handles specification coming from [xfun] *)
        | xsimpl_no_cancel_wand tt; unfold protect; xapp_try_clear_unit_result ].

Tactic Notation "xapp_pre" :=
  xtriple_if_needed; xseq_xlet_if_needed; xstruct_if_needed.

(** [xapp_nosubst E] implements the heart of [xapp E]. If the argument [E] was
    always a triple, it would suffice to run [applys xapp_lemma E; xapp_simpl].
    Yet, [E] might be an specification involving quantifiers. These quantifiers
    need to be first instantiated. This instantiation is achieved by means of
    the tactic [forwards_nounfold_then] offered by the TLC library. *)

Tactic Notation "xapp_nosubst" constr(E) :=
  xapp_pre;
  forwards_nounfold_then E ltac:(fun K => applys xapp_lemma K; xapp_simpl).

(** [xapp_apply_spec] implements the heart of [xapp], when called without
    argument. If finds out the specification triple, either in the hint data
    base named [triple], or in the context by looking for an induction
    hypothesis. Disclaimer: as explained in chapter [WPgen], the simple
    implementation of [xapp_apply_spec] which we use here does not apply when
    the specification includes premises that cannot be solved by [eauto];
    it such cases, the tactic [xapp E] must be called, providing the
    specification [E] explicitly. This limitation is overcome using more
    involved [Hint Extern] tricks in CFML 2.0. *)

Tactic Notation "xapp_apply_spec" :=
  first [ solve [ eauto with triple ]
        | match goal with H: _ |- _ => eapply H end ].

(** [xapp_nosubst_for_records] is place holder for implementing [xapp] on
    records. It is implemented further on. *)

Ltac xapp_nosubst_for_records tt :=
 fail.

(** [xapp] first calls [xtriple] if the goal is [triple t H Q] instead
    of [H ==> wp t Q]. *)

Tactic Notation "xapp_nosubst" :=
  xapp_pre;
  first [ applys xapp_lemma; [ xapp_apply_spec | xapp_simpl ]
        | xapp_nosubst_for_records tt ].

(** [xapp_try_subst] checks if the goal is of the form:
    - either [forall (r:val), (r = ...) -> ...]
    - or [forall (r:val), forall x, (r = ...) -> ...]

    in which case it substitutes [r] away. *)

Tactic Notation "xapp_try_subst" :=
  try match goal with
  | |- forall (r:val), (r = _) -> _ => intros ? ->
  | |- forall (r:val), forall x, (r = _) -> _ =>
      let y := fresh x in intros ? y ->; revert y
  end.

Tactic Notation "xapp" constr(E) :=
  xapp_nosubst E; xapp_try_subst.

Tactic Notation "xapp" :=
  xapp_nosubst; xapp_try_subst.

Tactic Notation "xapp_view" :=
  xseq_xlet_if_needed; xstruct_if_needed; applys xapp_lemma.

(** [xapp] is essentially equivalent to
    [ xapp_view; [ xapp_apply_spec | xapp_simpl ] ]. *)

(** [xfun] handles local functions, only for functions of one argument. *)

Tactic Notation "xfun" constr(S) :=
  xseq_xlet_if_needed; xstruct_if_needed;
  first [ applys xfun_spec_lemma S
        | applys xfix_spec_lemma S ].

Tactic Notation "xfun" :=
  xseq_xlet_if_needed; xstruct_if_needed;
  first [ applys xfun_nospec_lemma
        | applys xfix_nospec_lemma ].

(** [xvars] may be called for unfolding "program variables as definitions",
    which take the form [Vars.x], and revealing the underlying string. *)

Tactic Notation "xvars" :=
  DefinitionsForVariables.libsepvar_unfold.

(** [xwp_simpl] is a specialized version of [simpl] to be used for
    getting the function [wp] to compute properly. *)

From Coq Require Bool.

Ltac xwp_simpl :=
  xvars;
  cbn beta delta [
     LibListExec.combine List.combine
     wpgen wpgen_var isubst lookup var_eq
     string_dec string_rec string_rect
     sumbool_rec sumbool_rect
     Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
     Bool.bool_dec bool_rec bool_rect ] iota zeta;
  simpl.

(** [xwp] evaluates [wpgen] for the term appearing in the goal.
    This implementation of [xwp] is for functions of arity one only,
    refined further on for arbitrary arities. *)

Tactic Notation "xwp_arity_one_only" :=
  intros;
  first [ applys xwp_lemma_fun; [ reflexivity | ]
        | applys xwp_lemma_fix; [ reflexivity | ] ];
  xwp_simpl.

(* ================================================================= *)
(** ** Additional Tooling for [xapp] *)

(** [xapp*] is a convenient notation for [xapp; auto_star].
    [xapp* E] is a convenient notation for [xapp E; auto_star]. *)

Tactic Notation "xapp" "*" :=
  xapp; auto_star.

Tactic Notation "xapp" "*" constr(E) :=
  xapp E; auto_star.

(** [xapp_debug] is a tactic to help debugging a call to [xapp]. *)

Tactic Notation "xapp_debug" :=
  let step msg := (idtac msg; match goal with |- ?H => idtac H end) in
  xapp_pre;
  step "============= goal after [xapp_pre] ==============";
  first
  [ applys xapp_lemma;
     [ step "============= triple for [xapp_apply_spec] ==============";
       first [ xapp_apply_spec; fail 1
             | idtac "=====================================================";
               idtac "===> [xapp_apply_spec] failed!";
               idtac "===> [eauto with triple] could not solve find a specification";
               idtac "===> try [xapp_view. eapply myspec.] or [xapp myspec]. ";
               idtac "===> if side-conditions are not solved by [eauto], [xapp] won't work."]
     | idtac ]
  | applys xapp_lemma;
    [ xapp_apply_spec
    | step "============= entailment for [xapp_simpl] ==============";
       xapp_simpl  ] ].

(* ================================================================= *)
(** ** Notations for Triples and [wpgen] *)

Declare Scope wp_scope.

(** Notation for printing proof obligations arising from [wpgen]. *)

Notation "'PRE' H 'CODE' F 'POST' Q" :=
  (H ==> (mkstruct F) Q)
  (at level 8, H at level 0, F, Q at level 0,
   format "'[v' 'PRE'  H  '/' 'CODE'  F '/' 'POST'  Q ']'") : wp_scope.

Notation "` F" :=
  (mkstruct F)
  (at level 10,
   format "` F") : wp_scope.

(** Custom grammar for the display of characteristic formulae. *)

Declare Custom Entry wp.

Notation "<[ e ]>" :=
  e
  (at level 0, e custom wp at level 99) : wp_scope.

Notation "` F" :=
  (mkstruct F)
  (in custom wp at level 10,
   format "` F") : wp_scope.

Notation "( x )" :=
  x
  (in custom wp,
   x at level 99) : wp_scope.

Notation "{ x }" :=
  x
  (in custom wp at level 0,
   x constr,
   only parsing) : wp_scope.

Notation "x" :=
  x
  (in custom wp at level 0,
   x constr at level 0) : wp_scope.

Notation "'Fail'" :=
  ((wpgen_fail))
  (in custom wp at level 69) : wp_scope.

Notation "'Val' v" :=
  ((wpgen_val v))
  (in custom wp at level 69) : wp_scope.

Notation "'Let' x ':=' F1 'in' F2" :=
  ((wpgen_let F1 (fun x => F2)))
  (in custom wp at level 69,
   x name, (* NOTE: For compilation with Coq 8.12, replace "name" with "ident",
               here and in the next 3 occurrences in the rest of the section. *)
   F1 custom wp at level 99,
   F2 custom wp at level 99,
   right associativity,
  format "'[v' '[' 'Let'  x  ':='  F1  'in' ']' '/' '[' F2 ']' ']'") : wp_scope.

Notation "'Seq' F1 ; F2" :=
  ((wpgen_seq F1 F2))
  (in custom wp at level 68,
   F1 custom wp at level 99,
   F2 custom wp at level 99,
   right associativity,
   format "'[v' 'Seq'  '[' F1 ']'  ; '/' '[' F2 ']' ']'") : wp_scope.

Notation "'App' t0 t1 .. tn" :=
 ((wpgen_app (trm_app .. (trm_app t0 t1) .. tn)))
  (in custom wp at level 68,
   t0 constr at level 0,
   t1 constr at level 0,
   tn constr at level 0)
  : wp_scope.

Notation "'If_' v 'Then' F1 'Else' F2" :=
  ((wpgen_if v F1 F2))
  (in custom wp at level 69,
   F1 custom wp at level 99,
   F2 custom wp at level 99,
   left associativity,
   format "'[v' '[' 'If_'  v  'Then'  ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'") : wp_scope.

Notation "'Fun' x '=>' F1" :=
  ((wpgen_fun (fun x => F1)))
  (in custom wp at level 69,
   x name,
   F1 custom wp at level 99,
   right associativity,
  format "'[v' '[' 'Fun'  x  '=>'  F1  ']' ']'") : wp_scope.

Notation "'Fix' vf x '=>' F1" :=
  ((wpgen_fix (fun vf x => F1)))
  (in custom wp at level 69,
   vf name, x name,
   F1 custom wp at level 99,
   right associativity,
   format "'[v' '[' 'Fix'  vf  x  '=>'  F1  ']' ']'") : wp_scope.

(* ================================================================= *)
(** ** Notation for Concrete Terms *)

(** The custom grammar for [trm] is defined in [LibSepVar]. *)

Declare Scope val_scope.

(** Terms *)

Notation "<{ e }>" :=
  e
  (at level 0, e custom trm at level 99) : trm_scope.

Notation "( x )" :=
  x
  (in custom trm, x at level 99) : trm_scope.

Notation "'begin' e 'end'" :=
  e
  (in custom trm, e custom trm at level 99, only parsing) : trm_scope.

Notation "{ x }" :=
  x
  (in custom trm, x constr) : trm_scope.

Notation "x" := x
  (in custom trm at level 0,
   x constr at level 0) : trm_scope.

Notation "t1 t2" := (trm_app t1 t2)
  (in custom trm at level 30,
   left associativity,
   only parsing) : trm_scope.

Notation "'if' t0 'then' t1 'else' t2" :=
  (trm_if t0 t1 t2)
  (in custom trm at level 69,
   t0 custom trm at level 99,
   t1 custom trm at level 99,
   t2 custom trm at level 99,
   left associativity,
   format "'[v' '[' 'if'  t0  'then'  ']' '/' '['   t1 ']' '/' 'else' '/' '['   t2 ']' ']'") : trm_scope.

Notation "'if' t0 'then' t1 'end'" :=
  (trm_if t0 t1 (trm_val val_unit))
  (in custom trm at level 69,
   t0 custom trm at level 99, (* at level 0 ? *)
   t1 custom trm at level 99,
   left associativity,
   format "'[v' '[' 'if'  t0  'then'  ']' '/' '['   t1 ']' '/' 'end' ']'") : trm_scope.

Notation "t1 ';' t2" :=
  (trm_seq t1 t2)
  (in custom trm at level 68,
   t2 custom trm at level 99,
   right associativity,
   format "'[v' '[' t1 ']' ';' '/' '[' t2 ']' ']'") : trm_scope.

Notation "'let' x '=' t1 'in' t2" :=
  (trm_let x t1 t2)
  (in custom trm at level 69,
   x at level 0,
   t1 custom trm at level 99,
   t2 custom trm at level 99,
   right associativity,
   format "'[v' '[' 'let'  x  '='  t1  'in' ']' '/' '[' t2 ']' ']'") : trm_scope.

(* Let-functions *)

Notation "'let' f x1 '=' t1 'in' t2" :=
  (trm_let f (trm_fun x1 t1) t2)
  (in custom trm at level 69,
   t1 custom trm,
   t2 custom trm,
   f, x1 at level 0,
   format "'let'  f  x1  '='  t1  'in'  t2") : val_scope.

Notation "'let' f x1 .. xn '=' t1 'in' t2" :=
  (trm_let f (trm_fun x1 .. (trm_fun xn t1) ..) t2)
  (in custom trm at level 69,
   t1 custom trm,
   t2 custom trm,
   f, x1, xn at level 0,
   format "'let'  f  x1  ..  xn  '='  t1  'in'  t2") : val_scope.

Notation "'let' 'rec' f x1 '=' t1 'in' t2" :=
  (trm_let f (trm_fix f x1 t1) t2)
  (in custom trm at level 69,
   t1 custom trm,
   t2 custom trm,
   f, x1 at level 0,
   format "'let'  'rec'  f  x1  '='  t1  'in'  t2") : val_scope.

Notation "'let' 'rec' f x1 x2 .. xn '=' t1 'in' t2" :=
  (trm_let f (trm_fix f x1 (trm_fun x2 .. (trm_fun xn t1) ..)) t2)
  (in custom trm at level 69,
   t1 custom trm,
   t2 custom trm,
   f, x1, x2, xn at level 0,
   format "'let'  'rec'  f  x1  x2  ..  xn  '='  t1  'in'  t2") : val_scope.

(* On-the-fly functions, as values *)

Notation "'fun' x1 '=>' t" :=
  (val_fun x1 t)
  (in custom trm at level 69,
   x1 at level 0,
   t custom trm at level 99,
   format "'fun'  x1  '=>'  t") : val_scope.

Notation "'fun' x1 x2 .. xn '=>' t" :=
  (val_fun x1 (trm_fun x2 .. (trm_fun xn t) ..))
  (in custom trm at level 69,
   t custom trm,
   x1, x2, xn at level 0,
   format "'fun'  x1  x2  ..  xn  '=>'  t") : val_scope.

Notation "'fix' f x1 '=>' t" :=
  (val_fix f x1 t)
  (in custom trm at level 69,
   f, x1 at level 0,
   t custom trm at level 99,
   format "'fix'  f  x1  '=>'  t") : val_scope.

Notation "'fix' f x1 x2 .. xn '=>' t" :=
  (val_fix f x1 (trm_fun x2 .. (trm_fun xn t) ..))
  (in custom trm at level 69,
   t custom trm,
   f, x1, x2, xn at level 0,
   format "'fix'  f  x1  x2  ..  xn  '=>'  t") : val_scope.

(* On-the-fly functions, as terms *)

Notation "'fun_' x1 '=>' t" :=
  (trm_fun x1 t)
  (in custom trm at level 69,
   x1 at level 0,
   t custom trm at level 99,
   format "'fun_'  x1  '=>'  t") : trm_scope.

Notation "'fun_' x1 .. xn '=>' t" :=
  (trm_fun x1 .. (trm_fun xn t) ..)
  (in custom trm at level 69,
   t custom trm,
   x1, xn at level 0,
   format "'fun_'  x1  ..  xn  '=>'  t") : trm_scope.

Notation "'fix_' vf x1 '=>' t" :=
  (trm_fix vf x1 t)
  (in custom trm at level 69,
   vf, x1 at level 0,
   t custom trm at level 99,
   format "'fix_'  vf x1  '=>'  t") : trm_scope.

Notation "'fix_' vf x1 x2 .. xn '=>' t" :=
  (trm_fix vf x1 (trm_fun x2 .. (trm_fun xn t) ..))
  (in custom trm at level 69,
   t custom trm,
   vf, x1, x2, xn at level 0,
   format "'fix_'  vf  x1  x2  ..  xn  '=>'  t") : trm_scope.

Notation "()" :=
  (trm_val val_unit)
  (in custom trm at level 0) : trm_scope.

Notation "()" :=
  (val_unit)
  (at level 0) : val_scope.

(** Notation for Primitive Operations. *)

Notation "'ref'" :=
  (trm_val (val_prim val_ref))
  (in custom trm at level 0, only parsing) : trm_scope.

Notation "'free'" :=
  (trm_val (val_prim val_free))
  (in custom trm at level 0, only parsing) : trm_scope.

Notation "'not'" :=
  (trm_val (val_prim val_neg))
  (in custom trm at level 0, only parsing) : trm_scope.

Notation "! t" :=
  (val_get t)
  (in custom trm at level 67,
   t custom trm at level 99) : trm_scope.

Notation "t1 := t2" :=
  (val_set t1 t2)
  (in custom trm at level 67) : trm_scope.

Notation "t1 + t2" :=
  (val_add t1 t2)
  (in custom trm at level 58) : trm_scope.

Notation "'- t" :=
  (val_opp t)
  (in custom trm at level 57,
   t custom trm at level 99) : trm_scope.

Notation "t1 - t2" :=
  (val_sub t1 t2)
  (in custom trm at level 58) : trm_scope.

Notation "t1 * t2" :=
  (val_mul t1 t2)
  (in custom trm at level 57) : trm_scope.

Notation "t1 / t2" :=
  (val_div t1 t2)
  (in custom trm at level 57) : trm_scope.

Notation "t1 'mod' t2" :=
  (val_mod t1 t2)
  (in custom trm at level 57) : trm_scope.

Notation "t1 = t2" :=
  (val_eq t1 t2)
  (in custom trm at level 58) : trm_scope.

Notation "t1 <> t2" :=
  (val_neq t1 t2)
  (in custom trm at level 58) : trm_scope.

Notation "t1 <= t2" :=
  (val_le t1 t2)
  (in custom trm at level 60) : trm_scope.

Notation "t1 < t2" :=
  (val_lt t1 t2)
  (in custom trm at level 60) : trm_scope.

Notation "t1 >= t2" :=
  (val_ge t1 t2)
  (in custom trm at level 60) : trm_scope.

Notation "t1 > t2" :=
  (val_gt t1 t2)
  (in custom trm at level 60) : trm_scope.

(* TESTING
Module TestingNotation.
Local Open Scope val_scope.
Local Open Scope trm_scope.

Definition test_app1 t1 t2 : trm :=
  <{ t1 t2 }>.

Definition test_app2 t1 t2 t3 : trm :=
  <{ t1 t2 t3 }>.

Definition test_fun1 x1 t : val :=
  <{ fun x1 => t }>.

Definition test_fun2 x1 x2 t : val :=
  <{ fun x1 x2 => t }>.

Definition test_fun3 x1 x2 x3 t : val :=
  <{ fun x1 x2 x3 => t }>.

Definition test_fix1 f x1 t : val :=
  <{ fun f x1 => t }>.

Definition test_fix2 f x1 x2 t : val :=
  <{ fun f x1 x2 => t }>.

Definition test_fix3 f x1 x2 x3 t : val :=
  <{ fun f x1 x2 x3 => t }>.

Definition test_trmfun_1 f x1 : trm :=
  <{ fun_ f x1 => x1 }>.

Definition test_trmfun_2 f x1 x2 : trm :=
  <{ fun_ f x1 x2 => x1 }>.

Definition test_trmfun_3 f x1 x2 x3 : trm :=
  <{ fun_ f x1 x2 x3 => x1 }>.

Definition test_trmfix1 f x1 t : trm :=
  <{ fix_ f x1 => t }>.

Definition test_trmfix2 f x1 x2 t : trm :=
  <{ fix_ f x1 x2 => t }>.

Definition test_trmfix3 f x1 x2 x3 t : trm :=
  <{ fix_ f x1 x2 x3 => t }>.

Definition test_letfun_1 f x1 t : trm :=
  <{ let f x1 = x1 in t }>.

Definition test_letfun_2 f x1 x2 t : trm :=
  <{ let f x1 x2 = x1 in t }>.

Definition test_letfun_3 f x1 x2 x3 t : trm :=
  <{ let f x1 x2 x3 = x1 in t }>.

Definition test_letfix_1 f x1 t : trm :=
  <{ let rec f x1 = x1 in t }>.

Definition test_letfix_2 f x1 x2 t : trm :=
  <{ let rec f x1 x2 = x1 in t }>.

Definition test_letfix_3 f x1 x2 x3 t : trm :=
  <{ let rec f x1 x2 x3 = x1 in t }>.

Print test_app1.
Print test_app2.
Print test_trmfix3.
Print test_fun3.

End TestingNotation.
*)

(* ================================================================= *)
(** ** Scopes, Coercions and Notations for Concrete Programs *)

Module ProgramSyntax.

Export NotationForVariables.

Module Vars := DefinitionsForVariables.

Close Scope fmap_scope.
Open Scope string_scope.
Open Scope val_scope.
Open Scope trm_scope.
Open Scope wp_scope.
Coercion string_to_var (x:string) : var := x.

End ProgramSyntax.

(* ################################################################# *)
(** * Additional Separation Logic Operators *)

(* ================================================================= *)
(** ** Disjunction: Definition and Properties of [hor] *)

Definition hor (H1 H2 : hprop) : hprop :=
  \exists (b:bool), if b then H1 else H2.

Lemma hor_sym : forall H1 H2,
  hor H1 H2 = hor H2 H1.
Proof using.
  intros. unfold hor. applys himpl_antisym.
  { applys himpl_hexists_l. intros b.
    applys himpl_hexists_r (neg b). destruct* b. }
  { applys himpl_hexists_l. intros b.
    applys himpl_hexists_r (neg b). destruct* b. }
Qed.

Lemma himpl_hor_r_l : forall H1 H2,
  H1 ==> hor H1 H2.
Proof using. intros. unfolds hor. exists* true. Qed.

Lemma himpl_hor_r_r : forall H1 H2,
  H2 ==> hor H1 H2.
Proof using. intros. unfolds hor. exists* false. Qed.

Lemma himpl_hor_l : forall H1 H2 H3,
  H1 ==> H3 ->
  H2 ==> H3 ->
  hor H1 H2 ==> H3.
Proof using.
  introv M1 M2. unfolds hor. applys himpl_hexists_l. intros b. case_if*.
Qed.

Lemma triple_hor : forall t H1 H2 Q,
  triple t H1 Q ->
  triple t H2 Q ->
  triple t (hor H1 H2) Q.
Proof using.
  introv M1 M2. unfold hor. applys triple_hexists.
  intros b. destruct* b.
Qed.

(* ================================================================= *)
(** ** Conjunction: Definition and Properties of [hand] *)

Definition hand (H1 H2 : hprop) : hprop :=
  \forall (b:bool), if b then H1 else H2.

Lemma hand_sym : forall H1 H2,
  hand H1 H2 = hand H2 H1.
Proof using.
  intros. unfold hand. applys himpl_antisym.
  { applys himpl_hforall_r. intros b.
    applys himpl_hforall_l (neg b). destruct* b. }
  { applys himpl_hforall_r. intros b.
    applys himpl_hforall_l (neg b). destruct* b. }
Qed.

Lemma himpl_hand_l_r : forall H1 H2,
  hand H1 H2 ==> H1.
Proof using. intros. unfolds hand. applys* himpl_hforall_l true. Qed.

Lemma himpl_hand_l_l : forall H1 H2,
  hand H1 H2 ==> H2.
Proof using. intros. unfolds hand. applys* himpl_hforall_l false. Qed.

Lemma himpl_hand_r : forall H1 H2 H3,
  H1 ==> H2 ->
  H1 ==> H3 ->
  H1 ==> hand H2 H3.
Proof using.
  introv M1 M2. unfold hand. applys himpl_hforall_r. intros b. case_if*.
Qed.

Lemma triple_hand_l : forall t H1 H2 Q,
  triple t H1 Q ->
  triple t (hand H1 H2) Q.
Proof using. introv M1. unfold hand. applys~ triple_hforall true. Qed.

Lemma triple_hand_r : forall t H1 H2 Q,
  triple t H2 Q ->
  triple t (hand H1 H2) Q.
Proof using. introv M1. unfold hand. applys~ triple_hforall false. Qed.

(* ################################################################# *)
(** * Generalization to N-ary Functions *)

(* ================================================================= *)
(** ** Smart Constructors for N-ary Functions and Applications *)

Definition vars : Type := list var.
Definition vals : Type := list val.
Definition trms : Type := list trm.

(** [trm_apps f ts] builds the application of the function [f] to the list
    of terms [ts]. *)

Fixpoint trm_apps (f:trm) (ts:trms) : trm :=
  match ts with
  | nil => f
  | ti::ts' => trm_apps (trm_app f ti) ts'
  end.

(** [trm_funs xs t] builds a term describing a function that expects
    arguments with names [xs], and that has [t] for body. *)

Fixpoint trm_funs (xs:vars) (t:trm) : trm :=
  match xs with
  | nil => t
  | x1::xs' => trm_fun x1 (trm_funs xs' t)
  end.

(** [val_funs xs t] is similar to [trm_funs xs t] but produces a value. *)

Definition val_funs (xs:vars) (t:trm) : val :=
  match xs with
  | nil => arbitrary
  | x1::xs' => val_fun x1 (trm_funs xs' t)
  end.

(** [trm_fixs f xs t] builds a term describing a recursive function
    named [f] that expects  arguments with names [xs], and that has [t]
    for body. *)

Definition trm_fixs (f:var) (xs:vars) (t:trm) : trm :=
  match xs with
  | nil => arbitrary
  | x1::xs' => trm_fix f x1 (trm_funs xs' t)
  end.

(** [val_fixs xs t] is similar to [trm_fixs xs t] but produces a value. *)

Definition val_fixs (f:var) (xs:vars) (t:trm) : val :=
  match xs with
  | nil => arbitrary
  | x1::xs' => val_fix f x1 (trm_funs xs' t)
  end.

(** [var_funs xs n] asserts that [xs] is a nonempty list made of
    [n] distinct variable names. *)

Definition var_funs (xs:vars) (n:nat) : Prop :=
     LibList.noduplicates xs
  /\ length xs = n
  /\ xs <> nil.

(** [trms_vals vs] converts a list of values [vs] into a list of terms
    made of the corresponding values, each converted using [trm_val]. *)

Coercion trms_vals (vs:vals) : trms :=
  LibList.map trm_val vs.

Lemma trms_vals_nil :
  trms_vals nil = nil.
Proof using. auto. Qed.

Lemma trms_vals_cons : forall v vs,
  trms_vals (v :: vs) = trm_val v :: trms_vals vs.
Proof using. intros. unfold trms_vals. rew_listx*. Qed.

#[local] Hint Rewrite trms_vals_nil trms_vals_cons : rew_listx.

(* ================================================================= *)
(** ** Evaluation Rules for N-ary Constructs *)

(** [subst_trm_funs] distributes [subst] over [trm_funs]. *)

Lemma subst_trm_funs : forall xs x v t1,
  ~ mem x xs ->
  subst x v (trm_funs xs t1) = trm_funs xs (subst x v t1).
Proof using.
  intros xs. induction xs as [|x xs']; introv N.
  { auto. }
  { rew_listx in N. rew_logic in N. destruct N. simpl. case_var. fequals*. }
Qed.

(** Evaluation rule for reducing [trm_funs] into [val_funs] *)

Lemma eval_like_trm_funs : forall xs t1,
  xs <> nil ->
  eval_like (val_funs xs t1) (trm_funs xs t1).
Proof using.
  introv N M. destruct xs; tryfalse. simpls. inverts M. applys* eval_fun.
Qed.

(** Auxiliary lemma: evaluation rule for reducing the first argument
    of a [val_funs] applied to an argument. *)

Lemma eval_like_app_val_funs_cons : forall x xs t1 t0 v,
  eval_like (val_funs (x :: xs) t1) t0 ->
  ~ mem x xs ->
  xs <> nil ->
  eval_like (val_funs xs (subst x v t1)) (t0 v).
Proof using.
  introv R Nx Hx M. unfolds eval_like. applys eval_app_arg1'.
  { applys R. applys eval_val_minimal. }
  { simpl. intros ? ? (->&->). applys* eval_app_fun.
    rewrite* subst_trm_funs. applys* eval_like_trm_funs. }
Qed.

(** Auxiliary lemma: evaluation rule for reducing a [val_funs] applied
    to its last argument. *)

Lemma eval_like_app_val_funs_one : forall x t1 t0 v,
  eval_like ((val_funs (x::nil) t1)) t0 ->
  eval_like (subst x v t1) (trm_app t0 v).
Proof using.
  introv R N. applys eval_app_arg1'.
  { applys R. applys eval_val_minimal. }
  { simpl. intros ? ? (->&->). applys* eval_app_fun. }
Qed.

(** Evaluation rule for the application of a [val_funs] with [n] variables
    to a list of [n] values. *)

Lemma eval_like_trm_apps_funs : forall xs t0 vs t1,
  eval_like (val_funs xs t1) t0 ->
  var_funs xs (length vs) ->
  eval_like (isubst (combine xs vs) t1) (trm_apps t0 (trms_vals vs)).
Proof using.
  introv E (R1&R2&R3). gen t1 t0 vs. induction xs; intros.
  { false*. }
  { inverts R1. destruct vs as [|v vs]; rew_list in *; tryfalse.
    rew_listx. rewrite isubst_cons. simpl.
    tests: (xs = nil).
    { destruct vs as [|]; tryfalse.
      rew_listx. rewrite isubst_nil. simpl.
      applys* eval_like_app_val_funs_one. }
    { applys* IHxs. applys* eval_like_app_val_funs_cons. } }
Qed.

(** Evaluation rule for application of a recursive n-ary function of the form
    [val_fix f (trm_funs xs t1)] to a list of values of the appropriate length. *)

Lemma eval_like_trm_apps_fixs : forall f xs vs t1 v0,
  v0 = val_fixs f xs t1 ->
  var_funs xs (length vs) ->
  ~ mem f xs ->
  xs <> nil ->
  eval_like (isubst (combine (f::xs) (v0::vs)) t1) (trm_apps v0 (trms_vals vs)).
Proof using.
  introv E F N1 N2. rew_listx. rewrite isubst_cons.
  destruct F as (F1&F2&F3).
  destruct xs as [|x xs']; tryfalse.
  destruct vs as [|v vs']; tryfalse.
  tests C: (xs' = nil).
  { destruct vs' as [|]; tryfalse.
    rew_listx. rewrite isubst_cons, isubst_nil. simpl.
    introv M. applys* eval_app_fix. }
  { rew_listx. rewrite isubst_cons. simpl. rew_listx in N1.
    rew_logic in N1. destruct N1 as (Nf&N1). inverts F1 as (Fx&F1).
    applys eval_like_trm_apps_funs.
    { introv M. applys* eval_app_fix.
      inverts M. rewrite* subst_trm_funs. rewrite* subst_trm_funs.
      applys* eval_like_trm_funs. applys* eval_val. }
    { rew_list in F2. splits*. } }
Qed.

(* ================================================================= *)
(** ** Tooling for N-ary Functions and Applications *)

(** [var_funs_exec xs n] is a computable version of [var_funs xs n]. *)

Section Var_funs_exec.
Import LibListExec.RewListExec.

Definition var_funs_exec (xs:vars) (n:nat) : bool :=
     LibListExec.noduplicates var_eq xs
  && (LibNat.beq (LibListExec.length xs) n
  && LibListExec.is_not_nil xs).

Lemma var_funs_exec_eq : forall xs (n:nat),
  var_funs_exec xs n = isTrue (var_funs xs n).
Proof using.
  intros. hint var_eq_spec.
  unfold var_funs_exec, var_funs.
  rewrite LibNat.beq_eq. rew_list_exec; auto.
  extens; rew_istrue. splits*.
Qed.

End Var_funs_exec.

(** [trms_to_vals] is the reciprocal of [trms_vals], in the sense that
    [trms_to_vals ts = Some vs] ensurse that [ts = trms_vals vs]. *)

Fixpoint trms_to_vals (ts:trms) : option vals :=
  match ts with
  | nil => Some nil
  | (trm_val v)::ts' =>
      match trms_to_vals ts' with
      | None => None
      | Some vs' => Some (v::vs')
      end
  | _ => None
  end.

Lemma trms_to_vals_spec : forall ts vs,
  trms_to_vals ts = Some vs ->
  ts = trms_vals vs.
Proof using.
  intros ts. induction ts as [|t ts']; simpl; introv E.
  { inverts E. auto. }
  { destruct t; inverts E as E. cases (trms_to_vals ts') as C; inverts E.
    rename v0 into vs'. rewrite* (IHts' vs'). }
Qed.

(** [trm_apps_of_trm t] is a tactic that takes a term [t] and returns a
    corresponding term in the form [trm_apps f ts], assuming it is possible. *)

Ltac trm_apps_of_trm t :=
  let rec aux acc t :=
    match t with
    | trm_app ?t0 ?t1 =>
        let acc' := constr:(t1::acc) in
        aux acc' t0
    | _ => constr:(trm_apps t acc)
    end in
  aux (@nil trm) t.

Lemma trm_apps_of_trm_demo : forall (f x1 x2 x3:trm) H Q,
  triple (f x1 x2 x3) H Q.
Proof using.
  intros.
  match goal with |- triple ?t _ _ =>
    let r := trm_apps_of_trm t in
    change t with r end.
Abort.

(** [prove_eq_trm_apps] applies to a goal of the form [t = trm_apps ?f ?vs],
    and solve it by instantiating [f] and [vs], assuming it is possible. *)

Ltac prove_eq_trm_apps :=
  match goal with |- ?t = trm_apps _ _ =>
    let r := trm_apps_of_trm t in
    apply (refl_equal r) end.

Lemma prove_eq_trm_apps_demo : forall (f x1 x2 x3:trm),
  (forall t ts, f x1 x2 x3 = trm_apps t ts -> (t,ts) = (t,ts) -> True) ->
  True.
Proof using. intros. eapply H. prove_eq_trm_apps. Abort.

(** [trm_funs_of_trm t] is a tactic that takes a term [t] and returns a
    corresponding term in the form [trm_funs xs t1], assuming it is possible. *)

Ltac trm_funs_of_trm t :=
  let rec aux t :=
    match t with
    | trm_fun ?x ?t1 =>
        match aux t1 with
        | trm_funs ?xs ?t0 => constr:(trm_funs (x::xs) t0)
        | ?t0 => constr:(trm_funs (x::nil) t0)
        end
    | _ => constr:(t)
    end in
  let t := eval hnf in t in
  aux t.

(** [val_funs_of_trm t] is a tactic that takes a term [t] and returns a
    corresponding term in the form [val_funs xs t1], assuming it is possible. *)

Ltac val_funs_of_trm t :=
  let t := eval hnf in t in
  match t with
  | val_fun ?x ?t1 =>
      match trm_funs_of_trm t1 with
      | trm_funs ?xs ?t0 => constr:(val_funs (x::xs) t0)
      | ?t0 => constr:(val_funs (x::nil) t0)
      end
  | _ => constr:(t)
  end.

(** [prove_eq_val_funs] applies to a goal of the form [v = val_funs ?xs ?t1]
    and solves it is possible by instantiating [xs] and [t1] *)

Ltac prove_eq_val_funs :=
  match goal with |- ?t = val_funs _ _ =>
    let r := val_funs_of_trm t in
    apply (refl_equal r) end.

Lemma prove_eq_val_funs_demo : forall (x1 x2:var) (t0:trm),
  (forall xs t, val_fun x1 (trm_fun x2 t0) = val_funs xs t -> (xs,t) = (xs,t) -> True) ->
  True.
Proof using. intros. eapply H. prove_eq_val_funs. Abort.

(** [val_fixs_of_trm t] is a tactic that takes a term [t] and returns a
    corresponding term in the form [val_fixs xs t1], if possible. *)

Ltac val_fixs_of_trm t :=
  let t := eval hnf in t in
  match t with
  | val_fix ?f ?x ?t1 =>
      match trm_funs_of_trm t1 with
      | trm_funs ?xs ?t0 => constr:(val_fixs f (x::xs) t0)
      | _ => constr:(val_fixs f (x::nil) t1)
      end
  | _ => constr:(t)
  end.

(** [prove_eq_val_fix_trm_funs] applies to a goal of the form
    [v = val_fix ?f (trm_funs ?xs ?t1)] and solves it is possible. *)

Ltac prove_eq_val_fix_trm_funs :=
  match goal with |- ?t = val_fixs _ _ _ =>
    let r := val_fixs_of_trm t in
    apply (refl_equal r) end.

Lemma prove_eq_val_fix_trm_funs_demo : forall (x1 x2:var) (t0:trm),
  (forall f xs t, val_fix f x1 (trm_fun x2 t0) = val_fixs f xs t -> (f,xs,t) = (f,xs,t) -> True) ->
  True.
Proof using. intros. eapply H. prove_eq_val_fix_trm_funs. Abort.

(* ================================================================= *)
(** ** Implementation of the Tactic [xwp] *)

Lemma xwp_lemma_funs : forall t v0 ts vs xs t1 H Q,
  t = trm_apps v0 ts ->
  v0 = val_funs xs t1 ->
  trms_to_vals ts = Some vs ->
  var_funs_exec xs (LibList.length vs) ->
  H ==> (wpgen (LibListExec.combine xs vs) t1) Q ->
  triple t H Q.
Proof using.
  introv -> E M1 F M2. rewrite var_funs_exec_eq in F. rew_bool_eq in F.
  lets HL: (proj32 F). rewrite* LibListExec.combine_eq in M2.
  lets ->: trms_to_vals_spec (rm M1).
  rewrite <- wp_equiv. xchange (rm M2). xchange wpgen_sound.
  applys wp_eval_like. applys* eval_like_trm_apps_funs.
  { subst. introv M. applys M. }
Qed.

Lemma xwp_lemma_fixs : forall t v0 ts vs f xs t1 H Q,
  t = trm_apps v0 ts ->
  v0 = val_fixs f xs t1 ->
  trms_to_vals ts = Some vs ->
  var_funs_exec xs (LibList.length vs) ->
  negb (LibListExec.mem var_eq f xs) ->
  H ==> (wpgen (LibListExec.combine (f::xs) (v0::vs)) t1) Q ->
  triple t H Q.
Proof using.
  introv -> E M1 F N1 M2. rewrite var_funs_exec_eq in F. rew_bool_eq in F.
  lets HL: (proj32 F). rewrite* LibListExec.combine_eq in M2; [|rew_list*].
  lets Nxs: (proj33 F). lets ->: trms_to_vals_spec (rm M1).
  rewrite LibListExec.mem_eq in N1; [| applys var_eq_spec ]. rew_bool_eq in N1.
  rewrite <- wp_equiv. xchange (rm M2). xchange wpgen_sound.
  applys wp_eval_like. applys* eval_like_trm_apps_fixs.
Qed.

Tactic Notation "xwp" :=
  intros;
  first [ applys xwp_lemma_funs;
          [ prove_eq_trm_apps
          | prove_eq_val_funs
          | reflexivity
          | try reflexivity
          | ]
        | applys xwp_lemma_fixs;
          [ prove_eq_trm_apps
          | prove_eq_val_fix_trm_funs
          | reflexivity
          | try reflexivity
          | try reflexivity
          | ] ];
  xwp_simpl.

(* ================================================================= *)
(** ** Specification of Array Operations *)

(** See chapter [Array]. *)

(* ================================================================= *)
(** ** Specification of Record Operations *)

(** The chapter [Struct] shows how to these specifications may be
    realized. *)

Implicit Types k : nat.

(* ----------------------------------------------------------------- *)
(** *** Representation of Records *)

(** A field name is implemented as a natural number *)

Definition field : Type := nat.

(** A record field is described as the pair of a field and a value stored
    in that field. *)

Definition hrecord_field : Type := (field * val).

(** A record consists of a list of fields. *)

Definition hrecord_fields : Type := list hrecord_field.

Implicit Types kvs : hrecord_fields.

(** Record fields syntax, e.g., [`{ head := x; tail := q }]. *)

Notation "`{ k1 := v1 }" :=
  ((k1,(v1:val))::nil)
  (at level 0, k1 at level 0, only parsing)
  : val_scope.

Notation "`{ k1 := v1 ; k2 := v2 }" :=
  ((k1,(v1:val))::(k2,(v2:val))::nil)
  (at level 0, k1, k2 at level 0, only parsing)
  : val_scope.

Notation "`{ k1 := v1 ; k2 := v2 ; k3 := v3 }" :=
  ((k1,(v1:val))::(k2,(v2:val))::(k3,(v3:val))::nil)
  (at level 0, k1, k2, k3 at level 0, only parsing)
  : val_scope.

Notation "`{ k1 := v1 }" :=
  ((k1,v1)::nil)
  (at level 0, k1 at level 0, only printing)
  : val_scope.

Notation "`{ k1 := v1 ; k2 := v2 }" :=
  ((k1,v1)::(k2,v2)::nil)
  (at level 0, k1, k2 at level 0, only printing)
  : val_scope.

Notation "`{ k1 := v1 ; k2 := v2 ; k3 := v3 }" :=
  ((k1,v1)::(k2,v2)::(k3,v3)::nil)
  (at level 0, k1, k2, k3 at level 0, only printing)
  : val_scope.

Open Scope val_scope.

(** [hrecord kvs p], written [p ~~~> kvs], describes a record at location [p],
    with fields described by the list [kvs]. *)

Parameter hrecord : forall (kvs:hrecord_fields) (p:loc), hprop.

Notation "p '~~~>' kvs" := (hrecord kvs p)
  (at level 32) : hprop_scope.

(** The heap predicate [hrecord kvs p] captures in particular the invariant
    that the location [p] is not null. *)

Parameter hrecord_not_null : forall p kvs,
  hrecord kvs p ==> hrecord kvs p \* \[p <> null].

(* ----------------------------------------------------------------- *)
(** *** Read Operation on Record Fields *)

(** [val_get_field k p], written [p'.k], reads field [k] from the record
    at location [p]. *)

Parameter val_get_field : field -> val.

Notation "t1 '`.' k" :=
  (val_get_field k t1)
  (in custom trm at level 56, k at level 0, format "t1 '`.' k" ) : trm_scope.

(** Generator of specifications of [val_get_field]. *)

Fixpoint hfields_lookup (k:field) (kvs:hrecord_fields) : option val :=
  match kvs with
  | nil => None
  | (ki,vi)::kvs' => if Nat.eq_dec k ki
                       then Some vi
                       else hfields_lookup k kvs'
  end.

(** Specification of [val_get_field] in terms of [hrecord]. *)

Parameter triple_get_field_hrecord : forall kvs p k v,
  hfields_lookup k kvs = Some v ->
  triple (val_get_field k p)
    (hrecord kvs p)
    (fun r => \[r = v] \* hrecord kvs p).

(* ----------------------------------------------------------------- *)
(** *** Write Operation on Record Fields *)

(** [val_set_field k p v], written [Set p'.k ':= v], update the contents
    of the field [k] from the record at location [p], with the value [v]. *)

Parameter val_set_field : field -> val.

Notation "t1 '`.' k ':=' t2" :=
  (val_set_field k t1 t2)
  (in custom trm at level 56,
   k at level 0, format "t1 '`.' k  ':='  t2")
   : trm_scope.

(** Generator of specifications for [val_set_field]. *)

Fixpoint hfields_update (k:field) (v:val) (kvs:hrecord_fields)
                        : option hrecord_fields :=
  match kvs with
  | nil => None
  | (ki,vi)::kvs' => if Nat.eq_dec k ki
                   then Some ((k,v)::kvs')
                   else match hfields_update k v kvs' with
                        | None => None
                        | Some LR => Some ((ki,vi)::LR)
                        end
  end.

(** Specification of [val_set_field] in terms of [hrecord]. *)

Parameter triple_set_field_hrecord : forall kvs kvs' k p v,
  hfields_update k v kvs = Some kvs' ->
  triple (val_set_field k p v)
    (hrecord kvs p)
    (fun _ => hrecord kvs' p).

(* ----------------------------------------------------------------- *)
(** *** Allocation of Records *)

(** [val_alloc_hrecord ks] allocates a record with fields [ks], storing
    uninitialized contents. *)

Parameter val_alloc_hrecord : forall (ks:list field), trm.

Parameter triple_alloc_hrecord : forall ks,
  ks = nat_seq 0 (LibListExec.length ks) ->
  triple (val_alloc_hrecord ks)
    \[]
    (funloc p => hrecord (LibListExec.map (fun k => (k,val_uninit)) ks) p).

(** An arity-generic version of the definition of allocation combined with
    initialization is beyond the scope of this course. We only include
    constructors for arity 2 and 3. *)

(** [val_new_record_2 k1 k2 v1 v2], written [`{ k1 := v1 ; k2 := v2 }],
    allocates a record with two fields and initialize the fields. *)

Parameter val_new_hrecord_2 : forall (k1:field) (k2:field), val.

Notation "`{ k1 := v1 ; k2 := v2 }" :=
  (val_new_hrecord_2 k1 k2 v1 v2)
  (in custom trm at level 65,
   k1, k2 at level 0,
   v1, v2 at level 65) : trm_scope.

Open Scope trm_scope.

Parameter triple_new_hrecord_2 : forall k1 k2 v1 v2,
  k1 = 0%nat ->
  k2 = 1%nat ->
  triple <{ `{ k1 := v1; k2 := v2 } }>
    \[]
    (funloc p => p ~~~> `{ k1 := v1 ; k2 := v2 }).

#[global] Hint Resolve val_new_hrecord_2 : triple.

(** [val_new_record_3 k1 k2 k3 v1 v2 v3], written
    [`{ k1 := v1 ; k2 := v2 ; k3 := v3 }],
    allocates a record with three fields and initialize the fields. *)

Parameter val_new_hrecord_3 : forall (k1:field) (k2:field) (k3:field), val.

Notation "`{ k1 := v1 ; k2 := v2 ; k3 := v3 }" :=
  (val_new_hrecord_3 k1 k2 k3 v1 v2 v3)
  (in custom trm at level 65,
   k1, k2, k3 at level 0,
   v1, v2, v3 at level 65) : trm_scope.

Parameter triple_new_hrecord_3 : forall k1 k2 k3 v1 v2 v3,
  k1 = 0%nat ->
  k2 = 1%nat ->
  k3 = 2%nat ->
  triple <{ `{ k1 := v1; k2 := v2; k3 := v3 } }>
    \[]
    (funloc p => p ~~~> `{ k1 := v1 ; k2 := v2 ; k3 := v3 }).

#[global] Hint Resolve val_new_hrecord_3 : triple.

(* ----------------------------------------------------------------- *)
(** *** Deallocation of Records *)

(** [val_dealloc_hrecord p], written [delete p], deallocates the record
    at location [p]. *)

Parameter val_dealloc_hrecord : val.

Notation "'delete'" :=
  (trm_val val_dealloc_hrecord)
  (in custom trm at level 0) : trm_scope.

Parameter triple_dealloc_hrecord : forall kvs p,
  triple (val_dealloc_hrecord p)
    (hrecord kvs p)
    (fun _ => \[]).

#[global] Hint Resolve triple_dealloc_hrecord : triple.

(* ----------------------------------------------------------------- *)
(** *** Extending [xapp] to Support Record Access Operations *)

(** The tactic [xapp] is refined to automatically invoke the lemmas
    [triple_get_field_hrecord] and [triple_set_field_hrecord]. *)

Parameter xapp_get_field_lemma : forall H k p Q,
  H ==> \exists kvs, (hrecord kvs p) \*
     match hfields_lookup k kvs with
     | None => \[False]
     | Some v => ((fun r => \[r = v] \* hrecord kvs p) \--* protect Q) end ->
  H ==> wpgen_app (val_get_field k p) Q.

Parameter xapp_set_field_lemma : forall H k p v Q,
  H ==> \exists kvs, (hrecord kvs p) \*
     match hfields_update k v kvs with
     | None => \[False]
     | Some kvs' => ((fun _ => hrecord kvs' p) \--* protect Q) end ->
  H ==> wpgen_app (val_set_field k p v) Q.

Ltac xapp_nosubst_for_records tt ::=
  first [ applys xapp_set_field_lemma; xsimpl; simpl; xapp_simpl
        | applys xapp_get_field_lemma; xsimpl; simpl; xapp_simpl ].

(* ----------------------------------------------------------------- *)
(** *** Extending [xsimpl] to Simplify Record Equalities *)

(** [fequals_fields] simplifies equalities between values of types
    [hrecord_fields], i.e. list of pairs of field names and values. *)

Ltac fequals_fields :=
  match goal with
  | |- nil = nil => reflexivity
  | |- cons _ _ = cons _ _ => applys args_eq_2; [ fequals | fequals_fields ]
  end.

(** At this point, the tactic [xsimpl] is refined to take into account
    simplifications of predicates of the form [p ~~~> kvs]. The idea is to find
    a matching predicate of the form [p ~~~> kvs'] on the right-hand side of
    the entailment, then to simplify the list equality [kvs = kvs']. *)

Ltac xsimpl_hook_hrecord p :=
  xsimpl_pick_st ltac:(fun H' =>
    match H' with hrecord ?kvs' p =>
      constr:(true) end);
  apply xsimpl_lr_cancel_eq;
  [ fequal; first [ reflexivity | try fequals_fields ] | ].

Ltac xsimpl_hook H ::=
  match H with
  | hsingle ?p ?v => xsimpl_hook_hsingle p
  | hrecord ?kvs ?p => xsimpl_hook_hrecord p
  end.

(* ################################################################# *)
(** * Demo Programs *)

Module DemoPrograms.
Export ProgramSyntax.

(* ----------------------------------------------------------------- *)
(** *** Definition and Verification of [incr]. *)

(** Here is an implementation of the increment function,
    written in A-normal form.

OCaml:

   let incr p =
       let n = !p in
       let m = n + 1 in
       p := m

The notation ['p] stands for [("x":var)]. It is defined in [LibSepVar.v]. *)

Definition incr : val :=
  <{ fun 'p =>
     let 'n = ! 'p in
     let 'm = 'n + 1 in
     'p := 'm }>.

(** Here is the Separation Logic triple specifying increment.
    And the proof follows. Note that the script contains explicit
    references to the specification lemmas of the functions being
    called (e.g. [triple_get] for the [get] operation). The actual
    CFML2 setup is able to automatically infer those names. *)

Lemma triple_incr : forall (p:loc) (n:int),
  triple (incr p)
    (p ~~> n)
    (fun _ => (p ~~> (n+1))).
Proof using.
  xwp. xapp. xapp. xapp. xsimpl*.
Qed.

(** We register this specification so that it may be automatically invoked
    in further examples. *)

#[global] Hint Resolve triple_incr : triple.

(** Alternative definition using variable names without quotes, obtained
    by importing the module [Vars] from [LibSepVar.v]. *)

Module Export Def_incr. Import Vars.

Definition incr' : val :=
  <{ fun p =>
       let n = ! p in
       let m = n + 1 in
       p := m }>.

End Def_incr.

Lemma triple_incr' : forall (p:loc) (n:int),
  triple (incr' p)
    (p ~~> n)
    (fun _ => (p ~~> (n+1))).
Proof using.
  xwp. xapp. xapp. xapp. xsimpl*.
Qed.

(* ----------------------------------------------------------------- *)
(** *** The Decrement Function *)

Definition decr : val :=
  <{ fun 'p =>
       let 'n = ! 'p in
       let 'm = 'n - 1 in
       'p := 'm }>.

Module Export Def_decr. Import Vars.

Definition decr : val :=
  <{ fun p =>
       let n = !p in
       let m = n - 1 in
       p := m }>.

End Def_decr.

Lemma triple_decr : forall (p:loc) (n:int),
  triple (trm_app decr p)
    (p ~~> n)
    (fun _ => p ~~> (n-1)).
Proof using.
  xwp. xapp. xapp. xapp. xsimpl*.
Qed.

#[global] Hint Resolve triple_decr : triple.

(* ----------------------------------------------------------------- *)
(** *** Definition and Verification of [mysucc]. *)

(** Another example, involving a call to [incr]. *)

Module Export Def_mysucc. Import Vars.

Definition mysucc : val :=
  <{ fun n =>
       let r = ref n in
       incr r;
       let x = !r in
       free r;
       x }>.

End Def_mysucc.

Lemma triple_mysucc : forall n,
  triple (trm_app mysucc n)
    \[]
    (fun v => \[v = n+1]).
Proof using.
  xwp. xapp. intros r. xapp. xapp. xapp. xval. xsimpl. auto.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Definition and Verification of [myrec]. *)

(** Another example, involving a function involving 3 arguments, as
    well as record operations.

OCaml:

   let myrec r n1 n2 =
      r.myfield := r.myfield + n1 + n2
*)

Definition myfield : field := 0%nat.

Module Export Def_myrec. Import Vars.

Definition myrec : val :=
  <{ fun p n1 n2 =>
       let n = (p`.myfield) in
       let m1 = n + n1 in
       let m2 = m1 + n2 in
       p`.myfield := m2 }>.

Lemma triple_myrec : forall (p:loc) (n n1 n2:int),
  triple (myrec p n1 n2)
    (p ~~~> `{ myfield := n})
    (fun _ => p ~~~> `{ myfield := (n+n1+n2) }).
Proof using.
  xwp. xapp. xapp. xapp. xapp. xsimpl.
Qed.

End Def_myrec.

(* ----------------------------------------------------------------- *)
(** *** Definition and Verification of [myfun]. *)

(** Another example involving a local function definition. *)

Module Export Def_myfun. Import Vars.

Definition myfun : val :=
  <{ fun p =>
       let f = (fun_ u => incr p) in
       f();
       f() }>.

End Def_myfun.

Lemma triple_myfun : forall (p:loc) (n:int),
  triple (myfun p)
    (p ~~> n)
    (fun _ => p ~~> (n+2)).
Proof using.
  xwp.
  xfun (fun (f:val) => forall (m:int),
    triple (f())
      (p ~~> m)
      (fun _ => p ~~> (m+1))); intros f Hf.
  { intros. applys Hf. clear Hf. xapp. xsimpl. }
  xapp. xapp.
  replace (n+1+1) with (n+2); [|math]. xsimpl.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Demo of a Function with Multiple Arguments. *)

Definition project_32 : val :=
  <{ fun 'a 'b 'c => 'b }>.

Lemma triple_project_32 : forall (a b c : int),
  triple (project_32 a b c)
    \[]
    (fun r => \[r = b]).
Proof using. xwp. xval. xsimpl*. Qed.

Definition project_32_rec : val :=
  <{ fix 'f 'a 'b 'c => if false then 'f 'b end }>.

Lemma triple_project_32_rec : forall (a b c : int),
  triple (project_32_rec a b c)
    \[]
    (fun _ => \[]).
Proof using. xwp. xif; auto_false. intros _. xval. xsimpl. Qed.

End DemoPrograms.

(* 2025-01-06 19:51 *)
