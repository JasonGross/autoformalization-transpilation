(** * Hprop: Heap Predicates *)

Set Implicit Arguments.
From SLF Require Export LibSepReference.
Import ProgramSyntax.

(* ################################################################# *)
(** * First Pass *)

(** The first two chapters have illustrated how to specify and verify programs
    using Separation Logic. The purpose of the coming chapters is to explain how
    to formally assign meaning to the tokens used in the statement of
    specifications (e.g., the star operator), formally define the notion of
    Separation Triples, and prove the reasoning rules of Separation Logic. These
    rules are exploited by the "x-tactics" used in the first two chapters. *)

(** This chapter presents the formal definitions of the key heap predicate
    operators from Separation Logic:

    - [\[]] denotes the empty heap predicate,
    - [\[P]] denotes a pure fact,
    - [p ~~> v] denotes a predicate that characterizes a singleton heap,
    - [H1 \* H2] denotes the separating conjunction,
    - [Q1 \*+ H2] denotes the separating conjunction between a
                  postcondition and a heap predicate,
    - [\exists x, H] denotes an existential quantifier. *)

(** To begin with, we define the types [heap], used to represent a memory state,
    or a piece of a memory state.

    In Separation Logic, specifications are expressed using "heap predicates",
    predicates over heaps, of type [heap->Prop]. We define [hprop] to be a
    shorthand for that type.

    By convention, throughout the course:

    - [H] denotes a heap predicate of type [hprop]; it describes a
      piece of state,
    - [Q] denotes a postcondition, of type [val->hprop]; it describes
      both a result value and a piece of state. *)

(* ================================================================= *)
(** ** Description of Memory States *)

(** To reason about imperative programs, Separation Logic relies on heap
    predicates for describing memory states. As the name suggests, a "heap
    predicate" is a predicate over heaps, i.e., over memory states. Heap
    predicates such as [p ~~> n], or [H1 \* H2] admit the type [heap -> Prop],
    where the type [heap] corresponds to a finite map used to describe the
    contents of a piece of the memory. In what follows, we give the formal
    definition of [heap] and of the type of heap predicates. *)

(** In the previous chapters, we have assumed a type [val] to range over program
    values and a type [loc] to denote memory locations. Concrete definitions
    will be provided later on, in chapter [Rules]. At this point, we are
    interested in the definition of the type [heap], used to describe the
    contents of the memory during the execution of a program. *)

(** A [heap] is a finite map from locations to values. The file [LibSepFmap.v]
    provides a self-contained formalization of finite maps. An object of type
    [fmap A B] represents a finite map binding keys of type [A] to values of
    type [B]. We define the type [heap] as a map from locations, of type [loc],
    to program values, of type [val]. Internally, [fmap A B] is implemented as a
    function of type [A -> option B], like in [Maps.v] from the LF volume. *)

Definition heap : Type := fmap loc val.

(** The file [LibSepReference] introduces the module name [Fmap] as a shorthand
    for [LibSepFmap]. The key operations associated with finite maps are:

    - [Fmap.empty] denotes the empty state,
    - [Fmap.single p v] denotes a singleton state, that is, a unique cell
      at location [p] with contents [v],
    - [Fmap.union h1 h2] denotes the union of the two states [h1] and [h2].
    - [Fmap.disjoint h1 h2] asserts that [h1] and [h2] have disjoint domains.

    Note that the union operation is commutative only when its arguments have
    disjoint domains. Throughout the course, we only consider disjoint unions,
    for which commutativity holds.

    Hereafter, to improve readability of statements in proofs, we introduce the
    notation [h1 \u h2] for heap union. *)

Notation "h1 \u h2" := (Fmap.union h1 h2) (at level 37, right associativity).

(* ================================================================= *)
(** ** Heap Predicates *)

(** In Separation Logic, the state is described using "heap predicates", of type
    [hprop]. *)

Definition hprop := heap -> Prop.

(** [H] ranges over heap predicates. *)

Implicit Type H : hprop.

(** An essential aspect of Separation Logic is that all heap predicates defined
    and used in practice are built using a few basic combinators. In other
    words, except for the definition of the combinators themselves, we will
    never define a custom heap predicate directly as a function of the state. *)

(** We next describe the most important combinators, which were used pervasively
    throughout the first two chapters. *)

(** The [hempty] predicate, usually written [\[]], characterizes an empty heap.
    *)

Definition hempty : hprop :=
  fun (h:heap) => (h = Fmap.empty).

Notation "\[]" := (hempty) (at level 0).

(** The pure fact predicate, written [\[P]], characterizes an empty state and
    moreover asserts that the proposition [P] is true. *)

Definition hpure (P:Prop) : hprop :=
  fun (h:heap) => (h = Fmap.empty) /\ P.

Notation "\[ P ]" := (hpure P) (at level 0, format "\[ P ]").

(** The singleton heap predicate, written [p ~~> v], characterizes a state with
    a single allocated cell, at location [p], storing the value [v]. *)

Definition hsingle (p:loc) (v:val) : hprop :=
  fun (h:heap) => (h = Fmap.single p v).

Notation "p '~~>' v" := (hsingle p v) (at level 32).

(** The "separating conjunction", written [H1 \* H2], characterizes a state that
    can be decomposed in two disjoint parts, one that satisfies [H1] and another
    that satisfies [H2]. *)

Definition hstar (H1 H2 : hprop) : hprop :=
  fun (h:heap) => exists h1 h2, H1 h1
                             /\ H2 h2
                             /\ Fmap.disjoint h1 h2
                             /\ h = h1 \u h2.

Notation "H1 '\*' H2" := (hstar H1 H2) (at level 41, right associativity).

(** The existential quantifier for heap predicates, written [\exists x, H]
    characterizes a heap that satisfies [H] for some [x]. The variable [x] has
    type [A], for some arbitrary [A]. *)

(** The notation [\exists x, H] stands for [hexists (fun x => H)]. The
    generalized notation [\exists x1 ... xn, H] is also available.

    The definition of [hexists] is a bit technical, and it is not essential to
    master it at this point. Additional explanations are provided near the end
    of this chapter. *)

Definition hexists (A:Type) (J:A->hprop) : hprop :=
  fun (h:heap) => exists x, J x h.

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ '  x1  ..  xn , '/ '  H ']'").

(** Universal quantification in [hprop] is also possible, but it is only useful
    for more advanced features of Separation Logic. We postpone its introduction
    to chapter [Wand]. *)

(** All the definitions above will eventually be made [Opaque], after the
    appropriate introduction and elimination lemmas have been established,
    making it no longer possible to execute, say, [unfold hstar]. Opacity is
    essential to ensure that proofs do not depend on the details of the
    definitions. *)

(* ================================================================= *)
(** ** Extensionality for Heap Predicates *)

(** To work in Separation Logic, it is extremely convenient to be able to state
    equalities between heap predicates. For example, we wish to establish the
    associativity property for the star operator in the form of an equality: *)

Parameter hstar_assoc_statement : forall H1 H2 H3,
  ((H1 \* H2) \* H3) = (H1 \* (H2 \* H3)).

(** How can we prove a goal of the form [H1 = H2] when [H1] and [H2] have type
    [hprop], that is, [heap->Prop]? Intuitively, [H] and [H'] are equal if and
    only if they characterize exactly the same set of heaps, that is, if
    [forall (h:heap), H1 h <-> H2 h].

    This reasoning principle, a specific form of extensionality property, is not
    available by default in Coq. But we can safely assume it if we extend the
    logic of Coq with a standard axiom called "predicate extensionality". *)

Axiom predicate_extensionality : forall (A:Type) (P Q:A->Prop),
  (forall x, P x <-> Q x) ->
  P = Q.

(** By specializing [P] and [Q] above to the type [hprop], we obtain exactly the
    desired extensionality principle. *)

Lemma hprop_eq : forall (H1 H2:hprop),
  (forall (h:heap), H1 h <-> H2 h) ->
  H1 = H2.
Proof using. apply predicate_extensionality. Qed.

(** More information about extensionality axioms may be found near the end of
    this chapter. *)

(* ================================================================= *)
(** ** Fundamental Properties of Operators *)

(** By exploiting extensionality, the following properties of Separation Logic
    operators can be established (they are proved further on in the chapter). *)

(** (1) The star operator is associative. *)

Parameter hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).

(** (2) The star operator is commutative. *)

Parameter hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.

(** (3) The empty heap predicate is a neutral element for the star.

    Because star is commutative, it is equivalent to state that [hempty] is a
    left or a right neutral element for [hstar]. We choose, arbitrarily, to
    state the left-neutrality property. *)

Parameter hstar_hempty_l : forall H,
  \[] \* H = H.

(** (4) Existentials can be "extruded" out of stars, that is:
    [(\exists x, J x) \* H] is equivalent to [\exists x, (J x \* H)]. *)

Parameter hstar_hexists : forall A (J:A->hprop) H,
  (\exists x, J x) \* H = \exists x, (J x \* H).

(** (5) Pure facts can be extruded out of stars. *)

Parameter hstar_hpure_l : forall P H h,
  (\[P] \* H) h = (P /\ H h).

(* ================================================================= *)
(** ** Postconditions: Type, Syntax, and Extensionality *)

(** A specification takes the form [triple t H Q], where [t] is a term, [H] is a
    precondition of type [hprop], and [Q] is a postcondition.

    For example, a read at location [p], written [!p] in OCaml, is specified as:
    [triple <{ !p }> (p ~~> v) (fun r => (p ~~> v) \* \[r = v])].

    In general, a postcondition has type [val -> hprop], which is equivalent to
    [val -> heap -> Prop]. The postcondition thereby capture the properties of
    both the output value and the output state. *)

Implicit Type Q : val -> hprop.

(** One common operation is augmenting a postcondition with a description of
    another piece of state. This operation is written as [Q \*+ H], which is
    just a convenient notation for [fun x => (Q x \* H)]. We will use this
    operator in particular in the statement of the frame rule in the next
    chapter. *)

Notation "Q \*+ H" := (fun x => hstar (Q x) H) (at level 40).

(** Intuitively, in order to prove that two postconditions [Q1] and [Q2] are
    equal, it suffices to show that the heap predicates [Q1 v] and [Q2 v] are
    equal for any value [v].

    Again, the extensionality property that we need is not built into Coq. We
    need another axiom called "functional extensionality". *)

Axiom functional_extensionality : forall A B (f g:A->B),
  (forall x, f x = g x) ->
  f = g.

(** The desired equality property for postconditions follows directly from this
    axiom. *)

Lemma qprop_eq : forall (Q1 Q2:val->hprop),
  (forall (v:val), Q1 v = Q2 v) ->
  Q1 = Q2.
Proof using. apply functional_extensionality. Qed.

(* ================================================================= *)
(** ** Introduction and Inversion Lemmas for Basic Operators *)

(** This section presents a collection of lemmas capturing the properties of the
    definitions of heap predicates. They include "introduction lemmas" for
    proving goals of the form [H h], and "inversion lemmas" for extracting
    information from hypotheses of the form [H h]. These lemmas will be
    exploited pervasively in the next chapters for establishing reasoning rules.
    *)

Implicit Types P : Prop.
Implicit Types v : val.

(** The introduction lemmas show how to prove goals of the form [H h], for
    various forms of the heap predicate [H]. *)

Lemma hempty_intro :
  \[] Fmap.empty.
Proof using.
(** The tactic [hnf], for "head normal form", unfolds the head constants. *)
  hnf. auto.
Qed.

Lemma hpure_intro : forall P,
  P ->
  \[P] Fmap.empty.
Proof using. introv M. hnf. auto. Qed.

Lemma hsingle_intro : forall p v,
  (p ~~> v) (Fmap.single p v).
Proof using. intros. hnf. auto. Qed.

Lemma hstar_intro : forall H1 H2 h1 h2,
  H1 h1 ->
  H2 h2 ->
  Fmap.disjoint h1 h2 ->
  (H1 \* H2) (h1 \u h2).
Proof using. intros. exists* h1 h2. Qed.

Lemma hexists_intro : forall A (x:A) (J:A->hprop) h,
  J x h ->
  (\exists x, J x) h.
Proof using. introv M. hnf. eauto. Qed.

(** The inversion lemmas show how to extract information from hypotheses of the
    form [H h], for various forms of the heap predicate [H].*)

Lemma hempty_inv : forall h,
  \[] h ->
  h = Fmap.empty.
Proof using. introv M. hnf in M. auto. Qed.

Lemma hpure_inv : forall P h,
  \[P] h ->
  P /\ h = Fmap.empty.
Proof using. introv M. hnf in M. autos*. Qed.

Lemma hsingle_inv: forall p v h,
  (p ~~> v) h ->
  h = Fmap.single p v.
Proof using. introv M. hnf in M. auto. Qed.

Lemma hstar_inv : forall H1 H2 h,
  (H1 \* H2) h ->
  exists h1 h2, H1 h1 /\ H2 h2 /\ Fmap.disjoint h1 h2 /\ h = h1 \u h2.
Proof using. introv M. hnf in M. eauto. Qed.

Lemma hexists_inv : forall A (J:A->hprop) h,
  (\exists x, J x) h ->
  exists x, J x h.
Proof using. introv M. hnf in M. eauto. Qed.

(* ================================================================= *)
(** ** Proofs of Fundamental Properties *)

(** The fundamental properties of Separation Logic operators were stated earlier
    in this chapter. This section presents their proofs. To avoid name
    conflicts, we wrap the new statements in a module. *)

Module HpropProofs.

(* ----------------------------------------------------------------- *)
(** *** Extraction of Existential Quantifiers *)

(** Let us prove that [(\exists x, J x) \* H] is equivalent to
    [\exists x, (J x \* H)].

    Note that, somewhat confusingly, Coq displays none of the parentheses. You
    may want to use [Set Printing Parentheses] to more easily follow through the
    proof. *)

Lemma hstar_hexists : forall A (J:A->hprop) H,
  (\exists x, J x) \* H = \exists x, (J x \* H).
Proof using.
(** First, we exploit extensionality, using [hprop_eq] or [himpl_antisym]. *)
  intros. apply hprop_eq. split.
(** Then we reveal the definitions of [==>], [hexists] and [hstar]. *)
  { intros (h1&h2&M1&M2&D&U). destruct M1 as (x&M1). exists* x h1 h2. }
  { intros (x&M). destruct M as (h1&h2&M1&M2&D&U). exists h1 h2.
    splits~. exists* x. }
Qed.

(* ----------------------------------------------------------------- *)
(** *** Neutral of Separating Conjunction *)

(** **** Exercise: 3 stars, standard, especially useful (hstar_hempty_l)

    Prove that the empty heap predicate is a neutral element for the star. You
    will need to exploit the fact that the union with an empty map is the
    identity, as captured by lemma [Fmap.union_empty_l].

  Check Fmap.union_empty_l : forall h,
    Fmap.empty \u h = h.
*)

Lemma hstar_hempty_l : forall H,
  \[] \* H = H.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Commutativity of Separating Conjunction *)

(** We next aim to prove the commutativity of the star operator, i.e., that
    [H1 \* H2] is equivalent to [H2 \* H1]. By symmetry, it suffices to prove
    the entailment in one direction, e.g., [H1 \* H2 ==> H2 \* H1]. The
    symmetry argument for any binary operator on heap predicates is captured by
    the lemma [hprop_op_comm] shown below. *)

Lemma hprop_op_comm : forall (op:hprop->hprop->hprop),
  (forall H1 H2 h, op H1 H2 h -> op H2 H1 h) ->
  (forall H1 H2, op H1 H2 = op H2 H1).
Proof using. introv M. intros. apply hprop_eq. split; apply M. Qed.

(** To prove commutativity of star, we need to exploit the fact that the union
    of two finite maps with disjoint domains commutes. This fact is captured by
    a lemma coming from the finite map library.

    Check Fmap.union_comm_of_disjoint : forall h1 h2,
      Fmap.disjoint h1 h2 ->
      h1 \u h2 = h2 \u h1.

    The commutativity result is then proved as follows. *)

Lemma hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.
Proof using.
  (* Exploit symmetry. *)
  apply hprop_op_comm.
  (* Unfold the definition of [star]. *)
  introv (h1&h2&M1&M2&D&U).
  exists h2 h1. subst. splits~.
  (* Exploit commutativity of disjoint union *)
  { rewrite Fmap.union_comm_of_disjoint; auto. }
Qed.

(* ----------------------------------------------------------------- *)
(** *** Associativity of Separating Conjunction *)

(** Associativity of star is slightly more tedious to derive. We need to exploit
    the associativity of union on finite maps, as well as lemmas about the
    disjointness of a map with the result of the union of two maps.

  Check Fmap.union_assoc : forall h1 h2 h3,
    (h1 \u h2) \u h3 = h1 \u (h2 \u h3).

  Check Fmap.disjoint_union_eq_l : forall h1 h2 h3,
      Fmap.disjoint (h2 \u h3) h1
    = (Fmap.disjoint h1 h2 /\ Fmap.disjoint h1 h3).

  Check Fmap.disjoint_union_eq_r : forall h1 h2 h3,
     Fmap.disjoint h1 (h2 \u h3)
   = (Fmap.disjoint h1 h2 /\ Fmap.disjoint h1 h3).
*)

(** **** Exercise: 1 star, standard, optional (hstar_assoc)

    Complete the right-to-left part of the proof of associativity of the star
    operator. *)

Lemma hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
Proof using.
  intros. apply hprop_eq. split.
  { intros (h'&h3&M1&M2&D&U). destruct M1 as (h1&h2&M3&M4&D'&U').
    subst h'. rewrite Fmap.disjoint_union_eq_l in D.
    exists h1 (h2 \u h3). splits.
    { apply M3. }
    { exists* h2 h3. }
    { rewrite* @Fmap.disjoint_union_eq_r. }
    { rewrite* @Fmap.union_assoc in U. } }
(* FILL IN HERE *) Admitted.

(** [] *)

(** The lemma showing that [hempty] is a right neutral can be derived from the
    fact that [hempty] is a left neutral, plus commutativity. *)

Lemma hstar_hempty_r : forall H,
  H \* \[] = H.
Proof using.
  intros. rewrite hstar_comm. rewrite hstar_hempty_l. auto.
Qed.

(** **** Exercise: 1 star, standard, especially useful (hstar_comm_assoc)

    The commutativity and associativity results combine into one result that is
    sometimes convenient to exploit in proofs. *)

Lemma hstar_comm_assoc : forall H1 H2 H3,
  H1 \* H2 \* H3 = H2 \* H1 \* H3.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Extracting Pure Facts from Separating Conjunctions *)

(** The lemma [hstar_hpure_l] stated below explains how to extract a pure fact
    from an assertion. It asserts that the proposition [(\[P] \* H) h] is
    equivalent to [P /\ H h]. This lemma will also be used pervasively in proofs
    in subsequent chapters. *)

(** **** Exercise: 4 stars, standard, especially useful (hstar_hpure_l) *)

(** Prove that a heap [h] satisfies [\[P] \* H] if and only if [P] is true and
    [h] satisfies [H]. The proof requires two lemmas on finite maps from
    [LibSepFmap.v]:

    Check Fmap.union_empty_l : forall h,
      Fmap.empty \u h = h.
    Check Fmap.disjoint_empty_l : forall h,
      Fmap.disjoint Fmap.empty h.

    Note that [auto] can apply [Fmap.disjoint_empty_l] automatically.

    Hint: begin the proof by appyling [propositional_extensionality]. *)

Lemma hstar_hpure_l : forall P H h,
  (\[P] \* H) h = (P /\ H h).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End HpropProofs.

(* ################################################################# *)
(** * More Details *)

(* ================================================================= *)
(** ** Alternative Definitions for Heap Predicates *)

(** We pause here to discuss some alternative, equivalent definitions for the
    fundamental heap predicates. We write these equivalences using equalities of
    the form [H1 = H2]. Recall that the lemma [hprop_eq] enables deriving such
    equalities by invoking predicate extensionality. *)

(** The empty heap predicate [\[]] is equivalent to the pure fact predicate
    [\[True]]. *)

Lemma hempty_eq_hpure_true :
  \[] = \[True].
Proof using.
  unfold hempty, hpure. apply hprop_eq. intros h. iff Hh.
  { auto. }
  { destruct Hh. auto. }
Qed.

(** Thus, [hempty] could be defined in terms of [hpure], as [hpure True],
    written [\[True]]. *)

Definition hempty' : hprop :=
  \[True].

(** The pure fact predicate [[\P]] is equivalent to the existential
    quantification over a proof of [P] in the empty heap, that is, to the heap
    predicate [\exists (p:P), \[]]. *)

Lemma hpure_eq_hexists_proof : forall P,
  \[P] = (\exists (p:P), \[]).
Proof using.
  unfold hempty, hpure, hexists. intros P.
  apply hprop_eq. intros h. iff Hh.
  { destruct Hh as (E&p). exists p. auto. }
  { destruct Hh as (p&E). auto. }
Qed.

(** Thus, [hpure] could be defined in terms of [hexists] and [hempty], as
    [hexists (fun (p:P) => hempty)], also written [\exists (p:P), \[]]. In fact,
    this is how [hpure] is defined in the rest of the course. *)

Definition hpure' (P:Prop) : hprop :=
  \exists (p:P), \[].

(** It is useful to minimize the number of combinators, both for elegance and to
    reduce proof effort. We cannot do without [hexists], thus there remains a
    choice between considering either [hpure] or [hempty] as primitive, and the
    other one as derived. The predicate [hempty] is simpler and appears as more
    fundamental. Hence, in the subsequent chapters, we define [hpure] in terms
    of [hexists] and [hempty], as in the definition of [hpure'] shown above. In
    other words, we assume the definition:

  Definition hpure (P:Prop) : hprop :=
    \exists (p:P), \[].
*)

(* ################################################################# *)
(** * Optional Material *)

(* ================================================================= *)
(** ** More on the Definition of the Existential Quantifier *)

(** The heap predicate [\exists (n:int), p ~~> (val_int n)] characterizes a
    state that contains a single memory cell, at address [p], storing the
    integer value [n], for "some" (unspecified) integer [n].

    Parameter (p:loc).
    Check (\exists (n:int), p ~~> (val_int n)) : hprop.

    The type of [\exists], which operates on [hprop],is very similar to that of
    [exists], which operates on [Prop]. The key difference is that a witness for
    a [\exists] can depend on the current heap, whereas a witness for a [exists]
    cannot.

    The notation [exists x, P] stands for [ex (fun x => P)], where [ex] has the
    following type:

    Check ex : forall A : Type, (A -> Prop) -> Prop.

    Likewise, [\exists x, H] stands for [hexists (fun x => H)], where [hexists]
    has the following type:

    Check hexists : forall A : Type, (A -> hprop) -> hprop.
*)

(** The notation for [\exists] is directly adapted from that of [exists], which
    supports the quantification an arbitrary number of variables, and is defined
    in [Coq.Init.Logic] as follows.

    Notation "'exists' x1 .. xn , p" := (ex (fun x1 => .. (ex (fun xn => p)) ..))
      (at level 200, x1 binder, right associativity,
       format "'[' 'exists' '/ ' x1 .. xn , '/ ' p ']'").

    Notation "'\exists' x1 .. xn , H" :=
      (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
      (at level 39, x1 binder, right associativity, H at level 50,
      format "'[' '\exists' '/ '  x1  ..  xn , '/ '  H ']'").
*)

(* ================================================================= *)
(** ** Formulation of the Extensionality Axioms *)

Module Extensionality.

(** To establish extensionality of entailment, we have used the predicate
    extensionality axiom. In fact, this axiom can be derived by combining the
    axiom of "functional extensionality" with another one called "propositional
    extensionality". The axiom of "propositional extensionality" asserts that
    two propositions that are logically equivalent, in the sense that they imply
    each other, can be considered equal. *)

Axiom propositional_extensionality : forall (P Q:Prop),
  (P <-> Q) ->
  P = Q.

(** The axiom of "functional extensionality", as we saw above, asserts that two
    functions are equal if they provide equal result for every argument. *)

Axiom functional_extensionality : forall A B (f g:A->B),
  (forall x, f x = g x) ->
  f = g.

(** **** Exercise: 1 star, standard, especially useful (predicate_extensionality_derived)

    Use [propositional_extensionality] and [functional_extensionality] to derive
    [predicate_extensionality]. *)

Lemma predicate_extensionality_derived : forall A (P Q:A->Prop),
  (forall x, P x <-> Q x) ->
  P = Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End Extensionality.

(* ================================================================= *)
(** ** Historical Notes *)

(** In this chapter, we have defined the Separation Logic operators, in
    particular the "separating conjunction" operator, as a Coq predicate. This
    formalization style is called "shallow embedding". It has been employed in
    the first mechanized formalizations of Separation Logic, in Coq by
    [Yu, Hamid, and Shao 2003] (in Bib.v), and in Isabelle/HOL by [Weber 2004] (in Bib.v).
    These two formalizations were carried out soon after the invention of
    Separation Logic, by researchers who were used to mechanizing Hoare logic and
    had spotted the potential benefit of working with the separating
    conjunction. *)

(* 2024-12-26 10:22 *)
