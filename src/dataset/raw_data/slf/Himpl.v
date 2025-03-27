(** * Himpl: Heap Entailment *)

Set Implicit Arguments.
From SLF Require LibSepReference.
From SLF Require Export Hprop.

(* ################################################################# *)
(** * First Pass *)

(** In the previous chapter, we introduced the type [hprop] and the key
    operators over this type: [\[]], [\[P]], [p ~~> v], [H1 \* H2], [Q1 \*+ H2],
    and [\exists x, H].

    In order to state the reasoning rules of Separation Logic, we need to
    introduce the "entailment relation" on heap predicates. This relation,
    written [H1 ==> H2], asserts that any heap that satisfies [H1] also
    satisfies [H2]. We also need to extend the entailment relation to
    postconditions. We write [Q1 ===> Q2] to asserts that, for any result value
    [v], the entailment [Q1 v ==> Q2 v] holds.

    Both entailment relations [==>] and [===>] appear in the statement of the
    "consequence-frame rule", exploited by the tactic [xapp] for reasoning about
    every function call. This rule explains how to derive a triple of the form
    [triple t H Q], knowing that the term [t] admits the specification
    [triple t H1 Q1]. There are two requirements: First, the precondition [H]
    must decompose into [H1], which denotes the precondition expected by the
    specification, and some remaining part, [H2]. Second, the targeted
    postcondition [Q] must be a consequence of the conjunction of [Q1], which
    denotes the postcondition asserted by the specification, and [H2], which
    again denotes the remaining part, which should not have been affected during
    the evaluation of the term [t].

    The formal statement of the frame rule is as follows.

    Lemma triple_conseq_frame : forall H2 H1 Q1 t H Q,
      triple t H1 Q1 ->
      H ==> (H1 \* H2) ->
      (Q1 \*+ H2) ===> Q ->
      triple t H Q.

    This chapter presents:

    - the formal definition of the entailment relations for heap predicates
      and for postconditions,
    - the lemmas capturing the interaction of entailment with the star operator,
      and
    - the features of the tactics [xsimpl] and [xchange], which are critically
      useful for manipulating entailments in practice.

    The tactics [xsimpl] and [xchange] were already used in the first two
    chapters. The implementation of these tactics (from [LibSepSimpl.v]) is out
    of scope for the present course, but in this chapter we explore their
    features in more depth through examples.

    This chapter exploits one additional TLC tactic for improving scripts:
    [applys] is an enhanced version of [eapply]. This tactic takes as argument a
    lemma or hypothesis, plus (optionally) a variable number of arguments, which
    are fed to the lemma on a first-match basis. In other words, [applys L x y]
    is equivalent to [eapply (L _ _ .. _ x _ _ .. _ _ y _ _ ..)] for an
    appropriate number of underscore symbols. *)

(* ================================================================= *)
(** ** Definition of Entailment *)

(** The _entailment relationship_ [H1 ==> H2] asserts that any heap [h] that
    satisfies the heap predicate [H1] also satisfies [H2]. *)

Definition himpl (H1 H2:hprop) : Prop :=
  forall (h:heap), H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55).

(** Entailment is reflexive, transitive, and antisymmetric. It thus forms an
    order relation on heap predicates. *)

Lemma himpl_refl : forall H,
  H ==> H.
Proof using. intros h. hnf. auto. Qed.

Lemma himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).
Proof using. introv M1 M2. intros h H1h. eauto. Qed.

(** **** Exercise: 1 star, standard, optional (himpl_antisym)

    Prove the antisymmetry of entailment result shown below. Hint: use
    [predicate_extensionality]. *)

Lemma himpl_antisym : forall H1 H2,
  (H1 ==> H2) ->
  (H2 ==> H1) ->
  H1 = H2.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Entailment for Postconditions *)

(** The entailment relation on postconditions, written [Q1 ===> Q2], asserts
    that the heap predicate [Q1 v] entails [Q2 v] for any value [v]. *)

Definition qimpl (Q1 Q2:val->hprop) : Prop :=
  forall (v:val), Q1 v ==> Q2 v.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2) (at level 55).

(** In other words, [Q1 ===> Q2] holds if and only if, for any value [v] and any
    heap [h], the proposition [Q1 v h] implies [Q2 v h]. *)

(** Entailment on postconditions also forms an order relation: *)

Lemma qimpl_refl : forall Q,
  Q ===> Q.
Proof using. intros Q v. apply himpl_refl. Qed.

Lemma qimpl_trans : forall Q2 Q1 Q3,
  (Q1 ===> Q2) ->
  (Q2 ===> Q3) ->
  (Q1 ===> Q3).
Proof using. introv M1 M2. intros v. eapply himpl_trans; eauto. Qed.

(** **** Exercise: 1 star, standard, optional (qimpl_antisym)

    Prove the antisymmetry of entailment on postconditions. Hint: exploit
    [functional_extensionality]. *)

Lemma qimpl_antisym : forall Q1 Q2,
  (Q1 ===> Q2) ->
  (Q2 ===> Q1) ->
  (Q1 = Q2).
Proof using.  (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Frame Rule for Entailment *)

(** A fundamental property is that the star operator is _monotone_ with respect
    to entailment, meaning that if [H1 ==> H1'] then
    [(H1 \* H2) ==> (H1' \* H2)]. In other words, an arbitrary heap predicate
    [H2] can be "framed" on both sides of an entailment.

    Viewed the other way around, if we have to prove the entailment relation
    [(H1 \* H2) ==> (H1' \* H2)], we can "cancel out" [H2] on both sides. In
    this view, the monotonicity property is a sort of frame rule for the
    entailment relation.

    Due to commutativity of star, it suffices to state only the left version of
    the monotonicity property. *)

Parameter himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).

(* ================================================================= *)
(** ** Rules for Proving Entailments *)

(** The rules for introducing and eliminating pure facts and existential
    quantifiers in entailments are essential. They are presented next. *)

(** The first rule is captured by the lemma [himpl_hstar_hpure_r]. Consider an
    entailment of the form [H ==> (\[P] \* H')]. To establish this entailment,
    we must prove that [P] is true and that [H] entails [H']. *)

(** **** Exercise: 2 stars, standard, especially useful (himpl_hstar_hpure_r).

    Prove the rule [himpl_hstar_hpure_r].

    Hint: recall from [Hprop] the lemma [hstar_hpure_l], which asserts the
    equality [(\[P] \* H) h = (P /\ H h)]. *)

Lemma himpl_hstar_hpure_r : forall (P:Prop) H H',
  P ->
  (H ==> H') ->
  H ==> (\[P] \* H').
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** Reciprocally, consider an entailment of the form [(\[P] \* H) ==> H']. To
    establish this entailment, we must prove that [H] entails [H'] under the
    assumption that [P] is true. The "extraction rule for pure facts in the left
    of an entailment" captures the property that the pure fact [\[P]] can be
    extracted into the Coq context. It is stated as follows. *)

(** **** Exercise: 2 stars, standard, especially useful (himpl_hstar_hpure_l).

    Prove the rule [himpl_hstar_hpure_l]. *)

Lemma himpl_hstar_hpure_l : forall (P:Prop) (H H':hprop),
  (P -> H ==> H') ->
  (\[P] \* H) ==> H'.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** Consider an entailment of the form [H ==> (\exists x, J x)], where [x] has
    some type [A] and [J] has type [A->hprop]. To establish this entailment, we
    must exhibit a value for [x] for which [H] entails [J x]. *)

(** **** Exercise: 2 stars, standard, optional (himpl_hexists_r).

    Prove the rule [himpl_hexists_r]. *)

Lemma himpl_hexists_r : forall A (x:A) H J,
  (H ==> J x) ->
  H ==> (\exists x, J x).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** Reciprocally, consider an entailment [(\exists x, (J x)) ==> H]. To
    establish this entailment, one has to prove that, whatever the value of [x],
    the predicate [J x] entails [H]. Indeed the former proposition asserts that
    if a heap [h] satisfies [J x] for some [x], then [h] satisfies [H'], while
    the latter asserts that if, for some [x], the predicate [h] satisfies [J x],
    then [h] satisfies [H'].

    The "extraction rule for existentials in the left of an entailment" captures
    the property that existentials can be extracted into the Coq context. It is
    stated as follows. (Observe how the existential quantifier on the left of
    the entailment becomes a universal quantifier outside of the arrow.) *)

(** **** Exercise: 2 stars, standard, especially useful (himpl_hexists_l).

    Prove the rule [himpl_hexists_l]. *)

Lemma himpl_hexists_l : forall (A:Type) (H:hprop) (J:A->hprop),
  (forall x, J x ==> H) ->
  (\exists x, J x) ==> H.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Extracting Information from Heap Predicates *)

(** We next present an example showing how entailments can be used to state
    lemmas allowing that extract information from particular heap predicates.
    Concretely, we show that, from a heap predicate of the form
    [(p ~~> v1) \* (p ~~> v2)], describing two "disjoint" cells that are both
    "at location [p]", one can extract a contradiction. Indeed, such a state
    cannot exist. *)

Lemma hstar_hsingle_same_loc : forall (p:loc) (v1 v2:val),
  (p ~~> v1) \* (p ~~> v2) ==> \[False].

(** The proof of this result exploits a result on finite maps. Essentially, the
    domain of a single singleton map that binds a location [p] to some value is
    the singleton set [\{p}], so such a singleton map cannot be disjoint from
    another singleton map that binds the same location [p].

    Check disjoint_single_single_same_inv : forall (p:loc) (v1 v2:val),
      Fmap.disjoint (Fmap.single p v1) (Fmap.single p v2) ->
      False.
*)

(** Using this lemma, we can prove [hstar_hsingle_same_loc] by unfolding the
    definition of [hstar] to reveal the contradiction on the disjointness
    assumption. *)

Proof using.
  intros. unfold hsingle. intros h (h1&h2&E1&E2&D&E). false.
  subst. eapply Fmap.disjoint_single_single_same_inv. eapply D.
Qed.

(** More generally, a heap predicate of the form [H \* H] is usually suspicious
    in Separation Logic. In the simple variant of Separation Logic that we
    consider in this course, there are only three typical situations where
    [H \* H] makes sense:

       - (1) if [H] is the empty heap predicate [\[]],
       - (2) if [H] is a pure heap predicate of the form [\[P]], or
       - (3) if [H] has the form [\exists (H0:hprop), H0], which will be written
             [\GC] in chapter [Affine]. *)

(* ----------------------------------------------------------------- *)
(** *** Rules for Naming Heaps *)

(** We write [= h] as a shorthand for [fun h' => h' = h], that is, the heap
    predicate that only accepts heaps exactly equal to [h]. *)

(** **** Exercise: 3 stars, standard, optional (hexists_named_eq)

    Prove that a heap predicate [H] is equivalent to
    [\exists h, \[H h] \* (= h))].

    Hint: In one direction, use [hexists_intro] and [hstar_hpure_l]. In the
    other, use the extraction rules [himpl_hexists_l] and [himpl_hstar_hpure_l].
    *)

Lemma hexists_named_eq : forall H,
  H = (\exists h, \[H h] \* (= h)).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** The [xsimpl] Tactic *)

(** Simplifying entailments by hand is extremely tedious. Fortunately, it can be
    automated using a specialized Coq tactic. This tactic, called [xsimpl],
    applies to an entailment and implements a 3-step process:

    - extract pure facts and existential quantifiers from the LHS;
    - instantial existential quantifiers from the RHS, using either Coq
      unification variables or user-provided hints (details are explained
      further on);
    - cancel out predicates that occur on both the LHS and RHS; certain
      Coq unification variables may be instantiated during that process.

    These steps are detailed and illustrated in the subsections that follow. *)

(** To make the [xsimpl] tactic available, we import the [LibSepReference], over
    a scope delimited by the module named [XsimplTactic]. When doing so, the
    Separation Logic operators and entailments refer to the definitions from
    [LibSepReference]. These definitions are essentially the same as those
    presented in [Hprop] and earlier in the present chapter. *)

Module XsimplTactic.
Import LibSepReference.

(* ----------------------------------------------------------------- *)
(** *** [xsimpl] Extracts Pure Facts and Quantifiers in LHS *)

(** The first feature of [xsimpl] is its ability to extract the pure facts and
    existential quantifiers from the left-hand side out into the Coq context.

    In the example below, the pure fact [n > 0] appears in the LHS. After
    calling [xsimpl], this pure fact is turned into a hypothesis, which may be
    introduced with a name into the Coq context. *)

Lemma xsimpl_demo_lhs_hpure : forall H1 H2 H3 H4 (n:int),
  H1 \* H2 \* \[n > 0] \* H3 ==> H4.
Proof using.
  intros. xsimpl. intros Hn.
Abort.

(** In case the LHS includes a contradiction, such as the pure fact [False], the
    goal gets solved immediately by [xsimpl]. *)

Lemma xsimpl_demo_lhs_hpure : forall H1 H2 H3 H4,
  H1 \* H2 \* \[False] \* H3 ==> H4.
Proof using.
  intros. xsimpl.
Qed.

(** The [xsimpl] tactic also extracts existential quantifiers from the LHS. It
    turns them into universally quantified variables outside of the entailment
    relation. *)

Lemma xsimpl_demo_lhs_hexists : forall H1 H2 H3 H4 (p:loc),
  H1 \* \exists (n:int), (p ~~> n \* H2) \* H3 ==> H4.
Proof using.
  intros. xsimpl. intros n.
Abort.

(** A single call to [xsimpl] extracts _all_ the pure facts and quantifiers from
    the LHS. *)

Lemma xsimpl_demo_lhs_several : forall H1 H2 H3 H4 (p q:loc),
  H1 \* \exists (n:int), (p ~~> n \* \[n > 0] \* H2) \* \[p <> q] \* H3 ==> H4.
Proof using.
  intros. xsimpl. intros n Hn Hp.
Abort.

(* ----------------------------------------------------------------- *)
(** *** [xsimpl] Cancels Out Heap Predicates from LHS and RHS *)

(** The second feature of [xsimpl] is its ability to cancel out similar heap
    predicates that occur on both sides of an entailment.

    In the example below, [H2] occurs on both sides, so it is canceled out by
    [xsimpl]. *)

Lemma xsimpl_demo_cancel_one : forall H1 H2 H3 H4 H5 H6 H7,
  H1 \* H2 \* H3 \* H4 ==> H5 \* H6 \* H2 \* H7.
Proof using.
  intros. xsimpl.
Abort.

(** [xsimpl] actually cancels out _all_ the heap predicates that it can spot
    appearing on both sides. In the example below, [H2], [H3], and [H4] are
    canceled out. *)

Lemma xsimpl_demo_cancel_many : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* H3 \* H4 ==> H4 \* H3 \* H5 \* H2.
Proof using.
  intros. xsimpl.
Abort.

(** If all the pieces of heap predicate get canceled out, the remaining proof
    obligation is [\[] ==> \[]]. In this case, [xsimpl] automatically solves the
    goal by invoking the reflexivity of entailment. *)

Lemma xsimpl_demo_cancel_all : forall H1 H2 H3 H4,
  H1 \* H2 \* H3 \* H4 ==> H4 \* H3 \* H1 \* H2.
Proof using.
  intros. xsimpl.
Qed.

(* ----------------------------------------------------------------- *)
(** *** [xsimpl] Instantiates Pure Facts and Quantifiers in the RHS *)

(** The third feature of [xsimpl] is its ability to extract pure facts from the
    RHS as separate subgoals and to instantiate existential quantifiers from the
    RHS.

    Let us first illustrate how it deals with pure facts. In the example below,
    the fact [n > 0] gets spawned in a separated subgoal. *)

Lemma xsimpl_demo_rhs_hpure : forall H1 H2 H3 (n:int),
  H1 ==> H2 \* \[n > 0] \* H3.
Proof using.
  intros. xsimpl.
Abort.

(** When it encounters an existential quantifier in the RHS, the [xsimpl] tactic
    introduces a unification variable denoted by a question mark, that is, an
    "evar", in Coq terminology. Here, [xsimpl] turns [\exists n, .. p ~~> n ..]
    into [.. p ~~> ?Goal ..], where [?Goal] is the evar. *)

Lemma xsimpl_demo_rhs_hexists : forall H1 H2 H3 H4 (p:loc),
  H1 ==> H2 \* \exists (n:int), (p ~~> n \* H3) \* H4.
Proof using.
  intros. xsimpl.
(** The output of the command [Show Existentials] shows [Existential 1], named
    [?Goal], of type [int]. This "evar" corresponds to the value assigned to the
    existentially quantified variable [n]. *)
Abort.

(** The "evar" often gets subsequently instantiated as a result of a
    cancellation step. For example, in the example below, [xsimpl] instantiates
    the existentially quantified variable [n] as [?Goal], then cancels out
    [p ~~> ?Goal] from the LHS against [p ~~> 3] on the right-hand-side, thereby
    unifying [?Goal] with [3]. As a result, the "evar" [?Goal] is never visible.
    *)

Lemma xsimpl_demo_rhs_hexists_unify : forall H1 H2 H3 H4 (p:loc),
  H1 \* (p ~~> 3) ==> H2 \* \exists (n:int), (p ~~> n \* H3) \* H4.
Proof using.
  intros. xsimpl.
Abort.

(** The instantiation of "evars" can only be observed if there is another
    occurrence of the same variable in the entailment. In the next example,
    which refines the previous one, observe how the assertion [n > 0] that
    appears in the LHS gets turned into the proof obligation [3 > 0]. This
    results from [n] being unified with [3] when [p ~~> n] is cancelled against
    [p ~~> 3]. *)

Lemma xsimpl_demo_rhs_hexists_unify_view : forall H1 H2 H4 (p:loc),
  H1 \* (p ~~> 3) ==> H2 \* \exists (n:int), (p ~~> n \* \[n > 0]) \* H4.
Proof using.
  intros. xsimpl.
Abort.

(** In practice, in most cases, [xsimpl] would instantiate existentials on the
    left-hand side, then discharge what remains of the entailment. Here are two
    typical examples. *)

Lemma xsimpl_demo_rhs_exists_solved_1 : forall (p:loc),
  p ~~> 3 ==>
  \exists (n:int), p ~~> n.
Proof using. xsimpl. Qed.

Lemma xsimpl_demo_rhs_exists_solved_2 : forall (p q:loc),
  p ~~> 3 \* q ~~> 3 ==>
  \exists (n:int), p ~~> n \* q ~~> n.
Proof using. xsimpl. Qed.

(** In certain situations, it may be desirable to provide an explicit value for
    instantiating an existential quantifier that occurs in the RHS. The [xsimpl]
    tactic accepts arguments, which will be used to instantiate the existentials
    (on a first-match basis). The syntax is [xsimpl v1 .. vn]. *)

Lemma xsimpl_demo_rhs_hints : forall H1 (p q:loc),
  H1 ==> \exists (n m:int), (p ~~> n \* q ~~> m).
Proof using.
  intros. xsimpl 8 9.
Abort.

(** If two existential quantifiers quantify variables of the same type, it is
    possible to provide a value for only the second quantifier by passing as
    first argument to [xsimpl] the special value [__]. The following example
    shows how, on LHS of the form [\exists n m, ...], the tactic [xsimpl __ 9]
    instantiates [m] with [9] while leaving [n] as an unresolved evar. *)

Lemma xsimpl_demo_rhs_hints_evar : forall H1 (p q:loc),
  H1 ==> \exists (n m:int), (p ~~> n \* q ~~> m).
Proof using.
  intros. xsimpl __ 9.
Abort.

(* ----------------------------------------------------------------- *)
(** *** [xsimpl] on Entailments Between Postconditions *)

(** The tactic [xsimpl] also applies on goals of the form [Q1 ===> Q2].

    For such goals, it unfolds the definition of [===>] to reveal an entailment
    of the form [==>], then invokes the [xsimpl] tactic. *)

Lemma qimpl_example_1 : forall (Q1 Q2:val->hprop) (H2 H3:hprop),
  Q1 \*+ H2 ===> Q2 \*+ H2 \*+ H3.
Proof using. intros. xsimpl. intros r. Abort.

(* ----------------------------------------------------------------- *)
(** *** Example: Entailment Proofs using [xpull] and [xsimpl] *)

(** The [xpull] tactic is a restricted version of [xsimpl]: it operates on the
    left-hand side of the entailment, but leaves the right-hand side untouched.
    In other words, [xpull] performs only the first half of the work that
    [xsimpl] would do. *)

Lemma xpull_example_1 : forall (p:loc),
  \exists (n:int), p ~~> n ==>
  \exists (m:int), p ~~> (m + 1).
Proof using.
  intros. xpull.
Abort.

Lemma xpull_example_2 : forall (H:hprop),
  \[False] ==> H.
Proof using. xpull. Qed.

(** The next example illustrates an interesting situation where [xpull] is
    required because a plain call to [xsimpl] leads to an awkward goal. This
    examples involves a nontrivial instantiation of an existential quantifier on
    the right-hand side of the entailment. However, we cannot provide an
    explicit hint to [xsimpl] before extracting an existential quantifier that
    appears on the left-hand side of the entailment. Here is the example. *)

Lemma xpull_example_3 : forall (p:loc),
  (\exists (n:int), p ~~> n) ==>
  (\exists (m:int), p ~~> (m + 1)).
Proof using.
  intros.
  (* xsimpl.

    Invoking [xsimpl] here leaves the goal [forall x, x = ?Goal + 1]. This
    statement is technically provable, because [?Goal] can be instantiated with
    [x - 1]. Yet, discharging such a proof obligation, which features a Coq
    meta-variable [?Goal] that depends on a bound variable [x] is rather awkward
    and impractical.

    The proper route to solving this kind of entailment is to first extract the
    [\exists n] into the context, then use [xsimpl (n-1)] to provide as hint to
    [xsimpl] that [m] should be instantiated with [n-1]. *)
  xpull. intros n. xsimpl (n-1). math.
Qed.

(* ================================================================= *)
(** ** The [xchange] Tactic *)

(** The tactic [xchange] is to entailment what [rewrite] is to equality.

    Assume an entailment goal of the form [H1 \* H2 \* H3 ==> H4]. Assume an
    entailment assumption [M], say [H2 ==> H2']. Then [xchange M] turns the goal
    into [H1 \* H2' \* H3 ==> H4], effectively replacing [H2] with [H2']. *)

Lemma xchange_demo_base : forall H1 H2 H2' H3 H4,
  H2 ==> H2' ->
  H1 \* H2 \* H3 ==> H4.
Proof using.
  introv M. xchange M.
  (* Note that freshly produced items appear to the front *)
Abort.

(** The [xchange] tactic can also take an equality as an argument; [xchange M]
    exploits the left-to-right direction of an equality [M], whereas
    [xchange <- M] exploits the right-to-left direction. *)

Lemma xchange_demo_eq : forall H1 H2 H3 H4 H5,
  H1 \* H3 = H5 ->
  H1 \* H2 \* H3 ==> H4.
Proof using.
  introv M. xchange M.
  xchange <- M.
Abort.

(** The tactic [xchange M] will accept a lemma or hypothesis [M] with universal
    quantifiers, as long as its conclusion is an equality or an entailment. In
    such case, [xchange M] instantiates [M] before attemting to perform a
    replacement. *)

Lemma xchange_demo_inst : forall H1 (J J':int->hprop) H3 H4,
  (forall n, J n = J' (n+1)) ->
  H1 \* J 3 \* H3 ==> H4.
Proof using.
  introv M. xchange M.
Abort.

(* ================================================================= *)
(** ** Identifying True and False Entailments *)

(** Quiz: For each entailment below, indicate (without a Coq proof) whether it
    is true or false. Solutions appear further on. *)

Module EntailmentQuiz.

Implicit Types p q : loc.
Implicit Types n m : int.

Parameter case_study_1 : forall p q,
      p ~~> 3 \* q ~~> 4
  ==> q ~~> 4 \* p ~~> 3.

Parameter case_study_2 : forall p q,
      p ~~> 3
  ==> q ~~> 4 \* p ~~> 3.

Parameter case_study_3 : forall p q,
      q ~~> 4 \* p ~~> 3
  ==> p ~~> 3.

Parameter case_study_4 : forall p q,
      \[False] \* p ~~> 3
  ==> p ~~> 4 \* q ~~> 4.

Parameter case_study_5 : forall p q,
      p ~~> 3 \* q ~~> 4
  ==> \[False].

Parameter case_study_6 : forall p,
      p ~~> 3 \* p ~~> 4
  ==> \[False].

Parameter case_study_7 : forall p,
      p ~~> 3 \* p ~~> 3
  ==> \[False].

Parameter case_study_8 : forall p,
      p ~~> 3
  ==> \exists n, p ~~> n.

Parameter case_study_9 : forall p,
      exists n, p ~~> n
  ==> p ~~> 3.

Parameter case_study_10 : forall p,
      \exists n, p ~~> n \* \[n > 0]
  ==> \exists n, \[n > 1] \* p ~~> (n-1).

Parameter case_study_11 : forall p q,
      p ~~> 3 \* q ~~> 3
  ==> \exists n, p ~~> n \* q ~~> n.

Parameter case_study_12 : forall p n,
      p ~~> n \* \[n > 0] \* \[n < 0]
  ==> p ~~> n \* p ~~> n.

End EntailmentQuiz.

Module EntailmentQuizAnswers.

(** The answers to the quiz are as follows.

    1. True, by commutativity.

    2. False, because one cell does not entail two cells.

    3. False, because two cells do not entail one cell.

    4. True, because \[False] entails anything.

    5. False, because a satisfiable heap predicate does not entail \[False].

    6. True, because a cell cannot be starred with itself.

    7. True, because a cell cannot be starred with itself.

    8. True, by instantiating [n] with [3].

    9. False, because [n] could be something else than [3].

    10. True, by instantiating [n] in RHS with [n+1] for the [n] of the LHS.

    11. True, by instantiating [n] with [3].

    12. True, because it is equivalent to [\[False] ==> \[False]].

    Proofs for the true results appear below, using the [xsimpl] tactic. *)

Implicit Types p q : loc.
Implicit Types n m : int.

Lemma case_study_1 : forall p q,
      p ~~> 3 \* q ~~> 4
  ==> q ~~> 4 \* p ~~> 3.
Proof using. xsimpl. Qed.

Lemma case_study_4 : forall p q,
      \[False] \* p ~~> 3
  ==> p ~~> 4 \* q ~~> 4.
Proof using. xsimpl. Qed.

Lemma case_study_6 : forall p,
      p ~~> 3 \* p ~~> 4
  ==> \[False].
Proof using. intros. xchange (hstar_hsingle_same_loc p). Qed.

Lemma case_study_7 : forall p,
      p ~~> 3 \* p ~~> 3
  ==> \[False].
Proof using. intros. xchange (hstar_hsingle_same_loc p). Qed.

Lemma case_study_8 : forall p,
      p ~~> 3
  ==> \exists n, p ~~> n.
Proof using. xsimpl. Qed.

Lemma case_study_10 : forall p,
      \exists n, p ~~> n \* \[n > 0]
  ==> \exists n, \[n > 1] \* p ~~> (n-1).
Proof using.
  intros. xpull. intros n Hn. xsimpl (n+1).
  math. math.
Qed.

Lemma case_study_11 : forall p q,
      p ~~> 3 \* q ~~> 3
  ==> \exists n, p ~~> n \* q ~~> n.
Proof using. xsimpl. Qed.

Lemma case_study_12 : forall p n,
  p ~~> n \* \[n > 0] \* \[n < 0] ==> p ~~> n \* p ~~> n.
Proof using. intros. xsimpl. intros Hn1 Hn2. false. math. Qed.

End EntailmentQuizAnswers.

(* ################################################################# *)
(** * More Details *)

(* ================================================================= *)
(** ** Proving Entailments by Hand *)

Module EntailmentProofs.
Implicit Types p : loc.
Implicit Types n : int.

(** Proving an entailment by hand is generally a tedious task. This is why most
    frameworks based on Separation Logic include an automated tactic for
    simplifying entailments. In this course, the relevant tactic is named
    [xsimpl]. In order to fully appreciate what a simplification tactic provides
    and better understand how it works internally, it is very useful to complete
    a few entailment proofs by hand. *)

(** **** Exercise: 3 stars, standard, optional (himpl_example_1)

    Prove the example entailment below. Hint: exploit [hstar_comm],
    [hstar_assoc], or [hstar_comm_assoc] which combines the two, and exploit
    [himpl_frame_l] or [himpl_frame_r] to cancel out matching pieces. *)

Lemma himpl_example_1 : forall p1 p2 p3 p4,
      p1 ~~> 6 \* p2 ~~> 7 \* p3 ~~> 8 \* p4 ~~> 9
  ==> p4 ~~> 9 \* p3 ~~> 8 \* p2 ~~> 7 \* p1 ~~> 6.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (himpl_example_2)

    Prove the example entailment below. Hint: use [himpl_hstar_hpure_l] to
    extract pure facts, once they appear at the head of the left-hand side of
    the entailment. For arithmetic inequalities, use the [math] tactic. *)

Lemma himpl_example_2 : forall p1 p2 p3 n,
      p1 ~~> 6 \* \[n > 0] \* p2 ~~> 7 \* \[n < 0]
  ==> p3 ~~> 8.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (himpl_example_3)

    Prove the example entailment below. Hint: use [himpl_hexists_r],
    [himpl_hexists_l], [himpl_hstar_hpure_l] and/or [himpl_hstar_hpure_r] to
    deal with pure facts and quantifiers. You may find the TLC tactic
    [math_rewrite (n+1-1 = n)] helpful here. *)

Lemma himpl_example_3 : forall p,
      \exists n, p ~~> n \* \[n > 0]
  ==> \exists n, \[n > 1] \* p ~~> (n-1).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End EntailmentProofs.

(* ================================================================= *)
(** ** Inside the [xchange] Tactic *)

(** How does the [xchange] tactic work? Consider a goal of the form [H ==> H']
    and assume [xchange] is invoked with an hypothesis of type [H1 ==> H1'] as
    argument. It attempts to decompose [H] as the star of [H1] and the rest of
    [H], call it [H2]. If it succeeds, then the goal [H ==> H'] can be rewritten
    as [H1 \* H2 ==> H']. To exploit the hypothesis [H1 ==> H1'], the tactic
    should replace the goal with the entailment [H1' \* H2 ==> H']. The lemma
    below mimics this piece of reasoning. *)

(** **** Exercise: 2 stars, standard, especially useful (xchange_lemma)

    Prove the following lemma without using [xchange]. *)

Lemma xchange_lemma : forall H1 H1' H H' H2,
  H1 ==> H1' ->
  H ==> H1 \* H2 ->
  H1' \* H2 ==> H' ->
  H ==> H'.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End XsimplTactic.

(* ################################################################# *)
(** * Optional Material *)

(* ================================================================= *)
(** ** Proofs of Rules for Entailment *)

(** We next show the details of the proofs establishing some of the fundamental
    properties of Separation Logic operators. All these results must be proved
    without help of [xsimpl], because the implementation of [xsimpl] itself
    depends on these properties.

    We begin with the frame property, which is the simplest to prove. *)

Module EntailmentRulesProofs.

(** **** Exercise: 1 star, standard, especially useful (himpl_frame_l)

    Prove the frame property for entailment. Hint: unfold the definition of
    [hstar]. *)

Lemma himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** The lemma [himpl_frame_l] admits two useful corollaries, presented next. *)

(** **** Exercise: 1 star, standard, especially useful (himpl_frame_r)

    Prove [himpl_frame_r], which is the symmetric of [himpl_frame_l]. *)

Lemma himpl_frame_r : forall H1 H2 H2',
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1 \* H2').
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, standard, especially useful (himpl_frame_lr)

    The monotonicity property of the star operator w.r.t. entailment can also be
    stated in a symmetric fashion, as shown next. Prove this result. Hint:
    exploit the transitivity of entailment ([himpl_trans]) and the asymmetric
    monotonicity results from the two prior exercises. *)

Lemma himpl_frame_lr : forall H1 H1' H2 H2',
  H1 ==> H1' ->
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1' \* H2').
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End EntailmentRulesProofs.

(* ================================================================= *)
(** ** Historical Notes *)

(* 2025-01-06 19:51 *)
