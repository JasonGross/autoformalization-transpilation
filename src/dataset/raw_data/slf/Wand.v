(** * Wand: The Magic Wand and Other Operators *)

Set Implicit Arguments.
From SLF Require Import LibSepReference.
From SLF Require Repr.
Close Scope trm_scope.

Implicit Types h : heap.
Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.

(* ################################################################# *)
(** * First Pass *)

(** This chapter presents some additional Separation Logic operators:

    - the disjunction, written [hor H1 H2],
    - the non-separating conjunction, written [hand H1 H2],
    - the "forall", named [hforall] and written [\forall x, H],
    - the "magic wand", named [hwand] and written [H1 \-* H2],
    - the "magic wand for postconditions", named [qwand] and written
      [Q1 \--* Q2].

    The magic wand operator has multiple uses:

    - it is key to formulating the "ramified frame rule", a more practical rule
      for exploiting the frame and consequence properties,
    - it will be used in the chapter [WPgen] to define a
      weakest-precondition generator, and
    - it can be useful to state the specifications for certain data structures.

    This chapter is organized as follows:

    - definition and properties of [hand], [hor], and [hforall],
    - definition and properties of the magic wand operator,
    - generalization of the magic wand to postconditions,
    - extension of the [xsimpl] tactic to handle the magic wand,
    - statement and benefits of the ramified frame rule.

    The "optional material" presents several equivalent definitions for magic
    wand. *)

(* ================================================================= *)
(** ** Definition of the Operator [hforall] *)

Module Hforall.

(** The heap predicate [\forall x, H] holds of a heap [h] that, for any possible
    value of [x], satisfies [H]. It may be puzzling at first what could possibly
    be the use case for such a universal quantification, but we will see several
    examples through this chapter -- in particular the encoding of the
    non-separating conjunction ([hand]) and of the magic wand on postconditions
    ([qwand]).

    The predicate [\forall x, H] stands for [hforall (fun x => H)], where the
    definition of [hforall] follows the same pattern as [hexists]. *)

Definition hforall (A : Type) (J : A -> hprop) : hprop :=
  fun h => forall x, J x h.

Notation "'\forall' x1 .. xn , H" :=
  (hforall (fun x1 => .. (hforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\forall' '/ '  x1  ..  xn , '/ '  H ']'").

(** To follow the rest of this chapter, it suffices to have in mind the
    introduction and elimination rules for [hforall]. *)

Lemma hforall_intro : forall A (J:A->hprop) h,
  (forall x, J x h) ->
  (hforall J) h.
Proof using. introv M. applys* M. Qed.

Lemma hforall_inv : forall A (J:A->hprop) h,
  (hforall J) h ->
  forall x, J x h.
Proof using. introv M. applys* M. Qed.

(** The introduction rule in an entailment for [\forall] appears below. To
    prove that a heap satisfies [\forall x, J x], we must show that, for any
    [x], this heap satisfies [J x]. *)

Lemma himpl_hforall_r : forall A (J:A->hprop) H,
  (forall x, H ==> J x) ->
  H ==> (\forall x, J x).
Proof using. introv M. intros h K x. apply~ M. Qed.

(** The elimination rule in an entailment for [\forall] appears below. Assuming
    a heap satisfies [\forall x, J x], we can derive that the same heap
    satisfies [J v] for any desired value [v]. *)

Lemma hforall_specialize : forall A (v:A) (J:A->hprop),
  (\forall x, J x) ==> (J v).
Proof using. intros. intros h K. apply* K. Qed.

(** The lemma [hforall_specialize] can equivalently be formulated in the
    following way, which makes it easier to apply in some cases. *)

Lemma himpl_hforall_l : forall A (v:A) (J:A->hprop) H,
  J v ==> H ->
  (\forall x, J x) ==> H.
Proof using. introv M. applys himpl_trans_r M. applys hforall_specialize. Qed.

(** Universal quantifers that appear in the precondition of a triple may be
    specialized like universal quantifiers appearing on the left-hand side of an
    entailment. *)

Lemma triple_hforall : forall A (v:A) t (J:A->hprop) Q,
  triple t (J v) Q ->
  triple t (\forall x, J x) Q.
Proof.
  introv M. applys triple_conseq M.
  { applys hforall_specialize. }
  { applys qimpl_refl. }
Qed.

End Hforall.

(* ================================================================= *)
(** ** Definition of the Operator [hor] *)

Module Hor.

(** The heap predicate [hor H1 H2] describes a heap that satisfies [H1] or
    satifies [H2] (or possibly both). In other words, the heap predicate
    [hor H1 H2] lifts the disjunction operator [P1 \/ P2] from [Prop] to
    [hprop].

    The disjunction operator does not appear to be critically useful in
    practice, because it can be encoded using Coq's conditional construct, or
    using pattern matching. Nevertheless, there are situations where it proves
    handy.

    The heap disjunction predicate admits a direct definition as a function over
    heaps, written [hor']. *)

Definition hor' (H1 H2 : hprop) : hprop :=
  fun h => H1 h \/ H2 h.

(** An alternative definition leverages the [\exists] quantifier. The
    definition, shown below, reads as follows: "there exists an unspecified
    boolean value [b] such that if [b] is true then [H1] holds, else if [b] is
    false then [H2] holds".

    The benefit of this definition is that its properties can be established
    without manipulating heaps explicitly. *)

Definition hor (H1 H2 : hprop) : hprop :=
  \exists (b:bool), if b then H1 else H2.

(** **** Exercise: 3 stars, standard, optional (hor_eq_hor')

    Prove the equivalence of the definitions [hor] and [hor']. *)

Lemma hor_eq_hor' :
  hor = hor'.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** The two introduction rules for [hor] assert that if [H1] holds, then
    [hor H1 H2] holds; and, symmetrically, if [H2] holds, then [hor H1 H2]
    holds. *)

Lemma himpl_hor_r_l : forall H1 H2,
  H1 ==> hor H1 H2.
Proof using. intros. unfolds hor. exists* true. Qed.

Lemma himpl_hor_r_r : forall H1 H2,
  H2 ==> hor H1 H2.
Proof using. intros. unfolds hor. exists* false. Qed.

(** In practice, these rules are easier to exploit when combined with a
    transitivity step. *)

Lemma himpl_hor_r_l_trans : forall H1 H2 H3,
  H3 ==> H1 ->
  H3 ==> hor H1 H2.
Proof using. introv W. applys himpl_trans W. applys himpl_hor_r_l. Qed.

Lemma himpl_hor_r_r_trans : forall H1 H2 H3,
  H3 ==> H2 ->
  H3 ==> hor H1 H2.
Proof using. introv W. applys himpl_trans W. applys himpl_hor_r_r. Qed.

(** The elimination rule asserts that, if [hor H1 H2] holds, then we can perform
    a case analysis on whether it is [H1] or [H2] that holds. Concretely, to
    show that [hor H1 H2] entails a heap predicate [H3], we must show both that
    [H1] entails [H3] and that [H2] entails [H3]. *)

Lemma himpl_hor_l : forall H1 H2 H3,
  H1 ==> H3 ->
  H2 ==> H3 ->
  hor H1 H2 ==> H3.
Proof using.
  introv M1 M2. unfolds hor. applys himpl_hexists_l. intros b. case_if*.
Qed.

(** The operator [hor] is commutative. To establish this property, it is useful
    to exploit the following lemma, called [if_neg], for swapping the two
    branches of a conditional by negating its boolean condition. *)

Lemma if_neg : forall (b:bool) A (X Y:A),
  (if b then X else Y) = (if neg b then Y else X).
Proof using. intros. case_if*. Qed.

(** **** Exercise: 2 stars, standard, especially useful (hor_comm)

    Prove that [hor] is a symmetric operator. Hint: exploit [hprop_op_comm] and
    [if_neg] (from chapter [Himpl]). *)

Lemma hor_comm : forall H1 H2,
  hor H1 H2 = hor H2 H1.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

Module HorExample.
Import Repr.
Implicit Types q : loc.

(** **** Exercise: 4 stars, standard, especially useful (hor_comm)

    Prove that the representation predicate [MList] introduced in chapter
    [Repr] can be equivalently characterized using the predicate [hor], as
    shown below. Hint: to prove this equivalence, do not attempt a proof by
    induction, and do not attempt to unfold [MList]. Instead, work using the
    equalities [MList_nil] and [MList_cons]. You may want to begin the proof by
    applying [himpl_antisym] and calling [destruct] on [L]. *)

Lemma MList_using_hor : forall L p,
  MList L p =
     hor (\[L = nil /\ p = null])
         (\exists x q L', \[L = x::L']
                       \* (p ~~~>`{ head := x; tail := q})
                       \* (MList L' q)).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End HorExample.
End Hor.

(* ================================================================= *)
(** ** Definition of the Operator [hand] *)

Module Hand.
Import Hforall Hor.

(** The heap predicate [hand H1 H2] describes a single heap that satisfies [H1]
    and at the same time satifies [H2]. In other words, the heap predicate
    [hand H1 H2] lifts the disjunction operator [P1 /\ P2] from [Prop] to
    [hprop]. The heap predicate [hand] admits a direct definition as a function
    over heaps. *)

Definition hand' (H1 H2 : hprop) : hprop :=
  fun h => H1 h /\ H2 h.

(** An alternative definition leverages the [\forall] quantifier. The definition
    reads as follows: "for any boolean value [b], if [b] is true then [H1]
    should hold, and if [b] is false then [H2] should hold". *)

Definition hand (H1 H2 : hprop) : hprop :=
  \forall (b:bool), if b then H1 else H2.

(** **** Exercise: 2 stars, standard, especially useful (hand_eq_hand')

    Prove the equivalence of the definitions [hand] and [hand']. Use functional
    extensionality to get started. *)

Lemma hand_eq_hand' :
  hand = hand'.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** The introduction and elimination rules for [hand] are as follows.

    - If "[H1] and [H2]" holds, then in particular [H1] holds.
    - Symmetrically, if "[H1] and [H2]" holds, then in particular [H2] holds.
    - Reciprocally, to prove that a heap predicate [H3] entails
      "[H1] and [H2]", we must prove that [H3] entails [H1], and that
      [H3] satisfies [H2].
*)

Lemma himpl_hand_l_r : forall H1 H2,
  hand H1 H2 ==> H1.
Proof using. intros. unfolds hand. applys* himpl_hforall_l true. Qed.

Lemma himpl_hand_l_l : forall H1 H2,
  hand H1 H2 ==> H2.
Proof using. intros. unfolds hand. applys* himpl_hforall_l false. Qed.

Lemma himpl_hand_r : forall H1 H2 H3,
  H3 ==> H1 ->
  H3 ==> H2 ->
  H3 ==> hand H1 H2.
Proof using. introv M1 M2 Hh. intros b. case_if*. Qed.

(** **** Exercise: 1 star, standard, especially useful (hand_comm)

    Prove that [hand] is symmetric. Hint: use [hprop_op_comm] and
    [rewrite if_neg], or a case analysis on the boolean value coming from
    [hand]. *)

Lemma hand_comm : forall H1 H2,
  hand H1 H2 = hand H2 H1.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End Hand.

(* ================================================================= *)
(** ** Definition of the Magic Wand Operator: [hwand] *)

Module Hwand.

(* ----------------------------------------------------------------- *)
(** *** Definition of [hwand] *)

(** The magic wand operation [H1 \-* H2], pronounced "H1 wand H2", defines a
    heap predicate such that, if we extend it with [H1], we obtain [H2].
    Formally, the following entailment holds:

      H1 \* (H1 \-* H2) ==> H2.

    Intuitively, if we think of the star [H1 \* H2] as a sort of addition,
    [H1 + H2], then we can think of [H1 \-* H2] as the subtraction [-H1 + H2].
    The entailment above intuitively captures the idea that [(-H1 + H2) + H1]
    simplifies to [H2].

    Note, however, that the operation [H1 \-* H2] only makes sense if [H1]
    describes a piece of heap that "can" be subtracted from [H2]. Otherwise, the
    predicate [H1 \-* H2] characterizes a heap that cannot possibly exist.
    Informally speaking, [H1] must somehow be a subset of [H2] for the
    subtraction [-H1 + H2] to make sense.

    Another possible analogy is that of logical operators. If [P1] and [P2] were
    propositions (of type [Prop]), then [P1 \* P2] would mean [P1 /\ P2] and
    [P1 \-* P2] would mean [P1 -> P2]. The entailment [P1 \* (P1 \-* P2) ==> P2]
    then corresponds to the tautology [(P1 /\ (P1 -> P2)) -> P2].

    Technically, [H1 \-* H2] holds of a heap [h] if, for any heap [h'] disjoint
    from [h] and satisfying [H1], the union of [h] and [h'] satisfies [H2]. The
    operator [hwand], which implements the notation [H1 \-* H2], may thus be
    defined as follows. *)

Definition hwand' (H1 H2:hprop) : hprop :=
  fun h => forall h', Fmap.disjoint h h' -> H1 h' -> H2 (h \u h').

(** The definition above is perfectly fine, however it is more practical to use
    an alternative, equivalent definition of [hwand], expressed in terms of
    previously introduced Separation Logic operators. Doing so enables us to
    establish all the properties of the magic wand by exploiting the tactic
    [xsimpl], thereby conducting all the reasoning at the level of [hprop],
    rather than having to work with concrete heaps.

    The alternative definition asserts that [H1 \-* H2] corresponds to some heap
    predicate, called [H0], such that [H0] starred with [H1] yields [H2]. In
    other words, [H0] is such that [(H1 \* H0) ==> H2]. In the definition below,
    observe how [H0] is existentially quantified. *)

Definition hwand (H1 H2:hprop) : hprop :=
  \exists H0, H0 \* \[ H1 \* H0 ==> H2 ].

Notation "H1 \-* H2" := (hwand H1 H2) (at level 43, right associativity).

(* ----------------------------------------------------------------- *)
(** *** Characteristic Equivalence for [hwand] *)

(** The magic wand is not easy to make sense of at first. Reading its
    introduction and elimination rules may help further appreciate its meaning.

    The operator [H1 \-* H2] satisfies the following equivalence. Informally
    speaking, think of [H0 = -H1+H2] and [H1+H0 = H2] being equivalent claims.
    *)

Lemma hwand_equiv : forall H0 H1 H2,
  (H0 ==> H1 \-* H2) <-> (H1 \* H0 ==> H2).
Proof using.
  unfold hwand. iff M.
  { xchange M. intros H N. xchange N. }
  { xsimpl H0. xchange M. }
Qed.

(** Indeed, we will see below that the magic wand operator is _uniquely defined_
    by the equivalence [(H0 ==> H1 \-* H2) <-> (H1 \* H0 ==> H2)]. In other
    words, any operator that satisfies the above equivalence is provably equal
    to [hwand]. *)

(** The right-to-left direction of the equivalence is an introduction rule: it
    tells what needs to be proved for constructing a magic wand [H1 \-* H2] from
    a state [H0].

    To establish that [H0] entails [H1 \-* H2], we have to show that the
    conjunction of [H0] and [H1] yields [H2]. *)

Lemma himpl_hwand_r : forall H0 H1 H2,
  (H1 \* H0) ==> H2 ->
  H0 ==> (H1 \-* H2).
Proof using. introv M. applys hwand_equiv. applys M. Qed.

(** The left-to-right direction of the equivalence is an elimination rule: it
    tells what can be deduced from an entailment [H0 ==> (H1 \-* H2)] -- namely,
    if [H0] is starred with [H1], then [H2] can be recovered. *)

Lemma himpl_hwand_r_inv : forall H0 H1 H2,
  H0 ==> (H1 \-* H2) ->
  (H1 \* H0) ==> H2.
Proof using. introv M. applys hwand_equiv. applys M. Qed.

(** This elimination rule can be equivalently reformulated in the following
    handy form: [H1 \-* H2], when starred with [H1], yields [H2]. *)

Lemma hwand_cancel : forall H1 H2,
  H1 \* (H1 \-* H2) ==> H2.
Proof using. intros. applys himpl_hwand_r_inv. applys himpl_refl. Qed.

Arguments hwand_cancel : clear implicits.

(* ----------------------------------------------------------------- *)
(** *** Further Properties of [hwand] *)

(** We next present the most important properties of the magic wand operator.
    Here, the tactic [xsimpl] is available only in a restricted form that does
    not support magic wand. (The full [xsimpl] tactic would trivially solve many
    of these lemmas, but using it here would be cheating because the
    implementation of [xsimpl] itself relies on several of these lemmas.) *)

(** The operator [H1 \-* H2] is contravariant in [H1] and covariant in [H2],
    like the implication operator [->]. *)

Lemma hwand_himpl : forall H1 H1' H2 H2',
  H1' ==> H1 ->
  H2 ==> H2' ->
  (H1 \-* H2) ==> (H1' \-* H2').
Proof using.
  introv M1 M2. applys himpl_hwand_r. xchange M1.
  xchange (hwand_cancel H1 H2). applys M2.
Qed.

(** The predicates [H1 \-* H2] and [H2 \-* H3] together simplify to [H1 \-* H3].
    This is reminiscent of the arithmetic identity
    [(-H1 + H2) + (-H2 + H3) = (-H1 + H3)] (and to the transitivity of ordinary
    implication). *)

Lemma hwand_trans_elim : forall H1 H2 H3,
  (H1 \-* H2) \* (H2 \-* H3) ==> (H1 \-* H3).
Proof using.
  intros. applys himpl_hwand_r. xchange (hwand_cancel H1 H2).
Qed.

(** The predicate [H \-* H] holds of the empty heap. Intuitively, we can rewrite
    [0] as [-H + H]. *)

Lemma himpl_hempty_hwand_same : forall H,
  \[] ==> (H \-* H).
Proof using. intros. apply himpl_hwand_r. xsimpl. Qed.

(** Let's now study the interaction of [hwand] with [hempty] and [hpure]. *)

(** The heap predicate [\[] \-* H] is equivalent to [H]. Intuitively, we can
    rewrite [-0+H] as [+H]. *)

Lemma hwand_hempty_l : forall H,
  (\[] \-* H) = H.
Proof using.
  intros. unfold hwand. xsimpl.
  { intros H0 M. xchange M. }
  { xsimpl. }
Qed.

(** The lemma above shows that [\[]] can be removed from the LHS of a magic
    wand.

    More generally, a pure predicate [\[P]] can be removed from the LHS of a
    magic wand as long as [P] is true. Formally: *)

(** **** Exercise: 2 stars, standard, especially useful (hwand_hpure_l) *)

Lemma hwand_hpure_l : forall P H,
  P ->
  (\[P] \-* H) = H.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** Reciprocally, to prove that a heap satisfies [\[P] \-* H2], it suffices to
    prove that this heap satisfies [H2] under the assumption that [P] is true.
    Formally: *)

Lemma himpl_hwand_hpure_r : forall H1 H2 P,
  (P -> H1 ==> H2) ->
  H1 ==> (\[P] \-* H2).
Proof using. introv M. applys himpl_hwand_r. xsimpl. applys M. Qed.

(** **** Exercise: 2 stars, standard, optional (himpl_hwand_hpure_lr)

    Prove that [\[P1 -> P2]] entails [\[P1] \-* \[P2]]. Hint: use [xpull], then
    use [xsimpl] by providing an explicit argument to indicate how the [\exists]
    on the right-hand side of the entailment should be instantiated. *)
Lemma himpl_hwand_hpure_lr : forall (P1 P2:Prop),
  \[P1 -> P2] ==> (\[P1] \-* \[P2]).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** Another interesting property is that arguments on the LHS of a magic wand
    can equivalently be "curried" or "uncurried", just as a function of type
    [(A * B) -> C] is equivalent to a function of type [A -> B -> C].

    The heap predicates [(H1 \* H2) \-* H3], [H1 \-* (H2 \-* H3)], and
    [H2 \-* (H1 \-* H3)] are all equivalent. Intuitively, they all describe [H3]
    with the missing pieces [H1] and [H2]. *)

(** The equivalence between the uncurried form [(H1 \* H2) \-* H3] and the
    curried form [H1 \-* (H2 \-* H3)] is formalized by the lemma shown below.
    The third form, [H2 \-* (H1 \-* H3)], follows from the commutativity
    property [H1 \* H2 = H2 \* H1]. *)

Lemma hwand_curry_eq : forall H1 H2 H3,
  (H1 \* H2) \-* H3 = H1 \-* (H2 \-* H3).
Proof using.
  intros. applys himpl_antisym.
  { apply himpl_hwand_r. apply himpl_hwand_r.
    xchange (hwand_cancel (H1 \* H2) H3). }
  { apply himpl_hwand_r. xchange (hwand_cancel H1 (H2 \-* H3)).
    xchange (hwand_cancel H2 H3). }
Qed.

(** Yet another interesting property is that the RHS of a magic wand can absorb
    resources that the magic wand is starred with.

    Concretely, from [(H1 \-* H2) \* H3], we can get the predicate [H3] to be
    absorbed by the [H2] in the magic wand, yielding [H1 \-* (H2 \* H3)]. One
    way to read this: "if you own [H3] and, when given [H1], you own [H2], then,
    when given [H1], you own both [H2] and [H3]." *)

Lemma hstar_hwand : forall H1 H2 H3,
  (H1 \-* H2) \* H3 ==> H1 \-* (H2 \* H3).
Proof using.
  intros. applys himpl_hwand_r. xsimpl. xchange (hwand_cancel H1 H2).
Qed.

(** The reciprocal entailment is false: [H1 \-* (H2 \* H3)] does not entail
    [(H1 \-* H2) \* H3].

    To see why, instantiate [H1] with [\[False]]. The predicate
    [\[False] \-* (H2 \* H3)] is equivalent to [True], hence imposes no
    restriction on the heap. But, to establish [(\[False] \-* H2) \* H3], we
    would need to exhibit a piece of heap satisfiying [H3]. *)

(** **** Exercise: 1 star, standard, especially useful (himpl_hwand_hstar_same_r)

    Prove that [H1] entails [H2 \-* (H2 \* H1)]. *)

Lemma himpl_hwand_hstar_same_r : forall H1 H2,
  H1 ==> (H2 \-* (H2 \* H1)).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (hwand_cancel_part)

    Prove that [H1 \* ((H1 \* H2) \-* H3)] simplifies to [H2 \-* H3]. *)

Lemma hwand_cancel_part : forall H1 H2 H3,
  H1 \* ((H1 \* H2) \-* H3) ==> (H2 \-* H3).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard, optional (hwand_frame)

    Prove that [H1 \-* H2] entails to [(H1 \* H3) \-* (H2 \* H3)]. Hint: use
    [xsimpl]. *)

Lemma hwand_frame : forall H1 H2 H3,
  H1 \-* H2 ==> (H1 \* H3) \-* (H2 \* H3).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard, optional (hwand_inv)

    Prove the following inversion lemma for [hwand]. This lemma essentially
    captures the fact that [hwand] entails the alternative definition named
    [hwand']. *)

Lemma hwand_inv : forall h1 h2 H1 H2,
  (H1 \-* H2) h2 ->
  H1 h1 ->
  Fmap.disjoint h1 h2 ->
  H2 (h1 \u h2).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End Hwand.

(* ================================================================= *)
(** ** Definition of the Magic Wand Operator for Postconditions: [qwand] *)

Module Qwand.
Import Hwand.

(** In what follows, we generalize the magic wand to operate on postconditions,
    introducing a heap predicate of the form [Q1 \--* Q2], of type [hprop].

    Note that the magic wand between two postconditions produces a heap
    predicate, not a postcondition. *)

(** There are two ways to define the operator [qwand]. The first is to follow
    the same pattern as for [hwand], that is, to quantify some heap predicate
    [H0] such that [H0] starred with [Q1] yields [Q2]. *)

Definition qwand' (Q1 Q2:val->hprop) : hprop :=
  \exists H0, H0 \* \[ Q1 \*+ H0 ===> Q2 ].

(** The second possibility is to define [qwand] directly on top of [hwand], by
    means of the [hforall] quantifier. *)

Definition qwand (Q1 Q2:val->hprop) : hprop :=
  \forall v, (Q1 v) \-* (Q2 v).

Notation "Q1 \--* Q2" := (qwand Q1 Q2) (at level 43).

(** As we establish later in this chapter, [qwand] and [qwand'] both define the
    same operator. We prefer taking [qwand] as the definition because in
    practice instantiating the universal quantifier is the most useful way to
    exploit a magic wand between postconditions. This specialization operation
    is formalized next. This result is a direct consequence of the
    specialization result for [\forall]. *)

Lemma qwand_specialize : forall (v:val) (Q1 Q2:val->hprop),
  (Q1 \--* Q2) ==> (Q1 v \-* Q2 v).
Proof using.
  intros. unfold qwand. applys himpl_hforall_l v. xsimpl.
Qed.

(** The predicate [qwand] satisfies numerous properties that are direct
    counterparts of the properties on [hwand]. First, [qwand] satisfies a
    characteristic equivalence rule. *)

Lemma qwand_equiv : forall H Q1 Q2,
      H ==> (Q1 \--* Q2)
  <-> (Q1 \*+ H) ===> Q2.
Proof using.
  intros. iff M.
  { intros x. xchange M. xchange (qwand_specialize x).
    xchange (hwand_cancel (Q1 x)). }
  { applys himpl_hforall_r. intros x. applys himpl_hwand_r.
    xchange (M x). }
Qed.

(** Second, [qwand] satisfies a cancellation rule. *)

Lemma qwand_cancel : forall Q1 Q2,
  Q1 \*+ (Q1 \--* Q2) ===> Q2.
Proof using. intros. rewrite <- qwand_equiv. applys qimpl_refl. Qed.

(** Third, the operation [Q1 \--* Q2] is contravariant in [Q1] and covariant in
    [Q2]. *)

Lemma qwand_himpl : forall Q1 Q1' Q2 Q2',
  Q1' ===> Q1 ->
  Q2 ===> Q2' ->
  (Q1 \--* Q2) ==> (Q1' \--* Q2').
Proof using.
  introv M1 M2. rewrite qwand_equiv. intros x.
  xchange (qwand_specialize x). xchange M1.
  xchange (hwand_cancel (Q1 x)). xchange M2.
Qed.

(** Fourth the operation [Q1 \--* Q2] can absorb in its RHS resources to which
    it is starred. *)

Lemma hstar_qwand : forall Q1 Q2 H,
  (Q1 \--* Q2) \* H ==> Q1 \--* (Q2 \*+ H).
Proof using.
  intros. rewrite qwand_equiv. xchange (@qwand_cancel Q1).
Qed.

(** **** Exercise: 1 star, standard, especially useful (himpl_qwand_hstar_same_r)

    Prove that [H] entails [Q \--* (Q \*+ H)]. *)

Lemma himpl_qwand_hstar_same_r : forall H Q,
  H ==> Q \--* (Q \*+ H).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (qwand_cancel_part)

    Prove that [H \* ((Q1 \*+ H) \--* Q2)] simplifies to [Q1 \--* Q2]. Hint: use
    [xchange]. *)

Lemma qwand_cancel_part : forall H Q1 Q2,
  H \* ((Q1 \*+ H) \--* Q2) ==> (Q1 \--* Q2).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End Qwand.

(* ================================================================= *)
(** ** Simplifications of Magic Wands using [xsimpl] *)

(** We can extend the tactic [xsimpl] to recognize the magic wand and
    automatically perform a number of obvious simplifications. This extension is
    implemented in the file [LibSepSimpl], which exports the version of [xsimpl]
    illustrated here. *)

Module XsimplDemo.

(** [xsimpl] is able to spot a magic wand that cancels out. For example, if an
    iterated separating conjunction includes both [H2 \-* H3] and [H2], then
    these two heap predicates can be simplified into [H3]. *)

Lemma xsimpl_demo_hwand_cancel : forall H1 H2 H3 H4 H5,
  H1 \* (H2 \-* H3) \* H4 \* H2 ==> H5.
Proof using. intros. xsimpl. Abort.

(** [xsimpl] is able to simplify uncurried magic wands. For example, if an
    iterated separating conjunction includes [(H1 \* H2 \* H3) \-* H4] and [H2],
    the two predicates can be simplified into [(H1 \* H3) \-* H4]. *)

Lemma xsimpl_demo_hwand_cancel_partial : forall H1 H2 H3 H4 H5 H6,
  ((H1 \* H2 \* H3) \-* H4) \* H5 \* H2 ==> H6.
Proof using. intros. xsimpl. Abort.

(** [xsimpl] automatically applies the introduction rule [himpl_hwand_r] when
    the right-hand-side, after prior simplification, reduces to just a magic
    wand. In the example below, [H1] is first cancelled out from both sides,
    then [H3] is moved from the RHS to the LHS. *)

Lemma xsimpl_demo_himpl_hwand_r : forall H1 H2 H3 H4 H5,
  H1 \* H2 ==> H1 \* (H3 \-* (H4 \* H5)).
Proof using. intros. xsimpl. Abort.

(** [xsimpl] can iterate a number of simplifications involving different magic
    wands. *)

Lemma xsimpl_demo_hwand_iter : forall H1 H2 H3 H4 H5,
  H4 \* H3 ==> H5 ->
  H2 \* (H1 \-* H3) \* H4 \* (H2 \-* H1) ==> H5.
Proof using. intros. xsimpl. auto. Qed.

(** [xsimpl] can iterate simplifications on both sides. *)

Lemma xsimpl_demo_hwand_iter_2 : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* ((H1 \* H3) \-* (H4 \-* H5)) \* H4 ==> ((H2 \-* H3) \-* H5).
Proof using. intros. xsimpl. Qed.

(** [xsimpl] is also able to deal with the magic wand for postconditions. In
    particular, it is able to simplify the conjunction of [Q1 \--* Q2] and
    [Q1 v] into [Q2 v]. *)

Lemma xsimpl_demo_qwand_cancel : forall v (Q1 Q2:val->hprop) H1 H2,
  (Q1 \--* Q2) \* H1 \* (Q1 v) ==> H2.
Proof using. intros. xsimpl. Abort.

(** [xsimpl] is able to prove entailments whose right-hand side is a magic wand.
    *)
Lemma xsimpl_hwand_frame : forall H1 H2 H3,
  (H1 \-* H2) ==> ((H1 \* H3) \-* (H2 \* H3)).
Proof using.
  intros.
  (* [xsimpl]'s first step is to turn the goal into
     [(H1 \-* H2) \* (H1 \* H3) ==> (H2 \* H3)]. *)
  xsimpl.
Qed.

End XsimplDemo.

(* ================================================================= *)
(** ** Summary of All the Separation Logic Operators *)

Module SummaryHprop.

(** The core operators are defined as functions over heaps. *)

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

(** The remaining operators can be defined in terms of the core operators. *)

Module ReaminingOperatorsDerived.

  Definition hpure (P:Prop) : hprop :=
    \exists (p:P), \[].

  Definition hand (H1 H2 : hprop) : hprop :=
    \forall (b:bool), if b then H1 else H2.

  Definition hor (H1 H2 : hprop) : hprop :=
    \exists (b:bool), if b then H1 else H2.

  Definition hwand (H1 H2 : hprop) : hprop :=
    \exists H0, H0 \* \[ (H1 \* H0) ==> H2 ].

  Definition qwand (Q1 Q2 : val->hprop) : hprop :=
    \forall v, (Q1 v) \-* (Q2 v).

End ReaminingOperatorsDerived.

(** Of course, these derived operators could also be defined directly as
    predicate over heaps. The definitions are shown below. However, establishing
    properties of such low-level definitions requires more effort than
    establishing properties for the derived definitions shown above. Indeed,
    when operators are defined as derived operations, their properties may be
    established with help of the powerful entailment simplification tactic
    [xsimpl]. *)

Module ReaminingOperatorsDirect.

  Definition hpure (P:Prop) : hprop :=
    fun h => (h = Fmap.empty) /\ P.

  Definition hor (H1 H2 : hprop) : hprop :=
    fun h => H1 h \/ H2 h.

  Definition hand (H1 H2 : hprop) : hprop :=
    fun h => H1 h /\ H2 h.
  Definition hwand (H1 H2:hprop) : hprop :=
    fun h => forall h', Fmap.disjoint h h' -> H1 h' -> H2 (h \u h').

  Definition qwand (Q1 Q2:val->hprop) : hprop :=
    fun h => forall v h', Fmap.disjoint h h' -> Q1 v h' -> Q2 v (h \u h').

End ReaminingOperatorsDirect.

End SummaryHprop.

(* ================================================================= *)
(** ** The Ramified Frame Rule *)

Module RamifiedFrame.
Import Hwand Qwand.

(** Recall the consequence-frame rule, which is used pervasively -- for example
    by the tactic [xapp], for reasoning about applications. *)

Parameter triple_conseq_frame : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.

(** This rule suffers from a practical issue, which we illustrate in detail on a
    concrete example further on. At a high-level, though, the problem stems from
    the fact that we need to instantiate [H2] when applying the rule. Providing
    [H2] by hand is not practical, thus we need to infer it. The value of [H2]
    can be computed as the subtraction of [H] minus [H1]. The resulting value
    may then exploited in the last premise for constructing [Q1 \*+ H2]. This
    transfer of information via [H2] from one subgoal to another can be obtained
    by introducing an "evar" (Coq unification variable) for [H2]. However this
    approach does not work well in cases where [H] contains existential
    quantifiers. This is because such existential quantifiers are typically
    first extracted out of the entailment [H ==> H1 \* H2] by the tactic
    [xsimpl]. But these existentially quantified variables are not in the scope
    of [H2], so the instantiation of the evar associated with [H2] typically
    fails. *)

(** The "ramified frame rule" exploits the magic wand operator to circumvent
    this problem, by merging the two premises [H ==> H1 \* H2] and
    [Q1 \*+ H2 ===> Q] into a single premise that no longer mentions [H2]. This
    replacement premise is [H ==> H1 \* (Q1 \--* Q)]. To understand where it
    comes from, observe first that the second premise [Q1 \*+ H2 ===> Q] is
    equivalent to [H2 ==> (Q1 \--* Q)]. By replacing [H2] with [Q1 \--* Q]
    inside the first premise [H ==> H1 \* H2], we obtain the new premise
    [H ==> H1 \* (Q1 \--* Q)]. This merge of the two entailments leads us to the
    statement of the "ramified frame rule" shown below. *)

Lemma triple_ramified_frame : forall H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  triple t H Q.
Proof using.
  introv M W. applys triple_conseq_frame (Q1 \--* Q) M.
  { applys W. } { applys qwand_cancel. }
Qed.

(** Reciprocally, we can prove that the ramified frame rule entails the
    consequence-frame rule. Hence, the ramified frame rule has the same
    expressive power as the consequence-frame rule. *)

Lemma triple_conseq_frame_of_ramified_frame : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.
Proof using.
  introv M WH WQ. applys triple_ramified_frame M.
  xchange WH. xsimpl. rewrite qwand_equiv. applys WQ.
Qed.

(* ################################################################# *)
(** * More Details *)

(* ================================================================= *)
(** ** Benefits of the Ramified Frame Rule *)

(** Earlier on, we sketched an argument claiming that the consequence-frame rule
    is not very well suited for carrying out proofs in practice, due to issues
    with working with evars for instantiating the heap predicate [H2] in the
    rule. Let us come back to this point and describe the issue in depth on a
    concrete example, then show how the ramified frame rule smoothly handles
    that example. *)

(** Recall, once again, the consequence-frame rule. *)

Parameter triple_conseq_frame' : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.

(** One practical caveat with this rule is that we must resolve [H2], which
    corresponds to the difference between [H] and [H1]. In practice, providing
    [H2] explicitly is extremely tedious. The alternative is to leave [H2] as an
    evar, and count on the fact that the tactic [xsimpl], when applied to
    [H ==> H1 \* H2], will correctly instantiate [H2]. This approach works in
    simple cases, but fails in particular in the case where [H] contains an
    existential quantifier.

    For a concrete example, recall the specification of the primitive [ref],
    which allocates a reference. *)

Parameter triple_ref : forall (v:val),
  triple (val_ref v)
    \[]
    (funloc p => p ~~> v).

(** Assume that wish to derive the following triple, which extends both the
    precondition and the postcondition of [triple_ref] with the heap predicate
    [\exists l' v', l' ~~> v'].

    This predicate describes the existence of some other, totally unspecified,
    reference cell. It is a bit artificial but illustrates the issue. *)

Lemma triple_ref_extended : forall (v:val),
  triple (val_ref v)
    (\exists l' v', l' ~~> v')
    (funloc p => p ~~> v \* \exists l' v', l' ~~> v').

(** Let's try to prove that this specification is derivable from the original
    [triple_ref]. *)

Proof using.
  intros. applys triple_conseq_frame.
  (* observe the evar [?H2] that appears in the second and third subgoals *)
  { applys triple_ref. }
  { (* here, [?H2] should in theory be instantiated with the LHS.
       but [xsimpl]'s strategy is to first extract the quantifiers
       from the LHS. After that, the instantiation of [?H2] fails,
       because the LHS contains variables that are not defined in
       the scope of the evar [?H2] at the time it was introduced. *)
    xsimpl.
Abort.

(** Now, let us apply the ramified frame rule to carry out the same proof, and
    observe how the problem does not show up. *)

Lemma triple_ref_extended' : forall (v:val),
  triple (val_ref v)
    (\exists l' v', l' ~~> v')
    (funloc p => p ~~> v \* \exists l' v', l' ~~> v').
Proof using.
  intros. applys triple_ramified_frame.
  { applys triple_ref. }
  { xsimpl.
    (* Here again, [xsimpl]'s strategy pulls out the existentially quantified
       variables from the LHS. But it works here because the remainder of the
       reasoning takes place in the same subgoal, in the scope of the extended
       Coq context. *)
    intros l' v'.
     (* The proof obligation is of the form [(l' ~~> v) ==> (Q1 \--* Q2)],
        which is equivalent to [Q1 \*+ (l' ~~> v) ===> Q2] according to
        the lemma [qwand_equiv]. *)
    rewrite qwand_equiv. (* same as [apply qwand_equiv] *)
    intros x. xsimpl. auto. }
Qed.

End RamifiedFrame.

(* ================================================================= *)
(** ** Some Tempting, But False, Properties of the Magic Wand *)

Module HwandFalse.
Import Hwand.

(** The entailment [\[] ==> (H \-* H)] holds for any [H]. But the symmetrical
    entailement [(H \-* H) ==> \[]] is false. For a counterexample, instantiate
    [H] as [\[False]]. Any heap satisfies [\[False] \-* \[False]]. But only the
    empty heap satisfies [\[]]. *)

Lemma himpl_hwand_same_hempty_counterexample :
  ~ (forall H, (H \-* H) ==> \[]).
Proof using.
  rew_logic. (* rewrite "not forall" as "exists not" *)
  exists \[False]. intros M.
  lets (h,Hh): (@Fmap.exists_not_empty val _).
  forwards K: M h.
  { applys* himpl_hwand_r (fun h => h <> Fmap.empty). xsimpl*. }
  lets: hempty_inv K. false* Hh.
Qed.

(** As another tempting yet false property of the magic wand, consider the
    converse of the cancellation lemma, that is, [H2 ==> H1 \* (H1 \-* H2)]. It
    does not hold in general. As a counter-example, consider [H2 = \[]] and
    [H1 = \[False]]. The empty heap satisfies the left-hand side of the
    entailment, but it does does not satisfy [\[False] \* (\[False] \-* \[])],
    because there is no way to establish [False] out of thin air. *)

Lemma not_himpl_hwand_r_inv_reciprocal : exists H1 H2,
  ~ (H2 ==> H1 \* (H1 \-* H2)).
Proof using.
  exists \[False] \[]. intros N. forwards K: N (Fmap.empty:heap).
  applys hempty_intro. rewrite hstar_hpure_l in K. destruct K. auto.
Qed.

(** More generally, we should be suspicious of any entailment that introduces
    wands "out of nowhere".

    The entailment [hwand_trans_elim]:
    [(H1 \-* H2) \* (H2 \-* H3) ==> (H1 \-* H3)] is correct because,
    intuitively, the left-hand-side captures that [H1 <= H2] and that [H2 <= H3]
    for some vaguely defined notion of [<=] as "being a subset of". On the
    contrary, the reciprocal entailment
    [(H1 \-* H3) ==> (H1 \-* H2) \* (H2 \-* H3)] is false. Intuitively, from
    [H1 <= H3] there is no way to justify [H1 <= H2] nor [H2 <= H3]. *)

End HwandFalse.

(* ################################################################# *)
(** * Optional Material *)

(* ================================================================= *)
(** ** Equivalence Between Alternative Definitions of the Magic Wand *)

Module HwandEquiv.
Implicit Type op : hprop->hprop->hprop.

(** In what follows we prove the equivalence between the three characterizations
    of [hwand H1 H2] that we have presented:

    1. The definition [hwand] expressed directly in terms of heaps:
    [fun h => forall h', Fmap.disjoint h h' -> H1 h' -> H2 (h' \u h)]

    2. The definition [hwand] expressed in terms of existing operators:
    [\exists H0, H0 \* \[ (H1 \* H0) ==> H2]]

    3. The characterization via the equivalence [hwand_equiv]:
    [forall H0 H1 H2, (H0 ==> H1 \-* H2) <-> (H1 \* H0 ==> H2)].

    4. The characterization via the pair of the introduction rule
    [himpl_hwand_r] and the elimination rule [hwand_cancel].

    To prove the 4-way equivalence, we first prove the equivalence between (1)
    and (2), then prove the equivalence between (2) and (3), and finally the
    equivalence between (3) and (4). *)

Definition hwand_characterization_1 (op:hprop->hprop->hprop) :=
  op = (fun H1 H2 =>
         (fun h => forall h', Fmap.disjoint h h' -> H1 h' -> H2 (h' \u h))).

Definition hwand_characterization_2 (op:hprop->hprop->hprop) :=
  op = (fun H1 H2 => \exists H0, H0 \* \[ H1 \* H0 ==> H2 ]).

Definition hwand_characterization_3 (op:hprop->hprop->hprop) :=
  forall H0 H1 H2, (H0 ==> op H1 H2) <-> (H1 \* H0 ==> H2).

Definition hwand_characterization_4 (op:hprop->hprop->hprop) :=
     (forall H0 H1 H2, (H1 \* H0 ==> H2) -> (H0 ==> op H1 H2))
  /\ (forall H1 H2, (H1 \* (op H1 H2) ==> H2)).

(** The equivalence proofs are given here for reference. The reader needs not
    follow through the details of these proofs. *)

Lemma hwand_characterization_1_eq_2 :
  hwand_characterization_1 = hwand_characterization_2.
Proof using.
  applys pred_ext_1. intros op.
  unfold hwand_characterization_1, hwand_characterization_2.
  asserts K: (forall A B, A = B -> (op = A <-> op = B)).
  { intros. iff; subst*. } apply K; clear K.
  apply pred_ext_3. intros H1 H2 h. iff M.
  { exists (=h). rewrite hstar_hpure_r. split.
    { auto. }
    { intros h3 K3. rewrite hstar_comm in K3.
      destruct K3 as (h1&h2&K1&K2&D&U). subst h1 h3.
      rewrites (>> union_comm_of_disjoint D). applys M D K2. } }
  { (* This direction reproduces the proof of [hwand_inv]. *)
    intros h1 D K1. destruct M as (H0&M).
    destruct M as (h0&h2&K0&K2&D'&U).
    lets (N&E): hpure_inv (rm K2). subst h h2.
    rewrite Fmap.union_empty_r in *.
    applys N. applys hstar_intro K1 K0. applys disjoint_sym D. }
Qed.

Lemma hwand_characterization_2_eq_3 :
  hwand_characterization_2 = hwand_characterization_3.
Proof using.
  applys pred_ext_1. intros op.
  unfold hwand_characterization_2, hwand_characterization_3. iff K.
  { subst. intros. (* apply hwand_equiv. *) iff M.
    { xchange M. intros H3 N. xchange N. }
    { xsimpl H0. xchange M. } }
  { apply fun_ext_2. intros H1 H2. apply himpl_antisym.
    { lets (M&_): (K (op H1 H2) H1 H2). xsimpl (op H1 H2).
      applys M. applys himpl_refl. }
    { xsimpl. intros H0 M. rewrite K. applys M. } }
Qed.

Lemma hwand_characterization_3_eq_4 :
  hwand_characterization_3 = hwand_characterization_4.
Proof using.
  applys pred_ext_1. intros op.
  unfold hwand_characterization_3, hwand_characterization_4. iff K.
  { split.
    { introv M. apply <- K. apply M. }
    { intros. apply K. auto. } }
  { destruct K as (K1&K2). intros. split.
    { introv M. xchange M. xchange (K2 H1 H2). }
    { introv M. applys K1. applys M. } }
Qed.

End HwandEquiv.

(* ================================================================= *)
(** ** Equivalence Results for the Magic Wand for Postconditions *)

Module QwandEquiv.
Implicit Type op : (val->hprop)->(val->hprop)->hprop.

(** In what follows we prove the equivalence between five equivalent
    characterizations of [qwand H1 H2]:

    1. The definition expressed directly in terms of heaps:
    [fun h => forall v h', Fmap.disjoint h h' -> Q1 v h' -> Q2 v (h \u h')]

    2. The definition [qwand], expressed in terms of existing operators:
    [\exists H0, H0 \* \[ (Q1 \*+ H0) ===> Q2]]

    3. The definition expressed using the universal quantifier:
    [\forall v, (Q1 v) \-* (Q2 v)]

    4. The characterization via the equivalence [hwand_equiv]:
    [forall H0 H1 H2, (H0 ==> H1 \-* H2) <-> (H1 \* H0 ==> H2)].

    5. The characterization via the pair of the introduction rule
    [himpl_qwand_r] and the elimination rule [qwand_cancel].

    The proof are essentially identical to the equivalence proofs for [hwand],
    except for definition (3), which is specific to [qwand]. *)

Definition qwand_characterization_1 op :=
  op = (fun Q1 Q2 => (fun h => forall v h', Fmap.disjoint h h' ->
                                            Q1 v h' -> Q2 v (h \u h'))).

Definition qwand_characterization_2 op :=
  op = (fun Q1 Q2 => \exists H0, H0 \* \[ Q1 \*+ H0 ===> Q2 ]).

Definition qwand_characterization_3 op :=
  op = (fun Q1 Q2 => \forall v, (Q1 v) \-* (Q2 v)).

Definition qwand_characterization_4 op :=
  forall H0 Q1 Q2, (H0 ==> op Q1 Q2) <-> (Q1 \*+ H0 ===> Q2).

Definition qwand_characterization_5 op :=
     (forall H0 Q1 Q2, (Q1 \*+ H0 ===> Q2) -> (H0 ==> op Q1 Q2))
  /\ (forall Q1 Q2, (Q1 \*+ (op Q1 Q2) ===> Q2)).

(** Here again, we show proofs for the reference, but the reader needs not
    follow through the details. *)

Lemma hwand_characterization_1_eq_2 :
  qwand_characterization_1 = qwand_characterization_2.
Proof using.
  applys pred_ext_1. intros op.
  unfold qwand_characterization_1, qwand_characterization_2.
  asserts K: (forall A B, A = B -> (op = A <-> op = B)).
  { intros. iff; subst*. } apply K; clear K.
  apply pred_ext_3. intros Q1 Q2 h. iff M.
  { exists (=h). rewrite hstar_hpure_r. split.
    { auto. }
    { intros v h3 K3. rewrite hstar_comm in K3.
      destruct K3 as (h1&h2&K1&K2&D&U). subst h1 h3. applys M D K2. } }
  { intros v h1 D K1. destruct M as (H0&M).
    destruct M as (h0&h2&K0&K2&D'&U).
    lets (N&E): hpure_inv (rm K2). subst h h2.
    rewrite Fmap.union_empty_r in *.
    applys N. rewrite hstar_comm. applys hstar_intro K0 K1 D. }
Qed.

Lemma qwand_characterization_2_eq_3 :
  qwand_characterization_2 = qwand_characterization_3.
Proof using.
  applys pred_ext_1. intros op.
  unfold qwand_characterization_2, qwand_characterization_3.
  asserts K: (forall A B, A = B -> (op = A <-> op = B)).
  { intros. iff; subst*. } apply K; clear K.
  apply fun_ext_2. intros Q1 Q2. apply himpl_antisym.
  { xpull. intros H0 M. applys himpl_hforall_r. intros v.
    rewrite hwand_equiv. xchange M. }
  { xsimpl (qwand Q1 Q2). applys qwand_cancel. }
Qed.

Lemma qwand_characterization_2_eq_4 :
  qwand_characterization_2 = qwand_characterization_4.
Proof using.
  applys pred_ext_1. intros op.
  unfold qwand_characterization_2, qwand_characterization_4. iff K.
  { subst. intros. iff M.
    { xchange M. intros v H3 N. xchange N. }
    { xsimpl H0. xchange M. } }
  { apply fun_ext_2. intros H1 H2. apply himpl_antisym.
    { lets (M&_): (K (op H1 H2) H1 H2). xsimpl (op H1 H2).
      applys M. applys himpl_refl. }
    { xsimpl. intros H0 M. rewrite K. applys M. } }
Qed.

Lemma qwand_characterization_4_eq_5 :
  qwand_characterization_4 = qwand_characterization_5.
Proof using.
  applys pred_ext_1. intros op.
  unfold qwand_characterization_4, qwand_characterization_5. iff K.
  { split.
    { introv M. apply <- K. apply M. }
    { intros. apply K. auto. } }
  { destruct K as (K1&K2). intros. split.
    { introv M. xchange M. xchange (K2 Q1 Q2). }
    { introv M. applys K1. applys M. } }
Qed.

End QwandEquiv.

(* ================================================================= *)
(** ** Historical Notes *)

(** The magic wand is an operator that was introduced in the very first days of
    Separation Logic. From a logical perspective, it makes total sense to have
    it. From a practical perspective, however, it was not always entirely
    obvious how the magic wand could simplify specifications and proofs.
    Experience with CFML-1.0 shows that it is possible to develop a verification
    framework and verify thousands of lines of advanced data structures and
    algorithms without ever involving the magic wand operator. The magic wand,
    however, reveals its interest when exploited (1) in the ramified frame rule,
    and (2) in weakest-precondition style reasoning rules.

    The idea of the ramified frame rule was introduced by
    [Krishnaswami, Birkedal, and Aldrich 2010] (in Bib.v). Its general statement, as
    formulated in the present chapter, was proposed by
    [Hobor and Villard 2013] (in Bib.v). The rule has later been popularized by the
    Iris framework, in particular. *)

(* 2025-01-06 19:51 *)
