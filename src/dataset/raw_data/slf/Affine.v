(** * Affine: Affine Separation Logic *)

Set Implicit Arguments.
From SLF Require Rules.
From SLF Require Export LibSepReference.

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types v : val.
Implicit Types h : heap.
Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.

(* ################################################################# *)
(** * First Pass *)

(** The Separation Logic framework that we have constructed is well suited for a
    language with explicit deallocation, but cannot be used as-is for a language
    equipped with a garbage collector. As pointed out in chapter [Basic],
    there is no rule in our basic Separation Logic that allows discarding a heap
    predicate from the precondition or the postcondition. From a theoretical
    perspective, discarding predicates from the postcondition is sufficient.
    From a practical perspective, however, the user may wish to clarify the
    proof obligations by discarding predicates appearing in the precondition as
    soon as they are no longer useful.

    In this chapter, we explain how to generalize the Separation Logic framework
    to support a "discard rule", which one may invoke to discard heap predicates
    from the precondition or postcondition.

    The framework extended with the discard rule corresponds to an "affine"
    logic, where heap predicates may be freely discarded, as opposed to a
    "linear" logic, where heap predicates cannot be thrown away. As we argue, it
    may be interesting for a program logic to accomodate both "affine"
    predicates and "linear" predicates. We will explain how to fine tune which
    heap predicates may be freely discarded.

    For example, even in a programming language featuring a garbage collector,
    it may be useful to ensure that every file handle opened eventually gets
    closed, or that every lock acquired is eventually released. File handles and
    locks are example of resources that may be described in Separation Logic,
    yet that one should not be allowed to discard freely.

    Regarding garbage-collected data, another possible approach is to require
    the programmer to integrate "free" operations defined as no-ops, to
    materialize the places where memory cells can and should be discarded. This
    approach, however, is cumbersome for freeing recursive data structures. For
    example, to free a mutable list, the programmer would need to iterate over
    the list to free its cells one by one. In contrast, with a "discard rule" in
    the program logic, the user can discard at once the representation predicate
    for the full list, without involving any form of iteration. *)

(** The chapter is organized as follows:

    - first, we recall the example illustrating the limitation of a logic
      without a discard rule for a garbage-collected language;
    - second, we present several versions of the "discard rule";
    - third, we show how to refine the definition of Separation Logic
      triples in such a way that the discard rules are satisfied
      for certain classes of heap predicates. *)

(* ================================================================= *)
(** ** Motivation for the Discard Rule *)

Module MotivatingExample.
Export DemoPrograms.

(** Recall the example of the function [succ_using_incr_attempt] from chapter
    [Basic]. This function allocates a reference with contents [n], then
    increments that reference, and finally returning its contents, that is,
    [n+1]. Let us revisit this example, this time with the intention of
    establishing for it a postcondition that does not leak the existence of a
    left-over reference cell. *)

Definition succ_using_incr :=
  <{ fun 'n =>
       let 'p = ref 'n in
       incr 'p;
       ! 'p }>.

(** In the framework developed so far, the heap predicate describing the
    reference cell allocated by the function cannot be discarded, because the
    code does not include a deallocation operation. Thus, we are forced to
    include in the postcondition the description of a left-over reference with a
    heap predicate, e.g., [\exists p, p ~~> (n+1)], or [\exists p m, p ~~> m].
    *)

Lemma triple_succ_using_incr : forall (n:int),
  triple (succ_using_incr n)
    \[]
    (fun r => \[r = n+1] \* \exists p, (p ~~> (n+1))).
Proof using.
  xwp. xapp. intros p. xapp. xapp. xsimpl. auto.
Qed.

(** If we try to prove a specification that does not mention the left-over
    reference, then we get stuck with a proof obligation of the form
    [p ~~> (n+1) ==> \[]]. *)

Lemma triple_succ_using_incr' : forall (n:int),
  triple (succ_using_incr n)
    \[]
    (fun r => \[r = n+1]).
Proof using.
  xwp. xapp. intros p. xapp. xapp. xsimpl. { auto. } (* stuck here *)
Abort.

(** In what follows, we extend our Separation Logic with a "discard rule" that
    allows proving the above specification for [succ_using_incr]. *)

End MotivatingExample.

(* ================================================================= *)
(** ** Statement of The Discard Rule *)

(** There are several ways to state the "discard rule". Let us begin with two
    variants: one that discards a heap predicate [H'] from the postcondition,
    and one that discards a heap predicate [H'] from the precondition.

    The first rule, named [triple_hany_post], asserts that an arbitrary heap
    predicate [H'] can be dropped from the postcondition, simplifying it from
    [Q \*+ H'] to [Q]. *)

Parameter triple_hany_post : forall t H H' Q,
  triple t H (Q \*+ H') ->
  triple t H Q.

(** Let us show that, using the rule [triple_hany_post], we can derive the
    desired specification for the motivating example from the specification that
    mentions the left-over postcondition. *)

Module MotivatingExampleSolved.
Export MotivatingExample.

Lemma triple_succ_using_incr' : forall (n:int),
  triple (succ_using_incr n)
    \[]
    (fun r => \[r = n+1]).
Proof using.
  intros. applys triple_hany_post. applys triple_succ_using_incr.
Qed.

End MotivatingExampleSolved.

(** A symmetric rule, named [triple_hany_pre], asserts that an arbitrary heap
    predicate [H'] can be dropped from the precondition, simplifying it from
    [H \* H'] to [H]. *)

Parameter triple_hany_pre : forall t H H' Q,
  triple t H Q ->
  triple t (H \* H') Q.

(** Observe the difference between the two rules. In [triple_hany_post], the
    discarded predicate [H'] appears in the premise, reflecting the fact that we
    discard it after the evaluation of the term [t].

    Conversely, in [triple_hany_pre], the discarded predicate [H'] appears in
    the conclusion, reflecting the fact that we discard it before the evaluation
    of [t]. *)

(** The rules [triple_hany_pre] and [triple_hany_post] can be derived from each
    other. As we will establish further on, [triple_hany_pre] is derivable from
    [triple_hany_post] by a simple application of the frame rule. Reciprocally,
    [triple_hany_post] is derivable from [triple_hany_pre], though the proof is
    slightly more involved. This proof appears in lemma
    [triple_hgc_post_from_hgc_pre] in the "optional material" section. *)

(* ================================================================= *)
(** ** Fine-grained Control of Collectable Predicates *)

(* ----------------------------------------------------------------- *)
(** *** Axiomatization of [heap_affine] and [haffine] *)

(** As suggested in the introduction, it may be useful to constrain the discard
    rule in such a way that it can be used to discard only certain types of heap
    predicates, not arbitrary ones.

    The idea is to restrict the discard rules so that only predicates satisfying
    a predicate called [haffine] may be discarded.

    The two discard rules should thus feature an extra premise: to discard a
    heap predicate [H'], the proposition [haffine H'] must hold. *)

Module Preview.

Parameter haffine : hprop -> Prop.

Parameter triple_haffine_post : forall t H H' Q,
  haffine H' ->
  triple t H (Q \*+ H') ->
  triple t H Q.

Parameter triple_haffine_pre : forall t H H' Q,
  haffine H' ->
  triple t H Q ->
  triple t (H \* H') Q.

End Preview.

(** The predicate [haffine H] is defined in terms of a lower-level predicate
    [heap_affine]. The proposition [heap_affine h] asserts that the piece of
    heap [h] may be freely discarded, in the sense that it does not have to be
    accounted for in the program logic. The question of whether a heap or a heap
    predicate should be affine or not is to be decided on a case-by-case basis.
    It depends on the intention of the designer of the program logic. For the
    moment, we leave the predicate [heap_affine] abstract, and allow it to be
    customized later on. *)

Parameter heap_affine : heap -> Prop.

(** The only assumptions we need to make about [heap_affine] is that it holds of
    the empty heap and that it is preserved by a disjoint union operation. *)

Parameter heap_affine_empty :
  heap_affine Fmap.empty.

Parameter heap_affine_union : forall h1 h2,
  heap_affine h1 ->
  heap_affine h2 ->
  Fmap.disjoint h1 h2 ->
  heap_affine (Fmap.union h1 h2).

(** We will later show two extreme instantiations: one that leads to a logic
    where all predicates are affine (i.e. can be freely discarded), and one that
    leads to a logic where all predicates are linear (i.e. none can be freely
    discarded, like in our previous set up). *)

(* ----------------------------------------------------------------- *)
(** *** Definition and Properties of [heap_affine] *)

(** The predicate [haffine H] captures the notion of "affine heap predicate".

    A heap predicate is affine iff it holds only of affine heaps. *)

Definition haffine (H:hprop) : Prop :=
  forall h, H h -> heap_affine h.

(** The predicate [haffine] distributes in a natural way over each of the
    operators of Separation Logic -- i.e., the combination of affine heap
    predicates yields affine heap predicates. In particular:

    - [\[]] and [\[P]], which describe empty heaps, can always be discarded;
    - [H1 \* H2] can be discarded if both [H1] and [H2] can be discarded;
    - [\forall x, H] can be discarded if [H] can be discarded for at least one
      [x];
    - [\exists x, H] can be discarded if [H] can be discarded for every [x].

    The treatment of universal quantifiers can be explained as follows. Consider
    a heap [h] that satisfies [\forall (x:A), H], and consider a particular
    value [v] of type [A]. The heap [h] also satisfies [[x:=v]H]. Thus, if the
    heap predicate [[x:=v]H] can be discarded, the stronger predicate
    [\forall (x:A), H] can also be discarded.

    Existential quantifiers can be explained as follows. Consider a heap [h]
    that satisfies [\exists (x:A), H]. We know that there exists a value [v] of
    type [A] such that [h] satisfies [[x:=v]H]. However, we know nothing about
    this value [v]. Therefore, to discard [\exists (x:A), H], we need to know
    that [[x:=v]H] can be discarded for every possible [v]. *)

Lemma haffine_hempty :
  haffine \[].
Proof using.
  introv K. lets E: hempty_inv K. subst. applys heap_affine_empty.
Qed.

Lemma haffine_hpure : forall P,
  haffine \[P].
Proof using.
  intros. intros h K. lets (HP&M): hpure_inv K.
  subst. applys heap_affine_empty.
Qed.

Lemma haffine_hstar : forall H1 H2,
  haffine H1 ->
  haffine H2 ->
  haffine (H1 \* H2).
Proof using.
  introv M1 M2 K. lets (h1&h2&K1&K2&D&U): hstar_inv K.
  subst. applys* heap_affine_union.
Qed.

Lemma haffine_hexists : forall A (J:A->hprop),
  (forall x, haffine (J x)) ->
  haffine (\exists x, (J x)).
Proof using. introv F1 (x&Hx). applys* F1. Qed.

Lemma haffine_hforall' : forall A (J:A->hprop),
  (exists x, haffine (J x)) ->
  haffine (\forall x, (J x)).
Proof using.
  introv (x&Hx) M. lets N: hforall_inv M. applys* Hx.
Qed.

(** The rule [haffine_hforall'] requires the user to provide evidence that there
    exists at least one value [x] of type [A] for which [haffine (J x)] is true.
    In practice, the user is generally not interested in proving properties of a
    specific value [x], but is happy to justify that [J x] is affine for any
    [x]. The corresponding statement appears below, with an assumption [Inhab A]
    asserting that the type [A] is inhabited. In practice, the [\forall]
    quantifier is always invoked on inhabited types, so this is a benign
    restriction. *)

Lemma haffine_hforall : forall A `{Inhab A} (J:A->hprop),
  (forall x, haffine (J x)) ->
  haffine (\forall x, (J x)).
Proof using.
  introv IA M. applys haffine_hforall'. exists (arbitrary (A:=A)). applys M.
Qed.

(** Another useful fact about [haffine] is that to prove [haffine (\[P] \* H)]
    it is sufficient to prove [haffine H] under the hypothesis that [P] is true.
    Formally: *)

Lemma haffine_hstar_hpure_l : forall P H,
  (P -> haffine H) ->
  haffine (\[P] \* H).
Proof using. introv M. intros h K. rewrite hstar_hpure_l in K. applys* M. Qed.

(* ================================================================= *)
(** ** The Affine-Top Heap Predicate: [\GC] *)

(* ----------------------------------------------------------------- *)
(** *** Definition of The Affine-Top Predicate *)

(** We next introduce a new heap predicate, called "affine top", that is very
    handy for describing "the possibility to discard a heap predicate". We use
    this predicate to reformulate the discard rules in a more concise and usable
    manner. This predicate is written [\GC] and named [hgc] in the
    formalization. The predicate [\GC] holds of any affine heap.

    The reason [\GC] is named "affine top" is because it refines a
    representation predicate called "top", and written [\Top]. The predicate
    [\Top] is the heap predicate that holds of any heap. It can be defined as
    [fun (h:heap) => True], or, equivalently, as [\exists (H:hprop), H]. The
    characteristic property of [\Top] is the entailment
    [forall H, (H ==> \Top)].

    The affine top predicate [\GC] can be defined as
    [exists H, \[haffine H] \* H]. As we prove further on, it could be
    equivalently defined as [fun h => heap_affine h]. We prefer the former
    definition as it is easier to manipulate using the [xsimpl] tactic. *)

Definition hgc : hprop :=
  \exists H, \[haffine H] \* H.

Declare Scope hgc_scope.
Open Scope hgc_scope.

Notation "\GC" := (hgc) : hgc_scope.

(** The following introduction lemma asserts that [\GC h] holds when [h]
    satisfies [heap_affine]. *)

(** **** Exercise: 2 stars, standard, especially useful (triple_frame)

    Prove that the affine heap predicate holds of any affine heap. *)

Lemma hgc_intro : forall h,
  heap_affine h ->
  \GC h.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** The elimination lemma asserts the converse. *)

(** **** Exercise: 2 stars, standard, optional (hgc_inv)

    Prove the elimination lemma for [\GC] expressed using [heap_affine]. *)

Lemma hgc_inv : forall h,
  \GC h ->
  heap_affine h.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** Together, the introduction and the elimination rule justify the fact that
    [hgc] could equivalently have been defined as [heap_affine]. *)

Lemma hgc_eq_heap_affine :
  hgc = heap_affine.
Proof using.
  intros. applys himpl_antisym.
  { intros h M. applys* hgc_inv. }
  { intros h M. applys* hgc_intro. }
Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of the Affine-Top Predicate *)

(** One fundamental property of [\GC] that is useful in the soundness proofs is
    that the conjunction of two occurences of [\GC] may be merged into a single
    [\GC]. *)

Lemma hstar_hgc_hgc :
  (\GC \* \GC) = \GC.
Proof using.
  unfold hgc. applys himpl_antisym.
  { xpull. intros H1 K1 H2 K2. xsimpl (H1 \* H2). applys* haffine_hstar. }
  { xpull. intros H K. xsimpl H \[]. auto. applys haffine_hempty. }
Qed.

(** Another useful property is that the heap predicate [\GC] itself satisifes
    [haffine]. *)

Lemma haffine_hgc :
  haffine \GC.
Proof using.
  applys haffine_hexists. intros H. applys haffine_hstar_hpure_l. auto.
Qed.

(** The process of exploiting [\GC] to "absorb" affine heap predicates is
    captured by the following lemma, which asserts that a heap predicate [H]
    entails [\GC] whenever [H] is affine. *)

Lemma himpl_hgc_r : forall H,
  haffine H ->
  H ==> \GC.
Proof using. introv M. intros h K. applys hgc_intro. applys M K. Qed.

(** In particular, the empty heap predicate [\[]] entails [\GC], because the
    empty heap predicate is affine (lemma [haffine_hempty]). *)

Lemma hempty_himpl_hgc :
  \[] ==> \GC.
Proof using. applys himpl_hgc_r. applys haffine_hempty. Qed.

(** **** Exercise: 3 stars, standard, especially useful (himpl_hgc_absorb)

    Show that [\GC * H] entails [\GC] for any [H] satisfying [haffine]. *)

Lemma himpl_hgc_absorb_r : forall H,
  haffine H ->
  \GC \* H ==> \GC.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** Using the predicate [\GC], we can reformulate the constrained discard rule
    [triple_haffine_post] as follows. *)

Parameter triple_hgc_post : forall t H Q,
  triple t H (Q \*+ \GC) ->
  triple t H Q.

(** This rule is more concise than [triple_haffine_post]. Moreover, the piece of
    heap being discarded, previously described by [H'], no longer needs to be
    provided up front, at the moment of applying the rule. Instead, it can be
    provided further on in the reasoning, by exploiting [himpl_hgc_r] to prove
    an entailment of the form [H' ==> \GC]. *)

(* ================================================================= *)
(** ** Example Instantiations of [heap_affine] *)

(* ----------------------------------------------------------------- *)
(** *** Instantiation of [heap_affine] for a Fully Affine Logic *)

Module FullyAffineLogic.

(** To set up a fully affine logic, we consider a definition of [heap_affine]
    that holds of any heap. *)

Parameter heap_affine_def : forall h,
  heap_affine h = True.

(** It is trivial to check that [heap_affine] satisfies the required
    distribution properties on the empty heap and the union of heaps. *)

Lemma heap_affine_empty :
  heap_affine Fmap.empty.
Proof using. rewrite* heap_affine_def. Qed.

Lemma heap_affine_union : forall h1 h2,
  heap_affine h1 ->
  heap_affine h2 ->
  Fmap.disjoint h1 h2 ->
  heap_affine (Fmap.union h1 h2).
Proof using. intros. rewrite* heap_affine_def. Qed.

(** With that instantiation, [haffine] holds of any heap predicate. *)

Lemma haffine_equiv : forall H,
  (haffine H) <-> True.
Proof using.
  intros. iff M.
  { auto. }
  { unfold haffine. intros. rewrite* heap_affine_def. }
Qed.

(** Moreover, the affine top predicate [\GC] is equivalent to the top predicate
    [htop], defined as [fun h => True] or equivalently as [\exists H, H]. *)

Definition htop : hprop :=
  \exists H, H.

Lemma hgc_eq_htop : hgc = htop.
Proof using.
  unfold hgc, htop. applys himpl_antisym.
  { xsimpl. }
  { xsimpl. intros. rewrite* haffine_equiv. }
Qed.

End FullyAffineLogic.

(* ----------------------------------------------------------------- *)
(** *** Instantiation of [heap_affine] for a Fully Linear Logic *)

Module FullyLinearLogic.

(** To set up a fully affine logic, we consider a definition of [heap_affine]
    that holds only of empty heaps. *)

Parameter heap_affine_def : forall h,
  heap_affine h = (h = Fmap.empty).

(** Again, it is not hard to check that [heap_affine] satisfies the required
    distributivity properties. *)

Lemma heap_affine_empty :
  heap_affine Fmap.empty.
Proof using. rewrite* heap_affine_def. Qed.

Lemma heap_affine_union : forall h1 h2,
  heap_affine h1 ->
  heap_affine h2 ->
  Fmap.disjoint h1 h2 ->
  heap_affine (Fmap.union h1 h2).
Proof using.
  introv K1 K2 D. rewrite heap_affine_def in *.
  subst. rewrite* Fmap.union_empty_r.
Qed.

(** With that instantiation, the predicate [haffine H] is equivalent to
    [H ==> \[]], that is, it characterizes heap predicates that hold of the
    empty heap. *)

Lemma haffine_equiv : forall H,
  haffine H <-> (H ==> \[]).
Proof using.
  intros. unfold haffine. iff M.
  { intros h K. specializes M K. rewrite heap_affine_def in M.
    subst. applys hempty_intro. }
  { intros h K. specializes M K. rewrite heap_affine_def.
    applys hempty_inv M. }
Qed.

(** Moreover, the affine top predicate [\GC] is equivalent to the empty heap
    predicate [hempty]. *)

Lemma hgc_eq_hempty : hgc = hempty.
Proof using.
  unfold hgc. applys himpl_antisym.
  { xpull. introv N. rewrite* haffine_equiv in N. }
  { xsimpl \[]. applys haffine_hempty. }
Qed.

End FullyLinearLogic.

(* ================================================================= *)
(** ** Definition of a Partially Affine Separation Logic *)

(* ----------------------------------------------------------------- *)
(** *** Refined Definition of Triples *)

Module NewTriples.

(** We now explain how to refine the notion of Separation Logic triple so as to
    accomodate the discard rule. Recall the previous definition of triples,
    capturing a linear logic.

    Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
      forall s, H s -> eval s t Q.

    The new discard rule [triple_htop_post] asserts that postconditions may be
    freely extended with the [\GC] predicate. To support this rule, it suffices
    to modify the definition of [triple] to include the predicate [\GC] in the
    postcondition of the underlying Hoare triple, as follows. *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall s, H s -> eval s t (Q \*+ \GC).

(** Next, for the updated definition of [triple] using [\GC], we establish:

    - that all the existing reasoning rules of Separation Logic remain sound,
      and
    - that the new discard rules [triple_htop_post], [triple_haffine_hpost], and
      [triple_haffine_hpre] are provable. *)

(* ----------------------------------------------------------------- *)
(** *** Soundness of the Existing Rules *)

(** Let us update the soundness proof of the rules of Separation Logic to
    account for the addition of [\GC] in the definition of [triples]. All the
    rules are proved using exactly the same proof scripts as before, with
    [xsimpl] possibly performing extra work for cancelling out occurrences of
    [\GC] on both sides of an entailment. *)

Lemma triple_conseq : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof using.
  unfolds triple. introv M MH MQ HF. applys* eval_conseq. xsimpl*.
Qed.

Lemma triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof using.
  introv M HF. lets (h1&h2&M1&M2&MD&MU): hstar_inv (rm HF).
  subst. specializes M M1. applys eval_conseq.
  { applys eval_frame M MD. } { xsimpl. intros h' ->. applys M2. }
Qed.

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
Proof using. introv M (x&K). applys M K. Qed.

(** We also need to update the reasoning rules for terms. We present one
    representative example: the proof rule for sequences. *)

Lemma triple_seq : forall t1 t2 H Q H1,
  triple t1 H (fun v => H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.
Proof using.
(** The proof is structured like in lemma [triple_seq] from chapter
    [Rules]. *)
  unfold triple. introv M1 M2. intros s Hs. applys eval_seq.
  { applys M1 Hs. }
  { simpl. intros v1 s2 Hs2. lets (h1&h2&N1&N2&D&->): hstar_inv (rm Hs2).
    applys eval_conseq. { applys eval_frame D. applys* M2. }
(** The main difference is the need to to invoke the lemma [hstar_hgc_hgc] for
    merging the left-over that originates from [t1] with the [\GC] that
    originates from [t2] into a single [\GC]. *)
    asserts R: ((= h2) ==> \GC). { intros ? ->. auto. } xchange (rm R).
    xchange hstar_hgc_hgc. xsimpl. }
Qed.

(* ----------------------------------------------------------------- *)
(** *** Soundness of the Discard Rules *)

(** Let us first establish the soundness of the discard rule [triple_htop_post].
    *)

(** **** Exercise: 3 stars, standard, especially useful (triple_hgc_post)

    Prove [triple_hgc_post] with respect to the refined definition of [triple]
    that includes [\GC] in the postcondition. Hint: exploit [hstar_hgc_hgc],
    with help from the tactics [xchange] and [xsimpl]. *)

Lemma triple_hgc_post : forall t H Q,
  triple t H (Q \*+ \GC) ->
  triple t H Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, standard, especially useful (triple_haffine_post)

    Prove that [triple_haffine_post] is derivable from [triple_hgc_post]. Hint:
    use the property [himpl_hgc_r], which asserts [H' ==> \GC]. *)

Lemma triple_haffine_post : forall t H H' Q,
  haffine H' ->
  triple t H (Q \*+ H') ->
  triple t H Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, standard, optional (triple_hgc_post_from_triple_haffine_post)

    Conversely, prove that [triple_hgc_post] is derivable from
    [triple_haffine_post]. *)

Lemma triple_hgc_post_from_triple_haffine_post : forall t H Q,
  triple t H (Q \*+ \GC) ->
  triple t H Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, standard, optional (triple_haffine_pre)

    Prove that [triple_haffine_pre] is derivable from [triple_hgc_post]. Hint:
    exploit the frame rule, and leverage [triple_hgc_post] either directly or by
    invoking its corollary [triple_haffine_post]. *)

Lemma triple_haffine_pre : forall t H H' Q,
  haffine H' ->
  triple t H Q ->
  triple t (H \* H') Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Combined Structural Rules *)

(** **** Exercise: 2 stars, standard, optional (triple_conseq_frame_hgc)

    Prove the combined structural rule [triple_conseq_frame_hgc], which extends
    [triple_conseq_frame] with the discard rule, replacing [Q1 \*+ H2 ===> Q]
    with [Q1 \*+ H2 ===> Q \*+ \GC]. *)

Lemma triple_conseq_frame_hgc : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q \*+ \GC ->
  triple t H Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, standard, optional (triple_ramified_frame_hgc)

    Prove the following generalization of the ramified frame rule that includes
    the discard rule. Hint: take inspiration from the proof of
    [triple_ramified_frame] presented in the chapter [Wand]. *)

Lemma triple_ramified_frame_hgc : forall H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* (Q \*+ \GC)) ->
  triple t H Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ################################################################# *)
(** * More Details *)

(* ================================================================= *)
(** ** Discard Rules in WP Style *)

(* ----------------------------------------------------------------- *)
(** *** Definition of WP for a Partially Affine Separation Logic *)

(** In chapter [WPsem], we defined [wp t Q s] as [eval s t Q]. To account
    for affine heaps, we refine the definition to [eval s t (Q \*+ \GC)]. *)

Definition wp (t:trm) (Q:val->hprop) : hprop :=
  fun s => eval s t (Q \*+ \GC).

(** The characteristic equivalence of [wp] remains valid, with respect to the
    definition of [wp] extended with [\GC] and the definition of [triple]
    extended with [\GC]. *)

Lemma wp_equiv : forall t H Q,
  (H ==> wp t Q) <-> (triple t H Q).
Proof using. iff M; introv Hs; applys M Hs. Qed.

(** The structural reasoning rules also remain valid. *)

Lemma wp_conseq : forall t Q1 Q2,
  Q1 ===> Q2 ->
  wp t Q1 ==> wp t Q2.
Proof using.
  unfold wp. introv M. intros s Hs. applys* eval_conseq. xsimpl*.
Qed.

Lemma wp_frame : forall t H Q,
  (wp t Q) \* H ==> wp t (Q \*+ H).
Proof using.
  intros. unfold wp. intros h HF.
  lets (h1&h2&M1&M2&MD&MU): hstar_inv (rm HF).
  subst. applys eval_conseq.
  { applys eval_frame M1 MD. }
  { xsimpl. intros h' ->. applys M2. }
Qed.

(** In weakest precondition style, the discard rule [triple_hgc_post] translates
    into the entailment [wp t (Q \*+ \GC) ==> wp t Q]. *)

(** **** Exercise: 1 star, standard, optional (wp_hgc_post) *)
Lemma wp_hgc_post : forall t Q,
  wp t (Q \*+ \GC) ==> wp t Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** The wp-style presentation of the rule [triple_hgc_pre] is captured by the
    lemma [wp_haffine_pre] shown below. *)

(** **** Exercise: 3 stars, standard, optional (wp_haffine_pre)

    Prove [wp_haffine_pre]. Hint: one possibility is to use [eval_conseq] and
    [wp_frame], as well as [himpl_hgc_r] and [hstar_hgc_hgc]. Another
    possibility is to refine the proof of [wp_frame]. *)

Lemma wp_haffine_pre : forall t H Q,
  haffine H ->
  (wp t Q) \* H ==> wp t Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** The revised presentation of the wp-style ramified frame rule includes an
    extra [\GC] predicate. This rule captures at once all the structural
    properties of Separation Logic, including the discard rule. *)

(** **** Exercise: 3 stars, standard, optional (wp_haffine_pre)

    Prove [wp_ramified] with support for [\GC]. *)

Lemma wp_ramified : forall Q1 Q2 t,
  (wp t Q1) \* (Q1 \--* (Q2 \*+ \GC)) ==> (wp t Q2).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Exploiting the Discard Rule in Proofs *)

(** In a practical verification proof, there are two useful ways to discard heap
    predicates that are no longer needed:

    - by invoking [triple_haffine_pre] to remove a specific
      predicate from the current state, i.e., the precondition; or
    - by invoking [triple_htop_post] to add a [\GC] into the
      current postcondition and allow subsequent removal of any
      predicate that may be left-over in the final entailment
      justifying that the final state satisfies the postcondition.

    Eager removal of predicates from the current state is never necessary: one
    can always be lazy and postpone the application of the discard rule until
    the last step of reasoning.

    It is cumbersome for the user to anticipate, right from the beginning of the
    proof of a function, the need to discard heap predicates at the last line of
    the function body. To ease the work of the user, it suffices to
    systematically apply the rule [triple_htop_post] as very first step of the
    proof of every function. The effect is to extend the postcondition of the
    function with a [\GC] predicate. This predicate may be used to absorb any
    garbage left-over at the end of the proof of the function body. If there is
    no such garbage, the tactic [xsimpl] automatically discards the [\GC]
    predicate.

    We implement this strategy by integrating the rule [triple_htop_post] into
    the tactic [xwp], which sets up the verification proof by computing the
    characteristic formula. To that end, we generalize the lemma [xwp_lemma],
    which the tactic [xwp] applies. Its original statement is as follows. *)

Parameter xwp_lemma : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.

(** Its generalized form extends the postcondition from [Q] to [Q \*+ \GC], as
    shown below. *)

Lemma xwp_lemma' : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 (Q \*+ \GC) ->
  triple (trm_app v1 v2) H Q.
Proof using. introv E M. applys triple_hgc_post. applys* xwp_lemma. Qed.

(** We update the tactic [xwp] to exploit the lemma [xwp_lemma'] instead of
    [xwp_lemma]. *)

Tactic Notation "xwp" :=
  intros; applys xwp_lemma';
  [ reflexivity | simpl; unfold wpgen_var; simpl ].

(* ----------------------------------------------------------------- *)
(** *** Example Proof in an Affine Separation Logic *)

(** Using the updated version of [xwp], let us revisite the proof of our
    motivating example [succ_using_incr] in a fully affine logic where any
    predicate can be discarded. *)

Module MotivatingExampleWithUpdatedXwp.
Export MotivatingExample.

(** Assume a fully affine logic. *)

Parameter haffine_hany : forall (H:hprop),
  haffine H.

(** Observe, in the proof below, the [\GC] introduced in the postcondition by
    the call to [xwp]. *)

Lemma triple_succ_using_incr : forall (n:int),
  triple (succ_using_incr n)
    \[]
    (fun r => \[r = n+1]).
Proof using.
  xwp. xapp. intros r. xapp. xapp. xsimpl. { auto. }
  (* It remains to absorb the left-over reference into the [\GC] predicate *)
  applys himpl_hgc_r. applys haffine_hany.
Qed.

(** We will show further on how to automate the work from the last line of the
    proof above, by setting up [xsimpl] to automatically resolve goals of the
    form [H ==> \GC]. *)

End MotivatingExampleWithUpdatedXwp.

(* ================================================================= *)
(** ** Revised Definition of [mkstruct] *)

(** Recall the definition [mkstruct], which is key to implementing [wpgen] and
    the x-tactics.

    Definition mkstruct (F:formula) : formula :=
      fun Q => \exists Q', (F Q') \* (Q' \--* Q).

    This definition can be generalized to handle not just the consequence and
    frame rules, but also the discard rule. To that end, [mkstruct] is extended
    with an additional [\GC], as follows. *)

Definition mkstruct (F:formula) : formula :=
  fun Q => \exists Q', F Q' \* (Q' \--* (Q \*+ \GC)).

(** Let us prove that this revised definition of [mkstruct] does indeed satisfy
    the [wp]-style statement of the discard rule, which is stated in a way
    similar to [wp_hgc_post]. *)

Lemma mkstruct_hgc : forall Q F,
  mkstruct F (Q \*+ \GC) ==> mkstruct F Q.
Proof using.
  intros. unfold mkstruct. set (X := hgc) at 3. replace X with (\GC \* \GC).
  { xsimpl. } { subst X. apply hstar_hgc_hgc. }
Qed.

(** Further, let us prove that the revised definition of [mkstruct] still
    satisfies the four originally required properties: erasure, consequence,
    frame, and monoticity. *)

Lemma mkstruct_erase : forall F Q,
  F Q ==> mkstruct F Q.
Proof using.
  intros. unfold mkstruct. xsimpl Q. apply himpl_hgc_r. apply haffine_hempty.
Qed.

Lemma mkstruct_conseq : forall F Q1 Q2,
  Q1 ===> Q2 ->
  mkstruct F Q1 ==> mkstruct F Q2.
Proof using.
  introv WQ. unfold mkstruct. xpull. intros Q'. xsimpl Q'. xchange WQ.
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

(** **** Exercise: 2 stars, standard, optional (mkstruct_haffine_post)

    Prove the reformulation of [triple_haffine_post] adapted to [mkstruct], for
    discarding an affine piece of postcondition. *)

Lemma mkstruct_haffine_post : forall H Q F,
  haffine H ->
  mkstruct F (Q \*+ H) ==> mkstruct F Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (mkstruct_haffine_pre)

    Prove the reformulation of [triple_haffine_pre] adapted to [mkstruct], for
    discarding an affine piece of postcondition. *)

Lemma mkstruct_haffine_pre : forall H Q F,
  haffine H ->
  (mkstruct F Q) \* H ==> mkstruct F Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End NewTriples.

(* ================================================================= *)
(** ** The Tactic [xaffine] and the Behavior of [xsimpl] on [\GC] *)

Module Xaffine.

(** The tactic [xaffine] applies to a goal of the form [haffine H]. It
    simplifies the goal using all the distributivity rules associated with
    [haffine]. Ultimately, it invokes [eauto with haffine], which can leverage
    knowledge specific to the definition of [haffine] from the Separation Logic
    setup at hand. *)

Create HintDb haffine.

Tactic Notation "xaffine" :=
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

Lemma xaffine_demo : forall H1 H2 H3,
  haffine H1 ->
  haffine H3 ->
  haffine (H1 \* H2 \* H3).
Proof using. introv K1 KJ. xaffine. (* remains [haffine H2] *) Abort.

End Xaffine.

Module XsimplExtended.
Import LibSepReference.

(** The tactic [xsimpl] is extended with support for simplifying goals of the
    form [H ==> \GC] into [haffine H], using lemma [himpl_hgc_r]. For example,
    [xsimpl] can simplify the goal [H1 \* H2 ==> H2 \* \GC] into just
    [haffine H1]. *)

Lemma xsimpl_xgc_demo : forall H1 H2,
  H1 \* H2 ==> H2 \* \GC.
Proof using. intros. xsimpl. (* remains [haffine H1] *) Abort.

(** In addition, [xsimpl] invokes the tactic [xaffine] to simplify
    side-conditions of the form [haffine H]. For example, [xsimpl] can prove the
    following lemma. *)

Lemma xsimpl_xaffine_demo : forall H1 H2,
  haffine H1 ->
  H1 \* H2 ==> H2 \* \GC.
Proof using. introv K1. xsimpl. Qed.

End XsimplExtended.

(* ================================================================= *)
(** ** Tactics for Applying the Discard Rules *)

Module XGC.
Import LibSepReference.

(** This section presents the discard tactics [xgc], [xc_keep], and [xgc_post].
    Their implementation leverages the discard property of [mkstruct],
    reproduced below. *)

Parameter mkstruct_hgc : forall Q F,
  mkstruct F (Q \*+ \GC) ==> mkstruct F Q.

(** The tactic [xgc H1] removes [H1] from the precondition (i.e., from the
    current state), in the course of a proof exploiting a formula produced by
    [wpgen]. More precisely, the tactic [xgc H1] removes [H1] from the current
    precondition [H]. It leverages [xsimpl] to simplify the entailment
    [H ==> H1 \* H2] and infer [H2], which describes what remains after removing
    [H1] from [H]. *)

Lemma xgc_lemma: forall H1 H2 H F Q,
  H ==> H1 \* H2 ->
  haffine H1 ->
  H2 ==> mkstruct F Q ->
  H ==> mkstruct F Q.
Proof using.
  introv WH K M. xchange WH. xchange M.
  applys himpl_trans mkstruct_frame.
  applys himpl_trans_r mkstruct_hgc.
  applys mkstruct_conseq. xsimpl.
Qed.

Tactic Notation "xgc" constr(H) :=
  eapply (@xgc_lemma H); [ xsimpl | xaffine | ].

Lemma xgc_demo : forall H1 H2 H3 F Q,
  haffine H2 ->
  (H1 \* H2 \* H3) ==> mkstruct F Q.
Proof using. introv K2. xgc H2. (* clears [H2] *) Abort.

(** The tactic [xgc_keep H] is a variant of [xgc] that enables discarding
    everything but [H] from the precondition.

    The implementation of the tactic leverages the same lemma [xgc_lemma], but
    providing [H2] instead of [H1]. *)

Tactic Notation "xgc_keep" constr(H) :=
  eapply (@xgc_lemma _ H); [ xsimpl | xaffine | ].

Lemma xgc_keep_demo : forall H1 H2 H3 F Q,
  haffine H1 ->
  haffine H3 ->
  (H1 \* H2 \* H3) ==> mkstruct F Q.
Proof using. introv K1 K3. xgc_keep H2. Abort.

(** The tactic [xgc_post] simply extends the postcondition with a [\GC], to
    enable subsequent discarding of heap predicates in the final entailment. *)

Lemma xgc_post_lemma : forall H Q F,
  H ==> mkstruct F (Q \*+ \GC) ->
  H ==> mkstruct F Q.
Proof using. introv M. xchange M. applys mkstruct_hgc. Qed.

Tactic Notation "xgc_post" :=
  apply xgc_post_lemma.

(** The example below illustrates a usage of the [xgc_post] tactic. *)

Lemma xgc_keep_demo : forall H1 H2 H3 F Q,
  haffine H1 ->
  haffine H3 ->
  H1 ==> mkstruct F (Q \*+ H2 \*+ H3) ->
  H1 ==> mkstruct F Q.
Proof using.
  introv K1 K3 M.
  xgc_post. (* add [\GC] to the postcondition [Q] *)
  xchange M. applys mkstruct_conseq.
  xsimpl.
Qed.

End XGC.

(* ################################################################# *)
(** * Optional Material *)

(* ================================================================= *)
(** ** Alternative Statement for Distribution of [haffine] on Quantifiers *)

Module HaffineQuantifiers.

(** Recall the lemmas [haffine_hexists] and [haffine_hforall].

    Lemma haffine_hexists : forall A (J:A->hprop),
      (forall x, haffine (J x)) ->
      haffine (\exists x, (J x)).
    Lemma haffine_hforall : forall A `{Inhab A} (J:A->hprop),
      (forall x, haffine (J x)) ->
      haffine (\forall x, (J x)).

    They can be reformulated in a more concise way, as explained next. *)

(** First, to smoothly handle the distribution on the quantifiers, let us extend
    the notion of "affinity" to postconditions. The predicate [haffine_post J]
    asserts that [haffine] holds of [J x] for any [x]. *)

Definition haffine_post (A:Type) (J:A->hprop) : Prop :=
  forall x, haffine (J x).

(** The rules then reformulate as follows. *)

Lemma haffine_hexists : forall A (J:A->hprop),
  haffine_post J ->
  haffine (hexists J).
Proof using. introv F1 (x&Hx). applys* F1. Qed.

Lemma haffine_hforall : forall A `{Inhab A} (J:A->hprop),
  haffine_post J ->
  haffine (hforall J).
Proof using.
  introv IA F1 Hx. lets N: hforall_inv Hx. applys* F1 (arbitrary (A:=A)).
Qed.

End HaffineQuantifiers.

(* ================================================================= *)
(** ** Deriving the Rule GC-Post from the Rule GC-Pre *)

Module FromPreToPostGC.
Import Rules ProofsSameSemantics.

(** Earlier on, we proved that [triple_hgc_pre] is derivable from
    [triple_hgc_post], through a simple application of the frame rule. We wrote
    that, reciprocally, the rule [triple_hgc_post] is derivable from
    [triple_hgc_pre], yet with a slightly more involved proof. Let us present
    this proof. Concretely, assume [triple_hgc_pre] and let us prove the result
    [triple_hgc_post]. *)

Parameter triple_hgc_pre : forall t H Q,
  triple t H Q ->
  triple t (H \* \GC) Q.

Parameter triple_hgc_post : forall t H Q,
  triple t H (Q \*+ \GC) ->
  triple t H Q.

(** The key idea of the proof is that a term [t] admits the same behavior as
    [let x = t in x]. Recall from chapter [Rules] the lemma
    [eta_same_triples] which asserts the equivalence of [t] and
    [let x = t in x]. *)

Parameter eta_same_triples : forall (t:trm) (x:var) H Q,
   triple t H Q <-> triple (trm_let x t x) H Q.

(** To discard a predicate from the postcondition of [t] if we only have at hand
    a rule for discarding predicates from preconditions, we replace [t] with
    [let x = t in x] and apply the discard rule after evaluating [t] but before
    returning the variable [x]. *)

Lemma triple_hgc_post_from_hgc_pre : forall t H Q,
  triple t H (Q \*+ \GC) ->
  triple t H Q.
Proof using.
  introv M. rewrite (eta_same_triples t "x"). applys triple_let.
  { applys M. }
  { intros v. simpl. applys triple_hgc_pre. applys triple_val. auto. }
Qed.

End FromPreToPostGC.

(* ================================================================= *)
(** ** Historical Notes *)

(** The seminal presentation of Separation Logic concerned a linear logic for a
    programming language with explicit deallocation. More recent works on
    Separation Logic for ML-style languages equipped with a garbage collector
    consider affine logics. For example, the original presentation of the Iris
    framework provides an affine entailment, for which [H ==> \[]] is always
    true. Follow-up work on Iris provides encodings for supporting linear
    resources, i.e., resources that cannot be dropped on the floor.

    The present chapter gives a presentation of Separation Logic featuring a
    customizable predicate [haffine] for controlling which resources should be
    treated as affine, and which ones should be treated as linear. This direct
    approach to controlling linearity was introduced in the context of CFML, in
    work by [Guéneau, Jourdan, Charguéraud, and Pottier 2019] (in Bib.v). *)

(* 2025-01-06 19:51 *)
