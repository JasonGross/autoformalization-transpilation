(** * WPsem: Semantics of Weakest Preconditions *)

Set Implicit Arguments.
From SLF Require Export Rules.

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types v w : val.
Implicit Types p : loc.
Implicit Types h : heap.
Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.

(* ################################################################# *)
(** * First Pass *)

(** In this chapter, we introduce the notion of "weakest precondition" for
    Separation Logic triples, written [wp t Q].

    The intention is for [wp t Q] to be a heap predicate (of type [hprop]) such
    that [H ==> wp t Q] iff [triple t H Q]. *)

(** The benefits of introducing weakest preconditions are twofold.

      - The use of [wp] greatly reduces the number of structural rules required,
        thus reducing the number of tactics required for carrying out proofs in
        practice;

      - The predicate [wp] will serve as guidelines for setting up (in the next
        chapter) a "characteristic formula generator", which is the key
        ingredient at the heart of the CFML tool. *)

(** The high-level picture is:

       - (1) wp and triples are equivalent presentations of the same thing.

       - (2) wp has practical benefits, reducing the number of reasoning rules
             and tactics that are needed, by a fair amount.

       - (3) specifications of functions remain more intuitive to read with
             triples.
*)

(** The chapter presents:

      - the notion of weakest precondition, as captured by [wp],
      - the reformulation of structural rules in [wp]-style, and
      - the reformulation of reasoning rules in [wp]-style.

    Throughout the chapter, we aim to establish reasoning rules in [wp]-style
    directly with respect to the semantics defined by [eval], as opposed to
    deriving [wp]-style rules from the reasoning rules on triples proved in the
    previous chapters. The interest is to present the proofs involved in the
    most direct construction of a program verification framework based on [wp].
    *)

(** The "optional material" section presents several equivalent definitions for
    [wp], alternative proofs for deriving [wp]-style reasoning rules, as well as
    a presentation of "Texan triples", which reformulate function specifications
    using magic wands instead of triples. *)

(* ================================================================= *)
(** ** Definition of Weakest Preconditions *)

(** Consider a term [t] and a postcondition [Q].

    The expression [wp t Q] is called the "weakest precondition" of the term [t]
    with respect to the postcondition [Q].

    It is a heap predicate such that, for any heap predicate [H], the entailment
    [H ==> wp t Q] holds if and only if [triple t H Q] does. *)

(** The concept of [wp] might seem a bit mysterious at this point. Hopefully it
    will become clearer in the rest of this chapter. *)

(** The first critical observation is that [wp] is in fact nothing but a
    reformulation of the predicate [eval]. To see why, recall the definition of
    [triple t H Q].

    Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
      forall s, H s -> eval s t Q.

    By definition, the predicate [wp] should be such that [H ==> wp t Q] is
    equivalent to [triple t H Q]. But [H ==> wp t Q] unfolds to
    [forall s, H s -> wp t Q s]. If we compare [forall s, H s -> eval s t Q]
    with [forall s, H s -> wp t Q s], we see that [wp t Q s] should match
    [eval s t Q]. In other words, [wp t Q] should correspond to
    [fun s => eval s t Q]. *)

Definition wp (t : trm) (Q : val->hprop) : hprop :=
  fun s => eval s t Q.

(** Remark: the reader may wonder why [wp] is not just defined to *be* [eval],
    by simply modifying our earlier definition of [eval] to take its arguments
    in a different order. Certainly, it could be done. However, the benefits of
    identifying [wp] and [eval] are limited, and there are two orthogonal
    motivations for not following that route.

    Firstly, the omni-big-step predicate [eval s t Q] is devised as an immediate
    generalization of the big-step predicate [eval s t s' v], by generalizing
    from out final configuration [(s',v)] to a set [Q] of final configurations.
    From the perspective of a semantics, we view the configuration [(s,t)] as an
    input and the set [Q] as an output, thus it would be fairly awckward to
    write [eval t Q s], with the input state [s] taken as last argument.

    Secondly, we are looking here at a simple Separation Logic where heap
    predicates are predicates over the physical state. They have type
    [heap->Prop], where [heap] corresponds exactly to the type of of a state
    [s]. More advanced Separation Logic feature something known as "ghost state"
    (used, e.g., to represent invariants associated with locks). In such logics,
    heap predicates are predicates over both the physical and the ghost state.
    In other words, the type [heap] in general may consist of more than just a
    state [s]. The point of this discussion is that, for more advanced
    Separation Logics, [wp] is more than just [eval]. Thus, there is no reason
    to attempt to identify the two. *)

(** As intended, the entailment [H ==> wp t Q] holds if and only if
    [triple t H Q] does.*)

Lemma wp_equiv : forall t H Q,
  (H ==> wp t Q) <-> (triple t H Q).
Proof using.
  iff M. { introv Hs. applys M Hs. } { introv Hs. applys M Hs. }
Qed.

(** There are several other ways of defining [wp]. As we show near the end of
    this chapter, they are all equivalent. The definition above is the one that
    leads to the simplest proofs for the reasoning rules. Indeed, reasoning
    rules must be proved correct with respect to the semantics, and the
    semantics is captured by the predicate [eval]. *)

(** Let us now explain why [wp] is called a "weakest precondition". First,
    [wp t Q] is always a _valid_ precondition for [t] with respect to the
    postcondition [Q]. *)

Lemma wp_pre : forall t Q,
  triple t (wp t Q) Q.
Proof using. intros. rewrite <- wp_equiv. applys himpl_refl. Qed.

(** Second, [wp t Q] is the "weakest" of all valid preconditions for [t] and
    [Q], in the sense that, for any other valid precondition [H] (i.e., such
    that [triple t H Q] holds), it is the case that [H] entails [wp t Q]. *)

Lemma wp_weakest : forall t H Q,
  triple t H Q ->
  H ==> wp t Q.
Proof using. introv M. rewrite wp_equiv. applys M. Qed.

(* ================================================================= *)
(** ** Structural Rules in Weakest-Precondition Style *)

(** We next present reformulations of the frame rule and the rule of consequence
    in _weakest-precondition style_.

    Given a term [t] and a postcondition [Q], we say that "[t] produces [Q]" if
    [t] terminates and produces a output value and an output state that,
    together, satisfy the postcondition [Q]. *)

(* ----------------------------------------------------------------- *)
(** *** The Frame Rule *)

(** The frame rule for [wp] asserts that [(wp t Q) \* H] entails
    [wp t (Q \*+ H)]. This statement can be read as follows: if you own both a
    piece of state satisfying [H] and a piece of state in which the execution of
    [t] produces [Q], then you own a piece of state in which the execution of
    [t] produces [Q \*+ H], that is, produces both [Q] and [H]. *)

Lemma wp_frame : forall t H Q,
  (wp t Q) \* H ==> wp t (Q \*+ H).

(** The lemma is proved by exploiting the frame property on [eval]. (It could
    also be derived using [wp_equiv] and [triple_frame], but the point here is
    to derive properties of [wp] without mentioning [triple].) *)

Proof using.
  intros. unfold wp. intros h HF.
  lets (h1&h2&M1&M2&MD&MU): hstar_inv HF.
  subst. applys eval_conseq.
  { applys eval_frame M1 MD. }
  { xsimpl. intros h' ->. applys M2. }
Qed.

(** Looking at the entaileent expressed by [wp_frame], the reader may wander
    whether the reverse entailment holds, that is, if [wp t (Q \*+ H)] entails
    [(wp t Q) \* H]. This reverse entailment does not hold in general. Consider
    the following counterexample term [t], defined as [let p = ref 1 in 0]. This
    term returns [0] and produces a dangling reference cell that can be
    described as [\exists p, (p ~~> 1)]. Let [Q] be [fun r => \[r = 0]] and [H]
    be [\exists p, (p ~~> 1)]. The term [t], executed in the empty heap,
    terminates with postcondition [Q \*+ H]. Therefore, the predicate
    [wp t (Q \*+ H)] holds of the empty heap. However, [(wp t Q) \* H] does not
    hold of the empty heap, because [H], which describes one memory cell, cannot
    be carved out of the empty heap. We conclude that [wp t (Q \*+ H)] does not
    entail [(wp t Q) \* H] in general. *)

(** The connection between [wp_frame] and the rule [triple_frame] is not be
    totally obvious. Recall the statement of the frame rule for triples.

    triple t H1 Q ->
    triple t (H1 \* H) (Q \*+ H)

    Let us replace the pattern [triple t H Q] with the pattern [H ==> wp t Q],
    following the characteristic equivalence [wp_equiv]. We obtain the statement
    shown below. *)

Lemma wp_frame_trans : forall t H1 Q H,
  H1 ==> wp t Q ->
  (H1 \* H) ==> wp t (Q \*+ H).

(** If we exploit transitivity of entailment to eliminate [H1], then we obtain
    exactly [wp_frame], as illustrated by the proof script below. *)

Proof using. introv M. xchange M. applys* wp_frame. Qed.

(* ----------------------------------------------------------------- *)
(** *** The Rule of Consequence *)

(** The rule of consequence for [wp] is a covariance property: it asserts that
    [wp t Q] is covariant in [Q]. In other words, if [Q1] entails [Q2], then
    [wp t Q1] entails [wp t Q2]. *)

Lemma wp_conseq : forall t Q1 Q2,
  Q1 ===> Q2 ->
  wp t Q1 ==> wp t Q2.
Proof using. unfold wp. introv M. intros s Hs. applys* eval_conseq. Qed.

(** Here again, the connection with the corresponding reasoning rule for triples
    is not totally obvious. Recall the statement of the rule of consequence.

    triple t H1 Q1 ->
    H2 ==> H1 ->
    Q1 ===> Q2 ->
    triple t H2 Q2

    Let us replace [triple t H Q] with [H ==> wp t Q] to obtain the following
    statement: *)

Lemma wp_conseq_trans : forall t H1 H2 Q1 Q2,
  H1 ==> wp t Q1 ->
  H2 ==> H1 ->
  Q1 ===> Q2 ->
  H2 ==> wp t Q2.

(** If we exploit transitivity of entailment to eliminate [H1] and [H2], then we
    obtain exactly [wp_conseq], as illustrated by the proof script below. *)

Proof using.
  introv M WH WQ. xchange WH. xchange M. applys wp_conseq WQ.
Qed.

(* ----------------------------------------------------------------- *)
(** *** The Extraction Rules *)

(** The extraction rules [triple_hpure] and [triple_hexists] have no specific
    counterpart with the [wp] presentation. Indeed, in a weakest-precondition
    style presentation, the extraction rules for triples correspond exactly to
    the extraction rules for entailment.

    To see why, consider the rule [triple_hpure]. *)

Parameter triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.

(** Replacing [triple t H Q] with [H ==> wp t Q] yields the following: *)

Lemma triple_hpure_with_wp : forall t H Q (P:Prop),
  (P -> (H ==> wp t Q)) ->
  (\[P] \* H) ==> wp t Q.

(** This implication is just a special case of the extraction lemma for pure
    facts on the left on an entailment, [himpl_hstar_hpure_l]:

    (P -> (H ==> H')) ->
    (\[P] \* H) ==> H'.
*)

Proof using. introv M. applys himpl_hstar_hpure_l M. Qed.

(** Similar reasoning applies to the extraction rule for existentials. *)

(* ----------------------------------------------------------------- *)
(** *** The Ramified Frame Rule *)

(** Recall the ramified frame rule: *)

Parameter triple_ramified_frame : forall H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  triple t H Q.

(** The ramified frame rule in weakest-precondition style, named [wp_ramified],
    admits a concise statement and subsumes all the other structural rules of
    Separation Logic. Its very elegant statement is as follows. *)

Lemma wp_ramified : forall t Q1 Q2,
  (wp t Q1) \* (Q1 \--* Q2) ==> (wp t Q2).
Proof using. intros. applys wp_conseq_frame. applys qwand_cancel. Qed.

(** The following reformulation of [wp_ramified] can be more practical to
    exploit in practice, because it applies to any goal of the form
    [H ==> wp t Q]. *)

Lemma wp_ramified_trans : forall t H Q1 Q2,
  H ==> (wp t Q1) \* (Q1 \--* Q2) ->
  H ==> (wp t Q2).
Proof using. introv M. xchange M. applys wp_ramified. Qed.

(** **** Exercise: 3 stars, standard, especially useful (wp_conseq_of_wp_ramified)

    Prove that [wp_conseq] is derivable from [wp_ramified]. Concretely, prove
    [wp_conseq] using only [wp_ramified] or [wp_ramified_trans], plus properties
    of the entailment relation. *)

Lemma wp_conseq_of_wp_ramified : forall t Q1 Q2,
  Q1 ===> Q2 ->
  wp t Q1 ==> wp t Q2.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (wp_frame_of_wp_ramified)

    Prove that [wp_frame] is derivable from [wp_ramified]. Concretely, prove
    [wp_frame] using only [wp_ramified] plus properties of entailment. *)

Lemma wp_frame_of_wp_ramified : forall t H Q,
  (wp t Q) \* H ==> wp t (Q \*+ H).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Reasoning Rules for Terms in Weakest-Precondition Style *)

(* ----------------------------------------------------------------- *)
(** *** Values *)

(** Recall the rule [triple_val] which establishes a triple for a value [v]. *)

Parameter triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.

(** If we rewrite this rule in [wp] style, we obtain this:

    H ==> Q v ->
    H ==> wp (trm_val v) Q.

    By exploiting transitivity of entailment, we can eliminate [H]. We obtain
    the following rule: If you own a state satisfying [Q v], then you own a
    state from which the evaluation of the value [v] produces [Q]. *)

Lemma wp_val : forall v Q,
  Q v ==> wp (trm_val v) Q.
Proof using. unfold wp. intros. intros h K. applys* eval_val. Qed.

(* ----------------------------------------------------------------- *)
(** *** Sequences *)

(** Recall the reasoning rule for a sequence [trm_seq t1 t2]. *)

Parameter triple_seq : forall t1 t2 H Q H1,
  triple t1 H (fun _ => H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.

(** Replacing [triple t H Q] with [H ==> wp t Q] gives this:

      H ==> (wp t1) (fun _ => H1) ->
      H1 ==> (wp t2) Q ->
      H ==> wp (trm_seq t1 t2) Q.

    This entailment holds for any [H] and [H1]. Let us specialize it to
    [H1 := (wp t2) Q] and [H := (wp t1) (fun v => (wp t2) Q)].

    This leads us to the following rule: If you own a state from which the
    evaluation of [t1] produces a state from which the evaluation of [t2]
    produces the postcondition [Q], then you own a state from which the
    evaluation of the sequence [t1;t2] produces [Q]. *)

Lemma wp_seq : forall t1 t2 Q,
  wp t1 (fun v => wp t2 Q) ==> wp (trm_seq t1 t2) Q.
Proof using. unfold wp. intros. intros h K. applys* eval_seq. Qed.

(* ----------------------------------------------------------------- *)
(** *** Let-Bindings *)

(** Recall the reasoning rule for a term [trm_let x t1 t2]. *)

Parameter triple_let : forall x t1 t2 Q1 H Q,
  triple t1 H Q1 ->
  (forall v1, triple (subst x v1 t2) (Q1 v1) Q) ->
  triple (trm_let x t1 t2) H Q.

(** The rule of [trm_let x t1 t2] is very similar to that for [trm_seq], the
    only difference being the substitution of [x] by [v] in [t2], where [v]
    denotes the result of [t1]. *)

Lemma wp_let : forall x t1 t2 Q,
  wp t1 (fun v1 => wp (subst x v1 t2) Q) ==> wp (trm_let x t1 t2) Q.
Proof using. unfold wp. intros. intros h K. applys* eval_let. Qed.

(* ----------------------------------------------------------------- *)
(** *** Functions *)

(** Recall the reasoning rule for a term [trm_fun x t1], which evaluates to the
    value [val_fun x t1]. *)

Parameter triple_fun : forall x t1 H Q,
  H ==> Q (val_fun x t1) ->
  triple (trm_fun x t1) H Q.

(** The rule for functions follows exactly the same pattern as for values. *)

Lemma wp_fun : forall x t Q,
  Q (val_fun x t) ==> wp (trm_fun x t) Q.
Proof using. unfold wp. intros. intros h K. applys* eval_fun. Qed.

(** A similar rule holds for the evaluation of a recursive function. *)

Lemma wp_fix : forall f x t Q,
  Q (val_fix f x t) ==> wp (trm_fix f x t) Q.
Proof using. unfold wp. intros. intros h K. applys* eval_fix. Qed.

(* ----------------------------------------------------------------- *)
(** *** Conditionals *)

(** Recall the reasoning rule for a term [triple_if b t1 t2]. *)

Parameter triple_if : forall b t1 t2 H Q,
  triple (if b then t1 else t2) H Q ->
  triple (trm_if (val_bool b) t1 t2) H Q.

(** Replacing [triple] using [wp] entailments yields

    H ==> wp (if b then t1 else t2) Q ->
    H ==> wp (trm_if (val_bool b) t1 t2) Q

    A necessary and sufficient condition to prove a proposition of the form
    [forall H, (H ==> H1) -> (H ==> H2)] is [H1 ==> H2]. Indeed, if we
    instantiate [H] with [H1], we have [(H1 ==> H1) -> (H1 ==> H2)], thus we
    deduce [H1 ==> H2]. Reciprocally, if we have [H1 ==> H2] and [H ==> H1],
    then by the transitivity property [himpl_trans], we deduce [H ==> H2].

    Therefore, the previous entailment simplifies to:

    wp (if b then t1 else t2) Q ==> wp (trm_if (val_bool b) t1 t2) Q.

    This is the wp-style reasoning rule for conditionals. *)

Lemma wp_if : forall b t1 t2 Q,
  wp (if b then t1 else t2) Q ==> wp (trm_if (val_bool b) t1 t2) Q.
Proof using. unfold wp. intros. intros h K. applys* eval_if. Qed.

(** Equivalently, the rule may be stated with the conditional around the calls
    to [wp t1 Q] and [wp t2 Q]. *)

(** **** Exercise: 1 star, standard, optional (wp_if')

    Prove the alternative statement of rule [wp_if], either from [wp_if] or
    directly from [eval_if]. *)

Lemma wp_if' : forall b t1 t2 Q,
  (if b then (wp t1 Q) else (wp t2 Q)) ==> wp (trm_if b t1 t2) Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Rule For Function Applications *)

(** Recall the reasoning rule for an application [(val_fun x t1) v2]. *)

Parameter triple_app_fun : forall x v1 v2 t1 H Q,
  v1 = val_fun x t1 ->
  triple (subst x v2 t1) H Q ->
  triple (trm_app v1 v2) H Q.

(** The corresponding [wp] rule is: *)

Lemma wp_app_fun : forall x v1 v2 t1 Q,
  v1 = val_fun x t1 ->
  wp (subst x v2 t1) Q ==> wp (trm_app v1 v2) Q.
Proof using. unfold wp. intros. intros h K. applys* eval_app_fun. Qed.

(** A similar rule holds for the application of a recursive function. *)

Lemma wp_app_fix : forall f x v1 v2 t1 Q,
  v1 = val_fix f x t1 ->
  wp (subst x v2 (subst f v1 t1)) Q ==> wp (trm_app v1 v2) Q.
Proof using. unfold wp. intros. intros h K. applys* eval_app_fix. Qed.

(* ################################################################# *)
(** * More Details *)

(* ================================================================= *)
(** ** Combined Structural Rule *)

(** Recall the combined consequence-frame rule for [triple]. *)

Parameter triple_conseq_frame : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.

(** Let us reformulate this rule using [wp], replacing [triple t H Q] with
    [H ==> wp t Q]. *)

(** **** Exercise: 2 stars, standard, especially useful (wp_conseq_frame_trans)

    Prove the combined structural rule in [wp] style. Hint: exploit
    [wp_conseq_trans] and [wp_frame]. *)

Lemma wp_conseq_frame_trans : forall t H H1 H2 Q1 Q,
  H1 ==> wp t Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  H ==> wp t Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** The combined structural rule for [wp] can actually be stated in a more
    concise way. The rule reads as follows: If you own a state from which the
    execution of [t] produces (a result and a state satisfying) [Q1] and you
    also own [H]; and if, furthermore, you can trade the combination of [Q1] and
    [H] against [Q2]; then you own a piece of state from which the execution of
    [t] produces [Q2]. *)

(** **** Exercise: 2 stars, standard, especially useful (wp_conseq_frame)

    Prove the concise version of the combined structural rule in [wp] style.
    (Many proofs are possible.) *)

Lemma wp_conseq_frame : forall t H Q1 Q2,
  Q1 \*+ H ===> Q2 ->
  (wp t Q1) \* H ==> (wp t Q2).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** Let us reformulate the rule [wp_conseq_frame] using a magic wand. The
    premise [Q1 \*+ H ===> Q2] can be rewritten as [H ==> (Q1 \--* Q2)]. By
    replacing [H] with [Q1 \--* Q2] in the conclusion of [wp_conseq_frame], we
    obtain the ramified rule for [wp].

    Lemma wp_ramified : forall t Q1 Q2,
      (wp t Q1) \* (Q1 \--* Q2) ==> (wp t Q2).

    This explaination suggests how one might have come up with the statement of
    the ramified frame rule. *)

(* ################################################################# *)
(** * Optional Material *)

(* ================================================================= *)
(** ** Weakest Preconditions Derived from Triples, a First Route *)

Module WpFromTriple.

(** The lemma [wp_equiv] captures the characteristic property of [wp], that is,
    [(H ==> wp t Q) <-> (triple t H Q)]. The predicate [wp] can be defined in
    terms of [eval], like [triple]. Interestingly, [wp] may also be defined in
    terms of [triple]. The idea is to define [wp t Q] as the predicate
    [\exists H, H \* \[triple t H Q]], which, reading literally, is satisfied by
    "any" heap predicate [H] which is a valid precondition for a triple for the
    term [t] and the postcondition [Q]. *)

Definition wp_1 (t:trm) (Q:val->hprop) : hprop :=
  \exists (H:hprop), H \* \[triple t H Q].

(** **** Exercise: 3 stars, standard, especially useful (wp_equiv_1)

    Prove that the alternative definition [wp_1] satisfies the characteristic
    equivalence for weakest preconditions. Hint: use the consequence rule and
    the extraction rules. *)

Lemma wp_equiv_1 : forall t H Q,
  (H ==> wp_1 t Q) <-> (triple t H Q).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End WpFromTriple.

(* ================================================================= *)
(** ** Weakest Preconditions Derived From Triples, a Second Route *)

Module WpFromTriple2.

(** The concrete definition for [wp] given above is expressed in terms of
    Separation Logic combinators. In contrast to this "high level" definition,
    there exists a more "low level" definition, expressed directly as a function
    over heaps. In this alternative definition, the heap predicate [wp t Q] is
    defined as a predicate that holds of a heap [h] if and only if the execution
    of [t] starting in exactly the heap [h] produces the post-condition [Q]. The
    latter statement is formally captured as [triple t (fun h' => h' = h) Q].
    The low-level definition of [wp] is thus as shown below. *)

Definition wp_2 (t:trm) (Q:val->hprop) : hprop :=
  fun (h:heap) => triple t (fun h' => (h' = h)) Q.

(** **** Exercise: 4 stars, standard, optional (wp_equiv_2)

    Prove that the low-level definition [wp_2] also satisfies the characteristic
    equivalence [H ==> wp Q <-> triple t H Q]. Hint: exploit the lemma
    [triple_named_heap] which was established as an exercise in the chapter
    [Triples]. *)

Lemma wp_equiv_2 : forall t H Q,
  (H ==> wp_2 t Q) <-> (triple t H Q).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End WpFromTriple2.

(* ================================================================= *)
(** ** Equivalent Characterizations of [wp] *)

(** First, we establish that the equivalence [(triple t H Q) <-> (H ==> wp t Q)]
    defines a unique predicate [wp]. In other words, all possible definitions of
    [wp] are equivalent to each another. Thus, it really does not matter which
    concrete definition of [wp] we consider: they are all equivalent.
    Concretely, assume two predicates [wp1] and [wp2] to both satisfy the
    characteristic equivalence. We prove that they are equal. *)

Lemma wp_unique : forall wp1 wp2,
  (forall t H Q, (triple t H Q) <-> (H ==> wp1 t Q)) ->
  (forall t H Q, (triple t H Q) <-> (H ==> wp2 t Q)) ->
  wp1 = wp2.
Proof using.
  introv M1 M2. applys fun_ext_2. intros t Q. applys himpl_antisym.
  { rewrite <- M2. rewrite M1. auto. }
  { rewrite <- M1. rewrite M2. auto. }
Qed.

(** Second, we establish that the property of "being the weakest precondition"
    also uniquely characterizes the definition of [wp]. This property is the
    conjunction of two facts: [wp t Q] must be a valid precondition for a triple
    involving [t] and [Q]; and [wp t Q] must be entailed by any valid
    precondition of a triple involving [t] and [Q]. These two facts correspond
    to [wp_pre] and [wp_weakest]. *)

(** **** Exercise: 2 stars, standard, especially useful (wp_equiv_iff_wp_pre_and_wp_weakest)

    Prove that the conjunction of the properties [wp_pre] and [wk_weakest] is
    equivalent to the property [wp_equiv]. *)

Lemma wp_equiv_iff_wp_pre_and_wp_weakest : forall wp',
  (   (forall t Q, triple t (wp' t Q) Q) (* [wp_pre] *)
   /\ (forall t H Q, triple t H Q -> H ==> wp' t Q)) (* [wp_weakest] *)
  <->
  (forall t H Q, H ==> wp' t Q <-> triple t H Q). (* [wp_equiv] *)
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Texan Triples *)

(** In this section, we show that specification triples can be presented in a
    different style using weakest preconditions. This style has appeared under
    the name "Texan triples" in certain work related to the Iris framework. The
    main motivation is to slighly simplify the implementation of the tactic
    [xapp]. The main drawback is that it makes specifications, one could argue,
    slightly less easy to read. For this reason, users of the Iris framework
    usually stick to the standard triple notation in their publications. Despite
    the readability issue, it may be interesting for the reader to be aware of
    the possibility of stating specifications directly using [wp], as there
    might be useful applications of this technique in certain contexts. *)

Module TexanTriples.

(* ----------------------------------------------------------------- *)
(** *** 1. An Example *)

(** Consider the specification triple for allocation. *)

Parameter triple_ref : forall v,
  triple (val_ref v)
    \[]
    (funloc p => p ~~> v).

(** This specification may be equivalently reformulated in the form of an
    entailment, as shown below. Note that we purposely leave an empty heap
    predicate at the front to indicate where the precondition, if it were not
    empty, would go in the reformulation. *)

Parameter wp_ref : forall Q v,
  \[] \* (\forall p, p ~~> v \-* Q (val_loc p)) ==> wp (val_ref v) Q.

(** In what follows, we describe a chain of transformations that can take us
    from the triple form to the [wp] form, and we establish the reciprocal.
    Afterwards, we will formalize the general pattern of the translation from a
    triple to a "texan triple", that is, to a wp-based specification. *)

(** By replacing [triple t H Q] with [H ==> wp t Q], the specification
    [triple_ref] can be reformulated as follows. *)

Lemma wp_ref_0 : forall v,
  \[] ==> wp (val_ref v) (funloc p => p ~~> v).
Proof using. intros. rewrite wp_equiv. applys triple_ref. Qed.

(** We wish to cast the RHS in the form [wp (val_ref v) Q] for an abstract
    postcondition [Q]. To that end, we reformulate the above statement by
    including a magic wand relating the postcondition [(funloc p => p ~~> v)]
    with [Q]. *)

Lemma wp_ref_1 : forall Q v,
  ((funloc p => p ~~> v) \--* Q) ==> wp (val_ref v) Q.
Proof using. intros. xchange (wp_ref_0 v). applys wp_ramified. Qed.

(** This statement can be made slightly more readable by unfolding the
    definition of the magic wand for postconditions. Doing so amounts to
    quantifying explicitly on the result, named [r]. *)

Lemma wp_ref_2 : forall Q v,
  (\forall r,     (\exists p, \[r = val_loc p] \* p ~~> v) \-* Q r)
              ==> wp (val_ref v) Q.
Proof using. intros. applys himpl_trans wp_ref_1. xsimpl. Qed.

(** Interestingly, the variable [r], which is equal to [val_loc p], can now be
    substituted away, further increasing readability. We obtain the
    specification of [val_ref] in "Texan triple style". *)

Lemma wp_ref_3 : forall Q v,
  (\forall p, (p ~~> v) \-* Q (val_loc p)) ==> wp (val_ref v) Q.
Proof using.
  intros. applys himpl_trans_r wp_ref_2. xsimpl. intros ? p ->.
  xchange (hforall_specialize p).
Qed.

(* ----------------------------------------------------------------- *)
(** *** 2. The General Pattern *)

(** Most specification triples can be cast in the form:
    [triple t H (fun r => exists x1 .. xN, \[r = v] \* H')]. In such a
    specification:

    - the value [v] may depend on the [xi] variables,
    - the heap predicate [H'] may depend on [r] and the [xi],
    - the number of existentials [xi] may vary, possibly be zero,
    - the equality [\[r = v]] may be removed if no pure fact is needed
      about [r].

    Such a specification triple of the form
    [triple t H (fun r => exists x1 xN, \[r = v] \* H'] can be be reformulated
    as the Texan triple: [(\forall x1 xN, H \-* Q v) ==> wp t Q].

    We next formalize the equivalence between the two presentations, for the
    specific case where the specification involves a single auxiliary variable,
    named [x]. The statement below makes it explicit that [v] may depend on [x],
    and that [H] may depend on [r] and [x]. *)

Lemma texan_triple_equiv : forall t H A (Hof:val->A->hprop) (vof:A->val),
      (triple t H (fun r => \exists x, \[r = vof x] \* Hof r x))
  <-> (forall Q, H \* (\forall x, Hof (vof x) x \-* Q (vof x)) ==> wp t Q).
Proof using.
  intros. rewrite <- wp_equiv. iff M.
  { intros Q. xchange M. applys wp_ramified_trans.
    xsimpl. intros r x ->.
    xchange (hforall_specialize x). }
  { applys himpl_trans_r M. xsimpl~. }
Qed.

(* ----------------------------------------------------------------- *)
(** *** 3. Further Examples *)

Section WpSpecRef.

(** The wp-style specifications of [ref], [get], and [set] are presented next.
    *)

Lemma wp_get : forall v p Q,
  (p ~~> v) \* (p ~~> v \-* Q v) ==> wp (val_get p) Q.
Proof using.
  intros. rewrite wp_equiv. applys triple_conseq_frame.
  { applys triple_get. } { applys himpl_refl. } { xsimpl. intros ? ->. auto. }
Qed.

Lemma wp_set : forall v w p Q,
  (p ~~> v) \* (\forall r, p ~~> w \-* Q r) ==> wp (val_set p w) Q.
Proof using.
  intros. rewrite wp_equiv. applys triple_conseq_frame.
  { applys triple_set. } { applys himpl_refl. }
  { intros r. xchange (hforall_specialize r). xsimpl. }
Qed.

Lemma wp_free : forall v p Q,
  (p ~~> v) \* (\forall r, Q r) ==> wp (val_free p) Q.
Proof using.
  intros. rewrite wp_equiv. applys triple_conseq_frame.
  { applys triple_free. } { applys himpl_refl. }
  { intros r. xchange (hforall_specialize r). }
Qed.

(** Alternatively, the specifications of [set] and [free] may advertize that the
    output value is the unit value. *)

Parameter triple_set' : forall w p v,
  triple (val_set p w)
    (p ~~> v)
    (fun r => \[r = val_unit] \* p ~~> w).

Lemma wp_set' : forall v w p Q,
  (p ~~> v) \* (p ~~> w \-* Q val_unit) ==> wp (val_set p w) Q.
Proof using.
  intros. rewrite wp_equiv. applys triple_conseq_frame.
  { applys triple_set'. }
  { applys himpl_refl. }
  { xsimpl. intros ? ->. auto. }
Qed.

Parameter triple_free' : forall p v,
  triple (val_free p)
    (p ~~> v)
    (fun r => \[r = val_unit]).

Lemma wp_free' : forall v w p Q,
  (p ~~> v) \* (Q val_unit) ==> wp (val_free p) Q.
Proof using.
  intros. rewrite wp_equiv. applys triple_conseq_frame.
  { applys triple_free'. }
  { applys himpl_refl. }
  { xsimpl. intros ? ->. auto. }
Qed.

End WpSpecRef.

(* ----------------------------------------------------------------- *)
(** *** 4. Exercise *)

(** Let us put to practice the use of a Texan triple on a different example.
    Recall the function [incr] and its specification (from [Hprop.v]). *)

Parameter incr : val.

Parameter triple_incr : forall (p:loc) (n:int),
  triple (incr p)
    (p ~~> n)
    (fun v => \[v = val_unit] \* (p ~~> (n+1))).

(** **** Exercise: 3 stars, standard, especially useful (wp_incr)

    State a Texan triple for [incr] as a lemma called [wp_incr], then prove this
    lemma from [triple_incr]. *)

(* FILL IN HERE *)

(** [] *)

End TexanTriples.

(* ================================================================= *)
(** ** Historical Notes *)

(** The idea of weakest precondition was introduced by [Dijstra 1975] (in Bib.v) in
    his seminal paper "Guarded Commands, Nondeterminacy and Formal Derivation of
    Programs". Weakest preconditions provide a reformulation of Floyd-Hoare
    logic. Numerous practical verification tools leverage weakest preconditions,
    e.g. ESC/Java, Why3, Boogie, Spec#, etc.

    In the context of Separation Logic in proof assistants, the Iris framework
    (https://iris-project.org/), developed since 2015, prevasively exploits
    weakest preconditions to state reasoning rules. The developers of Iris and
    VST have advocated for this rule. The ramified frame rule was integrated in
    CFML 2.0 in 2018. *)

(* 2025-01-06 19:51 *)
