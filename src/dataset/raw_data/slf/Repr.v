(** * Repr: Representation Predicates *)

Set Implicit Arguments.
From SLF Require Import LibSepReference.
Import ProgramSyntax DemoPrograms.
From SLF Require Import Basic.
Open Scope liblist_scope.

Implicit Types n m : int.
Implicit Types p q s c : loc.
Implicit Types x : val.

(* ################################################################# *)
(** * First Pass *)

(** The previous chapter ([Basic]) covered simple programs that manipulate
    individual mutable cells. This chapter focuses on the specification and
    verification of programs manipulating mutable data structures like lists and
    trees. In Separation Logic, such data structures are specified using
    _representation predicates_.

    A representation predicate is a heap predicate that describes a mutable data
    structure. For example, the heap predicate [MList L p] describes a mutable
    linked list whose head cell is at location [p] and whose elements are
    described by the Coq list [L]. In this chapter, we will see how to define
    [MList] and how to use this predicate for specifying and verifying functions
    that operate on mutable linked lists. We will also study representation
    predicates for mutable trees, as well as for counter functions, which
    feature an internal state.

    As explained in the [Preface], this chapter, like all the following
    ones, is structured in three parts:

    - The _First Pass_ section presents the most important ideas only.
    - The _More Details_ section presents additional material explaining in more
      depth the meaning and the consequences of the key results. By default,
      readers would eventually read all this material.
    - The _Optional Material_ section contains more advanced material, for
      readers who can afford to invest more time in the topic.

    While going through proofs, we will introduce a few additional tactics.

    - [xpull] to extract pure facts and quantifiers from the LHS of [==>].
    - [xchange E] for exploiting a lemma [E] with a conclusion of the
      form [H1 ==> H2] or [H1 = H2].
    - [xchange <- E] for exploiting an entailment [H2 ==> H1] in the case
      [E] is a lemma with a conclusion of the form [H1 = H2].
    - [xchanges] is a shorthand for [xchange] followed with [xsimpl].
    - [xfun] to reason about function definitions.
    - [xtriple] to establish specifications for abstract functions.
    - [introv] (a TLC tactic) like [intros] but takes as arguments
      only the name of the hypotheses, not of all variables.
    - [rew_list] (a TLC tactic) to normalize list expressions.

    Furthermore, TLC tactics and most x-tactics may be followed with a star
    symbol to invoke [eauto]. For example, [xsimpl*] is a shorthand for
    [xsimpl; eauto]. The star symbol is used to make proof scripts more concise,
    yet exercises can all be solved without this feature. *)

(* ================================================================= *)
(** ** The List Representation Predicate *)

(** The implementation of mutable lists and trees involves the use of records.
    For simplicity, field names are represented as natural numbers. For example,
    to represent a list cell with a head and a tail field, we define [head] as
    the constant zero, and [tail] as the constant one. *)

Definition head : field := 0%nat.
Definition tail : field := 1%nat.

(** The heap predicate [p ~~~>`{ head := x; tail := q }] describes a record
    allocated at location [p], with a head field storing [x] and a tail field
    storing [q]. The arrow [~~~>] is provided by the framework for describing
    records. The notation [`{...}] is a handy notation for a list of pairs of
    field names and values of arbitrary types. (Further details on the
    formalization of records are presented in chapter [Records].)

    A mutable list consists of a chain of cells. Each cell stores a tail pointer
    that gives the location of the next cell in the chain. The last cell stores
    the [null] value in its tail field.

    The heap predicate [MList L p] describes a list whose head cell is at
    location [p] and whose elements are described by the list [L]. This
    predicate is defined recursively on the structure of [L].

    - If [L] is empty, then [p] is the null pointer.
    - If [L] is of the form [x::L'], then [p] is not null, the head field of
      [p] contains [x], and the tail field of [p] contains a pointer [q] such
      that [MList L' q] describes the tail of the list.

    This definition is formalized as follows. *)

Fixpoint MList (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | x::L' => \exists q, (p ~~~> `{ head := x; tail := q}) \* (MList L' q)
  end.

(* ================================================================= *)
(** ** Alternative Characterizations of [MList] *)

(** Carrying out proofs directly with [MList] can be slightly cumbersome, mainly
    due to Coq's limited support for re-folding definitions. We find it more
    practical to explicitly state equalities that paraphrase the definition of
    [MList]. There is one equality for the [nil] case and one for the [cons]
    case. *)

Lemma MList_nil : forall p,
  (MList nil p) = \[p = null].
Proof using. auto. Qed.

Lemma MList_cons : forall p x L',
  MList (x::L') p =
  \exists q, (p ~~~> `{ head := x; tail := q}) \* (MList L' q).
Proof using. auto. Qed.

(** In addition, it is also very useful in proofs to reformulate the definition
    of [MList L p] in the form of a case analysis on whether the pointer [p] is
    null or not. This corresponds to the programming pattern
    [if p == null then ... else ...]. This alternative characterization of
    [MList L p] asserts the following.

    - If [p] is null, then [L] is empty.
    - Otherwise, [L] decomposes as [x::L'], the head field of [p] contains [x],
      and the tail field of [p] contains a pointer [q] such that [MList L' q]
      describes the tail of the list. *)

(** The corresponding lemma, shown below, is stated using the
    [If P then X else Y] construction, which generalizes Coq's construction
    [if b then X else Y] to discriminate over a proposition [P] as opposed to a
    boolean value [b]. The [If] construct leverages classical logic; it is
    provided by the TLC library. The tactic [case_if] is convenient for
    performing the case analysis on whether [P] is true or false. *)

Lemma MList_if : forall (p:loc) (L:list val),
      (MList L p)
  ==> (If p = null
        then \[L = nil]
        else \exists x q L', \[L = x::L']
             \* (p ~~~> `{ head := x; tail := q}) \* (MList L' q)).
(** The proof is a bit technical: it may be skipped on a first reading. *)
Proof using. (* FILL IN HERE *) Admitted.

(** Note that the reciprocal entailment to the one stated in [MList_if] is also
    true, but we do not need it so we do not bother proving it here. In the rest
    of the course, we will never unfold the definition [MList], but only work
    with [MList_nil], [MList_cons], and [MList_if]. We therefore make the
    definition of [MList] opaque to prevent Coq from performing undesired
    simplifications. *)

Global Opaque MList.

(* ================================================================= *)
(** ** In-place Concatenation of Two Mutable Lists *)

(** The function [append] expects two arguments: a pointer [p1] to a nonempty
    list, and a pointer [p2] to another list, possibly empty. The function
    updates the last cell from the first list in such a way that its tail points
    to the head cell of [p2]. After this operation, the pointer [p1] points to a
    list that corresponds to the concatenation of the two input lists.

OCaml:

    let rec append p1 p2 =
      if p1.tail == null
        then p1.tail <- p2
        else append p1.tail p2
*)

Definition append : val :=
  <{ fix 'f 'p1 'p2 =>
       let 'q1 = 'p1`.tail in
       let 'b = ('q1 = null) in
       if 'b
         then 'p1`.tail := 'p2
         else 'f 'q1 'p2 }>.

(** The append function is specified and verified as shown below. The proof
    pattern is representative of that of many list-manipulating functions, so it
    is essential that you take the time to play through every step of this
    proof. Several exercises will require a very similar proof pattern. *)

Lemma triple_append : forall (L1 L2:list val) (p1 p2:loc),
  p1 <> null ->
  triple (append p1 p2)
    (MList L1 p1 \* MList L2 p2)
    (fun _ => MList (L1++L2) p1).
Proof using.
(** The TLC tactic [introv] is very convenient for providing explicit names for
    hypotheses without having to provide names for the variables already named
    in the lemma statement. *)
  introv N.
(** The induction principle provides a hypothesis for the tail of [L1]. The
    predicate [list_sub L1' L1] asserts that [L1] decomposes as [x::L1'] for
    some [x]. *)
  gen p1. induction_wf IH: list_sub L1. intros. xwp.
(** To begin the proof, we reveal the head cell of [p1], exploiting the
    assumption that [p1 <> null]. *)
  xchange (MList_if p1). case_if.
(** Using [xpull], we extract the existentially quantified variables: we let
    [q1] denote the tail of [p1], [x] the head element of [L1], and [L1'] the
    tail of [L1]. *)
  xpull.
(** The tactic [intros ->] is a shorthand for [intros E; rewrite E; clear E]. *)
  intros x q1 L1' ->.
(** We then reason about the if statement. *)
  xapp. xapp. xif; intros Cq1.
(** If [q1] is null, then [L1'] is empty. *)
  { xchange (MList_if q1). case_if. xpull.
    intros ->.
(** In this case, we reason about the assignment, then we fold back the head
    cell. To that end, we exploit the tactic [xchange <- MList_cons], which is
    similar to [xchange MList_cons] but exploits the equality asserted by
    [MList_cons] in the reverse direction. *)
    xapp. xchange <- MList_cons.
(** Above, the tactic [xchange] discharges the goal because the LHS, after the
    operation, matches the RHS. To see the details, change the line of script
    to: [xapp. eapply himpl_trans. xchange <- MList_cons. apply himpl_refl.] *)
    }
(** Otherwise, if [q1] is not null, we reason about the recursive call using the
    induction hypothesis; then we re-fold the head cell. *)
  { xapp. xchange <- MList_cons. }
Qed.

(* ================================================================= *)
(** ** Smart Constructors for Linked Lists *)

(** We next introduce two smart constructors for linked lists, called [mnil] and
    [mcons]. The operation [mnil()] creates an empty list. Its implementation
    simply returns the value [null]. Its specification asserts that the return
    value is a pointer [p] such that [MList nil p]. In the specification below,
    recall that [funloc p => H] is a notation for
    [fun (r:val) => \exists (p:loc), \[r = val_loc p] \* H]. *)

Definition mnil : val :=
  <{ fun 'u =>
       null }>.

(** Note: in theory, we could present [mnil] as a constant rather than as a
    function that takes unit as argument. However, viewing it as a function like
    all the other example programs helps keep the framework minimal. *)

Lemma triple_mnil :
  triple (mnil ())
    \[]
    (funloc p => MList nil p).
Proof using.
  xwp.
(** We are requested to prove that, under the empty precondition, the value
    [null] satisfies the postcondition
    [fun (r:val) => \exists (p:loc), \[r = val_loc p] \* (MList nil p)]. As the
    tactic [xval] shows, this is equivalent to proving that the precondition
    [\[]] entails [exists p, \[null = val_loc p] \* (MList nil p))]. *)
  xval.
(** To conclude the proof, it suffices to instantiate [p] with [null], and to
    argue that [MList nil null] can created out of thin air. This is indeed true
    because [MList nil null] is equivalent to [\[]]. The first step is to obtain
    an explicit statement of this equivalence, in the form of an hypothesis
    named [E]. By instantiating the lemma [MList_nil], which asserts that
    [forall p, MList nil p = \[p = null]], we obtain the equality
    [MList nil null = \[null = null]]. *)
  generalize (MList_nil null). intros E.
(** Then, we invoke [xchange <- E]. In exchange for proving [null = null], this
    tactic replaces the empty heap predicate [\[]] with [MList nil null]. *)
  xchange <- E. { auto. }
(** At this stage, the tactic [xsimpl] is able to automatically instantiate [p]
    with [null], and [auto] checks that [null = null]. *)
   xsimpl. auto.
Qed.

(** The proof above can be greatly shortened by using the tactic [xchanges],
    which is a shorthand for [xchange <- E] followed by [xsimpl]. In fact, we
    even use [xchanges* <- E], to invoke [xchanges <- E] followed by [eauto]. *)

Lemma triple_mnil' :
  triple (mnil ())
    \[]
    (funloc p => MList nil p).
Proof using. xwp. xval. xchanges* <- (MList_nil null). Qed.

#[global] Hint Resolve triple_mnil : triple.

(** Observe that the specification [triple_mnil] does not mention the [null]
    pointer anywhere. Hence, this specification abstracts away from the
    implementation details of how mutable lists are represented internally. *)

(** The operation [mcons x q] creates a fresh list cell, with [x] in the head
    field and [q] in the tail. Its implementation allocates and initializes a
    fresh record made of two fields. The allocation operation leverages the
    allocation construct written [`{ head := 'x; tail := 'q }] in the code. This
    construct is in fact a notation for a primitive operation called
    [val_new_hrecord_2]. The details of record constructions are explained in
    the chapter [Record]. There is no need to understand the details at
    this stage. *)

Definition mcons : val :=
  <{ fun 'x 'q =>
       `{ head := 'x; tail := 'q } }>.

(** The operation [mcons] admits two specifications. The first one says that it
    produces a record described with a record heap predicate. *)

Lemma triple_mcons : forall x q,
  triple (mcons x q)
    \[]
    (funloc p => p ~~~> `{ head := x ; tail := q }).

(** To prove this lemma, we need to know that the record allocation operation is
    in fact a notation for a call to [val_new_hrecord_2], hence we need to
    invoke a library lemma called [triple_new_hrecord_2] for reasoning about
    this call. (Don't worry: this proof pattern will not appear in exercises!)
    *)
Proof using. xwp. xapp triple_new_hrecord_2; auto. xsimpl*. Qed.

(** The second specification asserts that [mcons] can be used to extend a
    mutable list. It assumes that the argument [q] comes with a list
    representation of the form [Mlist q L], and it specifies that the function
    [mcons] produces the representation predicate [Mlist p (x::L)]. This second
    specification is derivable from the first one, by folding the representation
    predicate [MList] using the tactic [xchange]. *)

Lemma triple_mcons' : forall L x q,
  triple (mcons x q)
    (MList L q)
    (funloc p => MList (x::L) p).
Proof using.
  intros. xapp triple_mcons.
  intros p. xchange <- MList_cons. xsimpl*.
Qed.

(** In practice, this second specification is more often useful than the first
    one, hence we register it in the database for [xapp]. It remains possible to
    invoke [xapp triple_mcons] to exploit the first specification, where needed.
    *)

#[global] Hint Resolve triple_mcons' : triple.

(** In what follows, we consider several classic operations on mutable lists,
    each illustrating an idiomatic proof pattern. *)

(* ================================================================= *)
(** ** Copy Function for Lists *)

(** The function [mcopy] takes a mutable linked list and builds an independent
    copy of it, with the help of the functions [mnil] and [mcons].

OCaml:

    let rec mcopy p =
      if p == null
        then mnil ()
        else mcons (p.head) (mcopy p.tail)
*)

Definition mcopy : val :=
  <{ fix 'f 'p =>
       let 'b = ('p = null) in
       if 'b
         then mnil ()
         else
           let 'x = 'p`.head in
           let 'q = 'p`.tail in
           let 'q2 = ('f 'q) in
           mcons 'x 'q2 }>.

(** The precondition of [mcopy] requires a linked list described as
    [MList L p]. The postcondition asserts that the function returns a pointer
    [p'] and a list described as [MList L p'], in addition to the original list
    [MList L p]. The two lists are totally disjoint and independent, as captured
    by the separating conjunction symbol (the star). *)

Lemma triple_mcopy : forall L p,
  triple (mcopy p)
    (MList L p)
    (funloc p' => (MList L p) \* (MList L p')).

(** The proof structure is like the previous ones. While playing the script, try
    to spot the places where - [mnil] produces an empty list of the form
    [MList nil p'], - the recursive call produces a list of the form
    [MList L' q'], and - [mcons] produces a list of the form [MList (x::L') p'].
    *)
Proof using.
  intros. gen p. induction_wf IH: list_sub L.
  xwp. xapp. xchange MList_if. xif.
  { intros C.
(** Note that [C] is actually [val_loc p = val_loc null], and not simply
    [p = null]. This explains why a call to [subst] does nothing. If needed, use
    the TLC tactic, [inverts C] or [invert C] to exploit the equality. In this
    specific proof, though, we don't need that. *)
    case_if. (* automatically rules out the case [p <> null] *)
    xpull. intros E. subst L.
    xapp. xsimpl. { auto. }
    subst. xchange <- MList_nil. auto. }
  { intros C. case_if. (* automatically rules out [p = null] *)
    xpull. intros x q L' E. subst L.
    xapp. xapp. xapp. intros q'.
    xapp. intros p'.
    xchange <- MList_cons. xsimpl. auto. }
Qed.

(** A Coq expert would typically write the same proof script in a more compact
    fashion, as follows. Recall that the token [->] can be provided instead of a
    fresh name to indicate on-the-fly substitution, and that the star token
    after a tactic indicates a call to [eauto]. *)

Lemma triple_mcopy' : forall L p,
  triple (mcopy p)
    (MList L p)
    (funloc p' => (MList L p) \* (MList L p')).
Proof using.
  intros. gen p. induction_wf IH: list_sub L.
  xwp. xapp. xchange MList_if. xif; intros C; case_if; xpull.
  { intros ->. xapp. xsimpl*. subst. xchange* <- MList_nil. }
  { intros x q L' ->. xapp. xapp. xapp. intros q'.
    xapp. intros p'. xchange <- MList_cons. xsimpl*. }
Qed.

(* ================================================================= *)
(** ** Length Function for Lists *)

(** The function [mlength] computes the length of a mutable linked list.

OCaml:

    let rec mlength p =
      if p == null
        then 0
        else 1 + mlength p.tail
*)

Definition mlength : val :=
  <{ fix 'f 'p =>
       let 'b = ('p = null) in
       if 'b
         then 0
         else (let 'q = 'p`.tail in
               let 'n = 'f 'q in
               'n + 1) }>.

(** **** Exercise: 3 stars, standard, especially useful (triple_mlength)

    Prove the correctness of the function [mlength]. Hint: use the tactic
    [rew_list] to normalize list expressions -- in particular, to prove
    [length L' + 1 = length (x :: L')]. *)

Lemma triple_mlength : forall L p,
  triple (mlength p)
    (MList L p)
    (fun r => \[r = val_int (length L)] \* (MList L p)).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Alternative Length Function for Lists *)

(** In this section, we consider an alternative implementation of [mlength] that
    uses an auxiliary reference cell to keep track of the number of cells
    traversed so far. The list is traversed recursively, incrementing the
    contents of the reference once for every cell.

OCaml:

    let rec listacc c p =
      if p == null
        then ()
        else (incr c; listacc c p.tail)

    let mlength' p =
      let c = ref 0 in
      listacc c p;
      !c
*)

Definition acclength : val :=
  <{ fix 'f 'c 'p =>
       let 'b = ('p <> null) in
       if 'b then
         incr 'c;
         let 'q = 'p`.tail in
         'f 'c 'q
       end }>.

Definition mlength' : val :=
  <{ fun 'p =>
       let 'c = ref 0 in
       acclength 'c 'p;
       get_and_free 'c }>.

(** (Recall that [get_and_free] was defined in chapter [Basic]. *)

(** **** Exercise: 3 stars, standard, especially useful (triple_mlength')

    Prove the correctness of the function [mlength']. Hint: start by stating a
    lemma [triple_acclength] expressing the specification of the recursive
    function [acclength]. Make sure to generalize the appropriate variables
    before applying the well-founded induction tactic. Then complete the proof
    of the specification [triple_mlength'], using [xapp triple_acclength] to
    reason about the call to the auxiliary function. Recall that [rew_list] can
    be used to simplify [length (x :: L')] into [length L' + 1] and that [math]
    can be used to prove arithmetic equalities such as
    [(n + 1) + m = n + (m + 1)]. *)

(* FILL IN HERE *)

Lemma triple_mlength' : forall L p,
  triple (mlength' p)
    (MList L p)
    (fun r => \[r = val_int (length L)] \* (MList L p)).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Free Function for Lists *)

(** The operation [mfree] deallocates all the cells in a given list. Each cell
    consists of a record that can be deallocated using the primitive operation
    [delete]. The deallocation of a list is implemented by recursively
    traversing the list, invoking [delete] on each cell after reading its tail
    pointer.

OCaml:

    let rec mfree p =
      if p != null then begin
        let q = p.tail in
        delete p;
        mfree q
      end
*)

Definition mfree : val :=
  <{ fix 'f 'p =>
       let 'b = ('p <> null) in
       if 'b then
         let 'q = 'p`.tail in
         delete 'p;
         'f 'q
       end }>.

(** The precondition of [mfree] requires a full list [MList L p]. The
    postcondition is empty: the entire list is destroyed. *)

(** **** Exercise: 3 stars, standard, especially useful (Triple_mfree)

    Verify the function [mfree]. *)

Lemma triple_mfree : forall L p,
  triple (mfree p)
    (MList L p)
    (fun _ => \[]).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** In-Place Reversal Function for Lists *)

(** The function [mrev] takes as argument a pointer to a mutable list, and
    returns a pointer on the reverse list, that is, a list with elements in the
    reverse order. The cells from the input list are reused for constructing the
    output list: the operation is said to be "in place".

OCaml:

    let rec mrev_aux p1 p2 =
      if p2 == null
        then p1
        else (let p3 = p2.tail in
              p2.tail <- p1;
              mrev_aux p2 p3)

    let mrev p =
      mrev_aux null p
*)

Definition mrev_aux : val :=
  <{ fix 'f 'p1 'p2 =>
       let 'b = ('p2 = null) in
       if 'b
         then 'p1
         else (
           let 'p3 = 'p2`.tail in
           'p2`.tail := 'p1;
           'f 'p2 'p3) }>.

Definition mrev : val :=
  <{ fun 'p =>
       mrev_aux null 'p }>.

(** **** Exercise: 4 stars, standard, optional (triple_mrev)

    Prove the correctness of the functions [mrev_aux] and [mrev]. Hint: here
    again, start by stating a lemma [triple_mrev_aux] expressing the
    specification of the recursive function [mrev_aux]. Make sure to generalize
    the appropriate variables before applying the well-founded induction tactic.

    Then complete the proof of [triple_mrev], using [xapp triple_mrev_aux].
    Hint: in [triple_mrev], you will need to create an empty list out of thin
    air, using [xchange <- (MList_nil null)]. Also, make sure to call [rew_list]
    before [xsimpl]; otherwise [xsimpl] might not guess the right existential
    variable. The syntax [xsimpl v] is also available if you want to specify the
    witness [x] inside a goal of the form [H1 ==> (\exists x, H2)]. *)

(* FILL IN HERE *)

Lemma triple_mrev : forall L p,
  triple (mrev p)
    (MList L p)
    (funloc q => MList (rev L) q).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ################################################################# *)
(** * More Details *)

(** The rest of this chapter presents the formal verification of more advanced
    data structures and algorithms. The remaining chapters in the book explain
    how to construct the program verification framework that we have been using
    so far.

    The two aspects are completely orthogonal. Thus, if you have time and are
    interested in the practical aspects of program verification, you should
    complete the present chapter before moving on. On the other hand, if you are
    eager to dive into the construction of Separation Logic, then you may safely
    move on to the next chapter and come back to this later. *)

(* ================================================================= *)
(** ** A Stack Represented as a List and a Size *)

Module SizedStack.

(** In this section, we consider the implementation of a mutable stack featuring
    a constant-time access to the size of the stack. This stack structure
    consists of a 2-field record storing a pointer to a mutable linked list plus
    an integer recording the length of that list. The implementation includes a
    function [create] to allocate an empty stack, a function [sizeof] for
    reading the size, and functions [push], [top], and [pop] for manipulating
    the top of the stack.

OCaml:

    type 'a stack = {
      data : 'a list;
      size : int }

    let create () =
      { data = null;
        size = 0 }

    let sizeof s =
      s.size

    let push p x =
      s.data <- mcons x s.data;
      s.size <- s.size + 1

    let top s =
      let p = s.data in
      p.head

    let pop s =
      let p = s.data in
      let x = p.head in
      let q = p.tail in
      delete p;
      s.data <- q in
      s.size <- s.size - 1;
      x
*)

(** The constants [data] and [size] are introduced as identifiers for the record
    fields of the type ['a stack]. *)

Definition data : field := 0%nat.
Definition size : field := 1%nat.

(** The representation predicate for the stack takes the form [Stack L s], where
    [s] denotes the location of the record describing the stack and [L] denotes
    the list of items stored in the stack. The underlying mutable list is
    described as [MList L p], where [p] is the location [p] stored in the first
    field of the record. The definition of [Stack] is as follows. *)

Definition Stack (L:list val) (s:loc) : hprop :=
  \exists p, s ~~~>`{ data := p; size := length L } \* (MList L p).

(** Observe that the predicate [Stack] does not expose the location of the
    mutable list; this location is existentially quantified in the definition.
    It also does not expose the size of the stack, as this value can be obtained
    from [length L]. Let's start with the specification and verification of
    [create] and [sizeof]. *)

Definition create : val :=
  <{ fun 'u =>
      `{ data := null; size := 0 } }>.

Lemma triple_create :
  triple (create ())
    \[]
    (funloc s => Stack nil s).
Proof using.
  xwp. xapp triple_new_hrecord_2; auto. intros s.
  unfold Stack. xsimpl*. xchange* <- (MList_nil null).
Qed.

(** The [sizeof] operation returns the contents of the [size] field of a stack.
    *)

Definition sizeof : val :=
  <{ fun 'p =>
      'p`.size }>.

Lemma triple_sizeof : forall L s,
  triple (sizeof s)
    (Stack L s)
    (fun r => \[r = length L] \* Stack L s).
Proof using.
  xwp. unfold Stack. xpull. intros p. xapp. xsimpl*.
Qed.

(** The [push] operation extends the head of the list and increments the size
    field. *)

Definition push : val :=
  <{ fun 's 'x =>
       let 'p = 's`.data in
       let 'p2 = mcons 'x 'p in
       's`.data := 'p2;
       let 'n = 's`.size in
       let 'n2 = 'n + 1 in
       's`.size := 'n2 }>.

(** **** Exercise: 3 stars, standard, especially useful (triple_push)

    Prove the following specification for the [push] operation. *)

Lemma triple_push : forall L s x,
  triple (push s x)
    (Stack L s)
    (fun u => Stack (x::L) s).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** The [pop] operation extracts the element at the head of the list, updates
    the [data] field to the tail of the list and decrements the size field. *)

Definition pop : val :=
  <{ fun 's =>
       let 'p = 's`.data in
       let 'x = 'p`.head in
       let 'p2 = 'p`.tail in
       delete 'p;
       's`.data := 'p2;
       let 'n = 's`.size in
       let 'n2 = 'n - 1 in
       's`.size := 'n2;
       'x }>.

(** **** Exercise: 4 stars, standard, especially useful (triple_pop)

    Prove the following specification for the [pop] operation. Hint: You'll need
    to unfold the definition of [Stack] as in the proofs above, and at some
    point you'll want to destruct [L]. *)

Lemma triple_pop : forall L s,
  L <> nil ->
  triple (pop s)
    (Stack L s)
    (fun x => \exists L', \[L = x::L'] \* Stack L' s).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** The [top] operation extracts the element at the head of the list. *)

Definition top : val :=
  <{ fun 's =>
       let 'p = 's`.data in
       'p`.head }>.

(** **** Exercise: 2 stars, standard, optional (triple_top)

    Prove the following specification for the [top] operation. *)

Lemma triple_top : forall L s,
  L <> nil ->
  triple (top s)
    (Stack L s)
    (fun x => \exists L', \[L = x::L'] \* Stack L s).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End SizedStack.

(* ================================================================= *)
(** ** Formalization of the Tree Representation Predicate [MTree] *)

(** In this section, we generalize the ideas presented for linked lists to
    binary trees that store integer values in their nodes. Just as mutable lists
    are specified with respect to Coq's purely functional lists, mutable binary
    trees are specified with respect to Coq trees.

    Consider the following inductive definition of the type [tree]. A leaf is
    represented by the constructor [Leaf], and a node takes the form
    [Node n T1 T2], where [n] is an integer and [T1] and [T2] are its two
    subtrees. *)

Inductive tree : Type :=
  | Leaf : tree
  | Node : int -> tree -> tree -> tree.

Implicit Types T : tree.

(** In a program manipulating a mutable tree, an empty tree is represented using
    the [null] pointer, and a node is represented in memory using a three-cell
    record. The first field, "item", stores an integer. The other two fields,
    "left" and "right", store pointers to the left and right subtrees,
    respectively. *)

Definition item : field := 0%nat.
Definition left : field := 1%nat.
Definition right : field := 2%nat.

(** The heap predicate [p ~~~>`{ item := n; left := p1; right := p2 }] describes
    a record allocated at location [p], storing the integer [n] and the two
    pointers [p1] and [p2].

    The representation predicate [MTree T p], of type [hprop], asserts that the
    mutable tree structure with root at location [p] describes the logical tree
    [T]. The predicate is defined recursively on the structure of [T].

    - If [T] is a [Leaf], then [p] is the null pointer.
    - If [T] is a node [Node n T1 T2], then [p] is not null and at location
      [p] one finds a record with field contents [n], [p1] and [p2], with
      [MTree T1 p1] and [MTree T2 p2] describing the two subtrees. *)

Fixpoint MTree (T:tree) (p:loc) : hprop :=
  match T with
  | Leaf => \[p = null]
  | Node n T1 T2 => \exists p1 p2,
         (p ~~~>`{ item := n; left := p1; right := p2 })
      \* (MTree T1 p1)
      \* (MTree T2 p2)
  end.

(* ================================================================= *)
(** ** Alternative Characterization of [MTree] *)

(** As for [MList], it is very useful for proofs to state three lemmas that
    paraphrase the definition of [MTree]. The first two lemmas correspond to the
    folding/unfolding rules for leaves and nodes. *)

Lemma MTree_Leaf : forall p,
  (MTree Leaf p) = \[p = null].
Proof using. auto. Qed.

Lemma MTree_Node : forall p n T1 T2,
  (MTree (Node n T1 T2) p) =
  \exists p1 p2,
       (p ~~~>`{ item := n; left := p1; right := p2 })
    \* (MTree T1 p1) \* (MTree T2 p2).
Proof using. auto. Qed.

(** The third lemma reformulates [MTree T p] using a case analysis on whether
    [p] is the null pointer. This formulation matches the case analysis
    typically performed in the code of functions that operates on trees. *)

Lemma MTree_if : forall (p:loc) (T:tree),
      (MTree T p)
  ==> (If p = null
        then \[T = Leaf]
        else \exists n p1 p2 T1 T2, \[T = Node n T1 T2]
             \* (p ~~~>`{ item := n; left := p1; right := p2 })
             \* (MTree T1 p1) \* (MTree T2 p2)).
Proof using.
  intros. destruct T as [|n T1 T2].
  { xchange MTree_Leaf. intros M. case_if. xsimpl*. }
  { xchange MTree_Node. intros p1 p2.
    xchange hrecord_not_null. intros N. case_if. xsimpl*. }
Qed.

(** Beyond this point, the definition of [Mtree] not longer needs to be
    unfolded: we make it opaque. *)

Opaque MTree.

(* ================================================================= *)
(** ** Additional Tooling for [MTree] *)

(** For reasoning about recursive functions over trees, it is useful to exploit
    the well-founded order associated with "immediate subtrees". Concretely,
    [tree_sub T1 T] asserts that the tree [T1] is either the left or the right
    subtree of the tree [T]. This order may be exploited for verifying recursive
    functions over trees using the tactic [induction_wf IH: tree_sub T]. The
    relation [tree_sub] is defined as follows. *)

Inductive tree_sub : binary (tree) :=
  | tree_sub_1 : forall n T1 T2,
      tree_sub T1 (Node n T1 T2)
  | tree_sub_2 : forall n T1 T2,
      tree_sub T2 (Node n T1 T2).

Lemma tree_sub_wf : wf tree_sub.
Proof using.
  intros T. induction T; constructor; intros t' H; inversions~ H.
Qed.

#[global] Hint Resolve tree_sub_wf : wf.

(** For allocating fresh tree nodes as a 3-field record, we introduce the
    operation [mnode n p1 p2], defined and specified as follows. *)

Definition mnode : val :=
  val_new_hrecord_3 item left right.

(** A first specification of [mnode] describes the allocation of a record. *)

Lemma triple_mnode : forall n p1 p2,
  triple (mnode n p1 p2)
    \[]
    (funloc p => p ~~~> `{ item := n ; left := p1 ; right := p2 }).
Proof using. intros. apply triple_new_hrecord_3; auto. Qed.

(** A second specification, derived from the first, asserts that, when provided
    two subtrees [T1] and [T2] at locations [p1] and [p2], the operation
    [mnode n p1 p2] builds, at a fresh location [p], a tree described by
    [Mtree [Node n T1 T2] p]. Compared with the first specification, this second
    specification is said to "transfer ownership" of the two subtrees. *)

(** **** Exercise: 2 stars, standard, optional (triple_mnode')

    Prove the specification [triple_mnode'] for node allocation. Because this
    specification refines the previous specification [triple_mnode], the proof
    should begin with [xapp triple_mnode]. *)

Lemma triple_mnode' : forall T1 T2 n p1 p2,
  triple (mnode n p1 p2)
    (MTree T1 p1 \* MTree T2 p2)
    (funloc p => MTree (Node n T1 T2) p).
Proof using. (* FILL IN HERE *) Admitted.

#[global] Hint Resolve triple_mnode' : triple.

(** [] *)

(** Similarly to what we had done for [mnil], we could implement a function
    [mleaf] that returns the [null] pointer and derive a specification for it in
    terms of [MTree]. Instead, we will see through the next examples how one may
    directly reason about occurrences of [null] appearing in tree- manipulating
    code, using [xchange <- (MTree_Leaf null)] directly. *)

(* ================================================================= *)
(** ** Deep-Copy of a Tree *)

(** The operation [tree_copy] takes as argument a pointer [p] on a mutable tree
    and returns a fresh copy of that tree. It is defined in a similar way to the
    function [mcopy] for lists.

OCaml:

    let rec tree_copy p =
      if p = null
        then null
        else mnode p.item (tree_copy p.left) (tree_copy p.right)
*)

Definition tree_copy :=
  <{ fix 'f 'p =>
       let 'b = ('p = null) in
       if 'b then null else (
         let 'n = 'p`.item in
         let 'p1 = 'p`.left in
         let 'p2 = 'p`.right in
         let 'q1 = 'f 'p1 in
         let 'q2 = 'f 'p2 in
         mnode 'n 'q1 'q2
      ) }>.

(** **** Exercise: 3 stars, standard, especially useful (triple_tree_copy)

    Prove the specification of [tree_copy]. Hint: you'll need to use
    [xchange <- (MTree_Leaf null)] twice. *)

Lemma triple_tree_copy : forall p T,
  triple (tree_copy p)
    (MTree T p)
    (funloc q => (MTree T p) \* (MTree T q)).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Computing the Sum of the Items in a Tree *)

(** The operation [mtreesum] takes as argument the location [p] of a mutable
    tree, and it returns the sum of all the integers stored in the nodes of that
    tree. The implementation traverses the tree, using an auxiliary reference
    cell to maintain the sum of all the items visited so far.

OCaml:

    let rec treeacc c p =
      if p <> null then (
        c := !c + p.item;
        treeacc c p.left;
        treeacc c p.right)

    let mtreesum p =
      let c = ref 0 in
      treeacc c p;
      !c
*)

Definition treeacc : val :=
  <{ fix 'f 'c 'p =>
       let 'b = ('p <> null) in
       if 'b then
         let 'm = ! 'c in
         let 'x = 'p`.item in
         let 'm2 = 'm + 'x in
         'c := 'm2;
         let 'p1 = 'p`.left in
         'f 'c 'p1;
         let 'p2 = 'p`.right in
         'f 'c 'p2
       end }>.

Definition mtreesum : val :=
  <{ fun 'p =>
       let 'c = ref 0 in
       treeacc 'c 'p;
       get_and_free 'c }>.

(** The specification of [mtreesum] is expressed in terms of the Coq function
    [treesum], which computes the sum of the node items stored in a logical
    tree. This operation is defined by recursion over the tree. *)

Fixpoint treesum (T:tree) : int :=
  match T with
  | Leaf => 0
  | Node n T1 T2 => n + treesum T1 + treesum T2
  end.

(** **** Exercise: 4 stars, standard, optional (triple_mtreesum)

    Prove the correctness of the function [mtreesum]. Hint: to begin with, state
    and prove the specification lemma [triple_treeacc]. *)

(* FILL IN HERE *)

Lemma triple_mtreesum : forall T p,
  triple (mtreesum p)
    (MTree T p)
    (fun r => \[r = treesum T] \* (MTree T p)).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Verification of a Counter Function with Local State *)

(** This section is concerned with the verification of counter functions, which
    feature internal, mutable state. A counter function [f] is a function that,
    each time it is called, returns the next integer. Concretely, the first call
    to [f()] returns [1], the second call returns [2], the third returns [3],
    and so on.

    A counter function can be implemented using a reference cell, [p], that
    stores the integer last returned by the counter. Initially, the contents of
    the cell is zero. Each time the counter function is called, the contents is
    increased by one unit, and the new value of the contents is returned to the
    caller.

    The function [create_counter] produces a fresh counter function. Concretely,
    [create_counter()] returns a counter function [f] that is independent from
    any other previously existing counter function.

OCaml:

    let create_counter () =
       let p = ref 0 in
       (fun () -> (incr p; !p))
*)

Definition create_counter : val :=
  <{ fun 'u =>
       let 'p = ref 0 in
       (fun_ 'u => (incr 'p; !'p)) }>.

(** In this section, we present two specifications for counter functions. The
    first specification is the most direct, but it exposes the existence of the
    reference cell, revealing implementation details about the counter function.
    The second specification is more abstract, hiding from the client the
    internal representation of the counter using an abstract representation
    predicate. *)

(** Let us begin with the simple, direct specification. The proposition
    [CounterSpec f p] asserts that [f] is a counter function [f] whose internal
    state is stored in a reference cell at location [p]. Thus, invoking [f] in a
    state [p ~~> m] updates the state to [p ~~> (m+1)] and produces the output
    value [m+1]. *)

Definition CounterSpec (f:val) (p:loc) : Prop :=
  forall m, triple (f ())
                    (p ~~> m)
                    (fun r => \[r = m+1] \* p ~~> (m+1)).

Implicit Type f : val.

(** The function [create_counter] creates a fresh counter. Its precondition is
    empty. Its postcondition asserts that the function [f] being returned
    satisfies [CounterSpec f p] and the output state contains a cell [p ~~> 0]
    for some existentially quantified location [p]. *)

Lemma triple_create_counter :
  triple (create_counter ())
    \[]
    (fun f => \exists p, (p ~~> 0) \* \[CounterSpec f p]).

(** Observe how the postcondition that appears in the triple above refers to
    [CounterSpec], which itself involves a triple. In other words, a triple
    appears nested inside another triple. In technical terms, we are leveraging
    the "impredicativity of triples", which holds as a consequence of the
    "impredicativity of predicates" in the logic of Coq. *)

(** The proof involves the use of a new tactic, called [xfun], for reasoning
    about local function definitions. Here, [xfun] gives us the hypothesis [Hf]
    that specifies the code of [f]. This hypothesis is of the form:
    [forall v H' Q', (PRE H' CODE B POST Q') -> triple (f v) H' Q'], where [B]
    denotes the code of the body of the function [f] instantiated on the
    argument [v], and where [H'] and [Q'] denote arbitrary pre- and
    postconditions. Exploiting this assumption enables the user to subsequently
    derive triples about the local function [f], by reasoning about the code of
    the [f], just in the same way as when the user invokes [xwp] for reasoning
    about a top-level function. *)
Proof using.
  xwp. xapp. intros p.
  xfun. intros f Hf.
  xsimpl.
  { intros m.
    (* To reason about the call to the function [f], we can exploit [Hf], either
       explicitly by calling [apply Hf], or automatically by calling [xapp]. *)
    xapp.
    xapp. xapp. xsimpl. auto. }
Qed.

(** Let us move on to the presentation of more abstract specifications. Their
    purpose is to hide from the client the existence of the reference cell used
    to represent the internal state of the counter functions. To that end, we
    introduce the heap predicate [IsCounter f n], which relates a function [f],
    its current value [n], and the piece of memory state involved in the
    implementation of this function. This piece of memory is of the form
    [p ~~> n], for some location [p], such that [CounterSpec f p] holds. *)

Definition IsCounter (f:val) (n:int) : hprop :=
  \exists p, p ~~> n \* \[CounterSpec f p].

(** Using [IsCounter], we can reformulate the specification of [create_counter]
    with a postcondition asserting that the output function [f] is described by
    the heap predicate [IsCounter f 0]. *)

Lemma triple_create_counter_abstract :
  triple (create_counter ())
    \[]
    (fun f => IsCounter f 0).
(** This lemma is the same as [triple_create_counter], except that the reference
    cell [p] is no longer explicitly mentioned in the postcondition. In other
    words, the address of the reference cell [p] used internally by the counter
    becomes hidden from the user. *)
Proof using. unfold IsCounter. apply triple_create_counter. Qed.

(** Next, we reformulate the specification of a call to a counter function. A
    call to [f()], in a state satisfying [IsCounter f n], produces a state
    satisfying [IsCounter f (n+1)], and returns [n+1]. *)

(** **** Exercise: 4 stars, standard, especially useful (triple_apply_counter_abstract)

    Prove the abstract specification for a counter function. You will need to
    begin the proof using the tactic [xtriple], for turning goal into a form on
    which other x-tactics can be invoked. Then, use [xpull] to extract facts
    from the precondition. *)

Lemma triple_apply_counter_abstract : forall f n,
  triple (f ())
    (IsCounter f n)
    (fun r => \[r = n+1] \* (IsCounter f (n+1))).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

Opaque IsCounter.

(** Finally, let us illustrate how a client might work with counter functions.

OCaml:

    let test_counter () =
       let c1 = create_counter () in
       let c2 = create_counter () in
       let n1 = c1() in
       let n2 = c2() in
       let n3 = c1() in
       n2 + n3
*)

Definition test_counter : val :=
  <{ fun 'u =>
       let 'c1 = create_counter () in
       let 'c2 = create_counter () in
       let 'n1 = 'c1 () in
       let 'n2 = 'c2 () in
       let 'n3 = 'c1 () in
       'n2 + 'n3 }>.

(** **** Exercise: 2 stars, standard, optional (triple_test_counter)

    Prove the example function manipulating abstract counters. In the
    specification below, the heap predicate [\exists H, H] corresponds to the
    two counters, which we currently have no way of deallocating. The necessary
    mechanism for garbage collection will be introduced later in chapter
    [Affine].

    Hint: use [xapp triple_create_counter_abstract] and
    [xapp triple_apply_counter_abstract] to invoke the specifications. *)

Lemma triple_test_counter :
  triple (test_counter ())
    \[]
    (fun r => \[r = 3] \* (\exists H, H)).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ################################################################# *)
(** * Optional Material *)

(** The verification of higher-order functions, and of their interaction with
    mutable state, was a formidable challenge prior to the introduction of
    Separation Logic. The rest of this chapter illustrates how to reason about
    imperative, higher-order programs. *)

(* ================================================================= *)
(** ** Specification of a Higher-Order Repeat Operator *)

(** Consider the higher-order iterator [repeat]: a call to [repeat f n] executes
    [n] times the call [f()].

OCaml:

    let rec repeat f n =
      if n > 0 then (f(); repeat f (n-1))
*)

Definition repeat : val :=
  <{ fix 'g 'f 'n =>
       let 'b = ('n > 0) in
       if 'b then
         'f ();
         let 'n2 = 'n - 1 in
         'g 'f 'n2
       end }>.

(** For simplicity, let us assume for now [n >= 0]. The specification of
    [repeat n f] can be expressed in terms of an invariant, named [I],
    describing the state in between every two calls to [f]. We assume that the
    initial state satisfies [I 0]. Moreover, we assume that, for every index [i]
    in the range from [0] (inclusive) to [n] (exclusive), a call [f()] can
    execute in a state that satisfies [I i] and produce a state that satisfies
    [I (i+1)]. The specification below asserts that, under these two
    assumptions, after the [n] calls to [f()], the final state satisfies [I n].
    The specification takes the form:

      n >= 0 ->
      Hypothesis_on_f ->
      triple (repeat f n)
        (I 0)
        (fun u => I n)

    where [Hypothesis_on_f] is a proposition that captures the following
    specification:

      forall i,
      0 <= i < n ->
      triple (f ())
        (I i)
        (fun u => I (i+1))

    The complete specification of [repeat n f] is thus as shown below. *)

Lemma triple_repeat : forall (I:int->hprop) (f:val) (n:int),
  n >= 0 ->
  (forall i, 0 <= i < n ->
    triple (f ())
      (I i)
      (fun u => I (i+1))) ->
  triple (repeat f n)
    (I 0)
    (fun u => I n).
Proof using.
  introv Hn Hf.

(** To establish this specification, we carry out a proof by induction over a
    generalized specification, covering the case where there remains [m]
    iterations to perform, for any value of [m] between [0] and [n] inclusive.

      forall m, 0 <= m <= n ->
      triple (repeat f m)
        (I (n-m))
        (fun u => I n))

    We use the TLC tactics [cuts], a variant of [cut], to state show that the
    generalized specification entails the statement of [triple_repeat]. *)
  cuts G: (forall m, 0 <= m <= n ->
    triple (repeat f m)
      (I (n-m))
      (fun u => I n)).
  { replace 0 with (n - n). { eapply G. math. } { math. } }
(** We then carry a proof by induction: during the execution, the value of [m]
    decreases step by step down to [0]. *)
  intros m. induction_wf IH: (downto 0) m. intros Hm.
  xwp. xapp. xif; intros C.
(** We reason about the call to [f] *)
  { xapp. { math. } xapp.
(** We next reason about the recursive call. *)
    xapp. { math. } { math. }
(** We need to exploit an arithmetic equality. We do so using [math_rewrite],
    which is a convenient TLC tactic to assert an equality proved by the [math]
    tactic, then immediately invoke [rewrite] with this equality. *)
    math_rewrite ((n - m) + 1 = n - (m - 1)). xsimpl. }
(** Finally, when [m] reaches zero, we check that we obtain [I n]. *)
  { xval. math_rewrite (n - m = n). xsimpl. }
Qed.


(* ================================================================= *)
(** ** Specification of an Iterator on Mutable Lists *)

(** The operation [miter] takes as argument a function [f] and a pointer [p] on
    a mutable list and invokes [f] on each of the items stored in that list.

OCaml:

    let rec miter f p =
      if p <> null then (f p.head; miter f p.tail)
*)

Definition miter : val :=
  <{ fix 'g 'f 'p =>
       let 'b = ('p <> null) in
       if 'b then
         let 'x = 'p`.head in
         'f 'x;
         let 'q = 'p`.tail in
         'g 'f 'q
       end }>.

(** The specification of [miter] follows the same structure as that of the
    function [repeat] from the previous section, with two main differences. The
    first difference is that the invariant is expressed not in terms of an index
    [i] ranging from [0] to [n], but in terms of a prefix of the list [L] being
    traversed. This prefix ranges from [nil] to the full list [L]. The second
    difference is that the operation [miter f p] requires in its precondition,
    in addition to [I nil], the description of the mutable list [MList L p].
    This predicate is returned in the postcondition, unchanged, reflecting the
    fact that the iteration process does not alter the contents of the list. *)

(** **** Exercise: 5 stars, standard, especially useful (triple_miter)

    Prove the correctness of [triple_miter]. *)

Lemma triple_miter : forall (I:list val->hprop) L (f:val) p,
  (forall x L1 L2, L = L1++x::L2 ->
    triple (f x)
      (I L1)
      (fun u => I (L1++(x::nil)))) ->
  triple (miter f p)
    (MList L p \* I nil)
    (fun u => MList L p \* I L).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** For exploiting the specification [triple_miter] to reason about a call to
    [miter], it is necessary to provide an invariant [I] of type
    [list val -> hprop], that is, of the form [fun (K:list val) => ...]. This
    invariant, which generally cannot be inferred automatically, should describe
    the state at the point where the iteration has traversed a prefix [K] of the
    list [L]. Concretely, for reasoning about a call to [miter], one should
    exploit the tactic [xapp (triple_miter (fun K => ...))]. An example appears
    next. *)

(* ================================================================= *)
(** ** Computing the Length of a Mutable List using an Iterator *)

(** The function [mlength_using_miter] computes the length of a mutable list by
    iterating over that list a function that increments a reference cell once
    for every item.

OCaml:

    let mlength_using_miter p =
      let c = ref 0 in
      miter (fun x -> incr c) p;
      !c
*)

(** **** Exercise: 4 stars, standard, especially useful (triple_mlength_using_miter)

    Prove the correctness of [mlength_using_iter]. Hint: as explained earlier,
    use [xfun; intros f Hf] for reasoning about the function definition, then
    use [xapp] for reasoning about a call to [f]. Use of [xlet] is optional. *)

Definition mlength_using_miter : val :=
  <{ fun 'p =>
       let 'c = ref 0 in
       let 'f = (fun_ 'x => incr 'c) in
       miter 'f 'p;
       get_and_free 'c }>.

Lemma triple_mlength_using_miter : forall p L,
  triple (mlength_using_miter p)
    (MList L p)
    (fun r => \[r = length L] \* MList L p).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** ** Factorial Function in Continuation-Passing Style*)

(** This section and the next one present examples of functions involving
    "continuations". As a warm-up, we first consider consider a function that
    does not involve any mutable state.

    The function [cps_facto_aux n k] performs a call to the function [k] on the
    value [facto n]. The function [cps_facto n] computes the value of [facto n]
    by applying [cps_facto_aux] to the identity function.

OCaml:

    let rec cps_facto_aux n k =
      if n <= 1
        then k 1
        else cps_facto_aux (n-1) (fun r -> k (n * r))

    let cps_facto n =
      cps_facto_aux n (fun r -> r)
*)

Definition cps_facto_aux : val :=
  <{ fix 'f 'n 'k =>
       let 'b = 'n <= 1 in
       if 'b
         then 'k 1
         else let 'k2 = (fun_ 'r => let 'r2 = 'n * 'r in 'k 'r2) in
              let 'n2 = 'n - 1 in
              'f 'n2 'k2 }>.

Definition cps_facto : val :=
  <{ fun 'n  =>
       let 'k = (fun_ 'r => 'r) in
       cps_facto_aux 'n 'k }>.

Import Facto.

(** **** Exercise: 4 stars, standard, optional (triple_cps_facto_aux)

    Verify [cps_facto_aux]. Hints: To set up the induction, use the usual
    pattern [induction_wf IH: (downto 0) n]. To reason about the function
    definition, use [xfun]. To reason about the recursive call, you'll need to
    exploit the induction hypothesis, called [IH], which universally quantifies
    over a function [F] of type [int->int]. To do so, use the syntax
    [xapp (>> IH (fun a => ..))]. The function provided should describe the
    behavior of the continuation [k2] that appears in the code. For the
    mathematical reasoning, use the same pattern as in the proof of [factorec],
    applying the tactics [rewrite facto_init] and [rewrite (@facto_step n)]. *)

Lemma triple_cps_facto_aux : forall (n:int) (k:val) (F:int->int),
  n >= 0 ->
  (forall (a:int), triple (k a) \[] (fun r => \[r = F a])) ->
  triple (cps_facto_aux n k)
    \[]
    (fun r => \[r = F (facto n)]).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (triple_cps_facto)

    Verify [cps_facto]. Hint: use the syntax [xapp (>> triple_cps_append_aux F)]
    to provide the function [F] that describes the behavior of the identity
    continuation. *)

Lemma triple_cps_facto : forall n,
  n >= 0 ->
  triple (cps_facto n)
    \[]
    (fun r => \[r = facto n]).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** In-Place Concatenation Function in Continuation-Passing Style *)

(** This section presents an example verification of a function involving
    "continuations". The function [cps_append] is similar to the function
    [append] presented previously: it also performs in-place concatenation of
    two lists. The main difference is that it is implemented using an auxiliary
    recursive function in "continuation-passing style" (CPS).

    The presentation of [cps_append p1 p2] is also slightly different: this
    operation returns a pointer [p3] that describes the head of the result of
    the concatenation. In the general case, [p3] is equal to [p1], but if [p1]
    is the null pointer, meaning that the first list is empty, then [p3] is
    equal to [p2].

    The code of [cps_append] involves the auxiliary function
    [cps_append_aux p1 p2 k], which invokes the continuation function [k] on the
    result of concatenating the lists at locations [p1] and [p2]. Its code
    appears at first quite puzzling, because the recursive call is performed
    inside the continuation. It takes a good drawing and at least a couple
    minutes to figure out how the function works.

OCaml:

    let rec cps_append_aux p1 p2 k =
      if p1 == null
        then k p2
        else cps_append_aux p1.tail p2 (fun r => (p1.tail <- r); k p1)

    let cps_append p1 p2 =
      cps_append_aux p1 p2 (fun r => r)
*)

Definition cps_append_aux : val :=
  <{ fix 'f 'p1 'p2 'k =>
       let 'b = ('p1 = null) in
       if 'b
         then 'k 'p2
         else
           let 'q1 = 'p1`.tail in
           let 'k2 = (fun_ 'r => ('p1`.tail := 'r; 'k 'p1)) in
           'f 'q1 'p2 'k2 }>.

Definition cps_append : val :=
  <{ fun 'p1 'p2 =>
      let 'f = (fun_ 'r => 'r) in
      cps_append_aux 'p1 'p2 'f }>.

(** The goal is to establish the following specification for [cps_append].

  Lemma triple_cps_append : forall (L1 L2:list val) (p1 p2:loc),
    triple (cps_append p1 p2)
      (MList L1 p1 \* MList L2 p2)
      (funloc p3 => MList (L1++L2) p3).

   If you are interested in the challenge of solving a 6-star exercise, then try
   to prove the above specification without reading any further. If, however,
   you are only looking for a 5-star exercise, keep reading. *)

(** **** Exercise: 5 stars, standard, optional (triple_cps_append_aux)

    The specification of [cps_append_aux] involves an hypothesis describing the
    behavior of the continuation [k]. For this function, and more generally for
    code in CPS form, we cannot easily leverage the frame property, thus we need
    to quantify explicitly over a heap predicate [H] for describing the "rest of
    the state". Prove that specification. Hint: you can use the syntax
    [xapp (>> IH H')] to instantiate the induction hypothesis [IH] on a specific
    heap predicate [H']. *)

Lemma triple_cps_append_aux : forall H Q (L1 L2:list val) (p1 p2:loc) (k:val),
  (forall (p3:loc), triple (k p3) (MList (L1 ++ L2) p3 \* H) Q) ->
  triple (cps_append_aux p1 p2 k)
    (MList L1 p1 \* MList L2 p2 \* H)
    Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard, optional (triple_cps_append)

    Verify [cps_append]. Hint: use the syntax [@triple_cps_append_aux H' Q'] to
    specialize the specification of the auxiliary function to specific pre- and
    post-conditions. *)

Lemma triple_cps_append : forall (L1 L2:list val) (p1 p2:loc),
  triple (cps_append p1 p2)
    (MList L1 p1 \* MList L2 p2)
    (funloc p3 => MList (L1++L2) p3).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Historical Notes *)

(** The representation predicate for lists appears in the seminal publications
    on Separation Logic: the notes by Reynolds from the summer 1999, updated the
    next summer [Reynolds 2000] (in Bib.v), and the paper by
    [O’Hearn, Reynolds, and Yang 2001] (in Bib.v). The function [cps_append] was
    proposed in Reynolds's article as an open challenge for verification.
    Zhaozhong Ni and Zhong Shao presented the framework XCAP, which was the
    first to support reasoning on embedded code pointers [Ni, Shao 2006] (in Bib.v).
    Their proof, carried on a 23-line assembly program, consists of 1500+ lines
    of Coq. Subsequently, Charguéraud presented a concise proof for a high-level
    implementation of the [cps_append] function, essentially equivalent to the
    formalization presented above [Charguéraud 2011] (in Bib.v).

    The specification of higher-order iterators requires higher-order Separation
    Logic. Being embedded in the higher-order logic of Coq, the Separation Logic
    that we work with is inherently higher-order. Further information on the
    history of higher-order Separation Logic for higher-order programs may be
    found in the companion course notes, linked in the [Preface]. *)

(* 2024-12-26 10:22 *)
