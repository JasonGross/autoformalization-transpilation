(** * WPgen: Weakest Precondition Generator *)

Set Implicit Arguments.
From SLF Require Import WPsem.

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types v : val.
Implicit Types h : heap.
Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.

(* ################################################################# *)
(** * First Pass *)

(** The previous chapter introduced a predicate called [wp] to describe the
    weakest precondition of a term [t] with respect to a given postcondition
    [Q]. *)

(** The weakest precondition [wp] was characterized by the equivalence
    [H ==> wp t Q] iff [triple t H Q]. We proved "wp-style" reasoning rules,
    such as:

    wp t1 (fun r => wp t2 Q) ==> wp (trm_seq t1 t2) Q

    In this chapter, we introduce a function, called [wpgen], to _compute_ the
    weakest precondition of a term. *)

(** The value of [wpgen t Q] is defined recursively over the structure of the
    term [t], and it computes a formula that is logically equivalent to
    [wp t Q]. The fundamental difference between [wp] and [wpgen] is that,
    whereas [wp t Q] is a predicate that we can reason about by applying
    reasoning rules, [wpgen t Q] is a predicate that we can reason about simply
    by _unfolding_ its definition. (This sentence will probably make more sense
    to the reader later on in the chapter.)

    Another key difference between [wp] and [wpgen] is that the formulae
    produced by [wpgen] no longer refer to program syntax. In particular, all
    program variables involved in a term [t] in a statement of the form [wp t Q]
    are replaced with Coq variables when computing [wpgen t Q]. The benefit of
    eliminating program variables is that formulae produced by [wpgen] can be
    manipulated without the need to simplify substitutions of the form
    [subst x v t2]. Instead, the beta reduction mechanism of Coq will
    automatically perform substitutions for Coq variables.

    The reader might have encountered the term "weakest precondition generator"
    in the past. Such generators take as input a program annotated with all
    function specifications and loop invariants and produce a set of proof
    obligations that need to be checked in order to conclude that the code
    indeed satisfies its logical annotations. In contrast, the weakest
    preconditions computed by [wpgen] apply to a piece of code independent of
    any specification or invariant. More precisely, the computation of
    [wpgen t Q] treats the postcondition [Q] as an abstract variable.

    At a high level, [wpgen] is a key ingredient for smoothing the user
    experience of conducting interactive proofs in Separation Logic. The
    x-tactics presented in the first two chapters of the course were built on
    top of [wpgen]. The matter of the present chapter is to show:

    - how to define [wpgen t Q] as a recursive function in Coq,
    - how to integrate support for the frame rule in this definition,
    - how to carry out practical proofs using [wpgen].

  The rest of the "first pass" section gives a high-level tour of the steps of
  the construction of [wpgen]. The formal definitions and the set up of
  x-tactics follow in the "more details" section. The treatment of local
  functions is presented in the "optional material" section.

  This chapter is probably the most technical of the course. The reader who
  finds it hard to follow the entire chapter may safely jump to the next chapter
  at any point after the "first pass" section. *)

(* ================================================================= *)
(** ** The Basic Structure of [wpgen] *)

(** As first approximation, [wpgen t Q] is defined as a recursive function that
    pattern matches on its argument [t], and produces an appropriate heap
    predicate in each case. The definitions somewhat mimic the reasoning rules
    of [wp]. Let us show the pattern of the definition and comment it
    afterwards.

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_val v => Q v
      | trm_var x => \[False]
      | trm_app v1 v2 => \exists H, H \* \[triple t H Q]
      | trm_let x t1 t2 => wpgen t1 (fun v => wpgen (subst x v t2) Q)
      ...
      end.
*)
(** Recall from the previous chapter that the rule [wp_val] asserts that [Q v]
    entails [wp (trm_val v) Q]. Well, [wpgen (trm_val v) Q] is defined as [Q v].

    Likewise, recall that the rule [wp_let] asserts that
    [wp t1 (fun v => wp (subst x v t2) Q)] entails [wp (trm_let x t1 t2) Q].
    Well, the definition of [wpgen] is such that [wpgen (trm_let x t1 t2) Q] is
    defined to be [wpgen t1 (fun v => wpgen (subst x v t2) Q)], that is, the
    same expression as in [wp_let] only with [wp] replaced by [wpgen].

    An interesting case is [wgen (trm_var x) Q]. There are no rules on [wp] to
    reason about variables, because they correspond to stuck terms. To reflect
    the fact that [wgen (trm_var x) Q] cannot be derived, we define it as
    [\[False]].

    The last key case is that of function calls. Consider a term [t] that
    consists of a function application [trm_app v1 v2]. How should we define
    [wpgen (trm_app t1 t2) Q]? We need to define it to be a heap predicate, call
    it [H], such that the function call [trm_app t1 t2] admits [H] as
    precondition and [Q] as postcondition. In other words, the definition of
    [wpgen (trm_app t1 t2) Q] should consist of a heap predicate [H] such that
    [triple t H Q] holds. We do not know what this [H] should be, so we simply
    quantify it existentially. This suggests why the definition of
    [wpgen (trm_app t1 t2) Q] should be [\exists H, H \* \[triple t H Q]]. *)

(** To obtain the actual definition of [wpgen], we need to refine the above
    definition in four steps. *)

(* ================================================================= *)
(** ** Step 1: [wpgen] as a Recursive Function over Terms *)

(** In a first step, we modify the definition in order to make it structurally
    recursive. Indeed, in the above the recursive call [wpgen (subst x v t2)] is
    not made on a strict subterm of [trm_let x t1 t2], so Coq will reject this
    definition as it stands.

    To fix the issue, we change the definition to the form [wpgen E t Q], where
    [E] denotes an association list bindings values to variables. The intention
    is that [wpgen E t Q] computes the weakest precondition for the term
    obtained by substituting all the bindings from [E] in [t]. This term is
    described by the operation [isubst E t], which is formally defined later in
    the chapter.

    The updated definition looks as follows. Observe how, when traversing
    [trm_let x t1 t2], the context [E] gets extended as [(x,v)::E]. Observe also
    how, when reaching a variable [x], a lookup for [x] into the context [E] is
    performed for recovering the value bound to [x].

    Fixpoint wpgen (E:ctx) (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_val v => Q v
      | trm_var x =>
           match lookup x E with
           | Some v => Q v
           | None => \[False]
           end
      | trm_app v1 v2 => \exists H, H \* \[triple (isubst E t) H Q]
      | trm_let x t1 t2 => wpgen E t1 (fun v => wpgen ((x,v)::E) t2 Q)
      ...
      end.
*)

(* ================================================================= *)
(** ** Step 2: [wpgen] Reformulated to Eagerly Match on the Term *)

(** In a second step, we slightly tweak the definition in order to move the
    [fun (Q:val->hprop)], by which the postcondition is taken as argument, to
    place it inside every case of the pattern matching. The idea is to make it
    explicit that [wpgen E t] can be computed without any knowledge of [Q]. In
    the definition shown below, [formula] is a shorthand for the type
    [(val->hprop)->hprop], which is the type of [wpgen E t].

    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      match t with
      | trm_val v =>  fun (Q:val->hprop) => Q v
      | trm_var x =>  fun (Q:val->hprop) =>
           match lookup x E with
           | Some v => Q v
           | None => \[False]
           end
      | trm_app t1 t2 => fun (Q:val->hprop) =>
                            \exists H, H \* \[triple (isubst E t) H Q]
      | trm_let x t1 t2 => fun (Q:val->hprop) =>
                              wpgen E t1 (fun v => wpgen ((x,v)::E) t2 Q)
      ...
      end.
*)

(* ================================================================= *)
(** ** Step 3: [wpgen] Reformulated with Auxiliary Definitions *)

(** In a third step, we introduce auxiliary definitions to improve the
    readability of the output of [wpgen]. For example, we let [wpgen_val v] be a
    shorthand for [fun (Q:val->hprop) => Q v]. Likewise, we let
    [wpgen_let F1 F2] be a shorthand for
    [fun (Q:val->hprop) => F1 (fun v => F2 Q)], where [v] can appear in [F2].
    Using these auxiliary definitions, the definition of [wpgen] can be
    reformulated as follows.

    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      match t with
      | trm_val v => wpgen_val v
      | trm_var x => wpgen_var E x
      | trm_app t1 t2 => wpgen_app (isubst E t)
      | trm_let x t1 t2 => wpgen_let (wpgen E t1) (fun v => wpgen ((x,v)::E) t2)
      ...
      end.
*)
(** Each of the auxiliary definitions introduced for [wpgen] comes with a custom
    notation that enables a nice display of the output of [wpgen]. For example,
    the notation [Let' v := F1 in F2] stands for [wpgen_let F1 (fun v => F2)].
    Thanks to this notation, the result of computing [wpgen] on a source term
    [Let x := t1 in t2], which is an Coq expression of type [trm], is a Coq
    expression of type [formula] displayed as [Let' x := F1 in F2].

    Thanks to these auxiliary definitions and pieces of notation, the formula
    that [wpgen] produces as output reads pretty much like the source term
    provided as input. The benefits, illustrated in the first two chapters
    ([Basic] and [Repr]), is that the proof obligations can be easily
    related to the source code that they arise from. *)

(* ================================================================= *)
(** ** Step 4: [wpgen] Augmented with Support for Structural Rules *)

(** In a fourth step, we refine the definition of [wpgen] in order to equip it
    with inherent support for applications of the structural rules of the logic,
    namely the frame rule and the rule of consequence. To achieve this, we
    carefully craft a predicate called [mkstruct] and insert it at the head of
    the output of every call to [wpgen], including all its recursive calls. In
    other words, the definition of [wpgen] hereafter has the following
    structure.

    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      mkstruct (match t with
                | trm_val v => ...
                | ...
                end).
*)
(** Without going into the details at this stage, the predicate [mkstruct] is a
    function of type [formula->formula] that captures the essence of the
    wp-style consequence-frame rule [wp_conseq_frame], presented the previous
    chapter. This rule asserts that [Q1 \*+ H ===> Q2] implies
    [(wp t Q1) \* H ==> (wp t Q2)]. *)

(** This concludes our little journey towards the definition of [wpgen]. For
    conducting proofs in practice, it remains to state lemmas and define
    "x-tactics" to assist the user in the manipulation of the formulae produced
    by [wpgen]. Ultimately, the end-user only manipulates "x-tactics" as in the
    first two chapters, without ever being required to understand how [wpgen] is
    defined.

    The "more details" section recapitulates each of the four steps presented in
    the above summary, but explaining in detail all the Coq definitions
    involved. *)

(* ################################################################# *)
(** * More Details *)

(* ================================================================= *)
(** ** Definition of [wpgen] for Each Term Construct *)

(** The function [wpgen] computes a heap predicate that has the same meaning as
    [wp]. In essence, [wpgen] takes the form of a recursive function that, like
    [wp], expects a term [t] and a postcondition [Q] and produces a heap
    predicate. The function is recursively defined, and its result is guided by
    the structure of the term [t]. In essence, the definition of [wpgen] has the
    following shape:

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_val v => ..
      | trm_seq t1 t2 => ..
      | trm_let x t1 t2 => ..
      | trm_var x => ..
      | trm_app t1 t2 => ..
      | trm_fun x t1 => ..
      | trm_fix f x t1 => ..
      | trm_if v0 t1 t2 => ..
      end.

    Our first goal is to figure out how to fill in the dots for each of the term
    constructors. The intention that guides us is the soundness theorem for
    [wpgen], which has the following form:

      wpgen t Q ==> wp t Q
*)
(** This entailment asserts in particular that, if we are able to establish a
    statement of the form [H ==> wpgen t Q], then we can derive [H ==> wp t Q]
    from it. The latter is also equivalent to [triple t H Q]. Thus, [wpgen] can
    be viewed as a practical tool for establishing triples.

    The reciprocal implication, namely [wp t Q ==> wpgen t Q], would correspond
    to a completeness theorem. Completeness is beyond the scope of this course.
    The historical notes section, located at the end of the chapter, contains a
    few comments on this question. *)

(* ----------------------------------------------------------------- *)
(** *** Definition of [wpgen] for Values *)

(** Consider first the case of a value [v]. Recall the reasoning rule for values
    in weakest-precondition style. *)

Parameter wp_val : forall v Q,
  Q v ==> wp (trm_val v) Q.

(** The soundness theorem for [wpgen] requires the entailment
    [wpgen (trm_val v) Q ==> wp (trm_val v) Q] to hold.

    To satisfy this entailment, according to the rule [wp_val], it suffices to
    define [wpgen (trm_val v) Q] as [Q v].

    Concretely, we fill in the first dots as follows:

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_val v => Q v
      ...
*)

(* ----------------------------------------------------------------- *)
(** *** Definition of [wpgen] for Functions *)

(** Consider the case of a function definition [trm_fun x t]. Recall that the
    [wp] reasoning rule for functions is very similar to the one for values. *)

Parameter wp_fun : forall x t1 Q,
  Q (val_fun x t1) ==> wp (trm_fun x t1) Q.

(** Following this rule, we define [wpgen (trm_fun x t1) Q] as
    [Q (val_fun x t1)]. Likewise for recursive functions, we define
    [wpgen (trm_fix f x t1) Q] as [Q (val_fix f x t1)].

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ...
      | trm_fun x t1   => Q (val_fun x t1)
      | trm_fix f x t1 => Q (val_fix f x t1)
      ...
*)

(** An interesting question that arises here is: why does
    [wpgen (trm_fun x t1) Q] not trigger a recursive call to [wpgen] on [t1]?
    The long answer is detailed in the last section of this chapter (module
    [WPgenRec]). The short answer is:

    - it is not technically needed to recurse in the body of local functions, in
      the sense that the user does not loose any ability to reason about local
      functions;
    - it may be interesting to recurse the body of local functions because it
      may save the need for the user to manually invoke the tactic [xwp] for
      each local function.
*)

(* ----------------------------------------------------------------- *)
(** *** Definition of [wpgen] for Sequences *)

(** Recall the [wp] reasoning rule for a sequence [trm_seq t1 t2]. *)

Parameter wp_seq : forall t1 t2 Q,
  wp t1 (fun v => wp t2 Q) ==> wp (trm_seq t1 t2) Q.

(** The intention is for [wpgen] to admit the same semantics as [wp]. We thus
    expect the definition of [wpgen (trm_seq t1 t2) Q] to have a similar shape
    to [wp t1 (fun v => wp t2 Q)].

    We therefore define [wpgen (trm_seq t1 t2) Q] as
    [wpgen t1 (fun v => wpgen t2 Q)]. The definition of [wpgen] is extended as
    follows:

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ...
      | trm_seq t1 t2 => wpgen t1 (fun v => wpgen t2 Q)
      ...
*)

(* ----------------------------------------------------------------- *)
(** *** Definition of [wpgen] for Let-Bindings *)

(** The case of let bindings is similar to that of sequences, except that it
    involves a substitution. Recall the [wp] rule: *)

Parameter wp_let : forall x t1 t2 Q,
  wp t1 (fun v => wp (subst x v t2) Q) ==> wp (trm_let x t1 t2) Q.

(** We fill in the dots as follows:

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ...
      | trm_let x t1 t2 => wpgen t1 (fun v => wpgen (subst x v t2) Q)
      ...
*)
(** Observe that in the above definition, the second recursive call is invoked
    on [subst x v t2], which is not a strict subterm of [t]. As explained
    earlier, this recursion pattern motivates the introduction of substitution
    contexts, written [E], to delay the computation of substitutions until the
    leaves of the recursion. *)

(* ----------------------------------------------------------------- *)
(** *** Definition of [wpgen] for Variables *)

(** We have seen no reasoning rules for establishing a triple for a program
    variable, that is, to prove [triple (trm_var x) H Q]. Indeed, [trm_var x] is
    a stuck term: its execution does not produce an output. A source term may of
    course contain program variables, but all these variables should be
    substituted away before the execution reaches them.

    In the case of the function [wpgen], a variable bound by a let-binding get
    substituted while traversing that let-binding construct. Thus, if a free
    variable is reached by [wpgen], it means that this variable was originally a
    dangling free variable, and therefore that the initial source term was
    invalid.

    But, although we have no reasoning rules for [triple (trm_var x) H Q] nor
    for [H ==> wp (trm_var x) Q], we nevertheless have to provide some
    meaningful definition for [wpgen (trm_var x) Q]. This definition should
    capture the fact that this case must not happen. The heap predicate
    [\[False]] appropriately captures this intention.

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ...
      | trm_var x => \[False]
      ...
*)

(** Remark: the use of \[False] embodies the fact that, technically, we could
    have stated a Separation Logic rule for free variables, using [False] as
    precondition. There are three ways of presenting this rule: *)

Lemma wp_var : forall x Q,
  \[False] ==> wp (trm_var x) Q.
Proof using. intros. intros h Hh. destruct (hpure_inv Hh). false. Qed.

Lemma triple_var : forall x H Q,
  False ->
  triple (trm_var x) H Q.
Proof using. intros. false. Qed.

Lemma triple_var' : forall x Q,
  triple (trm_var x) \[False] Q.
Proof using. intros. rewrite <- wp_equiv. applys wp_var. Qed.

(** All these rules are correct, albeit totally useless. *)

(* ----------------------------------------------------------------- *)
(** *** Definition of [wpgen] for Function Applications *)

(** Consider an application in A-normal form, that is, an application of the
    form [trm_app v1 v2]. We have seen [wp]-style rules to reason about the
    application of a known function, e.g. [trm_app (val_fun x t1) v2]. Yet,
    typically the function [v1] is a function specified in terms of [triple].
    (If [v1] is a primitive function, or if it comes from a function argument,
    it might not even be the case that [v1] admits the shape [val_fun x t1].)

    Thus, we wish to reason about an application [trm_app v1 v2] by exhibiting a
    triple of the form [triple (trm_app v1 v2) H Q]. As suggested earlier in the
    chapter, the definition of [wpgen (trm_app t1 t2) Q] needs to correspond to
    some heap predicate [H] for which [triple (trm_app v1 v2) H Q] holds. *)

(** The formula that formalizes this intuition is:

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ...
      | trm_app t1 t2 => exists H, H \* \[triple t H Q]
      ...
*)

(** Another possibility would be to define [wpgen (trm_app t1 t2) Q] as
    [wp (trm_app t1 t2) Q]. In other words, to define [wpgen] for a function
    application, we could fall back to the semantic definition of [wp].

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ...
      | trm_app t1 t2 => wp t Q
      ...

    However, this definition would require converting the [wp] into a [triple]
    each time, because specifications are, by convention, expressed using the
    predicate [triple]. *)

(** Remark: we assume throughout the course that terms are written in A-normal
    form. Nevertheless, we need to define [wpgen] even on terms that are not in
    A-normal form. One possibility is to map all these terms to [\[False]].
    However, even in the case of an application of the form [trm_app t1 t2]
    where [t1] and [t2] are not both values, it is still correct to define
    [wpgen (trm_app t1 t2))] as [wp (trm_app t1 t2)]. So, we need not bother
    checking in the definition of [wpgen] that the arguments of [trm_app] are
    actually values. *)

(* ----------------------------------------------------------------- *)
(** *** Definition of [wpgen] for Conditionals *)

(** Finally, consider an if-statement. Recall the [wp]-style reasoning rule
    stated using a Coq conditional. *)

Parameter wp_if : forall (b:bool) t1 t2 Q,
  (if b then (wp t1 Q) else (wp t2 Q)) ==> wp (trm_if (val_bool b) t1 t2) Q.

(** Typically, a source program may feature a conditional
    [trm_if (trm_var x) t1 t2] that, after substitution for [x], becomes
    [trm_if (trm_val v) t1 t2], for some abstract [v] of type [val]. Yet, in
    general, because we are working here with possibly ill-typed programs, this
    value is not know to be a boolean value. We therefore need to define [wpgen]
    for all if-statements of the form [trm_if (trm_val v0) t1 t2], where [v0]
    could be a value of unknown shape.

    However, the reasoning rule [wp_if] stated above features a right-hand side
    of the form [wp (trm_if (val_bool b) t1 t2) Q]. It only applies when the
    first argument of [trm_if] is syntactically a boolean value [b]. To resolve
    this mismatch, the definition of [wpgen] for a term [trm_if t0 t1 t2]
    quantifies existentially over a boolean value [b] such that
    [t0 = trm_val (val_bool b)]. This way, if [t0] is not a boolean value, then
    [wpgen (trm_if t0 t1 t2) Q] is equivalent to [\[False]]. Otherwise, if [t0]
    is of the form [val_bool b], and we are able to perform a case analysis on
    [b], to switch between [wpgen t1 Q] and [wpgen t2 Q] depending on the value
    of [b]. *)

(** The formal definition is:

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ...
      | trm_if t0 t1 t2 =>
          \exists (b:bool), \[t0 = trm_val (val_bool b)]
            \* (if b then (wpgen t1) Q else (wpgen t2) Q)
      ...
*)

(* ----------------------------------------------------------------- *)
(** *** Summary of the Definition So Far *)

(** In summary, we have defined:

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_val v => Q v
      | trm_fun x t1 => Q (val_fun x t)
      | trm_fix f x t1 => Q (val_fix f x t)
      | trm_seq t1 t2 => wpgen t1 (fun v => wpgen t2 Q)
      | trm_let x t1 t2 => wpgen t1 (fun v => wpgen (subst x v t2) Q)
      | trm_var x => \[False]
      | trm_app t1 t2 => exists H, H \* \[triple t H Q]
      | trm_if t0 t1 t2 =>
          \exists (b:bool), \[t0 = trm_val (val_bool b)]
            \* (if b then (wpgen t1) Q else (wpgen t2) Q)
      end.

    As pointed out earlier, this definition is not structurally recursive and is
    thus not accepted by Coq, due to the recursive call
    [wpgen (subst x v t2) Q]. Our next step is to fix this issue. *)

(* ================================================================= *)
(** ** Computing with [wpgen] *)

(** To make [wpgen] structurally recursive, the idea is to postpone the
    substitutions until the leaves of the recursion. To that end, we introduce a
    substitution context, written [E], to record the substitutions that must be
    performed. Concretely, we modify the function to take the form [wpgen E t],
    where [E] denotes a list of bindings from variables to values. The intention
    is that [wpgen E t] should compute the weakest precondition for the term
    [isubst E t], which denotes the result of substituting all bindings from E
    inside the term [t]. *)

(* ----------------------------------------------------------------- *)
(** *** Contexts *)

(** A context [E] is represented as an association list relating variables to
    values. Recall that all values are closed, i.e., without free variables. *)

Definition ctx : Type := list (var * val).

(** The "iterated substitution" operation, written [isubst E t], describes the
    substitution of _all_ the bindings from a context [E] into a term [t]. *)

(** Its implementation is standard: the function traverses the term recursively
    and, when reaching a variable, performs a lookup in the context [E]. The
    operation needs to take care to respect variable shadowing. To that end,
    when traversing a binder for a variable [x], all occurrences of [x] that
    might previously exist in [E] are removed.

    The formal definition of [isubst] involves two auxiliary functions -- lookup
    and removal -- on association lists. The definition of the operation
    [lookup x E] on association lists is standard. It returns an option on a
    value. *)

Fixpoint lookup (x:var) (E:ctx) : option val :=
  match E with
  | nil => None
  | (y,v)::E1 => if var_eq x y
                   then Some v
                   else lookup x E1
  end.

(** The definition of the removal operation, written [rem x E], is also
    standard. It returns a filtered context. *)

Fixpoint rem (x:var) (E:ctx) : ctx :=
  match E with
  | nil => nil
  | (y,v)::E1 =>
      let E1' := rem x E1 in
      if var_eq x y then E1' else (y,v)::E1'
  end.

(** The definition of the operation [isubst E t] can then be expressed as a
    recursive function over the term [t]. It invokes [lookup x E] when it
    reaches a variable [x]. It invokes [rem x E] when traversing a binding on
    the name [x]. *)

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
  | trm_app t1 t2 =>
       trm_app (isubst E t1) (isubst E t2)
  | trm_seq t1 t2 =>
       trm_seq (isubst E t1) (isubst E t2)
  | trm_let x t1 t2 =>
       trm_let x (isubst E t1) (isubst (rem x E) t2)
  | trm_if t0 t1 t2 =>
       trm_if (isubst E t0) (isubst E t1) (isubst E t2)
  end.

(** Remark: it is also possible to define the substitution by iterating the
    unary substitution [subst] over the list of bindings from [E]. However, this
    alternative approach yields a less efficient function and leads to more
    complicated proofs. *)

(** We now present the reformulated definition of [wpgen E t], case by case.
    Throughout these definitions, recall that [wpgen E t] is interpreted as the
    weakest precondition of [isubst E t]. *)

(* ----------------------------------------------------------------- *)
(** *** The Let-Binding Case *)

(** When the function [wpgen] traverses a let-binding, rather than eagerly
    performing a substitution, it simply extends the current context.
    Concretely, a call to [wpgen E (trm_let x t1 t2)] triggers a recursive call
    to [wpgen ((x,v)::E) t2]. The corresponding definition is:

    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      mkstruct (match t with
        ...
        | trm_let x t1 t2 => fun Q =>
             (wpgen E t1) (fun v => wpgen ((x,v)::E) t2)
        ...
        ) end.
*)

(* ----------------------------------------------------------------- *)
(** *** The Variable Case *)

(** When [wpgen] reaches a variable, it looks for a binding on the variable [x]
    inside the context [E]. Concretely, the evaluation of [wpgen E (trm_var x)]
    triggers a call to [lookup x E]. If the context [E] binds the variable [x]
    to some value [v], then the operation [lookup x E] returns [Some v]. In that
    case, [wpgen] returns the weakest precondition for the value [v], that is,
    [Q v]. Otherwise, if [E] does not bind [x], the lookup operation returns
    [None]. In that case, [wpgen] returns [\[False]], the weakest precondition
    for a stuck program.

    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      mkstruct (match t with
        ...
        | trm_var x => fun Q =>
             match lookup x E with
             | Some v => Q v
             | None => \[False]
             end
        ...
        ) end.
*)

(* ----------------------------------------------------------------- *)
(** *** The Application Case *)

(** Recall the definition of [wpgen] without substitution contexts:

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
       match t with
       ..
       | trm_app t1 t2 => fun Q => exists H, H \* \[triple t H Q]
*)

(** In the definition with contexts, the term [t] appearing in [triple t H Q]
    needs to be replaced with [isubst E t].

    Fixpoint wpgen (t:trm) : formula :=
      mkstruct (match t with
        ...
        | trm_app v1 v2 => fun Q => exists H, H \* \[triple (isubst E t) H Q]
        ..
*)

(* ----------------------------------------------------------------- *)
(** *** The Function Definition Case *)

(** Suppose [t] is a function definition, for example [trm_fun x t1]. Here
    again, the formula [wpgen E t] is interpreted as the weakest precondition of
    [isubst E t].

    By unfolding the definition of [isubst] in the case where [t] is
    [trm_fun x t1], we obtain [trm_fun x (isubst (rem x E) t1)].

    The corresponding value is [trm_val x (isubst (rem x E) t1)]. The weakest
    precondition for that value is
    [fun Q => Q (val_fun x (isubst (rem x E) t1))].

    Thus, [wpgen E t] handles functions (and recursive functions) as follows: *)

(**
    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      mkstruct (match t with
        ...
        | trm_fun x t1 => fun Q => Q (val_fun x (isubst (rem x E) t1))
        | trm_fix f x t1 => fun Q => Q (val_fix f x (isubst (rem x (rem f E)) t1))
        ...
        ) end.
*)

(* ----------------------------------------------------------------- *)
(** *** [wpgen]: At Last, an Executable Function *)

Module WpgenExec1.

(** At last, we arrive at a definition of [wpgen] that type-checks in Coq and
    that can be used to effectively compute weakest preconditions in Separation
    Logic. *)

Fixpoint wpgen (E:ctx) (t:trm) (Q:val->hprop) : hprop :=
  match t with
  | trm_val v => Q v
  | trm_fun x t1 => Q (val_fun x (isubst (rem x E) t1))
  | trm_fix f x t1 => Q (val_fix f x (isubst (rem x (rem f E)) t1))
  | trm_seq t1 t2 => wpgen E t1 (fun v => wpgen E t2 Q)
  | trm_let x t1 t2 => wpgen E t1 (fun v => wpgen ((x,v)::E) t2 Q)
  | trm_var x =>
       match lookup x E with
       | Some v => Q v
       | None => \[False]
       end
  | trm_app v1 v2 => \exists H, H \* \[triple (isubst E t) H Q]
  | trm_if t0 t1 t2 =>
      \exists (b:bool), \[t0 = trm_val (val_bool b)]
        \* (if b then (wpgen E t1) Q else (wpgen E t2) Q)
  end.

(** In the next chapter, we will establish the soundness of the [wpgen]. For the
    moment, we simply state the soundness theorem, then explain how it can be
    exploited for verifying concrete programs. *)

Parameter wpgen_sound : forall E t Q,
   wpgen E t Q ==> wp (isubst E t) Q.

(** The entailment above asserts in particular that we can derive [triple t H Q]
    by proving [H ==> wpgen t Q]. A useful corollary combines this soundness
    theorem with the rule [triple_app_fun], which allows establishing triples
    for functions.

    Recall [triple_app_fun] from chapter [Rules]. *)

Parameter triple_app_fun : forall x v1 v2 t1 H Q,
  v1 = val_fun x t1 ->
  triple (subst x v2 t1) H Q ->
  triple (trm_app v1 v2) H Q.

(** Reformulating the rule above into a rule for [wpgen] takes 3 steps.

    First, we rewrite the premise [triple (subst x v2 t1) H Q] using [wp]. It
    becomes [H ==> wp (subst x v2 t1) Q].

    Second, we observe that the term [subst x v2 t1] is equal to
    [isubst ((x,v2)::nil) t1]. (This equality is captured by the lemma
    [subst_eq_isubst_one] proved in the next chapter.) Thus, the heap predicate
    [wp (subst x v2 t1) Q] is equivalent to [wp (isubst ((x,v2)::nil) t1)].

    Third, according to [wpgen_sound], [wp (isubst ((x,v2)::nil) t1)] is
    entailed by [wpgen ((x,v2)::nil) t1]. Thus, we can use the latter as premise
    in place of the former. We thereby obtain the following lemma, which is at
    the heart of the implementation of the tactic [xwp]. *)

Parameter triple_app_fun_from_wpgen : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.

(* ----------------------------------------------------------------- *)
(** *** Executing [wpgen] on a Concrete Program *)

Import ExamplePrograms.

(** Let us exploit [triple_app_fun_from_wpgen] to demonstrate the computation of
    [wpgen] on a practical program. Recall the function [incr] (defined in
    Rules), and its specification below. *)

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~> n)
    (fun _ => p ~~> (n+1)).
Proof using.
  intros. applys triple_app_fun_from_wpgen. { reflexivity. }
  simpl. (* Read the goal here... *)
Abort.

(** At the end of the above proof fragment, the goal takes the form [H ==> F Q],
    where [H] denotes the precondition, [Q] the postcondition, and [F] is a
    formula describing the body of the function [incr]. Inside this formula, the
    reader can spot triples for the primitive operations involved. Observe that
    the goal is nevertheless somewhat hard to relate to the original program. In
    what follows, we explain how to remedy the situation by setting up [wpgen]
    so that its output is human-readable and resembles the original source code.
    *)

(* ----------------------------------------------------------------- *)
(** *** Consequence and Frame Properties for [wpgen] *)

(** **** Exercise: 3 stars, standard, especially useful (wpgen_conseq)

    Prove that [wpgen E t] satisfies the same consequence rule as [wp t]. The
    statement is directly adapted from [wp_conseq], from [WPsem]. Hint:
    begin the proof with [intros t. induction t.]. *)

Lemma wpgen_conseq : forall t E Q1 Q2,
  Q1 ===> Q2 ->
  wpgen E t Q1 ==> wpgen E t Q2.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 4 stars, standard, especially useful (wpgen_frame)

    Prove that [wpgen E t] satisfies the same frame rule as [wp t]. The
    statement is directly adapted from [wp_frame], from [WPsem]. The
    sequence case is not easy. *)

Lemma wpgen_frame : forall t E H Q,
  (wpgen E t Q) \* H ==> wpgen E t (Q \*+ H).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End WpgenExec1.

(* ================================================================= *)
(** ** Optimizing the Readability of [wpgen]'s Output *)

(** To improve the readability of the formulae produced by [wpgen], we take the
    following 3 steps:

    - first, we modify the presentation of [wpgen] so that the
      [fun (Q:val->hprop) =>] appears insides the branches of the
      [match t with] rather than around it,
    - second, we introduce one auxiliary definition for each branch
      of the [match t with], and
    - third, we introduce a Notation for each of these auxiliary definitions. *)

(* ----------------------------------------------------------------- *)
(** *** Reability Step 1: Moving the Function below the Branches. *)

(** We distribute the [fun Q] into the branches of the [match t]. Concretely, we
    change from:

 Fixpoint wpgen (E:ctx) (t:trm) (Q:val->hprop) : hprop :=
   match t with
   | trm_val v     =>  Q v
   | trm_fun x t1  =>  Q (val_fun x (isubst (rem x E) t1))
   ...
   end.

    to the equivalent form:

 Fixpoint wpgen (E:ctx) (t:trm) : (val->hprop)->hprop :=
   match t with
   | trm_val v     =>  fun (Q:val->hprop) => Q v
   | trm_fun x t1  =>  fun (Q:val->hprop) => Q (val_fun x (isubst (rem x E) t1))
   ...
   end.
*)

(** The result type of [wpgen E t] is [(val->hprop)->hprop]. Hereafter, we let
    [formula] be a shorthand for this type. This shorthand will improve
    readability, especially when defining the [mkstruct] combinator, which has
    type [formula->formula]. *)

Definition formula : Type := (val->hprop)->hprop.

(* ----------------------------------------------------------------- *)
(** *** Readability Steps 2 and 3 for the Case of Sequences *)

(** We next introduce auxiliary definitions to denote the result of each of the
    branches of the [match t] construct. Concretely, we change from

    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      match t with
      ...
      | trm_seq t1 t2 =>  fun Q => (wpgen E t1) (fun v => wpgen E t2 Q)
      ...
      end.

    to the equivalent form:

    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      match t with
      ...
      | trm_seq t1 t2 =>  wpgen_seq (wpgen E t1) (wpgen E t2)
      ...
     end.

    where [wpgen_seq] is defined below. *)

Definition wpgen_seq (F1 F2:formula) : formula := fun Q =>
  F1 (fun v => F2 Q).

(** Here, [F1] and [F2] denote the results of the recursive calls, [wpgen E t1]
    and [wpgen E t2], respectively.

    With the above definitions, [wgpen E (trm_seq t1 t2)] evaluates to
    [wp_seq (wpgen E t1) (wpgen E t2)]. *)

(** Finally, we introduce a piece of notation for each case. For sequence, we
    set up the notation defined next to so that any formula of the form
    [wpgen_seq F1 F2] gets displayed as [Seq F1 ; F2 ]. *)

Notation "'Seq' F1 ; F2" :=
  ((wpgen_seq F1 F2))
  (at level 68, right associativity,
   format "'[v' 'Seq'  '[' F1 ']'  ';'  '/'  '[' F2 ']' ']'").

(** Thanks to this notation, the [wpgen] of a sequence [t1 ; t2] displays as
    [Seq F1 ; F2] where [F1] and [F2] denote the [wpgen] of [t1] and [t2],
    respectively. The "format" clause in the notation definition is there only
    to improve the pretty-printing of formulae. The semantics of ['/'] is to
    encourage a line break. The semantics of square brackets is to delimit
    blocks. The "v" character next to the leading bracket encourages a vertical
    alignement of the blocks. Double spaces in the format clause indicate the
    need to pretty-print a single space, as opposed to an empty spacing. *)

(* ----------------------------------------------------------------- *)
(** *** Readability Step 2: Auxiliary Definitions for other Constructs *)

(** We generalize the approach illustrated above for sequences to every other
    term construct... *)

Definition wpgen_val (v:val) : formula := fun Q =>
  Q v.

Definition wpgen_let (F1:formula) (F2of:val->formula) : formula := fun Q =>
  F1 (fun v => F2of v Q).

Definition wpgen_if (t:trm) (F1 F2:formula) : formula := fun Q =>
  \exists (b:bool), \[t = trm_val (val_bool b)] \* (if b then F1 Q else F2 Q).

Definition wpgen_fail : formula := fun Q =>
  \[False].

Definition wpgen_var (E:ctx) (x:var) : formula :=
  match lookup x E with
  | None => wpgen_fail
  | Some v => wpgen_val v
  end.

Definition wpgen_app (t:trm) : formula := fun Q =>
  \exists H, H \* \[triple t H Q].

(** The new definition of [wpgen] reads as follows: *)

Module WpgenExec2.

Fixpoint wpgen (E:ctx) (t:trm) : formula :=
  match t with
  | trm_val v => wpgen_val v
  | trm_var x => wpgen_var E x
  | trm_fun x t1 => wpgen_val (val_fun x (isubst (rem x E) t1))
  | trm_fix f x t1 => wpgen_val (val_fix f x (isubst (rem x (rem f E)) t1))
  | trm_app t1 t2 => wpgen_app (isubst E t)
  | trm_seq t1 t2 => wpgen_seq (wpgen E t1) (wpgen E t2)
  | trm_let x t1 t2 => wpgen_let (wpgen E t1) (fun v => wpgen ((x,v)::E) t2)
  | trm_if t0 t1 t2 => wpgen_if (isubst E t0) (wpgen E t1) (wpgen E t2)
  end.

End WpgenExec2.

(* ----------------------------------------------------------------- *)
(** *** Readability Step 3: Notations for Auxiliary Definitions *)

(** We generalize the notation introduced for sequences to every other term
    construct. The corresponding notation is defined below. To avoid a conflict
    with the TLC notation for classical conditionals, we write [If_] in place of
    [If]. *)

Declare Scope wpgen_scope.

Notation "'Val' v" :=
  ((wpgen_val v))
  (at level 69) : wpgen_scope.

Notation "'Let' x ':=' F1 'in' F2" :=
  ((wpgen_let F1 (fun x => F2)))
  (at level 69, x name, right associativity,
  format "'[v' '[' 'Let'  x  ':='  F1  'in' ']'  '/'  '[' F2 ']' ']'")
  : wpgen_scope.

Notation "'If_' b 'Then' F1 'Else' F2" :=
  ((wpgen_if b F1 F2))
  (at level 69) : wpgen_scope.

Notation "'Fail'" :=
  ((wpgen_fail))
  (at level 69) : wpgen_scope.

(** In addition, we introduce a handy notation for the result of [wpgen t] where
    [t] denotes an application. (We cover here only functions of arity one or
    two. The file [LibSepReference.v] provides arity-generic definitions.) *)

Notation "'App' f v1 " :=
  ((wpgen_app (trm_app f v1)))
  (at level 68, f, v1 at level 0) : wpgen_scope.

Notation "'App' f v1 v2 " :=
  ((wpgen_app (trm_app (trm_app f v1) v2)))
  (at level 68, f, v1, v2 at level 0) : wpgen_scope.

(* ----------------------------------------------------------------- *)
(** *** Demo of [wpgen] with Notation. *)

Module WPgenWithNotation.
Import ExamplePrograms WpgenExec2.
Open Scope wpgen_scope.

(** Here again, we temporarily axiomatize the soundness result for the purpose
    of looking at how that result can be exploited in practice. *)

Parameter triple_app_fun_from_wpgen : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.

(** Consider again the example of [incr]. *)

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~> n)
    (fun _ => p ~~> (n+1)).
Proof using.
  intros. applys triple_app_fun_from_wpgen. { reflexivity. }
  simpl. (* Read the goal here... It is of the form [H ==> F Q],
            where [F] vaguely looks like the code of the body of [incr]. *)
Abort.

(** Up to whitespace, alpha-renaming, removal of parentheses, and removal of
    quotes after [Let] and [If]), the formula [F] reads as:

      Let n := App val_get p in
      Let m := App (val_add n) 1 in
      App (val_set p) m
*)

(** With the introduction of intermediate definitions for [wpgen] and the
    introduction of associated notations for each term construct, what we have
    achieved is that the output of [wpgen] is, for any input term [t], a human-
    readable formula whose display closely resembles the source code of [t]. *)

End WPgenWithNotation.

(* ================================================================= *)
(** ** Extension of [wpgen] to Handle Structural Rules *)

(** The definition of [wpgen] proposed so far integrates the logic of the
    reasoning rules for terms. The lemmas [wpgen_conseq] and [wpgen_frame]
    established earlier establish that [wpgen] moreover supports the structural
    rules of the logic. Yet, when we are in the middle of the verification of a
    concrete program [t], the expression [wpgen nil t] is already simplified,
    making it hard to exploit the lemmas [wpgen_conseq] and [wpgen_frame].

    In order to support convenient application of these rules during the
    verification of concrete programs, we tweak the definition of [wpgen] in
    such a way that, even after simplification, it obviously satisfies both the
    rule of consequence and the frame rule. *)

(* ----------------------------------------------------------------- *)
(** *** Introduction of [mkstruct] in the Definition of [wpgen] *)

(** The tweak consists of introducing, at every step of the recursion of
    [wpgen], a special predicate called [mkstruct] to capture the possibility of
    applying structural rules.

    Fixpoint wpgen (E:ctx) (t:trm) : (val->hprop)->hprop :=
      mkstruct (
        match t with
        | trm_val v => wpgen_val v
        ...
        end).

  With this definition, any output of [wpgen E t] is necessarily of the form
  [mkstruct F], for some formula [F] describing the weakest precondition of [t].

  The next step is to investigate what properties [mkstruct] should satisfy. *)

(* ----------------------------------------------------------------- *)
(** *** Properties of [mkstruct] *)

Module MkstructProp.

(** Because [mkstruct] appears between the prototype and the [match] in the body
    of [wpgen], it must have type [formula->formula]. *)

Parameter mkstruct : formula->formula.

(** Next, [mkstruct] should satisfy reasoning rules that mimic the statements of
    the frame rule and the consequence rule in weakest-precondition style
    ([wp_frame] and [wp_conseq]). *)

Parameter mkstruct_frame : forall (F:formula) H Q,
  (mkstruct F Q) \* H ==> mkstruct F (Q \*+ H).

Parameter mkstruct_conseq : forall (F:formula) Q1 Q2,
  Q1 ===> Q2 ->
  mkstruct F Q1 ==> mkstruct F Q2.

(** In addition, the user manipulating a formula produced by [wpgen] should be
    able to discard the predicate [mkstruct] from the head of the output when
    there is no need to apply the frame rule or the rule of consequence. The
    erasure property is captured by the following entailment. *)

Parameter mkstruct_erase : forall (F:formula) Q,
  F Q ==> mkstruct F Q.

(** Moreover, in order to complete the soundness proof for [wpgen], the
    predicate [mkstruct] should be covariant: if [F1] entails [F2], then
    [mkstruct F1] should entail [mkstruct F2]. *)

Parameter mkstruct_monotone : forall F1 F2 Q,
  (forall Q, F1 Q ==> F2 Q) ->
  mkstruct F1 Q ==> mkstruct F2 Q.

End MkstructProp.

(* ----------------------------------------------------------------- *)
(** *** Realization of [mkstruct] *)

(** The great news is that there exists a predicate satisfying the four required
    properties of [mkstruct]. The definition may appear magic at first, and
    indeed there is no need to deeply understand it or the proofs that follow.
    The only critical observation is that there exists a predicate [mkstruct]
    satisfying the required properties. *)

Definition mkstruct (F:formula) : formula :=
  fun Q => \exists Q1, F Q1 \* (Q1 \--* Q).

(** The magic wand may appear somewhat puzzling, but the above statement is
    reminiscent from the statement of [wp_ramified], which captures the
    expressive power of all the structural reasoning rules of Separation Logic
    at once. If we unfold the definition of the magic wand, we can see more
    clearly that [mkstruct F] is a formula that describes a program that
    produces a postcondition [Q] when executed in the current state if and only
    if the formula [F] describes a program that produces a postcondtion [Q1] in
    a subset of the current state and if the postcondition [Q1] augmented with
    the remainder of the current state (i.e., the piece described by [H])
    corresponds to the postcondition [Q]. *)

Definition mkstruct' (F:formula) : formula :=
  fun (Q:val->hprop) => \exists Q1 H, F Q1 \* H \* \[Q1 \*+ H ===> Q].

(** The four properties of [mkstruct] can be easily verified. *)

Lemma mkstruct_frame : forall F H Q,
  (mkstruct F Q) \* H ==> mkstruct F (Q \*+ H).
Proof using. intros. unfold mkstruct. xpull. intros Q'. xsimpl*. Qed.

Lemma mkstruct_conseq : forall F Q1 Q2,
  Q1 ===> Q2 ->
  mkstruct F Q1 ==> mkstruct F Q2.
Proof using. introv WQ. unfold mkstruct. xpull. intros Q'. xsimpl*. Qed.

Lemma mkstruct_erase : forall F Q,
  F Q ==> mkstruct F Q.
Proof using. intros. unfold mkstruct. xsimpl. Qed.

Lemma mkstruct_monotone : forall F1 F2 Q,
  (forall Q, F1 Q ==> F2 Q) ->
  mkstruct F1 Q ==> mkstruct F2 Q.
Proof using. introv WF. unfolds mkstruct. xpull. intros Q'. xchanges WF. Qed.

(* ----------------------------------------------------------------- *)
(** *** Definition of [wpgen] with [mkstruct] *)

(** The final definition of [wpgen] refines the previous one by inserting the
    [mkstruct] predicate at the front of the [match t with] construct. *)

Fixpoint wpgen (E:ctx) (t:trm) : formula :=
  mkstruct (match t with
  | trm_val v => wpgen_val v
  | trm_var x => wpgen_var E x
  | trm_fun x t1 => wpgen_val (val_fun x (isubst (rem x E) t1))
  | trm_fix f x t1 => wpgen_val (val_fix f x (isubst (rem x (rem f E)) t1))
  | trm_app t1 t2 => wpgen_app (isubst E t)
  | trm_seq t1 t2 => wpgen_seq (wpgen E t1) (wpgen E t2)
  | trm_let x t1 t2 => wpgen_let (wpgen E t1) (fun v => wpgen ((x,v)::E) t2)
  | trm_if t0 t1 t2 => wpgen_if (isubst E t0) (wpgen E t1) (wpgen E t2)
  end).

(** To avoid clutter in reading the output of [wpgen], we introduce a
    lightweight shorthand to denote [mkstruct F], allowing it to display simply
    as [`F]. *)

Notation "` F" := (mkstruct F) (at level 10, format "` F") : wpgen_scope.

(** Once again, we temporarily axiomatize the soundness result for the purpose
    of looking at how that result can be exploited in practice. *)

Parameter triple_app_fun_from_wpgen : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.

(* ================================================================= *)
(** ** Implementation of X-tactics *)

(* ----------------------------------------------------------------- *)
(** *** X-lemmas for Implementing X-tactics *)

(** The last major step in the setup of our verification framework consists of
    lemmas and tactics to assist in the processing of formulas produced by
    [wpgen]. For each term construct, and for [mkstruct], we introduce a
    dedicated lemma, called "x...-lemma", to help with the elimination of that
    construct. *)

(** [xstruct_lemma] is a reformulation of [mkstruct_erase]. *)

Lemma xstruct_lemma : forall F H Q,
  H ==> F Q ->
  H ==> mkstruct F Q.
Proof using. introv M. xchange M. applys mkstruct_erase. Qed.

(** [xval_lemma] reformulates the definition of [wpgen_val]. It just unfolds the
    definition. *)

Lemma xval_lemma : forall v H Q,
  H ==> Q v ->
  H ==> wpgen_val v Q.
Proof using. introv M. applys M. Qed.

(** [xlet_lemma] reformulates the definition of [wpgen_let]. It just unfolds the
    definition. *)

Lemma xlet_lemma : forall H F1 F2of Q,
  H ==> F1 (fun v => F2of v Q) ->
  H ==> wpgen_let F1 F2of Q.
Proof using. introv M. xchange M. Qed.

(** Likewise, [xseq_lemma] reformulates [wpgen_seq]. *)

Lemma xseq_lemma : forall H F1 F2 Q,
  H ==> F1 (fun v => F2 Q) ->
  H ==> wpgen_seq F1 F2 Q.
Proof using. introv M. xchange M. Qed.

(** [xapp_lemma] applies to goals produced by [wpgen] on an application. In such
    cases, the proof obligation is of the form [H ==> (wpgen_app t) Q].
    [xapp_lemma] reformulates the frame-consequence rule in a way that enables
    exploiting a specification triple for a function to reason about a call to
    that function. *)

Lemma xapp_lemma : forall t Q1 H1 H2 H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  H ==> wpgen_app t Q.
Proof using.
  introv M WH WQ. unfold wpgen_app. xsimpl. applys* triple_conseq_frame M.
Qed.

(** [xwp_lemma] is another name for [triple_app_fun_from_wpgen]. It is used for
    establishing a triple for a function application. *)

Lemma xwp_lemma : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.
Proof using. introv M1 M2. applys* triple_app_fun_from_wpgen. Qed.

(* ----------------------------------------------------------------- *)
(** *** Example Proofs using X-lemmas *)

(** Let us illustrate how "x-lemmas" help clarifying verification proof scripts.
    *)

Module ProofsWithXlemmas.
Import ExamplePrograms.
Open Scope wpgen_scope.

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~> n)
    (fun _ => p ~~> (n+1)).
Proof using.
  intros.
  applys xwp_lemma. { reflexivity. }
  (* Here the [wpgen] function computes. *)
  simpl.
  (* Observe how each node begin with [mkstruct].
     Observe how program variables are all eliminated. *)
  applys xstruct_lemma.
  applys xlet_lemma.
  applys xstruct_lemma.
  applys xapp_lemma. { apply triple_get. } { xsimpl. }
  xpull; intros ? ->.
  applys xstruct_lemma.
  applys xlet_lemma.
  applys xstruct_lemma.
  applys xapp_lemma. { apply triple_add. } { xsimpl. }
  xpull; intros ? ->.
  applys xstruct_lemma.
  applys xapp_lemma. { apply triple_set. } { xsimpl. }
  xsimpl.
Qed.

(** **** Exercise: 2 stars, standard, especially useful (triple_succ_using_incr_with_xlemmas)

    Using x-lemmas, simplify the proof of [triple_succ_using_incr], which was
    carried out using triples in chapter [Rules]. *)

Lemma triple_succ_using_incr_with_xlemmas : forall (n:int),
  triple (trm_app succ_using_incr n)
    \[]
    (fun v => \[v = n+1]).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End ProofsWithXlemmas.


(* ----------------------------------------------------------------- *)
(** *** Definition of X-tactics *)

(** Next, for each x-lemma, we introduce a dedicated tactic to apply that lemma
    and perform the associated bookkeeping. [xstruct] eliminates the leading
    [mkstruct] that appears in a goal of the form [H ==> mkstruct F Q]. *)

Tactic Notation "xstruct" :=
  applys xstruct_lemma.

(** The tactics [xval], [xseq] and [xlet] invoke the corresponding x-lemmas,
    after calling [xstruct] if a leading [mkstruct] is in the way. *)

Tactic Notation "xstruct_if_needed" :=
  try match goal with |- ?H ==> mkstruct ?F ?Q => xstruct end.

Tactic Notation "xval" :=
  xstruct_if_needed; applys xval_lemma.

Tactic Notation "xlet" :=
  xstruct_if_needed; applys xlet_lemma.

Tactic Notation "xseq" :=
  xstruct_if_needed; applys xseq_lemma.

(** [xapp_nosubst] applys [xapp_lemma], after calling [xseq] or [xlet] if
    applicable. Further on, we will define [xapp] as an enhanced version of
    [xapp_nosubst] that is able to automatically perform substitutions. *)

Tactic Notation "xseq_xlet_if_needed" :=
  try match goal with |- ?H ==> mkstruct ?F ?Q =>
  match F with
  | wpgen_seq ?F1 ?F2 => xseq
  | wpgen_let ?F1 ?F2of => xlet
  end end.

Tactic Notation "xapp_nosubst" constr(E) :=
  xseq_xlet_if_needed; xstruct_if_needed;
  applys xapp_lemma E; [ xsimpl | xpull ].

(** [xwp] applys [xwp_lemma], then requests Coq to evaluate the [wpgen]
    function. (For technical reasons, in the definition shown below we need to
    explicitly request the unfolding of [wpgen_var].) *)

Tactic Notation "xwp" :=
  intros; applys xwp_lemma;
  [ first [ reflexivity | eassumption ]
  | simpl; unfold wpgen_var; simpl ].

(** Now let us revisit the previous proof scripts using x-tactics instead of
    x-lemmas. The reader is invited to contemplate the gain in conciseness. *)

Module ProofsWithXtactics.
Import ExamplePrograms.
Open Scope wpgen_scope.

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~> n)
    (fun _ => p ~~> (n+1)).
Proof using.
  xwp.
  xapp_nosubst triple_get. intros ? ->.
  xapp_nosubst triple_add. intros ? ->.
  xapp_nosubst triple_set.
  xsimpl.
Qed.

(** **** Exercise: 2 stars, standard, especially useful (triple_succ_using_incr_with_xtactics)

    Using x-tactics, prove [succ_using_incr]. *)

Lemma triple_succ_using_incr_with_xtactics : forall (n:int),
  triple (trm_app succ_using_incr n)
    \[]
    (fun v => \[v = n+1]).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End ProofsWithXtactics.

(* ----------------------------------------------------------------- *)
(** *** Improved Postprocessing for [xapp]. *)

(** The above proofs frequently exhibit the patterns [intros ? ->] or
    [intros ? x ->] for some variable [x]. This pattern is typically occurs
    whenever the specification of the function being called in the code features
    a postcondition of the form [fun v => \[v = ..]] or of the form
    [fun v => \[v = ..] \* ..]. Let us devise a tactic called [xapp] to
    automatically handle this pattern.

    The pattern in its implementation matches on the shape of the goal being
    produced by a call to [xapp_nosubst]. It attempts to perform the
    introduction and the substitution. The reader need not follow through the
    details of this Ltac definition. *)

Tactic Notation "xapp_try_subst" := (* for internal use only *)
  try match goal with
  | |- forall (r:val), (r = _) -> _ => intros ? ->
  | |- forall (r:val), forall x, (r = _) -> _ =>
      let y := fresh x in intros ? y ->; revert y
  end.

Tactic Notation "xapp" constr(E) :=
  xapp_nosubst E; xapp_try_subst.

(* ----------------------------------------------------------------- *)
(** *** Database of Specification Lemmas for the [xapp] Tactic. *)

(** Explicitly providing arguments to [xapp_nosubst] or [xapp] is tedious. To
    avoid this effort, we set up a database of specification lemmas. Using this
    database, [xapp] can automatically look up the relevant specification. The
    actual CFML tool uses a proper lookup table binding function names to
    specification lemmas. In this course, however, we'll rely on a simpler
    mechanism, based on standard hints for [eauto]. In this setting, we can
    register specification lemmas using the [Hint Resolve ... : triple] command,
    as illustrated below. *)

#[global] Hint Resolve triple_get triple_set triple_ref
                       triple_free triple_add : triple.

(** The argument-free variants [xapp_subst] and [xapp] are implemented by
    invoking [eauto with triple] to retrieve the relevant specification.

    One shortcoming of the version of the [xapp] tactic that leverages the
    [triple] database is that it is not able to automatically apply
    specifications that involve a premise that [eauto] cannot solve. To exploit
    such specifications, we need to provide the specification explicitly using
    [xapp E]. This tactic is defined in [LibSepReference.v]. Its implementation
    is a bit technical, we do not describe it here. *)

Tactic Notation "xapp_nosubst" :=
  xseq_xlet_if_needed; xstruct_if_needed;
  applys xapp_lemma; [ solve [ eauto with triple ] | xsimpl | xpull ].

Tactic Notation "xapp" :=
  xapp_nosubst; xapp_try_subst.

(* ----------------------------------------------------------------- *)
(** *** Demo of Verification using X-tactics *)

Module ProofsWithAdvancedXtactics.
Import ExamplePrograms.
Open Scope wpgen_scope.

(** The tactics defined in the previous sections may be used to complete proofs
    like done in the first two chapters of the course. For example, here is the
    proof of the increment function. *)

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~> n)
    (fun _ => p ~~> (n+1)).
Proof using.
  xwp. xapp. xapp. xapp. xsimpl.
Qed.

#[global] Hint Resolve triple_incr : triple.

(** In summary, we have shown how to leverage [wpgen], x-lemmas and x-tactics to
    implement the core of a practical verification framework based on Separation
    Logic. *)

End ProofsWithAdvancedXtactics.

(* ================================================================= *)
(** ** Reasoning about Local Functions *)

Module ExampleLocalFunWpgen.
Import DemoPrograms WpgenExec2.
Open Scope wpgen_scope.

(** Consider the following program, which defines a local function named [f] for
    incrementing a reference cell [p], then invokes [f()] twice. The purpose of
    this example is to illustrate how to reason about a local function.

OCaml:

  fun p ->
    let f = (fun () -> incr p) in
    f();
    f()
*)

Definition incrtwice : val :=
  <{ fun 'p =>
       let 'f = (fun_ 'u => incr 'p) in
       'f ();
       'f () }>.

(** There are two possible approaches to reasoning about this code.

    In the first approach, we store the hypothesis capturing that [f] has for
    code [fun () -> incr p], and each time we encounter a call to [f], we
    "inline" the code of [f] at the call site. This approach is very effective
    when [f] has a unique occurrence. However, if [f] has multiple occurrences,
    then the user has to reason several times about the same code pattern.

    The second approach yields a modular proof. When reasoning about the
    definition of [f], we assert and prove a specification for [f], then
    immediately discard any information revealing what the code of [f] is. Then,
    each time we encounter a call to [f], we use [xapp] to leverage the
    specification of the local function [f], exactly like we have been doing
    everywhere for reasoning about calls to top-level functions.

    Let us illustrate the two approaches, and introduce on the way a few
    additional x-tactics relevant for local functions. *)

(* ----------------------------------------------------------------- *)
(** *** 1. Reasoning about Local Functions by Inlining *)

(** To begin with, let us naively attempt to use the tactics [xlet] and [xval]
    to reason about the function definitions. *)

Lemma triple_incrtwice_using_xval : forall (p:loc) (n:int),
  triple (incrtwice p)
    (p ~~> n)
    (fun _ => p ~~> (n+2)).
Proof using.
  xwp.
(** At this point, we have the formula for the body of the function [incrtwice],
    which binds (under the name [v]) the value [fun {"u"} => {incr p}]. *)
  xlet.
(** By typing [xlet], we focus on this value [fun {"u"} => {incr p}]. The tactic
    [xval] then substitutes this value throughout the remaining of the formula.
    *)
  xval.
(** Because the body of [incrtwice] contains two calls to the local function
    [f], the resulting formula contains two copies of the function
    [fun {"u"} => {incr p}]. This kind of duplication, in general, is
    problematic, because the size of the formulae grow significantly. *)
Abort.

(** We therefore introduce a variant of the [xlet] tactic, called [xletval],
    that processes let-bindings by introducing an equality in the Coq context.
    For example, for our local function [f], a fresh hypothesis named [f] of
    type [val] is introduced, and an hypothesis of type asserting that [f] is
    equal to [fun {"u"} => {incr p}] is provided to characterize the value [f].
    Let us first defined the tactic [xval], then illustrate its usage. *)

(** The tactic [xletval] applies to formulae arising from terms of the form
    [let x = v1 in t2]. It processes the binding [let x = v1] by introducing in
    the goal a universal quantification over a variable [x] and over an
    hypothesis of type [x = v1]. *)

Lemma xletval_lemma : forall H v1 F2of Q,
  (forall x, x = v1 -> H ==> F2of x Q) ->
  H ==> wpgen_let (mkstruct (wpgen_val v1)) F2of Q.
Proof using.
  introv M. applys xlet_lemma. apply xstruct_lemma.
  apply xval_lemma. applys* M.
Qed.

Tactic Notation "xletval" :=
  xstruct_if_needed; applys xletval_lemma.

Lemma triple_incrtwice_using_xletval : forall (p:loc) (n:int),
  triple (incrtwice p)
    (p ~~> n)
    (fun _ => p ~~> (n+2)).
Proof using.
  xwp. xletval. intros f Hf.
(** As announced, reasoning about the local function definition using [xletval]
    introduces a name [f] and an hypothesis [Hf] of type
    [f = <{ fun {"u"} => {incr p} }>]

    There remains to reason about calls to the function [f]. Let us first show
    how it could be done step by step. We will subsequently define a tactic,
    named [xappfun], to improve conciseness. To reason about the remaining of
    the code of [incrtwice], we begin by focusing on the first call to [f()],
    using [xseq]. *)
  xseq.
(** At this stage, we can remove the leading [mkstruct], unfold the definition
    of [wgpgen_app], and simplify the resulting statement using [xsimpl]. *)
  xstruct. unfold wpgen_app. xsimpl.
(** We are left with proving that [f()] admits a certain behaviour, under the
    hypothesis that the code of [f] is [fun {"u"} => {incr p}]. We can make
    progress by invoking the tactic [xwp], exactly as we do for reasoning about
    top-level functions. *)
   xwp.
(** There remains to reason about the code from the body of the function [f],
    that is, the instruction [incr p]. We can use [xapp] for that purpose. *)
  xapp.
(** We could similarly handle the second call to [f], then complete the proof.
    Let us show how to do so in the next lemma, after introducing a tactic to
    factorize the proof pattern for reasoning about calls to local functions. *)
Abort.

(** The tactic [xappfun] applies to formulae arising from function calls of the
    form [f v] where [f] is a local function previously handled using [xletval].
    Essentially, this tactic inline the formula associated with the body of [f],
    specializing the body to the argument [v]. *)

Lemma xappfun_lemma : forall t H Q,
  triple t H Q ->
  H ==> wpgen_app t Q.
Proof using. introv M. unfold wpgen_app. xsimpl*. Qed.

Tactic Notation "xappfun" :=
  xseq_xlet_if_needed; xstruct_if_needed; applys xappfun_lemma; xwp.

(** Let us revisit the previous proof using this new tactic [xappfun]. *)

Lemma triple_incrtwice_using_xletva_and_xapp_fun : forall (p:loc) (n:int),
  triple (incrtwice p)
    (p ~~> n)
    (fun _ => p ~~> (n+2)).
Proof using.
  xwp.
  xletval. intros f Hf. (* Reason about the definition of [f]. *)
  xappfun. (* Reason about the 1st call to [f]. *)
  xapp. (* Reason about the call to [incr] triggered by the 1st call to [f]. *)
  xappfun. (* Reason about the 2nd call to [f]. *)
  xapp. (* Reason about the call to [incr] triggered by the 2nd call to [f]. *)
  xsimpl. math. (* Conclude the proof. *)
Qed.

(** This completes the presentation of the first approach. As illustrated in the
    example proof above, reasoning twice about the body of the function [f]
    leads to some duplication. The second approach shows how to avoid
    duplication, by stating and proving a specification for [f]. *)

(* ----------------------------------------------------------------- *)
(** *** 2. Reasoning about Local Functions Modularly *)

(** In the second approach, immediately after obtaining the hypothesis that [f]
    has code [fun {"u"} => {incr p}], we establish a specification for [f],
    expressed using a triple, then discard the hypothesis about the code of [f].
    *)

Lemma triple_incrtwice_with_assert : forall (p:loc) (n:int),
  triple (incrtwice p)
    (p ~~> n)
    (fun _ => p ~~> (n+2)).
Proof using.
(** We begin the proof like the previous one. *)
  xwp. xletval. intros f Hf.
(** As soon as [f] is introduced, we assert the specification of this function.
    *)
  assert (Sf : forall (m:int),
    triple <{ f () }> (p ~~> m) (fun _ => p ~~> (m+1))). {
(** To establish this specification, we inline the code of [f]. This is the one
    and only place where we inline the code of [f]. *)
    intros. subst f.
(** Then, we complete the verification of [f] as usual. *)
    xwp. xapp. xsimpl. }
(** We have introduced an hypothesis [Sf] that characterizes the behavior of [f]
    by means of a triple. We can drop the hypothesis about the code of [f]. *)
    clear Hf.
(** The remaining of the proof now proceeds just like if [f] was a top-level
    function, using [xapp] for reasoning about each call to [f]. *)
  xapp.
  xapp.
  xsimpl.
  math.
Qed.

(** The tactic [xfun] applies to a formula arising from terms of the form
    [let f = (fun x -> t1) in t2]. This tactic simulates the invokation of
    [assert] over the desired specification for [f]. The tactic [xfun] takes as
    argument the desired specification for the function. For example, in the
    proof of [incrtwice] we will use a call of the form:

    xfun (fun f => forall (m:int),
      triple <{ f () }> (p ~~> m) (fun _ => p ~~> (m+1)))
*)

Lemma xfun_lemma : forall (Sof:val->Prop) H v1 F2of Q,
  Sof v1 ->
  (forall x, Sof x -> H ==> F2of x Q) ->
  H ==> wpgen_let (mkstruct (wpgen_val v1)) F2of Q.
Proof using. introv Sf M. applys xletval_lemma. intros ? ->. applys* M. Qed.

Tactic Notation "xfun" constr(Sof) :=
  let f := fresh in let Hf := fresh in
  xstruct_if_needed; applys (@xfun_lemma Sof).

(** We are ready, at last, to show an elegant proof script for [incrtwice]. *)

Lemma triple_incrtwice_with_xfun : forall (p:loc) (n:int),
  triple (incrtwice p)
    (p ~~> n)
    (fun _ => p ~~> (n+2)).
Proof using.
  xwp.
(** The key step is to invoke [xfun] by providing the desired specification for
    the local function [f]. *)
  xfun (fun (f:val) => forall (m:int),
    triple <{ f () }> (p ~~> m) (fun _ => p ~~> (m+1))).
(** The verification of the local function [f] is similar to that of any
    top-level function. *)
  { xwp. xapp. xsimpl. }
(** There remains to assign a name to the function and its specification. *)
  intros f Sf.
(** The rest of the proof is the same as before. *)
  xapp.
  xapp.
  xsimpl.
  math.
Qed.

(** In summary, we have presented the tactic [xfun] for reasoning about local
    functions using the exact same mechanisms as for reasoning about top-level
    functions. The only difference is that the specification is not provided by
    the user as a lemma, but as an argument to [xfun]. Using the tactic [xfun]
    leads to modular proofs, whereby the body of the local function is only
    processed once by the user. *)

(* ----------------------------------------------------------------- *)
(** *** 3. Exercises on Local Functions *)

(** This section presents an exercice involving the verification of a program
    featuring a simple local functions, which consists of the 'successor'
    function.

OCaml:

  fun n ->
    let f = (fun m -> m + 1) in
    let a = f 2 in
    f a
*)

Definition succtwice : val :=
  <{ fun 'n =>
       let 'f = (fun_ 'm => 'm + 1) in
       let 'a = 'f 'n in
       'f 'a }>.

(** **** Exercise: 2 stars, standard, optional (triple_succtwice_using_xletval)

    Verify the function [succtwice] using [xletval] and [xappfun], without using
    [xfun]. *)

Lemma triple_succtwice_using_xletval : forall (n:int),
  triple (succtwice n)
    \[]
    (fun r => \[r = n + 2]).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (triple_succtwice_using_xfun)

    Verify the function [succtwice] using [xfun]. *)

Lemma triple_succtwice_using_xfun : forall (n:int),
  triple (succtwice n)
    \[]
    (fun r => \[r = n + 2]).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** A more challenging exercise, named [forloop], may be found near the end of
    the chapter. It can be resolved using the tactic [xfun], even without
    reading all the text from the 'optional material' section. *)

End ExampleLocalFunWpgen.

(* ================================================================= *)
(** ** Proof Structure and Proof Automation *)

(** When looking at a proof of the form [xwp. xapp. xapp. xapp. xsimpl.], where
    the application of tactics is fully directed by the code to be verified, one
    might wander why we do not take x-tactics one step further in terms of
    automation. Concretely, why not introduce a tactic for repeatedly applying
    the relevant x-tactics as far as possible?

    Such a tactic -- let's call it [xgo] -- can indeed be defined, and can prove
    handy for proving short programs compactly. However, it often turns out to
    be counterproductive when verifying nontrivial programs. Let us explain why.

    In a nontrivial proof, calls to x-tactics do not appear in sequence: they
    are interleaved with conventional Coq tactics for discharging side
    conditions. Typically, when reasoning about a function whose specification
    contains preconditions, [xapp] generates one subgoal for each precondition.
    Now, suppose that we have a sequence made of 3 such function calls. The
    proof script would look like:

    xapp. { prove_side_1_1. } { prove_side_1_2. }
    xapp. { prove_side_2_1. } { prove_side_2_2. } { prove_side_2_3. }
    xapp. { prove_side_3_1. } { prove_side_3_2. } { prove_side_3_3. }

    If we use [xgo] instead of 3 calls to [xapp], we replace 3 calls to [xapp]
    with a single call to [xgo], which may seem at first sight like to be
    improvement. However, the proof script now looks like:

    xgo. { prove_side_1_1. } { prove_side_1_2. }
    { prove_side_2_1. } { prove_side_2_2. } { prove_side_2_3. }
    { prove_side_3_1. } { prove_side_3_2. } { prove_side_3_3. }

    With [xgo], all the side-conditions are produced at once. Why is this a
    problem? Well suppose that either the code or the specifications of the
    functions being called are later modified. When we re-play the proof script
    with [xgo], a number of proof obligations will be added, others will be
    removed. The user will have no obvious way of associating proof obligations
    with the function call they arise from. In summary, in nontrivial proofs,
    the use of [xgo] just to make the proof script a tiny bit more concise makes
    proof scripts much harder to maintain.

    One way to make proof script more concise without harming maintainability is
    to use a tactic call [xstep]. A call to [xstep n] invokes [n] times in a row
    the relevant x-tactic, with only the last of these x-tactics being allowed
    to produce subgoals. With [xstep n], we are able to factorize consecutive
    calls to certain x-tactics, yet we are forced to keep all the x-tactics that
    participate in structuring the proof scripts.

    A useful generalization is the tactic [xstep* n], which is like [xstep n]
    except that the x-tactics before the last one are allowed to produce
    subgoals as long as these subgoals are all solved by automation. The tactic
    [xgo*] can now be defined as [xstep* n] for the maximal possible value of
    [n], with a check that all the code has been processed, i.e., that the point
    of a [xsimpl] has been reached. Examples of usage of [xstep] and [xgo] are
    beyond the scope of this course. *)

(* ################################################################# *)
(** * Optional Material *)

(* ================================================================= *)
(** ** Additional Tactics [xconseq] and [xframe] *)

(** The tactic [xconseq] applies the weakening rule; from the perspective of the
    user, it replaces the current postcondition with a stronger one. Optionally,
    the tactic can be passed an explicit argument, using the syntax [xconseq Q].

    The tactic is implemented by applying the lemma [xconseq_lemma], stated
    below. *)

Lemma xconseq_lemma : forall Q1 Q2 H F,
  H ==> mkstruct F Q1 ->
  Q1 ===> Q2 ->
  H ==> mkstruct F Q2.

(** **** Exercise: 1 star, standard, optional (xconseq_lemma)

    Prove the [xconseq_lemma]. *)

Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

Tactic Notation "xconseq" :=
  applys xconseq_lemma.

Tactic Notation "xconseq" constr(Q) :=
  applys xconseq_lemma Q.

(** The tactic [xframe] enables applying the frame rule on a formula produced by
    [wpgen]. The syntax [xframe H] is used to specify the heap predicate to
    keep, and the syntax [xframe_out H] is used to specify the heap predicate to
    frame out---everything else is kept. *)

Lemma xframe_lemma : forall H1 H2 H Q Q1 F,
  H ==> H1 \* H2 ->
  H1 ==> mkstruct F Q1 ->
  Q1 \*+ H2 ===> Q ->
  H ==> mkstruct F Q.

(** **** Exercise: 2 stars, standard, optional (xframe_lemma)

    Prove the [xframe_lemma]. Exploit the properties of [mkstruct]; do not try
    to unfold the definition of [mkstruct]. *)

Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

Tactic Notation "xframe" constr(H) :=
  eapply (@xframe_lemma H); [ xsimpl | | ].

Tactic Notation "xframe_out" constr(H) :=
  eapply (@xframe_lemma _ H); [ xsimpl | | ].

(** Let's illustrate the use of [xframe] on an example. *)

Module ProofsWithStructuralXtactics.
Import ExamplePrograms.
Open Scope wpgen_scope.

Lemma triple_incr_frame : forall (p q:loc) (n m:int),
  triple (trm_app incr p)
    (p ~~> n \* q ~~> m)
    (fun _ => (p ~~> (n+1)) \* (q ~~> m)).
Proof using.
  xwp.
(** Instead of calling [xapp], we put aside [q ~~> m] and focus on [p ~~> n]. *)
  xframe (p ~~> n). (* equivalent to [xframe_out (q ~~> m)].

    Then we can work in a smaller state that mentions only [p ~~> n]. *)
  xapp. xapp. xapp.
(** Finally we check the check that the current state augmented with the framed
    predicate [q ~~> m] matches with the claimed postcondition. *)
  xsimpl.
Qed.

End ProofsWithStructuralXtactics.

(* ================================================================= *)
(** ** Evaluation of [wpgen] Recursively inside Local Functions *)

Module WPgenRec.
Implicit Types vx vf : val.

(* ----------------------------------------------------------------- *)
(** *** 1. Motivation for [wpgen] to Recurse in Local Functions *)

(** So far in the chapter, in the definition of [wpgen], we have treated the
    constructions [trm_fun] and [trm_fix] as terms directly constructing a
    value, following the same pattern as for the construction [trm_val].

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_val v      => Q v
      | trm_fun x t1   => Q (val_fun x t1)
      | trm_fix f x t1 => Q (val_fix f x t1)
      ...
      end.

    This section explains how to extend the definition of [wpgen] to make it
    recurse inside the body of the function definitions. Doing so does not
    increase expressiveness, because the user had the possibility of manually
    requesting the computation of [wpgen] on a function value of the form
    [val_fun] or [val_fix]. However, having [wpgen] automatically recurse into
    function bodies simplifies and improves the efficiency of the implementation
    of the [xfun] tactic.

    The new definition of [wpgen] takes the shape shown below, for well-suited
    definitions of [wpgen_fun] and [wpgen_fix] yet to be introduced. In the code
    snippet below, [vx] denotes a value to which the function may be applied,
    and [vf] denotes the value associated with the function itself. This value
    is involved where the function defined by [trm_fix f x t1] invokes itself
    recursively inside its body [t1].

    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      mkstruct match t with
      | trm_val v      => wpgen_val v
      | trm_fun x t1   => wpgen_fun (fun vx => wpgen ((x,vx)::E) t1)
      | trm_fix f x t1 => wpgen_fix (fun vf vx => wpgen ((f,vf)::(x,vx)::E) t1)
      ...
      end.
*)

(* ----------------------------------------------------------------- *)
(** *** 2. A New Definition of [wpgen] that Recurses in Local Functions *)

(** For simplicity, let us assume for now the substitution context [E] to be
    empty and ignore the presence of the predicate [mkstruct]. Our first task is
    to provide a definition for [wpgen (trm_fun x t1) Q], expressed in terms of
    [wpgen t1].

    Let [vf] denote the function [val_fun x t1], which the term [trm_fun x t1]
    evaluates to. The heap predicate [wpgen (trm_fun x t1) Q] should assert that
    that the postcondition [Q] holds of the result value [vf], i.e., that [Q vf]
    should hold.

    Rather than specifying that [vf] is equal to [val_fun x t1] as we were doing
    previously, we would like to specify that [vf] denotes a function whose body
    admits [wpgen t1] as weakest precondition. To that end, we define the heap
    predicate [wpgen (trm_fun x t1) Q] to be of the form
    [\forall vf, \[P vf] \-* Q vf] for a carefully crafted predicate [P] that
    describes the behavior of the function by means of its weakest precondition.
    This predicate [P] is defined further on.

    The universal quantification on [vf] is intended to hide away from the user
    the fact that [vf] actually denotes [val_fun x t1]. It would be correct to
    replace [\forall vf, ...] with [let vf := val_fun x t1 in ...], yet we are
    purposely trying to abstract away from the syntax of [t1], hence the
    universal quantification of [vf].

    In the heap predicate [\forall vf, \[P vf] \-* Q vf], the magic wand
    features a left-hand side of the form [\[P vf]] intended to provide to the
    user the knowledge of the weakest precondition of the body [t1] of the
    function, in such a way that the user is able to derive the specification
    aimed for the local function [vf].

    Concretely, the proposition [P vf] should enable the user establishing
    properties of applications of the form [trm_app vf vx], where [vf] denotes
    the function and [vx] denotes an argument to which the function is applied.

    To figure out the details of the statement of [P], it is useful to recall
    from chapter [WPgen] the statement of the lemma
    [triple_app_fun_from_wpgen], which we used for reasoning about top-level
    functions. *)

Parameter triple_app_fun_from_wpgen : forall vf vx x t1 H' Q',
  vf = val_fun x t1 ->
  H' ==> wpgen ((x,vx)::nil) t1 Q' ->
  triple (trm_app vf vx) H' Q'.

(** The lemma above enables establishing a triple for an application
    [trm_app vf vx] with precondition [H'] and postcondition [Q'], from the
    premise [H' ==> wgen ((x,vx)::nil) t1 Q'].

    It therefore makes sense, in our definition of the predicate
    [wpgen (trm_fun x t1) Q], which we said would take the form
    [\forall vf, \[P vf] \-* Q vf], to define [P vf] as:

    forall vx H' Q', (H' ==> wpgen ((x,vx)::nil) t1 Q') ->
                     triple (trm_app vf vx) H' Q'

    Overall, the definition of [wpgen E t] is as follows. Note that the
    occurence of [nil] is replaced with [E] to account for the case of a
    nonempty context.

  Fixpoint wpgen (E:ctx) (t:trm) : formula :=
    mkstruct match t with
    ...
    | trm_fun x t1 => fun Q =>
       let P vf :=
         (forall vx H' Q',
            H' ==> wpgen ((x,vx)::E) t1 Q' ->
            triple (trm_app vf vx) H' Q') in
       \forall vf, \[P vf] \-* Q vf
   ...
   end.
*)

(** The actual definition of [wpgen] exploits an intermediate definition called
    [wpgen_fun], as shown below:

    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      mkstruct match t with
      ...
      | trm_fun x t1 => wpgen_fun (fun vx => wpgen ((x,vx)::E) t1)
      ...
      end.

    where [wpgen_fun] could be defined as follows: *)

Definition wpgen_fun' (Fof:val->formula) : formula := fun Q =>
  \forall vf, \[forall vx H' Q',
                  H' ==> Fof vx Q' ->
                  triple (trm_app vf vx) H' Q']
              \-* Q vf.

(** In the definition above, the assumption about [vf], enclosed above in
    brackets, can be slightly simplfied, by using [wp] instead of [triple],
    allowing to eliminate [H']. This observation leads to a more concise
    definition of [wpgen_fun]. *)

Definition wpgen_fun (Fof:val->formula) : formula := fun Q =>
  \forall vf, \[forall vx Q', Fof vx Q' ==> wp (trm_app vf vx) Q'] \-* Q vf.

(** **** Exercise: 2 stars, standard, optional (wpgen_fun_eq)

    Prove that [wpgen_fun'] is equivalent to [wpgen_fun]. *)

Lemma wpgen_fun_eq :
  wpgen_fun = wpgen_fun'.
Proof using.
  unfold wpgen_fun, wpgen_fun'. applys fun_ext_2.
  intros Fof Q. applys himpl_antisym.
 { applys himpl_hforall_r. intros vf. xchange (hforall_specialize vf).
   xsimpl. intros M. rewrite hwand_hpure_l. xsimpl.
   introv. rewrite wp_equiv. applys M. xsimpl. }
 (* FILL IN HERE *) Admitted.

(** [] *)

(** Like for other auxiliary functions associated with [wpgen], we introduce a
    custom notation for [wpgen_fun]. Here, we let [Fun x := F] stand for
    [wpgen_fun (fun x => F)]. *)

Notation "'Fun' x ':=' F1" :=
  ((wpgen_fun (fun x => F1)))
  (at level 69, x name, right associativity,
  format "'[v' '[' 'Fun'  x  ':='  F1  ']' ']'").

(* ----------------------------------------------------------------- *)
(** *** 3. Treatment of Recursive Functions *)

(** The formula produced by [wpgen] for a recursive function [trm_fix f x t1] is
    almost the same as for a non-recursive function. The main difference is that
    we need to add a binding in the context from the name [f] to the value [vf].
    Like for [trm_fun], the heap predicate [wpgen (trm_fix f x t1) Q] is of the
    form [\forall vf, \[P vf] \-* Q vf]. The predicate [P] is similar to that
    for [trm_fun], the only difference is that the context [E] needs to be
    extended not with one but with two bindings: one for the argument, and one
    for the function. Concretely, [P] is defined as:

    forall vx H' Q',
      H' ==> wpgen ((f,vf)::(x,vx)::E) t1 Q' ->
      triple (trm_app vf vx) H' Q'

    Like for [wpgen_fun], we can make the definition more concise by eliminating
    [H']. Concretely, we define: *)

Definition wpgen_fix (Fof:val->val->formula) : formula := fun Q =>
  \forall vf, \[forall vx Q', Fof vf vx Q' ==> wp (trm_app vf vx) Q'] \-* Q vf.

(** Then we integrate this definition is [wpgen] as shown below.

    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      mkstruct match t with
      | ..
      | trm_fix f x t1 => wpgen_fix (fun vf v => wpgen ((f,vf)::(x,v)::E) t1)
      | ..
      end
*)

(** Here again, we introduce a piece of notation for [wpgen_fix]. We let
    [Fix f x := F] stand for [wpgen_fix (fun f x => F)]. *)

Notation "'Fix' f x ':=' F1" :=
  ((wpgen_fix (fun f x => F1)))
  (at level 69, f name, x name, right associativity,
  format "'[v' '[' 'Fix'  f  x  ':='  F1  ']' ']'").

(* ----------------------------------------------------------------- *)
(** *** 4. Final Definition of [wpgen], with Processing a Local Functions *)

(** The final definition of [wpgen], including the recursive processing of local
    function definitions, appears below. Note that we here aim at supporting
    only local functions with one argument. The proper treatment of n-ary local
    functions would require a nested recursive function for accumulating the
    list of arguments involved in each local function. It is beyond the scope of
    this course. *)

Fixpoint wpgen (E:ctx) (t:trm) : formula :=
  mkstruct match t with
  | trm_val v => wpgen_val v
  | trm_var x => wpgen_var E x
  | trm_fun x t1 => wpgen_fun (fun v => wpgen ((x,v)::E) t1)
  | trm_fix f x t1 => wpgen_fix (fun vf v => wpgen ((f,vf)::(x,v)::E) t1)
  | trm_app t1 t2 => wpgen_app (isubst E t)
  | trm_seq t1 t2 => wpgen_seq (wpgen E t1) (wpgen E t2)
  | trm_let x t1 t2 => wpgen_let (wpgen E t1) (fun v => wpgen ((x,v)::E) t2)
  | trm_if t0 t1 t2 => wpgen_if (isubst E t0) (wpgen E t1) (wpgen E t2)
  end.

(* ----------------------------------------------------------------- *)
(** *** 5. Tactic for Reasoning About Functions *)

(** This section refines the tactic [fun], to reflect on the fact that the new
    definition of [wpgen] removes the need for the user to invoke [xwp] by hand
    for reasoning about the body of local functions. The tactic [xfun] presented
    here may be invoked either with or without providing a specification for the
    local function. If no specification is provided, the formula associated with
    the local function is taken as specification. This formula corresponds to
    the "most general specification" of the function. Exploiting this formula
    has a similar effect as inlining the code of the local function.

    First, we describe the tactic [xfun S], where [S] describes the
    specification of the local function. A typical call is of the form
    [xfun (fun (f:val) => forall ..., triple (f ..) .. ..)]. The tactic [xfun S]
    generates two subgoals. The first one requires the user to establish the
    specification [S] for the function. The second one requires the user to
    prove that the rest of the program is correct, in a context where the local
    function can be assumed to satisfy the specification [S]. The definition of
    [xfun S] appears next. It is not required to understand the details. An
    example use case appears further on. *)

Lemma xfun_spec_lemma : forall (S:val->Prop) H Q Fof,
  (forall vf,
    (forall vx H' Q', (H' ==> Fof vx Q') -> triple (trm_app vf vx) H' Q') ->
    S vf) ->
  (forall vf, S vf -> (H ==> Q vf)) ->
  H ==> wpgen_fun Fof Q.
Proof using.
  introv M1 M2. unfold wpgen_fun. xsimpl. intros vf N.
  applys M2. applys M1. introv K. rewrite <- wp_equiv.
  applys himpl_trans_r K. applys N.
Qed.

Tactic Notation "xfun" constr(S) :=
  xseq_xlet_if_needed; xstruct_if_needed; applys xfun_spec_lemma S.

(** Second, we describe the tactic [xfun] with no argument. It applies to a goal
    of the form [H ==> wpgen_fun Fof Q]. The tactic [xfun] simply provides an
    hypothesis about the local function. The user may subsequently exploit this
    hypothesis for reasoning about a call to that function, just like if the
    code of the function was inlined at its call site. In practice, the use of
    [xfun] without argument is most relevant for local functions that are
    invoked exactly once. For example, higher-order iterators such as
    [List.iter] or [List.map] are typically invoked with an ad-hoc functions
    that appears exactly once. *)

Lemma xfun_nospec_lemma : forall H Q Fof,
  (forall vf,
     (forall vx H' Q', (H' ==> Fof vx Q') -> triple (trm_app vf vx) H' Q') ->
     (H ==> Q vf)) ->
  H ==> wpgen_fun Fof Q.
Proof using.
  introv M. unfold wpgen_fun. xsimpl. intros vf N. applys M.
  introv K. rewrite <- wp_equiv. applys himpl_trans_r K. applys N.
Qed.

Tactic Notation "xfun" :=
  xseq_xlet_if_needed; xstruct_if_needed; applys xfun_nospec_lemma.

(** A generalization of [xfun] that handles recursive functions may be defined
    following exactly the same pattern. Details may be found in the file
    [LibSepReference.v] *)

(** This completes our presentation of a version of [wpgen] that recursively
    processes the local definition of non-recursive functions. A practical
    example is presented next. *)

(* ----------------------------------------------------------------- *)
(** *** 6. Example Revisited with the New [wpgen] *)

Module ExampleLocalFunWpgenRec.
Import DemoPrograms ExampleLocalFunWpgen.

(** We import here the definitions from [LibSepReference], which provides the a
    definition of [wpgen] that recurse in function bodies exactly as defined in
    subsection #4 above, and which defines all the other x-tactics as previously
    but for this recursive version of [wpgen]. *)

Import LibSepReference.
Open Scope wp_scope.

(** Consider again the example program [myincr], whose code is:

OCaml:

  fun p ->
    let f = (fun () -> incr p) in
    f();
    f()
*)

(** We first illustrate a call to [xfun] with an explicit specification. Here,
    the function [f] is specified as incrementing the reference [p]. Observe
    that the body function of the function [f] is verified only once. The
    reasoning about the two calls to the function [f] that appears in the code
    are done with respect to the specification that we provide as argument to
    [xfun] in the proof script. *)

Lemma triple_incrtwice : forall (p:loc) (n:int),
  triple (trm_app incrtwice p)
    (p ~~> n)
    (fun _ => p ~~> (n+2)).
Proof using.
  xwp.
  xfun (fun (f:val) => forall (m:int),
    triple (f())
      (p ~~> m)
      (fun _ => p ~~> (m+1))); intros f Hf.
  { intros.
    applys Hf. (* [Hf] is the name of the hypothesis on the body of [f] *)
    clear Hf.
    xapp. (* exploits [triple_incr] *) xsimpl. }
  xapp. (* exploits [Hf]. *)
  xapp. (* exploits [Hf]. *)
  xsimpl. math.
Qed.

(** We next illustrate a call to [xfun] without argument. The "generic
    specification" that comes as hypothesis about the local function is a
    proposition that describes the behavior of the function in terms of the
    weakest-precondition of its body. When reasoning about a call to the
    function, one can invoke this generic specification. The effect is
    equivalent to that of inlining the code of the function at its call site.
    The example shown below contains two calls to the function [f]. The script
    invokes [xfun] without argument. Then, each of the two calls to [f] executes
    a call to [incr]. Thus the proof script involves two calls to [xapp] that
    each exploit the specification [triple_incr]. *)

Lemma triple_incrtwice' : forall (p:loc) (n:int),
  triple (trm_app incrtwice p)
    (p ~~> n)
    (fun _ => p ~~> (n+2)).
Proof using.
  xwp.
  xfun; intros f Hf.
  xapp. (* exploits [Hf] *)
  xapp. (* exploits [triple_incr] *)
  xapp. (* exploits [Hf] *)
  xapp. (* exploits [triple_incr] *)
  xsimpl. math.
Qed.

(* ----------------------------------------------------------------- *)
(** *** 7. Exercise on a Local Recursive Function *)

(** Consider a program that uses a local function to encode a for-loop. This
    program generalizes the [repeat] program presented in the chapter
    [Repr]. The loop function takes as argument the loop bounds [a] and
    [b], as well a function [f] describing the body of the loop. A locally
    defined, recursive function named [g] is used to execute [f i] for every
    integer value of [i] in the range from [a] inclusive to [b] exclusive.

OCaml:

  fun a b f ->
    let g = (fix g i -> if i < b then (f i; g (i+1)) end) in
    g a
*)

Definition forloop : val :=
  <{ fun 'a 'b 'f =>
       let 'g = (fix_ 'g 'i =>
          let 'c = 'i < 'b in
          if 'c then
            'f 'i ;
            let 'j = 'i + 1 in
            'g 'j
          end) in
       'g 'a }>.

(** Like for the function [repeat], the specification of [forloop] is expressed
    using an invariant, named [I], of type [int->hprop]. The hypothesis on [f]
    asserts that a call to [f i] takes a state satisfying [I i] to a state
    satisfying [I (i+1)]. For simplicity, we specify the function only in the
    case where [a <= b]. *)

(** **** Exercise: 4 stars, standard, especially useful (triple_forloop)

    Verify the function [forloop]. Hint: provide the specification of [g] to
    [xfun]. To set up the induction, use the sequence:
    [intros i. induction_wf IH: (upto b) i. intros Hi.]. Besides, the tactics
    [math_rewrite] is helpful at one point in the proof. *)

Lemma triple_forloop : forall (I:int->hprop) (a b:int) (f:val),
  a <= b ->
  (forall i, a <= i <= b ->
    triple (f i)
      (I i)
      (fun u => I (i+1))) ->
  triple (forloop a b f)
    (I a)
    (fun r => I b).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End ExampleLocalFunWpgenRec.
End WPgenRec.

(* ================================================================= *)
(** ** Historical Notes *)

(** Many verification tools for Hoare Logic are based on weakest-precondition
    generators. Typically, a tool takes as input source code annotated with
    specifications and invariants and produces a logical formula that entails
    the correctness of the program. This logical formula is typically expressed
    in first-order logic and is discharged using automated tools such as SMT
    solvers.

    In contrast, the weakest-precondition generator presented in this chapter
    applies to un-annotated code. It thus produces a logical formula that does
    not depend at all on the specifications and invariants. Such formula, which
    can be constructed in a systematic manner, is called a "characteristic
    formula" in the literature. The notion of characteristic formulae was
    introduced in work by [Hennessy and Milner 1985] (in Bib.v) on process calculi. It
    was first applied to program logics by
    [Honda, Berger, and Yoshida 2006] (in Bib.v) and to Separation Logic in the PhD
    work of [Charguéraud 2010] (in Bib.v), which led to CFML.

    In general, a characteristic formula provides not just a sound but also a
    complete description of the semantics of a program. In Charguéraud's PhD
    thesis, completeness is established on paper, and a mechanized proof in Coq
    is provided only for the simple IMP language. Even if a result of the form
    [wp t Q ==> wpgen t Q] were proved in Coq, such a completeness result would
    be relatively unsatisfying. Indeed, this entailment asserts that if a
    program admits a behavior, then the program logic can be used to establish
    that this program admits that behavior. Yet, this statement does not capture
    the existence of a _pretty_ Separation Logic proof featuring local reasoning
    --that is, allowing for maximal usage of the frame rule. *)

(* 2024-12-26 10:22 *)
