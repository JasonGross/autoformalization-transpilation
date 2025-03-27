(** * Triples: Structural Reasoning Rules *)

Set Implicit Arguments.

(** The file [LibSepReference.v] contains definitions that are essentially the
    same as those from [Hprop.v] and [Himpl.v], but with one key difference:
    [LibSepReference] makes the definition of Separation Logic operators opaque.
    This chapter and the following ones import [LibSepReference.v] instead of
    [Hprop.v] and [Himpl.v].

    As a result, we cannot unfold the definition of [hstar], [hpure], etc. any
    more. To reason, we must instead use the introduction and elimination
    lemmas, such as [hstar_intro] and [hstar_elim]. These lemmas enforce
    abstraction, ensuring that the proofs do not depend on the particular choice
    of the definitions used for constructing Separation Logic. For example, we
    should not depend on whether [\[P]] is internally implemented as
    [fun h => h = empty /\ P] or as [\exists (p:P), \[]]. *)

From SLF Require Export LibSepReference.
From SLF Require Basic.

(* ################################################################# *)
(** * First Pass *)

(** In chapter [Hprop], we formalized heap predicates, of type [hprop], and
    several operators on them: [\[]], [\[P]], [p ~~> v], [H1 \* H2],
    [Q1 \*+ H2], and [\exists x, H]. In chapter [Himpl], we formalized the
    heap entailment relations [H1 ==> H2] and [Q1 ===> Q2]. The goal of the
    present chapter and the next one is to formalize the definition of triples,
    written [triple t H Q], and the reasoning rules of Separation Logic.

    More precisely, the present chapter focuses on the definition of triples and
    the proofs of the "structural rules", which are essential in particular for
    implementing the tactics [xpull] and [xapp]. The structural rules include
    the "frame rule", which lies at the heart of Separation Logic, as well as
    the "consequence rule" and two "extraction rules", which admit similar
    statements as in Hoare Logic. The reasoning rules concerned with term
    constructs are discussed in the next chapter ([Rules]).

    This chapter starts with a formalization of the syntax and the semantics of
    the programming language we are using for examples. The semantics is
    axiomatized using a variant of big-step semantics called "omni-big-step
    semantics". This presentation is well suited for capturing safety and
    termination in nondeterministic programming languages. Near the end of the
    chapter, we explain how an omni-big-step semantics can be formally related
    to a standard small-step semantics. *)

(** This chapter exploits a few additional TLC tactics to enable concise proofs.
    Recall from chapter [Himpl] that [applys] is an enhanced version of
    [eapply], which takes as argument a lemma or hypothesis, followed by a
    variable number of arguments, which are fed to the lemma on a first-match
    basis. For example, [applys L x y] is equivalent to
    [eapply (L _ _ .. _ x _ _ .. _ _ y _ _ ..)] for an appropriate number of
    underscore symbols.

    Likewise, the tactics [lets], [forwards], and [specializes] can be used to
    instantiate a lemma or an existing hypothesis:

    - [lets H: L x y] introduces an hypothesis named [H], whose statement
      is the specialization of the lemma [L] on the arguments [x] and [y].
      It is equivalent to [generalize (L _ _ .. _ x _ _ .. _ _ y); intros H],
      for the appropriate number of underscore symbols.
    - [forwards H: L x y] is very similar to [lets], except that it attempts
      to instantiate all arguments of [L]. It is equivalent to
      [generalize (L _ _ .. _ x _ _ .. _ _ y _ _ .. _ _); intros H].
    - [specializes H x y] specializes an existing hypothesis [H] in place.
      It is equivalent to [lets H2: H x y; clear H; rename H2 into H].

    The reader will find many occurrences of these tactics in proofs and
    solutions. However, exploiting these tactics is never required for solving
    exercises. *)

(* ================================================================= *)
(** ** Formalized Syntax of the Programming Language *)

(** In what follows, we present the formalization of the syntax of the
    programming language. This material corresponds to a large subset of the
    material from the file [LibSepReference]. Further on in this file, we will
    want to refer to the definitions from [LibSepReference], to avoid having to
    copy-paste all the construction of Separation Logic operators, which depend
    on the type [heap] and therefore depend on the type [val] associated with
    program values. Hence, we wrap the definitions of syntax presented below
    inside a module. *)

Module Syntax.

(* ----------------------------------------------------------------- *)
(** *** Values and Terms *)

(** The syntax of our example programming language is described using an
    _abstract syntax tree_. Its presentation distiguishes between closed values
    (i.e., values with no free variables inside) and terms. This presentation
    simplifies the definition and evaluation of the substitution function.
    Indeed, since values are always closed, the substitution function never
    needs to traverse through values.

    The grammar for values includes the unit value, booleans, integers,
    locations, functions, recursive functions, and primitive operations. For
    example, [val_int 3] denotes the integer value [3], while [val_fun x t]
    denotes the function [fun x => t], and [val_fix f x t] denotes the function
    [fix f x => t], which is written [let rec f x = t in f] in OCaml syntax.

    For conciseness, we include just a few primitive operations: [val_ref],
    [val_get], [val_set], and [val_free] for manipulating the mutable state,
    [val_add] to illustrate a simple arithmetic operation, [val_div] to
    illustrate a partial operation, and [val_rand] to illustrate nondeterminism.
    *)

Inductive val : Type :=
  | val_unit : val
  | val_bool : bool -> val
  | val_int : int -> val
  | val_loc : loc -> val
  | val_fun : var -> trm -> val
  | val_fix : var -> var -> trm -> val
  | val_ref : val
  | val_get : val
  | val_set : val
  | val_free : val
  | val_add : val
  | val_div : val
  | val_rand : val

(** The grammar for terms includes values, variables, function definitions,
    recursive function definitions, function applications, sequences,
    let-bindings, and conditionals. *)

with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_fun : var -> trm -> trm
  | trm_fix : var -> var -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_seq : trm -> trm -> trm
  | trm_let : var -> trm -> trm -> trm
  | trm_if : trm -> trm -> trm -> trm.

(** Note that [trm_fun] and [trm_fix] denote functions that may feature free
    variables, unlike [val_fun] and [val_fix], which denote closed values. More
    concretely, in the term [trm_fun x t], the term [t] may refer to the
    variable [x] or to other free variables. In contrast, in the term
    [val_fun x t], the only free variable that [t] may have is [x].

    We will see, below, evaluation rules asserting that [trm_fun x t] reduces,
    in the empty context, to [val_fun x t]. Likewise, [trm_fix f x t] reduces,
    in the empty context, to [val_fix f x t].

    At a high level, the term [val_fun x t] may be thought of as the term
    [trm_fun x t] augmented with a proof that this term [trm_fun x t] is a
    closed term. The syntax that we consider therefore embeds "proofs that
    values are closed". Thanks to this presentation, the substitution function
    [subst], which will be presented shortly afterwards, need not recurse
    through values. Moreover, we never need to manipulate proofs that specific
    terms are closed. *)

(** Functions of several arguments are encoded as nested functions (curried
    functions). For example, the syntax [fun x1 x2 x3 => t] used to define a
    top-level function in the chapters [Basic] and [Repr] is encoded as
    [val_fun x1 (trm_fun x2 (trm_fun x3 t))]. Observe how the outer constructor
    asserts that the whole function is a closed value, whereas the inner
    functions are terms. In particular [t] may refer to [x1] and [x2], which are
    free variables for the term [trm_fun x3 t].

    Likewise, a closed recursive function [fix f x1 x2 x3 => t] is encoded as
    [val_fix f x1 (trm_fun x2 (trm_fun x3 t))]. Here only the outermost function
    is recursive (and closed).

    In the rest of the course, we will focus on functions with a single
    argument. The treatment of n-ary functions is the topic of a
    yet-to-be-released chapter. *)

(* ----------------------------------------------------------------- *)
(** *** State *)

(** The language we consider is imperative, with primitive functions for
    manipulating the state. Thus, the statements of the evaluation rules involve
    memory states. *)

(** Recall from chapter [Hprop] that a state is represented as a finite map
    from location to values. Finite maps are presented using the type [fmap].
    Details of the construction of finite maps may be found in the file
    [LibSepFmap.v]. (The construction is beyond the scope of this course,
    because it leverages dependent pairs to realize the type of finite maps.) *)

Definition heap : Type := fmap loc val.

(** For technical reasons related to the internal representation of finite maps,
    to enable reading in a state, we need to justify that the grammar of values
    is inhabited. This property is captured by the following command, whose
    details are not relevant for understanding the rest of the chapter. *)

Global Instance Inhab_val : Inhab val.
Proof using. apply (Inhab_of_val val_unit). Qed.

(* ----------------------------------------------------------------- *)
(** *** Substitution *)

(** The semantics of the evaluation of a program function is described by means
    of a substitution function, written [subst y w t], which replaces all
    occurrences of a variable [y] with a value [w] inside a term [t].

    The substitution function is always the identity on values, because our
    language only considers closed values. In other words, we define
    [subst y w (trm_val v) = (trm_val v)].

    When it reaches a variable, substitution performs a comparison between two
    variables. To that end, it exploits the comparison function [var_eq x y],
    which produces a boolean value indicating whether [x] and [y] denote the
    same variable. *)

(** The remainder of this subsection describes the implementation of the
    substitution function [subst]. This operation traverses all other language
    constructs in a structural manner. It takes care of avoiding "variable
    capture" when traversing binders: [subst y w t] does not recurse below the
    scope of binders whose bound name is equal to [y]. For example, the result
    of [subst y w (trm_let x t1 t2)] is
    [trm_let x (subst y w t1) (if var_eq x y then t2 else (subst y w t2))].

    The auxiliary function [if_y_eq], which appears in the definition of
    [subst], helps factorizing the comparisons required to prevent variable
    capture. *)

Fixpoint subst (y:var) (w:val) (t:trm) : trm :=
  let aux t := subst y w t in
  let if_y_eq x t1 t2 := if var_eq x y then t1 else t2 in
  match t with
  | trm_val v => trm_val v
  | trm_var x => if_y_eq x (trm_val w) t
  | trm_fun x t1 => trm_fun x (if_y_eq x t1 (aux t1))
  | trm_fix f x t1 => trm_fix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1)))
  | trm_app t1 t2 => trm_app (aux t1) (aux t2)
  | trm_seq t1 t2 => trm_seq  (aux t1) (aux t2)
  | trm_let x t1 t2 => trm_let x (aux t1) (if_y_eq x t2 (aux t2))
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  end.

(* ----------------------------------------------------------------- *)
(** *** Implicit Types and Coercions *)

(** To improve the readability of the evaluation rules below, we take advantage
    of Coq's _implicit types_ and _coercions_.

    First off, we give several Implicit Types declarations. For example, the
    first command indicates that variables whose name begins with the letter 'b'
    are, by default, of type [bool]. *)

Implicit Types b : bool.
Implicit Types v r : val.
Implicit Types t : trm.

(** Next, we give a collection of coercions. Coercions correspond to implicit
    function calls, which aim to make statements more concise. For example,
    [val_loc] is declared as a coercion, so that a location [p] of type [loc]
    can be viewed as the value [val_loc p] where an expression of type [val] is
    expected. Likewise, a boolean [b] may be viewed as the value [val_bool b],
    and an integer [n] may be viewed as the value [val_int n]. *)

Coercion val_loc : loc >-> val.
Coercion val_bool : bool >-> val.
Coercion val_int : Z >-> val.

(** The constructor [trm_val] is also declared as a coercion. Thus, instead of
    writing [trm_val v] at a place where a term is expected, we can write just
    [v]. *)

Coercion trm_val : val >-> trm.

(** The constructor [trm_app] is declared as a "Funclass" coercion. This bit of
    magic enables us to write [t1 t2] as a shorthand for [trm_app t1 t2]. The
    idea of associating [trm_app] as the "Funclass" coercion for the type [trm]
    is that if a term [t1] of type [trm] is applied like a function to an
    argument, then [t1] should be interpreted as [trm_app t1]. *)

Coercion trm_app : trm >-> Funclass.

(** The "Funclass" coercion for [trm_app] can be iterated. The expression
    [t1 t2 t3] is parsed by Coq as [(t1 t2) t3]. The first application [t1 t2]
    is interpreted as [trm_app t1 t2]. This expression, which itself has type
    [trm], is applied to [t3]. Hence, [t1 t2 t3] is interpreted as
    [trm_app (trm_app t1 t2) t3]. *)

(* ----------------------------------------------------------------- *)
(** *** Loading Definitions from LibSepReference *)

(** As announced earlier, we will carry out proofs not with respect to the above
    definitions, but with respect to the definitions from [LibSepReference.v].

    Concretely, we close the scope of the module [Syntax], and re-enter the
    scope of the definitions from [LibSepReference]. *)

End Syntax.

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types p : loc.
Implicit Types n : int.
Implicit Types v w r : val.
Implicit Types t : trm.
Implicit Types h s : heap.
Implicit Types H : hprop.

(* ================================================================= *)
(** ** Formalized Semantics of the Programming Language *)

(* ----------------------------------------------------------------- *)
(** *** Standard Big-Step Semantics *)

(** We are now ready to present a formal semantics for the language. To begin
    with, we present a big-step evaluation judgment, written [big s t s' v].
    This judgment asserts that, starting from state [s], the evaluation of the
    term [t] terminates in a state [s'], and produces an output value [v].

    For simplicity, we assume terms to be in "A-normal form": the arguments of
    applications and of conditionals are restricted to variables and values.
    Such a requirement does not limit expressiveness, but it simplifies the
    statement of the evaluation rules.

    For example, if a source program includes a conditional [trm_if t0 t1 t2],
    then it is required that [t0] be either a variable or a value. This is not a
    real restriction, because [trm_if t0 t1 t2] can always be encoded as
    [let x = t0 in if x then t1 else t2].

    The big-step judgment is inductively defined as follows. By convention, we
    let [s] range over entire memory states, and let [h] range over pieces of
    states thay may correspond to a subset of the entire state. *)

Inductive big : heap -> trm -> heap -> val -> Prop :=

(** 1. [big] for values and function definitions.

      A value evaluates to itself. A term function evaluates to a value
      function. Likewise for a recursive function. *)

  | big_val : forall s v,
      big s (trm_val v) s v
  | big_fun : forall s x t1,
      big s (trm_fun x t1) s (val_fun x t1)
  | big_fix : forall s f x t1,
      big s (trm_fix f x t1) s (val_fix f x t1)

(** 2. [big] for function applications.

     The beta-reduction rule asserts that [(val_fun x t1) v2] evaluates to the
     same result as [subst x v2 t1]. Likewise, [(val_fix f x t1) v2] evaluates
     to [subst x v2 (subst f v1 t1)], where [v1] denotes the recursive function
     itself, that is, [val_fix f x t1]. *)

  | big_app_fun : forall s1 s2 v1 v2 x t1 v,
      v1 = val_fun x t1 ->
      big s1 (subst x v2 t1) s2 v ->
      big s1 (trm_app v1 v2) s2 v
  | big_app_fix : forall s1 s2 v1 v2 f x t1 v,
      v1 = val_fix f x t1 ->
      big s1 (subst x v2 (subst f v1 t1)) s2 v ->
      big s1 (trm_app v1 v2) s2 v

(** 3. [big] for structural constructs.

      A sequence [trm_seq t1 t2] first evaluates [t1], taking the state from
      [s1] to [s2], then drops the result of [t1] and evaluates [t2], taking the
      state from [s2] to [s3].

      The let-binding [trm_let x t1 t2] is similar, except that the variable [x]
      gets substituted with the result of [t1] inside [t2]. *)

  | big_seq : forall s1 s2 s3 t1 t2 v1 v,
      big s1 t1 s2 v1 ->
      big s2 t2 s3 v ->
      big s1 (trm_seq t1 t2) s3 v
  | big_let : forall s1 s2 s3 x t1 t2 v1 r,
      big s1 t1 s2 v1 ->
      big s2 (subst x v1 t2) s3 r ->
      big s1 (trm_let x t1 t2) s3 r

(** 4. [big] for conditionals.

      A conditional in a source program is assumed to be of the form
      [if t0 then t1 else t2], where [t0] is either a variable or a value. If
      [t0] is a variable, then, by the time it reaches an evaluation position,
      the variable must have been substituted by a value. Thus, the evaluation
      rule only considers the form [if v0 then t1 else t2]. The value [v0] must
      be a boolean value, otherwise evaluation gets stuck.

      The term [trm_if (val_bool true) t1 t2] behaves like [t1], whereas the
      term [trm_if (val_bool false) t1 t2] behaves like [t2]. This behavior is
      described by a single rule, leveraging Coq's "if" constructor to factor
      out the two cases. *)

  | big_if : forall s1 s2 b v t1 t2,
      big s1 (if b then t1 else t2) s2 v ->
      big s1 (trm_if (val_bool b) t1 t2) s2 v

(** 5. [big] for primitive stateless operations.

      For similar reasons, the behavior of applied primitive functions only
      needs to be described for the case of value arguments.

      An arithmetic operation expects integer arguments. The addition of
      [val_int n1] and [val_int n2] produces [val_int (n1 + n2)].

      The division operation, on the same arguments, produces the quotient
      [n1 / n2], under the assumption that the divisor [n2] is non-zero. In
      other words, if a program performs a division by zero, then it cannot
      satisfy the [big] judgment.

      The random number generator [val_rand n] produces an integer [n1] in the
      range from [0] (inclusive) to [n] (exclusive). *)

  | big_add : forall s n1 n2,
      big s (val_add (val_int n1) (val_int n2)) s (val_int (n1 + n2))
  | big_div : forall s n1 n2,
      n2 <> 0 ->
      big s (val_div (val_int n1) (val_int n2)) s (val_int (Z.quot n1 n2))
  | big_rand : forall s n n1,
      0 <= n1 < n ->
      big s (val_rand (val_int n)) s (val_int n1)

(** 6. [big] for primitive operations on memory.

      The term [val_ref v] allocates a fresh cell with contents [v] and returns
      the location, [p], of the new cell. This location must not be previously
      in the domain of the store [s].

      The term [val_get (val_loc p)] reads the value in the store [s] at
      location [p]. The location must be bound to a value in the store,
      otherwise evaluation is stuck.

      The term [val_set (val_loc p) v] updates the store at a location [p]
      assumed to be bound in the store [s]. The operation modifies the store and
      returns the unit value.

      The term [val_free (val_loc p)] deallocates the cell at location [p]. *)

  | big_ref : forall s v p,
      ~ Fmap.indom s p ->
      big s (val_ref v) (Fmap.update s p v) (val_loc p)
  | big_get : forall s p,
      Fmap.indom s p ->
      big s (val_get (val_loc p)) s (Fmap.read s p)
  | big_set : forall s p v,
      Fmap.indom s p ->
      big s (val_set (val_loc p) v) (Fmap.update s p v) val_unit
  | big_free : forall s p,
      Fmap.indom s p ->
      big s (val_free (val_loc p)) (Fmap.remove s p) val_unit.

(* ----------------------------------------------------------------- *)
(** *** Omni-Big-Step Semantics *)

(** A triple of the form [triple t H Q] aims to capture the property that, for
    any input state [s] satisfying the precondition [H], any possible execution
    of the program starting from the initial configuration [(s,t)] will
    terminate and reach a final configuration satisfying the postcondition [Q].

    However, the standard big-step judgment, [big s t s' v], only describes
    _one_ possible execution. Using this judgment, we can capture the property
    that "if a particular execution terminates, then it reaches a final
    configuration satisfying [Q]". But we do not capture the property that "all
    possible executions terminate".

    The omni-big-step judgment is a generalization of the standard big-step
    judgment that allows capturing properties of all possible executions. The
    judgment takes the form [eval s t Q], where [Q] denotes a set of final
    configurations. It captures the fact that all possible executions starting
    on the configuration [(s,t)] terminate safely and reach a final
    configuration in the set [Q]. We can think of [Q] as a set of pairs made of
    values and a state. Equivalently, we can think of [Q] as a postcondition, of
    type [val->heap->Prop]. *)

Implicit Types Q : val->heap->Prop.

(** The inductive definition below defines the omni-big-step judgment, which has
    the form [eval s t Q], where [Q] is a postcondition. The generalization from
    standard-big-step to omni-big-step follows a regular pattern, which should
    become apparent while stepping through the rules. *)
Inductive eval : heap -> trm -> (val->heap->Prop) -> Prop :=

(** 1. [eval] for values and function definitions.

      The judgment [eval s v Q] asserts that the value [v] in the state [s]
      satisfies the postcondition [Q]. The premise for deriving that judgment is
      thus that [Q v s] must hold. *)

  | eval_val : forall s v Q,
      Q v s ->
      eval s (trm_val v) Q
  | eval_fun : forall s x t1 Q,
      Q (val_fun x t1) s ->
      eval s (trm_fun x t1) Q
  | eval_fix : forall s f x t1 Q,
      Q (val_fix f x t1) s ->
      eval s (trm_fix f x t1) Q

(** 2. [eval] for function applications.

     Consider a function [v1] of the form [val_fun x t1]. The term
     [trm_app v1 v2] terminates with postcondition [Q] provided that the
     substituted term [subst x v2 t1] terminates with postcondition [Q]. Hence,
     to prove [eval s1 (trm_app v1 v2) Q], we must establish
     [eval s1 (subst x v2 t1) Q]. *)

  | eval_app_fun : forall s1 v1 v2 x t1 Q,
      v1 = val_fun x t1 ->
      eval s1 (subst x v2 t1) Q ->
      eval s1 (trm_app v1 v2) Q
  | eval_app_fix : forall s v1 v2 f x t1 Q,
      v1 = val_fix f x t1 ->
      eval s (subst x v2 (subst f v1 t1)) Q ->
      eval s (trm_app v1 v2) Q

(** 3. [eval] for sequencing.

      Consider a sequence [trm_seq t1 t2] in a state [s]. What is the
      requirement for this configuration to terminate with postcondition [Q]?
      First, we need the evaluation of [t1] in [s] to terminate. Let [Q1] be (an
      overapproximation of) the set of possible results for the execution of
      [(s,t1)]. Then, to prove that the sequence [trm_seq t1 t2] terminates in
      [Q], we need to show that, for any intermediate state [s2] satisfying
      [Q1], the evaluation of [t2] terminates with postcondition [Q].

      The case of let-bindings is similar, only with an additional substitution.
      *)

  | eval_seq : forall Q1 s t1 t2 Q,
      eval s t1 Q1 ->
      (forall v1 s2, Q1 v1 s2 -> eval s2 t2 Q) ->
      eval s (trm_seq t1 t2) Q
  | eval_let : forall Q1 s x t1 t2 Q,
      eval s t1 Q1 ->
      (forall v1 s2, Q1 v1 s2 -> eval s2 (subst x v1 t2) Q) ->
      eval s (trm_let x t1 t2) Q

(** 4. [eval] for conditionals.

      The term [(trm_if (val_bool b) t1 t2)] has the same behaviors as the term
      [t1] when [b] is [true], and as the term [t2] when [b] is false. *)

  | eval_if : forall s (b:bool) t1 t2 Q,
      eval s (if b then t1 else t2) Q ->
      eval s (trm_if (val_bool b) t1 t2) Q

(** 5. [eval] for primitive stateless operations.

    The judgment [eval s (val_add n1 n2) Q] asserts that the pair of the state
    [s] and the value [n1+n2] produced by the addition operation satisfies the
    postcondition [Q]. Hence, the premise is [Q (val_int (n1 + n2)) s].

    Nondeterministic constructs are more interesting. The rule [eval_rand] gives
    the condition under which the term [val_rand n], evaluated in a state [s],
    produces an output satisfying [Q]. The first premise of the rule requires
    [n > 0]. The second premise requires that, for any value [n1] that
    [val_rand n] may evaluate to -- that is, such that [0 <= n1 < n] -- the
    configuration made of [n1] and [s] satisfies the postcondition [Q].
    Formally: [forall n1, (0 <= n1 < n) -> (Q n1 s)]. *)

  | eval_add : forall s n1 n2 Q,
      Q (val_int (n1 + n2)) s ->
      eval s (val_add (val_int n1) (val_int n2)) Q
  | eval_div : forall s n1 n2 Q,
      n2 <> 0 ->
      Q (val_int (Z.quot n1 n2)) s ->
      eval s (val_div (val_int n1) (val_int n2)) Q
  | eval_rand : forall s n Q,
      n > 0 ->
      (forall n1, 0 <= n1 < n -> Q n1 s) ->
      eval s (val_rand (val_int n)) Q

(** 6. [eval] for primitive operations on memory.

    The most interesting case here is that of allocation, which is
    nondeterministic. For [val_ref v], evaluated in a state [s], to produce a
    configuration in [Q], we require that, for any location [p] that is "fresh"
    for the state [s], the pair made of [p] and "[s] extended with a binding
    from [p] to [v]" satisfies [Q]. *)

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

(** Note that, given [eval s t Q], it is *not* necessarily the case that [Q] is
    the exact set of configurations that are reachable from [(s,t)]; it may
    rather be an _overapproximation_ of that set. Trying to set up an inductive
    definition that relates [(s,t)] with _exactly_ its set of reachable
    configurations would introduce unnecessary complications.

    Note, also, that [eval s t Q] will not hold if there exist one or more
    executions of [(s,t)] that run into an error, i.e., that reach a
    configuration that is stuck. To see why, consider a program of the form
    [let n = rand 10 in (f n)]. When applying the rule [eval_let] to this
    program, the postcondition [Q1] associated with [rand 10] must include all
    integers in the range [0..9]. The second premise of the rule [eval_let] is
    of the form [forall v1 s2, Q1 v1 s2 -> eval s2 (subst x v1 t2) Q]. In our
    specific example, this premise asserts that for any result in [Q1], which
    includes all integers [n] in the range [0..9], it is the case that the term
    [f n] terminates. *)

(* ================================================================= *)
(** ** Definition of Triples *)

(** Now we come to the most important definition of the whole course! *)

(** A triple [triple t H Q] asserts that, for any input state [s] satisfying the
    precondition [H], any possible execution of [(s,t)] terminates and reaches a
    final configuration satisfying the postcondition [Q]. This statement is
    captured in terms of the omni-big-step semantics as follows. *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall s, H s -> eval s t Q.

(** Because the predicate [eval s t Q] captures termination, the predicate
    [triple t H Q] that we build on top of it also captures termination. It
    therefore yields a "total correctness" triple. If we had defined the
    predicate [eval] as [CoInductive] instead of [Inductive], we would have
    allowed for infinite executions.

    With such a coinductive definition of [eval], we would have obtained a
    "partial correctness" triple instead. Such a partial correctness triple
    would still capture the property that none of the possible executions can
    get stuck -- each possible execution either terminates safely with a result
    satisfying the postcondition, or else diverges. *)

(** Throughout the development of program logics, most research has concentrated
    on "partial correctness" logics. Depending on the set up, capturing "total
    correctness" is often much more challenging. In particular, when considering
    nondeterministic small-step semantics, and in particular when targeting
    concurrent programs, it can be nonobvious how to account for termination.
    But as long as we are concerned with sequential programs (i.e., without
    concurrency), omni-big-step semantics simplify reasoning about
    nondeterministic termination. *)

(* ================================================================= *)
(** ** Structural Rules *)

(** Now that triples are defined, we can state and prove reasoning rules of
    Separation Logic. This chapter focuses on structural rules; the other rules
    will be presented in the next chapter. We begin with the statements of the
    rules and present their proofs afterwards. *)

Module StructuralRules.

(** The frame rule asserts that an arbitrary heap predicate may be added to both
    the precondition and the postcondition of any triple. *)

Parameter triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').

(** The consequence rule asserts, as in Hoare Logic, that the validity of a
    triple is preserved if we strengthen its precondition or weaken its
    postcondition. *)

Parameter triple_conseq : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.

(** The "extraction rule for pure facts" asserts that a judgment of the form
    [triple t (\[P] \* H) Q] is derivable from [P -> triple t H Q]. This
    structural rule captures the extraction of the pure facts out of the
    precondition of a triple, like [himpl_hstar_hpure_l] for entailments. *)

Parameter triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.

(** The "extraction rule for existentials" asserts that a judgment of the form
    [triple t (\exists x, J x) Q] is derivable from
    [forall x, triple t (J x) Q]. Again, this rule is the counterpart of the
    corresponding rule on entailments, [himpl_hexists_l]. *)

Parameter triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (\exists x, J x) Q.

(* ================================================================= *)
(** ** Derived Structural Rules *)

(** Given a triple to be established, is is very unlikely for the frame rule to
    be applicable directly, because the precondition must be exactly of the form
    [H \* H'] and the postcondition exactly of the form [Q \*+ H'] for some
    [H']. For example, the frame rule would not apply to a proof obligation of
    the form [triple t (H' \* H) (Q \*+ H')] because [H' \* H] does not match
    [H \* H'].

    This limitation rule can be addressed by combining the frame rule and the
    rule of consequence into a single rule, called the "consequence-frame rule".
    This rule, shown below, enables deriving a triple from another triple,
    without syntactic restrictions on the shape of the precondition and
    postcondition of the two triples involved. *)

Lemma triple_conseq_frame : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.

(** **** Exercise: 1 star, standard, especially useful (triple_conseq_frame)

    Prove the combined consequence-frame rule. *)

Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** The extraction rule [triple_hpure] assumes a precondition of the form
    [\[P] \* H]. The variant rule [triple_hpure'], stated below, assumes instead
    a precondition with only the pure part, i.e., of the form [\[P]]. *)

(** **** Exercise: 1 star, standard, optional (triple_hpure')

    Prove that [triple_hpure'] is indeed a corollary of [triple_hpure]. *)

Lemma triple_hpure' : forall t (P:Prop) Q,
  (P -> triple t \[] Q) ->
  triple t \[P] Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End StructuralRules.

(* ################################################################# *)
(** * More Details *)

(* ================================================================= *)
(** ** Proof of the Consequence Rule *)

(** The proof of the consequence rule relies on establishing that the
    omni-big-step judgment is preserved under weakening its postcondition.
    Recall that in [eval s t Q1], the postcondition [Q1] is an overapproximation
    of the set of configurations reachable from [(s,t)]. Thus, if [Q1] is
    included in a larger set [Q2], then [Q2] is also an overapproximation of the
    configurations reachable from [(s,t)]. The formalization is a
    straightforward induction. *)

Lemma eval_conseq : forall s t Q1 Q2,
  eval s t Q1 ->
  Q1 ===> Q2 ->
  eval s t Q2.
Proof using.
  introv M W.
  asserts W': (forall v h, Q1 v h -> Q2 v h). { auto. } clear W.
  induction M; try solve [ constructors* ].
Qed.

(** From there, it is straightforward to derive the consequence rule. *)

Lemma triple_conseq : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof using. unfolds triple. introv M MH MQ HF. applys* eval_conseq. Qed.

(* ================================================================= *)
(** ** Proof of the Frame Rule *)

(** The second key property that we wish to establish is the "frame rule". The
    frame rule asserts that if a specification [triple H t Q] holds, then one
    may derive [triple (H \* H') t (Q \*+ H')] for any [H']. Recall from chapter
    [Hprop] that the operator [Q \*+ H'] is a notation for
    [fun x => (Q x \* H')].

    Intuitively, if the term [t] executes safely in a heap [H], then this this
    term should behave similarly in any extension of [H] with a disjoint part
    [H']. Moreover, its evaluation should leave this piece of state [H']
    unmodified throughout the execution of [t]. *)

(** The crux of the proof of the frame rule is to argue that [eval] is stable
    under extension with a disjoint piece of heap. *)

Lemma eval_frame : forall h1 h2 t Q,
  eval h1 t Q ->
  Fmap.disjoint h1 h2 ->
  eval (h1 \u h2) t (Q \*+ (= h2)).

(** This proof goes by induction. The most interesting step is for allocation.
    In a derivation built using [eval_ref], we are given as assumption a
    property that holds for any location [p] fresh from [h1], and we are
    requested to prove a property that holds for any location [p] fresh from
    [h1 \u h2]. We are thus restricting the set of [p] that can be considered
    for allocation, and so the result holds. *)

Proof using.
  introv M HD. gen h2. induction M; intros;
    try solve [ hint hstar_intro; constructors* ].
    { rename M into M1, H into M2, IHM into IH1, H0 into IH2.
    specializes IH1 HD. applys eval_seq IH1. introv HK.
    lets (h1'&h2'&K1'&K2'&KD&KU): hstar_inv HK. subst. applys* IH2. }
  { rename M into M1, H into M2, IHM into IH1, H0 into IH2.
    specializes IH1 HD. applys eval_let IH1. introv HK.
    lets (h1'&h2'&K1'&K2'&KD&KU): hstar_inv HK. subst. applys* IH2. }
  { (* Here is the interesting case about allocation. *)
    rename H into M. applys eval_ref. intros p Hp.
    rewrite Fmap.indom_union_eq in Hp. rew_logic in Hp.
    destruct Hp as [Hp1 Hp2].
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

(** The frame rule is derived from [eval_frame] and [eval_conseq]. *)

Lemma triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof.
  introv M. intros h HF. lets (h1&h2&M1&M2&MD&MU): hstar_inv (rm HF).
  subst. specializes M M1. applys eval_conseq.
  { applys eval_frame M MD. } { xsimpl. intros h' ->. applys M2. }
Qed.

(* ================================================================= *)
(** ** Proof of the Extraction Rules *)

(** The extraction rules are proved by unfolding the definition of [triple] and
    inverting the hypothesis capturing the fact that the input state satisfies
    the precondition. *)

Lemma triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using.
  introv M. intros h (h1&h2&M1&M2&D&U). destruct M1 as (M1&HP).
  lets E: hempty_inv HP. subst. rewrite Fmap.union_empty_l. applys~ M.
Qed.

(** **** Exercise: 1 star, standard, especially useful (triple_hexists)

    Prove [triple_hexists]. *)

Lemma triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall (x:A), triple t (J x) Q) ->
  triple t (hexists J) Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Rule for Naming Heaps *)

(** To prove [triple t H Q], it suffices to show that, for any heap [h]
    satisfying [H], the triple [triple t (= h) Q] holds. In other words, even
    though the predicate [triple] abstracts away from the input heap, it remains
    technically possible to introduce an entity, namely [h], that refers to the
    specific heap at hand during the evaluation of [t]. (An example use case
    will appear in a later chapter ([WPsem], lemma [wp_equiv_2]). *)

(** **** Exercise: 1 star, standard, optional (triple_named_heap)

    Prove the reasoning rule [hoare_named_heap]. *)

Lemma triple_named_heap : forall t H Q,
  (forall h, H h -> triple t (= h) Q) ->
  triple t H Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ################################################################# *)
(** * Optional Material *)

(* ================================================================= *)
(** ** An Alternative Structural Rule for Existentials *)

Module AlternativeExistentialRule.

(** Traditional papers on Separation Logic do not include [triple_hexists], but
    instead include a rule called here [triple_hexists2], which features an
    existential quantifier both in the precondition and in the postcondition. As
    we show next, in the presence of the consequence rule, the two rules are
    equivalent. *)

(** **** Exercise: 2 stars, standard, especially useful (triple_hexists2)

    Using [triple_hexists] and [triple_conseq], as well as the tactic [xsimpl],
    prove that [triple_hexists2] is derivable. *)

Lemma triple_hexists2 : forall A (Hof:A->hprop) (Qof:A->val->hprop) t,
  (forall x, triple t (Hof x) (Qof x)) ->
  triple t (\exists x, Hof x) (fun v => \exists x, Qof x v).
Proof using. (* FILL IN HERE *) Admitted.

(* [] *)

(** **** Exercise: 2 stars, standard, especially useful (triple_hexists_of_triple_hexists2)

    Reciprocally, using [triple_hexists2] and [triple_conseq], as well as the
    tactic [xsimpl], prove that [triple_hexists] is derivable. Of course, you
    may not use [triple_hexists] in this proof.) *)

Lemma triple_hexists_of_triple_hexists2 : forall t (A:Type) (Hof:A->hprop) Q,
  (forall x, triple t (Hof x) Q) ->
  triple t (\exists x, Hof x) Q.
Proof using. (* FILL IN HERE *) Admitted.

(* [] *)

(** Compared with [triple_hexists2], the formulation of [triple_hexists] is more
    concise, and is easier to exploit in practice. *)

End AlternativeExistentialRule.

(* ================================================================= *)
(** ** Small-Step Semantics *)

(** Suppose we have a language with a formal semantics written not in big-step
    stype but in small-step style. What are the options for formalizing total
    correctness triples? We discuss two approaches. The first one consists of
    formally relating the small-step judgment with the omni-big-step judgment.
    The second consists of directly defining triples in terms of the small-step
    judgment. Before explaining the two approaches, let us present the
    formalization of the small-step semantics. *)

(** The judgment [step s t s' t'] describes the small-step reduction relation:
    it asserts that the program configuration [(s,t)] can take one reduction
    step to reach the program configuration [(s',t')]. Its definition is
    standard. *)

Inductive step : heap -> trm -> heap -> trm -> Prop :=

(* Context rules *)
| step_seq_ctx : forall s1 s2 t1 t1' t2,
    step s1 t1 s2 t1' ->
    step s1 (trm_seq t1 t2) s2 (trm_seq t1' t2)
| step_let_ctx : forall s1 s2 x t1 t1' t2,
    step s1 t1 s2 t1' ->
    step s1 (trm_let x t1 t2) s2 (trm_let x t1' t2)

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

(* Primitive operations *)
| step_add : forall s n1 n2,
    step s (val_add (val_int n1) (val_int n2)) s (val_int (n1 + n2))
| step_div : forall s n1 n2,
    n2 <> 0 ->
    step s (val_div (val_int n1) (val_int n2)) s (Z.quot n1 n2)
| step_rand : forall s n n1,
    0 <= n1 < n ->
    step s (val_rand (val_int n)) s (val_int n1)
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

(** The judgment [steps s t s' t'] corresponds to the reflexive and transitive
    closure of [step]. Concretely, it asserts that the configuration [(s,t)] can
    reduce in zero, one, or several steps to [(s',t')]. *)

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
Proof using.
  introv M1. induction M1; introv M2. { auto. } { constructors*. }
Qed.

(** The predicate [trm_is_val t] asserts that [t] is a value. *)

Definition trm_is_val (t:trm) : Prop :=
  match t with trm_val v => True | _ => False end.

(** Consider a configuration [(s,t)], where [t] is not a value. If this
    configuration cannot take any reduction step, it is said to be _stuck_.
    Conversely, a configuration [(s,t)] that can take a step is said to be
    _reducible_. *)

Definition reducible (s:heap) (t:trm) : Prop :=
  exists s' t', step s t s' t'.

(** Values are not reducible. *)

Lemma reducible_val_inv : forall s v,
  ~ reducible s v.
Proof using. introv (s'&t'&M). inverts M. Qed.

(** The predicate [notstuck s t] asserts that either [t] is a value or [t] is
    reducible. *)

Definition notstuck (s:heap) (t:trm) : Prop :=
  trm_is_val t \/ reducible s t.

(* ================================================================= *)
(** ** Equivalence Between Small-Step and Omni-Big-Step *)

(** If we consider the omni-big-step semantics to be the starting point of a
    development, then the definition of [triple] is obviously sound with respect
    to that semantics, as it concludes [eval s t Q]. If, however, we consider
    the small-step semantics to be the starting point, then to establish
    soundness it is required to prove that [triple t H Q] ensures that all
    possible evaluations of [t] in a heap satisfying [H] are: (1) terminating,
    and (2) guaranteed to reach a value; moreover, (3) this value and the final
    state obtained must satisfy the postconditon [Q]. We begin by formalizing
    each of these properties. *)

(** The judgment [terminates s t] is defined inductively. The execution starting
    from [(s,t)] terminates if any possible step leads to a configuration that
    terminates. Note that a configuration that has reached a value cannot take a
    step, hence is considered terminating. *)

Inductive terminates : heap->trm->Prop :=
  | terminates_step : forall s t,
      (forall s' t', step s t s' t' -> terminates s' t') ->
      terminates s t.

(** The judgment [safe s t] asserts that no execution may reach a stuck term. In
    other words, for any configuration [(s',t')] reachable from [(s,t)], it is
    the case that the configuration [(s',t')] is either a value or is reducible.
    *)

Definition safe (s:heap) (t:trm) : Prop :=
  forall s' t', steps s t s' t' -> notstuck s' t'.

(** The judgment [correct s t Q] asserts that if the execution of [(s,t)]
    reaches a final configuration, then this final configuration satisfies [Q].
    *)

Definition correct (s:heap) (t:trm) (Q:val->hprop) : Prop :=
  forall s' v, steps s t s' v -> Q v s'.

(** The conjunction of [safe] and [correct] corresponds to "partial
    correctness". The conjunction of [safe], [correct] and [terminates]
    corresponds to "total correctness". The soundness theorem that we aim for
    establishes that [triple t H Q] entails total correctness.

    triple t H Q ->
    forall s, H s -> terminates s t /\ safe s t /\ correct s t Q.

    To prove soundness, we introduce an inductively predicate, named [seval],
    which captures total correctness in small-step style. On the one hand, we
    prove that [seval] entails [safe], [correct], and [terminates]. On the other
    hand, we prove that [seval] is related to the omni-big-step judgment,
    [eval].

    The judgment [seval s t Q] asserts that any execution of [(s,t)] terminates
    and reaches a configuration satisfying [Q]. In the "base" case,
    [seval s v Q] holds if the terminal configuration [(s,v)] satisfies [Q]. In
    the "step" case, [seval s t Q] holds if (1) the configuration [(s,t)] is
    reducible, and (2) if for any step that [(s,t)] may take to [(s',t')], the
    predicate [seval s' t' Q] holds. *)

Inductive seval : heap->trm->(val->hprop)->Prop :=
  | seval_val : forall s v Q,
      Q v s ->
      seval s v Q
  | seval_step : forall s t Q,
      reducible s t -> (* (exists s' t', step s t s' t') *)
      (forall s' t', step s t s' t' -> seval s' t' Q) ->
      seval s t Q.

(** **** Exercise: 2 stars, standard, optional (seval_val_inv)

    As a warm-up to get some familiary with [seval], prove the following
    inversion lemma, which asserts that, given a value [v], the property
    [seval s v Q] implies [Q s v]. *)

Lemma seval_val_inv : forall s v Q,
  seval s v Q ->
  Q v s.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** We begin with the three key properties of [seval]: termination, safety, and
    correctness. *)

(** **** Exercise: 2 stars, standard, especially useful (seval_terminates)

    Prove that [seval] captures termination. *)

Lemma seval_terminates : forall s t Q,
  seval s t Q ->
  terminates s t.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard, especially useful (seval_safe)

    Prove that [seval] captures safety. *)

Lemma seval_safe : forall s t Q,
  seval s t Q ->
  safe s t.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard, especially useful (seval_correct)

    Prove that [seval] captures correctness. *)

Lemma seval_correct : forall s t Q,
  seval s t Q ->
  correct s t Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** We can group the three results into a soundness theorem for [seval]. *)

Lemma seval_sound : forall s t Q,
  seval s t Q ->
  terminates s t /\ safe s t /\ correct s t Q.
Proof using.
  introv M. splits.
  { applys* seval_terminates. }
  { applys* seval_safe. }
  { applys* seval_correct. }
Qed.

(** We now establish that the omni-big-step evaluation judgment entails the
    small-step-based [seval] judgment. The proof is carried out by induction on
    the omni-big-step relation. It relies on a number of auxiliary results
    establishing that, for each term construct, the [seval] judgment admits an
    evaluation rule that mimics the omni-big-step evaluation rule. We begin with
    the statements of the auxiliary lemmas. *)

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
  { introv R. invert R; try solve [intros; false].     introv -> -> -> -> -> R. inverts E. applys M. }
Qed.

Lemma seval_app_fix : forall s f x v1 v2 t1 Q,
  v1 = val_fix f x t1 ->
  seval s (subst x v2 (subst f v1 t1)) Q ->
  seval s (trm_app v1 v2) Q.
Proof using.
  introv E M. applys seval_step.
  { do 2 esplit. applys* step_app_fix. }
  { introv R. invert R; try solve [intros; false].     introv -> -> -> -> -> R. inverts E. applys M. }
Qed.

(** **** Exercise: 5 stars, standard, especially useful (seval_seq)

    Prove the big-step reasoning rule for sequence for [seval]. *)

Lemma seval_seq : forall s t1 t2 Q1 Q,
  seval s t1 Q1 ->
  (forall s1 v1, Q1 v1 s1 -> seval s1 t2 Q) ->
  seval s (trm_seq t1 t2) Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 5 stars, standard, optional (seval_let)

    The proof of [seval_let] is the same as that of [seval_seq]. We also present
    it as an exercise to avoid giving away the solution. *)

Lemma seval_let : forall s x t1 t2 Q1 Q,
  seval s t1 Q1 ->
  (forall s1 v1, Q1 v1 s1 -> seval s1 (subst x v1 t2) Q) ->
  seval s (trm_let x t1 t2) Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

Lemma seval_if : forall s b t1 t2 Q,
  seval s (if b then t1 else t2) Q ->
  seval s (trm_if b t1 t2) Q.
Proof using.
  introv M. applys seval_step.
  { do 2 esplit. constructors*. }
  { introv R. inverts R; tryfalse. { applys M. } }
Qed.

(** We are now ready to prove by induction that the omni-big-step judgment
    entails the small-step-based judgment [seval]. Note that the reciprocal
    entailment also holds, however it is not needed for establishing soundness.
    *)

Lemma seval_of_eval : forall s t Q,
  eval s t Q ->
  seval s t Q.
Proof using.
  introv M. induction M.
  { applys* seval_val. }
  { applys* seval_fun. }
  { applys* seval_fix. }
  { applys* seval_app_fun. }
  { applys* seval_app_fix. }
  { applys* seval_seq. }
  { applys* seval_let. }
  { applys* seval_if. }
  { applys seval_step.
    { do 2 esplit. applys* step_add. }
    { introv K. inverts K. applys* seval_val. } }
  { applys seval_step.
    { do 2 esplit. applys* step_div. }
    { introv K. inverts K. applys* seval_val. } }
  { applys seval_step.
    { do 2 esplit. applys* step_rand 0. math. }
    { introv K. inverts K; tryfalse. applys* seval_val. } }
  { applys seval_step.
    { forwards~ (p&D&N): (exists_fresh null s).
      do 2 esplit. applys* step_ref. }
    { introv K. inverts K; tryfalse. applys* seval_val. } }
  { applys seval_step.
    { do 2 esplit. applys* step_get. }
    { introv K. inverts K; tryfalse. applys* seval_val. } }
  { applys seval_step.
    { do 2 esplit. applys* step_set. }
    { introv K. inverts K; tryfalse. applys* seval_val. } }
  { applys seval_step.
    { do 2 esplit. applys* step_free. }
    { introv K. inverts K; tryfalse. applys* seval_val. } }
Qed.

(** Putting it all together, we conclude on the soundness of Separation Logic
    with respect to the small-step semantics defined by the relation [step]. *)

Lemma soundness_small_step : forall t H Q,
  triple t H Q ->
  forall s, H s -> terminates s t /\ safe s t /\ correct s t Q.
Proof using.
  unfold triple. introv M Hs. specializes M Hs.
  lets R: seval_of_eval M. applys seval_sound R.
Qed.

(* ================================================================= *)
(** ** Small-Step-Based Triples *)

(** A second possible approach to setting up a Separation Logic starting from a
    small-step semantics consists of defining [triple] directly in terms of
    [seval], without introducing the omni-big-step judgment [eval].

    Let [striple] denote triples built from [seval]. *)

Definition striple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (s:heap), H s -> seval s t Q.

(** The first step is to check that this new definition of triple is sound. This
    property has been essentially been established in the previous section via
    the lemma [seval_sound]. *)

Lemma striple_sound : forall t H Q,
  striple t H Q ->
  forall s, H s -> terminates s t /\ safe s t /\ correct s t Q.
Proof using. introv M Hs. specializes M Hs. applys seval_sound M. Qed.

(** The second step is to establish reasoning rules for [striple]. Let us begin
    with the consequence rule and the frame rule. For those, we need to
    establish the consequence and the frame property directly for [seval]. The
    proofs differ from the corresponding proofs on [eval]. *)

(** The consequence rule for [seval] is established by induction. *)

Lemma seval_conseq : forall s t Q Q',
  seval s t Q' ->
  Q' ===> Q ->
  seval s t Q.
Proof using.
  introv M WQ. induction M.
  { applys seval_val. applys* WQ. }
  { rename H1 into IH.
    applys seval_step.
    { auto. }
    { introv HR. applys* IH. } }
Qed.

(** The consequence rule follows directly. *)

Lemma striple_conseq : forall t H' Q' H Q,
  striple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  striple t H Q.
Proof using.
  introv M MH MQ HF. applys seval_conseq M MQ. applys* MH.
Qed.

(** The frame property for [seval] is also established by induction, however the
    proof is more involved. *)

Section stepsFrame.
Hint Constructors step.

Lemma seval_frame : forall h1 h2 t Q,
  seval h1 t Q ->
  Fmap.disjoint h1 h2 ->
  seval (h1 \u h2) t (Q \*+ (= h2)).
Proof using.
  introv M HD. gen h2. induction M; intros.
  { applys seval_val. applys* hstar_intro. }
  { rename H into M1, H0 into M2, H1 into IH2.
    applys seval_step.
    { unfolds reducible. clear M2 IH2. destruct M1 as (s'&t'&R).
      induction R; tryfalse; try solve [ do 2 esplit; constructors* ].
      { forwards* (s'&t'&R'): IHR. }
      { forwards* (s'&t'&R'): IHR. }
      { lets (p'&F&_): exists_fresh null (Fmap.union s h2). do 2 esplit.
        applys step_ref v p'. eauto. }
      { do 2 esplit. applys step_get. applys* Fmap.indom_union_l. }
      { do 2 esplit. applys step_set. applys* Fmap.indom_union_l. }
      { do 2 esplit. applys step_free. applys* Fmap.indom_union_l. } }
    { introv R. cuts (s1'&E'&D'&R'):
        (exists s1', s' = s1' \u h2 /\ Fmap.disjoint s1' h2 /\ step s t s1' t').
      { subst. applys* IH2. }
      clear M2 IH2.
      gen_eq su: (s \u h2). gen s.
      unfolds reducible. induction R; intros; subst; eauto.
      { destruct M1 as (s0&t0&R0).
        rename R into R1. forwards* (s1'&E&D&R1'): IHR s.
        { inverts R0. { eauto. } { inverts R1. } } }
      { destruct M1 as (s0&t0&R0).
        rename R into R1. forwards* (s1'&E&D&R1'): IHR s.
        { inverts R0. { eauto. } { inverts R1. } } }
      { rename H into D. rewrite Fmap.indom_union_eq in D. rew_logic in D.
        destruct D as (D1&D2). esplit. splits.
        { rewrite* Fmap.update_union_not_r. }
        { applys* Fmap.disjoint_update_not_r. }
        { eauto. } }
      { destruct M1 as (se&te&Re). inverts Re; tryfalse.
        rewrite* Fmap.read_union_l. }
      { destruct M1 as (se&te&Re). inverts Re; tryfalse. esplit. splits.
        { rewrite* Fmap.update_union_l. }
        { applys* Fmap.disjoint_update_l. }
        { eauto. } }
      { destruct M1 as (se&te&Re). inverts Re; tryfalse. esplit. splits.
        { rewrite* remove_disjoint_union_l. }
        { applys* Fmap.disjoint_remove_l. }
        { eauto. } } } }
Qed.

End stepsFrame.

(** The frame rule for [striple] then follows from the frame and the consequence
    properties for [seval]. *)

Lemma striple_frame : forall t H Q H',
  striple t H Q ->
  striple t (H \* H') (Q \*+ H').
Proof.
  introv M. intros h HF. lets (h1&h2&M1&M2&MD&MU): hstar_inv (rm HF).
  subst. specializes M M1. applys seval_conseq.
  { applys seval_frame M MD. } { xsimpl. intros h' ->. applys M2. }
Qed.

(** To establish other reasoning rules for [striple], one need to prove
    big-step-style evaluation rules for [seval], such as the lemma [seval_let]
    stated earlier. *)

(** In summary, it is possible to set up a Separation Logic directly based on
    the small-step-based judgment [seval], without going through a definition of
    the omni-big-step judgment [eval]. However, most of the proof effort
    remains, as one needs to establish the frame property and to derive
    big-step-style evaluation rules such as [seval_let]. *)

(* ================================================================= *)
(** ** Separation Logic Triples for Quasi-Deterministic Semantics *)

Module BakedInFrame.

(** Consider a programming language that is deterministic except for the
    allocation operation, which may pick any fresh location. For such languages,
    it is possible to define Separation Logic triples in terms of the standard
    big-step semantics, using a technique known as the "baked-in frame rule".

    Recall the big-step judgment. *)

Parameter eval : heap -> trm -> heap -> val -> Prop.

(** First, we define a (total correctness) Hoare triple, written [hoare t H Q].
    This judgment asserts that, starting from a state [s] satisfying the
    precondition [H], the term [t] evaluates to a value [v] and to a state [s']
    that, together, satisfy the postcondition [Q]. Formally: *)

Definition hoare (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (s:heap), H s ->
  exists (s':heap) (v:val), eval s t s' v /\ Q v s'.

(** **** Exercise: 2 stars, standard, especially useful (hoare_conseq)

    To gain familiarity with the [hoare] judgment, prove the consequence rule
    for Hoare triples. *)

Lemma hoare_conseq : forall t H Q H' Q',
  hoare t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  hoare t H Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** The judgment [hoare t H Q] satisfies the consequence rule, yet it does not
    satisfy the frame property. Can you figure out a counter-example? *)

(** It is nevertheless possible to define [triple] on top of [hoare] by "baking
    in" the frame rule. The relevant definition is as follows. *)

Definition btriple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (H':hprop), hoare t (H \* H') (Q \*+ H').

(** This definition inherently satisfies the frame rule, as we show below. The
    proof essentially exploits the associativity of the star operator. *)

(** **** Exercise: 3 stars, standard, especially useful (btriple_frame)

    Prove that [btriple t H Q] is a judgment satisfying the frame rule. *)

Lemma btriple_frame : forall t H Q H',
  btriple t H Q ->
  btriple t (H \* H') (Q \*+ H').
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** We have previously defined [btriple] on top of [hoare], with the help of the
    separating conjunction operator, in the form:
    [forall (H':hprop), hoare (H \* H') t (Q \*+ H')]. In what follows, we give
    an equivalent characterization, expressed directly in terms of heaps and
    heap unions.

    The alternative definition of [triple t H Q] asserts that if [h1] satisfies
    the precondition [H] and [h2] describes the rest of the state, then the
    evaluation of [t] produces a value [v] in a final state made that can be
    decomposed between a part [h1'] and [h2] unchanged, in such a way that [v]
    and [h1'] together satisfy the postcondition [Q].

    Formally: *)

Definition btriple_lowlevel (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall h1 h2,
  Fmap.disjoint h1 h2 ->
  H h1 ->
  exists h1' v,
       Fmap.disjoint h1' h2
    /\ eval (h1 \u h2) t (h1' \u h2) v
    /\ Q v h1'.

(** Let us establish the equivalence between this alternative definition of
    [triple] and the original one. *)

Lemma btriple_iff_btriple_lowlevel : forall t H Q,
  btriple t H Q <-> btriple_lowlevel t H Q.
Proof using.
  unfold triple, btriple_lowlevel, hoare. iff M.
  { introv D P1.
    forwards (h'&v&HR&HQ): M (=h2) (h1 \u h2). { applys* hstar_intro. }
    destruct HQ as (h1'&h2'&N0&N1&N2&N3). subst.
    exists h1' v. auto. }
  { intros H' h. introv (h1&h2&N1&N2&D&U).
    forwards (h1'&v&D'&HR&HQ): M h1 h2; auto. subst.
    exists (h1' \u h2) v. split. { eauto. } { applys* hstar_intro. } }
Qed.

(** The low-level definition of triple leveraging the baked-in frame rule may be
    convenient for formalizing certain extensions of Separation Logic. *)

End BakedInFrame.

(* ================================================================= *)
(** ** Historical Notes *)

(** The definition of Separation Logic triples based on the use of an
    omni-big-step semantics is a contribution of [Charguéraud et al 2023] (in Bib.v).
    Omni-big-step semantics was introduced by [Schäfer et al 2016] (in Bib.v), with
    applications to a Hoare logic. The technique of the "baked-in frame rule"
    presented near the end of this chapter was introduced by
    [Birkedal, Torp-Smith and Yang 2006] (in Bib.v), who developed the first
    Separation Logic for a higher-order programming language. Since then, this
    technique has been employed successfully in numerous formalizations of
    Separation Logic. *)

(* 2024-12-26 10:22 *)
