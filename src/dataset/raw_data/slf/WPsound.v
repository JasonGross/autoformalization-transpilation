(** * WPsound: Soundness of the Weakest Precondition Generator *)

Set Implicit Arguments.
From SLF Require Import WPsem WPgen.
Import WPgenRec.

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types v : val.
Implicit Types h : heap.
Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.

(* ################################################################# *)
(** * More Details *)

(** This chapter develops the soundness proof for [wpgen]. The key theorem
    asserts that, for any term and and postcondition, [wpgen] (on an empty
    substitution context) yields a formula that entails [wp]. Formally:
    [wpgen nil t Q ==> wp t Q]. The present "more details" section contains the
    proof of this theorem. The "optional material" section details the proofs of
    two technical lemmas related to permutation of substitutions. This chapter
    may be safely skipped. *)

(* ================================================================= *)
(** ** Definition of the Predicate [formula_sound] *)

(** The soundness theorem that we aim to establish for [wpgen] is:

    Parameter wpgen_sound : forall E t Q,
      wpgen E t Q ==> wp (isubst E t) Q.
*)

(** Before entering into the details of the proof, let us reformulate the
    statement of the soundness theorem to make proof obligations and induction
    hypotheses easier to read. To that end, we introduce the predicate
    [formula_sound t F], read "F is a formula sound for t". It asserts that [F]
    is a weakest-precondition style formula that entails [wp t]. Formally: *)

Definition formula_sound (t:trm) (F:formula) : Prop :=
  forall Q, F Q ==> wp t Q.

(** Using [formula_sound], the soundness theorem for [wpgen] is reformulated as
    follows.

    Parameter wpgen_sound : forall E t,
      formula_sound (isubst E t) (wpgen E t).
*)

(** The soundness theorem [wpgen_sound] is proved by induction on [t]. Each case
    of this inductive proof corresponds to a term construct. For each term
    construct, we need to exploit two lemmas. The first lemma, common to all
    term constructs, is called [mkstruct_sound], and is used to argue that the
    presence of [mkstruct] in the definition of [wpgen] is sound. The second
    lemma is specific to the term construct. For example, [wpgen_sound_seq] is
    of the form [formula_sound (trm_seq t1 t2) (wpgen_seq F1 F2)]. We next
    explain the details of how to state and prove [wpgen_sound_seq], then
    present the other auxiliary lemmas useful for completing the proof by
    induction of [wpgen_sound]. *)

(* ================================================================= *)
(** ** Soundness for the Case of Sequences *)

(** Consider the soundness theorem [wpgen_sound] and let us specialize it to the
    particular case where [t] is of the form [trm_seq t1 t2]. The corresponding
    statement is: *)

Parameter wpgen_sound_seq_1 : forall E t1 t2,
  formula_sound (isubst E (trm_seq t1 t2))
                (wpgen E (trm_seq t1 t2)).

(** Let us ignore [mkstruct] for a minute -- that is, pretend that [wpgen] is
    defined without [mkstruct]. Under this assumption, [wpgen E (trm_seq t1 t2)]
    evaluates to [wpgen_seq (wpgen E t1) (wpgen E t2)]. Besides, the expression
    [isubst E (trm_seq t1 t2)] evaluates to
    [trm_seq (isubst E t1) (isubst E t2)]. Therefore, the soundness statement to
    establish can be reformulated as: *)

Parameter wpgen_sound_seq_2 : forall E t1 t2,
  formula_sound (trm_seq (isubst E t1) (isubst E t2))
                (wpgen_seq (wpgen E t1) (wpgen E t2)).

(** By induction hypothesis, we can assume that [wpgen E t1] is a sound formula
    for [isubst E t1], and likewise [wpgen E t2] is a sound formula for
    [isubst E t2]. Thus, what we actually will need to prove as part of the
    induction is: *)

Parameter wpgen_sound_seq_3 : forall E t1 t2,
  formula_sound (isubst E t1) (wpgen E t1) ->
  formula_sound (isubst E t2) (wpgen E t2) ->
  formula_sound (trm_seq (isubst E t1) (isubst E t2))
                (wpgen_seq (wpgen E t1) (wpgen E t2)).

(** In the above statement, let us abstract [isubst E t1] as [t1'] and
    [wpgen t1] as [F1], and similarly [isubst E t2] as [t2'] and [wpgen t2] as
    [F2]. The statement reformulates as: *)

Lemma wpgen_seq_sound : forall t1' t2' F1 F2,
  formula_sound t1' F1 ->
  formula_sound t2' F2 ->
  formula_sound (trm_seq t1' t2') (wpgen_seq F1 F2).

(** This statement captures the essence of the correctness of the definition of
    [wpgen_seq]. Now let's prove it. *)

Proof using.
  introv S1 S2.
  (* Reveal the soundness statement *)
  unfolds formula_sound.
  (* Consider a postcondition [Q] *)
  intros Q.
  (* Reveal [wpgen_seq F1 F2], which is defined as [F1 (fun v => F2 Q)]. *)
  unfolds wpgen_seq.
  (* By transitivity of entailment *)
  applys himpl_trans.
  (* Apply the wp-style reasoning rule for sequences:
     [wp t1 (fun v => wp t2 Q) ==> wp (trm_seq t1 t2) Q]. *)
  2:{ applys wp_seq. }
  (* Exploit the induction hypotheses to conclude *)
  { applys himpl_trans.
    { applys S1. }
    { applys wp_conseq. intros v. applys S2. } }
Qed.

(* ================================================================= *)
(** ** Soundness for the Other Term Constructs *)

(** Similarly, for every other language construct, we state and prove a lemma
    about [formula_sound]. The reader may skip over the proof details. What is
    most interesting here is the pattern followed by the statements. *)

Lemma wpgen_val_sound : forall v,
  formula_sound (trm_val v) (wpgen_val v).
Proof using. intros. intros Q. unfolds wpgen_val. applys wp_val. Qed.

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

Lemma wpgen_fail_sound : forall t,
  formula_sound t wpgen_fail.
Proof using. intros. intros Q. unfold wpgen_fail. xpull. Qed.

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

(** Additional lemmas establishing the soundness of a version of [wpgen] that
    does not recurse inside local function definitions. *)

Lemma wpgen_fun_val_sound : forall x t,
  formula_sound (trm_fun x t) (wpgen_val (val_fun x t)).
Proof using. intros. intros Q. unfolds wpgen_val. applys wp_fun. Qed.

Lemma wpgen_fix_val_sound : forall f x t,
  formula_sound (trm_fix f x t) (wpgen_val (val_fix f x t)).
Proof using. intros. intros Q. unfolds wpgen_val. applys wp_fix. Qed.

(* ================================================================= *)
(** ** Soundness of the Predicate Transformer [mkstruct] *)

(** Above, we have ignored the existence of [mkstruct] at the head of
    formulae produced by [wpgen]. We next show that the insertion of [mkstruct]
    in formulae preserves their soundness. In other words, if the formula [F] is
    a valid weakest precondition for [t], then so is [mkstruct F].

    Lemma mkstruct_sound : forall t F,
      formula_sound t F ->
      formula_sound t (mkstruct F).

    In order to prove this result, we first need to show that [mkstruct] is a
    predicate transformer that does not affect the meaning of any formula of the
    form [wp t]. Intuitively, [mkstruct] adds support for applying structural
    rules of Separation Logic; but a formula [wp t] _inherently_ satisfies all
    the structural rules; hence wrapping [wp t] inside a call to [mkstruct] does
    not increase (nor decrease) its expressive power. *)

Lemma mkstruct_wp : forall t,
  mkstruct (wp t) = (wp t).
Proof using.
  intros. applys fun_ext_1. intros Q. applys himpl_antisym.
  { unfold mkstruct. xpull. intros H Q' M. applys wp_conseq_frame M. xsimpl. }
  { applys mkstruct_erase. }
Qed.

(** We are now ready to prove the desired result [mkstruct_sound]. *)

Lemma mkstruct_sound : forall t F,
  formula_sound t F ->
  formula_sound t (mkstruct F).
Proof using.
  introv M. unfolds formula_sound. intros Q.
  rewrite <- mkstruct_wp. applys mkstruct_monotone. applys M.
Qed.

(** Another, lower-level proof for the same result reveals the definition of
    [mkstruct] and exploits the consequence-frame rule for [wp]. *)

Lemma mkstruct_sound' : forall t F,
  formula_sound t F ->
  formula_sound t (mkstruct F).
Proof using.
  introv M. unfolds formula_sound.
  (* Consider a postcondition [Q] *)
  intros Q.
  (* Reveal the definition of [mkstruct] *)
  unfolds mkstruct.
  (* Extract the [Q'] quantified in the definition of [mkstruct] *)
  xsimpl. intros Q'.
  (* Exploit the assumption on [forall Q, F Q ==> wp t Q] *)
  xchange (M Q').
  (* Conclude using the structural rules for [wp]. *)
  applys wp_ramified.
Qed.

(** Another interesting property of [mkstruct] is its idempotence property, that
    is, it is such that [mkstruct (mkstruct F) = mkstruct F]. Idempotence
    asserts that applying the predicate [mkstruct] more than once does not
    provide more expressiveness than applying it just once.

    Intuitively, idempotence reflects in particular the fact that two nested
    applications of the rule of consequence can always be combined into a single
    application of that rule (due to the transitivity of entailment); and that,
    similarly, two nested applications of the frame rule can always be combined
    into a single application of that rule (framing on [H1] then framing on [H2]
    is equivalent to framing on [H1 \* H2]). *)

(** **** Exercise: 3 stars, standard, especially useful (mkstruct_idempotent)

    Complete the proof of the idempotence of [mkstruct]. Hint: leverage [xpull]
    and [xsimpl]. *)

Lemma mkstruct_idempotent : forall F,
  mkstruct (mkstruct F) = mkstruct F.
Proof using.
  intros. apply fun_ext_1. intros Q. applys himpl_antisym.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Lemmas Capturing Properties of Iterated Substitutions *)

(** In the soundness proof for [wpgen], we need to exploit two basic properties
    of the iterated substitution function [isubst]. The first property asserts
    that the substitution for the empty context is the identity. This result is
    useful to beautify the final statement of the soundness theorem. *)

Parameter isubst_nil : forall t,
  isubst nil t = t.

(** The second property asserts that the substitution for a context [(x,v)::E]
    is the same as the substitution for the context [rem x E] followed with the
    substitution of [subst x v]. This second property is needed to handle the
    case of let-bindings. *)

Parameter isubst_rem : forall x v E t,
  isubst ((x,v)::E) t = subst x v (isubst (rem x E) t).

(** The proofs for these two lemmas is fairly technical and of limited interest
    for the course. They can be found in the "optional material" near the end of
    this chapter. *)

(* ================================================================= *)
(** ** Main Induction for the Soundness Proof of [wpgen] *)

(** At last, we are ready to establish the soundness of [wpgen E t]. As
    previously announced, the proof is by structural induction on [t]. For each
    term construct, the proof has two steps:

    - first, invoke the lemma [mkstruct_sound] to justify soundness
      of the leading [mkstruct] produced by [wpgen],
    - second, invoke the the soundness lemma specific to that term
      construct, e.g. [wpgen_seq_sound] for sequences. *)

Lemma wpgen_sound_induct : forall E t,
  formula_sound (isubst E t) (wpgen E t).
Proof using.
  intros. gen E. induction t; intros; simpl;
   applys mkstruct_sound. (* common to all cases *)
  { applys wpgen_val_sound. }
  { rename v into x. unfold wpgen_var. case_eq (lookup x E).
    { intros v EQ. applys wpgen_val_sound. }
    { intros N. applys wpgen_fail_sound. } }
  { applys wpgen_fun_sound.
     { intros vx. rewrite <- isubst_rem. applys IHt. } }
  { introv IH. applys wpgen_fix_sound IH.
    { intros vf vx. rewrite <- isubst_rem_2. applys IHt. } }
  { applys wpgen_app_sound. }
  { applys wpgen_seq_sound. { applys IHt1. } { applys IHt2. } }
  { rename v into x. applys wpgen_let_sound.
    { applys IHt1. }
    { intros v. rewrite <- isubst_rem. applys IHt2. } }
  { applys wpgen_if_sound. { applys IHt2. } { applys IHt3. } }
Qed.

(* ================================================================= *)
(** ** Statement of Soundness of [wpgen] for Closed Terms *)

(** For a closed term [t], the context [E] is instantiated as [nil], and
    [isubst nil t] simplifies to [t]. We derive the main soundness statement for
    [wpgen]. *)

Lemma wpgen_sound : forall t Q,
  wpgen nil t Q ==> wp t Q.
Proof using.
  introv M. lets N: (wpgen_sound nil t). rewrite isubst_nil in N. applys* N.
Qed.

(** The lemma [triple_of_wpgen] triggers the initial evaluation of [wpgen] for a
    given program [t] that appears in a triple. *)

Lemma triple_of_wpgen : forall t H Q,
  H ==> wpgen nil t Q ->
  triple t H Q.
Proof using.
  introv M. rewrite <- wp_equiv. xchange M. applys wpgen_sound.
Qed.

(** The lemma [triple_app_fun_from_wpgen] is at the core of the implementation
    of the tactic [xwp]. It is a specialized version of triple_of_wpgen]
    specialized for establishing a triple for a function application. In
    essence, this lemma is a reformulation of the rule [triple_app_fun], but
    triggering an evaluation of [wpgen] for the body of the function. *)

Lemma triple_app_fun_from_wpgen : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.
Proof using.
  introv M1 M2. applys triple_app_fun M1.
  asserts_rewrite (subst x v2 t1 = isubst ((x,v2)::nil) t1).
  { rewrite isubst_rem. rewrite* isubst_nil. }
  rewrite <- wp_equiv. xchange M2. applys wpgen_sound_induct.
Qed.

(** The lemma [triple_app_fix_from_wpgen] is similar but handles recursive
    functions. *)

Lemma triple_app_fix_from_wpgen : forall v1 v2 f x t1 H Q,
  v1 = val_fix f x t1 ->
  H ==> wpgen ((f,v1)::(x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.
Proof using.
  introv M1 M2. applys triple_app_fix M1.
  asserts_rewrite (subst x v2 (subst f v1 t1)
                 = isubst ((f,v1)::(x,v2)::nil) t1).
  { rewrite isubst_rem_2. rewrite* isubst_nil. }
  rewrite <- wp_equiv. xchange M2. applys wpgen_sound_induct.
Qed.

(* ################################################################# *)
(** * Optional Material *)

(* ================================================================= *)
(** ** Proofs of Properties of Iterated Substitution *)

Module IsubstProp.

Open Scope liblist_scope.

Implicit Types E : ctx.

(** Recall that [isubst E t] denotes the multi-substitution in the term [t] of
    all bindings form the association list [E]. The soundness proof for [wpgen]
    and the proof of its corollary [triple_app_fun_from_wpgen] rely on two key
    properties of iterated substitutions, captured by the lemmas called
    [isubst_nil] and [isubst_rem], which we state and prove next.

    isubst nil t = t

    subst x v (isubst (rem x E) t) = isubst ((x,v)::E) t
*)

(** The first lemma is straightforward by induction. The TLC tactic [fequals] is
    an enhanced variant of Coq's tactic [f_equal]. *)

Lemma isubst_nil : forall t,
  isubst nil t = t.
Proof using.
  intros t. induction t; simpl; fequals.
Qed.

(** The second lemma is much more involved to prove. We introduce the notion of
    "two equivalent contexts" [E1] and [E2], and argue that substitution for two
    equivalent contexts yields the same result. We then introduce the notion of
    "contexts with disjoint domains", and argue that if [E1] and [E2] are
    disjoint then [isubst (E1 ++ E2) t = isubst E1 (isubst E2 t)].

Before we start, we describe the tactic [case_var], which helps with the
case_analyses on variable equalities, and we prove an auxiliary lemma that
describes the result of a lookup on a context from which a binding has been
removed. It is defined in the file [LibSepVar.v] as:

    Tactic Notation "case_var" :=
      repeat rewrite var_eq_spec in *; repeat case_if.

    The tactic [case_var*] is a shorthand for [case_var] followed with
    automation (essentially, [eauto]). *)

(** A key auxiliary lemma relates [subst] and [isubst]. *)

Lemma subst_eq_isubst_one : forall x v t,
  subst x v t = isubst ((x,v)::nil) t.
Proof using.
  intros. induction t; simpl.
  { fequals. }
  { case_var*. }
  { fequals. case_var*. { rewrite* isubst_nil. } }
  { fequals. case_var; try case_var; simpl; try case_var;
              try rewrite isubst_nil; auto. }
  { fequals*. }
  { fequals*. }
  { fequals*. case_var*. { rewrite* isubst_nil. } }
  { fequals*. }
Qed.

(** A lemma about the lookup in a removal. *)

Lemma lookup_rem : forall x y E,
  lookup x (rem y E) = if var_eq x y then None else lookup x E.
Proof using.
  intros. induction E as [|(z,v) E'].
  { simpl. case_var*. }
  { simpl. case_var*; simpl; case_var*. }
Qed.

(** A lemma about the removal over an append. *)

Lemma rem_app : forall x E1 E2,
  rem x (E1 ++ E2) = rem x E1 ++ rem x E2.
Proof using.
  intros. induction E1 as [|(y,w) E1']; rew_list; simpl. { auto. }
  { case_var*. { rew_list. fequals. } }
Qed.

(** The definition of equivalent contexts. *)

Definition ctx_equiv E1 E2 :=
  forall x, lookup x E1 = lookup x E2.

(** The fact that removal preserves equivalence. *)

Lemma ctx_equiv_rem : forall x E1 E2,
  ctx_equiv E1 E2 ->
  ctx_equiv (rem x E1) (rem x E2).
Proof using.
  introv M. unfolds ctx_equiv. intros y.
  do 2 rewrite lookup_rem. case_var*.
Qed.

(** The fact that substitution for equivalent contexts yields equal results. *)

Lemma isubst_ctx_equiv : forall t E1 E2,
  ctx_equiv E1 E2 ->
  isubst E1 t = isubst E2 t.
Proof using.
  hint ctx_equiv_rem.
  intros t. induction t; introv EQ; simpl; fequals*.
  { rewrite EQ. auto. }
Qed.

(** The definition of disjoint contexts. *)

Definition ctx_disjoint E1 E2 :=
  forall x v1 v2, lookup x E1 = Some v1 -> lookup x E2 = Some v2 -> False.

(** Removal preserves disjointness. *)

Lemma ctx_disjoint_rem : forall x E1 E2,
  ctx_disjoint E1 E2 ->
  ctx_disjoint (rem x E1) (rem x E2).
Proof using.
  introv D. intros y v1 v2 K1 K2. rewrite lookup_rem in *.
  case_var. applys* D K1 K2.
Qed.

(** Lookup in the concatenation of two disjoint contexts [E1] and [E2] is
    equivalent to a lookup in [E1] if it succeeds, or a lookup in [E2]
    otherwise. *)

Lemma lookup_app : forall x E1 E2,
  lookup x (E1 ++ E2) = match lookup x E1 with
                        | None => lookup x E2
                        | Some v => Some v
                        end.
Proof using.
  introv. induction E1 as [|(y,w) E1']; rew_list; simpl; intros.
  { auto. }
  { case_var*. }
Qed.

(** The key induction shows that [isubst] distributes over context
    concatenation. *)

Lemma isubst_app : forall t E1 E2,
  isubst (E1 ++ E2) t = isubst E2 (isubst E1 t).
Proof using.
  hint ctx_disjoint_rem.
  intros t. induction t; simpl; intros.
  { fequals. }
  { rename v into x. rewrite* lookup_app.
    case_eq (lookup x E1); introv K1; case_eq (lookup x E2); introv K2; auto.
    { simpl. rewrite* K2. }
    { simpl. rewrite* K2. } }
  { fequals. rewrite* rem_app. }
  { fequals. do 2 rewrite* rem_app. }
  { fequals*. }
  { fequals*. }
  { fequals*. { rewrite* rem_app. } }
  { fequals*. }
Qed.

(** The next lemma asserts that the concatenation order is irrelevant in a
    substitution if the contexts have disjoint domains. *)

Lemma isubst_app_swap : forall t E1 E2,
  ctx_disjoint E1 E2 ->
  isubst (E1 ++ E2) t = isubst (E2 ++ E1) t.
Proof using.
  introv D. applys isubst_ctx_equiv. applys* ctx_disjoint_equiv_app.
Qed.

(** At last, we derive the desired property of [isubst]. *)

Lemma isubst_rem : forall x v E t,
  isubst ((x, v)::E) t = subst x v (isubst (rem x E) t).
Proof using.
  intros. rewrite subst_eq_isubst_one. rewrite <- isubst_app.
  rewrite isubst_app_swap.
  { applys isubst_ctx_equiv. intros y. rew_list. simpl. case_var*.
    { rewrite lookup_rem. case_var*. } }
  { intros y v1 v2 K1 K2. simpls. case_var.
    { subst. rewrite lookup_rem in K1. case_var*. } }
Qed.

(** We also prove the variant lemma which is useful for handling recursive
    functions in the soundness proof for [wpgen]. *)

Lemma isubst_rem_2 : forall f x vf vx E t,
    isubst ((f,vf)::(x,vx)::E) t
  = subst x vx (subst f vf (isubst (rem x (rem f E)) t)).
Proof using.
  intros. do 2 rewrite subst_eq_isubst_one. do 2 rewrite <- isubst_app.
  rewrite isubst_app_swap.
  { applys isubst_ctx_equiv. intros y. rew_list. simpl.
    do 2 rewrite lookup_rem. case_var*. }
  { intros y v1 v2 K1 K2. rew_listx in *. simpls.
    do 2 rewrite lookup_rem in K1. case_var. }
Qed.

End IsubstProp.

(* 2025-01-06 19:51 *)
