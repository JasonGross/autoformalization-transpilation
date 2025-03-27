(** * LibSepSimpl: Appendix - Simplification Tactic for Entailments *)

Set Implicit Arguments.
From SLF Require Export LibCore.
From SLF Require Export LibSepTLCbuffer.

(* ################################################################# *)
(** * A Functor for Separation Logic Entailment *)

(** This file consists of a functor that provides a tactic for simplifying
    entailment relations. This tactic is somewhat generic in that it can
    be used for several variants of Separation Logic, hence the use of a
    functor to implement the tactic with respect to abstract definitions of
    heap predicates.

    The file provides a number of lemmas that hold in any variant of
    Separation Logic satisfying the requirements of the functor.
    It also provides the following key tactics:

    - [xsimpl] simplifies heap entailments.
    - [xpull] is a restricted version of [xsimpl] that only act over the
      left-hand side of the entailment, leaving the right-hand side unmodified.
    - [xchange] performs transitivity steps in entailments, it enables
      replacing a subset of the heap predicates on the right-hand side with
      another set of heap predicates entailed by the former. *)

(** Bonus: the tactic [rew_heap] normalizes heap predicate expressions;
    it is not used in the course. *)

(* ################################################################# *)
(** * Assumptions of the functor *)

Module Type XsimplParams.

(* ================================================================= *)
(** ** Operators *)

(** The notion of heap predicate and entailment must be provided. *)

Parameter hprop : Type.

Parameter himpl : hprop -> hprop -> Prop.

Definition qimpl A (Q1 Q2:A->hprop) :=
  forall r, himpl (Q1 r) (Q2 r).

(** The core operators of Separation Logic must be provided. *)

Parameter hempty : hprop.

Parameter hstar : hprop -> hprop -> hprop.

Parameter hpure : Prop -> hprop.

Parameter htop : hprop.

Parameter hgc : hprop.

Parameter hwand : hprop -> hprop -> hprop.

Parameter qwand : forall A, (A->hprop) -> (A->hprop) -> hprop.

Parameter hexists : forall A, (A->hprop) -> hprop.

Parameter hforall : forall A, (A->hprop) -> hprop.

(** The predicate [haffine] must be provided. For a fully linear logic, use
    the always-false predicate. For a fully affine logic, use the always-true
    predicate. *)

Parameter haffine : hprop -> Prop.

(* ================================================================= *)
(** ** Notation *)

(** The following notation is used for stating the required properties. *)

Declare Scope heap_scope.

Notation "H1 ==> H2" := (himpl H1 H2)
  (at level 55) : heap_scope.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2)
  (at level 55) : heap_scope.

Notation "\[]" := (hempty)
  (at level 0) : heap_scope.

Notation "\[ P ]" := (hpure P)
  (at level 0, format "\[ P ]") : heap_scope.

Notation "\Top" := (htop) : heap_scope.

Notation "\GC" := (hgc) : heap_scope.

Notation "H1 '\*' H2" := (hstar H1 H2)
  (at level 41, right associativity) : heap_scope.

Notation "Q \*+ H" := (fun x => hstar (Q x) H)
  (at level 40) : heap_scope.

Notation "H1 \-* H2" := (hwand H1 H2)
  (at level 43, right associativity) : heap_scope.

Notation "Q1 \--* Q2" := (qwand Q1 Q2)
  (at level 43) : heap_scope.

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ '  x1  ..  xn , '/ '  H ']'") : heap_scope.

Notation "'\forall' x1 .. xn , H" :=
  (hforall (fun x1 => .. (hforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\forall' '/ '  x1  ..  xn , '/ '  H ']'") : heap_scope.

Local Open Scope heap_scope.

(* ================================================================= *)
(** ** Properties Assumed by the Functor *)

(** The following properties must be satisfied. *)

Implicit Types P : Prop.
Implicit Types H : hprop.

(** Entailment must be an order. *)

Parameter himpl_refl : forall H,
  H ==> H.

Parameter himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).

Parameter himpl_antisym : forall H1 H2,
  (H1 ==> H2) ->
  (H2 ==> H1) ->
  (H1 = H2).

(** The star and the empty heap predicate must form a commutative monoid. *)

Parameter hstar_hempty_l : forall H,
  \[] \* H = H.

Parameter hstar_hempty_r : forall H,
  H \* \[] = H.

Parameter hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.

Parameter hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).

(** The frame property for entailment must hold. *)

Parameter himpl_frame_lr : forall H1 H1' H2 H2',
  H1 ==> H1' ->
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1' \* H2').

Parameter himpl_hstar_trans_l : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H2 \* H3 ==> H4 ->
  H1 \* H3 ==> H4.

(** Characterization of hpure *)

Parameter himpl_hempty_hpure : forall P,
  P ->
  \[] ==> \[P].

Parameter himpl_hstar_hpure_l : forall P H H',
  (P -> H ==> H') ->
  (\[P] \* H) ==> H'.

(** Characterization of [hexists] *)

Parameter himpl_hexists_l : forall A H (J:A->hprop),
  (forall x, J x ==> H) ->
  (hexists J) ==> H.

Parameter himpl_hexists_r : forall A (x:A) H J,
  (H ==> J x) ->
  H ==> (hexists J).

Parameter hstar_hexists : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (fun x => (J x) \* H).

(** Characterization of [hforall] *)

Parameter himpl_hforall_r : forall A (J:A->hprop) H,
  (forall x, H ==> J x) ->
  H ==> (hforall J).

Parameter hstar_hforall : forall H A (J:A->hprop),
  (hforall J) \* H ==> hforall (J \*+ H).

(** Characterization of [hwand] *)

Parameter hwand_equiv : forall H0 H1 H2,
  (H0 ==> H1 \-* H2) <-> (H1 \* H0 ==> H2).

Parameter hwand_curry_eq : forall H1 H2 H3,
  (H1 \* H2) \-* H3 = H1 \-* (H2 \-* H3).

Parameter hwand_hempty_l : forall H,
  (\[] \-* H) = H.

(** Characterization of [qwand] *)

Parameter qwand_equiv : forall H A (Q1 Q2:A->hprop),
  H ==> (Q1 \--* Q2) <-> (Q1 \*+ H) ===> Q2.

Parameter hwand_cancel : forall H1 H2,
  H1 \* (H1 \-* H2) ==> H2.

Parameter qwand_specialize : forall A (x:A) (Q1 Q2:A->hprop),
  (Q1 \--* Q2) ==> (Q1 x \-* Q2 x).

(** Characterization of [htop] *)

Parameter himpl_htop_r : forall H,
  H ==> \Top.

Parameter hstar_htop_htop :
  \Top \* \Top = \Top.

(** Characterization of [hgc] *)

Parameter haffine_hempty :
  haffine \[].

Parameter himpl_hgc_r : forall H,
  haffine H ->
  H ==> \GC.

Parameter hstar_hgc_hgc :
  \GC \* \GC = \GC.

End XsimplParams.

(* ################################################################# *)
(** * Body of the Functor *)

(** When all the assumptions of the functor are statisfied, all the lemmas
    stated below hold, and all the tactics defined below may be used. *)

Module XsimplSetup (HP : XsimplParams).
Import HP.

Local Open Scope heap_scope.

Implicit Types H : hprop.
Implicit Types P : Prop.

#[global]
Hint Resolve himpl_refl.

(* ================================================================= *)
(** ** Properties of [himpl] *)

Lemma himpl_of_eq : forall H1 H2,
  H1 = H2 ->
  H1 ==> H2.
Proof. intros. subst. applys~ himpl_refl. Qed.

Lemma himpl_of_eq_sym : forall H1 H2,
  H1 = H2 ->
  H2 ==> H1.
Proof. intros. subst. applys~ himpl_refl. Qed.

Lemma himpl_hstar_trans_l : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H2 \* H3 ==> H4 ->
  H1 \* H3 ==> H4.
Proof using.
  introv M1 M2. applys himpl_trans M2. applys* himpl_frame_lr M1.
Qed.

(* ================================================================= *)
(** ** Properties of [qimpl] *)

Lemma qimpl_refl : forall A (Q:A->hprop),
  Q ===> Q.
Proof using. intros. hnfs*. Qed.

#[global] Hint Resolve qimpl_refl.

Lemma qimpl_trans : forall A (Q2 Q1 Q3:A->hprop),
  (Q1 ===> Q2) ->
  (Q2 ===> Q3) ->
  (Q1 ===> Q3).
Proof using. introv M1 M2. intros v. applys* himpl_trans. Qed.

Lemma qimpl_antisym : forall A (Q1 Q2:A->hprop),
  (Q1 ===> Q2) ->
  (Q2 ===> Q1) ->
  (Q1 = Q2).
Proof using. introv M1 M2. apply fun_ext_1. intros v. applys* himpl_antisym. Qed.

(* ================================================================= *)
(** ** Properties of [hstar] *)

Lemma hstar_comm_assoc : forall H1 H2 H3,
  H1 \* H2 \* H3 = H2 \* H1 \* H3.
Proof using.
  intros. rewrite <- hstar_assoc.
  rewrite (@hstar_comm H1 H2). rewrite~ hstar_assoc.
Qed.

(* ================================================================= *)
(** ** Representation Predicates *)

(** The arrow notation typically takes the form [x ~> R x],
   to indicate that [X] is the logical value that describes the
   heap structure [x], according to the representation predicate [R].
   It is just a notation for the heap predicate [R X x]. *)

Definition repr (A:Type) (S:A->hprop) (x:A) : hprop :=
  S x.

Notation "x '~>' S" := (repr S x)
  (at level 33, no associativity) : heap_scope.

Lemma repr_eq : forall (A:Type) (S:A->hprop) (x:A),
  (x ~> S) = (S x).
Proof using. auto. Qed.

(** [x ~> Id X] holds when [x] is equal to [X] in the empty heap.
   [Id] is called the identity representation predicate. *)

Definition Id {A:Type} (X:A) (x:A) :=
  \[ X = x ].

(** [xrepr_clean] simplifies instances of
   [p ~> (fun _ => _)] by unfolding the arrow,
   but only when the body does not captures
   mklocally bound variables. This tactic should
   normally not be used directly *)

Ltac xrepr_clean_core tt :=
  repeat match goal with |- context C [?p ~> ?E] =>
   match E with (fun _ => _) =>
     let E' := eval cbv beta in (E p) in
     let G' := context C [E'] in
     let G := match goal with |- ?G => G end in
     change G with G' end end.

Tactic Notation "xrepr_clean" :=
  xrepr_clean_core tt.

Lemma repr_id : forall A (x X:A),
  (x ~> Id X) = \[X = x].
Proof using. intros. unfold Id. xrepr_clean. auto. Qed.

(* ================================================================= *)
(** ** [rew_heap] Tactic to Normalize Expressions with [hstar] *)

(** [rew_heap] removes empty heap predicates, and normalizes w.r.t.
    associativity of star.

    [rew_heap_assoc] only normalizes w.r.t. associativity.
    (It should only be used internally for tactic implementation. *)

Lemma star_post_empty : forall B (Q:B->hprop),
  Q \*+ \[] = Q.
Proof using. extens. intros. rewrite* hstar_hempty_r. Qed.

#[global]
Hint Rewrite hstar_hempty_l hstar_hempty_r
            hstar_assoc star_post_empty hwand_hempty_l : rew_heap.

Tactic Notation "rew_heap" :=
  autorewrite with rew_heap.
Tactic Notation "rew_heap" "in" "*" :=
  autorewrite with rew_heap in *.
Tactic Notation "rew_heap" "in" hyp(H) :=
  autorewrite with rew_heap in H.

Tactic Notation "rew_heap" "~" :=
  rew_heap; auto_tilde.
Tactic Notation "rew_heap" "~" "in" "*" :=
  rew_heap in *; auto_tilde.
Tactic Notation "rew_heap" "~" "in" hyp(H) :=
  rew_heap in H; auto_tilde.

Tactic Notation "rew_heap" "*" :=
  rew_heap; auto_star.
Tactic Notation "rew_heap" "*" "in" "*" :=
  rew_heap in *; auto_star.
Tactic Notation "rew_heap" "*" "in" hyp(H) :=
  rew_heap in H; auto_star.

#[global]
Hint Rewrite hstar_assoc : rew_heap_assoc.

Tactic Notation "rew_heap_assoc" :=
  autorewrite with rew_heap_assoc.

(* ================================================================= *)
(** ** Auxiliary Tactics Used by [xpull] and [xsimpl] *)

Ltac remove_empty_heaps_from H :=
  match H with context[ ?H1 \* \[] ] =>
    match is_evar_as_bool H1 with
    | false => rewrite (@hstar_hempty_r H1)
    | true => let X := fresh in
              set (X := H1);
              rewrite (@hstar_hempty_r X);
              subst X
    end end.

Ltac remove_empty_heaps_haffine tt :=
  repeat match goal with |- haffine ?H => remove_empty_heaps_from H end.

Ltac remove_empty_heaps_left tt :=
  repeat match goal with |- ?H1 ==> _ => remove_empty_heaps_from H1 end.

Ltac remove_empty_heaps_right tt :=
  repeat match goal with |- _ ==> ?H2 => remove_empty_heaps_from H2 end.


(* ================================================================= *)
(** ** Tactics [xsimpl] and [xpull] for Heap Entailments *)

(** The implementation of the tactics is fairly involved. The high-level
    specification of the tactic appears in the last appendix of:
    http://www.chargueraud.org/research/2020/seq_seplogic/seq_seplogic.pdf . *)

(* ----------------------------------------------------------------- *)
(** *** [xaffine] placeholder *)

Ltac xaffine_core tt := (* to be generalized lated *)
  try solve [ assumption | apply haffine_hempty ].

Tactic Notation "xaffine" :=
  xaffine_core tt.

(* ----------------------------------------------------------------- *)
(** *** Hints for tactics such as [xsimpl] *)

Inductive Xsimpl_hint : list Boxer -> Type :=
  | xsimpl_hint : forall (L:list Boxer), Xsimpl_hint L.

Ltac xsimpl_hint_put L :=
  let H := fresh "Hint" in
  generalize (xsimpl_hint L); intros H.

Ltac xsimpl_hint_next cont :=
  match goal with H: Xsimpl_hint ((boxer ?x)::?L) |- _ =>
    clear H; xsimpl_hint_put L; cont x end.

Ltac xsimpl_hint_remove tt :=
  match goal with H: Xsimpl_hint _ |- _ => clear H end.

(* ----------------------------------------------------------------- *)
(** *** Lemmas [hstars_reorder_..] to flip an iterated [hstar]. *)

(** [hstars_flip tt] applies to a goal of the form [H1 \* .. \* Hn \* \[]= ?H]
    and instantiates [H] with [Hn \* ... \* H1 \* \[]].
    If [n > 9], the maximum arity supported, the tactic unifies [H] with
    the original LHS. *)

Lemma hstars_flip_0 :
  \[] = \[].
Proof using. auto. Qed.

Lemma hstars_flip_1 : forall H1,
  H1 \* \[] = H1 \* \[].
Proof using. auto. Qed.

Lemma hstars_flip_2 : forall H1 H2,
  H1 \* H2 \* \[] = H2 \* H1 \* \[].
Proof using. intros. rew_heap. rewrite (hstar_comm H2). rew_heap~. Qed.

Lemma hstars_flip_3 : forall H1 H2 H3,
  H1 \* H2 \* H3 \* \[] = H3 \* H2 \* H1 \* \[].
Proof using. intros. rewrite <- (hstars_flip_2 H1). rew_heap. rewrite (hstar_comm H3). rew_heap~. Qed.

Lemma hstars_flip_4 : forall H1 H2 H3 H4,
  H1 \* H2 \* H3 \* H4 \* \[] = H4 \* H3 \* H2 \* H1 \* \[].
Proof using. intros. rewrite <- (hstars_flip_3 H1). rew_heap. rewrite (hstar_comm H4). rew_heap~. Qed.

Lemma hstars_flip_5 : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* H3 \* H4 \* H5 \* \[] = H5 \* H4 \* H3 \* H2 \* H1 \* \[].
Proof using. intros. rewrite <- (hstars_flip_4 H1). rew_heap. rewrite (hstar_comm H5). rew_heap~. Qed.

Lemma hstars_flip_6 : forall H1 H2 H3 H4 H5 H6,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* \[]
  = H6 \* H5 \* H4 \* H3 \* H2 \* H1 \* \[].
Proof using. intros. rewrite <- (hstars_flip_5 H1). rew_heap. rewrite (hstar_comm H6). rew_heap~. Qed.

Lemma hstars_flip_7 : forall H1 H2 H3 H4 H5 H6 H7,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* \[]
  = H7 \* H6 \* H5 \* H4 \* H3 \* H2 \* H1 \* \[].
Proof using. intros. rewrite <- (hstars_flip_6 H1). rew_heap. rewrite (hstar_comm H7). rew_heap~. Qed.

Lemma hstars_flip_8 : forall H1 H2 H3 H4 H5 H6 H7 H8,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* \[]
  = H8 \* H7 \* H6 \* H5 \* H4 \* H3 \* H2 \* H1 \* \[].
Proof using. intros. rewrite <- (hstars_flip_7 H1). rew_heap. rewrite (hstar_comm H8). rew_heap~. Qed.

Lemma hstars_flip_9 : forall H1 H2 H3 H4 H5 H6 H7 H8 H9,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* H9 \* \[]
  = H9 \* H8 \* H7 \* H6 \* H5 \* H4 \* H3 \* H2 \* H1 \* \[].
Proof using. intros. rewrite <- (hstars_flip_8 H1). rew_heap. rewrite (hstar_comm H9). rew_heap~. Qed.

Ltac hstars_flip_lemma i :=
  match number_to_nat i with
  | 0%nat => constr:(hstars_flip_0)
  | 1%nat => constr:(hstars_flip_1)
  | 2%nat => constr:(hstars_flip_2)
  | 3%nat => constr:(hstars_flip_3)
  | 4%nat => constr:(hstars_flip_4)
  | 5%nat => constr:(hstars_flip_5)
  | 6%nat => constr:(hstars_flip_6)
  | 7%nat => constr:(hstars_flip_7)
  | 8%nat => constr:(hstars_flip_8)
  | 9%nat => constr:(hstars_flip_9)
  | _ => constr:(hstars_flip_1) (* unsupported *)
  end.

Ltac hstars_arity i Hs :=
  match Hs with
  | \[] => constr:(i)
  | ?H1 \* ?H2 => hstars_arity (S i) H2
  end.

Ltac hstars_flip_arity tt :=
  match goal with |- ?HL = ?HR => hstars_arity 0%nat HL end.

Ltac hstars_flip tt :=
  let i := hstars_flip_arity tt in
  let L := hstars_flip_lemma i in
  eapply L.

(* ----------------------------------------------------------------- *)
(** *** Lemmas [hstars_pick_...] to extract hyps in depth. *)

(** [hstars_search Hs test] applies to an expression [Hs]
    of the form either [H1 \* ... \* Hn \* \[]]
    or [H1 \* ... \* Hn]. It invokes the function [test i Hi]
    for each of the [Hi] in turn until the tactic succeeds.
    In the particular case of invoking [test n Hn] when there
    is no trailing [\[]], the call is of the form [test (hstars_last n) Hn]
    where [hstars_last] is an identity tag. *)

Definition hstars_last (A:Type) (X:A) := X.

Ltac hstars_search Hs test :=
  let rec aux i Hs :=
    first [ match Hs with ?H \* _ => test i H end
          | match Hs with _ \* ?Hs' => aux (S i) Hs' end
          | match Hs with ?H => test (hstars_last i) H end ] in
  aux 1%nat Hs.

(** [hstars_pick_lemma i] returns one of the lemma below,
    which enables reordering in iterated stars, by extracting
    the i-th item to bring it to the front. *)

Lemma hstars_pick_1 : forall H1 H,
  H1 \* H = H1 \* H.
Proof using. auto. Qed.

Lemma hstars_pick_2 : forall H1 H2 H,
  H1 \* H2 \* H = H2 \* H1 \* H.
Proof using. intros. rewrite~ (hstar_comm_assoc H1). Qed.

Lemma hstars_pick_3 : forall H1 H2 H3 H,
  H1 \* H2 \* H3 \* H = H3 \* H1 \* H2 \* H.
Proof using. intros. rewrite~ (hstar_comm_assoc H2). applys hstars_pick_2. Qed.

Lemma hstars_pick_4 : forall H1 H2 H3 H4 H,
  H1 \* H2 \* H3 \* H4 \* H = H4 \* H1 \* H2 \* H3 \* H.
Proof using. intros. rewrite~ (hstar_comm_assoc H3). applys hstars_pick_3. Qed.

Lemma hstars_pick_5 : forall H1 H2 H3 H4 H5 H,
  H1 \* H2 \* H3 \* H4 \* H5 \* H = H5 \* H1 \* H2 \* H3 \* H4 \* H.
Proof using. intros. rewrite~ (hstar_comm_assoc H4). applys hstars_pick_4. Qed.

Lemma hstars_pick_6 : forall H1 H2 H3 H4 H5 H6 H,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H
  = H6 \* H1 \* H2 \* H3 \* H4 \* H5 \* H.
Proof using. intros. rewrite~ (hstar_comm_assoc H5). applys hstars_pick_5. Qed.

Lemma hstars_pick_7 : forall H1 H2 H3 H4 H5 H6 H7 H,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H
  = H7 \* H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H.
Proof using. intros. rewrite~ (hstar_comm_assoc H6). applys hstars_pick_6. Qed.

Lemma hstars_pick_8 : forall H1 H2 H3 H4 H5 H6 H7 H8 H,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* H
  = H8 \* H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H.
Proof using. intros. rewrite~ (hstar_comm_assoc H7). applys hstars_pick_7. Qed.

Lemma hstars_pick_9 : forall H1 H2 H3 H4 H5 H6 H7 H8 H9 H,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* H9 \* H
  = H9 \* H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* H.
Proof using. intros. rewrite~ (hstar_comm_assoc H8). applys hstars_pick_8. Qed.

Lemma hstars_pick_last_1 : forall H1,
  H1 = H1.
Proof using. auto. Qed.

Lemma hstars_pick_last_2 : forall H1 H2,
  H1 \* H2 = H2 \* H1.
Proof using. intros. rewrite~ (hstar_comm). Qed.

Lemma hstars_pick_last_3 : forall H1 H2 H3,
  H1 \* H2 \* H3 = H3 \* H1 \* H2.
Proof using. intros. rewrite~ (hstar_comm H2). applys hstars_pick_2. Qed.

Lemma hstars_pick_last_4 : forall H1 H2 H3 H4,
  H1 \* H2 \* H3 \* H4 = H4 \* H1 \* H2 \* H3.
Proof using. intros. rewrite~ (hstar_comm H3). applys hstars_pick_3. Qed.

Lemma hstars_pick_last_5 : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* H3 \* H4 \* H5 = H5 \* H1 \* H2 \* H3 \* H4.
Proof using. intros. rewrite~ (hstar_comm H4). applys hstars_pick_4. Qed.

Lemma hstars_pick_last_6 : forall H1 H2 H3 H4 H5 H6,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6
  = H6 \* H1 \* H2 \* H3 \* H4 \* H5.
Proof using. intros. rewrite~ (hstar_comm H5). applys hstars_pick_5. Qed.

Lemma hstars_pick_last_7 : forall H1 H2 H3 H4 H5 H6 H7,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7
  = H7 \* H1 \* H2 \* H3 \* H4 \* H5 \* H6.
Proof using. intros. rewrite~ (hstar_comm H6). applys hstars_pick_6. Qed.

Lemma hstars_pick_last_8 : forall H1 H2 H3 H4 H5 H6 H7 H8,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8
  = H8 \* H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7.
Proof using. intros. rewrite~ (hstar_comm H7). applys hstars_pick_7. Qed.

Lemma hstars_pick_last_9 : forall H1 H2 H3 H4 H5 H6 H7 H8 H9,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* H9
  = H9 \* H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8.
Proof using. intros. rewrite~ (hstar_comm H8). applys hstars_pick_8. Qed.

Ltac hstars_pick_lemma i :=
  let unsupported tt := fail 100 "hstars_pick supports only arity up to 9" in
  match i with
  | hstars_last ?j => match number_to_nat j with
    | 1%nat => constr:(hstars_pick_last_1)
    | 2%nat => constr:(hstars_pick_last_2)
    | 3%nat => constr:(hstars_pick_last_3)
    | 4%nat => constr:(hstars_pick_last_4)
    | 5%nat => constr:(hstars_pick_last_5)
    | 6%nat => constr:(hstars_pick_last_6)
    | 7%nat => constr:(hstars_pick_last_7)
    | 8%nat => constr:(hstars_pick_last_8)
    | 9%nat => constr:(hstars_pick_last_9)
    | _ => unsupported tt
    end
  | ?j => match number_to_nat j with
    | 1%nat => constr:(hstars_pick_1)
    | 2%nat => constr:(hstars_pick_2)
    | 3%nat => constr:(hstars_pick_3)
    | 4%nat => constr:(hstars_pick_4)
    | 5%nat => constr:(hstars_pick_5)
    | 6%nat => constr:(hstars_pick_6)
    | 7%nat => constr:(hstars_pick_7)
    | 8%nat => constr:(hstars_pick_8)
    | 9%nat => constr:(hstars_pick_9)
    | _ => unsupported tt
    end
  end.

(* ----------------------------------------------------------------- *)
(** *** Documentation for the Tactic [xsimpl] *)

(** ... doc for [xsimpl] to update

   At the end, there remains a heap entailment with a simplified
   LHS and a simplified RHS, with items not cancelled out.
   At this point, if the goal is of the form [H ==> \GC] or [H ==> \Top] or
   [H ==> ?H'] for some evar [H'], then [xsimpl] solves the goal.
   Else, it leaves whatever remains.

   For the cancellation part, [xsimpl] cancels out [H] from the LHS
   with [H'] from the RHS if either [H'] is syntactically equal to [H],
   or if [H] and [H'] both have the form [x ~> ...] for the same [x].
   Note that, in case of a mismatch with [x ~> R X] on the LHS and
   [x ~> R' X'] on the RHS, [xsimpl] will produce a goal of the form
   [(x ~> R X) = (x ~> R' X')] which will likely be unsolvable.
   It is the user's responsability to perform the appropriate conversion
   steps prior to calling [xsimpl].

   Remark: the reason for the special treatment of [x ~> ...] is that
   it is very useful to be able to automatically cancel out
   [x ~> R X] from the LHS with [x ~> R ?Y], for some evar [?Y] which
   typically is introduced from an existential, e.g. [\exists Y, x ~> R Y].

   Remark: importantly, [xsimpl] does not attempt any simplification on
   a representation predicate of the form [?x ~> ...], when the [?x]
   is an uninstantiated evar. Such situation may arise for example
   with the following RHS: [\exists p, (r ~> Ref p) \* (p ~> Ref 3)].

   As a special feature, [xsimpl] may be provided optional arguments
   for instantiating the existentials (instead of introducing evars).
   These optional arguments need to be given in left-right order,
   and are used on a first-match basis: the head value is used if its
   type matches the type expected by the existential, else an evar
   is introduced for that existential. *)

(** [Xsimpl (Hla, Hlw, Hlt) (Hra, Hrg, Hrt)] is interepreted as
    the entailment [Hla \* Hlw \* Hlt ==> Hra \* Hrg \* Hrt] where
    - [Hla] denotes "cleaned up" items from the left hand side
    - [Hlw] denotes the [H1 \-* H2] and [Q1 \--* Q2] items from the left hand side
    - [Hlt] denotes the remaining items to process  items from the left hand side
    - [Hra] denotes "cleaned up" items from the right hand side
    - [Hrg] denotes the [\GC] and [\Top] items from the right hand side
    - [Hrt] denotes the remaining items to process from the right hand side

    Note: we assume that all items consist of iterated hstars, and are
    always terminated by an empty heap. *)

Definition Xsimpl (HL HR:hprop*hprop*hprop) :=
  let '(Hla,Hlw,Hlt) := HL in
  let '(Hra,Hrg,Hrt) := HR in
  Hla \* Hlw \* Hlt ==> Hra \* Hrg \* Hrt.

(** [protect X] is use to prevent [xsimpl] from investigating inside [X] *)

Definition protect (A:Type) (X:A) : A := X.

(** Auxiliary lemmas to prove lemmas for [xsimpl] implementation. *)

Lemma Xsimpl_trans_l : forall Hla1 Hlw1 Hlt1 Hla2 Hlw2 Hlt2 HR,
  Xsimpl (Hla2,Hlw2,Hlt2) HR ->
  Hla1 \* Hlw1 \* Hlt1 ==> Hla2 \* Hlw2 \* Hlt2 ->
  Xsimpl (Hla1,Hlw1,Hlt1) HR.
Proof using.
  introv M1 E. destruct HR as [[Hra Hrg] Hrt]. unfolds Xsimpl.
  applys* himpl_trans M1.
Qed.

Lemma Xsimpl_trans_r : forall Hra1 Hrg1 Hrt1 Hra2 Hrg2 Hrt2 HL,
  Xsimpl HL (Hra2,Hrg2,Hrt2) ->
  Hra2 \* Hrg2 \* Hrt2 ==> Hra1 \* Hrg1 \* Hrt1 ->
  Xsimpl HL (Hra1,Hrg1,Hrt1).
Proof using.
  introv M1 E. destruct HL as [[Hla Hlw] Hlt]. unfolds Xsimpl.
  applys* himpl_trans M1.
Qed.

Lemma Xsimpl_trans : forall Hla1 Hlw1 Hlt1 Hla2 Hlw2 Hlt2 Hra1 Hrg1 Hrt1 Hra2 Hrg2 Hrt2,
  Xsimpl (Hla2,Hlw2,Hlt2) (Hra2,Hrg2,Hrt2) ->
  (Hla2 \* Hlw2 \* Hlt2 ==> Hra2 \* Hrg2 \* Hrt2 ->
   Hla1 \* Hlw1 \* Hlt1 ==> Hra1 \* Hrg1 \* Hrt1) ->
  Xsimpl (Hla1,Hlw1,Hlt1) (Hra1,Hrg1,Hrt1).
Proof using. introv M1 E. unfolds Xsimpl. eauto. Qed.

(* ----------------------------------------------------------------- *)
(** *** Basic cancellation tactic used to establish lemmas used by [xsimpl] *)

Lemma hstars_simpl_start : forall H1 H2,
  H1 \* \[] ==> \[] \* H2 \* \[] ->
  H1 ==> H2.
Proof using. introv M. rew_heap~ in *. Qed.

Lemma hstars_simpl_keep : forall H1 Ha H Ht,
  H1 ==> (H \* Ha) \* Ht ->
  H1 ==> Ha \* H \* Ht.
Proof using. introv M. rew_heap in *. rewrite~ hstar_comm_assoc. Qed.

Lemma hstars_simpl_cancel : forall H1 Ha H Ht,
  H1 ==> Ha \* Ht ->
  H \* H1 ==> Ha \* H \* Ht.
Proof using. introv M. rewrite hstar_comm_assoc. applys~ himpl_frame_lr. Qed.

Lemma hstars_simpl_pick_lemma : forall H1 H1' H2,
  H1 = H1' ->
  H1' ==> H2 ->
  H1 ==> H2.
Proof using. introv M. subst~. Qed.

Ltac hstars_simpl_pick i :=
  (* Remark: the [hstars_pick_last] lemmas should never be needed here *)
  let L := hstars_pick_lemma i in
  eapply hstars_simpl_pick_lemma; [ apply L | ].

Ltac hstars_simpl_start tt :=
  match goal with |- ?H1 ==> ?H2 => idtac end;
  applys hstars_simpl_start;
  rew_heap_assoc.

Ltac hstars_simpl_step tt :=
  match goal with |- ?Hl ==> ?Ha \* ?H \* ?H2 =>
    first [
      hstars_search Hl ltac:(fun i H' =>
        match H' with H => hstars_simpl_pick i end);
      apply hstars_simpl_cancel
    | apply hstars_simpl_keep ]
  end.

Ltac hstars_simpl_post tt :=
  rew_heap; try apply himpl_refl.

Ltac hstars_simpl_core tt :=
  hstars_simpl_start tt;
  repeat (hstars_simpl_step tt);
  hstars_simpl_post tt.

Tactic Notation "hstars_simpl" :=
  hstars_simpl_core tt.

(* ----------------------------------------------------------------- *)
(** *** Transition lemmas *)

(** Transition lemmas to start the process *)

Lemma xpull_protect : forall H1 H2,
  H1 ==> protect H2 ->
  H1 ==> H2.
Proof using. auto. Qed.

Lemma xsimpl_start : forall H1 H2,
  Xsimpl (\[], \[], (H1 \* \[])) (\[], \[], (H2 \* \[])) ->
  H1 ==> H2.
Proof using. introv M. unfolds Xsimpl. rew_heap~ in *. Qed.
(* Note: [repeat rewrite hstar_assoc] after applying this lemma *)

(** Transition lemmas for LHS extraction operations *)

Ltac xsimpl_l_start M :=
  introv M;
  match goal with HR: hprop*hprop*hprop |- _ =>
    destruct HR as [[Hra Hrg] Hrt]; unfolds Xsimpl end.

Ltac xsimpl_l_start' M :=
  xsimpl_l_start M; applys himpl_trans (rm M); hstars_simpl.

Lemma xsimpl_l_hempty : forall Hla Hlw Hlt HR,
  Xsimpl (Hla, Hlw, Hlt) HR ->
  Xsimpl (Hla, Hlw, (\[] \* Hlt)) HR.
Proof using. xsimpl_l_start' M. Qed.

Lemma xsimpl_l_hpure : forall P Hla Hlw Hlt HR,
  (P -> Xsimpl (Hla, Hlw, Hlt) HR) ->
  Xsimpl (Hla, Hlw, (\[P] \* Hlt)) HR.
Proof using.
  xsimpl_l_start M. rewrite hstars_pick_3. applys* himpl_hstar_hpure_l.
Qed.

Lemma xsimpl_l_hexists : forall A (J:A->hprop) Hla Hlw Hlt HR,
  (forall x, Xsimpl (Hla, Hlw, (J x \* Hlt)) HR) ->
  Xsimpl (Hla, Hlw, (hexists J \* Hlt)) HR.
Proof using.
  xsimpl_l_start M. rewrite hstars_pick_3. rewrite hstar_hexists.
  applys* himpl_hexists_l. intros. rewrite~ <- hstars_pick_3.
Qed.

Lemma xsimpl_l_acc_wand : forall H Hla Hlw Hlt HR,
  Xsimpl (Hla, (H \* Hlw), Hlt) HR ->
  Xsimpl (Hla, Hlw, (H \* Hlt)) HR.
Proof using. xsimpl_l_start' M. Qed.

Lemma xsimpl_l_acc_other : forall H Hla Hlw Hlt HR,
  Xsimpl ((H \* Hla), Hlw, Hlt) HR ->
  Xsimpl (Hla, Hlw, (H \* Hlt)) HR.
Proof using. xsimpl_l_start' M. Qed.

(** Transition lemmas for LHS cancellation operations
    ---Hlt is meant to be empty there *)

Lemma xsimpl_l_cancel_hwand_hempty : forall H2 Hla Hlw Hlt HR,
  Xsimpl (Hla, Hlw, (H2 \* Hlt)) HR ->
  Xsimpl (Hla, ((\[] \-* H2) \* Hlw), Hlt) HR.
Proof using. xsimpl_l_start' M. Qed.

Lemma xsimpl_l_cancel_hwand : forall H1 H2 Hla Hlw Hlt HR,
  Xsimpl (\[], Hlw, (Hla \* H2 \* Hlt)) HR ->
  Xsimpl ((H1 \* Hla), ((H1 \-* H2) \* Hlw), Hlt) HR.
Proof using. xsimpl_l_start' M. applys~ hwand_cancel. Qed.

Lemma xsimpl_l_cancel_qwand : forall A (x:A) (Q1 Q2:A->hprop) Hla Hlw Hlt HR,
  Xsimpl (\[], Hlw, (Hla \* Q2 x \* Hlt)) HR ->
  Xsimpl ((Q1 x \* Hla), ((Q1 \--* Q2) \* Hlw), Hlt) HR.
Proof using.
  xsimpl_l_start' M. rewrite hstar_comm. applys himpl_hstar_trans_l.
  applys qwand_specialize x. rewrite hstar_comm. applys hwand_cancel.
Qed.

Lemma xsimpl_l_keep_wand : forall H Hla Hlw Hlt HR,
  Xsimpl ((H \* Hla), Hlw, Hlt) HR ->
  Xsimpl (Hla, (H \* Hlw), Hlt) HR.
Proof using. xsimpl_l_start' M. Qed.

Lemma xsimpl_l_hwand_reorder : forall H1 H1' H2 Hla Hlw Hlt HR,
  H1 = H1' ->
  Xsimpl (Hla, ((H1' \-* H2) \* Hlw), Hlt) HR ->
  Xsimpl (Hla, ((H1 \-* H2) \* Hlw), Hlt) HR.
Proof using. intros. subst*. Qed.

Lemma xsimpl_l_cancel_hwand_hstar : forall H1 H2 H3 Hla Hlw Hlt HR,
  Xsimpl (Hla, Hlw, ((H2 \-* H3) \* Hlt)) HR ->
  Xsimpl ((H1 \* Hla), (((H1 \* H2) \-* H3) \* Hlw), Hlt) HR.
Proof using.
  xsimpl_l_start' M. rewrite hwand_curry_eq. applys hwand_cancel.
Qed.

Lemma xsimpl_l_cancel_hwand_hstar_hempty : forall H2 H3 Hla Hlw Hlt HR,
  Xsimpl (Hla, Hlw, ((H2 \-* H3) \* Hlt)) HR ->
  Xsimpl (Hla, (((\[] \* H2) \-* H3) \* Hlw), Hlt) HR.
Proof using. xsimpl_l_start' M. Qed.

(** Transition lemmas for RHS extraction operations *)

Ltac xsimpl_r_start M :=
  introv M;
  match goal with HL: hprop*hprop*hprop |- _ =>
    destruct HL as [[Hla Hlw] Hlt]; unfolds Xsimpl end.

Ltac xsimpl_r_start' M :=
  xsimpl_r_start M; applys himpl_trans (rm M); hstars_simpl.

Lemma xsimpl_r_hempty : forall Hra Hrg Hrt HL,
  Xsimpl HL (Hra, Hrg, Hrt) ->
  Xsimpl HL (Hra, Hrg, (\[] \* Hrt)).
Proof using. xsimpl_r_start' M. Qed.

Lemma xsimpl_r_hwand_same : forall H Hra Hrg Hrt HL,
  Xsimpl HL (Hra, Hrg, Hrt) ->
  Xsimpl HL (Hra, Hrg, ((H \-* H) \* Hrt)).
Proof using. xsimpl_r_start' M. rewrite hwand_equiv. rew_heap~. Qed.

Lemma xsimpl_r_hpure : forall P Hra Hrg Hrt HL,
  P ->
  Xsimpl HL (Hra, Hrg, Hrt) ->
  Xsimpl HL (Hra, Hrg, (\[P] \* Hrt)).
Proof using.
  introv HP. xsimpl_r_start' M. applys* himpl_hempty_hpure.
Qed.

Lemma xsimpl_r_hexists : forall A (x:A) (J:A->hprop) Hra Hrg Hrt HL,
  Xsimpl HL (Hra, Hrg, (J x \* Hrt)) ->
  Xsimpl HL (Hra, Hrg, (hexists J \* Hrt)).
Proof using. xsimpl_r_start' M. applys* himpl_hexists_r. Qed.

Lemma xsimpl_r_id : forall A (x X:A) Hra Hrg Hrt HL,
  (X = x) ->
  Xsimpl HL (Hra, Hrg, Hrt) ->
  Xsimpl HL (Hra, Hrg, (x ~> Id X \* Hrt)).
Proof using.
  introv ->. xsimpl_r_start' M. rewrite repr_id.
  applys* himpl_hempty_hpure.
Qed.

Lemma xsimpl_r_id_unify : forall A (x:A) Hra Hrg Hrt HL,
  Xsimpl HL (Hra, Hrg, Hrt) ->
  Xsimpl HL (Hra, Hrg, (x ~> Id x \* Hrt)).
Proof using. introv M. applys~ xsimpl_r_id. Qed.

Lemma xsimpl_r_keep : forall H Hra Hrg Hrt HL,
  Xsimpl HL ((H \* Hra), Hrg, Hrt) ->
  Xsimpl HL (Hra, Hrg, (H \* Hrt)).
Proof using. xsimpl_r_start' M. Qed.

(** Transition lemmas for [\Top] and [\GC] cancellation *)

  (* [H] meant to be [\GC] or [\Top] *)
Lemma xsimpl_r_hgc_or_htop : forall H Hra Hrg Hrt HL,
  Xsimpl HL (Hra, (H \* Hrg), Hrt) ->
  Xsimpl HL (Hra, Hrg, (H \* Hrt)).
Proof using. xsimpl_r_start' M. Qed.

Lemma xsimpl_r_htop_replace_hgc : forall Hra Hrg Hrt HL,
  Xsimpl HL (Hra, (\Top \* Hrg), Hrt) ->
  Xsimpl HL (Hra, (\GC \* Hrg), (\Top \* Hrt)).
Proof using. xsimpl_r_start' M. applys himpl_hgc_r. xaffine. Qed.

Lemma xsimpl_r_hgc_drop : forall Hra Hrg Hrt HL,
  Xsimpl HL (Hra, Hrg, Hrt) ->
  Xsimpl HL (Hra, Hrg, (\GC \* Hrt)).
Proof using. xsimpl_r_start' M. applys himpl_hgc_r. xaffine. Qed.

Lemma xsimpl_r_htop_drop : forall Hra Hrg Hrt HL,
  Xsimpl HL (Hra, Hrg, Hrt) ->
  Xsimpl HL (Hra, Hrg, (\Top \* Hrt)).
Proof using. xsimpl_r_start' M. applys himpl_htop_r. Qed.

(** Transition lemmas for LHS/RHS cancellation
    --- meant to be applied when Hlw and Hlt are empty *)

Ltac xsimpl_lr_start M :=
  introv M; unfolds Xsimpl; rew_heap in *.

Ltac xsimpl_lr_start' M :=
  xsimpl_lr_start M; hstars_simpl;
  try (applys himpl_trans (rm M); hstars_simpl).

Lemma xsimpl_lr_cancel_same : forall H Hla Hlw Hlt Hra Hrg Hrt,
  Xsimpl (Hla, Hlw, Hlt) (Hra, Hrg, Hrt) ->
  Xsimpl ((H \* Hla), Hlw, Hlt) (Hra, Hrg, (H \* Hrt)).
Proof using. xsimpl_lr_start' M. Qed.

Lemma xsimpl_lr_cancel_htop : forall H Hla Hlw Hlt Hra Hrg Hrt,
  Xsimpl (Hla, Hlw, Hlt) (Hra, (\Top \* Hrg), Hrt) ->
  Xsimpl ((H \* Hla), Hlw, Hlt) (Hra, (\Top \* Hrg), Hrt).
Proof using.
  xsimpl_lr_start M. rewrite (hstar_comm_assoc Hra) in *.
  rewrite <- hstar_htop_htop. rew_heap. applys himpl_frame_lr M.
  applys himpl_htop_r.
Qed.

Lemma xsimpl_lr_cancel_hgc : forall Hla Hlw Hlt Hra Hrg Hrt,
  Xsimpl (Hla, Hlw, Hlt) (Hra, (\GC \* Hrg), Hrt) ->
  Xsimpl ((\GC \* Hla), Hlw, Hlt) (Hra, (\GC \* Hrg), Hrt).
Proof using.
  xsimpl_lr_start M. rewrite (hstar_comm_assoc Hra).
  rewrite <- hstar_hgc_hgc at 2. rew_heap.
  applys~ himpl_frame_lr. applys himpl_trans M. hstars_simpl.
Qed.

Lemma xsimpl_lr_cancel_eq : forall H1 H2 Hla Hlw Hlt Hra Hrg Hrt,
  (H1 = H2) ->
  Xsimpl (Hla, Hlw, Hlt) (Hra, Hrg, Hrt) ->
  Xsimpl ((H1 \* Hla), Hlw, Hlt) (Hra, Hrg, (H2 \* Hrt)).
Proof using. introv ->. apply~ xsimpl_lr_cancel_same. Qed.

Lemma xsimpl_lr_cancel_eq_repr : forall A p (E1 E2:A->hprop) Hla Hlw Hlt Hra Hrg Hrt,
  E1 = E2 ->
  Xsimpl (Hla, Hlw, Hlt) (Hra, Hrg, Hrt) ->
  Xsimpl (((p ~> E1) \* Hla), Hlw, Hlt) (Hra, Hrg, ((p ~> E2) \* Hrt)).
Proof using. introv M. subst. apply~ xsimpl_lr_cancel_same. Qed.

Lemma xsimpl_lr_hwand : forall H1 H2 Hla,
  Xsimpl (\[], \[], (H1 \* Hla)) (\[], \[], H2 \* \[]) ->
  Xsimpl (Hla, \[], \[]) ((H1 \-* H2) \* \[], \[], \[]).
Proof using.
  xsimpl_lr_start' M. rewrite hwand_equiv.
  applys himpl_trans (rm M). hstars_simpl.
Qed.

Lemma xsimpl_lr_hwand_hfalse : forall Hla H1,
  Xsimpl (Hla, \[], \[]) ((\[False] \-* H1) \* \[], \[], \[]).
Proof using.
  intros. generalize True. xsimpl_lr_start M. rewrite hwand_equiv.
  applys himpl_hstar_hpure_l. auto_false.
Qed.

Lemma xsimpl_lr_qwand : forall A (Q1 Q2:A->hprop) Hla,
  (forall x, Xsimpl (\[], \[], (Q1 x \* Hla)) (\[], \[], Q2 x \* \[])) ->
  Xsimpl (Hla, \[], \[]) ((Q1 \--* Q2) \* \[], \[], \[]).
Proof using.
  xsimpl_lr_start M. rewrite qwand_equiv. intros x.
  specializes M x. rew_heap~ in M.
Qed.

Lemma xsimpl_lr_qwand_unit : forall (Q1 Q2:unit->hprop) Hla,
  Xsimpl (\[], \[], (Q1 tt \* Hla)) (\[], \[], (Q2 tt \* \[])) ->
  Xsimpl (Hla, \[], \[]) ((Q1 \--* Q2) \* \[], \[], \[]).
Proof using. introv M. applys xsimpl_lr_qwand. intros []. applys M. Qed.

Lemma xsimpl_lr_hforall : forall A (J:A->hprop) Hla,
  (forall x, Xsimpl (\[], \[], Hla) (\[], \[], J x \* \[])) ->
  Xsimpl (Hla, \[], \[]) ((hforall J) \* \[], \[], \[]).
Proof using.
  xsimpl_lr_start M. applys himpl_hforall_r. intros x.
  specializes M x. rew_heap~ in M.
Qed.

Lemma himpl_lr_refl : forall Hla,
  Xsimpl (Hla, \[], \[]) (Hla, \[], \[]).
Proof using. intros. unfolds Xsimpl. hstars_simpl. Qed.

Lemma himpl_lr_qwand_unify : forall A (Q:A->hprop) Hla,
  Xsimpl (Hla, \[], \[]) ((Q \--* (Q \*+ Hla)) \* \[], \[], \[]).
Proof using. intros. unfolds Xsimpl. hstars_simpl. rewrite~ qwand_equiv. Qed.

Lemma himpl_lr_htop : forall Hla Hrg,
  Xsimpl (\[], \[], \[]) (\[], Hrg, \[]) ->
  Xsimpl (Hla, \[], \[]) (\[], (\Top \* Hrg), \[]).
Proof using.
  xsimpl_lr_start M. rewrite <- (hstar_hempty_l Hla).
  applys himpl_hstar_trans_l M. hstars_simpl. apply himpl_htop_r.
Qed.

Lemma himpl_lr_hgc : forall Hla Hrg,
  haffine Hla ->
  Xsimpl (\[], \[], \[]) (\[], Hrg, \[]) ->
  Xsimpl (Hla, \[], \[]) (\[], (\GC \* Hrg), \[]).
Proof using.
  introv N. xsimpl_lr_start M. rewrite <- (hstar_hempty_l Hla).
  applys himpl_hstar_trans_l M. hstars_simpl. apply* himpl_hgc_r.
Qed.

Lemma xsimpl_lr_exit_nogc : forall Hla Hra,
  Hla ==> Hra ->
  Xsimpl (Hla, \[], \[]) (Hra, \[], \[]).
Proof using. introv M. unfolds Xsimpl. hstars_simpl. auto. Qed.

Lemma xsimpl_lr_exit : forall Hla Hra Hrg,
  Hla ==> Hra \* Hrg ->
  Xsimpl (Hla, \[], \[]) (Hra, Hrg, \[]).
Proof using. introv M. unfolds Xsimpl. hstars_simpl. rewrite~ hstar_comm. Qed.

(** Lemmas to flip accumulators back in place *)

Lemma xsimpl_flip_acc_l : forall Hla Hra Hla' Hrg,
  Hla = Hla' ->
  Xsimpl (Hla', \[], \[]) (Hra, Hrg, \[]) ->
  Xsimpl (Hla, \[], \[]) (Hra, Hrg, \[]).
Proof using. introv E1 M. subst*. Qed.

Lemma xsimpl_flip_acc_r : forall Hla Hra Hra' Hrg,
  Hra = Hra' ->
  Xsimpl (Hla, \[], \[]) (Hra', Hrg, \[]) ->
  Xsimpl (Hla, \[], \[]) (Hra, Hrg, \[]).
Proof using. introv E1 M. subst*. Qed.

Ltac xsimpl_flip_acc_l tt :=
  eapply xsimpl_flip_acc_l; [ hstars_flip tt | ].

Ltac xsimpl_flip_acc_r tt :=
  eapply xsimpl_flip_acc_r; [ hstars_flip tt | ].

Ltac xsimpl_flip_acc_lr tt :=
  xsimpl_flip_acc_l tt; xsimpl_flip_acc_r tt.

(* ----------------------------------------------------------------- *)
(** *** Lemmas to pick the hypothesis to cancel *)

(** [xsimpl_pick i] applies to a goal of the form
    [Xsimpl ((H1 \* .. \* Hi \* .. \* Hn), Hlw, Hlt) HR] and turns it into
    [Xsimpl ((Hi \* H1 .. \* H{i-1} \* H{i+1} \* .. \* Hn), Hlw, Hlt) HR]. *)

Lemma xsimpl_pick_lemma : forall Hla1 Hla2 Hlw Hlt HR,
  Hla1 = Hla2 ->
  Xsimpl (Hla2, Hlw, Hlt) HR ->
  Xsimpl (Hla1, Hlw, Hlt) HR.
Proof using. introv M. subst~. Qed.

Ltac xsimpl_pick i :=
  let L := hstars_pick_lemma i in
  eapply xsimpl_pick_lemma; [ apply L | ].

(** [xsimpl_pick_st f] applies to a goal of the form
    [Xsimpl ((H1 \* .. \* Hi \* .. \* Hn), Hlw, Hlt) HR] and turns it into
    [Xsimpl ((Hi \* H1 .. \* H{i-1} \* H{i+1} \* .. \* Hn), Hlw, Hlt) HR]
    for the first [i] such that [f Hi] returns [true]. *)

Ltac xsimpl_pick_st f :=
  match goal with |- Xsimpl (?Hla, ?Hlw, ?Hlt) ?HR =>
    hstars_search Hla ltac:(fun i H =>
      match f H with true => xsimpl_pick i end)
  end.

(** [xsimpl_pick_syntactically H] is a variant of the above that only
    checks for syntactic equality, not unifiability. *)

Ltac xsimpl_pick_syntactically H :=
  xsimpl_pick_st ltac:(fun H' =>
    match H' with H => constr:(true) end).

(** [xsimpl_pick_unifiable H] applies to a goal of the form
    [Xsimpl (Hla, Hlw, Hlt) HR], where [Hla] is of the form
    [H1 \* .. \* Hn \* \[]]. It searches for [H] among the [Hi].
    If it finds it, it moves this [Hi] to the front, just before [H1].
    Else, it fails. *)

Ltac xsimpl_pick_unifiable H :=
  match goal with |- Xsimpl (?Hla, ?Hlw, ?Hlt) ?HR =>
    hstars_search Hla ltac:(fun i H' =>
      unify H H'; xsimpl_pick i)
  end.

(** [xsimpl_pick_same H] is a choice for one of the above two,
    it is the default version used by [xsimpl].
    Syntactic matching is faster but less expressive. *)

Ltac xsimpl_pick_same H :=
  xsimpl_pick_unifiable H.

(** [xsimpl_pick_applied Q] applies to a goal of the form
    [Xsimpl (Hla, Hlw, Hlt) HR], where [Hla] is of the form
    [H1 \* .. \* Hn \* \[]]. It searches for [Q ?x] among the [Hi].
    If it finds it, it moves this [Hi] to the front, just before [H1].
    Else, it fails. *)

Ltac xsimpl_pick_applied Q :=
  xsimpl_pick_st ltac:(fun H' =>
    match H' with Q _ => constr:(true) end).

(** [repr_get_predicate H] applies to a [H] of the form [p ~> R _ ... _]
    and it returns [R]. *)

Ltac repr_get_predicate H :=
  match H with ?p ~> ?E => get_head E end.

(** [xsimpl_pick_repr H] applies to a goal of the form
    [Xsimpl (Hla, Hlw, Hlt) HR], where [Hla] is of the form
    [H1 \* .. \* Hn \* \[]], and where [H] is of the form [p ~> R _]
    (same as [repr _ p]). It searches for [p ~> R _] among the [Hi].
    If it finds it, it moves this [Hi] to the front, just before [H1].
    Else, it fails. *)

Ltac xsimpl_pick_repr H :=
  match H with ?p ~> ?E =>
    let R := get_head E in
    xsimpl_pick_st ltac:(fun H' =>
      match H' with (p ~> ?E') =>
        let R' := get_head E' in
        match R' with R => constr:(true) end end)
  end.

(* ----------------------------------------------------------------- *)
(** *** Tactic start and stop *)

Opaque Xsimpl.

Ltac xsimpl_handle_qimpl tt :=
  match goal with
  | |- @qimpl _ _ ?Q2 => is_evar Q2; apply qimpl_refl
  | |- @qimpl unit ?Q1 ?Q2 => let t := fresh "_tt" in intros t; destruct t
  | |- @qimpl _ _ _ => let r := fresh "r" in intros r
  | |- himpl _ ?H2 => is_evar H2; apply himpl_refl
  | |- himpl _ _ => idtac
  | |- @eq hprop _ _ => applys himpl_antisym
  | |- @eq (_ -> hprop) _ _ => applys fun_ext_1; applys himpl_antisym
  | _ => fail 1 "not a goal for xsimpl/xpull"
  end.

Ltac xsimpl_intro tt :=
  applys xsimpl_start.

Ltac xpull_start tt :=
  pose ltac_mark;
  intros;
  xsimpl_handle_qimpl tt;
  applys xpull_protect;
  xsimpl_intro tt.

Ltac xsimpl_start tt :=
  pose ltac_mark;
  intros;
  xsimpl_handle_qimpl tt;
  xsimpl_intro tt.

Ltac xsimpl_post_before_generalize tt :=
  idtac.

Ltac xsimpl_post_after_generalize tt :=
  idtac.

Ltac himpl_post_processing_for_hyp H :=
  idtac.

Ltac xsimpl_handle_false_subgoals tt :=
  tryfalse.

Ltac xsimpl_clean tt :=
  try remove_empty_heaps_right tt;
  try remove_empty_heaps_left tt;
  try xsimpl_hint_remove tt.

Ltac gen_until_mark_with_processing_and_cleaning cont :=
  match goal with H: ?T |- _ =>
  match T with
  | ltac_Mark => clear H
  | _ => cont H;
         let T := type of H in
         generalize H; clear H;
         (* discard non-dependent hyps that are not of type Prop *)
         try (match goal with |- _ -> _ =>
              match type of T with
              | Prop => idtac
              | _ => intros _
              end end);
         gen_until_mark_with_processing cont
  end end.

Ltac xsimpl_generalize tt :=
  xsimpl_post_before_generalize tt;
  xsimpl_handle_false_subgoals tt;
  gen_until_mark_with_processing_and_cleaning
    ltac:(himpl_post_processing_for_hyp);
  xsimpl_post_after_generalize tt.

Ltac xsimpl_post tt :=
  xsimpl_clean tt;
  xsimpl_generalize tt.

Ltac xpull_post tt :=
  xsimpl_clean tt;
  unfold protect;
  xsimpl_generalize tt.

(* ----------------------------------------------------------------- *)
(** *** Auxiliary functions step *)

(** [xsimpl_lr_cancel_eq_repr_post tt] is meant to simplify goals of the form [E1 = E2]
   that arises from cancelling [p ~> E1] with [p ~> E2] in the case where [E1] and [E2]
   share the same head symbol, that is, the same representation predicate [R]. *)

Ltac xsimpl_lr_cancel_eq_repr_post tt :=
  try fequal; try reflexivity.
  (* Later refined for records *)

(** [xsimpl_r_hexists_apply tt] is a tactic to apply [xsimpl_r_hexists]
    by exploiting a hint if one is available (see the hint section above)
    to specify the instantiation of the existential. *)

(* Note: need to use [nrapply] instead of [eapply] to correctly handle [\exists (EA:Enc ?A)] *)
Ltac xsimpl_r_hexists_apply tt :=
  first [
    xsimpl_hint_next ltac:(fun x =>
      match x with
      | __ => nrapply xsimpl_r_hexists
      | _ => apply (@xsimpl_r_hexists _ x)
      end)
  | nrapply xsimpl_r_hexists ].

(** [xsimpl_hook H] can be customize to handle cancellation of specific
    kind of heap predicates (e.g., [hsingle]). *)

Ltac xsimpl_hook H := fail.

(* ----------------------------------------------------------------- *)
(** *** Tactic step *)

Ltac xsimpl_hwand_hstars_l tt :=
  match goal with |- Xsimpl (?Hla, ((?H1s \-* ?H2) \* ?Hlw), \[]) ?HR =>
    hstars_search H1s ltac:(fun i H =>
      let L := hstars_pick_lemma i in
      eapply xsimpl_l_hwand_reorder;
      [ apply L
      | match H with
        | \[] => apply xsimpl_l_cancel_hwand_hstar_hempty
        | _ => xsimpl_pick_same H; apply xsimpl_l_cancel_hwand_hstar
        end
      ])
  end.

Ltac xsimpl_step_l cancel_wands :=
  (* next line is for backward compatibility for calls to [xsimpl_step_l tt]. *)
  let cancel_wands := match cancel_wands with tt => constr:(true) | ?x => x end in
  match goal with |- Xsimpl ?HL ?HR =>
  match HL with
  | (?Hla, ?Hlw, (?H \* ?Hlt)) =>
    match H with
    | \[] => eapply xsimpl_l_hempty
    | \[?P] => eapply xsimpl_l_hpure; intro
    | ?H1 \* ?H2 => rewrite (@hstar_assoc H1 H2)
    | hexists ?J => eapply xsimpl_l_hexists; intro
    | ?H1 \-* ?H2 => eapply xsimpl_l_acc_wand
    | ?Q1 \--* ?Q2 => eapply xsimpl_l_acc_wand
    | _ => eapply xsimpl_l_acc_other
    end
  | (?Hla, ((?H1 \-* ?H2) \* ?Hlw), \[]) =>
      match H1 with
      | \[] => apply xsimpl_l_cancel_hwand_hempty
      | (_ \* _) => xsimpl_hwand_hstars_l tt
      | _ =>
        match cancel_wands with
        | true => xsimpl_pick_same H1; eapply xsimpl_l_cancel_hwand (* else continue *)
        | _ => eapply xsimpl_l_keep_wand
        end
      end
  | (?Hla, ((?Q1 \--* ?Q2) \* ?Hlw), \[]) =>
        match cancel_wands with
        | true => xsimpl_pick_applied Q1; eapply xsimpl_l_cancel_qwand (* else continue *)
        | _ => eapply xsimpl_l_keep_wand
        end
  end end.

Ltac xsimpl_hgc_or_htop_cancel cancel_item cancel_lemma :=
  (* Applies to goal of the form:
     [match goal with |- Xsimpl (?Hla, \[], \[]) (?Hra, (?H \* ?Hrg), ?Hrt) =>] *)
  repeat (xsimpl_pick_same cancel_item; apply cancel_lemma).

Ltac xsimpl_hgc_or_htop_step tt :=
  match goal with |- Xsimpl (?Hla, \[], \[]) (?Hra, ?Hrg, (?H \* ?Hrt)) =>
    match constr:((Hrg,H)) with
    | (\[], \GC) => applys xsimpl_r_hgc_or_htop;
                    xsimpl_hgc_or_htop_cancel (\GC) xsimpl_lr_cancel_hgc
    | (\[], \Top) => applys xsimpl_r_hgc_or_htop;
                    xsimpl_hgc_or_htop_cancel (\GC) xsimpl_lr_cancel_htop;
                    xsimpl_hgc_or_htop_cancel (\Top) xsimpl_lr_cancel_htop
    | (\GC \* \[], \Top) => applys xsimpl_r_htop_replace_hgc;
                            xsimpl_hgc_or_htop_cancel (\Top) xsimpl_lr_cancel_htop
    | (\GC \* \[], \GC) => applys xsimpl_r_hgc_drop
    | (\Top \* \[], \GC) => applys xsimpl_r_hgc_drop
    | (\Top \* \[], \Top) => applys xsimpl_r_htop_drop
    end end.

Ltac xsimpl_cancel_same H :=
  xsimpl_pick_same H; apply xsimpl_lr_cancel_same.

Ltac xsimpl_step_r tt :=
  match goal with |- Xsimpl (?Hla, \[], \[]) (?Hra, ?Hrg, (?H \* ?Hrt)) =>
  match H with
  | ?H' => xsimpl_hook H (* else continue *)
  | \[] => apply xsimpl_r_hempty
  | \[?P] => apply xsimpl_r_hpure
  | ?H1 \* ?H2 => rewrite (@hstar_assoc H1 H2)
  | ?H \-* ?H'eqH =>
      match H with
      | \[?P] => fail 1 (* don't cancel out cause [P] might contain a contradiction *)
      | _ =>
        match H'eqH with
        | H => eapply xsimpl_r_hwand_same
     (* | protect H => we purposely refuse to unify if proetcted*)
        end
      end
  | hexists ?J => xsimpl_r_hexists_apply tt
  | \GC => xsimpl_hgc_or_htop_step tt
  | \Top => xsimpl_hgc_or_htop_step tt
  | protect ?H' => eapply xsimpl_r_keep
  | protect ?Q' _ => eapply xsimpl_r_keep
  | ?H' => is_not_evar H;  xsimpl_cancel_same H (* else continue *)
  | ?p ~> _ => xsimpl_pick_repr H; eapply xsimpl_lr_cancel_eq_repr;
               [ xsimpl_lr_cancel_eq_repr_post tt | ]  (* else continue *)
  | ?x ~> Id ?X => has_no_evar x; eapply xsimpl_r_id
    | ?x ~> ?T_evar ?X_evar => has_no_evar x; is_evar T_evar; is_evar X_evar;
                           eapply xsimpl_r_id_unify
  | _ => eapply xsimpl_r_keep
  end end.

Ltac xsimpl_step_lr tt :=
  match goal with |- Xsimpl (?Hla, \[], \[]) (?Hra, ?Hrg, \[]) =>
    match Hrg with
    | \[] =>
       match Hra with
       | ?H1 \* \[] =>
         match H1 with
         | ?Hra_evar => is_evar Hra_evar; rew_heap; eapply himpl_lr_refl (* else continue *)
         | ?Q1 \--* ?Q2 => is_evar Q2; eapply himpl_lr_qwand_unify
         | \[False] \-* ?H2 => apply xsimpl_lr_hwand_hfalse
         | ?H1 \-* ?H2 => xsimpl_flip_acc_l tt; apply xsimpl_lr_hwand
         | ?Q1 \--* ?Q2 =>
             xsimpl_flip_acc_l tt;
             match H1 with
             | @qwand unit ?Q1' ?Q2' => eapply xsimpl_lr_qwand_unit
             | _ => eapply xsimpl_lr_qwand; intro
             end
         | hforall _ => xsimpl_flip_acc_l tt; apply xsimpl_lr_hforall; intro
                                 end
       | \[] => eapply himpl_lr_refl
       | _ => xsimpl_flip_acc_lr tt; eapply xsimpl_lr_exit_nogc
       end
    | (\Top \* _) => eapply himpl_lr_htop
    | (\GC \* _) => eapply himpl_lr_hgc;
                    [ try remove_empty_heaps_haffine tt; xaffine | ]
    | ?Hrg' => xsimpl_flip_acc_lr tt; eapply xsimpl_lr_exit
  end end.

Ltac xsimpl_step cancel_wands :=
  first [ xsimpl_step_l cancel_wands
        | xsimpl_step_r tt
        | xsimpl_step_lr tt ].

(* ----------------------------------------------------------------- *)
(** *** Tactic Notation *)

Ltac xpull_core tt :=
  xpull_start tt;
  repeat (xsimpl_step tt);
  xpull_post tt.

Tactic Notation "xpull" := xpull_core tt.
Tactic Notation "xpull" "~" := xpull; auto_tilde.
Tactic Notation "xpull" "*" := xpull; auto_star.

Ltac xsimpl_core_mode cancel_wands :=
  xsimpl_start tt;
  repeat (xsimpl_step cancel_wands);
  xsimpl_post tt.

Ltac xsimpl_core tt := (* cancel wands *)
  xsimpl_core_mode constr:(true).

Ltac xsimpl_no_cancel_wand tt := (* don't cancel wands *)
  xsimpl_core_mode constr:(false).

Tactic Notation "xsimpl" := xsimpl_core tt.
Tactic Notation "xsimpl" "~" := xsimpl; auto_tilde.
Tactic Notation "xsimpl" "*" := xsimpl; auto_star.

Tactic Notation "xsimpl" constr(L) :=
  match type of L with
  | list Boxer => xsimpl_hint_put L
  | _ => xsimpl_hint_put (boxer L :: nil)
  end; xsimpl.
Tactic Notation "xsimpl" constr(X1) constr(X2) :=
  xsimpl (>> X1 X2).
Tactic Notation "xsimpl" constr(X1) constr(X2) constr(X3) :=
  xsimpl (>> X1 X2 X3).
  Tactic Notation "xsimpl" constr(X1) constr(X2) constr(X3) constr(X4):=
  xsimpl (>> X1 X2 X3 X4).
Tactic Notation "xsimpl" constr(X1) constr(X2) constr(X3) constr(X4) constr(X5) :=
  xsimpl (>> X1 X2 X3 X4 X5).
Tactic Notation "xsimpl" constr(X1) constr(X2) constr(X3) constr(X4) constr(X5) constr(X6) :=
  xsimpl (>> X1 X2 X3 X4 X5 X6).

Tactic Notation "xsimpl" "~" constr(L) :=
  xsimpl L; auto_tilde.
Tactic Notation "xsimpl" "~" constr(X1) constr(X2) :=
  xsimpl X1 X2; auto_tilde.
Tactic Notation "xsimpl" "~" constr(X1) constr(X2) constr(X3) :=
  xsimpl X1 X2 X3; auto_tilde.
Tactic Notation "xsimpl" "~" constr(X1) constr(X2) constr(X3) constr(X4):=
  xsimpl X1 X2 X3 X4; auto_tilde.
Tactic Notation "xsimpl" "~" constr(X1) constr(X2) constr(X3) constr(X4) constr(X5) :=
  xsimpl X1 X2 X3 X4 X5; auto_tilde.
Tactic Notation "xsimpl" "~" constr(X1) constr(X2) constr(X3) constr(X4) constr(X5) constr(X6) :=
  xsimpl X1 X2 X3 X4 X5 X6; auto_tilde.

Tactic Notation "xsimpl" "*" constr(L) :=
  xsimpl L; auto_star.
Tactic Notation "xsimpl" "*" constr(X1) constr(X2) :=
  xsimpl X1 X2; auto_star.
Tactic Notation "xsimpl" "*" constr(X1) constr(X2) constr(X3) :=
  xsimpl X1 X2 X3; auto_star.
Tactic Notation "xsimpl" "*" constr(X1) constr(X2) constr(X3) constr(X4):=
  xsimpl X1 X2 X3 X4; auto_star.
Tactic Notation "xsimpl" "*" constr(X1) constr(X2) constr(X3) constr(X4) constr(X5) :=
  xsimpl X1 X2 X3 X4 X5; auto_star.
Tactic Notation "xsimpl" "*" constr(X1) constr(X2) constr(X3) constr(X4) constr(X5) constr(X6) :=
  xsimpl X1 X2 X3 X4 X5 X6; auto_star.

(* ----------------------------------------------------------------- *)
(** *** Tactic [xchange] *)

(** [xchange] performs rewriting on the LHS of an entailment.
  Essentially, it applies to a goal of the form [H1 \* H2 ==> H3],
  and exploits an entailment [H1 ==> H1'] to replace the goal with
  [H1' \* H2 ==> H3].

  The tactic is actually a bit more flexible in two respects:
  - it does not force the LHS to be exactly of the form [H1 \* H2]
  - it takes as argument any lemma, whose instantiation result in
    a heap entailment of the form [H1 ==> H1'].

  Concretely, the tactic is just a wrapper around an application
  of the lemma called [xchange_lemma], which appears below.

  [xchanges] combines a call to [xchange] with calls to [xsimpl]
  on the subgoals. *)

Lemma xchange_lemma : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H3 ==> H1 \* (H2 \-* protect H4) ->
  H3 ==> H4.
Proof using.
  introv M1 M2. applys himpl_trans (rm M2).
  applys himpl_hstar_trans_l (rm M1). applys hwand_cancel.
Qed.

Ltac xchange_apply L :=
  eapply xchange_lemma; [ eapply L | ].

(* Below, the modifier is either [__] or [himpl_of_eq]
   or [himpl_of_eq_sym] *)

Ltac xchange_build_entailment modifier K :=
  match modifier with
  | __ =>
     match type of K with
     | _ = _ => constr:(@himpl_of_eq _ _ K)
     | _ => constr:(K)
     end
  | _ => constr:(@modifier _ _ K)
  end.

Ltac xchange_perform L modifier cont :=
  forwards_nounfold_then L ltac:(fun K =>
    let X := fresh "TEMP" in
    set (X := K); (* intermediate [set] seems necessary *)
    let M := xchange_build_entailment modifier K in
    clear X;
    xchange_apply M;
    cont tt).

Ltac xchange_core L modifier cont :=
  pose ltac_mark;
  intros;
  match goal with
  | |- _ ==> _ => idtac
  | |- _ ===> _ => let x := fresh "r" in intros x
  end;
  xchange_perform L modifier cont;
  gen_until_mark.

(** Error reporting support for [xchange] (not for [xchanges]) *)

Definition xchange_hidden (P:Type) (e:P) := e.

Notation "'__XCHANGE_FAILED_TO_MATCH_PRECONDITION__'" :=
  (@xchange_hidden _ _).

Ltac xchange_report_error tt :=
  match goal with |- context [?H1 \-* protect ?H2] =>
    change (H1 \-* protect H2) with (@xchange_hidden _ (H1 \-* protect H2)) end.

Ltac xchange_xpull_cont tt :=
  xsimpl; first
  [ xchange_report_error tt
  | unfold protect; try solve [ apply himpl_refl ] ].

Ltac xchange_xpull_cont_basic tt := (* version without error reporting *)
  xsimpl; unfold protect; try solve [ apply himpl_refl ].

Ltac xchange_xsimpl_cont tt :=
  unfold protect; xsimpl; try solve [ apply himpl_refl ].

Ltac xchange_nosimpl_base E modifier :=
  xchange_core E modifier ltac:(idcont).

Tactic Notation "xchange_nosimpl" constr(E) :=
  xchange_nosimpl_base E __.
Tactic Notation "xchange_nosimpl" "->" constr(E) :=
  xchange_nosimpl_base E himpl_of_eq.
Tactic Notation "xchange_nosimpl" "<-" constr(E) :=
  xchange_nosimpl_base himpl_of_eq_sym.

Ltac xchange_base E modif :=
  xchange_core E modif ltac:(xchange_xpull_cont).

Tactic Notation "xchange" constr(E) :=
  xchange_base E __.
Tactic Notation "xchange" "~" constr(E) :=
  xchange E; auto_tilde.
Tactic Notation "xchange" "*" constr(E) :=
  xchange E; auto_star.

Tactic Notation "xchange" "->" constr(E) :=
  xchange_base E himpl_of_eq.
Tactic Notation "xchange"  "~" "->" constr(E) :=
  xchange -> E; auto_tilde.
Tactic Notation "xchange" "*" "->" constr(E) :=
  xchange -> E; auto_star.

Tactic Notation "xchange" "<-" constr(E) :=
  xchange_base E himpl_of_eq_sym.
Tactic Notation "xchange" "~" "<-" constr(E) :=
  xchange <- E; auto_tilde.
Tactic Notation "xchange" "*" "<-" constr(E) :=
  xchange <- E; auto_star.

Ltac xchanges_base E modif :=
  xchange_core E modif ltac:(xchange_xsimpl_cont).

Tactic Notation "xchanges" constr(E) :=
  xchanges_base E __.
Tactic Notation "xchanges" "~" constr(E) :=
  xchanges E; auto_tilde.
Tactic Notation "xchanges" "*" constr(E) :=
  xchanges E; auto_star.

Tactic Notation "xchanges" "->" constr(E) :=
  xchanges_base E himpl_of_eq.
Tactic Notation "xchanges"  "~" "->" constr(E) :=
  xchanges -> E; auto_tilde.
Tactic Notation "xchanges" "*" "->" constr(E) :=
  xchanges -> E; auto_star.

Tactic Notation "xchanges" "<-" constr(E) :=
  xchanges_base E himpl_of_eq_sym.
Tactic Notation "xchanges" "~" "<-" constr(E) :=
  xchanges <- E; auto_tilde.
Tactic Notation "xchanges" "*" "<-" constr(E) :=
  xchanges <- E; auto_star.

Tactic Notation "xchange" constr(E1) "," constr(E2) :=
  xchange E1; try xchange E2.
Tactic Notation "xchange" constr(E1) "," constr(E2) "," constr(E3) :=
  xchange E1; try xchange E2; try xchange E3.
Tactic Notation "xchange" constr(E1) "," constr(E2) "," constr(E3) "," constr(E4) :=
  xchange E1; try xchange E2; try xchange E3; try xchange E4.


(* ################################################################# *)
(** * Demos *)

(* ----------------------------------------------------------------- *)
(** *** [rew_heap] demos *)

Lemma rew_heap_demo_with_evar : forall H1 H2 H3,
  (forall H, H1 \* (H \* H2) \* \[] = H3 -> True) -> True.
Proof using.
  introv M. dup 3.
  { eapply M. rewrite hstar_assoc. rewrite hstar_assoc. demo. }
  { eapply M. rew_heap_assoc. demo. }
  { eapply M. rew_heap. demo. }
Abort.

(* ----------------------------------------------------------------- *)
(** *** [hstars] demos *)

Lemma hstars_flip_demo : forall H1 H2 H3 H4,
  (forall H, H1 \* H2 \* H3 \* H4 \* \[] = H -> H = H -> True) -> True.
Proof using.
  introv M. eapply M. hstars_flip tt.
Abort.

Lemma hstars_flip_demo_0 :
  (forall H, \[] = H -> H = H -> True) -> True.
Proof using.
  introv M. eapply M. hstars_flip tt.
Abort.

(* ----------------------------------------------------------------- *)
(** *** [xsimpl_hint] demos *)

Lemma xsimpl_demo_hints : exists n, n = 3.
Proof using.
  xsimpl_hint_put (>> 3 true).
  xsimpl_hint_next ltac:(fun x => exists x).
  xsimpl_hint_remove tt.
Abort.

(* ----------------------------------------------------------------- *)
(** *** [hstars_pick] demos *)

Lemma demo_hstars_pick_1 : forall H1 H2 H3 H4 Hresult,
  (forall H, H1 \* H2 \* H3 \* H4 = H -> H = Hresult -> True) -> True.
Proof using.
  introv M. dup 2.
  { eapply M. let L := hstars_pick_lemma 3 in eapply L. demo. }
  { eapply M. let L := hstars_pick_lemma (hstars_last 4) in eapply L. demo. }
Qed.

(* ----------------------------------------------------------------- *)
(** *** [hstars_simpl] demos *)

Lemma demo_hstars_simpl_1 : forall H1 H2 H3 H4 H5,
  H2 ==> H5 ->
  H1 \* H2 \* H3 \* H4 ==> H4 \* H5 \* H3 \* H1.
Proof using.
  intros. dup.
  { hstars_simpl_start tt.
    hstars_simpl_step tt.
    hstars_simpl_step tt.
    hstars_simpl_step tt.
    hstars_simpl_step tt.
    hstars_simpl_post tt. auto. }
  { hstars_simpl. auto. }
Qed.

Lemma demo_hstars_simpl_2 : forall H1 H2 H3 H4 H5,
  (forall H, H \* H2 \* H3 \* H4 ==> H4 \* H5 \* H3 \* H1 -> True) -> True.
Proof using.
  introv M. eapply M. hstars_simpl.
Abort.

(* ----------------------------------------------------------------- *)
(** *** [xsimpl_pick] demos *)

Lemma xsimpl_pick_demo : forall (Q:bool->hprop) (P:Prop) H1 H2 H3 Hlw Hlt Hra Hrg Hrt,
  (forall HX HY,
    Xsimpl ((H1 \* H2 \* H3 \* Q true \* (\[P] \-* HX) \* HY \* \[]), Hlw, Hlt)
           (Hra, Hrg, Hrt)
  -> True) -> True.
Proof using.
  introv M. applys (rm M).
  let L := hstars_pick_lemma 2%nat in set (X:=L).
  eapply xsimpl_pick_lemma. apply X.
  xsimpl_pick 2%nat.
  xsimpl_pick_same H3.
  xsimpl_pick_applied Q.
  xsimpl_pick_same H2.
  xsimpl_pick_unifiable H3.
  xsimpl_pick_unifiable \[True].
  xsimpl_pick_unifiable (\[P] \-* H1).
Abort.

(* ----------------------------------------------------------------- *)
(** *** [xpull] and [xsimpl] demos *)

Tactic Notation "xpull0" := xpull_start tt.
Tactic Notation "xsimpl0" := xsimpl_start tt.
Tactic Notation "xsimpl1" := xsimpl_step tt.
Tactic Notation "xsimpl2" := xsimpl_post tt.
Tactic Notation "xsimpll" := xsimpl_step_l tt.
Tactic Notation "xsimplr" := xsimpl_step_r tt.
Tactic Notation "xsimpllr" := xsimpl_step_lr tt.

Declare Scope xsimpl_scope.

Notation "'HSIMPL' Hla Hlw Hlt =====> Hra Hrg Hrt" := (Xsimpl (Hla, Hlw, Hlt) (Hra, Hrg, Hrt))
  (at level 69, Hla, Hlw, Hlt, Hra, Hrg, Hrt at level 0,
   format "'[v' 'HSIMPL' '/' Hla  '/' Hlw  '/' Hlt  '/' =====> '/' Hra  '/' Hrg  '/' Hrt ']'")
  : xsimpl_scope.

Local Open Scope xsimpl_scope.

Lemma xpull_demo : forall H1 H2 H3 H,
  (H1 \* \[] \* (H2 \* \exists (y:int) z (n:nat), \[y = y + z + n]) \* H3) ==> H.
Proof using.
  dup.
  { intros. xpull0. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl2. demo. }
  { xpull. intros. demo. }
Abort.

Lemma xsimpl_demo_stars : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* H3 \* H4 ==> H4 \* H3 \* H5 \* H2.
Proof using.
  dup 3.
  { xpull. demo. }
  { intros. xsimpl0. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl1. demo. }
  { intros. xsimpl. demo. }
Abort.

Lemma xsimpl_demo_keep_order : forall H1 H2 H3 H4 H5 H6 H7,
  H1 \* H2 \* H3 \* H4 ==> H5 \* H3 \* H6 \* H7.
Proof using. intros. xsimpl. demo. Abort.

Lemma xsimpl_demo_stars_top : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* H3 \* H4 \* H5 ==> H3 \* H1 \* H2 \* \Top.
Proof using.
  dup.
  { intros. xsimpl0. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. }
  { intros. xsimpl. }
Abort.

Lemma xsimpl_demo_hint : forall H1 (Q:int->hprop),
  Q 4 ==> Q 3 ->
  H1 \* Q 4 ==> \exists x, Q x \* H1.
Proof using.
  introv W. dup.
  { intros. xsimpl_hint_put (>> 3).
    xsimpl0. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl2. auto. }
  { xsimpl 3. auto. }
Qed.

Lemma xsimpl_demo_stars_gc : forall H1 H2,
  haffine H2 ->
  H1 \* H2 ==> H1 \* \GC.
Proof using.
  dup.
  { intros. xsimpl0. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. }
  { intros. xsimpl~. }
Abort.

Lemma xsimpl_demo_evar_1 : forall H1 H2,
  (forall H, H1 \* H2 ==> H -> True) -> True.
Proof using. intros. eapply H. xsimpl. Abort.

Lemma xsimpl_demo_evar_2 : forall H1,
  (forall H, H1 ==> H1 \* H -> True) -> True.
Proof using.
  introv M. dup.
  { eapply M. xsimpl0. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. }
  { eapply M. xsimpl~. }
Abort.

Lemma xsimpl_demo_htop_both_sides : forall H1 H2,
  H1 \* H2 \* \Top ==> H1 \* \Top.
Proof using.
  dup.
  { intros. xsimpl0. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. }
  { intros. xsimpl~. }
Abort.

Lemma xsimpl_demo_htop_multiple : forall H1 H2,
  H1 \* H2 \* \Top ==> H1 \* \Top \* \Top.
Proof using. intros. xsimpl~. Abort.

Lemma xsimpl_demo_hgc_multiple : forall H1 H2,
  haffine H2 ->
  H1 \* H2 \* \GC ==> H1 \* \GC \* \GC.
Proof using. intros. xsimpl~. Qed.

Lemma xsimpl_demo_hwand : forall H1 H2 H3 H4,
  (H1 \-* (H2 \-* H3)) \* H1 \* H4 ==> (H2 \-* (H3 \* H4)).
Proof using.
  dup.
  { intros. xsimpl0. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. }
  { intros. xsimpl~. }
Qed.

Lemma xsimpl_demo_qwand : forall A (x:A) (Q1 Q2:A->hprop) H1,
  H1 \* (H1 \-* (Q1 \--* Q2)) \* (Q1 x) ==> (Q2 x).
Proof using. intros. xsimpl~. Qed.

Lemma xsimpl_demo_hwand_r : forall H1 H2 H3,
  H1 \* H2 ==> H1 \* (H3 \-* (H2 \* H3)).
Proof using. intros. xsimpl~. Qed.

Lemma xsimpl_demo_qwand_r : forall A (x:A) (Q1 Q2:A->hprop) H1 H2,
  H1 \* H2 ==> H1 \* (Q1 \--* (Q1 \*+ H2)).
Proof using. intros. xsimpl. Qed.

Lemma xsimpl_demo_hwand_multiple_1 : forall H1 H2 H3 H4 H5,
  H1 \-* H4 ==> H5 ->
  (H2 \* ((H1 \* H2 \* H3) \-* H4)) \* H3 ==> H5.
Proof using. introv M. xsimpl. auto. Qed.

Lemma xsimpl_demo_hwand_multiple_2 : forall H1 H2 H3 H4 H5,
  (H1 \* H2 \* ((H1 \* H3) \-* (H4 \-* H5))) \* (H2 \-* H3) \* H4 ==> H5.
Proof using. intros. xsimpl. Qed.

Lemma xsimpl_demo_hwand_hempty : forall H1 H2 H3,
  (\[] \-* H1) \* H2 ==> H3.
Proof using. intros. xsimpl. Abort.

Lemma xsimpl_demo_hwand_hstar_hempty : forall H0 H1 H2 H3,
  ((H0 \* \[]) \-* \[] \-* H1) \* H2 ==> H3.
Proof using. intros. xsimpl. rew_heap. Abort.
(* [xsimpl] does not simplify inner [\[] \-* H1], known limitation. *)

Lemma xsimpl_demo_hwand_iter : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* ((H1 \* H3) \-* (H4 \-* H5)) \* H4 ==> ((H2 \-* H3) \-* H5).
Proof using.
  intros. dup.
  { xsimpl0. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. }
  { xsimpl. }
Qed.

Lemma xsimpl_demo_repr_1 : forall p q (R:int->int->hprop),
  p ~> R 3 \* q ~> R 4 ==> \exists n m, p ~> R n \* q ~> R m.
Proof using.
  intros. dup.
  { xsimpl0. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. }
  { xsimpl~. }
Qed.

Lemma xsimpl_demo_repr_2 : forall p (R R':int->int->hprop),
  R = R' ->
  p ~> R' 3 ==> \exists n, p ~> R n.
Proof using. introv E. xsimpl. subst R'. xsimpl. Qed.

Lemma xsimpl_demo_repr_3 : forall p (R:int->int->hprop),
  let R' := R in
  p ~> R' 3 ==> \exists n, p ~> R n.
Proof using.
  intros. dup.
  { xsimpl0. xsimpl1. xsimpl1. xsimpl1. xsimpl1. }
  { xsimpl~. }
Qed.

Lemma xsimpl_demo_repr_4 : forall p n m (R:int->int->hprop),
  n = m + 0 ->
  p ~> R n ==> p ~> R m.
Proof using. intros. xsimpl. math. Qed.

Lemma xsimpl_demo_gc_0 : forall H1 H2,
  H1 ==> H2 \* \GC \* \GC.
Proof using. intros. xsimpl. Abort.

Lemma xsimpl_demo_gc_1 : forall H1 H2,
  H1 ==> H2 \* \GC \* \Top \* \Top \* \GC.
Proof using.
  intros. dup.
  { xsimpl0. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl2. demo. }
  { xsimpl~. demo. }
Abort.

Lemma xsimpl_demo_gc_2 : forall H1 H2 H3,
  H1 \* H2 \* \Top \* \GC \* \Top ==> H3 \* \GC \* \GC.
Proof using. intros. xsimpl. Abort.
  (* Note that no attempt to collapse [\Top] or [\GC] on the RHS is performed,
     they are dealt with only by cancellation from the LHS *)

Lemma xsimpl_demo_gc_3 : forall H1 H2,
  H1 \* H2 \* \GC \* \GC ==> H2 \* \GC \* \GC \* \GC.
Proof using. intros. xsimpl. xaffine. Abort.

Lemma xsimpl_demo_gc_4 : forall H1 H2,
  H1 \* H2 \* \GC  ==> H2 \* \GC \* \Top \* \Top \* \GC.
Proof using. intros. xsimpl. Abort.

(* ----------------------------------------------------------------- *)
(** *** [xchange] demos *)

Lemma xchange_demo_1 : forall H1 H2 H3 H4 H5 H6,
  H1 ==> H2 \* H3 ->
  H1 \* H4 ==> (H5 \-* H6).
Proof using.
  introv M. dup 3.
  { xchange_nosimpl M. xsimpl. demo. }
  { xchange M. xsimpl. demo. }
  { xchanges M. demo. }
Qed.

Lemma xchange_demo_2 : forall A (Q:A->hprop) H1 H2 H3,
  H1 ==> \exists x, Q x \* (H2 \-* H3) ->
  H1 \* H2 ==> \exists x, Q x \* H3.
Proof using.
  introv M. dup 3.
  { xchange_nosimpl M. xsimpl. unfold protect. xsimpl. }
  { xchange M. xsimpl. }
  { xchanges M. }
Qed.

Lemma xchange_demo_4 : forall A (Q1 Q2:A->hprop) H,
  Q1 ===> Q2 ->
  Q1 \*+ H ===> Q2 \*+ H.
Proof using. introv M. xchanges M. Qed.

Lemma xsimpl_demo_hfalse : forall H1 H2,
  H1 ==> \[False] ->
  H1 \* H2 ==> \[False].
Proof using.
  introv M. dup.
  { xchange_nosimpl M. xsimpl0. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl1. }
  { xchange M. }
Qed.

Lemma xchange_demo_hforall_l :
 forall (hforall_specialize : forall A (x:A) (J:A->hprop), (hforall J) ==> (J x)),
 forall (Q:int->hprop) H1,
  (\forall x, Q x) \* H1 ==> Q 2 \* \Top.
Proof using.
  intros. xchange (>> hforall_specialize 2). xsimpl.
Qed.

End XsimplSetup.

(* 2025-01-06 19:51 *)
