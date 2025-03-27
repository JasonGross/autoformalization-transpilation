(** * Maps: Total and Partial Maps *)

(** This brief chapter defines two kinds of maps: _total_ maps, which
    include a _default_ element to be returned when a key being looked
    up does not exist, and _partial_ maps, which return an [option] to
    indicate success or failure. We'll use maps in upcoming chapters
    to verify other data structures. *)

From Coq Require Import Bool.
From Coq Require Import FunctionalExtensionality.
From VFA Require Import Perm.

(* ################################################################# *)
(** * Total Maps *)

(** The [Lists] chapter in Volume 1 previously
    implemented maps with lists of key-value pairs. Here, we instead
    use functions to implement maps. Functions enable an _extensional_
    treatment of maps: two maps will be equal if they take the keys to
    the same values. We won't have to worry about issues that arise
    with lists, such as duplicate keys, or order of pairs in the list,
    etc. Proofs that use maps will therefore be simpler.

    Intuitively, a total map over a type [A] _is_ just a function that
    can be used to look up keys, yielding [A]s.  For simplicity, the
    keys in our maps will be natural numbers. *)

Definition total_map (A : Type) : Type := nat -> A.

(** The function [t_empty] yields an empty total map, given a
    default element; this map always returns the default element when
    applied to any id. *)

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

(** More interesting is the [update] function, which (as before)
    takes a map [m], a key [x], and a value [v] and returns a new map
    that takes [x] to [v] and takes every other key to whatever [m]
    does. *)

Definition t_update {A : Type}
           (m : total_map A) (x : nat) (v : A) : total_map A :=
  fun x' => if x =? x' then v else m x'.

(** This definition is a nice example of higher-order programming.
    The [t_update] function takes a _function_ [m] and yields a new
    function [fun x' => ...] that behaves like the desired map.

    For example, we can build a map taking [id]s to [bool]s, where [Id 3]
    is mapped to [true] and every other key is mapped to [false], like
    this: *)

Definition examplemap :=
  t_update (t_update (t_empty false) 1 false) 3 true.

(** This completes the definition of total maps.  Note that we don't
    need to define a [find] operation because it is just function
    application! *)

Example update_example1 : examplemap 0 = false.
Proof. reflexivity. Qed.

Example update_example2 : examplemap 1 = false.
Proof. reflexivity. Qed.

Example update_example3 : examplemap 2 = false.
Proof. reflexivity. Qed.

Example update_example4 : examplemap 3 = true.
Proof. reflexivity. Qed.

(** To use maps in later chapters, we'll need several
    fundamental facts about how they behave.  Even if you don't work
    the following exercises, make sure you thoroughly understand the
    statements of the lemmas!  (Some of the proofs require the
    [functional_extensionality] axiom, which is discussed in the
    [Logic] chapter.)  *)

(** **** Exercise: 1 star, standard (t_apply_empty)

    The empty map returns its default element for all keys: *)
Lemma t_apply_empty:  forall A x v, @t_empty A v x = v.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (t_update_eq)

    If we update a map [m] at a key [x] with a new value [v] and then
    look up [x] in the map resulting from the [update], we get back
    [v]: *)

Lemma t_update_eq : forall A (m: total_map A) x v,
  (t_update m x v) x = v.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, standard (t_update_neq)

    If we update a map [m] at a key [x1] and then look up a
    _different_ key [x2] in the resulting map, we get the same result
    that [m] would have given: *)

Theorem t_update_neq : forall (X:Type) v x1 x2
                         (m : total_map X),
  x1 <> x2 ->
  (t_update m x1 v) x2 = m x2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (t_update_shadow)

    If we update a map [m] at a key [x] with a value [v1] and then
    update again with the same key [x] and another value [v2], the
    resulting map behaves the same (gives the same result when applied
    to any key) as the simpler map obtained by performing just
    the second [update] on [m]: *)

Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
    t_update (t_update m x v1) x v2
  = t_update m x v2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (t_update_same)

    If we update a map to assign key [x] the same value as it already
    has in [m], then the result is equal to [m]: *)

Theorem t_update_same : forall X x (m : total_map X),
  t_update m x (m x) = m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (t_update_permute)

    If we update a map [m] at two distinct keys, it doesn't matter in
    which order we do the updates. *)

Theorem t_update_permute : forall (X:Type) v1 v2 x1 x2
                             (m : total_map X),
  x2 <> x1 ->
    (t_update (t_update m x2 v2) x1 v1)
  = (t_update (t_update m x1 v1) x2 v2).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Partial Maps *)

(** A partial map with elements of type [A] is simply a total map with
    elements of type [option A] and default element [None]. *)

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type}
           (m : partial_map A) (x : nat) (v : A) : partial_map A :=
  t_update m x (Some v).

(** We can easily lift all of the basic lemmas about total maps to
    partial maps.  *)

Lemma apply_empty : forall A x, @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall A (m: partial_map A) x v,
  (update m x v) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall (X:Type) v x1 x2
                       (m : partial_map X),
  x2 <> x1 ->
  (update m x2 v) x1 = m x1.
Proof.
  intros X v x1 x2 m H.
  unfold update. rewrite t_update_neq; auto.
Qed.

Lemma update_shadow : forall A (m: partial_map A) v1 v2 x,
  update (update m x v1) x v2 = update m x v2.
Proof.
  intros A m v1 v2 x1. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall X v x (m : partial_map X),
  m x = Some v ->
  update m x v = m.
Proof.
  intros X v x m H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (X:Type) v1 v2 x1 x2
                                (m : partial_map X),
  x2 <> x1 ->
    (update (update m x2 v2) x1 v1)
  = (update (update m x1 v1) x2 v2).
Proof.
  intros X v1 v2 x1 x2 m. unfold update.
  apply t_update_permute.
Qed.

(* 2025-01-06 17:19 *)
