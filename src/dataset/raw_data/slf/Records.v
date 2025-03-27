(** * Records: Reasoning about Records *)

Set Implicit Arguments.
From SLF Require Import LibSepReference LibSepTLCbuffer.
From SLF Require Import Arrays. Import Realization.

Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.
Implicit Type p q : loc.
Implicit Type k : nat.
Implicit Type i : int.
Implicit Type n z : nat.
Implicit Type v : val.
Implicit Type L : list val.

(* ################################################################# *)
(** * First Pass *)

(** This chapter explains how to specify operations on ML-style records in
    Separation Logic. In ML-like languages, a record is an allocated object
    whose header field stores the number of fields of the record. Concretely,
    each field is stored at a specific offset relative to the header. For
    example, consider a mutable list cell allocated at location [p]. It is
    represented in memory as:

    - a header at location [p], storing the number of fields, that is, the value
      [2];
    - a cell at location [p+1], storing the contents of the head field,
    - a cell at location [p+2], storing the contents of the tail field.

    Thus, at a low level, such a record can be represented by the heap
    predicate: [(hheader 2 p) \* ((p+1) ~~> x) \* ((p+2) ~~> q)]. To avoid
    exposing pointer arithmetic to the end user, we introduce the predicate
    [hfield p k v], written [p`.k ~~> v], to describe the contents of the field
    named [k] of the record at location [p].

    The chapter starts by presenting the representation predicate [hfield], as
    well as a higher-level predicate named [hrecord] for describing all fields
    at once. The second part of the chapter presents the specification of access
    and allocation operations. The last part explains how to implement and
    verify these operations using block allocation and pointer arithmetic. *)

(* ================================================================= *)
(** ** Representation of Individual Record Fields *)

(** Let us assume that each field name corresponds to a nonnegative offset. Let
    [field] denote the type of field names, an alias for [nat]. *)

Definition field : Type := nat.

(** The predicate [hfield p k v], written [p`.k ~~> v], asserts that the field
    [k] of the record [p] stores the value [v]. This predicate is presented as
    an abstract predicate to the end user. Internally, it may be defined using
    pointer arithmetic. *)

Definition hfield (p:loc) (k:field) (v:val) : hprop :=
  (p+1+k)%nat ~~> v.

Global Opaque hfield.

Notation "p `. k '~~>' v" := (hfield p k v)
  (at level 32, k at level 0, no associativity,
   format "p `. k  '~~>'  v").

(** Writing [(hheader 2 p) \* (p`.head ~~> x) \* (p`.tail ~~> q)] to describe a
    list cell record is fairly verbose and cumbersome to manipulate. To improve
    the situation, we introduce a generic representation predicate for records.
    This predicate allows us to describe the same list cell much more concisely
    as [p ~~~>`{ head := x; tail := q }].

    It what follows, we show how to implement this notation by introducing the
    heap predicates [hfields] and [hrecords]. These predicates will be used for
    stating both small-footprint and large-footprint specifications for record
    operations. *)

(* ================================================================= *)
(** ** Representation of Sets of Fields *)

(** A record field is described as the pair of a field and a value stored in
    this field. *)

Definition hrecord_field : Type := (field * val).

(** A record is described as a list of fields. *)

Definition hrecord_fields : Type := list hrecord_field.

(** We let the meta-variable [kvs] range over such lists. *)

Implicit Types kvs : hrecord_fields.

(** The heap predicate [hfields kvs p] asserts that, at location [p], one finds
    the representation of the fields described by the list [kvs]. The predicate
    [hfields kvs p] is defined recursively on the list [kvs]. If [kvs] is empty,
    the predicate describes the empty heap predicate. Otherwise, [kvs]
    decomposes as a head [(k,v)] and a tail [kvs']. The predicate [p`.k ~~> v]
    describes the field at offset [k], with contents [v]. The predicate
    [hfields kvs' p] describes the remaining fields. *)

Fixpoint hfields (kvs:hrecord_fields) (p:loc) : hprop :=
  match kvs with
  | nil => \[]
  | (k,v)::kvs' => (p`.k ~~> v) \* (hfields kvs' p)
  end.

(** A list cell with head field [x] and tail field [q] is represented by the
    list [(head,x)::(tail,q)::nil]. To support the syntax
    [`{ head := x; tail := q }], we introduce the following notation. For
    technical reasons associated with coercions, we need to separately define
    notation for parsing, where a cast to the type [val] is included, from
    notation for printing, where such a cast is not included. *)

Notation "`{ k1 := v1 }" :=
  ((k1,(v1:val))::nil)
  (at level 0, k1 at level 0, only parsing).

Notation "`{ k1 := v1 ; k2 := v2 }" :=
  ((k1,(v1:val))::(k2,(v2:val))::nil)
  (at level 0, k1, k2 at level 0, only parsing).

Notation "`{ k1 := v1 ; k2 := v2 ; k3 := v3 }" :=
  ((k1,(v1:val))::(k2,(v2:val))::(k3,(v3:val))::nil)
  (at level 0, k1, k2, k3 at level 0, only parsing).

Notation "`{ k1 := v1 }" :=
  ((k1,v1)::nil)
  (at level 0, k1 at level 0, only printing).

Notation "`{ k1 := v1 ; k2 := v2 }" :=
  ((k1,v1)::(k2,v2)::nil)
  (at level 0, k1, k2 at level 0, only printing).

Notation "`{ k1 := v1 ; k2 := v2 ; k3 := v3 }" :=
  ((k1,v1)::(k2,v2)::(k3,v3)::nil)
  (at level 0, k1, k2, k3 at level 0, only printing).

Open Scope val_scope.

(* ================================================================= *)
(** ** Representation of Records *)

(** The heap predicate [hrecord kvs p] describes a record by covering not just
    all the fields of the record but also the header. The cells are described by
    [hfields kvs p], and the header is described by [hheader n p], where [n]
    should be such that the keys in the list [kvs] are between [0] inclusive and
    [n] exclusive.

    A permissive definition of [hrecord kvs p] would allow the fields from the
    list [kvs] to be permuted arbitrarily. However, to avoid complications
    related to permutations, we make in this course the simplifying assumptions
    that fields are always listed in the order of their offsets.

    The auxiliary predicate [maps_all_fields z kvs] asserts that the keys from
    the association list [kvs] correspond exactly to the sequence made of the
    first [n] natural numbers, that is, [0; 1; ...; n-1]. *)

Definition maps_all_fields (n:nat) (kvs:hrecord_fields) : Prop :=
  LibList.map fst kvs = nat_seq 0 n.

(** The predicate [hrecord kvs p] exploits [maps_all_fields n kvs] to relate the
    value [n] stored in the header with the association list [kvs] that
    describes the contents of the fields. *)

Definition hrecord (kvs:hrecord_fields) (p:loc) : hprop :=
  \exists n, hheader n p \* hfields kvs p \* \[maps_all_fields n kvs].

(** We introduce the notation [p ~~~> kvs] for [hrecord kvs p], allowing to
    write, e.g., [p ~~~>`{ head := x; tail := q }]. *)

Notation "p '~~~>' kvs" := (hrecord kvs p)
  (at level 32).

(** The following lemma may be used to convert a concrete [hrecord] predicate
    into a [hheader] and a conjunction of [hfield] predicates. In the statement
    below, [LibListExec.length] is a variant of [LibList.length] that computes
    in Coq using [simpl] or [reflexivity]. *)

Lemma hrecord_elim : forall p kvs,
  hrecord kvs p ==> hheader (LibListExec.length kvs) p \* hfields kvs p.
Proof using.
  intros. unfold hrecord. xpull. intros z Hz. xsimpl. xsimpl.
  rewrite LibListExec.length_eq. applys himpl_of_eq. fequal. gen Hz.
  unfold maps_all_fields. generalize 0%nat. gen z.
  induction kvs; intros; destruct z as [|z']; rew_listx in *; tryfalse.
  { math. } { inverts Hz. forwards*: IHkvs H1. math. }
Qed.

(** For example, let us show how to convert from
    [p ~~~> `{ head := x ; tail := q }] to the conjunction of [hheader 2 p] and
    [p`.head ~~> x] and [p`.tail ~~> q]. *)

Definition head : field := 0%nat.
Definition tail : field := 1%nat.

Lemma demo_hrecord_intro_elim : forall p x q,
      p ~~~> `{ head := x ; tail := q } ==> \[].
Proof using. intros. xchange hrecord_elim; simpl. Abort.

(* ================================================================= *)
(** ** Reasoning about Reads from Record Fields *)

Declare Scope trm_scope_ext.

(** The read operation is described by an expression of the form
    [val_get_field k p], where [k] denotes a field name and [p] denotes the
    location of a record.

    Observe that [k] is _not_ a program value of type [val], but rather a name
    for a natural number.

    The expression [val_get_field] has type [field -> val], and for a given
    field [k] the expression [val_get_field k] is a value, which may be applied
    in the program syntax to a pointer [p]. *)

Parameter val_get_field : field -> val.

(** The read operation [val_get_field k p] is written [p`.k]. *)

Notation "t1 '`.' k" :=
  (val_get_field k t1)
  (in custom trm at level 56, k at level 0, format "t1 '`.' k" )
  : trm_scope_ext.

(** The operation [val_get_field k p] can be specified at three levels.

    First, its small-footprint specification operates at the level of a single
    field, described by [p`.k ~~> v]. The specification is very similar to that
    of [val_get]. The return value is exactly [v]. *)

Parameter triple_get_field : forall p k v,
  triple (val_get_field k p)
    (p`.k ~~> v)
    (fun r => \[r = v] \* (p`.k ~~> v)).

(** Second, the read operation [val_get_field] can be specified with respect to
    a list of fields, described in the form [hfields kvs p]. To that end, we
    introduce a function called [hfields_lookup] for extracting the value [v]
    associated with a field [k] in a list of record fields [kvs]. Note that the
    operation [hfields_lookup k kvs] returns an [option val], because we cannot
    presume that the field [k] occurs in [kvs]. *)

Fixpoint hfields_lookup (k:field) (kvs:hrecord_fields) : option val :=
  match kvs with
  | nil => None
  | (ki,vi)::kvs' => if Nat.eq_dec k ki
                       then Some vi
                       else hfields_lookup k kvs'
  end.

(** Under the assumption that [hfields_lookup k kvs] returns [Some v], the read
    operation [val_get_field k p] is specified to return [v]. *)

Parameter triple_get_field_hfields : forall kvs p k v,
  hfields_lookup k kvs = Some v ->
  triple (val_get_field k p)
    (hfields kvs p)
    (fun r => \[r = v] \* hfields kvs p).

(** Third, the read operation [val_get_field] can be specified with respect to
    the predicate [hrecord kvs p], describing the full record, including its
    header. The corresponding specification shown below follows a similar
    pattern as the specification of [hfield]. *)

Parameter triple_get_field_hrecord : forall kvs p k v,
  hfields_lookup k kvs = Some v ->
  triple (val_get_field k p)
    (hrecord kvs p)
    (fun r => \[r = v] \* hrecord kvs p).

(* ================================================================= *)
(** ** Reasoning about Writes To Record Fields *)

(** The write operation is described by an expression of the form
    [val_set_field k p v], where [k] denotes a field name, and where [p] denotes
    the location of a record, and where [v] is the new value for the field. *)

Parameter val_set_field : field -> val.

(** The operation [val_set_field k p v] is abbreviated [Set p`.k ':= v]. *)

Notation "t1 '`.' k ':=' t2" :=
  (val_set_field k t1 t2)
  (in custom trm at level 56, k at level 0, format "t1 '`.' k  ':=' t2")
  : trm_scope_ext.

(** As for the read operation, the write operation can be specified at three
    levels. First, it may be specified at the level of an individual field. *)

Parameter triple_set_field : forall v p k v',
  triple (val_set_field k p v)
    (p`.k ~~> v')
    (fun _ => p`.k ~~> v).

(** Alternatively, it may be specified in terms of [hfields] or [hrecord], using
    an auxiliary function called [hrecord_update]. This function computes an
    updated list of fields to reflect the action of a write operation.

    Concretely, [hrecord_update k w kvs] replaces the contents of the field
    named [k] with the value [w]. It returns a description [kvs'] of the record
    fields, provided the update operation succeeded, i.e., provided that the
    field [k] on which the update is to be performed actually occurs in the list
    [kvs]. *)

Fixpoint hfields_update (k:field) (v:val) (kvs:hrecord_fields)
                        : option hrecord_fields :=
  match kvs with
  | nil => None
  | (ki,vi)::kvs' => if Nat.eq_dec k ki
                       then Some ((k,v)::kvs')
                       else match hfields_update k v kvs' with
                            | None => None
                            | Some LR => Some ((ki,vi)::LR)
                            end
  end.

(** The specification in terms of [hfields] is as follows. *)

Parameter triple_set_field_hfields : forall kvs kvs' k p v,
  hfields_update k v kvs = Some kvs' ->
  triple (val_set_field k p v)
    (hfields kvs p)
    (fun _ => hfields kvs' p).

(** The specification in terms of [hrecord] follows a similar pattern. *)

Parameter triple_set_field_hrecord : forall kvs kvs' k p v,
  hfields_update k v kvs = Some kvs' ->
  triple (val_set_field k p v)
    (hrecord kvs p)
    (fun _ => hrecord kvs' p).

(* ================================================================= *)
(** ** Reasoning about Record Allocation with Initializers *)

(** In ML, records may only be allocated by providing values to initialize every
    field. This allocation operation can be defined in an arity-generic way.
    However, to avoid technicalities, we here present only its specialization
    for arity 2. For example, the notation [`{ head := x; tail := q }] stands
    for the term [(val_new_hrecord_2 head tail) x q].

    Here, [val_new_hrecord_2] is a Coq function that expects two names as
    arguments and produces a value. For example, the expression
    [val_new_hrecord_2 head tail] is a value that may be applied to two
    arguments in the program syntax. *)

Parameter val_new_hrecord_2 : field -> field -> val.

Notation "`{ k1 := v1 ; k2 := v2 }" :=
  (val_new_hrecord_2 k1 k2 v1 v2)
  (in custom trm at level 65,
   k1, k2 at level 0,
   v1, v2 at level 65).

(** The record allocation operation [`{ k1 := v1 ; k2 := v2 }] is specified as
    follows. The premises [k1 = 0] and [k2 = 1] enforce the field names to be
    provided in increasing order, starting from zero. The postcondition
    describes a record at address [p] using the predicate
    [p ~~~> `{ k1 := v1 ; k2 := v2 }], i.e.,
    [hrecord ((k1,v1)::(k2,v2)::nil) p]. *)

Parameter triple_new_hrecord_2 : forall (k1 k2:field) (v1 v2:val),
  k1 = 0%nat ->
  k2 = 1%nat ->
  triple <{ `{ k1 := v1; k2 := v2 } }>
    \[]
    (funloc p => p ~~~> `{ k1 := v1 ; k2 := v2 }).

(** For example, the operation [mcons x q] allocates a list cell with head value
    [x] and tail pointer [q]. *)

Definition mcons : val :=
  val_new_hrecord_2 head tail.

Lemma triple_mcons : forall (x q:val),
  triple (mcons x q)
    \[]
    (funloc p => p ~~~> `{ head := x ; tail := q }).
Proof using. intros. applys* triple_new_hrecord_2. Qed.

(** This completes the presentation of the formalization of the mechanisms for
    reasoning about records. These mechanisms were illustrated throughout the
    chapter [Repr]. *)

(* ################################################################# *)
(** * Optional Material *)

Module Realization.
Import ProgramSyntax.
Open Scope trm_scope_ext.

(** In this section, we explain how [val_get_field], [val_set_field], and
    [val_new_hrecord_2] can be realized in terms of block allocation and pointer
    arithmetic, following the same approach as in the previous chapter on
    arrays. In particular, we use a similar proof set up. *)

Global Transparent hfield.

#[local] Hint Extern 1 (_ >= _) => math : triple.

Ltac is_additional_arith_type T ::=
  match T with
  | loc => constr:(true)
  | field => constr:(true)
  end.

(* ================================================================= *)
(** ** Implementation of Record Accesses using Pointer Arithmetic *)

(** The get operation on a field, written [p`.k], is encoded as
    [val_get (p+1+k)]. In the definition shown below, the braces around
    [nat_to_Z k] are used to embed the Coq natural number [k] into the code, in
    the form of an integer represented in the grammar of terms using the
    implicit coercion [val_int]. *)

Definition val_get_field (k:field) : val :=
  <{ fun 'p =>
       let 'p1 = val_ptr_add 'p 1 in
       let 'q = val_ptr_add 'p1 {nat_to_Z k} in
       val_get 'q }>.

Notation "t1 '`.' f" :=
  (val_get_field f t1)
  (in custom trm at level 56, f at level 0, format "t1 '`.' f" ).

#[export]Hint Resolve triple_ptr_add_nonneg : triple.

Lemma triple_get_field : forall p k v,
  triple ((val_get_field k) p)
    (p`.k ~~> v)
    (fun r => \[r = v] \* (p`.k ~~> v)).
Proof using.
  unfold hfield. xwp. xapp. xapp. unfolds field.
  math_rewrite (p + abs 1 + abs k = p+1+k)%nat. xapp. xsimpl*.
Qed.

(** The set operation on a field, written [Set p`.k := v], is encoded as
    [val_set (p+1+k) v]. *)

Definition val_set_field (k:field) : val :=
  <{ fun 'p 'v =>
       let 'p1 = val_ptr_add 'p 1 in
       let 'q = val_ptr_add 'p1 {nat_to_Z k} in
       val_set 'q 'v }>.

Lemma triple_set_field : forall v1 p k v2,
  triple ((val_set_field k) p v2)
    (p`.k ~~> v1)
    (fun _ => p`.k ~~> v2).
Proof using.
  unfold hfield. intros. xwp. xapp. xapp.
  math_rewrite (p + abs 1 + abs k = p+1+k)%nat. xapp. xsimpl.
Qed.

Notation "t1 '`.' f ':=' t2" :=
  (val_set_field f t1 t2)
  (in custom trm at level 56, f at level 0, format "t1 '`.' f  ':='  t2").

(* ================================================================= *)
(** ** Specification of Record Accesses w.r.t. [hfields] *)

(** The specifications [triple_get_field] and [triple_set_field] proved in the
    previous section correspond to small-footprint specifications, with
    preconditions mentioning a single field. Corollaries to these specifications
    can be established with preconditions mentioning a list of fields, with
    preconditions expressed using [hfields]. *)

Lemma triple_get_field_hfields : forall kvs p k v,
  hfields_lookup k kvs = Some v ->
  triple (val_get_field k p)
    (hfields kvs p)
    (fun r => \[r = v] \* hfields kvs p).
Proof using.
  intros L. induction L as [| [ki vi] L']; simpl; introv E.
  { inverts E. }
  { case_if.
    { inverts E. subst ki. applys triple_conseq_frame.
      { applys triple_get_field. } { xsimpl. } { xsimpl*. } }
    { applys triple_conseq_frame.
      { applys IHL' E. }
      { xsimpl. }
      { xsimpl*. } } }
Qed.

Lemma triple_set_field_hfields : forall kvs kvs' k p v,
  hfields_update k v kvs = Some kvs' ->
  triple (val_set_field k p v)
    (hfields kvs p)
    (fun _ => hfields kvs' p).
Proof using.
  intros kvs. induction kvs as [| [ki vi] kvs']; simpl; introv E.
  { inverts E. }
  { case_if.
    { inverts E. subst ki. applys triple_conseq_frame.
      { applys triple_set_field. } { xsimpl. } { xsimpl*. } }
    { cases (hfields_update k v kvs') as C2; tryfalse. inverts E.
      applys triple_conseq_frame. { applys IHkvs' C2. }
      { xsimpl. } { simpl. xsimpl*. } } }
Qed.

(* ================================================================= *)
(** ** Specification of Record Accesses w.r.t. [hrecord] *)

(** This section further refines the specification for [val_get_field] and
    [val_set_field], into specification expressed using [hrecord]. For
    [val_get_field], the proof is straightforward. *)

Lemma triple_get_field_hrecord : forall kvs p k v,
  hfields_lookup k kvs = Some v ->
  triple (val_get_field k p)
    (hrecord kvs p)
    (fun r => \[r = v] \* hrecord kvs p).
Proof using.
  introv M. unfold hrecord. xtriple. xpull. intros z Hz.
  xapp (>> triple_get_field_hfields M). xsimpl*.
Qed.

(** For [val_set_field], however, we need an auxiliary lemma about
    [hfields_update], showing that the update operation preserves the names of
    the fields. This lemma is established in two steps. *)

Lemma hfields_update_preserves_fields : forall kvs kvs' k v,
  hfields_update k v kvs = Some kvs' ->
  LibList.map fst kvs' = LibList.map fst kvs.
Proof using.
  intros kvs. induction kvs as [|[ki vi] kvs1]; simpl; introv E.
  { introv _ H. inverts H. }
  { case_if.
    { inverts E. rew_listx*. subst. fequals. }
    { cases (hfields_update k v kvs1).
      { inverts E. rew_listx. fequals*. }
      { inverts E. } } }
Qed.

Lemma hfields_update_preserves_maps_all_fields : forall kvs kvs' z k v,
  hfields_update k v kvs = Some kvs' ->
  maps_all_fields z kvs = maps_all_fields z kvs'.
Proof using.
  introv M. unfold maps_all_fields. extens.
  rewrites* (>> hfields_update_preserves_fields M).
Qed.

(** We are then ready to derive the specification for [val_set_field]. *)

Lemma triple_set_field_hrecord : forall kvs kvs' k p v,
  hfields_update k v kvs = Some kvs' ->
  triple (val_set_field k p v)
    (hrecord kvs p)
    (fun _ => hrecord kvs' p).
Proof using.
  introv M. unfold hrecord. xtriple. xpull. intros z Hz.
  xapp (>> triple_set_field_hfields M). xsimpl.
  rewrites* <- (>> hfields_update_preserves_maps_all_fields z M).
Qed.

(* ================================================================= *)
(** ** Implementation of Record Allocation without Initialization *)

(** Recall that a record with [n] fields is represented as a memory block of
    size [n+1]. The first memory cell in the block corresponds to the header,
    and stores the number of fields, that is, the value [n]. The [n] other cells
    store the value associated with each of the fields.

    The operation that allocates and initializes a fresh record with specific
    values can be implemented in two stages. The first function, named
    [val_alloc_hrecord], takes a list of [n] field names, and allocates a record
    with [n] fields, with contents specified as "uninitialized". The second
    function, named [val_new_hrecord], takes [n] field names and [n] values. It
    invokes the first function to allocate the record, then performs one write
    per field to store the provided values into the corresponding memory cells.

    The present section focuses on the first part, namely the allocation without
    initialization. The Coq value [val_alloc_hrecord ks] depends on a list of
    field names. This value corresponds to a function that, when applied to a
    unit argument, allocates a record with [length ks] fields. The operation
    [(val_alloc_hrecord ks) ()] is only specified when [ks] corresponds to a
    list of names whose unfolding is of the form [0 :: 1 :: 2 :: ... (n-1)].

    The implementation of this operation allocates a block of size [n+1] at a
    fresh location [p], then sets the header cell to the value [n], then returns
    the address [p]. In the statement below, the expression
    [{LibListExec.length ks}] in braces computes in Coq the expression
    [length ks], and inserts the result in the code as a constant integer --
    that is, as a value of the form [val_int (LibListExec.length ks)]. *)

Definition val_alloc_hrecord (ks:list field) : val :=
  <{ fun 'v =>
       let 'm = {LibListExec.length ks} + 1 in
       let 'p = val_alloc 'm in
       val_set 'p {LibListExec.length ks};
       'p }>.

(** A key auxiliary result asserts that, if [kvs] is a list of key-value pairs
    such that the keys correspond to consecutive field names, then a list of
    fields described as [hfields kvs p] corresponds to a range of consecutive
    cells as described by [hrange (List.map snd kvs) (p+1)], for the definition
    of [hrange] given in [Arrays]. *)

Lemma hfields_eq_hrange : forall z L p kvs,
  maps_all_fields z kvs ->
  z = length L ->
  L = LibList.map snd kvs ->
  hfields kvs p = hrange L (p+1)%nat.
Proof using.
  asserts Ind: (forall L p kvs o,
    LibList.map fst kvs = nat_seq o (length L) ->
    L = LibList.map snd kvs ->
    hfields kvs p = hrange L (p+1+o)%nat).
  { intros L. induction L as [|v L']; introv M E; rew_listx in *;
    destruct kvs as [|[k v'] kvs']; tryfalse; rew_listx in *.
    { auto. }
    { simpls. inverts M as M'. inverts E as E'. rew_listx in *.
      unfold hfield. fequals. math_rewrite (p+1+o+1=p+1+(o+1))%nat.
      applys* IHL'. math_rewrite* (o+1=S o)%nat. } }
  introv M HL E. subst z. rewrites (>> Ind M E). fequals. unfold loc. math.
Qed.

(** The specification of [val_alloc_hrecord ks] involves an empty precondition
    and a postcondition of the form [hrecord kvs p], where the list [kvs] maps
    the fields names from [ks] to the value [val_uninit]. The premise
    [ks = nat_seq 0 (length ks)] checks that the list [ks] contains consecutive
    offsets starting from zero.

    Recall that [LibListExec.length] is a variant of [LibList.length] that
    computes in Coq (using [simpl] or [reflexivity]). Likewise [LibListExec.map]
    is a computable version of [LibList.map]. *)

Lemma triple_alloc_hrecord : forall ks,
  ks = nat_seq 0 (LibListExec.length ks) ->
  triple ((val_alloc_hrecord ks) ())
    \[]
    (funloc p => hrecord (LibListExec.map (fun k => (k,val_uninit)) ks) p).
Proof using.
  introv Hks. xwp. xapp. xapp. intros p Hp. unfolds field.
  rewrite LibListExec.length_eq in *. set (n := length ks) in *.
  math_rewrite (abs (n + 1) = S n). rew_listx. simpl.
  xapp. xval. xsimpl*. unfold hrecord. autorewrite with rew_list_exec.
  asserts R: (maps_all_fields n (LibList.map (fun k => (k, val_uninit)) ks)).
  { unfolds. rewrite Hks. clears ks p. generalize 0%nat as o.
    induction n as [|n']; intros; simpl; rew_listx; fequals*. }
  xsimpl* n. xchange* <- (@hfields_eq_hrange n). { rew_listx*. }
  { unfold n. clears n p. induction ks as [|ks']; rew_listx; fequals*. }
Qed.

#[global] Hint Resolve triple_alloc_hrecord : triple.

(** The interest of using the computable counterparts of the function [length]
    and [map] is that a call to [simpl] will yield exactly the expected result,
    with lists indexed using field names. For example, the allocation of a list
    cell is specified as follows. *)

Lemma triple_alloc_mcons :
  triple (val_alloc_hrecord (head::tail::nil) ())
    \[]
    (funloc p => p ~~~> `{ head := val_uninit ; tail := val_uninit }).
Proof using.
  dup.
  { (* Detailed proof: *)
    applys triple_alloc_hrecord. simpl. rew_listx. reflexivity. }
  { (* Short proof: *)
    applys* triple_alloc_hrecord. }
Qed.

(* ================================================================= *)
(** ** Implementation of Record Allocation with Initialization *)

(** We now show the implementation of record initialization in the particular
    case of records with exactly 2 fields. Recall that [val_new_hrecord_2 k1 k2]
    denotes a Coq value of type [val], which may be applied in the grammar of
    terms to two arguments, [x1] and [x2]. The definition below shows an
    implementation for [val_new_hrecord_2]. In this definition, the expression
    in braces [val_alloc_hrecord (k1::k2::nil)] refers to a Coq term, embedded
    in the syntax of program terms. *)

Definition val_new_hrecord_2 (k1:field) (k2:field) : val :=
  <{ fun 'x1 'x2 =>
       let 'p = {val_alloc_hrecord (k1::k2::nil)} () in
       'p`.k1 := 'x1;
       'p`.k2 := 'x2;
       'p }>.

(** To improve readability, we introduce notation to allow writing, e.g.,
    [`{ head := x; tail := q }] for the allocation and initialization of a list
    cell. *)

Notation "`{ k1 := v1 ; k2 := v2 }" :=
  (val_new_hrecord_2 k1 k2 v1 v2)
  (in custom trm at level 65,
   k1, k2 at level 0,
   v1, v2 at level 65) : trm_scope_ext.

(** This operation is specified as follows. *)

Lemma triple_new_hrecord_2 : forall k1 k2 v1 v2,
  k1 = 0%nat ->
  k2 = 1%nat ->
  triple <{ `{ k1 := v1; k2 := v2 } }>
    \[]
    (funloc p => p ~~~> `{ k1 := v1 ; k2 := v2 }).
Proof using.
  introv -> ->. xwp. xapp triple_alloc_hrecord. { reflexivity. }
  intros p. simpl.
  xapp triple_set_field_hrecord. { reflexivity. }
  xapp triple_set_field_hrecord. { reflexivity. }
  xval. xsimpl*.
Qed.

End Realization.

(** This completes the verification of the implementation of record operations
    in terms of block allocation and pointer arithmetic. The generalization of
    [val_new_hrecord_2] to handle arbitrary arities involves more technical
    meta-programming, beyond the scope of this course. *)

(* ================================================================= *)
(** ** Extending [xapp] to Support Record Access Operations *)

(** This section generalizes the tactic [xapp] to enable it to automatically
    reason about read and write on records specified using [hrecord]. The lemma
    [xapp_get_field_lemma] reformulates the specification
    [triple_get_field_hrecord] in weakest-precondition form. Its statement takes
    the form:
    [H ==> \exists kvs, (hrecord kvs p) \* (match ... with Some .. => ..)],
    where the [match] construct reflects the preconditions
    [hfields_lookup k kvs = Some v]. *)

Lemma xapp_get_field_lemma : forall H k p Q,
  H ==> \exists kvs, (hrecord kvs p) \*
     match hfields_lookup k kvs with
     | None => \[False]
     | Some v => ((fun r => \[r = v] \* hrecord kvs p) \--* protect Q) end ->
  H ==> wpgen_app (val_get_field k p) Q.
Proof using.
  introv N. xchange N. intros kvs. cases (hfields_lookup k kvs).
  { unfold wpgen_app. xsimpl.
    applys* triple_conseq_frame triple_get_field_hrecord.
    { xsimpl. }
    { xpull. intros r ->. xchange (qwand_specialize v).
      rewrite* hwand_hpure_l. } }
  { xpull. }
Qed.

(** Likewise, the lemma [xapp_set_field_lemma] reformulates the specification
    [triple_set_field_hrecord]. The assumption
    [hfields_update k v kvs = Some ks'] is also captured by a pattern matching.
    *)

Lemma xapp_set_field_lemma : forall H k p v Q,
  H ==> \exists kvs, (hrecord kvs p) \*
     match hfields_update k v kvs with
     | None => \[False]
     | Some kvs' => ((fun _ => hrecord kvs' p) \--* protect Q) end ->
  H ==> wpgen_app (val_set_field k p v) Q.
Proof using.
  introv N. xchange N. intros kvs. cases (hfields_update k v kvs).
  { unfold wpgen_app. xsimpl.
    applys* triple_conseq_frame triple_set_field_hrecord.
    { xsimpl. }
    { xpull. intros r. xchange (qwand_specialize r). } }
  { xpull. }
Qed.

(** The hook [xapp_nosubst_for_records], invoked by [xapp], is then implemented
    by exploiting the two lemmas above, in conjunction with [xsimpl]. *)

Ltac xapp_nosubst_for_records tt ::=
  first [ applys xapp_set_field_lemma; xsimpl; simpl; xapp_simpl
        | applys xapp_get_field_lemma; xsimpl; simpl; xapp_simpl ].

(** The above definition is the one used in [LibSepReference]. It was put to
    practice in the chapters [Basic] and [Repr]. *)

(* 2024-12-26 10:22 *)
