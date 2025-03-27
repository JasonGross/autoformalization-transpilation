(** * Arrays: Reasoning about Arrays *)

Set Implicit Arguments.
From SLF Require Import LibSepReference LibSepTLCbuffer.
#[global] Hint Rewrite conseq_cons' : rew_listx.
Open Scope wp_scope.

Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.
Implicit Type p q : loc.
Implicit Type k : nat.
Implicit Type i n : int.
Implicit Type v : val.
Implicit Types z : nat.

(* ################################################################# *)
(** * First Pass *)

(** This chapter explains how to specify operations on ML-style arrays in
    Separation Logic. In ML-like languages, an array of size [n] is an allocated
    block of size [n+1] with a header field that stores the length of the array.
    To perform a [get] or a [set] operation on an array, the programmer provides
    the pointer to the array object -- that is, the address of the header cell
    -- as well as the index on which to operate.

    The chapter starts with a presentation of _large-footprint_ operations for
    arrays, expressed with respect to a representation predicate of the form
    [harray L p]. Then it presents _small-footprint_ specifications for the same
    operations, involving a representation predicate of the form [hcell v p i]
    for representing each cell, as well as a predicate, written [hheader p n]
    for representing the header field. Interestingly, the header cell predicate
    alone suffices for reading the length of an array.

    We will illustrate the benefits of small-footprint specifications for
    reasoning about the recursive function [quicksort], which operates on array
    segments. Segments are described using the heap predicate [harray_seg L p i]
    . Array segments allow "framing" the parts of arrays that are not involved
    in a recursive call.

    The "More Details" part of the chapter explains how to define the predicates
    [hheader], [hcell], [hseg], and [harray] with respect to the representation
    of heaps as a finite map from locations to values. The "optional material"
    part of the chapter shows how to implement and verify [make], [length],
    [get], and [set] in terms of block allocation and pointer arithmetic. *)

(* ================================================================= *)
(** ** Large-Footprint Specifications for Array Operations *)

(** The heap predicate [harray L p] asserts that an array is allocated at
    address [p] and that its elements are described by the list [L]. At this
    stage, let us axiomatize this predicate. *)

Parameter harray : forall (L:list val) (p:loc), hprop.

(** The primitive operation [val_array_make n v] allocates a fresh array of
    length [n], with each of its cells containing the value [v]. *)

Parameter val_array_make : val.

(** The specification of [val_array_make] requires the length [n] to be
    nonnegative. The output array is described as a list made of [n] copies of
    the value [v]. This list is built by the utility function
    [LibList.make (abs n) v], where [abs] converts the integer [n] into a
    natural number. *)

Parameter triple_array_make : forall n v,
  n >= 0 ->
  triple (val_array_make n v)
    \[]
    (funloc p => harray (LibList.make (abs n) v) p).

(** Alternatively, the array produced by [make n v] can be described
    extensionally, as a list [L] of length [n] such that all its elements are
    equal to [v]. *)

Parameter triple_array_make' : forall n v,
  n >= 0 ->
  triple (val_array_make n v)
    \[]
    (funloc p => \exists L, harray L p
                 \* \[n = length L]
                 \* \[forall i, 0 <= i < n -> LibList.nth (abs i) L = v]).

(** We'll come back shortly afterwards on the benefits of using the first
    presentation, expressed using [LibList.make]. *)

(** The operation [val_array_length p] returns the length of the array allocated
    at location [p]. *)

Parameter val_array_length : val.

(** The specification for [val_array_length] expects a heap predicate of the
    form [harray L p] and asserts that the return value is the length of the
    logical list [L]. The postcondition repeats [harray L p] to capture the fact
    that the array is not modified during the operation. *)

Parameter triple_array_length : forall L p,
  triple (val_array_length p)
    (harray L p)
    (fun r => \[r = length L] \* harray L p).

(** The operation [val_array_get p i] returns the contents of the [i]-th cell of
    the array at location [p]. *)

Parameter val_array_get : val.

(** The specification of [val_array_get] is as follows. The precondition
    describes the array in the form [harray L p], with a premise that requires
    the index [i] to be in the valid range, that is, between zero (inclusive)
    and the length of [L] (exclusive). The postcondition asserts that the result
    value is the [i]-th element of the list [L], written [nth (abs i) L]. The
    postcondition again repeats [harray L p] because the array is unchanged. *)

Parameter triple_array_get : forall L p i,
  0 <= i < length L ->
  triple (val_array_get p i)
    (harray L p)
    (fun r => \[r = LibList.nth (abs i) L] \* harray L p).

(** The operation [val_array_set p i v] updates the contents of the [i]-th cell
    of the array at location [p]. *)

Parameter val_array_set : val.

(** The specification of [val_array_set] admits the same precondition as
    [val_array_get], with [harray L p] and the constraint [0 <= i < length L].
    Its postcondition describes the updated array using a predicate of the form
    [harray L' p], where [L'] corresponds to the update of the [i]-th item of
    the list [L] with the value [v], written [update (abs i) v L]. *)

Parameter triple_array_set : forall L p i v,
  0 <= i < length L ->
  triple (val_array_set p i v)
    (harray L p)
    (fun _ => harray (LibList.update (abs i) v L) p).

#[global] Hint Resolve triple_array_get triple_array_set
                       triple_array_make triple_array_length : triple.

(** Above, we saw two ways of stating the postcondition of the [array_make]
    operation: either describing the result using a corresponding logical
    operation, like in [triple_array_make]; or describing the result
    extensionally by specifying the value of each cell, as in
    [triple_array_make']. A question of this kind appears not only here for
    [array_make], but for numerous other operations involving arrays. There is
    no definite rule, but the following considerations motivate our preference
    for the first style.

    A first aspect to take into account is that expressing the postcondition in
    terms of a logical operation like in [triple_array_make] leads to a more
    concise specification.

    A second aspect to consider is how to reason about a sequence of operations
    involving arrays. For example, consider the following program fragment.

OCaml:

    let t = Array.make n v in
    t.(i) <- w;
    t.(j)

    When using logical operations, the resulting array may be described as
    [nth (abs j) (update (abs i) w (make n v))]. If [i <> j], this expression
    can be simplified by rewriting into [v]. In other words, all the reasoning
    is carried out by in-place rewriting without involving any hypothesis.

    When using extensional characterization, the operation [Array.make n v] is
    described as an array [L] such that [nth (abs k) L = v] holds for any valid
    index [k]. In that same style, the operation [Array.set t i w] would be
    described as returning an array [L'] such that [nth (abs i) L' = w] and
    [nth (abs k) L' = nth (abs k) L] for any valid index [k] such that [k <> i].
    Then, the final value is described as [nth (abs j) L']. To prove this value
    equal to [v] under the assumption [i <> j], we would need to perform two
    rewriting steps using each of the two hypotheses: [nth (abs j) L'] is equal
    to [nth (abs j) L], hence equal to [v].

    In summary, both approach work. But when a logical function corresponding to
    the program function can be used, hypotheses are more concise and tend to be
    better suited for automated simplification by rewriting. Of course, there
    might be overheads to defining this logical function, but if it already
    exists in the library of our theorem prover, then the overhead is null. *)

(* ================================================================= *)
(** ** Small-Footprint Specifications for Array Operations *)

(** The large-footprint specifications presented above are sufficently
    expressive for verifying sequential programs manipulating arrays, but they
    are too limited for verifying a parallel program that concurrently updates
    two independent segments of an array. Indeed, even the verification of
    certain sequential programs can benefit from the use of smaller-footprint
    specifications, which require the ownership not of the whole array but only
    of a specific subset of the array cells.

    For example, the divide-and-conquer [quicksort] function sorts the elements
    in a given range of cells. Even though [quicksort] is not a concurrent
    function, using a small-footprint specification avoids the need to
    explicitly state the fact that cells of the array outside of the segment
    targeted by a recursive call remain unmodified.

    In what follows, we present small-footprint specifications for operating on
    individual cells and for operating on array segments, then present the proof
    of quicksort. *)

(** Small-footprint specifications are expressed using heap predicates for
    individual array and header cells.

    The heap predicate [hcell v p i] asserts that the cell at index [i] in the
    array [p] stores the value [v].

    Internally, as explained below, [hcell v p i] can be defined as
    [(p+1+i) ~~> v], with the [+1] corresponding to the header cell. *)

Parameter hcell : forall (v:val) (p:loc) (i:int), hprop.

(** The heap predicate [hheader n p] asserts that the header cell of the array
    at address [p] stores the length [n]. Internally, [hheader n p] can be
    defined as [p ~~> n]. *)

Parameter hheader : forall (n:int) (p:loc), hprop.

(** To read the length of an array, it is sufficient to provide the heap
    predicate associated with the header field of that array. In other words,
    there is no need to have the ownership of any cell of an array for reading
    its length. *)

Parameter triple_array_length_hheader : forall n p,
  triple (val_array_length p)
    (hheader n p)
    (fun r => \[r = (n:int)] \* hheader n p).

(** To read or write in a given array cell, it is sufficient to provide the
    [hcell] predicate associated with that cell. There is no need to own the
    header cell or other cells of the array. *)

Parameter triple_array_get_hcell : forall p i v,
  triple (val_array_get p i)
    (hcell v p i)
    (fun r => \[r = v] \* hcell v p i).

Parameter triple_array_set_hcell : forall p i v w,
  triple (val_array_set p i v)
    (hcell w p i)
    (fun _ => hcell v p i).

(** Note: technically, an ML runtime performs bound checks on [get] and [set]
    operations, to ensure that the indices provided fall within the array. These
    bound-checks operations do involve a read to the header field. Thus, it may
    appear that the header cell ought to be involved in the specification of
    [get] and [set]. However, providing the [hheader] predicate is not actually
    required for verifying the correctness a program. If one wanted to formally
    verify a _runtime system_, on the other hand, one would argue instead that
    headers are read-only cells, and that the access permissions over such cells
    can be "divided" among the client code and the runtime system. The
    realization of this "division" mechanism is based on the use of "fractional
    permissions", a Separation Logic concept that is just beyond the scope of
    the present course. *)

(* ================================================================= *)
(** ** Heap Predicate for Array Segments *)

(** So far, we have presented small-footprint specifications expressed in terms
    of [hheader] and [hcell]. But the creation of an array via
    [val_array_make n v] produces a heap predicate of the form [harray L p].
    Thus, it remains to explain how to convert an [harray] predicate into the
    separating conjunction of an [hheader] predicate and a set of [hcell]
    predicates. *)

(** The auxiliary predicate [hseg L p j] describes an "array segment": it
    describes the iterated separating conjunction of the predicate [hcell] over
    a set of consecutive cells starting at index [j], with elements described by
    the list [L]. For example, [hseg (x0::x1::x2::nil) p j] corresponds to
    [hcell x0 p (j+0) \* hcell x1 p (j+1) \* hcell x2 p (j+2)]. Internally, this
    corresponds to the cells at address [p+1+j], [p+2+j], and [p+3+j], skipping
    the header cell located at address [p+j]. *)

Fixpoint hseg (L:list val) (p:loc) (j:int) : hprop :=
  match L with
  | nil => \[]
  | x::L' => (hcell x p j) \* (hseg L' p (j+1))
  end.

(** If the list [L] is empty, then [hseg nil p j] is equivalent to the empty
    heap predicate. In particular, it does not assert that [j] is a valid index
    in the array. (The proofs of this lemma and the following one appear further
    in the file.) *)

Parameter hseg_nil : forall p j,
  hseg nil p j = \[].

(** If the list [L] is a singleton, then [hseg (v::nil) p j] is equivalent to
    [hcell v p j]. *)

Parameter hseg_one : forall v p j,
  hseg (v::nil) p j = hcell v p j.

(** A key result captures how a range of consecutive cells may be split in two
    parts. Concretely, a heap predicate describing a segment with elements
    [(L1++L2)] can be split into a predicate describing a first segment with
    elements [L1] and another predicate describing a second segment with
    elements [L2]. The two parts can be merged back into the original form at
    any time, as captured by the equality symbol in the statement below. *)

Parameter hseg_app : forall p j L1 L2,
    hseg (L1 ++ L2) p j
  = hseg L1 p j \* hseg L2 p (j + length L1).

(** For verifying programs, two corollaries are convenient. The lemma
    [hseg_cons] isolates the first cell of a segment, whereas the lemma
    [hseg_last] isolates the last cell of a segment. *)

Lemma hseg_cons : forall v p j L,
  hseg (v::L) p j = hcell v p j \* hseg L p (j+1).
Proof using. auto. Qed.

Lemma hseg_last : forall v p j L,
  hseg (L&v) p j = hseg L p j \* hcell v p (j+length L).
Proof using. intros. rewrite hseg_app. rewrite hseg_cons, hseg_nil. xsimpl. Qed.

(** These two corollaries themselves admit additional reformulations that help
    merge back the isolated head and tail cells. *)

(** Their statements do not constraint the offsets to be syntactically of the
    form [j + 1] or [j + length L1], but instead introduce arithmetic equalities
    that the tactic [math] can generally handle. *)

Lemma hseg_cons_r : forall L v p j1 j2,
  j2 = j1 + 1 ->
  hcell v p j1 \* hseg L p j2 ==> hseg (v::L) p j1.
Proof using. intros. subst. rewrite* hseg_cons. Qed.

Lemma hseg_app_r : forall p L1 L2 j1 j2,
  j2 = j1 + length L1 ->
  hseg L1 p j1 \* hseg L2 p j2 ==> hseg (L1 ++ L2) p j1.
Proof using. intros. subst. rewrite* hseg_app. Qed.

Lemma hseg_last_r : forall v p j L j',
  j' = (j+length L) ->
  hseg L p j \* hcell v p j' ==> hseg (L&v) p j.
Proof using. intros. subst. rewrite* hseg_last. Qed.

(* ================================================================= *)
(** ** Derived Segment-Based Specifications for Array Operations *)

(** For reasoning about programs that operate over array segments, such as
    [quicksort], it is convenient to specify the functions [make], [length],
    [get] and [set] exclusively in terms of [hheader] and [hseg]. The lemma
    [triple_array_length_header], already stated earlier, specifies [length] in
    terms of [hheader]. For the other operations, we consider the following
    derived specifications. *)

 Parameter triple_array_make_hseg : forall n v,
  n >= 0 ->
  triple (val_array_make n v)
    \[]
    (funloc p => hheader (abs n) p \* hseg (LibList.make (abs n) v) p 0).

Parameter triple_array_get_hseg : forall L p i j,
  0 <= i - j < length L ->
  triple (val_array_get p i)
    (hseg L p j)
    (fun r => \[r = LibList.nth (abs (i-j)) L] \* hseg L p j).

Parameter triple_array_set_hseg : forall L p i j v,
  0 <= i - j < length L ->
  triple (val_array_set p i v)
    (hseg L p j)
    (fun _ => hseg (LibList.update (abs (i-j)) v L) p j).

(* ================================================================= *)
(** ** Verification of the Safety of QuickSort *)

Module QuickSort.
Export NotationForVariables.

(** Let us illustrate the benefits of these segment-based specifications by
    reasoning about the divide-and-conquer [quicksort] function. For simplicity,
    let us consider an array that stores integer values. The implementation of
    quicksort is standard, using an auxiliary [pivot] function. The operation
    [pivot p i n] processes the segment of array [p] that starts at index [i]
    and is made of [n] elements. It first chooses an arbitrary element from that
    segment as pivot. It then reorders the elements from the segment, separating
    the values less than or equal to the pivot value from the values greater
    than the pivot value. It returns the index at which the pivot value ends up
    being stored in the segment.

    OCaml:

  let pivot p i n = ...
    (* [pivot] modifies an array [p], and returns the index [j] of a pivot
       value [x], with [j] in the range [i <= j < i+n], such that elements
       in the range [i .. j-1] are smaller than or equal to [x], and elements
       in the range [j+1 .. i+n-1] are greater than [x]. *)

  (* [quicksort] sorts an array [p] on the range of indices [i .. i+n-1]. *)
  let rec quicksort p i n =
    if n > 1 then begin
      let j = pivot p i n in
      let n1 = j - i in
      quicksort p i n1;
      quicksort p (j+1) (n-n1-1)
    end
*)

(** As a warm-up before establishing the full functional correctness of
    [quicksort], we begin by establishing its safety and termination. The core
    of this argument is proving that every array access is valid, through the
    use of array-segment specifications. The safety proof captures the essence
    of the ownership reasoning at play, including the framing process over
    recursive calls. In the "More Details" section, we generalize the proof to
    show that [quicksort] also correctly sorts its input array. *)

(** First, [pivot].

    Its safety specification asserts that [pivot p i n] operates on a range of
    size [n], starting at index [i] of the array [p]. This range is described in
    the precondition by a list [L], and in the postcondition by a list [L'].
    This list [L'] decomposes as [L1 ++ x :: L2], where [x] denotes the pivot
    value. *)

(** In the full correctness proof, we will further assert that [L1] contains
    only values smaller than [x] and [L2] only values at least as large as [x],
    but for establishing safety these assertions are not needed. *)

Parameter val_pivot : val.

Parameter triple_pivot_safety : forall p i n L,
  n = length L ->
  n >= 1 ->
  triple (val_pivot p i n)
    (hseg L p i)
    (fun r => \exists (j:int), \[r = val_int j] \*
              \exists (x:int) (L' L1 L2:list val), hseg L' p i \* \[
                  length L' = length L
               /\ L' = L1 ++ val_int x :: L2
               /\ j - i = length L1 ]).

(** Now, the recursive function [quicksort p i n] sorts an segment of length
    [n], starting at index [i], in the array [p]. *)

Definition val_quicksort : val :=
  <{ fix 'f 'p 'i 'n =>
       let 'b = 'n > 1 in
       if 'b then
         let 'j = val_pivot 'p 'i 'n in
         let 'n1 = 'j - 'i in
         'f 'p 'i 'n1;
         let 'i2 = 'j + 1 in
         let 'n3 = 'n - 'n1 in
         let 'n2 = 'n3 - 1 in
         'f 'p 'i2 'n2
       end }>.

(** **** Exercise: 4 stars, standard, especially useful (triple_quicksort_safety)

    Prove that [quicksort] operates on the targeted array segment without
    interfering with the other cells of the array. This property is captured by
    the specification shown below. Hint: use [xapp triple_pivot_safety] to
    reason about the call to [pivot]. *)

Lemma triple_quicksort_safety : forall p i n L,
  n = length L ->
  i >= 0 ->
  triple (val_quicksort p i n)
    (hseg L p i)
    (fun _ => \exists L', \[length L' = length L] \* hseg L' p i).
Proof using.
  introv Hn Hi. gen i L. induction_wf IH: (downto 0) n. intros.
 (* FILL IN HERE *) Admitted.

(** [] *)

(* ################################################################# *)
(** * More Details *)

(* ================================================================= *)
(** ** Formalization of Sorted Lists *)

Section SortedLists.

(** To refine the above safety proof into a functional correctness proof, we
    first need to formalize the notations of permutation and sortedness.

    The predicate [permut L L'] asserts that [L'] is a permutation of [L]. *)

Inductive permut (A:Type) : list A -> list A -> Prop :=
  | permut_mid : forall L1 L2 L3 L4,
      permut (L1 ++ L2 ++ L3 ++ L4) (L1 ++ L3 ++ L2 ++ L4)
  | permut_trans : forall L3 L1 L2,
      permut L1 L2 ->
      permut L2 L3 ->
      permut L1 L3.

(** The predicate [permut] is reflexive and symmetric. *)

Lemma permut_refl : forall A (L:list A),
  permut L L.
Proof using. intros. applys permut_mid (@nil A) (@nil A) (@nil A) L. Qed.

Lemma permut_sym : forall A (L1 L2: list A),
  permut L1 L2 ->
  permut L2 L1.
Proof using.
  introv M. induction M.
  { applys* permut_mid. }
  { applys* permut_trans IHM2. }
Qed.

#[local] Hint Resolve permut_refl.

(** If [L'] is a permutation of [L], then it has the same length as [L]. *)

Lemma permut_length : forall A (L L':list A),
  permut L L' ->
  length L = length L'.
Proof using. introv M. induction M; rew_list in *; try math. Qed.

(** If [L1'] is a permutation of [L1] and [L2'] is a permutation of [L2], then
    [L1' ++ L2'] is a permutation of [L1 ++ L2]. *)

Lemma permut_app : forall A (L1 L2 L1' L2':list A),
  permut L1 L1' ->
  permut L2 L2' ->
  permut (L1 ++ L2) (L1' ++ L2').
Proof using.
  introv M1 M2. applys permut_trans (L1' ++ L2).
  { clear M2. induction M1.
    { rew_list. applys permut_mid. }
    { applys* permut_trans IHM1_2. } }
  { clear M1. induction M2.
    { repeat rewrite <- (app_assoc L1'). applys permut_mid. }
    { applys* permut_trans IHM2_2. } }
Qed.

(** Useful corollaries for [cons] and [last]: *)

Lemma permut_cons : forall A (x:A) L1 L1',
  permut L1 L1' ->
  permut (x :: L1) (x :: L1').
Proof using. intros. applys* permut_app (x::nil) L1 (x::nil) L1'. Qed.

Lemma permut_last : forall A (x:A) L1 L1',
  permut L1 L1' ->
  permut (L1 & x) (L1' & x).
Proof using. intros. applys* permut_app L1 (x::nil) L1' (x::nil). Qed.

(** Swapping of consecutive elements or moving the first element to the last
    position yield valid permutations. *)

Lemma permut_swap_first_two : forall A (x y : A) (L:list A),
  permut (x :: y :: L) (y :: x :: L).
Proof using.
  intros. applys permut_mid (@nil A) (x::nil) (y::nil) L.
Qed.

Lemma permut_swap_first_last : forall A (x : A) (L:list A),
  permut (x::L) (L&x).
Proof using.
  intros. applys_eq (>> permut_mid (@nil A) (x::nil) L (@nil A)). rew_list*.
Qed.

(** If a property [P] holds for all elements of a list [L], it also holds for
    all the elements of any permutation of [L]. *)

Lemma permut_Forall : forall A (P:A->Prop) L L',
  Forall P L ->
  permut L L' ->
  Forall P L'.
Proof using.
  introv N M. gen N. induction M; intros; auto.
  { repeat rewrite Forall_app_eq in *. autos*. }
Qed.

(** The predicate [sorted L] asserts that [L] is a sorted list of integers. *)

Inductive sorted : list int -> Prop :=
  | sorted_nil :
     sorted nil
  | sorted_one : forall x,
     sorted (x :: nil)
  | sorted_cons : forall x y L,
     x <= y ->
     sorted (y :: L) ->
     sorted (x :: y :: L).

(** The proposition [list_of_gt x L] asserts that all elements in [L] are
    greater than [x]. Symmetrically, the proposition [list_of_le x L] asserts
    that all elements in [L] is no greater than [x]. *)

Definition list_of_gt (x:int) (L:list int) : Prop :=
  Forall (fun y => y > x) L.

Definition list_of_le (x:int) (L:list int) : Prop :=
  Forall (fun y => y <= x) L.

(** Two key lemmas for verifying sorting algorithms are stated below.

    First, if [L] is sorted, then adding an element [x] no greater than elements
    in [L] to the front of [L] yields a sorted list. *)

Lemma sorted_cons_gt : forall x L,
  list_of_gt x L ->
  sorted L ->
  sorted (x :: L).
Proof using.
  introv N M. destruct L as [|].
  { applys sorted_one. }
  { lets (Hv&_): Forall_cons_inv N. applys* sorted_cons. math. }
Qed.

(** Second, if [L1] is a sorted list, [x] is no less than the elements in [L1],
    and [x::L2] is a sorted list, then [L1 ++ x :: L2] is sorted. *)

Lemma sorted_app_le : forall x L1 L2,
  list_of_le x L1 ->
  sorted L1 ->
  sorted (x :: L2) ->
  sorted (L1 ++ x :: L2).
Proof using.
  introv N M1 M2. induction M1; rew_list in *. { auto. }
  { lets (Hv&_): Forall_cons_inv N. applys* sorted_cons. }
  { lets (_&N'): Forall_cons_inv N. applys* sorted_cons. }
Qed.

End SortedLists.

(* ================================================================= *)
(** ** Formalization of Arrays of Integer Values *)

(** To specify [quicksort] and other functions manipulating lists of integers,
    it is useful to introduce a conversion function [vals_int], which converts a
    list of integers (type [list int]) into a list of values (type [list val]).

    In particular, [hseg (vals_int L) p i] describes an array segment containing
    integer values. *)

Definition vals_int (L:list int) : list val :=
  LibList.map val_int L.

(** To ease the reasoning about [vals_int], we add the rewriting rules, stated
    below, to the tactics [rew_list] and [rew_listx]. These tactics perform
    normalization by means of Coq's [autorewrite] tactic. In an ideal world, we
    would use a single tactic [rew_list] to handle all rewriting rules related
    to lists. Unfortunately, [autorewrite] is undesirably slow when handling a
    large the data base of rewriting rules. The TLC library therefore relies on
    a 2-layer design: the tactic [rew_list] covers only the most frequently used
    rewriting rules, whereas the tactic [rew_listx] is slower but covers all
    rewriting rules. *)

Lemma vals_int_nil :
  vals_int nil = nil.
Proof using. intros. unfold vals_int. rew_listx*. Qed.

Lemma vals_int_cons : forall x L,
  vals_int (x :: L) = val_int x :: vals_int L.
Proof using. intros. unfold vals_int. rew_listx*. Qed.

Lemma vals_int_app : forall L1 L2,
  vals_int (L1 ++ L2) = vals_int L1 ++ vals_int L2.
Proof using. intros. unfold vals_int. rew_listx*. Qed.

Lemma vals_int_last : forall x L,
  vals_int (L & x) = vals_int L & val_int x.
Proof using. intros. unfold vals_int. rew_listx*. Qed.

Lemma length_vals_int : forall L,
  length (vals_int L) = length L.
Proof using. intros. unfold vals_int. rew_listx*. Qed.

#[export] Hint Rewrite vals_int_nil vals_int_cons vals_int_app
    vals_int_last length_vals_int : rew_list.
#[export] Hint Rewrite vals_int_nil vals_int_cons vals_int_app
    vals_int_last length_vals_int : rew_listx.

(* ================================================================= *)
(** ** Functional Correctness of Quicksort *)

(** In order to verify [quicksort], we need to refine the specification of the
    [pivot] function to include functional correctness properties.

    The postcondition of the pivot operation describes the elements in the
    segment as the list [L']. This list decomposes as [L1 ++ x :: L2], where [x]
    corresponds to the pivot. This time, the assertions [list_of_le x L1] and
    [list_of_gt x L2] are included. *)

Parameter triple_pivot : forall n p i L,
  n = length L ->
  n >= 1 ->
  triple (val_pivot p i n)
    (hseg (vals_int L) p i)
    (fun r => \exists j, \[r = val_int j] \*
              \exists x L' L1 L2, hseg (vals_int L') p i \* \[
                  permut L L'
               /\ L' = L1 ++ x :: L2
               /\ j - i = length L1
               /\ list_of_le x L1
               /\ list_of_gt x L2 ]).

(** **** Exercise: 5 stars, standard, optional (triple_quicksort)

    Prove that [quicksort] sorts the array segment targeted by its arguments.
    Hint: use [xapp triple_pivot]. *)

Lemma triple_quicksort : forall p i n L,
  n = length L ->
  i >= 0 ->
  triple (val_quicksort p i n)
    (hseg (vals_int L) p i)
    (fun _ => \exists L', \[permut L L' /\ sorted L']
                          \* hseg (vals_int L') p i).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** The function [quicksort_full p] sorts all the elements stored in the array
    at address [p]. *)

Definition val_quicksort_full : val :=
  <{ fun 'p =>
       let 'n = val_array_length 'p in
       val_quicksort 'p 0 'n }>.

(** The predicate [harray L p] is defined as the conjunction of
    [hheader (length L) p], which captures the fact that the header stores the
    length of the list [L], and of [hseg L p 0], which describes "full" array
    segment, ranging from the first to the last cell of the array. *)

Parameter harray_eq : forall p L,
  harray L p = \exists n, \[n = length L] \* hheader n p \* hseg L p 0.

(** **** Exercise: 2 stars, standard, optional (triple_quicksort_full)

    Prove that [val_quicksort_full] sorts an array. Hint: use [xchange] and
    [xchange <-] on [harray_eq] to convert between [harray] and [hseg]. *)

Lemma triple_quicksort_full : forall p L,
  triple (val_quicksort_full p)
    (harray (vals_int L) p)
    (fun _ => \exists L', \[permut L L' /\ sorted L']
              \* harray (vals_int L') p).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End QuickSort.

(* ================================================================= *)
(** ** Realization of [hheader] and [hcell] *)

Module Realization.

(** So far, the predicates [hheader] and [hcell] were axiomatized. Let us show
    how they can be realized with respect to the concrete representation of the
    memory state, of type [heap]. The predicates [hseg] and [harray] can then be
    defined on top of [hheader] and [hcell].

    Following the standard memory layout of allocated blocks in ML programs, we
    represent ML-style array of size [n] as a memory block of size [n+1]. The
    first cell, called the "header cell", stores the length of the array. The
    remaining cells store the elements from the array.

    The heap predicate [hheader n p] describes a cell at location [p] with
    contents [n]. Recall that the definition of [hheader] is opaque when
    reasoning about array-using programs, so there is no risk that the
    programmer attempts to reason about code that modifies header fields. *)

Definition hheader (n:int) (p:loc) : hprop :=
  p ~~> (val_int n).

(** Because Coq's [fold] operation rarely applys as the user expects, we state a
    lemma that reformulates the definition of [hheader] as an equality.
    Performing a [rewrite] using this lemma corresponds either to an [unfold] or
    to a [fold] operation, depending on the direction. More generally,
    reformulating a definition as an equality is strongly recommended for every
    representation predicate. *)

Lemma hheader_eq : forall p n,
  (hheader n p) = (p ~~> (val_int n)).
Proof using. auto. Qed.

(** The predicate [hcell v p i] asserts that the cell at index [i] from the
    array at address [p] stores the value [p]. We defined this predicate
    informally by asserting that the cell in memory at address [p+1+i] stores
    the value [v]. Thus, as first approximation, the predicate [hcell v p i]
    could be defined as [(p + 1 + abs i) ~~> v]. The actual definition also
    embeds the assertion [i >= 0] to guarantee that [i] refers to a valid index
    and [p + 1 + abs i] computes the expected offset. *)

Definition hcell (v:val) (p:loc) (i:int) : hprop :=
  ((p + 1 + abs i)%nat ~~> v) \* \[i >= 0].

(** The following lemma is useful for folding or unfolding the definition. *)

Lemma hcell_eq : forall v p i,
  (hcell v p i) = ((p + 1 + abs i)%nat ~~> v) \* \[i >= 0].
Proof using. auto. Qed.

(** This one extracts the property [i >= 0] from [hcell v p i] . *)

Lemma hcell_nonneg : forall v p i,
  hcell v p i ==> hcell v p i \* \[i >= 0].
Proof using. unfold hcell. xsimpl*. Qed.

(* ================================================================= *)
(** ** Realization of [hseg] and [harray] *)

(** The heap predicate [hseg] for array segments can be defined in terms of
    [hcell] as suggested earlier. *)

Fixpoint hseg (L:list val) (p:loc) (j:int) : hprop :=
  match L with
  | nil => \[]
  | x::L' => (hcell x p j) \* (hseg L' p (j+1))
  end.

(** The predicate for full arrays, [harray], can be defined as the pair of an
    [hheader] predicate describing the header cell and a [hseg] covering the
    full contents of the array. *)

Definition harray (L:list val) (p:loc) : hprop :=
  hheader (length L) p \* hseg L p 0.

(** The lemma [harray_eq] can be used for folding or unfolding [harray]. *)

Lemma harray_eq : forall p L,
  harray L p = \exists n, \[n = length L] \* hheader n p \* hseg L p 0.
Proof using. unfold harray. xsimpl*. { intros; subst*. } Qed.

(** When proving properties about [hseg L p j], one frequently faces a mismatch
    between [hseg L p j1] and [hseg L p j2], where [j1] and [j2] are provably
    equal yet do not unify. To avoid cluttering proofs, the following lemma and
    associated hint are very useful. *)

Lemma hseg_start_eq : forall L p j1 j2,
  j1 = j2 ->
  hseg L p j1 ==> hseg L p j2.
Proof using. intros. subst*. Qed.

#[local] Hint Extern 1 (hseg ?L ?p ?j1 ==> hseg ?L ?p ?j2) =>
  apply hseg_start_eq; math.

(** We now prove the lemmas [hseg_nil] and [hseg_one] and [hseg_cons], which we
    presented and used earlier in the chapter. *)

Lemma hseg_nil : forall p j,
  hseg nil p j = \[].
Proof using. auto. Qed.

Lemma hseg_one : forall v p j,
  hseg (v::nil) p j = hcell v p j.
Proof using. intros. simpl. xsimpl*. Qed.

Lemma hseg_cons : forall v p j L,
  hseg (v::L) p j = hcell v p j \* hseg L p (j+1).
Proof using. intros. simpl. xsimpl*. Qed.

(** **** Exercise: 3 stars, standard, especially useful (hseg_app)

    Prove the splitting lemma for array segments. Hint: [rew_list] is helpful
    for simplifying list operations. Recall that [xsimpl] helps proving
    equalities on [hprop]. *)

Lemma hseg_app : forall L1 L2 p j,
    hseg (L1 ++ L2) p j
  = hseg L1 p j \* hseg L2 p (j + length L1).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Focus Lemmas for Array Segments *)

(** With a predicate [harray L p] at hand, it may be useful to isolate the cell
    at an index [i], that is, to extract the predicate [hcell v p i], where
    [0 <= i < length L] and [v = LibList.nth (abs i) L]. By "giving back" the
    predicate [hcell v p i], we can get back to the original predicate
    [harray L p]. *)

Parameter harray_focus_read' : forall i L p,
  0 <= i < length L ->
      harray L p
  ==> let v := LibList.nth (abs i) L in
      (hcell v p i) \* (hcell v p i \-* harray L p).

(** The lemma above, called a "focus" lemma or "borrowing" lemma in Rust's
    terminology, only supports reading into the "focused" cell at index [i]; it
    does not allow modifying the contents of the cell. Indeed, if [hcell v p i]
    is updated to [hcell w p i], then the magic wand
    [hcell v p i \-* harray L p] can no longer be exploited.

    Fortunately, it is straightforward to generalize the focus lemma into a form
    that supports updates. The general focus lemma shown below makes use of a
    universal quantification over the value [w] that the cell [i] may contain
    after potential update operations. *)

Parameter harray_focus' : forall i L p,
  0 <= i < length L ->
      harray L p
  ==> let v := LibList.nth (abs i) L in
         (hcell v p i)
      \* (\forall w, hcell w p i \-* harray (LibList.update (abs i) w L) p).

(** The focus lemmas are critically useful. Without them, we would need to
    repeat a number of tedious splitting and merging steps. *)

(** **** Exercise: 4 stars, standard, especially useful (hseg_focus)

    Prove the following focus lemma for array _segments_. Hint: although a proof
    by induction is possible, a simpler proof can be achieved by exploiting
    [LibList.list_middle_inv], [LibList.nth_middle] and [LibList.update_middle].
    Also, recall that lemma [Inhab_val] proves [Inhab val]. *)

Lemma hseg_focus_relative : forall (k:nat) L p j,
  0 <= k < length L ->
      hseg L p j
  ==> let v := LibList.nth k L in
         hcell v p (j+k)
      \* (\forall w, hcell w p (j+k) \-* hseg (LibList.update k w L) p j).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

Arguments hseg_focus_relative : clear implicits.

(** In the statement above, [k] is an index relative to the start of the
    segment. The focus lemma can also be expressed in terms of absolute indices.
    Below, [i] denotes a valid array index within the targeted segment. *)

Lemma hseg_focus : forall i L p j,
  0 <= i-j < length L ->
      hseg L p j
  ==> let v := LibList.nth (abs (i-j)) L in
         hcell v p i
      \* (\forall w, hcell w p i \-* hseg (LibList.update (abs (i-j)) w L) p j).
Proof using.
  introv Hk. xchange (hseg_focus_relative (abs (i-j))). { math. }
  math_rewrite (j + abs (i - j) = i). xsimpl.
Qed.

Arguments hseg_focus : clear implicits.

(** We can derive the final focus lemma for [harray] from the one for [hseg]. *)

Lemma harray_focus : forall i L p,
  0 <= i < length L ->
      harray L p
  ==> let v := LibList.nth (abs i) L in
         hcell v p i
      \* (\forall w, hcell w p i \-* harray (LibList.update (abs i) w L) p).
Proof using.
  introv Hi. unfold harray. xchange (hseg_focus i). { math. }
  math_rewrite (i - 0 = i). xsimpl. intros w.
  xchange (hforall_specialize w). xsimpl.
  rewrite* LibList.length_update.
Qed.

Arguments harray_focus : clear implicits.

(** **** Exercise: 3 stars, standard, optional (harray_focus_read)

    Prove that the "focus-read" lemma is a direct consequence of the general
    version of the focus lemma [harray_focus]. Hint: use
    [LibList.update_nth_same]. *)

Lemma harray_focus_read : forall i L p,
  0 <= i < length L ->
      harray L p
  ==> let v := LibList.nth (abs i) L in
      hcell v p i \* (hcell v p i \-* harray L p).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

Arguments harray_focus_read : clear implicits.

(* ################################################################# *)
(** * Optional Material *)

(** In this section, we show how to implement array operations in terms of
    lower-level primitive operations such as block allocation and pointer
    arithmetic. *)

(* ================================================================= *)
(** ** Semantics of Pointer Arithmetic *)

(** The operation [val_ptr_add p n] applies to a pointer [p] and an integer [n],
    and returns the address [p+n]. In other words, it computes the address of
    the [n]-th cell past the cell at location [p]. We assume [val_ptr_add] to be
    a primitive of the language. *)

Parameter val_ptr_add : prim.

(** The evaluation rule and the general specification for pointer addition are
    shown below. They both require [p+n] to be a nonnegative integer. *)

Parameter eval_ptr_add : forall p n s Q,
  p + n >= 0 ->
  Q (val_loc (abs (p + n))) s ->
  eval s (val_ptr_add (val_loc p) (val_int n)) Q.

Lemma triple_ptr_add : forall (p:loc) (n:int),
  p + n >= 0 ->
  triple (val_ptr_add p n)
    \[]
    (fun r => \[r = val_loc (abs (p + n))]).
Proof using.
  introv R Hs. applys* eval_ptr_add. lets ->: hempty_inv Hs.
  applys hpure_intro. auto.
Qed.

(** For the [math] tactic provided by the TLC library to behave well on goals
    involving expressions of the form [p+n] involved in calls to [val_ptr_add],
    we need a small tweak. We instantiate a hook of the [math] tactic to
    registier [loc] as transparent type for this tactic. *)

Ltac is_additional_arith_type T ::=
  match T with
  | loc => constr:(true)
  end.

(** For the purpose of this course, we only need to shift pointers by a
    nonnegative number of cells. We show below a simplified specification
    featuring the premise [n >= 0] instead of [p+n >= 0]. *)

Lemma triple_ptr_add_nonneg : forall (p:loc) (n:int),
  n >= 0 ->
  triple (val_ptr_add p n)
    \[]
    (fun r => \[r = val_loc (p + abs n)%nat]).
Proof using.
  introv Hn. applys triple_conseq triple_ptr_add.
  { math. } { xsimpl. } { xsimpl. intros ? ->. fequal. math. }
Qed.

#[export]Hint Resolve triple_ptr_add_nonneg : triple.

(* ================================================================= *)
(** ** Semantics of Low-Level Block Allocation *)

(** The operation [val_alloc n] allocates a block of [n] consecutive cells.
    Starting from a state [sa], it produces a state described as the union of
    [sb] and [sa], where [sb] consists of consecutive of [n] consecutive cells.
    In the evaluation rule shown below, [Fmap.conseq ... p] builds a state with
    a range of cells starting a location [p] and with contents described by the
    list [L]. Each of these cells is specified as having the special value
    [val_uninit] as contents. *)

Parameter val_alloc : val.

Parameter eval_alloc : forall n sa Q,
  n >= 0 ->
  (forall p sb,
    sb = Fmap.conseq (LibList.make (abs n) val_uninit) p ->
    p <> null ->
    Fmap.disjoint sa sb ->
    Q (val_loc p) (sb \u sa)) ->
  eval sa (val_alloc (val_int n)) Q.

(** The specification of [val_alloc] is expressed using the heap predicate
    [hrange L p] to describe a range of consecutive cells -- a heap produced by
    [Fmap.conseq L p]. The structure of the recursive definition of [hrange]
    resembles that of [hseg]. *)

Fixpoint hrange (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[]
  | x::L' => (p ~~> x) \* (hrange L' (p+1)%nat)
  end.

Lemma hrange_intro : forall L p,
  (hrange L p) (Fmap.conseq L p).
Proof using.
  intros L. induction L as [|L']; intros; rew_listx.
  { applys hempty_intro. }
  { simpl. applys hstar_intro.
    { applys* hsingle_intro. }
    { applys IHL. }
    { applys Fmap.disjoint_single_conseq. left. math. } }
Qed.

(** The allocation operation [val_alloc] is then specified as producing a heap
    described using [hrange] for a list of uninitialized values. Note: in ML,
    uninitialized values are never exposed to the programmer; [val_alloc] is
    only meant to be invoked internally by the runtime system. *)

Lemma triple_alloc : forall n,
  n >= 0 ->
  triple (val_alloc n)
    \[]
    (funloc p => hrange (LibList.make (abs n) val_uninit) p \* \[p <> null]).
Proof using.
  introv Hn Hsa. applys* eval_alloc. intros p sb Esb Hp D.
  lets ->: hempty_inv Hsa. applys hexists_intro p.
  rewrite hstar_hpure_l. split*. rewrite Fmap.union_empty_r.
  rewrite hstar_hpure_r. split*. subst sb. applys* hrange_intro.
Qed.

#[export]Hint Resolve triple_alloc : triple.

(* ================================================================= *)
(** ** Low-Level Implementation of Arrays *)

(** We are now ready to explain how a runtime system could implement the
    operations [length], [get], [set], and [make] on arrays, in terms of
    [val_alloc] and [val_ptr_add] for allocating memory blocks and computing
    pointer offsets, as well as [val_get] and [val_set] for reading and writing
    into individual memory cells. *)

Import NotationForVariables.

(** The operation that obtains the [length] of an array is implemented by
    reading the integer stored into the header field of that array. *)

Definition val_array_length : val :=
  <{ fun 'p => val_get 'p }>.

(** The operation that reads into an array cell, written [val_array_get p i], is
    implemented as a read at the location [p + 1 + abs i]. *)

Definition val_array_get : val :=
  <{ fun 'p 'i =>
       let 'p1 = val_ptr_add 'p 1 in
       let 'q = val_ptr_add 'p1 'i in
       val_get 'q }>.

(** The operation that reads into an array cell, written [val_array_set p i v],
    is implemented as a write of [v] at the location [p + 1 + abs i]. *)

Definition val_array_set : val :=
  <{ fun 'p 'i 'v =>
       let 'p1 = val_ptr_add 'p 1 in
       let 'q = val_ptr_add 'p1 'i in
       val_set 'q 'v }>.

(** The auxiliary function [fill] is used to implement [make]. The operation
    [fill p i n v] fills the range of the array [p], starting at index [i], with
    [n] copies of the value [v]. The code below provides a naive recursive
    implementation of [fill]. *)

Definition val_array_fill : val :=
  <{ fix 'f 'p 'i 'n 'v =>
       let 'b = 'n > 0 in
       if 'b then
         val_array_set 'p 'i 'v;
         let 'm = 'n - 1 in
         let 'j = 'i + 1 in
         'f 'p 'j 'm 'v
       end }>.

(** The operation [val_array_make n v] creates an array of length [n] filled
    with copies of the value [v]. It is implemented as the allocation of a block
    of length [n+1] at a fresh address [p], followed by the write of the value
    [n] in the header, and with a call to [fill p 0 n v] for filling the [n]
    cells of the array [p] with copies of the value [v]. *)

Definition val_array_make : val :=
  <{ fun 'n 'v =>
       let 'm = 'n + 1 in
       let 'p = val_alloc 'm in
       val_set 'p 'n;
       val_array_fill 'p 0 'n 'v;
       'p }>.

(* ================================================================= *)
(** ** Verification of Low-Level Operations for Arrays *)

(** Now we can prove that the implementations presented above for [length],
    [get], [set], and [make] indeed satisfy the specifications axiomatized for
    them earlier in this chapter. For these proofs, we need to set the
    definition of [hheader] as transparent. *)

Global Transparent hheader.

(** We also add a hint for [xapp], to automatically handle the arithmetic
    preconditions arising from calls to [val_ptr_add] and [val_alloc]. *)

#[local] Hint Extern 1 (_ >= _) => math : triple.

(** Moreover, we customize the behavior of the "*" suffix that appears in next
    to Coq tactics, for this symbol to trigger not a call to [eauto] but instead
    a call to [eauto with maths]. *)

Local Ltac auto_star ::= eauto with maths.

(** Here are the proofs for the small-footprint specifications. *)

Lemma triple_array_length_hheader : forall n p,
  triple (val_array_length p)
    (hheader n p)
    (fun r => \[r = n] \* hheader n p).
Proof using. xwp. unfold hheader. xapp. xsimpl*. Qed.

Lemma triple_array_get_hcell : forall v p i,
  triple (val_array_get p i)
    (hcell v p i)
    (fun r => \[r = v] \* hcell v p i).
Proof using.
  xwp. unfold hcell. xpull. intros Hi. xapp. xapp. xapp. xsimpl*.
Qed.

Lemma triple_array_set_hcell : forall p i v w,
  triple (val_array_set p i v)
    (hcell w p i)
    (fun _ => hcell v p i).
Proof using.
  xwp. unfold hcell. xpull. intros Hi. xapp. xapp. xapp. xsimpl*.
Qed.

(** Then, the proofs of specifications operating on array segments ([hseg]). *)

Lemma triple_array_get_hseg : forall L p i j,
  0 <= i - j < length L ->
  triple (val_array_get p i)
    (hseg L p j)
    (fun r => \[r = LibList.nth (abs (i-j)) L] \* hseg L p j).
Proof using.
  introv M. xtriple. xchange* (hseg_focus i).
  xapp triple_array_get_hcell.
  xchange (hforall_specialize (nth (abs (i - j)) L)).
  rewrite* update_nth_same. { xsimpl*. }
Qed.

Lemma triple_array_set_hseg : forall L p i j v,
  0 <= i - j < length L ->
  triple (val_array_set p i v)
    (hseg L p j)
    (fun _ => hseg (LibList.update (abs (i-j)) v L) p j).
Proof using.
  introv M. xtriple. xchange* (hseg_focus i).
  xapp triple_array_set_hcell. xchange (hforall_specialize v).
Qed.

Lemma hseg_eq_hrange : forall L p,
  hseg L p 0 = hrange L (p+1)%nat.
Proof using.
  asserts M: (forall L (k:nat) p, hseg L p k = hrange L (p+1+k)%nat).
  { intros L. induction L; intros; simpl.
    { auto. }
    { math_rewrite (p + 1 + k + 1 = p + 1 + (k + 1))%nat.
      rewrite <- IHL. unfold hcell. xsimpl.
      { intros _. applys himpl_of_eq; fequals_rec; math. }
      { math. }
      { applys himpl_of_eq; fequals_rec; math. } } }
  intros. rewrite (M L 0%nat). fequals. math.
Qed.

Lemma triple_array_fill : forall n L p i v,
  n = length L ->
  triple (val_array_fill p i n v)
    (hseg L p i)
    (fun _ => hseg (LibList.make (abs n) v) p i).
Proof using.
  intros n. induction_wf IH: (downto 0) n.
  introv Hn. xwp. xapp. xif; intros C.
  { xapp triple_array_set_hseg. { math. }
    math_rewrite (abs (i - i) = 0%nat).
   destruct L as [|x L']; rew_list in *. { false. math. }
   rew_listx. xchange hseg_cons. xapp. xapp.
    xapp; try math. xchange <- hseg_cons.
    rewrites* (>> LibList.make_pos (abs n) v).
    math_rewrite* (abs (n-1) = abs n - 1)%nat. }
  { xval. math_rewrite (n = 0) in *.
    destruct L; rew_listx in *; tryfalse. auto. }
Qed.

Lemma triple_array_make_hseg : forall n v,
  n >= 0 ->
  triple (val_array_make n v)
    \[]
    (funloc p => hheader (abs n) p \* hseg (LibList.make (abs n) v) p 0).
Proof using.
  introv Hn. xwp. xapp. xapp. intros q Hq.
  math_rewrite (abs (n+1) = S (abs n)). rew_listx. simpl.
  xapp. xchange* <- (hheader_eq q). xchange <- hseg_eq_hrange.
  xapp triple_array_fill. rew_listx*. xval. xsimpl*.
  applys himpl_of_eq; fequals_rec; math.
Qed.

(** Finally, the proofs of specifications expressed in terms of [harray]. *)

Lemma triple_array_get : forall L p i,
  0 <= i < length L ->
  triple (val_array_get p i)
    (harray L p)
    (fun r => \[r = LibList.nth (abs i) L] \* harray L p).
Proof using.
  introv M. xtriple. unfold harray. xapp triple_array_get_hseg. { math. }
  math_rewrite (i - 0 = i). xsimpl*.
Qed.

Lemma triple_array_set : forall L p i v,
  0 <= i < length L ->
  triple (val_array_set p i v)
    (harray L p)
    (fun _ => harray (LibList.update (abs i) v L) p).
Proof using.
  introv M. xtriple. unfold harray. xapp triple_array_set_hseg. { math. }
  math_rewrite (i - 0 = i). rew_listx. xsimpl*.
Qed.

Lemma triple_array_length : forall L p,
  triple (val_array_length p)
    (harray L p)
    (fun r => \[r = length L] \* harray L p).
Proof using.
  intros. xtriple. unfold harray. xapp triple_array_length_hheader. xsimpl*.
Qed.

Lemma triple_array_make : forall n v,
  n >= 0 ->
  triple (val_array_make n v)
    \[]
    (funloc p => harray (LibList.make (abs n) v) p).
Proof using.
  intros. xtriple. unfold harray. xapp triple_array_make_hseg. { math. }
  rew_listx. xsimpl*.
Qed.

End Realization.

(* ################################################################# *)
(** * Appendix *)

(* ================================================================= *)
(** ** Verification of the Pivot Function *)

Module Pivot.
Import QuickSort.
Local Ltac auto_star ::= eauto with maths.

(** For completeness, we include the formal verification of the [pivot]
    function. The proof is unfortunately rather cluttered with reasoning about
    the [vals_int] conversion function. The need for it stems from the fact that
    we are reasoning on untyped code. The actual CFML tool provides reasoning
    rule for well-typed code, and is thereby avoids all this kind of clutter.

    We consider a simple, unoptimized implementation of the [pivot] function.
    This implementation is recursive and performs a series of [swap] operations.

OCaml:

   let swap =
    fun p j1 j2 ->
      let x1 = p.(j1) in
      let x2 = p.(j2) in
      p.(j1) <- x2;
      p.(j2) <- x1

  let pivot p i n =
    if n < 2 then i else begin
      let j = i+1 in
      let x = p.(i) in
      let y = p.(j) in
      if y <= x then begin
        swap p i j;
        pivot p j (n-1);
      end else begin
        swap p j k;
        pivot p i (n-1)
      end
*)

Definition val_array_swap : val :=
  <{ fun 'p 'j1 'j2 =>
      let 'x1 = val_array_get 'p 'j1 in
      let 'x2 = val_array_get 'p 'j2 in
      val_array_set 'p 'j1 'x2;
      val_array_set 'p 'j2 'x1 }>.

Definition val_pivot : val :=
  <{ fix 'f 'p 'i 'n =>
       let 'b = 'n < 2 in
       if 'b then
         'i
       else
         let 'x = val_array_get 'p 'i in
         let 'j = 'i + 1 in
         let 'y = val_array_get 'p 'j in
         let 'm = 'n - 1 in
         let 'c = 'y <= 'x in
         if 'c then
           val_array_swap 'p 'i 'j;
           'f 'p 'j 'm
         else
           let 'k = 'i + 'm in
           val_array_swap 'p 'j 'k;
           'f 'p 'i 'm }>.

(** We first state a specialized version of [array_get] for array segments
    storing integer values. *)

Lemma triple_array_get_hseg_vals_int : forall (L:list int) p i j,
  0 <= i - j < length L ->
  triple (val_array_get p i)
    (hseg (vals_int L) p j)
    (fun r => \[r = LibList.nth (abs (i-j)) L] \* hseg (vals_int L) p j).
Proof using.
  introv M. xtriple. xapp triple_array_get_hseg. { rew_list. math. }
  xsimpl. unfolds vals_int. rewrite nth_map.   fequals. math.
Qed.

(** Next, we verify the [swap] function, which permutes elements at two indices
    inside a given array segment. *)

Lemma triple_array_swap_seg : forall p i j1 j2 (L:list val),
  0 <= j1-i < length L ->
  0 <= j2-i < length L ->
  triple (val_array_swap p j1 j2)
    (hseg L p i)
    (fun _ =>
      hseg (LibList.update (abs (j2-i)) (LibList.nth (abs (j1-i)) L)
           (LibList.update (abs (j1-i)) (LibList.nth (abs (j2-i)) L) L)) p i).
Proof using.
  introv Hj1 Hj2. xwp.
  xapp triple_array_get_hseg. { math. }
  xapp triple_array_get_hseg. { math. }
  xapp triple_array_set_hseg. { math. }
  xapp triple_array_set_hseg. { rew_listx. math. } xsimpl.
Qed.

(** We derive a specification for [swap] specialized for the case where the
    elements appear in array segments. *)

Lemma triple_array_swap_seg_lists : forall L1 L2 L3 x y p i j1 j2,
  j1 = i + length L1 ->
  j2 = i + length L1 + 1 + length L2 ->
  triple (val_array_swap p j1 j2)
    (hseg (L1 ++ x :: L2 ++ y :: L3) p i)
    (fun _ => hseg (L1 ++ y :: L2 ++ x :: L3) p i).
Proof using.
  hint Inhab_val. introv H1 H2. xapp triple_array_swap_seg; rew_list*.
  applys himpl_of_eq. fequal.
  math_rewrite (abs (j1 - i) = length L1).
  math_rewrite (abs (j2 - i) = (length L1 + 1 + length L2)%nat).
  rewrite nth_middle; [|rew_list*].
  asserts_rewrite (L1 ++ x :: L2 ++ y :: L3 = (L1 ++ x :: L2) ++ y :: L3).
  { rew_list*. }
  rewrite nth_middle; [|rew_list*]. rew_list.
  rewrite* update_middle.
  asserts_rewrite (L1 & y ++ L2 ++ y :: L3 = (L1 & y ++ L2) ++ y :: L3).
  { rew_list*. }
  rewrite* update_middle; rew_list*.
Qed.

(** We also derive a specification for [swap] specialized for the case where it
    permutes an element with itself. *)

Lemma triple_array_swap_seg_self : forall L p i j1 j2,
  0 <= j1 - i < length L ->
  j2 = j1 ->
  triple (val_array_swap p j1 j2)
    (hseg L p i)
    (fun _ => hseg L p i).
Proof using.
  introv H1 ->. xapp* triple_array_swap_seg.
  do 2 rewrite* LibList.update_nth_same.
Qed.

(** We are now ready to prove the [pivot] function. For the recursion, we need
    to furthermore assert in the postcondition that the pivot value [x] is, at
    each recursive call, located at the head of the segment on which the
    recursive call is performed. This property is captured by the additional
    assertion [x = LibList.nth 0%nat L]. This assertion was not needed for the
    verification of [quicksort]. *)

Lemma triple_pivot' : forall n p i L,
  n = length L ->
  n >= 1 ->
  triple (val_pivot p i n)
    (hseg (vals_int L) p i)
    (fun r => \exists j, \[r = val_int j] \*
              \exists x L' L1 L2, hseg (vals_int L') p i \* \[
                  permut L L'
               /\ x = LibList.nth 0%nat L
               /\ L' = L1 ++ x :: L2
               /\ j - i = length L1
               /\ list_of_le x L1
               /\ list_of_gt x L2 ]).
Proof using.
  intros n. induction_wf IH: (downto 0) n; introv HL Hn. xwp.
  xapp. xif; intros C.
  { xval. xsimpl (>> i (LibList.nth 0%nat L) L (@nil int) (@nil int)).
    { auto. }
    { destruct L as [|x [|]]; rew_list in *; try (false; math). splits.
      { applys permut_refl. }
      { rew_listx*. }
      { rew_listx*. }
      { math. }
      { applys Forall_nil. }
      { applys Forall_nil. } } }
  { xapp* triple_array_get_hseg_vals_int.
    xapp. xapp* triple_array_get_hseg_vals_int.
    xapp. xapp.
    math_rewrite (abs (i - i) = 0%nat).
    math_rewrite (abs (i + 1 - i) = 1%nat).
    lets* (x&L'&->): length_pos_inv_cons L. rew_list in *.
    lets* (y&L''&->): length_pos_inv_cons L'. rew_listx.
    xif; intros C'.
    { xapp (>> triple_array_swap_seg_lists
             (@nil val) (@nil val) (vals_int L'')); rew_list*.
      xchange hseg_cons. rew_list in *. xapp (>> IH (x::L'')); rew_list*.
      intros j' x' L' L1' L2' (HP&Hx&HE&Hji&Hle&Hgt). rew_listx in Hx. subst x'.
      xchange <- hseg_cons. xsimpl* (>> j' x (y::L') (y::L1') L2'). splits.
      { subst L'. applys permut_trans. applys permut_swap_first_two.
        applys* permut_cons. }
      { subst L'. rew_list*. }
      { subst L'. rew_list*. }
      { rew_list*. }
      { applys* Forall_cons. }
      { auto. } }
    { xapp. tests Cend: (L'' = nil).
      { rew_listx in *. xapp triple_array_swap_seg_self; rew_list*.
        change (val_int x::val_int y::nil) with ((val_int x::nil) & val_int y).
        xchange hseg_last. xapp (>> IH (x::nil)); rew_list*.
        intros j' L' x' L1' L2' (HP&Hx&HE&Hji&Hle&Hgt).
        lets HEQ: permut_length HP. subst L'. subst x'. rew_list in *.
        asserts ->: (L1' = nil). applys* length_zero_inv.
        asserts ->: (L2' = nil). applys* length_zero_inv.
        xchange hseg_last_r. { rew_listx. math. } rew_listx.
        xsimpl* (>> j' x (x::y::nil) (@nil int) (y::nil)); rew_listx. splits*.
        { applys permut_refl. }
        { applys* Forall_cons. } }
      { lets* (z&L'''&->): list_neq_nil_inv_last L''. rew_listx in *.
         xapp (>> triple_array_swap_seg_lists (val_int x :: nil)
          (vals_int L''') (@nil val) y z); rew_list*.
         replace (val_int x :: val_int z :: vals_int L''' & val_int y)
           with ((val_int x :: val_int z :: vals_int L''') & val_int y);
           [|rew_list*].
         xchange hseg_last.
         xapp (>> IH (x::z::L''')); rew_list*.
         intros j' x' L' L1' L2' (HP&Hx&HE&Hji&Hle&Hgt).
         lets HEQ: permut_length HP. rew_listx in *. subst x'.
         xchange hseg_last_r. { rew_list*. }
         xsimpl* (>> j' x (L1' ++ x :: L2' & y) L1' (L2'&y)). splits*.
         { subst L'. applys permut_trans. applys permut_swap_first_two.
           applys permut_trans. applys permut_swap_first_last.
           asserts_rewrite (L1' ++ x :: L2' & y = (L1' ++ x :: L2') & y).
           { rew_list*. }
           applys permut_last. applys permut_trans HP. applys permut_cons.
           applys permut_sym. applys permut_swap_first_last. }
         { subst L'. applys* Forall_last. }
         { subst L'. rew_listx*. } } } }
Qed.

(** As mentioned earlier, the proof is longer than we would like it to be. (It
    would be much simpler in the CFML tool, where invariants need not mention
    the [vals_int] conversion function.) *)

End Pivot.

(* 2024-12-26 10:22 *)
