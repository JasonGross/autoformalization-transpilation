(** * Spec_stdlib: Specification of external malloc, free, exit functions *)

(* ################################################################# *)
(** * Abstract Predicate Definition *)

Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import VC.stdlib.

(** In the first view chapters of this volume ([Verif_stack],
  [Verif_triang], etc.) we demonstrated all-in-one-file C programs,
  and we used a form of [malloc_token] with the type, *)

Require VST.floyd.library.  (* Only needed for the next line *)
About VST.floyd.library.malloc_token.
(*  library.malloc_token : compspecs -> share -> type -> val -> mpred
    Arguments library.malloc_token {cs}    

    That is, [malloc_token] takes an implicit compspecs argument,
   and the interpretation of the [type] argument depends on the
   compspecs.  Basically, the [malloc_token] needs to know how many
   bytes the malloc'd record is, so it needs the compspecs in order
   to interpret the type.
       But now we are doing _modular_ C programming, in which each .c file
   can have its own struct and union types -- that is, its own compspecs.
   Our [malloc_token] with a compspecs parameter cannot assume that
   every module will have the same compspecs.  For modular programming,
   we'll start with a more primitive form,  [malloc_token_sz], that just 
   depends on the _size_ of the object, of type [Z].  No compspecs required.
      Later in this file, we show how to recover the type-based
   [malloc_token] _within_ each module.

   In the memory-manager APD we have two abstract predicates, [mem_mgr]
   and [malloc_token].  The predicate [mem_mgr] represents the state
   of the memory manager's free list.  That is, when you call [free(p)]
    you might imagine that the memory-block at address p gets
    added back into a free list (or some other data structure), and
    when you call [malloc(n)] then it takes a block from the free list.
    Since the internal representation of the free list is private to
     this module ([stdlib]), it's an abstract predicate.

*)

Record MallocFreeAPD := {
   mem_mgr: globals -> mpred;
   malloc_token_sz: share -> Z -> val -> mpred;
   malloc_token_sz_valid_pointer: forall sh sz p, 
      sz <= 0 -> malloc_token_sz sh sz p |-- valid_pointer p;
   malloc_token_sz_local_facts:  forall sh sz p, 
      malloc_token_sz sh sz p |-- !! malloc_compatible sz p
}.

#[export] Hint Resolve malloc_token_sz_valid_pointer : valid_pointer.
#[export] Hint Resolve malloc_token_sz_local_facts : saturate_local.

(* ################################################################# *)
(** * Abstract Specification Interface *)

(** As usual, build a Section to parameterize the interface by the APD: *)
Section MallocFreeASI.
Variable M:MallocFreeAPD.

(** Specification of [malloc] has the same issue with [compspecs] that we
  discussed above for [malloc_token]:  That is, we need the ASI to be 
  independent of any particular module's struct/union declarations.
  So we will define [malloc_spec_sz] which is a size-based, not type-based,
  specification. *)

Definition malloc_spec_sz :=
 DECLARE _malloc
   WITH n:Z, gv: globals
   PRE [ size_t ]
       PROP (0 <= n <= Ptrofs.max_unsigned)
       PARAMS (Vptrofs (Ptrofs.repr n)) GLOBALS (gv)
       SEP (mem_mgr M gv)
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (mem_mgr M gv;
             if eq_dec p nullval then emp
            else (malloc_token_sz M Ews n p * memory_block Ews n p)).

Definition free_spec_sz :=
 DECLARE _free
   WITH n:Z, p:val, gv: globals
   PRE [ tptr tvoid ]
       PROP ()
       PARAMS (p) GLOBALS (gv)
       SEP (mem_mgr M gv;
              if eq_dec p nullval then emp
              else (malloc_token_sz M Ews n p * memory_block Ews n p))
    POST [ Tvoid ]
       PROP ()
       LOCAL ()
       SEP (mem_mgr M gv).

(**  Of course the [exit] system call is not really part of the malloc/free 
   library, but this is a convenient place to put its specification. *)

Definition exit_spec :=
 DECLARE _exit
 WITH i: Z
 PRE [tint]
   PROP () PARAMS (Vint (Int.repr i)) GLOBALS () SEP()
 POST [ tvoid ]
   PROP(False) LOCAL() SEP().

(** And now we can construct the ASI, which (as usual) is just a list
  of (APD-parameterized) funspecs. *)

Definition MallocFreeASI:funspecs := [ malloc_spec_sz; free_spec_sz; exit_spec].

End MallocFreeASI.

(* ################################################################# *)
(** * Type-based specification of malloc and free *)

(** Of course, it is much easer for the user to use a funspec for
  malloc whose postcondition has a [data_at_] of the right type.
  So here we will define an alternate [malloc_token] and [malloc_spec]
  that uses compspecs and types. *)

Definition malloc_token {cs: compspecs} (M:MallocFreeAPD) sh t v := 
   !! field_compatible t [] v && 
   malloc_token_sz M sh (sizeof t) v.

Lemma malloc_token_valid_pointer: forall {cs: compspecs} M sh t p, 
      sizeof t <= 0 -> malloc_token M sh t p |-- valid_pointer p.
Proof. intros. unfold malloc_token.
 apply andp_left2. apply malloc_token_sz_valid_pointer; auto.
Qed.

Ltac malloc_token_data_at_valid_pointer :=
  (* If the size of t is unknown, can still prove valid pointer
      from (malloc_token sh t p * ... * data_at[_] sh t p)  *)
  match goal with |- ?A |-- valid_pointer ?p =>
   match A with
   | context [malloc_token _ _ ?t p] =>
         try (assert (sizeof t <= 0)
	  by (simpl sizeof in *; rep_lia); fail 1);
         try (assert (sizeof t > 0)
	  by (simpl sizeof in *; rep_lia); fail 1);
         destruct (zlt 0 (sizeof t));
         auto with valid_pointer
   | context [malloc_token_sz _ _ ?n p] =>
         try (assert (n <= 0) by rep_lia; fail 1);
         try (assert (n > 0) by rep_lia; fail 1);
         destruct (zlt 0 n);
         auto with valid_pointer
   end
 end.

#[export] Hint Extern 1 (malloc_token _ _ _ _ |-- valid_pointer _) =>
  (simple apply malloc_token_valid_pointer; data_at_valid_aux) : valid_pointer.
#[export] Hint Extern 4 (_ |-- valid_pointer _) => malloc_token_data_at_valid_pointer : valid_pointer.

Lemma malloc_token_local_facts:  forall {cs: compspecs} M sh t p,
      malloc_token M sh t p |-- !! (field_compatible t [] p /\ malloc_compatible (sizeof t) p).
Proof. intros.
 unfold malloc_token.
 normalize. rewrite prop_and.
 apply andp_right. apply prop_right; auto.
 apply malloc_token_sz_local_facts.
Qed.
#[export] Hint Resolve malloc_token_local_facts : saturate_local.

Definition malloc_spec (M:MallocFreeAPD) {cs: compspecs} (t: type) :=
 DECLARE _malloc
   WITH gv: globals
   PRE [ size_t ]
       PROP (0 <= sizeof t <= Ptrofs.max_unsigned;
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       PARAMS (Vptrofs (Ptrofs.repr (sizeof t))) GLOBALS (gv)
       SEP (mem_mgr M gv)
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (mem_mgr M gv;
             if eq_dec p nullval then emp
            else (malloc_token M Ews t p * data_at_ Ews t p)).

Definition free_spec (M:MallocFreeAPD)  {cs: compspecs} (t: type) :=
 DECLARE _free
   WITH p: val, gv: globals
   PRE [ tptr tvoid ]
       PROP ()
       PARAMS (p) GLOBALS (gv)
       SEP (mem_mgr M gv;
              if eq_dec p nullval then emp
              else (malloc_token M Ews t p * data_at_ Ews t p))
    POST [ Tvoid ]
       PROP ()
       LOCAL ()
       SEP (mem_mgr M gv).

(* ================================================================= *)
(** ** How to use the type-based [malloc_spec] *)

(** Both [malloc_spec_sz] and [malloc_spec] are specifications of the 
  same malloc function, so any given program (.c file) can be verified
  using either of the specs.  However, since the ASI provides
  [malloc_spec_sz], then in order to use [malloc_spec] in the verification
  of the client, one must do [forward_call] with the (optional)
  [funspec_sub] argument.

   Here we prove that (for any compspecs), 
    [malloc_spec_sz] implies [malloc_spec]. *)

Lemma malloc_spec_sub:
 forall  (M:MallocFreeAPD) {cs: compspecs} (t: type), 
   funspec_sub (snd (malloc_spec_sz M)) (snd (malloc_spec M t)).
Proof.
  do_funspec_sub. rename w into gv. clear H.
  Exists (sizeof t, gv) emp. simpl; entailer!.
  intros tau ? ?. Exists (eval_id ret_temp tau).
  entailer!.
  if_tac; auto.
  unfold malloc_token.
  assert_PROP (field_compatible t [] (eval_id ret_temp tau)).
  { entailer!.
    apply malloc_compatible_field_compatible; auto. }
  entailer!.
  rewrite memory_block_data_at_; auto.
Qed.

Lemma free_spec_sub:
 forall (M:MallocFreeAPD) {cs: compspecs} (t: type), 
   funspec_sub (snd (free_spec_sz M)) (snd (free_spec M t)).
Proof.
  do_funspec_sub. destruct w as [p gv]. clear H.
  Exists (sizeof t, p, gv) emp. simpl; entailer!.
  if_tac; trivial.
  sep_apply data_at__memory_block_cancel.
  unfold malloc_token; entailer!.
Qed.

(** Now, the pattern for using [malloc_spec] will be as shown in
  [VSU_stack], like this:

   [forward_call (malloc_spec_sub M t) gv]

   [forward_call (free_spec_sub M (Tstruct _cons noattr)) (q, gv)]

   It works like this:  [t] (or, for example, [Tstruct _cons noattr]) is
   any type of the client's choosing, interpreted using the client's own
   compspecs.  [forward_call] looks up [malloc] in the imported
   ASIs (that is, in the Gprog), and finds [malloc_spec_sz] as its 
   specification.   Then it uses the [funspec_sub] proof to adapt
   the spec into [malloc_spec M {cs} t], where the [cs] argument is
   instantiated using the _client's_  compspecs, as desired.

   And similarly for [free].
*)

(* ================================================================= *)
(** ** Next Chapter: [VSU_stack] *)

(* 2023-03-25 11:30 *)
