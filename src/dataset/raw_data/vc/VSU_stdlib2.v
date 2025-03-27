(** * VSU_stdlib2: Malloc/free/exit programmed in C *)

(** In contrast to [VSU_stdlib] which axiomatized malloc, free,
  and exit as external functions, in this chapter we construct them as
  ordinary C functions, and prove them correct.  This chapter shows
  how to manage global variables that are private to a module.

 In the C code, there is a [stdlib.h] interface, with alternative
 implementations [stdlib.c] and [stdlib2.c] that are quite
 independent of each other.

 The the proofs, there is a specification [Spec_stdlib.MallocFreeASI]
 (that is, the "malloc-free Abstract Specification Interface")
 with two alternative implementations-with-proofs,
 [VSU_stdlib.MallocFreeVSU] and [VSU_stdlib2.MallocFreeVSU].

 That second VSU is the one we build in this chapter.
*)

(* ################################################################# *)
(** * The C program *)

(** Here is our C program.  Notice the variables [pool, pool_index, freelist] 
that are global to the module, but meant to be private--not to be
directly manipulated by clients of the module.  Furthermore, these
variables have initial values ([pool_index=0, freelist=NULL],
and [pool] zero-initialized implicitly) that 
represent a meaningful initial state.

/* stdlib2.c */
#include <stddef.h>
#include "stdlib.h"

struct cell {struct cell *a, *b, *c, *d;};

#define N 80000

struct cell pool[N];
int pool_index = 0;
struct cell *freelist=NULL;

void *malloc (size_t n) {
  struct cell *p;
  if (n>sizeof(struct cell)) return NULL;
  if (freelist) {
    p = freelist;
    freelist = p->a;
  } else if (pool_index < N) {
    p = pool+pool_index++;
  } else p=NULL;
  return (void* ) p;
}

void free (void *p) {
  struct cell *pp = p;
  if (pp==NULL) return;
  pp->a = freelist;
  freelist=pp;
}

void exit (int n) {
  while (1) ;
}

As you can see, malloc can allocate blocks whose size ranges from
 0 to sizeof(struct cell), that is, up to four words long.  Any malloc
 request larger than that will return NULL, which is legal behavior
 for malloc.  Furthermore, the maximum size of the pool is N=80000,
 beyond which malloc will return NULL.

  The exit() function infinite-loops, so that it satisfies its postcondition
  of False in our Hoare logic of partial correctness.
*)
 
(* ################################################################# *)
(** * The normal boilerplate *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VC.stdlib2.
Require Import VC.Spec_stdlib.
#[export] Instance CompSpecs : compspecs. make_compspecs stdlib2.prog. Defined.

(** As usual, we define representation relations.  First, for the free list,
    which is just a linked list much as in [VSU_stack].*)

Definition tcell := Tstruct _cell noattr.

Fixpoint freelistrep (n: nat) (p: val) : mpred :=
 match n with
 | S n' => EX y: val, 
        !! malloc_compatible (sizeof tcell) p && 
        data_at Ews tcell (y, (Vundef, (Vundef, Vundef))) p *
        freelistrep n' y
 | O => !! (p = nullval) && emp
 end.

Arguments freelistrep n p : simpl never.

Lemma freelistrep_local_prop: forall n p, 
   freelistrep n p |--  !! (is_pointer_or_null p /\ (n=0<->p=nullval) /\ (n>0<->isptr p))%nat.
(* FILL IN HERE *) Admitted.
#[export] Hint Resolve freelistrep_local_prop : saturate_local.

Lemma freelistrep_valid_pointer:
  forall n p,
   freelistrep n p |-- valid_pointer p.
(* FILL IN HERE *) Admitted.
#[export] Hint Resolve freelistrep_valid_pointer : valid_pointer.
(** [] *)

(* ################################################################# *)
(** * malloc_token *)

(** Suppose the user does [p = malloc(7);].  Then [p] points to
  a newly allocated block of 7 bytes.  What does [malloc_token(p)]
  represent?
  - Normally, there must be some way for [free(p)] to figure out
   the size of the block.  This can be done by having a header word,
   just before address p, that gives the size (though there are other
   ways to do it).  Normally, this header word is part of what 
   malloc_token represents.  But in this implementation, all blocks
   are the same size, so there's no need for such a header.
  - The memory-manager's free list contains blocks all of size
   sizeof(tcell), which  is 16 bytes when [sizeof(size_t)=4] or 
   32 bytes when [sizeof(size_t)=8].  When [malloc(7)] splits a
   block into two pieces, the malloc_token represents the
   second piece, the portion of the block between offset 7 and the end.
   That is the [memory_block] shown in the definition below.
  - In addition, the malloc_token has three propositional facts about
   address [p], that will assist the [free()] function in reconstituting
   the two parts of the split block. *)
 
Definition malloc_token_sz (sh: share) (n: Z) (p: val) : mpred := 
  !! (field_compatible tcell [] p 
      /\ malloc_compatible (sizeof tcell) p
      /\ 0 <= n <= sizeof tcell) 
 &&  memory_block Ews (sizeof tcell - n) (offset_val n p).

(** **** Exercise: 2 stars, standard (malloc_token_properties) *)
Lemma malloc_token_sz_valid_pointer:
    forall (sh : share) (sz : Z)  (p : val),
            sz <= 0 ->
              malloc_token_sz sh sz p |-- valid_pointer p.
(* FILL IN HERE *) Admitted.

Lemma  malloc_token_sz_local_facts : 
   forall (sh : share) (sz : Z) (p : val),
     malloc_token_sz sh sz p |-- !! malloc_compatible sz p.
(* FILL IN HERE *) Admitted.
(** [] *)

(** The next three lines define an opaque constant that, nevertheless,
  rep_lia can unfold.     See VC.pdf, chapter 65 "Opaque Constants". *)
Definition N : Z := proj1_sig (opaque_constant 80000).
Definition N_eq : N=_ := proj2_sig (opaque_constant _).
#[export] Hint Rewrite N_eq : rep_lia.

(* ----------------------------------------------------------------- *)
(** *** Digression (feel free to skip this) *)

Module Digression.
(** Suppose someone changes the source program stdlib2.c,  putting a
  different constant than 80000.  You would like your verification 
  script to automatically adjust.    We will revise the line,
  [Definition N : Z := ...]  to find the constant automagically.

  Step one is to find the constant.  You can look in stdlib2.v, which
  is produced by CompCert clightgen from stdlib2.c, for the variable
  definition v_pool.  And now look where the number 80000 appears
  in [gvar_info(v_pool)]: *)
Compute gvar_info (stdlib2.v_pool).
  (*   = Tarray
         (Tstruct 57 {| attr_volatile := false; attr_alignas := None |})
         80000
         {| attr_volatile := false; attr_alignas := None |}
     : type *)

(** It's easy to extract that number automatically: *)

Compute match gvar_info (stdlib2.v_pool) with Tarray _ n _ => n | _ => 0 end.
  (*  = 80000: Z *)

(** The following definition of [N] won't work well, because N will 
  not be a constant, it'll be a match expression: *)
Definition N' := match gvar_info (stdlib2.v_pool) with Tarray _ n _ => n | _ => 0 end.
Print N'.  (* N' = match gvar_info v_pool with Tarray _ n _ => n | _ => 0 end *)

(** So instead, use this Coq trick: *)

Definition N'' := 
  ltac:(let x := constr:(match gvar_info (stdlib2.v_pool) with
                         | Tarray _ n _ => n
			 | _ => 0 end)
        in let x := eval compute in x in exact x).
Print N''. (* N'' = 80000 : Z *)

(** Now, throw away N'' and we'll combine the two tricks together:
 - [opaque_constant] to define a constant that won't unfold except 
    by explicit rewriting; and
 - extract the value of the constant from the program itself. *)
Definition N := proj1_sig (opaque_constant 
                            (ltac:(let x := constr:(match gvar_info (stdlib2.v_pool) with
                                          Tarray _ n _ => n | _ => 0 end)
                                    in let x := eval compute in x in exact x))).
Definition N_eq : N=_ := proj2_sig (opaque_constant _).
#[export] Hint Rewrite N_eq : rep_lia.
Check N_eq.  (* : N = 80000 *)

End Digression.

(* ----------------------------------------------------------------- *)
(** *** End of digression. Aren't you glad you skipped it? *)

(* ################################################################# *)
(** * Defining the mem_mgr APD *)

(** This [mem_mgr] predicate is the client-view abstract predicate
  that characterizes the contents of this module's global state variables,
  [pool], [pool_index], and [freelist]. *)

Definition mem_mgr (gv: globals) : mpred :=
 EX i: Z, EX p: val, EX frees: nat,
  !! (0 <= i <= N) &&
  data_at Ews tint (Vint (Int.repr i)) (gv _pool_index) *
  data_at_ Ews (tarray tcell (N-i))
     (field_address0 (tarray tcell N) [ArraySubsc i]  (gv _pool)) *
  data_at Ews (tptr tcell) p (gv _freelist) *
  freelistrep frees p.

Definition M : MallocFreeAPD := 
    Build_MallocFreeAPD mem_mgr malloc_token_sz
           malloc_token_sz_valid_pointer malloc_token_sz_local_facts.

(* ################################################################# *)
(** * Constructing Vprog and Gprog *)

  Definition MF_ASI: funspecs := MallocFreeASI M.
  Definition MF_imported_specs:funspecs :=  nil.
  Definition MF_internal_specs: funspecs := MF_ASI.
  Definition MF_globals gv : mpred:= Spec_stdlib.mem_mgr M gv.
  Definition MFVprog : varspecs. mk_varspecs stdlib2.prog. Defined.
  Definition MFGprog: funspecs := MF_imported_specs ++ MF_internal_specs.

(** **** Exercise: 3 stars, standard (stdlib2_body_malloc) *)

Lemma body_malloc: semax_body MFVprog MFGprog f_malloc (malloc_spec_sz M).
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard (stdlib2_body_free) *)
Lemma body_free: semax_body MFVprog MFGprog f_free (free_spec_sz M).
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (stdlib2_body_exit) *)
Lemma body_exit: semax_body MFVprog MFGprog f_exit exit_spec.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Initializers for global data *)

Check @Comp_MkInitPred.
(**  Each VSU may have private global variables that constitute its
  "local state".  The client of the VSU should not access these
  directly; and in separation logic all these variables should be
  abstracted as a single abstract predicate.  Since these variables
  may have initial values that concretely represent some abstract
  state, we need an axiom in the VSU interface (proved as a lemma
  in the VSU implementation), saying that the initial values
  properly represent a proper state of the abstract predicate. *)

(** **** Exercise: 2 stars, standard (stdlib2_initialize) *)
Lemma initialize: VSU_initializer prog MF_globals.
Proof.
InitGPred_tac.
unfold MF_globals.
(* FILL IN HERE *) Admitted.

(* ================================================================= *)
(** ** Defining the pieces of a VSU

    And now, in the usual way, we can put totether the pieces: *)

(* ################################################################# *)
(** * Constructing the Component and the VSU *)

  Definition MF_Externs : funspecs := nil.

Definition MallocFreeVSU: @VSU NullExtension.Espec
         MF_Externs MF_imported_specs ltac:(QPprog prog) MF_ASI MF_globals.
  Proof. 
 mkVSU prog MF_internal_specs.
    - solve_SF_internal body_malloc.
    - solve_SF_internal body_free.
    - solve_SF_internal body_exit.
    - apply initialize; auto.
Qed.

(* ================================================================= *)
(** ** Next Chapter: [VSU_main2] *)

(* 2023-03-25 11:30 *)
