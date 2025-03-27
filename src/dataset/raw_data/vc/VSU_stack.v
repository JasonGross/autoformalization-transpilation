(** * VSU_stack: VSU verification of the Stack module *)
 
(* ================================================================= *)
(** ** stack2.c

    The module stack2.c is slightly adjusted from stack.c; it uses an
  internal function surely_malloc, just to illustrate how to handle
  local functions that are not exported in the ASI module interface.

    #include <stddef.h>
    #include "stdlib.h"
    #include "stack2.h"

    struct cons { int value; struct cons *next; };

    struct stack { struct cons *top; };

    void *surely_malloc (size_t n) {
      void *p = malloc(n);
      if (!p) exit(1);
      return p;
    }

    struct stack *newstack(void) {
      struct stack *p;
      p = (struct stack * ) surely_malloc(sizeof (struct stack));
      p->top = NULL;
      return p;
    }

    void push (struct stack *p, int i) {
      struct cons *q;
      q = (struct cons * ) surely_malloc(sizeof (struct cons));
      q->value = i;
      q->next = p->top;
      p->top = q;
    }

    int pop (struct stack *p) {
      struct cons *q;
      int i;
      q = p->top;
      p->top = q->next;
      i = q->value;
      free(q);
      return i;
    }
*)

(* ################################################################# *)
(** * Building the VSU

    Now we can verify the implementations of the individual modules.
  That is, for each module, we produce a VSU, a Verified Software Unit.
  
  Each of these verifications imports only ASIs (abstract specification
  interfaces), not other VSUs; that is, the verification of a module
  depends only on interfaces, not on the implementations (or
  verifications) of other modules.

  We start by importing floyd.proofauto, as usual, but also
  the floyd.VSU support. *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.

(** Next, we import the ASIs of the imported modules, and of this
  module.  Since [stack2.c] uses the malloc/free library (exported
  from our stdlib module), we import [Spec_stdlib] as well
  as [Spec_stack]. *)

Require Import VC.Spec_stdlib.
Require Import VC.Spec_stack.

(** Next, as usual we import a C program file (as parsed by clightgen).
  But we can import just this module: *)
Require Import VC.stack2.

(** _CompSpecs_ stands for "composite specifications", that is,
  CompCert's description of the struct and union types defined
  in this module.  The different modules of a program, that is,
  the different .c files that will be linked together,  may have
  different structs and unions.  Here we process the compspecs
  of _this_ module. Here, [prog] is really VC.stack2.prog.  *)
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.

(** Recall that our ASIs are parameterized by the APDs they use;
  and we used a Section for that purpose in [Spec_stack].
  The StackASI was parameterized by (M: MallocFreeAPD) and
  (STACK: StackAPD).

  The Stack VSU will use the same two APDs.  As before, M will
  be a parameter.  But STACK will not be a parameter: we will
  build and instantiate that APD in this verification.  So our
  [Section Stack_VSU] is only for the purpose of parameterizing by M. *)

Section Stack_VSU.
Variable M: MallocFreeAPD.

(* ================================================================= *)
(** ** First, instantiate the APD *)

(** Now it's time to build an instance of StackAPD.  To do that,
  we need to construct the same [stack] mpred that we constructed
  in [Verif_stack].  In this exercise, you will paste in
  your solutions to the corresponding exercises in [Verif_stack],
  leading up to the definition of a StackAPD. *)

(** **** Exercise: 2 stars, standard (STACK) *)

Fixpoint listrep (il: list Z) (p: val) : mpred :=
 match il with
 | i::il' => EX y: val, 
        malloc_token M Ews (Tstruct _cons noattr) p *
        data_at Ews (Tstruct _cons noattr) (Vint (Int.repr i),y) p *
	listrep il' y
 | nil => !! (p = nullval) && emp
 end.

Lemma listrep_local_prop: forall il p, listrep il p |--
        !! (is_pointer_or_null p  /\ (p=nullval <-> il=nil)).
(* FILL IN HERE *) Admitted.
Local Hint Resolve listrep_local_prop : saturate_local.

Lemma listrep_valid_pointer:
  forall il p,
   listrep il p |-- valid_pointer p.
(* FILL IN HERE *) Admitted.
Local Hint Resolve listrep_valid_pointer : valid_pointer.

Definition stack (il: list Z) (p: val) :=
 EX q: val,
  malloc_token M Ews (Tstruct _stack noattr) p * 
  data_at Ews (Tstruct _stack noattr) q p *
  listrep il q.

Arguments stack il p : simpl never.

Lemma stack_local_prop: forall il p, stack il p |--  !! (isptr p).
(* FILL IN HERE *) Admitted.
Local Hint Resolve stack_local_prop : saturate_local.

Lemma stack_valid_pointer:
  forall il p,
   stack il p |-- valid_pointer p.
(* FILL IN HERE *) Admitted.
Local Hint Resolve stack_valid_pointer : valid_pointer.
(** [] *)

(** Now we can construct STACK, an instance of StackAPD, by
  gluing together the [stack] predicate with the two lemmas
  about it. *)

Definition STACK : StackAPD := 
    Build_StackAPD stack stack_local_prop stack_valid_pointer.

(* ################################################################# *)
(** * Internal functions *)

(** Each internal function needs a funspec.  Unlike the exported
  functions, whose funspecs go in the ASI (such as [Spec_stack]),
  funspecs for internal functions go here in the VSU. *)

Definition surely_malloc_spec :=
  DECLARE _surely_malloc
   WITH t:type, gv: globals
   PRE [ size_t ]
       PROP (0 <= sizeof t <= Ptrofs.max_unsigned;
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       PARAMS (Vptrofs (Ptrofs.repr (sizeof t))) GLOBALS (gv)
       SEP (mem_mgr M gv)
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       RETURN (p)
       SEP (mem_mgr M gv; malloc_token M Ews t p * data_at_ Ews t p).

(* ================================================================= *)
(** ** Constructing Vprog and Gprog *)

(** Imports of a VSU is just the concatenation of all the
   ASIs of the modules that it's importing: *)
Definition Stack_imports : funspecs := MallocFreeASI M.

(** Privates of a module are the funspecs of locally defined
  functions that are _not_ to be exported for client use *)
Definition Stack_private : funspecs := [surely_malloc_spec].

(** Internals are just the Privates and the other internal funspecs.
  _IF_ the module does not re-export any imported functions, then that's
  just the same as the Privates plus the Exports, as shown here: *)
Definition Stack_internals : funspecs := Stack_private ++ (StackASI M STACK).

(** Gprog is the basis on which to prove each semax_body;
  it is always the Imports plus the Internals *)
Definition Stack_Gprog : funspecs := Stack_imports ++ Stack_internals.

(** For every module except Main, the Vprog is computed as, *)
Definition Stack_Vprog : varspecs.  mk_varspecs prog. Defined.

(* ================================================================= *)
(** ** Proofs of the function bodies *)
(** **** Exercise: 2 stars, standard (stack_bodies)

    Copy and adapt these proofs from [Verif_stack]. *)

Lemma body_pop: semax_body Stack_Vprog Stack_Gprog f_pop (pop_spec M STACK).
Proof.
start_function.
simpl stackrep.
(* FILL IN HERE *) Admitted.

Lemma body_push: semax_body Stack_Vprog Stack_Gprog f_push (push_spec M STACK).
Proof.
start_function.
simpl stackrep.
forward_call (Tstruct _cons noattr, gv).
(* FILL IN HERE *) Admitted.

Lemma body_newstack: semax_body Stack_Vprog Stack_Gprog f_newstack (newstack_spec M STACK).
Proof.
start_function.
(* FILL IN HERE *) Admitted.

Lemma body_surely_malloc: semax_body Stack_Vprog Stack_Gprog f_surely_malloc surely_malloc_spec.
Proof.
start_function.
forward_call (malloc_spec_sub M t) gv.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Construction of the VSU *)

(** Programs that do input/output need an "External Specification" 
  (or [Espec]) that characterizes the interaction.  All the VSUs of the
  program must use the same Espec.   Since this program doesn't do
  any I/O, it can use the standard trivial Espec, as follows: *)
#[export] Existing Instance NullExtension.Espec.

(** Notice that all the [semax_body] proofs above didn't depend at all
  on which Espec we use, so they're portable to any Espec.  That wouldn't
  be true if some of them did I/O. *)

(** To construct the StackVSU, we first define its _type_, as follows: *)
Lemma StackVSU: VSU nil Stack_imports ltac:(QPprog stack2.prog)
                                           (StackASI M STACK) emp.
(** That is,
 - nil,  the Externs of this module;
 - [Stack_imports], the Imports of this module;
 - [prog], the _program_ of this module, but transformed into a [QP.program]
   by the [QPprog] tactic;
 - [StackASI], the Exports of this module;
 - [emp] is the global-variable specifier, since this implementation
      of the stack module has no global variables of its own.
     *)

(**  Having specified the StackVSU lemma, we now prove it.
  The [mkVSU] line has two arguments: The C program (stack2.prog),
  and the Internals (that were not mentioned in the _type_ of the VSU).
  Then, there is one subgoal for each function-body defined in the .c file.
  In each subgoal,  [solve_SF_internal] solves the goal, using the
  appropriate [semax_body] lemma that you have proved. *)

Proof.
  mkVSU prog Stack_internals.
  + solve_SF_internal body_surely_malloc.
  + solve_SF_internal body_newstack.
  +
(** How do you know which [semax_body] proof to supply for 
   each subgoal?  It's easy -- the subgoal has the form,
  [SF Gprog name fundef funspec], where in this case 
  name is [_surely_malloc] and fundef is [Internal f_surely_malloc],
  so it's pretty clear that [body_surely_malloc] is what we want to
 provide here. *)
      solve_SF_internal body_push.
  + solve_SF_internal body_pop.
Qed.

End Stack_VSU.

(* ================================================================= *)
(** ** Next Chapter: [VSU_triang] *)

(* 2023-03-25 11:30 *)
