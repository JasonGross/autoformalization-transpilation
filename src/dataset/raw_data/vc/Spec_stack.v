(** * Spec_stack: VSU specification of the Stack module *)

(** Recall the Stack module described in [Verif_stack].  Recall that
   [stack.c] really contained two modules, "stack" and "triang".  We 
   will break this program into four pieces, as follows:

 - [stdlib.c]  (and [stdlib.h]) characterizing the external library functions, malloc, free, exit. 
 - [stack2.c]  (and [stack2.h]) with newstack, push, pop.
 - [triang2.c] (and [triang2.h]) with push_increasing, pop_and_add, and triang.
 - [main2.c] with a main function that calls triang.

For the [stack] module we have the header file [stack2.h]: 

    /* stack2.h */
    #include <stddef.h>
    struct stack;
    struct stack *newstack(void);
    void push (struct stack *p, int i);
    int pop (struct stack *p);
*)

(* ################################################################# *)
(** * Let's verify! *)

Require Import VST.floyd.proofauto.
Require Import VC.stack2.
Require Import VC.Spec_stdlib.

(* ================================================================= *)
(** ** Abstract Predicate Declaration (APD)

    As you recall from [Verif_stack], the stack module implements
  an abstract data type; that is, a data structure with a private representation
  and public operators.  In the C program, the name of the type is [struct stack],
  and in the header file above, we emphasize that the representation is
  private by writing [struct stack;] instead of [struct stack {...fields...};].

  That means any .c file that imports just [stack.h] can't access the individual
  fields, and is meant to use the API functions [newstack], [push], and [pop] to
  create and manipulate values of type <struct stack *>.  C programs can't
  exactly _enforce_ this, because the client could "cheat" by declaring
  <struct stack {...fields...}> or by casting values of type <struct stack *> to 
  other types.  But in our VST verification, we _can_ enforce this data abstraction.
  We do so by making an _Abstract Predicate Declaration_  (APD) . *)

Record StackAPD := {
  stackrep: list Z -> val -> mpred;
  stackrep_local_facts: forall il p, stackrep il p |-- !! (isptr p);
  stackrep_valid_pointer: forall il p, stackrep il p |-- valid_pointer p
}.

(** Here, [stackrep] serves the same purpose as [stack] in [Verif_stack];
  that is, it is the separation-logic representation relation for stacks.
  In particular, [stackrep il p]  is an [mpred] that says, "at address p is
  a data structure representing the sequence il".  But the difference here
  is that we don't say _what_ the representation is, we just give its type
  signature, [list Z -> val -> mpred].  In addition, we must provide
  the [local_facts] and the [valid_pointer] lemmas for this relation, just
  as we did in [Verif_stack]; but here we just present them as axioms,
  not as theorems.  All of this is bundled into a Record, the _abstract
  predicate declaration_ (APD).  The client need never know how the 
  data structure is really represented, that is, the details of the stackrep 
  predicate. *)

(** If we examine the type of [stackrep], ... *)
Check stackrep.  (* : StackAPD -> list Z -> val -> mpred

    we find that, given an _instance_    [S:StackAPD], then
   [stackrep S] will be a relation of type [list Z -> val -> mpred].
  At the moment, we don't yet have an instance; after all, this is an
  abstract data type whose representation will be provided by the 
  implementation of a module, and in this file we are describing only
  the interface, not the implementation. *)

(** Now, just as we did in [Verif_stack], we add the lemmas/axioms
    about stackrep to the respective hint databases. *)
#[export] Hint Resolve stackrep_local_facts : saturate_local.
#[export] Hint Resolve stackrep_valid_pointer: valid_pointer.

(* ================================================================= *)
(** ** Abstract Specification Interface (ASI) *)

(** The specification interface between one module and another consists
  primarily of the _funspecs_ of API functions that the client module
  can call upon.  In an Abstract Specification Interface (ASI) we present those
  funspecs, but not their proofs.  Those funspecs, in their preconditions and
  postconditions, may use separation-logic predicates (mpreds) that are
  APDs -- of this module or of other modules -- and these APDs will be
  parameters of the module.  The funspecs can also use ordinary mpreds
  such as [data_at].

  In this case, the Stack ASI needs to refer to 2 APDs: the [MallocFreeAPD]
  imported from the MallocFree module, and the [StackAPD] that will be
  exported from this module.  That is, every funspec will be parameterized
  by [M] (an instance of [MallocFreeAPD]), and by STACK (an instance of
  [StackAPD]).  We do this using a [Section]. *)

Section StackASI.
Variable M: MallocFreeAPD.
Variable STACK: StackAPD.

(** Now the funspecs look just as they did in [Verif_stack], except that
  we write [mem_mgr M] instead of [mem_mgr], and we write [stackrep STACK]
  instead of [stack].  By the way, in [Verif_stack] the identifier 
  mem_mgr referred to [VST.floyd.library.mem_mgr], but here we are 
  referring to [Spec_stdlib.mem_mgr] which is not the same.
  We'll explain that one in Chapter [Spec_stdlib]. *)

Locate mem_mgr.  (* short for  VC.Spec_stdlib.mem_mgr *)
Check mem_mgr.  (* MallocFreeAPD -> globals -> mpred. *)

Definition newstack_spec : ident * funspec :=
 DECLARE _newstack
 WITH gv: globals
 PRE [ ] 
    PROP () PARAMS() GLOBALS(gv) SEP (mem_mgr M gv)
 POST [ tptr (Tstruct _stack noattr) ] 
    EX p: val, PROP ( ) RETURN (p) 
               SEP (stackrep STACK nil p; mem_mgr M gv).

Definition push_spec : ident * funspec :=
 DECLARE _push
 WITH p: val, i: Z, il: list Z, gv: globals
 PRE [ tptr (Tstruct _stack noattr), tint ] 
    PROP (Int.min_signed <= i <= Int.max_signed) 
    PARAMS (p; Vint (Int.repr i)) GLOBALS(gv) 
    SEP (stackrep STACK il p; mem_mgr M gv)
 POST [ tvoid ] 
    PROP ( ) RETURN ()
    SEP (stackrep STACK (i::il) p; mem_mgr M gv).

Definition pop_spec : ident * funspec :=
 DECLARE _pop
 WITH p: val, i: Z, il: list Z, gv: globals
 PRE [ tptr (Tstruct _stack noattr) ] 
    PROP () 
    PARAMS (p) GLOBALS(gv) 
    SEP (stackrep STACK (i::il) p; mem_mgr M gv)
 POST [ tint ] 
    PROP ( ) RETURN (Vint (Int.repr i))
    SEP (stackrep STACK il p; mem_mgr M gv).

(** Now the "Stack Abstract Specification Interface" is just a list of the 
   exported funspecs *)

Definition StackASI : funspecs := [  newstack_spec; push_spec; pop_spec ].

End StackASI.

(** And remember that StackASI is parameterized by the Variables of the Section: *)
Check StackASI.  (*   : MallocFreeAPD -> StackAPD -> funspecs *)

(* ================================================================= *)
(** ** Next Chapter: [Spec_triang] *)

(* 2023-03-25 11:30 *)
