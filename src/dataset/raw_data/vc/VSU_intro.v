(** * VSU_intro: Introduction to Verified Software Units *)

(* ################################################################# *)
(** * Looking back: single-module programs *)

(** You've now seen how to verify programs that use many of C's data
  structures (arrays, pointers, structs, integers) and control
  structures (functions, if-then-else, loops), and abstraction 
  structures (data abstraction, module interfaces).  The capstone exercise
  (hash tables) demonstrated all of these at once, in addition to a
  key concept: layering the proof using a functional model,
  so that proofs about the properties of the functional model ([Hashfun])
  cleanly separate from the implementation proof ([Verif_hash]) showing
  that the C program refines the functional model. *)

(* ################################################################# *)
(** * Next: modular verification of modular programs *)

(** VST's facility for verifying modular programs is called "Verified 
   Software Units,"  designed and implemented by Lennart Beringer.

   A program module in C
  - is implemented in one or more .c files;
  - exports some set of functions (an API) described in a .h file
  - (perhaps) has some private functions that are not exported
  - imports from other modules, various sets of functions described in .h files
  - (perhaps) manipulates data structures whose representations should be kept private from client modules
  - (perhaps) has global variables of its own that (perhaps) other modules should not directly manipulate

  Although the C programming language has the notion of [static] functions
  and variables that are "global" only within a .c file, and not exported from
  that .c file, we will not rely on this feature; 
  - in part because a single "module" may be implemented in more than one .c file, to which the [static] keyword does not generalize;
  - in part because we will use Verifiable C's  "VSU" facility to enforce this kind of locality.

  Therefore the private functions and private variables of a module will
  be [extern] in the C sense.

  The C programs you have already seen in previous chapters -- stack, strlib, hash --
  are already written as program modules in this sense.  But the VST
  verifications in [Verif_stack], [Verif_hash], don't enforce
  data abstraction, and don't show you how to link the modules together.
  That is a job for VSU - Verified Software Units -- and the next chapters
  show how to verify those same .c programs in the VSU style.

   VSU verification of a module (for example, "Stack") usually comprises these separate files:
   - [Model_stack.v],  the functional model, just in the sense that [hash.v] is the
       functional model for our hash table.  But the functional model for stacks
       is so simple -- just Coq lists -- that we will merge that into Spec_stack.v.
   - [Spec_stack.v], the API specification of the stack module.  This is the one that
       clients import; it contains (for example) funspecs and the names of
       abstract data types (ADTs).  The important thing is that it contains
       nothing about the _implementation_ of the function bodies, or
       the representations of ADTs, or any mention of internal functions
       that are not meant to be exported through the API.
   - [VSU_stack.v] is the proof that the implementation of the stack module,
        [stack.c], correctly implements the API spec in [Spec_stack.v].
*)

(* ################################################################# *)
(** * A Stack/Triang program to verify *)

(** As an exercise in VSU verification, we will use the [stack.c] program
  that was introduced in [Verif_stack] and [Verif_triang].  
  But first we'll break it up into modules: *)
(* ----------------------------------------------------------------- *)
(** *** stdlib.h

  #include <stddef.h>
  extern void * malloc (size_t n);
  extern void free (void *p);
  extern void exit(int n);
*)
(* ----------------------------------------------------------------- *)
(** *** stack2.h

  struct stack;
  struct stack *newstack(void);
  void push (struct stack *p, int i);
  int pop (struct stack *p);
*)
(* ----------------------------------------------------------------- *)
(** *** triang2.h

  int triang (int n);
*)
(* ----------------------------------------------------------------- *)
(** *** main2.c

  #include "triang2.h"
  int main(void) { return triang(10); }
*)

(** With, of course, stack2.c and triang2.c that implement
 modules corresponding to stack2.h and triang2.h. *)

(* ================================================================= *)
(** ** Let's verify!

    And with that preamble, you can move on to the next chapter,
   [Spec_stack].
*)

(* ================================================================= *)
(** ** Warning *)

(** VSU is still a new feature, and some of the VSU tactics don't give
   very good error diagnostics when something goes wrong.
*)

(* ================================================================= *)
(** ** Next Chapter: [Spec_stack] *)

(* 2023-03-25 11:30 *)
