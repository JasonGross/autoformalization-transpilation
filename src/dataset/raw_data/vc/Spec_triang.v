(** * Spec_triang: VSU specification of the Triang module *)

(** We will now write the ASI (abstract specification interface) of
  the [triang2] module. *)

(* ----------------------------------------------------------------- *)
(** *** triang2.h

#include <stddef.h>
int triang (int n);

This header file suggests that the [triang] module exports just one function, 
that computes the triangular number of its input, that is, 1+2+...+n.
*)

(* ----------------------------------------------------------------- *)
(** *** triang2.c

#include <stddef.h>
#include "stdlib.h"
#include "stack2.h"
#include "triang2.h"

void push_increasing (struct stack *st, int n) {
  int i=0;
  while (i<n) { i++; push(st,i); }
}

int pop_and_add (struct stack *st, int n) {
  int i=0;
  int t, s=0;
  while (i<n) { t=pop(st); s += t; i++; }
  return s;
}

int triang(int n) {
  struct stack *st;
  int i,t,s;
  st = newstack();
  push_increasing(st, n);
  s = pop_and_add(st, n);
  return s;
}  

In the file [triang2.c], the functions [push_increasing] and [pop_and_add]
are identical to the ones in [Verif_stack].  These are _internal_
functions to the module, not exported.  In a typical C program, you
might make these functions _static_ to restrict visibility, but we won't
do that here, for two reasons:
 - We will use VSU's specification facilities to enforce locality in the proof;
 - One might build the [triang] module from more than one .c file, with
    the different .c files referencing "internal" functions from each other.
    In this case, _static_ won't work in C, but our VSU can still specify
    the module structure.
*)

(* ################################################################# *)
(** * Let's verify! *)

Require Import VST.floyd.proofauto.
Require Import VC.triang2.
Require Import VC.Spec_stdlib.
Require Import VC.Spec_stack.

(* ================================================================= *)
(** ** Abstract Predicate Declaration (APD) *)

(** This module does not use any abstract data types in its 
  external interface.  The only type used in [int triang (int n)] is
  the [int] type.  So this module does not need any APDs at all.

  Conversely, a module whose API uses more than one abstract
  data type might have more than one APD.  There is no 1-1
  matching between APDs and ASIs. *)

(* ================================================================= *)
(** ** Abstract Specification Interface (ASI) *)

(** As usual, we make a Section to introduce the APD parameters *)

Section TriangASI.

(** We need to mention the MallocFreeAPD because the [triang]
  function uses [mem_mgr] in its pre and postconditions. *)
Variable M: MallocFreeAPD.

(** Although the _implementation_ of this module uses the StackAPD,
  that use is purely internal, and does not need to be mentioned
  in the external interface specification. *)

(** **** Exercise: 2 stars, standard (triang_spec)

    Adjust this funspec until it properly specifies the triang function.
   Suggestion: the PROP clause of the precondition could very reasonably
   limit the size of the input to approximately the square root of the
   maxium integer, so that the triangular number does not overflow. *)
Definition triang_spec : ident * funspec :=
 DECLARE _triang
 WITH gv: globals (*... more WITH variables... *)
(* FILL IN HERE *)
 PRE [ 
(* FILL IN HERE *)
       ] 
    PROP (
(* FILL IN HERE *)
     ) 
    PARAMS( 
(* FILL IN HERE *)
     ) 
    GLOBALS(gv) 
    SEP (mem_mgr M gv)
 POST [ tint ] 
    (* Suggestion: this postcondition does not need an EX, but you 
       may add one if you wish to. *)
    PROP ( 
(* FILL IN HERE *) 
    )
    RETURN (
(* FILL IN HERE *)
    ) 
    SEP (mem_mgr M gv).

(** If you don't get this quite right, you will notice it either when
  you prove [VSU_triang] (verification of [triang.c]) or when
  you prove [VSU_main] (verification of the client).  In that case,
  just come back here and adjust the funspec. *)

(** [] *)

(** Because the functions [push_increasing] and [pop_and_add] are not
  exported from the module -- they are used only internally by [triang],
  their funspecs need not be mentioned here. *)

(* ----------------------------------------------------------------- *)
(** *** Completing the Triang ASI *)

(** Now the "Triang Abstract Specification Interface" is just a list of the 
   exported funspecs *)

Definition TriangASI : funspecs := [  triang_spec ].

End TriangASI.

(** And remember that StackASI is parameterized by the Variables of the Section: *)
Check TriangASI.  (*   : MallocFreeAPD -> funspecs *)

(* ================================================================= *)
(** ** Next Chapter: [Spec_stdlib] *)

(* 2023-03-25 11:30 *)
