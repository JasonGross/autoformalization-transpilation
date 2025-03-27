(** * VSU_triang: VSU verification of the Triang module *)

(** In this chapter we construct the VSU proving that [triang2.c]
  implements the specification from [Spec_triang]. *)

(* ================================================================= *)
(** ** Imports *)

(**  
  - We import the standard [floyd.proofauto] and [floyd.VSU].
  - This module calls upon functions from [stack2.c], so it needs to import [Spec_stack].
  - The module implements the [TriangASI], so it needs to import [Spec_triang], which defines that.
  - This module uses the [MallocFreeAPD], but not (directly) the [MallocFreeASI].  That is, it uses the [mem_mgr] predicate but doesn't call any of the malloc or free functions.  If we had defined the APD in a separate file from the ASI, we would need to import only one of those files.  As it is, we import [Spec_stdlib].
  - And we must import the C program, [triang2].
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VC.Spec_stdlib.
Require Import VC.Spec_stack.
Require Import VC.Spec_triang.
Require Import VC.triang2.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.

(* ================================================================= *)
(** ** Parameters for the VSU *)

(** As usual, we make a Section to parameterize the VSU by the
 imported APDs. *)

Section Triang_VSU.
Variable M: MallocFreeAPD.
Variable STACK: StackAPD.

(** **** Exercise: 3 stars, standard (Triang_private)

    Write funspecs for the two private internal functions, and list them in
    [Triang_private].   Hint: copy and adapt from [Verif_triang],
    bringing in supporting definitions (such as [decreasing]) as needed.
    Refer to [Stack_private] in [VSU_stack] for an example.
 *)

Definition push_increasing_spec : ident * funspec 
 (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Definition pop_and_add_spec  : ident * funspec 
 (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Definition Triang_private : funspecs := [
  (* FILL IN HERE *)
  ].   

(** [] *)

Definition Triang_imports : funspecs := StackASI M STACK.
Definition Triang_internals : funspecs := Triang_private ++ (TriangASI M).
Definition Triang_Gprog : funspecs := Triang_imports ++ Triang_internals.
Definition Triang_Vprog : varspecs.  mk_varspecs prog. Defined.

(** **** Exercise: 2 stars, standard (body_push_increasing) *)

(** Prove the semax_body lemma for push_increasing.
   You'll want to copy definitions and lemmas from your solution
   to [Verif_triang]. *)

Lemma body_push_increasing: semax_body Triang_Vprog Triang_Gprog
                         f_push_increasing push_increasing_spec.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (body_pop_and_add) *)

(** Prove the semax_body lemma for pop_and_add.
   You'll want to copy definitions and lemmas from your solution
   to [Verif_triang]. *)

Lemma body_pop_and_add: semax_body Triang_Vprog Triang_Gprog f_pop_and_add pop_and_add_spec.
(* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard (body_triang)

    Prove the correctness of the triang function. 

   When you get near the end, you may come upon the proof goal,
   [ stackrep STACK nil st |-- emp ]

   This goal arises because the current assertion is,
    [ ... SEP(mem_mgr M gv;  stackrep STACK nil st)  ]
   but the postcondition of triang contains just,
   [ ... SEP(mem_mgr M gv) ].

  This is a symptom of the fact that the specifications and abstractions
  don't actually fit together!   There are three possible ways to fix
  the problem:

  - Adjust the postcondition of [triang] to [...SEP(mem_mgr M gv; TT)],
     which means that [triang] is permitted to have a "space leak".
     That is, [triang] may allocate things that it does not free.
  - Adjust the StackAPD with one more field in its Coq record:
     [stackrep_nil: forall st, stackrep STACK [] st |-- emp].
     This specifies that, whatever is the low-level representation
     of a stack, the empty stack will always use no memory.
     Although that is true of our [stack2.c] implementation, one
     can easily imagine other implementations of stacks in which
     that is not true.  Therefore, this design choice limits the
     generality of the interface.
  - Adjust the Stack API with another function, [freestack],
     perhaps with precondition [SEP(mem_mgr M gv; stackrep STACK st)]
     and postcondition [SEP(mem_mgr M gv)].  Then call this at the
     end of the [triang] function.

   Any one of these choices is a legitimate software-engineering
   design decision, but the point is that _some_ choice must be made,
   otherwise this collection of modules (stack, triang) can't be verified.

   As a work-around, you can finish the verification of body_triang
   by assuming this axiom: *)

Axiom stackrep_nil: forall st, stackrep STACK [] st |-- emp.



Lemma body_triang: semax_body Triang_Vprog Triang_Gprog f_triang (triang_spec M).
(* FILL IN HERE *) Admitted.
(** [] *)

Definition TriangVSU: @VSU NullExtension.Espec nil Triang_imports
     ltac:(QPprog prog) (TriangASI M) emp.
Proof.
(** with the right definition of [body_push_increasing] etc. this will work: *)
(* mkVSU prog Triang_internals.
 + solve_SF_internal body_push_increasing.
   solve_SF_internal body_push_increasing.
 + solve_SF_internal body_pop_and_add.
 + solve_SF_internal body_triang. *)
(* FILL IN HERE *) Admitted.

End Triang_VSU.

(* ================================================================= *)
(** ** Next Chapter: [VSU_stdlib] *)

(* 2023-03-25 11:30 *)
