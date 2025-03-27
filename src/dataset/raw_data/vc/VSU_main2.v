(** * VSU_main2: linking with stdlib2 instead of with stdlib *)

(**  In this chapter we link the stack/triang program with 
  stdlib2 (our internal implementation of malloc/free/exit) instead
 of with stdlib (which axiomatizes malloc/free/exit as external functions).

  Both programs use the exact same main.c program: 

#include <stddef.h>
#include "stdlib.h"
#include "stack2.h"
#include "triang2.h"

int main(void) {
  return triang(10);
}

and the only difference would be in the Makefile, the Unix [ld] or [cc] command
would link the programs together with stdlib2.o instead of stdlib.o.

The Coq code in this chapter is practically the same as in [VSU_main],
since the client program (main.c) should be oblivious of private data
representations (etc.) of the stdlib module. The only difference is that
in some places it says [stdlib2] instead of [stdlib].

In addition, we illustrate a new concept, restrictExports, a more general 
mechanism than privatizeExports. *)

(* ################################################################# *)
(** * The VSU for main *)

(** This VSU has the standard preamble: *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VC.main2.
Require VC.stdlib2 VC.stack2 VC.triang2.
Require VC.Spec_stdlib VC.Spec_stack VC.Spec_triang.

Require VC.VSU_stdlib2 VC.VSU_stack VC.VSU_triang.
#[export] Instance Compspecs: compspecs. make_compspecs VC.main2.prog. Defined.

Definition M : Spec_stdlib.MallocFreeAPD := VSU_stdlib2.M.
Definition STACK : Spec_stack.StackAPD := VSU_stack.STACK M.

Time Definition stacktriangVSU1 := ltac:(linkVSUs 
         (VSU_stack.StackVSU M) (VSU_triang.TriangVSU M STACK)). 
   (* 1.98 seconds to 6  seconds  *)

(* ================================================================= *)
(** ** An alternate way to adjust the Exports of a VSU *)

(** Recall that in [VSU_main] we needed to restrict the Exports list
   of [stacktriangVSU1], to obtain [stacktriangVSU].  We did this using
   [privatizeExports].  But sometimes one _also_ wants to restrict the
   Exports list in a different way: weaken some of the funspecs using
   funspec_sub, to provide more abstraction (give the client less information).

    In this stack+triang+main program, we have no need to do that, but
    we illustrate the process. *)

Check restrictExports. (* :  VSU E Imports p Exports GP -> funspecs -> Type *)

Check prove_restrictExports. (*
 : forall (v: VSU ?E ?Imports ?p ?Exports ?GP )
          (Exports': funspecs),
       list_norepet (map fst Exports') ->
       Forall (funspec_sub_in ?Exports) Exports' ->
       restrictExports v Exports'  *)

(** Given a VSU v,  [restrictExports v Exports'] is the type of a new VSU
   whose Exports list has been replaced by Exports'.

  The lemma [prove_restrictExports] says,
  - if Exports' does not have any repeated identifiers, and
  - if for every (id,fspec') in Exports', there is an (id,fspec) in Exports
       such that funspec_sub (fspec,fspec'),
  - then there is a new VSU whose exports is Exports'. 

  We will now use this to build [stacktriangVSU].  *)

Eval simpl in VSU_Exports stacktriangVSU1.  (* newstack, push, pop, triang *)

Lemma stacktriangVSU: 
   restrictExports stacktriangVSU1
   (Spec_triang.TriangASI M).
Proof.
prove_restrictExports.
(** At this point, we must prove [funspec_sub] for every (id,fspec') in
  the TriangASI.  There is just one, namely  [triang_spec].  So just
  one bulleted subgoal.  And because (in this use of restrictExports)
  we did not change the funspec between Exports and Exports',
  we can use [funspec_sub_refl] to prove it. *)
- apply funspec_sub_refl.
Qed.

Eval hnf in VSU_Exports stacktriangVSU.  (* newstack, push, pop, triang *)

(** For more significant uses of funspec_sub to adapt and abstract VSUs, see:
   "Verified Software Units", by Lennart Beringer, ESOP'21. *)

(* ================================================================= *)
(** ** End of digression about restrictExports *)

Time Definition coreVSU := 
   privatizeExports
   ltac:(linkVSUs stacktriangVSU VSU_stdlib2.MallocFreeVSU)
  [stdlib._malloc; stdlib._free; stdlib._exit] .

Time Definition whole_prog := ltac:(QPlink_progs (QPprog prog) (VSU_prog coreVSU)).
(** The funspec for [main] is just as it was in [VSU_main]. *)

Definition main_spec :=
 DECLARE _main
 WITH gv: globals
 PRE [ ] main_pre whole_prog tt gv
 POST[ tint ]
    PROP()
    RETURN (Vint (Int.repr 55))
    SEP(TT).

Definition Vprog: varspecs := QPvarspecs whole_prog.

Definition Main_imports: funspecs := Spec_triang.TriangASI M.
Definition Main_Gprog : funspecs := main_spec :: Main_imports.

Lemma body_main: semax_body Vprog Main_Gprog f_main main_spec.
(** Identical to the proof of [body_main] in [VSU_main]. *)
(* FILL IN HERE *) Admitted.

Definition MainComp:  MainCompType nil ltac:(QPprog prog) coreVSU whole_prog (snd main_spec) emp.
Proof.
mkComponent prog.
solve_SF_internal body_main.
Qed.

Lemma WholeComp: WholeCompType coreVSU MainComp.
Proof. proveWholeComponent. Qed.

Lemma WholeProgSafe: WholeProgSafeType WholeComp tt.
Proof. proveWholeProgSafe. Qed.

Eval red in WholeProgSafeType WholeComp tt.

(* 2023-03-25 11:30 *)
