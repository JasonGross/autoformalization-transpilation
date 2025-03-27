(** * VSU_stdlib: Axiomatization of malloc/free/exit *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VC.stdlib.
Require Import VC.Spec_stdlib.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.

(** The VSU for external axiomatized functions is much like any
 other VSU, except that we use [Axiom]s instead of [Definition]s
 and [Lemma]s.

 Because this VSU does not import any APDs, we don't need a [Section].

 Normally at this point, we would construct an [M] showing how the
 [mem_mgr] predicate is implemented.  But here we just axiomatize: *)

Axiom M: MallocFreeAPD.

Axiom make_mem_mgr: forall gv, emp |-- mem_mgr M gv.

(** Normally at this point, we would prove a [semax_body] lemma for each
  function that the module exports.  But here, we use [body_lemma_of_funspec]
  for external functions; and we write this as an axiom: *)
   
Axiom body_malloc:
 forall {Espec: OracleKind} {cs: compspecs} ,
   VST.floyd.library.body_lemma_of_funspec EF_malloc (snd (malloc_spec_sz M)).

Axiom body_free:
 forall {Espec: OracleKind} {cs: compspecs} ,
   VST.floyd.library.body_lemma_of_funspec EF_free (snd (free_spec_sz M)).

Axiom body_exit:
 forall {Espec: OracleKind},
  VST.floyd.library.body_lemma_of_funspec
    (EF_external "exit" (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
    (snd (exit_spec)).

(* ================================================================= *)
(** ** Internal functions *)

(** There is one internal (nonexported) function, so as usual we must write
  a funspec for it.  That is, the [placeholder], which is a useless function
  whose only purpose was to force [clightgen] to keep the external declarations
  for [malloc], [free], [exit].  Because nobody will call [placeholder()], we
 can give it a trivial funspec whose precondition is [False]. *)

Definition placeholder_spec :=
    (_placeholder, vacuous_funspec (Internal f_placeholder)).

(* ================================================================= *)
(** ** Definining the pieces of a VSU

    And now, in the usual way, we can put totether the pieces: *)

  Definition MF_ASI: funspecs := MallocFreeASI M.
  Definition MF_imported_specs:funspecs :=  nil.
  Definition MF_internal_specs: funspecs := placeholder_spec::MF_ASI.
  Definition MF_globals: globals -> mpred:= Spec_stdlib.mem_mgr M.
  Definition MFVprog : varspecs. mk_varspecs prog. Defined.
  Definition MFGprog: funspecs := MF_imported_specs ++ MF_internal_specs.

(* ################################################################# *)
(** * Constructing the Component and the VSU *)

(** This lemma is required for the [solve_SF_external (body_malloc)] below.
     The basic purpose is to ensure that the postcondition of the external
     function ensures a return value that's strictly compatible with the calling
     conventions specified by the C-language return-type of the function.
     The particular form of the lemma is derived from the proof goal
     of solve_SF_external below.
 *)

Lemma semax_func_cons_malloc_aux {cs: compspecs} (gv: globals)
         (gx : genviron) (ret : option val) n:
 (EX x : val,
  (PROP ( )
   RETURN (x) SEP (mem_mgr M gv;
             if eq_dec x nullval
             then emp
             else malloc_token_sz M Ews n x * memory_block Ews n x))
    (make_ext_rval gx (rettype_of_type (tptr tvoid)) ret)) &&
  !! Builtins0.val_opt_has_rettype ret
     (rettype_of_type (tptr tvoid))
 |-- !! tc_option_val (tptr tvoid) ret.
Proof.
 intros.
 Intros p.
 rewrite <- insert_local.
 rewrite lower_andp.
 apply derives_extract_prop; intro.
 red in H0; unfold_lift in H0; destruct H0.
 destruct ret; try contradiction.
 unfold eval_id in H0; simpl in H0. subst v.
 if_tac. rewrite H0; entailer!.
 renormalize. entailer!.
 simpl. auto.
Qed.

  Definition MF_E : funspecs := MF_ASI.

(**  Each VSU may have private global variables that constitute its
  "local state".  This [VSU_initializer] lemma calculates how to
  reason about their initial values.   But the module stdlib.c does 
  not have any global variables, so this [initialize] lemma is
  rather trivial here.  See [VSU_stdlib2.v], lemma [initialize],
  for a more interesting example. *)

Lemma initialize: VSU_initializer prog MF_globals.
Proof.
InitGPred_tac.
apply make_mem_mgr.
Qed.

(** Now that all the subcomponents are ready, we can bundle up the VSU: *)

Definition MallocFreeVSU: @VSU NullExtension.Espec
         MF_E MF_imported_specs ltac:(QPprog prog) MF_ASI MF_globals.
  Proof. 
    mkVSU prog MF_internal_specs.
    - solve_SF_external (@body_malloc NullExtension.Espec CompSpecs).
       apply (semax_func_cons_malloc_aux gv gx ret n).
    - solve_SF_external (@body_free NullExtension.Espec CompSpecs).
    - solve_SF_external (@body_exit NullExtension.Espec).
    - apply initialize.
Qed.

(* ================================================================= *)
(** ** Next Chapter: [VSU_main] *)

(* 2023-03-25 11:30 *)
