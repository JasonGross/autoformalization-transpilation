(** * VSU_main: linking all the VSUs together with main VSU *)

(** This file is not only a VSU for the "main" function, but also shows
  how to link all the VSUs together to make a complete verified program.

  The [main()] function is special, in VST's separation logic, in that the SEP clause
  of its precondition contains _all_ the global variables of _all_ the modules.

  That won't be very noticeable in this example (stdlib/stack/triang/main), because
  none of the modules has global variables.  But in general, each module has its own
  "extern" or "static" global variables, initialized or default-zero-initialized.  They 
  constitute the initial footprint (in the separation-logic sense) of the program.

   We might expect that each module -- each .c file, or each VSU -- manages (some
  subset of) its own global variables as "private with a hidden representation".
  Clients of the module can refer to this using an abstract predicate, an APD.

   Indeed, the [mem_mgr] predicate serves exactly this role:  it serves as an
   abstraction for the data structures that the malloc/free system uses to manage
   its free-list.  When we write,

     Precondition: PROP ... LOCAL ... SEP(mem_mgr M gv; other_stuff)
       p = malloc(n);
     Precondition: PROP ... LOCAL ... SEP(data_at ...; mem_mgr M gv; other_stuff)

   the [mem_mgr M gv] in the postcondition stands for a _different state_ of the
   free-list (with one item removed from it) compared to the [mem_mgr M gv] in
   the precondition.

   When verifying any program in VST, the precondition of main (written as [main_pre]) 
   contains all of these global variables.  The [start_function] tactic
   for VSUs has the job of abstracting these into into module-specific APDs,
   using the mkInitPred lemma that comes with each VSU, as you will see. *)

(* ################################################################# *)
(** * The VSU for main *)

(** This VSU has the standard preamble: *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VC.main2.
Require VC.stdlib VC.stack2 VC.triang2.
Require VC.Spec_stdlib VC.Spec_stack VC.Spec_triang.
(* ================================================================= *)
(** ** Funspec for main function *)

(** Because the funspec for main refers to all the initial values of all
    the global variables of all the modules, before writing [main_spec]
    we must link all the modules together into a single program. *)

(** First, gain access to the VSUs that we have built. *)
Require VC.VSU_stdlib VC.VSU_stack VC.VSU_triang.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.

(** Those VSUs are parametrized by Abstract Predicate Definitions (APDs),
  - [M],  the internal data representation of the malloc/free library, and
  - [STACK], the internal data representation of the stack module.
  For example, the StackVSU is parametrized by M, and the TriangVSU is
  parametrized by both M and STACK.

 But now in linking the whole program together, we must instantiate those
 parameters with the actual representations defined in their respective VSUs: *)

Definition M : Spec_stdlib.MallocFreeAPD := VSU_stdlib.M.
Definition STACK : Spec_stack.StackAPD := VSU_stack.STACK M.
Definition stackVSU := VSU_stack.StackVSU M.
Definition triangVSU := VSU_triang.TriangVSU M STACK.
(** Each VSU has
  - [Externs] :   functions entirely external to the whole C program, such as system calls
               and assembly-language functions that we won't prove in VST.  The
               function-specifications (funspecs) that we give for these functions are
               _axioms_  (but see "Connecting Higher-Order Separation Logic to a 
               First-Order Outside World" by Mansky et al. 2020 to see how these axioms
               can be proved as theorems in Coq).
  - [Imports]:  functions external to _this_ module, but which will be proved in other VSUs;
               the [Imports] list says what funspecs we assume about them.
  - [Exports]:  functions exported from this module, with funspecs guaranteed by proofs.
  - [G]:   funspecs of _internal_ functions of the module.  Since these functions are
        not exported, not used in other modules, we don't need to "publish" these
        funspecs; they existed only in support of [semax_body] proofs of the exported
         functions.  Therefore, the [G] list is private to the VSU, and hidden by Coq's
         opacity mechanisms.

   Let's examine the Externs, Imports, and Exports of StackVSU and TriangVSU: *)

Eval hnf in VSU_Externs stackVSU.   (* nil *)
Eval hnf in VSU_Imports stackVSU.   (* malloc, free, exit *)
Eval hnf in VSU_Exports stackVSU.   (* newstack, push, pop *)

Eval hnf in VSU_Externs triangVSU.   (* nil *)
Eval hnf in VSU_Imports triangVSU.   (* newstack, push, pop *)
Eval hnf in VSU_Exports triangVSU.   (* triang *)

(** We link together [stackVSU] and [triangVSU] to make [stacktriangVSU1]: *)

Definition stacktriangVSU1 := ltac:(linkVSUs stackVSU triangVSU).

(** When we link VSUs, C=linkVSUs(A,B),  the Imports of C are the union of
   the Imports of A and B, _minus_ the defined functions (and externs) of A and B.
   So, for example, newstack,push,pop are imported by triangVSU,
  but they are not in the Imports of stacktriangVSU because they are provided 
  by stackVSU.

  Similarly, the Exports of C are the union of the Exports of A and B. *)

Eval simpl in VSU_Externs stacktriangVSU1.  (* nil *)
Eval simpl in VSU_Imports stacktriangVSU1.  (* malloc, free, exit *)
Eval simpl in VSU_Exports stacktriangVSU1.  (* newstack, push, pop, triang *)

(** If we view stack+triang as a module, then what is the client view?
   (Hint:  the client is main.c, so what functions does main() call?)
  The client computes the triangular number of N.  So therefore this module
  should not export [newstack,push,pop] to the client; it should export only
  [triang].  The stack functions are there only to support the triang function.

  To make a stack+triang  VSU that exports only triang, we start with 
  stacktriangVSU1, and privatize the three functions that we want to hide
  from clients.  As follows: *)

Definition stacktriangVSU :=
 privatizeExports stacktriangVSU1
  [stack2._newstack; stack2._push; stack2._pop].

(** Having done that, we can examine the exports of this new VSU: *)

Eval simpl in VSU_Exports stacktriangVSU.   (* triang *)

(** Next, let's examine the MallocFreeVSU:  *)

Eval hnf in VSU_Externs VSU_stdlib.MallocFreeVSU.  (* malloc, free, exit *)
Eval hnf in VSU_Imports VSU_stdlib.MallocFreeVSU.  (* nil *)
Eval hnf in VSU_Exports VSU_stdlib.MallocFreeVSU.  (* malloc, free, exit *)

(** What we learn here (which we could have known already by reading VSU_stdlib.v)
   is that malloc,free,exit are _external_ functions, not implemented within the
   entire C program we are verifying.  Once the MallocFree module (stdlib.c)
   re-exports them, the clients (such as stackVSU) will treat them as ordinary Imports,
   not knowing the difference.  *)

(**  We link the stacktriangVSU with the MallocFreeVSU.   We can do the privateExports
    step at the same time, without needing a separate Definition. *)

Time Definition coreVSU := 
   privatizeExports
   ltac:(linkVSUs stacktriangVSU VSU_stdlib.MallocFreeVSU)
  [stdlib._malloc; stdlib._free; stdlib._exit] .

Eval simpl in VSU_Externs coreVSU.  (* malloc, free, exit *)
Eval simpl in VSU_Imports coreVSU.  (* nil *)
Eval simpl in VSU_Exports coreVSU.  (* triang *)

(** We call this the "core" VSU for a specific reason:  It's everything except main().
   We have to treat main() specially, because the [main] function is the one that
   receives the initial values of all the global variables -- even the ones in other
  modules.  This is just a feature of how Separation Logic accounts for these variables.

   So therefore, the "recipe" is this:  First, construct the coreVSU that includes
   everything except main;  then construct the whole_prog that's the entire
   program including main: *)

Time Definition whole_prog := ltac:(QPlink_progs (QPprog prog) (VSU_prog coreVSU)).

(** The main point about whole_prog is that it contains the intializers for
   every global variable _including_ main.  

   The funspec for [main] should have precondition [main_pre p z gv], where
  - [p] is the program (e.g., all the .c files linked together),
  - [z] is the "external oracle" characterizing the initial state of the outside world,
  - [gv] is the usual global-variable mapping.

 Because our stacktriang program doesn't interact with the outside world, the type of its
 external oracle can be simply [unit], and for [z] we can use [tt].   Which is to say,
 we have been using NullExtension.Espec as the Espec for all our VSUs in this program,
 and [@OK_ty NullExtension.Espec = tt].

 The definition [main_pre p z gv] calculates a separation-logic mpred that characterizes
 all the initialized global variables of the program [p].

 The postcondition of [main_spec], in this case, says that it returns the
 10th triangular number. *)

Definition main_spec :=
 DECLARE _main
 WITH gv: globals
 PRE [ ] main_pre whole_prog tt gv
 POST[ tint ]
    PROP()
    RETURN (Vint (Int.repr 55))
    SEP(TT).

(** Soon we will prove [semax_body V G f_main main_spec],  where [f_main]
   is the function-body from main.c, and main_spec is the funspec just above. *)

Locate f_main.  (* VC main2.f_main *)

(** In order to prove a semax_body, we need a CompSpecs (which is an implicit
  parameter of @semax_body).  We compute this in the ordinary way from
   VC.main2.prog, just as you would in any module.  *)
#[export] Instance Compspecs: compspecs. make_compspecs VC.main2.prog. Defined.

(** It's important to build this [Instance] _after_ the [Require] statements just above,
 so that this is the [compspecs] instance that typeclass-resolution will find, instead
 of finding [VSU_stdlib.CompSpecs], [VSU_stack.CompSpecs], etc. *)

(** The [body_main] lemma will need a Vprog, which in this case must
  be the [varspecs] for the whole program: *)

Definition Vprog: varspecs := QPvarspecs whole_prog.

(** The Gprog for main is, as usual, the funspecs of all the functions in this
   module plus the Imports of this module. *)

Definition Main_imports: funspecs := Spec_triang.TriangASI M.
Definition Main_Gprog : funspecs := main_spec :: Main_imports.

(* ################################################################# *)
(** * Proof of body_main *)

(** The [semax_body] proof for [main] is _almost_ like any other,
 except that before [start_function] we do [pose proof Core_VSU].
 This signals to [start_function] that it can use the [mkInitPred]
 lemmas from [Core_VSU] to process all the global variables *)

Lemma body_main: semax_body Vprog Main_Gprog f_main main_spec.
Proof.
pose coreVSU.
start_function.
fold M.  (* See "Exercise: Delete" below to see why this is needed *)

(** Now the SEP clause of the precondition is, [ (Spec_stdlib.mem_mgr M gv; has_ext tt) ]

 In general, there will be one clause for each VSU that has a
 state predicate, plus a [has_ext] clause to characterize the
 external world.  In this program, which does no I/O, the
 external world is trivial, characterized by the unit value [tt].
 In this program, just one of the modules has a state predicate;
 that's the [stdlib] module with its [mem_mgr] predicate.
 That was put into the SEP clause by [start_function], signalled
 to do so by [pose proof Core_VSU]. *)

(** Now, as usual prove correctness of the function body.  Start with a
  [forward_call(XX)] to the [triang] function.  The parameter XX will 
 depend on what you have put in the WITH clause of the [triang_spec]
 in [Spec_triang]. *)
(* FILL IN HERE *) Admitted.

(** Exercise:  Once you've finished the proof of [body_main], go back and delete the
   [fold M] near the top of [body_main], and proceed to the point immediately
  after the [forward_call].  You'll probably see an extra proof obligation here, 
  which is provable by (fold M; cancel).   That suggests why the [fold M] is
  useful at the top of the function. *)

(* ################################################################# *)
(** * The Main Component, the Whole Component *)

(** There are several different concepts (and types) here:
  - [Clight.program]   is the Abstract Syntax Tree (AST) of a Clight program 
                as produced by clightgen;
  - [QP.program]  is an alternate version of that AST that's more
                efficient to link computationally in Coq;
  - [Component] is a set of correctness proofs (and other property proofs) about
                a QP.program;
  - [VSU] is a [Component] with its internal funspecs hidden by Coq's abstraction
       mechanism (sigT), and with the component's varspecs in a standard form.

  Unlike ordinary modules, we don't turn main.c (or the module containing main())
  into a VSU; it's slightly nonstandard because it imports the "varspecs" of all
  the other modules (i.e., global-variable-initializer specifications).   We make
  a [Component]. *)

Definition MainComp:  MainCompType nil ltac:(QPprog prog) coreVSU whole_prog (snd main_spec) emp.
Proof.
mkComponent prog.
(** Now, for each function in the Main module, we have a solve_SF_internal just
   as we would (for ordinary components) after [mkVSU]. *)
- solve_SF_internal body_main.
Qed.

(** The arguments of MainCompType (above) are,
    -  nil,   the Externs of Main, just in case main() calls some system-calls directly
                  (in this case, there are none);
    - (QPprog prog),   the main.c program,
    - coreVSU,   the VSU of the entire program except main.c;
    - whole_prog,   the whole program including main.c+core;
    - snd main_spec,  the funspec of the main function;
    - emp,   the separation-logic characterization of all the global variables 
                     of main.c (in this case, there are none).  
*)

(** Having made the Main component, we link it with the coreVSU to form the
    Component corresponding to the whole program. *)

Lemma WholeComp: WholeCompType coreVSU MainComp.
Proof. proveWholeComponent. Qed.

(* ################################################################# *)
(** * Soundness! *)

Import SeparationLogicSoundness.VericMinimumSeparationLogic.CSHL_Defs.
Require Import VST.veric.SequentialClight.

(** VST's program logic is proved sound with respect to the operational semantics
   of Clight.  That means, 
  - if you prove in VST that some program satisfies its specification, written
      as [@semax_prog Espec CompSpecs prog init V G]
  - then (in the operational semantics of CompCert Clight) it will behave 
      according to that specification. *)

About semax_prog.   (*
   semax_prog : forall {Espec : OracleKind},
          compspecs -> Clight.program -> OK_ty -> varspecs -> funspecs -> Prop *)

(** [semax_prog] basically means that all the function-bodies in prog satisfy their
      funspecs in G, along with some other useful side-conditions. *)

(** If we could just prove [semax_prog] about a program, then we could apply
 the following soundness theorem to prove it runs correctly: *)
Check whole_program_sequential_safety_ext.

(** That's a complicated theorem-statement, but the main premise is
   -  [semax_prog prog initial_oracle V G]
   meaning "you proved the program correct",  and the main conclusion is
   -  [step_lemmas.dry_safeN ...]
   meaning "the program runs safely, interacting correctly as specified 
   with its external environment."

   What we want from the VSU system is a proof that the C program you get by
   linking all these VSUs together (with the MainComponent) satisfies [semax_prog]. 
   And here is that theorem: *)

Lemma WholeProgSafe: WholeProgSafeType WholeComp tt.
Proof.  proveWholeProgSafe. Qed.

(** And you can see what was just proved by unfolding WholeProgSafeType: *)

Eval red in (WholeProgSafeType WholeComp tt).
(*   {G : funspecs
       | semax_prog (prog_of_component WholeComp) tt (QPvarspecs whole_prog) G} *)

(** or in other words, there exists a complete set [G] of funspecs (for all the
    functions in the program) such that the Clight program corresponding to 
    the WholeComponent is proved correct.  Now we could apply 
    [whole_program_sequential_safety_ext] to get the corollary that the program
   runs correctly. *)

(* ================================================================= *)
(** ** Next Chapter: [VSU_stdlib2] *)

(* 2023-03-25 11:30 *)
