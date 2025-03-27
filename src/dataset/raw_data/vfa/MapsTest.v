Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From VFA Require Import Maps.

Parameter MISSING: Type.

Module Check.

Ltac check_type A B :=
    match type of A with
    | context[MISSING] => idtac "Missing:" A
    | ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"]
    end.

Ltac print_manual_grade A :=
    match eval compute in A with
    | Some (_ ?S ?C) =>
        idtac "Score:"  S;
        match eval compute in C with
          | ""%string => idtac "Comment: None"
          | _ => idtac "Comment:" C
        end
    | None =>
        idtac "Score: Ungraded";
        idtac "Comment: None"
    end.

End Check.

From VFA Require Import Maps.
Import Check.

Goal True.

idtac "-------------------  t_apply_empty  --------------------".
idtac " ".

idtac "#> t_apply_empty".
idtac "Possible points: 1".
check_type @t_apply_empty (
(forall (A : Type) (x : nat) (v : A), @eq A (@t_empty A v x) v)).
idtac "Assumptions:".
Abort.
Print Assumptions t_apply_empty.
Goal True.
idtac " ".

idtac "-------------------  t_update_eq  --------------------".
idtac " ".

idtac "#> t_update_eq".
idtac "Possible points: 1".
check_type @t_update_eq (
(forall (A : Type) (m : total_map A) (x : nat) (v : A),
 @eq A (@t_update A m x v x) v)).
idtac "Assumptions:".
Abort.
Print Assumptions t_update_eq.
Goal True.
idtac " ".

idtac "-------------------  t_update_neq  --------------------".
idtac " ".

idtac "#> t_update_neq".
idtac "Possible points: 1".
check_type @t_update_neq (
(forall (X : Type) (v : X) (x1 x2 : nat) (m : total_map X)
   (_ : not (@eq nat x1 x2)), @eq X (@t_update X m x1 v x2) (m x2))).
idtac "Assumptions:".
Abort.
Print Assumptions t_update_neq.
Goal True.
idtac " ".

idtac "-------------------  t_update_shadow  --------------------".
idtac " ".

idtac "#> t_update_shadow".
idtac "Possible points: 1".
check_type @t_update_shadow (
(forall (A : Type) (m : total_map A) (v1 v2 : A) (x : nat),
 @eq (total_map A) (@t_update A (@t_update A m x v1) x v2)
   (@t_update A m x v2))).
idtac "Assumptions:".
Abort.
Print Assumptions t_update_shadow.
Goal True.
idtac " ".

idtac "-------------------  t_update_same  --------------------".
idtac " ".

idtac "#> t_update_same".
idtac "Possible points: 1".
check_type @t_update_same (
(forall (X : Type) (x : nat) (m : total_map X),
 @eq (total_map X) (@t_update X m x (m x)) m)).
idtac "Assumptions:".
Abort.
Print Assumptions t_update_same.
Goal True.
idtac " ".

idtac "-------------------  t_update_permute  --------------------".
idtac " ".

idtac "#> t_update_permute".
idtac "Possible points: 1".
check_type @t_update_permute (
(forall (X : Type) (v1 v2 : X) (x1 x2 : nat) (m : total_map X)
   (_ : not (@eq nat x2 x1)),
 @eq (total_map X) (@t_update X (@t_update X m x2 v2) x1 v1)
   (@t_update X (@t_update X m x1 v1) x2 v2))).
idtac "Assumptions:".
Abort.
Print Assumptions t_update_permute.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 6".
idtac "Max points - advanced: 6".
idtac "".
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "functional_extensionality_dep".
idtac "FunctionalExtensionality.functional_extensionality_dep".
idtac "int".
idtac "Abs".
idtac "Abs_inj".
idtac "ltb".
idtac "ltb_lt".
idtac "leb".
idtac "leb_le".
idtac "Extract.int".
idtac "Extract.Abs".
idtac "Extract.Abs_inj".
idtac "Extract.ltb".
idtac "Extract.ltb_lt".
idtac "Extract.leb".
idtac "Extract.leb_le".
idtac "".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "Below is a summary of the automatically graded exercises that are incomplete.".
idtac "".
idtac "The output for each exercise can be any of the following:".
idtac "  - 'Closed under the global context', if it is complete".
idtac "  - 'MANUAL', if it is manually graded".
idtac "  - A list of pending axioms, containing unproven assumptions. In this case".
idtac "    the exercise is considered complete, if the axioms are all allowed.".
idtac "".
idtac "********** Standard **********".
idtac "---------- t_apply_empty ---------".
Print Assumptions t_apply_empty.
idtac "---------- t_update_eq ---------".
Print Assumptions t_update_eq.
idtac "---------- t_update_neq ---------".
Print Assumptions t_update_neq.
idtac "---------- t_update_shadow ---------".
Print Assumptions t_update_shadow.
idtac "---------- t_update_same ---------".
Print Assumptions t_update_same.
idtac "---------- t_update_permute ---------".
Print Assumptions t_update_permute.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2025-01-06 19:52 *)

(* 2025-01-06 19:52 *)
