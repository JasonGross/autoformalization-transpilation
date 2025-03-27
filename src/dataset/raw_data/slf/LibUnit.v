(* This file is extracted from the TLC library.
   http://github.com/charguer/tlc
   DO NOT EDIT. *)

(**************************************************************************
* Product of Data Structures                                              *
**************************************************************************)

Set Implicit Arguments.
From SLF Require Import LibTactics LibLogic LibReflect.

(* ********************************************************************** *)
(* ################################################################# *)
(** * Unit type *)

(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(** ** Definition *)

(** From the Prelude.

  Inductive unit : Type :=
    | tt : unit.

  Add Printing If bool.
  Delimit Scope bool_scope with bool.

*)

(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(** ** Inhabited *)

#[global]
Instance Inhab_unit : Inhab unit.
Proof using. intros. apply (Inhab_of_val tt). Qed.

(* ********************************************************************** *)
(* ################################################################# *)
(** * Properties *)

(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(** ** Uniqueness *)

Lemma unit_eq : forall (tt1 tt2 : unit),
  tt1 = tt2.
Proof using. intros. destruct tt1. destruct~ tt2. Qed.



(* 2024-12-26 10:22 *)
