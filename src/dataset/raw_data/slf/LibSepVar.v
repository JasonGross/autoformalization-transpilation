(** * LibSepVar: Appendix - Program Variables *)

Set Implicit Arguments.
From SLF Require LibListExec.
From SLF Require Export LibString LibList LibCore.
From SLF Require Import LibSepFmap LibSepTLCbuffer.
Open Scope string_scope.
Generalizable Variables A.

(* ################################################################# *)
(** * Representation of Program Variables *)

(** This file contains definitions, lemmas, tactics and notations for
    manipulating program variables and list of program variables. *)

(* ================================================================= *)
(** ** Representation of Variables *)

(** Variables are represented as strings *)

Definition var : Type := string.

(** The boolean function [var_eq s1 s2] compares two variables. *)

Definition var_eq (s1:var) (s2:var) : bool :=
  if String.string_dec s1 s2 then true else false.

(** The boolean function [var_eq s1 s2] returns [true] iff the
    equality [v1 = v2] holds. *)

Lemma var_eq_spec : forall s1 s2,
  var_eq s1 s2 = isTrue (s1 = s2).
Proof using.
  intros. unfold var_eq. case_if; rew_bool_eq~.
Qed.

Global Opaque var.

(* ================================================================= *)
(** ** Tactic [case_var] *)

(** The tactic [case_var] performs case analysis on expressions of the
    form [if var_eq x y then .. else ..] that appear in the goal. *)

Tactic Notation "case_var" :=
  repeat rewrite var_eq_spec in *; repeat case_if.

Tactic Notation "case_var" "~" :=
  case_var; auto_tilde.

Tactic Notation "case_var" "*" :=
  case_var; auto_star.

(* ################################################################# *)
(** * Representation of List of Variables *)

(* ================================================================= *)
(** ** Definition of Distinct Variables *)

(** [vars] is the type of a list of variables *)

Definition vars : Type := list var.

(** [var_fresh y xs] asserts that [y] does not belong to the list [xs] *)

Definition var_fresh (y:var) (xs:vars) : Prop :=
  ~ mem y xs.

(** The following lemma asserts that if [x] is a variable in the list [xs],
    and [y] is fresh from this list [xs], then [y] is not equal to [x]. *)

Lemma var_fresh_mem_inv : forall y x xs,
  var_fresh x xs ->
  mem y xs ->
  x <> y.
Proof using. introv H M N. unfolds var_fresh. subst*. Qed.

(* ================================================================= *)
(** ** Generation of [n] Distinct Variables *)

(** [nat_to_var n] converts [nat] values into distinct [name] values. *)

Definition dummy_char :=
  Ascii.ascii_of_nat 0%nat.

Fixpoint nat_to_var (n:nat) : var :=
  match n with
  | O => String.EmptyString
  | S n' => String.String dummy_char (nat_to_var n')
  end.

Lemma injective_nat_to_var :
  injective nat_to_var.
Proof using.
  intros n. induction n as [|n']; intros m E; destruct m as [|m']; tryfalse.
  { auto. }
  { inverts E. fequals~. }
Qed.

(** [var_seq i n] generates a list of variables [x1;x2;..;xn] with [x1=i] and
    [xn=i+n-1]. The ability to start at a given offset is sometimes useful. *)

Fixpoint var_seq (start:nat) (nb:nat) : vars :=
  match nb with
  | O => nil
  | S nb' => (nat_to_var start) :: var_seq (S start) nb'
  end.

(** The properties of [var_seq] are stated next. They assert that this
    function produce the expected number of variables, that the variables
    are pairwise distinct *)

Section Var_seq.
Implicit Types start nb : nat.

Lemma var_fresh_var_seq_lt : forall (x:nat) start nb,
  (x < start)%nat ->
  var_fresh (nat_to_var x) (var_seq start nb).
Proof using.
  intros. unfold var_fresh. gen start. induction nb; simpl; introv N; rew_listx.
  { auto. }
  { simpl. case_var. rew_logic. split.
    { intros E. lets: injective_nat_to_var E. math. }
    { applys IHnb. math. } }
Qed.

Lemma var_fresh_var_seq_ge : forall (x:nat) start nb,
  (x >= start+nb)%nat ->
  var_fresh (nat_to_var x) (var_seq start nb).
Proof using.
  intros. unfold var_fresh. gen start. induction nb; simpl; introv N; rew_listx.
  { auto. }
  { simpl. case_var. rew_logic. split.
    { intros E. lets: injective_nat_to_var E. math. }
    { applys IHnb. math. } }
Qed.

Lemma noduplicates_var_seq : forall start nb,
  LibList.noduplicates (var_seq start nb).
Proof using.
  intros. gen start. induction nb; intros; simpl; rew_listx.
  { auto. }
  { split.
    { applys var_fresh_var_seq_lt. math. }
    { auto. } }
Qed.

Lemma length_var_seq : forall start nb,
  length (var_seq start nb) = nb.
Proof using.
  intros. gen start. induction nb; simpl; intros.
  { auto. } { rew_list. rewrite~ IHnb. }
Qed.

End Var_seq.

(* ################################################################# *)
(** * Notation for Program Variables *)

(** When writing deeply-embedded programs, it is nice to write identifiers
    (program variables) without quotes. In the future, the "Custom Entry"
    mechanism might allow for this in a generic manner. In the meantime,
    we need one definition or one notation for each identifier *)

(* ================================================================= *)
(** ** Program Variables Expressed Using Definitions *)

(** These definitions allowing to use the string notation ["x"] without
    any double quote or quotes. However, the scope of these definitions
    should be wrapped in a module to avoid clashes with local variables.
    E.g. [Module Export Foo. Import DefinitionsForVariables. (...) End Foo.] *)

Module DefinitionsForVariables.

Definition a := ("a":var).
Definition b := ("b":var).
Definition c := ("c":var).
Definition d := ("d":var).
Definition e := ("e":var).
Definition f := ("f":var).
Definition g := ("g":var).
Definition h := ("h":var).
Definition i := ("i":var).
Definition j := ("j":var).
Definition k := ("k":var).
Definition l := ("l":var).
Definition m := ("m":var).
Definition n := ("n":var).
Definition o := ("o":var).
Definition p := ("p":var).
Definition q := ("q":var).
Definition r := ("r":var).
Definition s := ("s":var).
Definition t := ("t":var).
Definition u := ("u":var).
Definition v := ("v":var).
Definition w := ("w":var).
Definition x := ("x":var).
Definition y := ("y":var).
Definition z := ("z":var).

Definition a1 := ("a1":var).
Definition b1 := ("b1":var).
Definition c1 := ("c1":var).
Definition d1 := ("d1":var).
Definition e1 := ("e1":var).
Definition f1 := ("f1":var).
Definition g1 := ("g1":var).
Definition h1 := ("h1":var).
Definition i1 := ("i1":var).
Definition j1 := ("j1":var).
Definition k1 := ("k1":var).
Definition l1 := ("l1":var).
Definition m1 := ("m1":var).
Definition n1 := ("n1":var).
Definition o1 := ("o1":var).
Definition p1 := ("p1":var).
Definition q1 := ("q1":var).
Definition r1 := ("r1":var).
Definition s1 := ("s1":var).
Definition t1 := ("t1":var).
Definition u1 := ("u1":var).
Definition v1 := ("v1":var).
Definition w1 := ("w1":var).
Definition x1 := ("x1":var).
Definition y1 := ("y1":var).
Definition z1 := ("z1":var).

Definition a2 := ("a2":var).
Definition b2 := ("b2":var).
Definition c2 := ("c2":var).
Definition d2 := ("d2":var).
Definition e2 := ("e2":var).
Definition f2 := ("f2":var).
Definition g2 := ("g2":var).
Definition h2 := ("h2":var).
Definition i2 := ("i2":var).
Definition j2 := ("j2":var).
Definition k2 := ("k2":var).
Definition l2 := ("l2":var).
Definition m2 := ("m2":var).
Definition n2 := ("n2":var).
Definition o2 := ("o2":var).
Definition p2 := ("p2":var).
Definition q2 := ("q2":var).
Definition r2 := ("r2":var).
Definition s2 := ("s2":var).
Definition t2 := ("t2":var).
Definition u2 := ("u2":var).
Definition v2 := ("v2":var).
Definition w2 := ("w2":var).
Definition x2 := ("x2":var).
Definition y2 := ("y2":var).
Definition z2 := ("z2":var).

Definition a3 := ("a3":var).
Definition b3 := ("b3":var).
Definition c3 := ("c3":var).
Definition d3 := ("d3":var).
Definition e3 := ("e3":var).
Definition f3 := ("f3":var).
Definition g3 := ("g3":var).
Definition h3 := ("h3":var).
Definition i3 := ("i3":var).
Definition j3 := ("j3":var).
Definition k3 := ("k3":var).
Definition l3 := ("l3":var).
Definition m3 := ("m3":var).
Definition n3 := ("n3":var).
Definition o3 := ("o3":var).
Definition p3 := ("p3":var).
Definition q3 := ("q3":var).
Definition r3 := ("r3":var).
Definition s3 := ("s3":var).
Definition t3 := ("t3":var).
Definition u3 := ("u3":var).
Definition v3 := ("v3":var).
Definition w3 := ("w3":var).
Definition x3 := ("x3":var).
Definition y3 := ("y3":var).
Definition z3 := ("z3":var).

(** Tactic to unfold these definitions. Useful to avoid the definitions
    to get in the way of [simpl]. *)

Ltac libsepvar_unfold :=
  unfold
  a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z,
  a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1, q1, r1, s1, t1, u1, v1, w1, x1, y1, z1,
  a2, b2, c2, d2, e2, f2, g2, h2, i2, j2, k2, l2, m2, n2, o2, p2, q2, r2, s2, t2, u2, v2, w2, x2, y2, z2,
  a3, b3, c3, d3, e3, f3, g3, h3, i3, j3, k3, l3, m3, n3, o3, p3, q3, r3, s3, t3, u3, v3, w3, x3, y3, z3.

End DefinitionsForVariables.

(* ================================================================= *)
(** ** Program Variables Expressed Using Notation, with a Quote Symbol *)

(** To avoid using the string notation ["x"] for refering to a
    variable called [x], one can use the notation ['x], available
    by importing the following module. *)

Declare Custom Entry trm.

Module NotationForVariables.

Declare Scope trm_scope.

Notation "''a'" := ("a":var) (in custom trm at level 0) : trm_scope.
Notation "''b'" := ("b":var) (in custom trm at level 0) : trm_scope.
Notation "''c'" := ("c":var) (in custom trm at level 0) : trm_scope.
Notation "''d'" := ("d":var) (in custom trm at level 0) : trm_scope.
Notation "''e'" := ("e":var) (in custom trm at level 0) : trm_scope.
Notation "''f'" := ("f":var) (in custom trm at level 0) : trm_scope.
Notation "''g'" := ("g":var) (in custom trm at level 0) : trm_scope.
Notation "''h'" := ("h":var) (in custom trm at level 0) : trm_scope.
Notation "''i'" := ("i":var) (in custom trm at level 0) : trm_scope.
Notation "''j'" := ("j":var) (in custom trm at level 0) : trm_scope.
Notation "''k'" := ("k":var) (in custom trm at level 0) : trm_scope.
Notation "''l'" := ("l":var) (in custom trm at level 0) : trm_scope.
Notation "''m'" := ("m":var) (in custom trm at level 0) : trm_scope.
Notation "''n'" := ("n":var) (in custom trm at level 0) : trm_scope.
Notation "''o'" := ("o":var) (in custom trm at level 0) : trm_scope.
Notation "''p'" := ("p":var) (in custom trm at level 0) : trm_scope.
Notation "''q'" := ("q":var) (in custom trm at level 0) : trm_scope.
Notation "''r'" := ("r":var) (in custom trm at level 0) : trm_scope.
Notation "''s'" := ("s":var) (in custom trm at level 0) : trm_scope.
Notation "''t'" := ("t":var) (in custom trm at level 0) : trm_scope.
Notation "''u'" := ("u":var) (in custom trm at level 0) : trm_scope.
Notation "''v'" := ("v":var) (in custom trm at level 0) : trm_scope.
Notation "''w'" := ("w":var) (in custom trm at level 0) : trm_scope.
Notation "''x'" := ("x":var) (in custom trm at level 0) : trm_scope.
Notation "''y'" := ("y":var) (in custom trm at level 0) : trm_scope.
Notation "''z'" := ("z":var) (in custom trm at level 0) : trm_scope.

Notation "''a1'" := ("a1":var) (in custom trm at level 0) : trm_scope.
Notation "''b1'" := ("b1":var) (in custom trm at level 0) : trm_scope.
Notation "''c1'" := ("c1":var) (in custom trm at level 0) : trm_scope.
Notation "''d1'" := ("d1":var) (in custom trm at level 0) : trm_scope.
Notation "''e1'" := ("e1":var) (in custom trm at level 0) : trm_scope.
Notation "''f1'" := ("f1":var) (in custom trm at level 0) : trm_scope.
Notation "''g1'" := ("g1":var) (in custom trm at level 0) : trm_scope.
Notation "''h1'" := ("h1":var) (in custom trm at level 0) : trm_scope.
Notation "''i1'" := ("i1":var) (in custom trm at level 0) : trm_scope.
Notation "''j1'" := ("j1":var) (in custom trm at level 0) : trm_scope.
Notation "''k1'" := ("k1":var) (in custom trm at level 0) : trm_scope.
Notation "''l1'" := ("l1":var) (in custom trm at level 0) : trm_scope.
Notation "''m1'" := ("m1":var) (in custom trm at level 0) : trm_scope.
Notation "''n1'" := ("n1":var) (in custom trm at level 0) : trm_scope.
Notation "''o1'" := ("o1":var) (in custom trm at level 0) : trm_scope.
Notation "''p1'" := ("p1":var) (in custom trm at level 0) : trm_scope.
Notation "''q1'" := ("q1":var) (in custom trm at level 0) : trm_scope.
Notation "''r1'" := ("r1":var) (in custom trm at level 0) : trm_scope.
Notation "''s1'" := ("s1":var) (in custom trm at level 0) : trm_scope.
Notation "''t1'" := ("t1":var) (in custom trm at level 0) : trm_scope.
Notation "''u1'" := ("u1":var) (in custom trm at level 0) : trm_scope.
Notation "''v1'" := ("v1":var) (in custom trm at level 0) : trm_scope.
Notation "''w1'" := ("w1":var) (in custom trm at level 0) : trm_scope.
Notation "''x1'" := ("x1":var) (in custom trm at level 0) : trm_scope.
Notation "''y1'" := ("y1":var) (in custom trm at level 0) : trm_scope.
Notation "''z1'" := ("z1":var) (in custom trm at level 0) : trm_scope.

Notation "''a2'" := ("a2":var) (in custom trm at level 0) : trm_scope.
Notation "''b2'" := ("b2":var) (in custom trm at level 0) : trm_scope.
Notation "''c2'" := ("c2":var) (in custom trm at level 0) : trm_scope.
Notation "''d2'" := ("d2":var) (in custom trm at level 0) : trm_scope.
Notation "''e2'" := ("e2":var) (in custom trm at level 0) : trm_scope.
Notation "''f2'" := ("f2":var) (in custom trm at level 0) : trm_scope.
Notation "''g2'" := ("g2":var) (in custom trm at level 0) : trm_scope.
Notation "''h2'" := ("h2":var) (in custom trm at level 0) : trm_scope.
Notation "''i2'" := ("i2":var) (in custom trm at level 0) : trm_scope.
Notation "''j2'" := ("j2":var) (in custom trm at level 0) : trm_scope.
Notation "''k2'" := ("k2":var) (in custom trm at level 0) : trm_scope.
Notation "''l2'" := ("l2":var) (in custom trm at level 0) : trm_scope.
Notation "''m2'" := ("m2":var) (in custom trm at level 0) : trm_scope.
Notation "''n2'" := ("n2":var) (in custom trm at level 0) : trm_scope.
Notation "''o2'" := ("o2":var) (in custom trm at level 0) : trm_scope.
Notation "''p2'" := ("p2":var) (in custom trm at level 0) : trm_scope.
Notation "''q2'" := ("q2":var) (in custom trm at level 0) : trm_scope.
Notation "''r2'" := ("r2":var) (in custom trm at level 0) : trm_scope.
Notation "''s2'" := ("s2":var) (in custom trm at level 0) : trm_scope.
Notation "''t2'" := ("t2":var) (in custom trm at level 0) : trm_scope.
Notation "''u2'" := ("u2":var) (in custom trm at level 0) : trm_scope.
Notation "''v2'" := ("v2":var) (in custom trm at level 0) : trm_scope.
Notation "''w2'" := ("w2":var) (in custom trm at level 0) : trm_scope.
Notation "''x2'" := ("x2":var) (in custom trm at level 0) : trm_scope.
Notation "''y2'" := ("y2":var) (in custom trm at level 0) : trm_scope.
Notation "''z2'" := ("z2":var) (in custom trm at level 0) : trm_scope.

Notation "''a3'" := ("a3":var) (in custom trm at level 0) : trm_scope.
Notation "''b3'" := ("b3":var) (in custom trm at level 0) : trm_scope.
Notation "''c3'" := ("c3":var) (in custom trm at level 0) : trm_scope.
Notation "''d3'" := ("d3":var) (in custom trm at level 0) : trm_scope.
Notation "''e3'" := ("e3":var) (in custom trm at level 0) : trm_scope.
Notation "''f3'" := ("f3":var) (in custom trm at level 0) : trm_scope.
Notation "''g3'" := ("g3":var) (in custom trm at level 0) : trm_scope.
Notation "''h3'" := ("h3":var) (in custom trm at level 0) : trm_scope.
Notation "''i3'" := ("i3":var) (in custom trm at level 0) : trm_scope.
Notation "''j3'" := ("j3":var) (in custom trm at level 0) : trm_scope.
Notation "''k3'" := ("k3":var) (in custom trm at level 0) : trm_scope.
Notation "''l3'" := ("l3":var) (in custom trm at level 0) : trm_scope.
Notation "''m3'" := ("m3":var) (in custom trm at level 0) : trm_scope.
Notation "''n3'" := ("n3":var) (in custom trm at level 0) : trm_scope.
Notation "''o3'" := ("o3":var) (in custom trm at level 0) : trm_scope.
Notation "''p3'" := ("p3":var) (in custom trm at level 0) : trm_scope.
Notation "''q3'" := ("q3":var) (in custom trm at level 0) : trm_scope.
Notation "''r3'" := ("r3":var) (in custom trm at level 0) : trm_scope.
Notation "''s3'" := ("s3":var) (in custom trm at level 0) : trm_scope.
Notation "''t3'" := ("t3":var) (in custom trm at level 0) : trm_scope.
Notation "''u3'" := ("u3":var) (in custom trm at level 0) : trm_scope.
Notation "''v3'" := ("v3":var) (in custom trm at level 0) : trm_scope.
Notation "''w3'" := ("w3":var) (in custom trm at level 0) : trm_scope.
Notation "''x3'" := ("x3":var) (in custom trm at level 0) : trm_scope.
Notation "''y3'" := ("y3":var) (in custom trm at level 0) : trm_scope.
Notation "''z3'" := ("z3":var) (in custom trm at level 0) : trm_scope.

End NotationForVariables.


(* ################################################################# *)
(** * Optional Material *)

(* ================================================================= *)
(** ** Bonuse: the Tactic [var_neq] *)

(** This tactic is not used in the SLF volume. *)

(** The tactic [var_neq] helps prove calls of the form [x <> y],
    where [x] and [y] are two concrete program variables.
    This tactic is registered as hint for [auto] *)

Ltac var_neq :=
  match goal with |- ?x <> ?y :> var =>
    solve [ let E := fresh in
            destruct (String.string_dec x y) as [E|E];
              [ false | apply E ] ] end.

#[global]
Hint Extern 1 (?x <> ?y) => var_neq.

(* 2024-12-26 10:22 *)
