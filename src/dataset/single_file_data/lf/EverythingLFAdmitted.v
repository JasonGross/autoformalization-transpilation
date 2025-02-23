(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "-deprecated-native-compiler-option,-native-compiler-disabled" "-native-compiler" "ondemand" "-Q" "." "LF" "-top" "LF.Everything") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 55 lines to 59 lines, then from 73 lines to 341 lines, then from 346 lines to 101 lines, then from 114 lines to 197 lines, then from 202 lines to 131 lines, then from 144 lines to 571 lines, then from 576 lines to 305 lines, then from 318 lines to 699 lines, then from 704 lines to 356 lines, then from 369 lines to 442 lines, then from 447 lines to 386 lines, then from 399 lines to 921 lines, then from 926 lines to 396 lines, then from 409 lines to 482 lines, then from 487 lines to 426 lines, then from 439 lines to 528 lines, then from 533 lines to 436 lines, then from 449 lines to 960 lines, then from 965 lines to 495 lines, then from 508 lines to 616 lines, then from 621 lines to 527 lines, then from 540 lines to 971 lines, then from 976 lines to 579 lines, then from 592 lines to 1120 lines, then from 1125 lines to 638 lines, then from 651 lines to 920 lines, then from 925 lines to 682 lines, then from 695 lines to 1221 lines, then from 1226 lines to 743 lines, then from 756 lines to 886 lines, then from 891 lines to 776 lines, then from 789 lines to 1771 lines, then from 1774 lines to 1020 lines, then from 1033 lines to 1994 lines, then from 1999 lines to 1349 lines, then from 1362 lines to 1725 lines, then from 1730 lines to 1397 lines, then from 1410 lines to 1493 lines, then from 1498 lines to 1427 lines, then from 1440 lines to 1551 lines, then from 1556 lines to 1458 lines, then from 1471 lines to 1560 lines, then from 1565 lines to 1488 lines, then from 1501 lines to 1648 lines, then from 1653 lines to 1530 lines, then from 1543 lines to 2023 lines, then from 2028 lines to 1936 lines, then from 1949 lines to 2359 lines, then from 2364 lines to 2114 lines, then from 2127 lines to 2200 lines, then from 2205 lines to 2144 lines, then from 2157 lines to 2196 lines, then from 2201 lines to 2154 lines, then from 2167 lines to 2696 lines, then from 2701 lines to 2216 lines, then from 2229 lines to 2311 lines, then from 2316 lines to 2246 lines, then from 2259 lines to 3017 lines, then from 3019 lines to 2525 lines, then from 2538 lines to 4641 lines, then from 4646 lines to 3284 lines, then from 3297 lines to 3687 lines, then from 3692 lines to 3447 lines, then from 3460 lines to 3739 lines, then from 3744 lines to 3489 lines, then from 3502 lines to 5354 lines, then from 5359 lines to 4024 lines, then from 4037 lines to 6786 lines, then from 6789 lines to 4883 lines, then from 4896 lines to 6705 lines, then from 6709 lines to 5428 lines, then from 5441 lines to 6695 lines, then from 6700 lines to 5754 lines, then from 5767 lines to 7002 lines, then from 7007 lines to 6301 lines, then from 6314 lines to 7530 lines, then from 7535 lines to 6781 lines, then from 6794 lines to 7601 lines, then from 7606 lines to 6976 lines, then from 6989 lines to 9031 lines, then from 9036 lines to 7632 lines, then from 7637 lines to 7634 lines *)
(* coqc version 9.1+alpha compiled with OCaml 4.14.2
   coqtop version 9.1+alpha
   Expected coqc runtime on this file: 2.148 sec *)

Require Corelib.Init.Ltac.
Require Stdlib.Arith.Arith.
Require Stdlib.Lists.List.
Require Corelib.Init.Nat.
Require Stdlib.Strings.String.
Require Corelib.Setoids.Setoid.
Require Stdlib.Strings.Ascii.
Require Stdlib.micromega.Lia.
Require Stdlib.setoid_ring.Ring.
Require Stdlib.Bool.Bool.
Require Stdlib.Logic.FunctionalExtensionality.
Require Stdlib.Arith.EqNat.
Require Stdlib.extraction.Extraction.
Require Stdlib.Arith.PeanoNat.
Require Corelib.extraction.ExtrOcamlBasic.
Require Stdlib.extraction.ExtrOcamlString.

Module Export LF_DOT_Basics.
Module Export LF.
Module Basics.

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_working_day (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

Compute (next_working_day friday).

Compute (next_working_day (next_working_day saturday)).

Example test_next_working_day:
  (next_working_day (next_working_day saturday)) = tuesday.
Admitted.

Export Stdlib.Strings.String.

Inductive bool : Type :=
  | true
  | false.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1:  (orb true  false) = true.
Admitted.
Example test_orb2:  (orb false false) = false.
Admitted.
Example test_orb3:  (orb false true)  = true.
Admitted.
Example test_orb4:  (orb true  true)  = true.
Admitted.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5:  false || false || true = true.
Admitted.

Definition negb' (b:bool) : bool :=
  if b then false
  else true.

Definition andb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.

Definition orb' (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.

Inductive bw : Type :=
  | bw_black
  | bw_white.

Definition invert (x: bw) : bw :=
  if x then bw_white
  else bw_black.

Compute (invert bw_black).

Compute (invert bw_white).

Definition nandb (b1:bool) (b2:bool) : bool
  .
Admitted.

Example test_nandb1:               (nandb true false) = true.
 Admitted.
Example test_nandb2:               (nandb false false) = true.
 Admitted.
Example test_nandb3:               (nandb false true) = true.
 Admitted.
Example test_nandb4:               (nandb true true) = false.
 Admitted.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool
  .
Admitted.

Example test_andb31:                 (andb3 true true true) = true.
 Admitted.
Example test_andb32:                 (andb3 false true true) = false.
 Admitted.
Example test_andb33:                 (andb3 true false true) = false.
 Admitted.
Example test_andb34:                 (andb3 true true false) = false.
 Admitted.

Check true.

Check true
  : bool.
Check (negb true)
  : bool.

Check negb
  : bool -> bool.

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

Module Export Playground.
  Definition foo : rgb := blue.
End Playground.

Definition foo : bool := true.

Check Playground.foo : rgb.
Check foo : bool.

Module Export TuplePlayground.

Inductive bit : Type :=
  | B1
  | B0.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0)
  : nybble.

Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
  end.

Compute (all_zero (bits B1 B0 B1 B0)).

Compute (all_zero (bits B0 B0 B0 B0)).

End TuplePlayground.

Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n : nat).

Inductive otherNat : Type :=
  | stop
  | tick (foo : otherNat).

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End NatPlayground.

Check (S (S (S (S O)))).

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute (minustwo 4).

Check S        : nat -> nat.
Check pred     : nat -> nat.
Check minustwo : nat -> nat.

Fixpoint even (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => even n'
  end.

Definition odd (n:nat) : bool :=
  negb (even n).

Example test_odd1:    odd 1 = true.
Admitted.
Example test_odd2:    odd 4 = false.
Admitted.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Compute (plus 3 2).

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Admitted.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O   , _    => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

Fixpoint factorial (n:nat) : nat
  .
Admitted.

Example test_factorial1:          (factorial 3) = 6.
 Admitted.
Example test_factorial2:          (factorial 5) = (mult 10 12).
 Admitted.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Check ((0 + 1) + 1) : nat.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Example test_leb1:                leb 2 2 = true.
Admitted.
Example test_leb2:                leb 2 4 = true.
Admitted.
Example test_leb3:                leb 4 2 = false.
Admitted.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3': (4 <=? 2) = false.
Admitted.

Definition ltb (n m : nat) : bool
  .
Admitted.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1:             (ltb 2 2) = false.
 Admitted.
Example test_ltb2:             (ltb 2 4) = true.
 Admitted.
Example test_ltb3:             (ltb 4 2) = false.
 Admitted.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Admitted.

Theorem plus_O_n' : forall n : nat, 0 + n = n.
Admitted.

Theorem plus_O_n'' : forall n : nat, 0 + n = n.
Admitted.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Admitted.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Admitted.

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Admitted.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
   Admitted.

Check mult_n_O.

Check mult_n_Sm.

Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Admitted.

Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
   Admitted.

Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Admitted.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Admitted.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Admitted.

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Admitted.

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Admitted.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
   Admitted.

Theorem plus_1_neq_0' : forall n : nat,
  (n + 1) =? 0 = false.
Admitted.

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Admitted.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
   Admitted.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Fixpoint plus' (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus' n' m)
  end.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
   Admitted.

Definition manual_grade_for_negation_fn_applied_twice : option (nat*string) := None.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
   Admitted.

Module Export LateDays.

Inductive letter : Type :=
  | A | B | C | D | F.

Inductive modifier : Type :=
  | Plus | Natural | Minus.

Inductive grade : Type :=
  Grade (l:letter) (m:modifier).

Inductive comparison : Type :=
  | Eq
  | Lt
  | Gt.

Definition letter_comparison (l1 l2 : letter) : comparison :=
  match l1, l2 with
  | A, A => Eq
  | A, _ => Gt
  | B, A => Lt
  | B, B => Eq
  | B, _ => Gt
  | C, (A | B) => Lt
  | C, C => Eq
  | C, _ => Gt
  | D, (A | B | C) => Lt
  | D, D => Eq
  | D, _ => Gt
  | F, (A | B | C | D) => Lt
  | F, F => Eq
  end.

Compute letter_comparison B A.

Compute letter_comparison D D.

Compute letter_comparison B F.

Theorem letter_comparison_Eq :
  forall l, letter_comparison l l = Eq.
Proof.
   Admitted.

Definition modifier_comparison (m1 m2 : modifier) : comparison :=
  match m1, m2 with
  | Plus, Plus => Eq
  | Plus, _ => Gt
  | Natural, Plus => Lt
  | Natural, Natural => Eq
  | Natural, _ => Gt
  | Minus, (Plus | Natural) => Lt
  | Minus, Minus => Eq
  end.

Definition grade_comparison (g1 g2 : grade) : comparison
  .
Admitted.

Example test_grade_comparison1 :
  (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
 Admitted.

Example test_grade_comparison2 :
  (grade_comparison (Grade A Minus) (Grade A Plus)) = Lt.
 Admitted.

Example test_grade_comparison3 :
  (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
 Admitted.

Example test_grade_comparison4 :
  (grade_comparison (Grade B Minus) (Grade C Plus)) = Gt.
 Admitted.

Definition lower_letter (l : letter) : letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F
  end.

Theorem lower_letter_F_is_F:
  lower_letter F = F.
Admitted.

Theorem lower_letter_lowers:
  forall (l : letter),
    letter_comparison F l = Lt ->
    letter_comparison (lower_letter l) l = Lt.
Proof.
 Admitted.

Definition lower_grade (g : grade) : grade
  .
Admitted.

Example lower_grade_A_Plus :
  lower_grade (Grade A Plus) = (Grade A Natural).
Proof.
 Admitted.

Example lower_grade_A_Natural :
  lower_grade (Grade A Natural) = (Grade A Minus).
Proof.
 Admitted.

Example lower_grade_A_Minus :
  lower_grade (Grade A Minus) = (Grade B Plus).
Proof.
 Admitted.

Example lower_grade_B_Plus :
  lower_grade (Grade B Plus) = (Grade B Natural).
Proof.
 Admitted.

Example lower_grade_F_Natural :
  lower_grade (Grade F Natural) = (Grade F Minus).
Proof.
 Admitted.

Example lower_grade_twice :
  lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
Proof.
 Admitted.

Example lower_grade_thrice :
  lower_grade (lower_grade (lower_grade (Grade B Minus))) = (Grade C Minus).
Proof.
 Admitted.

Theorem lower_grade_F_Minus : lower_grade (Grade F Minus) = (Grade F Minus).
Proof.
 Admitted.

Theorem lower_grade_lowers :
  forall (g : grade),
    grade_comparison (Grade F Minus) g = Lt ->
    grade_comparison (lower_grade g) g = Lt.
Proof.
   Admitted.

Definition apply_late_policy (late_days : nat) (g : grade) : grade :=
  if late_days <? 9 then g
  else if late_days <? 17 then lower_grade g
  else if late_days <? 21 then lower_grade (lower_grade g)
  else lower_grade (lower_grade (lower_grade g)).

Theorem apply_late_policy_unfold :
  forall (late_days : nat) (g : grade),
    (apply_late_policy late_days g)
    =
    (if late_days <? 9 then g  else
       if late_days <? 17 then lower_grade g
       else if late_days <? 21 then lower_grade (lower_grade g)
            else lower_grade (lower_grade (lower_grade g))).
Admitted.

Theorem no_penalty_for_mostly_on_time :
  forall (late_days : nat) (g : grade),
    (late_days <? 9 = true) ->
    apply_late_policy late_days g = g.
Proof.
   Admitted.

Theorem grade_lowered_once :
  forall (late_days : nat) (g : grade),
    (late_days <? 9 = false) ->
    (late_days <? 17 = true) ->
    (apply_late_policy late_days g) = (lower_grade g).
Proof.
   Admitted.

End LateDays.

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m:bin) : bin
  .
Admitted.

Fixpoint bin_to_nat (m:bin) : nat
  .
Admitted.

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
 Admitted.

Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
 Admitted.

Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
 Admitted.

Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
 Admitted.

Example test_bin_incr5 :
        bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
 Admitted.

Example test_bin_incr6 :
        bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
 Admitted.

End Basics.

End LF.

End LF_DOT_Basics.

Module Export LF_DOT_Induction.
Module Export LF.
Module Induction.

Export LF.Basics.

Theorem add_0_r : forall n:nat, n + 0 = n.
Admitted.

Theorem minus_n_n : forall n,
  minus n n = 0.
Admitted.

Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
   Admitted.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
   Admitted.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
   Admitted.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
   Admitted.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
   Admitted.

Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
   Admitted.

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
   Admitted.

Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Admitted.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Admitted.

Theorem add_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Admitted.

Theorem add_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Admitted.

Definition manual_grade_for_add_comm_informal : option (nat*string) := None.

Definition manual_grade_for_eqb_refl_informal : option (nat*string) := None.

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
   Admitted.

Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
   Admitted.

Check leb.

Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
   Admitted.

Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof.
   Admitted.

Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
Proof.
   Admitted.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
   Admitted.

Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
   Admitted.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
   Admitted.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
   Admitted.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
   Admitted.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
   Admitted.

Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
   Admitted.

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin)
.

Fixpoint incr (m:bin) : bin
  .
Admitted.

Fixpoint bin_to_nat (m:bin) : nat
  .
Admitted.

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
   Admitted.

Fixpoint nat_to_bin (n:nat) : bin
  .
Admitted.

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
   Admitted.

Lemma double_incr : forall n : nat, double (S n) = S (S (double n)).
Proof.
   Admitted.

Definition double_bin (b:bin) : bin
  .
Admitted.

Example double_bin_zero : double_bin Z = Z.
 Admitted.

Lemma double_incr_bin : forall b,
    double_bin (incr b) = incr (incr (double_bin b)).
Proof.
   Admitted.

Fixpoint normalize (b:bin) : bin
  .
Admitted.

Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
   Admitted.

End Induction.

End LF.

End LF_DOT_Induction.

Module Export LF_DOT_Lists.
Module Export LF.
Module Lists.

Export LF.Induction.
Module Export NatList.

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

Check (pair 3 5) : natprod.

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Admitted.

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Admitted.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
   Admitted.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
   Admitted.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].
Admitted.
Example test_app2:             nil ++ [4;5] = [4;5].
Admitted.
Example test_app3:             [1;2;3] ++ nil = [1;2;3].
Admitted.

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1:             hd 0 [1;2;3] = 1.
Admitted.
Example test_hd2:             hd 0 [] = 0.
Admitted.
Example test_tl:              tl [1;2;3] = [2;3].
Admitted.

Fixpoint nonzeros (l:natlist) : natlist
  .
Admitted.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
   Admitted.

Fixpoint oddmembers (l:natlist) : natlist
  .
Admitted.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
   Admitted.

Definition countoddmembers (l:natlist) : nat
  .
Admitted.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
   Admitted.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
   Admitted.

Example test_countoddmembers3:
  countoddmembers nil = 0.
   Admitted.

Fixpoint alternate (l1 l2 : natlist) : natlist
  .
Admitted.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
   Admitted.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
   Admitted.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
   Admitted.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
   Admitted.

Definition bag := natlist.

Fixpoint count (v : nat) (s : bag) : nat
  .
Admitted.

Example test_count1:              count 1 [1;2;3;1;4;1] = 3.
  Admitted.
Example test_count2:              count 6 [1;2;3;1;4;1] = 0.
  Admitted.

Definition sum : bag -> bag -> bag
  .
Admitted.

Example test_sum1:              count 1 (sum [1;2;3] [1;4;1]) = 3.
  Admitted.

Definition add (v : nat) (s : bag) : bag
  .
Admitted.

Example test_add1:                count 1 (add 1 [1;4;1]) = 3.
  Admitted.
Example test_add2:                count 5 (add 1 [1;4;1]) = 0.
  Admitted.

Fixpoint member (v : nat) (s : bag) : bool
  .
Admitted.

Example test_member1:             member 1 [1;4;1] = true.
  Admitted.

Example test_member2:             member 2 [1;4;1] = false.
 Admitted.

Fixpoint remove_one (v : nat) (s : bag) : bag
  .
Admitted.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
   Admitted.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
   Admitted.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
   Admitted.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
   Admitted.

Fixpoint remove_all (v:nat) (s:bag) : bag
  .
Admitted.

Example test_remove_all1:  count 5 (remove_all 5 [2;1;5;4;1]) = 0.
  Admitted.
Example test_remove_all2:  count 5 (remove_all 5 [2;1;4;1]) = 0.
  Admitted.
Example test_remove_all3:  count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
  Admitted.
Example test_remove_all4:  count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
  Admitted.

Fixpoint included (s1 : bag) (s2 : bag) : bool
  .
Admitted.

Example test_included1:              included [1;2] [2;1;4;1] = true.
  Admitted.
Example test_included2:              included [1;2;2] [2;1;4;1] = false.
  Admitted.

Definition manual_grade_for_add_inc_count : option (nat*string) := None.

Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Admitted.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Admitted.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Admitted.

Theorem repeat_plus: forall c1 c2 n: nat,
    repeat n c1 ++ repeat n c2 = repeat n (c1 + c2).
Admitted.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

Example test_rev1:            rev [1;2;3] = [3;2;1].
Admitted.
Example test_rev2:            rev nil = nil.
Admitted.

Theorem app_length_S: forall l n,
  length (l ++ [n]) = S (length l).
Admitted.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Admitted.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Admitted.

Search rev.

Search (_ + _ = _ + _).

Search (_ + _ = _ + _) inside Induction.

Search (?x + ?y = ?y + ?x).

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
   Admitted.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
   Admitted.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
   Admitted.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
   Admitted.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
   Admitted.

Fixpoint eqblist (l1 l2 : natlist) : bool
  .
Admitted.

Example test_eqblist1 :
  (eqblist nil nil = true).
  Admitted.

Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
 Admitted.

Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
  Admitted.

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
   Admitted.

Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
   Admitted.

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Admitted.

Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
   Admitted.

Theorem involution_injective : forall (f : nat -> nat),
    (forall n : nat, n = f (f n)) -> (forall n1 n2 : nat, f n1 = f n2 -> n1 = n2).
Proof.
   Admitted.

Theorem rev_injective : forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
   Admitted.

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42
  | a :: l' => match n with
               | 0 => a
               | S n' => nth_bad l' n'
               end
  end.

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Admitted.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Admitted.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Admitted.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Definition hd_error (l : natlist) : natoption
  .
Admitted.

Example test_hd_error1 : hd_error [] = None.
  Admitted.

Example test_hd_error2 : hd_error [1] = Some 1.
  Admitted.

Example test_hd_error3 : hd_error [5;6] = Some 5.
  Admitted.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
   Admitted.

End NatList.

Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

Theorem eqb_id_refl : forall x, eqb_id x x = true.
Proof.
   Admitted.

Module Export PartialMap.
Export NatList.

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.

Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  Admitted.

Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
  Admitted.

End PartialMap.

End Lists.

End LF.

End LF_DOT_Lists.

Module Export LF_DOT_Poly.
Module Export LF.
Module Poly.

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Export LF.Lists.

Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Check list : Type -> Type.

Check (nil nat) : list nat.

Check (cons nat 3 (nil nat)) : list nat.

Check nil : forall X : Type, list X.

Check cons : forall X : Type, X -> list X -> list X.

Check (cons nat 2 (cons nat 1 (nil nat)))
      : list nat.

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Admitted.

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Admitted.

Module MumbleGrumble.

Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.

Inductive grumble (X:Type) : Type :=
  | d (m : mumble)
  | e (x : X).

End MumbleGrumble.

Fixpoint repeat' X x count : list X :=
  match count with
  | 0        => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Check repeat'
  : forall X : Type, X -> nat -> list X.
Check repeat
  : forall X : Type, X -> nat -> list X.

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0        => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat''' x count')
  end.

Inductive list' {X:Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Admitted.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Admitted.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Admitted.

Fail Definition mynil := nil.

Definition mynil : list nat := nil.

Check @nil : forall X : Type, list X.

Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Definition list123''' := [1; 2; 3].

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
   Admitted.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
   Admitted.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
   Admitted.

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
   Admitted.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
   Admitted.

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y)
  .
Admitted.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
 Admitted.

Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X}.
Arguments None {X}.

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Admitted.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Admitted.
Example test_nth_error3 : nth_error [true] 2 = None.
Admitted.

Definition hd_error {X : Type} (l : list X) : option X
  .
Admitted.

Check @hd_error : forall X : Type, list X -> option X.

Example test_hd_error1 : hd_error [1;2] = Some 1.
  Admitted.
Example test_hd_error2 : hd_error  [[1];[2]]  = Some [1].
  Admitted.

Definition doit3times {X : Type} (f : X->X) (n : X) : X :=
  f (f (f n)).

Check @doit3times : forall X : Type, (X -> X) -> X -> X.

Example test_doit3times: doit3times minustwo 9 = 3.
Admitted.

Example test_doit3times': doit3times negb true = false.
Admitted.

Fixpoint filter {X:Type} (test: X->bool) (l:list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.

Example test_filter1: filter even [1;2;3;4] = [2;4].
Admitted.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Admitted.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter odd l).

Example test_countoddmembers'1:   countoddmembers' [1;0;3;1;4;5] = 4.
Admitted.
Example test_countoddmembers'2:   countoddmembers' [0;2;4] = 0.
Admitted.
Example test_countoddmembers'3:   countoddmembers' nil = 0.
Admitted.

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Admitted.

Example test_filter2':
    filter (fun l => (length l) =? 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Admitted.

Definition filter_even_gt7 (l : list nat) : list nat
  .
Admitted.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
  Admitted.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
  Admitted.

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X
  .
Admitted.

Example test_partition1: partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
 Admitted.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
 Admitted.

Fixpoint map {X Y : Type} (f : X->Y) (l : list X) : list Y :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Admitted.

Example test_map2:
  map odd [2;1;2;5] = [false;true;false;true].
Admitted.

Example test_map3:
    map (fun n => [even n;odd n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Admitted.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
   Admitted.

Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X)
                   : list Y
  .
Admitted.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
  Admitted.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.

Fixpoint fold {X Y: Type} (f : X->Y->Y) (l : list X) (b : Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Check (fold andb) : list bool -> bool -> bool.

Example fold_example1 :
  fold andb [true;true;false;true] true = false.
Admitted.

Example fold_example2 :
  fold mult [1;2;3;4] 1 = 24.
Admitted.

Example fold_example3 :
  fold app  [[1];[];[2;3];[4]] [] = [1;2;3;4].
Admitted.

Definition constfun {X: Type} (x: X) : nat -> X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Admitted.

Example constfun_example2 : (constfun 5) 99 = 5.
Admitted.

Check plus : nat -> nat -> nat.

Definition plus3 := plus 3.
Check plus3 : nat -> nat.

Example test_plus3 :    plus3 4 = 7.
Admitted.
Example test_plus3' :   doit3times plus3 0 = 9.
Admitted.
Example test_plus3'' :  doit3times (plus 3) 0 = 9.
Admitted.

Module Exercises.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Admitted.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
 Admitted.

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y
  .
Admitted.

Definition manual_grade_for_fold_map : option (nat*string) := None.

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z
  .
Admitted.

Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Admitted.

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
   Admitted.

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
   Admitted.

Definition manual_grade_for_informal_proof : option (nat*string) := None.

Module Export Church.
Definition cnat := forall X : Type, (X -> X) -> X -> X.

Definition one : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

Definition two : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

Definition three : cnat := @doit3times.

Definition zero' : cnat :=
  fun (X : Type) (succ : X -> X) (zero : X) => zero.
Definition one' : cnat :=
  fun (X : Type) (succ : X -> X) (zero : X) => succ zero.
Definition two' : cnat :=
  fun (X : Type) (succ : X -> X) (zero : X) => succ (succ zero).

Example zero_church_peano : zero nat S O = 0.
Admitted.

Example one_church_peano : one nat S O = 1.
Admitted.

Example two_church_peano : two nat S O = 2.
Admitted.

Definition scc (n : cnat) : cnat
  .
Admitted.

Example scc_1 : scc zero = one.
Proof.
 Admitted.

Example scc_2 : scc one = two.
Proof.
 Admitted.

Example scc_3 : scc two = three.
Proof.
 Admitted.

Definition plus (n m : cnat) : cnat
  .
Admitted.

Example plus_1 : plus zero one = one.
Proof.
 Admitted.

Example plus_2 : plus two three = plus three two.
Proof.
 Admitted.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof.
 Admitted.

Definition mult (n m : cnat) : cnat
  .
Admitted.

Example mult_1 : mult one one = one.
Proof.
 Admitted.

Example mult_2 : mult zero (plus three three) = zero.
Proof.
 Admitted.

Example mult_3 : mult two three = plus three three.
Proof.
 Admitted.

Definition exp (n m : cnat) : cnat
  .
Admitted.

Example exp_1 : exp two two = plus two two.
Proof.
 Admitted.

Example exp_2 : exp three zero = one.
Proof.
 Admitted.

Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof.
 Admitted.

End Church.
End Exercises.

End Poly.

End LF.

End LF_DOT_Poly.

Module Export LF_DOT_Tactics.
Module Export LF.
Module Tactics.

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Export LF.Poly.

Theorem silly1 : forall (n m : nat),
  n = m ->
  n = m.
Admitted.

Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Admitted.

Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m)  ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Admitted.

Theorem silly_ex : forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (S p) = true.
Proof.
   Admitted.

Theorem silly3 : forall (n m : nat),
  n = m ->
  m = n.
Admitted.

Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' ->
  l' = rev l.
Proof.
   Admitted.

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Admitted.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Admitted.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Admitted.

Example trans_eq_example'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Admitted.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
   Admitted.

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Admitted.

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Admitted.

Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] ->
  n = m.
Admitted.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
   Admitted.

Theorem discriminate_ex1 : forall (n m : nat),
  false = true ->
  n = m.
Admitted.

Theorem discriminate_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Admitted.

Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
   Admitted.

Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Admitted.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Admitted.

Theorem eq_implies_succ_equal : forall (n m : nat),
  n = m -> S n = S m.
Admitted.

Theorem eq_implies_succ_equal' : forall (n m : nat),
  n = m -> S n = S m.
Admitted.

Theorem S_inj : forall (n m : nat) (b : bool),
  ((S n) =? (S m)) = b  ->
  (n =? m) = b.
Admitted.

Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.
Admitted.

Theorem specialize_example: forall n,
     (forall m, m*n = 0)
  -> n = 0.
Admitted.

Example trans_eq_example''' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Admitted.

Theorem double_injective : forall n m,
  double n = double m ->
  n = m.
Admitted.

Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
   Admitted.

Definition manual_grade_for_informal_proof : option (nat*string) := None.

Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
   Admitted.

Theorem double_injective_take2 : forall n m,
  double n = double m ->
  n = m.
Admitted.

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
   Admitted.

Definition square n := n * n.

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Admitted.

Definition foo (x: nat) := 5.

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Admitted.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Admitted.

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Admitted.

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Admitted.

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
   Admitted.

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

Theorem sillyfun1_odd : forall (n : nat),
  sillyfun1 n = true ->
  odd n = true.
Admitted.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
   Admitted.

Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
   Admitted.

Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
   Admitted.

Definition split_combine_statement : Prop

  .
Admitted.

Theorem split_combine : split_combine_statement.
Proof.
 Admitted.

Definition manual_grade_for_split_combine : option (nat*string) := None.

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                                 (x : X) (l lf : list X),
  filter test l = x :: lf ->
  test x = true.
Proof.
   Admitted.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool
  .
Admitted.

Example test_forallb_1 : forallb odd [1;3;5;7;9] = true.
Proof.
 Admitted.

Example test_forallb_2 : forallb negb [false;false] = true.
Proof.
 Admitted.

Example test_forallb_3 : forallb even [0;2;4;5] = false.
Proof.
 Admitted.

Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof.
 Admitted.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool
  .
Admitted.

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof.
 Admitted.

Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof.
 Admitted.

Example test_existsb_3 : existsb odd [1;0;0;0;0;3] = true.
Proof.
 Admitted.

Example test_existsb_4 : existsb even [] = false.
Proof.
 Admitted.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool
  .
Admitted.

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof.
 Admitted.

End Tactics.

End LF.

End LF_DOT_Tactics.

Module Export LF_DOT_Logic.
Module Export LF.
Module Logic.

Set Warnings "-notation-overridden,-parsing".
Set Warnings "-deprecated-hint-without-locality".
Export LF.Tactics.

Check (forall n m : nat, n + m = m + n) : Prop.

Check 2 = 2 : Prop.

Check 3 = 2 : Prop.

Check forall n : nat, n = 2 : Prop.

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Admitted.

Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim : Prop.

Theorem plus_claim_is_true :
  plus_claim.
Admitted.

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three : nat -> Prop.

Definition injective {A B} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Admitted.

Check @eq : forall A : Type, A -> A -> Prop.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Admitted.

Check @conj : forall A B : Prop, A -> B -> A /\ B.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Admitted.

Example plus_is_O :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
   Admitted.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Admitted.

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Admitted.

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Admitted.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Admitted.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Admitted.

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
   Admitted.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Admitted.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
   Admitted.

Check and : Prop -> Prop -> Prop.

Lemma factor_is_O:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Admitted.

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Admitted.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Admitted.

Lemma mult_is_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
   Admitted.

Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
   Admitted.

Definition not (P:Prop) := P -> False.

Check not : Prop -> Prop.

Notation "~ x" := (not x) : type_scope.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Admitted.

Theorem not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
   Admitted.

Notation "x <> y" := (~(x = y)) : type_scope.

Theorem zero_not_one : 0 <> 1.
Admitted.

Theorem not_False :
  ~ False.
Admitted.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Admitted.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Admitted.

Definition manual_grade_for_double_neg_informal : option (nat*string) := None.

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
   Admitted.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
   Admitted.

Definition manual_grade_for_not_PNP_informal : option (nat*string) := None.

Theorem de_morgan_not_or : forall (P Q : Prop),
    ~ (P \/ Q) -> ~P /\ ~Q.
Proof.
   Admitted.

Lemma not_S_pred_n : ~(forall n : nat, S (pred n) = n).
Proof.
   Admitted.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Admitted.

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Admitted.

Lemma True_is_true : True.
Admitted.

Definition disc_fn (n: nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.

Theorem disc_example : forall n, ~ (O = S n).
Admitted.

Theorem nil_is_not_cons : forall X (x : X) (xs : list X), ~ (nil = x :: xs).
Proof.
   Admitted.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Admitted.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Admitted.

Lemma apply_iff_example1:
  forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
Admitted.

Lemma apply_iff_example2:
  forall P Q R : Prop, (P <-> Q) -> (P -> R) -> (Q -> R).
Admitted.

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
   Admitted.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
   Admitted.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
   Admitted.

Import Corelib.Setoids.Setoid.

Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Admitted.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Admitted.

Lemma mul_eq_0_ternary :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Admitted.

Definition Even x := exists n : nat, x = double n.
Check Even : nat -> Prop.

Lemma four_is_Even : Even 4.
Admitted.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Admitted.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
   Admitted.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
    Admitted.

Theorem leb_plus_exists : forall n m, n <=? m = true -> exists x, m = n+x.
Proof.
 Admitted.

Theorem plus_exists_leb : forall n m, (exists x, m = n+x) -> n <=? m = true.
Proof.
   Admitted.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Admitted.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Admitted.

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
         In x l ->
         In (f x) (map f l).
Admitted.

Theorem In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
         In y (map f l) <->
         exists x, f x = y /\ In x l.
Proof.
  intros A B f l y.
split.
  -
 induction l as [|x l' IHl'].
     Admitted.

Theorem In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l.
induction l as [|a' l' IH].
   Admitted.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop
  .
Admitted.

Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
   Admitted.

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop
  .
Admitted.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (odd n = true -> Podd n) ->
    (odd n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
   Admitted.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = true ->
    Podd n.
Proof.
   Admitted.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = false ->
    Peven n.
Proof.
   Admitted.

Check plus : nat -> nat -> nat.
Check @rev : forall X, list X -> list X.

Check add_comm        : forall n m : nat, n + m = m + n.
Check plus_id_example : forall n m : nat, n = m -> n + n = m + m.

Lemma add_comm3_take2 :
  forall x y z, x + (y + z) = (z + y) + x.
Admitted.

Lemma add_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Admitted.

Lemma add_comm3_take4 :
  forall x y z, x + (y + z) = (z + y) + x.
Admitted.

Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Admitted.

Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> l <> [].
Admitted.

Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Admitted.

Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Admitted.

Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Admitted.

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Admitted.

Example even_42_bool : even 42 = true.
Admitted.

Example even_42_prop : Even 42.
Admitted.

Lemma even_double : forall k, even (double k) = true.
Admitted.

Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.

   Admitted.

Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
Admitted.

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Admitted.

Fail
Definition is_even_prime n :=
  if n = 2 then true
  else false.

Definition is_even_prime n :=
  if n =? 2 then true
  else false.

Example even_1000 : Even 1000.
Admitted.

Example even_1000' : even 1000 = true.
Admitted.

Example even_1000'' : Even 1000.
Admitted.

Example not_even_1001 : even 1001 = false.
Admitted.

Example not_even_1001' : ~(Even 1001).
Admitted.

Lemma plus_eqb_example : forall n m p : nat,
  n =? m = true -> n + p =? m + p = true.
Admitted.

Theorem andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
   Admitted.

Theorem orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
   Admitted.

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
   Admitted.

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
                  (l1 l2 : list A) : bool
  .
Admitted.

Theorem eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
 Admitted.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool
  .
Admitted.

Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
   Admitted.

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Admitted.

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Admitted.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
 Admitted.

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Admitted.

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Admitted.

Theorem excluded_middle_irrefutable: forall (P : Prop),
  ~ ~ (P \/ ~ P).
Proof.
   Admitted.

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
   Admitted.

Definition peirce := forall P Q: Prop,
  ((P -> Q) -> P) -> P.

Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P \/ Q.

Definition implies_to_or := forall P Q:Prop,
  (P -> Q) -> (~P \/ Q).

Definition consequentia_mirabilis := forall P:Prop,
  (~P -> P) -> P.

End Logic.

End LF.

End LF_DOT_Logic.

Module Export LF_DOT_IndProp.
Module Export LF.
Module IndProp.

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Export LF.Logic.

Fixpoint div2 (n : nat) : nat :=
  match n with
    0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.

Definition csf (n : nat) : nat :=
  if even n then div2 n
  else (3 * n) + 1.

Fail Fixpoint reaches1_in (n : nat) : nat :=
  if n =? 1 then 0
  else 1 + reaches1_in (csf n).

Fail Fixpoint Collatz_holds_for (n : nat) : Prop :=
  match n with
  | 0 => False
  | 1 => True
  | _ => if even n then Collatz_holds_for (div2 n)
                   else Collatz_holds_for ((3 * n) + 1)
  end.

Inductive Collatz_holds_for : nat -> Prop :=
  | Chf_one : Collatz_holds_for 1
  | Chf_even (n : nat) : even n = true ->
                         Collatz_holds_for (div2 n) ->
                         Collatz_holds_for n
  | Chf_odd (n : nat) :  even n = false ->
                         Collatz_holds_for ((3 * n) + 1) ->
                         Collatz_holds_for n.

Example Collatz_holds_for_12 : Collatz_holds_for 12.
Admitted.

Conjecture collatz : forall n, n <> 0 -> Collatz_holds_for n.

Module Export LePlayground.

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)   : le n n
  | le_S (n m : nat) : le n m -> le n (S m).

Notation "n <= m" := (le n m) (at level 70).

Example le_3_5 : 3 <= 5.
Admitted.

End LePlayground.

Inductive clos_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | t_step (x y : X) :
      R x y ->
      clos_trans R x y
  | t_trans (x y z : X) :
      clos_trans R x y ->
      clos_trans R y z ->
      clos_trans R x z.

Inductive Person : Type := Sage | Cleo | Ridley | Moss.

Inductive parent_of : Person -> Person -> Prop :=
  po_SC : parent_of Sage Cleo
| po_SR : parent_of Sage Ridley
| po_CM : parent_of Cleo Moss.

Definition ancestor_of : Person -> Person -> Prop :=
  clos_trans parent_of.

Example ancestor_of_ex : ancestor_of Sage Moss.
Admitted.

Inductive clos_refl_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | rt_step (x y : X) :
      R x y ->
      clos_refl_trans R x y
  | rt_refl (x : X) :
      clos_refl_trans R x x
  | rt_trans (x y z : X) :
      clos_refl_trans R x y ->
      clos_refl_trans R y z ->
      clos_refl_trans R x z.

Definition cs (n m : nat) : Prop := csf n = m.

Definition cms n m := clos_refl_trans cs n m.
Conjecture collatz' : forall n, n <> 0 -> cms n 1.

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

Inductive ev : nat -> Prop :=
  | ev_0                       : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

Fail Inductive wrong_ev (n : nat) : Prop :=
  | wrong_ev_0 : wrong_ev 0
  | wrong_ev_SS (H: wrong_ev n) : wrong_ev (S (S n)).

Check ev_0 : ev 0.
Check ev_SS : forall (n : nat), ev n -> ev (S (S n)).

Module Export EvPlayground.

Inductive ev : nat -> Prop :=
  | ev_0  : ev 0
  | ev_SS : forall (n : nat), ev n -> ev (S (S n)).

End EvPlayground.

Theorem ev_4 : ev 4.
Admitted.

Theorem ev_4' : ev 4.
Admitted.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Admitted.

Theorem ev_double : forall n,
  ev (double n).
Proof.
   Admitted.

Lemma Perm3_rev : Perm3 [1;2;3] [3;2;1].
Admitted.

Lemma Perm3_rev' : Perm3 [1;2;3] [3;2;1].
Admitted.

Lemma Perm3_ex1 : Perm3 [1;2;3] [2;3;1].
Proof.
   Admitted.

Lemma Perm3_refl : forall (X : Type) (a b c : X),
  Perm3 [a;b;c] [a;b;c].
Proof.
   Admitted.

Theorem ev_inversion : forall (n : nat),
    ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Admitted.

Theorem le_inversion : forall (n m : nat),
  le n m ->
  (n = m) \/ (exists m', m = S m' /\ le n m').
Proof.
   Admitted.

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Admitted.

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Admitted.

Theorem one_not_even : ~ ev 1.
Admitted.

Theorem one_not_even' : ~ ev 1.
Admitted.

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
   Admitted.

Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
   Admitted.

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Admitted.

Theorem inversion_ex2 : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Admitted.

Lemma ev_Even : forall n,
  ev n -> Even n.
Admitted.

Theorem ev_Even_iff : forall n,
  ev n <-> Even n.
Admitted.

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
   Admitted.

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.

Proof.
   Admitted.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
   Admitted.

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  Admitted.

Module Export Perm3Reminder.

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

End Perm3Reminder.

Lemma Perm3_symm : forall (X : Type) (l1 l2 : list X),
  Perm3 l1 l2 -> Perm3 l2 l1.
Admitted.

Lemma Perm3_In : forall (X : Type) (x : X) (l1 l2 : list X),
    Perm3 l1 l2 -> In x l1 -> In x l2.
Proof.
   Admitted.

Lemma Perm3_NotIn : forall (X : Type) (x : X) (l1 l2 : list X),
    Perm3 l1 l2 -> ~In x l1 -> ~In x l2.
Proof.
   Admitted.

Example Perm3_example2 : ~ Perm3 [1;2;3] [1;2;4].
Proof.
   Admitted.

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)                : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

Notation "n <= m" := (le n m).

Theorem test_le1 :
  3 <= 3.
Admitted.

Theorem test_le2 :
  3 <= 6.
Admitted.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Admitted.

Definition lt (n m : nat) := le (S n) m.

Notation "n < m" := (lt n m).

Definition ge (m n : nat) : Prop := le n m.
Notation "m >= n" := (ge m n).

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
   Admitted.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
   Admitted.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
   Admitted.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
   Admitted.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
   Admitted.

Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
  Admitted.

Theorem plus_le_cases : forall n m p q,
  n + m <= p + q -> n <= p \/ m <= q.

Proof.
 Admitted.

Theorem plus_le_compat_l : forall n m p,
  n <= m ->
  p + n <= p + m.
Proof.
   Admitted.

Theorem plus_le_compat_r : forall n m p,
  n <= m ->
  n + p <= m + p.
Proof.
   Admitted.

Theorem le_plus_trans : forall n m p,
  n <= m ->
  n <= m + p.
Proof.
   Admitted.

Theorem lt_ge_cases : forall n m,
  n < m \/ n >= m.
Proof.
   Admitted.

Theorem n_lt_m__n_le_m : forall n m,
  n < m ->
  n <= m.
Proof.
   Admitted.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
 Admitted.

Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
   Admitted.

Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
   Admitted.

Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
   Admitted.

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
   Admitted.

Inductive R : nat -> nat -> nat -> Prop :=
  | c1                                     : R 0     0     0
  | c2 m n o (H : R m     n     o        ) : R (S m) n     (S o)
  | c3 m n o (H : R m     n     o        ) : R m     (S n) (S o)
  | c4 m n o (H : R (S m) (S n) (S (S o))) : R m     n     o
  | c5 m n o (H : R m     n     o        ) : R n     m     o
.

Definition manual_grade_for_R_provability : option (nat*string) := None.

Definition fR : nat -> nat -> nat
  .
Admitted.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
 Admitted.

Inductive subseq : list nat -> list nat -> Prop :=

.

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
   Admitted.

Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
   Admitted.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.

   Admitted.

Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR s2 re1 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)

  where "s =~ re" := (exp_match s re).

Example reg_exp_ex1 : [1] =~ Char 1.
Admitted.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Admitted.

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Admitted.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Admitted.

Lemma MStar1 :
  forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Admitted.

Lemma EmptySet_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
   Admitted.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
   Admitted.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
   Admitted.

Definition EmptyStr' {T:Type} := @Star T (EmptySet).

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Admitted.

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool
  .
Admitted.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
   Admitted.

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Admitted.

Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
   Admitted.

Module Export Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star r => pumping_constant r
  end.

Lemma pumping_constant_ge_1 :
  forall T (re : reg_exp T),
    pumping_constant re >= 1.
Admitted.

Lemma pumping_constant_0_false :
  forall T (re : reg_exp T),
    pumping_constant re = 0 -> False.
Admitted.

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Admitted.

Lemma napp_star :
  forall T m s1 s2 (re : reg_exp T),
    s1 =~ re -> s2 =~ Star re ->
    napp m s1 ++ s2 =~ Star re.
Admitted.

Lemma weak_pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  -

    simpl.
intros contra.
inversion contra.
   Admitted.

Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    length s1 + length s2 <= pumping_constant re /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  -

    simpl.
intros contra.
inversion contra.
   Admitted.

End Pumping.

Theorem filter_not_empty_In : forall n l,
  filter (fun x => n =? x) l <> [] -> In n l.
Admitted.

Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT (H :   P) : reflect P true
  | ReflectF (H : ~ P) : reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Admitted.

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
   Admitted.

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Admitted.

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Admitted.

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n l Hcount.
induction l as [| m l' IHl'].
   Admitted.

Inductive nostutter {X:Type} : list X -> Prop :=

.

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
 Admitted.

Example test_nostutter_2:  nostutter (@nil nat).
 Admitted.

Example test_nostutter_3:  nostutter [5].
 Admitted.

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
 Admitted.

Definition manual_grade_for_nostutter : option (nat*string) := None.

Inductive merge {X:Type} : list X -> list X -> list X -> Prop :=

.

Theorem merge_filter : forall (X : Set) (test: X->bool) (l l1 l2 : list X),
  merge l1 l2 l ->
  All (fun n => test n = true) l1 ->
  All (fun n => test n = false) l2 ->
  filter test l = l1.
Proof.
   Admitted.

Inductive pal {X:Type} : list X -> Prop :=

.

Theorem pal_app_rev : forall (X:Type) (l : list X),
  pal (l ++ (rev l)).
Proof.
   Admitted.

Theorem pal_rev : forall (X:Type) (l: list X) , pal l -> l = rev l.
Proof.
   Admitted.

Theorem palindrome_converse: forall {X: Type} (l: list X),
    l = rev l -> pal l.
Proof.
   Admitted.

Module RecallIn.
   Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=
     match l with
     | [] => False
     | x' :: l' => x' = x \/ In A x l'
     end.
End RecallIn.

Definition manual_grade_for_NoDup_disjoint_etc : option (nat*string) := None.

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
   Admitted.

Inductive repeats {X:Type} : list X -> Prop :=

.

Definition manual_grade_for_check_repeats : option (nat*string) := None.

Theorem pigeonhole_principle: excluded_middle ->
  forall (X:Type) (l1  l2:list X),
  (forall x, In x l1 -> In x l2) ->
  length l2 < length l1 ->
  repeats l1.
Proof.
  intros EM X l1.
induction l1 as [|x l1' IHl1'].
   Admitted.

Import Coq.Strings.Ascii.

Definition string := list ascii.

Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Admitted.

Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
Admitted.

Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
Admitted.

Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = [ ].
Admitted.

Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Admitted.

Lemma char_nomatch_char :
  forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
Admitted.

Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = [ ].
Admitted.

Lemma app_exists : forall (s : string) re0 re1,
  s =~ App re0 re1 <->
  exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Admitted.

Lemma app_ne : forall (a : ascii) s re0 re1,
  a :: s =~ (App re0 re1) <->
  ([ ] =~ re0 /\ a :: s =~ re1) \/
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
   Admitted.

Lemma union_disj : forall (s : string) re0 re1,
  s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Admitted.

Lemma star_ne : forall (a : ascii) s re,
  a :: s =~ Star re <->
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
   Admitted.

Definition refl_matches_eps m :=
  forall re : reg_exp ascii, reflect ([ ] =~ re) (m re).

Fixpoint match_eps (re: reg_exp ascii) : bool
  .
Admitted.

Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
   Admitted.

Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.

Definition derives d := forall a re, is_der re a (d a re).

Fixpoint derive (a : ascii) (re : reg_exp ascii) : reg_exp ascii
  .
Admitted.

Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.

Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof.
   Admitted.

Example test_der1 : match_eps (derive c (Char c)) = true.
Proof.
   Admitted.

Example test_der2 : match_eps (derive c (Char d)) = false.
Proof.
   Admitted.

Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof.
   Admitted.

Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof.
   Admitted.

Example test_der5 : match_eps (derive c (Star (Char c))) = true.
Proof.
   Admitted.

Example test_der6 :
  match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof.
   Admitted.

Example test_der7 :
  match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof.
   Admitted.

Lemma derive_corr : derives derive.
Proof.
   Admitted.

Definition matches_regex m : Prop :=
  forall (s : string) re, reflect (s =~ re) (m s re).

Fixpoint regex_match (s : string) (re : reg_exp ascii) : bool
  .
Admitted.

Theorem regex_match_correct : matches_regex regex_match.
Proof.
   Admitted.

End IndProp.

End LF.

End LF_DOT_IndProp.

Module Export LF_DOT_AltAuto.
Module Export LF.
Module Export AltAuto.

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality,-deprecated-syntactic-definition,-deprecated]".
Import Stdlib.Arith.Arith Stdlib.Lists.List.
Import LF.IndProp.

Fixpoint re_opt_e {T:Type} (re: reg_exp T) : reg_exp T :=
  match re with
  | App EmptyStr re2 => re_opt_e re2
  | App re1 re2 => App (re_opt_e re1) (re_opt_e re2)
  | Union re1 re2 => Union (re_opt_e re1) (re_opt_e re2)
  | Star re => Star (re_opt_e re)
  | _ => re
  end.

Lemma re_opt_e_match : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt_e re.
Admitted.

Theorem silly1 : forall n, 1 + n = S n.
Admitted.

Theorem silly2 : forall (P : Prop), P -> P.
Admitted.

Lemma simple_semi : forall n, (n + 1 =? 0) = false.
Admitted.

Lemma simple_semi' : forall n, (n + 1 =? 0) = false.
Admitted.

Lemma simple_semi'' : forall n, (n + 1 =? 0) = false.
Admitted.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
 Admitted.

Theorem add_assoc : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
 Admitted.

Fixpoint nonzeros (lst : list nat) :=
  match lst with
  | [] => []
  | 0 :: t => nonzeros t
  | h :: t => h :: nonzeros t
  end.

Lemma nonzeros_app : forall lst1 lst2 : list nat,
  nonzeros (lst1 ++ lst2) = (nonzeros lst1) ++ (nonzeros lst2).
Proof.
 Admitted.

Lemma re_opt_e_match' : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt_e re.
Admitted.

Theorem app_length : forall (X : Type) (lst1 lst2 : list X),
    length (lst1 ++ lst2) = (length lst1) + (length lst2).
Admitted.

Theorem app_length' : forall (X : Type) (lst1 lst2 : list X),
    length (lst1 ++ lst2) = (length lst1) + (length lst2).
Admitted.

Theorem add_assoc' : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
 Admitted.

Lemma re_opt_e_match'' : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt_e re.
Admitted.

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Admitted.

Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Admitted.

Theorem ev100: ev 100.
Proof.
 Admitted.

Fixpoint re_opt {T:Type} (re: reg_exp T) : reg_exp T :=
  match re with
  | App _ EmptySet => EmptySet
  | App EmptyStr re2 => re_opt re2
  | App re1 EmptyStr => re_opt re1
  | App re1 re2 => App (re_opt re1) (re_opt re2)
  | Union EmptySet re2 => re_opt re2
  | Union re1 EmptySet => re_opt re1
  | Union re1 re2 => Union (re_opt re1) (re_opt re2)
  | Star EmptySet => EmptyStr
  | Star EmptyStr => EmptyStr
  | Star re => Star (re_opt re)
  | EmptySet => EmptySet
  | EmptyStr => EmptyStr
  | Char x => Char x
  end.

Lemma re_opt_match : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt re.
Admitted.

Lemma re_opt_match' : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt re.
Proof.
 Admitted.

Definition manual_grade_for_re_opt : option (nat*string) := None.

Theorem hyp_name : forall (P : Prop), P -> P.
Admitted.

Theorem no_hyp_name : forall (P : Prop), P -> P.
Admitted.

Theorem false_assumed : False -> 0 = 1.
Admitted.

Theorem false_assumed' : False -> 0 = 1.
Admitted.

Theorem contras : forall (P : Prop), P -> ~P -> 0 = 1.
Admitted.

Theorem contras' : forall (P : Prop), P -> ~P -> 0 = 1.
Admitted.

Theorem many_eq : forall (n m o p : nat),
  n = m ->
  o = p ->
  [n; o] = [m; p].
Admitted.

Theorem many_eq' : forall (n m o p : nat),
  n = m ->
  o = p ->
  [n; o] = [m; p].
Admitted.

Check ev_0 : ev 0.
Check ev_SS : forall n : nat, ev n -> ev (S (S n)).

Example constructor_example: forall (n:nat),
    ev (n + n).
Admitted.

Import Stdlib.micromega.Lia.

Theorem lia_succeed1 : forall (n : nat),
  n > 0 -> n * 2 > n.
Admitted.

Theorem lia_succeed2 : forall (n m : nat),
    n * m = m * n.
Admitted.

Import Stdlib.setoid_ring.Ring.

Theorem mult_comm : forall (n m : nat),
    n * m = m * n.
Admitted.

Theorem eq_example1 :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (x : A) (y : B),
    y = f x -> g y = g (f x).
Admitted.

Theorem eq_example1' :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (x : A) (y : B),
    y = f x -> g y = g (f x).
Admitted.

Theorem eq_example2 : forall (n m o p : nat),
    n = m ->
    o = p ->
    (n, o) = (m, p).
Admitted.

Theorem eq_example3 : forall (X : Type) (h : X) (t : list X),
    [] <> h :: t.
Admitted.

Theorem intuition_succeed1 : forall (P : Prop),
    P -> P.
Admitted.

Theorem intuition_succeed2 : forall (P Q : Prop),
    ~ (P \/ Q) -> ~P /\ ~Q.
Admitted.

Theorem intuition_simplify2 : forall (x y : nat) (P Q : nat -> Prop),
  x = y /\ (P x -> Q x) /\ P x -> Q y.
Admitted.

Theorem intuition_simplify2' : forall (x y : nat) (P Q : nat -> Prop),
  x = y /\ (P x -> Q x) /\ P x -> Q y.
Admitted.

Theorem plus_id_exercise_from_basics : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
 Admitted.

Theorem add_assoc_from_induction : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
 Admitted.

Theorem S_injective_from_tactics : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
 Admitted.

Theorem or_distributes_over_and_from_logic : forall P Q R : Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
 Admitted.

Example auto_example_1 : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Admitted.

Example auto_example_1' : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Admitted.

Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P -> Q) -> (P -> S)) ->
  T ->
  P ->
  U.
Admitted.

Example auto_example_3 : forall (P Q R S T U: Prop),
  (P -> Q) ->
  (Q -> R) ->
  (R -> S) ->
  (S -> T) ->
  (T -> U) ->
  P ->
  U.
Admitted.

Example auto_example_4 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Admitted.

Example auto_example_5 : 2 = 2.
Admitted.

Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> n = m.
Admitted.

Example auto_example_6 : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Admitted.

Create HintDb le_db.
Hint Resolve le_antisym : le_db.

Example auto_example_6' : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Admitted.

Definition is_fortytwo x := (x = 42).

Hint Unfold is_fortytwo : le_db.

Example auto_example_7' : forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Admitted.

Example auto_example_8 : forall (n m : nat),
    n + m = m + n.
Admitted.

Lemma re_opt_match'' : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt re.
Proof.
 Admitted.

Definition manual_grade_for_re_opt_match'' : option (nat*string) := None.

Import Pumping.

Lemma weak_pumping : forall T (re : reg_exp T) s,
    s =~ re ->
    pumping_constant re <= length s ->
    exists s1 s2 s3,
      s = s1 ++ s2 ++ s3 /\
        s2 <> [] /\
        forall m, s1 ++ napp m s2 ++ s3 =~ re.

Proof.
 Admitted.

Definition manual_grade_for_pumping_redux : option (nat*string) := None.

Lemma pumping : forall T (re : reg_exp T) s,
    s =~ re ->
    pumping_constant re <= length s ->
    exists s1 s2 s3,
      s = s1 ++ s2 ++ s3 /\
        s2 <> [] /\
        length s1 + length s2 <= pumping_constant re /\
        forall m, s1 ++ napp m s2 ++ s3 =~ re.

Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ];
    simpl; try lia;
    intros Hlen.
 Admitted.

Definition manual_grade_for_pumping_redux_strong : option (nat*string) := None.

Example trans_example1:  forall a b c d,
    a <= b + b * c  ->
    (1 + c) * b <= d ->
    a <= d.
Admitted.

Example trans_example1':  forall a b c d,
    a <= b + b * c  ->
    (1 + c) * b <= d ->
    a <= d.
Admitted.

Example trans_example2:  forall a b c d,
    a <= b + b * c  ->
    b + b * c <= d ->
    a <= d.
Admitted.

Ltac simpl_and_try tac := simpl; try tac.

Example sat_ex1 : 1 + 1 = 2.
Admitted.

Example sat_ex2 : forall (n : nat), 1 - 1 + n + 1 = 1 + n.
Admitted.

Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Admitted.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Admitted.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Admitted.

Ltac destructpf x :=
  destruct x; try reflexivity.

Theorem plus_1_neq_0' : forall n : nat,
    (n + 1) =? 0 = false.
Admitted.

Theorem negb_involutive' : forall b : bool,
  negb (negb b) = b.
Admitted.

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Admitted.

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
 Admitted.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Admitted.

Theorem andb_true_elim2' : forall b c : bool,
    andb b c = true -> c = true.
Proof.
 Admitted.

Theorem andb3_exchange' :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
 Admitted.

Theorem app_nil_r : forall (X : Type) (lst : list X),
    lst ++ [] = lst.
Admitted.

Theorem match_ex1 : True.
Admitted.

Theorem match_ex2 : True /\ True.
Admitted.

Theorem match_ex2' : True /\ True.
Admitted.

Fail Definition redundant_match (n : nat) : nat :=
  match n with
  | x => x
  | 0 => 1
  end.

Theorem match_ex2'' : True /\ True.
Admitted.

Theorem match_ex3 : forall (P : Prop), P -> P.
Admitted.

Theorem match_ex3' : forall (P : Prop), P -> P.
Admitted.

Theorem match_ex4 : forall (P Q : Prop), P -> Q -> P.
Admitted.

Theorem match_ex5 : forall (P Q : Prop), P -> Q -> P.
Admitted.

Fail Definition dup_first_two_elts (lst : list nat) :=
  match lst with
  | x :: x :: _ => true
  | _ => false
  end.

Theorem app_nil_r' : forall (X : Type) (lst : list X),
    lst ++ [] = lst.
Admitted.

Ltac simple_induction t :=
  induction t; simpl;
  try match goal with
      | [H : _ = _ |- _] => rewrite H
      end;
  reflexivity.

Theorem app_nil_r'' : forall (X : Type) (lst : list X),
    lst ++ [] = lst.
Admitted.

Theorem add_assoc'' : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Admitted.

Theorem add_assoc''' : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Admitted.

Theorem plus_n_Sm : forall n m : nat,
    S (n + m) = n + (S m).
Admitted.

Theorem plus_n_Sm' : forall n m : nat,
    S (n + m) = n + (S m).
Admitted.

Ltac imp_intuition :=
  repeat match goal with
         | [ H : ?P |- ?P ] => apply H
         | [ |- forall _, _ ] => intro
         | [ H1 : ?P -> ?Q, H2 : ?P |- _ ] => apply H1 in H2
         end.

Example imp1 : forall (P : Prop), P -> P.
Admitted.

Example imp2 : forall (P Q : Prop), P -> (P -> Q) -> Q.
Admitted.

Example imp3 : forall (P Q R : Prop), (P -> Q -> R) -> (Q -> P -> R).
Admitted.

Inductive nor (P Q : Prop) :=
| stroke : ~P -> ~Q -> nor P Q.

Theorem nor_not_or : forall (P Q : Prop),
    nor P Q -> ~ (P \/ Q).
Admitted.

Theorem nor_comm : forall (P Q : Prop),
    nor P Q <-> nor Q P.
Admitted.

Theorem nor_not : forall (P : Prop),
    nor P P <-> ~P.
Admitted.

Theorem nor_comm' : forall (P Q : Prop),
    nor P Q <-> nor Q P.
Proof.
 Admitted.

Theorem nor_not' : forall (P : Prop),
    nor P P <-> ~P.
Proof.
 Admitted.

Theorem nor_not_and' : forall (P Q : Prop),
    nor P Q -> ~ (P /\ Q).
Proof.
 Admitted.

Definition manual_grade_for_nor_intuition : option (nat*string) := None.

End AltAuto.

End LF.

End LF_DOT_AltAuto.

Module Export LF_DOT_AltAutoTest.
Set Warnings "-notation-overridden,-parsing".
Export Stdlib.Strings.String.
Import LF.AltAuto.

Parameter MISSING: Type.

Module Export Check.

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
Import LF.AltAuto.
Import Check.
Print Assumptions andb_eq_orb.
Print Assumptions add_assoc.
Print Assumptions nonzeros_app.
Print Assumptions add_assoc'.
Print Assumptions ev100.
Print Assumptions plus_id_exercise_from_basics.
Print Assumptions add_assoc_from_induction.
Print Assumptions S_injective_from_tactics.
Print Assumptions or_distributes_over_and_from_logic.
Print Assumptions andb3_exchange.
Print Assumptions andb_true_elim2'.
Print Assumptions andb3_exchange'.

End LF_DOT_AltAutoTest.

Module Export LF_DOT_Maps.
Module Export LF.
Module Export Maps.

Import Stdlib.Arith.Arith.
Import Stdlib.Bool.Bool.
Export Stdlib.Strings.String.
Import Stdlib.Logic.FunctionalExtensionality.
Import Stdlib.Lists.List.
Import ListNotations.
Set Default Goal Selector "!".

Locate "+".

Print Init.Nat.add.

Check String.eqb_refl :
  forall x : string, (x =? x)%string = true.

Check String.eqb_eq :
  forall n m : string, (n =? m)%string = true <-> n = m.
Check String.eqb_neq :
  forall n m : string, (n =? m)%string = false <-> n <> m.
Check String.eqb_spec :
  forall x y : string, reflect (x = y) (String.eqb x y).

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.

Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Example example_empty := (_ !-> false).

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _     !-> false
  ).

Example update_example1 : examplemap' "baz" = false.
Admitted.

Example update_example2 : examplemap' "foo" = true.
Admitted.

Example update_example3 : examplemap' "quux" = false.
Admitted.

Example update_example4 : examplemap' "bar" = true.
Admitted.

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
  (_ !-> v) x = v.
Proof.
   Admitted.

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof.
   Admitted.

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 ->
  (x1 !-> v ; m) x2 = m x2.
Proof.
   Admitted.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
   Admitted.

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
  (x !-> m x ; m) = m.
Proof.
   Admitted.

Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
  x2 <> x1 ->
  (x1 !-> v1 ; x2 !-> v2 ; m)
  =
  (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
   Admitted.

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

Notation "x '|->' v" := (update empty x v)
  (at level 100).

Definition examplepmap :=
  ("Church" |-> true ; "Turing" |-> false).

Lemma apply_empty : forall (A : Type) (x : string),
  @empty A x = None.
Admitted.

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
  (x |-> v ; m) x = Some v.
Admitted.

#[global] Hint Resolve update_eq : core.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
  x2 <> x1 ->
  (x2 |-> v ; m) x1 = m x1.
Admitted.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
  (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Admitted.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
  m x = Some v ->
  (x |-> v ; m) = m.
Admitted.

Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
  x2 <> x1 ->
  (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Admitted.

Definition includedin {A : Type} (m m' : partial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.

Lemma includedin_update : forall (A : Type) (m m' : partial_map A)
                                 (x : string) (vx : A),
  includedin m m' ->
  includedin (x |-> vx ; m) (x |-> vx ; m').
Admitted.

End Maps.

End LF.

End LF_DOT_Maps.

Module Export LF_DOT_Imp.
Module Export LF.
Module Imp.

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Import Stdlib.Bool.Bool.
Import Corelib.Init.Nat.
Import Stdlib.Arith.Arith.
Import Stdlib.Arith.EqNat.
Import Nat.
Import Stdlib.micromega.Lia.
Import Stdlib.Lists.List.
Import ListNotations.
Import Stdlib.Strings.String.
Import LF.Maps.
Set Default Goal Selector "!".

Module Export AExp.

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus  a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult  a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Admitted.

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval a1) =? (aeval a2)
  | BNeq a1 a2  => negb ((aeval a1) =? (aeval a2))
  | BLe a1 a2   => (aeval a1) <=? (aeval a2)
  | BGt a1 a2   => negb ((aeval a1) <=? (aeval a2))
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus  e1 e2 => APlus  (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult  e1 e2 => AMult  (optimize_0plus e1) (optimize_0plus e2)
  end.

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Admitted.

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Admitted.

Theorem silly1 : forall (P : Prop), P -> P.
Admitted.

Theorem silly2 : forall ae, aeval ae = aeval ae.
Admitted.

Lemma foo : forall n, 0 <=? n = true.
Admitted.

Lemma foo' : forall n, 0 <=? n = true.
Admitted.

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Admitted.

Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Admitted.

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Admitted.

Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Admitted.

Theorem repeat_loop : forall (m n : nat),
  m + n = n + m.
Proof.
  intros m n.

Admitted.

Fixpoint optimize_0plus_b (b : bexp) : bexp
  .
Admitted.

Example optimize_0plus_b_test1:
  optimize_0plus_b (BNot (BGt (APlus (ANum 0) (ANum 4)) (ANum 8))) =
                   (BNot (BGt (ANum 4) (ANum 8))).
Proof.
 Admitted.

Example optimize_0plus_b_test2:
  optimize_0plus_b (BAnd (BLe (APlus (ANum 0) (ANum 4)) (ANum 5)) BTrue) =
                   (BAnd (BLe (ANum 4) (ANum 5)) BTrue).
Proof.
 Admitted.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
   Admitted.

Ltac invert H :=
  inversion H; subst; clear H.

Lemma invert_example1: forall {a b c: nat}, [a ;b] = [a;c] -> b = c.
Admitted.

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Admitted.

Example add_comm__lia : forall m n,
    m + n = n + m.
Admitted.

Example add_assoc__lia : forall m n p,
    m + (n + p) = m + n + p.
Admitted.

Module Export aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      aevalR (ANum n) n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

Module Export HypothesisNames.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      aevalR (ANum n) n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMult e1 e2) (n1 * n2).

End HypothesisNames.

Notation "e '==>' n"
         := (aevalR e n)
            (at level 90, left associativity)
         : type_scope.

End aevalR_first_try.

Reserved Notation "e '==>' n" (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (APlus e1 e2)  ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMult e1 e2)  ==> (n1 * n2)

  where "e '==>' n" := (aevalR e n) : type_scope.

Definition manual_grade_for_beval_rules : option (nat*string) := None.

Theorem aevalR_iff_aeval : forall a n,
  (a ==> n) <-> aeval a = n.
Admitted.

Theorem aevalR_iff_aeval' : forall a n,
  (a ==> n) <-> aeval a = n.
Admitted.

Reserved Notation "e '==>b' b" (at level 90, left associativity).
Inductive bevalR: bexp -> bool -> Prop :=

where "e '==>b' b" := (bevalR e b) : type_scope
.

Lemma bevalR_iff_beval : forall b bv,
  b ==>b bv <-> beval b = bv.
Proof.
   Admitted.

End AExp.

Module Export aevalR_division.

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp).

Reserved Notation "e '==>' n"
                  (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (APlus a1 a2) ==> (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMinus a1 a2) ==> (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMult a1 a2) ==> (n1 * n2)
  | E_ADiv (a1 a2 : aexp) (n1 n2 n3 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (n2 > 0) ->
      (mult n2 n3 = n1) -> (ADiv a1 a2) ==> n3

where "a '==>' n" := (aevalR a n) : type_scope.

End aevalR_division.

Module Export aevalR_extended.

Reserved Notation "e '==>' n" (at level 90, left associativity).

Inductive aexp : Type :=
  | AAny
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any (n : nat) :
      AAny ==> n
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (APlus a1 a2) ==> (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMinus a1 a2) ==> (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMult a1 a2) ==> (n1 * n2)

where "a '==>' n" := (aevalR a n) : type_scope.

End aevalR_extended.

Definition state := total_map nat.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.
Declare Custom Entry com_aux.

Notation "<{ e }>" := e (e custom com_aux) : com_scope.
Notation "e" := e (in custom com_aux at level 0, e custom com) : com_scope.

Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y"   := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).

Open Scope com_scope.

Definition example_aexp : aexp := <{ 3 + (X * 2) }>.
Definition example_bexp : bexp := <{ true && ~(X <= 4) }>.

Fixpoint aeval (st : state)
               (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state)
               (b : bexp) : bool :=
  match b with
  | <{true}>      => true
  | <{false}>     => false
  | <{a1 = a2}>   => (aeval st a1) =? (aeval st a2)
  | <{a1 <> a2}>  => negb ((aeval st a1) =? (aeval st a2))
  | <{a1 <= a2}>  => (aeval st a1) <=? (aeval st a2)
  | <{a1 > a2}>   => negb ((aeval st a1) <=? (aeval st a2))
  | <{~ b1}>      => negb (beval st b1)
  | <{b1 && b2}>  => andb (beval st b1) (beval st b2)
  end.

Definition empty_st := (_ !-> 0).

Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100).

Example aexp1 :
    aeval (X !-> 5) <{ 3 + (X * 2) }>
  = 13.
Admitted.

Example aexp2 :
    aeval (X !-> 5 ; Y !-> 4) <{ Z + (X * Y) }>
  = 20.
Admitted.

Example bexp1 :
    beval (X !-> 5) <{ true && ~(X <= 4) }>
  = true.
Admitted.

Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90,
            right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
           (in custom com at level 89, x at level 99,
            y at level 99) : com_scope.

Definition fact_in_coq : com :=
  <{ Z := X;
     Y := 1;
     while Z <> 0 do
       Y := Y * Z;
       Z := Z - 1
     end }>.

Print fact_in_coq.

Unset Printing Notations.
Print fact_in_coq.

Set Printing Notations.

Print example_bexp.

Set Printing Coercions.
Print example_bexp.

Print fact_in_coq.

Unset Printing Coercions.

Locate aexp.

Locate "&&".

Locate ";".

Locate "while".

Definition plus2 : com :=
  <{ X := X + 2 }>.

Definition XtimesYinZ : com :=
  <{ Z := X * Y }>.

Definition subtract_slowly_body : com :=
  <{ Z := Z - 1 ;
     X := X - 1 }>.

Definition subtract_slowly : com :=
  <{ while X <> 0 do
       subtract_slowly_body
     end }>.

Definition subtract_3_from_5_slowly : com :=
  <{ X := 3 ;
     Z := 5 ;
     subtract_slowly }>.

Definition loop : com :=
  <{ while true do
       skip
     end }>.

Fixpoint ceval_fun_no_while (st : state) (c : com) : state :=
  match c with
    | <{ skip }> =>
        st
    | <{ x := a }> =>
        (x !-> (aeval st a) ; st)
    | <{ c1 ; c2 }> =>
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | <{ if b then c1 else c2 end}> =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | <{ while b do c end }> =>
        st
  end.

Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

Example ceval_example1:
  empty_st =[
     X := 2;
     if (X <= 1)
       then Y := 3
       else Z := 4
     end
  ]=> (Z !-> 4 ; X !-> 2).
Admitted.

Example ceval_example2:
  empty_st =[
    X := 0;
    Y := 1;
    Z := 2
  ]=> (Z !-> 2 ; Y !-> 1 ; X !-> 0).
Proof.
   Admitted.

Set Printing Implicit.
Check @ceval_example2.

Definition pup_to_n : com
  .
Admitted.

Theorem pup_to_2_ceval :
  (X !-> 2) =[
    pup_to_n
  ]=> (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
Proof.
   Admitted.

Theorem ceval_deterministic: forall c st st1 st2,
     st =[ c ]=> st1  ->
     st =[ c ]=> st2 ->
     st1 = st2.
Admitted.

Theorem plus2_spec : forall st n st',
  st X = n ->
  st =[ plus2 ]=> st' ->
  st' X = n + 2.
Admitted.

Definition manual_grade_for_XtimesYinZ_spec : option (nat*string) := None.

Theorem loop_never_stops : forall st st',
  ~(st =[ loop ]=> st').
Proof.
  intros st st' contra.
unfold loop in contra.
  remember <{ while true do skip end }> as loopdef
           eqn:Heqloopdef.

   Admitted.

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | <{ skip }> =>
      true
  | <{ _ := _ }> =>
      true
  | <{ c1 ; c2 }> =>
      andb (no_whiles c1) (no_whiles c2)
  | <{ if _ then ct else cf end }> =>
      andb (no_whiles ct) (no_whiles cf)
  | <{ while _ do _ end }>  =>
      false
  end.

Inductive no_whilesR: com -> Prop :=

.

Theorem no_whiles_eqv:
  forall c, no_whiles c = true <-> no_whilesR c.
Proof.
   Admitted.

Definition manual_grade_for_no_whiles_terminating : option (nat*string) := None.

Inductive sinstr : Type :=
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult.

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat
  .
Admitted.

Check s_execute.

Example s_execute1 :
     s_execute empty_st []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
 Admitted.

Example s_execute2 :
     s_execute (X !-> 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
 Admitted.

Fixpoint s_compile (e : aexp) : list sinstr
  .
Admitted.

Example s_compile1 :
  s_compile <{ X - (2 * Y) }>
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
 Admitted.

Theorem execute_app : forall st p1 p2 stack,
  s_execute st stack (p1 ++ p2) = s_execute st (s_execute st stack p1) p2.
Proof.
   Admitted.

Lemma s_compile_correct_aux : forall st e stack,
  s_execute st stack (s_compile e) = aeval st e :: stack.
Proof.
   Admitted.

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
   Admitted.

Module BreakImp.

Inductive com : Type :=
  | CSkip
  | CBreak
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'break'" := CBreak (in custom com at level 0).
Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.

Inductive result : Type :=
  | SContinue
  | SBreak.

Reserved Notation "st '=[' c ']=>' st' '/' s"
     (at level 40, c custom com at level 99, st' constr at next level).

Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
      st =[ CSkip ]=> st / SContinue

  where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').

Theorem break_ignore : forall c st st' s,
     st =[ break; c ]=> st' / s ->
     st = st'.
Proof.
   Admitted.

Theorem while_continue : forall b c st st' s,
  st =[ while b do c end ]=> st' / s ->
  s = SContinue.
Proof.
   Admitted.

Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  st =[ c ]=> st' / SBreak ->
  st =[ while b do c end ]=> st' / SContinue.
Proof.
   Admitted.

Theorem seq_continue : forall c1 c2 st st' st'',
  st =[ c1 ]=> st' / SContinue ->
  st' =[ c2 ]=> st'' / SContinue ->
  st =[ c1 ; c2 ]=> st'' / SContinue.
Proof.
   Admitted.

Theorem seq_stops_on_break : forall c1 c2 st st',
  st =[ c1 ]=> st' / SBreak ->
  st =[ c1 ; c2 ]=> st' / SBreak.
Proof.
   Admitted.

Theorem while_break_true : forall b c st st',
  st =[ while b do c end ]=> st' / SContinue ->
  beval st' b = true ->
  exists st'', st'' =[ c ]=> st' / SBreak.
Proof.
 Admitted.

Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     st =[ c ]=> st1 / s1 ->
     st =[ c ]=> st2 / s2 ->
     st1 = st2 /\ s1 = s2.
Proof.
   Admitted.

End BreakImp.

End Imp.

End LF.

End LF_DOT_Imp.

Module Export LF_DOT_Auto.
Module Export LF.
Module Export Auto.

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Import Stdlib.micromega.Lia.
Import Stdlib.Strings.String.
Import LF.Maps.
Import LF.Imp.

Theorem ceval_deterministic: forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Admitted.

Example auto_example_1 : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Admitted.

Example auto_example_1' : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Admitted.

Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P -> Q) -> (P -> S)) ->
  T ->
  P ->
  U.
Admitted.

Example auto_example_3 : forall (P Q R S T U: Prop),
  (P -> Q) ->
  (Q -> R) ->
  (R -> S) ->
  (S -> T) ->
  (T -> U) ->
  P ->
  U.
Admitted.

Example auto_example_4 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Admitted.

Example auto_example_5: 2 = 2.
Admitted.

Example auto_example_5' : forall (P Q R S T U W: Prop),
  (U -> T) ->
  (W -> U) ->
  (R -> S) ->
  (S -> T) ->
  (P -> R) ->
  (U -> T) ->
  P ->
  T.
Admitted.

Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> n = m.
Admitted.

Example auto_example_6 : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Admitted.

Hint Resolve le_antisym : core.

Example auto_example_6' : forall n m p : nat,
  (n<= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Admitted.

Definition is_fortytwo x := (x = 42).

Hint Unfold is_fortytwo : core.

Example auto_example_7' : forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Admitted.

Theorem ceval_deterministic': forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Admitted.

Theorem ceval_deterministic'_alt: forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Admitted.

Ltac rwd H1 H2 := rewrite H1 in H2; discriminate.

Theorem ceval_deterministic'': forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Admitted.

Ltac find_rwd :=
  match goal with
    H1: ?E = true,
    H2: ?E = false
    |- _ => rwd H1 H2
  end.

Theorem ceval_deterministic''': forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Admitted.

Ltac find_eqn :=
  match goal with
    H1: forall x, ?P x -> ?L = ?R,
    H2: ?P ?X
    |- _ => rewrite (H1 X H2) in *
  end.

Theorem ceval_deterministic'''': forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Admitted.

Module Export Repeat.

Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CRepeat (c : com) (b : bexp).

Notation "'repeat' x 'until' y 'end'" :=
         (CRepeat x y)
            (in custom com at level 0,
             x at level 99, y at level 99).
Notation "'skip'"  :=
         CSkip (in custom com at level 0).
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).

Reserved Notation "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''
  | E_RepeatEnd : forall st st' b c,
      st  =[ c ]=> st' ->
      beval st' b = true ->
      st  =[ repeat c until b end ]=> st'
  | E_RepeatLoop : forall st st' st'' b c,
      st  =[ c ]=> st' ->
      beval st' b = false ->
      st' =[ repeat c until b end ]=> st'' ->
      st  =[ repeat c until b end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

Theorem ceval_deterministic: forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Admitted.

Theorem ceval_deterministic': forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Admitted.

End Repeat.

Example ceval_example1:
  empty_st =[
    X := 2;
    if (X <= 1)
      then Y := 3
      else Z := 4
    end
  ]=> (Z !-> 4 ; X !-> 2).
Admitted.

Example ceval'_example1:
  empty_st =[
    X := 2;
    if (X <= 1)
      then Y := 3
      else Z := 4
    end
  ]=> (Z !-> 4 ; X !-> 2).
Admitted.

Hint Constructors ceval : core.
Hint Transparent state total_map : core.

Example eauto_example : exists s',
  (Y !-> 1 ; X !-> 2) =[
    if (X <= Y)
      then Z := Y - X
      else Y := X + Z
    end
  ]=> s'.
Admitted.

Lemma silly2_fixed :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Admitted.

Lemma silly2_eassumption : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Admitted.

Lemma silly2_eauto : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Admitted.

End Auto.

End LF.

End LF_DOT_Auto.

Module Export LF_DOT_AutoTest.
Set Warnings "-notation-overridden,-parsing".
Export Stdlib.Strings.String.
Import LF.Auto.

Parameter MISSING: Type.

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
Import LF.Auto.
Import Check.

End LF_DOT_AutoTest.

Module Export LF_DOT_BasicsTest.
Set Warnings "-notation-overridden,-parsing".
Export Stdlib.Strings.String.
Import LF.Basics.

Parameter MISSING: Type.

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
Import LF.Basics.
Import Check.
Print Assumptions test_nandb4.
Print Assumptions test_andb34.
Print Assumptions test_factorial2.
Print Assumptions test_ltb3.
Print Assumptions plus_id_exercise.
Print Assumptions mult_n_1.
Print Assumptions andb_true_elim2.
Print Assumptions zero_nbeq_plus_1.
Print Assumptions identity_fn_applied_twice.
Print Assumptions LateDays.letter_comparison_Eq.
Print Assumptions LateDays.test_grade_comparison1.
Print Assumptions LateDays.test_grade_comparison2.
Print Assumptions LateDays.test_grade_comparison3.
Print Assumptions LateDays.test_grade_comparison4.
Print Assumptions LateDays.lower_letter_lowers.
Print Assumptions LateDays.lower_grade_A_Plus.
Print Assumptions LateDays.lower_grade_A_Natural.
Print Assumptions LateDays.lower_grade_A_Minus.
Print Assumptions LateDays.lower_grade_B_Plus.
Print Assumptions LateDays.lower_grade_F_Natural.
Print Assumptions LateDays.lower_grade_twice.
Print Assumptions LateDays.lower_grade_thrice.
Print Assumptions LateDays.lower_grade_F_Minus.
Print Assumptions LateDays.lower_grade_lowers.
Print Assumptions LateDays.no_penalty_for_mostly_on_time.
Print Assumptions LateDays.grade_lowered_once.
Print Assumptions test_bin_incr1.
Print Assumptions test_bin_incr2.
Print Assumptions test_bin_incr3.
Print Assumptions test_bin_incr4.
Print Assumptions test_bin_incr5.
Print Assumptions test_bin_incr6.

End LF_DOT_BasicsTest.

Module Export LF_DOT_Bib.
Module Export LF.
Module Export Bib.

End Bib.

End LF.

End LF_DOT_Bib.

Module Export LF_DOT_BibTest.
Set Warnings "-notation-overridden,-parsing".
Export Stdlib.Strings.String.
Import LF.Bib.

Parameter MISSING: Type.

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
Import LF.Bib.
Import Check.

End LF_DOT_BibTest.

Module Export LF_DOT_ImpCEvalFun.
Module Export LF.
Module Export ImpCEvalFun.

Import Stdlib.micromega.Lia.
Import Stdlib.Arith.Arith.
Import Stdlib.Arith.PeanoNat.
Import Nat.
Import Stdlib.Arith.EqNat.
Import LF.Imp LF.Maps.

Fixpoint ceval_step1 (st : state) (c : com) : state :=
  match c with
    | <{ skip }> =>
        st
    | <{ l := a1 }> =>
        (l !-> aeval st a1 ; st)
    | <{ c1 ; c2 }> =>
        let st' := ceval_step1 st c1 in
        ceval_step1 st' c2
    | <{ if b then c1 else c2 end }> =>
        if (beval st b)
          then ceval_step1 st c1
          else ceval_step1 st c2
    | <{ while b1 do c1 end }> =>
        st
  end.

Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with
  | O => empty_st
  | S i' =>
    match c with
      | <{ skip }> =>
          st
      | <{ l := a1 }> =>
          (l !-> aeval st a1 ; st)
      | <{ c1 ; c2 }> =>
          let st' := ceval_step2 st c1 i' in
          ceval_step2 st' c2 i'
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step2 st c1 i'
            else ceval_step2 st c2 i'
      | <{ while b1 do c1 end }> =>
          if (beval st b1)
          then let st' := ceval_step2 st c1 i' in
               ceval_step2 st' c i'
          else st
    end
  end.

Fixpoint ceval_step3 (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | <{ skip }> =>
          Some st
      | <{ l := a1 }> =>
          Some (l !-> aeval st a1 ; st)
      | <{ c1 ; c2 }> =>
          match (ceval_step3 st c1 i') with
          | Some st' => ceval_step3 st' c2 i'
          | None => None
          end
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step3 st c1 i'
            else ceval_step3 st c2 i'
      | <{ while b1 do c1 end }> =>
          if (beval st b1)
          then match (ceval_step3 st c1 i') with
               | Some st' => ceval_step3 st' c i'
               | None => None
               end
          else Some st
    end
  end.

Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).

Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | <{ skip }> =>
          Some st
      | <{ l := a1 }> =>
          Some (l !-> aeval st a1 ; st)
      | <{ c1 ; c2 }> =>
          LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | <{ while b1 do c1 end }> =>
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
    end
  end.

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None    => None
  | Some st => Some (st X, st Y, st Z)
  end.

Example example_test_ceval :
     test_ceval empty_st

     <{ X := 2;
        if (X <= 1)
        then Y := 3
        else Z := 4
        end }>

     = Some (2, 0, 4).
Admitted.

Definition pup_to_n : com
  .
Admitted.

Example pup_to_n_1 :
  test_ceval (X !-> 5) pup_to_n
  = Some (0, 15, 0).
 Admitted.

Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      st =[ c ]=> st'.
Admitted.

Definition manual_grade_for_ceval_step__ceval_inf : option (nat*string) := None.

Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 ->
  ceval_step st c i1 = Some st' ->
  ceval_step st c i2 = Some st'.
Admitted.

Theorem ceval__ceval_step: forall c st st',
      st =[ c ]=> st' ->
      exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st' Hce.
  induction Hce.
   Admitted.

Theorem ceval_and_ceval_step_coincide: forall c st st',
      st =[ c ]=> st'
  <-> exists i, ceval_step st c i = Some st'.
Admitted.

Theorem ceval_deterministic' : forall c st st1 st2,
     st =[ c ]=> st1 ->
     st =[ c ]=> st2 ->
     st1 = st2.
Admitted.

End ImpCEvalFun.

End LF.

End LF_DOT_ImpCEvalFun.

Module Export LF_DOT_ImpParser.
Module Export LF.
Module Export ImpParser.

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Import Stdlib.Strings.String.
Import Stdlib.Strings.Ascii.
Import Stdlib.Arith.Arith.
Import Corelib.Init.Nat.
Import Stdlib.Arith.EqNat.
Import Stdlib.Lists.List.
Import ListNotations.
Import LF.Maps LF.Imp.

Definition isWhite (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (orb (n =? 32)
           (n =? 9))
      (orb (n =? 10)
           (n =? 13)).

Notation "x '<=?' y" := (x <=? y)
  (at level 70, no associativity) : nat_scope.

Definition isLowerAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    andb (97 <=? n) (n <=? 122).

Definition isAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    orb (andb (65 <=? n) (n <=? 90))
        (andb (97 <=? n) (n <=? 122)).

Definition isDigit (c : ascii) : bool :=
  let n := nat_of_ascii c in
     andb (48 <=? n) (n <=? 57).

Inductive chartype := white | alpha | digit | other.

Definition classifyChar (c : ascii) : chartype :=
  if isWhite c then
    white
  else if isAlpha c then
    alpha
  else if isDigit c then
    digit
  else
    other.

Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s => c :: (list_of_string s)
  end.

Definition string_of_list (xs : list ascii) : string :=
  fold_right String EmptyString xs.

Definition token := string.

Fixpoint tokenize_helper (cls : chartype) (acc xs : list ascii)
                       : list (list ascii) :=
  let tk := match acc with [] => [] | _::_ => [rev acc] end in
  match xs with
  | [] => tk
  | (x::xs') =>
    match cls, classifyChar x, x with
    | _, _, "("      =>
      tk ++ ["("]::(tokenize_helper other [] xs')
    | _, _, ")"      =>
      tk ++ [")"]::(tokenize_helper other [] xs')
    | _, white, _    =>
      tk ++ (tokenize_helper white [] xs')
    | alpha,alpha,x  =>
      tokenize_helper alpha (x::acc) xs'
    | digit,digit,x  =>
      tokenize_helper digit (x::acc) xs'
    | other,other,x  =>
      tokenize_helper other (x::acc) xs'
    | _,tp,x         =>
      tk ++ (tokenize_helper tp [x] xs')
    end
  end %char.

Definition tokenize (s : string) : list string :=
  map string_of_list (tokenize_helper white [] (list_of_string s)).

Example tokenize_ex1 :
    tokenize "abc12=3  223*(3+(a+c))" %string
  = ["abc"; "12"; "="; "3"; "223";
       "*"; "("; "3"; "+"; "(";
       "a"; "+"; "c"; ")"; ")"]%string.
Admitted.

Inductive optionE (X:Type) : Type :=
  | SomeE (x : X)
  | NoneE (s : string).

Arguments SomeE {X}.
Arguments NoneE {X}.

Notation "' p <- e1 ;; e2"
   := (match e1 with
       | SomeE p => e2
       | NoneE err => NoneE err
       end)
   (right associativity, p pattern, at level 60, e1 at next level).

Notation "'TRY' e1 'OR' e2"
   := (
    let result := e1 in
    match result with
       | SomeE _  => result
       | NoneE _ => e2
       end)
   (right associativity,
    at level 60, e1 at next level, e2 at next level).

Open Scope string_scope.

Definition parser (T : Type) :=
  list token -> optionE (T * list token).

Fixpoint many_helper {T} (p : parser T) acc steps xs :=
  match steps, p xs with
  | 0, _ =>
      NoneE "Too many recursive calls"
  | _, NoneE _ =>
      SomeE ((rev acc), xs)
  | S steps', SomeE (t, xs') =>
      many_helper p (t :: acc) steps' xs'
  end.

Definition many {T} (p : parser T) (steps : nat) : parser (list T) :=
  many_helper p [] steps.

Definition firstExpect {T} (t : token) (p : parser T)
                     : parser T :=
  fun xs => match xs with
            | x::xs' =>
              if string_dec x t
              then p xs'
              else NoneE ("expected '" ++ t ++ "'.")
            | [] =>
              NoneE ("expected '" ++ t ++ "'.")
            end.

Definition expect (t : token) : parser unit :=
  firstExpect t (fun xs => SomeE (tt, xs)).

Definition parseIdentifier (xs : list token)
                         : optionE (string * list token) :=
match xs with
| [] => NoneE "Expected identifier"
| x::xs' =>
    if forallb isLowerAlpha (list_of_string x) then
      SomeE (x, xs')
    else
      NoneE ("Illegal identifier:'" ++ x ++ "'")
end.

Definition parseNumber (xs : list token)
                     : optionE (nat * list token) :=
match xs with
| [] => NoneE "Expected number"
| x::xs' =>
    if forallb isDigit (list_of_string x) then
      SomeE (fold_left
               (fun n d =>
                  10 * n + (nat_of_ascii d -
                            nat_of_ascii "0"%char))
               (list_of_string x)
               0,
             xs')
    else
      NoneE "Expected number"
end.

Fixpoint parsePrimaryExp (steps:nat)
                         (xs : list token)
                       : optionE (aexp * list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
      TRY ' (i, rest) <- parseIdentifier xs ;;
          SomeE (AId i, rest)
      OR
      TRY ' (n, rest) <- parseNumber xs ;;
          SomeE (ANum n, rest)
      OR
      ' (e, rest) <- firstExpect "(" (parseSumExp steps') xs ;;
      ' (u, rest') <- expect ")" rest ;;
      SomeE (e,rest')
  end

with parseProductExp (steps:nat)
                     (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    ' (e, rest) <- parsePrimaryExp steps' xs ;;
    ' (es, rest') <- many (firstExpect "*" (parsePrimaryExp steps'))
                          steps' rest ;;
    SomeE (fold_left AMult es e, rest')
  end

with parseSumExp (steps:nat) (xs : list token)  :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    ' (e, rest) <- parseProductExp steps' xs ;;
    ' (es, rest') <-
        many (fun xs =>
                TRY ' (e,rest') <-
                    firstExpect "+"
                                (parseProductExp steps') xs ;;
                    SomeE ( (true, e), rest')
                OR
                ' (e, rest') <-
                    firstExpect "-"
                                (parseProductExp steps') xs ;;
                SomeE ( (false, e), rest'))
        steps' rest ;;
      SomeE (fold_left (fun e0 term =>
                          match term with
                          | (true,  e) => APlus e0 e
                          | (false, e) => AMinus e0 e
                          end)
                       es e,
             rest')
  end.

Definition parseAExp := parseSumExp.

Fixpoint parseAtomicExp (steps:nat)
                        (xs : list token)  :=
match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
     TRY ' (u,rest) <- expect "true" xs ;;
         SomeE (BTrue,rest)
     OR
     TRY ' (u,rest) <- expect "false" xs ;;
         SomeE (BFalse,rest)
     OR
     TRY ' (e,rest) <- firstExpect "~"
                                   (parseAtomicExp steps')
                                   xs ;;
         SomeE (BNot e, rest)
     OR
     TRY ' (e,rest) <- firstExpect "("
                                   (parseConjunctionExp steps')
                                   xs ;;
         ' (u,rest') <- expect ")" rest ;;
         SomeE (e, rest')
     OR
     ' (e, rest) <- parseProductExp steps' xs ;;
     TRY ' (e', rest') <- firstExpect "="
                                  (parseAExp steps') rest ;;
         SomeE (BEq e e', rest')
     OR
     TRY ' (e', rest') <- firstExpect "<="
                                      (parseAExp steps') rest ;;
         SomeE (BLe e e', rest')
     OR
     NoneE "Expected '=' or '<=' after arithmetic expression"
end

with parseConjunctionExp (steps:nat)
                         (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    ' (e, rest) <- parseAtomicExp steps' xs ;;
    ' (es, rest') <- many (firstExpect "&&"
               (parseAtomicExp steps'))
            steps' rest ;;
    SomeE (fold_left BAnd es e, rest')
  end.

Definition parseBExp := parseConjunctionExp.

Check parseConjunctionExp.

Definition testParsing {X : Type}
           (p : nat ->
                list token ->
                optionE (X * list token))
           (s : string) :=
  let t := tokenize s in
  p 100 t.

Fixpoint parseSimpleCommand (steps:nat)
                            (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    TRY ' (u, rest) <- expect "skip" xs ;;
        SomeE (<{skip}>, rest)
    OR
    TRY ' (e,rest) <-
            firstExpect "if"
                        (parseBExp steps') xs ;;
        ' (c,rest') <-
            firstExpect "then"
                        (parseSequencedCommand steps') rest ;;
        ' (c',rest'') <-
            firstExpect "else"
                        (parseSequencedCommand steps') rest' ;;
        ' (tt,rest''') <-
            expect "end" rest'' ;;
       SomeE(<{if e then c else c' end}>, rest''')
    OR
    TRY ' (e,rest) <-
            firstExpect "while"
                        (parseBExp steps') xs ;;
        ' (c,rest') <-
            firstExpect "do"
                        (parseSequencedCommand steps') rest ;;
        ' (u,rest'') <-
            expect "end" rest' ;;
        SomeE(<{while e do c end}>, rest'')
    OR
    TRY ' (i, rest) <- parseIdentifier xs ;;
        ' (e, rest') <- firstExpect ":=" (parseAExp steps') rest ;;
        SomeE (<{i := e}>, rest')
    OR
        NoneE "Expecting a command"
end

with parseSequencedCommand (steps:nat)
                           (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    ' (c, rest) <- parseSimpleCommand steps' xs ;;
    TRY ' (c', rest') <-
            firstExpect ";"
                        (parseSequencedCommand steps') rest ;;
        SomeE (<{c ; c'}>, rest')
    OR
    SomeE (c, rest)
  end.

Definition bignumber := 1000.

Definition parse (str : string) : optionE com :=
  let tokens := tokenize str in
  match parseSequencedCommand bignumber tokens with
  | SomeE (c, []) => SomeE c
  | SomeE (_, t::_) => NoneE ("Trailing tokens remaining: " ++ t)
  | NoneE err => NoneE err
  end.

Example eg1 : parse "
  if x = y + 1 + 2 - y * 6 + 3 then
    x := x * 1;
    y := 0
  else
    skip
  end  "
=
  SomeE <{
      if ("x" = ("y" + 1 + 2 - "y" * 6 + 3)) then
        "x" := "x" * 1;
        "y" := 0
      else
        skip
      end }>.
Admitted.

Example eg2 : parse "
  skip;
  z:=x*y*(x*x);
  while x=x do
    if (z <= z*z) && ~(x = 2) then
      x := z;
      y := z
    else
      skip
    end;
    skip
  end;
  x:=z  "
=
  SomeE <{
      skip;
      "z" := "x" * "y" * ("x" * "x");
      while ("x" = "x") do
        if ("z" <= "z" * "z") && ~("x" = 2) then
          "x" := "z";
          "y" := "z"
        else
          skip
        end;
        skip
      end;
      "x" := "z" }>.
Admitted.

End ImpParser.

End LF.

End LF_DOT_ImpParser.

Module Export LF_DOT_Extraction.
Module Export LF.
Module Export Extraction.

Extraction Language OCaml.

Import Stdlib.Arith.Arith.
Import Corelib.Init.Nat.
Import Stdlib.Arith.EqNat.
Import LF.ImpCEvalFun.

Extraction "imp1.ml" ceval_step.

Extract Inductive bool => "bool" [ "true" "false" ].

Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n ->
      if n=0 then zero () else succ (n-1))".

Extract Constant plus => "( + )".
Extract Constant mult => "( * )".
Extract Constant eqb => "( = )".

Extraction "imp2.ml" ceval_step.

Import Corelib.extraction.ExtrOcamlBasic.
Import Stdlib.extraction.ExtrOcamlString.

Extract Inductive sumbool => "bool" ["true" "false"].

Import LF.Imp.
Import LF.ImpParser.
Import LF.Maps.
Extraction "imp.ml" empty_st ceval_step parse.

End Extraction.

End LF.

End LF_DOT_Extraction.

Module Export LF_DOT_ExtractionTest.
Set Warnings "-notation-overridden,-parsing".
Export Stdlib.Strings.String.
Import LF.Extraction.

Parameter MISSING: Type.

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
Import LF.Extraction.
Import Check.

End LF_DOT_ExtractionTest.

Module Export LF_DOT_ImpCEvalFunTest.
Set Warnings "-notation-overridden,-parsing".
Export Stdlib.Strings.String.
Import LF.ImpCEvalFun.

Parameter MISSING: Type.

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
Import LF.ImpCEvalFun.
Import Check.
Print Assumptions ceval__ceval_step.

End LF_DOT_ImpCEvalFunTest.

Module Export LF_DOT_ImpParserTest.
Set Warnings "-notation-overridden,-parsing".
Export Stdlib.Strings.String.
Import LF.ImpParser.

Parameter MISSING: Type.

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
Import LF.ImpParser.
Import Check.

End LF_DOT_ImpParserTest.

Module Export LF_DOT_ImpTest.
Set Warnings "-notation-overridden,-parsing".
Export Stdlib.Strings.String.
Import LF.Imp.

Parameter MISSING: Type.

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
Import LF.Imp.
Import Check.
Print Assumptions AExp.optimize_0plus_b_test1.
Print Assumptions AExp.optimize_0plus_b_test2.
Print Assumptions AExp.optimize_0plus_b_sound.
Print Assumptions AExp.bevalR_iff_beval.
Print Assumptions ceval_example2.
Print Assumptions loop_never_stops.
Print Assumptions no_whiles_eqv.
Print Assumptions s_execute1.
Print Assumptions s_execute2.
Print Assumptions s_compile1.
Print Assumptions execute_app.
Print Assumptions s_compile_correct_aux.
Print Assumptions s_compile_correct.
Print Assumptions BreakImp.break_ignore.
Print Assumptions BreakImp.while_continue.
Print Assumptions BreakImp.while_stops_on_break.
Print Assumptions BreakImp.seq_continue.
Print Assumptions BreakImp.seq_stops_on_break.

End LF_DOT_ImpTest.

Module Export LF_DOT_ProofObjects.
Module Export LF.
Module Export ProofObjects.

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Export LF.IndProp.

Inductive ev : nat -> Prop :=
  | ev_0                       : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

Check ev_SS
  : forall n,
    ev n ->
    ev (S (S n)).

Theorem ev_4 : ev 4.
Admitted.

Print ev_4.

Check (ev_SS 2 (ev_SS 0 ev_0))
  : ev 4.

Theorem ev_4': ev 4.
Admitted.

Theorem ev_4'' : ev 4.
Admitted.

Definition ev_4''' : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

Print ev_4.

Print ev_4'.

Print ev_4''.

Print ev_4'''.

Theorem ev_8 : ev 8.
Proof.
   Admitted.

Definition ev_8' : ev 8
  .
Admitted.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Admitted.

Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun (n : nat) => fun (H : ev n) =>
    ev_SS (S (S n)) (ev_SS n H).

Definition ev_plus4'' (n : nat) (H : ev n)
                    : ev (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4'' : forall n : nat, ev n -> ev (4 + n).

Definition ev_plus2 : Prop :=
  forall n, forall (E : ev n), ev (n + 2).

Definition ev_plus2' : Prop :=
  forall n, forall (_ : ev n), ev (n + 2).

Definition ev_plus2'' : Prop :=
  forall n, ev n -> ev (n + 2).

Definition add1 : nat -> nat.
intro n.
Show Proof.
apply S.
Show Proof.
apply n.
Defined.

Print add1.

Compute add1 2.

Module Props.

Module And.

Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q.

Arguments conj [P] [Q].

Notation "P /\ Q" := (and P Q) : type_scope.

Print prod.

Theorem proj1' : forall P Q,
  P /\ Q -> P.
Admitted.

Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Admitted.

End And.

Definition proj1'' P Q (HPQ : P /\ Q) : P :=
  match HPQ with
  | conj HP HQ => HP
  end.

Definition and_comm'_aux P Q (H : P /\ Q) : Q /\ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R
  .
Admitted.

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Arguments or_introl [P] [Q].
Arguments or_intror [P] [Q].

Notation "P \/ Q" := (or P Q) : type_scope.

Definition inj_l : forall (P Q : Prop), P -> P \/ Q :=
  fun P Q HP => or_introl HP.

Theorem inj_l' : forall (P Q : Prop), P -> P \/ Q.
Admitted.

Definition or_elim : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R :=
  fun P Q R HPQ HPR HQR =>
    match HPQ with
    | or_introl HP => HPR HP
    | or_intror HQ => HQR HQ
    end.

Theorem or_elim' : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R.
Admitted.

Definition or_commut' : forall P Q, P \/ Q -> Q \/ P
  .
Admitted.

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
  | ex_intro : forall x : A, P x -> ex P.

Notation "'exists' x , p" :=
  (ex (fun x => p))
    (at level 200, right associativity) : type_scope.

Check ex (fun n => ev n) : Prop.

Definition some_nat_is_even : exists n, ev n :=
  ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

Definition ex_ev_Sn : ex (fun n => ev (S n))
  .
Admitted.

Definition dist_exists_or_term (X:Type) (P Q : X -> Prop) :
  (exists x, P x \/ Q x) -> (exists x, P x) \/ (exists x, Q x) :=
  fun H => match H with
           | ex_intro _ x Hx =>
               match Hx with
               | or_introl HPx => or_introl (ex_intro _ x HPx)
               | or_intror HQx => or_intror (ex_intro _ x HQx)
               end
           end.

Definition ex_match : forall (A : Type) (P Q : A -> Prop),
  (forall x, P x -> Q x) ->
  (exists x, P x) -> (exists x, Q x)
  .
Admitted.

Inductive True : Prop :=
  | I : True.

Definition p_implies_true : forall P, P -> True
  .
Admitted.

Inductive False : Prop := .

Fail
  Definition contra : False :=
  42.

Definition false_implies_zero_eq_one : False -> 0 = 1 :=
  fun contra => match contra with end.

Definition ex_falso_quodlibet' : forall P, False -> P
  .
Admitted.

End Props.

Module Export EqualityPlayground.

Inductive eq {X:Type} : X -> X -> Prop :=
  | eq_refl : forall x, eq x x.

Notation "x == y" := (eq x y)
                       (at level 70, no associativity)
                     : type_scope.

Lemma four: 2 + 2 == 1 + 3.
Admitted.

Definition four' : 2 + 2 == 1 + 3 :=
  eq_refl 4.

Definition singleton : forall (X:Type) (x:X), []++[x] == x::[]  :=
  fun (X:Type) (x:X) => eq_refl [x].

Definition eq_add : forall (n1 n2 : nat), n1 == n2 -> (S n1) == (S n2) :=
  fun n1 n2 Heq =>
    match Heq with
    | eq_refl n => eq_refl (S n)
    end.

Theorem eq_add' : forall (n1 n2 : nat), n1 == n2 -> (S n1) == (S n2).
Admitted.

Definition eq_cons : forall (X : Type) (h1 h2 : X) (t1 t2 : list X),
    h1 == h2 -> t1 == t2 -> h1 :: t1 == h2 :: t2
  .
Admitted.

Lemma equality__leibniz_equality : forall (X : Type) (x y: X),
  x == y -> forall (P : X -> Prop), P x -> P y.
Proof.
   Admitted.

Definition equality__leibniz_equality_term : forall (X : Type) (x y: X),
    x == y -> forall P : (X -> Prop), P x -> P y
  .
Admitted.

Lemma leibniz_equality__equality : forall (X : Type) (x y: X),
  (forall P:X->Prop, P x -> P y) -> x == y.
Proof.
 Admitted.

End EqualityPlayground.

Fail Definition or_bogus : forall P Q, P \/ Q -> P :=
  fun (P Q : Prop) (A : P \/ Q) =>
    match A with
    | or_introl H => H
    end.

Fail Fixpoint infinite_loop {X : Type} (n : nat) {struct n} : X :=
  infinite_loop n.

Fail Definition falso : False := infinite_loop 0.

Definition and_assoc : forall P Q R : Prop,
    P /\ (Q /\ R) -> (P /\ Q) /\ R
  .
Admitted.

Definition or_distributes_over_and : forall P Q R : Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R)
  .
Admitted.

Definition double_neg : forall P : Prop,
    P -> ~~P
  .
Admitted.

Definition contradiction_implies_anything : forall P Q : Prop,
    (P /\ ~P) -> Q
  .
Admitted.

Definition de_morgan_not_or : forall P Q : Prop,
    ~ (P \/ Q) -> ~P /\ ~Q
  .
Admitted.

Definition curry : forall P Q R : Prop,
    ((P /\ Q) -> R) -> (P -> (Q -> R))
  .
Admitted.

Definition uncurry : forall P Q R : Prop,
    (P -> (Q -> R)) -> ((P /\ Q) -> R)
  .
Admitted.

Definition propositional_extensionality : Prop :=
  forall (P Q : Prop), (P <-> Q) -> P = Q.

Theorem pe_implies_or_eq :
  propositional_extensionality ->
  forall (P Q : Prop), (P \/ Q) = (Q \/ P).
Proof.
   Admitted.

Lemma pe_implies_true_eq :
  propositional_extensionality ->
  forall (P : Prop), P -> True = P.
Proof.
 Admitted.

Definition proof_irrelevance : Prop :=
  forall (P : Prop) (pf1 pf2 : P), pf1 = pf2.

Theorem pe_implies_pi :
  propositional_extensionality -> proof_irrelevance.
Proof.
 Admitted.

End ProofObjects.

End LF.

End LF_DOT_ProofObjects.

Module Export LF_DOT_IndPrinciples.
Module Export LF.
Module Export IndPrinciples.

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Export LF.ProofObjects.

Check nat_ind :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, P n -> P (S n)) ->
    forall n : nat, P n.

Theorem mul_0_r' : forall n:nat,
  n * 0 = 0.
Admitted.

Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
Proof.
   Admitted.

Inductive time : Type :=
  | day
  | night.

Check time_ind :
  forall P : time -> Prop,
    P day ->
    P night ->
    forall t : time, P t.

Inductive rgb : Type :=
  | red
  | green
  | blue.
Check rgb_ind.

Inductive natlist : Type :=
  | nnil
  | ncons (n : nat) (l : natlist).

Check natlist_ind :
  forall P : natlist -> Prop,
    P nnil  ->
    (forall (n : nat) (l : natlist),
        P l -> P (ncons n l)) ->
    forall l : natlist, P l.

Inductive natlist' : Type :=
  | nnil'
  | nsnoc (l : natlist') (n : nat).

Check natlist'_ind :
  forall P : natlist' -> Prop,
    P nnil' ->
    (forall l : natlist', P l -> forall n : nat, P (nsnoc l n)) ->
    forall n : natlist', P n.

Inductive booltree : Type :=
  | bt_empty
  | bt_leaf (b : bool)
  | bt_branch (b : bool) (t1 t2 : booltree).

Definition booltree_property_type : Type := booltree -> Prop.

Definition base_case (P : booltree_property_type) : Prop
  .
Admitted.

Definition leaf_case (P : booltree_property_type) : Prop
  .
Admitted.

Definition branch_case (P : booltree_property_type) : Prop
  .
Admitted.

Definition booltree_ind_type :=
  forall (P : booltree_property_type),
    base_case P ->
    leaf_case P ->
    branch_case P ->
    forall (b : booltree), P b.

Theorem booltree_ind_type_correct : booltree_ind_type.
Proof.
 Admitted.

Inductive Toy : Type :=

.

Theorem Toy_correct : exists f g,
  forall P : Toy -> Prop,
    (forall b : bool, P (f b)) ->
    (forall (n : nat) (t : Toy), P t -> P (g n t)) ->
    forall t : Toy, P t.
Proof.
 Admitted.

Inductive tree (X:Type) : Type :=
  | leaf (x : X)
  | node (t1 t2 : tree X).
Check tree_ind.

Inductive foo' (X:Type) : Type :=
  | C1 (l : list X) (f : foo' X)
  | C2.

Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.

Definition P_m0r' : nat -> Prop :=
  fun n => n * 0 = 0.

Theorem mul_0_r'' : forall n:nat,
  P_m0r n.
Admitted.

Theorem add_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Admitted.

Theorem add_comm' : forall n m : nat,
  n + m = m + n.
Admitted.

Theorem add_comm'' : forall n m : nat,
  n + m = m + n.
Admitted.

Print ev.

Check ev_ind :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, ev n -> P n -> P (S (S n))) ->
    forall n : nat, ev n -> P n.

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

Theorem ev_ev' : forall n, ev n -> ev' n.
Admitted.

Inductive le1 : nat -> nat -> Prop :=
  | le1_n : forall n, le1 n n
  | le1_S : forall n m, (le1 n m) -> (le1 n (S m)).

Notation "m <=1 n" := (le1 m n) (at level 70).

Inductive le2 (n:nat) : nat -> Prop :=
  | le2_n : le2 n n
  | le2_S m (H : le2 n m) : le2 n (S m).

Notation "m <=2 n" := (le2 m n) (at level 70).

Check le1_ind :
  forall P : nat -> nat -> Prop,
    (forall n : nat, P n n) ->
    (forall n m : nat, n <=1 m -> P n m -> P n (S m)) ->
    forall n n0 : nat, n <=1 n0 -> P n n0.

Check le2_ind :
  forall (n : nat) (P : nat -> Prop),
    P n ->
    (forall m : nat, n <=2 m -> P m -> P (S m)) ->
    forall n0 : nat, n <=2 n0 -> P n0.

Check nat_ind :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, P n -> P (S n)) ->
    forall n : nat, P n.

Print nat_ind.

Fixpoint build_proof
         (P : nat -> Prop)
         (evPO : P 0)
         (evPS : forall n : nat, P n -> P (S n))
         (n : nat) : P n :=
  match n with
  | 0 => evPO
  | S k => evPS k (build_proof P evPO evPS k)
  end.

Definition nat_ind_tidy := build_proof.

Definition nat_ind2 :
  forall (P : nat -> Prop),
  P 0 ->
  P 1 ->
  (forall n : nat, P n -> P (S(S n))) ->
  forall n : nat , P n :=
    fun P => fun P0 => fun P1 => fun PSS =>
      fix f (n:nat) := match n with
                         0 => P0
                       | 1 => P1
                       | S (S n') => PSS n' (f n')
                       end.

Lemma even_ev : forall n, even n = true -> ev n.
Admitted.

Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

Inductive t_tree (X : Type) : Type :=
| t_leaf
| t_branch : (t_tree X * X * t_tree X) -> t_tree X.

Arguments t_leaf {X}.
Arguments t_branch {X}.

Check t_tree_ind.

Fixpoint reflect {X : Type} (t : t_tree X) : t_tree X :=
  match t with
  | t_leaf => t_leaf
  | t_branch (l, v, r) => t_branch (reflect r, v, reflect l)
  end.

Definition better_t_tree_ind_type : Prop
  .
Admitted.

Definition better_t_tree_ind : better_t_tree_ind_type
  .
Admitted.

Theorem reflect_involution : forall (X : Type) (t : t_tree X),
    reflect (reflect t) = t.
Proof.
 Admitted.

End IndPrinciples.

End LF.

End LF_DOT_IndPrinciples.

Module Export LF_DOT_IndPrinciplesTest.
Set Warnings "-notation-overridden,-parsing".
Export Stdlib.Strings.String.
Import LF.IndPrinciples.

Parameter MISSING: Type.

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
Import LF.IndPrinciples.
Import Check.
Print Assumptions plus_one_r'.
Print Assumptions booltree_ind_type_correct.
Print Assumptions Toy_correct.

End LF_DOT_IndPrinciplesTest.

Module Export LF_DOT_IndPropTest.
Set Warnings "-notation-overridden,-parsing".
Export Stdlib.Strings.String.
Import LF.IndProp.

Parameter MISSING: Type.

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
Import LF.IndProp.
Import Check.
Print Assumptions ev_double.
Print Assumptions Perm3_ex1.
Print Assumptions Perm3_refl.
Print Assumptions le_inversion.
Print Assumptions SSSSev__even.
Print Assumptions ev5_nonsense.
Print Assumptions ev_sum.
Print Assumptions ev_ev__ev.
Print Assumptions Perm3_In.
Print Assumptions le_trans.
Print Assumptions O_le_n.
Print Assumptions n_le_m__Sn_le_Sm.
Print Assumptions Sn_le_Sm__n_le_m.
Print Assumptions le_plus_l.
Print Assumptions plus_le.
Print Assumptions plus_le_cases.
Print Assumptions plus_le_compat_l.
Print Assumptions plus_le_compat_r.
Print Assumptions le_plus_trans.
Print Assumptions subseq_refl.
Print Assumptions subseq_app.
Print Assumptions subseq_trans.
Print Assumptions EmptySet_is_empty.
Print Assumptions MUnion'.
Print Assumptions MStar'.
Print Assumptions re_not_empty.
Print Assumptions re_not_empty_correct.
Print Assumptions Pumping.weak_pumping.
Print Assumptions reflect_iff.
Print Assumptions eqbP_practice.
Print Assumptions merge_filter.

End LF_DOT_IndPropTest.

Module Export LF_DOT_InductionTest.
Set Warnings "-notation-overridden,-parsing".
Export Stdlib.Strings.String.
Import LF.Induction.

Parameter MISSING: Type.

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
Import LF.Induction.
Import Check.
Print Assumptions mul_0_r.
Print Assumptions plus_n_Sm.
Print Assumptions add_comm.
Print Assumptions add_assoc.
Print Assumptions double_plus.
Print Assumptions eqb_refl.
Print Assumptions add_shuffle3.
Print Assumptions mul_comm.
Print Assumptions bin_to_nat_pres_incr.
Print Assumptions nat_bin_nat.
Print Assumptions double_incr.
Print Assumptions double_bin_zero.
Print Assumptions double_incr_bin.
Print Assumptions bin_nat_bin.

End LF_DOT_InductionTest.

Module Export LF_DOT_ListsTest.
Set Warnings "-notation-overridden,-parsing".
Export Stdlib.Strings.String.
Import LF.Lists.

Parameter MISSING: Type.

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
Import LF.Lists.
Import Check.
Print Assumptions NatList.snd_fst_is_swap.
Print Assumptions NatList.test_nonzeros.
Print Assumptions NatList.test_oddmembers.
Print Assumptions NatList.test_countoddmembers2.
Print Assumptions NatList.test_countoddmembers3.
Print Assumptions NatList.test_alternate1.
Print Assumptions NatList.test_alternate2.
Print Assumptions NatList.test_alternate4.
Print Assumptions NatList.test_count2.
Print Assumptions NatList.test_sum1.
Print Assumptions NatList.test_add1.
Print Assumptions NatList.test_add2.
Print Assumptions NatList.test_member1.
Print Assumptions NatList.test_member2.
Print Assumptions NatList.app_nil_r.
Print Assumptions NatList.rev_app_distr.
Print Assumptions NatList.rev_involutive.
Print Assumptions NatList.app_assoc4.
Print Assumptions NatList.nonzeros_app.
Print Assumptions NatList.eqblist_refl.
Print Assumptions NatList.count_member_nonzero.
Print Assumptions NatList.remove_does_not_increase_count.
Print Assumptions NatList.involution_injective.
Print Assumptions NatList.rev_injective.
Print Assumptions NatList.test_hd_error1.
Print Assumptions NatList.test_hd_error2.
Print Assumptions eqb_id_refl.
Print Assumptions PartialMap.update_eq.
Print Assumptions PartialMap.update_neq.

End LF_DOT_ListsTest.

Module Export LF_DOT_LogicTest.
Set Warnings "-notation-overridden,-parsing".
Export Stdlib.Strings.String.
Import LF.Logic.

Parameter MISSING: Type.

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
Import LF.Logic.
Import Check.
Print Assumptions plus_is_O.
Print Assumptions and_assoc.
Print Assumptions mult_is_O.
Print Assumptions or_commut.
Print Assumptions contrapositive.
Print Assumptions not_both_true_and_false.
Print Assumptions de_morgan_not_or.
Print Assumptions or_distributes_over_and.
Print Assumptions dist_not_exists.
Print Assumptions dist_exists_or.
Print Assumptions In_map_iff.
Print Assumptions In_app_iff.
Print Assumptions All_In.
Print Assumptions even_double_conv.
Print Assumptions andb_true_iff.
Print Assumptions orb_true_iff.
Print Assumptions eqb_neq.
Print Assumptions eqb_list_true_iff.
Print Assumptions forallb_true_iff.
Print Assumptions tr_rev_correct.
Print Assumptions excluded_middle_irrefutable.
Print Assumptions not_exists_dist.

End LF_DOT_LogicTest.

Module Export LF_DOT_MapsTest.
Set Warnings "-notation-overridden,-parsing".
Export Stdlib.Strings.String.
Import LF.Maps.

Parameter MISSING: Type.

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
Import LF.Maps.
Import Check.
Print Assumptions t_update_same.
Print Assumptions t_update_permute.

End LF_DOT_MapsTest.

Module Export LF_DOT_PolyTest.
Set Warnings "-notation-overridden,-parsing".
Export Stdlib.Strings.String.
Import LF.Poly.

Parameter MISSING: Type.

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
Import LF.Poly.
Import Check.
Print Assumptions app_nil_r.
Print Assumptions app_assoc.
Print Assumptions app_length.
Print Assumptions rev_app_distr.
Print Assumptions rev_involutive.
Print Assumptions split.
Print Assumptions test_split.
Print Assumptions test_filter_even_gt7_1.
Print Assumptions test_filter_even_gt7_2.
Print Assumptions partition.
Print Assumptions test_partition1.
Print Assumptions test_partition2.
Print Assumptions map_rev.
Print Assumptions flat_map.
Print Assumptions test_flat_map1.
Print Assumptions Exercises.fold_length_correct.
Print Assumptions Exercises.uncurry_curry.
Print Assumptions Exercises.curry_uncurry.
Print Assumptions Exercises.Church.scc_2.
Print Assumptions Exercises.Church.scc_3.
Print Assumptions Exercises.Church.plus_1.
Print Assumptions Exercises.Church.plus_2.
Print Assumptions Exercises.Church.plus_3.
Print Assumptions Exercises.Church.mult_1.
Print Assumptions Exercises.Church.mult_2.
Print Assumptions Exercises.Church.mult_3.
Print Assumptions Exercises.Church.exp_1.
Print Assumptions Exercises.Church.exp_2.
Print Assumptions Exercises.Church.exp_3.

End LF_DOT_PolyTest.

Module Export LF_DOT_Postscript.
Module Export LF.
Module Export Postscript.

End Postscript.

End LF.

End LF_DOT_Postscript.

Module Export LF_DOT_PostscriptTest.
Set Warnings "-notation-overridden,-parsing".
Export Stdlib.Strings.String.
Import LF.Postscript.

Parameter MISSING: Type.

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
Import LF.Postscript.
Import Check.

End LF_DOT_PostscriptTest.

Module Export LF_DOT_Preface.
Module Export LF.
Module Export Preface.

End Preface.

End LF.

End LF_DOT_Preface.

Module Export LF_DOT_PrefaceTest.
Set Warnings "-notation-overridden,-parsing".
Export Stdlib.Strings.String.
Import LF.Preface.

Parameter MISSING: Type.

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
Import LF.Preface.
Import Check.

End LF_DOT_PrefaceTest.

Module Export LF_DOT_ProofObjectsTest.
Set Warnings "-notation-overridden,-parsing".
Export Stdlib.Strings.String.
Import LF.ProofObjects.

Parameter MISSING: Type.

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
Import LF.ProofObjects.
Import Check.
Print Assumptions ev_8.
Print Assumptions ev_8'.
Print Assumptions Props.conj_fact.
Print Assumptions Props.or_commut'.
Print Assumptions Props.ex_ev_Sn.
Print Assumptions Props.ex_match.
Print Assumptions Props.p_implies_true.
Print Assumptions Props.ex_falso_quodlibet'.
Print Assumptions EqualityPlayground.eq_cons.
Print Assumptions EqualityPlayground.equality__leibniz_equality.
Print Assumptions EqualityPlayground.equality__leibniz_equality_term.
Print Assumptions and_assoc.
Print Assumptions or_distributes_over_and.
Print Assumptions double_neg.
Print Assumptions contradiction_implies_anything.
Print Assumptions de_morgan_not_or.
Print Assumptions curry.
Print Assumptions uncurry.
Print Assumptions pe_implies_or_eq.
Print Assumptions pe_implies_true_eq.
Print Assumptions pe_implies_pi.

End LF_DOT_ProofObjectsTest.
Module Export LF.
Module Export Rel.

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Export LF.IndProp.

Definition relation (X: Type) := X -> X -> Prop.

Print le.

Check le : nat -> nat -> Prop.
Check le : relation nat.

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

Check next_nat : relation nat.

Theorem next_nat_partial_function :
  partial_function next_nat.
Admitted.

Theorem le_not_a_partial_function :
  ~ (partial_function le).
Admitted.

Inductive total_relation : nat -> nat -> Prop :=

.

Theorem total_relation_not_partial_function :
  ~ (partial_function total_relation).
Proof.
   Admitted.

Inductive empty_relation : nat -> nat -> Prop :=

.

Theorem empty_relation_partial_function :
  partial_function empty_relation.
Proof.
   Admitted.

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Admitted.

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Admitted.

Theorem lt_trans:
  transitive lt.
Admitted.

Theorem lt_trans' :
  transitive lt.
Proof.

  unfold lt.
unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
     Admitted.

Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt.
unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
   Admitted.

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Admitted.

Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
   Admitted.

Theorem le_Sn_n : forall n,
  ~ (S n <= n).
Proof.
   Admitted.

Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
   Admitted.

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

Theorem le_antisymmetric :
  antisymmetric le.
Proof.
   Admitted.

Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof.
   Admitted.

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order :
  order le.
Admitted.

Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
  | rt_step x y (H : R x y) : clos_refl_trans R x y
  | rt_refl x : clos_refl_trans R x x
  | rt_trans x y z
        (Hxy : clos_refl_trans R x y)
        (Hyz : clos_refl_trans R y z) :
        clos_refl_trans R x z.

Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Admitted.

Inductive clos_refl_trans_1n {A : Type}
                             (R : relation A) (x : A)
                             : A -> Prop :=
  | rt1n_refl : clos_refl_trans_1n R x x
  | rt1n_trans (y z : A)
      (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) :
      clos_refl_trans_1n R x z.

Lemma rsc_R : forall (X:Type) (R:relation X) (x y : X),
  R x y -> clos_refl_trans_1n R x y.
Admitted.

Lemma rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      clos_refl_trans_1n R x y  ->
      clos_refl_trans_1n R y z ->
      clos_refl_trans_1n R x z.
Proof.
   Admitted.

Theorem rtc_rsc_coincide :
  forall (X:Type) (R: relation X) (x y : X),
    clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
Proof.
   Admitted.

End Rel.

End LF.

Module Export LF_DOT_RelTest.
Set Warnings "-notation-overridden,-parsing".
Export Stdlib.Strings.String.
Import LF.Rel.

Parameter MISSING: Type.

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
Import LF.Rel.
Import Check.

End LF_DOT_RelTest.
Set Warnings "-notation-overridden,-parsing".
Export Stdlib.Strings.String.
Import LF.Tactics.

Parameter MISSING: Type.

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
Import LF.Tactics.
Import Check.
Print Assumptions rev_exercise1.
Print Assumptions injection_ex3.
Print Assumptions discriminate_ex3.
Print Assumptions eqb_true.
Print Assumptions plus_n_n_injective.
Print Assumptions nth_error_after_last.
Print Assumptions combine_split.
Print Assumptions bool_fn_applied_thrice.
Print Assumptions eqb_sym.
Print Assumptions filter_exercise.
Print Assumptions existsb_existsb'.
