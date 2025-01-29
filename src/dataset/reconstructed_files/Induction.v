From LF Require Export Basics.

Theorem add_0_r_firsttry : forall n:nat,
  n + 0 = n.

Proof.
  intros n.
  simpl.
Abort.

Theorem add_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  -
    reflexivity.
  -
    simpl.
Abort.

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  -     reflexivity.
  -  simpl. rewrite -> IHn'. reflexivity.  Qed.

Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.

intros n. induction n as [| n' IHn'].
  -
    simpl. reflexivity.
  -
    simpl. rewrite -> IHn'. reflexivity.  Qed.

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
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    { rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
  rewrite -> H.
  reflexivity.  Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.

rewrite add_comm.

Abort.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity.  Qed.

Theorem add_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
  simpl. rewrite IHn'. reflexivity.  Qed.

Theorem add_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  -
    reflexivity.
  -
    simpl. rewrite IHn'. reflexivity.   Qed.

*)

Definition manual_grade_for_add_comm_informal : option (nat*string) := None.

*)

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
  . Admitted.

Fixpoint bin_to_nat (m:bin) : nat
  . Admitted.

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
   Admitted.

Fixpoint nat_to_bin (n:nat) : bin
  . Admitted.

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
   Admitted.

Theorem bin_nat_bin_fails : forall b, nat_to_bin (bin_to_nat b) = b.
Abort.

Lemma double_incr : forall n : nat, double (S n) = S (S (double n)).
Proof.
   Admitted.

Definition double_bin (b:bin) : bin
  . Admitted.

Example double_bin_zero : double_bin Z = Z.
 Admitted.

Lemma double_incr_bin : forall b,
    double_bin (incr b) = incr (incr (double_bin b)).
Proof.
   Admitted.

Theorem bin_nat_bin_fails : forall b, nat_to_bin (bin_to_nat b) = b.
Abort.

Fixpoint normalize (b:bin) : bin
  . Admitted.

Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
   Admitted.

