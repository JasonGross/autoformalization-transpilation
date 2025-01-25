Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".

From Coq Require Import Bool.

From Coq Require Import Init.Nat.

From Coq Require Import Arith.

From Coq Require Import EqNat. Import Nat.

From Coq Require Import Lia.

From Coq Require Import List. Import ListNotations.

From Coq Require Import Strings.String.

From LF Require Import Maps.

Set Default Goal Selector "!".

Module AExp.

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
Proof. reflexivity. Qed.

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
Proof. reflexivity. Qed.

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  -  reflexivity.
  -  destruct a1 eqn:Ea1.
    +  destruct n eqn:En.
      *   simpl. apply IHa2.
      *  simpl. rewrite IHa2. reflexivity.
    +
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    +
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    +
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  -
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  -
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.  Qed.















Theorem silly1 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity.
  apply HP.
Qed.

Theorem silly2 : forall ae, aeval ae = aeval ae.
Proof.
    try reflexivity.
Qed.

Lemma foo : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n.

    -  simpl. reflexivity.
    -  simpl. reflexivity.
Qed.

Lemma foo' : forall n, 0 <=? n = true.
Proof.
  intros.

  destruct n;

  simpl;

  reflexivity.
Qed.

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;

    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).

  -  reflexivity.
  -
    destruct a1 eqn:Ea1;

      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).

    +  destruct n eqn:En;
      simpl; rewrite IHa2; reflexivity.   Qed.





Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;

    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);

    try reflexivity.

  -
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    +  destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.











Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat simpl.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.

Theorem repeat_loop : forall (m n : nat),
  m + n = n + m.
Proof.
  intros m n.


Admitted.

Fixpoint optimize_0plus_b (b : bexp) : bexp
  . Admitted.

Example optimize_0plus_b_test1:
  optimize_0plus_b (BNot (BGt (APlus (ANum 0) (ANum 4)) (ANum 8))) =
                   (BNot (BGt (ANum 4) (ANum 8))).
Proof.  Admitted.

Example optimize_0plus_b_test2:
  optimize_0plus_b (BAnd (BLe (APlus (ANum 0) (ANum 4)) (ANum 5)) BTrue) =
                   (BAnd (BLe (ANum 4) (ANum 5)) BTrue).
Proof.  Admitted.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
   Admitted.

Ltac invert H :=
  inversion H; subst; clear H.

Lemma invert_example1: forall {a b c: nat}, [a ;b] = [a;c] -> b = c.
  intros.
  invert H.
  reflexivity.
Qed.

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. lia.
Qed.

Example add_comm__lia : forall m n,
    m + n = n + m.
Proof.
  intros. lia.
Qed.

Example add_assoc__lia : forall m n p,
    m + (n + p) = m + n + p.
Proof.
  intros. lia.
Qed.

Module aevalR_first_try.

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

Module HypothesisNames.

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
Proof.
  split.
  -
    intros H.
    induction H; simpl.
    +
      reflexivity.
    +
      rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
    +
      rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
    +
      rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
  -
    generalize dependent n.
    induction a;
       simpl; intros; subst.
    +
      apply E_ANum.
    +
      apply E_APlus.
      * apply IHa1. reflexivity.
      * apply IHa2. reflexivity.
    +
      apply E_AMinus.
      * apply IHa1. reflexivity.
      * apply IHa2. reflexivity.
    +
      apply E_AMult.
      * apply IHa1. reflexivity.
      * apply IHa2. reflexivity.
Qed.

Theorem aevalR_iff_aeval' : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.

  split.
  -
    intros H; induction H; subst; reflexivity.
  -
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.

Reserved Notation "e '==>b' b" (at level 90, left associativity).

Inductive bevalR: bexp -> bool -> Prop :=

where "e '==>b' b" := (bevalR e b) : type_scope
.

Lemma bevalR_iff_beval : forall b bv,
  b ==>b bv <-> beval b = bv.
Proof.
   Admitted.

End AExp.

Module aevalR_division.

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

Module aevalR_extended.



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
Proof. reflexivity. Qed.

Example aexp2 :
    aeval (X !-> 5 ; Y !-> 4) <{ Z + (X * Y) }>
  = 20.
Proof. reflexivity. Qed.

Example bexp1 :
    beval (X !-> 5) <{ true && ~(X <= 4) }>
  = true.
Proof. reflexivity. Qed.

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
Proof.

  apply E_Seq with (X !-> 2).
  -
    apply E_Asgn. reflexivity.
  -
    apply E_IfFalse.
    + reflexivity.
    + apply E_Asgn. reflexivity.
Qed.

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
  . Admitted.

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
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2; inversion E2; subst.
  -  reflexivity.
  -  reflexivity.
  -
    rewrite (IHE1_1 st'0 H1) in *.
    apply IHE1_2. assumption.
  -
      apply IHE1. assumption.
  -
      rewrite H in H5. discriminate.
  -
      rewrite H in H5. discriminate.
  -
      apply IHE1. assumption.
  -
    reflexivity.
  -
    rewrite H in H2. discriminate.
  -
    rewrite H in H4. discriminate.
  -
    rewrite (IHE1_1 st'0 H3) in *.
    apply IHE1_2. assumption.  Qed.






Theorem plus2_spec : forall st n st',
  st X = n ->
  st =[ plus2 ]=> st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.



  inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq.  Qed.






Definition manual_grade_for_XtimesYinZ_spec : option (nat*string) := None.



Theorem loop_never_stops : forall st st',
  ~(st =[ loop ]=> st').
Proof.
  intros st st' contra. unfold loop in contra.
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
  . Admitted.

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
  . Admitted.

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
