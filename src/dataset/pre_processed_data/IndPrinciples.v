Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".

From LF Require Export ProofObjects.

Check nat_ind :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, P n -> P (S n)) ->
    forall n : nat, P n.

Theorem mul_0_r' : forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  -  reflexivity.
  -  simpl. intros n' IHn'. rewrite -> IHn'.
    reflexivity.  Qed.





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
  . Admitted.

Definition leaf_case (P : booltree_property_type) : Prop
  . Admitted.

Definition branch_case (P : booltree_property_type) : Prop
  . Admitted.

Definition booltree_ind_type :=
  forall (P : booltree_property_type),
    base_case P ->
    leaf_case P ->
    branch_case P ->
    forall (b : booltree), P b.

Theorem booltree_ind_type_correct : booltree_ind_type.
Proof.  Admitted.

Inductive Toy : Type :=

.

Theorem Toy_correct : exists f g,
  forall P : Toy -> Prop,
    (forall b : bool, P (f b)) ->
    (forall (n : nat) (t : Toy), P t -> P (g n t)) ->
    forall t : Toy, P t.
Proof.  Admitted.

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
Proof.
  apply nat_ind.
  -  reflexivity.
  -

    intros n IHn.
    unfold P_m0r in IHn. unfold P_m0r. simpl. apply IHn. Qed.










Theorem add_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.

  intros n m p.

  induction n as [| n'].
  -  reflexivity.
  -
    simpl. rewrite -> IHn'. reflexivity.  Qed.



Theorem add_comm' : forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [| n'].
  -  intros m. rewrite -> add_0_r. reflexivity.
  -  intros m. simpl. rewrite -> IHn'.
    rewrite <- plus_n_Sm. reflexivity.  Qed.



Theorem add_comm'' : forall n m : nat,
  n + m = m + n.
Proof.

  induction m as [| m'].
  -  simpl. rewrite -> add_0_r. reflexivity.
  -  simpl. rewrite <- IHm'.
    rewrite <- plus_n_Sm. reflexivity.  Qed.










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
Proof.
  apply ev_ind.
  -
    apply ev'_0.
  -
    intros m Hm IH.
    apply (ev'_sum 2 m).
    + apply ev'_2.
    + apply IH.
Qed.

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

Lemma even_ev : forall n: nat, even n = true -> ev n.
Proof.
  induction n; intros.
  - apply ev_0.
  - destruct n.
    + simpl in H. inversion H.
    + simpl in H.
      apply ev_SS.
Abort.

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
Proof.
  intros.
  induction n as [ | |n'] using nat_ind2.
  - apply ev_0.
  - simpl in H.
    inversion H.
  - simpl in H.
    apply ev_SS.
    apply IHn'.
    apply H.
Qed.

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

Theorem reflect_involution : forall (X : Type) (t : t_tree X),
    reflect (reflect t) = t.
Proof.
  intros X t. induction t.
  - reflexivity.
  - destruct p as [[l v] r]. simpl. Abort.



Definition better_t_tree_ind_type : Prop
  . Admitted.



Definition better_t_tree_ind : better_t_tree_ind_type
  . Admitted.



Theorem reflect_involution : forall (X : Type) (t : t_tree X),
    reflect (reflect t) = t.
Proof.  Admitted.
