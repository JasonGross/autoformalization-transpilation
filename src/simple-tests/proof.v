(* First prove the helper lemma plus_0_r *)
Theorem plus_0_r : forall n : nat, n + 0 = n.
Proof.
    intros n.
    induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite IHn'. reflexivity.
Qed.

(* Now we can prove plus_comm *)
Theorem plus_comm : forall a b : nat, a + b = b + a.
Proof.
    intros a b.
    induction a as [| a' IHa'].
    - simpl. rewrite plus_0_r. reflexivity.
    - simpl. rewrite IHa'. rewrite plus_n_Sm. reflexivity.
Qed.