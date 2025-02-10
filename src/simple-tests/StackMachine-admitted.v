From Coq Require Import Bool Arith List.
(* Set Implicit Arguments.
Set Asymmetric Patterns. *)

(*Define the source language first*)
Inductive binop : Set := Plus | Times.

Inductive exp : Set :=
 Const : nat -> exp
| Binop : binop -> exp -> exp -> exp. (* Binop is a function which takes exp and exp and gives exp. This is just currying*)

Definition binopDenote (b : binop) : nat -> nat -> nat :=
match b with
    | Plus => plus
    | Times => mult
end.

Fixpoint expDenote (e: exp) : nat :=
    match e with
    | Const n => n
    | Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
    end.

(*Define the target language*)

Inductive instr: Set :=
| iConst : nat -> instr
| iBinop : binop -> instr. (*Instructions can be either constants or binary operation*)

Definition prog := list instr. (*Program is a list of instructions*)
Definition stack := list nat. (*Instruction either pushes a constant to the stack or applies binop on two elements on the stack*)

Definition instrDenote (i : instr) (s: stack): option stack :=
match i with
 | iConst n => Some (n :: s)
 | iBinop b =>
    match s with
     | arg1 :: arg2 :: s' => Some ((binopDenote b) arg1 arg2 :: s')
     | _ => None
    end
end.

Fixpoint progDenote (p : prog) (s: stack) : option stack :=
match p with
 | nil => Some s
 | i::p' =>
   match instrDenote i s with
    | None => None
    | Some s' => progDenote p' s'
   end
end. (*Run instructions one by one*)

(*Translation for the language i.e. Compiler*)
Fixpoint compile (e : exp): prog :=
    match e with
       | Const n => iConst n::nil
       | Binop b e1 e2 => compile e2 ++ compile e1 ++ iBinop b :: nil
    end.

(*Check the correctness of the compiler itself*)
Definition compile_one_instr_statement:= forall e p s, progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).
Lemma compile_one_instr: forall e p s, progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).
Admitted.

Definition compile_correct_statement:= forall e, progDenote (compile e) nil = Some (expDenote e::nil).
Theorem compile_correct: forall e, progDenote (compile e) nil = Some (expDenote e::nil).
Admitted.

Definition bin_op_comm_statement:= forall b e1 e2, expDenote (Binop b e1 e2) = expDenote (Binop b e2 e1).
Lemma bin_op_comm: forall b e1 e2, expDenote (Binop b e1 e2) = expDenote (Binop b e2 e1).
Proof.
Admitted.

Definition reverse_merge_statement:= forall e1 e2 b, compile e2 ++ compile e1 ++ iBinop b::nil = compile (Binop b e1 e2).
Lemma reverse_merge: forall e1 e2 b, compile e2 ++ compile e1 ++ iBinop b::nil = compile (Binop b e1 e2).
Proof.
Admitted.

Definition compile_op_comm_statement:= forall b e1 e2, progDenote (compile e2 ++ compile e1 ++ iBinop b::nil) nil = progDenote (compile e1 ++ compile e2 ++ iBinop b::nil) nil.
Theorem compile_op_comm: forall b e1 e2, progDenote (compile e2 ++ compile e1 ++ iBinop b::nil) nil = progDenote (compile e1 ++ compile e2 ++ iBinop b::nil) nil.
Proof.
Admitted.

Definition const_eq_statement:= forall n n', Const n = Const n' -> n = n'.
Theorem const_eq: forall n n', Const n = Const n' -> n = n'.
Proof.
Admitted.

Definition const_ins_eq_statement:= forall n n', iConst n = iConst n' -> n = n'.
Theorem const_ins_eq: forall n n', iConst n = iConst n' -> n = n'.
Proof.
Admitted.

Definition const_only_const_statement:= forall e n, Const n = e -> e = Const n.
Theorem const_only_const: forall e n, Const n = e -> e = Const n.
Proof.
Admitted.

Definition list_eq_statement:= forall a1 a2 : Type, a1::nil = a2::nil -> a1 = a2.
Theorem list_eq: forall  a1 a2 : Type, a1::nil = a2::nil -> a1 = a2.
Proof.
Admitted.

Definition const_cmpl_statement:= forall n b e1 e2, compile e2 ++ compile e1 ++ iBinop b :: nil <> iConst n :: nil.
Lemma const_cmpl: forall n b e1 e2, compile e2 ++ compile e1 ++ iBinop b :: nil <> iConst n :: nil.
Proof.
Admitted.