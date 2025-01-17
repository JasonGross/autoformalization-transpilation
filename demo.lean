
inductive Binop where
  | plus
  | times
deriving Repr, DecidableEq

inductive Exp where
  | const : Nat → Exp
  | binop : Binop → Exp → Exp → Exp
deriving Repr, DecidableEq

def binopDenote : Binop → Nat → Nat → Nat
  | Binop.plus, x, y  => x + y
  | Binop.times, x, y => x * y

def expDenote : Exp → Nat
  | Exp.const n      => n
  | Exp.binop b e1 e2 => binopDenote b (expDenote e1) (expDenote e2)


inductive Instr where
  | iConst : Nat → Instr
  | iBinop : Binop → Instr
deriving Repr, DecidableEq

def Prog := List Instr
def Stack := List Nat

def instrDenote (i : Instr) (s : Stack) : Option Stack :=
  match i with
  | Instr.iConst n => some (n :: s)
  | Instr.iBinop b =>
    match s with
    | arg1 :: arg2 :: s' => some ((binopDenote b) arg1 arg2 :: s')
    | _                  => none

def progDenote : Prog → Stack → Option Stack
  | [],      s => some s
  | i :: p', s =>
    match instrDenote i s with
    | none    => none
    | some s' => progDenote p' s'


-- Explicitly open the List namespace to resolve `++` operation ambiguity
open List

-- Define HAppend instance for Prog
instance : HAppend Prog Prog Prog where
  hAppend := List.append
instance : HAppend Prog (List Instr) Prog where
  hAppend := List.append

-- Translation of the `compile` function
def compile : Exp → Prog
  | Exp.const n      => [Instr.iConst n]
  | Exp.binop b e1 e2 => compile e2 ++ compile e1 ++ [Instr.iBinop b]

-- Translation of the correctness property: compile_one_instr_statement
def compileOneInstrStatement (e : Exp) (p : Prog) (s : Stack) : Prop :=
  progDenote (compile e ++ p) s = progDenote p (expDenote e :: s)

-- Translation of the correctness property: compile_correct
def compileCorrect (e : Exp) : Prop :=
  progDenote (compile e) [] = some [expDenote e]

-- Translation of additional properties
def binOpComm (b : Binop) (e1 e2 : Exp) : Prop :=
  expDenote (Exp.binop b e1 e2) = expDenote (Exp.binop b e2 e1)

def reverseMerge (e1 e2 : Exp) (b : Binop) : Prop :=
  compile e2 ++ compile e1 ++ [Instr.iBinop b] = compile (Exp.binop b e1 e2)

def compileOpComm (b : Binop) (e1 e2 : Exp) : Prop :=
  progDenote (compile e2 ++ compile e1 ++ [Instr.iBinop b]) [] =
  progDenote (compile e1 ++ compile e2 ++ [Instr.iBinop b]) []

-- Translation of miscellaneous definitions and proofs
def constEq (n n' : Nat) : Prop :=
  Exp.const n = Exp.const n' → n = n'

def constInsEq (n n' : Nat) : Prop :=
  Instr.iConst n = Instr.iConst n' → n = n'

def constOnlyConst (e : Exp) (n : Nat) : Prop :=
  Exp.const n = e → e = Exp.const n

def listEq {A : Type} (a1 a2 : A) : Prop :=
  [a1] = [a2] → a1 = a2

def constCmpl (n : Nat) (b : Binop) (e1 e2 : Exp) : Prop :=
  compile e2 ++ compile e1 ++ [Instr.iBinop b] ≠ [Instr.iConst n]
