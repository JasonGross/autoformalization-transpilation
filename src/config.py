BUILD_DIR = "/root/build"
SOURCE_DIR = "/root/autoformalization"
EXPORT_DIR = "/root/lean4export"
ISO_RETRIES = 30  # TODO: change back to 3 when we make this per-iso
ISO_HEADER = """From IsomorphismChecker Require Import Automation EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)
"""
ISO_INTERFACE_HEADER = """From IsomorphismChecker Require Import Automation EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
Import KnownConstantHints RelIsoInterfaceHints.
From IsomorphismChecker Require Original.
Module Type Interface.
"""
ISO_CHECKER_HEADER = """From Stdlib Require Import Derive.
From IsomorphismChecker Require Import Automation EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
Import KnownConstantHints RelIsoInterfaceHints.
From IsomorphismChecker Require Original Interface Isomorphisms.
Module CheckAssumptions.
Import Ltac2.Ltac2 Ltac2.Printf.
Ltac2 Eval printf "Begin Print Assumptions Isomorphisms.everything.".
Print Assumptions Isomorphisms.everything.
Ltac2 Eval printf "End Print Assumptions Isomorphisms.everything.".
End CheckAssumptions.
#[local] Unset Universe Checking.
#[local] Unset Universe Polymorphism.
Module DoesItCheck <: Interface.Interface.
"""
EXAMPLE_STATEMENTS = [
    """inductive Binop where
| plus
| times
deriving Repr, DecidableEq""",
    """inductive Exp where
| const : Nat → Exp
| binop : Binop → Exp → Exp → Exp
deriving Repr, DecidableEq""",
    """def binopDenote : Binop → Nat → Nat → Nat
| Binop.plus, x, y  => x + y
| Binop.times, x, y => x * y""",
    """def expDenote : Exp → Nat
| Exp.const n      => n
| Exp.binop b e1 e2 => binopDenote b (expDenote e1) (expDenote e2)""",
    """inductive Instr where
| iConst : Nat → Instr
| iBinop : Binop → Instr
deriving Repr, DecidableEq""",
    """def Prog := List Instr""",
    """def Stack := List Nat""",
    """def instrDenote (i : Instr) (s : Stack) : Option Stack :=
match i with
| Instr.iConst n => some (n :: s)
| Instr.iBinop b =>
    match s with
    | arg1 :: arg2 :: s' => some ((binopDenote b) arg1 arg2 :: s')
    | _                  => none""",
    """def progDenote : Prog → Stack → Option Stack
| [],      s => some s
| i :: p', s =>
    match instrDenote i s with
    | none    => none
    | some s' => progDenote p' s'""",
    """-- Explicitly open the List namespace to resolve `++` operation ambiguity
open List
-- Define HAppend instance for Prog
instance : HAppend Prog Prog Prog where
hAppend := List.append
instance : HAppend Prog (List Instr) Prog where
hAppend := List.append""",
    """-- Translation of the `compile` function
def compile : Exp → Prog
| Exp.const n      => [Instr.iConst n]
| Exp.binop b e1 e2 => compile e2 ++ compile e1 ++ [Instr.iBinop b]""",
    """-- Translation of the correctness property: compile_one_instr_statement
def compileOneInstrStatement (e : Exp) (p : Prog) (s : Stack) : Prop :=
progDenote (compile e ++ p) s = progDenote p (expDenote e :: s)""",
    """-- Translation of the correctness property: compile_correct
def compileCorrect (e : Exp) : Prop :=
progDenote (compile e) [] = some [expDenote e]""",
    """-- Translation of additional properties
def binOpComm (b : Binop) (e1 e2 : Exp) : Prop :=
expDenote (Exp.binop b e1 e2) = expDenote (Exp.binop b e2 e1)""",
    """def reverseMerge (e1 e2 : Exp) (b : Binop) : Prop :=
compile e2 ++ compile e1 ++ [Instr.iBinop b] = compile (Exp.binop b e1 e2)""",
    """def compileOpComm (b : Binop) (e1 e2 : Exp) : Prop :=
progDenote (compile e2 ++ compile e1 ++ [Instr.iBinop b]) [] =
progDenote (compile e1 ++ compile e2 ++ [Instr.iBinop b]) []""",
    """-- Translation of miscellaneous definitions and proofs
def constEq (n n' : Nat) : Prop :=
Exp.const n = Exp.const n' → n = n'""",
    """def constInsEq (n n' : Nat) : Prop :=
Instr.iConst n = Instr.iConst n' → n = n'""",
    """def constOnlyConst (e : Exp) (n : Nat) : Prop :=
Exp.const n = e → e = Exp.const n""",
    """def listEq {A : Type} (a1 a2 : A) : Prop :=
[a1] = [a2] → a1 = a2""",
    """def constCmpl (n : Nat) (b : Binop) (e1 e2 : Exp) : Prop :=
compile e2 ++ compile e1 ++ [Instr.iBinop b] ≠ [Instr.iConst n]""",
]
from project_util import CoqIdentifier, LeanIdentifier

DEFINITION_PAIRS = list(
    map(
        lambda x: (CoqIdentifier(x[0]), LeanIdentifier(x[1])),
        [  # TODO: Resolve https://github.com/JasonGross/autoformalization/pull/47#issuecomment-2655085138
            ("$binop", "$Binop"),
            ("$exp", "$Exp"),
            ("$stack", "$Stack"),
            ("$instr", "$Instr"),
            ("$binopDenote", "$binopDenote"),
            ("$instrDenote", "$instrDenote"),
            ("$prog", "$Prog"),
            ("$expDenote", "$expDenote"),
            ("$progDenote", "$progDenote"),
            ("$compile", "$compile"),
        ],
    )
)
KNOWN_PAIRS = [
    ("Nat.add", "Imported.Nat_add"),
    ("Nat.mul", "Imported.Nat_mul"),
    ("app", "Imported.List_append_inst1"),
]
KNOWN_IMPORTS = {"Nat.add_comm": "From Stdlib Require Import Arith."}
