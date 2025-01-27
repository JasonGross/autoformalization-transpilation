#!/usr/bin/env python
from utils import run_cmd, logging

build_dir = "/root/build"
source_dir = "/root/autoformalization"
export_dir = "/root/lean4export"


def add_lean():
    # For now, just add the Lean example to a file
    lean = """-- Lean 4 translation, CHUNK #1

namespace CompilerPlayground

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

end CompilerPlayground

-- Lean 4 translation, CHUNK #2

namespace CompilerPlayground

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

end CompilerPlayground



namespace CompilerPlayground

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

end CompilerPlayground"""

    run_cmd(f"""cat << 'EOF' > {export_dir}/Origin.lean
    {lean}""")


def extract_definitions():
    # TODO: Actually do something with Origin.lean
    # For now, just do this
    lst = "CompilerPlayground.Binop CompilerPlayground.Exp CompilerPlayground.Instr CompilerPlayground.Prog CompilerPlayground.Stack CompilerPlayground.binopDenote CompilerPlayground.expDenote CompilerPlayground.instrDenote CompilerPlayground.progDenote CompilerPlayground.compile CompilerPlayground.compileOneInstrStatement CompilerPlayground.compileCorrect CompilerPlayground.binOpComm CompilerPlayground.reverseMerge CompilerPlayground.compileOpComm CompilerPlayground.constEq CompilerPlayground.constInsEq CompilerPlayground.constOnlyConst CompilerPlayground.listEq CompilerPlayground.constCmpl"
    definitions = lst.split()
    return definitions


def lean_to_coq():
    # For now we use pre-generated Lean code
    add_lean()
    # Export statements from Lean
    export_from_lean()
    # Import statements back into Coq
    success = import_to_coq()
    return success


def export_from_lean():
    # Mangle files
    run_cmd(
        f"(grep -q 'lean_lib Origin' {export_dir}/lakefile.lean || (sed '8i\\lean_lib Origin' {export_dir}/lakefile.lean > temp && mv temp {export_dir}/lakefile.lean))"
    )

    run_cmd(
        f"(grep -q '^import Origin' {export_dir}/Main.lean || ((echo 'import Origin' && cat {export_dir}/Main.lean) > temp && mv temp {export_dir}/Main.lean))"
    )

    # Run lake build to verify it's valid code
    run_cmd(f"cd {export_dir} && lake update && lake build")

    # Run Lake exe export to get the exported code
    definitions = extract_definitions()
    cmd = f"cd {export_dir} && lake exe lean4export Main --"
    for definition in definitions:
        cmd += f" {definition}"

    # Produce .out file and put in right place
    cmd += f" > {source_dir}/target.out"
    run_cmd(cmd)

    return True


def import_to_coq():
    # Copy files first
    run_cmd(f"mkdir -p {build_dir}")
    run_cmd(f"cp {source_dir}/target.out {build_dir}")

    run_cmd(f"""echo 'From LeanImport Require Import Lean.
    Redirect "target.log" Lean Import "target.out".' > {build_dir}/target.v""")

    # Then run coqc and check its status
    # Plausibly we should be generating a list of statements ready for the isomorphism proofs
    # But for now we just check the status
    result = run_cmd(f"cd {build_dir} && coqc target.v", check=False)
    if result.returncode == 0:
        return True
    else:
        logging.error("Coq compilation failed")
        return False


if __name__ == "__main__":
    # Extract list of statements from input
    # @@Shiki to explain how we are doing this
    # and add the code to this repo

    # Translate statements from Coq to Lean
    # TBD by all of us, with varying degrees of handholding

    # Import statements back into Coq
    reimport_success = lean_to_coq()

    # Generate and prove isomorphism

    # If successful, extract statement pairs and add to training set

    # Return success or failure
    print("Success!")
