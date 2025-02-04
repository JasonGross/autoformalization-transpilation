#!/usr/bin/env python
from utils import run_cmd, logging
import os
import re
import sys

BUILD_DIR = "/root/build"
SOURCE_DIR = "/root/autoformalization"
EXPORT_DIR = "/root/lean4export"
ISO_HEADER = """From IsomorphismChecker Require Import Automation EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Print Imported.
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


def add_lean(code, target):
    # @@Jacob: Takes a list of lean statements and a target file
    lean = "\n".join(code)
    run_cmd(f"""cat << 'EOF' > {target}
    {lean}""")


def extract_definitions(file):
    # TODO: Actually do something with Origin.lean
    # For now, just do this
    lst = "Binop Exp Instr Prog Stack binopDenote expDenote instrDenote progDenote compile compileOneInstrStatement compileCorrect binOpComm reverseMerge compileOpComm constEq constInsEq constOnlyConst listEq constCmpl"
    definitions = lst.split()
    return definitions


def lean_to_coq(statements):
    # Construct a Lean file from all our snippets
    add_lean(statements, f"{EXPORT_DIR}/Origin.lean")
    # Export statements from Lean
    export_from_lean()
    # Import statements back into Coq
    success = import_to_coq()
    return success


def export_from_lean():
    # Mangle files
    run_cmd(
        f"(grep -q 'lean_lib Origin' {EXPORT_DIR}/lakefile.lean || (sed '8i\\lean_lib Origin' {EXPORT_DIR}/lakefile.lean > temp && mv temp {EXPORT_DIR}/lakefile.lean))"
    )

    run_cmd(
        f"(grep -q '^import Origin' {EXPORT_DIR}/Main.lean || ((echo 'import Origin' && cat {EXPORT_DIR}/Main.lean) > temp && mv temp {EXPORT_DIR}/Main.lean))"
    )

    # Run lake build to verify it's valid code
    run_cmd(f"cd {EXPORT_DIR} && lake update && lake build")

    # Run Lake exe export to get the exported code
    definitions = extract_definitions("{EXPORT_DIR}/Origin.lean")
    cmd = f"cd {EXPORT_DIR} && lake exe lean4export Main --"
    for definition in definitions:
        cmd += f" {definition}"

    # Produce .out file and put in right place
    cmd += f" > {SOURCE_DIR}/target.out"
    run_cmd(cmd)

    return True


def import_to_coq():
    # Copy files first
    run_cmd(f"mkdir -p {BUILD_DIR}")
    run_cmd(f"cp {SOURCE_DIR}/target.out {BUILD_DIR}")

    run_cmd(f"""echo 'From LeanImport Require Import Lean.
    Redirect "target.log" Lean Import "target.out".' > {BUILD_DIR}/target.v""")

    # Then run coqc and check its status
    # Plausibly we should be generating a list of statements ready for the isomorphism proofs
    # But for now we just check the status
    result = run_cmd(f"cd {BUILD_DIR} && coqc target.v", check=False)
    if result.returncode == 0:
        return True
    else:
        logging.error("Coq compilation failed")
        return False


def check_compilation(lean_statements):
    # Check that we can compile in Lean
    run_cmd(f"mkdir -p {BUILD_DIR}")
    if not os.path.exists(f"{BUILD_DIR}/lean-build"):
        run_cmd(f"cd {BUILD_DIR} && lake new lean-build", shell=True, check=False)

    # Clear existing code, if any
    run_cmd(f"rm -f {BUILD_DIR}/lean-build/LeanBuild/Basic.lean")
    run_cmd(f"rm -f {BUILD_DIR}/lean-build/Main.lean")

    # Put new code in the right place
    add_lean(lean_statements, f"{BUILD_DIR}/lean-build/LeanBuild/Basic.lean")
    run_cmd(
        [
            f"""cat > {BUILD_DIR}/lean-build/Main.lean << 'EOL'
import LeanBuild
def main : IO Unit :=
 IO.println s!"Compilation succeeded!"
EOL"""
        ]
    )

    # Then build
    run_cmd(f"cd {BUILD_DIR}/lean-build/ && lake update")
    result = run_cmd(
        f"cd {BUILD_DIR}/lean-build/ && lake build", shell=True, check=False
    )
    if result.returncode != 0:
        error_message = f"{result.stdout}\n{result.stderr}".strip()
        logging.error(f"Compilation failed: {error_message}")
        return False
    return True


def generate_isos():
    # TODO: Implement https://github.com/JasonGross/autoformalization/pull/19#discussion_r1934686304
    # Can make these parameters if needed
    original_name, imported_name, output_file = (
        "Original",
        "Imported",
        f"{SOURCE_DIR}/iso-checker/Isomorphisms.v",
    )

    # Should also be generating these programmatically, for now these are manual
    definition_pairs = [
        ("binop", "Binop"),
        ("exp", "Exp"),
        ("add", "Nat.add"),
        ("mul", "Nat.mul"),
        ("prod", "PProd"),
        ("stack", "Stack"),
        ("instr", "Instr"),
        ("binopDenote", "binopDenote"),
        ("app", "List.append.inst1"),
        ("instrDenote", "instrDenote"),
        ("prog", "Prog"),
        ("expDenote", "expDenote"),
        ("progDenote", "progDenote"),
        ("compile", "compile"),
        ("Binop", "Exp.binop"),
        ("Const", "Exp.const"),
        ("iConst", "Instr.iConst"),
        ("iBinop", "Instr.iBinop"),
    ]

    # Generate the isomorphism checks for each definition pair
    iso_checks = []
    iso_names = []
    for coq_name, lean_name in definition_pairs:
        # Replace dots with asterisks in lean name
        coq_lean_name = lean_name.replace(".", "_")
        iso_names.append(f"{coq_lean_name}_iso")

        iso_block = f"""Instance {coq_lean_name}_iso : iso_statement {original_name}.{coq_name} {imported_name}.{coq_lean_name}.
Proof. iso. Defined.
Instance: KnownConstant {original_name}.{coq_name} := {{}}.
Instance: KnownConstant {imported_name}.{coq_lean_name} := {{}}."""

        iso_checks.append(iso_block)

    # Generate a `Print Assumptions` check for dependencies
    print_assumptions_block = f"""Import IsomorphismChecker.Automation.HList.HListNotations.
Definition everything := ({" :: ".join(iso_names)} :: [])%hlist.
Print Assumptions everything."""

    # Combine all sections
    full_content = "\n\n".join(
        [ISO_HEADER, "\n\n".join(iso_checks), print_assumptions_block]
    )
    logging.info(f"{full_content}")

    # Write to file
    # TODO: Respond to https://github.com/JasonGross/autoformalization/pull/19#discussion_r1934670423
    with open(output_file, "w") as f:
        f.write(full_content)


def generate_and_prove_iso():
    # Make demo file
    generate_isos()

    # Check that the iso proof compiles
    result, isos = make_isos()

    # Eventually will want to feed back isos but for now just return result
    return result


def make_isos():
    run_cmd(f"cd {SOURCE_DIR}/iso-checker/ && make clean", shell=True, check=False)
    result = run_cmd(f"cd {SOURCE_DIR}/iso-checker/ && make", shell=True, check=False)
    if result.returncode != 0:
        # We want to feed this back to the iso prover if we've failed, but for now just crash
        error_message = f"{result.stdout}\n{result.stderr}".strip()
        logging.error(f"Make failed: {error_message}")
        # Check error message for missing isomorphisms
        if iso_pairs := [
            (match.group(1), match.group(2))
            for match in re.finditer(
                r"Could not find iso for (\w+) -> (\w+)", error_message
            )
        ]:
            logging.info(f"Found missing isomorphisms: {iso_pairs}")
        return False, iso_pairs
    return True, None


def extract_and_add(c_stms, l_stms):
    for coq, lean in zip(c_stms, l_stms):
        # Add this to the training set, if not already in it
        pass
    return True


def preprocess_source(src):
    if src is None:
        return []

    # Extract list of statements from input
    # @@Shiki to explain how we are doing this
    # and add the code to this repo


def translate(coq):
    if not coq:
        return EXAMPLE_STATEMENTS

    else:
        # Translate things!
        pass


def translate_and_prove(coq_statements):
    success = False
    while not success:
        # Translate statements from Coq to Lean
        # TBD by all of us, with varying degrees of handholding
        # @@Jacob: Takes a list of Coq statements, returns list of translated Lean statements
        lean_statements = translate(coq_statements)

        # Verify that the Lean code compiles
        compile_success = check_compilation(lean_statements)
        if not compile_success:
            assert False, "Lean code does not compile!"
            continue

        # Import statements back into Coq
        # @@Jacob: I expect this to take the list of statements and return a bool
        reimport_success = lean_to_coq(lean_statements)
        if not reimport_success:
            assert False, "Importing from Lean to Coq failed!"
            continue

        # Generate and prove isomorphism
        iso_success = generate_and_prove_iso()
        if not iso_success:
            assert False, "Failed to prove isomorphisms!"
            continue
        success = True
    return success, lean_statements


if __name__ == "__main__":
    # Extract a list of Coq statements from the input file(s)
    # @@Shiki @@Jacob: I expect this to take a filename (or maybe directory path) and return an ordered list of strings (Coq statements) to translate, for example
    # []"""Definition binopDenote (b : binop) : nat -> nat -> nat :=
    # match b with
    #     | Plus => plus
    #     | Times => mult
    # end."""]
    coq_statements = preprocess_source(None)

    # Translate them all into Lean and prove equivalence
    # @@Jacob: Will take a list of strings and return a bool and a list of lean statements, for example
    # (True, ["""def binopDenote : Binop → Nat → Nat → Nat
    #   | Binop.plus, x, y  => x + y
    #   | Binop.times, x, y => x * y"""])
    success, lean_statements = translate_and_prove(coq_statements)

    # If successful, extract statement pairs and add to training set
    if success:
        extract_and_add(coq_statements, lean_statements)

        # Return success or failure
        print("Success!")
        sys.exit(0)
    else:
        # TODO: Explain in more detail what needs fixing manually
        print("Could not translate and/or prove")
        sys.exit(1)
