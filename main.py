#!/usr/bin/env python
from utils import run_cmd, logging

BUILD_DIR = "/root/build"
SOURCE_DIR = "/root/autoformalization"
EXPORT_DIR = "/root/lean4export"


def add_lean():
    # For now, just add the Lean example to a file
    with open("example.lean", "r", encoding="utf-8") as f:
        lean = f.read()

    run_cmd(f"""cat << 'EOF' > {EXPORT_DIR}/Origin.lean
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
        f"(grep -q 'lean_lib Origin' {EXPORT_DIR}/lakefile.lean || (sed '8i\\lean_lib Origin' {EXPORT_DIR}/lakefile.lean > temp && mv temp {EXPORT_DIR}/lakefile.lean))"
    )

    run_cmd(
        f"(grep -q '^import Origin' {EXPORT_DIR}/Main.lean || ((echo 'import Origin' && cat {EXPORT_DIR}/Main.lean) > temp && mv temp {EXPORT_DIR}/Main.lean))"
    )

    # Run lake build to verify it's valid code
    run_cmd(f"cd {EXPORT_DIR} && lake update && lake build")

    # Run Lake exe export to get the exported code
    definitions = extract_definitions()
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
