#!/usr/bin/env python
from utils import run_cmd, logging
import os

BUILD_DIR = "/root/build"
SOURCE_DIR = "/root/autoformalization"
EXPORT_DIR = "/root/lean4export"
ISO_HEADER = """From Stdlib Require Import Arith.
From IsomorphismChecker Require Import Automation EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Print Imported.
"""


def add_lean(target):
    # For now, just add the Lean example to a file
    with open("example.lean", "r", encoding="utf-8") as f:
        lean = f.read()

    run_cmd(f"""cat << 'EOF' > {target}
    {lean}""")


def extract_definitions():
    # TODO: Actually do something with Origin.lean
    # For now, just do this
    lst = "CompilerPlayground.Binop CompilerPlayground.Exp CompilerPlayground.Instr CompilerPlayground.Prog CompilerPlayground.Stack CompilerPlayground.binopDenote CompilerPlayground.expDenote CompilerPlayground.instrDenote CompilerPlayground.progDenote CompilerPlayground.compile CompilerPlayground.compileOneInstrStatement CompilerPlayground.compileCorrect CompilerPlayground.binOpComm CompilerPlayground.reverseMerge CompilerPlayground.compileOpComm CompilerPlayground.constEq CompilerPlayground.constInsEq CompilerPlayground.constOnlyConst CompilerPlayground.listEq CompilerPlayground.constCmpl"
    definitions = lst.split()
    return definitions


def lean_to_coq():
    # For now we use pre-generated Lean code
    add_lean(f"{EXPORT_DIR}/Origin.lean")
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


def check_compilation():
    # Check that we can compile in Lean
    run_cmd(f"mkdir -p {BUILD_DIR}")
    if not os.path.exists(f"{BUILD_DIR}/lean-build"):
        run_cmd(f"cd {BUILD_DIR} && lake new lean-build", shell=True, check=False)

    # Clear existing code, if any
    run_cmd(f"rm -f {BUILD_DIR}/lean-build/LeanBuild/Basic.lean")
    run_cmd(f"rm -f {BUILD_DIR}/lean-build/Main.lean")

    # Put new code in the right place
    add_lean(f"{BUILD_DIR}/lean-build/LeanBuild/Basic.lean")
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
    for coq_name, lean_name in definition_pairs:
        # Replace dots with asterisks in lean name
        coq_lean_name = lean_name.replace(".", "_")

        iso_block = f"""Instance {coq_lean_name}_iso : iso_statement {original_name}.{coq_name} {imported_name}.{coq_lean_name}.
Proof. iso. Defined.
Instance: KnownConstant {original_name}.{coq_name} := {{}}.
Instance: KnownConstant {imported_name}.{coq_lean_name} := {{}}."""

        iso_checks.append(iso_block)

    # Combine all sections
    full_content = "\n\n".join([ISO_HEADER, "\n\n".join(iso_checks)])
    logging.info(f"{full_content}")

    # Write to file
    with open(output_file, "w") as f:
        f.write(full_content)


def generate_and_prove_iso():
    # Make demo file
    generate_isos()

    # Check that the iso proof compiles
    return make_isos()


def make_isos():
    run_cmd(f"cd {SOURCE_DIR}/iso-checker/ && make clean", shell=True, check=False)
    result = run_cmd(f"cd {SOURCE_DIR}/iso-checker/ && make", shell=True, check=False)
    if result.returncode != 0:
        # We want to feed this back to the iso prover if we've failed, but for now just crash
        error_message = f"{result.stdout}\n{result.stderr}".strip()
        logging.error(f"Make failed: {error_message}")
        return False
    return True


def extract_and_add():
    return True


if __name__ == "__main__":
    # Extract list of statements from input
    # @@Shiki to explain how we are doing this
    # and add the code to this repo

    success = False
    # Should have a counter / timer so we don't go forever
    while not success:
        # Translate statements from Coq to Lean
        # TBD by all of us, with varying degrees of handholding

        # Verify that the Lean code compiles
        compile_success = check_compilation()
        if not compile_success:
            assert False, "Lean code does not compile!"
            continue

        # Import statements back into Coq
        reimport_success = lean_to_coq()
        if not reimport_success:
            assert False, "Importing from Lean to Coq failed!"
            continue

        # Generate and prove isomorphism
        iso_success = generate_and_prove_iso()
        if not iso_success:
            assert False, "Failed to prove isomorphisms!"
            continue
        success = True

    # If successful, extract statement pairs and add to training set
    extract_and_add()

    # Return success or failure
    print("Success!")
