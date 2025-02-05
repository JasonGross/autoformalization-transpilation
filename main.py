#!/usr/bin/env python
from utils import run_cmd, logging
import os
import re
import sys
from config import (
    BUILD_DIR,
    SOURCE_DIR,
    EXPORT_DIR,
    ISO_RETRIES,
    ISO_HEADER,
    EXAMPLE_STATEMENTS,
)
from typing import Optional


class Project:
    # See this comment (https://github.com/JasonGross/autoformalization/pull/27#discussion_r1942030347) by Jason for a suggestion of structure here
    def __init__(self):
        pass


class LeanProject(Project):
    pass


class CoqProject(Project):
    pass


class File:
    def __init__(self, contents: str):
        self.contents = contents

    def __str__(self) -> str:
        return self.contents

    def write(self, filepath: str) -> None:
        logging.debug(
            f"Writing {self.__class__.__name__} to {filepath}\nContents:\n{self.contents}"
        )
        with open(filepath, "w") as f:
            f.write(self.contents)


class LeanFile(File):
    pass


class CoqFile(File):
    pass


class ExportFile(File):
    pass


class Identifier:
    def __init__(self, name: str):
        self.name = name

    def __str__(self) -> str:
        return self.name


class LeanIdentifier(Identifier):
    pass


class CoqIdentifier(Identifier):
    pass


def extract_definitions(file: str) -> list[LeanIdentifier]:
    # TODO: Actually do something with Origin.lean
    # For now, just do this
    lst = "Binop Exp Instr Prog Stack binopDenote expDenote instrDenote progDenote compile compileOneInstrStatement compileCorrect binOpComm reverseMerge compileOpComm constEq constInsEq constOnlyConst listEq constCmpl"
    definitions = lst.split()
    return list(map(LeanIdentifier, definitions))


def lean_to_coq(
    statements: LeanFile, identifiers: list[tuple[CoqIdentifier, LeanIdentifier]]
) -> tuple[bool, list[tuple[CoqIdentifier, CoqIdentifier]], str]:
    # Construct a Lean file from all our snippets
    statements.write(f"{EXPORT_DIR}/Origin.lean")
    # Export statements from Lean
    _, lean_export = export_from_lean()  # Surely this will always succeed
    # Import statements back into Coq
    # TODO: convert the Lean identifiers into Coq identifiers
    success, error = import_to_coq(lean_export)
    return success, [], error


def export_from_lean() -> tuple[bool, ExportFile]:
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

    # # Produce .out file
    export_file = ExportFile(run_cmd(cmd).stdout)
    return True, export_file


def import_to_coq(lean_export: ExportFile) -> tuple[bool, str]:
    # Copy files first
    run_cmd(f"mkdir -p {BUILD_DIR}")
    lean_export.write(f"{BUILD_DIR}/target.out")

    run_cmd(f"""echo 'From LeanImport Require Import Lean.
    Redirect "target.log" Lean Import "target.out".' > {BUILD_DIR}/target.v""")

    # Then run coqc and check its status
    # Plausibly we should be generating a list of statements ready for the isomorphism proofs
    # But for now we just check the status
    result = run_cmd(f"cd {BUILD_DIR} && coqc target.v", check=False)
    if result.returncode == 0:
        return True, ""
    else:
        logging.error("Coq compilation failed")
        return False, "Coq compilation failed"  # TODO: Actually retrieve error


def check_compilation(lean_statements: LeanFile) -> tuple[bool, str]:
    # Check that we can compile in Lean
    run_cmd(f"mkdir -p {BUILD_DIR}")
    if not os.path.exists(f"{BUILD_DIR}/lean-build"):
        run_cmd(f"cd {BUILD_DIR} && lake new lean-build", shell=True, check=False)

    # Clear existing code, if any
    run_cmd(f"rm -f {BUILD_DIR}/lean-build/LeanBuild/Basic.lean")
    run_cmd(f"rm -f {BUILD_DIR}/lean-build/Main.lean")

    # Put new code in the right place
    lean_statements.write(f"{BUILD_DIR}/lean-build/LeanBuild/Basic.lean")
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
        return False, error_message
    return True, ""


def generate_isos(cc_identifiers: list[tuple[CoqIdentifier, CoqIdentifier]]):
    # TODO: Implement https://github.com/JasonGross/autoformalization/pull/19#discussion_r1934686304
    # Can make these parameters if needed
    original_name, imported_name, output_file = (
        "Original",
        "Imported",
        f"{SOURCE_DIR}/iso-checker/Isomorphisms.v",
    )

    # Retrieve exported Lean file
    run_cmd(f"cp {BUILD_DIR}/target.out {SOURCE_DIR}/iso-checker/imported.out")

    # Should also be generating these programmatically, for now these are manual
    # TODO: This should happen in the reimport step!
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


def repair_isos(errors: Optional[str]):
    # Look at the errors, attempt to fix the isos
    return True


def generate_and_prove_iso(
    cc_identifiers: list[tuple[CoqIdentifier, CoqIdentifier]],
) -> tuple[bool, Optional[str]]:
    # Make demo file
    generate_isos(cc_identifiers)

    # Check that the iso proof compiles
    result, errors = make_isos()

    if result:
        logging.info("Isomorphism proof succeeded")
    else:
        attempt = 0
        while attempt < ISO_RETRIES:
            repair_isos(errors)
            # Check that the iso proof compiles
            result, errors = make_isos()
            if not result:
                # Should feed all errors for iso repair
                logging.info(
                    f"Isomorphism proof failed on attempt {attempt}: : {errors}"
                )
                if attempt < ISO_RETRIES - 1:
                    logging.info("Retrying...")
                else:
                    logging.info("Isomorphism proof failed on final attempt")
            attempt += 1

    # Eventually will want to feed back isos but for now just return result
    return result, errors


def make_isos() -> tuple[bool, Optional[str]]:
    run_cmd(f"cd {SOURCE_DIR}/iso-checker/ && make clean", shell=True, check=False)
    result = run_cmd(f"cd {SOURCE_DIR}/iso-checker/ && make", shell=True, check=False)
    if result.returncode != 0:
        # We log this and then feed it into our iso repair model
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
        return False, error_message
    return True, None


def extract_and_add(
    c_stms: CoqFile,
    l_stms: LeanFile,
    cl_identifiers: list[tuple[CoqIdentifier, LeanIdentifier]],
) -> bool:
    # Use the identifier list to extract the statements from the file and add them to the training set, if not already in it
    return True


def preprocess_source(src):  # Optional[CoqProject]) -> CoqFile:
    if src is None:
        return []

    # Extract list of statements from input
    # @@Shiki to explain how we are doing this
    # and add the code to this repo
    # At the moment there is an assumption that we only produce a single CoqFile, which will obviously not hold as project size scales


def translate(
    coq: CoqFile, error_code: Optional[str], error: Optional[str]
) -> tuple[LeanFile, list[tuple[CoqIdentifier, LeanIdentifier]]]:
    # If it's not the first attempt, we have an error code and message from the previous failure
    if not coq:
        # TODO: Have the actual identifier pairs
        return LeanFile("\n".join(EXAMPLE_STATEMENTS)), []

    else:
        # Translate things!
        return LeanFile("\n"), []


def translate_and_prove(
    coq_statements: CoqFile,
) -> tuple[bool, LeanFile, list[tuple[CoqIdentifier, LeanIdentifier]]]:
    success = False
    error_code, error = None, None  # Used for subsequent attempts of translation
    while not success:
        # Translate statements from Coq to Lean
        # TBD by all of us, with varying degrees of handholding
        # @@Jacob: Takes a list of Coq statements, returns list of translated Lean statements
        lean_statements, cl_identifiers = translate(coq_statements, error_code, error)

        # Verify that the Lean code compiles
        compile_success, error = check_compilation(lean_statements)
        if not compile_success:
            assert False, "Lean code does not compile!"
            # TODO: Kick this back to the translator
            error_code = "compilation_failure"
            continue

        # Import statements back into Coq
        reimport_success, cc_identifiers, error = lean_to_coq(
            lean_statements, cl_identifiers
        )
        # TODO: Kick this back to the translator (if export failed) or end user (if import failed)
        if not reimport_success:
            assert False, "Importing from Lean to Coq failed!"
            error_code = "export_import_failure"
            continue

        # Generate and prove isomorphism
        iso_success, error = generate_and_prove_iso(cc_identifiers)
        if not iso_success:
            assert False, "Failed to prove isomorphisms!"
            error_code = "isomorphism_failure"
            continue
        success = True
    return success, lean_statements, cl_identifiers


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
    # Will take a list of strings and return a bool and a list of lean statements, for example
    # (True, ["""def binopDenote : Binop → Nat → Nat → Nat
    #   | Binop.plus, x, y  => x + y
    #   | Binop.times, x, y => x * y"""])
    # We expect failures to be like "out of disk space" or "ran out of attempts to try", which should probably be raised rather than returned
    success, lean_statements, cl_identifiers = translate_and_prove(coq_statements)

    # If successful, extract statement pairs and add to training set
    if success:
        # Need to decide how this actually works
        # extract_and_add(coq_statements, lean_statements, cl_identifiers)

        # Return success or failure
        print("Success!")
        sys.exit(0)
    else:
        # TODO: Explain in more detail what needs fixing manually
        print("Could not translate and/or prove")
        sys.exit(1)
