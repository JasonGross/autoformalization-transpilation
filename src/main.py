#!/usr/bin/env python
import os
import re
import shlex
import sys
from dataclasses import dataclass
from typing import Optional

from config import (
    BUILD_DIR,
    EXAMPLE_STATEMENTS,
    EXPORT_DIR,
    ISO_CHECKER_HEADER,
    ISO_HEADER,
    ISO_INTERFACE_HEADER,
    ISO_RETRIES,
    SOURCE_DIR,
)
from utils import logging, run_cmd


class Project:
    # See this comment (https://github.com/JasonGross/autoformalization/pull/27#discussion_r1942030347) by Jason for a suggestion of structure here
    def __init__(self):
        pass


class LeanProject(Project):
    pass


class CoqProject(Project):
    pass


@dataclass
class File:
    contents: str

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


@dataclass
class Identifier:
    name: str

    def __str__(self) -> str:
        return self.name


class LeanIdentifier(Identifier):
    pass


class CoqIdentifier(Identifier):
    pass


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
]


def extract_definitions(file_name: str) -> list[LeanIdentifier]:
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
    export_success, lean_export = export_from_lean()
    assert export_success, "Lean export failed!"
    # Import statements back into Coq
    cc_identifiers = []
    for coq_id, lean_id in identifiers:
        cc_identifiers.append((coq_id, lean_id_to_coq(lean_id)))

    success, error = import_to_coq(lean_export)
    return success, cc_identifiers, error


def lean_id_to_coq(lean_id: LeanIdentifier) -> CoqIdentifier:
    return CoqIdentifier(str(lean_id).replace(".", "_"))


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


def import_to_coq(
    lean_export: ExportFile, coq_file: str = "target"
) -> tuple[bool, str]:
    # Copy files first
    run_cmd(f"mkdir -p {BUILD_DIR}")
    lean_export.write(f"{BUILD_DIR}/{coq_file}.out")

    run_cmd(
        f"""echo 'From LeanImport Require Import Lean.
    Redirect "{coq_file}.log" Lean Import "{coq_file}.out".' > {BUILD_DIR}/{coq_file}.v"""
    )

    # Then run coqc and check its status
    # Plausibly we should be generating a list of statements ready for the isomorphism proofs
    # But for now we just check the status
    result = run_cmd(f"cd {BUILD_DIR} && coqc {coq_file}.v", check=False)
    if result.returncode == 0:
        return True, ""
    else:
        logging.error("Coq compilation failed")
        # TODO: Actually retrieve error, for example look at result.stderr, search for the last
        # instance of 'File "[^"]+", line ([0-9]+), characters ([0-9]+)-([0-9]+):\n', pick out the
        #  line numbers from the file, so the LLM doesn't have to do arithmetic
        return False, "Coq compilation failed"


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
        f"""cat > {BUILD_DIR}/lean-build/Main.lean << 'EOL'
import LeanBuild
def main : IO Unit :=
 IO.println s!"Compilation succeeded!"
EOL"""
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


def generate_interface(coq_identifiers: list[CoqIdentifier]):
    # TODO: Implement https://github.com/JasonGross/autoformalization/pull/19#discussion_r1934686304
    # Can make these parameters if needed
    original_name, output_file, checker_file = (
        "Original",
        f"{SOURCE_DIR}/iso-checker/Interface.v",
        f"{SOURCE_DIR}/iso-checker/Checker.v",
    )

    # Should also be generating these programmatically, for now these are manual
    # TODO: This should happen in the reimport step!
    # Generate the isomorphism checks for each definition pair
    iso_interface_checks = []
    iso_checks = []
    iso_names = []
    for coq_name in coq_identifiers:
        first_id = str(coq_name)
        coq_id = str(coq_name).replace(".", "_")
        iso_name = f"{coq_id}_iso"
        if str(coq_name)[0] == "$":
            # Python is dynamically typed for a reason
            coq_name = str(coq_name)[1:]
            coq_id = coq_id[1:]
            first_id = f"{original_name}.{coq_name}"
            iso_name = f"{coq_id}_iso"
            iso_names.append(iso_name)
        iso_interface_block = f"""Parameter imported_{coq_id} : import_of {first_id}.
Parameter {iso_name} : iso_statement {first_id} imported_{coq_id}.
Existing Instance {iso_name}."""
        iso_interface_checks.append(iso_interface_block)
        iso_block = f"""Derive imported_{coq_id} in (iso_statement {first_id} (imported_{coq_id} :> import_of {first_id})) as {iso_name}.
Proof. subst imported_{coq_id}. exact Isomorphisms.{iso_name}. Defined.
Existing Instance {iso_name}."""
        iso_checks.append(iso_block)

    # Generate a `Print Assumptions` check for dependencies
    everything_interface_block = f"""Import IsomorphismChecker.Automation.HList.HListNotations.
Definition everything := ({" :: ".join(iso_names)} :: [])%hlist."""

    everything_block = f"""Definition everything := Isomorphisms.everything."""

    # Combine all sections
    full_interface_content = "\n\n".join(
        [
            ISO_INTERFACE_HEADER,
            "\n\n".join(iso_interface_checks),
            everything_interface_block,
            "End Interface.",
        ]
    )
    logging.debug(f"{full_interface_content}")

    full_content = "\n\n".join(
        [
            ISO_CHECKER_HEADER,
            "\n\n".join(iso_checks),
            everything_block,
            "End DoesItCheck.",
        ]
    )
    logging.debug(f"{full_content}")

    # Write to file
    # TODO: Respond to https://github.com/JasonGross/autoformalization/pull/19#discussion_r1934670423
    with open(output_file, "w") as f:
        f.write(full_interface_content)

    # Write to file
    # TODO: Respond to https://github.com/JasonGross/autoformalization/pull/19#discussion_r1934670423
    with open(checker_file, "w") as f:
        f.write(full_content)


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
    # Generate the isomorphism checks for each definition pair
    iso_checks = []
    iso_names = []
    for coq_name, coq_lean_name in cc_identifiers:
        first_id = coq_name
        second_id = coq_lean_name
        coq_id = str(coq_name).replace(".", "_")
        iso_name = f"{coq_id}_iso"
        if str(coq_name)[0] == "$":
            # Python is dynamically typed for a reason
            coq_name = str(coq_name)[1:]  # type: ignore
            coq_id = coq_id[1:]
            first_id = f"{original_name}.{coq_name}"  # type: ignore
            iso_name = f"{coq_id}_iso"
            iso_names.append(iso_name)
        if str(coq_lean_name)[0] == "$":
            coq_lean_name = str(coq_lean_name)[1:]  # type: ignore
            second_id = imported_name + "." + coq_lean_name  # type: ignore

        iso_names.append(iso_name)

        iso_block = f"""Instance {iso_name} : iso_statement {first_id} {second_id}.
Proof. iso. Defined.
Instance: KnownConstant {first_id} := {{}}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant {second_id} := {{}}. (* only needed when rel_iso is typeclasses opaque *)"""

        iso_checks.append(iso_block)

    # Generate a `Print Assumptions` check for dependencies
    print_assumptions_block = f"""Import IsomorphismChecker.Automation.HList.HListNotations.
Definition everything := ({" :: ".join(iso_names)} :: [])%hlist.
Print Assumptions everything."""

    # Combine all sections
    full_content = "\n\n".join(
        [ISO_HEADER, "\n\n".join(iso_checks), print_assumptions_block]
    )
    logging.debug(f"{full_content}")

    # Write to file
    # TODO: Respond to https://github.com/JasonGross/autoformalization/pull/19#discussion_r1934670423
    with open(output_file, "w") as f:
        f.write(full_content)


def parse_iso_errors(errors: str) -> str:
    # Yes I know this should probably return an enum or something
    if "Could not find iso" in errors:
        return "missing_type_iso"
    elif bool(re.search(r"Error:.*?constructor", errors, re.IGNORECASE)):
        return "disordered_constr"
    elif "Unfolding unknown" in errors or "Reducing unknown" in errors:
        return "maybe_missing_stmnt_iso"
    else:
        return "other_iso_issue"


def desigil(s, prefix: str = ""):
    if s[0] == "$":
        return prefix + s[1:]
    return s


def repair_isos_interface(
    errors: str, coq_identifiers: list[CoqIdentifier]
) -> list[CoqIdentifier]:
    # Look at the errors, attempt to fix the isos
    error = parse_iso_errors(errors)
    iso_file = f"{SOURCE_DIR}/iso-checker/Interface.v"
    result = re.search(
        r"While importing ([\w\.]+): Consider adding iso_statement ([\w\.]+) ",
        re.sub(r"\s+", " ", errors),
    )
    assert result is not None, re.sub(r"\s+", " ", errors)
    orig_source, source = result.groups()
    coq_identifiers_str = [desigil(str(s), "Original.") for s in coq_identifiers]
    assert orig_source in coq_identifiers_str, (
        orig_source,
        coq_identifiers_str,
    )
    logging.info(f"Adding iso_statement {source} for {orig_source}")
    index = coq_identifiers_str.index(orig_source)
    coq_identifiers.insert(index, CoqIdentifier(source))
    generate_interface(coq_identifiers)
    return coq_identifiers


def repair_isos(
    errors: str, cc_identifiers: list[tuple[CoqIdentifier, CoqIdentifier]]
) -> list[tuple[CoqIdentifier, CoqIdentifier]]:
    # Look at the errors, attempt to fix the isos
    error = parse_iso_errors(errors)
    iso_file = f"{SOURCE_DIR}/iso-checker/Isomorphisms.v"
    match error:
        case "missing_type_iso":
            # Add the missing iso and regenerate
            result = re.search(
                r"While proving iso_statement ([\w\.]+) ([\w\.]+): Could not find iso for ([\w\.]+) -> ([\w\.]+)",
                errors,
            )
            assert result is not None, errors
            orig_source, orig_target, source, target = result.groups()
            cc_identifiers_str = [
                (desigil(str(s), "Original."), desigil(str(t), "Imported."))
                for s, t in cc_identifiers
            ]
            assert (orig_source, orig_target) in cc_identifiers_str, (
                (orig_source, orig_target),
                cc_identifiers_str,
            )
            index = cc_identifiers_str.index((orig_source, orig_target))
            cc_identifiers.insert(index, (CoqIdentifier(source), CoqIdentifier(target)))
            generate_isos(cc_identifiers)
        case "disordered_constr":
            # Reorder goals (via LLM) and update proof
            # TODO: Should just define prompts in a dict somewhere
            llm_repair(
                iso_file,
                f"Constructors are out of order, please reorder the goals - the error is {error}",
            )
        case "maybe_missing_stmnt_iso":
            csts = re.findall(
                r"(Unfolding|Reducing) unknown \w+ on (lhs|rhs)\s*:\s*([^ $]+)$",
                errors,
                flags=re.MULTILINE,
            )
            last_proving_instance = re.findall(
                r"Proving iso_statement ([\w\.]+) ([\w\.]+)", errors
            )
            if last_proving_instance:
                last_proving_statement = last_proving_instance[-1]
                logging.info("Last proving statement found: %s", last_proving_statement)
            else:
                logging.info("No proving statement found in the errors.")
                assert False, errors
            orig_source, orig_target = last_proving_statement
            cc_identifiers_str = [
                (desigil(str(s), "Original."), desigil(str(t), "Imported."))
                for s, t in cc_identifiers
            ]
            assert (orig_source, orig_target) in cc_identifiers_str, (
                (orig_source, orig_target),
                cc_identifiers_str,
            )
            cc_lhs = [s for s, _ in cc_identifiers]
            cc_rhs = [t for _, t in cc_identifiers]
            lhs = []
            rhs = []
            for _, side, statement in csts:
                if (
                    side == "lhs"
                    and statement not in lhs
                    and statement not in cc_lhs
                    and statement != orig_source
                ):
                    lhs.append(statement)
                elif (
                    side == "rhs"
                    and statement not in rhs
                    and statement not in cc_rhs
                    and statement != orig_target
                ):
                    rhs.append(statement)
            new_pair = llm_suggest_paired_identifier(lhs, rhs)
            if new_pair:
                logging.info(
                    f"Adding iso_statement {str(new_pair[0])}, {str(new_pair[1])} for {orig_source}, {orig_target}"
                )
                index = cc_identifiers_str.index((orig_source, orig_target))
                cc_identifiers.insert(index, new_pair)
                generate_isos(cc_identifiers)
            else:
                # TODO: rewrite with Nat.add_comm or w/e
                logging.info((lhs, rhs))
                assert False, errors
        case "other_iso_issue":
            # Heuristically rewrite to account for Lean vs Coq differences (via LLM / COPRA)
            llm_repair(iso_file, f"Please fix this error in our isomorphisms: {error}")
    return cc_identifiers


def llm_repair(file, prompt: str) -> None:
    # Call out to the LLM
    return None


def llm_suggest_paired_identifier(
    lhs: list[str], rhs: list[str]
) -> tuple[CoqIdentifier, CoqIdentifier] | None:
    for coq_id, imported_id in KNOWN_PAIRS:
        if coq_id in lhs and imported_id in rhs:
            return (CoqIdentifier(coq_id), CoqIdentifier(imported_id))
    return None


def generate_and_prove_iso_interface(
    coq_identifiers: list[CoqIdentifier],
) -> tuple[bool, Optional[str]]:
    # Make interface file
    generate_interface(coq_identifiers)

    # Check that the iso proof compiles
    result, errors = make_isos_interface()

    if result:
        logging.info("Isomorphism interface proof succeeded")
    else:
        attempt = 0
        while errors:
            attempt += 1
            logging.info(f"Isomorphism interface proof failed on attempt {attempt}")
            logging.debug(errors)
            repair_isos_interface(errors, coq_identifiers)
            result, errors = make_isos_interface()

    # Eventually will want to feed back isos but for now just return result
    return result, errors


def generate_and_prove_iso(
    cc_identifiers: list[tuple[CoqIdentifier, CoqIdentifier]],
) -> tuple[bool, Optional[str]]:
    # Make demo file
    generate_isos(cc_identifiers)

    # Check that the iso proof compiles
    result, errors = make_isos("Checker.vo")

    if result:
        logging.info("Isomorphism proof succeeded")
    else:
        attempt = 0
        # TODO: Only steps that call out to the llm should decrease the retry count, and the retry count should be per-isomorphism.
        # That is, we should be able to add as many missing isomorphisms as are required, and we shouldn't quit early if we are
        # making progress towards proving more and more isomorphisms.
        while attempt < ISO_RETRIES and errors:
            cc_identifiers = repair_isos(errors, cc_identifiers)
            # Check that the iso proof compiles
            result, errors = make_isos("Checker.vo")
            if not result:
                # Should feed all errors for iso repair
                logging.info(f"Isomorphism proof failed on attempt {attempt}:")
                if attempt < ISO_RETRIES - 1:
                    logging.debug(errors)
                    logging.info("Retrying...")
                else:
                    logging.info(errors)
                    logging.info("Isomorphism proof failed on final attempt")
            attempt += 1

    # Eventually will want to feed back isos but for now just return result
    return result, errors


def make_isos(*targets: str) -> tuple[bool, Optional[str]]:
    run_cmd(f"cd {SOURCE_DIR}/iso-checker/ && make clean", shell=True, check=False)
    result = run_cmd(
        f"cd {SOURCE_DIR}/iso-checker/ && {shlex.join(['make', *targets])}",
        shell=True,
        check=False,
    )
    if result.returncode != 0:
        # We log this and then feed it into our iso repair model
        error_message = f"{result.stdout}\n{result.stderr}".strip()
        logging.debug(f"Make failed: {error_message}")
        # Check error message for missing isomorphisms
        if iso_pairs := [
            (match.group(1), match.group(2))
            for match in re.finditer(
                r"Could not find iso for (\w+) -> (\w+)", error_message
            )
        ]:
            logging.info(f"Found missing isomorphisms: {set(iso_pairs)}")
        return False, error_message
    return True, None


def make_isos_interface() -> tuple[bool, Optional[str]]:
    return make_isos("Interface.vo")


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


def extract_coq_identifiers(coq: CoqFile) -> list[CoqIdentifier]:
    # Extract identifiers from Coq statements
    if not coq:
        # TODO: Have the actual identifier pairs
        return [coq_id for coq_id, _ in DEFINITION_PAIRS]

    else:
        # extract things
        assert False


def translate(
    coq: CoqFile, error_code: Optional[str], error: Optional[str]
) -> tuple[LeanFile, list[tuple[CoqIdentifier, LeanIdentifier]]]:
    # If it's not the first attempt, we have an error code and message from the previous failure
    if not coq:
        # TODO: Have the actual identifier pairs
        return LeanFile("\n".join(EXAMPLE_STATEMENTS)), DEFINITION_PAIRS

    else:
        # Translate things!
        return LeanFile("\n"), []


def translate_and_prove(
    coq_statements: CoqFile,
) -> tuple[bool, LeanFile, list[tuple[CoqIdentifier, LeanIdentifier]]]:
    success = False
    error_code, error = None, None  # Used for subsequent attempts of translation

    coq_identifiers = extract_coq_identifiers(coq_statements)
    interface_success, error = generate_and_prove_iso_interface(coq_identifiers)
    if not interface_success:
        assert False, "Failed to generate isomorphism interface!"
        error_code = "isomorphism_interface_failure"

    while not success:
        # Translate statements from Coq to Lean
        # TBD by all of us, with varying degrees of handholding
        lean_statements, cl_identifiers = translate(coq_statements, error_code, error)

        success, error_code, error = check_translation(lean_statements, cl_identifiers)

        # TODO: we might retry this (or control retries from inspect, TBD)
        if error_code == "isomorphism_failure":
            assert False, "Failed to prove isomorphisms!"
        elif error_code == "export_import_failure":
            assert False, "Importing from Lean to Coq failed!"
        elif error_code == "compilation_failure":
            assert False, "Lean code does not compile!"

    return success, lean_statements, cl_identifiers


# TODO: Move this (and called functions) to a different file
def check_translation(
    lean_statements: LeanFile,
    cl_identifiers: list[tuple[CoqIdentifier, LeanIdentifier]],
) -> tuple[bool, Optional[str], Optional[str]]:
    success, error_code = False, None
    # Verify that the Lean code compiles
    compile_success, error = check_compilation(lean_statements)
    # TODO: Use a class derived from Enum or StrEnum
    if not compile_success:
        # TODO: Kick this back to the translator
        error_code = "compilation_failure"
        return success, error_code, error

    # Import statements back into Coq
    reimport_success, cc_identifiers, error = lean_to_coq(
        lean_statements, cl_identifiers
    )
    # TODO: Kick this back to the translator (if export failed) or end user (if import failed)
    if not reimport_success:
        error_code = "export_import_failure"
        return success, error_code, error

    # Generate and prove isomorphism
    iso_success, error = generate_and_prove_iso(cc_identifiers)
    if not iso_success:
        error_code = "isomorphism_failure"
        return success, error_code, error
    success = True
    return success, error_code, error


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
