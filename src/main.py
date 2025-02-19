#!/usr/bin/env python
import contextlib
import re
import sys
import tempfile
from enum import StrEnum
from pathlib import Path
from typing import Optional

from config import (
    EXAMPLE_STATEMENTS,
    EXPORT_DIR,
    ISO_CHECKER_HEADER,
    ISO_HEADER,
    ISO_INTERFACE_HEADER,
    ISO_RETRIES,
    SOURCE_DIR,
)
from project_util import (
    CoqFile,
    CoqIdentifier,
    CoqProject,
    ExportFile,
    LeanFile,
    LeanIdentifier,
    LeanProject,
)
from utils import logging, run_cmd
from utils.memoshelve import cache

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


def extract_definitions(file: LeanFile) -> list[LeanIdentifier]:
    # TODO: Actually do something with Origin.lean
    # For now, just do this
    lst = "Binop Exp Instr Prog Stack binopDenote expDenote instrDenote progDenote compile compileOneInstrStatement compileCorrect binOpComm reverseMerge compileOpComm constEq constInsEq constOnlyConst listEq constCmpl"
    definitions = lst.split()
    return list(map(LeanIdentifier, definitions))


def lean_to_coq(
    lean_project: LeanProject,
    coq_project: CoqProject,
    statements: LeanFile,
    identifiers: list[tuple[CoqIdentifier, LeanIdentifier]],
) -> tuple[
    LeanProject,
    CoqProject,
    bool,
    list[tuple[CoqIdentifier, CoqIdentifier, str | None]],
    str,
]:
    lean_project = lean_project.copy()

    # Construct a Lean file from all our snippets
    lean_project["Origin.lean"] = statements

    # Export statements from Lean
    lean_project, export_success, lean_export = export_from_lean(lean_project)
    assert export_success, "Lean export failed!"
    # Import statements back into Coq
    cc_identifiers = []
    for coq_id, lean_id in identifiers:
        cc_identifiers.append((coq_id, lean_id_to_coq(lean_id), None))

    coq_project, success, error = import_to_coq(coq_project, lean_export)
    return lean_project, coq_project, success, cc_identifiers, error


def lean_id_to_coq(lean_id: LeanIdentifier) -> CoqIdentifier:
    return CoqIdentifier(str(lean_id).replace(".", "_"))


@cache()
def export_from_lean(project: LeanProject) -> tuple[LeanProject, bool, ExportFile]:
    project = project.copy()
    with project.tempdir():
        # Mangle files
        run_cmd(
            f"(grep -q 'lean_lib Origin' lakefile.lean || (sed '8i\\lean_lib Origin' lakefile.lean > temp && mv temp lakefile.lean))",
            shell=True,
        )

        run_cmd(
            f"(grep -q '^import Origin' Main.lean || ((echo 'import Origin' && cat Main.lean) > temp && mv temp Main.lean))",
            shell=True,
        )

        # Run lake build to verify it's valid code
        run_cmd(f"lake update && lake build")

        # Run Lake exe export to get the exported code
        definitions = extract_definitions(LeanFile.read_text("Origin.lean"))
        cmd = f"lake exe lean4export Main --"
        for definition in definitions:
            cmd += f" {definition}"

        # # Produce .out file
        export_file = ExportFile(run_cmd(cmd).stdout)
        return LeanProject.read("."), True, export_file


def import_to_coq(
    project: CoqProject, lean_export: ExportFile, coq_file: str = "target"
) -> tuple[CoqProject, bool, str]:
    # Copy files first
    project = project.copy()
    project[f"{coq_file}.out"] = lean_export

    project[f"{coq_file}.v"] = CoqFile(
        f"""From LeanImport Require Import Lean.
Redirect "{coq_file}.log" Lean Import "{coq_file}.out"."""
    )

    # Then run coqc and check its status
    # Plausibly we should be generating a list of statements ready for the isomorphism proofs
    # But for now we just check the status
    result, project = project.run_cmd(
        ["coqc", f"{coq_file}.v"], check=False, shell=False
    )
    if result.returncode == 0:
        return project, True, ""
    else:
        logging.error("Coq compilation failed")
        # TODO: Actually retrieve error, for example look at result.stderr, search for the last
        # instance of 'File "[^"]+", line ([0-9]+), characters ([0-9]+)-([0-9]+):\n', pick out the
        #  line numbers from the file, so the LLM doesn't have to do arithmetic
        return project, False, "Coq compilation failed"


@cache()
def new_lake_project(name: str = "lean-build") -> LeanProject:
    with tempfile.TemporaryDirectory() as tempdir:
        tempdir = Path(tempdir)
        (tempdir / name).mkdir()
        with contextlib.chdir(tempdir):
            run_cmd(["lake", "new", name], check=False, shell=False)
        return LeanProject.read(tempdir / name)


@cache()
def check_compilation(
    lean_statements: LeanFile, project: LeanProject | None = None
) -> tuple[LeanProject, bool, str]:
    if project is None:
        project = new_lake_project(name="lean-build")

    # Clear existing code, if any
    if "LeanBuild/Basic.lean" in project:
        del project["LeanBuild/Basic.lean"]
    if "Main.lean" in project:
        del project["Main.lean"]

    # Put new code in the right place
    project["LeanBuild/Basic.lean"] = lean_statements
    project["Main.lean"] = LeanFile(
        """import LeanBuild
def main : IO Unit :=
 IO.println s!"Compilation succeeded!"
"""
    )

    # Then build
    project.write(Path(__file__).parent.parent / "temp_debug")
    _result, project = project.run_cmd(["lake", "update"], shell=False)
    result, project = project.run_cmd(["lake", "build"], shell=False)
    if result.returncode != 0:
        error_message = f"{result.stdout}\n{result.stderr}".strip()
        logging.error(f"Compilation failed: {error_message}")
        return project, False, error_message
    return project, True, ""


def generate_interface(
    project: CoqProject, coq_identifiers: list[CoqIdentifier]
) -> CoqProject:
    project = project.copy()
    # TODO: Implement https://github.com/JasonGross/autoformalization/pull/19#discussion_r1934686304
    # Can make these parameters if needed
    original_name, output_file, checker_file = (
        "Original",
        "Interface.v",
        "Checker.v",
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
    project[output_file] = CoqFile(full_interface_content)

    # Write to file
    project[checker_file] = CoqFile(full_content)

    return project


def generate_isos(
    project: CoqProject,
    cc_identifiers: list[tuple[CoqIdentifier, CoqIdentifier, str | None]],
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    output_file: str = "Isomorphisms.v",
) -> CoqProject:
    project = project.copy()

    # Retrieve exported Lean file
    project["imported.out"] = project["target.out"]

    # Should also be generating these programmatically, for now these are manual
    # TODO: This should happen in the reimport step!
    # Generate the isomorphism checks for each definition pair
    iso_checks = []
    iso_names = []
    for coq_name, coq_lean_name, proof in cc_identifiers:
        proof = proof or "iso."
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
Proof. {proof} Defined.
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
    project[output_file] = CoqFile(full_content)

    return project


class IsoError(StrEnum):
    MISSING_TYPE_ISO = "missing_type_iso"
    DISORDERED_CONSTR = "disordered_constr"
    MAYBE_MISSING_STMNT_ISO = "maybe_missing_stmnt_iso"
    OTHER_ISO_ISSUE = "other_iso_issue"
    MISSING_IMPORT = "missing_import"


def parse_iso_errors(errors: str) -> IsoError:
    # Yes I know this should probably return an enum or something
    if "Could not find iso" in errors:
        return IsoError.MISSING_TYPE_ISO
    elif bool(re.search(r"Error:.*?constructor", errors, re.IGNORECASE)):
        return IsoError.DISORDERED_CONSTR
    elif "was not found in the current environment." in errors:
        return IsoError.MISSING_IMPORT
    elif "Unfolding unknown" in errors or "Reducing unknown" in errors:
        return IsoError.MAYBE_MISSING_STMNT_ISO
    else:
        return IsoError.OTHER_ISO_ISSUE


def desigil(s: str, prefix: str = "") -> str:
    if s[0] == "$":
        return prefix + s[1:]
    return s


def repair_isos_interface(
    project: CoqProject,
    errors: str,
    coq_identifiers: list[CoqIdentifier],
    original_name: str = "Original",
) -> tuple[CoqProject, list[CoqIdentifier]]:
    # Look at the errors, attempt to fix the isos
    result = re.search(
        r"While importing ([\w\.]+): Consider adding iso_statement ([\w\.]+) ",
        re.sub(r"\s+", " ", errors),
    )
    assert result is not None, re.sub(r"\s+", " ", errors)
    orig_source, source = result.groups()
    coq_identifiers_str = [
        desigil(str(s), f"{original_name}.") for s in coq_identifiers
    ]
    assert orig_source in coq_identifiers_str, (
        orig_source,
        coq_identifiers_str,
    )
    logging.info(f"Adding iso_statement {source} for {orig_source}")
    index = coq_identifiers_str.index(orig_source)
    coq_identifiers.insert(index, CoqIdentifier(source))
    project = generate_interface(project, coq_identifiers)
    return project, coq_identifiers


def repair_isos(
    project: CoqProject,
    errors: str,
    cc_identifiers: list[tuple[CoqIdentifier, CoqIdentifier, str | None]],
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
) -> tuple[CoqProject, list[tuple[CoqIdentifier, CoqIdentifier, str | None]]]:
    project = project.copy()
    # Look at the errors, attempt to fix the isos
    error = parse_iso_errors(errors)
    iso_file = f"{SOURCE_DIR}/iso-checker/Isomorphisms.v"
    logging.info(f"Current error type is {error}")

    match error:
        case IsoError.MISSING_TYPE_ISO:
            # Add the missing iso and regenerate
            result = re.search(
                r"While proving iso_statement ([\w\.]+) ([\w\.]+): Could not find iso for ([\w\.]+) -> ([\w\.]+)",
                errors,
            )
            assert result is not None, errors
            orig_source, orig_target, source, target = result.groups()
            cc_identifiers_str = [
                (
                    desigil(str(s), f"{original_name}."),
                    desigil(str(t), f"{imported_name}."),
                )
                for s, t, _ in cc_identifiers
            ]
            assert (orig_source, orig_target) in cc_identifiers_str, (
                (orig_source, orig_target),
                cc_identifiers_str,
            )
            index = cc_identifiers_str.index((orig_source, orig_target))
            cc_identifiers.insert(
                index, (CoqIdentifier(source), CoqIdentifier(target), None)
            )
            project = generate_isos(
                project,
                cc_identifiers,
                original_name=original_name,
                imported_name=imported_name,
            )
        case IsoError.DISORDERED_CONSTR:
            # Reorder goals (via LLM) and update proof
            # TODO: Should just define prompts in a dict somewhere
            llm_repair(
                iso_file,
                f"Constructors are out of order, please reorder the goals - the error is {error}",
            )

        case IsoError.MISSING_IMPORT:
            known_imports = {"Nat.add_comm": "From Coq Require Import Arith."}
            import_str = re.search(
                r"Error: The reference ([^\s]+) was not found in the current environment.",
                errors,
            ).group(1)
            if import_str in known_imports:
                # Add the import to the top of the file
                run_cmd(
                    f"sed -i '1i\\{known_imports[import_str]}' {SOURCE_DIR}/iso-checker/Isomorphisms.v"
                )

            llm_repair(
                iso_file,
                f"We are missing an import, please add the correct one - the missing reference is {import_str}",
            )

        case IsoError.MAYBE_MISSING_STMNT_ISO:
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
                (
                    desigil(str(s), f"{original_name}."),
                    desigil(str(t), f"{imported_name}."),
                )
                for s, t, _ in cc_identifiers
            ]
            assert (orig_source, orig_target) in cc_identifiers_str, (
                (orig_source, orig_target),
                cc_identifiers_str,
            )
            cc_lhs = [s for s, _, _ in cc_identifiers]
            cc_rhs = [t for _, t, _ in cc_identifiers]
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
            index = cc_identifiers_str.index((orig_source, orig_target))
            new_pair = llm_suggest_paired_identifier(lhs, rhs)
            if new_pair:
                logging.info(
                    f"Adding iso_statement {str(new_pair[0])}, {str(new_pair[1])} for {orig_source}, {orig_target}"
                )
                cc_identifiers.insert(index, (*new_pair, None))
                project = generate_isos(
                    project,
                    cc_identifiers,
                    original_name=original_name,
                    imported_name=imported_name,
                )
            else:
                # TODO: rewrite with Nat.add_comm or w/e
                result = re.search(
                    r"While proving iso_statement ([\w\.]+) ([\w\.]+): \d+ goals? not fully solved:(.*)",
                    errors,
                    flags=re.DOTALL,
                )
                known_proofs = {
                    "Nat.add": "iso_no_debug. iso_rel_rewrite Nat.add_comm."
                }
                if result:
                    lhs, rhs, errors = result.groups()
                    if lhs in known_proofs:
                        insert_proof(lhs, known_proofs[lhs])
                    else:
                        assert cc_identifiers_str[index][:2] == (
                            lhs,
                            rhs,
                        ), cc_identifiers_str[index]
                        new_proof = llm_repair_proof(
                            "Please fix proof", errors, *cc_identifiers[index]
                        )
                        logging.info(
                            f"Setting proof for {lhs}, {rhs} to {new_proof} (from {cc_identifiers[index][2]})"
                        )
                        cc_identifiers[index] = cc_identifiers[index][:2] + (new_proof,)
                        project = generate_isos(
                            project,
                            cc_identifiers,
                            original_name=original_name,
                            imported_name=imported_name,
                        )
                else:
                    logging.info((lhs, rhs, result))
                    assert False, errors
        case IsoError.OTHER_ISO_ISSUE:
            # Heuristically rewrite to account for Lean vs Coq differences (via LLM / COPRA)
            llm_repair(iso_file, f"Please fix this error in our isomorphisms: {errors}")
    return project, cc_identifiers


def llm_repair_proof(
    prompt: str,
    errors: str,
    lhs: CoqIdentifier,
    rhs: CoqIdentifier,
    cur_proof: str | None,
) -> str:
    if cur_proof is None and re.search(
        r"rel_iso nat_iso .[\w\.\d]+ \+ [\w\.\d]+.", errors
    ):
        return "iso_no_debug. iso_rel_rewrite Nat.add_comm. iso."
    # Call out to the LLM
    assert False, (lhs, rhs, errors, cur_proof)


def llm_repair(file, prompt: str) -> None:
    # Call out to the LLM
    assert False, (file, prompt)


def insert_proof(identifier: str, proof: str) -> None:
    iso_file = f"{SOURCE_DIR}/iso-checker/Isomorphisms.v"
    cmd = f'grep -n "iso_statement {identifier}" {iso_file} | cut -d: -f1 | xargs -I{{}} bash -c \'sed -i "$(({{}}+1))s/.*/Proof. {proof} iso. Defined./" {iso_file}\''
    run_cmd(cmd)


def llm_suggest_paired_identifier(
    lhs: list[str], rhs: list[str]
) -> tuple[CoqIdentifier, CoqIdentifier] | None:
    for coq_id, imported_id in KNOWN_PAIRS:
        if coq_id in lhs and imported_id in rhs:
            return (CoqIdentifier(coq_id), CoqIdentifier(imported_id))
    return None


def generate_and_prove_iso_interface(
    project: CoqProject,
    coq_identifiers: list[CoqIdentifier],
) -> tuple[CoqProject, bool, Optional[str]]:
    # Make interface file
    project = generate_interface(project, coq_identifiers)

    # Check that the iso proof compiles
    project, result, errors = make_isos_interface(project)

    if result:
        logging.info("Isomorphism interface proof succeeded")
    else:
        attempt = 0
        while errors:
            attempt += 1
            logging.info(f"Isomorphism interface proof failed on attempt {attempt}")
            logging.debug(errors)
            project, coq_identifiers = repair_isos_interface(
                project, errors, coq_identifiers
            )
            project, result, errors = make_isos_interface(project)

    # Eventually will want to feed back isos but for now just return result
    return project, result, errors


def generate_and_prove_iso(
    project: CoqProject,
    cc_identifiers: list[tuple[CoqIdentifier, CoqIdentifier, str | None]],
) -> tuple[CoqProject, bool, Optional[str]]:
    # Make demo file
    project = generate_isos(project, cc_identifiers)

    # Check that the iso proof compiles
    project, result, errors = make_isos(project, "Checker.vo")

    if result:
        logging.info("Isomorphism proof succeeded")
    else:
        attempt = 0
        # TODO: Only steps that call out to the llm should decrease the retry count, and the retry count should be per-isomorphism.
        # That is, we should be able to add as many missing isomorphisms as are required, and we shouldn't quit early if we are
        # making progress towards proving more and more isomorphisms.
        while attempt < ISO_RETRIES and errors:
            project, cc_identifiers = repair_isos(project, errors, cc_identifiers)
            # Check that the iso proof compiles
            project, result, errors = make_isos(project, "Checker.vo")
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
    return project, result, errors


def make_isos(
    project: CoqProject, *targets: str
) -> tuple[CoqProject, bool, Optional[str]]:
    result, project = project.make(*targets, check=False)
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
        return project, False, error_message
    return project, True, None


def make_isos_interface(project: CoqProject) -> tuple[CoqProject, bool, Optional[str]]:
    return make_isos(project, "Interface.vo")


def extract_and_add(
    c_stms: CoqFile,
    l_stms: LeanFile,
    cl_identifiers: list[tuple[CoqIdentifier, LeanIdentifier]],
) -> bool:
    # Use the identifier list to extract the statements from the file and add them to the training set, if not already in it
    return True


def preprocess_source(src) -> CoqFile | None:  # Optional[CoqProject]) -> CoqFile:
    # if src is None:
    # return []
    return None

    # Extract list of statements from input
    # @@Shiki to explain how we are doing this
    # and add the code to this repo
    # At the moment there is an assumption that we only produce a single CoqFile, which will obviously not hold as project size scales


def extract_coq_identifiers(coq: CoqFile | None) -> list[CoqIdentifier]:
    # Extract identifiers from Coq statements
    if not coq:
        # TODO: Have the actual identifier pairs
        return [coq_id for coq_id, _ in DEFINITION_PAIRS]

    else:
        # extract things
        assert False


def translate(
    coq: CoqFile | None, error_code: Optional[str], error: Optional[str]
) -> tuple[LeanFile, list[tuple[CoqIdentifier, LeanIdentifier]]]:
    # If it's not the first attempt, we have an error code and message from the previous failure
    if not coq:
        # TODO: Have the actual identifier pairs
        return LeanFile("\n".join(EXAMPLE_STATEMENTS)), DEFINITION_PAIRS

    else:
        # Translate things!
        return LeanFile("\n"), []


class ErrorCode(StrEnum):
    COMPILATION_FAILURE = "compilation_failure"
    EXPORT_IMPORT_FAILURE = "export_import_failure"
    ISOMORPHISM_FAILURE = "isomorphism_failure"


def translate_and_prove(
    lean_export_project: LeanProject,
    lean_project: LeanProject | None,
    coq_project: CoqProject,
    coq_statements: CoqFile | None,
) -> tuple[
    LeanProject,
    LeanProject,
    CoqProject,
    bool,
    LeanFile,
    list[tuple[CoqIdentifier, LeanIdentifier]],
]:
    success = False
    error_code, error = None, None  # Used for subsequent attempts of translation

    coq_identifiers = extract_coq_identifiers(coq_statements)
    coq_project, interface_success, error = generate_and_prove_iso_interface(
        coq_project, coq_identifiers
    )
    if not interface_success:
        assert False, "Failed to generate isomorphism interface!"
        error_code = "isomorphism_interface_failure"

    while True:
        # Translate statements from Coq to Lean
        # TBD by all of us, with varying degrees of handholding
        lean_statements, cl_identifiers = translate(coq_statements, error_code, error)

        lean_export_project, lean_project, coq_project, success, error_code, error = (
            check_translation(
                lean_export_project,
                lean_project,
                coq_project,
                lean_statements,
                cl_identifiers,
            )
        )

        # TODO: we might retry this (or control retries from inspect, TBD)
        match error_code:
            case ErrorCode.ISOMORPHISM_FAILURE:
                assert False, "Failed to prove isomorphisms!"
            case ErrorCode.EXPORT_IMPORT_FAILURE:
                assert False, "Importing from Lean to Coq failed!"
            case ErrorCode.COMPILATION_FAILURE:
                assert False, "Lean code does not compile!"
            case None:
                pass

        if success:
            return (
                lean_export_project,
                lean_project,
                coq_project,
                success,
                lean_statements,
                cl_identifiers,
            )


# TODO: Move this (and called functions) to a different file
def check_translation(
    lean_export_project: LeanProject,
    lean_project: LeanProject | None,
    coq_project: CoqProject,
    lean_statements: LeanFile,
    cl_identifiers: list[tuple[CoqIdentifier, LeanIdentifier]],
) -> tuple[
    LeanProject, LeanProject, CoqProject, bool, Optional[ErrorCode], Optional[str]
]:
    success, error_code = False, None
    # Verify that the Lean code compiles
    lean_project, compile_success, error = check_compilation(
        lean_statements, project=lean_project
    )
    # TODO: Use a class derived from Enum or StrEnum
    if not compile_success:
        # TODO: Kick this back to the translator
        error_code = ErrorCode.COMPILATION_FAILURE
        return (
            lean_export_project,
            lean_project,
            coq_project,
            success,
            error_code,
            error,
        )

    # Import statements back into Coq
    lean_export_project, coq_project, reimport_success, cc_identifiers, error = (
        lean_to_coq(lean_export_project, coq_project, lean_statements, cl_identifiers)
    )
    # TODO: Kick this back to the translator (if export failed) or end user (if import failed)
    if not reimport_success:
        error_code = ErrorCode.EXPORT_IMPORT_FAILURE
        return (
            lean_export_project,
            lean_project,
            coq_project,
            success,
            error_code,
            error,
        )

    # Generate and prove isomorphism
    coq_project, iso_success, error = generate_and_prove_iso(
        coq_project, cc_identifiers
    )
    if not iso_success:
        error_code = ErrorCode.ISOMORPHISM_FAILURE
        return (
            lean_export_project,
            lean_project,
            coq_project,
            success,
            error_code,
            error,
        )
    success = True
    return lean_export_project, lean_project, coq_project, success, error_code, error


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
    _, coq_project = CoqProject.read(f"{SOURCE_DIR}/iso-checker").clean()
    lean_export_project = LeanProject.read(EXPORT_DIR)
    (
        lean_export_project,
        lean_project,
        coq_project,
        success,
        lean_statements,
        cl_identifiers,
    ) = translate_and_prove(lean_export_project, None, coq_project, coq_statements)

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
