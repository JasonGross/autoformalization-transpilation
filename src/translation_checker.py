import contextlib
from copy import deepcopy
import tempfile
from enum import StrEnum
from pathlib import Path
from typing import Optional

from isomorphism_prover import generate_and_prove_iso
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


class ErrorCode(StrEnum):
    COMPILATION_FAILURE = "compilation_failure"
    EXPORT_IMPORT_FAILURE = "export_import_failure"
    ISOMORPHISM_FAILURE = "isomorphism_failure"


def lean_id_to_coq(lean_id: LeanIdentifier) -> CoqIdentifier:
    return CoqIdentifier(str(lean_id).replace(".", "_"))


def import_to_coq(
    project: CoqProject, lean_export: ExportFile, coq_file: str = "target"
) -> tuple[CoqProject, bool, str]:
    # Copy files first
    project = project.copy()
    project[f"{coq_file}.out"] = lean_export

    project[f"{coq_file}.v"] = coq_import_file = CoqFile(
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
        msg = f"""Coq compilation failed, summon a wizard:
Lean export:
```
{lean_export.contents}
```
Coq project:
```coq
{coq_import_file.contents}
```
retcode: {result.returncode}
stdout:
```
{result.stdout}
```
stderr:
```
{result.stderr}
```
"""
        logging.error(msg)
        # TODO: Actually retrieve error, for example look at result.stderr, search for the last
        # instance of 'File "[^"]+", line ([0-9]+), characters ([0-9]+)-([0-9]+):\n', pick out the
        #  line numbers from the file, so the LLM doesn't have to do arithmetic
        return project, False, msg


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
        coq_project, list(cc_identifiers)
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


@cache(copy=deepcopy)
def new_lake_project(name: str = "lean-build") -> LeanProject:
    with tempfile.TemporaryDirectory() as tempdir:
        tempdir = Path(tempdir)
        (tempdir / name).mkdir()
        with contextlib.chdir(tempdir):
            run_cmd(["lake", "new", name], check=False, shell=False)
        return LeanProject.read(tempdir / name)


@cache(copy=deepcopy)
def check_compilation(
    lean_statements: LeanFile, project: LeanProject | None = None
) -> tuple[LeanProject, bool, str]:
    if project is None:
        project = new_lake_project(name="lean-build")
    else:
        project = project.copy()

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
    _result, project = project.run_cmd(["lake", "update"], shell=False, check=False)
    result, project = project.run_cmd(["lake", "build"], shell=False, check=False)

    if result.returncode != 0:
        error_message = f"{result.stdout}\n{result.stderr}".strip()
        logging.error(f"Compilation failed: {error_message}")
        return project, False, error_message
    return project, True, ""


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


def extract_definitions(file: LeanFile) -> list[LeanIdentifier]:
    # TODO: Actually do something with Origin.lean
    # For now, just do this
    lst = "Binop Exp Instr Prog Stack binopDenote expDenote instrDenote progDenote compile compileOneInstrStatement compileCorrect binOpComm reverseMerge compileOpComm constEq constInsEq constOnlyConst listEq constCmpl"
    definitions = lst.split()
    return list(map(LeanIdentifier, definitions))


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
