import contextlib
from copy import deepcopy
from subprocess import CompletedProcess
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
    desigil,
)
from utils import logging, run_cmd
from utils.memoshelve import cache, hash_as_tuples


class ErrorCode(StrEnum):
    COMPILATION_FAILURE = "compilation_failure"
    EXPORT_IMPORT_FAILURE = "export_import_failure"
    ISOMORPHISM_FAILURE = "isomorphism_failure"


def lean_id_to_coq(lean_id: LeanIdentifier) -> CoqIdentifier:
    return CoqIdentifier(str(lean_id).replace(".", "_"))


def import_to_coq(
    project: CoqProject, lean_export: ExportFile, *, coq_file_stem: str = "target"
) -> tuple[CoqProject, bool, str]:
    # Copy files first
    project = project.copy()
    project[f"{coq_file_stem}.out"] = lean_export

    project[f"{coq_file_stem}.v"] = coq_import_file = CoqFile(
        f"""From LeanImport Require Import Lean.
Redirect "{coq_file_stem}.log" Lean Import "{coq_file_stem}.out"."""
    )

    # Then run coqc and check its status
    # Plausibly we should be generating a list of statements ready for the isomorphism proofs
    # But for now we just check the status
    result, project = project.run_cmd(
        ["coqc", f"{coq_file_stem}.v"], check=False, shell=False
    )
    if result.returncode == 0:
        return project, True, ""
    else:
        if f"{coq_file_stem}.log" in project:
            coq_log = f"""Log:
```
{project[f"{coq_file_stem}.log"].contents}
```
"""
        else:
            coq_log = ""
        msg = f"""Coq compilation failed, summon a wizard:
Lean export:
```
{lean_export.contents}
```
Coq project:
```coq
{coq_import_file.contents}
```
{coq_log}
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
    *,
    coq_import_file_stem: str = "target",
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
        lean_to_coq(
            lean_export_project,
            coq_project,
            lean_statements,
            cl_identifiers,
            coq_file_stem=coq_import_file_stem,
        )
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


@cache(get_hash=hash_as_tuples, copy=deepcopy)
def new_lake_project(name: str = "lean-build") -> LeanProject:
    with tempfile.TemporaryDirectory() as tempdir:
        tempdir = Path(tempdir)
        (tempdir / name).mkdir()
        with contextlib.chdir(tempdir):
            run_cmd(["lake", "new", name], check=False, shell=False)
        return LeanProject.read(tempdir / name)


@cache(get_hash=hash_as_tuples, copy=deepcopy)
def check_compilation(
    lean_statements: LeanFile, project: LeanProject | None = None
) -> tuple[LeanProject, bool, str]:
    if project is None:
        project = new_lake_project(name="lean-build")
    else:
        project = project.copy()

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
    *,
    coq_file_stem: str = "target",
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
    lean_project, export_success, lean_export, result = export_from_lean(
        lean_project, [d for _, d in identifiers]
    )
    cc_identifiers = []
    if not export_success:
        logging.error(f"Lean export failed: {result.stderr}")
        return lean_project, coq_project, False, [], result.stderr
    # Import statements back into Coq
    for coq_id, lean_id in identifiers:
        cc_identifiers.append((coq_id, lean_id_to_coq(lean_id), None))

    coq_project, success, error = import_to_coq(
        coq_project, lean_export, coq_file_stem=coq_file_stem
    )
    return lean_project, coq_project, success, cc_identifiers, error


@cache(get_hash=hash_as_tuples, copy=deepcopy)
def export_from_lean(
    project: LeanProject, definitions: list[LeanIdentifier]
) -> tuple[LeanProject, bool, ExportFile, CompletedProcess[str]]:
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
        # we shouldn't have to rm -rf .lake, but it seems to be necessary
        result = run_cmd(
            f"rm -rf .lake && lake update && lake build", shell=True, check=False
        )
        if result.returncode != 0:
            project.write(Path(__file__).parent.parent / "temp_export_lean")
            logging.error(f"Compilation failed: {result.stderr}")
            return project, False, ExportFile(""), result

        # Run Lake exe export to get the exported code
        cmd = ["lake", "exe", "lean4export", "Main", "--"]
        raw_definitions = [desigil(str(definition)) for definition in definitions]
        cmd.extend(raw_definitions)

        # # Produce .out file
        logging.info(f"Exporting: {raw_definitions}")
        result = run_cmd(cmd, shell=False, check=False)
        if result.returncode != 0:
            lean_files = {k: v for k, v in project.items() if k.endswith(".lean")}
            project.write(Path(__file__).parent.parent / "temp_export_lean")
            logging.error(f"Export failed on {cmd} on {lean_files}: {result.stderr}")
            return project, False, ExportFile(""), result
        export_file = ExportFile(result.stdout)
        logging.debug(f"Export file: {export_file.contents}")
        return LeanProject.read("."), True, export_file, result
