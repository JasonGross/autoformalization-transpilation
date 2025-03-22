import contextlib
import tempfile
from copy import deepcopy
from enum import StrEnum
from pathlib import Path
from subprocess import CompletedProcess
from typing import Collection, Sequence

from config import DEFINITION_PAIRS, EXPORT_DIR, SOURCE_DIR
from isomorphism_prover import (
    add_files_to_CoqProject,
    generate_and_prove_iso_interface,
    init_coq_project,
)
from project_util import (
    CoqFile,
    CoqIdentifier,
    CoqProject,
    ExportFile,
    IsoBlock,
    LeanFile,
    LeanIdentifier,
    LeanProject,
    add_identifier_prefix,
    coq_identifiers_of_list,
    extract_coq_identifiers,
)
from utils import logging, run_cmd
from utils.memoshelve import cache


class ErrorCode(StrEnum):
    COMPILATION_FAILURE = "compilation_failure"
    EXPORT_IMPORT_FAILURE = "export_import_failure"
    ISOMORPHISM_FAILURE = "isomorphism_failure"


def lean_id_to_coq(
    lean_id: LeanIdentifier, *, imported_name: str = "Imported"
) -> CoqIdentifier:
    return CoqIdentifier(
        add_identifier_prefix(str(lean_id).replace(".", "_"), prefix=imported_name)
    )


def import_to_coq(
    project: CoqProject, lean_export: ExportFile, *, coq_file_stem: str = "target"
) -> tuple[CoqProject, bool, str]:
    # Copy files first
    project = project.copy()
    project[f"{coq_file_stem}.out"] = lean_export
    project.debug_files.add(f"{coq_file_stem}.out")

    project[f"{coq_file_stem}.v"] = coq_import_file = CoqFile(
        f"""From LeanImport Require Import Lean.
Redirect "{coq_file_stem}.log" Lean Import "{coq_file_stem}.out"."""
    )
    project = add_files_to_CoqProject(project, f"{coq_file_stem}.v")
    try:
        del project[f"{coq_file_stem}.vo"]
    except KeyError:
        pass

    # Then run coqc and check its status
    # Plausibly we should be generating a list of statements ready for the isomorphism proofs
    # But for now we just check the status
    result, project = project.run_cmd(
        ["coqc", "-q", f"{coq_file_stem}.v"],
        check=False,
        shell=False,
        sanitize="/tmp/import_to_coq",
    )
    try:
        del project[f"{coq_file_stem}.vo"]
    except KeyError:
        pass
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

    # Put new code in the right place
    project["LeanBuild/Basic.lean"] = lean_statements
    project["Main.lean"] = LeanFile(
        """import LeanBuild
def main : IO Unit :=
 IO.println s!"Compilation succeeded!"
"""
    )

    # Then build
    _result, project = project.run_cmd(
        ["lake", "update"], shell=False, check=False, sanitize="/tmp/check_compilation"
    )
    result, project = project.run_cmd(
        ["lake", "build"], shell=False, check=False, sanitize="/tmp/check_compilation"
    )
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
    imported_name: str = "Imported",
    coq_identifiers_to_unfold: Collection[CoqIdentifier] = (),
) -> tuple[
    LeanProject,
    CoqProject,
    bool,
    list[IsoBlock],
    str,
]:
    lean_project = lean_project.copy()

    # Construct a Lean file from all our snippets
    lean_project["Origin.lean"] = statements

    # Export statements from Lean
    lean_project, export_success, lean_export, result = export_from_lean(
        lean_project, [d for _, d in identifiers]
    )
    cc_identifiers: list[IsoBlock] = []
    if not export_success:
        logging.error(f"Lean export failed: {result.stderr}")
        return lean_project, coq_project, False, [], result.stderr
    # Import statements back into Coq
    for coq_id, lean_id in identifiers:
        cc_identifiers.append(
            IsoBlock(
                coq_id,
                lean_id_to_coq(lean_id, imported_name=imported_name),
                is_interface=True,
                is_original=True,
                needs_unfolding=coq_id in coq_identifiers_to_unfold,
            )
        )

    coq_project, success, error = import_to_coq(
        coq_project, lean_export, coq_file_stem=coq_file_stem
    )
    return lean_project, coq_project, success, cc_identifiers, error


@cache(copy=deepcopy)
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
        raw_definitions = [str(definition) for definition in definitions]
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


def init_translation_project(
    coq_statements: str | None = None,
    coq_names: list[str] | None = None,
    *,
    iso_checker_path: str | Path = f"{SOURCE_DIR}/iso-checker",
    init_coq_targets: str | Sequence[str] | None = "Automation.vo",
    lean_export_directory: str | Path = EXPORT_DIR,
    original_name: str = "Original",
) -> tuple[CoqProject, LeanProject, list[CoqIdentifier], list[CoqIdentifier]]:
    coq_statements_file = None if coq_statements is None else CoqFile(coq_statements)

    coq_project = init_coq_project(iso_checker_path)
    if coq_statements_file is not None:
        coq_project[f"{original_name}.v"] = coq_statements_file
        coq_project = add_files_to_CoqProject(coq_project, f"{original_name}.v")
    if init_coq_targets is not None:
        if isinstance(init_coq_targets, str):
            init_coq_targets = [init_coq_targets]
        result, coq_project = coq_project.make(
            *init_coq_targets, sanitize="/tmp/init_translation_project"
        )
        assert result.returncode == 0, (
            f"Failed to make Coq project with init targets {init_coq_targets}:\nstdout:\n```\n{result.stdout}\n```\nstderr:\n```\n{result.stderr}\n```"
        )
    lean_export_project = LeanProject.read(lean_export_directory)

    if coq_names is None:
        coq_identifiers = extract_coq_identifiers(
            coq_statements_file,
            default_definition_pairs=DEFINITION_PAIRS,
            prefix=original_name,
        )
        assert coq_identifiers, f"No Coq identifiers found in {coq_statements}"
    else:
        coq_identifiers = coq_identifiers_of_list(coq_names, prefix=original_name)
        assert coq_identifiers, f"No Coq identifiers found in {coq_names}"

    (
        coq_project,
        interface_success,
        error,
        coq_identifiers,
        coq_identifiers_to_unfold,
    ) = generate_and_prove_iso_interface(coq_project, coq_identifiers)
    assert interface_success, f"Failed to generate and prove interface:\n{error}"

    return coq_project, lean_export_project, coq_identifiers, coq_identifiers_to_unfold
