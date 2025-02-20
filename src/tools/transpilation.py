from pathlib import Path
from typing import Any, Sequence, TypedDict
from enum import StrEnum
from inspect_ai.tool import (
    tool,
    Tool,
    ToolError,
    ToolResult,
    ContentText,
    ToolError,
    ToolResult,
    tool,
)
import inspect_ai.util
from inspect_ai.util import Store
from inspect_ai.solver import TaskState

from config import EXPORT_DIR, SOURCE_DIR
from main import (
    DEFINITION_PAIRS,
    KNOWN_IMPORTS,
    DisorderedConstr,
    GenericIsoError,
    IsoError,
    LeanFile,
    MissingImport,
    MissingTypeIso,
    autofix_disordered_constr,
    can_autofix_disordered_constr,
    check_compilation,
    check_translation,
    desigil,
    extract_coq_identifiers,
    find_iso_index,
    generate_and_prove_iso,
    generate_and_prove_iso_interface,
    generate_isos,
    has_iso_from,
    has_iso_to,
    import_to_coq,
    lean_to_coq,
    llm_suggest_paired_identifier,
    make_isos,
    parse_iso_errors,
    repair_missing_type_iso,
)
from project_util import CoqFile, CoqIdentifier, CoqProject, LeanIdentifier, LeanProject
from tools.itp import run_lean_str
from utils import logging


class LeanError(Exception):
    pass


class ModelResponseError(Exception):
    pass


class CompilationPhase(StrEnum):
    LEAN_COMPILATION = "lean compilation"


class LeanCompilationResult(TypedDict):
    status: bool
    stdout: str
    suggestion: str
    stderr: str | None
    failure_phase: CompilationPhase | None
    error: IsoError | None
    unknown_lhs_identifiers: list[str]
    unknown_rhs_identifiers: list[str]


class ProjectState(TypedDict):
    result: LeanCompilationResult
    coq_project: CoqProject
    lean_export_project: LeanProject
    coq_identifiers: list[CoqIdentifier]
    cc_identifiers_blocks: list[str | tuple[CoqIdentifier, CoqIdentifier, str | None]]
    cl_identifiers: list[tuple[CoqIdentifier, LeanIdentifier]]
    lean_statements: LeanFile
    lean_project: LeanProject
    missing_identifiers: list[CoqIdentifier]
    excess_identifiers: list[tuple[str, str]]


async def generate_and_autorepair_isos(
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
) -> ToolResult:
    state: ProjectState = inspect_ai.util.store().get("translation_state")
    state["result"] = {
        "status": False,
        "suggestion": "",
        "stdout": "",
        "stderr": "",
        "failure_phase": None,
        "error": None,
        "unknown_lhs_identifiers": [],
        "unknown_rhs_identifiers": [],
    }
    result = state["result"]

    state["coq_project"] = generate_isos(
        state["coq_project"],
        state["cc_identifiers_blocks"],
        original_name=original_name,
        imported_name=imported_name,
        output_file=iso_file,
    )

    # Check that the iso proof compiles
    state["coq_project"], result["status"], result["stderr"] = make_isos(
        state["coq_project"], "Checker.vo"
    )
    if result["status"]:
        return ContentText(text="Success!")

    assert result["stderr"] is not None, state

    logging.info("Isomorphism proof failed to compile, attempting to repair...")

    error = result["error"] = parse_iso_errors(result["stderr"])
    logging.info(f"Current error type is {type(error)}")

    if isinstance(error, MissingTypeIso):
        state["coq_project"], state["cc_identifiers_blocks"] = repair_missing_type_iso(
            state["coq_project"],
            error,
            state["cc_identifiers_blocks"],
            original_name=original_name,
            imported_name=imported_name,
            iso_file=iso_file,
        )
        return await generate_and_autorepair_isos(
            original_name=original_name, imported_name=imported_name, iso_file=iso_file
        )
    elif isinstance(error, MissingImport):
        if error.import_str in KNOWN_IMPORTS:
            logging.info(
                f"Adding import {KNOWN_IMPORTS[error.import_str]} for iso_statement {error.orig_source} {error.orig_target}"
            )
            state["cc_identifiers_blocks"].insert(
                0,
                KNOWN_IMPORTS[error.import_str],
            )
            return await generate_and_autorepair_isos(
                original_name=original_name,
                imported_name=imported_name,
                iso_file=iso_file,
            )
        else:
            return ContentText(
                text=f"Failed to prove isomorphisms because of missing import, please invoke the add_import tool with an import to make available the missing reference {error.import_str}"
            )
    elif isinstance(error, DisorderedConstr):
        if can_autofix_disordered_constr(
            error,
            state["cc_identifiers_blocks"],
            original_name=original_name,
            imported_name=imported_name,
        ):
            state["coq_project"], state["cc_identifiers_blocks"] = (
                autofix_disordered_constr(
                    state["coq_project"],
                    error,
                    state["cc_identifiers_blocks"],
                    original_name=original_name,
                    imported_name=imported_name,
                    iso_file=iso_file,
                )
            )
            return await generate_and_autorepair_isos(
                original_name=original_name,
                imported_name=imported_name,
                iso_file=iso_file,
            )
        else:
            return ContentText(
                text=f"Failed to prove isomorphism between {error.orig_source} and {error.orig_target} because the constructors are out of order.  This can be fixed by invoking the repair_iso_by_reorder_constructors tool with a permutation. The constructor misalignment is: {error.hint}"
            )
    elif isinstance(error, GenericIsoError):
        index = find_iso_index(
            state["cc_identifiers_blocks"],
            error.orig_source,
            error.orig_target,
            original_name=original_name,
            imported_name=imported_name,
        )
        unknown_lhs = [
            cst
            for cst in error.unknown_lhs
            if not has_iso_from(
                state["cc_identifiers_blocks"],
                cst,
                original_name=original_name,
                imported_name=imported_name,
            )
        ]
        unknown_rhs = [
            cst
            for cst in error.unknown_rhs
            if not has_iso_to(
                state["cc_identifiers_blocks"],
                cst,
                original_name=original_name,
                imported_name=imported_name,
            )
        ]
        missing_iso_text = ""
        if unknown_lhs and unknown_rhs:
            missing_iso_text = f"""

This might be because we are missing an isomorphism between some identifier that we unfolded on the left and some identifier we unfolded on the right.  If this is the case, you can invoke the add_iso tool with the pair of identifiers, indicating that it should come before the isomorphism for {error.orig_source}. The candidates for missing isomorphisms are:
left: {unknown_lhs}
right: {unknown_rhs}
"""
        return ContentText(
            text=f"""Failed to prove isomorphism between {error.orig_source} and {error.orig_target}.
{missing_iso_text}

You might need to adjust the isomorphism proof of the isomorphism using the update_iso_proof tool with the new proof. Here is some information that might help diagnose the rewriting:
```
{error.prefix}
```
There remain {error.ngoals} goals unsolved:
```
{error.goals}
```
"""
        )
    else:
        raise ToolError(f"Unknown error type {type(error)}: {error}")


# TODO: add_import tool
# TODO: add_iso tool
# TODO: repair_iso_by_reorder_constructors tool


@tool
def transpilation_tool(
    coq_statements: str | None = None,
    iso_checker_path: str | Path = f"{SOURCE_DIR}/iso-checker",
    init_coq_targets: str | Sequence[str] | None = "Automation.vo",
    lean_export_directory: str | Path = EXPORT_DIR,
) -> Tool:

    coq_statements_file = None if coq_statements is None else CoqFile(coq_statements)

    _, init_coq_project = CoqProject.read(iso_checker_path).clean()
    # set some dummy files so that the makefile doesn't fail
    init_coq_project["Isomorphisms.v"] = CoqFile("")
    if init_coq_targets is not None:
        if isinstance(init_coq_targets, str):
            init_coq_targets = [init_coq_targets]
        result, coq_project = init_coq_project.make(*init_coq_targets)
        assert (
            result.returncode == 0
        ), f"Failed to make Coq project with init targets {init_coq_targets}:\nstdout:\n```\n{result.stdout}\n```\nstderr:\n```\n{result.stderr}\n```"
    init_lean_export_project = LeanProject.read(lean_export_directory)

    coq_identifiers = extract_coq_identifiers(coq_statements_file, sigil=False)
    init_coq_project, interface_success, error = generate_and_prove_iso_interface(
        init_coq_project, coq_identifiers
    )
    assert interface_success, f"Failed to generate and prove interface:\n{error}"

    async def translate(lean_code: str, coq_lean_identifiers: dict[str, str]):
        """
        Submits the given Lean 4 code as the result of translation, with paired identifiers between the Coq and Lean code.

        Args:
            lean_code (str): Lean code to be run
            coq_lean_identifiers (dict[str, str]): Mapping of Coq identifiers to the corresponding translated Lean identifier

        Returns:
            ToolResult: Messages that came up during execution
        """
        store = inspect_ai.util.store()
        if "translation_state" not in store:
            store.set("translation_state", {})
        state: ProjectState = store.get("translation_state")
        state["result"] = {
            "status": False,
            "suggestion": "",
            "stdout": "",
            "stderr": "",
            "failure_phase": None,
            "error": None,
            "unknown_lhs_identifiers": [],
            "unknown_rhs_identifiers": [],
        }
        result = state["result"]
        if "lean_export_project" not in state:
            state["lean_export_project"] = init_lean_export_project
        if "coq_project" not in state:
            state["coq_project"] = init_coq_project
        if "coq_identifiers" not in state:
            state["coq_identifiers"] = coq_identifiers

        state["lean_statements"] = LeanFile(lean_code)
        # Verify that the Lean code compiles
        state["lean_project"], result["status"], result["stderr"] = check_compilation(
            state["lean_statements"], project=None
        )
        if not result["status"]:
            result["suggestion"] = "Lean code failed to compile."
            result["failure_phase"] = CompilationPhase.LEAN_COMPILATION
            return ContentText(
                text=f"""Lean code failed to compile:
{result['stderr']}"""
            )

        state["cl_identifiers"] = [
            (CoqIdentifier(f"${k}"), LeanIdentifier(f"${coq_lean_identifiers[str(k)]}"))
            for k in coq_identifiers
            if str(k) in coq_lean_identifiers
        ]
        state["missing_identifiers"] = [
            k for k in coq_identifiers if str(k) not in coq_lean_identifiers
        ]
        state["excess_identifiers"] = [
            (k, v) for k, v in coq_lean_identifiers.items() if k not in coq_identifiers
        ]

        (
            state["lean_export_project"],
            state["coq_project"],
            result["status"],
            cc_identifiers_blocks,
            result["stderr"],
        ) = lean_to_coq(
            state["lean_export_project"],
            state["coq_project"],
            state["lean_statements"],
            state["cl_identifiers"],
        )
        state["cc_identifiers_blocks"] = list(cc_identifiers_blocks)

        if not result["status"]:
            raise ToolError(
                f"""Lean code failed to import to Coq (please summon a wizard):
{result['stderr']}"""
            )

        return await generate_and_autorepair_isos()

    return translate
