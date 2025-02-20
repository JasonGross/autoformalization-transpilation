from enum import StrEnum
from pathlib import Path
from typing import Any, Callable, Sequence, TypedDict

import inspect_ai.util
from inspect_ai.solver import TaskState
from inspect_ai.tool import (
    ContentText,
    Tool,
    ToolError,
    ToolResult,
    tool,
)
from inspect_ai.util import Store
from sympy.combinatorics.permutations import Permutation

from config import DEFINITION_PAIRS, EXPORT_DIR, KNOWN_IMPORTS, SOURCE_DIR
from isomorphism_prover import (
    autofix_disordered_constr,
    can_autofix_disordered_constr,
    find_iso_index,
    generate_and_prove_iso,
    generate_and_prove_iso_interface,
    generate_isos,
    has_iso_from,
    has_iso_to,
    llm_suggest_paired_identifier,
    make_identifiers_str,
    make_isos,
    parse_iso_errors,
    repair_missing_type_iso,
)
from main import (
    extract_coq_identifiers,
)
from project_util import (
    CoqFile,
    CoqIdentifier,
    CoqProject,
    DisorderedConstr,
    GenericIsoError,
    IsoError,
    LeanFile,
    LeanIdentifier,
    LeanProject,
    MissingImport,
    MissingTypeIso,
    desigil,
    sigil,
)
from tools.itp import run_lean_str
from translation_checker import (
    check_compilation,
    check_translation,
    import_to_coq,
    lean_to_coq,
)
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
    logging.info(f"Current error type is {type(error).__name__}")

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


@tool
def add_import(
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
) -> Tool:
    async def add_import(import_str: str) -> ToolResult:
        """
        Adds an import to the Coq project.

        Args:
            import_str: The import to be added, for example, "From Coq Require Import List." (str)
        """
        state: ProjectState = inspect_ai.util.store().get("translation_state")
        state["cc_identifiers_blocks"].insert(0, import_str)
        return await generate_and_autorepair_isos(
            original_name=original_name, imported_name=imported_name, iso_file=iso_file
        )

    return add_import


@tool
def remove_import(
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
) -> Tool:
    async def remove_import(code_str: str) -> ToolResult:
        """
        Removes an import or other custom added code from the Coq isomorphism file.

        Args:
            code_str: The line of code to be removed. (str)
        """
        state: ProjectState = inspect_ai.util.store().get("translation_state")
        if code_str not in state["cc_identifiers_blocks"]:
            return ContentText(
                text=f"Invalid code to remove: {code_str!r}\nValid codes to remove are: {'\n'.join(repr(v) for v in state['cc_identifiers_blocks'] if isinstance(v, str))}"
            )
        state["cc_identifiers_blocks"].remove(code_str)
        return await generate_and_autorepair_isos(
            original_name=original_name, imported_name=imported_name, iso_file=iso_file
        )

    return remove_import


def handle_value_error(
    cc_identifiers_blocks: list[str | tuple[CoqIdentifier, CoqIdentifier, str | None]],
    iso_source: str,
    iso_target: str | None = None,
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
) -> ContentText:
    cc_ids_str = [
        (s, t)
        for s, t in make_identifiers_str(
            cc_identifiers_blocks,
            original_name=original_name,
            imported_name=imported_name,
        )
        if s is not None
    ]
    if iso_target is not None:
        valid_identifiers = ", ".join(v for v, _ in cc_ids_str)
        return ContentText(
            text=f"Failed to find identifier {iso_source} in the isomorphism list; valid identifiers are: {valid_identifiers}"
        )
    else:
        valid_identifiers = "; ".join(f"({s}, {t})" for s, t in cc_ids_str)
        return ContentText(
            text=f"Failed to find isomorphism for {iso_source} to {iso_target} in the isomorphism list; valid pairs are: {valid_identifiers}"
        )


@tool
def add_lemma(
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
) -> Tool:
    async def add_lemma(
        code_str: str, before_source: str, before_target: str | None = None
    ) -> ToolResult:
        """
        Adds a Coq lemma to the Coq project isomorphism file.

        Args:
            code_str: The Coq code to be added. (str)
            before_source: The source identifier before which the lemma should be added. (str)
            before_target: The target identifier before which the lemma should be added. Optional. (str|None)
        """
        state: ProjectState = inspect_ai.util.store().get("translation_state")
        try:
            index = find_iso_index(
                state["cc_identifiers_blocks"],
                before_source,
                before_target,
                original_name=original_name,
                imported_name=imported_name,
            )
        except ValueError:
            return handle_value_error(
                state["cc_identifiers_blocks"],
                before_source,
                before_target,
                original_name=original_name,
                imported_name=imported_name,
            )

        state["cc_identifiers_blocks"].insert(index, code_str)

        return await generate_and_autorepair_isos(
            original_name=original_name, imported_name=imported_name, iso_file=iso_file
        )

    return add_lemma


@tool
def add_iso(
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
) -> Tool:
    async def add_iso(source: str, target: str, before_source: str) -> ToolResult:
        """
        Adds an isomorphism statement to the Coq project.

        Args:
            source: The source identifier for the isomorphism. (str)
            target: The target identifier for the isomorphism. (str)
            before_source: The source identifier before which the isomorphism should be added. (str)
        """
        state: ProjectState = inspect_ai.util.store().get("translation_state")

        try:
            index = find_iso_index(
                state["cc_identifiers_blocks"],
                before_source,
                original_name=original_name,
                imported_name=imported_name,
            )
        except ValueError:
            return handle_value_error(
                state["cc_identifiers_blocks"],
                before_source,
                original_name=original_name,
                imported_name=imported_name,
            )

        new_soruce = CoqIdentifier(source)
        new_target = CoqIdentifier(target)
        block = state["cc_identifiers_blocks"][index]
        assert not isinstance(block, str), block
        logging.info(
            f"Adding iso_statement {source}, {target} for {str(block[0])}, {str(block[1])}"
        )
        state["cc_identifiers_blocks"].insert(index, (new_soruce, new_target, None))

        return await generate_and_autorepair_isos(
            original_name=original_name, imported_name=imported_name, iso_file=iso_file
        )

    return add_iso


async def edit_proof_higher_order(
    iso_source: str,
    new_proof: Callable[[tuple[CoqIdentifier, CoqIdentifier, str | None]], str],
    iso_target: str | None = None,
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
) -> ToolResult:
    """
    Reorders the constructors of an isomorphism proof based on a given permutation.

    Args:
        iso_source: The source identifier for the isomorphism block to be reordered. (str)
        new_proof: The new proof for the isomorphism block, taking in the old source, target, and proof and returning the new proof. (Callable)
        iso_target: The target identifier for the isomorphism block to be reordered. Optional. (str|None)
    """
    state = inspect_ai.util.store().get("translation_state")
    try:
        index = find_iso_index(
            state["cc_identifiers_blocks"],
            iso_source,
            iso_target,
            original_name=original_name,
            imported_name=imported_name,
        )
    except ValueError:
        return handle_value_error(
            state["cc_identifiers_blocks"],
            iso_source,
            iso_target,
            original_name=original_name,
            imported_name=imported_name,
        )

    block = state["cc_identifiers_blocks"][index]
    assert not isinstance(block, str), block
    cur_proof = block[2]
    new_proof_str = new_proof(block).strip()

    # Be a bit more lenient with the proof string, and strip off the Proof. and Qed. parts
    if new_proof_str.startswith("Proof."):
        new_proof_str = new_proof_str[len("Proof.") :]
    if new_proof_str.endswith("Qed."):
        new_proof_str = new_proof_str[: -len("Qed.")]
    if new_proof_str.endswith("Defined."):
        new_proof_str = new_proof_str[: -len("Defined.")]
    new_proof_str = new_proof_str.strip()

    reordered_block = (
        block[0],
        block[1],
        new_proof_str,
    )
    state["cc_identifiers_blocks"][index] = reordered_block
    logging.info(
        f"Reordered constructors for {iso_source} ({block[0]}) to {block[1]}, new proof is {new_proof_str}, old proof was {cur_proof}"
    )

    return await generate_and_autorepair_isos(
        original_name=original_name, imported_name=imported_name, iso_file=iso_file
    )


@tool
def edit_proof(
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
) -> Tool:
    async def edit_proof(
        iso_source: str, new_proof: str, iso_target: str | None = None
    ) -> ToolResult:
        """
        Reorders the constructors of an isomorphism proof based on a given permutation.

        Args:
            iso_source: The source identifier for the isomorphism block to be reordered. (str)
            new_proof: The new proof for the isomorphism block. (str)
            iso_target: The target identifier for the isomorphism block to be reordered. Optional. (str|None)
        """
        return await edit_proof_higher_order(
            iso_source,
            lambda block: new_proof,
            iso_target=iso_target,
            original_name=original_name,
            imported_name=imported_name,
            iso_file=iso_file,
        )

    return edit_proof


@tool
def repair_iso_by_reorder_constructors(
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
) -> Tool:
    async def repair_iso_by_reorder_constructors(
        permutation: list[int], source: str
    ) -> ToolResult:
        """
        Reorders the constructors of an isomorphism proof based on a given permutation.

        Args:
            permutation: The new order for the constructors. (list[int])
            source: The source identifier for the isomorphism block to be reordered. (str)
        """

        def new_proof(block: tuple[CoqIdentifier, CoqIdentifier, str | None]):
            _, _, cur_proof = block
            logging.info(f"Reordering constructors using permutation {permutation}")
            permutation_obj: Permutation = Permutation(permutation)
            if cur_proof is not None and "revgoals" in cur_proof:
                permutation_obj = permutation_obj.inverse()
            transpositions = permutation_obj.transpositions()

            inverse_transpositions = permutation_obj.inverse().transpositions()
            transpose_tactic = " ".join(
                f"all: swap {i + 1} {j + 1}." for i, j in transpositions
            )
            inverse_transpose_tactic = " ".join(
                f"all: swap {i + 1} {j + 1}." for i, j in inverse_transpositions
            )

            return f"""start_iso.
    {{ start_step_iso. {transpose_tactic} finish_step_iso. }}
    {{ symmetrize_rel_iso; start_step_iso. {inverse_transpose_tactic} all: finish_step_iso. }}
    {{ start_iso_proof; step_iso_proof_full. }}
    {{ symmetrize_rel_iso; start_iso_proof; step_iso_proof_full. }}"""

        return await edit_proof_higher_order(
            source,
            new_proof,
            original_name=original_name,
            imported_name=imported_name,
            iso_file=iso_file,
        )

    return repair_iso_by_reorder_constructors


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
    init_coq_project["Interface.v"] = CoqFile("")
    init_coq_project["Checker.v"] = CoqFile("")
    if init_coq_targets is not None:
        if isinstance(init_coq_targets, str):
            init_coq_targets = [init_coq_targets]
        result, coq_project = init_coq_project.make(*init_coq_targets)
        assert result.returncode == 0, (
            f"Failed to make Coq project with init targets {init_coq_targets}:\nstdout:\n```\n{result.stdout}\n```\nstderr:\n```\n{result.stderr}\n```"
        )
    init_lean_export_project = LeanProject.read(lean_export_directory)

    coq_identifiers = extract_coq_identifiers(coq_statements_file, sigil=False)
    init_coq_project, interface_success, error = generate_and_prove_iso_interface(
        init_coq_project, list(map(sigil, coq_identifiers))
    )
    assert interface_success, f"Failed to generate and prove interface:\n{error}"

    async def translate(lean_code: str, coq_lean_identifiers: dict[str, str]):
        """
        Submits the given Lean 4 code as the result of translation, with paired identifiers between the Coq and Lean code.

        Args:
            lean_code: Lean code to be run (str)
            coq_lean_identifiers: Mapping of Coq identifiers to the corresponding translated Lean identifier (dict[str, str])

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
{result["stderr"]}"""
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
{result["stderr"]}"""
            )

        return await generate_and_autorepair_isos()

    return translate
