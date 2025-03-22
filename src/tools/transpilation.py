import datetime
from copy import deepcopy
from enum import StrEnum
from pathlib import Path
from typing import Callable, Sequence, TypedDict

import inspect_ai.util
from inspect_ai.tool import (
    ContentText,
    Tool,
    ToolError,
    ToolResult,
    tool,
)
from sympy.combinatorics.permutations import Permutation

from config import EXPORT_DIR, SOURCE_DIR
from isomorphism_prover import (
    IsoAlreadyExistsError,
    find_iso_and_index,
    find_iso_index,
    generate_and_autorepair_isos,
    insert_iso,
    make_identifiers_str,
)
from project_util import (
    AmbiguousIsoError,
    CoqIdentifier,
    CoqProject,
    DisorderedConstr,
    GenericIsoError,
    IsoBlock,
    IsoError,
    IsoErrorWithoutHints,
    LeanFile,
    LeanIdentifier,
    LeanProject,
    MissingImport,
    MissingTypeIso,
    NonIsoBlockError,
    remove_identifier_prefix,
)
from translation_checker import (
    check_compilation,
    init_translation_project,
    lean_to_coq,
)
from utils import logging
from utils.inspect_utils import handle_none_string

_DEFAULT_WRITE_TO_DIRECTORY_ON_ERROR = (
    Path(__file__).parent.parent.parent / "temp_transpilation_errors"
)


class LeanError(Exception):
    pass


class ModelResponseError(Exception):
    pass


class CompilationPhase(StrEnum):
    LEAN_COMPILATION = "lean compilation"
    PROVING_ISOS = "proving isomorphisms"


class LeanCompilationResult(TypedDict):
    status: bool
    stdout: str
    suggestion: str
    stderr: str | None
    failure_phase: CompilationPhase | None
    error: IsoError | None
    unknown_lhs_identifiers: list[str]
    unknown_rhs_identifiers: list[str]


_coq_project_map: list[CoqProject] = []
_lean_export_project_map: list[LeanProject] = []
_lean_project_map: list[LeanProject] = []


class ProjectState(TypedDict):
    result: LeanCompilationResult
    coq_project_id: int
    lean_export_project_id: int
    coq_identifiers: list[CoqIdentifier]
    coq_identifiers_to_unfold: list[CoqIdentifier]
    cc_identifiers_blocks: list[str | IsoBlock]
    cl_identifiers: list[tuple[CoqIdentifier, LeanIdentifier]]
    lean_statements: LeanFile
    lean_project_id: int
    missing_identifiers: list[CoqIdentifier]
    excess_identifiers: list[tuple[str, str]]


def get_coq_project() -> CoqProject:
    state: ProjectState = inspect_ai.util.store().get("translation_state")
    return _coq_project_map[state["coq_project_id"]]


def set_coq_project(coq_project: CoqProject):
    state: ProjectState = inspect_ai.util.store().get("translation_state")
    state["coq_project_id"] = len(_coq_project_map)
    _coq_project_map.append(coq_project)


def get_lean_export_project() -> LeanProject:
    state: ProjectState = inspect_ai.util.store().get("translation_state")
    return _lean_export_project_map[state["lean_export_project_id"]]


def set_lean_export_project(lean_export_project: LeanProject):
    state: ProjectState = inspect_ai.util.store().get("translation_state")
    state["lean_export_project_id"] = len(_lean_export_project_map)
    _lean_export_project_map.append(lean_export_project)


def get_lean_project() -> LeanProject:
    state: ProjectState = inspect_ai.util.store().get("translation_state")
    return _lean_project_map[state["lean_project_id"]]


def set_lean_project(lean_project: LeanProject):
    state: ProjectState = inspect_ai.util.store().get("translation_state")
    state["lean_project_id"] = len(_lean_project_map)
    _lean_project_map.append(lean_project)


def generate_and_autorepair_isos_tool(
    *,
    admit_failing_isos: bool = False,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
    write_to_directory_on_error: Path | str | None,
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
    coq_project = get_coq_project()

    try:
        (
            coq_project,
            state["cc_identifiers_blocks"],
            result["status"],
            result["error"],
        ) = generate_and_autorepair_isos(
            coq_project,
            state["cc_identifiers_blocks"],
            admit_failing_isos=admit_failing_isos,
            original_name=original_name,
            imported_name=imported_name,
            iso_file=iso_file,
            write_to_directory_on_error=write_to_directory_on_error,
        )
    except (AssertionError, ValueError) as e:
        new_exn = ToolError(str(e))
        # Remove the error message from the assertion error, we are already printing it
        e.args = ()
        raise new_exn from e

    set_coq_project(coq_project)
    if result["status"]:
        return ContentText(text="Success!")

    result["failure_phase"] = CompilationPhase.PROVING_ISOS
    error = result["error"]

    if write_to_directory_on_error:
        write_to_directory_on_error = Path(write_to_directory_on_error)
        key = str(hash(coq_project))
        (write_to_directory_on_error / key).mkdir(parents=True, exist_ok=True)
        now = datetime.datetime.now()
        iso_string = now.isoformat()
        if len(list((write_to_directory_on_error / key).iterdir())) == 0:
            coq_project.write(write_to_directory_on_error / key / iso_string)
            (write_to_directory_on_error / key / iso_string / "errors.txt").write_text(
                str(error)
            )
            (write_to_directory_on_error / key / iso_string / "result.txt").write_text(
                repr(result)
            )
        else:
            (write_to_directory_on_error / key / iso_string).touch()

    assert not result["status"], state
    assert error is not None, state
    assert not isinstance(error, MissingTypeIso), error
    if isinstance(error, MissingImport):
        return ContentText(
            text=f"Failed to prove isomorphisms because of missing import, please invoke `add_import_tool` with an import to make available the missing reference {error.import_str}"
        )
    elif isinstance(error, DisorderedConstr):
        return ContentText(
            text=f"Failed to prove isomorphism between {error.orig_source} and {error.orig_target} because the constructors are out of order.  This can be fixed by invoking `repair_iso_by_reorder_constructors_tool` with a permutation. The constructor misalignment is: {error.hint}"
        )
    elif isinstance(error, GenericIsoError):
        missing_iso_text = ""
        if error.unknown_lhs and error.unknown_rhs:
            missing_iso_text = f"""

This might be because we are missing an isomorphism between some identifier that we unfolded on the left and some identifier we unfolded on the right.  If this is the case, you can invoke `add_iso_tool` with the pair of identifiers, indicating that it should come before the isomorphism for {error.orig_source}. The candidates for missing isomorphisms are:
left: {error.unknown_lhs}
right: {error.unknown_rhs}
"""
        return ContentText(
            text=f"""Failed to prove isomorphism between {error.orig_source} and {error.orig_target}.
{missing_iso_text}

You might need to adjust the isomorphism proof of the isomorphism using the `edit_iso_proof_tool` with the new proof.
{"Likely this is" if not missing_iso_text else "This may be"} because of a difference in the elaboration of Lean and Coq.
For example, a standard library definition may be defined recursive on a different argument or calling a subdefinition with arguments in a different order, in which case you may need to rewrite with a commutativity lemma (e.g., using `iso. iso_rel_rewrite Nat.add_comm. iso.` or `iso. iso_rel_rewrite Nat.mul_comm. iso. iso_rel_rewrite Nat.add_comm. iso.`).
Or elaboration may pick different associativity for an infix operation, in which case you may need to rewrite with an associativity lemma.
Pay special attention to the left-hand-side of the isomorphism goal, which is the Coq source, rather than the right-hand-side, which is mangled by the Lean elaborator and re-import.
Here is some information that might help diagnose the rewriting:
```
{error.prefix}
```
There remain {error.ngoals} goals unsolved:
```
{error.simplified_goals or error.goals}
```
"""
        )
    elif isinstance(error, NonIsoBlockError):
        return ContentText(
            text=f"""Error occured while executing code:
```coq
{error.block}
```
Error occured on line: {error.error_line}
Error occured on characters: {error.error_start} - {error.error_end}
Error message: {error.error}

You can remove this block by invoking `remove_lemma_tool({error.block!r})` or replace it with a new block by invoking `edit_lemma_tool({error.block!r}, *new_block_text*)`.
"""
        )
    elif isinstance(error, IsoErrorWithoutHints) or isinstance(
        error, AmbiguousIsoError
    ):
        if isinstance(error, AmbiguousIsoError):
            logging.info(
                f"Ambiguous iso error most likely due to lack of `iso.`: {error}"
            )
        current_proof_text = (
            f""" with proof:
```coq
{error.orig_proof}
```
"""
            if error.orig_proof
            else "."
        )
        return ContentText(
            text=f"""Failed to prove isomorphism between {error.orig_source} and {error.orig_target}{current_proof_text}
Error message: {error.error}
Error occured on line: {error.error_line}
Error occured on characters: {error.error_start} - {error.error_end}

You can adjust the isomorphism proof of the isomorphism using the `edit_iso_proof_tool` with the new proof.  Most likely, the new proof should begin with `iso.` followed by other tactics.
"""
        )
    else:
        raise ToolError(f"Unknown error type {type(error)}: {error}")


@tool
def add_import_tool(
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
    write_to_directory_on_error: (
        Path | str | None
    ) = _DEFAULT_WRITE_TO_DIRECTORY_ON_ERROR,
) -> Tool:
    async def add_import(import_str: str) -> ToolResult:
        """
        Adds an import to the Coq project.

        Args:
            import_str: The import to be added, for example, "From Coq Require Import List." (str)
        """
        state: ProjectState = inspect_ai.util.store().get("translation_state")
        state["cc_identifiers_blocks"].insert(0, import_str)
        return generate_and_autorepair_isos_tool(
            original_name=original_name,
            imported_name=imported_name,
            iso_file=iso_file,
            write_to_directory_on_error=write_to_directory_on_error,
        )

    return add_import


@tool
def remove_lemma_tool(
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
    write_to_directory_on_error: (
        Path | str | None
    ) = _DEFAULT_WRITE_TO_DIRECTORY_ON_ERROR,
) -> Tool:
    async def remove_lemma(code_str: str) -> ToolResult:
        """
        Removes custom added code from the Coq isomorphism file.

        Args:
            code_str: The line of code to be removed. (str)
        """
        state: ProjectState = inspect_ai.util.store().get("translation_state")
        if code_str not in state["cc_identifiers_blocks"]:
            return ContentText(
                text=f"Invalid code to remove: {code_str!r}\nValid codes to remove are: {'\n'.join(repr(v) for v in state['cc_identifiers_blocks'] if isinstance(v, str))}"
            )
        state["cc_identifiers_blocks"].remove(code_str)
        return generate_and_autorepair_isos_tool(
            original_name=original_name,
            imported_name=imported_name,
            iso_file=iso_file,
            write_to_directory_on_error=write_to_directory_on_error,
        )

    return remove_lemma


@tool
def edit_lemma_tool(
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
    write_to_directory_on_error: (
        Path | str | None
    ) = _DEFAULT_WRITE_TO_DIRECTORY_ON_ERROR,
    permit_substring: bool = True,
    unique_substring_match: bool = True,
) -> Tool:
    async def edit_lemma(code_str: str, new_code_str: str) -> ToolResult:
        """
        Replaces a block of code from the Coq isomorphism file.  This tool does not replace isomoprhism proofs, only custom added code.

        Args:
            code_str: The line of code to be replaced. (str)
            new_code_str: The new line of code to replace it with. (str)
        """
        state: ProjectState = inspect_ai.util.store().get("translation_state")
        code_str = code_str.strip()
        new_code_str = new_code_str.strip()
        full_matches = [
            i
            for i, v in enumerate(state["cc_identifiers_blocks"])
            if isinstance(v, str) and v.strip() == code_str
        ]
        substring_matches = [
            i
            for i, v in enumerate(state["cc_identifiers_blocks"])
            if isinstance(v, str) and code_str in v
        ]
        indices = full_matches
        if not indices:
            if not substring_matches:
                return ContentText(
                    text=f"Invalid code to remove: {code_str!r}\nValid codes to remove are: {'\n'.join(repr(v) for v in state['cc_identifiers_blocks'] if isinstance(v, str))}"
                )
            elif not permit_substring:
                return ContentText(
                    text=f"Invalid code to remove (must be a full match, not a substring): {code_str!r}\nValid codes to remove are: {'\n'.join(repr(v) for v in state['cc_identifiers_blocks'] if isinstance(v, str))}"
                )
            elif len(substring_matches) > 1 and unique_substring_match:
                return ContentText(
                    text=f"Invalid code to remove (must be a unique substring match): {code_str!r} matches multiple blocks: {', '.join(repr(state['cc_identifiers_blocks'][i]) for i in substring_matches)}"
                )
            else:
                indices = substring_matches
        for index in indices:
            block = state["cc_identifiers_blocks"][index]
            assert isinstance(block, str)
            if block.strip() == code_str:
                state["cc_identifiers_blocks"][index] = new_code_str
            else:
                state["cc_identifiers_blocks"][index] = block.replace(
                    code_str, new_code_str
                )
        return generate_and_autorepair_isos_tool(
            original_name=original_name,
            imported_name=imported_name,
            iso_file=iso_file,
            write_to_directory_on_error=write_to_directory_on_error,
        )

    return edit_lemma


@tool
def remove_import_tool(
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
    write_to_directory_on_error: (
        Path | str | None
    ) = _DEFAULT_WRITE_TO_DIRECTORY_ON_ERROR,
) -> Tool:
    """like remove_lemma_tool, but with a different docstring"""
    remove_code = remove_lemma_tool(
        original_name=original_name,
        imported_name=imported_name,
        iso_file=iso_file,
        write_to_directory_on_error=write_to_directory_on_error,
    )

    async def remove_import(code_str: str) -> ToolResult:
        """
        Removes an import or other custom added code from the Coq isomorphism file.

        Args:
            code_str: The line of code to be removed. (str)
        """
        return await remove_code(code_str)

    return remove_import


def handle_value_error(
    cc_identifiers_blocks: list[str | IsoBlock],
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
    if iso_target is None:
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
def add_lemma_tool(
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
    write_to_directory_on_error: (
        Path | str | None
    ) = _DEFAULT_WRITE_TO_DIRECTORY_ON_ERROR,
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
        before_target = handle_none_string(before_target)
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

        return generate_and_autorepair_isos_tool(
            original_name=original_name,
            imported_name=imported_name,
            iso_file=iso_file,
            write_to_directory_on_error=write_to_directory_on_error,
        )

    return add_lemma


@tool
def add_iso_tool(
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
    write_to_directory_on_error: (
        Path | str | None
    ) = _DEFAULT_WRITE_TO_DIRECTORY_ON_ERROR,
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
            state["cc_identifiers_blocks"] = insert_iso(
                state["cc_identifiers_blocks"],
                source,
                target,
                before_source,
                original_name=original_name,
                imported_name=imported_name,
            )
        except ValueError as e:
            return handle_value_error(
                state["cc_identifiers_blocks"],
                before_source,
                original_name=original_name,
                imported_name=imported_name,
            )
        except IsoAlreadyExistsError as e:
            return ContentText(
                text=f"Cannot add iso_statement {source}, {target} for {e.args[0].before_source}, {e.args[0].before_target} at index {e.args[0].index} because it already exists at index {e.args[0].existing_index}"
            )

        return generate_and_autorepair_isos_tool(
            original_name=original_name,
            imported_name=imported_name,
            iso_file=iso_file,
            write_to_directory_on_error=write_to_directory_on_error,
        )

    return add_iso


@tool
def remove_iso_tool(
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
    write_to_directory_on_error: (
        Path | str | None
    ) = _DEFAULT_WRITE_TO_DIRECTORY_ON_ERROR,
) -> Tool:
    async def remove_iso(source: str, target: str | None = None) -> ToolResult:
        """
        Removes an isomorphism statement from the Coq project.

        Args:
            source: The source identifier for the isomorphism. (str)
            target: The target identifier for the isomorphism. (str | None)
        """
        target = handle_none_string(target)
        state: ProjectState = inspect_ai.util.store().get("translation_state")

        try:
            index, block = find_iso_and_index(
                state["cc_identifiers_blocks"],
                source,
                target,
                original_name=original_name,
                imported_name=imported_name,
            )
        except ValueError:
            return handle_value_error(
                state["cc_identifiers_blocks"],
                source,
                target,
                original_name=original_name,
                imported_name=imported_name,
            )

        if block.is_required:
            return ContentText(
                text=f"Only isomorphisms added by `add_iso_tool` can be removed by `remove_iso_tool`; {source}{' -> ' + target if target is not None else '(' + str(remove_identifier_prefix(block.target, prefix=imported_name)) + ')'} was part of the initial state."
            )

        logging.info(f"Removing iso_statement {block}")
        state["cc_identifiers_blocks"].pop(index)

        return generate_and_autorepair_isos_tool(
            original_name=original_name,
            imported_name=imported_name,
            iso_file=iso_file,
            write_to_directory_on_error=write_to_directory_on_error,
        )

    return remove_iso


async def edit_iso_proof_higher_order(
    iso_source: str,
    new_proof: Callable[[IsoBlock], str],
    iso_target: str | None = None,
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
    write_to_directory_on_error: (
        Path | str | None
    ) = _DEFAULT_WRITE_TO_DIRECTORY_ON_ERROR,
) -> ToolResult:
    state = inspect_ai.util.store().get("translation_state")
    try:
        index, block = find_iso_and_index(
            state["cc_identifiers_blocks"],
            iso_source,
            iso_target,
            original_name=original_name,
            imported_name=imported_name,
        )
    except ValueError as e:
        logging.warning(f"Error finding iso index: {e}")
        return handle_value_error(
            state["cc_identifiers_blocks"],
            iso_source,
            iso_target,
            original_name=original_name,
            imported_name=imported_name,
        )

    cur_proof = block.proof
    new_proof_str = new_proof(block).strip()

    # Be a bit more lenient with the proof string, and strip off the Proof. and Qed. parts
    if new_proof_str.startswith("Proof."):
        new_proof_str = new_proof_str[len("Proof.") :]
    if new_proof_str.endswith("Qed."):
        new_proof_str = new_proof_str[: -len("Qed.")]
    if new_proof_str.endswith("Defined."):
        new_proof_str = new_proof_str[: -len("Defined.")]
    new_proof_str = new_proof_str.strip()

    new_block = deepcopy(block)
    new_block.proof = new_proof_str
    state["cc_identifiers_blocks"][index] = new_block
    logging.info(
        f"Reordered constructors for {iso_source} ({block.source}) to {block.target}, new proof is {new_proof_str}, old proof was {cur_proof}"
    )

    return generate_and_autorepair_isos_tool(
        original_name=original_name,
        imported_name=imported_name,
        iso_file=iso_file,
        write_to_directory_on_error=write_to_directory_on_error,
    )


@tool
def edit_iso_proof_tool(
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
    write_to_directory_on_error: (
        Path | str | None
    ) = _DEFAULT_WRITE_TO_DIRECTORY_ON_ERROR,
) -> Tool:
    async def edit_iso_proof(
        iso_source: str, new_proof: str, iso_target: str | None = None
    ) -> ToolResult:
        """
        Edits the proof of an isomorphism block.

        Args:
            iso_source: The source identifier for the isomorphism block to be edited. (str)
            new_proof: The new proof for the isomorphism block.  This is likely to be something like 'iso. iso_rel_rewrite {lemma here}. iso.' (str)
            iso_target: The target identifier for the isomorphism block to be edited. Optional. (str|None)
        """
        iso_target = handle_none_string(iso_target)
        return await edit_iso_proof_higher_order(
            iso_source,
            lambda _block: new_proof,
            iso_target=iso_target,
            original_name=original_name,
            imported_name=imported_name,
            iso_file=iso_file,
            write_to_directory_on_error=write_to_directory_on_error,
        )

    return edit_iso_proof


@tool
def repair_iso_by_reorder_constructors_tool(
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
    write_to_directory_on_error: (
        Path | str | None
    ) = _DEFAULT_WRITE_TO_DIRECTORY_ON_ERROR,
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

        def new_proof(block: IsoBlock):
            cur_proof = block.proof
            logging.info(f"Reordering constructors using permutation {permutation}")
            permutation_obj: Permutation = Permutation(permutation)
            if cur_proof is not None and "revgoals" in cur_proof:
                permutation_obj = ~permutation_obj
            transpositions = permutation_obj.transpositions()

            inverse_transpositions = (~permutation_obj).transpositions()
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

        return await edit_iso_proof_higher_order(
            source,
            new_proof,
            original_name=original_name,
            imported_name=imported_name,
            iso_file=iso_file,
            write_to_directory_on_error=write_to_directory_on_error,
        )

    return repair_iso_by_reorder_constructors


def ensure_init_translation_state(
    coq_project: CoqProject,
    lean_export_project: LeanProject,
    coq_identifiers: list[CoqIdentifier],
    coq_identifiers_to_unfold: list[CoqIdentifier],
):
    store = inspect_ai.util.store()
    if "translation_state" not in store:
        store.set("translation_state", {})
    state = store.get("translation_state")
    if "lean_export_project_id" not in state:
        set_lean_export_project(lean_export_project)
    if "coq_project_id" not in state:
        set_coq_project(coq_project)
    if "coq_identifiers" not in state:
        state["coq_identifiers"] = coq_identifiers
    if "coq_identifiers_to_unfold" not in state:
        state["coq_identifiers_to_unfold"] = coq_identifiers_to_unfold


def make_submit_translation_tool(
    coq_statements: str | None = None,
    coq_names: list[str] | None = None,
    *,
    iso_checker_path: str | Path = f"{SOURCE_DIR}/iso-checker",
    init_coq_targets: str | Sequence[str] | None = "Automation.vo",
    lean_export_directory: str | Path = EXPORT_DIR,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
    write_to_directory_on_error: (
        Path | str | None
    ) = _DEFAULT_WRITE_TO_DIRECTORY_ON_ERROR,
    admit_failing_isos: bool = False,
) -> tuple[Callable[[], Tool], list[str]]:
    (
        init_coq_project,
        init_lean_export_project,
        coq_identifiers,
        coq_identifiers_to_unfold,
    ) = init_translation_project(
        coq_statements,
        coq_names,
        iso_checker_path=iso_checker_path,
        init_coq_targets=init_coq_targets,
        lean_export_directory=lean_export_directory,
        original_name=original_name,
    )

    @tool
    def submit_translation_tool() -> Tool:
        async def submit_translation(
            lean_code: str, coq_lean_identifiers: dict[str, str]
        ):
            """
            Submits the given Lean 4 code as the result of translation, with paired identifiers between the Coq and Lean code.

            Args:
                lean_code: Lean code to be run (str)
                coq_lean_identifiers: Mapping of Coq identifiers to the corresponding translated Lean identifier (dict[str, str])

            Returns:
                ToolResult: Messages that came up during execution
            """
            ensure_init_translation_state(
                init_coq_project,
                init_lean_export_project,
                coq_identifiers,
                coq_identifiers_to_unfold,
            )
            store = inspect_ai.util.store()
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

            if not coq_lean_identifiers:
                raise ToolError("coq_lean_identifiers must not be empty")

            state["lean_statements"] = LeanFile(lean_code)
            # Verify that the Lean code compiles
            lean_project, result["status"], result["stderr"] = check_compilation(
                state["lean_statements"], project=None
            )
            set_lean_project(lean_project)
            if not result["status"]:
                if write_to_directory_on_error is not None:
                    lean_project.write(write_to_directory_on_error)
                result["suggestion"] = "Lean code failed to compile."
                result["failure_phase"] = CompilationPhase.LEAN_COMPILATION
                return ContentText(
                    text=f"""Lean code failed to compile:
{result["stderr"]}"""
                )

            mapped_lean_identifiers = [
                coq_lean_identifiers.get(
                    str(k),
                    coq_lean_identifiers.get(
                        remove_identifier_prefix(str(k), prefix=original_name)
                    ),
                )
                for k in coq_identifiers
            ]
            state["cl_identifiers"] = [
                (source, LeanIdentifier(target))
                for source, target in zip(coq_identifiers, mapped_lean_identifiers)
                if target is not None
            ]
            state["missing_identifiers"] = [
                source
                for source, target in zip(coq_identifiers, mapped_lean_identifiers)
                if target is None
            ]
            state["excess_identifiers"] = [
                (k, v)
                for k, v in coq_lean_identifiers.items()
                if v not in mapped_lean_identifiers
            ]
            lean_export_project = get_lean_export_project()
            coq_project = get_coq_project()

            if not state["cl_identifiers"]:
                msg = f"No known Coq identifiers found in coq_lean_identifiers ({coq_lean_identifiers!r})"
                if state["missing_identifiers"]:
                    msg += f"\nMissing identifiers for {', '.join(map(str, state['missing_identifiers']))}"
                if state["excess_identifiers"]:
                    msg += f"\nUnrecognized identifiers: {', '.join(f'{k} -> {v}' for k, v in state['excess_identifiers'])}"
                raise ToolError(msg)

            (
                lean_export_project,
                coq_project,
                result["status"],
                cc_identifiers_blocks,
                result["stderr"],
            ) = lean_to_coq(
                lean_export_project,
                coq_project,
                state["lean_statements"],
                state["cl_identifiers"],
                coq_file_stem=imported_name,
                imported_name=imported_name,
                coq_identifiers_to_unfold=state["coq_identifiers_to_unfold"],
            )
            set_lean_export_project(lean_export_project)
            set_coq_project(coq_project)
            state["cc_identifiers_blocks"] = list(cc_identifiers_blocks)

            if not result["status"]:
                if write_to_directory_on_error is not None:
                    coq_project.write(write_to_directory_on_error)
                raise ToolError(
                    f"""Lean code failed to import to Coq (please summon a wizard):
{result["stderr"]}"""
                )

            return generate_and_autorepair_isos_tool(
                original_name=original_name,
                imported_name=imported_name,
                iso_file=iso_file,
                write_to_directory_on_error=write_to_directory_on_error,
                admit_failing_isos=admit_failing_isos,
            )

        return submit_translation

    return submit_translation_tool, [
        str(remove_identifier_prefix(i, prefix=original_name)) for i in coq_identifiers
    ]


@tool
def push_statement_to_queue_tool():
    async def push_statement_to_queue(statement: str):
        """
        Pushes the given statement to the queue.

        Args:
            statement: The statement to push to the queue. (str)

        Returns:
            ContentText: Confirmation that the statement was pushed to the queue.
        """
        store = inspect_ai.util.store()
        if "statement_queue" not in store:
            store.set("statement_queue", [])
        statement_queue: list[str] = store.get("statement_queue")
        statement_queue.append(statement)
        store.set("statement_queue", statement_queue)
        return ContentText(text="Statement pushed to queue.")

    return push_statement_to_queue


@tool
def pop_statement_from_queue_tool():
    async def pop_statement_from_queue():
        """
        Pops the first statement from the queue.

        Returns:
            ContentText: The popped statement
        """
        store = inspect_ai.util.store()
        if "statement_queue" not in store:
            store.set("statement_queue", [])
        statement_queue: list[str] = store.get("statement_queue")
        if not statement_queue:
            return ContentText(text="Queue is empty.")
        statement = statement_queue.pop(0)
        store.set("statement_queue", statement_queue)
        return ContentText(text=statement)

    return pop_statement_from_queue


@tool
def view_statement_queue_tool():
    async def view_statement_queue():
        """
        Views the current statement queue.

        Returns:
            ContentText: The entire statement queue, one per line, from first to last.
        """
        store = inspect_ai.util.store()
        if "statement_queue" not in store:
            return ContentText(text="Queue is empty.")
        statement_queue: list[str] = store.get("statement_queue")
        return ContentText(text="\n".join(statement_queue))

    return view_statement_queue


@tool
def swap_statements_in_queue_tool():
    async def swap_statements_in_queue(index1: int, index2: int):
        """
        Swaps the statements at the given indices in the queue.

        Args:
            index1: The index of the first statement to swap. (int)
            index2: The index of the second statement to swap. (int)

        Returns:
            ContentText: Confirmation that the statements were swapped.
        """
        store = inspect_ai.util.store()
        if "statement_queue" not in store:
            return ContentText(text="Queue is empty.")
        statement_queue: list[str] = store.get("statement_queue")
        statement_queue[index1], statement_queue[index2] = (
            statement_queue[index2],
            statement_queue[index1],
        )
        store.set("statement_queue", statement_queue)
        return ContentText(
            text=f"Swapped statements in {index1} and {index2} in queue."
        )

    return swap_statements_in_queue


@tool
def push_translation_to_queue_tool():
    async def push_translation_to_queue(lean_code: str):
        """
        Pushes the given translation to the queue.

        Args:
            lean_code: The Lean code to push to the queue. (str)

        Returns:
            ContentText: Confirmation that the translation was pushed to the queue.
        """
        store = inspect_ai.util.store()
        if "translation_queue" not in store:
            store.set("translation_queue", [])
        translation_queue: list[str] = store.get("translation_queue")
        translation_queue.append(lean_code)
        store.set("translation_queue", translation_queue)
        return ContentText(text="Translation pushed to queue.")

    return push_translation_to_queue


@tool
def pop_translation_from_queue_tool():
    async def pop_translation_from_queue():
        """
        Pops the first translation from the queue.

        Returns:
            ContentText: The popped translation
        """
        store = inspect_ai.util.store()
        if "translation_queue" not in store:
            return ContentText(text="Queue is empty.")
        translation_queue: list[str] = store.get("translation_queue")
        if not translation_queue:
            return ContentText(text="Queue is empty.")
        translation = translation_queue.pop(0)
        store.set("translation_queue", translation_queue)
        return ContentText(text=translation)

    return pop_translation_from_queue


@tool
def update_identifier_mappings_tool():
    async def update_identifier_mappings(coq_lean_identifiers: dict[str, str]):
        """
        Updates the identifier mapping.

        Args:
            coq_lean_identifiers: Mapping of Coq identifiers to the corresponding translated Lean identifier to add or update in the mapping (dict[str, str])

        Returns:
            ContentText: Confirmation that the identifier mappings were added or updated.
        """
        store = inspect_ai.util.store()
        if "identifier_mappings" not in store:
            store.set("identifier_mappings", {})
        identifier_mappings: dict[str, str] = store.get("identifier_mappings")
        response = ""
        for coq_identifier, lean_identifier in coq_lean_identifiers.items():
            if coq_identifier in identifier_mappings:
                response += f"Updated {coq_identifier} -> {lean_identifier}\n"
            else:
                response += f"Added {coq_identifier} -> {lean_identifier}\n"
            identifier_mappings[coq_identifier] = lean_identifier
        store.set("identifier_mappings", identifier_mappings)
        return ContentText(text=response)

    return update_identifier_mappings


@tool
def view_identifier_mappings_tool():
    async def view_identifier_mappings():
        """
        Views the current identifier mapping.

        Returns:
            ContentText: The entire identifier mapping, one per line, from Coq identifier to Lean identifier.
        """
        store = inspect_ai.util.store()
        if "identifier_mappings" not in store:
            return ContentText(text="No identifier mapping found.")
        identifier_mappings: dict[str, str] = store.get("identifier_mappings")
        return ContentText(text=str(identifier_mappings))

    return view_identifier_mappings
