from copy import deepcopy
from pathlib import Path
from typing import Any, Collection

import inspect_ai.util
from inspect_ai.scorer import (
    CORRECT,
    INCORRECT,
    PARTIAL,
    Score,
    Target,
    accuracy,
    mean,
    scorer,
)
from inspect_ai.solver import TaskState

from project_util import IsoBlock
from tools.transpilation import (
    CompilationPhase,
    ProjectState,
    generate_and_autorepair_isos_tool,
    get_coq_project,
)

_DEFAULT_WRITE_TO_DIRECTORY_ON_ERROR = (
    Path(__file__).parent.parent.parent / "temp_scorers_transpilation_errors"
)


class LeanError(Exception):
    pass


class ModelResponseError(Exception):
    pass


@scorer(metrics=[accuracy()])
def lean_compiles_scorer():
    """Checks if lean code compiles from the translation state taken from inspect store"""

    async def score(state: TaskState, target: Target | None):
        store = inspect_ai.util.store()
        p_state: ProjectState | None = deepcopy(store.get("translation_state"))
        metadata = {"translation_state": p_state}
        if p_state is None:
            return Score(
                value=INCORRECT,
                explanation="No translation state found",
                metadata=metadata,
            )
        # TODO: add lean project file contents to metadata
        if p_state["result"].get("failure_phase") == CompilationPhase.LEAN_COMPILATION:
            return Score(
                value=INCORRECT,
                explanation="Lean code does not compile",
                metadata=metadata,
            )
        return Score(value=CORRECT, explanation="Lean code compiles", metadata=metadata)

    return score


@scorer(metrics=[accuracy()])
def checker_compiles_scorer(
    *,
    allowed_flags: dict[str, Collection[str] | None] = {"definitional UIP": None},
    allowed_axioms: Collection[str] = ["functional_extensionality_dep"],
):
    """Checks if Checker.vo compiles and check print assumptions output

    Args:
        allowed_flags: mapping of flags (such as 'definitional UIP') to constants that are allowed to depend on that flag; mapping to None means every constant
        allowed_axioms: List of axiom names that are allowed to appear in Print Assumptions
    """

    async def score(state: TaskState, target: Target | None):
        store = inspect_ai.util.store()
        p_state: ProjectState | None = deepcopy(store.get("translation_state"))
        metadata: dict[str, Any] = {"translation_state": p_state}
        if p_state is None:
            return Score(
                value=INCORRECT,
                explanation="No translation state found",
                metadata=metadata,
            )
        result = p_state["result"]
        if result.get("failure_phase") == CompilationPhase.LEAN_COMPILATION:
            return Score(
                value=INCORRECT,
                explanation="Lean code does not compile",
                metadata=metadata,
            )

        coq_project = get_coq_project()
        if not coq_project:
            return Score(
                value=INCORRECT,
                explanation="No Coq project state found",
                metadata=metadata,
            )
        metadata["coq_project_debug_files"] = {
            f: f"```coq\n{coq_project[f].contents}\n```"
            for f in coq_project.debug_files
        }
        compilation_result, _ = coq_project.make("Checker.vo", check=False)

        if compilation_result.returncode != 0:
            return Score(
                value=INCORRECT,
                explanation=f"Checker.vo failed to build:\n{compilation_result.stderr}",
                metadata=metadata,
            )

        stdout = compilation_result.stdout
        if "Axioms:" not in stdout:
            return Score(value=CORRECT, explanation=stdout, metadata=metadata)

        axioms_section = stdout[
            stdout.find("Axioms:") : stdout.find("End Print Assumptions")
        ]
        disallowed_axioms = []

        for line in axioms_section.split("\n"):
            if not line or line.startswith("Axioms:"):
                continue

            # Start of new axiom definition
            if line == line.lstrip():
                if "relies on" in line:
                    current_axiom, current_flag = line.split("relies on")
                    current_axiom, current_flag = (
                        current_axiom.strip(),
                        current_flag.strip(),
                    )
                    cur_allowed_flags = allowed_flags.get(current_flag)
                    if current_flag not in allowed_flags:
                        disallowed_axioms.append(current_flag)
                    elif cur_allowed_flags and current_axiom not in cur_allowed_flags:
                        disallowed_axioms.append(line.strip().rstrip("."))
                else:
                    current_axiom = line.split(":")[0].strip()
                    if current_axiom not in allowed_axioms:
                        disallowed_axioms.append(current_axiom)

        if disallowed_axioms:
            return Score(
                value=INCORRECT,
                explanation=f"Compilation succeeded but has disallowed axioms: {', '.join(disallowed_axioms)}\n\nFull Print Assumptions output:\n{stdout}",
                metadata=metadata,
            )

        return Score(
            value=CORRECT,
            explanation=f"Checker.vo compiled successfully with only allowed axioms.\n\nFull Print Assumptions output:\n{stdout}",
            metadata=metadata,
        )

    return score


@scorer(metrics=[accuracy(), mean()])
def isos_proven_scorer(
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
    write_to_directory_on_error: (
        Path | str | None
    ) = _DEFAULT_WRITE_TO_DIRECTORY_ON_ERROR,
    only_required: bool = False,
    only_original: bool = False,
):
    """score based on how many isos were proven"""

    async def score(state: TaskState, target: Target | None):
        store = inspect_ai.util.store()
        p_state: ProjectState | None = deepcopy(store.get("translation_state"))
        metadata: dict[str, Any] = {"translation_state": p_state}
        if p_state is None:
            return Score(
                value=INCORRECT,
                explanation="No translation state found",
                metadata=metadata,
            )

        result = p_state["result"]
        if result.get("failure_phase") == CompilationPhase.LEAN_COMPILATION:
            return Score(
                value=INCORRECT,
                explanation="Lean code does not compile",
                metadata=metadata,
            )

        admit_msgs = generate_and_autorepair_isos_tool(
            original_name=original_name,
            imported_name=imported_name,
            iso_file=iso_file,
            write_to_directory_on_error=write_to_directory_on_error,
            admit_failing_isos=True,
        )
        p_state: ProjectState | None = deepcopy(store.get("translation_state"))
        metadata["postadmit_translation_state"] = p_state

        if admit_msgs:
            text = getattr(admit_msgs, "text", None)
            if text is not None:
                if not text.lower().startswith("Success"):
                    metadata["admit_msgs"] = text
            else:
                metadata["admit_msgs"] = admit_msgs
        blocks: list[str | IsoBlock] = (p_state or {}).get("cc_identifiers_blocks", [])
        if not blocks:
            return Score(
                value=INCORRECT, explanation="No blocks found", metadata=metadata
            )
        total_isos, proven_isos = 0, 0
        for block in blocks:
            if not isinstance(block, IsoBlock):
                continue
            if (
                block.proof is not None
                and (block.is_required or not only_required)
                and (block.is_original or not only_original)
            ):
                total_isos += 1
                if "Admitted" not in block.proof:
                    proven_isos += 1

        descr = "original " if only_original else "required " if only_required else ""
        if total_isos == 0:
            return Score(
                value=INCORRECT,
                explanation=f"No {descr}isomorphism proofs found",
                metadata=metadata,
            )
        return Score(
            value=proven_isos / total_isos,
            explanation=f"{proven_isos}/{total_isos} {descr}isomorphism proofs were proven",
            metadata=metadata,
        )

    return score


@scorer(metrics=[accuracy(), mean()])
def strict_isos_proven_scorer(
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
    write_to_directory_on_error: (
        Path | str | None
    ) = _DEFAULT_WRITE_TO_DIRECTORY_ON_ERROR,
):
    """score based on how many original isos were proven"""

    return isos_proven_scorer(
        original_name=original_name,
        imported_name=imported_name,
        iso_file=iso_file,
        write_to_directory_on_error=write_to_directory_on_error,
        only_required=True,
        only_original=False,
    )


def relaxed_isos_proven_scorer(
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
    write_to_directory_on_error: (
        Path | str | None
    ) = _DEFAULT_WRITE_TO_DIRECTORY_ON_ERROR,
):
    """score based on how many isos were proven overall"""

    return isos_proven_scorer(
        original_name=original_name,
        imported_name=imported_name,
        iso_file=iso_file,
        write_to_directory_on_error=write_to_directory_on_error,
        only_required=False,
        only_original=False,
    )
