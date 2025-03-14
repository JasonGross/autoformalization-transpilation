from pathlib import Path
from typing import Collection
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
import inspect_ai.util

from main import (
    DEFINITION_PAIRS,
    check_translation,
)
from tools.itp import run_lean_str_in_project
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
def lean_runs_scorer():
    async def score(state: TaskState, target: Target | None):
        answer = state.output.completion
        try:
            answer = answer[answer.find("```lean") + 7 : answer.rfind("```")]
            result = run_lean_str_in_project(answer)
            correct = result["status"] == 0
        except Exception as e:
            return Score(value=INCORRECT, explanation=f"Error running Lean code: {e}")
        return Score(
            value=CORRECT if correct else INCORRECT,
        )

    return score


# @scorer(metrics=[accuracy()])
# def transpilation_scorer():
#     async def score(state: TaskState, target: Target | None):
#         try:
#             # extract lean code
#             answer = state.output.completion
#             answer = answer[answer.find("```lean") + 7 : answer.rfind("```")]
#             if not answer:
#                 raise ModelResponseError("Unable to find lean code in model response.")

#             # TODO: extract identifiers rather than use sample
#             cl_identifiers = DEFINITION_PAIRS

#             result, error_code, error = check_translation(answer, cl_identifiers)

#             if result:
#                 return Score(value=CORRECT)

#             elif error_code in {
#                 "compilation_failure",
#                 "export_import_failure",
#                 "isomorphism_failure",
#             }:
#                 return Score(value=PARTIAL)

#             else:
#                 return Score(value=INCORRECT)
#         except Exception as e:
#             return Score(value=INCORRECT, explanation=str(e))

#     return score


@scorer(metrics=[accuracy()])
def lean_compiles_scorer():
    """Checks if lean code compiles from the translation state taken from inspect store"""

    async def score(state: TaskState, target: Target | None):
        store = inspect_ai.util.store()
        p_state: ProjectState | None = store.get("translation_state")
        metadata = {"translation_state": p_state}
        if p_state is None:
            return Score(
                value=INCORRECT,
                explanation="No translation state found",
                metadata=metadata,
            )
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
        p_state: ProjectState | None = store.get("translation_state")
        metadata = {"translation_state": p_state}
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
):
    """score based on how many isos were proven"""

    async def score(state: TaskState, target: Target | None):
        admit_msgs = generate_and_autorepair_isos_tool(
            original_name=original_name,
            imported_name=imported_name,
            iso_file=iso_file,
            write_to_directory_on_error=write_to_directory_on_error,
            admit_failing_isos=True,
        )

        store = inspect_ai.util.store()
        p_state: ProjectState | None = store.get("translation_state")
        metadata = {"translation_state": p_state}
        if admit_msgs:
            if hasattr(admit_msgs, "text"):
                if not admit_msgs.text.lower().startswith("Success"):
                    metadata["admit_msgs"] = admit_msgs.text
            else:
                metadata["admit_msgs"] = admit_msgs
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
        blocks = p_state.get("cc_identifiers_blocks", [])
        if not blocks:
            return Score(
                value=INCORRECT, explanation="No blocks found", metadata=metadata
            )
        total_isos, proven_isos = 0, 0
        for block in blocks:
            if isinstance(block, str):
                continue
            proof = block[2]
            if proof is not None:
                total_isos += 1
                if "Admitted" not in proof:
                    proven_isos += 1

        if total_isos == 0:
            return Score(
                value=INCORRECT,
                explanation="No isomorphism proofs found",
                metadata=metadata,
            )
        return Score(
            value=proven_isos / total_isos,
            explanation=f"{proven_isos}/{total_isos} isomorphism proofs were proven",
            metadata=metadata,
        )

    return score
