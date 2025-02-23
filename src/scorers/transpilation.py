from inspect_ai.scorer import (
    CORRECT,
    INCORRECT,
    PARTIAL,
    Score,
    Target,
    accuracy,
    scorer,
)
from inspect_ai.solver import TaskState
from inspect_ai.util import Store
import inspect_ai.util

from main import (
    DEFINITION_PAIRS,
    LeanFile,
    check_translation,
    generate_and_prove_iso,
    import_to_coq,
    lean_to_coq,
)
from tools.itp import run_lean_str
from tools.transpilation import CompilationPhase, ProjectState


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
            result = run_lean_str(answer)
            correct = result["status"] == 0
        except Exception as e:
            return Score(value=INCORRECT, explanation=f"Error running Lean code: {e}")
        return Score(
            value=CORRECT if correct else INCORRECT,
        )

    return score


@scorer(metrics=[accuracy()])
def transpilation_scorer():
    async def score(state: TaskState, target: Target | None):
        try:
            # extract lean code
            answer = state.output.completion
            answer = answer[answer.find("```lean") + 7 : answer.rfind("```")]
            if not answer:
                raise ModelResponseError("Unable to find lean code in model response.")

            # TODO: extract identifiers rather than use sample
            cl_identifiers = DEFINITION_PAIRS

            result, error_code, error = check_translation(answer, cl_identifiers)

            if result:
                return Score(value=CORRECT)

            elif error_code in {
                "compilation_failure",
                "export_import_failure",
                "isomorphism_failure",
            }:
                return Score(value=PARTIAL)

            else:
                return Score(value=INCORRECT)
        except Exception as e:
            return Score(value=INCORRECT, explanation=str(e))

    return score

@scorer(metrics=[accuracy()])
def lean_compiles_scorer():
    """Checks if lean code compiles from the translation state taken from inspect store"""
    async def score(state: TaskState, target: Target | None):
        store = inspect_ai.util.store()
        p_state: ProjectState = store.get("translation_state")
        if p_state is None:
            return Score(value=INCORRECT, explanation="No translation state found")
        if p_state["result"].get("failure_phase") == CompilationPhase.COMPILATION:
            return Score(value=INCORRECT, explanation="Lean code does not compile")
        return Score(value=CORRECT)
    return score

@scorer(metrics=[accuracy()])
def checker_compiles_scorer():
    """Checks if Checker.vo compiles and check print assumptions output"""
    async def score(state: TaskState, target: Target | None):
        store = inspect_ai.util.store()
        p_state: ProjectState = store.get("translation_state")
        if p_state is None:
            return Score(value=INCORRECT, explanation="No translation state found")
        result = p_state["result"]
        if result.get("failure_phase") == CompilationPhase.COMPILATION:
            return Score(value=INCORRECT, explanation="Lean code does not compile")

        coq_project = p_state.get("coq_project")
        if not coq_project:
            return Score(value=INCORRECT, explanation="No Coq project state found")
        compilation_result, _ = coq_project.make("Checker.vo", check=False)
        
        if compilation_result.returncode != 0:
            return Score(
                value=INCORRECT, 
                explanation=f"Checker.vo failed to build:\n{compilation_result.stderr}"
            )
        if "Axioms:" in compilation_result.stdout:
            return Score(
                # @Jason change to INCORRECT?
                value=PARTIAL,
                explanation="Compilation succeeded but has axioms in assumptions"
            )
        return Score(value=CORRECT, explanation="Checker.vo compiled successfully with no axioms")

    return score

@scorer(metrics=[accuracy()])
def isos_proven_scorer():
    """score based on how many isos were proven"""
    async def score(state: TaskState, target: Target | None):
        store = inspect_ai.util.store()
        p_state: ProjectState = store.get("translation_state")
        if p_state is None:
            return Score(value=INCORRECT, explanation="No translation state found")
        result = p_state["result"]
        if result.get("failure_phase") == CompilationPhase.COMPILATION:
            return Score(value=INCORRECT, explanation="Lean code does not compile")
        blocks = p_state.get("cc_identifiers_blocks", [])
        if not blocks:
            return Score(value=INCORRECT, explanation="No blocks found")
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
            return Score(value=INCORRECT, explanation="No isomorphism proofs found")
        return Score(
            value=proven_isos / total_isos,
            explanation=f"{proven_isos}/{total_isos} isomorphism proofs were proven"
        )
    return score
