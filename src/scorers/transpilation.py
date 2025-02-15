from inspect_ai.scorer import (
    CORRECT,
    INCORRECT,
    Score,
    Target,
    accuracy,
    scorer,
)
from inspect_ai.solver import TaskState

from main import (
    DEFINITION_PAIRS,
    LeanFile,
    generate_and_prove_iso,
    import_to_coq,
    lean_to_coq,
)
from tools.itp import run_lean_str


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

            # compile
            result = run_lean_str(answer)
            if result["status"] != 0:
                raise LeanError(f"Error compiling Lean code: {result['stderr']}")

            # import to Coq
            lean_file = LeanFile(answer)
            success, cc_identifiers, error = lean_to_coq(
                lean_file,
                DEFINITION_PAIRS,  # TODO: Replace?
            )
            if not success:
                raise LeanError(f"Error importing lean to Coq: {error}")

            # generate and prove isos - (still being worked on)
            result, errors = generate_and_prove_iso(cc_identifiers)
            if not result:
                raise LeanError(f"Error generating and proving iso: {errors}")

            return Score(
                value=CORRECT,
            )
        except Exception as e:
            return Score(value=INCORRECT, explanation=str(e))

    return score
