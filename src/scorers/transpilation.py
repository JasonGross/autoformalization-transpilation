from inspect_ai.scorer import (
    CORRECT,
    INCORRECT,
    Score,
    Target,
    accuracy,
    scorer,
)
from inspect_ai.solver import TaskState

from tools.itp import run_lean_str


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
