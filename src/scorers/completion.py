from inspect_ai.scorer import (
    CORRECT,
    INCORRECT,
    Score,
    Target,
    accuracy,
    scorer,
)
from inspect_ai.solver import TaskState
from inspect_ai.util import Store
import inspect_ai.util

from tools.itp import run_coq_str

@scorer(metrics=[accuracy()])
def coq_proven_scorer():
    async def score(state: TaskState, target: Target | None):
        store = state.store if state.store else inspect_ai.util.store()
        cur_index = store.get("cur_index", 0)
        if cur_index == 0:
            return Score(value=INCORRECT, explanation="No submission results found")
        for i in range(cur_index):
            result = store.get(f"result_{i}")
            if result["submission_status"]:
                return Score(value=CORRECT)
        return Score(value=INCORRECT, explanation="No correct submission found, total submissions: {cur_index}")
    return score

@scorer(metrics=[accuracy()])
def coq_runs_scorer():
    async def score(state: TaskState, target: Target | None):
        answer = state.output.completion
        try:
            answer = answer[answer.find("```coq") + 6 : answer.rfind("```")]
            result = run_coq_str(answer)
            correct = result["status"] == 0
        except Exception as e:
            return Score(value=INCORRECT, explanation=f"Error running Coq code: {e}")
        return Score(
            value=CORRECT if correct else INCORRECT,
        )

    return score
