from pathlib import Path

from inspect_ai import Task, eval, task
from inspect_ai.solver import generate, system_message, use_tools

from dataset.prepare import format_translation_input, prepare_dataset
from models import AnthropicModel
from prompts.completion import ALTERNATE_SYSTEM_MESSAGE, COQ_STATEMENTS
from scorers.completion import coq_runs_scorer
from tools.itp import coq_run_tool

EXAMPLE_COQ_FILEPATH = Path(__file__).parent / "simple-tests" / "incomplete.v"


@task
def coq_completion():
    # dataset
    input_msg = format_translation_input(COQ_STATEMENTS, EXAMPLE_COQ_FILEPATH)
    dataset = prepare_dataset([input_msg])

    # define task
    return Task(
        dataset=dataset,
        solver=[
            system_message(ALTERNATE_SYSTEM_MESSAGE),
            generate(),
            use_tools(coq_run_tool()),
        ],
        scorer=coq_runs_scorer(),
    )


if __name__ == "__main__":
    eval(coq_completion(), model=AnthropicModel.BEST, message_limit=20)
    pass
