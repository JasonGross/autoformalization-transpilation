from pathlib import Path

from inspect_ai import Task, eval, task
from inspect_ai.solver import basic_agent, generate, system_message, use_tools

from dataset.prepare import format_translation_input, prepare_dataset
from models import AnthropicModel, OpenAIModel
from prompts.transpilation import (
    ALTERNATIVE_SYSTEM_MESSAGE,
    SYSTEM_MESSAGE,
    TRANSLATION_STATE_TEMPLATE,
)
from scorers.transpilation import lean_runs_scorer
from tools.itp import lean_run_tool

EXAMPLE_COQ_FILEPATH = EXAMPLE_COQ_FILEPATH = (
    Path(__file__).parent / "simple-tests" / "proof.v"
)


@task
def coq_to_lean():
    # dataset
    input_msg = format_translation_input(
        TRANSLATION_STATE_TEMPLATE, EXAMPLE_COQ_FILEPATH
    )
    dataset = prepare_dataset([input_msg])

    # define task
    return Task(
        dataset=dataset,
        solver=basic_agent(
            init=system_message(ALTERNATIVE_SYSTEM_MESSAGE),
            tools=[lean_run_tool()],
            max_attempts=3,
            message_limit=30,
        ),
        scorer=lean_runs_scorer(),
    )


if __name__ == "__main__":
    eval(
        coq_to_lean(),
        # model=OpenAIModel.BEST,
        model=AnthropicModel.BEST,
    )
    pass
