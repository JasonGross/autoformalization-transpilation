from pathlib import Path

from inspect_ai import Task, eval, task
from inspect_ai.solver import basic_agent, system_message
from inspect_ai.model import CachePolicy

from dataset.prepare import format_translation_input, prepare_dataset
from models import AnthropicModel, OpenAIModel
from prompts.transpilation import (
    ALTERNATIVE_SYSTEM_MESSAGE,
    TRANSLATION_STATE_TEMPLATE,
)
from scorers.transpilation import checker_compiles_scorer, isos_proven_scorer
from tools.itp import lean_run_tool
from tools.transpilation import (
    add_import_tool,
    add_lemma_tool,
    add_iso_tool,
    edit_proof_tool,
    remove_import_tool,
    repair_iso_by_reorder_constructors_tool,
    transpilation_tool,
)

EXAMPLE_COQ_FILEPATH = EXAMPLE_COQ_FILEPATH = (
    Path(__file__).parent.parent / "simple-tests" / "incomplete_statements.v"
)


@task
def coq_to_lean(cache: CachePolicy | bool = False):
    # dataset
    input_msg = format_translation_input(
        TRANSLATION_STATE_TEMPLATE, EXAMPLE_COQ_FILEPATH
    )
    dataset = prepare_dataset([input_msg])

    # define task
    # TODO: Take Coq file and series of Coq identifiers and return a lean file and corresponding lean identifiers
    return Task(
        dataset=dataset,
        solver=basic_agent(
            init=system_message(ALTERNATIVE_SYSTEM_MESSAGE),
            tools=[
                lean_run_tool(),
                transpilation_tool(EXAMPLE_COQ_FILEPATH.read_text()),
                add_import_tool(),
                remove_import_tool(),
                add_lemma_tool(),
                add_iso_tool(),
                edit_proof_tool(),
                repair_iso_by_reorder_constructors_tool(),
            ],
            max_attempts=3,
            message_limit=30,
            token_limit=50_000,
            cache=cache,
        ),
        scorer=[checker_compiles_scorer(), isos_proven_scorer()],
    )


if __name__ == "__main__":
    eval(
        coq_to_lean(
            # cache=CachePolicy(expiry=None, per_epoch=False),
        ),
        # model=OpenAIModel.BEST,
        model=OpenAIModel.O1PREVIEW,
        token_limit=128000,
    )
    pass
