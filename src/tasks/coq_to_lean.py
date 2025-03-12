import logging
from pathlib import Path
from typing import Literal

from inspect_ai import Task, eval, task
from inspect_ai.model import CachePolicy
from inspect_ai.solver import basic_agent, system_message

from dataset.prepare import format_translation_input, prepare_dataset
from models import AnthropicModel, OpenAIModel
from prompts.transpilation import (
    REACT_SYSTEM_MESSAGE,
    TRANSLATION_STATE_TEMPLATE,
)
from scorers.transpilation import (
    checker_compiles_scorer,
    isos_proven_scorer,
    lean_compiles_scorer,
)
from solvers.agent import multiphase_agent
from solvers.workflows import SIMPLE_WORKFLOW
from tools.itp import lean_run_tool
from tools.transpilation import (
    add_import_tool,
    add_iso_tool,
    add_lemma_tool,
    edit_proof_tool,
    remove_import_tool,
    remove_iso_tool,
    repair_iso_by_reorder_constructors_tool,
    submit_translation_tool,
)

logger = logging.getLogger(__name__)

EXAMPLE_COQ_FILEPATH = EXAMPLE_COQ_FILEPATH = (
    Path(__file__).parent.parent / "simple-tests" / "StackMachine-statements.v"
)


@task
def coq_to_lean(
    cache: CachePolicy | bool = False,
    agent: Literal["basic", "multiphase"] = "multiphase",
):
    # dataset
    input_msg = format_translation_input(
        TRANSLATION_STATE_TEMPLATE, EXAMPLE_COQ_FILEPATH
    )
    dataset = prepare_dataset([input_msg])

    common_tools = [
        lean_run_tool(),
        submit_translation_tool(
            EXAMPLE_COQ_FILEPATH.read_text()
        ),  # NOTE: This will need rewriting when the input coq file is not hardcoded
        add_import_tool(),
        remove_import_tool(),
        add_lemma_tool(),
        add_iso_tool(),
        remove_iso_tool(),
        edit_proof_tool(),
        repair_iso_by_reorder_constructors_tool(),
    ]

    match agent:
        case "basic":
            solver = basic_agent(
                init=system_message(REACT_SYSTEM_MESSAGE),
                tools=common_tools,
                max_attempts=1,
                message_limit=30,
                cache=cache,
            )
        case "multiphase":
            solver = multiphase_agent(
                workflow=SIMPLE_WORKFLOW.with_tools(common_tools),
            )
    logger.info(f"Using {agent} agent")

    return Task(
        dataset=dataset,
        solver=solver,
        scorer=[
            lean_compiles_scorer(),
            checker_compiles_scorer(),
            isos_proven_scorer(),
        ],
        token_limit=256_000,
    )
