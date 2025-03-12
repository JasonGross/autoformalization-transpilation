from dataclasses import dataclass
from enum import StrEnum

from inspect_ai.model import (
    CachePolicy,
    ChatMessageSystem,
    ChatMessageUser,
    call_tools,
    get_model,
)
from inspect_ai.solver import Generate, Solver, TaskState, chain, solver, system_message
from inspect_ai.tool import Tool

from solvers.workflows import Workflow


@solver
def multiphase_agent(
    workflow: Workflow,
    cache: bool | CachePolicy = False,
) -> Solver:
    async def solve(state: TaskState, generate: Generate) -> TaskState:
        model = get_model()

        for phase in workflow:
            # clear the messages at the start of each phase
            state.messages = [
                ChatMessageSystem(content=workflow.system_prompt),
                ChatMessageUser(content=state.input_text),
                ChatMessageUser(content=phase.prompt),
            ]
            while True:
                generation_output = await model.generate(
                    [
                        *state.messages,
                    ],
                    tools=workflow.common_tools + phase.tools,
                    cache=cache,
                )
                state.messages.append(generation_output.message)

                if not generation_output.message.tool_calls:
                    break

                tool_results = await call_tools(
                    generation_output.message, workflow.common_tools + phase.tools
                )
                state.messages.extend(tool_results)

                if state.completed:
                    break

        return state

    return solve
