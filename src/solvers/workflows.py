from dataclasses import dataclass, field
from typing import Iterator, Self

from inspect_ai.tool import Tool

from prompts.transpilation import (
    MULTIPHASE_ANALYZE_MESSAGE,
    MULTIPHASE_FORMAT_OUTPUT_MESSAGE,
    MULTIPHASE_MAP_IDENTIFIERS_MESSAGE,
    MULTIPHASE_SYSTEM_MESSAGE,
    MULTIPHASE_TRANSLATE_MESSAGE,
)
from tools.transpilation import (
    pop_statement_from_queue_tool,
    pop_translation_from_queue_tool,
    push_statement_to_queue_tool,
    push_translation_to_queue_tool,
    swap_statements_in_queue_tool,
    update_identifier_mappings_tool,
    view_identifier_mappings_tool,
    view_statement_queue_tool,
)


@dataclass
class Phase:
    name: str
    prompt: str
    tools: list[Tool]
    number: int | None = None


@dataclass
class Workflow:
    system_prompt: str
    phases: list[Phase]
    common_tools: list[Tool] = field(default_factory=list)

    def __post_init__(self):
        for i, phase in enumerate(self.phases):
            phase.number = i + 1
            phase.prompt = phase.prompt.format(
                phase_number=phase.number, total_phases=len(self)
            )

    def with_tools(self, tools: list[Tool]) -> Self:
        self.common_tools.extend(tools)
        return self

    def __iter__(self) -> Iterator[Phase]:
        return iter(self.phases)

    def __len__(self) -> int:
        return len(self.phases)


# NOTE: This is basically just a config - probably better placed in a yaml/json file
SIMPLE_WORKFLOW = Workflow(
    system_prompt=MULTIPHASE_SYSTEM_MESSAGE,
    phases=[
        Phase(
            name="ANALYZE",
            prompt=MULTIPHASE_ANALYZE_MESSAGE,
            tools=[
                push_statement_to_queue_tool(),
                pop_statement_from_queue_tool(),
                view_statement_queue_tool(),
                swap_statements_in_queue_tool(),
            ],
        ),
        Phase(
            name="TRANSLATE",
            prompt=MULTIPHASE_TRANSLATE_MESSAGE,
            tools=[
                push_translation_to_queue_tool(),
                pop_translation_from_queue_tool(),
                pop_statement_from_queue_tool(),
                view_statement_queue_tool(),
            ],
        ),
        Phase(
            name="MAP_IDENTIFIERS",
            prompt=MULTIPHASE_MAP_IDENTIFIERS_MESSAGE,
            tools=[
                update_identifier_mappings_tool(),
                view_identifier_mappings_tool(),
            ],
        ),
        Phase(name="FORMAT_OUTPUT", prompt=MULTIPHASE_FORMAT_OUTPUT_MESSAGE, tools=[]),
    ],
)
