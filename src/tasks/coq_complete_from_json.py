import json
from pathlib import Path

from inspect_ai import Task, eval, task
from inspect_ai.dataset import MemoryDataset, Sample
from inspect_ai.solver import generate, system_message, use_tools

from models import AnthropicModel, OpenAIModel
from prompts.completion import ALTERNATE_SYSTEM_MESSAGE
from scorers.completion import coq_proven_scorer
from tools.itp import coq_run_tool
from tools.submission import coq_submit_tool


def load_theorems(json_path: str):
    """Load theorems from JSON file"""
    with open(json_path) as f:
        return json.load(f)


json_path = Path("src/dataset/processed_data/parsed_theorems.json")
theorems = load_theorems(str(json_path))


@task
def coq_completion_from_json():
    """Create a Coq completion task from JSON theorem data"""
    json_path = Path("src/dataset/processed_data/parsed_theorems.json")
    theorems = load_theorems(str(json_path))

    # Create a dataset with all theorems
    dataset_samples = []
    for theorem in theorems:
        input_msg = (
            "\n".join(dep["content"] for dep in theorem["dependencies"])
            + "\n\n"
            + theorem["statement"]
        )
        interface_file_contents = f"""Module Type Interface.
{input_msg}
Proof. Admitted.
End Interface.
"""
        definitions = theorem["name"]
        dataset_samples.append(Sample(input=f"```coq\n{input_msg}\n```", sandbox=True))

    dataset = MemoryDataset(dataset_samples)

    # Return task with same configuration as coq_complete.py
    return Task(
        dataset=dataset,
        solver=[
            system_message(ALTERNATE_SYSTEM_MESSAGE),
            use_tools(
                coq_run_tool(coq_flags=["-Q", ".", "LF"]),
                coq_submit_tool(
                    project_name="LF",
                    interface_file_contents=interface_file_contents,
                    definitions=definitions,
                ),
            ),
            generate(),
        ],
        scorer=coq_proven_scorer(),
    )


if __name__ == "__main__":
    print("Starting evaluation...")
    eval(coq_completion_from_json(), model=OpenAIModel.DEBUG, message_limit=20)
