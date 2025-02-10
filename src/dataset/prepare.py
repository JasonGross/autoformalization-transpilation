from pathlib import Path

from inspect_ai.dataset import MemoryDataset, Sample


def prepare_sample(input_msg: str) -> Sample:
    return Sample(input=input_msg)


def prepare_dataset(input_msgs: list[str]) -> MemoryDataset:
    return MemoryDataset([prepare_sample(msg) for msg in input_msgs])


def format_translation_input(prompt_template: str, coq_path: Path) -> str:
    if not coq_path.exists():
        raise FileNotFoundError(f"Coq file not found at {coq_path}")
    with open(coq_path, "r") as f:
        coq_input = f.read()
    return prompt_template.format(coq_script=coq_input)
