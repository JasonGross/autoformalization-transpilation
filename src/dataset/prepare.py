from pathlib import Path

from inspect_ai.dataset import MemoryDataset, Sample
from project_util import extract_coq_identifiers_str


def prepare_sample(input_msg: str) -> Sample:
    return Sample(input=input_msg)


def prepare_dataset(input_msgs: list[str]) -> MemoryDataset:
    return MemoryDataset([prepare_sample(msg) for msg in input_msgs])


def format_translation_input(prompt_template: str, coq_path: Path, coq_identifiers: list[str] | None = None) -> str:
    if not coq_path.exists():
        raise FileNotFoundError(f"Coq file not found at {coq_path}")
    coq_input = coq_path.read_text()
    if coq_identifiers is None:
        coq_identifiers = extract_coq_identifiers_str(coq_input, sigil=False)
    return prompt_template.format(coq_script=coq_input, coq_identifiers=coq_identifiers)
