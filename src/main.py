#!/usr/bin/env python
import argparse
from pathlib import Path

from config import SOURCE_DIR
from isomorphism_prover_heuristics import ALL_HEURISTICS
from tasks.coq_to_lean import AnthropicModel, CachePolicy, coq_to_lean, eval
from utils import logging, run_cmd


def make_single_file(project_name: str, robust: bool = False):
    logging.info(f"Making single file for {project_name}. This may take a while...")
    project_config = {
        "flocq": "./make_single_file.py raw_data/flocq/_CoqProject $(git ls-files --recurse-submodules 'raw_data/flocq/src/*.v' | grep -v _8_12) -o single_file_data/flocq/",
        "CompCert": "(cd raw_data/CompCert && ./configure x86_64-linux -ignore-coq-version) && (cd raw_data/CompCert && make) && ./make_single_file.py raw_data/CompCert/_CoqProject $(git ls-files --recurse-submodules 'raw_data/CompCert/*.v') -o single_file_data/CompCert/",
        "lf": "./make_single_file.py raw_data/lf/_CoqProject $(git ls-files 'raw_data/lf/*.v') -o single_file_data/lf/",
    }
    assert project_name in project_config, f"Project {project_name} not found"
    config = project_config[project_name]
    if robust:
        config += " --robust"
    command = f"cd {SOURCE_DIR}/src/dataset"
    run_cmd(f"{command} && {config}")


if __name__ == "__main__":
    # Process arguments
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--project", required=False, help="Name of the project to process", default="lf"
    )
    parser.add_argument(
        "--file",
        default="simple-tests/incomplete_statements.v",
        help="Path to the file to translate",
    )
    parser.add_argument(
        "--rebuild",
        action=argparse.BooleanOptionalAction,
        default=False,
        help="Do project processing",
    )
    parser.add_argument(
        "--robust",
        action=argparse.BooleanOptionalAction,
        default=False,
        help="Get all files, rather than just the ones with admits",
    )
    parser.add_argument(
        "--translation",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="Do project translation",
    )
    parser.add_argument(
        "--message-limit",
        type=int,
        default=30,
        help="Message limit for the model",
    )
    parser.add_argument(
        "--token-limit",
        type=int,
        default=128_000,
        help="Token limit for the model",
    )
    parser.add_argument(
        "--heuristics",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="Use all heuristics",
    )
    parser.add_argument(
        "--seed",
        type=str,
        default="",
        help="Seed for the messages, to allow bypassing the cache in a controlled way",
    )
    args = parser.parse_args()
    project_name = args.project

    # Make single file
    if args.rebuild:
        assert Path(f"src/dataset/raw_data/{project_name}").exists(), (
            "Project raw_data does not exist"
        )
        make_single_file(project_name, robust=args.robust)
    # Chunk the single file
    # @@Shiki

    if args.translation:
        # Translate Coq files to Lean
        eval_log = eval(
            coq_to_lean(
                coq_filepath=Path(__file__).parent / args.file,
                cache=CachePolicy(expiry=None, per_epoch=False),
                agent="basic",
                seed=args.seed,
                autofix_heuristics=ALL_HEURISTICS if args.heuristics else (),
                message_limit=args.message_limit,
                token_limit=args.token_limit,
            ),
            # model=OpenAIModel.BEST,
            # model=OpenAIModel.O1PREVIEW,
            model=AnthropicModel.BEST,
            token_limit=args.token_limit,
            message_limit=args.message_limit,
        )
    # If successful, extract statement pairs and add to training set
