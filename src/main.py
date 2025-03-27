#!/usr/bin/env python
import argparse
from pathlib import Path

from config import SOURCE_DIR
from isomorphism_prover_heuristics import ALL_HEURISTICS
from tasks.coq_to_lean import AnthropicModel, CachePolicy, coq_to_lean, eval
from utils import logging, run_cmd


def make_single_file(
    project_name: str,
    robust: bool = False,
    quiet: bool = False,
    resume: bool = False,
    yes: bool = False,
):
    logging.info(f"Making single file for {project_name}. This may take a while...")
    project_config = {
        "flocq": "./make_single_file.py raw_data/flocq/_CoqProject $(git ls-files --recurse-submodules 'raw_data/flocq/src/*.v' | grep -v _8_12) -o single_file_data/flocq/",
        "CompCert": "(cd raw_data/CompCert && ./configure x86_64-linux -ignore-coq-version) && (cd raw_data/CompCert && make) && ./make_single_file.py raw_data/CompCert/_CoqProject $(git ls-files --recurse-submodules 'raw_data/CompCert/*.v') -o single_file_data/CompCert/",
        "lf": "./make_single_file.py raw_data/lf/_CoqProject $(git ls-files 'raw_data/lf/*.v') -o single_file_data/lf/",
        "plf": "./make_single_file.py raw_data/plf/_CoqProject $(git ls-files 'raw_data/plf/*.v') -o single_file_data/plf/",
        "vfa": "./make_single_file.py raw_data/vfa/_CoqProject $(git ls-files 'raw_data/vfa/*.v') -o single_file_data/vfa/",
        "qc": "./make_single_file.py raw_data/qc/_CoqProject $(git ls-files 'raw_data/qc/*.v') -o single_file_data/qc/",
        "vc": "./make_single_file.py raw_data/vc/_CoqProject $(git ls-files 'raw_data/vc/*.v') -o single_file_data/vc/",
        "slf": "./make_single_file.py raw_data/slf/_CoqProject $(git ls-files 'raw_data/slf/*.v') -o single_file_data/slf/",
    }
    assert project_name in project_config, f"Project {project_name} not found"
    config = project_config[project_name]
    if robust:
        config += " --robust"
    if resume:
        config += " --resume"
    if yes or quiet:
        config += " --yes"
    if quiet:
        config += " --quiet"
    command = f"cd {SOURCE_DIR}/src/dataset"
    run_cmd(f"{command} && {config}", streaming=not quiet)


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
    parser.add_argument(
        "-q",
        "--quiet",
        action="store_true",
        default=False,
        help="Quiet mode",
    )
    parser.add_argument(
        "--resume",
        action=argparse.BooleanOptionalAction,
        default=False,
        help="Resume the build",
    )
    parser.add_argument(
        "-y",
        "--yes",
        action="store_true",
        default=False,
        help="Skip confirmation prompts",
    )
    args = parser.parse_args()
    project_name = args.project

    # Make single file
    if args.rebuild:
        assert Path(f"src/dataset/raw_data/{project_name}").exists(), (
            "Project raw_data does not exist"
        )
        make_single_file(
            project_name,
            robust=args.robust,
            quiet=args.quiet,
            resume=args.resume,
            yes=args.yes,
        )
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
            # model=AnthropicModel.DEBUG,
            model=AnthropicModel.BEST,
            token_limit=args.token_limit,
            message_limit=args.message_limit,
        )
    # If successful, extract statement pairs and add to training set
