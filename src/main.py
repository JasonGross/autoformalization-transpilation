#!/usr/bin/env python
import sys
from typing import Optional

from config import (
    DEFINITION_PAIRS,
    EXAMPLE_STATEMENTS,
    EXPORT_DIR,
    SOURCE_DIR,
)
from isomorphism_prover import generate_and_prove_iso_interface
from project_util import (
    CoqFile,
    CoqIdentifier,
    CoqProject,
    LeanFile,
    LeanIdentifier,
    LeanProject,
    desigil,
)
from translation_checker import ErrorCode, check_translation
from utils import logging


def extract_and_add(
    c_stms: CoqFile,
    l_stms: LeanFile,
    cl_identifiers: list[tuple[CoqIdentifier, LeanIdentifier]],
) -> bool:
    # Use the identifier list to extract the statements from the file and add them to the training set, if not already in it
    return True


def preprocess_source(src) -> CoqFile | None:  # Optional[CoqProject]) -> CoqFile:
    # if src is None:
    # return []
    return None

    # Extract list of statements from input
    # @@Shiki to explain how we are doing this
    # and add the code to this repo
    # At the moment there is an assumption that we only produce a single CoqFile, which will obviously not hold as project size scales


def extract_coq_identifiers(
    coq: CoqFile | None, sigil: bool = True
) -> list[CoqIdentifier]:
    # Extract identifiers from Coq statements
    if not coq:
        # TODO: Have the actual identifier pairs
        result = [coq_id for coq_id, _ in DEFINITION_PAIRS]
        if not sigil:
            result = [CoqIdentifier(desigil(str(coq_id))) for coq_id in result]
        return result

    else:
        # extract things
        assert False


def translate(
    coq: CoqFile | None, error_code: Optional[str], error: Optional[str]
) -> tuple[LeanFile, list[tuple[CoqIdentifier, LeanIdentifier]]]:
    # If it's not the first attempt, we have an error code and message from the previous failure
    if not coq:
        # TODO: Have the actual identifier pairs
        return LeanFile("\n".join(EXAMPLE_STATEMENTS)), DEFINITION_PAIRS

    else:
        # Translate things!
        return LeanFile("\n"), []


def translate_and_prove(
    lean_export_project: LeanProject,
    lean_project: LeanProject | None,
    coq_project: CoqProject,
    coq_statements: CoqFile | None,
) -> tuple[
    LeanProject,
    LeanProject,
    CoqProject,
    bool,
    LeanFile,
    list[tuple[CoqIdentifier, LeanIdentifier]],
]:
    success = False
    error_code, error = None, None  # Used for subsequent attempts of translation

    coq_identifiers = extract_coq_identifiers(coq_statements)
    coq_project, interface_success, error = generate_and_prove_iso_interface(
        coq_project, coq_identifiers
    )
    if not interface_success:
        assert False, "Failed to generate isomorphism interface!"
        error_code = "isomorphism_interface_failure"

    while True:
        # Translate statements from Coq to Lean
        # TBD by all of us, with varying degrees of handholding
        lean_statements, cl_identifiers = translate(coq_statements, error_code, error)

        lean_export_project, lean_project, coq_project, success, error_code, error = (
            check_translation(
                lean_export_project,
                lean_project,
                coq_project,
                lean_statements,
                cl_identifiers,
            )
        )

        # TODO: we might retry this (or control retries from inspect, TBD)
        match error_code:
            case ErrorCode.ISOMORPHISM_FAILURE:
                assert False, "Failed to prove isomorphisms!"
            case ErrorCode.EXPORT_IMPORT_FAILURE:
                assert False, "Importing from Lean to Coq failed!"
            case ErrorCode.COMPILATION_FAILURE:
                assert False, "Lean code does not compile!"
            case None:
                pass

        if success:
            return (
                lean_export_project,
                lean_project,
                coq_project,
                success,
                lean_statements,
                cl_identifiers,
            )


if __name__ == "__main__":
    # Extract a list of Coq statements from the input file(s)
    # @@Shiki @@Jacob: I expect this to take a filename (or maybe directory path) and return an ordered list of strings (Coq statements) to translate, for example
    # []"""Definition binopDenote (b : binop) : nat -> nat -> nat :=
    # match b with
    #     | Plus => plus
    #     | Times => mult
    # end."""]
    coq_statements = preprocess_source(None)

    # Translate them all into Lean and prove equivalence
    # Will take a list of strings and return a bool and a list of lean statements, for example
    # (True, ["""def binopDenote : Binop → Nat → Nat → Nat
    #   | Binop.plus, x, y  => x + y
    #   | Binop.times, x, y => x * y"""])
    # We expect failures to be like "out of disk space" or "ran out of attempts to try", which should probably be raised rather than returned
    _, coq_project = CoqProject.read(f"{SOURCE_DIR}/iso-checker").clean()
    lean_export_project = LeanProject.read(EXPORT_DIR)
    (
        lean_export_project,
        lean_project,
        coq_project,
        success,
        lean_statements,
        cl_identifiers,
    ) = translate_and_prove(lean_export_project, None, coq_project, coq_statements)

    # If successful, extract statement pairs and add to training set
    if success:
        # Need to decide how this actually works
        # extract_and_add(coq_statements, lean_statements, cl_identifiers)

        # Return success or failure
        logging.info("Success!")
        sys.exit(0)
    else:
        # TODO: Explain in more detail what needs fixing manually
        logging.info("Could not translate and/or prove")
        sys.exit(1)
