#!/usr/bin/env python
from pathlib import Path

from tasks.coq_to_lean import AnthropicModel, CachePolicy, coq_to_lean, eval

if __name__ == "__main__":
    # Extract a list of Coq statements from the input file(s)
    # @@Shiki @@Jacob: I expect this to take a filename (or maybe directory path) and return an ordered list of strings (Coq statements) to translate, for example
    # []"""Definition binopDenote (b : binop) : nat -> nat -> nat :=
    # match b with
    #     | Plus => plus
    #     | Times => mult
    # end."""]
    eval_log = eval(
        coq_to_lean(
            coq_filepath=Path(__file__).parent
            / "simple-tests"
            / "StackMachine-statements.v",
            cache=CachePolicy(expiry=None, per_epoch=False),
            agent="basic",
            seed="",
        ),
        # model=OpenAIModel.BEST,
        # model=OpenAIModel.O1PREVIEW,
        model=AnthropicModel.BEST,
        token_limit=256_000,
    )
    # # If successful, extract statement pairs and add to training set
    # if success:
    #     # Need to decide how this actually works
    #     # extract_and_add(coq_statements, lean_statements, cl_identifiers)

    #     # Return success or failure
    #     logging.info("Success!")
    #     sys.exit(0)
    # else:
    #     # TODO: Explain in more detail what needs fixing manually
    #     logging.info("Could not translate and/or prove")
    #     sys.exit(1)
