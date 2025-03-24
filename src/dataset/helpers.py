import re
from typing import List, Dict

from coq_tools.split_file import split_coq_file_contents_with_comments


class CoqBlockParser:
    """
    A parser class to encapsulate the logic for splitting and classifying
    Coq text blocks.
    """

    # Keep your existing list of block starters
    blockStarters = [
        "Fixpoint", "Definition", "Lemma", "Theorem", "Inductive",
        "Corollary", "Proposition", "Example", "Record", "CoFixpoint",
        "Fact", "Module", "Section", "Variable", "Hypothesis", "Axiom",
        "Parameter", "Goal", "Remark", "Notation", "Ltac", "Set", "Unset",
        "Require", "Import", "Export", "From", "Check", "Hint", "Create",
        "End", "Compute"
    ]

    proofEndings = ["Qed.", "Defined.", "Admitted.", "Abort."]

    @staticmethod
    def is_block_starter(line: str) -> bool:
        """
        Return True if the given line starts with a known Coq block keyword.
        """
        stripped_line = line.lstrip()
        for starter in CoqBlockParser.blockStarters:
            # The pattern enforces that the line starts with the block keyword
            pattern = r"^" + re.escape(starter) + r"(\b|\s|\()"
            if re.match(pattern, stripped_line):
                return True
        return False

    @staticmethod
    def classify_block(block_text: str) -> str:
        """
        Return a coarse classification of a block based on its first line.
        Uses a dictionary-based approach for clarity.
        """
        block_type_map = {
            "Set": "global_directive",
            "Unset": "global_directive",
            "Require": "Import",
            "Import": "Import",
            "Export": "Import",
            "From": "Import",
            "Fixpoint": "Fixpoint",
            "Definition": "Definition",
            "Lemma": "Lemma",
            "Theorem": "Theorem",
            "Ltac": "Ltac",
            "Inductive": "Inductive",
            "Check": "Check",
            "Hint": "Hint",
            "Example": "Example",
            "Module": "Module",
            "Section": "Section",
            "End": "End",
            "Compute": "Compute",
            "Notation": "Notation",
            "Intros": "Intros",
        }

        lines = block_text.strip().split('\n')
        if not lines:
            return "Misc"

        first_line = lines[0].strip()

        # Use the dictionary-based approach
        for key, value in block_type_map.items():
            if first_line.startswith(key):
                return value

        return "Misc"

    @staticmethod
    def get_coq_blocks(file_content: str) -> List[Dict[str, str]]:
        """
        Split the file content into Coq statements using split_coq_file_contents_with_comments,
        then classify each block. Return a list of dicts like:
            [
                {"type": <block_type>, "raw": <the block text>},
                ...
            ]
        """
        # Use the new function to get Coq statements
        statements = split_coq_file_contents_with_comments(file_content)

        blocks = []
        for statement in statements:
            # Trim and classify
            block_type = CoqBlockParser.classify_block(statement)
            blocks.append({
                "type": block_type,
                "raw": statement.strip()
            })

        return blocks
