import re
from typing import List, Dict


class CoqBlockParser:
    """
    A parser class to encapsulate the logic for splitting and classifying
    Coq text blocks.
    """

    # Added "Compute" to the list of known Coq starters
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
            "Intros": "Intros"
        }

        lines = block_text.strip().split('\n')
        if not lines:
            return "Misc"

        first_line = lines[0].strip()

        # Check dictionary-based approach: see if the block starts
        # with a recognized keyword.
        for key, value in block_type_map.items():
            if first_line.startswith(key):
                return value

        return "Misc"

    @staticmethod
    def get_coq_blocks(file_content: str) -> List[Dict[str, str]]:
        """
        Remove (* ... *) comments, split into logical blocks, and classify each
        block. Return a list of dicts like [{"type": ..., "raw": ...}, ...].
        """
        comment_pattern = re.compile(r'\(\*.*?\*\)', re.DOTALL)
        content_no_comments = re.sub(comment_pattern, '', file_content)

        lines = [line.rstrip() for line in content_no_comments.split('\n')]

        blocks = []
        current_block = []
        collecting_proof = False

        def flush_block() -> None:
            """
            Finalize the current block, classify it, and add it to blocks
            if non-empty.
            """
            nonlocal current_block
            # Trim empty lines from start/end
            while current_block and not current_block[0].strip():
                current_block.pop(0)
            while current_block and not current_block[-1].strip():
                current_block.pop()

            if current_block:
                block_text = "\n".join(current_block)
                block_type = CoqBlockParser.classify_block(block_text)
                blocks.append({
                    "type": block_type,
                    "raw": block_text.strip()
                })
            current_block = []

        for line in lines:
            stripped_line = line.strip()
            if collecting_proof:
                current_block.append(line)
                if stripped_line in CoqBlockParser.proofEndings:
                    flush_block()
                    collecting_proof = False
            else:
                if CoqBlockParser.is_block_starter(line):
                    flush_block()
                    current_block.append(line)
                elif stripped_line == "Proof.":
                    current_block.append(line)
                    collecting_proof = True
                else:
                    current_block.append(line)

        flush_block()
        return blocks
