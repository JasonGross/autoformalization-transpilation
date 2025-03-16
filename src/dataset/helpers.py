import re
from typing import List, Dict

class CoqBlockParser:
    """
    A parser class to encapsulate the logic for splitting and classifying Coq text blocks.
    """

    blockStarters = [
        "Fixpoint", "Definition", "Lemma", "Theorem", "Inductive", "Corollary",
        "Proposition", "Example", "Record", "CoFixpoint", "Fact", "Module",
        "Section", "Variable", "Hypothesis", "Axiom", "Parameter", "Goal",
        "Remark", "Notation", "Ltac", "Set", "Unset", "Require", "Import",
        "Export", "From", "Check", "Hint", "Create", "End"
    ]

    proofEndings = ["Qed.", "Defined.", "Admitted.", "Abort."]

    @staticmethod
    def is_block_starter(line: str) -> bool:
        """
        Returns True if the given line starts with a known Coq block keyword.
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
        Returns a coarse classification of a block based on its first line.
        """
        lines = block_text.strip().split('\n')
        if not lines:
            return "Misc"

        first_line = lines[0].strip()

        if first_line.startswith("Set") or first_line.startswith("Unset"):
            return "global_directive"
        if first_line.startswith("Require"):
            return "Import"
        if first_line.startswith("Fixpoint"):
            return "Fixpoint"
        if first_line.startswith("Lemma"):
            return "Lemma"
        if first_line.startswith("Theorem"):
            return "Theorem"
        if first_line.startswith("Definition"):
            return "Definition"
        if first_line.startswith("Ltac"):
            return "Ltac"
        if first_line.startswith("Inductive"):
            return "Inductive"
        if first_line.startswith("Check"):
            return "Dheck"
        if first_line.startswith("Hint"):
            return "Hint"
        if first_line.startswith("Create HintDb"):
            return "Create_hint_db"
        if (first_line.startswith("Import") or
            first_line.startswith("Export") or
            first_line.startswith("From")):
            return "Import"
        if first_line.startswith("Example"):
            return "Example"
        if first_line.startswith("Module"):
            return "Module"
        if first_line.startswith("Section"):
            return "Section"
        if first_line.startswith("End"):
            return "End"
        if first_line.startswith("Compute"):
            return "Compute"
        if first_line.startswith("Notation"):
            return "Notation"
        if first_line.startswith("Intros"):
            return "Intros"

        return "Misc"

    @staticmethod
    def get_coq_blocks(file_content: str) -> List[Dict[str, str]]:
        """
        Takes the full text of a Coq file, removes comments,
        splits it into logical blocks, and classifies each block.
        Returns a list of dicts: [{"type": ..., "raw": ...}, ...].
        """

        # Remove (* ... *) comments (including multiline)
        comment_pattern = re.compile(r'\(\*.*?\*\)', re.DOTALL)
        content_no_comments = re.sub(comment_pattern, '', file_content)

        # Split into lines, strip trailing spaces
        lines = [line.rstrip() for line in content_no_comments.split('\n')]

        blocks = []
        current_block = []
        collecting_proof = False

        def flush_block():
            """
            Utility function to finalize the current block, classify it,
            and add it to the blocks list if non-empty.
            """
            nonlocal current_block
            # Remove blank lines from start and end
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
            # If we are in proof mode, keep reading until we find a proof ending
            if collecting_proof:
                current_block.append(line)
                if stripped_line in CoqBlockParser.proofEndings:
                    flush_block()
                    collecting_proof = False
            else:
                # If this line starts a new block, flush the old one first
                if CoqBlockParser.is_block_starter(line):
                    flush_block()
                    current_block.append(line)
                elif stripped_line == "Proof.":
                    current_block.append(line)
                    collecting_proof = True
                else:
                    current_block.append(line)

        # Flush whatever is left
        flush_block()

        return blocks
