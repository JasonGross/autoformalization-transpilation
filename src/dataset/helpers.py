import re
from typing import List, Dict, Any

from coq_tools.split_file import split_coq_file_contents_with_comments


class CoqBlockParser:
    """
    A parser class that splits Coq file contents into chunks, classifies them,
    and extracts a statement if the chunk is Theoremish or Definitionish.
    """

    KEYWORD_TYPE_MAP = {
        # Theoremish
        "Lemma": "Theoremish",
        "Theorem": "Theoremish",
        "Corollary": "Theoremish",
        "Proposition": "Theoremish",
        "Example": "Theoremish",
        "Fact": "Theoremish",

        # Definitionish
        "Definition": "Definitionish",
        "Fixpoint": "Definitionish",
        "Inductive": "Definitionish",
        "CoFixpoint": "Definitionish",
        "Record": "Definitionish",
    }

    @staticmethod
    def classify_block(block_text: str) -> str:
        """
        Classify a block based on:
          1) If it contains 'Proof.' → always 'Theoremish'.
          2) Otherwise, check the first word in KEYWORD_TYPE_MAP.
          3) Fallback to 'Other'.
        """
        if "Proof." in block_text:
            return "Theoremish"

        stripped_block = block_text.lstrip()
        if not stripped_block:
            return "Other"

        first_line = stripped_block.split('\n', 1)[0]
        first_word_match = re.match(r'^(\S+)', first_line)
        if not first_word_match:
            return "Other"

        first_word = first_word_match.group(1)
        return CoqBlockParser.KEYWORD_TYPE_MAP.get(first_word, "Other")

    @staticmethod
    def extract_statement(block_text: str, block_type: str) -> Any:
        """
        If the block is Theoremish or Definitionish, return everything
        before the first '.' in the chunk. Otherwise, return None,
        which becomes 'null' in JSON.
        """
        if block_type not in ("Theoremish", "Definitionish"):
            return None

        # Grab everything up to the first '.' (if any), then strip whitespace.
        return block_text.split('.', 1)[0].strip()

    @staticmethod
    def get_coq_blocks(file_content: str) -> List[Dict[str, Any]]:
        """
        1. Split file content using 'split_coq_file_contents_with_comments'.
        2. Classify each chunk as 'Theoremish', 'Definitionish', or 'Other'.
        3. Extract a 'Statement' for Theoremish/Definitionish chunks; return
           None if 'Other'.
        4. Return a list of dicts with keys:
               {
                 "Type": <block_type>,
                 "Chunk": <chunk_text>,
                 "Statement": <str or None>
               }
        """
        statements = split_coq_file_contents_with_comments(file_content)
        blocks = []

        for chunk in statements:
            block_type = CoqBlockParser.classify_block(chunk)
            statement_text = CoqBlockParser.extract_statement(chunk, block_type)
            blocks.append({
                "Type": block_type,
                "Chunk": chunk,
                "Statement": statement_text
            })

        return blocks
