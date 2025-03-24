import re
from typing import List, Dict

from coq_tools.split_file import split_coq_file_contents_with_comments


class CoqBlockParser:
    """
    A parser class that splits Coq file contents into chunks and classifies
    each chunk as 'Theoremish', 'Definitionish', or 'Other' using a
    keyword-to-type map.
    """

    # Dictionary for coarse classification by the FIRST word of the chunk.
    # If the first word matches a key, we assign the corresponding type.
    # Otherwise, default to "Other".
    KEYWORD_TYPE_MAP = {
        # Theoremish keywords
        "Lemma": "Theoremish",
        "Theorem": "Theoremish",
        "Corollary": "Theoremish",
        "Proposition": "Theoremish",
        "Example": "Theoremish",
        "Fact": "Theoremish",

        # Definitionish keywords
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
          1) If it contains "Proof." → always "Theoremish".
          2) Otherwise, check the first word. If it appears in KEYWORD_TYPE_MAP,
             return that map's value.
          3) Fallback to "Other" if no keyword match.
        """
        # 1) Check for "Proof."
        if "Proof." in block_text:
            return "Theoremish"

        # 2) Identify the first word of the first non-whitespace line
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
    def get_coq_blocks(file_content: str) -> List[Dict[str, str]]:
        """
        1. Split file content using split_coq_file_contents_with_comments.
        2. Classify each chunk as 'Theoremish', 'Definitionish', or 'Other'.
        3. Return a list of dicts like:
               [
                   {
                     "type": <block_type>,
                     "raw": <the chunk's text>
                   },
                   ...
               ]
        """
        statements = split_coq_file_contents_with_comments(file_content)
        blocks = []

        for statement in statements:
            raw_statement = statement.strip()
            block_type = CoqBlockParser.classify_block(raw_statement)
            blocks.append({
                "type": block_type,
                "raw": raw_statement
            })

        return blocks
