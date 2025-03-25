import re
from typing import List, Dict, Any
import json

from coq_tools.split_file import split_coq_file_contents_with_comments


class CoqBlockParser:
    """
    A parser class that splits Coq file contents into chunks, classifies them,
    and extracts a statement if the chunk is Theoremish or Definitionish.
    """

    KEYWORD_TYPE_MAP = {
        "Lemma": "Theoremish",
        "Theorem": "Theoremish",
        "Corollary": "Theoremish",
        "Proposition": "Theoremish",
        "Example": "Theoremish",
        "Fact": "Theoremish",
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
        before the first '.' in the chunk. Otherwise, return None.
        """
        if block_type not in ("Theoremish", "Definitionish"):
            return None
        return block_text.split('.', 1)[0].strip()

    @staticmethod
    def get_coq_blocks(file_content: str) -> List[Dict[str, Any]]:
        """
        1. Split file content using 'split_coq_file_contents_with_comments'.
        2. Classify each chunk as 'Theoremish', 'Definitionish', or 'Other'.
        3. Extract a 'Statement' for Theoremish/Definitionish chunks.
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



def load_json(json_path):
    with open(json_path, 'r') as f:
        return json.load(f)
    
def chunk_df(data, chunksize, statement_only=True):
    """
    Takes parsed JSON data and returns chunks of specified size.

    Args:
        data (list): List of dicts (parsed JSON).
        chunksize (int): Number of items per chunk.
        statement_only (bool): If True, return only non-null statements.

    Returns:
        List[List[Any]]: Chunked list of data (full entries or just statements).
    """
    if statement_only:
        items = [entry["Statement"] for entry in data if entry["Statement"] is not None]
    else:
        items = data

    return [items[i:i + chunksize] for i in range(0, len(items), chunksize)]


def main():
    
    path = r'/root/autoformalization/src/dataset/processed_data/df.json'
    data = load_json(path)

    chunks = chunk_df(data, 2)

    print(chunks[20])

if __name__ == "__main__":
    main()
