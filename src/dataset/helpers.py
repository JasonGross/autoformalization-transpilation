import re
from typing import List, Dict

def remove_comments(coq_text: str) -> str:
    """Remove comments from Coq text."""
    comment_pattern = re.compile(r'\(\*.*?\*\)', re.DOTALL)
    return re.sub(comment_pattern, '', coq_text)

def parse_hierarchy(lines: List[str]) -> List[str]:
    """Parse module and section hierarchy from lines."""
    module_pattern = re.compile(r'\b(Module|Section)\s+(\w+)\b')
    end_pattern = re.compile(r'\bEnd\b')
    hierarchy = []

    for line in lines:
        module_match = module_pattern.match(line)
        end_match = end_pattern.match(line)

        if module_match:
            hierarchy.append(f"{module_match.group(1)}:{module_match.group(2)}")
        elif end_match and hierarchy:
            hierarchy.pop()

    return hierarchy

def extract_blocks(lines: List[str], hierarchy: List[str]) -> List[Dict]:
    """Extract Coq blocks with hierarchy from lines."""
    block_start_keywords = {
        "Fixpoint", "Definition", "Lemma", "Theorem", "Inductive", "Corollary",
        "Proposition", "Example", "Record", "CoFixpoint", "Fact", "Module", "Section",
        "Variable", "Hypothesis", "Axiom", "Parameter", "Goal", "Remark", "Notation", "Ltac"
    }
    results = []
    current_block = []
    inside_block = False

    for line in lines:
        stripped_line = line.strip()
        if any(stripped_line.startswith(keyword) for keyword in block_start_keywords):
            if inside_block:
                results.append({
                    "block": "\n".join(current_block).strip(),
                    "path": list(hierarchy) if hierarchy else ["__global__"]
                })
                current_block = []
            current_block.append(line)
            inside_block = True
        elif inside_block:
            current_block.append(line)
            if not stripped_line:  # Empty line indicates end of block
                results.append({
                    "block": "\n".join(current_block).strip(),
                    "path": list(hierarchy) if hierarchy else ["__global__"]
                })
                inside_block = False
                current_block = []

    if inside_block:  # Handle last block if still inside one
        results.append({
            "block": "\n".join(current_block).strip(),
            "path": list(hierarchy) if hierarchy else ["__global__"]
        })

    return results