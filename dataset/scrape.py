import os
import re
import pandas as pd
from typing import List, Tuple, Dict

def extract_coq_blocks_with_hierarchy(coq_text: str) -> List[Dict]:
    comment_pattern = re.compile(r'\(\*.*?\*\)', re.DOTALL)
    block_start_keywords = [
        "Fixpoint", "Definition", "Lemma", "Theorem", "Inductive",
        "Corollary", "Proposition", "Example", "Record", "CoFixpoint",
        "Fact", "Module", "Section", "Variable", "Hypothesis", "Axiom",
        "Parameter", "Goal", "Remark", "Notation", "Ltac"
    ]
    block_pattern = re.compile(r'^(?:' + '|'.join(block_start_keywords) + r')\b', re.MULTILINE)
    module_pattern = re.compile(r'\b(Module|Section)\s+(\w+)\b')
    end_pattern = re.compile(r'\bEnd\b')

    coq_text_no_comments = re.sub(comment_pattern, '', coq_text)
    hierarchy = []
    results = []

    lines = coq_text_no_comments.splitlines()
    current_block = ""
    inside_block = False

    for line in lines:
        module_match = module_pattern.match(line)
        end_match = end_pattern.match(line)

        if module_match:
            hierarchy.append(f"{module_match.group(1)}:{module_match.group(2)}")
        elif end_match and hierarchy:
            hierarchy.pop()

        if block_pattern.match(line):
            if inside_block:
                results.append({
                    "proof": current_block.strip(),
                    "path": list(hierarchy) if hierarchy else ["__global__"]
                })
            current_block = line
            inside_block = True
        elif inside_block:
            current_block += "\n" + line
            if line.strip() == "":
                results.append({
                    "proof": current_block.strip(),
                    "path": list(hierarchy) if hierarchy else ["__global__"]
                })
                inside_block = False
                current_block = ""

    if inside_block:
        results.append({
            "proof": current_block.strip(),
            "path": list(hierarchy) if hierarchy else ["__global__"]
        })

    return results

def process_coq_files_with_hierarchy(folder_path: str) -> pd.DataFrame:
    data = []
    
    coq_files = [f for f in os.listdir(folder_path) if f.endswith('.v')]
    total_files = len(coq_files)
    
    for i, filename in enumerate(coq_files):
        file_path = os.path.join(folder_path, filename)
        try:
            with open(file_path, 'r', encoding='utf-8') as file:
                coq_text = file.read()
        except (IOError, UnicodeDecodeError) as e:
            print(f"Error reading {filename}: {e}")
            continue
        
        proofs_with_hierarchy = extract_coq_blocks_with_hierarchy(coq_text)
        data.append({
            'filename': filename,
            'proofs': proofs_with_hierarchy,
            'incomplete_proofs': []  # Assuming no incomplete proofs for simplicity
        })
        
        if (i + 1) % 10 == 0 or i == total_files - 1:
            print(f"Processed {i + 1}/{total_files} files...")
    
    return pd.DataFrame(data)

if __name__ == "__main__":
    folder_path = r'dataset\raw_data\lf'
    output_path = r'dataset\processed_data\coq_proofs_dataset.json'
    
    df = process_coq_files_with_hierarchy(folder_path)
    
    df.to_json(output_path, orient='records', indent=4, force_ascii=False)
