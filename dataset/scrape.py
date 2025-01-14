import os
import re
import pandas as pd
from typing import List, Tuple

def extract_coq_blocks_without_comments(coq_text: str) -> List[str]:
    comment_pattern = re.compile(r'\(\*.*?\*\)', re.DOTALL)
    block_pattern = re.compile(r'((?:Fixpoint|Definition|Lemma|Theorem).*?(?:Qed\.|Admitted\.|end\.))', re.DOTALL)
    coq_text_no_comments = re.sub(comment_pattern, '', coq_text)
    return block_pattern.findall(coq_text_no_comments)

def separate_proofs(blocks: List[str]) -> Tuple[List[str], List[str]]:
    filtered_blocks, incomplete_proofs = [], []
    for block in blocks:
        (incomplete_proofs if 'Admitted.' in block else filtered_blocks).append(block)
    return filtered_blocks, incomplete_proofs

def process_coq_files(folder_path: str) -> pd.DataFrame:
    data = []
    
    # Filter only .v files before counting and iterating
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
        
        all_proofs = extract_coq_blocks_without_comments(coq_text)
        filtered_proofs, incomplete_proofs = separate_proofs(all_proofs)
        data.append({
            'filename': filename,
            'proofs': filtered_proofs,
            'incomplete_proofs': incomplete_proofs,
            'all_proofs': all_proofs
        })
        
        if (i + 1) % 10 == 0 or i == total_files - 1:
            print(f"Processed {i + 1}/{total_files} files...")
    
    return pd.DataFrame(data)

if __name__ == "__main__":
    folder_path = r'C:\Users\User\Downloads\lf\lf'
    output_path = r'C:\Users\User\Downloads\coq_proofs_dataset.json'
    
    df = process_coq_files(folder_path)
    
    df.to_json(output_path, orient='records', indent=4, force_ascii=False)
