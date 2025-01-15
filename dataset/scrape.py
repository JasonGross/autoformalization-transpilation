import os
import re
import json
from typing import List, Tuple, Dict, Any

def extract_coq_blocks_without_comments(coq_text: str) -> List[str]:
    # Remove comments first
    comment_pattern = re.compile(r'\(\*.*?\*\)', re.DOTALL)
    coq_text_no_comments = re.sub(comment_pattern, '', coq_text)
    
    # Extract proof blocks with comprehensive pattern
    block_pattern = re.compile(
        r'((?:Fixpoint|Function|Definition|Inductive|CoInductive|'
        r'Instance|Class|Record|Notation|Theorem|Lemma|Example|'
        r'Fact|Proposition|Corollary|Remark|Axiom|Parameter|'
        r'Variable|Variables|Hypothesis|Hypotheses|Scheme)'
        r'.*?(?:Qed\.|Admitted\.|end\.|}\.|defined\.|\.)\s*)',
        re.DOTALL
    )
    return block_pattern.findall(coq_text_no_comments)

def separate_proofs(blocks: List[str]) -> Tuple[List[str], List[str]]:
    filtered_blocks, incomplete_proofs = [], []
    for block in blocks:
        (incomplete_proofs if 'Admitted.' in block else filtered_blocks).append(block)
    return filtered_blocks, incomplete_proofs

def process_coq_file(file_path: str) -> Dict[str, Any]:
    with open(file_path, 'r', encoding='utf-8') as file:
        coq_text = file.read()
    
    proof_blocks = extract_coq_blocks_without_comments(coq_text)
    filtered_proofs, incomplete_proofs = separate_proofs(proof_blocks)
    
    # Track module/section hierarchy with proper prefixes
    current_path = []
    lines = coq_text.split('\n')
    path_map = {0: ["__global__"]}
    current_pos = 0
    
    for line in lines:
        line = line.strip()
        
        # Handle module start
        if line.startswith('Module ') and not line.startswith('Module Type'):
            name = line.split()[1].rstrip('.')
            current_path.append(f"Module:{name}")
            
        # Handle section start    
        elif line.startswith('Section '):
            name = line.split()[1].rstrip('.')
            current_path.append(f"Section:{name}")
            
        # Handle end of module/section    
        elif line.startswith('End '):
            name = line.split()[1].rstrip('.')
            # Look for matching module/section name with prefix
            if current_path:
                if f"Module:{name}" in current_path or f"Section:{name}" in current_path:
                    current_path.pop()
        
        # Store current path at this position
        path_map[current_pos] = list(current_path) if current_path else ["__global__"]
        current_pos += len(line) + 1

    result = {
        "filename": os.path.basename(file_path),
        "proofs": [],
        "incomplete_proofs": []
    }
    
    # Associate proofs with their paths
    for proof in filtered_proofs + incomplete_proofs:
        proof_pos = coq_text.find(proof)
        valid_positions = [k for k in path_map.keys() if k <= proof_pos]
        path = path_map[max(valid_positions)] if valid_positions else ["__global__"]
        
        proof_info = {
            "proof": proof,
            "path": path
        }
        
        if proof in filtered_proofs:
            result["proofs"].append(proof_info)
        else:
            result["incomplete_proofs"].append(proof_info)
    
    return result

def process_coq_files(folder_path: str) -> List[Dict[str, Any]]:
    results = []
    v_files = [f for f in os.listdir(folder_path) if f.endswith('.v')]
    total_files = len(v_files)
    
    for i, filename in enumerate(v_files):
        file_path = os.path.join(folder_path, filename)
        try:
            result = process_coq_file(file_path)
            results.append(result)
        except Exception as e:
            print(f"Error processing {filename}: {e}")
            continue
        
        if (i + 1) % 10 == 0 or i == total_files - 1:
            print(f"Processed {i + 1}/{total_files} files...")
    
    return results

if __name__ == "__main__":
    folder_path = r'dataset\raw_data\lf'
    output_path = r'dataset\processed_data\coq_proofs_dataset.json'
    
    results = process_coq_files(folder_path)
    
    with open(output_path, 'w', encoding='utf-8') as f:
        json.dump(results, f, indent=2, ensure_ascii=False)
