import json
from typing import List, Dict
from dataclasses import dataclass
import re

@dataclass
class TheoremData:
    name: str  # The name of the theorem
    statement: str  # Full theorem statement
    proof: str
    dependencies: List[Dict[str, str]]
    source_file: str

def extract_theorem_name(statement: str) -> str:
    """Extract the theorem name from the statement."""
    # Match pattern "Theorem name :" or "Theorem name:"
    match = re.match(r'Theorem\s+([^:]+?)\s*:', statement)
    if match:
        return match.group(1).strip()
    return ""

def extract_theorem_statement(raw: str) -> str:
    """Extract just the theorem statement before the Proof."""
    parts = raw.split("Proof.")
    if len(parts) > 1:
        return parts[0].strip()
    return raw.strip()

def extract_proof(raw: str) -> str:
    """Extract the proof part after 'Proof.'"""
    parts = raw.split("Proof.")
    if len(parts) > 1:
        return "Proof." + parts[1].strip()
    return ""

def parse_coq_dataset(json_data: List[dict]) -> List[TheoremData]:
    theorems = []

    # Iterate through each Coq file
    for file_data in json_data:
        current_dependencies = []  # Reset dependencies for each file
        file_name = file_data["fileName"]

        # Process items in this file
        for item in file_data["items"]:
            item_type = item.get("type", "")
            raw_content = item.get("raw", "").strip()

            if item_type == "theorem":
                # Create new theorem entry
                statement = extract_theorem_statement(raw_content)
                name = extract_theorem_name(statement)
                proof = extract_proof(raw_content)

                theorem = TheoremData(
                    name=name,
                    statement=statement,
                    proof=proof,
                    dependencies=[dep.copy() for dep in current_dependencies],
                    source_file=file_name
                )
                theorems.append(theorem)
            else:
                # Add to dependencies
                if raw_content:  # Only add non-empty content
                    current_dependencies.append({
                        "type": item_type,
                        "content": raw_content
                    })

    return theorems

def save_processed_dataset(theorems: List[TheoremData], output_file: str):
    """Save the processed dataset to a JSON file."""
    processed_data = []
    for theorem in theorems:
        processed_data.append({
            "name": theorem.name,
            "statement": theorem.statement,
            "proof": theorem.proof,
            "dependencies": theorem.dependencies,
            "source_file": theorem.source_file
        })

    with open(output_file, 'w', encoding='utf-8') as f:
        json.dump(processed_data, f, indent=2)

def main():
    # Read the input JSON file
    with open('src/dataset/processed_data/coq_proofs_dataset.json', 'r', encoding='utf-8') as f:
        json_data = json.load(f)

    # Parse the dataset
    theorems = parse_coq_dataset(json_data)

    # Save the processed dataset
    save_processed_dataset(theorems, 'src/dataset/processed_data/parsed_theorems.json')

    # Print some statistics
    print(f"Processed {len(theorems)} theorems")

    # Group theorems by source file
    file_counts = {}
    for theorem in theorems:
        file_counts[theorem.source_file] = file_counts.get(theorem.source_file, 0) + 1

    print("\nTheorems per file:")
    for file_name, count in file_counts.items():
        print(f"{file_name}: {count} theorems")

    print("\nSample theorem:")
    print(f"Source file: {theorems[0].source_file}")
    print(f"Name: {theorems[0].name}")
    print(f"Statement: {theorems[0].statement}")
    print(f"Proof: {theorems[0].proof}")
    print(f"Number of dependencies: {len(theorems[0].dependencies)}")

if __name__ == "__main__":
    main()