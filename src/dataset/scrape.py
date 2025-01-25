import os
import json
from helpers import extract_blocks_from_preprocessed

def scrape_preprocessed_coq_files(input_folder: str, output_json_path: str) -> None:
    results = []
    coq_files = [f for f in os.listdir(input_folder) if f.endswith('.v')]
    total_files = len(coq_files)
    for i, filename in enumerate(coq_files, start=1):
        file_path = os.path.join(input_folder, filename)
        with open(file_path, "r", encoding="utf-8") as f:
            content = f.read()
        items = extract_blocks_from_preprocessed(content)
        file_json = {
            "fileName": filename,
            "type": "coq_file",
            "items": items
        }
        results.append(file_json)
        print(f"[{i}/{total_files}] Parsed {filename} -> {len(items)} blocks.")
    with open(output_json_path, "w", encoding="utf-8") as out_f:
        json.dump(results, out_f, indent=2, ensure_ascii=False)
    print(f"Done! Wrote {len(results)} file entries to {output_json_path}")

if __name__ == "__main__":
    input_folder = r"src\dataset\pre_processed_data"
    output_json_path = r"src\dataset\processed_data\coq_proofs_dataset.json"
    scrape_preprocessed_coq_files(input_folder, output_json_path)
