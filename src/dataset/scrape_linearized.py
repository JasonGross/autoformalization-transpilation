import os
import json

# Reuse your helpers from the existing helpers.py:
from helpers import formatCoqFile, extractBlocksFromPreprocessed

def scrape_single_coq_file(input_file: str, output_json_path: str) -> None:
    """
    Preprocesses a single linearized .v file (e.g., EverythingLF.v),
    extracts theorem/proof blocks, and saves the result as JSON.
    """

    # 1) Preprocess: remove comments and adjust whitespace
    #    We'll store the preprocessed content in-memory (or you can
    #    store to a temp file). Below we do it in-memory:
    tmp_preprocessed_path = input_file + ".tmp"
    formatCoqFile(input_file, tmp_preprocessed_path)

    # 2) Read the preprocessed content
    with open(tmp_preprocessed_path, "r", encoding="utf-8") as f:
        preprocessed_content = f.read()

    # 3) Extract blocks
    items = extractBlocksFromPreprocessed(preprocessed_content)
    items = [itm for itm in items if itm["raw"].strip() != ""]

    # 4) Build a single JSON structure
    #    We mimic the older structure that had an array of file entries,
    #    but now it's just one entry referencing EverythingLF.v
    data = [
      {
        "fileName": os.path.basename(input_file),
        "type": "coq_file",
        "items": items
      }
    ]

    # 5) Write JSON output
    with open(output_json_path, "w", encoding="utf-8") as out_f:
        json.dump(data, out_f, indent=2, ensure_ascii=False)

    # Clean up temp file if desired
    os.remove(tmp_preprocessed_path)

    print(f"Scraping complete. Wrote {len(items)} blocks to {output_json_path}.")

if __name__ == "__main__":
    # Adjust paths as needed
    input_file = r"src/dataset/single_file_data/lf/EverythingLF.v"
    output_json_path = r"src/dataset/processed_data/coq_proofs_dataset_single.json"

    scrape_single_coq_file(input_file, output_json_path)
