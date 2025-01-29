import os
import json

def reconstruct_coq_files(input_json_path: str, output_folder: str) -> None:
    with open(input_json_path, "r", encoding="utf-8") as in_f:
        data = json.load(in_f)

    total_files = len(data)
    
    for i, file_data in enumerate(data, start=1):
        filename = file_data["fileName"]
        output_path = os.path.join(output_folder, filename)
        
        with open(output_path, "w", encoding="utf-8") as f:
            for item in file_data["items"]:
                raw_text = item["raw"]
                f.write(f"{raw_text}\n\n")
        
        print(f"[{i}/{total_files}] Reconstructed {filename}.")

    print(f"Done! Reconstructed {total_files} files into {output_folder}")

if __name__ == "__main__":
    input_json_path = r"src\dataset\processed_data\coq_proofs_dataset.json"
    output_folder = r"src\dataset\reconstructed_files"
    os.makedirs(output_folder, exist_ok=True)
    reconstruct_coq_files(input_json_path, output_folder)
