import os
from helpers import format_coq_file

def preprocess_coq_files(folder_path: str, out_folder: str) -> None:
    if not os.path.exists(out_folder):
        os.makedirs(out_folder)

    coq_files = [f for f in os.listdir(folder_path) if f.endswith('.v')]
    total_files = len(coq_files)

    for i, filename in enumerate(coq_files, start=1):
        input_path = os.path.join(folder_path, filename)
        output_path = os.path.join(out_folder, filename)
        try:
            format_coq_file(input_path, output_path)
            print(f"[{i}/{total_files}] Preprocessed {filename} -> {output_path}")
        except Exception as e:
            print(f"Error processing {filename}: {e}")

if __name__ == "__main__":
    folder_path = r"src\dataset\raw_data\lf"
    out_folder = r"src\dataset\pre_processed_data"
    preprocess_coq_files(folder_path, out_folder)

## "idtac" might not be handled correctly
## Require better logic for module/section End statements
## List.v check