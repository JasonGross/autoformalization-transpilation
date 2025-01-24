import json

json_file_path = 'data/processed/coq_proofs_dataset.json'

# Load JSON content from the file
with open(json_file_path, 'r', encoding='utf-8') as file:
    data = json.load(file)

# Define the keywords to filter
keywords = {"Inductive", "Definition", "Fixpoint", "CoFixpoint", "Theorem", "Lemma"}

# Process each file block
for file_entry in data:
    filename = file_entry["filename"].replace(".v", "")
    result_list = []
    
    for block_entry in file_entry["blocks"]:
        block_lines = block_entry["block"].splitlines()
        first_line = block_lines[0].strip() if block_lines else ""
        first_word = first_line.split()[0] if first_line else ""
        

        if first_word in keywords:
            path = ".".join(block_entry["path"])
            construct_name = first_line.split()[1].rstrip(':') 
            

            if path == "__global__":
                full_name = f"{filename}.{construct_name}"
            elif path:
                full_name = f"{filename}.{path}.{construct_name}"
            else:
                full_name = f"{filename}.{construct_name}"
            
            result_list.append(full_name)


    coq_output = (
        "Require dpdgraph.dpdgraph.\n"
        f"From LF Require {filename}.\n"
        'Set DependGraph File "dgraph.dpd".\n'
        f"Definition everything_{filename} := (\n  "
        + ",\n  ".join(result_list) +
        "\n).\n"
        f"Print DependGraph everything_{filename}.\n"
    )

    print(coq_output)
