from dataset.coq_tools.coq_tools.split_file import split_coq_file_contents_with_comments
import pandas as pd

# ...existing code...
if __name__ == "__main__":
    with open("/root/autoformalization/src/dataset/single_file_data/lf/EverythingLF.v", "r") as f:
        contents = f.read()

    statements = split_coq_file_contents_with_comments(contents)
    

    print(statements[23])