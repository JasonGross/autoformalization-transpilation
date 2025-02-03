# Dataset Processing for Logical Foundations

This directory contains scripts to preprocess, scrape, and reconstruct Coq files for the Logical Foundations project.

## Instructions

1. **Preprocess Coq Files:**
    - Run the `pre_process_files.py` script:
      ```sh
      python pre_process_files.py
      ```
      This script reads raw Coq files from the [lf](http://_vscodecontentref_/0) directory, preprocesses them, and saves the preprocessed files in the [pre_processed_data](http://_vscodecontentref_/1) directory.

2. **Scrape Preprocessed Coq Files:**
    - Run the [scrape.py](http://_vscodecontentref_/2) script:
      ```sh
      python scrape.py
      ```
      This script reads the preprocessed Coq files from the [pre_processed_data](http://_vscodecontentref_/3) directory, extracts blocks of content, and saves the results in a JSON file at [coq_proofs_dataset.json](http://_vscodecontentref_/4).

3. **Reconstruct Coq Files:**
    - Run the [reconstruct_coq.py](http://_vscodecontentref_/5) script:
      ```sh
      python reconstruct_coq.py
      ```
      This script reads the JSON file from [coq_proofs_dataset.json](http://_vscodecontentref_/6), reconstructs the Coq files, and saves them in the [reconstructed_files](http://_vscodecontentref_/7) directory.

## File Descriptions

- **pre_process_files.py**: This script preprocesses raw Coq files. It reads files from the [lf](http://_vscodecontentref_/8) directory, processes them using the [format_coq_file](http://_vscodecontentref_/9) function from the [helpers](http://_vscodecontentref_/10) module, and saves the preprocessed files in the [pre_processed_data](http://_vscodecontentref_/11) directory.

- **scrape.py**: This script scrapes preprocessed Coq files. It reads files from the [pre_processed_data](http://_vscodecontentref_/12) directory, extracts blocks of content using the [extract_blocks_from_preprocessed](http://_vscodecontentref_/13) function from the [helpers](http://_vscodecontentref_/14) module, and saves the results in a JSON file at [coq_proofs_dataset.json](http://_vscodecontentref_/15).

- **reconstruct_coq.py**: This script reconstructs Coq files from the JSON data. It reads the JSON file from [coq_proofs_dataset.json](http://_vscodecontentref_/16), reconstructs the Coq files by writing the extracted blocks back into files, and saves them in the [reconstructed_files](http://_vscodecontentref_/17) directory.

By following these instructions, you can preprocess, scrape, and reconstruct Coq files for the Logical Foundations project.# Dataset Processing for Logical Foundations

This directory contains scripts to preprocess, scrape, and reconstruct Coq files for the Logical Foundations project.

## Instructions

1. **Preprocess Coq Files:**
    - Run the `pre_process_files.py` script:
      ```sh
      python pre_process_files.py
      ```
      This script reads raw Coq files from the [lf](http://_vscodecontentref_/0) directory, preprocesses them, and saves the preprocessed files in the [pre_processed_data](http://_vscodecontentref_/1) directory.

2. **Scrape Preprocessed Coq Files:**
    - Run the [scrape.py](http://_vscodecontentref_/2) script:
      ```sh
      python scrape.py
      ```
      This script reads the preprocessed Coq files from the [pre_processed_data](http://_vscodecontentref_/3) directory, extracts blocks of content, and saves the results in a JSON file at [coq_proofs_dataset.json](http://_vscodecontentref_/4).

3. **Reconstruct Coq Files:**
    - Run the [reconstruct_coq.py](http://_vscodecontentref_/5) script:
      ```sh
      python reconstruct_coq.py
      ```
      This script reads the JSON file from [coq_proofs_dataset.json](http://_vscodecontentref_/6), reconstructs the Coq files, and saves them in the [reconstructed_files](http://_vscodecontentref_/7) directory.

## File Descriptions

- **pre_process_files.py**: This script preprocesses raw Coq files. It reads files from the [lf](http://_vscodecontentref_/8) directory, processes them using the [format_coq_file](http://_vscodecontentref_/9) function from the [helpers](http://_vscodecontentref_/10) module, and saves the preprocessed files in the [pre_processed_data](http://_vscodecontentref_/11) directory.

- **scrape.py**: This script scrapes preprocessed Coq files. It reads files from the [pre_processed_data](http://_vscodecontentref_/12) directory, extracts blocks of content using the [extract_blocks_from_preprocessed](http://_vscodecontentref_/13) function from the [helpers](http://_vscodecontentref_/14) module, and saves the results in a JSON file at [coq_proofs_dataset.json](http://_vscodecontentref_/15).

- **reconstruct_coq.py**: This script reconstructs Coq files from the JSON data. It reads the JSON file from [coq_proofs_dataset.json](http://_vscodecontentref_/16), reconstructs the Coq files by writing the extracted blocks back into files, and saves them in the [reconstructed_files](http://_vscodecontentref_/17) directory.

By following these instructions, you can preprocess, scrape, and reconstruct Coq files for the Logical Foundations project.