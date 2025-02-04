import os
from helpers import formatCoqFile

def preprocessCoqFiles(folderPath: str, outFolder: str) -> None:
    # Create output folder if it doesn't exist
    if not os.path.exists(outFolder):
        os.makedirs(outFolder)

    coqFiles: list[str] = [f for f in os.listdir(folderPath) if f.endswith('.v')]
    totalFiles: int = len(coqFiles)

    for index, filename in enumerate(coqFiles, start=1):
        inputPath: str = os.path.join(folderPath, filename)
        outputPath: str = os.path.join(outFolder, filename)
        try:
            formatCoqFile(inputPath, outputPath)
            print(f"[{index}/{totalFiles}] Preprocessed {filename} -> {outputPath}")
        except Exception as error:
            print(f"Error processing {filename}: {error}")

if __name__ == "__main__":
    folderPath: str = r"src\dataset\raw_data\lf"
    outFolder: str = r"src\dataset\pre_processed_data"
    preprocessCoqFiles(folderPath, outFolder)


## "idtac" might not be handled correctly
## Require better logic for module/section End statements
## List.v check