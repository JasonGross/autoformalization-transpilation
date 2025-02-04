import os
import json

def reconstructCoqFiles(inputJsonPath: str, outputFolder: str) -> None:
    with open(inputJsonPath, "r", encoding="utf-8") as inputFile:
        data = json.load(inputFile)

    totalFiles: int = len(data)
    
    for index, fileData in enumerate(data, start=1):
        fileName: str = fileData["fileName"]
        outputPath: str = os.path.join(outputFolder, fileName)
        
        with open(outputPath, "w", encoding="utf-8") as outputFile:
            for item in fileData["items"]:
                rawText: str = item["raw"]
                outputFile.write(f"{rawText}\n\n")
        
        print(f"[{index}/{totalFiles}] Reconstructed {fileName}.")

    print(f"Done! Reconstructed {totalFiles} files into {outputFolder}")

if __name__ == "__main__":
    inputJsonPath: str = r"src\dataset\processed_data\coq_proofs_dataset.json"
    outputFolder: str = r"src\dataset\reconstructed_files"
    os.makedirs(outputFolder, exist_ok=True)
    reconstructCoqFiles(inputJsonPath, outputFolder)
