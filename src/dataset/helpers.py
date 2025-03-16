import re

blockStarters = [
    "Fixpoint", "Definition", "Lemma", "Theorem", "Inductive", "Corollary",
    "Proposition", "Example", "Record", "CoFixpoint", "Fact", "Module",
    "Section", "Variable", "Hypothesis", "Axiom", "Parameter", "Goal",
    "Remark", "Notation", "Ltac", "Set", "Unset", "Require", "Import",
    "Export", "From", "Check", "Hint", "Create", "End"
]

proofEndings = ["Qed.", "Defined.", "Admitted.", "Abort."]

def isBlockStarter(line: str) -> bool:
    strippedLine = line.lstrip()
    for starter in blockStarters:
        pattern = r"^" + re.escape(starter) + r"(\b|\s|\()"
        if re.match(pattern, strippedLine):
            return True
    return False

def formatCoqFile(inputPath: str, outputPath: str) -> None:
    with open(inputPath, 'r', encoding='utf-8') as file:
        content = file.read()

    commentPattern = re.compile(r'\(\*.*?\*\)', re.DOTALL)
    content = re.sub(commentPattern, '', content)

    lines = content.split('\n')
    lines = [line.rstrip() for line in lines]

    preprocessedBlocks = []
    currentBlock = []
    collectingProof = False

    def flushBlock() -> None:
        nonlocal currentBlock
        if not currentBlock:
            return

        while currentBlock and not currentBlock[0].strip():
            currentBlock.pop(0)
        while currentBlock and not currentBlock[-1].strip():
            currentBlock.pop()

        if currentBlock:
            blockText = "\n".join(currentBlock)
            preprocessedBlocks.append(blockText)
        currentBlock = []

    for line in lines:
        strippedLine = line.strip()

        if collectingProof:
            currentBlock.append(line)
            if strippedLine in proofEndings:
                flushBlock()
                collectingProof = False
        else:
            if isBlockStarter(line):
                flushBlock()
                currentBlock.append(line)
            elif strippedLine == "Proof.":
                currentBlock.append(line)
                collectingProof = True
            elif strippedLine:
                currentBlock.append(line)
            else:
                if currentBlock:
                    currentBlock.append(line)

    flushBlock()

    finalContent = "\n\n".join(preprocessedBlocks) + "\n"

    with open(outputPath, 'w', encoding='utf-8') as file:
        file.write(finalContent)

def classifyBlock(blockText: str) -> str:
    lines = blockText.strip().split('\n')
    if not lines:
        return "Misc"
    firstLine = lines[0].strip()
    if firstLine.startswith("Set") or firstLine.startswith("Unset"):
        return "global_directive"
    if firstLine.startswith("Require"):
        return "Import"
    if firstLine.startswith("Fixpoint"):
        return "Fixpoint"
    if firstLine.startswith("Lemma"):
        return "Lemma"
    if firstLine.startswith("Theorem"):
        return "Theorem"
    if firstLine.startswith("Definition"):
        return "Definition"
    if firstLine.startswith("Ltac"):
        return "Ltac"
    if firstLine.startswith("Inductive"):
        return "Inductive"
    if firstLine.startswith("Check"):
        return "Dheck"
    if firstLine.startswith("Hint"):
        return "Hint"
    if firstLine.startswith("Create HintDb"):
        return "Create_hint_db"
    if firstLine.startswith("Import") or firstLine.startswith("Export") or firstLine.startswith("From"):
        return "Import"
    if firstLine.startswith("Example"):
        return "Example"
    if firstLine.startswith("Module"):
        return "Module"
    if firstLine.startswith("Section"):
        return "Section"
    if firstLine.startswith("End"):
        return "End"
    if firstLine.startswith("Compute"):
        return "Compute"
    if firstLine.startswith("Notation"):
        return "Notation"
    if firstLine.startswith("Intros"):
        return "Intros"
    return "Misc"

def extractBlocksFromPreprocessed(fileContent: str) -> list[dict[str, str]]:
    rawBlocks = fileContent.strip().split("\n\n")
    items = []
    for blockText in rawBlocks:
        blockType = classifyBlock(blockText)
        items.append({
            "type": blockType,
            "raw": blockText.strip()
        })
    return items



## "idtac" might not be handled correctly
## Require better logic for module/section End statements