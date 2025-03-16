import re

# Keywords recognized as possible block starts
blockStarters = [
    "Fixpoint", "Definition", "Lemma", "Theorem", "Inductive", "Corollary",
    "Proposition", "Example", "Record", "CoFixpoint", "Fact", "Module",
    "Section", "Variable", "Hypothesis", "Axiom", "Parameter", "Goal",
    "Remark", "Notation", "Ltac", "Set", "Unset", "Require", "Import",
    "Export", "From", "Check", "Hint", "Create", "End"
]

# Possible ways a proof can end
proofEndings = ["Qed.", "Defined.", "Admitted.", "Abort."]

def isBlockStarter(line: str) -> bool:
    """
    Returns True if the given line starts with a known Coq block keyword.
    """
    stripped_line = line.lstrip()
    for starter in blockStarters:
        # Example: If "Fixpoint" is at the start followed by a space, parentheses, or boundary
        # we treat it as a valid block start.
        pattern = r"^" + re.escape(starter) + r"(\b|\s|\()"
        if re.match(pattern, stripped_line):
            return True
    return False


def classifyBlock(blockText: str) -> str:
    """
    Returns a coarse classification of a block based on its first line.
    """
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
    if (firstLine.startswith("Import") or
        firstLine.startswith("Export") or
        firstLine.startswith("From")):
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


def get_coq_blocks(fileContent: str) -> list[dict[str, str]]:
    """
    Takes the full text of a Coq file, removes comments,
    splits it into logical blocks, and classifies each block.
    Returns a list of dictionaries: [{"type": ..., "raw": ...}, ...].
    """

    # Remove any (* ... *) comments (including multiline)
    comment_pattern = re.compile(r'\(\*.*?\*\)', re.DOTALL)
    content_no_comments = re.sub(comment_pattern, '', fileContent)

    # Split into lines, strip trailing spaces
    lines = [line.rstrip() for line in content_no_comments.split('\n')]

    blocks = []
    currentBlock = []
    collectingProof = False

    def flushBlock():
        """
        Utility function to finalize the current block, classify it,
        and add it to the blocks list if non-empty.
        """
        nonlocal currentBlock
        # Remove blank lines from start and end
        while currentBlock and not currentBlock[0].strip():
            currentBlock.pop(0)
        while currentBlock and not currentBlock[-1].strip():
            currentBlock.pop()

        if currentBlock:
            blockText = "\n".join(currentBlock)
            blockType = classifyBlock(blockText)
            blocks.append({
                "type": blockType,
                "raw": blockText.strip()
            })
        currentBlock = []

    for line in lines:
        strippedLine = line.strip()
        # If we are in proof mode, keep reading until we find a proof ending
        if collectingProof:
            currentBlock.append(line)
            if strippedLine in proofEndings:
                flushBlock()
                collectingProof = False
        else:
            # If this line starts a new block, flush the old one first
            if isBlockStarter(line):
                flushBlock()
                currentBlock.append(line)
            elif strippedLine == "Proof.":
                currentBlock.append(line)
                collectingProof = True
            else:
                currentBlock.append(line)

    # Flush whatever is left
    flushBlock()

    return blocks
