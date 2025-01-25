import re

BLOCK_STARTERS = [
    "Fixpoint", "Definition", "Lemma", "Theorem", "Inductive", "Corollary",
    "Proposition", "Example", "Record", "CoFixpoint", "Fact", "Module",
    "Section", "Variable", "Hypothesis", "Axiom", "Parameter", "Goal", 
    "Remark", "Notation", "Ltac", "Set", "Unset", "Require", "Import", 
    "Export", "From", "Check", "Hint", "Create", "End"
]

PROOF_ENDINGS = ["Qed.", "Defined.", "Admitted.", "Abort."]

def is_block_starter(line: str) -> bool:
    stripped_line = line.lstrip()
    for starter in BLOCK_STARTERS:
        pattern = r"^" + re.escape(starter) + r"(\b|\s|\()"
        if re.match(pattern, stripped_line):
            return True
    return False

def format_coq_file(input_path: str, output_path: str) -> None:
    with open(input_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    comment_pattern = re.compile(r'\(\*.*?\*\)', re.DOTALL)
    content = re.sub(comment_pattern, '', content)

    lines = content.split('\n')
    lines = [line.rstrip() for line in lines]

    preprocessed_blocks = []
    current_block = []
    collecting_proof = False

    def flush_block():
        nonlocal current_block
        if not current_block:
            return

        while current_block and not current_block[0].strip():
            current_block.pop(0)
        while current_block and not current_block[-1].strip():
            current_block.pop()

        if current_block:
            block_text = "\n".join(current_block)
            preprocessed_blocks.append(block_text)
        current_block = []

    for line in lines:
        stripped = line.strip()

        if collecting_proof:
            current_block.append(line)
            if stripped in PROOF_ENDINGS:
                flush_block()
                collecting_proof = False
        else:
            if is_block_starter(line):
                flush_block()
                current_block.append(line)
            elif stripped == "Proof.":
                current_block.append(line)
                collecting_proof = True
            elif stripped:
                current_block.append(line)
            else:
                if current_block:
                    current_block.append(line)

    flush_block()

    final_content = "\n\n".join(preprocessed_blocks) + "\n"

    with open(output_path, 'w', encoding='utf-8') as f:
        f.write(final_content)

def classify_block(block_text: str) -> str:
    lines = block_text.strip().split('\n')
    if not lines:
        return "misc"
    first_line = lines[0].strip()
    if first_line.startswith("Set") or first_line.startswith("Unset"):
        return "global_directive"
    if first_line.startswith("Require"): ## Check this
        return "require"
    if first_line.startswith("Fixpoint"):
        return "fixpoint"
    if first_line.startswith("Lemma"):
        return "lemma"
    if first_line.startswith("Theorem"):
        return "theorem"
    if first_line.startswith("Definition"):
        return "definition"
    if first_line.startswith("Ltac"):
        return "ltac"
    if first_line.startswith("Inductive"):
        return "inductive"
    if first_line.startswith("Check"):
        return "check"
    if first_line.startswith("Hint"):
        return "hint"
    if first_line.startswith("Create HintDb"): ## Check this
        return "create_hint_db"
    if first_line.startswith("Import") or first_line.startswith("Export") or first_line.startswith("From"):
        return "import"
    if first_line.startswith("Example"):
        return "example"
    if first_line.startswith("Module"):
        return "module"
    if first_line.startswith("Section"):
        return "section"
    if first_line.startswith("End"):
        return "end"
    return "misc"

## "idtac" might not be handled correctly
## Require better logic for module/section End statements

def extract_blocks_from_preprocessed(file_content: str):
    raw_blocks = file_content.strip().split("\n\n")
    items = []
    for block_text in raw_blocks:
        btype = classify_block(block_text)
        items.append({
            "type": btype,
            "raw": block_text.strip()
        })
    return items
