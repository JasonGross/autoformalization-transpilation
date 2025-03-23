import datetime
import re
from copy import deepcopy
from functools import lru_cache
from pathlib import Path
from typing import Any, Callable, Iterable, NamedTuple, Optional, Sequence

from config import (
    ISO_CHECKER_HEADER,
    ISO_HEADER,
    ISO_INTERFACE_HEADER,
    KNOWN_IMPORTS,
    KNOWN_PAIRS,
    SOURCE_DIR,
)
from project_util import (
    AmbiguousIsoError,
    CoqFile,
    CoqIdentifier,
    CoqProject,
    DisorderedConstr,
    File,
    GenericIsoError,
    IsoBlock,
    IsoError,
    IsoErrorWithoutHints,
    MissingImport,
    MissingTypeIso,
    NonIsoBlockError,
    has_identifier_prefix,
    remove_identifier_prefix,
)
from utils import logging
from utils.itertools_extra import unique

ISO_TARGET_PATTERN = r"(?:[\w\.]+|\(@[\w\.]+\))"


def make_isos_interface(project: CoqProject) -> tuple[CoqProject, bool, Optional[str]]:
    return make_isos(project, "Interface.vo")


class ProcessedCoqName(NamedTuple):
    first_id: str
    coq_id: str
    iso_name: str


def process_coq_name(
    coq_name: CoqIdentifier,
    *,
    original_name: str = "Original",
) -> ProcessedCoqName:
    first_id = str(coq_name)
    coq_id = first_id
    if coq_id[0] == "(":
        assert coq_id[-1] == ")", coq_id
        coq_id = coq_id[1:-1]
        if coq_id[0] == "@":
            coq_id = coq_id[1:]
    coq_id = remove_identifier_prefix(coq_id, prefix=original_name).replace(".", "_")
    iso_name = f"{coq_id}_iso"
    return ProcessedCoqName(first_id, coq_id, iso_name)


def iso_name_of_coq_name(
    coq_name: CoqIdentifier,
    *,
    original_name: str = "Original",
) -> str:
    return process_coq_name(coq_name, original_name=original_name).iso_name


def process_coq_lean_name(
    coq_lean_name: CoqIdentifier, *, imported_name: str = "Imported"
) -> str:
    if str(coq_lean_name)[0] == "$":
        coq_lean_name = str(coq_lean_name)[1:]  # type: ignore
        return f"{imported_name}.{coq_lean_name}"
    else:
        return str(coq_lean_name)


class CheckBlock(NamedTuple):
    # the block of Coq code that gets added to Isomorphisms.v
    check_block: str
    # the isomorphism name to add to the list for Print Assumptions, if any
    iso_name: str | None


def check_block_of_cc_identifier_block(
    block: str | IsoBlock,
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
) -> CheckBlock:
    if isinstance(block, IsoBlock):
        proof = block.proof or "iso."
        processed_coq_name = process_coq_name(block.source, original_name=original_name)
        first_id, coq_id, iso_name = processed_coq_name
        second_id = process_coq_lean_name(block.target, imported_name=imported_name)

        if not proof.endswith("Admitted."):
            proof = f"Proof. {proof} Defined."

        iso_block = f"""Instance {iso_name} : iso_statement {first_id} {second_id}.
{proof}
Instance: KnownConstant {first_id} := {{}}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant {second_id} := {{}}. (* only needed when rel_iso is typeclasses opaque *)"""

        return CheckBlock(iso_block, iso_name if block.is_required else None)
    else:
        return CheckBlock(block, None)


def generate_indexed_isos_blocks(
    cc_identifiers_blocks: list[str | IsoBlock],
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
) -> list[tuple[int | None, str]]:
    """
    Returns a list of blocks of Coq code for the isomorphisms file, paired with the index of the block in cc_identifiers_blocks.
    If the block does not correspond to any statement in the cc_identifiers_blocks, the index is None.
    """
    iso_checks = []
    iso_names = []
    for i, (iso_block, iso_name) in enumerate(
        check_block_of_cc_identifier_block(
            block, original_name=original_name, imported_name=imported_name
        )
        for block in cc_identifiers_blocks
    ):
        iso_checks.append((i, iso_block))
        if iso_name is not None:
            iso_names.append(iso_name)

    # Generate a `Print Assumptions` check for dependencies
    print_assumptions_block = f"""Import IsomorphismChecker.Automation.HList.HListNotations.
Definition everything := ({" :: ".join(iso_names)} :: [])%hlist.
Print Assumptions everything."""

    return [(None, ISO_HEADER), *iso_checks, (None, print_assumptions_block)]


def generate_isos(
    project: CoqProject,
    cc_identifiers_blocks: list[str | IsoBlock],
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    output_file: str = "Isomorphisms.v",
) -> CoqProject:
    project = project.copy()

    # Combine all sections
    full_content = "\n\n".join(
        block
        for _, block in generate_indexed_isos_blocks(
            cc_identifiers_blocks,
            original_name=original_name,
            imported_name=imported_name,
        )
    )
    logging.debug(f"{full_content}")

    # Write to file
    project[output_file] = CoqFile(full_content)
    try:
        del project[f"{output_file}o"]
    except KeyError:
        pass

    return project


def block_index_of_error_line(
    cc_identifiers_blocks: list[str | IsoBlock],
    linenum: int,
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
) -> int | None:
    """
    This function takes a list of Coq code blocks and a line number, and returns the index of the block that contains the line.

    linenum is 1-indexed
    """
    blocks = []
    for i, block in generate_indexed_isos_blocks(
        cc_identifiers_blocks, original_name=original_name, imported_name=imported_name
    ):
        if i is None:
            i = -1
        block = block.replace("\n", f"\n{i} ")
        blocks.append(f"{i} {block}")

    line_prefixed_code = "\n\n".join(blocks)
    lines = line_prefixed_code.split("\n")

    blocknum_str = lines[linenum - 1].split(" ")[0]
    blocknum = int(blocknum_str)
    return blocknum if blocknum != -1 else None


def insert_iso_block(
    cc_identifiers_blocks: list[str | IsoBlock],
    new_block: IsoBlock,
    before_source: str,
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
) -> list[str | IsoBlock]:
    cc_identifiers_blocks = deepcopy(cc_identifiers_blocks)
    index = find_iso_index(
        cc_identifiers_blocks,
        before_source,
        original_name=original_name,
        imported_name=imported_name,
    )

    block = cc_identifiers_blocks[index]
    assert isinstance(block, IsoBlock), block
    logging.info(
        f"Adding iso_statement {new_block.source}, {new_block.target} for {str(block.source)}, {str(block.target)}"
    )
    cc_identifiers_blocks_sources = [
        (block.source if isinstance(block, IsoBlock) else None)
        for block in cc_identifiers_blocks
    ]
    existing_index = None
    try:
        existing_index = cc_identifiers_blocks_sources.index(new_block.source)
    except ValueError:
        pass
    if existing_index is not None:
        old_block = cc_identifiers_blocks[existing_index]
        assert isinstance(old_block, IsoBlock), old_block
        if existing_index <= index:
            if old_block.target == new_block.target:
                raise IsoAlreadyExistsError(
                    IsoAlreadyExistsErrorArguments(
                        str(new_block.source),
                        str(new_block.target),
                        str(block.source),
                        str(block.target),
                        index,
                        existing_index,
                    )
                )
            else:
                logging.warning(
                    f"Overwriting {old_block.source} -> {old_block.target} at index {existing_index} with {new_block.source} -> {new_block.target}"
                )
                old_block.target = new_block.target
                cc_identifiers_blocks[existing_index] = old_block
                return cc_identifiers_blocks
        else:
            cc_identifiers_blocks.pop(existing_index)
            new_block.proof = new_block.proof or old_block.proof
            new_block.is_interface = new_block.is_interface or old_block.is_interface
            new_block.is_original = new_block.is_original or old_block.is_original
    cc_identifiers_blocks.insert(index, new_block)
    return cc_identifiers_blocks


def insert_iso(
    cc_identifiers_blocks: list[str | IsoBlock],
    source: str,
    target: str,
    before_source: str,
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    is_interface: bool = False,
    # add_target_prefix: bool = True,
) -> list[str | IsoBlock]:
    new_source = CoqIdentifier(source)
    new_target = CoqIdentifier(target)
    # if add_target_prefix:
    #     new_target = add_prefix(new_target, prefix=imported_name)
    new_block = IsoBlock(new_source, new_target, is_interface=is_interface)
    return insert_iso_block(
        cc_identifiers_blocks,
        new_block,
        before_source,
        original_name=original_name,
        imported_name=imported_name,
    )


def repair_missing_type_iso(
    project: CoqProject,
    error: MissingTypeIso,
    cc_identifiers_blocks: list[str | IsoBlock],
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
    is_interface: bool = False,
) -> tuple[CoqProject, list[str | IsoBlock]]:
    cc_identifiers_blocks = insert_iso(
        cc_identifiers_blocks,
        error.source,
        error.target,
        error.orig_source,
        original_name=original_name,
        imported_name=imported_name,
        is_interface=is_interface,
    )

    project = generate_isos(
        project,
        cc_identifiers_blocks,
        original_name=original_name,
        imported_name=imported_name,
        output_file=iso_file,
    )
    return project, cc_identifiers_blocks


ACTUAL_ERROR_REG_STRING = "(?!Warning)(?!The command has indeed failed with message:)"  # maybe we should just require Error or Timeout?
DEFAULT_PRE_PRE_ERROR_REG_STRING = (
    'File "([^"]+)", line ([0-9]+), characters ([0-9]+)-([0-9]+):\n'
)
DEFAULT_PRE_ERROR_REG_STRING = (
    DEFAULT_PRE_PRE_ERROR_REG_STRING + ACTUAL_ERROR_REG_STRING
)
DEFAULT_ERROR_REG_STRING = DEFAULT_PRE_ERROR_REG_STRING + "((?:.|\n)+)"
MAKE_ERROR_REG_STRING = r"^make[^:]*:\s*\*\*\*\s*\[[^\]]*\]\s*Error\s*"


def clean_irrelevant_warnings(errors: str) -> str:
    return re.sub(
        r"""File "[^"]*", line \d+, characters \d+-\d+:
Warning: Output directory is unset, using "[^"]*"\. Use command line option "-output-directory to set a default directory\. \[[^\]]*\]
""".replace(" ", r"[\n\s]+"),
        "",
        errors,
    )


def parse_iso_errors(
    errors: str,
    *,
    project: CoqProject,
    cc_identifiers_blocks: list[str | IsoBlock],
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
) -> IsoError | NonIsoBlockError:
    def assert_or_error(condition, extra: Any = ""):
        if extra:
            extra = f"\n{extra}"
        msg = f"{errors}\n{project.format(only_debug_files=True)}{extra}"
        if not condition:
            project.write(Path(__file__).parent.parent / "temp_iso_errors")
        assert condition, msg

    def compute_interface_iso_index(iso_index: int) -> int:
        return len(
            [
                block
                for block in cc_identifiers_blocks[:iso_index]
                if isinstance(block, IsoBlock) and block.is_interface
            ]
        )

    errors = clean_irrelevant_warnings(errors)

    if "Proving iso_statement " in errors:
        errors = "Proving iso_statement " + errors.split("Proving iso_statement ")[-1]

    missing_reference_match = re.search(
        r"Error: The reference ([^\s]+) was not found in the current environment.",
        errors,
    )

    missing_iso_result = list(
        unique(
            re.findall(
                # r"While proving iso_statement ([\w\.]+) ([\w\.]+):
                rf"(?:Could not find iso for|could not find iso_statement|Consider adding iso_statement) ({ISO_TARGET_PATTERN}) (?:-> )?({ISO_TARGET_PATTERN})",
                errors,
            )
        )
    )

    # First extract the block from the error message
    err_matches = re.findall(DEFAULT_ERROR_REG_STRING, errors)
    assert_or_error(err_matches)
    err_fname, err_linenum, err_start, err_end, error_msg = err_matches[-1]
    orig_source, orig_target, orig_proof, iso_index = None, None, None, None
    interface_iso_index = None
    if err_fname[:2] in ("./", ".\\"):
        err_fname = err_fname[2:]
    err_linenum = int(err_linenum)
    err_start = int(err_start)
    err_end = int(err_end)
    assert_or_error(err_fname in project, err_fname)
    err_file_contents = project.files[err_fname].contents
    assert_or_error(isinstance(err_file_contents, str), err_fname)
    assert isinstance(err_file_contents, str)  # for the type checker
    err_line = err_file_contents.split("\n")[err_linenum - 1]
    # if the error is in another file, we fall back on the hinting
    if err_fname in (iso_file, f"./{iso_file}", rf".\{iso_file}"):
        iso_index = block_index_of_error_line(
            cc_identifiers_blocks,
            err_linenum,
            original_name=original_name,
            imported_name=imported_name,
        )
        assert_or_error(iso_index is not None)
        assert iso_index is not None  # for the type checker
        block = cc_identifiers_blocks[iso_index]
        error_msg = re.split(MAKE_ERROR_REG_STRING, error_msg, flags=re.MULTILINE)[0]
        if not isinstance(block, IsoBlock):
            return NonIsoBlockError(
                err_line, err_start, err_end, error_msg, iso_index, block
            )
        orig_proof = block.proof
        orig_source = str(block.source)
        orig_target = str(block.target)
        interface_iso_index = compute_interface_iso_index(iso_index)

        # if there are no hints, return an IsoErrorWithoutHints
        if (
            "Proving iso_statement" not in errors
            and not missing_reference_match
            and not missing_iso_result
        ):
            return IsoErrorWithoutHints(
                orig_source,
                orig_target,
                orig_proof,
                iso_index,
                interface_iso_index,
                err_line,
                err_start,
                err_end,
                error_msg,
            )
    else:
        # if we can't extract a valid block, assume there must be hints
        assert_or_error("Proving iso_statement " in errors)
        errors = errors.split("Proving iso_statement ")[-1]
        last_proving_instance = re.match(
            rf"^({ISO_TARGET_PATTERN}) ({ISO_TARGET_PATTERN})[\s\n]+(.*)$",
            errors,
            flags=re.DOTALL,
        )
        assert_or_error(last_proving_instance)
        assert last_proving_instance, errors
        labeled_iso_statement_orig_source, labeled_iso_statement_orig_target, errors = (
            last_proving_instance.groups()
        )
        orig_source = orig_source or labeled_iso_statement_orig_source
        orig_target = orig_target or labeled_iso_statement_orig_target
        if (
            (
                labeled_iso_statement_orig_source != orig_source
                or labeled_iso_statement_orig_target != orig_target
            )
            and not missing_reference_match
            and not missing_iso_result
        ):
            pre_error = re.split(DEFAULT_PRE_ERROR_REG_STRING, errors)[0]
            assert_or_error(isinstance(error_msg, str), repr(error_msg))
            assert isinstance(error_msg, str)  # for the type checker
            return AmbiguousIsoError(
                orig_source,
                orig_target,
                orig_proof,
                iso_index,
                interface_iso_index,
                err_line,
                err_start,
                err_end,
                error_msg,
                labeled_iso_statement_orig_source,
                labeled_iso_statement_orig_target,
                orig_proof,
                iso_index,
                interface_iso_index,
                pre_error,
            )
        try:
            iso_index, block = find_iso_and_index(
                cc_identifiers_blocks,
                orig_source,
                orig_target,
                original_name=original_name,
                imported_name=imported_name,
            )
        except ValueError:
            pass
        if iso_index is not None:
            interface_iso_index = compute_interface_iso_index(iso_index)
            orig_proof = block.proof

    if missing_reference_match:
        return MissingImport(
            orig_source,
            orig_target,
            orig_proof,
            iso_index,
            interface_iso_index,
            missing_reference_match.group(1),
        )

    if missing_iso_result:
        logging.info(f"Found missing isomorphisms: {set(missing_iso_result)}")
        if len(missing_iso_result) > 1:
            logging.warning(
                f"Found multiple missing isomorphisms: {missing_iso_result}"
            )
        source, target = missing_iso_result[0]
        if (orig_source, orig_target) != (source, target):
            return MissingTypeIso(
                orig_source,
                orig_target,
                orig_proof,
                iso_index,
                interface_iso_index,
                source,
                target,
            )
    if (
        "Warning: The argument lengths don't match, perhaps the constructors were defined in different orders?"
        in errors
    ):
        blocks = errors.split(
            "Warning: The argument lengths don't match, perhaps the constructors were defined in different orders?"
        )
        hints = [v.strip() for v in dict.fromkeys(blocks[1:-1])]
        prefix, suffix = blocks[0], blocks[-1]
        return DisorderedConstr(
            orig_source,
            orig_target,
            orig_proof,
            iso_index,
            interface_iso_index,
            hints[0],
            prefix,
            hints[1:],
            suffix,
        )

    result = re.match(
        # r"^(.*)[\n\s]*While proving iso_statement ([\w\.]+) ([\w\.]+): (\d+) goals? not fully solved:[\s\n]*(.*)",
        r"^(.*)[\n\s]*Warning:[\s\n]*(\d+) goals? not fully solved:[\s\n]*(.*)",
        errors,
        flags=re.DOTALL,
    )
    assert result, errors
    prefix, ngoals, goals = result.groups()
    result = re.match(
        r"^(.*)[\n\s]*Warning:[\s\n]*(\d+) goals? not fully solved \(simplified printout\):[\s\n]*(.*)",
        goals,
        flags=re.DOTALL,
    )
    simplified_goals = ""
    if result:
        goals, _ngoals, simplified_goals = result.groups()
        simplified_goals = simplified_goals.strip()
    csts = list(
        dict.fromkeys(
            re.findall(
                r"(?:Unfolding unknown|Reducing unknown|Skipping the unfolding of) \w+ on (lhs|rhs)\s*:\s*([^ \n$]+)$",
                prefix,
                flags=re.MULTILINE,
            )
        )
    )
    unknown_lhs = [
        cst
        for side, cst in csts
        if side == "lhs"
        and cst != orig_source
        and (
            cc_identifiers_blocks is None
            or not has_iso_from(
                cc_identifiers_blocks,
                cst,
                original_name=original_name,
                imported_name=imported_name,
            )
        )
    ]
    unknown_rhs = [
        cst
        for side, cst in csts
        if side == "rhs"
        and cst != orig_target
        and (
            cc_identifiers_blocks is None
            or not has_iso_to(
                cc_identifiers_blocks,
                cst,
                original_name=original_name,
                imported_name=imported_name,
            )
        )
    ]
    prefix = re.sub(
        r"(?:Unfolding unknown|Reducing unknown|Skipping the unfolding of) \w+ on (lhs|rhs)\s*:\s*([^ \n$]+)$",
        "",
        prefix,
        flags=re.MULTILINE,
    ).strip()
    prefix = re.sub(
        r"(?:Unfolding|Reducing) unknown \w+ on (lhs|rhs)\s*.missing.$",
        "",
        prefix,
        flags=re.MULTILINE,
    ).strip()
    prefix = re.sub(
        "\n+",
        "\n",
        prefix,
    ).strip()
    return GenericIsoError(
        orig_source,
        orig_target,
        orig_proof,
        iso_index,
        interface_iso_index,
        unknown_lhs,
        unknown_rhs,
        prefix,
        int(ngoals),
        goals,
        simplified_goals,
    )


def make_isos(
    project: CoqProject, *targets: str
) -> tuple[CoqProject, bool, Optional[str]]:
    result, project = project.make(*targets, check=False, sanitize="/tmp/make_isos")
    if result.returncode != 0:
        # We log this and then feed it into our iso repair model
        error_message = f"{result.stdout}\n{result.stderr}".strip()
        logging.debug(f"Make failed: {error_message}")
        # Check error message for missing isomorphisms
        if iso_pairs := [
            (match.group(1), match.group(2))
            for match in re.finditer(
                rf"Could not find iso for ({ISO_TARGET_PATTERN}) -> ({ISO_TARGET_PATTERN})",
                error_message,
            )
        ]:
            logging.info(f"Found missing isomorphisms: {set(iso_pairs)}")
        return project, False, error_message
    return project, True, None


def generate_interface(
    project: CoqProject,
    coq_identifiers: list[CoqIdentifier],
    *,
    coq_identifiers_to_unfold: Sequence[CoqIdentifier] = [],
    original_name: str = "Original",
    output_file: str = "Interface.v",
    checker_file: str = "Checker.v",
) -> CoqProject:
    project = project.copy()
    coq_identifiers_to_unfold_str = [
        str(coq_id) for coq_id in coq_identifiers_to_unfold
    ]
    # TODO: Implement https://github.com/JasonGross/autoformalization/pull/19#discussion_r1934686304

    # Should also be generating these programmatically, for now these are manual
    # TODO: This should happen in the reimport step!
    # Generate the isomorphism checks for each definition pair
    iso_interface_checks, iso_checks, iso_names = [], [], []
    for coq_name in coq_identifiers:
        processed_coq_name = process_coq_name(coq_name, original_name=original_name)
        first_id, coq_id, iso_name = processed_coq_name
        iso_names.append(iso_name)

        iso_block = f"""Derive imported_{coq_id} in (iso_statement {first_id} (imported_{coq_id} :> import_of {first_id})) as {iso_name}.
Proof. subst imported_{coq_id}. exact Isomorphisms.{iso_name}. Defined.
Existing Instance {iso_name}."""
        iso_checks.append(iso_block)

        if first_id in coq_identifiers_to_unfold_str:
            iso_interface_block = f"""Derive imported_{coq_id} in (iso_statement {first_id} (imported_{coq_id} :> import_of {first_id})) as {iso_name}.
Proof. subst imported_{coq_id}. iso_for_interface. Defined.
Existing Instance {iso_name}."""
        else:
            iso_interface_block = f"""Parameter imported_{coq_id} : import_of {first_id}.
Parameter {iso_name} : iso_statement {first_id} imported_{coq_id}.
Existing Instance {iso_name}."""
        iso_interface_checks.append(iso_interface_block)

    # Generate a `Print Assumptions` check for dependencies
    everything_interface_block = f"""Import IsomorphismChecker.Automation.HList.HListNotations.
Definition everything := ({" :: ".join(iso_names)} :: [])%hlist."""

    everything_block = f"""Definition everything := Isomorphisms.everything."""

    force_unfold_block = "\n".join(
        f"#[local] Instance: MustUnfold {coq_id} := {{}}."
        for coq_id in coq_identifiers_to_unfold_str
    )

    # Combine all sections
    full_interface_content = "\n\n".join(
        [
            ISO_INTERFACE_HEADER,
            force_unfold_block,
            "Module Type Interface.",
            "\n\n".join(iso_interface_checks),
            everything_interface_block,
            "End Interface.",
        ]
    )
    logging.debug(f"{full_interface_content}")

    full_content = "\n\n".join(
        [
            ISO_CHECKER_HEADER,
            "\n\n".join(iso_checks),
            everything_block,
            "End DoesItCheck.",
        ]
    )
    logging.debug(f"{full_content}")

    # Write to file
    project[output_file] = CoqFile(full_interface_content)
    try:
        del project[f"{output_file}o"]
    except KeyError:
        pass

    # Write to file
    project[checker_file] = CoqFile(full_content)
    try:
        del project[f"{checker_file}o"]
    except KeyError:
        pass

    return project


def repair_isos_interface(
    project: CoqProject,
    errors: str,
    coq_identifiers: list[CoqIdentifier],
    *,
    coq_identifiers_to_unfold: Sequence[CoqIdentifier] = (),
    original_name: str = "Original",
    interface_file: str = "Interface.v",
    checker_file: str = "Checker.v",
) -> tuple[CoqProject, list[CoqIdentifier], list[CoqIdentifier]]:
    coq_identifiers_to_unfold = list(coq_identifiers_to_unfold)
    # Look at the errors, attempt to fix the isos
    result = re.search(
        rf"While importing ([\w\.]+): (?:While stating iso_statement [^:]*: )?Consider adding iso_statement ({ISO_TARGET_PATTERN}) (?:and unfolding \[([^\]]+)\])?",
        re.sub(r"\s+", " ", errors),
    )
    if result is None:
        project.write(Path(__file__).parent.parent / "temp_interface_errors")
    assert result is not None, (project[interface_file], re.sub(r"\s+", " ", errors))
    orig_source, source, unfold_list = result.groups()
    coq_identifiers_str = [str(s) for s in coq_identifiers]
    assert orig_source in coq_identifiers_str, (
        orig_source,
        coq_identifiers_str,
    )
    index = coq_identifiers_str.index(orig_source)
    if unfold_list:
        unfold_ids = unfold_list.split(", ")
        coq_identifiers_to_unfold += [CoqIdentifier(s) for s in unfold_ids]
        for coq_id in unfold_ids:
            if coq_id not in coq_identifiers_str:
                project.write(Path(__file__).parent.parent / "temp_interface_errors")
            assert coq_id in coq_identifiers_str, (coq_id, coq_identifiers_str)
            index = min(index, coq_identifiers_str.index(coq_id))
    logging.info(
        f"Adding iso_statement {source} for {orig_source}"
        f"{' before ' + coq_identifiers_str[index] if orig_source != coq_identifiers_str[index] else ''}"
        f"{' and unfolding ' + unfold_list if unfold_list else ''}"
    )

    if not (unfold_list or CoqIdentifier(source) not in coq_identifiers[:index]):
        project.write(Path(__file__).parent.parent / "temp_interface_errors")
        logging.error(errors)
    assert unfold_list or CoqIdentifier(source) not in coq_identifiers[:index], (
        source,
        coq_identifiers,
        re.sub(r"\s+", " ", errors),
    )
    if CoqIdentifier(source) in coq_identifiers[index:]:
        coq_identifiers.remove(CoqIdentifier(source))
    if CoqIdentifier(source) not in coq_identifiers:
        coq_identifiers.insert(index, CoqIdentifier(source))
    project = generate_interface(
        project,
        coq_identifiers,
        coq_identifiers_to_unfold=coq_identifiers_to_unfold,
        original_name=original_name,
        output_file=interface_file,
        checker_file=checker_file,
    )
    return project, coq_identifiers, coq_identifiers_to_unfold


@lru_cache()
def make_identifiers_str_helper(
    cc_identifiers_blocks: tuple[str | IsoBlock],
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
) -> list[tuple[str | None, str | None]]:
    return [
        (
            (
                str(block.source),
                str(block.target),
            )
            if isinstance(block, IsoBlock)
            else (None, None)
        )
        for block in cc_identifiers_blocks
    ]


@lru_cache()
def make_identifiers_iso_names_helper(
    cc_identifiers_blocks: tuple[str | IsoBlock],
    *,
    original_name: str = "Original",
) -> list[str | None]:
    return [
        (
            iso_name_of_coq_name(block.source, original_name=original_name)
            if isinstance(block, IsoBlock)
            else None
        )
        for block in cc_identifiers_blocks
    ]


def make_identifiers_iso_names(
    cc_identifiers_blocks: list[str | IsoBlock],
    *,
    original_name: str = "Original",
) -> list[str | None]:
    return make_identifiers_iso_names_helper(
        tuple(cc_identifiers_blocks), original_name=original_name
    )


def make_identifiers_str(
    cc_identifiers_blocks: list[str | IsoBlock],
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
) -> list[tuple[str | None, str | None]]:
    return make_identifiers_str_helper(
        tuple(cc_identifiers_blocks),
        original_name=original_name,
        imported_name=imported_name,
    )


def find_iso_index(
    cc_identifiers_blocks: list[str | IsoBlock],
    orig_source: str,
    orig_target: str | None = None,
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    fuzzy_sigil: bool = True,
    allow_iso_name: bool = True,
) -> int:
    cc_identifiers_str = make_identifiers_str(
        cc_identifiers_blocks, original_name=original_name, imported_name=imported_name
    )
    cc_identifiers_iso_names = (
        make_identifiers_iso_names(cc_identifiers_blocks, original_name=original_name)
        if allow_iso_name
        else []
    )
    orig_sources = [orig_source]
    orig_targets = [orig_target] if orig_target is not None else None
    if fuzzy_sigil:
        orig_sources += [f"{original_name}.{orig_source}"]
        if orig_target is not None and orig_targets is not None:
            orig_targets += [f"{imported_name}.{orig_target}"]

    if orig_targets is not None:
        for orig_source in orig_sources:
            for orig_target in orig_targets:
                try:
                    return cc_identifiers_str.index((orig_source, orig_target))
                except ValueError:
                    pass
        raise ValueError(
            f"Could not find iso for {orig_sources} to {orig_targets} in {cc_identifiers_str}"
        )
    else:
        c_identifiers_str = [s for s, _ in cc_identifiers_str]
        for orig_source in orig_sources:
            try:
                return c_identifiers_str.index(orig_source)
            except ValueError:
                pass
            if allow_iso_name:
                try:
                    return cc_identifiers_iso_names.index(orig_source)
                except ValueError:
                    pass
        raise ValueError(
            f"Could not find iso for {orig_sources} in {cc_identifiers_str}"
        )


def find_iso_and_index(
    cc_identifiers_blocks: list[str | IsoBlock],
    orig_source: str,
    orig_target: str | None = None,
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    fuzzy_sigil: bool = True,
    allow_iso_name: bool = True,
) -> tuple[int, IsoBlock]:
    index = find_iso_index(
        cc_identifiers_blocks,
        orig_source,
        orig_target,
        original_name=original_name,
        imported_name=imported_name,
        fuzzy_sigil=fuzzy_sigil,
        allow_iso_name=allow_iso_name,
    )
    block = cc_identifiers_blocks[index]
    assert isinstance(block, IsoBlock), block
    return index, block


def has_iso(
    cc_identifiers_blocks: list[str | IsoBlock],
    orig_source: str,
    orig_target: str | None = None,
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
) -> bool:
    try:
        find_iso_index(
            cc_identifiers_blocks,
            orig_source,
            orig_target,
            original_name=original_name,
            imported_name=imported_name,
        )
        return True
    except ValueError:
        return False


def has_iso_from(
    cc_identifiers_blocks: list[str | IsoBlock],
    orig_source: str,
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
) -> bool:
    cc_identifiers_str = make_identifiers_str(
        cc_identifiers_blocks, original_name=original_name, imported_name=imported_name
    )
    c_identifiers_str = [s for s, _ in cc_identifiers_str]
    return orig_source in c_identifiers_str


def has_iso_to(
    cc_identifiers_blocks: list[str | IsoBlock],
    orig_target: str,
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
) -> bool:
    cc_identifiers_str = make_identifiers_str(
        cc_identifiers_blocks, original_name=original_name, imported_name=imported_name
    )
    c_identifiers_str = [t for _, t in cc_identifiers_str]
    return orig_target in c_identifiers_str


def can_autofix_disordered_constr(
    error: DisorderedConstr,
    cc_identifiers_blocks: list[str | IsoBlock],
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
) -> bool:
    index = find_iso_index(
        cc_identifiers_blocks,
        error.orig_source,
        error.orig_target,
        original_name=original_name,
        imported_name=imported_name,
    )
    block = cc_identifiers_blocks[index]
    assert isinstance(block, IsoBlock), block
    return block.proof is None


def autofix_disordered_constr(
    project: CoqProject,
    error: DisorderedConstr,
    cc_identifiers_blocks: list[str | IsoBlock],
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
) -> tuple[CoqProject, list[str | IsoBlock]]:
    cc_identifiers_blocks = deepcopy(cc_identifiers_blocks)
    index = find_iso_index(
        cc_identifiers_blocks,
        error.orig_source,
        error.orig_target,
        original_name=original_name,
        imported_name=imported_name,
    )
    block = cc_identifiers_blocks[index]
    assert not isinstance(block, str), block
    new_proof = r"""start_iso.
{ start_step_iso. all: revgoals. all: finish_step_iso. }
{ symmetrize_rel_iso; start_step_iso. all: revgoals. all: finish_step_iso. }
{ start_iso_proof; step_iso_proof_full. }
{ symmetrize_rel_iso; start_iso_proof; step_iso_proof_full. }"""
    logging.info(
        f"Updating iso_statement {error.orig_source} {error.orig_target} with proof {new_proof}"
    )
    block.proof = new_proof
    cc_identifiers_blocks[index] = block
    project = generate_isos(
        project,
        cc_identifiers_blocks,
        original_name=original_name,
        imported_name=imported_name,
        output_file=iso_file,
    )
    return project, cc_identifiers_blocks


def generate_and_prove_iso_interface(
    project: CoqProject,
    coq_identifiers: list[CoqIdentifier],
    *,
    coq_identifiers_to_unfold: Sequence[CoqIdentifier] = (),
) -> tuple[CoqProject, bool, Optional[str], list[CoqIdentifier], list[CoqIdentifier]]:
    coq_identifiers_to_unfold = list(coq_identifiers_to_unfold)
    # Make interface file
    project = generate_interface(
        project,
        coq_identifiers,
        coq_identifiers_to_unfold=coq_identifiers_to_unfold,
    )

    # Check that the iso proof compiles
    project, result, errors = make_isos_interface(project)
    project.write(Path(__file__).parent.parent / "temp_interface_status")

    if result:
        logging.info("Isomorphism interface proof succeeded")
    else:
        attempt = 0
        while errors:
            attempt += 1
            logging.info(f"Isomorphism interface proof failed on attempt {attempt}")
            logging.debug(errors)
            project, coq_identifiers, coq_identifiers_to_unfold = repair_isos_interface(
                project,
                errors,
                coq_identifiers,
                coq_identifiers_to_unfold=coq_identifiers_to_unfold,
            )
            project.write(Path(__file__).parent.parent / "temp_interface_status")
            project, result, errors = make_isos_interface(project)

    # Eventually will want to feed back isos but for now just return result
    return project, result, errors, coq_identifiers, coq_identifiers_to_unfold


def add_files_to_CoqProject(coq_project: CoqProject, *files: str):
    coq_project = coq_project.copy()
    coq_project_contents = coq_project["_CoqProject"].contents
    assert isinstance(coq_project_contents, str), (
        f"{coq_project_contents!r} is not a string"
    )
    coq_project_lines = [f.strip() for f in coq_project_contents.splitlines()]
    coq_project_contents = "\n".join(
        coq_project_lines + [f for f in files if f not in coq_project_lines]
    )
    coq_project["_CoqProject"] = File(coq_project_contents)
    coq_project.debug_files.add("_CoqProject")
    return coq_project


def remove_files_from_CoqProject(coq_project: CoqProject, *files: str):
    coq_project = coq_project.copy()
    coq_project_contents = coq_project["_CoqProject"].contents
    assert isinstance(coq_project_contents, str), (
        f"{coq_project_contents!r} is not a string"
    )
    coq_project_lines = [f.strip() for f in coq_project_contents.splitlines()]
    coq_project_contents = "\n".join([f for f in coq_project_lines if f not in files])
    coq_project["_CoqProject"] = File(coq_project_contents)
    return coq_project


def init_coq_project(
    directory: str | Path = f"{SOURCE_DIR}/iso-checker",
    initial_targets: Iterable[str] | None = (),
    allow_build_failure: bool = True,
    init_empty_files: Iterable[str] = ("Isomorphisms.v", "Checker.v", "Interface.v"),
    filter_out_files: Iterable[str] = ("AutomationTests.v",),
) -> CoqProject:
    directory = Path(directory)
    init_empty_files = tuple(init_empty_files)
    file_filter = None
    coq_project_contents = None
    if (directory / "_CoqProject").exists():
        file_filter = set(["_CoqProject", "Makefile"])
        coq_project_contents = (directory / "_CoqProject").read_text()
        for line in coq_project_contents.splitlines():
            line = line.strip()
            if line.endswith(".v") and line not in filter_out_files:
                file_filter.add(line)
    _, coq_project = CoqProject.read(directory, file_filter=file_filter).clean()
    for f in coq_project:
        if f.endswith(".vo"):
            del coq_project[f]
    for f in init_empty_files:
        coq_project[f] = CoqFile("")
    coq_project.debug_files.update(init_empty_files)
    if coq_project_contents:
        coq_project["_CoqProject"] = File(coq_project_contents)
        coq_project = add_files_to_CoqProject(coq_project, *init_empty_files)
        coq_project = remove_files_from_CoqProject(coq_project, *filter_out_files)
    if initial_targets is not None:
        extra_flags = ["-k"] if allow_build_failure else []
        coq_project.write(Path(__file__).parent.parent / "temp_init_targets")
        result, coq_project = coq_project.make(
            *initial_targets, *extra_flags, check=not allow_build_failure
        )
        assert allow_build_failure or result.returncode == 0, (result, coq_project)
    return coq_project


class IsoIsAlreadyAdmittedError(ValueError):
    pass


def admit_failing_iso(
    cc_identifiers_blocks: list[str | IsoBlock],
    orig_source: str,
    orig_target: str | None = None,
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    remove_if_admitted: bool = True,
) -> list[str | IsoBlock]:
    cc_identifiers_blocks = deepcopy(cc_identifiers_blocks)
    index, block = find_iso_and_index(
        cc_identifiers_blocks,
        orig_source,
        orig_target,
        original_name=original_name,
        imported_name=imported_name,
    )
    if remove_if_admitted and block.proof == "Admitted.":
        if block.is_required:
            raise IsoIsAlreadyAdmittedError(
                f"Cannot remove required iso {orig_source} to {orig_target}"
            )
        else:
            logging.warning(
                f"Removing non-required iso {orig_source} to {orig_target} because it is already admitted"
            )
            del cc_identifiers_blocks[index]
        return cc_identifiers_blocks
    else:
        block.proof = "Admitted."
    cc_identifiers_blocks[index] = block
    logging.info(f"Admitted iso proof for {orig_source} to {orig_target}")
    return cc_identifiers_blocks


def generate_and_autorepair_isos(
    project: CoqProject,
    cc_identifiers_blocks: list[str | IsoBlock],
    *,
    admit_failing_isos: bool = False,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
    write_to_directory_on_error: Path | str | None = Path(__file__).parent.parent
    / "generate_and_autorepair_isos_errors",
    autofix_heuristics: Sequence[
        tuple[str, Callable[[IsoError], bool], Callable[[IsoError], str]]
    ] = (),
) -> tuple[
    CoqProject,
    list[str | IsoBlock],
    bool,
    IsoError | NonIsoBlockError | None,
]:
    project = generate_isos(
        project,
        cc_identifiers_blocks,
        original_name=original_name,
        imported_name=imported_name,
        output_file=iso_file,
    )

    # Check that the iso proof compiles
    project, result, errors = make_isos(project, "Checker.vo")
    if result:
        return project, cc_identifiers_blocks, True, None

    assert errors is not None, project

    if write_to_directory_on_error is not None:
        logging.info(f"Writing errors to {write_to_directory_on_error}")
        write_to_directory_on_error = Path(write_to_directory_on_error)

    extra_write = ""
    if write_to_directory_on_error:
        key = str(hash(project))
        (write_to_directory_on_error / key).mkdir(parents=True, exist_ok=True)
        now = datetime.datetime.now()
        iso_string = now.isoformat()
        extra_write = f" (in {write_to_directory_on_error / key / iso_string})"
        if len(list((write_to_directory_on_error / key).iterdir())) == 0:
            project.write(
                write_to_directory_on_error / key / iso_string, log=logging.error
            )
            (write_to_directory_on_error / key / iso_string / "errors.txt").write_text(
                errors
            )
        else:
            logging.error("Touching %s", write_to_directory_on_error / key / iso_string)
            (write_to_directory_on_error / key / iso_string).touch()

    logging.info(
        "Isomorphism proof%s failed to compile, attempting to repair...", extra_write
    )

    error = parse_iso_errors(
        errors,
        project=project,
        cc_identifiers_blocks=cc_identifiers_blocks,
        original_name=original_name,
        imported_name=imported_name,
        iso_file=iso_file,
    )
    logging.info(f"Current error type is {type(error).__name__}")

    try:
        if isinstance(error, MissingTypeIso):
            try:
                project, cc_identifiers_blocks = repair_missing_type_iso(
                    project,
                    error,
                    cc_identifiers_blocks,
                    original_name=original_name,
                    imported_name=imported_name,
                    iso_file=iso_file,
                )
            except (AssertionError, ValueError) as e:
                e.args = (*e.args, error, errors)
                raise e
            return generate_and_autorepair_isos(
                project,
                cc_identifiers_blocks,
                admit_failing_isos=admit_failing_isos,
                original_name=original_name,
                imported_name=imported_name,
                iso_file=iso_file,
                write_to_directory_on_error=write_to_directory_on_error,
            )
        elif isinstance(error, MissingImport):
            if error.import_str in KNOWN_IMPORTS:
                logging.info(
                    f"Adding import {KNOWN_IMPORTS[error.import_str]} for iso_statement {error.orig_source} {error.orig_target}"
                )
                cc_identifiers_blocks.insert(
                    0,
                    KNOWN_IMPORTS[error.import_str],
                )
            elif (
                has_identifier_prefix(error.import_str, imported_name)
                and error.iso_index is not None
            ):
                logging.info(
                    f"Removing import prefix {imported_name} from {error.import_str} for iso_statement {error.orig_source} {error.orig_target}"
                )
                block = cc_identifiers_blocks[error.iso_index]
                assert isinstance(block, IsoBlock), (
                    f"Block {error.iso_index} is not an IsoBlock: {block}"
                )
                assert str(block.target) == error.import_str, (
                    f"Block {error.iso_index} has target {block.target} which does not match import {error.import_str}"
                )
                block.target = remove_identifier_prefix(block.target, imported_name)
                cc_identifiers_blocks[error.iso_index] = block
            else:
                if (
                    has_identifier_prefix(error.import_str, imported_name)
                    and error.iso_index is None
                ):
                    logging.info(
                        f"Could not find iso_index for {error.import_str} for iso_statement {error.orig_source} {error.orig_target}"
                    )
                if admit_failing_isos:
                    cc_identifiers_blocks = admit_failing_iso(
                        cc_identifiers_blocks,
                        error.orig_source,
                        error.orig_target,
                        original_name=original_name,
                        imported_name=imported_name,
                    )
                else:
                    if write_to_directory_on_error is not None:
                        project.write(write_to_directory_on_error)
                    return project, cc_identifiers_blocks, False, error
            return generate_and_autorepair_isos(
                project,
                cc_identifiers_blocks,
                admit_failing_isos=admit_failing_isos,
                original_name=original_name,
                imported_name=imported_name,
                iso_file=iso_file,
                write_to_directory_on_error=write_to_directory_on_error,
            )

        elif isinstance(error, DisorderedConstr):
            can_autofix = can_autofix_disordered_constr(
                error,
                cc_identifiers_blocks,
                original_name=original_name,
                imported_name=imported_name,
            )
            if can_autofix or admit_failing_isos:
                if can_autofix:
                    project, cc_identifiers_blocks = autofix_disordered_constr(
                        project,
                        error,
                        cc_identifiers_blocks,
                        original_name=original_name,
                        imported_name=imported_name,
                        iso_file=iso_file,
                    )
                else:
                    cc_identifiers_blocks = admit_failing_iso(
                        cc_identifiers_blocks,
                        error.orig_source,
                        error.orig_target,
                        original_name=original_name,
                        imported_name=imported_name,
                    )
                return generate_and_autorepair_isos(
                    project,
                    cc_identifiers_blocks,
                    admit_failing_isos=admit_failing_isos,
                    original_name=original_name,
                    imported_name=imported_name,
                    iso_file=iso_file,
                    write_to_directory_on_error=write_to_directory_on_error,
                )
            else:
                if write_to_directory_on_error is not None:
                    project.write(write_to_directory_on_error)
                return project, cc_identifiers_blocks, False, error
        elif isinstance(error, GenericIsoError):
            for heuristic_name, can_autofix, autofix in autofix_heuristics:
                if can_autofix(error):
                    new_proof = autofix(error)
                    index, block = find_iso_and_index(
                        cc_identifiers_blocks,
                        error.orig_source,
                        error.orig_target,
                        original_name=original_name,
                        imported_name=imported_name,
                    )
                    logging.info(
                        f"Autofixing iso proof for {error.orig_source} to {error.orig_target} using heuristic {heuristic_name}"
                    )
                    block.proof = new_proof
                    cc_identifiers_blocks[index] = block
                    return generate_and_autorepair_isos(
                        project,
                        cc_identifiers_blocks,
                        admit_failing_isos=admit_failing_isos,
                        original_name=original_name,
                        imported_name=imported_name,
                        iso_file=iso_file,
                        write_to_directory_on_error=write_to_directory_on_error,
                    )
            if admit_failing_isos:
                cc_identifiers_blocks = admit_failing_iso(
                    cc_identifiers_blocks,
                    error.orig_source,
                    error.orig_target,
                    original_name=original_name,
                    imported_name=imported_name,
                )
                return generate_and_autorepair_isos(
                    project,
                    cc_identifiers_blocks,
                    admit_failing_isos=admit_failing_isos,
                    original_name=original_name,
                    imported_name=imported_name,
                    iso_file=iso_file,
                    write_to_directory_on_error=write_to_directory_on_error,
                )
            else:
                if write_to_directory_on_error is not None:
                    project.write(write_to_directory_on_error)
                return project, cc_identifiers_blocks, False, error
        elif isinstance(error, NonIsoBlockError):
            if admit_failing_isos:
                # remove the failing block
                logging.info(f"Remove block {error.block_index}: {error.block}")
                logging.debug(f"Error message: {error.error}")
                del cc_identifiers_blocks[error.block_index]
                return generate_and_autorepair_isos(
                    project,
                    cc_identifiers_blocks,
                    admit_failing_isos=admit_failing_isos,
                    original_name=original_name,
                    imported_name=imported_name,
                    iso_file=iso_file,
                    write_to_directory_on_error=write_to_directory_on_error,
                )
            else:
                if write_to_directory_on_error is not None:
                    project.write(write_to_directory_on_error)
                return project, cc_identifiers_blocks, False, error
        elif isinstance(error, AmbiguousIsoError) or isinstance(
            error, IsoErrorWithoutHints
        ):
            if admit_failing_isos:
                # we can remove this failing iso if it's actually an iso and the block is a string or is not required
                cc_identifiers_blocks = admit_failing_iso(
                    cc_identifiers_blocks,
                    error.orig_source,
                    error.orig_target,
                    original_name=original_name,
                    imported_name=imported_name,
                )
                return generate_and_autorepair_isos(
                    project,
                    cc_identifiers_blocks,
                    admit_failing_isos=admit_failing_isos,
                    original_name=original_name,
                    imported_name=imported_name,
                    iso_file=iso_file,
                    write_to_directory_on_error=write_to_directory_on_error,
                )
            if write_to_directory_on_error is not None:
                project.write(write_to_directory_on_error)
            return project, cc_identifiers_blocks, False, error
        else:
            assert False, f"Unknown error type {type(error)}: {error}"
    except IsoIsAlreadyAdmittedError as e:
        extra_err = f" because {str(e)}"
        if write_to_directory_on_error is not None:
            project.write(write_to_directory_on_error)
            extra_err += f" and written to {write_to_directory_on_error}"
        logging.error(f"Failed to admit iso proof for {error}{extra_err}")
        return project, cc_identifiers_blocks, False, error


class IsoAlreadyExistsErrorArguments(NamedTuple):
    source: str
    target: str
    before_source: str
    before_target: str
    index: int
    existing_index: int


class IsoAlreadyExistsError(Exception):
    args: tuple[IsoAlreadyExistsErrorArguments]
