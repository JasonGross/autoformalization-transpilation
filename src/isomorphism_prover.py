import re
from functools import lru_cache
from pathlib import Path
from typing import Iterable, Optional

from config import (
    ISO_CHECKER_HEADER,
    ISO_HEADER,
    ISO_INTERFACE_HEADER,
    ISO_RETRIES,
    KNOWN_IMPORTS,
    KNOWN_PAIRS,
    SOURCE_DIR,
)
from project_util import (
    CoqFile,
    CoqIdentifier,
    CoqProject,
    DisorderedConstr,
    GenericIsoError,
    IsoError,
    MissingImport,
    MissingTypeIso,
    desigil,
)
from utils import logging


def generate_and_prove_iso(
    project: CoqProject,
    cc_identifiers_blocks: list[str | tuple[CoqIdentifier, CoqIdentifier, str | None]],
) -> tuple[CoqProject, bool, Optional[str]]:
    # Make demo file
    project = generate_isos(project, cc_identifiers_blocks)

    # Check that the iso proof compiles
    project, result, errors = make_isos(project, "Checker.vo")

    if result:
        logging.info("Isomorphism proof succeeded")
    else:
        attempt = 0
        # TODO: Only steps that call out to the llm should decrease the retry count, and the retry count should be per-isomorphism.
        # That is, we should be able to add as many missing isomorphisms as are required, and we shouldn't quit early if we are
        # making progress towards proving more and more isomorphisms.
        while attempt < ISO_RETRIES and errors:
            project, cc_identifiers_blocks = repair_isos(
                project, errors, cc_identifiers_blocks
            )
            # Check that the iso proof compiles
            project, result, errors = make_isos(project, "Checker.vo")
            if not result:
                # Should feed all errors for iso repair
                logging.info(f"Isomorphism proof failed on attempt {attempt}:")
                if attempt < ISO_RETRIES - 1:
                    logging.debug(errors)
                    logging.info("Retrying...")
                else:
                    logging.info(errors)
                    logging.info("Isomorphism proof failed on final attempt")
            attempt += 1

    # Eventually will want to feed back isos but for now just return result
    return project, result, errors


def make_isos_interface(project: CoqProject) -> tuple[CoqProject, bool, Optional[str]]:
    return make_isos(project, "Interface.vo")


def generate_isos(
    project: CoqProject,
    cc_identifiers_blocks: list[str | tuple[CoqIdentifier, CoqIdentifier, str | None]],
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    output_file: str = "Isomorphisms.v",
) -> CoqProject:
    project = project.copy()

    # Retrieve exported Lean file
    project["imported.out"] = project["target.out"]

    # Should also be generating these programmatically, for now these are manual
    # TODO: This should happen in the reimport step!
    # Generate the isomorphism checks for each definition pair
    iso_checks = []
    iso_names = []
    for block in cc_identifiers_blocks:
        if isinstance(block, str):
            iso_checks.append(block)
        else:
            coq_name, coq_lean_name, proof = block
            proof = proof or "iso."
            first_id = coq_name
            second_id = coq_lean_name
            coq_id = str(coq_name).replace(".", "_")
            iso_name = f"{coq_id}_iso"
            if coq_id[0] == "$":
                # Python is dynamically typed for a reason
                coq_name = str(coq_name)[1:]  # type: ignore
                coq_id = coq_id[1:]
                first_id = f"{original_name}.{coq_name}"  # type: ignore
                iso_name = f"{coq_id}_iso"
                iso_names.append(iso_name)
            elif coq_id[0] == "(":
                assert coq_id[-1] == ")", coq_id
                coq_id = coq_id[1:-1]
                if coq_id[0] == "@":
                    coq_id = coq_id[1:]
                iso_name = f"{coq_id}_iso"
            if str(coq_lean_name)[0] == "$":
                coq_lean_name = str(coq_lean_name)[1:]  # type: ignore
                second_id = imported_name + "." + coq_lean_name  # type: ignore

            if not proof.endswith("Admitted."):
                proof = f"Proof. {proof} Defined."

            iso_block = f"""Instance {iso_name} : iso_statement {first_id} {second_id}.
{proof}
Instance: KnownConstant {first_id} := {{}}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant {second_id} := {{}}. (* only needed when rel_iso is typeclasses opaque *)"""

            iso_checks.append(iso_block)

    # Generate a `Print Assumptions` check for dependencies
    print_assumptions_block = f"""Import IsomorphismChecker.Automation.HList.HListNotations.
Definition everything := ({" :: ".join(iso_names)} :: [])%hlist.
Print Assumptions everything."""

    # Combine all sections
    full_content = "\n\n".join(
        [ISO_HEADER, "\n\n".join(iso_checks), print_assumptions_block]
    )
    logging.debug(f"{full_content}")

    # Write to file
    project[output_file] = CoqFile(full_content)

    return project


def repair_missing_type_iso(
    project: CoqProject,
    error: MissingTypeIso,
    cc_identifiers_blocks: list[str | tuple[CoqIdentifier, CoqIdentifier, str | None]],
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
) -> tuple[CoqProject, list[str | tuple[CoqIdentifier, CoqIdentifier, str | None]]]:
    index = find_iso_index(
        cc_identifiers_blocks,
        error.orig_source,
        error.orig_target,
        original_name=original_name,
        imported_name=imported_name,
    )
    logging.info(
        f"Adding iso_statement {error.source} {error.target} for {error.orig_source} {error.orig_target}"
    )
    assert not has_iso(cc_identifiers_blocks, error.source, error.target), (
        error,
        cc_identifiers_blocks,
    )
    cc_identifiers_blocks.insert(
        index, (CoqIdentifier(error.source), CoqIdentifier(error.target), None)
    )
    project = generate_isos(
        project,
        cc_identifiers_blocks,
        original_name=original_name,
        imported_name=imported_name,
        output_file=iso_file,
    )
    return project, cc_identifiers_blocks


def repair_isos(
    project: CoqProject,
    errors: str,
    cc_identifiers_blocks: list[str | tuple[CoqIdentifier, CoqIdentifier, str | None]],
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
) -> tuple[CoqProject, list[str | tuple[CoqIdentifier, CoqIdentifier, str | None]]]:
    project = project.copy()
    # Look at the errors, attempt to fix the isos
    error = parse_iso_errors(
        errors, iso_file=str(project[iso_file].contents), project=project
    )
    logging.info(f"Current error type is {type(error).__name__}")

    if isinstance(error, MissingTypeIso):
        project, cc_identifiers_blocks = repair_missing_type_iso(
            project,
            error,
            cc_identifiers_blocks,
            original_name=original_name,
            imported_name=imported_name,
            iso_file=iso_file,
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
            project = generate_isos(
                project,
                cc_identifiers_blocks,
                original_name=original_name,
                imported_name=imported_name,
                output_file=iso_file,
            )
        else:
            assert (
                False
            ), f"We are missing an import, please add the correct one - the missing reference is {error.import_str}"
    elif isinstance(error, DisorderedConstr):
        if can_autofix_disordered_constr(
            error,
            cc_identifiers_blocks,
            original_name=original_name,
            imported_name=imported_name,
        ):
            project, cc_identifiers_blocks = autofix_disordered_constr(
                project,
                error,
                cc_identifiers_blocks,
                original_name=original_name,
                imported_name=imported_name,
                iso_file=iso_file,
            )
        else:
            assert False, error
            # Reorder goals (via LLM) and update proof
            # Reorder goals (via LLM) and update proof
            # TODO: Should just define prompts in a dict somewhere
            llm_repair(
                iso_file,
                f"Constructors are out of order, please reorder the goals - the error is {error}",
            )
    elif isinstance(error, GenericIsoError):
        index = find_iso_index(
            cc_identifiers_blocks,
            error.orig_source,
            error.orig_target,
            original_name=original_name,
            imported_name=imported_name,
        )
        unknown_lhs = [
            cst
            for cst in error.unknown_lhs
            if not has_iso_from(
                cc_identifiers_blocks,
                cst,
                original_name=original_name,
                imported_name=imported_name,
            )
        ]
        unknown_rhs = [
            cst
            for cst in error.unknown_rhs
            if not has_iso_to(
                cc_identifiers_blocks,
                cst,
                original_name=original_name,
                imported_name=imported_name,
            )
        ]
        new_pair = llm_suggest_paired_identifier(unknown_lhs, unknown_rhs)
        if new_pair:
            logging.info(
                f"Adding iso_statement {str(new_pair[0])}, {str(new_pair[1])} for {error.orig_source}, {error.orig_target}"
            )
            cc_identifiers_blocks.insert(index, (*new_pair, None))
            project = generate_isos(
                project,
                cc_identifiers_blocks,
                original_name=original_name,
                imported_name=imported_name,
                output_file=iso_file,
            )
        else:
            block = cc_identifiers_blocks[index]
            assert not isinstance(block, str), block
            new_proof = llm_repair_proof(error, block[2])
            if new_proof:
                logging.info(
                    f"Updating iso_statement {error.orig_source} {error.orig_target} with proof {new_proof}"
                )
                cc_identifiers_blocks[index] = (block[0], block[1], new_proof)
                project = generate_isos(
                    project,
                    cc_identifiers_blocks,
                    original_name=original_name,
                    imported_name=imported_name,
                    output_file=iso_file,
                )
            else:
                assert False, error
            # case IsoError.OTHER_ISO_ISSUE:
            #     # Heuristically rewrite to account for Lean vs Coq differences (via LLM / COPRA)
            #     llm_repair(
            #         iso_file, f"Please fix this error in our isomorphisms: {errors}"
            #     )
    return project, cc_identifiers_blocks


def parse_iso_errors(
    errors: str,
    *,
    iso_file: str | None = None,
    project: CoqProject | None = None,
    cc_identifiers_blocks: (
        list[str | tuple[CoqIdentifier, CoqIdentifier, str | None]] | None
    ) = None,
    original_name: str = "Original",
    imported_name: str = "Imported",
) -> IsoError:
    def assert_or_error(condition):
        msg = f"{errors}\nIso file:\n```coq\n{iso_file}\n```" if iso_file else errors
        if not condition:
            assert project is not None, (project, msg)
            project.write(Path(__file__).parent.parent / "temp_iso_errors")
        assert condition, msg

    assert_or_error("Proving iso_statement " in errors)
    errors = errors.split("Proving iso_statement ")[-1]
    last_proving_instance = re.match(
        r"^([\w\.]+) ([\w\.]+)[\s\n]+(.*)$", errors, flags=re.DOTALL
    )
    assert_or_error(last_proving_instance)
    assert last_proving_instance, errors
    orig_source, orig_target, errors = last_proving_instance.groups()
    result = re.search(
        # r"While proving iso_statement ([\w\.]+) ([\w\.]+):
        r"(?:Could not find iso for|could not find iso_statement|Consider adding iso_statement) ([\w\.]+|\(@[\w\.]+\)) (?:-> )?([\w\.]+|\(@[\w\.]+\))",
        errors,
    )
    if result:
        source, target = result.groups()
        if (orig_source, orig_target) != (source, target):
            return MissingTypeIso(orig_source, orig_target, source, target)
    result = re.search(
        r"Error: The reference ([^\s]+) was not found in the current environment.",
        errors,
    )
    if result:
        return MissingImport(orig_source, orig_target, result.group(1))
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
            orig_source, orig_target, hints[0], prefix, hints[1:], suffix
        )

    result = re.match(
        # r"^(.*)[\n\s]*While proving iso_statement ([\w\.]+) ([\w\.]+): (\d+) goals? not fully solved:[\s\n]*(.*)",
        r"^(.*)[\n\s]*Warning:[\s\n]*(\d+) goals? not fully solved:[\s\n]*(.*)",
        errors,
        flags=re.DOTALL,
    )
    assert result, errors
    prefix, ngoals, goals = result.groups()
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
        orig_source, orig_target, unknown_lhs, unknown_rhs, prefix, int(ngoals), goals
    )


def make_isos(
    project: CoqProject, *targets: str
) -> tuple[CoqProject, bool, Optional[str]]:
    result, project = project.make(*targets, check=False)
    if result.returncode != 0:
        # We log this and then feed it into our iso repair model
        error_message = f"{result.stdout}\n{result.stderr}".strip()
        logging.debug(f"Make failed: {error_message}")
        # Check error message for missing isomorphisms
        if iso_pairs := [
            (match.group(1), match.group(2))
            for match in re.finditer(
                r"Could not find iso for (\w+) -> (\w+)", error_message
            )
        ]:
            logging.info(f"Found missing isomorphisms: {set(iso_pairs)}")
        return project, False, error_message
    return project, True, None


def generate_interface(
    project: CoqProject, coq_identifiers: list[CoqIdentifier]
) -> CoqProject:
    project = project.copy()
    # TODO: Implement https://github.com/JasonGross/autoformalization/pull/19#discussion_r1934686304
    # Can make these parameters if needed
    original_name, output_file, checker_file = (
        "Original",
        "Interface.v",
        "Checker.v",
    )

    # Should also be generating these programmatically, for now these are manual
    # TODO: This should happen in the reimport step!
    # Generate the isomorphism checks for each definition pair
    iso_interface_checks, iso_checks, iso_names = [], [], []
    for coq_name in coq_identifiers:
        first_id = str(coq_name)
        coq_id = str(coq_name).replace(".", "_")
        iso_name = f"{coq_id}_iso"
        if coq_id[0] == "$":
            # Python is dynamically typed for a reason
            coq_name = str(coq_name)[1:]
            coq_id = coq_id[1:]
            first_id = f"{original_name}.{coq_name}"
            iso_name = f"{coq_id}_iso"
            iso_names.append(iso_name)
        elif coq_id[0] == "(":
            assert coq_id[-1] == ")", coq_id
            coq_id = coq_id[1:-1]
            if coq_id[0] == "@":
                coq_id = coq_id[1:]
            iso_name = f"{coq_id}_iso"
        iso_interface_block = f"""Parameter imported_{coq_id} : import_of {first_id}.
Parameter {iso_name} : iso_statement {first_id} imported_{coq_id}.
Existing Instance {iso_name}."""
        iso_interface_checks.append(iso_interface_block)
        iso_block = f"""Derive imported_{coq_id} in (iso_statement {first_id} (imported_{coq_id} :> import_of {first_id})) as {iso_name}.
Proof. subst imported_{coq_id}. exact Isomorphisms.{iso_name}. Defined.
Existing Instance {iso_name}."""
        iso_checks.append(iso_block)

    # Generate a `Print Assumptions` check for dependencies
    everything_interface_block = f"""Import IsomorphismChecker.Automation.HList.HListNotations.
Definition everything := ({" :: ".join(iso_names)} :: [])%hlist."""

    everything_block = f"""Definition everything := Isomorphisms.everything."""

    # Combine all sections
    full_interface_content = "\n\n".join(
        [
            ISO_INTERFACE_HEADER,
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

    # Write to file
    project[checker_file] = CoqFile(full_content)

    return project


def repair_isos_interface(
    project: CoqProject,
    errors: str,
    coq_identifiers: list[CoqIdentifier],
    *,
    original_name: str = "Original",
    interface_file: str = "Interface.v",
) -> tuple[CoqProject, list[CoqIdentifier]]:
    # Look at the errors, attempt to fix the isos
    result = re.search(
        r"While importing ([\w\.]+): Consider adding iso_statement ([\w\.]+|\(@[\w\.]+\)) ",
        re.sub(r"\s+", " ", errors),
    )
    if result is None:
        project.write(Path(__file__).parent.parent / "temp_interface_errors")
    assert result is not None, (project[interface_file], re.sub(r"\s+", " ", errors))
    orig_source, source = result.groups()
    coq_identifiers_str = [
        desigil(str(s), f"{original_name}.") for s in coq_identifiers
    ]
    assert orig_source in coq_identifiers_str, (
        orig_source,
        coq_identifiers_str,
    )
    logging.info(f"Adding iso_statement {source} for {orig_source}")
    index = coq_identifiers_str.index(orig_source)
    coq_identifiers.insert(index, CoqIdentifier(source))
    project = generate_interface(project, coq_identifiers)
    return project, coq_identifiers


@lru_cache()
def make_identifiers_str_helper(
    cc_identifiers_blocks: tuple[str | tuple[CoqIdentifier, CoqIdentifier, str | None]],
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
) -> list[tuple[str | None, str | None]]:
    cc_identifiers = [
        (None, None, None) if isinstance(v, str) else v for v in cc_identifiers_blocks
    ]
    return [
        (
            desigil(str(s), f"{original_name}.") if s is not None else None,
            desigil(str(t), f"{imported_name}.") if t is not None else None,
        )
        for s, t, _ in cc_identifiers
    ]


def make_identifiers_str(
    cc_identifiers_blocks: list[str | tuple[CoqIdentifier, CoqIdentifier, str | None]],
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
    cc_identifiers_blocks: list[str | tuple[CoqIdentifier, CoqIdentifier, str | None]],
    orig_source: str,
    orig_target: str | None = None,
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
) -> int:
    cc_identifiers_str = make_identifiers_str(
        cc_identifiers_blocks, original_name=original_name, imported_name=imported_name
    )
    if orig_target is not None:
        return cc_identifiers_str.index((orig_source, orig_target))
    else:
        c_identifiers_str = [s for s, _ in cc_identifiers_str]
        return c_identifiers_str.index(orig_source)


def has_iso(
    cc_identifiers_blocks: list[str | tuple[CoqIdentifier, CoqIdentifier, str | None]],
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
    cc_identifiers_blocks: list[str | tuple[CoqIdentifier, CoqIdentifier, str | None]],
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
    cc_identifiers_blocks: list[str | tuple[CoqIdentifier, CoqIdentifier, str | None]],
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
    cc_identifiers_blocks: list[str | tuple[CoqIdentifier, CoqIdentifier, str | None]],
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
    assert not isinstance(block, str), block
    return block[2] is None


def autofix_disordered_constr(
    project: CoqProject,
    error: DisorderedConstr,
    cc_identifiers_blocks: list[str | tuple[CoqIdentifier, CoqIdentifier, str | None]],
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
) -> tuple[CoqProject, list[str | tuple[CoqIdentifier, CoqIdentifier, str | None]]]:
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
    cc_identifiers_blocks[index] = (block[0], block[1], new_proof)
    project = generate_isos(
        project,
        cc_identifiers_blocks,
        original_name=original_name,
        imported_name=imported_name,
        output_file=iso_file,
    )
    return project, cc_identifiers_blocks


def llm_repair_proof(
    error: GenericIsoError,
    cur_proof: str | None,
) -> str:
    if cur_proof is None:
        if re.search(r"rel_iso nat_iso .[\w\.\d]+ \+ [\w\.\d]+.", error.goals):
            return "iso_no_debug_init. iso_rel_rewrite Nat.add_comm. iso_continue."
        if re.search(r"rel_iso nat_iso .[\w\.\d]+ \* [\w\.\d]+.", error.goals):
            return "iso_no_debug_init. iso_rel_rewrite Nat.mul_comm. iso_continue."
        if " ++ " in error.goals:
            return "iso_no_debug_init. iso_rel_rewrite List.app_assoc. iso_continue."
    elif (
        re.search(r"rel_iso nat_iso .[\w\.\d]+ \+ [\w\.\d]+ \* [\w\.\d]+.", error.goals)
        and cur_proof
        == "iso_no_debug_init. iso_rel_rewrite Nat.mul_comm. iso_continue."
    ):
        return "iso_no_debug_init. iso_rel_rewrite Nat.mul_comm. iso_no_debug. iso_rel_rewrite Nat.add_comm. iso_continue."

    # Call out to the LLM
    logging.info(error)
    assert False, (error, cur_proof)


def llm_repair(file, prompt: str) -> None:
    # Call out to the LLM
    assert False, (file, prompt)


def llm_suggest_paired_identifier(
    lhs: list[str], rhs: list[str]
) -> tuple[CoqIdentifier, CoqIdentifier] | None:
    for coq_id, imported_id in KNOWN_PAIRS:
        if coq_id in lhs and imported_id in rhs:
            return (CoqIdentifier(coq_id), CoqIdentifier(imported_id))
    return None


def generate_and_prove_iso_interface(
    project: CoqProject,
    coq_identifiers: list[CoqIdentifier],
) -> tuple[CoqProject, bool, Optional[str]]:
    # Make interface file
    project = generate_interface(project, coq_identifiers)

    # Check that the iso proof compiles
    project, result, errors = make_isos_interface(project)

    if result:
        logging.info("Isomorphism interface proof succeeded")
    else:
        attempt = 0
        while errors:
            attempt += 1
            logging.info(f"Isomorphism interface proof failed on attempt {attempt}")
            logging.debug(errors)
            project, coq_identifiers = repair_isos_interface(
                project, errors, coq_identifiers
            )
            project, result, errors = make_isos_interface(project)

    # Eventually will want to feed back isos but for now just return result
    return project, result, errors


def init_coq_project(
    directory: str | Path = f"{SOURCE_DIR}/iso-checker",
    initial_targets: Iterable[str] | None = (),
    allow_build_failure: bool = True,
    init_empty_files: Iterable[str] = ("Isomorphisms.v", "Checker.v", "Interface.v"),
) -> CoqProject:
    _, coq_project = CoqProject.read(directory).clean()
    for f in init_empty_files:
        coq_project[f] = CoqFile("")
    if initial_targets is not None:
        extra_flags = ["-k"] if allow_build_failure else []
        result, coq_project = coq_project.make(
            *initial_targets, *extra_flags, check=not allow_build_failure
        )
        assert allow_build_failure or result.returncode == 0, (result, coq_project)
    return coq_project


def admit_failing_iso(
    project: CoqProject,
    cc_identifiers_blocks: list[str | tuple[CoqIdentifier, CoqIdentifier, str | None]],
    orig_source: str,
    orig_target: str | None = None,
    *,
    original_name: str = "Original",
    imported_name: str = "Imported",
) -> tuple[CoqProject, list[str | tuple[CoqIdentifier, CoqIdentifier, str | None]]]:
    index = find_iso_index(
        cc_identifiers_blocks,
        orig_source,
        orig_target,
        original_name=original_name,
        imported_name=imported_name,
    )
    block = cc_identifiers_blocks[index]
    assert not isinstance(block, str), (
        orig_source,
        orig_target,
        block,
        index,
        cc_identifiers_blocks,
    )
    cc_identifiers_blocks[index] = (
        block[0],
        block[1],
        "Admitted.",
    )
    logging.info(f"Admitted iso proof for {orig_source} to {orig_target}")
    return project, cc_identifiers_blocks


def generate_and_autorepair_isos(
    project: CoqProject,
    cc_identifiers_blocks: list[str | tuple[CoqIdentifier, CoqIdentifier, str | None]],
    *,
    admit_failing_isos: bool = False,
    original_name: str = "Original",
    imported_name: str = "Imported",
    iso_file: str = "Isomorphisms.v",
    write_to_directory_on_error: Path | str | None = Path(__file__).parent.parent
    / "generate_and_autorepair_isos_errors",
) -> tuple[
    CoqProject,
    list[str | tuple[CoqIdentifier, CoqIdentifier, str | None]],
    bool,
    IsoError | None,
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

    logging.info("Isomorphism proof failed to compile, attempting to repair...")

    error = parse_iso_errors(
        errors,
        iso_file=str(project[iso_file].contents),
        project=project,
        cc_identifiers_blocks=cc_identifiers_blocks,
        original_name=original_name,
        imported_name=imported_name,
    )
    logging.info(f"Current error type is {type(error).__name__}")

    if isinstance(error, MissingTypeIso):
        project, cc_identifiers_blocks = repair_missing_type_iso(
            project,
            error,
            cc_identifiers_blocks,
            original_name=original_name,
            imported_name=imported_name,
            iso_file=iso_file,
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
    elif isinstance(error, MissingImport):
        if error.import_str in KNOWN_IMPORTS or admit_failing_isos:
            if error.import_str in KNOWN_IMPORTS:
                logging.info(
                    f"Adding import {KNOWN_IMPORTS[error.import_str]} for iso_statement {error.orig_source} {error.orig_target}"
                )
                cc_identifiers_blocks.insert(
                    0,
                    KNOWN_IMPORTS[error.import_str],
                )
            else:
                project, cc_identifiers_blocks = admit_failing_iso(
                    project,
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
                project, cc_identifiers_blocks = admit_failing_iso(
                    project,
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
        if admit_failing_isos:
            project, cc_identifiers_blocks = admit_failing_iso(
                project,
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
    else:
        assert False, f"Unknown error type {type(error)}: {error}"
