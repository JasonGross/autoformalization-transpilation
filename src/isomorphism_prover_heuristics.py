import re

from project_util import GenericIsoError, IsoError


def can_autofix_nat_mul2_proof(e: IsoError) -> bool:
    if not isinstance(e, GenericIsoError):
        return False
    if not e.orig_source.endswith("Nat.mul"):
        return False
    if (
        e.orig_proof
        == "iso. iso_rel_rewrite Nat.mul_comm. iso. iso_rel_rewrite Nat.add_comm. iso."
    ):
        return False
    return bool(re.search(r"rel_iso nat_iso \(\w+ \+ \w+ \* \w+\)", e.simplified_goals))


def autofix_nat_mul2_proof(
    error: IsoError,
) -> str:
    return "iso. iso_rel_rewrite Nat.mul_comm. iso. iso_rel_rewrite Nat.add_comm. iso."


ALL_HEURISTICS = (
    ("second Nat.mul heuristic", can_autofix_nat_mul2_proof, autofix_nat_mul2_proof),
)
