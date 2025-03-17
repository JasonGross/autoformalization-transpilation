from typing import TypeVar


T = TypeVar("T")


def handle_none_string(x: T | str | None) -> T | str | None:
    """Since LLMs sometimes pass '"None"' instead of None, we need to handle this case."""
    if isinstance(x, str) and x == "None":
        return None
    return x
