from typing import Iterable, TypeVar

T = TypeVar("T")


def unique(iterable: Iterable[T]) -> Iterable[T]:
    """Return a new iterable with duplicates removed"""
    seen = []
    seen_set = set()
    for item in iterable:
        if seen_set is None and item in seen:
            continue
        if seen_set is not None and item in seen_set:
            continue
        yield item
        seen.append(item)
        if seen_set is not None:
            try:
                seen_set.add(item)
            except TypeError:
                seen_set = None
