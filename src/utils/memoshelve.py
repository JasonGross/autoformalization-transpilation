import os
import traceback
import shelve
from hashlib import sha256
import base64
from contextlib import contextmanager
from functools import wraps
from pathlib import Path
from typing import Any, Callable, Dict, Optional, Union, TypeVar
from utils import logging
from dill import Pickler, Unpickler

# from frozendict import frozendict
from utils.hashing import get_hash_ascii

from . import backup as backup_file

# from .utils.hashing import get_hash_ascii

# monkeypatch shelve as per https://stackoverflow.com/q/52927236/377022
shelve.Pickler = Pickler
shelve.Unpickler = Unpickler

memoshelve_cache: Dict[str, Dict[str, Any]] = {}
T = TypeVar("T")

DEFAULT_PRINT_MEM_CACHE_MISS = False
DEFAULT_PRINT_MEM_CACHE_HIT = False
DEFAULT_PRINT_DISK_CACHE_MISS = True
DEFAULT_PRINT_DISK_CACHE_HIT = False
DEFAULT_PRINT_CACHE_MISS_FN = logging.warning
DEFAULT_PRINT_CACHE_HIT_FN = logging.debug


# def to_tuples(arg: Any, *, dict_class: type = frozendict) -> Any:
#     """Converts a list or dict to an immutable version of itself."""
#     if isinstance(arg, list) or isinstance(arg, tuple):
#         return tuple(to_tuples(e, dict_class=dict_class) for e in arg)
#     elif isinstance(arg, dict):
#         return dict_class(
#             (k, to_tuples(v, dict_class=dict_class)) for k, v in arg.items()
#         )
#     else:
#         return arg


# def sha256_hash(obj: Any) -> str:
#     return sha256(repr(obj).encode("utf-8")).hexdigest()


# def hash_as_tuples(obj: Any) -> str:
#     return sha256_hash(to_tuples(obj))


def compact(filename: Union[Path, str], backup: bool = True):
    entries = {}
    with shelve.open(filename) as db:
        for k in db.keys():
            entries[k] = db[k]
    if backup:
        backup_name = backup_file(filename)
    else:
        backup_name = None
        os.remove(filename)
    with shelve.open(filename) as db:
        for k in entries.keys():
            db[k] = entries[k]
    if backup_name:
        assert backup_name != filename, backup_name
        os.remove(backup_name)


def memoshelve(
    value: Callable,
    filename: Union[Path, str],
    cache: Dict[str, Dict[str, Any]] = memoshelve_cache,
    get_hash: Callable = get_hash_ascii,
    get_hash_mem: Optional[Callable] = None,
    print_cache_miss: bool | None = None,
    print_cache_hit: bool | None = None,
    print_disk_cache_miss: bool | Callable[[str], None] | None = None,
    print_disk_cache_hit: bool | Callable[[str], None] | None = None,
    print_mem_cache_miss: bool | Callable[[str], None] | None = None,
    print_mem_cache_hit: bool | Callable[[str], None] | None = None,
    copy: Callable[[T], T] = lambda x: x,
):
    """Lightweight memoziation using shelve + in-memory cache"""

    def set_print_fn(
        print_val: bool | Callable[[str], None] | None,
        print_gen_val: bool | None,
        default_val: bool,
        default_fn: Callable[[str], None],
    ) -> Callable[[str], None]:
        if print_val is None:
            print_val = default_val if print_gen_val is None else print_gen_val
        if print_val is True:
            return default_fn
        elif print_val is False:
            return lambda _: None
        else:
            return print_val

    print_mem_cache_miss = set_print_fn(
        print_mem_cache_miss,
        print_cache_miss,
        DEFAULT_PRINT_MEM_CACHE_MISS,
        DEFAULT_PRINT_CACHE_MISS_FN,
    )
    print_mem_cache_hit = set_print_fn(
        print_mem_cache_hit,
        print_cache_hit,
        DEFAULT_PRINT_MEM_CACHE_HIT,
        DEFAULT_PRINT_CACHE_HIT_FN,
    )
    print_disk_cache_miss = set_print_fn(
        print_disk_cache_miss,
        print_cache_miss,
        DEFAULT_PRINT_DISK_CACHE_MISS,
        DEFAULT_PRINT_CACHE_MISS_FN,
    )
    print_disk_cache_hit = set_print_fn(
        print_disk_cache_hit,
        print_cache_hit,
        DEFAULT_PRINT_DISK_CACHE_HIT,
        DEFAULT_PRINT_CACHE_HIT_FN,
    )

    filename = str(Path(filename).absolute())
    mem_db = cache.setdefault(filename, {})
    if get_hash_mem is None:
        get_hash_mem = get_hash

    @contextmanager
    def open_db():
        Path(filename).parent.mkdir(parents=True, exist_ok=True)
        with shelve.open(filename) as db:

            def delegate(*args, **kwargs):
                mkey = get_hash_mem((args, kwargs))
                try:
                    result = mem_db[mkey]
                    print_mem_cache_hit(f"Cache hit (mem): {mkey}")
                    return result
                except KeyError:
                    print_mem_cache_miss(f"Cache miss (mem): {mkey}")
                    key = str(get_hash((args, kwargs)))
                    try:
                        mem_db[mkey] = db[key]
                        print_disk_cache_hit(f"Cache hit (disk): {key}")
                        return mem_db[mkey]
                    except Exception as e:
                        if isinstance(e, KeyError):
                            frames = traceback.extract_stack()
                            # Remove the current frame and the memoshelve internal frames
                            frames = [
                                f for f in frames if "memoshelve.py" not in f.filename
                            ]
                            print_disk_cache_miss(
                                f"Cache miss (disk): {key} ({value.__name__ if hasattr(value, '__name__') else 'anonymous'}) ({[f.filename + ":" + f.name for f in frames]})"
                            )
                        elif isinstance(e, (KeyboardInterrupt, SystemExit)):
                            raise e
                        else:
                            print(f"Error {e} in {filename} with key {key}")
                        if not isinstance(e, (KeyError, AttributeError)):
                            raise e
                    mem_db[mkey] = db[key] = copy(value(*args, **kwargs))
                    return mem_db[mkey]

            yield delegate

    return open_db


def uncache(
    *args,
    filename: Union[Path, str],
    cache: Dict[str, Dict[str, Any]] = memoshelve_cache,
    get_hash: Callable = get_hash_ascii,
    get_hash_mem: Optional[Callable] = None,
    **kwargs,
):
    """Lightweight memoziation using shelve + in-memory cache"""
    filename = str(Path(filename).absolute())
    mem_db = cache.setdefault(filename, {})
    if get_hash_mem is None:
        get_hash_mem = get_hash

    with shelve.open(filename) as db:
        mkey = get_hash_mem((args, kwargs))
        if mkey in mem_db:
            del mem_db[mkey]
        key = get_hash((args, kwargs))
        if key in db:
            del db[key]


# for decorators
def cache(
    filename: Path | str | None = None,
    cache: Dict[str, Dict[str, Any]] = memoshelve_cache,
    get_hash: Callable = get_hash_ascii,
    get_hash_mem: Optional[Callable] = None,
    print_cache_miss: bool | None = None,
    print_cache_hit: bool | None = None,
    print_disk_cache_miss: bool | Callable[[str], None] | None = None,
    print_disk_cache_hit: bool | Callable[[str], None] | None = None,
    print_mem_cache_miss: bool | Callable[[str], None] | None = None,
    print_mem_cache_hit: bool | Callable[[str], None] | None = None,
    disable: bool = False,
    copy: Callable[[T], T] = lambda x: x,
):
    def wrap(value):
        path = (
            Path(filename)
            if filename
            else Path(__file__).parent.parent.parent
            / ".cache"
            / f"{value.__name__}.shelve"
        )
        path.parent.mkdir(parents=True, exist_ok=True)

        @wraps(value)
        def wrapper(*args, **kwargs):
            if disable:
                return value(*args, **kwargs)
            else:
                with memoshelve(
                    value,
                    filename=path,
                    cache=cache,
                    get_hash=get_hash,
                    get_hash_mem=get_hash_mem,
                    print_cache_miss=print_cache_miss,
                    print_cache_hit=print_cache_hit,
                    print_disk_cache_miss=print_disk_cache_miss,
                    print_disk_cache_hit=print_disk_cache_hit,
                    print_mem_cache_miss=print_mem_cache_miss,
                    print_mem_cache_hit=print_mem_cache_hit,
                    copy=copy,
                )() as f:
                    return f(*args, **kwargs)

        return wrapper

    return wrap
