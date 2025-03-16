"""
Generate stable hashes for Python data objects.
Contains no business logic.

The hashes should be stable across interpreter implementations and versions.

Supports dataclass instances, datetimes, and JSON-serializable objects.

Empty dataclass fields are ignored, to allow adding new fields without
the hash changing. Empty means one of: None, '', (), [], or {}.

The dataclass type is ignored: two instances of different types
will have the same hash if they have the same attribute/value pairs.

"""

import dataclasses
import datetime
import hashlib
import json
from collections.abc import Collection
from typing import Any
from typing import Dict

# LICENSE for this file:
_LICENSE = """
Copyright 2018 lemon24

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

1.  Redistributions of source code must retain the above copyright
    notice, this list of conditions and the following disclaimer.

2.  Redistributions in binary form must reproduce the above copyright
    notice, this list of conditions and the following disclaimer in the
    documentation and/or other materials provided with the distribution.

3.  Neither the name of the copyright holder nor the names of its
    contributors may be used to endorse or promote products derived from
    this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

"""

# Implemented for https://github.com/lemon24/reader/issues/179


# The first byte of the hash contains its version,
# to allow upgrading the implementation without changing existing hashes.
# (In practice, it's likely we'll just let the hash change and update
# the affected objects again; nevertheless, it's good to have the option.)
#
# A previous version recommended using a check_hash(thing, hash) -> bool
# function instead of direct equality checking; it was removed because
# it did not allow objects to cache the hash.

_VERSION = 0
_EXCLUDE = "_hash_exclude_"


def get_hash(thing: object) -> bytes:
    prefix = _VERSION.to_bytes(1, "big")
    digest = hashlib.md5(_json_dumps(thing).encode("utf-8")).digest()
    return prefix + digest[:-1]

def get_hash_ascii(thing: object) -> str:
    return get_hash(thing).hex()

def _json_dumps(thing: object) -> str:
    return json.dumps(
        thing,
        default=_json_default,
        # force formatting-related options to known values
        ensure_ascii=False,
        sort_keys=True,
        indent=None,
        separators=(",", ":"),
    )


def _json_default(thing: object) -> Any:
    try:
        return _dataclass_dict(thing)
    except TypeError:
        pass
    if isinstance(thing, datetime.datetime):
        return thing.isoformat(timespec="microseconds")
    if isinstance(thing, set):
        return list(sorted(map(_json_dumps,thing)))
    if hasattr(thing, "to_json_for_hash"):
        return thing.to_json_for_hash()
    if hasattr(thing, "towards_json_for_hash"):
        return _json_dumps(thing.towards_json_for_hash())
    if hasattr(thing, "to_json"):
        return thing.to_json()
    if hasattr(thing, "towards_json"):
        return _json_dumps(thing.towards_json())
    raise TypeError(f"Object of type {type(thing).__name__} is not JSON serializable")


def _dataclass_dict(thing: object) -> Dict[str, Any]:
    # we could have used dataclasses.asdict()
    # with a dict_factory that drops empty values,
    # but asdict() is recursive and we need to intercept and check
    # the _hash_exclude_ of nested dataclasses;
    # this way, json.dumps() does the recursion instead of asdict()

    # raises TypeError for non-dataclasses
    fields = dataclasses.fields(thing)
    # ... but doesn't for dataclass *types*
    if isinstance(thing, type):
        raise TypeError("got type, expected instance")

    exclude = getattr(thing, _EXCLUDE, ())

    rv = {}
    for field in fields:
        if field.name in exclude:
            continue

        value = getattr(thing, field.name)
        if value is None or not value and isinstance(value, Collection):
            continue

        rv[field.name] = value

    return rv
