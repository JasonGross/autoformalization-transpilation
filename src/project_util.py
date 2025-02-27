import contextlib
import os
import re
import datetime
import tempfile
from collections import OrderedDict
from copy import deepcopy
from dataclasses import dataclass, field
from pathlib import Path
from subprocess import CompletedProcess
from typing import Any, Callable, Iterator, Literal, Self, TypeVar, cast, overload
import base64

from utils import logging, run_cmd
from utils.memoshelve import cache, hash_as_tuples

full_repr: bool = False
full_repr_threshold: int = 100


@dataclass
class File:
    # we would like to use str | bytes, but inspect wants its store to be utf-8 only
    _contents: str
    contents_is_bytes: bool = False

    def __init__(self, contents: str | bytes):
        super().__init__()
        if isinstance(contents, str):
            self._contents = contents
            self.contents_is_bytes = False
        else:
            self._contents = base64.b64encode(contents).decode("utf-8")
            self.contents_is_bytes = True

    def __hash__(self) -> int:
        return hash(self.contents)

    @property
    def contents(self) -> str | bytes:
        if self.contents_is_bytes:
            return base64.b64decode(self._contents)
        else:
            return self._contents

    def __str__(self) -> str:
        contents = self.contents
        if isinstance(contents, str):
            return contents
        if len(contents) <= 100:
            return str(contents)
        begin, end = self.contents[:10], self.contents[-10:]
        return f"{begin}...{end}"

    def __repr__(self, full: bool | None = False) -> str:
        full = full if full is not None else full_repr
        if full or len(self.contents) <= full_repr_threshold:
            return f"{self.__class__.__name__}({self.contents!r})"
        else:
            return f"{self.__class__.__name__}({self.contents[:full_repr_threshold//2]}...(hash={hash(self.contents)})...{self.contents[-full_repr_threshold//2:]})"

    def write(self, filepath: str | Path, *, mod_time: int | float | None = None) -> None:
        logging.debug(
            f"Writing {self.__class__.__name__} to {filepath}\nContents:\n{self}"
        )
        Path(filepath).parent.mkdir(parents=True, exist_ok=True)
        if isinstance(self.contents, bytes):
            Path(filepath).write_bytes(self.contents)
        else:
            assert isinstance(self.contents, str), type(self.contents)
            Path(filepath).write_text(self.contents)
        if mod_time is not None:
            os.utime(filepath, (mod_time, mod_time))

    @classmethod
    def read_text(cls, filepath: str | Path):
        return cls(Path(filepath).read_text())

    @classmethod
    def read_bytes(cls, filepath: str | Path):
        return cls(Path(filepath).read_bytes())

    @classmethod
    def read(cls, filepath: str | Path):
        try:
            contents = Path(filepath).read_text()
        except UnicodeDecodeError:
            contents = Path(filepath).read_bytes()
        return cls(contents)


class LeanFile(File):
    pass


class CoqFile(File):
    pass


class ExportFile(File):
    pass


@dataclass
class Project:
    # See this comment (https://github.com/JasonGross/autoformalization/pull/27#discussion_r1942030347) by Jason for a suggestion of structure here
    files: OrderedDict[str, File] = field(default_factory=OrderedDict)

    def __hash__(self) -> int:
        return hash(tuple(self.files.items()))

    def write(self, directory: str | Path) -> None:
        logging.debug("Writing %s to %s", self.__class__.__name__, directory)
        directory = Path(directory)
        directory.mkdir(parents=True, exist_ok=True)
        dt_epoch = datetime.datetime.now().timestamp()
        for i, (name, file) in reversed(list(enumerate(reversed(self.files.items())))):
            file.write(directory / name, mod_time=dt_epoch - i)

    def reread(self: Self, directory: str | Path) -> None:
        directory = Path(directory)
        self.files = OrderedDict()
        for file in sorted(directory.rglob("*"), key=lambda f: f.stat().st_mtime_ns):
            if file.is_file():
                relative_path = file.relative_to(directory)
                self.files[str(relative_path)] = File.read(file)

    @classmethod
    def read(cls, directory: str | Path):
        result = cls()
        result.reread(directory)
        return result

    def keys(self):
        return self.files.keys()

    def items(self):
        return self.files.items()

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}(files={self.files!r})"

    def __str__(self) -> str:
        return f"{self.__class__.__name__}({', '.join(self.files.keys())})"

    def format(self):
        result = []
        for name, file in self.files.items():
            result.append(f"File: {name}\n```\n{file}\n```\n")
        return "\n".join(result)

    def __iter__(self) -> Iterator[str]:
        return iter(self.files)

    def get(self, name: str, default: File | None = None) -> File | None:
        return self.files.get(name, default)

    def __getitem__(self, name: str):
        return self.files[name]

    def __contains__(self, name: str) -> bool:
        return name in self.files

    def __setitem__(self, name: str, file: File | None | str | bytes = None) -> None:
        if file is None:
            file = self.files[name]
        if name in self.files:
            del self.files[name]
        if not isinstance(file, File):
            file = File(file)
        self.files[name] = file

    def update(self: Self, other: Self | dict[str, File | bytes | str]) -> None:
        for name, file in other.items():
            self[name] = file

    def __ior__(self: Self, other: Self | dict[str, File | bytes | str]) -> Self:
        self.update(other)
        return self

    def __or__(self: Self, other: Self | dict[str, File | bytes | str]) -> Self:
        result = self.copy()
        result |= other
        return result

    def __delitem__(self, name: str):
        del self.files[name]

    def copy(self: Self) -> Self:
        return self.__class__(self.files.copy())

    @contextlib.contextmanager
    def tempdir(self, read_on_exit: bool = True, read_on_error: bool = True):
        with tempfile.TemporaryDirectory(delete=True) as tempdir:
            self.write(tempdir)
            with contextlib.chdir(tempdir):
                try:
                    yield Path(".").absolute()
                except Exception as e:
                    if read_on_error and read_on_exit:
                        self.reread(".")
                    raise e
                if read_on_exit:
                    self.reread(".")

    def irun_cmd(self: Self, *args, **kwargs) -> CompletedProcess[str]:
        with self.tempdir():
            return run_cmd(*args, **kwargs)

    @cache(get_hash=hash_as_tuples, copy=deepcopy)
    def run_cmd(self: Self, *args, **kwargs) -> tuple[CompletedProcess[str], Self]:
        project = self.copy()
        result = project.irun_cmd(*args, **kwargs)
        return result, project

    def make(
        self: Self, *targets: str, check: bool = False
    ) -> tuple[CompletedProcess[str], Self]:
        return self.run_cmd(["make", *targets], shell=False, check=check)

    def clean(self):
        return self.make("clean")


class LeanProject(Project):
    pass


class CoqProject(Project):
    pass


@dataclass
class Identifier:
    name: str

    def __str__(self) -> str:
        return self.name

    def __hash__(self) -> int:
        return hash(self.name)


class LeanIdentifier(Identifier):
    pass


class CoqIdentifier(Identifier):
    pass


@dataclass
class IsoError:
    orig_source: str
    orig_target: str


@dataclass
class MissingTypeIso(IsoError):
    source: str
    target: str


@dataclass
class MissingImport(IsoError):
    import_str: str


@dataclass
class GenericIsoError(IsoError):
    unknown_lhs: list[str]
    unknown_rhs: list[str]
    prefix: str
    ngoals: int
    goals: str

    def __str__(self):
        return f"GenericIsoError(orig_source={self.orig_source}, orig_target={self.orig_target}, unknown_lhs={self.unknown_lhs}, unknown_rhs={self.unknown_rhs}, unknown_lhs_filtered={self.unknown_lhs_filtered}, unknown_rhs_filtered={self.unknown_rhs_filtered}, ngoals={self.ngoals},\n prefix='''{self.prefix}''',\n goals='''{self.goals}''')"


@dataclass
class DisorderedConstr(IsoError):
    hint: str
    prefix: str
    extra_hints: list[str]
    suffix: str


# class IsoErrorKind(StrEnum, IsoError):
#     DISORDERED_CONSTR = "disordered_constr"
#     MAYBE_MISSING_STMNT_ISO = "maybe_missing_stmnt_iso"
#     OTHER_ISO_ISSUE = "other_iso_issue"


IDT = TypeVar(
    "IDT", Identifier, CoqIdentifier, LeanIdentifier, str, CoqIdentifier | str
)


def sigil(s: IDT) -> IDT:
    if isinstance(s, str):
        return "$" + s
    return s.__class__(sigil(str(s)))


def desigil(s: IDT, prefix: str = "") -> IDT:
    if isinstance(s, str):
        if s[0] == "$":
            return prefix + s[1:]
        return s
    return s.__class__(desigil(str(s), prefix))


def coq_identifiers_of_list(
    coq_list: list[str],
    sigil: Literal[False] | Callable[[CoqIdentifier], CoqIdentifier] = sigil,
) -> list[CoqIdentifier]:
    result = [CoqIdentifier(s) for s in coq_list]
    if sigil:
        result = [sigil(coq_id) for coq_id in result]
    return result


def extract_coq_identifiers_str(
    coq: CoqFile | None | str,
    sigil: Literal[False] | Callable[[str], str] = sigil,
    *,
    default_definition_pairs: list[tuple[CoqIdentifier, Any]] = [],
) -> list[str]:
    # Extract identifiers from Coq statements
    if not coq:
        # TODO: Have the actual identifier pairs
        result = [str(coq_id) for coq_id, _ in default_definition_pairs]
        if not sigil:
            result = [desigil(coq_id) for coq_id in result]
        return result
    else:
        coq_str = coq.contents if isinstance(coq, CoqFile) else coq
        # not perfect, but best-effort
        assert isinstance(coq_str, str), "CoqFile contents must be a string"
        result: list[str] = re.findall(
            r"(?:Theorem|Lemma|Fact|Remark|Corollary|Proposition|Property|Definition|Example|SubClass|Inductive|CoInductive|Variant|Record|Structure|Class|Fixpoint|CoFixpoint)\s+([^\s\(:]+)",
            coq_str,
            flags=re.DOTALL,
        )
        if sigil:
            result = [sigil(coq_id) for coq_id in result]
        return result


def extract_coq_identifiers(
    coq: CoqFile | None | str,
    sigil: Literal[False] | Callable[[str], str] = sigil,
    *,
    default_definition_pairs: list[tuple[CoqIdentifier, Any]] = [],
) -> list[CoqIdentifier]:
    return [CoqIdentifier(coq_id) for coq_id in extract_coq_identifiers_str(coq, sigil, default_definition_pairs=default_definition_pairs)]
