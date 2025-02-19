from dataclasses import dataclass, field
from pathlib import Path
from collections import OrderedDict
import contextlib
import tempfile
from typing import Self

from utils import logging, run_cmd
from utils.memoshelve import cache


@dataclass
class File:
    contents: str | bytes

    def __str__(self) -> str:
        return str(self.contents)

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}({self.contents!r})"

    def write(self, filepath: str | Path) -> None:
        logging.debug(
            f"Writing {self.__class__.__name__} to {filepath}\nContents:\n{self.contents}"
        )
        Path(filepath).parent.mkdir(parents=True, exist_ok=True)
        if isinstance(self.contents, bytes):
            Path(filepath).write_bytes(self.contents)
        else:
            Path(filepath).write_text(self.contents)

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


@dataclass
class LeanFile(File):
    pass


@dataclass
class CoqFile(File):
    pass


@dataclass
class ExportFile(File):
    pass


@dataclass
class Project:
    # See this comment (https://github.com/JasonGross/autoformalization/pull/27#discussion_r1942030347) by Jason for a suggestion of structure here
    files: OrderedDict[str, File] = field(default_factory=OrderedDict)

    def write(self, directory: str | Path) -> None:
        logging.debug("Writing %s to %s", self.__class__.__name__, directory)
        directory = Path(directory)
        directory.mkdir(parents=True, exist_ok=True)
        for name, file in self.files.items():
            file.write(directory / name)

    @classmethod
    def read(cls, directory: str | Path):
        directory = Path(directory)
        files = OrderedDict()
        for file in sorted(directory.iterdir(), key=lambda f: f.stat().st_mtime_ns):
            if file.is_file():
                relative_path = file.relative_to(directory)
                files[str(relative_path)] = File.read(file)
        return cls(files)

    def keys(self):
        return self.files.keys()

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}(files={self.files!r})"

    def __str__(self) -> str:
        return f"{self.__class__.__name__}({', '.join(self.files.keys())})"

    def format(self):
        result = []
        for name, file in self.files.items():
            result.append(f"File: {name}\n```\n{file.contents}\n```\n")
        return "\n".join(result)

    def __iter__(self):
        return iter(self.files)

    def __getitem__(self, name: str):
        return self.files[name]

    def __setitem__(self, name: str, file: File | None = None) -> None:
        if file is None:
            file = self.files[name]
        if name in self.files:
            del self.files[name]
        self.files[name] = file

    def __delitem__(self, name: str):
        del self.files[name]

    def copy(self: Self) -> Self:
        return self.__class__(self.files.copy())

    @contextlib.contextmanager
    def tempdir(self):
        with tempfile.TemporaryDirectory(delete=True) as tempdir:
            self.write(tempdir)
            with contextlib.chdir(tempdir):
                yield Path(".").absolute()

    @cache()
    def make(self: Self, *targets: str) -> Self:
        with self.tempdir():
            run_cmd(["make", *targets], shell=False, check=False)
            return self.__class__.read(".")

    def clean(self):
        return self.make("clean")


@dataclass
class LeanProject(Project):
    pass


@dataclass
class CoqProject(Project):
    pass


@dataclass
class Identifier:
    name: str

    def __str__(self) -> str:
        return self.name


@dataclass
class LeanIdentifier(Identifier):
    pass


@dataclass
class CoqIdentifier(Identifier):
    pass
