#!/usr/bin/env python
import argparse
from pathlib import Path
import shutil
import subprocess
import time
from contextlib import contextmanager
import logging
from typing import Sequence

logger = logging.getLogger(__name__)


@contextmanager
def with_time(description=None, quiet: bool = False):
    start_time = time.time()
    try:
        if description and not quiet:
            logger.info(f"Starting: {description}")
        yield
    finally:
        end_time = time.time()
        elapsed_time = end_time - start_time
        if description and not quiet:
            logger.info(f"Finished: {description}")
        if not quiet:
            logger.info(f"Elapsed time: {elapsed_time:.2f} seconds")


def process(*files: Path | str, output_dir: Path | str, quiet: bool = False):
    files = tuple(Path(f) for f in files)
    output_dir = Path(output_dir)

    # Check file names
    for file in files:
        if not (file.name == "_CoqProject" or file.suffix == ".v"):
            raise ValueError(f"Invalid file: {file}. Must be _CoqProject or .v files.")

    # Check for Everything.v
    for file in files:
        if file.name == "Everything.v":
            raise ValueError("File Everything.v is not allowed.")

    # Parse _CoqProject
    coqproject_file = next((f for f in files if f.name == "_CoqProject"), None)
    if not coqproject_file:
        raise ValueError("_CoqProject file is required.")

    with coqproject_file.open() as f:
        lines = f.readlines()

    lib_name = None
    bindings = {}
    for line in lines:
        if line.startswith("-Q ") or line.startswith("-R "):
            parts = line.split()
            assert len(parts) == 3, parts
            bindings[parts[1]] = parts[2]

    if not bindings:
        raise ValueError("Could not find -Q . LIB or -R . LIB in _CoqProject.")
    if len(bindings) > 1:
        raise ValueError("Multiple -Q or -R directives are not yet supported.")

    lib_name = list(bindings.values())[0]

    # Find shared parent directory
    shared_parent = coqproject_file.parent  # Path(os.path.commonpath(files))

    known_files = {k: [] for k in set(bindings.values())}
    unknown_files = []

    # Copy files to output directory maintaining structure
    for file in files:
        relative_path = file.relative_to(shared_parent)
        destination = output_dir / relative_path
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(file, destination)
        for dirname, libname in bindings.items():
            dirname = Path(dirname)
            if relative_path.is_relative_to(dirname):
                known_files[libname].append(relative_path.relative_to(dirname))
                break
        else:
            unknown_files.append(relative_path)

    # Create Everything.v
    everything_v_path = output_dir / "Everything.v"
    with everything_v_path.open("w") as f:
        for file in unknown_files:
            if file.suffix == ".v":
                module_name = str(
                    file.relative_to(shared_parent).with_suffix("")
                ).replace("/", ".")
                f.write(f"Require {module_name}.\n")
        for libname, libfiles in known_files.items():
            for file in libfiles:
                if file.suffix == ".v":
                    module_name = str(file.with_suffix("")).replace("/", ".")
                    if libname:
                        module_name = f"{libname}.{module_name}"
                    f.write(f"Require {module_name}.\n")

    # Run coq_makefile
    v_files = [str(f.relative_to(shared_parent)) for f in files if f.suffix == ".v"] + [
        "Everything.v"
    ]
    subprocess.run(
        ["coq_makefile", "-f", "_CoqProject", "-o", "Makefile"] + v_files,
        cwd=output_dir,
        check=True,
    )

    (output_dir / ".gitignore").write_text(
        f"""*
!Everything{lib_name}*.v
!.gitignore
"""
    )

    # Run make
    with with_time("make", quiet=quiet):
        subprocess.run(
            ["make"],
            cwd=output_dir,
            check=True,
            stdout=subprocess.DEVNULL if quiet else None,
        )

    with with_time("inlining imports", quiet=quiet):
        subprocess.run(
            [
                "coq-import-inliner",
                "-f",
                "_CoqProject",
                "Everything.v",
                f"Everything{lib_name}WithComments.v",
            ],
            cwd=output_dir,
            check=True,
            stdout=subprocess.DEVNULL if quiet else None,
        )
    with with_time("single file build", quiet=quiet):
        subprocess.run(
            ["coqc", "-q", f"Everything{lib_name}WithComments.v"],
            cwd=output_dir,
            check=False,
            stdout=subprocess.DEVNULL if quiet else None,
            stderr=subprocess.DEVNULL if quiet else None,
        )

    with with_time("inlining imports more robust admitted", quiet=quiet):
        subprocess.run(
            [
                "coq-bug-minimizer",
                "-f",
                "_CoqProject",
                "Everything.v",
                f"Everything{lib_name}Admitted.v",
                "--no-error",
                "--admit-opaque",
            ],
            cwd=output_dir,
            check=True,
            stdout=subprocess.DEVNULL if quiet else None
        )

    with with_time("inlining imports more robust", quiet=quiet):
        subprocess.run(
            [
                "coq-bug-minimizer",
                "-f",
                "_CoqProject",
                "Everything.v",
                f"Everything{lib_name}.v",
                "--no-error",
            ],
            cwd=output_dir,
            check=True,
            stdout=subprocess.DEVNULL if quiet else None
        )


def main(argv: Sequence[str] | None = None):
    parser = argparse.ArgumentParser(
        description="Process Coq files and generate a Makefile."
    )
    parser.add_argument("files", nargs="+", help="List of files to process")
    parser.add_argument("-o", "--output_dir", required=True, help="Output directory")
    parser.add_argument(
        "-q",
        "--quiet",
        action="store_true",
        default=False,
        help="Suppress timing information and stdout",
    )
    args = parser.parse_args(argv)

    return process(*args.files, output_dir=args.output_dir, quiet=args.quiet)


if __name__ == "__main__":
    main()
