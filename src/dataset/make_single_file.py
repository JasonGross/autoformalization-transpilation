#!/usr/bin/env python
import argparse
import pathlib
import shutil
import subprocess
import os
import time
from contextlib import contextmanager
import logging

logger = logging.getLogger(__name__)


@contextmanager
def with_time(description=None):
    start_time = time.time()
    try:
        if description:
            logger.info(f"Starting: {description}")
        yield
    finally:
        end_time = time.time()
        elapsed_time = end_time - start_time
        if description:
            logger.info(f"Finished: {description}")
        logger.info(f"Elapsed time: {elapsed_time:.2f} seconds")


def main():
    parser = argparse.ArgumentParser(
        description="Process Coq files and generate a Makefile."
    )
    parser.add_argument("files", nargs="+", help="List of files to process")
    parser.add_argument("-o", "--output_dir", required=True, help="Output directory")
    args = parser.parse_args()

    files = [pathlib.Path(f) for f in args.files]
    output_dir = pathlib.Path(args.output_dir)

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
    shared_parent = coqproject_file.parent  # pathlib.Path(os.path.commonpath(files))

    known_files = {k: [] for k in set(bindings.values())}
    unknown_files = []

    # Copy files to output directory maintaining structure
    for file in files:
        relative_path = file.relative_to(shared_parent)
        destination = output_dir / relative_path
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(file, destination)
        for dirname, libname in bindings.items():
            dirname = pathlib.Path(dirname)
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
    with with_time("make"):
        subprocess.run(["make"], cwd=output_dir, check=True)

    with with_time("inlining imports"):
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
        )
    with with_time("single file build"):
        subprocess.run(
            ["coqc", "-q", f"Everything{lib_name}WithComments.v"],
            cwd=output_dir,
            check=False,
        )

    with with_time("inlining imports more robust admitted"):
        subprocess.run(
            [
                "coq-bug-minimizer",
                "-f",
                "_CoqProject",
                "Everything.v",
                f"Everything{lib_name}.v",
                "--no-error",
                "--admit-opaque",
            ],
            cwd=output_dir,
            check=True,
        )

    with with_time("inlining imports more robust"):
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
        )


if __name__ == "__main__":
    main()
