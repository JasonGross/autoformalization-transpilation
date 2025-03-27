#!/usr/bin/env python
import argparse
import logging
import os.path
import shutil
import subprocess
import time
from contextlib import contextmanager
from pathlib import Path
from typing import Sequence

logger = logging.getLogger(__name__)


def do_backup(source: Path, target: Path):
    if target.exists():
        do_backup(target, target.with_suffix(target.suffix + ".bak"))
    source.rename(target)


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


def parse_coqproject(*files: Path):
    """Parse _CoqProject file to extract library bindings."""
    coqproject_file = next((f for f in files if f.name == "_CoqProject"), None)
    assert coqproject_file is not None, "_CoqProject file is required."

    lines = coqproject_file.read_text().splitlines()

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
    return bindings, lib_name, coqproject_file.parent


def check_file_validity(*files: Path, lib_name: str):
    """Check that files are valid (_CoqProject or .v files, no Everything*Requires.v)."""
    # Check file names
    for file in files:
        if not (file.name == "_CoqProject" or file.suffix == ".v"):
            raise ValueError(f"Invalid file: {file}. Must be _CoqProject or .v files.")

    # Ensure _CoqProject exists
    if not any(f.name == "_CoqProject" for f in files):
        raise ValueError("_CoqProject file is required.")

    for file in files:
        if file.name.startswith(f"Everything{lib_name}") and file.name.endswith(".v"):
            raise ValueError(
                f"File {file.name}(Everything{lib_name}*.v) is not allowed."
            )


def copy_if_different(source: Path, target: Path):
    if not target.exists():
        shutil.copy(source, target)
    elif source.read_bytes() != target.read_bytes():
        shutil.copy(source, target)


def copy_files_to_output(
    files: tuple[Path, ...], shared_parent: Path, output_dir: Path, bindings: dict
):
    """Copy files to output directory and categorize them."""
    known_files = {k: [] for k in set(bindings.values())}
    unknown_files = []

    for file in files:
        relative_path = file.relative_to(shared_parent)
        destination = output_dir / relative_path
        destination.parent.mkdir(parents=True, exist_ok=True)
        copy_if_different(file, destination)
        for dirname, libname in bindings.items():
            dirname = Path(dirname)
            if relative_path.is_relative_to(dirname):
                known_files[libname].append(relative_path.relative_to(dirname))
                break
        else:
            unknown_files.append(relative_path)

    return known_files, unknown_files


def create_everything_contents(
    unknown_files: list[Path], known_files: dict, shared_parent: Path
):
    """Create the contents for Everything*Requires.v file."""
    contents = []
    for file in unknown_files:
        if file.suffix == ".v":
            module_name = str(file.relative_to(shared_parent).with_suffix("")).replace(
                "/", "."
            )
            contents.append(f"Require {module_name}.\n")
    for libname, libfiles in known_files.items():
        for file in libfiles:
            if file.suffix == ".v":
                module_name = str(file.with_suffix("")).replace("/", ".")
                if libname:
                    module_name = f"{libname}.{module_name}"
                contents.append(f"Require {module_name}.\n")

    return "".join(contents)


def create_everything_file(output_dir: Path, lib_name: str, contents: str):
    """Create the Everything*Requires.v file."""
    everything_v_path = output_dir / f"Everything{lib_name}Requires.v"
    everything_v_path.write_text(contents)
    return everything_v_path


def create_makefile(
    output_dir: Path, files: tuple[Path, ...], shared_parent: Path, lib_name: str
):
    """Create Makefile using coq_makefile."""
    v_files = [str(f.relative_to(shared_parent)) for f in files if f.suffix == ".v"] + [
        f"Everything{lib_name}Requires.v"
    ]
    subprocess.run(
        ["coq_makefile", "-f", "_CoqProject", "-o", "Makefile"] + v_files,
        cwd=output_dir,
        check=True,
    )


def update_gitignore(output_dir: Path, lib_name: str):
    """Update .gitignore file."""
    (output_dir / ".gitignore").write_text(
        f"""*
!Everything{lib_name}*.v
Everything{lib_name}Requires.v
Everything{lib_name}*PartialProgress.v
!.gitignore
"""
    )


def run_make(output_dir: Path, quiet: bool):
    """Run make in the output directory."""
    with with_time("make", quiet=quiet):
        subprocess.run(
            ["make"],
            cwd=output_dir,
            check=True,
            stdout=subprocess.DEVNULL if quiet else None,
        )


def inline_imports_with_comments(output_dir: Path, lib_name: str, *, quiet: bool):
    """Inline imports with comments preserved."""
    with with_time("inlining imports", quiet=quiet):
        subprocess.run(
            [
                "coq-import-inliner",
                "-f",
                "_CoqProject",
                f"Everything{lib_name}Requires.v",
                f"Everything{lib_name}WithComments.v",
            ],
            cwd=output_dir,
            check=True,
            stdout=subprocess.DEVNULL if quiet else None,
        )


def build_single_file(output_dir: Path, lib_name: str, *, quiet: bool):
    """Build the single file version."""
    with with_time("single file build", quiet=quiet):
        subprocess.run(
            ["coqc", "-q", f"Everything{lib_name}WithComments.v"],
            cwd=output_dir,
            check=False,
            stdout=subprocess.DEVNULL if quiet else None,
            stderr=subprocess.DEVNULL if quiet else None,
        )


def run_bug_minimizer(
    description: str,
    output_dir: Path,
    input_fname: str,
    output_fname: str,
    *extra_args: str,
    quiet: bool,
    yes: bool,
    resume: bool,
    backup: bool,
):
    """Run bug minimizer."""
    with with_time(description, quiet=quiet):
        args = [
            "coq-bug-minimizer",
            "-f",
            "_CoqProject",
            *extra_args,
        ]
        if yes:
            args.append("-y")
        if resume and (output_dir / output_fname).exists():
            logger.info(f"Resuming from {output_fname}")
            output_stem, output_suffix = os.path.splitext(output_fname)
            input_fname = output_stem + "PartialProgress" + output_suffix
            if backup:
                do_backup(output_dir / output_fname, output_dir / input_fname)
            else:
                if os.path.exists(input_fname):
                    os.remove(input_fname)
                os.rename(output_dir / output_fname, output_dir / input_fname)
        args.extend([input_fname, output_fname])
        return subprocess.run(
            args,
            cwd=output_dir,
            check=True,
            stdout=subprocess.DEVNULL if quiet else None,
        )


def inline_imports_admitted(
    output_dir: Path,
    lib_name: str,
    *,
    quiet: bool,
    yes: bool,
    resume: bool,
    backup: bool,
):
    """Inline imports with admitted proofs."""
    run_bug_minimizer(
        "inlining imports more robust admitted",
        output_dir,
        f"Everything{lib_name}Requires.v",
        f"Everything{lib_name}Admitted.v",
        "--no-error",
        "--admit-opaque",
        quiet=quiet,
        yes=yes,
        resume=resume,
        backup=backup,
    )


def inline_imports_robust(
    output_dir: Path,
    lib_name: str,
    *,
    quiet: bool,
    yes: bool,
    resume: bool,
    backup: bool,
):
    """Inline imports with robust handling."""
    run_bug_minimizer(
        "inlining imports more robust",
        output_dir,
        f"Everything{lib_name}Requires.v",
        f"Everything{lib_name}.v",
        "--no-error",
        quiet=quiet,
        yes=yes,
        resume=resume,
        backup=backup,
    )


def process(
    *files: Path | str,
    output_dir: Path | str,
    quiet: bool = False,
    robust: bool = False,
    resume: bool = False,
    yes: bool = False,
    backup: bool = True,
):
    files = tuple(Path(f) for f in files)
    output_dir = Path(output_dir)

    # Parse _CoqProject
    bindings, lib_name, shared_parent = parse_coqproject(*files)
    check_file_validity(*files, lib_name=lib_name)

    # Copy files to output directory
    known_files, unknown_files = copy_files_to_output(
        files, shared_parent, output_dir, bindings
    )

    everything_contents = create_everything_contents(
        unknown_files, known_files, shared_parent
    )
    create_everything_file(output_dir, lib_name, everything_contents)
    create_makefile(output_dir, files, shared_parent, lib_name)
    update_gitignore(output_dir, lib_name)

    run_make(output_dir, quiet)

    # inline_imports_with_comments(output_dir, lib_name, quiet=quiet)
    # build_single_file(output_dir, lib_name, quiet=quiet)
    # input(f"inline_imports_admitted({output_dir}, {lib_name}, quiet={quiet}, yes={yes}, resume={resume}, backup={backup})")
    inline_imports_admitted(
        output_dir, lib_name, quiet=quiet, yes=yes, resume=resume, backup=backup
    )
    if robust:
        inline_imports_robust(
            output_dir, lib_name, quiet=quiet, yes=yes, resume=resume, backup=backup
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
    parser.add_argument(
        "--resume",
        action=argparse.BooleanOptionalAction,
        default=False,
        help="Resume the build",
    )
    parser.add_argument(
        "-y",
        "--yes",
        action="store_true",
        default=False,
        help="Skip confirmation prompts",
    )
    parser.add_argument(
        "--robust",
        action="store_true",
        default=False,
        help="Include the inline_imports_robust pass",
    )
    parser.add_argument(
        "--backup",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="Backup the original files",
    )
    args = parser.parse_args(argv)

    return process(
        *args.files,
        output_dir=args.output_dir,
        quiet=args.quiet,
        robust=args.robust,
        resume=args.resume,
        yes=args.yes,
        backup=args.backup,
    )


if __name__ == "__main__":
    main()
