import glob
import os
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Any, Dict


def run_coq_file(
    filename: str,
    project_root: str = "",
    extra_files: dict[str, bytes] | None = None,
    setup_cmds: list[str] | None = None,
    coq_flags: list[str] | None = None,
) -> Dict[str, Any]:
    """Runs a Coq file and returns compilation status"""
    extra_files = extra_files or {}
    setup_cmds = setup_cmds or []
    coq_flags = coq_flags or []
    result = {"status": 0, "stdout": "", "stderr": ""}
    with tempfile.TemporaryDirectory() as temp_dir:
        try:
            print(project_root)
            if project_root:
                shutil.copytree(project_root, temp_dir, dirs_exist_ok=True)
            for extra_filename, content in extra_files.items():
                file_path = Path(temp_dir) / extra_filename
                file_path.parent.mkdir(parents=True, exist_ok=True)
                file_path.write_bytes(content)
            for cmd in setup_cmds:
                subprocess.run(cmd, shell=True, check=True, cwd=temp_dir)
            temp_filename = os.path.join(temp_dir, os.path.basename(filename))

            coq_cmd = ["coqc", "-q"] + coq_flags + [temp_filename]
            # Hacky way, maybe we can include a flag?
            if "Makefile" in os.listdir(temp_dir) and "_CoqProject" in os.listdir(
                temp_dir
            ):
                coq_cmd = ["make"] + coq_flags
            process = subprocess.run(
                coq_cmd, capture_output=True, text=True, cwd=temp_dir
            )

            result["status"] = process.returncode
            result["stdout"] = process.stdout
            result["stderr"] = process.stderr
        except subprocess.CalledProcessError as e:
            result["status"] = 1
            result["stderr"] = e.stderr
            result["stdout"] = e.stdout
    return result


def run_coq_str(
    coq_code: str,
    project_root: str = ".",
    extra_files: dict[str, bytes] | None = None,
    setup_cmds: list[str] | None = None,
    coq_flags: list[str] | None = None,
) -> Dict[str, Any]:
    """Runs Coq code from a string and returns compilation status"""
    extra_files = extra_files or {}
    setup_cmds = setup_cmds or []
    coq_flags = coq_flags or []
    with tempfile.NamedTemporaryFile(
        prefix="coq_temp_", suffix=".v", dir=project_root
    ) as temp_file:
        temp_file.write(coq_code.encode("utf-8"))
        temp_file.flush()
        temp_filename = temp_file.name
        return run_coq_file(
            filename=temp_filename,
            project_root=project_root,
            extra_files=extra_files,
            setup_cmds=setup_cmds,
            coq_flags=coq_flags,
        )


def run_lean_file(
    filename: str,
    project_root: str = ".",
    extra_files: dict[str, bytes] | None = None,
    setup_cmds: list | None = None,
    lean_flags: list[str] | None = None,
) -> Dict[str, Any]:
    """Runs a Lean file and returns compilation status"""
    extra_files = extra_files or {}
    setup_cmds = setup_cmds or []
    lean_flags = lean_flags or []
    result = {"status": 0, "stdout": "", "stderr": ""}
    with tempfile.TemporaryDirectory() as temp_dir:
        try:
            shutil.copytree(project_root, temp_dir, dirs_exist_ok=True)
            for extra_filename, content in extra_files.items():
                file_path = Path(temp_dir) / extra_filename
                file_path.parent.mkdir(parents=True, exist_ok=True)
                file_path.write_bytes(content)
            for cmd in setup_cmds:
                subprocess.run(cmd, shell=True, check=True, cwd=temp_dir)
            temp_filename = os.path.join(temp_dir, os.path.basename(filename))
            shutil.copy(os.path.join(project_root, filename), temp_filename)

            lean_cmd = ["lean"] + lean_flags + [temp_filename]
            process = subprocess.run(
                lean_cmd, capture_output=True, text=True, cwd=temp_dir
            )
            result["status"] = process.returncode
            result["stdout"] = "\n".join(
                line for line in process.stdout.splitlines() if "error:" not in line
            )
            result["stderr"] = "\n".join(
                line for line in process.stdout.splitlines() if "error:" in line
            )
            if process.stderr:
                result["stderr"] += "\n" + process.stderr
        except subprocess.CalledProcessError as e:
            result["status"] = 1
            result["stderr"] = e.stderr
            result["stdout"] = e.stdout
    return result


def run_lean_str(
    lean_code: str,
    project_root: str = ".",
    extra_files: dict[str, bytes] | None = None,
    setup_cmds: list[str] | None = None,
    lean_flags: list[str] | None = None,
) -> Dict[str, Any]:
    """Runs Lean code from a string and returns compilation status"""
    extra_files = extra_files or {}
    setup_cmds = setup_cmds or []
    lean_flags = lean_flags or []
    with tempfile.NamedTemporaryFile(
        prefix="lean_temp_", suffix=".lean", dir=project_root
    ) as temp_file:
        temp_file.write(lean_code.encode("utf-8"))
        temp_file.flush()
        temp_filename = temp_file.name
        return run_lean_file(
            filename=temp_filename,
            project_root=project_root,
            extra_files=extra_files,
            setup_cmds=setup_cmds,
            lean_flags=lean_flags,
        )


if __name__ == "__main__":
    # Example usage
    coq_code = """
    Theorem addn0 : forall n : nat, n + 0 = n.
    Proof.
      intros n. induction n.
        - simpl. reflexivity.
      - simpl. rewrite IHn. reflexivity.
    Qed.
    """
    result = run_coq_str(coq_code=coq_code, project_root="./simple-tests")
    print(result)
    # result = run_coq_file(filename="StackMachine.v", project_root="../demo-stackmachine")
    print(result)
    # print(run_coq_file(filename="test_imp.v", project_root=".."))
    lean_code = """
    def myNat : Nat := 5
    def myNat2 : Nat := myNat + 3
    """
    result = run_lean_str(lean_code=lean_code, project_root="./simple-tests")
    print(result)
    result = run_lean_file(filename="demo.lean", project_root="../demo-stackmachine")
    print(result)
