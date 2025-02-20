import shutil
import subprocess
import tempfile
from pathlib import Path

from inspect_ai.tool import tool

from run_itp import run_coq_str, run_lean_str


@tool
def coq_run_tool(
    project_root: str = "",
    extra_files: dict[str, bytes] = {},
    setup_cmds: list = [],
    coq_flags: list[str] = [],
):
    temp_dir = tempfile.mkdtemp()
    if project_root:
        shutil.copytree(project_root, temp_dir, dirs_exist_ok=True)
    for extra_filename, content in extra_files.items():
        file_path = Path(temp_dir) / extra_filename
        file_path.parent.mkdir(parents=True, exist_ok=True)
        file_path.write_bytes(content)

    for cmd in setup_cmds:
        subprocess.run(cmd, shell=True, cwd=temp_dir, check=True)

    async def run(coq_code: str):
        """
        Runs the given Coq code in the project environment. It then returns a dictionary containing the status, stdout and stderr given from the execution of the code.

        Args:
            coq_code (str): Coq code to be run

        Returns:
            Dict: Compilation status (0 if it worked, 1 if there was an error), stdout (str), and stderr (str)
        """
        result = run_coq_str(coq_code, temp_dir, {}, [], coq_flags)
        return result, coq_code

    return run


@tool
def lean_run_tool(
    project_root: str = "",
    extra_files: dict[str, bytes] = {},
    setup_cmds: list = [],
    lean_flags: list[str] = [],
):
    temp_dir = tempfile.mkdtemp()
    if project_root:
        shutil.copytree(project_root, temp_dir, dirs_exist_ok=True)
    for extra_filename, content in extra_files.items():
        file_path = Path(temp_dir) / extra_filename
        file_path.parent.mkdir(parents=True, exist_ok=True)
        file_path.write_bytes(content)

    for cmd in setup_cmds:
        subprocess.run(cmd, shell=True, cwd=temp_dir, check=True)

    async def run(lean_code: str):
        """
        Runs the given Lean code in the project environment. It then returns a dictionary containing the status, stdout and stderr given from the execution of the code.

        Args:
            lean_code (str): Lean code to be run

        Returns:
            Dict: Compilation status (0 if it worked, 1 if there was an error), stdout (str), and stderr (str)
        """
        result = run_lean_str(lean_code, temp_dir, {}, [], lean_flags)
        return result

    return run
