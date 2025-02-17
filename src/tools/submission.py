from inspect_ai.tool import tool
from inspect_ai.util import Store
import inspect_ai.util
import tempfile
import subprocess
import shutil
import asyncio
from pathlib import Path

def store_result(result):
    cur_index = inspect_ai.util.store().get("cur_index", 0)
    inspect_ai.util.store().set(f"result_{cur_index}", result)
    inspect_ai.util.store().set("cur_index", cur_index + 1)

@tool
def coq_submit_tool (
    project_root: str = "",
    extra_files: dict[str, bytes] = {},
    setup_cmds: list = [],
    coq_flags: list[str] = [],
    definitions: list[str] = [],
    interface_file_contents: str = "",
    file_name: str = "submission.v",
    white_list: list[str] = ['Closed under the global context']
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

    interface_file = Path(temp_dir) / "Interface.v"
    interface_file.write_text(interface_file_contents)

    #assuming directory name is project_name
    project_name = Path(temp_dir).name
    checker_file = Path(temp_dir) / "Checker.v"
    checker_content = [
        f"From {project_name} Require Import Interface {Path(file_name).stem}.",
        f"Module DoesItCheck <: Interface.Interface := {Path(file_name).stem}.",
        '\n'.join(f"Print Assumptions DoesItCheck.{name}." for name in definitions)
    ]
    checker_file.write_text('\n'.join(checker_content))
    #remove
    # print(checker_file.read_text())

    async def submit(coq_code: str):
        """
        Submits the given Coq code in the project environment. Code needs to submitted using this tool to be considered for evaluation. The tool ensures that all definitions from the input file have been written in the submission and there are no assumptions in the given code. It then returns a dictionary containing the status, stdout, stderr, submission status and any assumptions given from the execution of the code. 

        Args:
            coq_code (str): Coq code to be run

        Returns:
            Dict: Compilation status (0 if it worked, 1 if there was an error), stdout (str), stderr (str), submission status (bool: true if the submission is correct, false otherwise) and assumptions (list[str])
        """
        file_path = Path(temp_dir) / file_name
        file_path.write_text(coq_code)
        command = f"coqc -q -Q . {project_name} Interface.v && coqc -q -Q . {project_name} {file_name} && coqc -q -Q . {project_name} Checker.v"
        # print(command)
        process = subprocess.run(command, shell=True, text=True, cwd=temp_dir, capture_output=True)
        result = {"status": process.returncode, "stdout": process.stdout, "stderr": process.stderr,"submission_status": False, "assumptions": []}
        if process.returncode == 0:
            assumptions = process.stdout.strip().split('\n')
            # print(assumptions)
            result["assumptions"] = assumptions
            if all(assumption in white_list for assumption in assumptions):
                result["submission_status"] = True
        store_result(result)
        return result
    return submit


sample_interface = \
"""
Module Type Interface.

From Coq Require Import Arith.

Theorem plus_0_r : forall n : nat, n + 0 = n.
Proof.
Admitted.

(* Now we can prove plus_comm *)
Theorem plus_comm : forall a b : nat, a + b = b + a.
Proof.
Admitted.
End Interface.
"""

my_submission = \
"""
(* First prove the helper lemma plus_0_r *)
Theorem plus_0_r : forall n : nat, n + 0 = n.
Proof.
    intros n.
    induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite IHn'. reflexivity.
Qed.

(* Now we can prove plus_comm *)
Theorem plus_comm : forall a b : nat, a + b = b + a.
Proof.
    intros a b.
    induction a as [| a' IHa'].
    - simpl. rewrite plus_0_r. reflexivity.
    - simpl. rewrite IHa'. rewrite plus_n_Sm. reflexivity.
Qed.
"""

sample_definitions = ["plus_0_r", "plus_comm"]

if __name__ == "__main__":
    # Example usage
    submit = coq_submit_tool(definitions=sample_definitions, interface_file_contents=sample_interface)
    result = asyncio.run(submit(my_submission))
    print(result)
    pass