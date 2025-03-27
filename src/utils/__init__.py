import logging
import subprocess
import sys
from pathlib import Path
from typing import Iterable, Optional, Sequence, TypeVar

# Simple logging setup
logging.basicConfig(
    level=logging.DEBUG,
    format="%(asctime)s - %(levelname)s - %(message)s",
    filename="autoformalization.log",
)

# Add console handler with INFO level
console_handler = logging.StreamHandler(sys.stdout)
console_handler.setLevel(logging.INFO)  # Only show INFO and higher
console_handler.setFormatter(logging.Formatter("%(levelname)s - %(message)s"))
logging.getLogger().addHandler(console_handler)


def run_cmd(cmd: str | list[str], shell=True, check=True, streaming=False):
    """Run subprocess command and log it"""
    assert isinstance(cmd, str) or not shell, "cmd must be a string if shell=True"
    logging.debug(f"Running: {cmd}")
    result = subprocess.run(
        cmd, shell=shell, check=check, text=True, capture_output=not streaming
    )
    logging.debug(f"Output: {result.stdout}")
    if result.stderr:
        logging.debug(f"Stderr: {result.stderr}")
    return result


def backup(filename: str | Path, ext: str = ".bak") -> Optional[Path]:
    filename = Path(filename)
    assert ext != ""
    backup_name = filename.with_suffix(filename.suffix + ext)
    if filename.exists():
        if backup_name.exists():
            backup(backup_name, ext=ext)
            assert not backup_name.exists()
            filename.rename(backup_name)
            return backup_name
    return None
