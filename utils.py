import subprocess
import logging

# Simple logging setup
logging.basicConfig(
    level=logging.DEBUG,
    format="%(asctime)s - %(levelname)s - %(message)s",
    filename="autoformalization.log",
)


def run_cmd(cmd, shell=True, check=True):
    """Run subprocess command and log it"""
    logging.debug(f"Running: {cmd}")
    result = subprocess.run(
        cmd, shell=shell, check=check, text=True, capture_output=True
    )
    logging.debug(f"Output: {result.stdout}")
    if result.stderr:
        logging.debug(f"Stderr: {result.stderr}")
    return result
