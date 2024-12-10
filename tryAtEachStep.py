from concurrent.futures import ProcessPoolExecutor
import logging
import os
import subprocess
import sys
import random
from pathlib import Path

def process_file(file_path, tactic, outdir):
    """Process a single file with the given tactic."""
    logging.debug(f"Processing file: {file_path}")

    # Create the output file path
    out_file = Path(outdir) / f"{str(file_path).replace('/', '_').replace('.', '_')}"

    # Run the `lake exe tryAtEachStep` command
    command = ["lake", "exe", "tryAtEachStep", tactic, str(file_path), "--outfile", str(out_file)]
    logging.debug(f"Running command: {' '.join(command)}")

    try:
        subprocess.run(command, check=True)
        return f"Completed: {file_path}"
    except subprocess.CalledProcessError as e:
        return f"Error with {file_path}: {e}"

if __name__ == "__main__":
    logging.basicConfig(level=logging.DEBUG)

    TACTIC = sys.argv[1] if len(sys.argv) > 1 else "exact?"

    # Output directory
    OUTDIR = Path("./try-at-each-step-out")
    OUTDIR.mkdir(exist_ok=True)

    lean_files = list(Path(".lake/packages/mathlib/Mathlib").rglob("*.lean"))
    random.shuffle(lean_files)

    max_workers = os.cpu_count()
    if max_workers > 1:
        max_workers -= 1

    with ProcessPoolExecutor(max_workers=max_workers) as executor:
        results = list(executor.map(process_file, lean_files, [TACTIC] * len(lean_files), [OUTDIR] * len(lean_files)))

    # Log results
    for result in results:
        logging.info(result)

