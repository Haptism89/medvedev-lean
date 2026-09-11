#!/usr/bin/env python3
"""Compile the whole audit module, then replay it and the project after import."""
import argparse
import os
from pathlib import Path
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    project = parser.parse_args().root.resolve()
    env = dict(os.environ, MEDVEDEV_AUDIT_ROOT=str(project))
    target = project / ".lake/build/lib/lean/Medvedev/Audit.olean"
    target.parent.mkdir(parents=True, exist_ok=True)
    # Compiling alone does not run the replay. Import the complete result below,
    # so declarations after the audit function cannot evade selection.
    subprocess.run(["lake", "env", "lean", "--trust=0", "-o", str(target),
                    "Medvedev/Audit.lean"], cwd=project, env=env, check=True)
    with tempfile.TemporaryDirectory(prefix="medvedev-audit-driver-") as directory:
        driver = Path(directory) / "Replay.lean"
        driver.write_text("import Medvedev.Audit\n"
                          "set_option maxHeartbeats 0 in\n"
                          "run_cmd Medvedev.auditProject\n")
        subprocess.run(["lake", "env", "lean", "--trust=0", str(driver)],
                       cwd=project, env=env, check=True)


if __name__ == "__main__":
    main()
