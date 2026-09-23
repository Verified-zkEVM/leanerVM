#!/usr/bin/env python3
"""Verify imported-module warning errors and the audit that prevents local overrides."""

import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import tomllib


ROOT = Path(__file__).resolve().parent.parent


def main() -> None:
    config = tomllib.loads((ROOT / "lakefile.toml").read_text())
    options = config.get("leanOptions", {})
    if options.get("warningAsError") is not True:
        raise SystemExit("Expected package-level warningAsError for every first-party module")
    with tempfile.TemporaryDirectory(prefix="leanisa-warning-policy-") as directory:
        root = Path(directory)
        (root / "lean-toolchain").write_text((ROOT / "lean-toolchain").read_text())
        (root / "lakefile.toml").write_text(
            'name = "warningPolicy"\n'
            f'[leanOptions]\nwarningAsError = {json.dumps(options["warningAsError"])}\n'
            '[[lean_lib]]\nname = "LeanerVM"\n'
            '[[lean_lib]]\nname = "LeanerVMTests"\nsrcDir = "tests"\n'
        )
        (root / "scripts").mkdir()
        for script in ("audit-lean.sh", "check-lean-options.py"):
            shutil.copy2(ROOT / "scripts" / script, root / "scripts" / script)
        (root / "tests").mkdir()
        clean_source = "import Lean\ndef warningPolicyValue : Nat := 0\n"
        for name, source_root in (("LeanerVM", root), ("LeanerVMTests", root / "tests")):
            (source_root / name).mkdir()
            (source_root / f"{name}.lean").write_text(f"import {name}.Leaf\n")
            leaf = source_root / name / "Leaf.lean"
            leaf.write_text(clean_source)
            clean = subprocess.run(
                ["lake", "build", name], cwd=root, capture_output=True, text=True
            )
            if clean.returncode != 0:
                raise SystemExit(clean.stdout + clean.stderr)
            audited = subprocess.run(
                ["./scripts/audit-lean.sh"], cwd=root, capture_output=True, text=True
            )
            if audited.returncode != 0:
                raise SystemExit(audited.stdout + audited.stderr)
            leaf.write_text(
                'import Lean\nrun_cmd Lean.logWarning "warning-policy-negative-control"\n'
            )
            warned = subprocess.run(
                ["lake", "build", name], cwd=root, capture_output=True, text=True
            )
            output = warned.stdout + warned.stderr
            if warned.returncode == 0 or "warning-policy-negative-control" not in output:
                raise SystemExit(f"Imported {name} warning was not rejected:\n{output}")
            # These are valid Lean overrides that defeat package-level warningAsError.
            # Check the real audit rejects each and that Lean still emits the planted
            # warning while succeeding without that audit (the load-bearing control).
            for separator in (
                " -- separator\n  ",
                " /- separator -/ ",
                ' /- outer " -- /- nested -/ remaining -/ ',
            ):
                for scope in ("", " in"):
                    leaf.write_text(
                        f"import Lean\nset_option{separator}warningAsError false{scope}\n"
                        'run_cmd Lean.logWarning "warning-policy-comment-control"\n'
                    )
                    audited = subprocess.run(
                        ["./scripts/audit-lean.sh"], cwd=root, capture_output=True, text=True
                    )
                    output = audited.stdout + audited.stderr
                    location = str(leaf.relative_to(root)) + ":2:"
                    if audited.returncode == 0 or location not in output or (
                        "must not be overridden" not in output
                    ):
                        raise SystemExit(f"Imported {name} override escaped the audit:\n{output}")
                    bypass = subprocess.run(
                        ["lake", "build", name], cwd=root, capture_output=True, text=True
                    )
                    output = bypass.stdout + bypass.stderr
                    if bypass.returncode != 0 or "warning-policy-comment-control" not in output:
                        raise SystemExit(f"Imported {name} override control was invalid:\n{output}")
            leaf.write_text(clean_source)
    print("Imported production/test warning policy and comment-override controls passed.")


if __name__ == "__main__":
    main()
