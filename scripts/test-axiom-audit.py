#!/usr/bin/env python3
"""Check the real namespace audit and its rejection of transitive foreign assumptions."""

from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parent.parent
DRIVER = ROOT / "scripts" / "audit-axioms.lean"


def main() -> None:
    positive = subprocess.run(
        ["lake", "env", "lean", "-E", "warning", str(DRIVER)],
        cwd=ROOT, capture_output=True, text=True, check=False,
    )
    positive_output = positive.stdout + positive.stderr
    if positive.returncode != 0 or "unexpected axioms: []" not in positive_output:
        raise RuntimeError(f"The unmodified audit did not pass:\n{positive_output}")
    print(positive_output, end="")

    source = DRIVER.read_text(encoding="utf-8")
    prefix, marker, suffix = source.rpartition("\nauditValidation\n")
    if not marker or suffix:
        raise RuntimeError("Expected the audit invocation at the end of the driver")
    # The deliberately untrusted fixture exists only in a temporary file. Neither project
    # namespace declares the foreign assumption: recursive dependency inspection must find it.
    injected = """
axiom AuditNegative.hidden : False
theorem LeanerVM.auditNegative : False := AuditNegative.hidden
theorem LeanerVMTests.auditNegative : False := AuditNegative.hidden

auditValidation
"""
    with tempfile.TemporaryDirectory(prefix="leanisa-axiom-audit-") as directory:
        probe = Path(directory) / "AuditNegative.lean"
        probe.write_text(prefix + injected, encoding="utf-8")
        negative = subprocess.run(
            ["lake", "env", "lean", "-E", "warning", str(probe)],
            cwd=ROOT, capture_output=True, text=True, check=False,
        )
        output = negative.stdout + negative.stderr
        expected = ("Unexpected axioms", "AuditNegative.hidden",
                    "LeanerVM.auditNegative", "LeanerVMTests.auditNegative")
        if negative.returncode == 0 or not all(text in output for text in expected):
            raise RuntimeError(f"Expected transitive rejection in both namespaces:\n{output}")
    print("Transitive foreign-assumption rejection passed for production and test namespaces.")


if __name__ == "__main__":
    main()
