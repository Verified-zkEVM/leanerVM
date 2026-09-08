#!/usr/bin/env python3
"""Exercise repository policy gates against planted positive and negative fixtures."""

from __future__ import annotations

import shutil
import subprocess
import tempfile
from contextlib import contextmanager
from pathlib import Path
from typing import Iterator


ROOT = Path(__file__).resolve().parent.parent
CHECKS = ("audit-lean.sh", "check-imports.sh", "check-layers.sh")


def write(path: Path, contents: str = "module\n") -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(contents, encoding="utf-8")


@contextmanager
def fixture() -> Iterator[Path]:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        scripts = root / "scripts"
        scripts.mkdir()
        for name in CHECKS:
            destination = scripts / name
            shutil.copy2(ROOT / "scripts" / name, destination)
            destination.chmod(0o755)

        for layer in ("Parameters", "Semantics", "Arithmetization", "Protocol"):
            write(root / "LeanerVM" / layer / "Basic.lean")
        write(
            root / "LeanerVM.lean",
            """module

public import LeanerVM.Arithmetization.Basic
public import LeanerVM.Parameters.Basic
public import LeanerVM.Protocol.Basic
public import LeanerVM.Semantics.Basic
""",
        )
        write(root / "tests" / "LeanerVMTests" / "Imports.lean")
        write(
            root / "tests" / "LeanerVMTests.lean",
            "module\n\npublic import LeanerVMTests.Imports\n",
        )
        write(root / "tests" / "Main.lean", "module\n\npublic import LeanerVMTests\n")
        yield root


def run(root: Path, check: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [str(root / "scripts" / check)],
        cwd=root,
        check=False,
        text=True,
        capture_output=True,
    )


def require_pass(result: subprocess.CompletedProcess[str], context: str) -> None:
    if result.returncode != 0:
        raise RuntimeError(
            f"{context}: expected success, got {result.returncode}\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )


def require_failure(
    result: subprocess.CompletedProcess[str], context: str, expected: str
) -> None:
    output = result.stdout + result.stderr
    if result.returncode == 0 or expected not in output:
        raise RuntimeError(
            f"{context}: expected failure containing {expected!r}, got {result.returncode}\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )


def test_source_audit() -> None:
    with fixture() as root:
        require_pass(run(root, "audit-lean.sh"), "clean source audit")
        probe = root / "LeanerVM" / "Semantics" / "Violation.lean"
        cases = (
            ("axiom planted : True", "Forbidden trust-sensitive"),
            ("set_option autoImplicit true", "must not be overridden"),
            ("set_option relaxedAutoImplicit true", "must not be overridden"),
            ("set_option linter.unusedVariables false", "must not be overridden"),
            ("set_option weak.linter.mathlibStandardSet false", "must not be overridden"),
        )
        for source, expected in cases:
            write(probe, f"module\n\n{source}\n")
            require_failure(run(root, "audit-lean.sh"), source, expected)
        probe.unlink()
        require_pass(run(root, "audit-lean.sh"), "source audit after cleanup")


def test_layer_gate() -> None:
    with fixture() as root:
        require_pass(run(root, "check-layers.sh"), "clean layer gate")
        probe = root / "LeanerVM" / "Semantics" / "Violation.lean"
        import_forms = (
            "import LeanerVM.Protocol.Basic",
            "public import LeanerVM.Protocol.Basic",
            "meta import LeanerVM.Protocol.Basic",
            "public meta import LeanerVM.Protocol.Basic",
            "import all LeanerVM.Protocol.Basic",
        )
        for declaration in import_forms:
            write(probe, f"module\n\n{declaration}\n")
            require_failure(
                run(root, "check-layers.sh"), declaration, "Forbidden Semantics dependency"
            )
        probe.unlink()

        unknown = root / "LeanerVM" / "Experimental" / "Basic.lean"
        write(unknown)
        require_failure(
            run(root, "check-layers.sh"),
            "unknown production layer",
            "Unknown production layer",
        )
        shutil.rmtree(unknown.parent)

        loose = root / "LeanerVM" / "Loose.lean"
        write(loose)
        require_failure(
            run(root, "check-layers.sh"),
            "loose production module",
            "must belong to a registered layer",
        )
        loose.unlink()
        require_pass(run(root, "check-layers.sh"), "layer gate after cleanup")


def test_aggregate_gate() -> None:
    with fixture() as root:
        require_pass(run(root, "check-imports.sh"), "clean aggregate gate")

        production = root / "LeanerVM" / "Semantics" / "Orphan.lean"
        write(production)
        require_failure(
            run(root, "check-imports.sh"),
            "orphan production module",
            "Missing from LeanerVM.lean",
        )
        production.unlink()

        test = root / "tests" / "LeanerVMTests" / "Orphan.lean"
        write(test)
        require_failure(
            run(root, "check-imports.sh"),
            "orphan test module",
            "Missing from tests/LeanerVMTests.lean",
        )
        test.unlink()

        misplaced = root / "tests" / "Loose.lean"
        write(misplaced)
        require_failure(
            run(root, "check-imports.sh"),
            "misplaced test module",
            "outside tests/LeanerVMTests/",
        )
        misplaced.unlink()

        main = root / "tests" / "Main.lean"
        write(main)
        require_failure(
            run(root, "check-imports.sh"),
            "disconnected test aggregate",
            "must import the LeanerVMTests aggregate",
        )
        write(main, "module\n\npublic import LeanerVMTests\n")
        require_pass(run(root, "check-imports.sh"), "aggregate gate after cleanup")

        # Plain (non-`module`) aggregates use `import`; they are checked the same way.
        aggregate = root / "LeanerVM.lean"
        plain_aggregate = """import LeanerVM.Arithmetization.Basic
import LeanerVM.Parameters.Basic
import LeanerVM.Protocol.Basic
import LeanerVM.Semantics.Basic
"""
        write(aggregate, plain_aggregate)
        write(root / "tests" / "LeanerVMTests.lean", "import LeanerVMTests.Imports\n")
        write(main, "import LeanerVMTests\n")
        require_pass(run(root, "check-imports.sh"), "plain aggregates")
        write(aggregate, plain_aggregate + "import LeanerVM.Semantics.Ghost\n")
        require_failure(
            run(root, "check-imports.sh"),
            "stale plain import",
            "Stale import in LeanerVM.lean",
        )
        write(aggregate, plain_aggregate + "import LeanerVM.Semantics.Basic\n")
        require_failure(
            run(root, "check-imports.sh"),
            "duplicate plain import",
            "Duplicate imports in LeanerVM.lean",
        )


def main() -> int:
    test_source_audit()
    test_layer_gate()
    test_aggregate_gate()
    print("Repository policy checker tests passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
