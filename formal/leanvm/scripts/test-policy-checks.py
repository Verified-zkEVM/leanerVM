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
SUPPORT = ("check-lean-options.py",)


def write(path: Path, contents: str = "module\n") -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(contents, encoding="utf-8")


@contextmanager
def fixture() -> Iterator[Path]:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        scripts = root / "scripts"
        scripts.mkdir()
        for name in CHECKS + SUPPORT:
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
            ("set_option warningAsError false", "must not be overridden"),
            ("set_option linter.unusedVariables false", "must not be overridden"),
            ("set_option weak.linter.mathlibStandardSet false", "must not be overridden"),
            ("set_option debug.skipKernelTC true", "must not be overridden"),
            ("theorem t : 2 ^ 10 = 1024 := by decide +native", "Forbidden trust-sensitive"),
            ("@[implemented_by id] def f (n : Nat) : Nat := n", "Forbidden trust-sensitive"),
            ('@[extern "f"] opaque f : Nat → Nat', "Forbidden trust-sensitive"),
            ("run_cmd Lean.addDecl default", "Forbidden trust-sensitive"),
        )
        for source, expected in cases:
            write(probe, f"module\n\n{source}\n")
            require_failure(run(root, "audit-lean.sh"), source, expected)
        probe.unlink()
        # The executable's sources are audited too.
        cli = root / "cli" / "Probe.lean"
        write(cli, "axiom planted : True\n")
        require_failure(run(root, "audit-lean.sh"), "cli source", "Forbidden trust-sensitive")
        shutil.rmtree(cli.parent)
        # Every protected option must be caught across Lean whitespace/comments, in both
        # production and imported-test source trees, including locally scoped overrides.
        for relative in ("LeanerVM/Semantics/Violation.lean", "tests/LeanerVMTests/Violation.lean"):
            probe = root / relative
            for option in (
                "autoImplicit true",
                "relaxedAutoImplicit true",
                "warningAsError false",
                "linter.unusedVariables false",
                "weak.linter.mathlibStandardSet false",
            ):
                for separator in (
                    "\t", "\n  ", "\n\t", "\r\n  ", " \n\n\t ",
                    " -- separator\n  ",
                    " /- separator -/ ",
                    "/-no whitespace-/",
                    " /- outer /- inner -/ still outer -/ ",
                    ' /- outer " -- /- inner /- deepest -/ -/ -/ ',
                    " /- first -/ -- line /- ignored\n /- last -/ ",
                ):
                    for scope in ("", " in\nexample : True := True.intro"):
                        source = f"set_option{separator}{option}{scope}"
                        write(probe, f"module\n\n{source}\n")
                        require_failure(run(root, "audit-lean.sh"), repr(source),
                                        "must not be overridden")
            for option in (
                "«autoImplicit» true",
                "«relaxedAutoImplicit» true",
                "«warningAsError» false",
                "«linter».unusedVariables false",
                "weak.«linter».mathlibStandardSet false",
            ):
                source = f"set_option /- separator -/ {option}"
                write(probe, f"module\n\n{source}\n")
                require_failure(run(root, "audit-lean.sh"), source, "must not be overridden")
            # Delimiters in strings must not hide a later command. The policy remains
            # conservative: command-shaped text in strings/comments is also rejected.
            for source in (
                'def start := "/-"\nset_option /- gap -/ warningAsError false\ndef stop := "-/"',
                '-- set_option /- gap -/ warningAsError false',
                '/- set_option /- gap -/ warningAsError false -/',
                'def text := "set_option /- gap -/ warningAsError false"',
            ):
                write(probe, f"module\n\n{source}\n")
                require_failure(run(root, "audit-lean.sh"), source, "must not be overridden")
            write(probe, "module\n\nset_option /- line one\n/- nested -/ -/\nwarningAsError false\n")
            require_failure(run(root, "audit-lean.sh"), "diagnostic line", f"{relative}:3:")
            write(probe, "module\n\nset_option /- unterminated\nwarningAsError false\n")
            require_failure(run(root, "audit-lean.sh"), "unterminated separator",
                            "unterminated block comment")
            for source in (
                "set_option /- allowed -/ maxRecDepth 4096",
                "set_option /- outer /- inner -/ warningAsError false -/ maxRecDepth 4096",
                "set_option -- warningAsError false\nmaxRecDepth 4096",
                "set_/- separator -/option warningAsError false",
            ):
                write(probe, f"module\n\n{source}\n")
                require_pass(run(root, "audit-lean.sh"), source)
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

        # A layer's root module beside its directory belongs to the layer, under its rules.
        rootmod = root / "LeanerVM" / "Semantics.lean"
        write(rootmod, "module\n\npublic import LeanerVM.Parameters.Basic\n")
        require_pass(run(root, "check-layers.sh"), "a layer's root module")
        write(rootmod, "module\n\npublic import LeanerVM.Protocol.Basic\n")
        require_failure(
            run(root, "check-layers.sh"), "a layer's root module importing upward", "Semantics"
        )
        rootmod.unlink()

        # The wall: a protocol module importing the arithmetization is rejected unless it is one
        # of the modules the allow-list names.
        wall = root / "LeanerVM" / "Protocol" / "Spine" / "Phase.lean"
        for declaration in import_forms:
            write(wall, f"module\n\n{declaration.replace('Protocol', 'Arithmetization')}\n")
            require_failure(run(root, "check-layers.sh"), f"wall: {declaration}", "the wall")
        wall.unlink()
        shutil.rmtree(wall.parent)
        allowed = root / "LeanerVM" / "Protocol" / "FixedColumns.lean"
        write(allowed, "module\n\npublic import LeanerVM.Arithmetization.Basic\n")
        require_pass(run(root, "check-layers.sh"), "wall allow-list")
        allowed.unlink()
        # The adaptor's modules under `LeanIsa/` are inside the wall; a sibling of the name is not.
        adaptor = root / "LeanerVM" / "Protocol" / "LeanIsa" / "Sound.lean"
        write(adaptor, "module\n\npublic import LeanerVM.Arithmetization.Basic\n")
        require_pass(run(root, "check-layers.sh"), "wall allow-list: the adaptor's directory")
        adaptor.unlink()
        shutil.rmtree(adaptor.parent)
        sibling = root / "LeanerVM" / "Protocol" / "LeanIsaExtra.lean"
        write(sibling, "module\n\npublic import LeanerVM.Arithmetization.Basic\n")
        require_failure(run(root, "check-layers.sh"), "wall: a sibling of the adaptor", "the wall")
        sibling.unlink()
        # The end-to-end theorems under `EndToEnd/` are inside the wall; a sibling is not.
        endtoend = root / "LeanerVM" / "Protocol" / "EndToEnd" / "Front" / "Layout.lean"
        write(endtoend, "module\n\npublic import LeanerVM.Arithmetization.Basic\n")
        require_pass(run(root, "check-layers.sh"), "wall allow-list: the end-to-end directory")
        endtoend.unlink()
        shutil.rmtree(endtoend.parent.parent)
        sibling = root / "LeanerVM" / "Protocol" / "EndToEndExtra.lean"
        write(sibling, "module\n\npublic import LeanerVM.Arithmetization.Basic\n")
        require_failure(run(root, "check-layers.sh"), "wall: a sibling of EndToEnd", "the wall")
        sibling.unlink()
        # The specification imports nothing of the repository outside `Spec/`.
        spec = root / "LeanerVM" / "Spec" / "Violation.lean"
        for declaration in import_forms:
            write(spec, f"module\n\n{declaration.replace('Protocol', 'Parameters')}\n")
            require_failure(
                run(root, "check-layers.sh"), f"spec: {declaration}", "Forbidden Spec dependency"
            )
        for declaration in import_forms:
            write(spec, f"module\n\n{declaration.replace('Protocol.Basic', 'Spec.Field')}\n")
            require_pass(run(root, "check-layers.sh"), f"spec importing spec: {declaration}")
        spec.unlink()
        shutil.rmtree(spec.parent, ignore_errors=True)
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
