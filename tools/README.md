# Tools for working on the proofs

For contributors and agents; a reviewer needs none of this. The gate is `./check-all.sh` at the
root (`./check-all.sh lean`, `./check-all.sh vectors`, or any of `statement common lean_xmss
lean_sphincs lean_da lean_vm leanvm`); [`../lake-build.py`](../lake-build.py) runs one project's
build with its modules admitted by memory (`python3 -I lake-build.py lean_vm LeanVM LeanVMTests`).

## What an edit rebuilds

Lake rebuilds a module when a module it imports, directly or not, changes. For a `module` file (all of `Statement`; `common`, `lean_xmss`, `lean_da` and `lean_vm` but the files below; of `lean_sphincs` only its nine scheme and statement files, `Sphincs/Scheme.lean`, `Statement.lean`, `WithHash.lean` and the like) that means a change of what the import exports: a declaration's statement, an exposed definition's body, a declaration added or removed; a proof, a comment or a docstring changes nothing downstream. A file outside the module system is rebuilt by any change of its imports: the projects' end files; most tests, which evaluate code a module cannot; `lean_sphincs` but its nine; `lean_da`'s `PqDas.lean` and `PqDas/AxiomCheck.lean`; and about thirty files of `lean_vm/LeanVM/`: the random-permutation layer (`Protocol/Rpm/`, `Protocol/LeanVMRpm.lean`, the experiment bridges, `Guest/EndRpm.lean`, `Guest/Batch/Rpm.lean`, `Guest/Child/NZRpm.lean`), the prover's (`Prover/Fast/`, `Prover/Assemble.lean`, `Complete.lean`, `End.lean`) and the firewalls (`…Firewall.lean`). So the cost of an edit is the work downstream of it, and what matters most is that the slow modules, the kernel-checked certificates and tables, import only what they evaluate.

* `python3 -I tools/deps.py cone FILE` says what an edit of `FILE`'s interface rebuilds: the modules, their CPU time and the longest chain, from the import graph and the times of the last `lake-build.py` runs; `deps.py slow` lists the slowest modules and how many modules can rebuild each, `deps.py path` the longest chain of a full build.
* `python3 -I tools/profile.py FILE` says where a slow file's time goes: its costliest declarations and, in each, the steps whose own time is largest (a tactic, a unification, a kernel check), from Lean's profiler with the declarations checked one after another; its docstring lists the usual fixes by kind of step.
* `lake env lean --run ../tools/NeededImports.lean MODULE`, in a project after building `MODULE`, says which of the repository's modules `MODULE` imports without needing them, and which needed modules bring them in (the modules to split). Kernel-checked modules are guarded by such a check in the build (`lean_sphincs/Sphincs/TablesFirewall.lean`).
* `lake env lean --run ../tools/Unused.lean ROOT... --prefix P`, in a project after building it, lists the theorems and definitions of the modules `P…` that nothing the roots import uses (give the end module and the tests as roots): dead proofs, or results kept for a reader; read before deleting.
* `python3 -I tools/escape-scan.py DIR...` fails on a proof escape outside comments (`sorry`, `admit`, `native_decide`, `+native`, `unsafe`, `implemented_by`, `#exit`, an `axiom` declaration, the ways to skip the kernel); the CI and `check-all.sh` run it on every project.
* `python3 -I tools/docnames.py` lists the names the READMEs and `statement.tex` cite that no Lean file has (renamed or removed declarations; some hits are leanVM's Rust names).
* To iterate on `lean_vm`, `lake build MODULE` builds one module and what it needs, and `python3 -I lake-build.py lean_vm --dev …` skips the kernel (see `lean_vm`'s README); the gate, `lake build` here, is for a change that is done.

## Against leanVM

[`leanvm-rev`](leanvm-rev) is the leanVM commit whose verifier, leanISA guest program and prover `lean_vm` is about. [`leanvm-tree.sh`](leanvm-tree.sh) checks it out into `.leanvm/`, with its `formal/lean_vm` a link to `lean_vm/`. There the Rust verifier is fuzzed against the Lean one, and `lean_vm/scripts/guest-export` writes the leanISA guest program's data (its bytecode into `Statement/Data/`) and the node vectors from leanVM's sources (at this pin leanVM has no tests that write Lean data); CI runs both.

leanVM's own `formal/` goes on changing. Following it is deliberate: bump `leanvm-rev`, carry over the matching `formal/` changes, and let the checks above say what is stale. The generated data's headers and some prose still name leanVM's paths (`formal/lean_vm/…`, `crates/…`); those are citations into the leanVM tree.
