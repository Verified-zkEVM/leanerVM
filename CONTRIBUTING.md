# Contributing to leanerVM

Thanks for contributing. This is a high-assurance formalization: a change is ready when
its code builds, its statement says the intended thing, and its evidence is reviewable.

## Start here

Read:

- [README.md](README.md) for project scope;
- [AGENTS.md](AGENTS.md) for the short operating contract;
- [docs/architecture.md](docs/architecture.md) for module ownership and dependency flow;
- [docs/dependencies.md](docs/dependencies.md) before changing Lake dependencies; and
- [docs/development.md](docs/development.md) for commands and test placement.

For a large contribution—such as a VM subsystem, table family, proof-system component,
or native boundary—open a design issue first. State the definitions, main theorems,
source revisions, dependency direction, tests, and known fidelity gaps before investing
in a large proof tree.

## Before opening a pull request

Run:

```sh
./scripts/validate.sh
```

The pull request description should include:

- the motivation and behavior change;
- the source/specification revision for semantic or implementation-correspondence work;
- the layer owning each new public definition;
- focused validation commands and meaningful test cases;
- whether the target is deployed behavior or a proposed repair; and
- linked issues or upstream pull requests.

Use the title form `type(scope): subject`, where `type` is normally `feat`, `fix`,
`docs`, `refactor`, `test`, `perf`, `ci`, or `chore`. Use imperative lower-case wording
without a trailing full stop.

## Lean files and modules

Production code lives under `LeanerVM/`; executable and proof-regression tests live
under `tests/`. New ordinary Lean files use Lean's module system by default and this shape:

```lean
/-
  LeanerVM.Example

  Optional context that helps a reader understand the module's purpose and
  relationship to the source material.
-/

module

public import LeanerVM.Semantics.Basic
import Some.Private.Implementation

/-!
# Descriptive module title

Explain the module's responsibility, principal definitions, and relevant sources.
-/

namespace LeanerVM.Example

public section

end
end LeanerVM.Example
```

A file may instead be a plain (non-`module`) file when it must import a non-`module`
dependency, or a file that does. Clean, at the pinned revision, is not written with the
module system, and Lean refuses to import a non-`module` from a `module` while a plain file
can import anything; so a plain file forces every file that imports it to be plain as well.
Keep that boundary as high in the import graph as the dependency allows. Today it is
`LeanerVM/Parameters/CleanField.lean`, the Clean-consuming modules of
`LeanerVM/Arithmetization/`, the aggregate `LeanerVM.lean`, and the test aggregate; the
`Parameters` and `Semantics` layers stay `module`s so that each other's modules can import
them. In a plain file, `public import`, `public section`, and `@[expose]` are rejected and
unnecessary: every import is re-exported and every body is visible to importers. Keep the
same header comment, module docstring, and section headings, and mark helpers `private`. A
plain file also lets the kernel unfold definitions the module system hides from importers,
which is why a plain test file can decide `E` arithmetic and a `module` cannot.

- Use the repository history for authorship rather than adding per-file author claims. Preserve
  copyright, licence, and attribution notices required by substantially derived upstream material.
- In a `module`, use `public import` only when downstream users need the dependency
  transitively, and plain `import` for implementation-only dependencies.
- In a `module`, put exported declarations in a `public section`; expose implementation
  details only when definitional unfolding is an intentional API promise.
- Keep repository-wide options in `lakefile.toml`; do not disable linters or re-enable
  implicit variables in individual files.
- Add every production module explicitly to `LeanerVM.lean` and every test module to
  `tests/LeanerVMTests.lean`. The validation script rejects missing, stale, and duplicate
  aggregate imports, and accepts `import` and `public import` lines alike.
- Import-only umbrella modules stay bare.

## Style and naming

Follow Lean and Mathlib conventions, adapted to this repository:

- files, structures, inductive types, and propositions use `UpperCamelCase`;
- functions and other terms use `lowerCamelCase`;
- theorem and lemma names use `snake_case`;
- treat acronyms as words (`OpcodeTable`, not `OPCODETable`);
- name declarations for what they state, not paper numbers, authors, or milestones;
- keep lines near 100 characters and indent with two spaces;
- use `fun x ↦ ...`, `where` structure syntax, and Mathlib-style `/-! ## Section -/`
  headings rather than ASCII banners; and
- prefer explicit intermediate lemmas over opaque, broad automation on unstable goals.

Every public definition and major theorem needs a declaration docstring. Ordinary files
need a module docstring. Cite papers by stable key or title and bind implementation claims
to an exact repository revision; do not rely on a floating branch URL as the specification.

## Proof and trust policy

Accepted production and test code must not introduce unproved declarations, unchecked
native evaluation, or unsafe execution. CI enforces a source-level gate. The first pull
request adding a production declaration must also enable `lean-action`'s kernel-level
axiom audit with `axiom-audit-root: LeanerVM`; it is intentionally disabled while the
namespace is empty.

For every proof deliverable:

1. review the statement independently of the proof;
2. identify assumptions and trusted dependencies;
3. add a concrete inhabitant for certificate/configuration types used positively;
4. include a mutation, counterexample, or negative test for the load-bearing condition;
5. distinguish generic reusable theory from leanVM-specific assembly; and
6. record any deployment mismatch explicitly.

Do not silence warnings or weaken repository policy to land a change. Fix the source or
propose a reviewed repository-wide policy change with tests.

## Porting and attribution

Port mathematics and proof ideas against current APIs; do not copy old subtrees. Preserve
required upstream attribution and license notices when material remains substantially
derived from another source. A porting pull request should identify the exact source commit
and old declarations, then explain statement or API changes made during the rewrite.

Reusable results should be proposed to their natural upstream library:

- CompPoly for computable polynomial and field algorithms;
- ArkLib for generic oracle reductions and proof systems;
- VCVio for oracle computations and cryptographic security carriers; and
- Clean for generic circuit, AIR, table, and witness-generation infrastructure.

Keep only leanVM-specific semantics, parameters, arithmetization instances, application
specifications, protocol assembly, and implementation-correspondence results here.

## Licensing

The repository is licensed under Apache 2.0. By contributing, you agree that your
contribution is licensed under the same terms. Do not add per-file authorship or separate
AI-attribution lines; preserve notices required by substantially derived upstream material.
