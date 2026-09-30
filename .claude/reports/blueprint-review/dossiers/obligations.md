# Dossier `obligations`: the hierarchy of proof obligations of the leanVM proof system

Task `obligations` of the blueprint review. Written 2026-09-30. Object: leanerVM `main` at
`b435631` (every Lean citation at that revision, `git show b435631:<path>`); ground truth leanVM
at `a386121f` (read with `git -C /home/scaraven/Documents/leanEthereum/leanVM show a386121f:<path>`;
the checkout has moved, brief §8); libraries at the old pins (ArkLib `dca90385`, CompPoly
`3468b38c`, VCVio `f9dc47d9`, Clean `93c9d1ef`) unless the new pin (`7653a901`, `572f9973`,
`a4232d08`, `42fe4b26`) is named. No Lean was run for this dossier: every status below rests on
the sibling dossiers' recorded probes (named at each node) or on reading the sources.

Inputs, read in the order the task gave: `docs/architecture.md` and
`docs/roadmap/protocol-blueprint.md` at `b435631`; the dossiers `code-spine`, `lib-arklib`,
`gt-bus`, `gt-table-pub`, `gt-flock-ring`, `code-pubinput`, `boundary-adaptor`, `literature`,
`code-layer1`, `gt-opening-compile` (complete when read: its summary is headed "Conclusions" with
five items and its sections A to G are written), `lib-others`, and the `register` staging (its
row identifiers are quoted in parentheses only where they locate a finding); the Lean sources
of `LeanerVM/Protocol/` at `b435631` for every name.

Abbreviations for pointers: `bp:NNN` is a line of the blueprint at `b435631`; `arch:NNN` a line of
`docs/architecture.md` at `b435631`; a dossier is named by its task name and section.

**Status vocabulary** (one tag per node, counted in the summary):

| Tag | Meaning at `b435631` |
| --- | --- |
| `[status: built and proved]` | stated and proved in leanerVM; `#print axioms` gives the kernel's three standard axioms only (as recorded by the named dossier's probe) |
| `[status: built, definition]` | a definition in leanerVM, load-bearing, with no proof obligation of its own (its content is what later theorems prove things about) |
| `[status: library, proved at the old pin]` | proved in ArkLib, VCVio, CompPoly, Clean or Mathlib at the old pin (and, where the dossier checked, at the new one) |
| `[status: library, proved at the new pin only]` | landed upstream between the pins |
| `[status: admitted upstream]` | stated in a library and `sorry` at both pins |
| `[status: specified only]` | stated in the blueprint (a sketch), not built |
| `[status: not specified]` | needed by the composition and stated nowhere in the blueprint |
| `[status: unprovable as written]` | the review found the blueprint's statement cannot be proved (or stated) as it stands |
| `[status: wrong as written]` | the review found the blueprint's description false of leanVM or of the code |
| `[status: trusted, assumed interface]` | a structure whose fields are theorems another roadmap or library owes; every theorem that uses it takes it as an argument |
| `[status: trusted, hypothesis]` | a hypothesis of a theorem on the chain that nothing on the chain discharges |
| `[status: trusted, transcribed data]` | Category B data (layouts, constants, schedules) whose only check is a fixture |

A node marked `[review: …]` is one on which the review found the blueprint's statement wrong,
missing or unprovable; the tag says which.

## 1. Summary

(written last; see the end of the file for the counts and the trusted leaves)

