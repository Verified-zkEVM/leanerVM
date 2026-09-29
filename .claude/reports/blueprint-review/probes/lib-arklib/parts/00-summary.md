# Dossier `lib-arklib`: ArkLib's framework for interactive oracle reductions at the pin

Reviewed: ArkLib at the pin `dca90385` (sources read in `.lake/packages/Arklib/`), leanerVM `main`
at `b435631`, ArkLib `origin/main` at `7653a901e` (fetched 2026-09-29, 347 commits after the pin),
ArkLib pull request #615 at its head `ca7a2577`. Every Lean statement below is copied from the
file named with it. Every probe is reproduced in the appendix with its command and its output.

**PRELIMINARY VERSION, being extended section by section. The summary is rewritten last.**

## Results established so far (evidence in the sections and the appendix)

1. leanerVM's master theorems and everything they are built from depend on the three standard
   axioms only (`propext`, `Classical.choice`, `Quot.sound`); no `sorryAx` (probe `AxiomsLeanerVM`).
2. ArkLib at the pin admits the composition of soundness, knowledge soundness and both
   round-by-round notions (`Verifier.append_*`, `Verifier.seqCompose_*`), and the implications
   from round-by-round knowledge soundness to plain knowledge soundness and soundness
   (`#print axioms` shows `sorryAx`; probe `AxiomsArkLibBuilt`; source `Security/Implications.lean`).
   They are still admitted on `origin/main`.
3. The local file `LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean` is the file of pull request
   #615 at `ca7a2577` up to the header, the module keywords, a namespace, added docstrings, two
   lemmas replaced by references to ArkLib's own, two names qualified, and the omission of the
   four wrapper theorems. Pull request #615 is open, not merged, and in conflict with `main`.
4. The notion is not vacuous: a verifier that accepts everything has no knowledge state
   function (no round), and is not knowledge sound at error 0 (one challenge), whatever the
   extractor; it is knowledge sound at error 1, as every verifier is (probe `NonVacuity`).
5. ArkLib's extractor type accepts an extractor that chooses a witness by classical choice, and
   such an extractor is "knowledge sound at error 0" for every relation whose language the
   verifier decides (probe `Extractors`): the existential form of the notion is soundness, not
   knowledge. The named form is meaningful only if the named extractor is read.
6. The three extractors of leanerVM are compiled definitions and run (probe `Extractors`).
7. `Component.Def` carries the real-valued error, so every phase definition with a challenge is
   `noncomputable`, and neither the verifier nor the extractor can be compiled when reached
   through the phase definition (probe `ExtractorsExpectedFailure`).
