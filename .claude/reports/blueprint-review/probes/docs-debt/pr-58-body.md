## Motivation

Hole **S** of the proof-system roadmap (#12, revision 2, section *The spine*): the trunk every other unit of the proof system plugs into. Before it, the open pull requests (#38 to #43) were algebra with nothing to hang on; after it, every phase, generic component, the adaptor and the compilation is a `Def`/`Complete`/`Security` triple against fixed seams, written over an abstract `I : M3Instance`, tested on a toy instance, and landed in isolation.

## What is added

`LeanerVM/Protocol/Spine/` (five `module` files: `Instance`, `Seams`, `Phase`, `Compose`, `Toy`),
`LeanerVM/Protocol/ToArkLib/` (six `module` files that are candidates for ArkLib: `Oracles`,
`Component`, `KnowledgeAppend`, `PassThrough`, `SendOracle`, `Refinement`), two oracle instances
for scalar messages in `LeanerVM/Protocol/Field.lean`, and
`tests/LeanerVMTests/Protocol/Spine.lean`; the sketch under "What the spine fixes" in
`docs/roadmap/protocol-blueprint.md` names what each file holds.

- `Instance.lean`: `Shape`, `Layout`, `Coord`, `BoundaryBlock`, `PublicLine`, `M3Instance` (with
  the degree bound `d` and its proofs `constraints_degree`, `flushes_degree`), the five clauses,
  `M3Holds` (decidable) and `M3Rel`.
- `Seams.lean`: `ColumnClaim`; `VirtualTerm`, a `K`-polynomial of a table's row with an `E`
  weight; `LinearClaim`, `Weight`, `WeightedClaim`; the phase outputs; the six seams through
  `Seam.of`, `Seam.bus` bounding the total degree of every term by `I.d`.
- `Component.lean`, `PassThrough.lean`, `SendOracle.lean`, `Phase.lean`: `Component.Def`,
  `Complete` and `Security` (a `Security` carries its extractor and knowledge state function)
  with their `append`, both proved; the pass-through and the one-message commit shape, each with
  both halves proved; their `Phase.*` specialisations.
- `KnowledgeAppend.lean`: the knowledge-soundness append ArkLib admits at the pin, ported with
  its attribution from ArkLib #615's `Append/Knowledge.lean` at `ca7a2577`, under
  `LeanerVM.Protocol` with ArkLib's names: `Verifier.KnowledgeStateFunction.appendGuarded` (the
  knowledge state function of the appended extractor, ArkLib's own
  `Extractor.RoundByRound.append`) and
  `Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first` (the bound, each
  challenge keeping its component's error). Deleted when the pin moves past #615.
- `Compose.lean`: the commit phase (both halves proved, at error zero), `Phases`,
  `Phases.Complete`, `Phases.Security`, `leanVmPiop`, `piopError`, `piopExtractor`, and the
  master theorems `piop_perfectCompleteness`, `piop_rbrKnowledgeSoundness` and
  `piop_rbrKnowledgeSoundness_exists`.
- `Refinement.lean`: `Refinement`, `Refinement.map_option_valid`, and
  `Extractor.Straightline.map` (an ArkLib candidate with no consumer yet).
- `Toy.lean`: one table of width 3 and height 2 on a stack of height 8, with one constraint, one
  push, one boundary pull, one count column, one public line and `d = 2`.
- Tests: `M3Holds` decided by `#guard` on the honest stack; each of the four checkable clauses
  made to fail alone (`badLine` for the public line); a char-2 witness (`badBalanceSum`) that a
  field-summed balance would accept and `List.Perm` rejects; a bus statement carrying a cubic
  term proved outside `Seam.bus`; `trivPhases`/`trivComplete` (five pass-through phases)
  inhabiting `Phases` and `Phases.Complete`, and a `Phase.Security` by the identity pass-through
  at the public-input seam; `piopExtractor` returning the honest stack on the honest transcript
  by `rfl`, for any `S`.

The knowledge theorem is stated for the named extractor `piopExtractor`: the commit phase's,
which reads the stack off the first message, followed by the phases', appended through the
verdicts by ArkLib's own `Extractor.RoundByRound.append`, with the ported knowledge state
function and bound. Category A; the ideal-oracle half of T4 (`docs/architecture.md`); both
master theorems are conditional on the phases' proofs only. The knowledge composition is proved
with no assumed statement (the port of ArkLib #615, which closes hole C1).

## Sources and revisions

Category A throughout, written from leanVM `a386121f` §5, §6.2, §8.2, §8.5 and the roadmap; nothing transcribes Rust. Framework: ArkLib `dca90385` (`OracleReduction`, `append`, `perfectCompleteness`, `rbrKnowledgeSoundnessWorstCase`, `KnowledgeStateFunction`, `GuardedForm`), CompPoly `3468b38c` (`CMvPolynomial`, `CMlPolynomialEval.evalMle`). Pattern: leanth's explore branch `scaraven/proof-system-explore` at `db895db` (a `Type 0` witness, the commit stage pinning the oracle to the witness of record, the abstract PCS boundary), without its two defects (a classical extractor, a field-summed balance).

## Design notes

- The witness is the stack `q : Column I.μ` itself; after the commit phase the oracle is the witness and every later witness is `Unit`. The adaptor (hole I2) reaches leanISA's `SatisfiedBy` from it.
- Decisions settled by construction (status file, reversible by a PR here): 2, 6, 7, 8 (the caps are not a clause of `M3Holds`), 9, 10; plus: seams carry claims only, and message schedules travel with each `Def` (only `commitSpec` is fixed). Taken with the review of 2026-09-28: 11 (extractor discipline: `piopExtractor`), 12 (the strong Flock predicate), 13 (public lines, not cells), 14 (the degree bound on the instance).
- `Layout` is a reading law, not a stacking law; the adaptor's `witnessOf_stackOf` pins the leanISA layout.
- The probabilistic transport of `knowledgeSoundnessWith` along a refinement is not proved (ArkLib's game fixes the prover's witness type; no consumer yet); T4 uses `map_option_valid` pointwise because its target witness is in `Type 1`.
- Two adversarial reviews by context-free agents (2026-09-25; 2026-09-28, `docs/reviews/protocol-spine.md`) found no theorem statement wrong or vacuous. The first's test and documentation findings, and the second's five interface findings (A1 to A5) and six compressions (H1 to H6), are applied; every finding was met before merge.

## Layer ownership of new public definitions

`Protocol` (spine): everything under `LeanerVM.Protocol` in the eleven modules under `Spine/` and `ToArkLib/`, and the two instances in `Field.lean`; the interfaces block of the blueprint lists them.

## Validation

```sh
./scripts/validate.sh
```

All gates pass; `lake build` and `lake test` succeed; the axiom audit reports 2884 declarations and no unexpected axiom (CI on the merged head). `#print axioms` on `main` at `5cb7da6` for `piop_perfectCompleteness`, `piop_rbrKnowledgeSoundness`, `piop_rbrKnowledgeSoundness_exists`, `commitComplete`, `commitSecurity`, `Component.Complete.append`, `Component.Security.append`, `Phases.Security.toDef`, `Component.passThroughSecurity`, `Verifier.KnowledgeStateFunction.appendGuarded`, `Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first`, `Toy.read_eval`: `propext, Classical.choice, Quot.sound`.

## Deployed behavior or repair

Neither: the relation and the composition are specification of intent (Category A); no correspondence to the Rust prover or verifier is claimed.

## Ledger and target

Ledger A2 is discharged by the port in `ToArkLib/KnowledgeAppend.lean` (hole C1 closes with this pull request; the file goes when the pin moves past ArkLib #615). A3 (round-by-round to plain knowledge soundness) is not consumed here; it is Layer 12's corollary. Feeds T4's ideal-oracle half. Tracks #12.

