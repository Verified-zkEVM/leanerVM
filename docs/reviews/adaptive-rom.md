# Review: the adaptive random-oracle theorems

> An archive of the review of the branches `stack/46-statement-hashes`, `stack/47-start-reader`
> and `stack/48-adaptive-rom` at `c3721ee4` (plus the staged move of `programBytes_injective`),
> against the adaptive branch `af5855a7`. The review was a specification review by a fresh agent,
> read-only, of the statements: the statement seeds and their reader, the in-play slot, the
> generic bound, the core, the adaptive and fixed-statement theorems, and the documents. What is
> accepted from it is text of the [protocol blueprint](../roadmap/protocol-blueprint.md), which is
> the specification. Findings are numbered by severity.

**Disposition**:

| Finding | Disposition |
| --- | --- |
| 1. the fixed-statement hypothesis `BlakeMisbehaves` changed meaning without a word: with the statement-free reader its flips counted on the chain of every statement the log opens, a strictly stronger hypothesis (an adversary that explores a cheating chain of another statement and then outputs an honest proof met the old one at `δ = 0` and failed the new one) | met in Lean, not only in the documents: `SlotReader.FlipFor st` counts the flips on the chains from a start that opens `st`; `core` concludes `HashMisbehavesFrom [] (rootsOf prog input) (leanVmReader.FlipFor (prog, input))`; `BlakeMisbehaves` and `BlakeMisbehavesAdaptive` read the flips on the chosen statement's chain; the random-oracle bounds still bound the statement-free event, which contains it (`flip_of_flipFor`, `HashMisbehavesFrom.mono`); a toy reader with two starts shows the restriction (`not_flipAtFor_true`); decision 43, Layer 13 and the status page state the change of the hits (the verifier's seed queries in the log, the program-hash slot in play, the first state no longer in play from the start) |
| 2. `StatementSeeds.lean`, not allowed to meet the arithmetization, used its bytecode encoding (`entry_injective`, `encodeSlots_getElem`) through a transitive import | met: `programBytes_injective` moved to `Transcript.lean`, which defines `programBytes` and is allowed; `StatementSeeds.lean` opens no arithmetization namespace (`ff801fd9`) |
| 3. stale documents: the deleted `Hit` and `HashMisbehaves` named in the blueprint and `LogScan.lean`; the new declarations missing from the inventories; the trust surface naming the selective headline; the `Flip` sketch contradicting its comment; a garbled sentence on `misbehaves_rom_coins` | met: the names replaced, the inventories extended (random-oracle and Layer 13 rows), the trust surface names `baseVerifier_extractsWitness_adaptive` and the definitions the hypothesis now depends on (`SeedLogged`, `stmtOf`, a classical choice, `programHashSlot`), the sketch defines `FlipFor` and `Flip` from it, and the sentence says that no random-oracle form exists for an adaptive adversary with coins |
| 4. hygiene: a proof line of 108 characters, a test comment about the history of the change, two overlong document lines | met (`1ce73fa1`, `a8f76375`) |
| the observations | the events are at the chosen statement and the three seed queries are counted (13700); an honest run meets the hit clauses (the scan finds none on the test vector); a log opens a wrong statement only through a collision, which the event contains; `StartsSafe []` is used by `charge_le` against double charging and is not vacuous; older status entries keep their names as a record |

Files read in full by the reviewer: `Headline.lean`, `AdaptiveGame.lean`, `StatementSeeds.lean`,
`RandomOracleGame.lean`, `RandomOracle.lean`, `ChainGroups.lean`, `RandomOracleBound.lean`,
`HashMisbehaves.lean`, `LeanVmReader.lean`, `Transcript.lean`, `Verify.lean`, `Core.lean`,
`Prove.lean`, the changed tests, `scripts/check-layers.sh` and the changed documents. After the
fixes, `./scripts/validate.sh` passes, `#print axioms` of every headline theorem gives `propext`,
`Classical.choice` and `Quot.sound`, `leanervm-prove` writes the test vector byte for byte, and
`leanervm-prove log` finds no collision and no hit.
