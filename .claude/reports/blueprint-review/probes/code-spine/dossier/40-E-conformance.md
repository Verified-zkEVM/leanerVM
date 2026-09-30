## E. Conformance with the blueprint

All blueprint lines are those of `docs/roadmap/protocol-blueprint.md` at `b435631`; all Lean
lines those of `main` at `b435631`.

### E.1 The Lean sketch (`:442-554`) against the code, declaration by declaration

The sketch is a compressed transcription of the code and matches it in every name, field and
signature it gives, with the following differences (none changes a statement):

| Sketch | Code | Difference |
| --- | --- | --- |
| `:445` `structure Shape where (ntab : ℕ) (τ width : Fin ntab → ℕ)` | `Instance.lean:57-63` | none (compressed) |
| `:447-450` `Layout … read_eval : ∀ q c z, eval₂Mle (read q c) z = eval₂Mle q (extend c z)` | `:79-81` | the code's law is on `.values` with `algebraMap K E`; same statement |
| `:451` `Coord … known (col : Column κ)` | `:86-89` | none |
| `:453-454` `PublicLine … (sent : Bool) (pos : 0 < S.τ col.1)` | `:102-114` | none |
| `:455-466` `M3Instance` | `:119-148` | the sketch omits `decAux`'s `attribute [instance]` (`:150`); otherwise field for field |
| `:467` `def M3Instance.column I q c ; def M3Instance.row I q j x ; def M3Instance.tuples I q (s : Side)` | `:160, 163, 185` | the sketch omits `κ`, `coordCell`, `flushTuples`, `boundaryTuples` (`:157, 167, 174, 180`), which `tuples` unfolds to and an auditor must read |
| `:468` `Balanced I q (List.Perm)` | `:201` | none |
| `:469-471` `M3Holds`, `deriving instance Decidable` | `:219-223` | none |
| `:472` `abbrev TheOracle I : Fin 1 → Type := fun _ ↦ Column I.μ` | `:226` `OneOracle (Column I.μ)` | same type |
| `:473` `M3Rel` | `:230-231` | none |
| `:476-484` claims and outputs | `Seams.lean:57-151` | `Weight`'s `mle : Vector E μ → E` and `mle_eq` are elided as `…`; the `.Holds` of each claim (`:66, 98, 123`), `VirtualTerm.table`, `VirtualTerm.eval` and `Weight.pair` (`:82, 87, 112`) are not in the sketch and are load-bearing |
| `:485-490` seams | `:166-191` | `Seam.table/pub/flock/done` are summarised in words; the code is as summarised |
| `:493-498` `KnowledgeAppend` | `KnowledgeAppend.lean:474-478, 510-518` | `rbrKSWorstCaseWith` is an abbreviation of the sketch for `rbrKnowledgeSoundnessWorstCaseWith`; otherwise as stated |
| `:501-513` `Component.Def/Complete/Security` | `Component.lean:52-106` | the sketch writes `Extractor.RoundByRound []ₒ …`; the code writes `OracleSpec.emptySpec.{0, 0}` to pin a universe (`:96-99`), and says so |
| `:514-515` the three `append`s | `:143, 162, 174` | the sketch omits `guardedAppend` and `stateFunctionOfEq` (`:156, 110`), which `Security.append` unfolds to |
| `:517-521` pass-through, send-oracle | `PassThrough.lean`, `SendOracle.lean` | the sketch omits `sendOracle_relOut`, `sendVerifierPure`, `sendStateFunction`, `sendWitMid` (`SendOracle.lean:71, 101, 145, 130`), all in the knowledge theorem's statement (section B) |
| `:523-525` `Phase.*` | `Phase.lean:37-74` | none |
| `:528-548` `Compose.lean` | `Compose.lean:51-185` | none; the sketch's comment on `piopExtractor`, "commitExtractor, then the phases'", is right of `extractMid` and wrong of `extractOut` (D.5) |
| `:551-553` `Refinement` | `Refinement.lean:31-71` | none |

**Names the sketch or the interface list (`:1365-1385`) give that do not exist under that name
or signature on `main`:** none in the spine block of the list (`:1366-1385`) — every name was
found (`Side` … `Toy.layout`), except that the list names `Ensemble.toM3 (Layer 2)` (not
built, marked) and `Component.Security.{witMid, extractor, kSF, rbr}` (fields, exist).
**Public declarations of the reviewed modules that the list does not name:** `M3Instance.κ`,
`M3Instance.coordCell`, `flushTuples`, `boundaryTuples`, `M3Instance.decAux` (as an
instance), the five `.Holds`, `VirtualTerm.table`, `VirtualTerm.eval`, `Weight.pair`,
`Component.stateFunctionOfEq`, `rbrKnowledgeSoundnessWorstCaseWith_of_eq`,
`Component.guardedAppend`, `Component.passThroughProver/Verifier/Pure/Extractor/StateFunction`,
`passThrough_materializeOutput`, `passThroughVerifier_toVerifier_run`, `passThrough_rbr`,
`Component.passThroughComplete`, `Component.sendSpec/sendProver/sendEmbedding/sendVerifier`,
`sendOracle_relOut`, `sendOracle_outputPure`, `send_materializeOutput`,
`sendVerifier_toVerifier_run`, `sendVerifierPure`, `sendOracle_complete`,
`sendOracleComplete`, `sendWitMid`, `sendExtractor`, `sendStateFunction`, `sendOracle_rbr`,
`sendOracleSecurity`, `noOracle_eq`, `Refinement.id`, `Refinement.comp`,
`Verifier.GuardedForm.of_probEvent_pos`, `Reduction.mem_support_run_of_guarded`,
`keepOracles`, `OracleVerifier.materializeOutput_of_keepOracles`, everything in
`KnowledgeAppend` but the two named theorems, `Toy.Col`, `Toy.slice`, `Toy.extend`,
`Toy.read_eval`, `Toy.constraint`, `Toy.flush`, `Toy.boundary`. The list's sentence
"Everything not listed is a proof, a helper, or a test" (`:1419`) is false of the fourteen of
these that section B counts as load-bearing (the `.Holds`, `table`, `eval`, `pair`,
`coordCell`, the two tuple lists, `sendOracle_relOut`, `sendVerifierPure`,
`sendStateFunction`, `sendWitMid`, `guardedAppend`, `stateFunctionOfEq`).

### E.2 The blueprint's other statements of the same objects

| Object | Where | As stated there | The spine as built | Which the code implements |
| --- | --- | --- | --- | --- |
| the knowledge theorem | headline `:14-16` | `piop_rbrKnowledgeSoundness (I : M3Instance) : for every prover, leanVmVerifier accepts → except with probability piopError I, the extractor's column q satisfies M3Holds I input q` | `(P) (S : P.Security) init impl : (leanVmVerifier P).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl (M3Rel I) (Seam.done I) S.toDef.witMid (piopExtractor P S) (S.toDef.kSF init impl) (piopError P)` | the spine's; the headline's has no `P`, `S`, a numeric `piopError I`, and a plain-form conclusion |
| the knowledge theorem | Layer 10 `:1127-1129` | `piop_rbrKnowledgeSoundness (hs : s.Admissible prog) : (leanVmVerifier prog s input flock).rbrKnowledgeSoundness init impl (m3Relation prog s) Set.univ (piopError s)` | as above | the spine's; Layer 10's is over `prog s input flock`, has an admissibility hypothesis, the existential and averaged `rbrKnowledgeSoundness`, the relation `m3Relation prog s`, `Set.univ` for `Seam.done`, and `piopError s`. The text at `:1104-1106` says these are "the spine's, stated over `Phases I`", contradicting the block below it |
| the completeness theorem | headline `:12-13`; Layer 10 `:1124-1126` | `(I) : M3Holds I input q → the honest prover makes leanVmVerifier accept with probability 1`; `(hs : s.Admissible prog) : (leanVmPiop prog s input flock).perfectCompleteness init impl (m3Relation prog s) Set.univ` | `(P) (C : P.Complete) init impl : (leanVmPiop P).perfectCompleteness init impl (M3Rel I) (Seam.done I)` | the spine's; Layer 10's admissibility hypothesis is not in the code and is not needed (the sizes are inside `I`) |
| `leanVmPiop` | Layer 10 `:1116-1119` | `leanVmPiop (prog) (s) (input) (flock : FlockInterface prog s) : OracleReduction []ₒ (StmtIn := PublicInput) (OStmtIn := fun _ : Empty ↦ Unit) (M3Witness prog s) (StmtOut := Unit) (OStmtOut := fun _ : Empty ↦ Unit) Unit (pSpec := …) := commitPhase ⟫ busPhase ⟫ tableSumcheck ⟫ publicInputPhase ⟫ flock.reduction ⟫ openingPhase` | `leanVmPiop (P : Phases I) : OracleReduction []ₒ I.Stmt NoOracle (Column I.μ) Unit (TheOracle I) Unit P.toDef.pSpec := P.toDef.red` | the spine's; `input` is not an argument (it is the statement), the oracle families are `Fin 0`/`Fin 1` not `Empty`, the witness is `Column I.μ` not `M3Witness prog s`, the output oracle is the stack not `Unit`, and the phases are fields of `P`, not named definitions |
| `piopError` | conventions `:318`; Layer 10 `:1122`, `:1130` | "the closed form is a `def` next to the theorem, and the interactive error is its sum"; `piopError (s : Sizes) : (pSpec …).ChallengeIdx → ℝ≥0`; `piopError_le (hs) : Σ i, piopError s i ≤ 2 ^ 40 / |E| + flockError` | `piopError (P : Phases I) := P.toDef.err`; no bound | the spine's (finding *the declared error is unconstrained*) |
| `BusOut` | Layer 6 `:960-964` | `structure BusOut where ζ : Fin μ_bus → E ; rem : Fin 3 → E ; pool : List Claim ; α : Fin 4 → E ; β : E` | `structure BusOut (I) where linear : List (LinearClaim I) ; columns : List (ColumnClaim I)` (`Seams.lean:130-134`) | the spine's; Layer 6's carries the challenges and the three totals, the spine's carries claims (the sibling dossier proposes the shape between the two) |
| `busPhase.relOut` | Layer 6 `:965-966` | `{…| (∀ j, Σ_x eq(ζ_{<τ_j}, x) · B_j^s(x) = rem s) ∧ every pooled claim holds for q ∧ (count root ≠ 0)}` | `Seam.bus` (`:175-177`) | the spine's; Layer 6's has no zerocheck claims, no lines, no `aux`, a count-root conjunct, and the forms as one equation per side |
| the table phase's statement types | Layer 7 `:988` | `tableSumcheck (prog) (s) : OracleReduction []ₒ (StmtIn := BusOut) … (StmtOut := BusOut × ColumnClaims)` | `Phase.Def I (I.Stmt × BusOut I) (I.Stmt × TableOut I)` (`Compose.lean:78`) | the spine's; Layer 7's output keeps `BusOut` |
| `FlockInterface` | Layer 9 `:1077-1085` | `reduction : OracleReduction []ₒ (StmtIn := ColumnClaims) (OStmtIn := fun _ : Unit ↦ Column μ) Unit (StmtOut := WeightedClaim) … pSpecFlock ; limbColumns ; relIn ; relOut ; perfectCompleteness ; rbrKnowledgeSoundness : … rbrKnowledgeSoundnessWorstCase … flockError ; flockError_le` | `Phases.flock : Phase.Def I (I.Stmt × PubOut I) (I.Stmt × FlockOut I)` with `Phase.Complete`/`Phase.Security` at `Seam.pub`/`Seam.flock` | the spine's; Layer 9's has its own relations, the existential `rbrKnowledgeSoundnessWorstCase` (no named extractor), a single `WeightedClaim` output, and an oracle family over `Unit` |
| `Weight` | Layer 10 `:1109` | `structure Weight (μ) where (onCube : ETable μ) (mle : (Fin μ → E) → E) (mle_eq : ∀ r, mle r = evalMle onCube r)` | `Weight (μ : ℕ) … mle : Vector E μ → E` (`Seams.lean:103-109`) | the spine's: points are `Vector E μ` (convention *Hypercube* `:312`), not `Fin μ → E` |
| `WeightedClaim` | Layer 10 `:1110`; Layer 11 `:1173` | `WeightedClaim (μ) where (W : Weight μ) (c : E)`; `whirOpen … (StmtIn := Fin J → WeightedClaim μ)` | `WeightedClaim (I : M3Instance) where weight : Weight I.μ ; value : E` (`:116-120`) | the spine's: indexed by the instance, fields `weight`/`value`; Layer 11's `WeightedClaim μ` does not exist |
| the opening phase's statement | Layer 10 `:1112` | `openingPhase (μ) (J : ℕ) : OracleReduction []ₒ (StmtIn := Fin J → WeightedClaim μ) … (StmtOut := Unit)` | `Phases.opening : Phase.Def I (I.Stmt × FlockOut I) Unit` | the spine's; the input carries column claims and weighted claims as lists, and the statement |
| the extractor | conventions `:334`; `:100-101`; `:1133-1135`; acceptance test 24 `:1333-1340` | "the commit phase's (which reads the stack off the oracle message) followed by the phases'"; "`piopExtractor`, which reads the stack `q` off the oracle message, followed by `witnessOf`"; "the spine's test proves by `rfl` that `piopExtractor` returns the committed stack" | `piopExtractor P S := S.toDef.extractor`, ArkLib's `RoundByRound.append` nested five times | the spine's; the words are right of `extractMid` at round 0 and wrong of `extractOut` (D.5) |
| the relation ladder's transport | `:364-366`; `:582-586` | "along which knowledge transports at the same error (pointwise, `Refinement.map_option_valid`)"; "the probabilistic transport … is not proved … and has no consumer yet" | `map_option_valid` only | the spine's; the probabilistic form is three lines (D.7) |
| `Seam.done` | Layer 10 `:1144` | "`Set.univ` as the output relation says the last phase leaves nothing to check" | `Seam.done := of I fun (_ : Unit) _ ↦ True` (`:191`), equal to `Set.univ` (probe D.2) | the spine's; same set, different spelling |
| the hole interfaces | conventions `:332` | "a phase or generic component is two structures: `X.Def` (the reduction, its relations and its per-challenge error) and `X.Security`" | three: `Def`, `Complete`, `Security extends Complete`; the relations are not in `Def` but arguments of `Complete`/`Security` | the spine's |
| the relation of the first phase | conventions `:316` | "The relation of the first phase is `M3Rel I`, that is `M3Holds I input q` on the stack `q`" | `commitDef I` at `M3Rel I` | agree |

Layer 6's `BusOut`, Layer 7's types, Layer 9's `FlockInterface` and Layer 10's block are the
pre-spine sketches; the text around them (`:951-952`, `:983-984`, `:1103-1106`) says the
phases are "over `I : M3Instance`" and "the spine's", but the blocks were not rewritten. A
reader who trusts the blocks builds against types that do not exist. The sibling dossier
`gt-table-pub.md` records the same for Layer 7 (its finding *Layer 7's sketch and the
tracker's signature predate the spine*); we add Layers 6, 9, 10 and the headline.

**Proposed change** (one for all): replace each pre-spine block by a signature over the spine's
types — `busPhase (I) : Phase.Def I I.Stmt (I.Stmt × BusOut I)`, `busComplete`, `busSecurity`
at `Seam.commit`/`Seam.bus`; `tableSumcheck (I) : Phase.Def I (I.Stmt × BusOut I) (I.Stmt ×
TableOut I)`; `FlockInterface (I)` as the pair `Phase.Def I (I.Stmt × PubOut I) (I.Stmt ×
FlockOut I)` with its `Phase.Security` at `Seam.pub`/`Seam.flock`; `openingPhase (I) :
Phase.Def I (I.Stmt × FlockOut I) Unit`; delete Layer 10's `leanVmPiop … piopError_le` block
and point at the spine, keeping `piopError_le` restated over `I` (section F, first finding).

### E.3 Acceptance tests 24 to 28 against the code

| Test | Claim | Status on `main` |
| --- | --- | --- |
| 24, the extractor computes | `piopExtractor` is a definition whose `extractOut` reads the stack; witness the `rfl` test | `piopExtractor` and everything it unfolds to is computable (D.5, `isNoncomputable = false`); the `rfl` witness holds for zero-round phases only; a classical phase extractor would go unnoticed and would not matter (D.5) |
| 25, the wall | no module above the adaptor imports `LeanerVM.Arithmetization` | `git grep -n "import LeanerVM.Arithmetization" b435631 -- LeanerVM/Protocol` gives two hits: `LeanerVM/Protocol/FixedColumns.lean:11` (a listed exception, `:331`) and `LeanerVM/Protocol/Basic.lean:3` (`public import LeanerVM.Arithmetization.Basic`, an otherwise empty placeholder module from before the spine, not among the exceptions of convention *The wall*). The spine's own five modules and `ToArkLib/` import nothing from `LeanerVM/Arithmetization/`. Minor: delete `Protocol/Basic.lean` or list it. |
| 26, seams are the contract | the compositions typecheck only when the seams agree | true by construction (`Phases.Complete.toDef`, `Phases.Security.toDef`); the junk bundle of D.3 (b) also typechecks, so the test says nothing about content |
| 27, the toy is honest | the honest stack passes, each checkable clause fails alone | met by the tests; D.1 adds the multiplicity cases; the fifth clause is untestable on the toy |
| 28, the bus seam bounds the degree | `Seam.bus` carries `totalDegree ≤ I.d`, the cubic is rejected | met as a conjunct; its cost is a guard in the table phase (C.3) |
