
## G. Findings

Each with a name, a severity on the brief's scale, the evidence (sections above), a
classification for a divergence from leanVM, and the change to the blueprint (`bp` =
`docs/roadmap/protocol-blueprint.md` at `b435631`).

### 1. The instance is not `Ensemble.toM3` of the eight tables (major)

**Evidence.** `bp:803-805`: "`def leanIsaInstance (prog : Program) (s : Sizes) : M3Instance --
`Ensemble.toM3` of the eight tables with leanISA's separators and directions`"; `bp:77`:
"which `Ensemble.toM3` derives from any Clean `Ensemble`"; `bp:21`: "the polynomial view of
any Clean ensemble". Against it: decision 8 ("the fixed columns are `Coord.known` data",
`protocol-status.md:220-223`), the spine's `boundary` field and `Coord.known`
(`Spine/Instance.lean:86-98, 136`), leanVM's three framework blocks per side (`layout.rs
:352-395`; `08-end-to-end-protocol.tex:70`, "three blocks per side belong to no table") whose
program columns the verifier evaluates itself (`leaf.rs:453`), and section A.5: an instance
whose blocks are tables of `q` makes `satisfiedBy_witnessOf` unprovable (probe
`KnownColumn`). An `M3Instance` also needs `μ`, `layout`, `publicLines`, `aux`, `Stmt`, none
of which a Clean `Ensemble` has, so no `Ensemble.toM3 : Ensemble → M3Instance` exists;
`Ensemble.toM3` is listed as an interface (`bp:1369, 1398`) and given no signature.
**Classification.** An error of the blueprint. **Change.** `bp:803-805`, as it stands: the
comment quoted. As proposed: "`Component.toM3` of the six opcode tables, with leanISA's
separators and directions and their count columns; three column groups for the shared
committed columns (`mem_0, mem_1, mem_2, cntfin_mem` at `2^logMem`; `cntfin_bc` at
`2^prog.logSize`; `q_flock` at `2^(τ_5 + 8)`), tables with no constraint, flush or count;
six boundary blocks written from `memTable`, `bytecodeTable` and `leanIsaVerifier prog` with
`idx ↦ Coord.known (idxColumn κ)`, the entry cells `↦ Coord.known (bytecodeSlotColumn prog k)`,
the sentinel `↦ Coord.const prog.finalPc`, the limbs and counts `↦ Coord.committed`; the
layout of `witness.rs:67-101`, `leaf.rs:53-156`; three public lines; `aux` the Flock predicate
of the region". Delete `Ensemble.toM3` from `bp:77, 1369, 1398` and from the sentence at
`bp:21`, or define it as the six-table part only.

### 2. No bridge lemma for the boundary blocks (major)

**Evidence.** Layer 2's two bridges are `toM3_constraints_iff` and `toM3_flushes_eq`
(`bp:775-777`), both about a Clean `Table` read as an instance *table*. The three balances
of `SatisfiedBy` range over `w.interactions`, which include the memory block's, the bytecode
block's and the verifier's rows (`FlatEnsemble.lean:225-226` at `93c9d1ef`;
`Statement.lean:207-209`); in the instance those are `boundaryTuples`, not `flushTuples`
(A.2, A.5). Nothing in Layers 2 or 3 states that the messages of `bytecodeRowOf prog i c`,
`memRowOf mem i c` and `leanIsaVerifier prog`'s row are the boundary tuples, coordinate by
coordinate. **Classification.** An error of the blueprint (omission). **Change.** Add to Layer
3 (`bp:810-819`): "`theorem boundary_tuples_eq (h₁ : IndexColumnsAreRowIndices w) (h₂ :
SeedRowsAreTheImage w) (h₃ : BytecodeRowsAreTheProgram prog w) (hs : Sizes.ofWitness w = some
s) : the multiset of sixteen-tuples of the messages of `w`'s memory block, bytecode block and
verifier row on each side = (leanIsaInstance prog s).boundaryTuples (stackOf gen w hs) side`",
and its use in both adaptor theorems; add to Layer 2's tests "the three block components
against their boundary blocks on the one-row witness". Reason: without it neither direction of
the adaptor can be proved, and it is the one place the program's `known` columns meet the
program's rows.

### 3. The base soundness theorem omits `WellFormedBytecode`, and is not a statement about `verify` (major)

**Evidence.** `bp:1247-1248`: "`theorem baseVerifier_extractsExecution (fs bcs mca flock)
(h : verify prog input proof = true) : except with probability niError, ∃ t, ValidExecution
prog input t`", "composes … `constraintSoundness`" (`:1253-1254`); `constraintSoundness (hwf :
WellFormedBytecode prog)` (`leanisa-blueprint.md:1163`; `architecture.md:224-228`;
`docs-debt.md` B.6). The `JUMP`-sentinel program has two rows that are steps and balance the
state channel with no `ValidExecution` for the image (`tests/LeanerVMTests/Semantics/
Execution.lean:415-461`, proved), so the theorem is false without the hypothesis. The
"except with probability" attaches to `verify prog input proof = true`, a closed Boolean of
the concrete BLAKE2s verifier, which has no probability; the theorem must be about the
random-oracle verifier of `verify_iff_compiled`, and the step to the concrete `verify` is the
random-oracle heuristic, stated nowhere (section C). The conclusion mentions no extracted
witness, so the statement is a soundness statement for a language (E.6, probe `Transport`
examples 3-4). **Classification.** An error of the blueprint. **Change.** `bp:1247-1248` as
proposed:

```lean
/-- Base soundness, in the random-oracle model: for a well-formed program and an input on
which no execution exists, every prover with at most `Q` oracle queries makes the
Fiat–Shamir-compiled verifier of `leanIsaInstance prog s` accept with probability at most
`niError Q` (the maximum over admissible `s`; finding 6). `verify` is that verifier with the
BLAKE2s chain in place of the oracle (`verify_iff_compiled`), which is a heuristic and not a
theorem. -/
theorem baseVerifier_sound (fs bcs mca flock) (hwf : WellFormedBytecode prog)
    (hno : ¬ ∃ t, ValidExecution prog input t) : ∀ prover, Pr[compiled verifier accepts] ≤ niError Q
/-- Pointwise, for the extractor's stack: what recursion consumes (T6). -/
theorem execution_of_extracted (hwf : WellFormedBytecode prog) (hs : s.Admissible prog)
    (h : M3Holds (leanIsaInstance prog s) input q) :
    ∃ t, AssignmentRepresents (witnessOf prog s q) t ∧ ValidExecution prog input t
```

and in the prose: who establishes `WellFormedBytecode` (the compiler, `lean_compiler/src/
lib.rs:162`, `filler.rs`; a check of T3 on the exact guest), and that the random-oracle
instantiation is a hypothesis of the deployment, not of any theorem. The same two edits in the
tracker's K4 section (`hole-comment.md:190`).

### 4. The base completeness theorem is false without resource hypotheses and needs a witness generator (major)

**Evidence.** `bp:1249-1250`: "`theorem baseProver_complete (hfill : HasFillBlocks prog) (h :
ValidExecution prog input t) : verify prog input (prove prog input (witness of t)) = true`",
"composes `constraintCompleteness`, `m3Holds_stackOf`, `piop_perfectCompleteness` and the
determinism of the Fiat–Shamir chain" (`:1255-1257`). (a) `HasPublicBoundary` allows `κ =
32` (`Execution.lean:108-110`); a valid execution at `κ = 16` is one at `κ = 32` with the
image extended by zeros (the same run); its four memory columns hold `4 · 2^32 = 2^34 >
2^28` cells, and the verifier rejects `μ > 28` (`cpu/mod.rs:174-176`, `pcs.rs:51`;
`verifier.py:1379`); `AssignmentRepresents` fixes `κ` (`Statement.lean:358`), so no witness of
`t` is provable. (b) `constraintCompleteness` gives `∃ w`; "`witness of t`" is a function
the blueprint excludes (T2 out of scope, `bp:147-148`). (c) `constraintCompleteness` takes
`WellFormedBytecode prog`, not `HasFillBlocks prog` (`leanisa-blueprint.md:1165`). (d) The
rate is not chosen by `t`. **Classification.** An error of the blueprint. **Change.**
`bp:1249-1250` as proposed:

```lean
/-- Base completeness: a satisfying witness whose sizes are admissible and any valid rate give
a proof `verify` accepts. -/
theorem baseProver_complete (gen : FlockWitnessGen) (hwf : WellFormedBytecode prog)
    (h : SatisfiedBy prog input w) (hs : Sizes.ofWitness w = some s) (hadm : s.Admissible prog)
    (hρ : validRate ρ) : verify prog input (prove gen prog input w ρ) = true
/-- With leanISA's existence theorem: a valid execution that some admissible-size witness
represents has an accepted proof. -/
theorem baseProver_complete_of_execution (hwf : WellFormedBytecode prog)
    (h : ValidExecution prog input t)
    (hfit : ∃ w s, SatisfiedBy prog input w ∧ AssignmentRepresents w t ∧
      Sizes.ofWitness w = some s ∧ s.Admissible prog) : ∃ proof, verify prog input proof = true
```

and in the prose: "The resource condition `architecture.md:273-275` asks for is `hfit`: the
stacking window forbids `κ > 26` and long runs; `constraintCompleteness` alone does not give
admissible sizes (and, as sketched, has no resource hypothesis of its own, note 18)". Ask the
leanISA roadmap (`Boundaries`, `bp:1433-1441`) for a `constraintCompleteness` that returns a
witness of *minimal* heights, or accept `hfit` as T4's hypothesis. The same in the tracker's
K4 section.

### 5. `Sizes`, `Sizes.ofWitness` and `admissible_iff_caps` cannot be stated as written (major)

**Evidence.** `bp:795-801`. `logInvRate` is announced (`cpu/mod.rs:118-124`, `verifier.py
:1372-1376`; not in the specification's Setup, `08-end-to-end-protocol.tex:55`) but no witness
determines it, so `Sizes.ofWitness w : Option Sizes` is ill-defined; `admissible_iff_caps :
s.Admissible prog ↔ (Caps w ∧ Sizes.ofWitness w = some s)` has a free `w` and, quantified,
is false in both directions (`Caps` lacks the `μ` and rate windows, `Statement.lean:79-81`;
another `w` has other sizes); `Sizes.ofWitness (w : EnsembleWitness leanIsaEnsemble)` lacks
`prog` (`bp:799`); `leanIsaInstance_fits` uses `layout.total` (`bp:808`), a field `Layout` has
not (`code-layer1.md` G.2). `gt-bus.md` G4 has the caps side. **Classification.** An error of
the blueprint. **Change.** `bp:795-808` as proposed:

```lean
structure Sizes where (logMem : ℕ) (τ : Fin 6 → ℕ)                 -- the family index
def Sizes.ofWitness (w : EnsembleWitness (leanIsaEnsemble prog)) : Option Sizes
def leanIsaBlocks (prog) (s) : Blocks ; def leanIsaμ (prog) (s) : ℕ  -- witness.rs:67-101
theorem leanIsaBlocks_fits : (leanIsaBlocks prog s).total ≤ 2 ^ leanIsaμ prog s
def Sizes.Admissible (prog) (s) : Prop  -- 16 ≤ logMem ≤ 32, τ j ≤ 32, 3 ≤ τ 5, leanIsaμ prog s ≤ 28
def validRate (ρ : ℕ) : Prop := 1 ≤ ρ ∧ ρ ≤ 4                        -- whir_config.rs:48-55, Layer 12
theorem caps_of_admissible (hs : s.Admissible prog) (q) : Caps (witnessOf prog s q)
theorem sizes_of_satisfiedBy (h : SatisfiedBy prog input w) : ∃ s, Sizes.ofWitness w = some s
```

Reason: the instance depends on the heights alone; the rate is Layer 12's; the two lemmas
are what the two directions use.

### 6. The composition over the prover's announced sizes is unspecified (major)

**Evidence.** Section B.3: `verify_iff_compiled` quantifies `∃ s` (`bp:1218-1221`),
`verify_knowledgeSound`'s error is `niError s Q` (`bp:1226-1227`), the per-instance theorems
bound one `s`, and ArkLib's `ProtocolSpec n` cannot express a protocol whose schedule depends
on a first message. A union over the admissible sizes costs about `2^34`; the `Q · max ε`
bound needs `FiatShamirSecurity` stated for the family with `s` in the hashed input.
**Classification.** An error of the blueprint (a missing decision). **Change.** In *Statements
and parameters* (`bp:316`) add: "The sizes are the prover's. The non-interactive theorem is
stated for the family: its error is `niError Q := max over admissible s of niError s Q` (or
the sum, if the interface is per instance), and `FiatShamirSecurity` is the family form, the
challenge oracle taking the announced sizes with the statement". In Layer 12 (`bp:1226-1227`)
replace `niError s Q` by that. In acceptance test 21 (`bp:1326-1328`) add "the error of
`verify` does not depend on the prover's choice".

### 7. The instance depends on a Flock interface that depends on the instance (major)

**Evidence.** `bp:846-848`: the instance's layout takes its slot map from
`FlockInterface.limbColumns`, and `structure FlockInterface (I : M3Instance)` (`bp:1077`);
`aux` of `leanIsaInstance` must be Flock's R1CS (decision 12), which only #3 defines; the
consequence lemma "R1CS ⇒ the limbs compress" that `satisfiedBy_witnessOf` consumes
(`bp:855-857`) has no carrier in any signature (`satisfiedBy_witnessOf`'s arguments,
`FlockInterface`'s fields, `FlockWitnessGen`). `gt-flock-ring.md` 8.2 and 8.3 propose the
split; `code-layer1.md` G.1 the reader. **Classification.** An error of the blueprint.
**Change.** Layer 3 takes, and #3 supplies, one instance-free structure:

```lean
/-- What the adaptor needs of Flock, none of it mentioning an instance. -/
structure FlockSpec where
  slot : Fin 18 → Fin 256                                   -- hash_flock.rs:87-115
  Holds (kBatch : ℕ) : Column (8 + kBatch) → Prop            -- the R1CS on the packed column
  decHolds : ∀ k, DecidablePred (Holds k)
  compress_of_holds : Holds k c → ∀ j, Blake2sRelation (limbs read at slot j of c)
  gen : (rows : List (Blake2sRow K)) → Column (8 + kBatch)   -- keeps the limbs in their slots
  holds_gen : (∀ r ∈ rows, Blake2sRelation r) → Holds k (gen rows)
```

`leanIsaInstance (F : FlockSpec) prog s` uses `F.slot` in its layout, `F.Holds` as `aux`;
`satisfiedBy_witnessOf` uses `F.compress_of_holds`; `stackOf` uses `F.gen`,
`m3Holds_stackOf` uses `F.holds_gen`; `FlockWitnessGen` and `FlockInterface.limbColumns` are
deleted; the phase-level `FlockInterface` keeps the reduction and its two proofs and takes the
`FlockRegion I` of `gt-flock-ring.md` 8.3, whose `aux_iff` is `F.Holds`.

### 8. The polynomial bridge of Layer 2 is noncomputable at the pin (major)

**Evidence.** Section E.5: `bp:762-771` produce Mathlib `MvPolynomial`s; the instance holds
`CMvPolynomial`s (`Spine/Instance.lean:123-125`); `toCMvPolynomial` is `noncomputable def`
(CompPoly `3468b38c`, `MvPolyEquiv/Core.lean:41`; unchanged in kind at `572f9973`, unverified);
`M3Holds` is meant to be decided by evaluation and `verify` to be computable (`bp:866-867,
1230-1231`). Probe `PolyBridge`: the direct translation is computable and agrees with
`Expression.eval`. **Classification.** A deviation forced by an upstream library, with a
workaround: the direct translation; retired if CompPoly makes `toCMvPolynomial` computable.
**Change.** `bp:762-767` as proposed: "`def Expression.toCMvPolynomial (n) : Expression K →
CMvPolynomial n K` (var `i < n` ↦ `X i`, else `0`, as `Environment.fromArray` reads a missing
cell); `theorem eval_toCMvPolynomial (row) (e) : (e.toCMvPolynomial n).eval (fun i ↦
row[i]?.getD 0) = e.eval (Environment.fromArray row data)`; `theorem
fromCMvPolynomial_toCMvPolynomial (e) : fromCMvPolynomial (e.toCMvPolynomial n) =
rename … e.toMvPolynomial`, through which `degreeBound` bounds `totalDegree`
(`totalDegree_equiv`)". `M3Table`'s fields become `CMvPolynomial`; `Direction` becomes `Side`
(or the spine adopts leanISA's `Direction`). Clean #466 (`Expression.toMvPolynomial`) stays the
proof-side bridge.

### 9. The column-only tables enter the generic table sumcheck's schedule (major)

**Evidence.** Section E.4; `bp:836-839` (the six shared columns are "tables of the instance
with no constraints and no flushes"); Layer 7's `τ_max`, "one value per column of every
table" (`bp:987-989`; `08-end-to-end-protocol.tex:76-77`; `constraints.rs:250`, the six
tables); `gt-bus.md` G16. A phase over the abstract `I` that ranges over all of `I.ntab` has
a different transcript from leanVM's on the leanISA instance, which `verify_iff_compiled`
would then fail. **Classification.** An error of the blueprint (a consequence of the
modelling choice, unstated). **Change.** In the spine's conventions (`bp:316`, or a new row
*Column groups*): "A table with no constraint, no flush and no count column is a column
group: it takes no part in the table sumcheck (no round, no term, no column value) and its
columns receive claims from the boundary blocks, the public lines and the Flock phase only.
`M3Instance.active j := (I.constraints j ≠ []) ∨ (I.flushes j ≠ []) ∨ (I.counts j ≠ [])` is
the criterion, decidable, and Layer 7 ranges over it." In Layer 7 (`bp:987`): `τ_max` and
`Σ_j width_j` over the active tables.

### 10. `witnessOf_stackOf` has no Lean statement (minor)

**Evidence.** Section E.2; `bp:819` ("`= w -- on the committed fields`"), `bp:1339`
("`#guard witnessOf (stackOf w) = w`"), `bp:866-867`. `EnsembleWitness` has a function field
and a free width and no `DecidableEq`. **Classification.** An error of the blueprint.
**Change.** `bp:819` as proposed: the statement of E.2 (`rowCells`, the three equalities
under `SatisfiedBy` and `Sizes.ofWitness`), and `bp:1339`: "`#guard` of those three
equalities on the one-row witness". Say in `bp:822-824` that neither T4 composition uses it.

### 11. `witnessOf` has no `input`, and the count columns have no derivation (minor)

**Evidence.** `bp:813-814`; `bp:773-777` (`Component.toM3 (c) (sep) (dir)` with a `count`
field and no rule); `layout.rs:412-414`; A.4 rows 1 and 4. **Classification.** An error of
the blueprint (imprecision). **Change.** `bp:813`: either add `(input : PublicInput)` to
`witnessOf` (the `Refinement.map` has the statement) or say "the lanes are read off cells 0
and 1 of `mem_0`, `mem_1`". `bp:773-774`: `Component.toM3 (c) (sep) (dir) (lookups :
List (RawChannel F))` with "`count` is coordinate 2 of every pull on a channel in `lookups`,
required to be a variable (`vars_lt_width`'s sibling `count_is_var`)", and the test "the
count columns of the six tables are those of `count_columns()` (`layout.rs:412-414`)".

### 12. `leanIsaInstance` must be reducible (minor)

**Evidence.** Probe `DefInstance`: the adaptor's statement elaborates on a `def` instance,
but no `Decidable` instance is found for `M3Holds (inst …) input q`, while the `abbrev` passes;
the toy is an `abbrev` for that reason (`Spine/Toy.lean:94-95`); the Layer 3 tests decide
`M3Holds` (`bp:866-867`). **Classification.** An error of the blueprint (omission of a
constraint on the code). **Change.** `bp:803`: "`abbrev leanIsaInstance …`, reducible, so that
`Decidable (M3Holds (leanIsaInstance prog s) input q)` and the instances on `I.Stmt` are found
by instance search, as the toy is".

### 13. `Refinement.map_option_valid` has the wrong polarity for ArkLib's game (minor)

**Evidence.** E.6; `Refinement.lean:55-57`; `Security/Basic.lean:316` at `dca90385` (the bad
event is `∀ w ∈ w?, (x, w) ∉ relIn`); probe `Transport`, `bad_of_bad`. Harmless (a case split on
the `Option` converts), and `code-spine.md`'s `knowledge_transport` is the probabilistic form.
**Classification.** Imprecision. **Change.** `bp:552` and `bp:582-586`: name
`Refinement.knowledge_transport` (the event form, `code-spine.md`) as what T4 composes, and
keep `map_option_valid` as the pointwise lemma of the honest direction; the T4 line at
`bp:407` becomes "`T4 = verify_knowledgeSound ∘ Refinement.knowledge_transport
satisfiedBy_witnessOf ∘ constraintSoundness`", and the tracker's
`knowledgeSound_of_refinement` (`hole-comment.md:190`) the same.

### 14. Stale names (minor)

**Evidence.** `bp:220` `StateMsg` (the state message is `Regs`, `Channels.lean:138-141`;
no `StateMsg` exists); `bp:1280` `leanIsaTables` (no such declaration; the ensemble is
`leanIsaEnsemble`); `bp:799` `EnsembleWitness leanIsaEnsemble` (needs `prog` since decision
14); `bp:808` `layout.total`; the tracker's `knowledgeSound_of_refinement`. **Change.**
Replace each by the name that exists.

### 15. Two deployed checks are discharged by type, and nobody is told to parse (minor)

**Evidence.** B.2 item 2: `read_public`'s checks (2) (the public words' third limb, `cpu/mod.rs
:141-143`) and (3) (the bytecode length and, in the Python, decodability) are "by type" in
Lean (`Statement.lean:71-75`); `verify : Program → PublicInput → Proof → Bool` (`bp:1217`)
takes the typed values; the fixture (`bp:1236-1240`) and T7's `PublicInput.encode` are the
parsers. **Classification.** An error of the blueprint (omission). **Change.** In *Verifier
shape* (`bp:326`) add: "`verify` takes a `Program` and a `PublicInput`; the deployed
verifier's rejection of a public word with a nonzero third limb and of a bytecode that is not
`2^k ≤ 2^32` decodable instructions are the obligations of whoever builds those values from
bytes (the fixture's loader in Layer 12, `PublicInput.encode` in T7), and the differential
fixture records a rejected public input as a parse failure, not as `verify = false`".

### 16. T4 drops the extracted witness that T6 needs (note)

**Evidence.** Section F, last paragraph; `architecture.md:332-335`. **Change.** The second
theorem of finding 3's proposal (`execution_of_extracted`).

### 17. The protocol's soundness is non-adaptive in the statement (note)

**Evidence.** B.3, last paragraph: ArkLib's games quantify `∀ stmtIn` outside the probability
(`Security/Basic.lean:299-323`); T7's public input has a prover-chosen part
(`architecture.md:191-195, 357-358`). **Change.** Record in `bp`'s *Out of scope* that
adaptive statement soundness in the random-oracle model (the input seeds the chain, `cpu/mod.rs
:712`) is T7's to state and is not given by the per-statement theorems of this roadmap.

### 18. `constraintCompleteness` needs a resource hypothesis of its own (note, leanISA's)

**Evidence.** Section C: `Caps.heights` bounds every table by `2^32` rows
(`Statement.lean:257`), `ValidExecution` bounds only `κ` (`Execution.lean:108-115`), and a
halting run visits distinct `(pc, fp)` states (the step is a function of the state and the
fixed image), so a run of more than `2^32` steps of one opcode has no satisfying witness.
Out of this review's scope; it reaches T4 through finding 4. **Change.** Report to the leanISA
roadmap (`Boundaries`, `bp:1433-1441`).
