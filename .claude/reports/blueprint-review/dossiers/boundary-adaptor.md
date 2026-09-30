# Dossier: the boundary between the proof system and the rest of the verification (task `boundary-adaptor`)

Written 2026-09-29/30. Object of the review: leanerVM `main` at `b435631`; every Lean line
number below is at that revision (`git show b435631:<path>`) unless another revision is named.
The arithmetization, semantics and parameters modules cited (`Statement.lean`, `Boundary.lean`,
`Channels.lean`, `Bytecode.lean`, `Memory.lean`, `Instruction.lean`, `Isa.lean`,
`Execution.lean`) are byte-identical between `b435631` and `144c5aa` (`git diff --stat`), and
`Spine/Instance.lean` differs by one import line. leanVM is at the pin `a386121f`
(`/home/scaraven/Documents/leanEthereum/leanVM`, verified `git rev-parse HEAD`). Library
facts are stated at the OLD pins (ArkLib `dca90385`, CompPoly `3468b38c`, Clean `93c9d1ef`),
the ones the reviewed revision builds against, read from `.lake/packages/` before the upgrade;
where the new pins (`144c5aa`: CompPoly `572f9973`, Clean `42fe4b26`, ArkLib `7653a901`)
matter, the text says so.

**Probes.** Six probe files under `.claude/reports/blueprint-review/probes/boundary-adaptor/`,
all run on 2026-09-29 against `main` at `b435631` with the old pins, under the shared lock; the
outputs are the `.out` files next to them and are reproduced in the appendix. `Shapes`,
`Transport`, `PolyBridge`, `KnownColumn` exited 0; `UniverseFail` and `DefInstance` are
expected failures and exited 1 with the recorded messages. After the upgrade no Lean can run
(brief §8); nothing was re-run. Two probes use numerals of `K` other than `0` and `1`
(`KnownColumn`: `2`; `PolyBridge`: `3, 5, 7`), which at the new CompPoly pin mean `0`, `1`,
`1`, `1`: their conclusions stand at the old pin, and a re-run at the new pin needs
`K.ofBits n` in place of the numerals (noted in the appendix). No file of any repository was
edited; nothing was posted; no checkout was moved; no build was started by this task.

## Summary

**What was examined.** The relation the proof system proves, `M3Holds I input q` on one
committed column (`Spine/Instance.lean:219-220`), against the relation the arithmetization
consumes, `SatisfiedBy prog input w` on a Clean `EnsembleWitness` (`Statement.lean:311-340`),
clause by clause; the adaptor between them as the blueprint sketches it (Layers 2 and 3,
`protocol-blueprint.md:757-867`), which is not built; the chain of theorems from `verify` to
`ValidExecution` and back (Layer 13, `:1242-1259`; leanISA Layer 10, `leanisa-blueprint.md
:1146-1179`, also not built, and blocked on Clean's balance); how the program and the public
input enter each link; the top limb of the public input along the whole chain; and the T4
obligation map of `docs/architecture.md`.

**Conclusions.**

1. **The adaptor's soundness direction can work as sketched, and the trap of the built parts
   is avoided for one reason only**: the memory and bytecode seed/finalize blocks and the
   state boundary are, in the instance, *boundary blocks* whose index and program coordinates
   are `Coord.known` data of `leanIsaInstance prog s` (decision 8), never columns of `q`. The
   witness `witnessOf prog s q` mixes parts built from `prog` (the bytecode block's rows, the
   index column) with parts read from `q`; its balance conjuncts follow from `I.Balanced q`
   exactly because the instance's boundary tuples are built from the same `prog`, so the
   statement `satisfiedBy_witnessOf` itself forces the instance's boundary to be the
   program's (section A.5, probe `KnownColumn`). The blueprint's sentence that the instance is
   "`Ensemble.toM3` of the eight tables" (`:803-805`) describes the wrong construction: with
   the two blocks as tables of the instance the program would be committed, `M3Holds` would
   not imply the mixed witness's balance, and no adaptor theorem could be proved (finding 1).
   A third bridge lemma (boundary blocks against the two Clean blocks and the verifier
   component) is needed and is absent from Layer 2 (finding 2).
2. **Both T4 statements are unprovable as written.** `baseVerifier_extractsExecution` lacks
   the hypothesis `WellFormedBytecode prog` that `constraintSoundness` carries (leanISA
   decision 9; the `JUMP`-sentinel program of `tests/LeanerVMTests/Semantics/Execution.lean
   :415-461` has steps that balance and no `ValidExecution`); its "except with probability"
   is not a statement about the concrete `verify : Program → PublicInput → Proof → Bool` at
   all, since a closed Boolean has no probability; and its conclusion drops the extracted
   witness, so it is a soundness statement for the language `{(prog, input) | ∃ t,
   ValidExecution prog input t}` (probe `Transport`). `baseProver_complete` is false: a valid
   execution with `κ = 32` (allowed by `HasPublicBoundary`, `Execution.lean:108-110`) has four
   memory columns of `2^32` cells, so its stack exceeds `2^28`, which `read_public` rejects
   (`cpu/mod.rs:174-176`, `pcs.rs:49-51`); the statement needs a resource hypothesis, and its
   "witness of t" needs T2 or a classical choice, neither planned (findings 3, 4).
3. **The relation `SatisfiedBy` and `M3Holds` anchor the top limb correctly**, as the sibling
   dossier `code-pubinput.md` §D found: a leanISA instance without the third public line
   leaves `satisfiedBy_witnessOf` unprovable for every possible `witnessOf` (a
   `SET_CONSTANT` at cell 0 with immediate `y²` gives a stack satisfying every other clause
   and a program with no execution on any input); a weakened `SatisfiedBy` would move the
   anchor to `constraintSoundness` through `HasPublicBoundary`, and the ultimate anchor is the
   literal `0` in `PublicInput.word0` (`Memory.lean:107-110`). Section D.
4. **Several of the adaptor's sketched statements cannot be written**: `Sizes` carries a
   `logInvRate` no witness determines and that the oracle protocol never reads;
   `admissible_iff_caps` has a free `w` and is false in either reading (with `gt-bus.md` G4);
   `leanIsaInstance_fits` refers to a field `Layout` does not have (with `code-layer1.md`
   G.2); `witnessOf_stackOf … = w` is not an equality any `EnsembleWitness` satisfies
   (`ProverData` is a function, `Table.width` is free); `leanIsaInstance`'s layout and `aux`
   depend on a `FlockInterface (I)` that takes the instance as its parameter (with
   `gt-flock-ring.md` 8.2, 8.3); Layer 2 produces Mathlib `MvPolynomial`s while the instance
   holds CompPoly `CMvPolynomial`s and the conversion is `noncomputable` at the pin
   (`MvPolyEquiv/Core.lean:41`), which would make `M3Holds (leanIsaInstance prog s)` undecidable
   by evaluation and `verify` noncomputable (probe `PolyBridge` shows the direct translation
   is twelve computable lines); and a `def` instance breaks the `Decidable` instance search
   the tests rely on, so `leanIsaInstance` must be reducible (probe `DefInstance`). Section E.
5. **The sizes are the prover's and admissibility is the verifier's check** (`read_public`,
   `cpu/mod.rs:130-178`; the Python `verifier.py:1372-1379`); `∃ s` is sound for the
   conclusion, since every admissible `s` yields an execution, but the probabilistic
   composition over the family of instances is unspecified: per-instance knowledge soundness
   summed over the announced sizes costs a union bound of about `2^34`, and the `Q · max ε`
   bound of the Fiat–Shamir heuristic needs the sizes inside the hashed statement of one
   protocol, which ArkLib's fixed `ProtocolSpec` cannot express (section B.3; finding 6).
6. **The obligation map of `architecture.md` is not met by the blueprint on three points**:
   the completeness dual composes T1-C, not T2 ("composes T2 with the honest prover",
   `architecture.md:273-275`), records no resource conditions, and the hash assumption
   (BLAKE2s as a random oracle) is nowhere an explicit hypothesis. Section F.

**Findings by severity** (section G): no critical. Major: (1) the instance is not
`Ensemble.toM3` of the eight tables; (2) no bridge lemma for the boundary blocks; (3) the
base soundness theorem omits `WellFormedBytecode` and is not a statement about `verify`;
(4) the base completeness theorem is false without resource hypotheses and needs a witness
generator; (5) `Sizes`, `Sizes.ofWitness` and `admissible_iff_caps` cannot be stated as
written; (6) the composition over prover-announced sizes is unspecified; (7) the instance
depends on a Flock interface that depends on the instance; (8) the polynomial bridge is
noncomputable at the pin; (9) the column-only tables enter the generic table sumcheck's
schedule (with `gt-bus.md` G16). Minor: (10) `witnessOf_stackOf` has no Lean statement;
(11) `witnessOf` lacks `input` and the count columns have no derivation; (12) `leanIsaInstance`
must be reducible; (13) the `Refinement` lemma has the wrong polarity for ArkLib's game
(harmless); (14) stale names in the blueprint (`StateMsg`, `leanIsaTables`,
`EnsembleWitness leanIsaEnsemble`, `knowledgeSound_of_refinement` in the tracker); (15) the
top-limb and decodability checks of the deployed verifier are discharged "by type" and the
blueprint does not say who parses. Notes: (16) T4 drops `AssignmentRepresents`, which T6
needs; (17) the protocol's knowledge soundness is non-adaptive in the statement (ArkLib's
`∀ stmtIn`), while T7 has a prover-chosen part of the public input; (18)
`constraintCompleteness` itself needs a resource hypothesis (leanISA's, out of scope).

## 0. The objects, introduced

Readers who know Lean may skip; every object below is quoted from the pinned sources.

- **Clean** (`93c9d1ef`) is the circuit library the arithmetization is written in. A
  `Component F` is one AIR table's row circuit: an input row type, and a `GeneralFormalCircuit`
  with its constraints, its bus interactions and its specification. An `Ensemble F PublicIO`
  is a list of components, a list of bus channels and one distinguished "verifier" component
  read once on the public input (`Air/FlatEnsemble.lean:11-17`). An `EnsembleWitness ens` is
  the prover's data for it: one `Table` (a list of raw rows, `Array F`) per component, the
  string-keyed `ProverData` (a function `String → (n : ℕ) → Array (Vector F n)`,
  `Circuit/Expression.lean:21-22`), and the public input (`FlatEnsemble.lean:19-25`). It lives
  in `Type 1` because a `Component` bundles type-level fields (probe `Shapes`, line 1-4 of the
  output). `w.Constraints` is "every component's asserted expressions vanish on every row and
  every lookup is contained" (`Operations.lean:687-688`; bus guarantees are *not* part of it,
  probe `Shapes`, output lines 154-159), and `w.interactions` is the concatenation of every
  table's emitted bus interactions, the verifier's one row first (`FlatEnsemble.lean:214-215`).
- **The spine** (leanerVM, `LeanerVM/Protocol/Spine/Instance.lean`) is the proof system's
  abstract view of an arithmetization. An `M3Instance` (`:119-148`) is: a `Shape` (a number
  of tables, each with a log-height `τ` and a width); a statement type `Stmt`; per table, a
  list of constraint polynomials and a list of flush tuples (a `Side`, push or pull, and
  sixteen coordinate polynomials, the domain separator first); a degree bound `d` with its
  two proofs; the count columns; the boundary blocks; the log-height `μ` of the one committed
  column and a `Layout` reading every column off it; the public lines; and the Flock
  predicate `aux`. A `Coord` of a boundary block (`:86-89`) is a constant, a `known` column
  (data both parties hold: the index column, the program) or a `committed` column of a table.
  `M3Holds I input q` (`:219-220`) is the conjunction of five clauses on the column `q`.
- **ArkLib** (`dca90385`) is the proof-system library. Its knowledge-soundness game
  `Verifier.knowledgeSoundnessWith` (`Security/Basic.lean:305-323`) fixes a statement, runs a
  malicious prover against the verifier, applies a named straight-line extractor to the
  transcript, and bounds the probability that the verifier accepts *and* no witness in the
  extractor's `Option` slot is valid. Statement and witness types are in `Type`. A
  `Refinement R S` (`ToArkLib/Refinement.lean:31-36`) is a map on witnesses sending every
  witness valid for `R` to one valid for `S`; its two witness universes are independent
  (probe `Shapes`, output lines 10-13).
- **CompPoly** (`3468b38c`) supplies the computable polynomials: `CMvPolynomial n K`
  (sparse maps from monomials to coefficients, with `eval` and `totalDegree`) and the hypercube
  tables `CMlPolynomialEval`. Mathlib's `MvPolynomial` is the classical object proofs are
  easiest in; `fromCMvPolynomial` maps the computable one to it (`MvPolyEquiv/Core.lean:35`),
  and `toCMvPolynomial` maps back and is `noncomputable` (`:41`).

## A. The two relations, side by side, clause by clause

### A.1 `SatisfiedBy`, with every definition it unfolds to, one level

`LeanerVM/Arithmetization/Statement.lean:311-340` (probe `Shapes`, output lines 29-55):

```lean
structure SatisfiedBy (prog : Program) (input : PublicInput)
    (w : EnsembleWitness (leanIsaEnsemble prog)) : Prop where
  public_input_eq : w.publicInput = PublicIO.ofInput input
  constraints : w.Constraints
  state_balanced : BalancedPair w StatePull.toRaw StatePush.toRaw
  mem_balanced : BalancedPair w MemPull.toRaw MemPush.toRaw
  bytecode_balanced : BalancedPair w BytecodePull.toRaw BytecodePush.toRaw
  counts_nonzero : CountsNonzero w
  caps : Caps w
  index_columns : IndexColumnsAreRowIndices w
  seed_rows : SeedRowsAreTheImage w
  bytecode_rows : BytecodeRowsAreTheProgram prog w
  blake2s_valid : Blake2sRowsValid w
  word0_eq : (imageOf w.data).2.read (gpow 0) = some input.word0
  word1_eq : (imageOf w.data).2.read (gpow 1) = some input.word1
```

One level down (same file):

```lean
-- :174-181  the ensemble: eight components, six channels, the program-bearing verifier
def leanIsaEnsemble (prog : Program) : Ensemble K PublicIO where
  tables := [⟨xorTable⟩, ⟨mulTable⟩, ⟨setTable⟩, ⟨derefTable⟩, ⟨jumpTable⟩, ⟨blake2sTable⟩,
    ⟨memTable⟩, ⟨bytecodeTable⟩]
  channels := [StatePull.toRaw, StatePush.toRaw, MemPull.toRaw, MemPush.toRaw,
    BytecodePull.toRaw, BytecodePush.toRaw]
  verifier := leanIsaVerifier prog
-- :207-209  messages by channel NAME, multiplicities ignored
def messagesOn (w : EnsembleWitness (leanIsaEnsemble prog)) (c : RawChannel K) :
    List (Array K) :=
  (w.interactions.filter (·.channel.name = c.name)).map (·.msg)
-- :229-231  balance: a permutation of message lists, counted in ℕ
def BalancedPair (w : EnsembleWitness (leanIsaEnsemble prog)) (pull push : RawChannel K) :
    Prop :=
  (messagesOn w push).Perm (messagesOn w pull)
-- :240-243  the count product: message index 1 of every pull of the six tables
def CountsNonzero (w : EnsembleWitness (leanIsaEnsemble prog)) : Prop :=
  ∀ t ∈ w.tables.take 6, ∀ i ∈ t.interactions,
    (i.channel.name = MemPull.name ∨ i.channel.name = BytecodePull.name) →
      ∀ h : 1 < i.msg.size, i.msg[1] ≠ 0
-- :250-263  three of read_public's eight checks, plus a shape of the data
structure Caps (w : EnsembleWitness (leanIsaEnsemble prog)) : Prop where
  minLogMem_le : minLogMem ≤ (imageOf w.data).1
  le_maxLogMem : (imageOf w.data).1 ≤ maxLogMem
  heights : ∀ t ∈ w.tables, ∃ τ ≤ maxLogRows, t.table.length = 2 ^ τ
  blake2s_height : 2 ^ minLogRowsBlake2s ≤ (blake2sRows w).length
  well_shaped : WellShapedData w.data
-- :272-273, :279-283, :290-293  the three facts Clean cannot express
def IndexColumnsAreRowIndices (w : EnsembleWitness (leanIsaEnsemble prog)) : Prop :=
  ∀ i (hi : i < (memBlockRows w).length), (memRowAt w (memBlockRows w)[i]).idx = gpow i
def SeedRowsAreTheImage (w : EnsembleWitness (leanIsaEnsemble prog)) : Prop :=
  ∃ idx cntFin : Fin (2 ^ (imageOf w.data).1) → K,
    memBlockRows w = List.ofFn fun i ↦
      (toElements (⟨idx i, cntFin i, #v[((imageOf w.data).2 i).limb 0,
        ((imageOf w.data).2 i).limb 1, ((imageOf w.data).2 i).limb 2]⟩ : MemRow K)).toArray
def BytecodeRowsAreTheProgram (prog : Program) (w : EnsembleWitness (leanIsaEnsemble prog)) :
    Prop :=
  ∃ cntFin : Fin (2 ^ prog.logSize) → K,
    bytecodeBlockRows w = List.ofFn fun i ↦ (toElements (bytecodeRowOf prog i (cntFin i))).toArray
-- :301-302  Flock's conjunct
def Blake2sRowsValid (w : EnsembleWitness (leanIsaEnsemble prog)) : Prop :=
  ∀ row ∈ blake2sRows w, Blake2sRelation (blake2sRowAt w row)
```

with, in `Channels.lean`, the image read off the prover data (`:188-190`):

```lean
def imageOf (data : ProverData K) : (κ : ℕ) × MemImage κ :=
  ⟨min (Nat.log 2 (memRows data).size) maxLogMem,
    fun i ↦ (((memRows data)[(i : ℕ)]?).map fun v ↦ E.ofLimbs v[0] v[1] v[2]).getD 0⟩
```

and, in `Boundary.lean`, the three block components and their honest rows: `memTable`
(`:157-160`, push `(idx, 1, m)`, pull `(idx, cntFin, m)`), `bytecodeTable` (`:240-243`, push
`(idx, 1, opcode, op)`, pull `(idx, cntFin, opcode, op)`), `leanIsaVerifier prog` (`:311-314`,
push `(1, 1)`, pull `(const prog.finalPc, 1)`), `memRowOf` (`:184-185`) and `bytecodeRowOf`
(`:274-276`: `⟨gpow i, cntFin, e[0], #v[e[1], …, e[7]]⟩` with `e := entry (prog.code i)`).
Clean's `w.Constraints` (`FlatEnsemble.lean:212`, `FlatComponent.lean:175-177`,
`Operations.lean:687-688`) is, for every table including the verifier's one-row table,
`(∀ e ∈ ops.constraints, env e = 0) ∧ (∀ l ∈ ops.lookups, l.Contains env)`; leanISA emits no
lookup (grep of `LeanerVM/Arithmetization/Tables/`: the word occurs in prose only) and only
`jumpTable` asserts (`Tables/Jump.lean:197-198`, the two residuals on its two local witness
cells `w`, `b`, `:195-196`).

### A.2 `M3Holds`, its five clauses

`LeanerVM/Protocol/Spine/Instance.lean` (probe `Shapes`, output lines 100-134):

```lean
-- :197-198
def ConstraintsVanish (q : Column I.μ) : Prop :=
  ∀ j, ∀ C ∈ I.constraints j, ∀ x, C.eval (I.row q j x) = 0
-- :201
def Balanced (q : Column I.μ) : Prop := (I.tuples q .push).Perm (I.tuples q .pull)
-- :204-205
def CountsNonzero (q : Column I.μ) : Prop :=
  ∀ j, ∀ i ∈ I.counts j, ∀ x, (I.column q ⟨j, i⟩).values.get x ≠ 0
-- :208-211
def PublicLinesHold (input : I.Stmt) (q : Column I.μ) : Prop :=
  ∀ l ∈ I.publicLines input,
    (I.column q l.col).values.get ⟨0, Nat.two_pow_pos _⟩ = l.cell0 ∧
      (I.column q l.col).values.get ⟨1, Nat.one_lt_two_pow l.pos.ne'⟩ = l.cell1
-- :219-220
def M3Holds (I : M3Instance) (input : I.Stmt) (q : Column I.μ) : Prop :=
  I.ConstraintsVanish q ∧ I.Balanced q ∧ I.CountsNonzero q ∧ I.PublicLinesHold input q ∧ I.aux q
```

where the tuples of a side are the tables' flushes evaluated on every row, then the boundary
blocks' tuples, coordinate by coordinate (`:167-186`):

```lean
def coordCell (q : Column I.μ) {κ : ℕ} : Coord I.toShape κ → Fin (2 ^ κ) → K
  | .const c, _ => c
  | .known col, x => col.values.get x
  | .committed c h, x => (I.column q c).values.get (Fin.cast (congrArg (2 ^ ·) h.symm) x)
def tuples (q : Column I.μ) (s : Side) : List (Vector K 16) :=
  I.flushTuples q s ++ I.boundaryTuples q s
```

### A.3 The leanISA instance the blueprint implies

Read from Layer 3 (`protocol-blueprint.md:794-867`), decision 8 (`protocol-status.md:220-223`:
"the fixed columns are `Coord.known` data") and the ground truth (`layout.rs:352-395`; the
table of `gt-bus.md` §E.3):

- **Tables 0-5**: the six opcode components through `Component.toM3` (Layer 2): width
  `component.width` (`JUMP`'s includes its two local witness cells), `τ j := s.τ j`, the
  constraint polynomials, the flush tuples with separator `g^0/g^1/g^2` first and side from
  `channelDir`, the count columns.
- **Column groups**: the six shared committed columns, "tables of the instance with no
  constraints and no flushes" (`:836-839`). They cannot be one table: their heights differ
  (`mem_0, mem_1, mem_2, cntfin_mem` at `2^logMem`; `cntfin_bc` at `2^prog.logSize`,
  `layout.rs:150`; `q_flock` at `2^(τ_5 + 8)`, `layout.rs:155` with `K_LOG = 14`,
  `LOG_PACKING = 6`). So at least three tables with empty `constraints`, `flushes` and
  `counts`, which the spine's `Shape` (`:57-63`) and `M3Instance.counts` allow.
- **Six boundary blocks**, `Coord.known (idxColumn κ)` for the index, `Coord.known
  (bytecodeSlotColumn prog s)` for the eight program columns (`FixedColumns.lean:75-76`),
  `Coord.committed` for the limbs and the finalize counts, `Coord.const` for the separators,
  the seed count `1` and the state boundary (κ = 0). The state pull's counter is
  `const prog.finalPc`, as `Boundary.lean:314` and `layout.rs:357`.
- **Three public lines** on `mem_0, mem_1, mem_2` (`:834-836`): cells `(lanes 0, lanes 2)`,
  `(lanes 1, lanes 3)`, `(0, 0)`, the first two `sent`.
- **`aux`**: Flock's R1CS on `q_flock` (decision 12), `decAux` its check.

### A.4 Conjunct by conjunct: what delivers it in `satisfiedBy_witnessOf`, and whether that works

`w := witnessOf prog s q`; `I := leanIsaInstance prog s`; hypotheses `hs : s.Admissible prog`
and `h : M3Holds I input q`. The earlier review's table (`docs/reviews/protocol-spine.md
:331-342`) was redone from the definitions; where it differs, the difference is stated.

| `SatisfiedBy` conjunct | Delivered by | Through | Verdict |
| --- | --- | --- | --- |
| `public_input_eq` | clause 4 (`PublicLinesHold`), lines 1-2, if `witnessOf` reads the lanes off cells 0, 1 of `mem_0`, `mem_1`; or by construction if the map takes `input` (the `Refinement.map` has it, the blueprint's `witnessOf prog s q` does not) | `limb_ofLimbs` | works either way; harmless as a built part, since no component reads the lanes (`Boundary.lean:120-123`) |
| `constraints` | clause 1 (`ConstraintsVanish`) for tables 0-5; vacuous for tables 6, 7 and the verifier (no assert) | Layer 2's `toM3_constraints_iff`, whose right side must be Clean's `Operations.ConstraintsHold` (the two-conjunct form, `Operations.lean:687`), not the flat `constraintsHold_iff_forall_mem` of `:168-182` the blueprint cites (`:292`), which includes the bus guarantees | works, provided `witnessOf` writes the `JUMP` witness cells read from `q` into the rows; citation to fix |
| `state_balanced`, `mem_balanced`, `bytecode_balanced` | clause 2 (`Balanced`), one permutation of sixteen-tuples, filtered by coordinate 0 (the separator) and mapped back to messages | `List.Perm.filter`, injectivity of `busTuple` on arrays of one size; Layer 2's `toM3_flushes_eq` for tables 0-5; **a lemma the blueprint does not have** for the memory block, the bytecode block and the verifier: their messages in `w` equal the instance's boundary tuples (A.5) | works only with the missing lemma and only because the boundary's `known` data are `prog`'s (A.5) |
| `counts_nonzero` | clause 3 (`CountsNonzero`) | per table, the pull's count coordinate is `var c` for `c ∈ I.counts j` (`memRead`, `bytecodeRead`, `Channels.lean:244-254`: the count is a column in every table) | works if `Component.toM3` computes `count` as "coordinate 2 of every pull on a lookup channel, when it is a variable"; the blueprint gives `toM3` no way to know which channels are lookups (`:773-774`; finding 11) |
| `caps` | nothing in `M3Holds`; `hs` and the construction: tables of exactly `2^τ` rows, `"mem"` data of `2^logMem` rows | `Admissible` must contain `16 ≤ logMem ≤ 32`, `τ_j ≤ 32`, `3 ≤ τ_5`; table 7's height is `2^prog.logSize ≤ 2^32` by `Program.logSize_le` and `maxLogBytecode = maxLogRows` | sound: the verifier checks the sizes (`cpu/mod.rs:157-176`); `WellShapedData` is a shape of the built data, no check |
| `index_columns` | construction: `idx := gpow i` | matched by `Coord.known (idxColumn logMem)` in both memory blocks (`idxColumn_get`, `FixedColumns.lean:50-53`) | sound (A.5) |
| `seed_rows` | construction: `"mem"` table and block rows both from `q`'s `mem_0, mem_1, mem_2`, `cntFin` from `cntfin_mem` | `imageOf` returns `logMem` only if `logMem ≤ 32` (the `min` in `Channels.lean:189`): needs `hs` | sound |
| `bytecode_rows` | construction: `bytecodeRowOf prog i (cntfin_bc[i])` | matched by `Coord.known (bytecodeSlotColumn prog k)`, `k = 3..10`, `encodeSlots = entry` at slots 3-10 (`Bytecode.lean:94-96`) | sound (A.5); the blueprint's `bytecodeColumn` of `FixedColumns.lean` is the sixteen-slot table, whose eight slices `bytecodeSlotColumn` are the block's columns (`slice_bytecodeColumn`, `:90-92`) |
| `blake2s_valid` | clause 5 (`aux`) | the Flock roadmap's lemma "the R1CS holds of the bits packed into `q_flock` ⇒ the eighteen limb slots compress" (decision 12); the limbs of the row are read strided off `q_flock` | works only with the lemma, which has no carrier in any sketched signature (finding 7) |
| `word0_eq`, `word1_eq` | clause 4, all three lines | `MemImage.read_gpow` (`κ < 64` from `hs`), `ofLimbs_limb`; the third line supplies limb 2 = 0 | works; the third line is load-bearing (section D) |

Two conjuncts hold trivially of the built witness (`index_columns`, `bytecode_rows`) and one
half-built (`seed_rows`); this is where the trap of the task statement lives.
