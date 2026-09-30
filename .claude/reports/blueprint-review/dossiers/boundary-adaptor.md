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
  table's emitted bus interactions, the verifier's one row first (`FlatEnsemble.lean:225-226`).
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
  `Verifier.knowledgeSoundnessWith` (`Security/Basic.lean:299-323`) fixes a statement, runs a
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
Clean's `w.Constraints` (`FlatEnsemble.lean:216`, `FlatComponent.lean:184-186`,
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

### A.5 The trap of the built parts, worked out

**What `witnessOf` builds and what it reads.** From `q` through `I.layout`: the rows of
tables 0-5 (the `BLAKE2S` limbs strided off `q_flock`), the memory limbs and the two finalize
counts. From `prog`: the eight entry cells of every bytecode-block row (`bytecodeRowOf prog i`)
and the sentinel constant of the verifier component. From arithmetic: the index column
`gpow i` of the memory block. From nothing: the `"mem"` table of the data is a copy of the
limbs. So `w` is a **mixed witness**, and `SatisfiedBy`'s `bytecode_balanced` and
`mem_balanced` are statements about lists that contain the built rows: `messagesOn w
BytecodePush` includes, for every slot `i`, the built message `(g^i, 1, entry (prog.code i))`
(`bytecodeTable.main`, `Boundary.lean:240-243`, on the row `bytecodeRowOf prog i _`), and
`messagesOn w BytecodePull` the read messages of tables 0-5, taken from `q`.

**What `M3Holds` establishes.** `I.Balanced q` is a permutation between two lists of
sixteen-tuples, both read from `q` *except* the coordinates the instance holds as `Coord.const`
and `Coord.known` (`coordCell`, A.2). Whether the built rows' messages are the instance's
boundary tuples is therefore decided by what `leanIsaInstance prog s` puts in `boundary`:

- If the bytecode blocks are boundary blocks with `Coord.known (bytecodeSlotColumn prog k)`
  and `Coord.known (idxColumn prog.logSize)` (decision 8; the shape leanVM has,
  `layout.rs:383-395`, `Coord::Public`, `Coord::Index`, and which the verifier evaluates
  itself, `leaf.rs:444, 453`), then for every slot `i` the instance's pushed tuple is
  `(g², g^i, 1, e[0], …, e[7], 0, …)` with `e = encodeSlots (prog.code i)` at slots 3-10 =
  `entry (prog.code i)` (`Bytecode.lean:94-96`), exactly the bus tuple of the built row's
  message. The same for the memory blocks (`known idxColumn`, `committed` limbs and counts read
  from `q`, which `witnessOf` also reads) and for the state boundary (`const prog.finalPc`
  against `Boundary.lean:314`). Then `I.Balanced q`, filtered by separator, *is* the three
  balances of the mixed witness, and the proof of `satisfiedBy_witnessOf` goes through.
- If instead the two blocks were tables of the instance with flushes, obtained by
  `Component.toM3 memTable` and `Component.toM3 bytecodeTable` as the blueprint's phrase
  "`Ensemble.toM3` of the eight tables with leanISA's separators and directions" (`:803-805`)
  says, then their `idx`, `opcode` and `op` columns would be columns of `q` (the row's cells,
  `BytecodeRow`, `Boundary.lean:211-220`), `I.Balanced q` would speak of whatever the prover
  committed there, and `witnessOf`, which must build the block's rows from `prog`
  (`bytecode_rows` demands it), would produce a witness whose `bytecode_balanced` does not
  follow from `I.Balanced q`. The theorem `satisfiedBy_witnessOf` would be unprovable; worse,
  the *protocol* would be a different one from leanVM's (a stack with committed index and
  program columns, `μ` and the layout changed), so `verify_iff_compiled` and the Rust fixture
  would fail too.

**Model.** Probe `KnownColumn` (run at the old pins, exit 0) builds the spine's toy instance in
both shapes. With the block's column `known` and equal to the "program" `[1, 1]`, the honest
stack satisfies `M3Holds`, and the same stack fails `Balanced` for the program `[1, g]`, so
the relation is about the program in the instance. With the block's column `committed`
(read off column 1 of the table), a stack whose columns are `[2, 2]` satisfies `M3Holds`
while the witness an adaptor would rebuild from it, block built from the program `[1, 1]`,
does not balance:

```
#guard M3Holds (toyOf prog) (1 : K) honest          -- passes
#guard ¬ M3Holds (toyOf prog') (1 : K) honest        -- passes
#guard M3Holds toyCommitted (1 : K) pushesTwo        -- passes: the trap
#guard ¬ (toyOf prog).Balanced pushesTwo             -- passes: the rebuilt witness fails
```

(the numeral `2 : K` is nonzero at the old CompPoly pin, as the spine's own test
`badConstraint` uses it; at the new pin it is `0` and the probe needs `K.ofBits 2`).

**Where "the accepted proof concerns the intended program" is decided.** Nowhere in the
oracle protocol, whose theorems hold for every `I`; in the adaptor, by the *statement* of
`satisfiedBy_witnessOf`, which names `leanIsaInstance prog s` and `SatisfiedBy prog` with one
`prog`, so that its proof can only close if the instance's `known` coordinates are the
program's and the verifier's sentinel is `prog.finalPc`; and in Layer 12's `verify prog input
proof`, which must evaluate those same `known` columns (`settleFixedClaims`) and seed the
transcript with the program (`fs_seed`, `cpu/mod.rs:82-93`), tied to the oracle verifier of
`leanIsaInstance prog s` by `verify_iff_compiled`. The three are consistent when they name
the same `prog`. What is missing is the lemma that lets the adaptor's proof close: Layer 2's
`toM3_flushes_eq` is about a table's flushes and cannot say anything about a boundary block.
A **third bridge lemma** is needed: for the two Clean block components and the verifier
component, the messages of the block's rows (`Boundary.lean:157-160, 240-243, 311-314`) equal,
as sixteen-tuples, the instance's boundary tuples, given the three fixed-column facts of the
witness (findings 1 and 2).

**A remark on `SatisfiedBy` that helps.** Its `word0_eq`, `word1_eq`, `caps.minLogMem_le`,
`caps.le_maxLogMem` and `seed_rows` are all stated on `imageOf w.data`, the `"mem"` table of
the prover data, not on the block's rows; and `MemPull.Guarantees` (`Channels.lean:214-216`)
too. `witnessOf` must therefore write the same limbs into the data and into the memory
block, and `seed_rows` is what ties them; Clean PR #446 would derive the data from the
block's columns and delete the conjunct (`Statement.lean:87-100`). Nothing in the chain reads
the data from anywhere else.

### A.6 The completeness direction, `m3Holds_stackOf`

`stackOf gen w hs : Column I.μ` stacks the committed columns of `w` at the aligned offsets
(Layer 1's `Blocks.stackColumn`, `Stack.lean:70`), with `q_flock` computed by the Flock
witness generator from the `BLAKE2S` rows' limbs. Clause by clause, from
`h : SatisfiedBy prog input w` and `hs : Sizes.ofWitness w = some s`:

| Clause of `M3Holds` | From | What else is needed |
| --- | --- | --- |
| `ConstraintsVanish` | `h.constraints`, tables 0-5 | `toM3_constraints_iff` on rows read back from the stack: `Blocks.readColumn_stackColumn` (`Stack.lean:85-87`) returns the block, so the rows read back are the rows stacked, provided every row has exactly `component.width` cells or `stackOf` reads `row[j]?.getD 0` as `Environment.fromArray` does; the `BLAKE2S` limbs read back from the strided slots equal the rows' limbs, which is the generator's "keeping the limbs in their slots" |
| `Balanced` | `h.state_balanced`, `h.mem_balanced`, `h.bytecode_balanced` | the missing boundary lemma in the other direction: the messages of `w`'s tables 6, 7 and of the verifier row are the instance's boundary tuples, which needs `h.index_columns` (the rows' `idx` cells are `g^i`, the stack does not hold them), `h.seed_rows` (the block's limbs are the data's, which the stack holds) and `h.bytecode_rows` (the rows' entry cells are `prog`'s, not stacked); then the three permutations concatenate into one, since every flush tuple carries exactly one of the three separators |
| `CountsNonzero` | `h.counts_nonzero` | `I.counts j` ⊆ the columns that appear as a pull's count coordinate (the converse inclusion the soundness direction needs; so `counts j` must be exactly that set) |
| `PublicLinesHold` | `h.word0_eq`, `h.word1_eq`, `h.seed_rows`, `h.caps` | `MemImage.read_gpow` at `κ < 64`, `limb_ofLimbs`; the third line's `(0, 0)` from the top limb of `input.word0`, `input.word1`, which is `0` by definition (`Memory.lean:107-110`) |
| `aux` | `h.blake2s_valid` | `FlockWitnessGen`'s lemma: the wires the generator computes from limbs that compress satisfy the R1CS (decision 12) |

What else `m3Holds_stackOf` needs: nothing on the caps beyond `Sizes.ofWitness w = some s`,
which `h.caps.heights` (every height a power of two at most `2^32`) supplies for the eight
tables, together with `h.seed_rows` (table 6 has `2^(imageOf w.data).1` rows) and
`h.bytecode_rows` (table 7 has `2^prog.logSize`); and `leanIsaInstance`'s layout fit, which is
a `Blocks` fact and must precede the instance (`code-layer1.md` G.2). What `verify`'s
acceptance needs beyond it is not in `SatisfiedBy` at all: the stacking window `μ ∈ [15, 28]`
and the rate window (section C, finding 4).

## B. The program and the public input, along the chain

### B.1 How each enters

| Link | The program | The public input |
| --- | --- | --- |
| (i) the deployed verifier (`cpu/mod.rs:711-779`) | seeds the transcript with `fs_seed(program)`, the BLAKE2s of `"leanvm" ‖ len ‖ R1CS_DIGEST ‖ bytecode_hash` (`:82-93`, `:712`), where `bytecode_hash` is the hash of the stacked sixteen-slot table (`:73-76`, `layout.rs:317-326`); builds the layout from `prog.prog` (`read_public`, `:171`): the final counter `g^(len−1)` as a constant of the state pull (`layout.rs:335, 357`) and the eight public columns of the two bytecode blocks (`layout.rs:343, 385-395`), which the verifier evaluates itself at `ζ_lo` (`leaf.rs:453`) and never opens; the bytecode length must be a power of two at most `2^32` (`:157-159`). The Python takes the raw stacked table (`verifier.py:1365-1368`) | seeds the transcript as four 64-bit words (`digest_words`, `:99-106`, `:712`), after rejecting a nonzero third limb (`:141-143`); enters the layout as `l.pi` (`layout.rs:83, 424`), read by the public-input check alone (`:752-755`); binds nothing else (the boundary tuples do not depend on it: `gt-bus.md` §E.3). The Python's `Digest` is 32 bytes by construction (`verifier.py:201-224`) |
| (ii) the spine | the instance `I : M3Instance` is a parameter of every phase and theorem; for leanISA it is `leanIsaInstance prog s`, whose `boundary` holds the program as `Coord.known` data (the eight `bytecodeSlotColumn prog k`, `FixedColumns.lean:75-76`, and `const prog.finalPc`) and whose `Stmt` is `PublicInput`. Nothing in `M3Holds` reads a program from `q` | `input : I.Stmt` is the statement of the oracle protocol (`M3Rel`, `Spine/Instance.lean:230-231`); it is read by one clause, `PublicLinesHold input q`, through `I.publicLines input` (three lines) |
| (iii) the adaptor (sketch) | `witnessOf prog s q` builds the bytecode block's rows and the verifier's sentinel from `prog`; `satisfiedBy_witnessOf` names the same `prog` in `leanIsaInstance prog s`, `witnessOf prog s q` and `SatisfiedBy prog input` | absent from `witnessOf`'s arguments (`:813-814`); recovered from `q` through the lines, or supplied by the refinement's `map : Stmt → W₁ → W₂` |
| (iv) `SatisfiedBy prog input w` | `bytecode_rows` (the block's rows are `bytecodeRowOf prog i`), `leanIsaVerifier prog` pulling `const prog.finalPc` (`Boundary.lean:311-314`), and nothing else: the six tables and the channels are program-free (decision 14, `Channels.lean:88-105`) | `public_input_eq` (the lanes, read by no component) and `word0_eq`, `word1_eq` on the image the data names |
| (v) `ValidExecution prog input t` | `run prog t.image t.steps Regs.initial = some (Regs.final prog)`, `Program.fetch` at every step (`Execution.lean:86-90, 114-115`) | `HasPublicBoundary input t`: `16 ≤ κ ≤ 32` and the two words at `g^0`, `g^1` (`:108-110`) |

### B.2 A different program or input?

Within one instantiation, no: `prog` and `input` are the same variables in `verify prog input
proof`, `verify_iff_compiled`, `leanIsaInstance prog s`, `satisfiedBy_witnessOf`,
`SatisfiedBy prog input` and `ValidExecution prog input`. Every theorem of the chain is
universally quantified over both outside any probability, and the built code confirms the
shape: `piop_rbrKnowledgeSoundness (P : Phases I) (S : P.Security)` is stated for a fixed `I`
(`Spine/Compose.lean:172-177`), and ArkLib's game fixes `stmtIn` before the prover runs
(`Security/Basic.lean:299-323`: `∀ stmtIn : StmtIn, ∀ witIn, ∀ prover, Pr[…] ≤ ε`). Three
observations on the edges of that answer:

1. **The program is bound by the transcript only through its stacked table.** The Lean side
   holds `prog : Program` (typed instructions, `Instruction.lean:87-93`) and `FsState.seed
   prog input` must hash `bytecodeColumn prog` (`FixedColumns.lean:78-82`), as the Rust hashes
   `bytecode_table` (`cpu/mod.rs:73-76, 89`). That `prog ↦ (prog.logSize, bytecodeColumn prog)`
   is injective follows from `entry_injective` (`Bytecode.lean:240-245`) and
   `bytecodeColumn_slot` (`FixedColumns.lean:84-87`); it is not stated anywhere and Layer 12
   will need it for "statement binding" (`architecture.md:453-454`). Unverified: no probe was
   written for the lemma.
2. **`Program` and `PublicInput` are narrower than the deployed surfaces.** The Rust verifier
   takes `Vec<Op>` with `u32` operands; Lean's operands are any `K` (a superset); the Python
   takes any `K`-array (`verifier.py:1365`), including undecodable entries, of which Lean has
   none (the faithfulness review's row 4, `docs/reviews/leanvm-faithfulness-review.md:72`). A
   public input with a nonzero third limb is rejected by the Rust (`:141-143`) and by the
   Python's `Digest` (`:223`), and cannot be written in Lean (`PublicInput` is four lanes of
   `K`, `Memory.lean:101-104`). So two of `read_public`'s eight checks (leanISA's numbering,
   `Statement.lean:71-73`) are discharged "by type" on the Lean side, which means: by whoever
   parses bytes into `Program` and `PublicInput`. The blueprint's *Verifier shape* convention
   (`:326`) says structure checks the Rust `assert!`s are "theorems about the layout, not
   branches of `verify`"; it does not say that these two are parsing obligations of the
   fixture harness and, later, of T7's `PublicInput.encode` (finding 15).
3. **The sizes are the prover's**, and this is where the family of instances is quantified.
   `verify_iff_compiled` (`:1218-1221`) has `∃ s, s.Admissible prog ∧ …`; the prover writes
   `log_mem`, six `τ_j` and `log_inv_rate` onto the stream (`announce_public`, `cpu/mod.rs
   :118-124`) and the verifier reads and checks them before anything else (`read_public`,
   `:144-176`; Python `:1372-1379`). Section B.3.

### B.3 Is `∃ s` sound, and who checks?

**For the conclusion, yes.** `satisfiedBy_witnessOf` is stated for every admissible `s`, and
its conclusion `SatisfiedBy prog input (witnessOf prog s q)` does not mention `s`; so whatever
sizes the prover announces, an accepting transcript whose extracted stack satisfies
`M3Holds (leanIsaInstance prog s) input q` yields a satisfying witness and, through
`constraintSoundness`, an execution. Admissibility is checked by the verifier: the Rust
rejects `log_mem ∉ [16, 32]`, `τ_j > 32`, `τ_5 < 3`, an invalid rate, and `μ ∉ [15, 28]`
(`cpu/mod.rs:157-176`); the Python checks the rate and the `μ` window (`verifier.py
:1377-1379`) and the rest through its layout (`gt-bus.md` G5 re-examined the status file's
claim that it omits four caps). The hypothesis `hs : s.Admissible prog` of the adaptor is
therefore discharged by a verifier check, as the blueprint says (`:824-831`).

**For the probability, the blueprint does not say how.** `verify_knowledgeSound` is sketched
with error `niError s Q` (`:1226-1227`), a function of `s`; the oracle protocol is "a family
indexed by them" (acceptance test 21, `:1326-1328`); and the per-instance theorems
(`piop_rbrKnowledgeSoundness` for one `I`, `FiatShamirSecurity` for one compiled protocol)
bound the event for one `s`. A prover against `verify` chooses `s` inside its proof, after
its random-oracle queries. Two ways to compose exist and they differ by about `2^34`:

- a union over the admissible sizes: `Pr[verify accepts ∧ bad] ≤ Σ_s Pr[accepts with s ∧ bad_s]
  ≤ Σ_s ε_s`, with `|{admissible s}| ≤ 11 · 28^5 · 25 · 4 ≈ 2^34` (`log_mem ≤ 26` and
  `τ_j ≤ 28` once `μ ≤ 28` is imposed; `τ_5 ≥ 3`; four rates), which the numeric target of
  acceptance test 23 (`< 2^-150`) absorbs for the oracle protocol but the 128-bit WHIR budget
  (`SECURITY_BITS`, `leaf.rs:143-145`) does not;
- the standard argument, `Q · max_s ε_s`: each random-oracle query commits to one `s`
  because the sizes are absorbed into the chain before any challenge (`announce_public`;
  acceptance test 12). This needs the sizes to be part of the statement the Fiat–Shamir
  transform hashes, i.e. one protocol whose first prover message is `s`, on which the rest
  of the schedule depends. ArkLib's `ProtocolSpec n` has a fixed `n` and fixed message types
  (`ProtocolSpec/Basic.lean`), so that protocol cannot be written at the pin; the family is
  the only shape available, and `FiatShamirSecurity` must then be stated for the family (the
  challenge oracle implemented by one BLAKE2s chain shared across `s`, with `s` in every
  query), not for one instance.

Finding 6 asks the blueprint to say which, and to make `niError` independent of the prover's
choice (a maximum over admissible `s`, or the union). Either way the *conclusion* of T4 is
unaffected; the *number* is.

**A remark for T7.** ArkLib's game fixes the statement before the prover runs. For T7
(`architecture.md:339-369`) the public input is `PublicInput.encode (FinalProof.metadata
proof) expectedStatement`, part of which the prover chooses; that needs adaptive soundness in
the statement, which the deployed transcript provides (the input seeds the chain) and which
no theorem of the blueprint states (note 17).

## C. Hypotheses, and where each is discharged

The chain, soundness direction: `verify prog input proof = true` →(`verify_iff_compiled`)→
`∃ s, s.Admissible prog ∧` the Fiat–Shamir-compiled oracle verifier of `leanIsaInstance prog s`
accepts →(`verify_knowledgeSound`, in the random-oracle model)→ the extracted stack `q`
satisfies `M3Holds (leanIsaInstance prog s) input q` except with probability `niError`
→(`satisfiedBy_witnessOf`)→ `SatisfiedBy prog input (witnessOf prog s q)`
→(`constraintSoundness`)→ `∃ t, AssignmentRepresents (witnessOf prog s q) t ∧ ValidExecution
prog input t`. Completeness direction: `ValidExecution prog input t` →(`constraintCompleteness`)→
`∃ w, SatisfiedBy prog input w ∧ AssignmentRepresents w t` →(`Sizes.ofWitness`, `stackOf gen`)→
`M3Holds (leanIsaInstance prog s) input (stackOf gen w hs)` →(`piop_perfectCompleteness`, the
compilation)→ `verify prog input (prove …) = true`.

Every hypothesis on the chain, in four kinds: **(P)** a condition on public data anyone can
check; **(V)** a property the verifier checks; **(O)** a theorem another roadmap or library
owes; **(N)** nothing discharges it.

| Hypothesis | Where it appears | Kind | Discharged by | Status |
| --- | --- | --- | --- | --- |
| `s.Admissible prog` | `satisfiedBy_witnessOf` (`:815`), `verify_iff_compiled` (`:1220`) | V | `read_public` (`cpu/mod.rs:157-176`), reproduced by `verify`; supplied by `verify_iff_compiled`'s `∃ s` | consistent, once `Admissible` contains the `μ` and rate windows (`gt-bus.md` G4) |
| `Sizes.ofWitness w = some s` | `stackOf`, `m3Holds_stackOf`, `witnessOf_stackOf` (`:811-819`) | O (leanISA) | `SatisfiedBy.caps.heights`, `seed_rows`, `bytecode_rows` give power-of-two heights | provable from `SatisfiedBy`; ill-defined while `Sizes` holds `logInvRate` (E.3) |
| `FlockWitnessGen` (the generator and its lemma "generated wires satisfy the R1CS when the limbs compress") | `stackOf` (`:811`), `m3Holds_stackOf` | O (#3) | an explicit argument until #3 supplies it (`:857-861`) | named; no statement of its type in the blueprint |
| "the R1CS holds of `q_flock` ⇒ the eighteen limb slots compress" | `satisfiedBy_witnessOf` (`:855-857`) | O (#3) | nothing carries it: `satisfiedBy_witnessOf`'s sketched signature has no argument for it, `FlockInterface (I)` has no such field (`:1077-1085`), and `leanIsaInstance`'s `aux` needs #3's R1CS to be *defined* | **N** until a carrier is named (finding 7) |
| `WellFormedBytecode prog` (`sentinelSafe`, used by soundness; `hasFillBlocks`, used by completeness) | `constraintSoundness`, `constraintCompleteness` (`leanisa-blueprint.md:1156-1166`) | P (decidable on the program: `SentinelSafe` has an instance, `Execution.lean:77-78`; `HasFillBlocks` is undefined yet) | no verifier checks it (leanVM's does not, `leanvm-target.md:57-62`); the compiler emits both (`lean_compiler/src/lib.rs:162`, `filler.rs`); the guest owner (T3) owes it | **N** in the blueprint: `baseVerifier_extractsExecution` (`:1247`) has no such hypothesis and `baseProver_complete` (`:1249`) has `HasFillBlocks` only (finding 3; `docs-debt.md` B.6) |
| `constraintSoundness`, `constraintCompleteness` themselves | Layer 13 (`:1253-1256`) | O (leanISA Layer 10) | not stated in Lean; Layer 9's four statements are block comments (`Statement.lean:442-480`), blocked on Clean's ℕ-counted balance (issue #16, Clean #452/#464) | planned |
| a resource bound on the trace (every table ≤ `2^32` rows) | `constraintCompleteness` as sketched has none | N (leanISA's) | nothing: `ValidExecution` bounds nothing but `κ ≤ 32`, and a run of `2^40` distinct `(pc, fp)` states needs `2^40` rows of one table, which `Caps.heights` forbids | **N** (note 18, out of scope; it reaches T4 through `baseProver_complete`) |
| the stacking window `μ ∈ [15, 28]` and the rate window | `verify`'s acceptance in `baseProver_complete` | V (`cpu/mod.rs:174-176`, `pcs.rs:49-51`) | nothing on the completeness side: `SatisfiedBy.caps` has neither (`Statement.lean:79-81`); a valid execution at `κ = 32` has `4 · 2^32 > 2^28` committed cells | **N**: `baseProver_complete` is false without it (finding 4) |
| a witness *constructed* from `t` ("`prove prog input (witness of t)`", `:1250`) | `baseProver_complete` | O (T2, out of scope `:147-148`) | `constraintCompleteness` gives `∃ w` only | **N** as written (finding 4) |
| `Phases.Complete`, `Phases.Security` for `leanIsaInstance prog s` | the two master theorems (`Spine/Compose.lean:162-177`) | O (holes P1-P8; P5 built) | the phases | assumed interface until every hole is filled (`:1419-1426`) |
| `FiatShamirSecurity`, `BcsSecurity`, `McaJohnson` | `verify_knowledgeSound` (`:1226`) | O (ArkLib, ledger rows *Fiat–Shamir and BCS*, *mutual correlated agreement*) | explicit arguments | assumed interfaces |
| the Flock phase's `Security` (`FlockInterface`) | `verify_knowledgeSound`'s `flock` argument | O (#3) | explicit argument | assumed interface; circular with the instance (finding 7) |
| BLAKE2s as a random oracle | the step from `verify_knowledgeSound` (ROM) to the concrete `verify` | N (a heuristic) | nothing; the blueprint's `baseVerifier_extractsExecution` names `verify` and a probability in one sentence (`:1247-1248`) | **N**: must be stated as the hypothesis it is (finding 3) |
| the round-by-round-to-plain implication | the plain corollary (`:261`) | O (ArkLib, admitted at the pin) | "stated once the implication lands upstream" | consistent; `code-spine.md` C.7 notes it forgets the named extractor |
| the top limb of the public words is zero | `read_public` (`cpu/mod.rs:141-143`) | V in the Rust; by type in Lean (`Memory.lean:107-110`) | the parser of `PublicInput` | consistent; undocumented as a parsing obligation (finding 15) |
| the bytecode is decodable and of power-of-two length ≤ `2^32` | `read_public` (`:157-159`); the Python accepts any array | V in the Rust; by type in Lean (`Program`, `Instruction.lean:87-93`) | the loader of `Program` | consistent; coverage gap recorded (`leanvm-faithfulness-review.md:72`) |
| `κ < 64` for `MemImage.read_gpow` | inside `satisfiedBy_witnessOf`'s `word0_eq` | V | from `s.Admissible prog` (`logMem ≤ 32`) | consistent |
| the count columns are exactly the pulls' count coordinates | `counts_nonzero` both ways | O (Layer 2/3) | a Category-B transcription of `count_columns()` per table (`layout.rs:412-414`), which `Component.toM3` cannot derive from `(sep, dir)` alone | unspecified (finding 11) |

Violations of "nothing is assumed on one side of the boundary which the other side does not
prove": the four rows marked **N** that are not heuristics, namely `WellFormedBytecode` (the
proof system assumes nothing of it and the arithmetization requires it), the resource
bounds and the constructed witness of completeness (the proof system's completeness theorem
requires what the arithmetization's does not give), and the Flock consequence lemma (the
adaptor consumes a theorem no interface carries). The random-oracle heuristic is a fifth,
inherent, and must simply be written down.

## D. The top limb of the public input, along the whole chain

The sibling dossier `code-pubinput.md` §D traced the limb through the phase, the spine and the
deployed verifiers; this section does not repeat it and adds the two ends of the chain and the
anchors. Its facts used here: the oracle protocol's theorems hold for every instance, so a
leanISA instance with two lines is as good an `M3Instance` as one with three (§D.1); the
deployed verifiers pool the third claim at `0` with no scalar (`cpu/mod.rs:746, 756`,
`bind_pi_claim` `:674-682`; `verifier.py:1399-1401`; §D.3).

**The type.** `PublicInput` is four lanes of `K`, and the two words are built with a literal
zero top limb (`Memory.lean:101-110`, probe `Shapes`, output lines 69-78):

```lean
structure PublicInput where
  lanes : Fin 4 → K
def PublicInput.word0 (p : PublicInput) : E := E.ofLimbs (p.lanes 0) (p.lanes 1) 0
def PublicInput.word1 (p : PublicInput) : E := E.ofLimbs (p.lanes 2) (p.lanes 3) 0
```

A public input with a nonzero top limb cannot be written; the probe proves
`p.word0.limb 2 = 0` and `p.word1.limb 2 = 0` for every `p` by `simp` (`Shapes.lean:45-49`,
exit 0). The specification agrees, "two 192-bit words (with top limb 0)"
(`08-end-to-end-protocol.tex:29`), the Rust rejects a third limb (`cpu/mod.rs:141-143`) and the
Python's `Digest` has none (`verifier.py:223`).

**What `SatisfiedBy` says of cells 0 and 1.** `word0_eq : (imageOf w.data).2.read (gpow 0) =
some input.word0` and `word1_eq` (`Statement.lean:338-340`): the *whole* `E`-word of the image
at index 0 is `input.word0`, top limb included; and `public_input_eq` (`:315`), which no
component reads. **What `ValidExecution` says**: `HasPublicBoundary input t` has the same two
equations on `t.image` (`Execution.lean:108-110`), whole words again.

**What the instance says.** Three lines (`:834-836`): `mem_0` with cells `(word0.limb 0,
word1.limb 0)`, `mem_1` with `(word0.limb 1, word1.limb 1)`, `mem_2` with `(0, 0)`.
`PublicLinesHold` on them is exactly the six limb equalities, from which
`E.ofLimbs mem_0[i] mem_1[i] mem_2[i] = input.word_i` follows (probe `Shapes.lean:57-63`,
the second `example`).

**If the instance omitted the third line.** `M3Holds` would say nothing of `mem_2[0]`,
`mem_2[1]`; the master theorems hold unchanged; the theorem left without a proof is
**`satisfiedBy_witnessOf`**, for *every* possible `witnessOf`, not only the natural one:

- the natural `witnessOf` writes the image's word 0 as `E.ofLimbs mem_0[0] mem_1[0] mem_2[0]`;
  with `mem_2[0] ≠ 0` it is not `input.word0`, whatever `input` (probe `Shapes.lean:51-55`:
  `E.ofLimbs a b c ≠ p.word0` when `c ≠ 0`, by comparing limb 2);
- a `witnessOf` that zeroed the limb when building the data and the block would break
  `mem_balanced` for any program that reads cell 0 (the reading row's pulled tuple carries
  `mem_2[0]` from `q`, the built seed carries `0`);
- and no `witnessOf` at all can serve when no satisfying witness exists: take the program
  whose first instruction is `SET_CONSTANT [g^0, y²]` (`Instr.setConstant 1 (E.ofLimbs 0 0 1)`;
  at `fp = 1` the operand `g^0` names cell 0) followed by a jump to the sentinel and the fill
  blocks. Its constraints are satisfiable only with cell 0 = `y²`, whose low limbs are `0, 0`:
  a stack with `mem_0[0] = mem_1[0] = 0`, `mem_2[0] = 1` satisfies the constraints, the
  balances, the counts and the two remaining lines at `input = ⟨![0, 0, l₂, l₃]⟩`, so it is
  in the two-line `M3Holds`; but `SatisfiedBy prog input w` demands `word0_eq` with
  `input.word0 = E.ofLimbs 0 0 0 ≠ y²`, and `ValidExecution` demands the same of `t.image`, so
  neither has an inhabitant. (An inference from the definitions: `execute` of `SET_CONSTANT`
  requires `[o] = k`, `Step.lean`; the honest stack of that program is not built as a probe.)

**If `SatisfiedBy` were weakened instead** (its two word conjuncts restricted to limbs 0
and 1), `satisfiedBy_witnessOf` would close with two lines, and the theorem left without a
proof would be **`constraintSoundness`**: it must produce `∃ t, AssignmentRepresents w t ∧
ValidExecution prog input t`, `AssignmentRepresents` fixes `t.image` to `imageOf w.data`
(`Statement.lean:355-362`, `assignmentRepresents_image`), and `HasPublicBoundary` then demands
the whole word (`Execution.lean:110`). For the program above no `t` exists, so the theorem is
false. **If `HasPublicBoundary` were weakened too**, nothing on the chain would object, and the
anchor would be the specification alone; the top limb would then be constrained only where a
guest reads it (T3). **The anchor** is therefore the pair `PublicInput.word0`,
`PublicInput.word1` with their literal `0` (`Memory.lean:107-110`), consumed verbatim by
`HasPublicBoundary` and by `SatisfiedBy`; the requirement of the owner's note ("a missing,
weak or wrong verifier check must leave knowledge soundness or completeness unprovable") is
met one level down from the oracle protocol, in the adaptor's theorem, and the acceptance
test that claims it (test 10, `:1293-1295`) should name that theorem, as `code-pubinput.md`
G.3 also asks.

## E. Are the adaptor's statements well formed and provable as sketched?

The Layer 3 sketch (`protocol-blueprint.md:794-820`), read as Lean to be written.

### E.1 `witnessOf` and `satisfiedBy_witnessOf`

`def witnessOf (prog) (s) (q : Column (leanIsaInstance prog s).μ) : EnsembleWitness
(leanIsaEnsemble prog)`, "total and computable". `EnsembleWitness` is in `Type 1` (probe
`Shapes`, output line 1-2); a computable definition may inhabit a type in `Type 1` (the
ensemble itself is a `def` that compiles), and the fields are constructible: eight `Table`s
with `component := (leanIsaEnsemble prog).tables[j]`, rows built by one pass over the columns
read through the layout, `data := fun name n ↦ if name = "mem" ∧ n = 3 then … else #[]`, the
public input off cells 0 and 1, and the three proof fields by `rfl`/`simp`. Total in `s`: for
an inadmissible `s` the tables are simply of the announced heights. Two things the sketch
omits: `witnessOf` has no `input` argument (B.1 (iii)), which is fine only if the lanes are
read off `q` (then `public_input_eq` needs the first two lines and `0 < logMem`); and the
instance must exist first (E.4, E.5, finding 7).

`theorem satisfiedBy_witnessOf (hs : s.Admissible prog) (h : M3Holds (leanIsaInstance prog s)
input q) : SatisfiedBy prog input (witnessOf prog s q)` typechecks as a statement provided
`(leanIsaInstance prog s).Stmt` reduces to `PublicInput`; with a `def` instance the elaborator
unfolds it (probe `DefInstance`, the `example` at line 34 elaborates), but instance search
does not, so `Decidable (M3Holds (leanIsaInstance prog s) input q)`, which every `#guard` of
the Layer 3 tests needs, is found only for an `abbrev` instance (probe `DefInstance`: the two
guards on `instA` pass, the two on `inst` fail with "Type mismatch … expected to have type
Bool"; the spine's toy is an `abbrev` for the same reason, `Spine/Toy.lean:94-95`). Provable
as sketched: yes, with the additions of A.4 (the boundary lemma, the count derivation, the
Flock consequence lemma).

### E.2 `stackOf`, `m3Holds_stackOf`, `witnessOf_stackOf`

`def stackOf (gen : FlockWitnessGen) (w) (hs : Sizes.ofWitness w = some s) : Column
(leanIsaInstance prog s).μ`: well formed (a `def` taking a proof to fix the index of its
result is ordinary Lean). `m3Holds_stackOf`: provable with the additions of A.6.

`theorem witnessOf_stackOf (hs) : witnessOf prog s (stackOf gen w hs) = w -- on the committed
fields` is not a Lean statement. As an equality of `EnsembleWitness`es it is false for
almost every `w`: `w.data : String → (n : ℕ) → Array (Vector K n)` is a function and
`witnessOf` rebuilds it with the `"mem"` table only; `Table.width` is a free field
(`FlatComponent.lean:151-156`) and `witnessOf` rebuilds rows of exactly the component's
width; the memory block's `idx` cells and the bytecode block's entry cells are rebuilt from
`gpow` and `prog`, so equality needs `index_columns` and `bytecode_rows` of `w`; and the
public input is rebuilt from cells 0 and 1, so it needs `public_input_eq` and the word
conjuncts. "On the committed fields" has to be spelled out; a statement that says what the
sketch means and is decidable on a small witness:

```lean
/-- The cells a component reads: the first `width` cells of a raw row, a missing cell `0`. -/
def rowCells (c : Component K) (row : Array K) : List K :=
  (List.range c.width).map fun j ↦ row[j]?.getD 0
theorem witnessOf_stackOf (h : SatisfiedBy prog input w) (hs : Sizes.ofWitness w = some s) :
    let w' := witnessOf prog s (stackOf gen w hs)
    (∀ j : Fin 8, (tableAt w' j).table.map (rowCells (tableAt w j).component) =
        (tableAt w j).table.map (rowCells (tableAt w j).component)) ∧
      memRows w'.data = memRows w.data ∧ w'.publicInput = w.publicInput
```

Neither T4 composition uses `witnessOf_stackOf` (soundness uses `satisfiedBy_witnessOf`,
completeness `m3Holds_stackOf`); its role is acceptance tests 19 and 24 (`:1320-1322,
1333-1340`), non-vacuity of `witnessOf`. `#guard witnessOf (stackOf w) = w` (`:1339`) cannot be
written, `EnsembleWitness` having no `DecidableEq`; the statement above can (finding 10).

### E.3 `Sizes.logInvRate`

The Rust announces `log_mem`, six `τ_j` and `log_inv_rate` (`announce_public`, `cpu/mod.rs
:118-124`; `read_public` `:144-149`); the Python reads the same `2 + 6` scalars
(`verifier.py:1372-1376`); the specification's Setup names `κ_mem` and the six `τ_j` only
(`08-end-to-end-protocol.tex:55`), a disagreement between the specification and both
implementations that the blueprint resolves the Rust's way (Category B, `:199`). So the rate
*is* announced with the sizes. It does not belong in the instance of the oracle protocol:
`leanIsaInstance prog s` reads `s.logMem` and `s.τ` (heights, `μ`, layout, lines) and nothing
of the rate, which parameterizes WHIR alone (Layer 11); `Sizes.ofWitness (w) : Option Sizes`
(`:799`) cannot produce a rate from a witness; and `Sizes.Admissible` would mix a check of
the oracle protocol's family index with a check of the commitment. `gt-bus.md` G4 reaches the
same point from the caps. Proposed: `Sizes` holds `logMem` and `τ`; the announcement of Layer
12 is `Sizes × logInvRate`; `Admissible prog s` (heights, `3 ≤ τ 5`, `μ_stack prog s ∈
[15, 28]`) and `validRate ρ` (`ρ ∈ [1, 4]`, `whir_config.rs:48-55`) are two predicates
(finding 5).

### E.4 The instance's tables, columns and blocks against `M3Instance` as built

Expressible, with one consequence:

- the six shared columns as tables of the instance: yes, as at least three tables (A.3), each
  with `constraints := []`, `flushes := []`, `counts := []`; `Shape.τ` is per table, so the
  memory columns' height `2^logMem` sits beside the six tables' heights;
- the finalize counts outside the count tree: `counts jMem = []`, `counts jBc = []`, as
  `layout.rs:412-414` (the count blocks are the tables' `count_columns()` only);
- the boundary blocks: `Coord.committed ⟨jMem, i⟩ rfl` at `κ = logMem`, `Coord.committed
  ⟨jBc, 0⟩ rfl` at `κ = prog.logSize`, the `known` and `const` coordinates of A.3; the
  `h : S.τ c.1 = κ` obligation is met by construction;
- the eighteen limb columns as strided slots of `q_flock`: the `Layout` law admits it
  (`Spine/Instance.lean:73-81`, a reading law), but no reader exists (`code-layer1.md` G.1)
  and the slot map is placed inside `FlockInterface (I)` (`gt-flock-ring.md` 8.2): finding 7;
- the three lines need `PublicLine.pos : 0 < τ`, i.e. `0 < s.logMem`; for a total
  `leanIsaInstance` the lines must be empty (or the instance junk) when `logMem = 0`, which is
  harmless because `verify` rejects such `s`, but must be written;
- **the consequence**: the generic table sumcheck (Layer 7) takes its rounds from
  `τ_max = max_j τ_j` over the instance's tables and sends "one value per column of every
  table" (`:987-989`, `08-end-to-end-protocol.tex:76-77`); with the shared columns as
  tables, a phase over the abstract `I` would run `max(τ_j, logMem, prog.logSize, τ_5 + 8)`
  rounds and send scalars for `mem_0, …, q_flock`, a transcript leanVM does not have
  (`constraints.rs:250`, the six tables; `gt-bus.md` G16). The instance needs a criterion the
  phase can read ("a table with a constraint, a flush or a count column takes part"), stated
  in the spine's conventions and used by Layer 7 (finding 9).

### E.5 Mathlib polynomials in Layer 2, CompPoly polynomials in the instance

Layer 2 produces `Expression.toMvPolynomial : Expression F → MvPolynomial ℕ F` and an
`M3Table F` whose constraints are `MvPolynomial (Fin width) F` (`:762-771`); `M3Instance`
holds `CMvPolynomial (width j) K` (`Spine/Instance.lean:123-125`). No conversion is named.
CompPoly's `toCMvPolynomial : MvPolynomial (Fin n) R → CMvPolynomial n R` is
`noncomputable def` at the pin `3468b38c` (`Multivariate/MvPolyEquiv/Core.lean:41`), so an
instance built through it is noncomputable: `M3Holds (leanIsaInstance prog s)` could not be
decided by evaluation (the Layer 3 tests, `:866-867`), the phases' verifiers, which evaluate
`I.constraints` at the claimed column values, would not compile, and `verify` (`:1230-1231`,
"total and computable") could not be defined from them. The degree bound travels the other
way without trouble: `totalDegree_equiv : p.totalDegree = (fromCMvPolynomial p).totalDegree`
(`MvPolyEquiv/Eval.lean:60-61`, `rfl`) and `eval_equiv` (`:53-57`) let Mathlib prove the
bound of a computable polynomial, as the toy does (`Spine/Toy.lean:68-74`). What Layer 2 must
produce is a *direct* computable translation `Expression K → CMvPolynomial n K` (structural
recursion on `var`, `const`, `add`, `mul`, `Expression.lean:12-16`, with `CMvPolynomial.X`,
`C`, `+`, `*`), and its bridge to Mathlib for the degree lemma. Probe `PolyBridge` (old pins,
exit 0) writes it in twelve lines, evaluates the `JUMP` residual `b + v_cond · w` on a row
and checks it against Clean's `Expression.eval` (`#guard polyValue = cleanValue`), checks
`totalDegree = 2`, and checks that a variable past the width reads `0` on both sides as
`Environment.fromArray` reads a missing cell (`Expression.lean:71-73`). At the new CompPoly
pin the probe's row numerals `3, 5, 7` read as `1, 1, 1`; the guards still hold but a re-run
should use `K.ofBits`. Finding 8. (The `Direction` of leanISA's `channelDir`,
`Channels.lean:262-272`, and the spine's `Side`, `Spine/Instance.lean:51-54`, are two
enumerations of the same two values; the translation is one match.)

### E.6 The T4 composition, arrow by arrow

"`T4 = verify_knowledgeSound ∘ Refinement.map_option_valid satisfiedBy_witnessOf ∘
constraintSoundness`" (`:407`, `:1253-1254`; the tracker's K4 section says
`knowledgeSound_of_refinement`, a name that exists nowhere).

- `verify_knowledgeSound (fs bcs mca flock)`: in ArkLib's shape it bounds, for a fixed
  `stmtIn = input` and every prover, the probability of the event "the compiled verifier
  accepts ∧ ∀ q ∈ (extracted slot), `(input, q) ∉ M3Rel (leanIsaInstance prog s)`" by
  `niError` (`Security/Basic.lean:299-323`, `knowledgeSoundnessWith`; the same event in the
  round-by-round form, `RoundByRound.lean:553`). The slot is an `Option (Column μ)`,
  `Column μ : Type`.
- `satisfiedBy_witnessOf`, made a `Refinement (M3Rel I) (SatRel prog)` with `SatRel prog :=
  {p | SatisfiedBy prog p.1.1 p.2}` on witnesses in `Type 1`: `Refinement`'s two universes
  are independent (probe `Shapes`, output lines 10-13), and the construction typechecks
  (probe `Transport`, example 1). `Refinement.map_option_valid` has the polarity "every
  witness in the slot is valid ⇒ every mapped witness is valid" (`Refinement.lean:55-57`),
  while the game's bad event is "no witness in the slot is valid" (an empty slot is bad);
  the transport of the bad event is `∀ w' ∈ w?.map f, (x, w') ∉ S → ∀ w ∈ w?, (x, w) ∉ R`,
  which follows from `map_valid` in one line (probe `Transport`, `bad_of_bad`), and
  `code-spine.md`'s probe `knowledge_transport` proves the probabilistic statement for
  ArkLib's game in the same way. `Extractor.Straightline.map` cannot serve: its `WitIn'` is in
  `Type` (probe `UniverseFail`: "`EnsembleWitness (leanIsaEnsemble prog)` has type `Type 1` …
  but is expected to have type `Type`").
- `constraintSoundness (hwf : WellFormedBytecode prog)`: pointwise.

The composition typechecks in principle as an inclusion of events (probe `Transport`,
examples 3 and 4): if `¬ ∃ t, ValidExecution prog input t`, then every extracted `q` is
outside `M3Rel`, so the game's bad event is "the verifier accepts", and `Pr[accepts] ≤
niError`. That is the correct form of T4's first half: **a soundness theorem for the
language `{(prog, input) | ∃ t, ValidExecution prog input t}`** (the conclusion is a
closed proposition, so "except with probability" attaches to acceptance, not to it), in the
random-oracle model, for each admissible `s` or with the family composition of B.3, and under
`WellFormedBytecode prog`. It is not, and cannot be, an ArkLib `knowledgeSoundness` of a
relation on `EnsembleWitness` (`WitIn : Type`), nor a statement about the concrete
`verify prog input proof = true` (a closed Boolean), and it does not need the round-by-round
implication if `FiatShamirSecurity` consumes the round-by-round form directly.

## F. `docs/architecture.md` validated against the blueprint and the code

The obligation map for the fourth target theorem (`architecture.md:261-275`, the "Proof
system" list `:446-462`, the ladder `:63-70`), item by item:

| Obligation (`architecture.md`) | In the blueprint | In the code at `b435631` | Verdict |
| --- | --- | --- | --- |
| the bridge "`BaseVerifier.Accepts … → except with probability baseError, ∃ assignment, Constraints.SatisfiedBy …`" (`:264-269`) | `verify_knowledgeSound` + `satisfiedBy_witnessOf` (`:1226-1227`, `:815-816`) | neither; `M3Holds`, `M3Rel`, `Refinement` built | consistent in content; the `version` parameter of the architecture is the pin recorded in prose, not a Lean argument |
| "then compose it with T1-S" (`:270`) | Layer 13 (`:1253-1254`) | `constraintSoundness` not stated | consistent, except that T1-S's hypothesis `WellFormedBytecode` (`architecture.md:224-228`) is dropped in the composed statement (finding 3) |
| expose "the component soundness/knowledge-soundness bounds, Fiat–Shamir or random-oracle model, commitment and hash assumptions, transcript/serialization agreement, and executable-verifier refinement" (`:270-273`) | `niError`, `FiatShamirSecurity`, `BcsSecurity`, `McaJohnson`, `verify_iff_compiled` (`:1218-1228`) | `piopError`, the two master theorems (`Compose.lean:149-185`) | the random-oracle model and the hash assumption are named as interfaces for the *compiled* protocol but the concrete `verify` uses BLAKE2s: the heuristic "BLAKE2s is the random oracle" is exposed nowhere (finding 3); the family composition over `s` is exposed nowhere (finding 6) |
| "Its completeness dual composes T2 with the honest prover and records any failure/resource conditions" (`:273-275`) | `baseProver_complete` composes T1-C, "witness generation (T2) … out of scope" (`:147-148`, `:1255-1256`); no resource condition | nothing built | **divergent**: T2 is replaced by an existence theorem, which does not yield the witness `prove` needs, and no resource condition is recorded although two are load-bearing (finding 4; `docs-debt.md` B.6 item 3) |
| "Relate the executable verifier to the protocol specification, including serialization, transcript order, domain separation, challenge derivation, statement binding, and rejection behavior" (`:453-455`) | Layer 12: `verify_iff_compiled`, the stream order, the tags, `FsState.seed`, total `verify` | nothing built | consistent; "statement binding" needs the injectivity of `prog ↦ bytecodeColumn prog` (B.2, item 1), unstated |
| "Prove completeness of the abstract prover and test or verify completeness of the executable prover" (`:456-457`) | `piop_perfectCompleteness`; `prove` "a specification that runs" (`:158`); the Rust prover by fixture only | `piop_perfectCompleteness` (conditional) | consistent; the executable (Rust) prover's completeness is evidence, not a theorem, as `architecture.md:530-533` allows |
| "T4 — base proof extraction/completeness: proof-system components, T1, and T2" (`:66`) | inputs: the components, T1; not T2 | | as above |
| `leanvm-target.md:123-124`: "T4: formal component notions, Fiat–Shamir assumptions, composed error bound, and verifier refinement"; "each [verifier implementation] accepts exactly the specified protocol and statement encoding" | the first is Layers 10-13; the second is the fixture plus `verify_iff_compiled` | | the Rust and Python verifiers do *not* accept exactly the specified protocol on the public-input check (status finding F18; `code-pubinput.md` G.2), so "exactly" is owed a lemma the blueprint assigns to Layer 12 |

Obligations of the map with no counterpart in the blueprint: T2 in the completeness dual;
the resource conditions; the random-oracle instantiation as an explicit hypothesis; the
statement-binding lemma. Blueprint layers that serve no obligation of T4: none (every layer
feeds `verify` or a theorem about it); three named declarations serve nothing on the chain and
are tests of non-vacuity or candidates for upstream: `witnessOf_stackOf` (E.2),
`Extractor.Straightline.map` (no possible consumer in this repository, E.6),
`piop_rbrKnowledgeSoundness_exists`.

One more point of the architecture the blueprint's T4 loses: "the extracted leanVM witness
should contain ordered `pc`/`fp` steps and the full memory image" (`architecture.md:332-335`,
for T6). The chain has it, `constraintSoundness` giving `AssignmentRepresents (witnessOf prog
s q) t` for the extracted `q`; `baseVerifier_extractsExecution` keeps only `∃ t,
ValidExecution prog input t` (`:1247-1248`), which is a language membership and needs no
extractor at all. Stating the pointwise theorem in the form "for the extractor's `q`, when it
satisfies `M3Holds`, `∃ t, AssignmentRepresents (witnessOf prog s q) t ∧ ValidExecution prog
input t`" costs nothing and is what recursion consumes (note 16).

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

## H. Negative results, what was not done, and what contradicts the brief

**Checked and found consistent** (no finding):

- `M3Holds`'s five clauses against `SatisfiedBy`'s thirteen conjuncts: every conjunct has a
  source (A.4); no conjunct of `SatisfiedBy` is delivered by nothing once the caps hypothesis,
  the boundary lemma, the count derivation and the Flock consequence lemma are in place.
- `w.Constraints` is asserts and lookups only (Clean `93c9d1ef`, `Operations.lean:687-688`,
  probe `Shapes` output 154-159); leanISA emits no lookup and only `JUMP` asserts; so
  `toM3_constraints_iff` is provable in principle.
- The degree bound `d = 2`: every flush coordinate of the six tables read (`Tables/*.lean`
  `main`) is of degree at most two (`JUMP`'s successor `b·v_pc + b·(g·pc) + g·pc`,
  `Jump.lean:199-201`; `DEREF`'s store `fbar·v3 + f_pc·(g²·pc) + f_fp·fp`, `Deref.lean:203-206`;
  `MUL_NATIVE`'s twelve products, `MulNative.lean:168-173`; the pushes' `g · count`).
- The state boundary as constants only (`Coord.committed` needs `τ = κ = 0`, impossible for a
  real column), as `layout.rs:354-358`; the memory and bytecode blocks' committed coordinates
  are columns of tables whose `τ` equals the block's `κ` by construction (E.4).
- `Caps` is derivable from `Admissible` plus the construction of `witnessOf` (A.4 row 5), and
  `Sizes.ofWitness w = some s` from `SatisfiedBy` (A.6).
- The chain names one `prog` and one `input` throughout (B.2); no theorem lets the prover
  choose either.
- The top limb is anchored (section D), agreeing with `code-pubinput.md` §D.
- `Refinement` accepts a `Type 1` target witness (probe `Transport`); the pointwise
  composition of T4 typechecks (examples 3-4); `Extractor.Straightline.map` cannot serve
  (probe `UniverseFail`).
- The axioms of every arithmetization declaration the chain will use (`assumptions_of_
  blake2sRowsValid`, `memRowOf_bindings`, `bytecodeRowOf_bindings`, `bytecodeRowOf_decodes`,
  `verifier_pull_eval`, `verifier_push_eval`, `rowAt_toElements`, `decode_eq_some_iff`,
  `assignmentRepresents_image`, the six tables, the two blocks, the verifier) and of the two
  master theorems, `bytecodeColumn_eval`, `idxColumn_eval`: the kernel's three (probe `Shapes`,
  output 168-187); `map_option_valid`: two.

**Not done, and how it would be verified.**

- The injectivity of `prog ↦ (prog.logSize, bytecodeColumn prog)` (B.2 item 1): inferred from
  `entry_injective` and `bytecodeColumn_slot`; a probe proving it was not written.
- The counterexample program of section D (`SET_CONSTANT [g^0, y²]`): its two-line stack was
  not built; the load-bearing fact, `E.ofLimbs a b c ≠ p.word0` for `c ≠ 0`, is proved
  (probe `Shapes`).
- The count of admissible size vectors (B.3, about `2^34`) is a hand estimate from the caps
  and the stacking window; the exact count depends on the layout's `μ`, which Layer 3 defines.
- Whether CompPoly's `toCMvPolynomial` is still `noncomputable` at the new pin `572f9973` was
  not checked (the review's object is the old pin).
- No probe was re-run after the upgrade; the two probes with numerals other than `0`, `1`
  need `K.ofBits` before a re-run (header).
- The claim that a run of a halting program visits distinct states (note 18) is an argument
  from determinism of `step`, not a Lean proof.

**Contradicts the brief.**

- The leanVM checkout `/home/scaraven/Documents/leanEthereum/leanVM` is **no longer at the
  pin**: on 2026-09-30 its `HEAD` is `248da0719e94ec253af47c930908f087a7be02a1` and the crate
  tree has changed (`crates/leanvm`, `crates/leanvm_core`; no `crates/lean_vm`). The brief
  (§3, §8) and the coordinator's message say it is unchanged at `a386121f`. This task did not
  move it (no `git checkout`, `pull`, `reset` or `switch` was run here; the shell history of
  this task holds only `git rev-parse`, `git status`, `git log`, `git show`, `git cat-file`,
  `git merge-base`). Every Rust citation of this dossier was read from the working tree on
  2026-09-29 when `HEAD` was `a386121f` (verified then), and the ones in sections C-F were
  re-verified on 2026-09-30 with `git show a386121f:<path>` from the object store (the
  commit is present: `git cat-file -t a386121f` = `commit`). Other agents citing the working
  tree after the move would cite the wrong revision.
