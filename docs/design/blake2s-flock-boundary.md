# Design note: the BLAKE2S table, Flock, and ring switching

The `BLAKE2S` table of leanISA reads nine memory cells as eighteen `K`-valued limbs and constrains
nothing about them: the compression is proved by Flock, a batched R1CS argument over GF(2) bits,
whose witness is committed packed, 64 bits to one `K` element, and opened through ring
switching. This note answers one question: how the `K`-valued table of
[`LeanerVM/Arithmetization/Tables/Blake2s.lean`](../../LeanerVM/Arithmetization/Tables/Blake2s.lean)
and the Boolean constraint system of Flock are to be reconciled in Lean so that the correctness
of the `BLAKE2S` opcode becomes a theorem rather than the named assumption `Blake2sRelation` it
is today, while the Lean stays faithful to the deployed leanVM.

**Ownership rule.** leanISA owns the constraint system *as a relation* and its *meaning*. For the
`BLAKE2S` table the constraints are three things: the nine bus reads, Flock's R1CS on a block of
`2^14` bits, and the identity between the row's eighteen limbs and the block's input and output
words. leanISA transcribes the R1CS and the slot map exactly and proves that this constraint
system represents a BLAKE2s compression. The protocol owns the *extraction*: from an accepted
proof, a witness satisfying those constraints, one block per `BLAKE2S` row included. How Flock
proves a block (zerocheck, lincheck, ring switching, the packed commitment, the circuit walk)
never appears in leanISA; nothing there mentions `q_flock`, a sumcheck or a challenge.

**Recommendation, in short.** The two worlds meet in one deterministic *encoding*, not in the
ring-switching protocol: the packing `packBits : (Fin 64 → Bool) → K` is a bijection that is
definitional for the pinned representation of `K`, and its inverse `bitOf` is the only
BLAKE2s-specific fact the protocol layer ever needs. leanISA's statement `SatisfiedBy` gains one
conjunct, *the constraints themselves*: for every `BLAKE2S` row there exists a block that
satisfies Flock's R1CS with the constant-one pin and whose input and output words are the row's
limbs. Three theorems, all in `Arithmetization` and all provable now, turn that conjunct into
`Blake2sRelation` inside T1: (1) a generic "circuit ↔ R1CS" theorem over GF(2), (2) a Boolean
theorem "the Flock BLAKE2s circuit computes `compress`", stated on `Bool`/`BitVec` with no field
extension in sight, and (3) the bridge from a block to the row's cells. The protocol's extractor
reads each row's limbs and its block *from the packed witness by definition*, which is exactly
what the Rust verifier does when it re-routes the limb claims; ring switching stays an
ArkLib-style oracle reduction whose soundness theorem mentions `bitOf` and nothing else about
BLAKE2s. No change to Clean, none to ArkLib, none to the landed Layer 6 table; one conjunct is
added to the leanISA `SatisfiedBy` sketch and two protocol-roadmap sketches are tightened.

The idea that prompted this note, "represent ring switching in the frontend as an encoding", is
right about the *witness* (bits and packed words are the same information, related by a
bijection) and must be adjusted about the *constraints*: there is no useful `K`-polynomial form of
the Boolean constraints on packed words (bit extraction is GF(2)-linear, hence a linearized
polynomial of degree up to `2^63` over `K`), so the constraints stay Boolean and the equivalence
to prove is between *relations*, "R1CS on bits" and "`compress` on words", with the packing as
the change of representation. Ring switching is what lets a *verifier* learn evaluation claims
about the bit columns from a commitment to the word column; it does not define what the bits
are.

Pins: leanVM
[`a386121f`](https://github.com/leanEthereum/leanVM/commit/a386121f84292f6fa663aaa3e570c15bc0240ea2),
Clean `93c9d1ef`, ArkLib `dca90385`, CompPoly `3468b38c`, Lean `v4.33.1`. Flock paper: ePrint
2026/1329 (the 45-page copy in the Flock issue's evidence baseline). This is a proposal to
review; nothing below is built. Decisions it asks for are collected in
[Decisions requested](#decisions-requested).

## For zkVM engineers

This section introduces every object the note uses, what it is for, and why it is kept, changed,
or rejected. Readers who know Lean, Clean and ArkLib can skip to [The problem](#the-problem-precisely).

**Lean and specifications.** A Lean definition both runs on inputs and is the object theorems are
stated about; the proof checker is small and trusted, so the risk lives entirely in whether the
definitions say what was meant. leanerVM's policy (`AGENTS.md`, `CONTRIBUTING.md`) forbids
`sorry`, `axiom`, `native_decide` and any admitted dependency in accepted code; a statement that
cannot yet be proved is left unlanded, not marked. Two kinds of source are distinguished. A
*Category A* definition states intent (the leanVM specification document, reasoned about first
and diffed against the Rust afterwards). A *Category B* definition transcribes a deployed
artifact (a column layout, a constant, a circuit) and is wrong if it deviates; it appears as a
*hypothesis* of soundness theorems, so paraphrasing it changes the machine being proved.

**The fields.** `K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)` is the 64-bit binary field; leanerVM
uses CompPoly's `BF64`, an `abbrev` for `BitVec 64` where bit `i` is the coefficient of `x^i`.
Two facts make the rest of this note possible and are checked in the kernel today: addition in
`K` is bitwise XOR (`a + b = a ^^^ b` holds by `rfl`), and the generator `g = 0x2` of Layer 0
is the polynomial variable `x`, so `g ^ k` is the word with only bit `k` set for `k < 64`
(`tests/LeanerVMTests/Parameters/Generator.lean:29`). `E = K[y]/(y^3 + y + 1)` is the 192-bit
extension, a triple of `K` limbs; a memory cell is an `E` word, and a *canonical 128-bit cell* is
one whose third limb is zero (`IsCanonical128`, `E.ofCell v = E.ofLimbs v[0] v[1] 0` in
`LeanerVM/Parameters/Field.lean`).

**The compression.** `compress h m t f0 f1 : Vector UInt32 8` in
`LeanerVM/Semantics/Blake2s.lean` is RFC 7693's BLAKE2s compression with both tree-mode flags as
32-bit words. `cellWords x : Vector UInt32 4` reads a canonical cell as four little-endian words
(low word of limb 0 first). `CompressCells m cv0 cv1 out0 out1 md : Prop` is the nine-cell
relation of the `BLAKE2S` opcode: all nine cells canonical and the output words equal to the
compression of the message and chaining-value words under the counter and flags read from the
metadata cell. It is decidable and is the semantic meaning every table theorem below is measured
against. Nothing in this note changes it.

**Clean.** Clean is the circuit framework the leanISA tables are written in. A
`GeneralFormalCircuit F Input Output` (`Clean/Circuit/Formal.lean:310`) bundles a program `main`
that emits constraints and bus interactions with four statements: `Assumptions` (assumed for
soundness), `Spec` (proved for soundness), `ProverAssumptions` (assumed for completeness) and
`ProverSpec`, plus the two proofs. A `Component F` wraps such a circuit as one row of a flat AIR
table; an `Ensemble F PublicIO` (`Clean/Air/FlatEnsemble.lean:11`) is a list of components, a
list of bus channels and a verifier component; an `EnsembleWitness ens` is the concrete tables
(rows), the prover data and the public input. Clean's own relation is `Ensemble.Statement`: some
witness has the given public input, satisfies every row's constraints (`witness.Constraints`) and
balances every channel (`witness.BalancedChannels`); note that it does *not* include the tables'
`Assumptions`. Clean's composition theorem `soundness_of_tableSoundness_and_specConsistency`
derives an ensemble-level spec from per-table soundness (`TableSoundness`, which takes
`witness.Assumptions` as a hypothesis) provided the ensemble-level assumptions imply every table's
`Assumptions` from the *public input alone* (`AssumptionsConsistency`). That last provision is
what a per-row assumption such as `Blake2sRelation` cannot meet; see D5. Clean also has
`FormalAssertion`, a subcircuit that only asserts constraints on given variables and allocates
none (`Formal.lean:254`), and a full BLAKE3 compression gadget over a prime field
(`Clean/Gadgets/BLAKE3/`) built by chaining adder, XOR and rotation gadgets; both matter for
Alternative B.

**The leanISA table.** `blake2sTable : GeneralFormalCircuit K Blake2sRow Regs` is Layer 6's
component (`LeanerVM/Arithmetization/Tables/Blake2s.lean`). `Blake2sRow K` is the row: `pc, fp`,
seven operands, the nine cells as `Vector K 2` limb pairs (`m0 … m3, out0, out1, cv0, cv1, md`),
nine read counts and a bytecode count, in the Rust's column order (`tables.rs:846-882`). Its
`main` pulls the state, pushes the successor, reads the bytecode entry and the nine cells with a
literal-zero third limb, and emits no constraint. `Blake2sRelation r := CompressCells` on the
row's cells is its `Assumptions` field; `Blake2sSpec` (the row's bindings to program and image
plus one `step`) is its `Spec`. So the table today proves "if the compression holds on the row's
limbs, the row is a valid `BLAKE2S` step", and the compression is the named boundary with Flock.
This note keeps the table exactly as it is.

**The statement.** `SatisfiedBy prog input w` (leanISA Layer 8, a sketch) is the relation the
proof system will prove and extract: Clean's `w.Constraints`, three balanced channel pairs,
nonzero counts, the caps, the three named row hypotheses, and the public words. T1 of
`docs/architecture.md` is `constraintSoundness : SatisfiedBy → ∃ trace, ValidExecution` and
its converse, both with the auxiliary columns existentially quantified rather than identified
with one generator. `docs/architecture.md` also asks that `Constraints.SatisfiedBy` include
"the BLAKE2s relation"; this note makes that the conjunct of D5.

**The protocol roadmap.** `docs/roadmap/protocol-blueprint.md` builds leanVM's verifier as
ArkLib oracle reductions over one committed multilinear `q` (the stack of every column).
`M3Holds prog input s q` (Layer 3) is the polynomial statement the protocol establishes about
`q`; `witnessOf prog s q` rebuilds an `EnsembleWitness` from `q` and `stackOf w` goes the other
way; `satisfiedBy_witnessOf` and `m3Holds_stackOf` are the bridge. `M3Holds` already carries a
BLAKE2S conjunct (`Blake2sRows q`), and Layer 9 names a `FlockInterface` structure with a field
`limbColumns` reading the eighteen limbs from the `q_flock` region (finding F3 of the leanISA
status: the limbs are *virtual* columns in the Rust, ordinary columns in Clean).

**ArkLib.** ArkLib is the Lean library of proof-system building blocks. An `OracleReduction` is
an interactive protocol with a fixed message schedule that turns a claim about one relation into
a claim about another; two properties are proved per reduction and composed: perfect
completeness and round-by-round knowledge soundness with an error per verifier challenge. ArkLib
also has `R1CS.relation R sz stmt matrices wit` (`ArkLib/ProofSystem/ConstraintSystem/R1CS.lean`),
the standard `(A z) ∘ (B z) = C z` over a commutative semiring, which D2 consumes as its
statement form.

ArkLib's ring-switching folder formalizes the Diamond–Posen (DP24) packing protocol, and three
words from it are used below and deserve a plain reading. A **basis** of a field `L` over a
subfield `B` is a list of elements of `L` such that every element of `L` is a unique `B`-linear
combination of them; `K` has the basis `1, x, x^2, …, x^63` over GF(2), which is why a `K`
element *is* 64 bits. Mathlib writes a basis as `Basis ι B L`, where `ι` is the *index type* of
the list; ArkLib's packing profile fixes `ι := Fin κ → Fin 2`, the `κ`-bit strings, so the list
has exactly `2^κ` members and `L` must have dimension exactly `2^κ` over `B`. The index type is
the Boolean cube because packing groups the values of a multilinear at the `2^κ` points that
share the high coordinates into one `L` element, one basis vector per low-coordinate string. A
**ring homomorphism**, written `f : R →+* S` in Lean, is a map between rings that preserves `0`,
`1`, addition *and multiplication*; an additive map that fails to preserve products (such as
`a ↦ a^2 + c · a^4` over a field of characteristic 2, which is GF(2)-linear) is not one. A
**carrier** is the auxiliary ring in which a protocol does its bookkeeping; DP24's is the tensor
product `L ⊗_B L`, a `2^κ`-dimensional algebra over `L` into which `L` embeds twice, as the left
factor `a ↦ a ⊗ 1` and as the right factor `a ↦ 1 ⊗ a`, both ring homomorphisms. ArkLib's
`RingSwitchingProfile B L κ` is the record of exactly these data: the cube-indexed basis, the
carrier `A`, the two homomorphisms `φ₀ φ₁ : L →+* A`, and coordinate maps with their
reconstruction laws. Its protocol then sends one carrier element, draws one batching challenge
`r'' ∈ L^κ`, and runs a relocation sumcheck, all inside `L`. Why leanVM's variant does not fit
this record, and what is reusable anyway, is explained at D6.

**Flock, as deployed.** One BLAKE2s compression is a block `z_t : Fin (2^14) → GF(2)`; the
fixed per-block matrices `A0, B0 ∈ GF(2)^{2^14 × 2^14}` and `C0 = I` encode a Boolean circuit
whose committed wires are the 256 chaining-value bits, the 512 message bits, the 64 counter bits,
the two 32-bit flag words, one constant-one wire at position 512, the 256 output bits, and one
product bit per AND gate of the 320 modular additions (`crates/flock/src/hash.rs:40-84`). The
batch of `2^kbatch` blocks is `z : Fin (2^(14 + kbatch)) → GF(2)` with `A = I ⊗ A0`, and the
R1CS statement is `a(u) b(u) + z(u) = 0` for every `u` (specification Annex C, eq. `flock:eq:r1cs`)
together with `z(512, t) = 1` for every block `t` (eq. `flock:eq:const-one`, enforced by lincheck
through an `α^3` term, `lincheck.rs:154-161`). The prover commits `z` *packed*: the low six
coordinates of `u` become the bit index inside a `K` element, giving `q_flock : Fin (2^(8 + kbatch)) → K`
with `q_flock(u) = Σ_{i<64} z(i, u) x^i` (Annex A, `rs:setting`; `pcs/src/pack.rs:7-21`,
`hash_flock.rs:190-203`). `q_flock` is one region of the stacked `q`. Zerocheck and lincheck
(Annex C.2, C.3) reduce the R1CS to 64 claimed values `s_i = MLE(Q_i)(r)` where `Q_i(u) = z(i, u)`
is the `i`-th *bit column* of `q_flock`; ring switching (Annex A) draws six challenges, forms a
random GF(2)-linear map `Φ : E → E` from them, and reduces the 64 claims to one weighted-sum
claim `Σ_u Φ(eq(r, u)) q_flock(u) = Σ_i x^i Φ(s_i)` that the single WHIR opening discharges.

## The problem, precisely

The eighteen words `m0.lo, m0.hi, …, md.hi` of one `BLAKE2S` row exist in three descriptions:

1. **In the table.** Fields of `Blake2sRow K`, `K`-valued, riding the memory bus tuples
   `(lo, hi, 0)` so that the write-once memory argument binds them to the cells the instruction
   reads.
2. **In Flock's witness.** Bits `z(j, t)` of block `t` at fixed positions: `h` at `0..255`,
   `out` at `256..511`, `m` at `640..1151`, counter at `1152..1215`, flags at `1216..1279`
   (`hash.rs:143-152`).
3. **In the commitment.** `K` words of the `q_flock` region: block `t` occupies words
   `t · 2^8 … t · 2^8 + 255`, and the VM-visible 64-bit word at bit base `64 s` of the block is
   word `t · 2^8 + s`, the *slot* `s` (`hash_flock.rs:79-115`, `SLOT_STRIDE_LOG = 8` at `:223`).

The Rust never commits description 1. The eighteen value columns are `Placement::VIRTUAL`
(`lean_vm/src/witness.rs:13-31`): the table sumcheck's claim on such a column at the row point
`r` is re-routed to the claim on `q_flock` at the point whose low eight coordinates are the slot's
bits and whose high coordinates are `r` (`cpu/mod.rs:443-452`, `:785-810`,
`SlotClaim::Strided`). The specification says the same in one sentence: "`BLAKE2S`'s eighteen
value limbs are columns of its table but live in `q_flock`, not the stack, so their claims route
there" (§8.5, `08-end-to-end-protocol.tex:77`). Description 2 is what the circuit constrains;
description 3 is what is committed and what ring switching speaks about.

The apparent incompatibility is this: a constraint on individual bits of a `K` word is not a
low-degree polynomial constraint on that word. Bit extraction `a ↦ bitOf a i` is GF(2)-linear,
so as a function `K → K` it is a linearized polynomial `Σ_k c_k a^{2^k}` of degree up to
`2^63`; no sumcheck carries it. This is exactly why Flock commits bits packed and needs ring
switching to open bit-column claims against the word commitment. But the *relation* between
descriptions 2 and 3 is fixed and deterministic: `q_flock(u) = packBits (fun i ↦ z(i, u))` and
`z(i, u) = bitOf (q_flock u) i`. In leanerVM's representation of `K` this bijection is
`BitVec.ofFnLE`/`BitVec.getLsbD` and is GF(2)-linear by `packBits (u ^^ v) = packBits u + packBits v`;
the round trip and the linearity were compiled in a scratch file against the pinned toolchain,
the linearity lemma's axiom footprint being `propext, Classical.choice, Quot.sound`. The relation
between descriptions 1 and 3 is the routing above, which in Lean becomes a *definition* of the
extractor (D7). The relation between description 2 and `compress` is a theorem about a Boolean
circuit (D3).

So the formal verification of the `BLAKE2S` table does not need ring switching at all. It needs:
the packing bijection stated once (D1); the circuit and its R1CS with the "faithful encoding"
theorem (D2); the theorem that this circuit computes `compress` (D3); the per-row constraint
"a pinned R1CS block whose words are the row's limbs" and its two-way bridge to
`Blake2sRelation` (D4); a `SatisfiedBy` that carries that constraint for every `BLAKE2S` row
(D5); a ring-switching reduction whose knowledge-soundness theorem is stated over `bitOf` (D6);
and an extractor that reads the row's limbs and its block from the packed region (D7). Ring
switching's soundness argument (Annex A, `rs:sound-maps`) is a self-contained piece of linear
algebra about Frobenius and the GF(2)-basis of `E`; it is owned by the Flock roadmap and never
mentions BLAKE2s.

## The recommended design

```text
   verify accepts                                        (Protocol Layers 11-12: WHIR, Fiat-Shamir)
     ⇓
   oracle verifier accepts ⇒ M3Holds prog input s q      (Protocol Layer 10, rbr knowledge soundness)
     ⇓  Flock reduction's relation                       (D6, Protocol Layer 9, owned by #3)
   FlockRelation L q : ∀ t, BlockR1CS blake2sCircuit (blockOf (qflockOf L q) t) ∧ pin at 512
     ⇓  witnessOf q: row t's limbs := slotWords … t, its block := blockOf … t   (D7)
   SatisfiedBy prog input (witnessOf q), Blake2sBlocks included   (Protocol Layer 3, satisfiedBy_witnessOf)
   ───────────────────── the protocol's obligation ends here ─────────────────────
     ⇓  blockR1CS_iff_trace (D2), blake2sCircuit_trace_out (D3), blake2sRelation_of_flockBlock (D4)
   ∀ BLAKE2S row r, Blake2sRelation r                    (leanISA Layer 10, inside T1-S)
     ⇓  blake2sTable.soundness with h_assumptions := Blake2sRelation r, through TableSoundness
   ∃ trace, AssignmentRepresents w trace ∧ ValidExecution prog input trace         (T1-S)
```

Completeness runs the chain upwards: a valid execution gives rows by `blake2sRowOf`, whose
`Blake2sRelation` is `blake2sRowOf_refines` plus `blake2s_refines_iff` (landed); the block of
each row is `blockOfRow r`, the circuit's trace on the row's words, and `flockBlockOf_blockOfRow`
(D4) shows it satisfies the conjunct; `stackOf w` packs those blocks into the region, and Flock's
honest prover passes by perfect completeness.

Each declaration below is stated intrinsically with the layer that owns it, its category and
source, and the wrong readings it must exclude. Names are proposals.

### D1. The packing, as a bijection (Parameters, extends Layer 0)

`LeanerVM/Parameters/Packing.lean` (`module`). Category B for the bit order (Annex A `rs:setting`:
`q_flock(u) = Σ Q_i(u) x^i`; `pack.rs:21-59`, "least significant bit first";
`hash_flock.rs:190-203`, "word for word"), Category A for the statements.

```lean
/-- Sixty-four bits as one `K` element, bit `i` the coefficient of `x^i`. -/
def packBits (bits : Fin 64 → Bool) : K := BitVec.ofFnLE bits           -- Batteries
/-- Bit `i` of a `K` element. -/
def bitOf (a : K) (i : Fin 64) : Bool := a.getLsbD i
theorem bitOf_packBits (bits) (i) : bitOf (packBits bits) i = bits i
theorem packBits_bitOf (a : K) : packBits (bitOf a) = a
/-- Packing is GF(2)-linear: XOR of bits is addition in `K`. -/
theorem packBits_xor (u v) : packBits (fun i ↦ (u i ^^ v i)) = packBits u + packBits v
/-- Annex A's formula: the packed word is the `K`-sum of the set bits' powers of `x = g`. -/
theorem packBits_eq_sum (bits) : packBits bits = ∑ i, if bits i then gpow i else 0

/-- Unpack a `K`-valued table of `2^n` words into `2^(n + 6)` bits: the low six coordinates of
the bit index are the position inside the word (Annex A: "within-block coordinates are the
low-order coordinates"). -/
def unpackColumn (q : Fin (2 ^ n) → K) : Fin (2 ^ (n + 6)) → Bool :=
  fun j ↦ bitOf (q ⟨j / 64, _⟩) ⟨j % 64, _⟩
def packColumn (z : Fin (2 ^ (n + 6)) → Bool) : Fin (2 ^ n) → K
theorem unpackColumn_packColumn, packColumn_unpackColumn
/-- Layer 1's word split is a bit slice. -/
theorem lowWord_getLsbD (a : K) (i : Fin 32) : (lowWord a).toBitVec.getLsbD i = bitOf a ⟨i, _⟩
theorem highWord_getLsbD (a : K) (i : Fin 32) : (highWord a).toBitVec.getLsbD i = bitOf a ⟨32 + i, _⟩
```

Why here: the bit order is a Layer 0 convention (bit `i` = coefficient of `x^i`) and
`packBits_eq_sum` is the only place Annex A's formula is spelled; `Semantics` and
`Arithmetization` consume it. Why an `Equiv` and not just `unpack`: completeness needs the
forward direction and its round trip. Wrong readings: big-endian packing (rejected by
`packBits (Pi.single 3 true) = gpow 3`, a kernel check); packing across word boundaries (the
`j / 64`, `j % 64` split is the Rust's `flatten_packed_into`, tested against a dumped window,
acceptance test 2). Tests: the three theorems on literals by `decide +kernel`; a `#guard` that
`unpackColumn` of a two-word column reads the Rust's `bit_layout` convention (`pack.rs:82-98`).

`ZMod 2` is the field of Boolean constraints below; the embeddings `Bool ≃ ZMod 2` and
`ZMod 2 →+* K` (`ZMod.castHom`, from `CharP K 2`) are the glue, both existing Mathlib
declarations. Note that `ZMod.algebra K 2 : Algebra (ZMod 2) K` is an `abbrev`, not an instance
(Mathlib avoids a diamond), so any use of ArkLib's `packMLE` for this instance takes it with
`letI`.

### D2. Boolean circuits and their R1CS, generically (Arithmetization, upstream candidate)

`LeanerVM/Arithmetization/Flock/Circuit.lean` (`module`; generic, so it follows the protocol
roadmap's `Generic/` convention with an upstream target, ArkLib `ConstraintSystem` or Clean).
Category A: Annex C.4 (`def:circuit`, `flock:rows`, `flock:forward`, `flock:backward`) and the
Flock paper §4.5. Written from the annex first; the Rust (`gf2.rs`, `hash.rs:295-537`) is
diffed afterwards. Whether this datatype or a Clean circuit over `ZMod 2` is the vehicle is
Alternative B and decision 7; the theorems named here are needed under either vehicle.

```lean
/-- A wire: the constant `1`, a free input, an XOR of earlier wires, or an AND of two. -/
inductive Wire | const | input | xor (preds : Finset ℕ) | and (u u' : ℕ)
/-- A circuit with committed positions: Definition C.1. -/
structure Circuit (k : ℕ) where
  wires : Array Wire                       -- topologically ordered, `wires[0] = .const`
  committed : ℕ → Option (Fin (2 ^ k))     -- the injection `pos`, on sources, ANDs and chosen XORs
  const_pos : committed 0 = some ⟨512, _⟩
  committed_injective : …
  sources_committed, ands_committed : …
def Circuit.eval (c) (inputs : ℕ → Bool) : ℕ → Bool                -- wire values
/-- The block a circuit writes: committed values at their positions, `0` at empty positions. -/
def Circuit.trace (c) (inputs) : Fin (2 ^ k) → Bool
/-- Rows `S^A_w`, `S^B_w` expanded over committed positions (eq. `flock:eq:row-lists`). -/
def Circuit.rowA (c) (j : Fin (2 ^ k)) : Finset (Fin (2 ^ k))
def Circuit.rowB (c) (j : Fin (2 ^ k)) : Finset (Fin (2 ^ k))
/-- `A0`, `B0` as Mathlib matrices over `GF(2)`: the specification form, noncomputable. -/
def Circuit.matrixA (c) : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) (ZMod 2)
/-- One block satisfies the R1CS with `C = I`: computable through the rows. -/
def BlockR1CS (c) (z : Fin (2 ^ k) → Bool) : Prop :=
  ∀ j, ((rowA c j).parity z && (rowB c j).parity z) = z j
theorem blockR1CS_iff_r1cs_relation (c) (z) :
    BlockR1CS c z ↔ R1CS.relation (ZMod 2) ⟨2 ^ k, 2 ^ k, 2 ^ k⟩ ![] (matricesOf c) (toZMod ∘ z)
/-- Annex C.4.2, "the R1CS faithfully encodes the circuit": a pinned satisfying block is the
trace of its own inputs, and every trace satisfies. -/
theorem blockR1CS_iff_trace (c) (z) :
    BlockR1CS c z ∧ z ⟨512, _⟩ = true ↔ ∃ inputs, z = c.trace inputs
/-- The forward walk over any commutative ring (Annex C.4.3): `(A0 W, B0 W)` without a matrix. -/
def Circuit.forwardWalk (c) (W : Fin (2 ^ k) → R) : (Fin (2 ^ k) → R) × (Fin (2 ^ k) → R)
theorem forwardWalk_eq_mulVec [CharP R 2] (c) (W) :
    (c.forwardWalk W).1 = c.matrixA.map (ZMod.castHom (dvd_refl 2) R) *ᵥ W ∧ …
/-- The transpose walk (Annex C.4.4): `A0ᵀ u`, the lincheck verifier's marginal. -/
def Circuit.transposeWalk (c) (u : Fin (2 ^ k) → R) : (Fin (2 ^ k) → R) × (Fin (2 ^ k) → R)
theorem transposeWalk_eq_vecMul …
/-- The batch: `A = I ⊗ A0` on `2^(k + b)` positions, block `t` the high coordinates. -/
def BatchR1CS (c) (b : ℕ) (z : Fin (2 ^ (k + b)) → Bool) : Prop := ∀ t, BlockR1CS c (block z t)
```

Why a circuit as *data* rather than the matrices as data: the matrices have about 89 million
nonzeros (Annex C.3.1) and are never built by the prover or the verifier; both directions of the
protocol are walks of the circuit (`hash.rs:295-537`), and the executable Lean verifier
(protocol Layer 12) must walk it too. The walk theorems make the executable verifier's matrix
evaluation a proved consequence of the specification matrices. Why `BlockR1CS` includes the
empty positions: a zero row forces `z j = 0` there, which is Annex C.1's "stores `0` at empty
positions". Why the pin `z 512 = true` is a hypothesis of `blockR1CS_iff_trace` and not a
consequence: the all-zero block satisfies every R1CS row (row 512 is `z_512 · z_512 = z_512`,
booleanity only), which is precisely the gap Annex C.1's eq. `flock:eq:const-one` closes through
lincheck; a reading that drops the hypothesis is false (acceptance test 3). Why `R1CS.relation`
appears: ArkLib's vocabulary is the statement form the protocol layer and any future Spartan
reuse speak (`ArkLib/ProofSystem/Spartan/Basic.lean` is a zerocheck-then-lincheck PIOP for exactly
this relation, with eight admitted leaves at the pin); nothing in the chain depends on it, so an
admitted ArkLib theorem never enters.

### D3. The BLAKE2s circuit (Arithmetization, Category B)

`LeanerVM/Arithmetization/Flock/Blake2sCircuit.lean` (`module`). Category B: the specific
circuit exists only in the Rust: `crates/flock/src/hash.rs:104-186` (layout constants, sub-block
offsets, bit helpers), `:295-360` (`forward_walk`, the gadget order), `crates/flock/src/gf2.rs:23-31`
(`CARRY_BITS_PER_ADD = 31`, `RIPPLE_BITS_PER_ADD3 = 30`, `ADD3_BITS = 61`), `:109-160`
(`walk_add`, `walk_add3_fused`: the row algebra of the two adders), and
`crates/flock/src/witness.rs:69-102` (the witness parts, the fused adder's shifted ripple slots).
The schedule and lanes are `primitives/src/hash.rs:36-60` (`ROUNDS`, `G_LANES`, `SIGMA`), which
Layer 1 already transcribes as `sigma` and `Blake2s.round`'s call order.

```lean
/-- A 32-bit two-operand adder: 31 carry-product wires at `base`, sum wires by XOR
(`walk_add`; bit 31's carry-out is dropped). -/
def addGadget (x y : WireWord) (base : ℕ) : CircuitBuilder WireWord
/-- The fused three-operand adder: 31 majority products at `base`, 30 ripple products at
`base + 31`, bit 0's ripple product omitted (`walk_add3_fused`). -/
def add3FusedGadget (x y z : WireWord) (base : ℕ) : CircuitBuilder WireWord
/-- One `G`: `ADD3 (a, b, mx); ADD (c, d₁); ADD3 (a₁, b₁, my); ADD (c₁, d₂)` in 184 slots from
`GS_BASE + 184 g`, rotations by 16, 12, 8, 7 as wire renumbering. -/
def gBlock (g : ℕ) …
/-- The circuit: sources at `CV_BASE, MSG_BASE, COUNTER_LO_BASE, COUNTER_HI_BASE, FINAL_BASE,
LAST_NODE_BASE`, the constant at 512, eighty `G` blocks by `sigma` and `G_LANES`, and the
committed finalization XORs `h[i] ^ v[i] ^ v[i + 8]` at `OUT_BASE`. -/
def blake2sCircuit : Circuit 14
/-- The inputs of a block from the words the VM sees. -/
def inputsOf (h : Vector UInt32 8) (m : Vector UInt32 16) (t : UInt64) (f0 f1 : UInt32) : ℕ → Bool
def outWords (z : Fin (2 ^ 14) → Bool) : Vector UInt32 8       -- bits 256..511
def cvWords, msgWords, counterOf, flagsOf : …                -- bits 0..255, 640..1151, …
/-- The circuit computes the compression of Layer 1. -/
theorem blake2sCircuit_trace_out (h m t f0 f1) :
    outWords (blake2sCircuit.trace (inputsOf h m t f0 f1)) = compress h m t f0 f1
/-- And leaves its inputs where it found them. -/
theorem blake2sCircuit_trace_inputs (h m t f0 f1) :
    cvWords (trace …) = h ∧ msgWords (trace …) = m ∧ counterOf (trace …) = t ∧ flagsOf (trace …) = (f0, f1)
```

The proof is structural, not by enumeration: `addGadget` against `x + y` on `UInt32` bit by bit
through core's ripple-carry lemmas `BitVec.getLsbD_add` and `BitVec.carry_succ`
(`Init/Data/BitVec/Bitblast.lean:184-282` at `v4.33.1`), the fused adder likewise with the
majority identity `carry (i+1) = atLeastTwo x_i y_i (carry i)`, then `gBlock = Blake2s.mix`,
the round, and the fold. One constraint on the proof deserves a sentence here because it shapes
effort: `bv_decide` is unavailable. Its certificate check runs through `Lean.ofReduceBool`, the
same trust as `native_decide`; the lexical audit does not see it, but the kernel axiom audit the
repository turns on with its first production declaration would reject the theorem. The
gadget lemmas are the only place this bites, and the core lemmas above are enough.

Fidelity evidence, beyond the theorem: (i) a `#guard` that `blake2sCircuit.trace` on Layer 1's
RFC vector reproduces `compress`, and that `BlockR1CS` decides `true` on it through the walk,
compiled; (ii) a Rust-dumped block `z` from `generate_witness_with_ab_packed_and_lincheck`
(`hash.rs:689-707`) checked equal to the Lean `trace`, position by position, through a dump
script under `scripts/` as Layer 1 does for `cellWords`; (iii) a Rust-dumped pair
`row_values_walk(w)` for a random `w` (`hash.rs:377-384`) compared with the Lean `forwardWalk`,
which pins the matrices to the Rust's beyond any single witness. The baked
`R1CS_DIGEST` (`hash.rs:276-281`) is a fourth check that needs the dense matrices and is left as
an open item ([Decisions requested](#decisions-requested), item 5).

### D4. The per-row constraint and its bridge to the row (Arithmetization)

`LeanerVM/Arithmetization/Flock/Bridge.lean` (`module`). Category B for the slot map
(`hash_flock.rs:79-115`, `SLOTS`, and `tables.rs:394-412`, `BLAKE2S_VALUE_COLS`), Category A for
the theorems. This is the constraint system of a `BLAKE2S` row, as a Lean relation, and the
proof that it represents a BLAKE2s compression.

```lean
/-- The eighteen within-block word slots, in the order of the table's value columns:
`m0.lo, m0.hi, m1.lo, m1.hi` are slots `10..13`; `m2, m3` slots `14..17`; `out0, out1` slots
`4..7`; `cv0, cv1` slots `0..3`; `md.lo, md.hi` slots `18, 19`. -/
def slots : Fin 18 → Fin 256 := ![10, 11, 12, 13, 14, 15, 16, 17, 4, 5, 6, 7, 0, 1, 2, 3, 18, 19]
/-- A row's eighteen limbs in the same order. -/
def rowWords (r : Blake2sRow K) : Fin 18 → K :=
  ![r.m0[0], r.m0[1], r.m1[0], r.m1[1], r.m2[0], r.m2[1], r.m3[0], r.m3[1],
    r.out0[0], r.out0[1], r.out1[0], r.out1[1], r.cv0[0], r.cv0[1], r.cv1[0], r.cv1[1], r.md[0], r.md[1]]
/-- Word `c` of a block: the 64 bits at `64 · slots c`, packed. -/
def blockWord (z : Fin (2 ^ 14) → Bool) (c : Fin 18) : K := packBits (fun i ↦ z ⟨64 * slots c + i, _⟩)

/-- **The constraint system of one `BLAKE2S` row**: a block that satisfies Flock's R1CS, carries
the constant-one pin, and whose eighteen words are the row's limbs. -/
structure FlockBlockOf (r : Blake2sRow K) (z : Fin (2 ^ 14) → Bool) : Prop where
  r1cs : BlockR1CS blake2sCircuit z
  pin : z ⟨512, _⟩ = true
  words : ∀ c, blockWord z c = rowWords r c

/-- Soundness bridge: the constraint system represents the compression. -/
theorem blake2sRelation_of_flockBlock {r z} (h : FlockBlockOf r z) : Blake2sRelation r
/-- The honest block of a row: the trace of the circuit on the row's input words. -/
def blockOfRow (r : Blake2sRow K) : Fin (2 ^ 14) → Bool :=
  blake2sCircuit.trace (inputsOf (cvWordsOfRow r) (msgWordsOfRow r) (counterOfRow r) (flagsOfRow r).1 (flagsOfRow r).2)
/-- Completeness bridge: a row satisfying the compression has a satisfying block, its trace. -/
theorem flockBlockOf_blockOfRow {r} (h : Blake2sRelation r) : FlockBlockOf r (blockOfRow r)
/-- The two together: the constraints on a row are satisfiable iff the row is a compression. -/
theorem flockBlockOf_iff (r) : (∃ z, FlockBlockOf r z) ↔ Blake2sRelation r

/-- The region view, for the protocol: block `t` of a `q_flock` region, and its words. -/
def blockOf (q : Fin (2 ^ (8 + b)) → K) (t : Fin (2 ^ b)) : Fin (2 ^ 14) → Bool :=
  fun j ↦ bitOf (q ⟨t * 256 + j / 64, _⟩) ⟨j % 64, _⟩
def slotWords (q) (t) : Fin 18 → K := fun c ↦ q ⟨t * 256 + slots c, _⟩
theorem blockWord_blockOf (q t c) : blockWord (blockOf q t) c = slotWords q t c
def packBlocks (zs : Fin (2 ^ b) → Fin (2 ^ 14) → Bool) : Fin (2 ^ (8 + b)) → K
theorem blockOf_packBlocks, slotWords_packBlocks
```

Why the canonicality conjuncts of `CompressCells` need no hypothesis: `E.ofCell v` has a zero
third limb by construction, so `Blake2sRelation r` reduces to the word equation; a statement that
adds `IsCanonical128` hypotheses here is redundant (a tautology check, acceptance test 9). Why
`rowWords` is spelled out: it is the order of `BLAKE2S_VALUE_COLS` and the order of the bus
reads of `blake2sTable.main`; `slots` is the Rust's `SLOTS` and is where the two orders meet
(message first in the table, chaining value first in the block). Why `FlockBlockOf` is a
structure with three fields: each is a distinct Category B artifact (the matrices, the pin, the
slot map) and a reviewer checks them separately. Wrong readings: swapping `a` and `b` message
halves (slots 10..13 versus 14..17) or `cv` and `out` (0..3 versus 4..7) is rejected by
acceptance test 2; the metadata split `counter = md.lo`, `f0 ‖ f1 = md.hi` matches Layer 1's
`unpackMetadata` and is pinned by the same vector.

### D5. The statement carries the constraints (leanISA Layer 8, one conjunct)

`SatisfiedBy prog input w` gains the conjunct

```lean
/-- Every `BLAKE2S` row has a block satisfying Flock's constraint system with the row's words. -/
def Blake2sBlocks (w : EnsembleWitness leanIsaEnsemble) : Prop :=
  ∀ r ∈ blake2sRows w, ∃ z, FlockBlockOf r z
/-- Derived, not assumed: the conjunct discharges the table's `Assumptions` field. -/
theorem assumptions_of_blake2sBlocks (h : Blake2sBlocks w) : w.Assumptions
```

Three choices are made here. **The conjunct is the constraints, not the derived relation.**
`SatisfiedBy` means "every constraint of the deployed system holds", and Flock's R1CS is a
constraint of the deployed system; `Blake2sRelation` is what the constraints *mean*, proved from
them by D4 inside T1-S. Stating the relation instead would make the proof system prove a
semantic fact it can only reach through the same bridge, and would put the bridge on the protocol
side, away from the layer that owns meaning. **The block is existential.** This is the T1 style
`docs/architecture.md` prescribes, "auxiliary columns existentially quantified rather than
identified with one particular generator"; the product bits are auxiliary columns. It also keeps
Clean's `EnsembleWitness` unchanged, since a block is not a table row. **`w.Assumptions` becomes
a lemma.** Clean's `Ensemble.Statement` does not mention `Assumptions`, and its composition
theorem `soundness_of_tableSoundness_and_specConsistency` obtains a table's `Assumptions` from
the *public input* (`AssumptionsConsistency`), which a per-row fact cannot come from; so leanISA
Layer 10 derives `w.Assumptions` from `Blake2sBlocks w` through D4 and applies Clean's
`TableSoundness` directly (it quantifies over witnesses and takes `witness.Assumptions` as a
hypothesis). No Clean change; the alternative, changing Clean's `Statement` to carry
`Assumptions`, is a breaking change to a shared library for no gain.

This is the only change to leanISA this note asks for, and it is a change to an unbuilt sketch,
plus one sentence of scope: the leanISA roadmap's "this roadmap consumes only the compression
relation on nine cells" becomes "this roadmap transcribes Flock's constraint system and the slot
map (Category B) and proves they represent the compression; zerocheck, lincheck and ring
switching stay out". T1 reads unchanged: `constraintSoundness : WellFormedBytecode prog →
SatisfiedBy prog input w → ∃ t, …`.

### D6. Flock and ring switching as oracle reductions (Protocol Layer 9, owned by #3)

The protocol blueprint's `FlockInterface` sketch becomes smaller and more concrete. Two of its
fields stop being fields, and no bridge to the compression remains on the protocol side:

```lean
/-- The `q_flock` region of the stack and its blocks: `qflockOf L q : Fin (2 ^ (8 + s.τ 5)) → K`
reads `2^(8 + τ_BLAKE2S)` words at `L.offset QFLOCK` (`cpu/layout.rs:25, 150-157`). -/
def qflockOf (L : StackLayout prog s) (q : Column μ) : Fin (2 ^ (8 + s.τ 5)) → K
/-- Was `FlockInterface.limbColumns`: the eighteen virtual columns are the slot words. -/
def blake2sLimbColumns (L) (q) (c : Fin 18) : Column (s.τ 5) := fun t ↦ slotWords (qflockOf L q) t c
/-- The relation Flock's reduction is knowledge-sound for: the R1CS on the unpacked region. -/
def FlockRelation (L) (q : Column μ) : Prop :=
  ∀ t, BlockR1CS blake2sCircuit (blockOf (qflockOf L q) t) ∧ blockOf (qflockOf L q) t ⟨512, _⟩ = true
```

`FlockRelation L q` replaces the blueprint's `Blake2sRows q` in `M3Holds`. What remains assumed,
and is the Flock roadmap's witness obligation (its gates F3, F4, F5):

```lean
structure FlockInterface (prog) (s) where
  reduction : OracleReduction []ₒ (StmtIn := Unit) (OStmtIn := fun _ : Unit ↦ Column μ) Unit
      (StmtOut := WeightedClaim μ) (OStmtOut := fun _ : Unit ↦ Column μ) Unit pSpecFlock
  perfectCompleteness : reduction.perfectCompleteness … {q | FlockRelation L q} {(c, q) | c.holds q}
  rbrKnowledgeSoundness : reduction.verifier.rbrKnowledgeSoundnessWorstCase … flockError
  flockError_le : ∑ i, flockError i ≤ (4 * s.τ 5 + 163) / |E| + 2 ^ 32 / |E|
```

The eighteen virtual-column claims are *not* part of this reduction: they are the table
sumcheck's column claims, which Layer 10's `Claim.toWeighted` already anticipates as "strided"
claims (the blueprint's Layer 10 sketch), turned into weighted claims on `q` with the weight
`eq((slot bits, r), ·)` on the region; their truth is what `witnessOf`'s definition of the row
limbs makes tautological (D7). This separation matches the Rust exactly: `slot_claims` routes the
column claims (`cpu/mod.rs:790-810`); `verify_reduction` and `ring_switch_verify` produce the one
validity claim (`cpu/mod.rs:759-770`); both meet in the single WHIR opening.

Inside `reduction`, ring switching is its own reduction, stated over D1 and nothing else:

```lean
/-- The `i`-th bit column of a word table, as a `{0, 1}`-valued table over `E`. -/
def bitColumn (q : Fin (2 ^ n) → K) (i : Fin 64) : ETable n := fun u ↦ if bitOf (q u) i then 1 else 0
/-- Annex A: six challenges `f : Fin 6 → E`, the map `Φ` of eq. `eq:phi`, the coefficients `c_k` of
eq. `eq:ck`. -/
def frobeniusMap (f : Fin 6 → E) : E → E                        -- a_{p+1} = a_p + f_p · a_p^(2^(2^(5-p)))
theorem frobeniusMap_add (f) (a b) : frobeniusMap f (a + b) = frobeniusMap f a + frobeniusMap f b
/-- The reduction: input, sixty-four claims `s i = evalMle (bitColumn q i) r`; output, the weighted
claim `⟨Φ ∘ eq(r, ·), q⟩ = Σ_i ofK (gpow i) · Φ(s i)`; one round, six challenges, no message. -/
def ringSwitch (n) : OracleReduction []ₒ (StmtIn := (Fin n → E) × (Fin 64 → E)) … (StmtOut := WeightedClaim n) …
theorem ringSwitch_perfectCompleteness           -- packBits_eq_sum, frobeniusMap_add
theorem ringSwitch_rbrKnowledgeSoundness : … (fun _ ↦ 2 ^ 32 / |E|)     -- Annex A rs:sound-maps, rs:map
/-- The verifier's weight at the opening point (Annex A `rs:weight`). -/
theorem weight_mle (f r r') : evalMle (Φ ∘ eq(r, ·)) r' = ∑ k, c_k f * ∏ n, (1 + (r n) ^ (2 ^ k) + r' n)
```

**Why ArkLib's ring-switching specification is not sufficient.** DP24, and ArkLib's
`RingSwitchingProfile B L κ` after it, has *one* large field `L`: the values are packed into
`L`, the evaluation point and the claimed values live in `L`, the challenges are drawn from `L`,
and the bookkeeping happens in `L ⊗_B L`. leanVM has *two* large fields. The values are packed
into `K` (64 bits, the basis `x^0 … x^63` over GF(2), so the packing step itself fits the
profile with `κ = 6`), but the sumchecks that produce the claims run over `E`, because `|K| = 2^64`
is far too small for the error bounds; so the point `r` and the 64 claimed values `s_i` live in
`E`, not in `K`. Three consequences, each fatal for the record as it stands:

- *The cube-indexed basis.* To evaluate in `E`, DP24 would have to pack GF(2) into `E`, which
  needs a `Basis (Fin κ → Fin 2) (ZMod 2) E`, that is, `2^κ = 192`. There is no such `κ`. Over
  `K` instead, `E` has dimension 3, also not a power of two, and packing into `E` is not what the
  prover does anyway.
- *The two homomorphisms.* DP24 embeds the point and the coefficients into the carrier by two
  ring homomorphisms out of the same `L`. leanVM's natural carrier is `K ⊗_{GF(2)} E` (the
  Rust's `transpose_s_hat`, `pcs/src/tensor_algebra.rs:42`, reads the 64 `E`-values `s_i` as
  192 `K`-values), whose two factors are *different* rings, so there is no `L` to write
  `φ₀ φ₁ : L →+* A` about.
- *The batching map.* DP24 batches the `2^κ` coordinate claims by drawing `r'' ∈ L^κ` and using
  `eq(r'', ·)` on the cube-indexed basis. With 192 coordinates and no cube, leanVM draws six
  challenges `f₀ … f₅ ∈ E` and uses `Φ(a) = a ↦ a + f_p · a^{2^{2^{5-p}}}` composed six times, a
  random GF(2)-linear map `E → E` with a monomial at each Frobenius power `a^{2^k}`, `k < 64`
  (Annex A `rs:map`). `Φ` preserves sums but not products, so it is not a `→+*` and cannot
  occupy `φ₀` or `φ₁`; its soundness argument (Annex A `rs:sound-maps`: 64 Frobenius terms give
  192 `K`-equations against the 192 unknowns of a nonzero error, then Schwartz–Zippel in six
  variables of degree below `2^32`) is not DP24's `κ/|L|` argument.

The message flow differs too: leanVM sends no carrier element and runs no relocation sumcheck;
the 64 values are already bound by lincheck's terminal identity, and the reduction is six
challenges and one weighted claim that the WHIR opening absorbs. Annex A's credits call this
"generalizing ring switching to extension degrees that are not powers of two"; the Flock issue
(#3, gate F5) already asks for "leanVM's rectangular/Frobenius instance its own contracts and
parameter proof". D6's `ringSwitch` is that contract.

**Why not ring-switch into `K` and then embed into `E`?** Because leanVM already does the
first half of that, and the second half is where the soundness lives. Write `eq(r, u) ∈ E` in
the GF(2)-basis `e_w` of `E`, `eq(r, u) = Σ_w E_w(u) e_w` with `E_w(u) ∈ GF(2)`. Then each
claimed `s_i = Σ_u eq(r, u) Q_i(u)` splits into 192 GF(2)-coordinates, and recombining the
coordinate `w` over `i` with `x^i` gives 192 *`K`-valued* claims
`t_w = Σ_u E_w(u) q_flock(u)`, inner products of the committed word column with GF(2)-valued
weights. This step is exact, needs no randomness, and is the Flock paper's "descend to GF(2),
recombine slice-wise" (Appendix B, eq. 8) and Annex A's transposition (`eq:transpose`); the Rust
performs it as `transpose_s_hat`. It *is* "ring switching into `K`", and in Lean it is linear
algebra, generic in `GF(2) ⊂ K ⊂ E`. What remains is 192 claims on `q_flock`, and they must be
batched into one before the opening. Batching with randomness drawn from `K` is unsound at the
target: a nonzero error `(δ_w) ∈ K^192` survives a `K`-random combination with probability
`1/|K| = 2^{-64}`, against the `2^{-160}` Annex A delivers and the `< 2^{-150}` the protocol
roadmap's acceptance test 23 requires. The randomness has to come from `E`, which is exactly
what makes the batched weight `Σ_w λ_w E_w(u)` `E`-valued and the opening an `E`-weighted sum
of `K`-values; the canonical embedding `K ↪ E` is used there, to multiply a `K`-value by an
`E`-scalar, and nowhere else. Drawing 192 independent `λ_w ∈ E` would cost 192 challenges;
leanVM derives them as `λ_w = Φ(e_w)` from six challenges through the Frobenius structure, at
the price of the degree-`2^32` Schwartz–Zippel bound. So the embedding is a step of the
construction, but it is applied to *values* under `E`-randomness, not to a finished `K`-claim:
a single `K`-claim embedded into `E` is still a claim that `2^{-64}` of the adversary's choices
pass. DP24 with `L := K` fails for the same reason twice over: its batching challenge `r''`
lives in `L^κ = K^6`, and its point `r` must be in `K^n`, whereas the sumchecks that produce
`r` and the `s_i` run over `E` precisely because `|K|` is too small for them.

What *is* reusable from ArkLib: the `OracleReduction` framework and its composition theorems, the
sumcheck component, the `eq` polynomial and Schwartz–Zippel lemmas the protocol roadmap already
lists, and the *definitions* `packMLE`/`unpackMLE` as a polynomial-level reference for D1's
`packColumn` (instantiated with `ZMod.algebra K 2` and the power basis of `BF64Quot`, an optional
agreement lemma, not a dependency). A generalized profile with two rings and a carrier
`K ⊗_B E` would be an additive ArkLib proposal that both DP24 and leanVM instantiate; it is not
needed for anything in this note and is listed as an optional upstream item, not a decision.

Sizes: `n_blocks_log = τ_BLAKE2S` exactly, since `min_n_blocks_log n = log₂ (max n 8)` rounded up
(`hash.rs:283-286`) and the table height is `2^τ` with `τ ≥ 3` (`minLogRowsBlake2s`, Layer 2;
verifier cap `cpu/mod.rs:166`); `qflock_kappa = 14 + τ - 6 = 8 + τ` (`hash.rs:764-766`,
`cpu/layout.rs:150-155`: "tau_5 IS n_blocks_log"). So there are no padding instances beyond the
table's rows, every block is an executed compression (fill rows included), and the pin holds for
every block of an honest witness.

### D7. The extractor reads the limbs and the blocks from the region (Protocol Layer 3)

`witnessOf prog s q` builds the `BLAKE2S` rows with `rowWords (row t) := slotWords (qflockOf L q) t`,
and its block for row `t` is `blockOf (qflockOf L q) t`. `stackOf w` fills the region with
`packBlocks (fun t ↦ blockOfRow (row t))`, the honest, computable block of each row. Then:

- `satisfiedBy_witnessOf (h : M3Holds …)` proves `Blake2sBlocks (witnessOf q)` with the witness
  `blockOf (qflockOf L q) t`: `r1cs` and `pin` are `h.flockRelation t`, `words` is
  `blockWord_blockOf`. **This is the exact point where the protocol's obligation meets the
  statement, and it delivers blocks, not relations.**
- `m3Holds_stackOf (h : SatisfiedBy …)` proves `FlockRelation L (stackOf w)`: from
  `h.blake2sBlocks` and `flockBlockOf_iff` each row satisfies `Blake2sRelation`, so
  `flockBlockOf_blockOfRow` gives the R1CS and the pin of `blockOfRow (row t)`, and
  `blockOf_packBlocks` reads it back; `witnessOf_stackOf` on the eighteen limbs is
  `slotWords_packBlocks`.

This is the Rust's "the bus-tied value IS the proven `q_flock` word, no separate check needed"
(`cpu/mod.rs:443-446`), made a definition. Instance `t` and table row `t` are the same index: the
Rust's `fill` walks `trace.blake2s` in order (`tables.rs`, `Blake2sTable::fill`) and the region
is built from the same rows in the same order, reading the nine cells from the finished
write-once image (`cpu/layout.rs:522-546`, "row j = flock instance j"); acceptance test 10
pins it.

### How the table ends up constrained

The Clean table carries no constraint on its eighteen limbs, and it must not: the deployed
table has none (`tables.rs:889-921`, "Constraints: none"). "Properly constrained" is a property
of the *composed statement*, and the chain above is what delivers it. The table below names every
way a limb could escape and what closes it. Each closing item is a theorem or a definition of
D1–D7 or of an existing layer, never a convention, and the type checker enforces the chain: the
proof of `constraintSoundness` can invoke `blake2sTable.soundness` only with a proof of
`Blake2sRelation r` in hand, whose only source is D4 applied to the block that `Blake2sBlocks`
provides; the extractor can prove `Blake2sBlocks (witnessOf q)` only from `FlockRelation L q`,
whose only source is Flock's knowledge soundness. A missing link is a compile error, not a
silent gap.

| A limb could be … | What closes it | Where |
| --- | --- | --- |
| unrelated to the memory cell the instruction reads | the memory bus: the read tuple `(lo, hi, 0)` must balance a write, with the count argument | leanISA Layers 5, 9 (`mem_channel_sound`) |
| different from the `q_flock` word Flock constrains | in Lean the limb *is* the slot word and the block *is* the unpacked region, by the definition of `witnessOf` (D7); in the Rust, by claim routing plus the WHIR opening | protocol Layer 3; `cpu/mod.rs:790-810` |
| a word whose bits do not satisfy the circuit's R1CS | Flock's zerocheck and lincheck knowledge soundness, stated for `FlockRelation` | D6, Flock roadmap F3, F4 |
| in a block that satisfies the R1CS trivially (all zero) | the pin `z 512 = 1` in `FlockBlockOf` and `FlockRelation`, enforced by lincheck's `α^3` term | D2 (`blockR1CS_iff_trace`), D4, D6 |
| in a block whose R1CS is satisfied by a non-trace (a wrong wire assignment) | `blockR1CS_iff_trace`: with the pin, a satisfying block is the trace of its inputs | D2 |
| the trace of a circuit that is not BLAKE2s | `blake2sCircuit_trace_out` against Layer 1's `compress`, plus the Rust dumps for fidelity | D3 |
| read from the wrong slot, or the wrong instance | `slots`, `rowWords`, `blockWord`, instance `t` = row `t`, pinned by dumped windows and a two-row fixture | D4, acceptance tests 2, 10 |
| a counter or flag word the circuit takes as a free input | the metadata cell is read on the memory bus like every other cell, so it is bound as above | Layer 6 `main`, §7.6 |
| a non-canonical cell (nonzero third limb) | the literal `0` third coordinate of every read tuple | Layer 6, acceptance test 12 of the leanISA roadmap |
| present as a limb of an honest row with no valid block behind it (completeness) | `flockBlockOf_blockOfRow`: the trace of the row's inputs satisfies, is pinned, and has the row's words | D4 |

**Where `Blake2sRelation` is consumed and where the constraints are discharged.** The relation
does not travel through the other tables: only `blake2sTable` has a non-trivial `Assumptions`,
and Clean's `w.Assumptions` is the conjunction over all tables, `True` for the other seven. Nor
is it a hypothesis of any theorem or a conjunct of the statement: it is *derived* from the
conjunct `Blake2sBlocks w`. Four places handle it:

1. *Relation consumed*, Layer 6 (landed): `blake2sTable.soundness` takes `Blake2sRelation r` as
   its `h_assumptions` and proves the row is a `step`.
2. *Relation derived and consumed*, leanISA Layer 10 (`constraintSoundness`, T1-S): from
   `h : SatisfiedBy`, for each `BLAKE2S` row take the block `h.blake2sBlocks r` provides, apply
   `blake2sRelation_of_flockBlock` (D4, on top of D2 and D3), and hand the result to Clean's
   `TableSoundness`. **This is where the constraint system is proved to represent the
   compression.**
3. *Constraints discharged on the honest side*, leanISA Layer 10 (`constraintCompleteness`,
   T1-C) and T2: every `BLAKE2S` row is `blake2sRowOf` of a valid step, `blake2sRowOf_refines`
   with `blake2s_refines_iff` (landed) gives its `Blake2sRelation`, and `flockBlockOf_blockOfRow`
   exhibits the block.
4. *Constraints discharged on the adversarial side*, protocol Layers 9 and 3 (T4): the Flock
   phase's knowledge soundness (`FlockInterface.rbrKnowledgeSoundness`, the one assumed field
   until the Flock roadmap proves it) yields `FlockRelation L q`; `satisfiedBy_witnessOf` in
   `LeanerVM/Protocol/M3.lean` turns it into `Blake2sBlocks (witnessOf q)` by exhibiting the
   unpacked block. Nothing in `Protocol` mentions the compression.

A variant was weighed and set aside: stating the *derived* relation `Blake2sRelation` as the
conjunct instead (through Clean's `w.Assumptions`). It reads naturally, but it makes the proof
system responsible for a semantic fact it can only establish through the same D2–D4 bridge, and
so moves the bridge into `Protocol`, away from the layer that owns meaning; and it departs from
the architecture's existential-auxiliary style for T1.

The work, in the order that keeps every intermediate state buildable: D5 first (it only changes
a sketch and makes the obligation visible); D1 (small); D2 (medium: the generic theorem is the
one to review hardest); D3 (the largest: two adder lemmas, then a mechanical composition over 80
`G` blocks, then the Rust dumps); D4 (small once D2 and D3 exist); D7 with protocol Layer 3; D6
with the Flock roadmap's F3–F5, which is the long pole and stays an interface until it lands.
Everything before D6 is provable now and is exactly the witness obligation the interface names.

## What changes where

| Where | Change | Breaking? |
| --- | --- | --- |
| `LeanerVM/Parameters/` | new `Packing.lean` (D1) | additive |
| `LeanerVM/Arithmetization/Flock/` | new `Circuit.lean`, `Blake2sCircuit.lean`, `Bridge.lean` (D2–D4) | additive |
| `LeanerVM/Arithmetization/Tables/Blake2s.lean` | none | no |
| leanISA blueprint Layer 8 (`SatisfiedBy`, unbuilt) | `∧ Blake2sBlocks w`; Layer 10 derives `w.Assumptions` through D4 and applies `TableSoundness` directly; the scope sentence on Flock (D5) | sketch |
| Protocol blueprint Layer 3 (`M3Holds`, `witnessOf`, `stackOf`, unbuilt) | `FlockRelation L q` replaces `Blake2sRows q`; limbs and blocks are read from the region; the region is the packed honest blocks (D7) | sketch |
| Protocol blueprint Layer 9 (`FlockInterface`, unbuilt) | `limbColumns` and the input relation become definitions; no bridge to the compression (D6) | sketch |
| Protocol blueprint Layer 12 (`verify`) | the Flock matrices are evaluated by `forwardWalk`/`transposeWalk` (D2) | none |
| Clean | none | no |
| ArkLib | none required; optional additive lemmas (`blockR1CS_iff_r1cs_relation`, `packMLE` agreement) | no |
| CompPoly | none | no |
| Flock issue #3 | F2 is D2 (generic) plus D3's gadgets; F5's leanVM lane is D6's `ringSwitch`; F8 is D3; F9 is D4, D5, D7; the Clean reuse bullet is superseded by Alternative B's experiment | scoping |

Ownership follows `docs/architecture.md`: encodings in `Parameters`; the circuit, its R1CS, the
per-row constraint, its bridge and the statement in `Arithmetization` ("a Boolean circuit/R1CS
theorem is only an ingredient of T1", issue #3); the reductions in `Protocol`. D2 is generic and
carries the `Generic/` convention: a module docstring naming its upstream target, deleted when
the upstream pull request merges.

## Alternatives considered

**A. Boolean columns in the `BLAKE2S` table over `K`.** Give the table one `K` column per
witness bit, constrain booleanity (`b · (b + 1) = 0` in characteristic 2), and write the adders
as `K` constraints; then Clean proves the compression unconditionally and Flock disappears from
the Lean. Rejected: it is a different machine. The deployed table has 37 columns and no
constraint (`tables.rs:846-921`); this one has about 16,000 columns and 16,000 constraints per
row, so T1 would be proved for a constraint system leanVM does not run, and the protocol
roadmap's degree and size caps would be wrong. It is the natural *repair proposal* if leanVM ever
drops Flock, and nothing else.

**B. The Flock constraint system as a Clean circuit over `ZMod 2`.** Write Flock's block as a
Clean `GeneralFormalCircuit (ZMod 2)` whose row is the whole `2^14`-bit block, whose `main`
allocates nothing and asserts the R1CS through `FormalAssertion` gadgets (so Flock's slot
positions are Clean's column indices by construction), and whose `Spec` is `compress` on the
block's words; D4's `FlockBlockOf` would then be "the Clean constraints hold on `z` and its words
are the row's". This is a serious alternative to D2's bespoke `Circuit`, and it is *open*
(decision 7). What it buys: one statement shape for every constraint system in the repository
and no second constraint-system vocabulary; Clean's gadget composition, with a worked precedent
in Clean's BLAKE3 compression gadget (`Clean/Gadgets/BLAKE3/Compress.lean`, chained adder, XOR
and rotation gadgets composed by `circuit_proof_all`); Clean's witness generation for the honest
block. What stands against it: (1) Flock's protocol needs the exact matrices `A0`, `B0` as
first-class objects, since the deployed lincheck walks them and the Fiat–Shamir seed digests
them, while Clean yields a list of constraints with no R1CS shape by construction, so the
matrices must be extracted from the expressions, the shape proved per gadget, and the walk
theorems proved against the extraction: the R1CS model is reached through Clean rather than
avoided. (2) Clean's compositional proofs pass *variables* between gadgets (its BLAKE3 gadget is
the "all wires committed" encoding); Flock commits only the product bits and substitutes every
XOR and rotation into its consumers, about 89 million nonzeros, so matching Flock's positions
makes the adders' operands expression trees that `circuit_norm` traverses, and Clean at the pin
already hits `maxRecDepth` and `whnf` timeouts on 37-column rows (leanISA findings E6, E7).
(3) A `ZMod 2` table cannot join the `K` ensemble, so the bridge to the `BLAKE2S` row is the
same hand-written D4 under either vehicle. Point (2) is an expectation, not a measurement, and it
decides the question; the experiment of decision 7 measures it.

**C. Keep Flock an assumed interface.** Leave `Assumptions := Blake2sRelation` and
`FlockInterface` a parameter of every protocol theorem. This is the current state and costs
nothing, but the `BLAKE2S` opcode stays unverified and T1 and T4 stay conditional; the interface's
witness obligation is exactly D2–D6. It is the starting point, not an end state.

**D. A Clean channel for the compression.** Make the table pull its eighteen limbs from a
`FlockPull` channel whose `Guarantees` is `CompressCells`, pushed by a `flockTable` component,
so the compression enters the way memory reads do. Rejected: there is no such flush in the
deployed tables (`tables.rs:889-921`); the Rust binds by claim routing, not by a multiset
argument; Clean's bus balance is vacuous over characteristic 2 today (leanISA finding C10); and
it would put a fictional channel into the M3 statement the protocol proves.

**E. Restate the R1CS over `K` words with bit extraction as a `K` operator.** Bit extraction is
GF(2)-linear, hence over `K` a linearized polynomial `Σ_k c_k a^{2^k}` of degree up to `2^63`.
No sumcheck or AIR carries it; this is the reason ring switching exists. Rejected.

**F. ArkLib's `RingSwitchingProfile` and DP24 `Packing` for the ring switch.** Rejected as the
vehicle for the reasons in D6: rank 192 of `E` over GF(2) is not a power of two, and `Φ` is not
a ring homomorphism into a carrier. Its definitions are reusable as a reference (optional).

**G. The derived relation as the `SatisfiedBy` conjunct.** Set aside in D5: it moves the bridge
into `Protocol` and departs from T1's existential-auxiliary style.

## Why this design

- **It is the deployed architecture, transcribed, not a reinterpretation.** Virtual columns are
  slot words (`blake2s_value_slot`); `q_flock` is the packed block list (`flatten_packed_into`);
  the matrices are a circuit walk; the constraints in the statement are Flock's constraints.
  Every Lean definition above cites the line it copies.
- **Meaning is proved where it is owned.** leanISA proves that the constraint system represents
  a compression (D2–D4, inside T1); the protocol extracts a witness of the constraint system and
  never restates what it means.
- **Three concerns, three independent theorems.** D2 is generic and never mentions BLAKE2s; D3
  is a Boolean theorem about `UInt32` adders and never mentions a field extension; D6 is a
  protocol theorem about Frobenius and the GF(2)-basis of `E` that never mentions a circuit.
  They meet only through `packBits`/`bitOf` and `slots`. Each is reviewable by a different
  reader, and a defect in one cannot hide in another.
- **Nothing breaks.** Clean and ArkLib are consumed as pinned; the landed Layer 6 table and its
  tests are untouched; the roadmap changes are to unbuilt sketches.
- **The trusted surface is small and reads in one sitting**: `packBits`, `bitOf`, `slots`,
  `rowWords`, `blockWord`, `Circuit`, `trace`, `BlockR1CS`, `FlockBlockOf`, `Blake2sBlocks`,
  `FlockRelation`, the two reduction statements, and `blake2sCircuit` (the largest, Category B,
  checked against Rust dumps). See [Trusted surface](#trusted-surface).

## Acceptance tests and wrong readings

Each names a reading that compiles and is wrong, and the witness that rejects it. Executable ones
become tests under `tests/` when the layer lands.

1. **Bit order.** Big-endian packing satisfies every round-trip lemma. `packBits (Pi.single 3 true)
   = gpow 3` (kernel) and `packBits_eq_sum` reject it; Layer 0's `gpow k = 1 <<< k` is the anchor.
2. **Slot order.** Swapping the message halves or `cv`/`out` slots changes `blockWord` but not
   `rowWords`; a Rust-dumped `q_flock` window (`qflock_words_match_layout`, `hash_flock.rs:271-311`)
   decoded by `slotWords` must give the row's limbs, `#guard`ed.
3. **The all-zero block.** `BlockR1CS blake2sCircuit 0` holds. `blockR1CS_iff_trace` without the
   pin hypothesis is false; the pin is lincheck's `α^3` term and must stay in `FlockBlockOf` and
   `FlockRelation`.
4. **Flags as words.** The circuit takes `f0, f1` as 32 free bits each with no booleanity (decision
   6 of the leanISA status, `hash.rs:150-151`); a block with `f0 = 0x1234` satisfies the R1CS and
   `CompressCells` accepts the corresponding metadata cell (Layer 1 acceptance test 10).
5. **Metadata split.** `counter = md.lo` (slot 18, bits `1152..1215` as `t_lo ‖ t_hi`) and
   `f0 ‖ f1 = md.hi` (slot 19); swapping the flags is rejected by Layer 1's vector.
6. **Padding.** With `τ ≥ 3`, `n_blocks_log = τ`; a reading that pads the region with
   `padding_block` instances beyond the rows would break `witnessOf_stackOf` on the region's
   length; `qflock_kappa` is a `decide` at `τ = 3`.
7. **Adder boundaries.** The fused adder has no ripple product at bit 0 and no carry at bit 31
   (`gf2.rs:26-31`); a gadget lemma proved on literals only, or by `bv_decide`, is not accepted;
   the structural lemma over all inputs is.
8. **Characteristic 2 hygiene.** `a + b = a ^^^ b` is `rfl`, `-1 = 1`; core's `BitVec` simprocs
   misread `K` numerals (leanISA finding E6); proofs in `Flock/` use `simp only` with named lemmas.
9. **No redundant hypotheses.** `blake2sRelation_of_flockBlock` takes no `IsCanonical128`
   hypothesis: `E.ofCell` is canonical by construction. A version that takes one still compiles;
   the substitution test (the same proof goes through with the hypothesis deleted) flags it.
10. **Instance alignment.** Instance `t` is row `t`. A two-row fixture whose rows differ in
    `m0` rejects the reversed order through `witnessOf_stackOf`.
11. **Clean's composition wall.** `soundness_of_tableSoundness_and_specConsistency` with
    `Assumptions := fun _ ↦ True` cannot discharge `Blake2sRelation`; the Layer 10 proof that
    tries it fails at `AssumptionsConsistency`. Deriving `w.Assumptions` from `Blake2sBlocks` and
    applying `TableSoundness` directly is the fix, not a Clean change.
12. **Ring switching's map.** A `Φ` with support smaller than 64 Frobenius powers (five challenges)
    is not injective on the error space (Annex A: 192 equations against 192 unknowns is tight);
    `ringSwitch_rbrKnowledgeSoundness` must fail to prove for `Fin 5 → E`, and the degree bound
    `2^32` is `RING_SWITCH_SOUNDNESS_DEGREE` (`ring_switch.rs:80-85`), a `decide`.
13. **The conjunct is not vacuous.** `flockBlockOf_blockOfRow` on the row of Layer 1's RFC
    vector exhibits a block, checked compiled (`#guard` on `BlockR1CS` through the walk and on
    `blockWord = rowWords`); a `Blake2sBlocks` that no honest witness satisfies would make T1-C
    unprovable, and this guard is the early warning.

## Decisions requested

1. **Amend leanISA Layer 8, Layer 10 and the scope section** as in D5: `SatisfiedBy ∧ Blake2sBlocks w`,
   Layer 10 derives `w.Assumptions` through D4 and applies `TableSoundness` directly, and the
   out-of-scope sentence on Flock becomes "transcribes the constraint system and the slot map,
   proves they represent the compression; zerocheck, lincheck and ring switching stay out".
   Through a `docs(leanisa)` pull request referencing #4.
2. **Amend protocol Layers 3 and 9** as in D6 and D7: `FlockRelation L q` replaces `Blake2sRows q`
   in `M3Holds`; `limbColumns` and the input relation become definitions; the virtual-column
   claims are strided pool claims of Layer 10; `witnessOf` exhibits the unpacked block. Through a
   `docs(protocol)` pull request referencing #12; the Flock issue #3 gets a comment mapping F2,
   F5, F8, F9 to D2–D7 and noting that its Clean reuse bullet is settled by decision 7.
3. **Ownership of D2.** Proposed: `LeanerVM/Arithmetization/Flock/Circuit.lean` under the
   `Generic/` convention with ArkLib `ConstraintSystem` as the upstream target (Clean is the other
   candidate; ArkLib is preferred because `R1CS.relation` and the Spartan PIOP already live there).
4. **Field of the R1CS statement.** `ZMod 2` for `BlockR1CS`'s matrix form and ArkLib's relation,
   `Bool` for the executable check and all BitVec proofs, related by `toZMod`. The alternative
   (everything in `Bool`, no `ZMod 2`) loses `R1CS.relation` and the protocol's embedding into `E`.
5. **`R1CS_DIGEST`.** The Fiat–Shamir seed absorbs a digest of the dense matrices
   (`hash.rs:263-281`) that the Rust can no longer recompute. Recomputing it from the Lean
   `blake2sCircuit` is the strongest possible fidelity check of D3 but needs the dense
   `2^14 × 2^14` bit images (three 32 MiB matrices) hashed by BLAKE2s, a native-execution task.
   Proposed: the walk-vector differential test (D3, evidence iii) as the standing test now, the
   digest recomputation as a one-off native check recorded in the status file when Layer 12
   transcribes the seed.
6. **`bv_decide`.** Confirm it stays out (it depends on `Lean.ofReduceBool`); the adder proofs are
   structural through core's `carry_succ`. If the policy ever admitted it, D3's proof would
   shrink, and nothing else in this note would change.
7. **The vehicle for the constraint system: D2's `Circuit` or a Clean circuit over `ZMod 2`
   (Alternative B).** Proposed: settle it by a bounded experiment before any layer lands. One
   32-bit two-operand adder as a `FormalAssertion (ZMod 2)` with expression-valued operands and
   31 product-bit inputs, spec "the sum wires evaluate to `x + y`", soundness proved; then one
   `G` block (two fused and two plain adders, rotations as renumbering); measure compile time and
   record the proof shape. If it goes through in reasonable time, the Flock block becomes a Clean
   component, the gadget proofs are Clean's, and D2 shrinks to the R1CS extraction and the
   walks; otherwise D2 stands as written. Either way `FlockBlockOf`, `Blake2sBlocks` and the
   chain above are unchanged.

## Trusted surface

What a reviewer must read and believe; everything else is a proof or a test.

| Declaration | Where | Category | Source |
| --- | --- | --- | --- |
| `packBits`, `bitOf`, `unpackColumn`, `packColumn` | D1 | B | Annex A `rs:setting`; `pack.rs:7-21`; `hash_flock.rs:190-203` |
| `Circuit`, `trace`, `rowA`/`rowB`, `BlockR1CS`, `BatchR1CS` | D2 | A | Annex C.1, C.4.1, C.4.2 |
| `blake2sCircuit`, `inputsOf`, `outWords`, … | D3 | B | `flock/src/hash.rs:104-186, 295-360`; `gf2.rs:23-160`; `witness.rs:69-102` |
| `slots`, `rowWords`, `blockWord`, `FlockBlockOf`, `blockOf`, `slotWords`, `blockOfRow` | D4 | B | `hash_flock.rs:79-115`; `tables.rs:394-412`; Annex C `flock:eq:const-one` |
| `SatisfiedBy … ∧ Blake2sBlocks w` | D5 | A | `docs/architecture.md` (T1, "the BLAKE2s relation") |
| `qflockOf`, `FlockRelation`, `FlockInterface`, `bitColumn`, `frobeniusMap`, `ringSwitch` (statements) | D6 | A | Annex C `flock:statement`, `flock:ringswitch`; Annex A `rs:reduction`, `rs:map`; `cpu/layout.rs:25, 150-157` |
| `witnessOf`, `stackOf` on the `BLAKE2S` rows and the region | D7 | B | `cpu/mod.rs:443-452, 790-810`; `witness.rs:13-31`; `cpu/layout.rs:522-546` |

Assumed interfaces after this note: `FlockInterface` (until #3 supplies its four fields), the
three named row hypotheses of `SatisfiedBy`, `WellFormedBytecode`, and the balance conjuncts.
`Blake2sRelation` leaves the list of standing hypotheses: it is derived from the constraints
inside T1.

## References

- leanVM at `a386121f`: `doc/leanvm/body/07-instruction-tables.tex` §7.6 (`sec:tab-blake2s`),
  `04-committing-the-witness.tex` (`sec:stacking`, `sec:ringswitch`), `08-end-to-end-protocol.tex`
  §8.5, Annex A (`a-ring-switching.tex`), Annex C (`c-flock-protocol.tex`);
  `crates/lean_vm/src/{tables.rs, hash_flock.rs, witness.rs, cpu/mod.rs, cpu/layout.rs}`,
  `crates/flock/src/{hash.rs, gf2.rs, witness.rs, lincheck.rs}`, `crates/pcs/src/{pack.rs, ring_switch.rs, tensor_algebra.rs}`.
- B. Bünz, R. D. Rothblum, W. Wang, *Flock: Fast Proving for Batch Boolean Computations*, ePrint
  2026/1329: §4.1 (batch R1CS), §4.5 (circuit walking), §4.6 (slot-aligned I/O regions),
  Appendix A (full protocol), Appendix B (ring switching, "descend to GF(2), recombine slice-wise").
- B. Diamond, J. Posen, *Polylogarithmic proofs for multilinears over binary towers* (DP24), for
  the packing idea and the tensor-algebra evaluation the Rust verifier uses.
- Clean `93c9d1ef`: `Clean/Circuit/Formal.lean` (`GeneralFormalCircuit`, `FormalAssertion`),
  `Clean/Air/FlatComponent.lean` (`Component`, `weakSoundness`), `Clean/Air/FlatEnsemble.lean`
  (`Ensemble`, `EnsembleWitness`, `Statement`, `TableSoundness`,
  `soundness_of_tableSoundness_and_specConsistency`), `Clean/Gadgets/BLAKE3/` (the prime-field
  compression gadget Alternative B refers to).
- ArkLib `dca90385` (reviewed at the local checkout `9c2f3379`, which is later and additive on
  the files cited): `ArkLib/ProofSystem/ConstraintSystem/R1CS.lean`, `ArkLib/ProofSystem/Spartan/Basic.lean`,
  `ArkLib/ProofSystem/RingSwitching/{Basic, Packing/Profile, Packing/Prelude, Packing/General}.lean`,
  `docs/kb/concepts/ring-switching.md`.
- leanerVM: [architecture.md](../architecture.md) (T1–T8, layer ownership),
  [leanvm-target.md](../leanvm-target.md), [leanisa-blueprint.md](../roadmap/leanisa-blueprint.md)
  (Layers 0, 1, 6, 8, 10), [leanisa-status.md](../roadmap/leanisa-status.md) (decision 6,
  findings C10, E6, F3), [protocol-blueprint.md](../roadmap/protocol-blueprint.md) (Layers 3, 9,
  10, 12), issues [#3](https://github.com/Verified-zkEVM/leanerVM/issues/3),
  [#4](https://github.com/Verified-zkEVM/leanerVM/issues/4),
  [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12).
