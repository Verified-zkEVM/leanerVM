# Roadmap: leanISA semantics and M3 constraints

leanISA is the six-instruction machine of leanVM: two `K`-valued registers, write-once memory of
`E`-valued words addressed by powers of a generator `g`, and a BLAKE2s compression opcode, over

```text
K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1),    E = K[y]/(y^3 + y + 1),    |E| = 2^192.
```

This roadmap builds, in Lean 4, one executable semantics for that machine and the six-table M3
constraint system that proves its executions, and states the two theorems that connect them:

```text
constraintSoundness :
  SatisfiedBy prog input w → ∃ t, AssignmentRepresents w t ∧ ValidExecution prog input t
constraintCompleteness :
  ValidExecution prog input t → ∃ w, SatisfiedBy prog input w ∧ AssignmentRepresents w t
```

The semantics is a single function `step`; the tables are Clean components over CompPoly's
binary fields; the statement is on Clean's `EnsembleWitness`. The route is chosen so that the
**trusted surface** — every definition, load-bearing statement, and hypothesis a reviewer must
read — stays under a few hundred lines, and so that every one of those lines cites the
specification section or the Rust lines it transcribes.

Suggested home: `LeanerVM/Parameters/`, `LeanerVM/Semantics/`, and
`LeanerVM/Arithmetization/`, following the layer ownership of
[architecture.md](architecture.md). The public declarations live in the namespaces
`LeanerVM.Parameters`, `LeanerVM.Semantics`, and `LeanerVM.Arithmetization`.

This document is the specification. The Lean signatures embedded in the layers pin the shapes
most likely to drift; they are not exhaustive. Where things stand is recorded separately in
[leanisa-status.md](leanisa-status.md), which is a snapshot and never the authority on what is
wanted. Work on a layer is claimed through the tracking issue
([#4](https://github.com/Verified-zkEVM/leanerVM/issues/4)); see
[How work is tracked](#how-work-is-tracked).

## For zkVM engineers

Lean is a programming language whose programs are also mathematical definitions, and a checker
for statements about them. A definition such as "one step of the VM" runs on test inputs *and*
is the object theorems are stated about. The checker is small and trusted; a theorem that
passes cannot be wrong relative to the definitions, so the whole risk is whether the definitions
say what we meant. That is why this roadmap spends most of its words on definitions, sources,
and the wrong readings each definition must exclude, and why it reuses Clean's notions of
table, bus, and witness instead of writing its own: those are read once, by everyone who uses
Clean.

Three things are built. **The machine**: one function `step` that, given the program, the
committed memory image, and the two registers, returns the next registers or fails; its cases
are the specification's instruction table in order, and "valid execution" is iterating it from
`(1, 1)` to `(g^(N-1), 1)`. **The tables**: each opcode table is a Clean component that reads the
row's columns, emits the row's bus tuples in the specification's coordinate order, and asserts
the two JUMP identities; each carries a spec ("this row is a `step`") with soundness and
completeness proofs. **The statement**: a witness satisfies every component, the three bus
channel pairs balance as multisets, read counts are nonzero, the caps hold, and the public words
are in place. The bus theorems that turn balance into an execution are the last layers and
consume a change to Clean's bus that is described exactly in
[Dependencies](#dependencies-and-exact-contracts).

## Scope

### In scope

- the fields `K` and `E`, their limb encodings, the generator `g` with a kernel-checked order
  certificate, and exponent addressing;
- the BLAKE2s compression function in tree mode (both finalization flags), the packing of
  128-bit cells, and the metadata cell;
- instructions, programs, the committed memory image, the two-cell public input, `step`, and
  `ValidExecution`;
- opcode codes, the sixteen-slot bytecode encoding, and its decoder;
- the three bus interactions as Clean channels with semantic guarantees;
- the six opcode tables, the memory and bytecode seed/finalize blocks, and the verifier boundary
  as Clean components, each with soundness and completeness;
- `SatisfiedBy` and `AssignmentRepresents`;
- the bus theorems (state walk, memory and bytecode lookup correctness) and the two T1 theorems;
- executable fixtures for every layer, including vectors dumped from the pinned Rust.

### Out of scope

- witness generation (the Rust executor's write-once bookkeeping, back-solving, and hints) —
  owned by the T2 work in `Arithmetization` and specified against `step`;
- Flock's zerocheck and lincheck, ring switching, and the BLAKE2s Boolean circuit — owned by
  [#3](https://github.com/Verified-zkEVM/leanerVM/issues/3); this roadmap consumes only the
  compression *relation* on nine cells;
- GKR, sumcheck, WHIR/Ligerito, Fiat–Shamir, and the stacking of columns — `Protocol`;
- recursion, deferred claims, and the aggregation guest — `Applications` and `Protocol`;
- a degree bound on Clean expressions and prover-chosen table heights as Clean objects — the
  degree of every transcribed coordinate is visibly at most two, and heights enter only through
  the caps.

The first two exclusions are ownership boundaries. A theorem here imports their declarations
when they exist and never rebuilds them under a leanISA-specific spelling.

## Dependencies and exact contracts

A prerequisite below is a named declaration at a pinned revision, an earlier layer here, or a
cited section of a source. The pins are in `upstreams.json` and
[dependencies.md](dependencies.md): leanVM `a386121f`, CompPoly `3468b38c`, Clean `93c9d1ef`,
Lean `v4.33.1`.

### The leanVM specification and implementation

Two kinds of source, with opposite disciplines (the authoring skill `lean-spec-authoring` sets
the rules). **Category A** content — what the machine means — is written from the specification
document first and then diffed against the Rust; the Lean is intended to become the standard.
**Category B** content — encodings, layouts, constants, tuple coordinates — is transcribed from
its source and is wrong if it deviates. Every module docstring names its category, its source
section or file and lines, and the pin.

| Artifact | Category | Source at the pin |
| --- | --- | --- |
| Instruction semantics, halting, public input, nondeterminism | A | specification §2 (`doc/leanvm/body/02-vm-specification.tex`), §8.2, §10.1 |
| Bus balance, lookup rules, boundary tuples | A (meaning) / B (tuple shapes) | specification §5.1, §6.1–§6.4 |
| Field moduli, limb order | B | specification §2 = CompPoly `BF64`/`Ext3` |
| Generator value | B | `crates/primitives/src/field/gf2_64.rs:28` (`F64::G = F64(2)`); `python-verifier/verifier.py:182` |
| Opcode codes, caps, κ bounds | B | specification §6.2, §6.4; `crates/lean_vm/src/tables.rs:79-100`, `cpu/mod.rs` |
| Bytecode slot layout | B | specification §8.1; `crates/lean_vm/src/cpu/layout.rs:252-290` |
| Table columns, constraints, flushes | B | specification §7; `crates/lean_vm/src/tables.rs:436-908` |
| Seed/read/finalize and boundary blocks | B | specification §6.1–§6.2; `crates/lean_vm/src/cpu/layout.rs:355-395` |
| BLAKE2s constants | B | RFC 7693 §2.6–§2.7 |
| BLAKE2s cell and metadata encoding | B | `crates/lean_vm/src/cpu/mod.rs` (`blake2s_compress`); `crates/lean_vm/src/hash_flock.rs:136-139` |
| Table row minimums and fill blocks | B | `crates/lean_vm/src/cpu/filler.rs:36-57`, `crates/lean_compiler/src/filler.rs` |

### CompPoly

| Declaration | Contract used here |
| --- | --- |
| `BF64` | `K`. An `abbrev` for `BitVec 64` with bit `i` the coefficient of `x^i`; `Field`, `Fintype`, `CharP BF64 2`, `DecidableEq`, `Repr`, `Hashable`, `OfNat` instances. Arithmetic is computable and kernel-reducible. |
| `BF64.basePoly_eq`, `BF64.basePoly_irreducible` | The modulus is `x^64 + x^4 + x^3 + x + 1`, irreducible. Cited, never re-proved. |
| `BF64.card_bf64` | `Fintype.card K = 2^64`; the only cardinality fact the generator certificate needs. |
| `BF64.Ext3` | `E`. An `abbrev` for `CompPoly.Extension.Ext BF64.ext3Params`, definitionally `Vector K 3` in limb order `c0 + c1·y + c2·y²`; `Field`, `Fintype`, `Algebra K E`, `CharP E 2`, `DecidableEq`, `Repr`. |
| `BF64.ext3Params_poly`, `BF64.ext3Poly_irreducible` | The modulus is `y^3 + y + 1`. `ext3Params_poly` is what ties the coefficient vector `#v[1, 1, 0]` to that polynomial and is the citation for the limb multiplication formula. |
| `BF64.ext3Gen`, `BF64.ext3Gen_pow_three` | `y` and `y^3 = y + 1`. |
| `BF64.card_ext3` | `Fintype.card E = 2^192`. |
| `CompPoly.Extension.Ext.ofBase`, `Ext.coeff_ofBase` | The embedding `K ↪ E` as the `y^0` limb; `algebraMap K E` by `rfl`. |
| `CompPoly.Extension.Ext.coeff`, `Ext.ofFn`, `Ext.ext`, `Ext.coeff_add/mul/…` | Limb projection and construction, extensionality, and the simp set that evaluates limbs of sums and products. |

CompPoly supplies no generator, no `IsPrimitiveRoot`, and no order lemma for any element; those
are Layer 0 here. `CompPoly.Fields.Binary.Tower` is a different presentation of `GF(2^64)`
whose bit encoding disagrees with `BF64` and is never used.

### Clean

| Declaration | Contract used here |
| --- | --- |
| `FiniteField F` (`Clean/Utils/FiniteField.lean`) | The field interface every Clean object is generic over. Layer 0 supplies the `K` instance; Clean's core never consumes `val` or `size`, only the witness-IR bridge does, and for a 64-bit field its `UInt64` truncation is the identity. |
| `GeneralFormalCircuit F Input Output` with `Assumptions`, `Spec`, `ProverAssumptions`, `ProverSpec`, `soundness`, `completeness` (`Clean/Circuit/Formal.lean`) | One per table and per boundary block. Soundness: constraints plus the guarantees of pulled tuples imply `Spec` and the requirements of pushed tuples. Completeness: an honest row satisfies the constraints. |
| `assertZero`, `witness`, `Channel.emit` (`Clean/Circuit/Basic.lean`, `Channel.lean`) | Constraints, prover-supplied columns, and bus tuples inside a component's `main`. |
| `Channel F Message` with `name` and `Guarantees (message) (data : ProverData F)` (`Clean/Circuit/Channel.lean:9`) | A bus interaction in one direction. `Guarantees` is what a pull may assume; it is stated here against `step` and the committed image. |
| `Air.Flat.Component`, `Air.Flat.Table` (`Clean/Air/FlatComponent.lean`) | A component is one row circuit checked independently on every row, with no adjacent-row access; a table is its rows. |
| `Air.Flat.Ensemble`, `EnsembleWitness`, `EnsembleWitness.Constraints` (`Clean/Air/FlatEnsemble.lean`) | The multi-table carrier and "every component's constraints hold on every row, lookups included". Consumed unchanged. |
| `ConstraintsHold.Soundness`, `Operations.Requirements` (`Clean/Circuit/Operations.lean`) | The shape of per-component soundness: interaction guarantees are hypotheses, requirements are conclusions. |
| `Ensemble.soundness_of_tableSoundness_and_specConsistency` | The composition of per-table soundness into ensemble soundness, used by Layer 10. |

Two Clean notions are *not* consumed, because their definitions do not survive characteristic 2,
and the contract this roadmap needs from their replacements is stated here so that the swap is a
deletion:

| Clean today | Why it is unusable over `K` | Contract required |
| --- | --- | --- |
| `Channel.toRaw` grants `Guarantees` when `mult = -1` and demands `Requirements` when `mult ∉ {-1, 0}` | `1 = -1` in `K`: a push is granted the guarantee it should establish, and requirements are vacuous | direction read from an explicit tag on the interaction, independent of the multiplicity's sign |
| `BalancedInteractions`: `length < ringChar F ∨ ringChar F = 0` and `∀ msg, balanceOf = 0` with `balanceOf` a sum in `F` | `ringChar K = 2` admits at most one interaction, and a field sum cannot count | balance as multiset equality of pushed and pulled messages, counted in `ℕ`, with no characteristic condition |

Until Clean supplies both, each interaction is a *pair* of channels (pull, push) emitted with
multiplicity `1`, so guarantees attach only to pulls and pushes are constrained by `Spec`; and
balance is the three-line `BalancedPair` of Layer 8. The ensemble theorems
`addVm_soundVmChannel_of_soundChannels` (`Clean/Air/Vm.lean:703`) and the `SoundChannels`
machinery (`Clean/Air/OrderedChannel.lean`) are the Layer 9 consumers once the change lands;
Clean issue [#452](https://github.com/Verified-zkEVM/clean/issues/452) is the tracker for the
balance side. Two further named hypotheses of Layer 8 (`IndexColumnsAreRowIndices`,
`SeedRowsAreTheImage`/`BytecodeRowsAreTheProgram`) are removed by Clean PR
[#446](https://github.com/Verified-zkEVM/clean/pull/446), which adds indexed fixed columns and
proof-committed `ProverData`.

### Mathlib

| Declaration | Contract used here |
| --- | --- |
| `orderOf_eq_of_pow_and_pow_div_prime` | Turns the seven prime-factor checks into `orderOf g = 2^64 - 1`. |
| `Nat.Prime` via `norm_num` (`Mathlib.Tactic.NormNum.Prime`) | Primality of `3, 5, 17, 257, 641, 65537, 6700417`. |
| `BitVec.toNat`, `BitVec.ofNat`, `BitVec.eq_of_toNat_eq`, `BitVec.toNat_ofNat` | The `FiniteField K` instance. |
| `List.Perm`, `Multiset` | `BalancedPair`. |

## Pinned conventions

| Subject | Convention |
| --- | --- |
| `K` carrier | `BitVec 64`, bit `i` = coefficient of `x^i`; never the tower presentation. |
| `E` carrier | `Vector K 3`, limb `i` = coefficient of `y^i`; `E.limb`, `E.ofLimbs c0 c1 c2`. |
| `K` inside `E` | `ofK a = a + 0·y + 0·y²`. "`x ∈ K`" means `x.limb 1 = 0 ∧ x.limb 2 = 0` (`IsInK`). A canonical 128-bit word has `x.limb 2 = 0` (`IsCanonical128`). |
| Generator | `g = x = 0x2`, order `2^64 - 1`, certified by seven `decide +kernel` checks. Symbolic everywhere; the value appears once. |
| Addresses | `K` elements. Logical index `i` has address `gpow i = g^i`; `0` is never an address; address `a` is valid for log-size `κ` iff `a = g^i` with `i < 2^κ`. |
| Registers | `pc`, `fp` are `K` elements, never exponents. Initial `(1, 1)`; fall-through successor `(g·pc, fp)`; final `(g^(N_prog - 1), 1)`. |
| Operands | `K` elements, the g-powers `o = g^j`; `SET_CONSTANT`'s immediate is one `E` word. |
| Memory | A committed image `MemImage κ = Fin (2^κ) → E`, total on its addresses. All nondeterminism is the image. |
| Halting | Tested before each fetch; the sentinel slot `g^(N_prog - 1)` is never executed; final `fp = 1` is required. |
| `DEREF` | Reads the pointer `fp·o1` (in `K`), the local `fp·o3` (in every mode), and the target `p·o2`; modes `(f_pc, f_fp) ∈ {(0,0), (1,0), (0,1)}`; `src(pc) = g²·pc`. |
| `JUMP` | The three `K` assertions are unconditional; taken iff `c ≠ 0`; flags `b = c·w`, `c·(b + 1) = 0`. |
| `BLAKE2S` | Tree-mode compression with both flags; metadata `counter = limb 0`, `final = low 32 bits of limb 1`, `last_node = high 32 bits of limb 1`; all nine cells canonical 128-bit; word order transcribed from the Rust. |
| Bus | One Clean channel per interaction and direction (`st/mem/bc` × `pull/push`); the domain separator is the channel; tuples are typed messages in the specification's coordinate order; `read(addr, count, v)` = pull `(addr, count, v)`, push `(addr, g·count, v)`; balance = multiset equality per pair. |
| Opcode codes | `g^0 … g^5` in the order XOR, MUL_NATIVE, SET_CONSTANT, DEREF, JUMP, BLAKE2S. |
| Bytecode slots | Sixteen `K` slots; opcode in slot 3; operands in slots 4..10; `SET`'s `k2` in slot 7; `BLAKE2S` uses all seven; zero elsewhere. |
| Caps | `16 ≤ κ_mem ≤ 32`; every table height `≤ 2^32`; bytecode `≤ 2^32`; the BLAKE2S table has at least `2^3` rows. |
| Trusted surface | Every trusted definition fits on one screen, cites its source line, and appears in [Interfaces](#interfaces-supplied-to-later-work); hypotheses appear in signatures, never in `variable` blocks or unstated instances. |
| Unproved targets | A statement that cannot yet be proved is a block comment at its place, carrying the statement and the consumed dependency. Never `sorry`, `axiom`, or a local re-derivation of the dependency. |
| Proof helpers | `private`, under `/-! ## Proof helpers -/`, never cited from another file. |

## The build, in eleven layers

Every layer names what to define and what to prove, intrinsically. The Lean shown pins the
shapes that would otherwise drift; docstrings are abbreviated. Each layer's tests are part of the
layer. Layers are landed only fully proved; a statement whose proof consumes something not yet
available is written as a block comment at its place (see
[Pinned conventions](#pinned-conventions)).

### Layer 0: fields, limbs, and the generator

`LeanerVM/Parameters/Field.lean`, `LeanerVM/Parameters/Generator.lean`.

Define `K`, `E`, `y`, `ofK`, `E.limb`, `E.ofLimbs`, `IsInK`, `IsCanonical128` as abbreviations
and one-line definitions over the CompPoly declarations of the dependency table, with
`DecidablePred` instances for the two predicates and `ToString E`. Prove `ofK_injective`,
`isInK_iff : IsInK x ↔ ∃ a, x = ofK a`, `ofLimbs_eq : E.ofLimbs c0 c1 c2 = ofK c0 + ofK c1 * y +
ofK c2 * y ^ 2`, and `limb_ofLimbs`.

Supply Clean's field interface for `K` and prove it introduces no second field structure:

```lean
instance : FiniteField K where
  val := BitVec.toNat
  fromNat n := BitVec.ofNat 64 n
  size := 2 ^ 64
  val_lt x := x.isLt
  val_injective := fun _ _ h ↦ BitVec.eq_of_toNat_eq h
  val_fromNat n hn := by simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  val_zero := rfl
  val_one := rfl

example : (@FiniteField.toField K _ : Field K) = inferInstance := rfl
```

Define the generator and certify its order:

```lean
/-- `g = x`. Bound to `crates/primitives/src/field/gf2_64.rs:28` (`F64::G = F64(2)`). -/
def g : K := 0x2
theorem card_sub_one_factorization : (2 : ℕ) ^ 64 - 1 = 3 * 5 * 17 * 257 * 641 * 65537 * 6700417
theorem g_pow_div_three_ne_one : g ^ ((2 ^ 64 - 1) / 3) ≠ 1      -- and six more, one per prime
theorem g_pow_card_sub_one : g ^ (2 ^ 64 - 1) = 1
theorem orderOf_g : orderOf g = 2 ^ 64 - 1
abbrev gpow (i : ℕ) : K := g ^ i
theorem gpow_injOn : Set.InjOn gpow (Set.Iio (2 ^ 64 - 1))
theorem gpow_succ (i : ℕ) : gpow (i + 1) = g * gpow i
theorem gpow_ne_zero (i : ℕ) : gpow i ≠ 0
```

The seven checks are separate theorems proved by `decide +kernel`; primality by `norm_num`;
"every prime dividing `2^64 - 1` is one of the seven" from the factorization and
`Nat.Prime.dvd_mul`. Tests: `#guard`s that `gpow k` is bit `k` for `k < 64`.

### Layer 1: BLAKE2s compression and the cell encoding

`LeanerVM/Parameters/Blake2s.lean`, `LeanerVM/Semantics/Blake2s.lean`.

Transcribe `iv : Vector UInt32 8` and `sigma : Vector (Vector (Fin 16) 16) 10` from RFC 7693
§2.6–§2.7, dumped mechanically. Define the tree-mode compression, the cell packing, the metadata
split, and the nine-cell relation:

```lean
def compress (h : Vector UInt32 8) (m : Vector UInt32 16) (t : UInt64) (f0 f1 : Bool) :
    Vector UInt32 8
def cellWords (x : E) : Vector UInt32 4          -- a canonical `a0 + a1·y` as four LE words
def wordsCell (w : Vector UInt32 4) : E
theorem wordsCell_cellWords (h : IsCanonical128 x) : wordsCell (cellWords x) = x
def unpackMetadata (md : E) : UInt64 × Bool × Bool
def CompressCells (m : Fin 4 → E) (cv0 cv1 out0 out1 md : E) : Prop   -- decidable
```

`CompressCells` requires all nine cells canonical and
`cellWords out0 ++ cellWords out1 = compress (cv words) (message words) t f0 f1` with
`(t, f0, f1) = unpackMetadata md`. Tests: the RFC 7693 vectors for `compress`; one vector for
`cellWords` and `unpackMetadata` dumped from the Rust test `blake2s_computes_the_compression`
(`crates/lean_vm/src/cpu/mod.rs:893`), with the dump command recorded under `scripts/`.

### Layer 2: instructions, programs, the memory image, and the public input

`LeanerVM/Parameters/Isa.lean` (the constants), `LeanerVM/Semantics/Instruction.lean`,
`LeanerVM/Semantics/Memory.lean`.

```lean
inductive Opcode | xor | mulNative | setConstant | deref | jump | blake2s
def Opcode.code : Opcode → K          -- g^0 … g^5 in this order
def minLogMem : ℕ := 16
def maxLogMem : ℕ := 32
def maxLogRows : ℕ := 32
def maxLogBytecode : ℕ := 32
def minLogRowsBlake2s : ℕ := 3

inductive DerefMode | cell | pc | fp
inductive Instr
  | xor (oA oB oC : K)
  | mulNative (oA oB oC : K)
  | setConstant (o : K) (k : E)
  | deref (o1 o2 o3 : K) (mode : DerefMode)
  | jump (oc od of : K)
  | blake2s (om : Fin 4 → K) (ocv oout omd : K)

structure Program where
  logSize : ℕ
  logSize_le : logSize ≤ maxLogBytecode
  code : Fin (2 ^ logSize) → Instr

def MemImage (κ : ℕ) : Type := Fin (2 ^ κ) → E
def gLog? (κ : ℕ) (a : K) : Option (Fin (2 ^ κ))
theorem gLog?_spec (hκ : κ ≤ maxLogMem) : gLog? κ a = some i ↔ a = gpow i
def MemImage.read (L : MemImage κ) (a : K) : Option E := (gLog? κ a).map L
def Program.fetch (prog : Program) (pc : K) : Option Instr := (gLog? prog.logSize pc).map prog.code

structure PublicInput where
  lanes : Fin 4 → K
def PublicInput.word0 (p : PublicInput) : E := E.ofLimbs (p.lanes 0) (p.lanes 1) 0
def PublicInput.word1 (p : PublicInput) : E := E.ofLimbs (p.lanes 2) (p.lanes 3) 0
theorem PublicInput.words_injective : Function.Injective fun p ↦ (p.word0, p.word1)
theorem Opcode.code_injective : Function.Injective Opcode.code
```

`gLog?` is the bounded discrete logarithm, the one non-field computation in the semantics; it is
trusted through `gLog?_spec` only, and its table implementation is never unfolded elsewhere.

### Layer 3: the step function and valid executions

`LeanerVM/Semantics/Step.lean`, `LeanerVM/Semantics/Execution.lean`. Category A: written from
specification §2 before the Rust executor is opened.

```lean
structure Regs where
  pc : K
  fp : K
def Regs.next (r : Regs) : Regs := ⟨g * r.pc, r.fp⟩
def derefSource : DerefMode → Regs → E → E
  | .cell, _, v3 => v3
  | .pc, r, _ => ofK (g ^ 2 * r.pc)
  | .fp, r, _ => ofK r.fp

/-- One step over the fixed image `L` (specification §2, "execute inst"). -/
def step (prog : Program) (L : MemImage κ) (r : Regs) : Option Regs := do
  match ← prog.fetch r.pc with
  | .xor oA oB oC =>
      let vA ← L.read (r.fp * oA); let vB ← L.read (r.fp * oB); let vC ← L.read (r.fp * oC)
      guard (vC = vA + vB); pure r.next
  | .mulNative oA oB oC =>
      let vA ← L.read (r.fp * oA); let vB ← L.read (r.fp * oB); let vC ← L.read (r.fp * oC)
      guard (vC = vA * vB); pure r.next
  | .setConstant o k =>
      let v ← L.read (r.fp * o)
      guard (v = k); pure r.next
  | .deref o1 o2 o3 mode =>
      let p ← L.read (r.fp * o1)
      guard (IsInK p)
      let v3 ← L.read (r.fp * o3)
      let v2 ← L.read (p.limb 0 * o2)
      guard (v2 = derefSource mode r v3); pure r.next
  | .jump oc od of =>
      let c ← L.read (r.fp * oc); let d ← L.read (r.fp * od); let f ← L.read (r.fp * of)
      guard (IsInK c ∧ IsInK d ∧ IsInK f)
      pure (if c = 0 then r.next else ⟨d.limb 0, f.limb 0⟩)
  | .blake2s om ocv oout omd =>
      let m ← (List.finRange 4).mapM fun i ↦ L.read (r.fp * om i)
      let cv0 ← L.read (r.fp * ocv);  let cv1 ← L.read (r.fp * g * ocv)
      let out0 ← L.read (r.fp * oout); let out1 ← L.read (r.fp * g * oout)
      let md ← L.read (r.fp * omd)
      guard (CompressCells m cv0 cv1 out0 out1 md); pure r.next

def Regs.initial : Regs := ⟨1, 1⟩
def Regs.final (prog : Program) : Regs := ⟨gpow (2 ^ prog.logSize - 1), 1⟩
def run (prog : Program) (L : MemImage κ) : ℕ → Regs → Option Regs

structure Trace (prog : Program) where
  κ : ℕ
  image : MemImage κ
  steps : ℕ
def HasPublicBoundary (input : PublicInput) (t : Trace prog) : Prop :=
  minLogMem ≤ t.κ ∧ t.κ ≤ maxLogMem ∧ t.image ⟨0, _⟩ = input.word0 ∧ t.image ⟨1, _⟩ = input.word1
def ValidExecution (prog : Program) (input : PublicInput) (t : Trace prog) : Prop :=
  HasPublicBoundary input t ∧ run prog t.image t.steps Regs.initial = some (Regs.final prog)
def Trace.regs (t : Trace prog) : List Regs
```

Values are read and compared, never computed into memory, so a table row's correspondence with
a step is a `simp`. `ValidExecution` is decidable on concrete inputs. Tests: the Rust executor
test `mul_192bit_word` (`cpu/mod.rs:985`) as a `ValidExecution` by `decide`; a taken `JUMP`; a
`DEREF` in `pc` mode; an out-of-range address giving `step = none`; a `JUMP` with `c = 0` and
`d ∉ K` giving `none`.

### Layer 4: the bytecode encoding

`LeanerVM/Arithmetization/Bytecode.lean`.

```lean
def encodeSlots : Instr → Vector K 16        -- opcode slot 3, operands 4..10, zero elsewhere
def entry (i : Instr) : Vector K 8            -- (opcode, op1, …, op7): the bus lookup entry
def decode : Vector K 8 → Option Instr
theorem decode_entry (i : Instr) : decode (entry i) = some i
theorem entry_injective : Function.Injective entry
```

`decode` is partial: a vector whose opcode is not one of the six codes, or whose `DEREF` flags
are `(1, 1)`, is not an instruction. This is where flag booleanity lives — in the public program,
not in an AIR constraint.

### Layer 5: the bus channels

`LeanerVM/Arithmetization/Channels.lean`.

```lean
structure StateMsg (F : Type) where (pc fp : F)
structure MemMsg (F : Type) where (addr count : F) (v : Vector F 3)
structure BytecodeMsg (F : Type) where (pc count opcode : F) (op : Vector F 7)
-- each `deriving ProvableStruct`

def imageOf (data : ProverData K) : (κ : ℕ) × MemImage κ
def programOf (data : ProverData K) : Program

def StatePull : Channel K StateMsg where
  name := "st.pull"
  Guarantees s data := ∃ n, run (programOf data) (imageOf data).2 n Regs.initial = some ⟨s.pc, s.fp⟩
def MemPull : Channel K MemMsg where
  name := "mem.pull"
  Guarantees m data := (imageOf data).2.read m.addr = some (E.ofLimbs m.v[0] m.v[1] m.v[2])
def BytecodePull : Channel K BytecodeMsg where
  name := "bc.pull"
  Guarantees b data := (programOf data).fetch b.pc = decode (b.opcode ::ᵥ b.op)
def StatePush    : Channel K StateMsg    := { name := "st.push",  Guarantees := fun _ _ ↦ True }
def MemPush      : Channel K MemMsg      := { name := "mem.push", Guarantees := fun _ _ ↦ True }
def BytecodePush : Channel K BytecodeMsg := { name := "bc.push",  Guarantees := fun _ _ ↦ True }

def memRead (addr count : Expression K) (v : Vector (Expression K) 3) : Circuit K Unit := do
  MemPull.emit 1 ⟨addr, count, v⟩
  MemPush.emit 1 ⟨addr, const g * count, v⟩
def bytecodeRead … : Circuit K Unit
```

A pulled state is reachable; a pulled memory tuple is a correct read; a pulled bytecode tuple is
the fetched instruction. Pushes carry no guarantee; what a push must satisfy is the emitting
component's `Spec`.

### Layer 6: the six opcode tables

`LeanerVM/Arithmetization/Tables/{Xor,MulNative,SetConstant,Deref,Jump,Blake2s}.lean`.

Each table is a `GeneralFormalCircuit K Row unit`: `Row` is the table's column list in the
Rust's order; `main` is the specification §7 entry read top to bottom (constraints as
`assertZero`, flushes as interactions in the specification's coordinate order); `Assumptions`
is `True`; `Spec r _ data` is `step (programOf data) (imageOf data).2 ⟨r.pc, r.fp⟩ = some (next)`
with the row's successor; `ProverAssumptions` says the row's reads are the image's values.
`XOR`, as the template:

```lean
structure XorRow (F : Type) where
  pc fp oA oB oC : F
  vA vB : Vector F 3
  rA rB rC rbc : F
def xorTable : GeneralFormalCircuit K XorRow unit where
  main r := do
    StatePull.emit 1 ⟨r.pc, r.fp⟩
    StatePush.emit 1 ⟨const g * r.pc, r.fp⟩
    bytecodeRead r.pc r.rbc (const Opcode.xor.code) ![r.oA, r.oB, r.oC, 0, 0, 0, 0]
    memRead (r.fp * r.oA) r.rA r.vA
    memRead (r.fp * r.oB) r.rB r.vB
    memRead (r.fp * r.oC) r.rC (r.vA + r.vB)
  Spec r _ data := step (programOf data) (imageOf data).2 ⟨r.pc, r.fp⟩ = some ⟨g * r.pc, r.fp⟩
  …
```

Prove soundness and completeness for each. Table-specific targets:

- **MUL_NATIVE.** The result read carries the twelve products over nine limb pairs
  (`vA[0]·vB[0] + vA[1]·vB[2] + vA[2]·vB[1]`, …; Rust `TOWER_LANES`). Prove
  `mul_limbs : a * b = E.ofLimbs (…)` by `Ext.ext` and `simp [Ext.coeff_mul]`; it licenses the
  soundness proof to rewrite the coordinates into `vA * vB`.
- **DEREF.** Columns add `f_pc`, `f_fp`, the pointer `p`, and `v3`; the target read carries
  `(f̄·v3[0] + f_pc·(g²·pc) + f_fp·fp, f̄·v3[1], f̄·v3[2])` with `f̄ = 1 + f_pc + f_fp`. Prove
  `storeCoords_eval`: for each of the three flag settings the coordinate is
  `derefSource mode`. No booleanity constraint (Layer 4).
- **JUMP.** Columns add `w`, `b` as `witness` operations with the honest inverse as generator,
  and the two `assertZero`s `b + c·w` and `c·(b + 1)`, written as residuals; the successor is
  `(b·d + b·(g·pc) + g·pc, b·f + b·fp + fp)`. Prove `flags_sound : b + c·w = 0 → c·(b+1) = 0 →
  b = if c = 0 then 0 else 1` and `flags_complete`.
- **BLAKE2S.** Nine `memRead`s of canonical words (third coordinate `const 0`), no constraints,
  `Spec` through `CompressCells`. The Flock relation on the eighteen low limbs is the named
  `Assumptions` field `Blake2sRelation r`; every consumer of this table carries it until #3
  supplies the circuit.

Tests: one satisfying row per table, accepted by completeness, and one mutated row per table
(a wrong result limb, a wrong flag, a non-canonical BLAKE2S cell) rejected.

### Layer 7: the boundary blocks

`LeanerVM/Arithmetization/Boundary.lean`.

```lean
structure MemRow (F : Type) where (idx cntFin : F) (m : Vector F 3)
def memTable : GeneralFormalCircuit K MemRow unit where           -- seed push, finalize pull
  main r := do MemPush.emit 1 ⟨r.idx, 1, r.m⟩; MemPull.emit 1 ⟨r.idx, r.cntFin, r.m⟩
  …
def bytecodeTable : GeneralFormalCircuit K BytecodeRow unit       -- likewise, entries public
def leanIsaVerifier : GeneralFormalCircuit K PublicIO unit where  -- push initial, pull final
  main _ := do StatePush.emit 1 ⟨1, 1⟩; StatePull.emit 1 ⟨const (gpow (N_prog - 1)), 1⟩
  …
```

Prove soundness and completeness for each; the verifier's `Spec` is "the final registers are
reachable".

### Layer 8: the constraint statement

`LeanerVM/Arithmetization/Statement.lean`.

```lean
def leanIsaEnsemble : Ensemble K PublicIO where
  tables := [⟨xorTable⟩, ⟨mulTable⟩, ⟨setTable⟩, ⟨derefTable⟩, ⟨jumpTable⟩, ⟨blake2sTable⟩,
             ⟨memTable⟩, ⟨bytecodeTable⟩]
  channels := [StatePull.toRaw, StatePush.toRaw, MemPull.toRaw, MemPush.toRaw,
               BytecodePull.toRaw, BytecodePush.toRaw]
  verifier := leanIsaVerifier

/-- Pushed and pulled messages of a pair form the same multiset (specification §5.1). -/
def BalancedPair (w : EnsembleWitness leanIsaEnsemble) (pull push : RawChannel K) : Prop :=
  ((w.interactions.filter (·.channel = push)).map (·.msg)).Perm
    ((w.interactions.filter (·.channel = pull)).map (·.msg))

def IndexColumnsAreRowIndices (w) : Prop       -- `idx` of row `i` is `gpow i`
def SeedRowsAreTheImage (w) : Prop             -- `memTable` rows are `imageOf w.data`
def BytecodeRowsAreTheProgram (w) : Prop       -- `bytecodeTable` rows are `programOf w.data`
def CountsNonzero (w) : Prop                   -- every read pull has `count ≠ 0`
def Caps (w) : Prop                            -- κ, heights, bytecode size, BLAKE2S floor

def SatisfiedBy (prog : Program) (input : PublicInput)
    (w : EnsembleWitness leanIsaEnsemble) : Prop :=
  w.publicInput = input ∧ w.Constraints ∧
  BalancedPair w StatePull.toRaw StatePush.toRaw ∧
  BalancedPair w MemPull.toRaw MemPush.toRaw ∧
  BalancedPair w BytecodePull.toRaw BytecodePush.toRaw ∧
  CountsNonzero w ∧ Caps w ∧
  IndexColumnsAreRowIndices w ∧ SeedRowsAreTheImage w ∧ BytecodeRowsAreTheProgram w ∧
  programOf w.data = prog ∧
  (imageOf w.data).2 ⟨0, _⟩ = input.word0 ∧ (imageOf w.data).2 ⟨1, _⟩ = input.word1

def AssignmentRepresents (w : EnsembleWitness leanIsaEnsemble) (t : Trace prog) : Prop
theorem assignmentRepresents_image : AssignmentRepresents w t → (imageOf w.data).2 = t.image
```

`w.Constraints` is Clean's. `AssignmentRepresents` says the image is the trace's and the state
rows embed the register sequence; the remaining rows are the closed walks of specification §8.3.
The three named hypotheses are the facts Clean cannot yet express (dependency table); they are
faithful — the index column is verifier-computed, the program is public, the memory columns are
the image. Tests: one hand-built `SatisfiedBy` witness for the Layer 3 program, which needs
eight BLAKE2S rows (acceptance test 14).

### Layer 9: bus soundness

`LeanerVM/Arithmetization/Statement.lean`, consuming Clean's direction-tagged, `ℕ`-counted
balance and `addVm_soundVmChannel_of_soundChannels`. Prove:

```lean
/-- Specification Prop. 6.1: balance of the state pair makes every pulled state reachable. -/
theorem state_channel_sound (h : SatisfiedBy prog input w) :
    ∀ i ∈ w.interactions, i.channel = StatePull.toRaw → StatePull.Guarantees i.msg w.data
/-- Specification Lemma 6.3, Thm. 6.4, Cor. 6.5: with nonzero counts and fewer than `2^64 - 1`
reads, balance of the memory pair makes every pulled memory tuple a correct read. -/
theorem mem_channel_sound (h : SatisfiedBy prog input w) :
    ∀ i ∈ w.interactions, i.channel = MemPull.toRaw → MemPull.Guarantees i.msg w.data
theorem bytecode_channel_sound …
```

`mem_channel_sound` is the one leanVM-specific bus argument: a multiset of counts closed under
multiplication by `g` with fewer than `2^64 - 1` elements is empty (Lemma 6.3), because `g` has
full order (Layer 0). The read bound is derived from `Caps` (`≤ 10 · 6 · 2^32`), not assumed.

### Layer 10: constraint soundness and completeness

```lean
theorem constraintSoundness (h : SatisfiedBy prog input w) :
    ∃ t, AssignmentRepresents w t ∧ ValidExecution prog input t
/-- `HasFillBlocks prog`: for every table and every size in `[128, 64, …, 1]` the program
contains a closed walk of that many rows of the table's opcode ending in a `JUMP` back to its
first instruction (`crates/lean_compiler/src/filler.rs`). -/
theorem constraintCompleteness (hfill : HasFillBlocks prog)
    (h : ValidExecution prog input t) :
    ∃ w, SatisfiedBy prog input w ∧ AssignmentRepresents w t
```

Soundness composes Layer 9 with the per-table soundness of Layer 6 through
`soundness_of_tableSoundness_and_specConsistency`. Completeness builds the rows of the run,
then pads each table to a power of two — and the BLAKE2S table to at least eight rows — with
closed walks from the fill blocks; the hypothesis is forced (acceptance test 14).

## Acceptance tests and nearby false statements

The following are part of the roadmap. Each names a reading that compiles and is wrong, and the
witness that rejects it. Where the witness is executable it is a test under `tests/`.

1. **Generator order.** `g = 0x2` has order exactly `2^64 - 1`. An element whose order divides
   `(2^64 - 1)/3` makes addresses `g^i` and `g^(i + (2^64-1)/3)` collide; the seven
   `decide +kernel` checks reject it. A docstring saying "generator" is not a certificate.
2. **Zero address.** `MemImage.read L 0 = none` for every image. `0` is not a power of `g`.
3. **Registers are field elements.** The successor of `pc` is `g·pc`, never `pc + 1`; a
   FemtoCairo-style `pc + 1` is rejected. `1 + 1 = 0` in `K`, so `pc + 1` is not even injective
   on a run.
4. **Final `fp`.** A run reaching `g^(N_prog - 1)` with `fp ≠ 1` is not a `ValidExecution`; the
   bus boundary pulls `(g^(N_prog - 1), g^0)` (specification §6.1) and the Rust asserts it.
   Witness: a `JUMP` to the sentinel with `fp ← g`.
5. **Halting order.** The halting test precedes the fetch, so the sentinel is never executed and
   the program with `N_prog = 1` has the empty execution. A semantics that executes the sentinel
   accepts traces the bus rejects.
6. **`DEREF` reads three cells in every mode.** In `pc` and `fp` modes the local address
   `fp·o3` must still be in range (specification §7.4, third memory read). Witness: a `deref … .pc`
   row with `fp·o3` out of range has `step = none`; a semantics that skips the read accepts it
   while the constraints do not.
7. **`JUMP` assertions are unconditional.** `c = 0` with `d ∉ K` is invalid. A semantics that
   checks `d, f ∈ K` only when taken is rejected.
8. **`JUMP` flags.** `b + c·w = 0 ∧ c·(b + 1) = 0` force `b = [c ≠ 0]`. Booleanity `b·(b + 1) = 0`
   alone admits `b = 1, c = 0` and a wrong successor; `flags_sound` is the theorem, and the
   mutated-row test has exactly that row.
9. **Twelve products.** The `MUL_NATIVE` result coordinate is the fold by `y^3 = y + 1`, five
   limb-products regrouped into three lanes. A five-lane or unfolded product is rejected by
   `mul_limbs`; witness `y · y · y = y + 1`.
10. **Two finalization flags.** `compress` takes `f0` (final) and `f1` (last node). The RFC's
    one-flag `F` ignores the high 32 bits of limb 1 of the metadata cell. Witness: the Rust
    vector with `f0 = 1, f1 = 0`.
11. **Metadata split.** `counter = limb 0`, `final = low 32 bits of limb 1`, `last_node = high
    32 bits of limb 1`. Swapping the two flags is rejected by the same vector.
12. **All nine BLAKE2S cells are canonical.** `CompressCells` requires `limb 2 = 0` on the two
    output cells too. The Rust executor checks only the seven read cells and constructs the
    outputs canonical; the constraints force all nine, and the semantics follows the
    constraints.
13. **Push and pull are not signs.** Over `K`, one Clean channel per interaction with
    multiplicities `±1` grants every component the guarantee on its own pushes and makes every
    requirement vacuous. Witness: a component that pushes an unreachable state passes such a
    soundness theorem. The channel pairs of Layer 5 and the `Spec`-side obligation are the
    accepted form.
14. **Balance counts in `ℕ`.** A message pushed twice and never pulled has field-sum balance
    `2 = 0` in `K`. `BalancedPair` is a `List.Perm`. The same fact makes Clean's
    `Ensemble.Statement` unsatisfiable over `K` beyond one interaction, so no theorem may be
    stated through it.
15. **No empty tables.** Every table has at least one row and the BLAKE2S table at least eight
    (`filler.rs:43`; the verifier enforces `τ_BLAKE2S ≥ 3`). A program with no `BLAKE2S`
    instruction and no fill block has *no* satisfying witness: the eight mandatory rows each
    pull a bytecode entry with opcode `g^5` that the public program lacks. Hence
    `constraintCompleteness` carries `HasFillBlocks prog`; a version without it is false.
16. **Slot layout.** `SET_CONSTANT`'s `k2` rides slot 7 and `BLAKE2S`'s `om3, ocv, oout, omd` ride
    slots 7–10 (specification §8.1). `decode_entry` on every constructor is the test.
17. **Public words.** `word0 = in0 + in1·y` and `word1 = in2 + in3·y`, top limbs zero. Packing
    three lanes into one word is rejected by `words_injective` failing to be the intended map
    and by the Rust seeding of `m[0], m[1]`.
18. **Flag pair `(1, 1)`.** Not an instruction; `decode` returns `none`. No AIR constraint
    enforces flag booleanity because the program is public.
19. **One semantics.** There is no second, relational or interpreter-style definition of a step.
    The Rust executor's write-once conflicts, zero reads of unset cells, `MUL` back-solving,
    `DEREF` fill and deferral, hints, step cap, and filler phase are witness-generation
    behaviour, specified later against `step`, never a second meaning of the machine.

## Interfaces supplied to later work

These names are the public boundary and the reviewer's reading list. The T2 witness-generation
work, the Flock integration (#3), and the `Protocol` layer consume them and do not reconstruct a
step, a table, or a balance predicate under another spelling.

```text
Parameters:       K  E  y  ofK  E.limb  E.ofLimbs  IsInK  IsCanonical128  instFiniteFieldK
                  g  gpow  orderOf_g  gpow_injOn
                  Opcode  Opcode.code
                  minLogMem  maxLogMem  maxLogRows  maxLogBytecode  minLogRowsBlake2s
                  iv  sigma
Semantics:        compress  cellWords  unpackMetadata  CompressCells
                  DerefMode  Instr  Program  Program.fetch
                  MemImage  gLog?  gLog?_spec  MemImage.read  PublicInput  word0  word1
                  Regs  derefSource  step  run  Trace  HasPublicBoundary  ValidExecution
Arithmetization:  encodeSlots  entry  decode  decode_entry
                  StateMsg  MemMsg  BytecodeMsg
                  StatePull  StatePush  MemPull  MemPush  BytecodePull  BytecodePush
                  memRead  bytecodeRead
                  imageOf  programOf
                  xorTable  mulTable  setTable  derefTable  jumpTable  blake2sTable
                  memTable  bytecodeTable  leanIsaVerifier  leanIsaEnsemble
                  BalancedPair
                  IndexColumnsAreRowIndices  SeedRowsAreTheImage  BytecodeRowsAreTheProgram
                  CountsNonzero  Caps  SatisfiedBy  AssignmentRepresents
                  state_channel_sound  mem_channel_sound  bytecode_channel_sound
                  constraintSoundness  constraintCompleteness  HasFillBlocks
```

Everything not listed is a proof, a helper, or a test. The named hypotheses a reviewer must
know are assumed rather than proved are exactly: `IndexColumnsAreRowIndices`,
`SeedRowsAreTheImage`, `BytecodeRowsAreTheProgram` (until Clean #446), `Blake2sRelation` (until
#3), `HasFillBlocks` (forced, acceptance test 15), and the balance conjuncts of `SatisfiedBy`,
which the proof system establishes. There are no axioms and no `variable`-block hypotheses.

### The boundary with the Flock roadmap

Flock (#3) owns the BLAKE2s Boolean circuit, its R1CS lowering, zerocheck, lincheck, and ring
switching. This roadmap owns `compress` and `CompressCells` and consumes nothing from #3; #3
consumes `CompressCells` as the relation its circuit must be sound and complete for, and
supplies the proof that discharges `Blake2sRelation`. No declaration here mentions a Flock
witness, a matrix, or a stack position.

## Ordering and parallelism

Layers 0, 1, and 4 are independent and can begin at once. Layer 2 needs Layer 0; Layer 3 needs
Layers 1 and 2; Layer 5 needs Layers 3 and 4; Layer 6 needs Layer 5, and its six tables are
independent of one another; Layer 7 needs Layer 5; Layer 8 needs Layers 6 and 7. Layer 9 needs
Layer 8 and the Clean contract of the dependency table; until that contract is met its
statements are block comments at their places. Layer 10 needs Layer 9, and its completeness
half additionally needs the fill-block lemma.

Each layer is one pull request (Layer 6 may be two), titled `feat(<layer>): …`, and it lands
with `./scripts/validate.sh` green, its modules registered in `LeanerVM.lean` and
`tests/LeanerVMTests.lean`, and a description naming the layer, the sources and pin, the
category of each new definition, and the T1 obligation it feeds. The first landed production
declaration also enables the kernel axiom audit (`axiom-audit-root: LeanerVM`).

## How work is tracked

- **This document** says what is wanted. It is edited by pull request and does not record
  history, status, or who is doing what.
- **[leanisa-status.md](leanisa-status.md)** says where things stand: coverage per layer, the
  frontier, open findings against the sources, and the decisions still pending. It is
  hand-maintained, headed by the commit it describes, and rewritten whole when a layer lands.
- **Issue [#4](https://github.com/Verified-zkEVM/leanerVM/issues/4)** is the dashboard: the
  layer checklist, links to the pull request that landed each layer, and the frontier. It is
  updated when the status file is.
- **To claim work**, open an issue titled `[Intention]: leanISA — Layer N: …` listing the exact
  targets taken (declaration names from the layer), so the rest stays open, and link it from
  #4. One layer, or a slice of one, per intention. Close it with the pull request that lands the
  slice.
- **To report a problem with this roadmap** — a wrong or unclear target, a source discrepancy, a
  missing prerequisite — open an issue titled `[Roadmap]: leanISA — …` naming the layer and the
  acceptance test or convention it touches. Durable source discrepancies are also recorded in
  [leanvm-target.md](leanvm-target.md).
- Pull requests carry `awaiting-review` when the author is done and `awaiting-author` after a
  review that asks for changes; the reviewer runs the `leanerVM-review` skill's three passes
  (specification, fidelity, hygiene) and reads the changed modules in full.

## References

- leanVM specification document, `doc/leanvm/` at pin `a386121f` (§2 machine, §5 M3 model,
  §6 bus interactions, §7 instruction tables, §8 end-to-end protocol).
- leanVM implementation at the same pin: `crates/lean_vm/src/cpu/{isa,execute,layout,filler}.rs`,
  `crates/lean_vm/src/tables.rs`, `crates/primitives/src/field/`.
- RFC 7693, *The BLAKE2 Cryptographic Hash and Message Authentication Code (MAC)*, §2.6–§2.7,
  §3.2; and the BLAKE2 specification's tree-mode finalization flags.
- Irreducible, *Multi-multiset matching (M3)*, Binius documentation.
- M. Blum, W. Evans, P. Gemmell, S. Kannan, M. Naor, *Checking the correctness of memories*,
  Algorithmica 12 (1994), for the offline memory-checking idea behind the counted lookup.
- [architecture.md](architecture.md) for the T1–T8 ladder and layer ownership;
  [leanvm-target.md](leanvm-target.md) for the pinned revision and its obligation table.
