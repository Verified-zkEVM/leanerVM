# Review: leanISA Layer 6 table contracts

Reviewed on 2026-09-14 against commit
`c4e0fef50e581ba46e163096491deb4f0346317c` (`feat(arithmetization): leanISA Layer 6: the six
opcode tables`). This is an implementation handoff: the findings are confirmed against that
commit; the proposed contracts and theorem names below are work to implement.

The requested outcome is stronger, opcode-specific table specifications and a clear path from
valid semantic steps to satisfying rows, using Clean's witness generation where applicable.
Keep `Semantics.step` as the common semantic reference.

## Scope and evidence

The review covered all six files in
[`LeanerVM/Arithmetization/Tables/`](../../LeanerVM/Arithmetization/Tables/), the change to
[`Channels.lean`](../../LeanerVM/Arithmetization/Channels.lean), the new
[`table tests`](../../tests/LeanerVMTests/Arithmetization/Tables.lean), and the relevant Clean
definitions. Table formulas and column layouts were compared with `crates/lean_vm/src/tables.rs`
and `doc/leanvm/body/07-instruction-tables.tex` at leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2`. Clean was inspected at
`93c9d1ef45be9f687214625d7857889cf2485504`.

Validation of the reviewed commit passed:

- `./scripts/validate.sh`, including build, tests, warning checks, and repository policy.
- `#print axioms` on all six table declarations: only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Separate Lean experiments confirming the weak specifications and deriving XOR's result-read
  assumption from a semantic step. Reproducible examples are included below; they do not depend
  on the review session's temporary files.

No counterexample to the tables' stated conditional soundness was found. The findings concern
the strength of the exported contracts, their completeness interpretation, and regression
coverage. The BLAKE2s/Flock and global bus obligations remain explicit boundaries.

Read [the root guide](../../AGENTS.md), [contributing conventions](../../CONTRIBUTING.md),
[architecture](../architecture.md), and the [leanISA roadmap](../roadmap/leanisa-blueprint.md)
before implementation.

## Findings

### R1: the public specifications forget the opcode and row values

All six definitions currently use:

```lean
Spec r next data := step (programOf data) (imageOf data).2 ⟨r.pc, r.fp⟩ = some next
```

For example, see `xorTable` in
[`Xor.lean`](../../LeanerVM/Arithmetization/Tables/Xor.lean), lines 123–132 at the reviewed
commit. This proposition depends on `pc` and `fp`, but ignores the row's operands, read words,
immediate, and mode flags. Kernel-checked consequences:

- An alleged XOR row at the fixture's SET instruction, with all three operand addresses zero,
  satisfies `xorTable.Spec`. Its bytecode pull fails.
- Replacing any XOR row's `vA` with an arbitrary vector leaves `Spec` definitionally unchanged.
- Replacing the honest DEREF row's flags with `(1, 1)` leaves its `Spec` true, although that
  flag pair is not a valid mode and its bytecode pull fails.

The soundness proofs already recover the fetched opcode from `BytecodePull.Guarantees` and
bind the input values through `MemPull.Guarantees`. Their final conclusions discard those
facts. A caller receiving only `Spec` cannot recover them.

**Required change:** export opcode-specific predicates that bind the semantic content of each
row and describe the operation it performs. Retain the current step statement as a corollary.
Do not put the new opcode/read facts into soundness `Assumptions`: the circuit must establish
them from its pulls.

### R2: current completeness is conditional row acceptance, not a semantic converse

At the pinned Clean revision, `Clean/Circuit/Formal.lean` defines
`GeneralFormalCircuit.Completeness` using `ProverAssumptions`, the input/environment agreement,
and `UsesLocalWitnessesCompleteness`. It concludes `ConstraintsHold.Completeness` and
`ProverSpec`. It does not take `Spec` or soundness `Assumptions` as premises. The two contracts
are deliberately independent; the tables leave `ProverSpec` at its default `True`.

For XOR, MUL, SET, and DEREF, the current prover assumptions largely restate the guarantees
that completeness needs to discharge. JUMP additionally proves that the generated inverse
and indicator satisfy its residuals. These proofs are valid, but they do not by themselves
construct a row from an arbitrary valid opcode step.

Prover assumptions are not additional axioms and are not assumed in adversarial soundness.
For a fixed, externally supplied row, fetch and read consistency are real requirements: its
arbitrary values cannot be made correct by deleting hypotheses.

**Required change:** connect the strengthened specification to completeness with explicit
semantic corollaries. Then discharge row-construction obligations through a proved constructor
or witness-producing wrapper. Distinguish this local result from global T1 completeness and
from executable T2 witness-generator correctness.

### R3: most negative tests do not exercise the table's emitted operations

The XOR mutation at `tests/LeanerVMTests/Arithmetization/Tables.lean:183`, for example, proves
that a manually assembled wrong memory message fails `MemPull.Guarantees`. It does not use
`xorTable.main`. Similar tests cover other tables. The JUMP tests check standalone residual
expressions rather than a complete table environment.

These are useful channel/algebra tests, but changes to the actual table emission can leave
them unchanged. The positive `Spec` examples also unfold directly to `step`, so they do not
exercise the circuit output. Only XOR's positive fixture explicitly invokes completeness.

**Required change:** retain useful lower-level tests and add tests of the actual `main`
operations and output. Distinguish rejection by local constraints plus required pull
guarantees from global bus rejection; the latter still needs the later bus theorem.

## Contract design to implement

### Shared approach

For each opcode, introduce a named predicate describing how its row matches the instruction
and memory, then define its functional specification as that predicate conjoined with `step`.
Names such as `XorRowBindings` and `XorSpec` below are proposed names, not existing API.

Use the following notation in the descriptions below:

```text
P       = programOf data
L       = (imageOf data).2
s       = ⟨r.pc, r.fp⟩
word v  = E.ofLimbs v[0] v[1] v[2]       -- v : Vector K 3
base c  = E.ofLimbs c 0 0
cell v  = cellOf v                     -- existing helper for Vector K 2
```

The uniform shape is:

```lean
def XorSpec (r : XorRow K) (next : Regs K) (data : ProverData K) : Prop :=
  XorRowBindings r data ∧
    step (programOf data) (imageOf data).2 ⟨r.pc, r.fp⟩ = some next
```

Use the corresponding row type and bindings for each table. Set each table's `Spec` to its
named predicate. Also prove an explicit `*_spec_iff` characterization that expands the step
into the opcode's memory equation and successor rule listed below. This exposes functionality
without defining a competing ISA semantics. Export a `*_spec_step` projection for consumers
that need only the common step property.

A structure or a conjunction is acceptable; prioritize readable theorem statements and
predictable projections. Reuse `E.ofLimbs` or a narrow shared helper rather than duplicating
word reconstruction. If a helper requires a new production module, update `LeanerVM.lean`.

Access counts are intentionally outside these functional bindings. Their nonzero conditions,
allocation, finalization, and interaction bounds belong to bus/global witness correctness.
Changing a count alone need not falsify an opcode's functional specification.

### XOR

`XorRowBindings r data` must contain:

```text
P.fetch r.pc = some (.xor r.oA r.oB r.oC)
L.read (r.fp * r.oA) = some (word r.vA)
L.read (r.fp * r.oB) = some (word r.vB)
```

Prove that `XorSpec r next data` is equivalent to those bindings together with:

```text
L.read (r.fp * r.oC) = some (word r.vA + word r.vB)
next = s.next
```

The operation is addition in `E`, whose limbs are bitwise XOR in `K`; it is not integer
addition with carry. Reuse `add_limbs` and `limb_add`. The pinned CompPoly theorem
`BF64.add_def` identifies base-field addition with bitwise XOR if an explicit bit-level
corollary is useful. Inspect its declaration before choosing that theorem's full namespace.

### MUL_NATIVE

`MulRowBindings` has the same two input-read bindings as XOR, with fetch naming
`.mulNative r.oA r.oB r.oC`. The expanded functional conclusion is:

```text
L.read (r.fp * r.oC) = some (word r.vA * word r.vB)
next = s.next
```

Keep the specification in extension-field multiplication. Use `mul_limbs` to connect it to
the twelve products in `main`; do not make the circuit's expanded polynomial the only public
description of multiplication.

### SET_CONSTANT

`SetRowBindings` only needs the instruction binding:

```text
P.fetch r.pc = some (.setConstant r.o (word r.k))
```

The expanded functional conclusion is:

```text
L.read (r.fp * r.o) = some (word r.k)
next = s.next
```

The immediate is already part of the fetched instruction; there is no independent input-word
column to bind. Every immediate limb must be accounted for.

### DEREF

`DerefRowBindings` must assert that there exists a `mode : DerefMode` such that:

```text
P.fetch r.pc = some (.deref r.o1 r.o2 r.o3 mode)
derefFlags mode = (r.fpc, r.ffp)
L.read (r.fp * r.o1) = some (base r.p)
L.read (r.fp * r.o3) = some (word r.v3)
```

The expanded specification must use the same existential mode and additionally assert:

```text
L.read (r.p * r.o2) = some (derefSource mode s (word r.v3))
next = s.next
```

Use `storeCoords_eval` to relate this to the emitted coordinates. Preserve the unconditional
local-cell read in all three modes and the return address `g ^ 2 * r.pc`. Keep the pointer's
upper limbs zero. Do not add independent flag Booleanity constraints: the exact fetched
instruction already forces one of the three permitted flag pairs.

### JUMP

`JumpRowBindings` must contain:

```text
P.fetch r.pc = some (.jump r.oc r.od r.of)
L.read (r.fp * r.oc) = some (base r.vcond)
L.read (r.fp * r.od) = some (base r.vpc)
L.read (r.fp * r.of) = some (base r.vfp)
```

The expanded functional conclusion is:

```text
next = if r.vcond = 0 then s.next else ⟨r.vpc, r.vfp⟩
```

All three words must be in `K` on both branches. Preserve both residuals and the existing
generated `w` and `b`; use `flags_sound`, `flags_complete`, and `ofLimbs_eq_zero_iff`.
The functional specification need not mention auxiliary `w`. For a zero condition, satisfying
constraints permit arbitrary `w`, although the honest generator chooses zero. Do not
accidentally require all satisfying assignments to equal the honest generator's assignment.

### BLAKE2S

`Blake2sRowBindings` must bind the exact instruction:

```text
P.fetch r.pc =
  some (.blake2s ![r.om0, r.om1, r.om2, r.om3] r.ocv r.oout r.omd)
```

It must bind all nine reads to the corresponding row cells:

| Address | Row value |
| --- | --- |
| `r.fp * r.om0` | `cell r.m0` |
| `r.fp * r.om1` | `cell r.m1` |
| `r.fp * r.om2` | `cell r.m2` |
| `r.fp * r.om3` | `cell r.m3` |
| `r.fp * r.ocv` | `cell r.cv0` |
| `r.fp * (g * r.ocv)` | `cell r.cv1` |
| `r.fp * r.oout` | `cell r.out0` |
| `r.fp * (g * r.oout)` | `cell r.out1` |
| `r.fp * r.omd` | `cell r.md` |

Each read is `L.read address = some value`. Prove that the strengthened specification is
equivalent to these bindings together with `Blake2sRelation r` and `next = s.next`.
`Blake2sRelation` already names `CompressCells` on these nine canonical cells, including the
counter and both finalization flags. Reuse it.

Retain `Assumptions r _ := Blake2sRelation r`. The present component proves memory/bytecode
binding; Flock must discharge the compression assumption for the composed system. Witness
generation does not discharge adversarial soundness. Do not silently advertise unconditional
compression enforcement after strengthening `Spec`.

## Completeness and witness construction

### First deliverable: connect the local contracts

For XOR, MUL, SET, DEREF, and JUMP, a useful semantic completeness premise is:

```lean
ProverAssumptions r data _ := ∃ next, XorSpec r next data
```

Substitute the appropriate named specification. Under the existing local-witness discipline,
derive the pull guarantees and residual equations from that premise. Prove that this premise
is equivalent to the previous honest-row predicate, or provide explicit implications in both
directions. For JUMP, the bindings alone already ensure that a successor exists.

This change makes the meaning of completeness explicit; it does not weaken the logical input
requirements. In particular, XOR's result-read equality follows from a valid XOR step plus the
fetch and two input bindings. The checked proof below demonstrates that derivation.

BLAKE2s is different: its existing local completeness accepts any correctly bound canonical
cells, without checking compression. Keep that useful low-level completeness premise as
`Blake2sRowBindings`. Add a semantic completeness corollary from `∃ next, Blake2sSpec r next
data`, which also establishes the compression assumption needed by soundness. Do not obscure
the distinction by claiming that its old prover assumptions alone imply its functional `Spec`.

For each table, establish an explicit theorem that a valid step of its opcode admits a row
with the same `pc` and `fp` and the strengthened specification. Quantify the actual opcode
operands and fetched instruction. State what happens to access counts: arbitrary counts can
be parameters for a local functional theorem, but global balance requires coordinated counts.
The generated row must represent the supplied step, not an unrelated satisfying execution.

### Second deliverable: discharge bindings by construction

Prefer a proved row builder or witness-producing wrapper around the existing table. It should
obtain the operands and read values from the supplied program/execution/memory representation,
then prove the row bindings and invoke semantic completeness. Preserve the pinned column
layout and emitted relations. Introduce shared machinery only for concrete consumers.

The implementation options and limits at the pinned dependencies are:

- JUMP already uses `witness` for its inverse and branch indicator. Keep that implementation.
- XOR, MUL, SET, DEREF, and BLAKE2s currently have no local `witness` operations. Their row
  fields are inputs. `Circuit.witgen` evaluates declared witness programs; it does not solve
  constraints, infer missing inputs, or satisfy bus reads automatically.
- Clean provides `witness`, `witnessProgram`, `witnessVectorProgram`, `Witgen.FExpr.dataGet`,
  `hintGet`, `Circuit.witgen`, and `Circuit.witgen_usesLocalWitnesses`. Inspect the pinned
  signatures and the `ComputableWitnesses` condition before composing their theorems.
- In `Clean/Circuit/WitnessGeneration.lean`, `ProverEnvironment.fromArray` sets `data` to empty.
  Every `witgenStep` evaluates its program in that environment. Setting committed data only
  after generation does not fix programs that read it during generation. A data-aware runner
  needs a proved bridge, preferably in Clean; a hint-backed design needs an explicit relation
  between those hints and the program/image used by the semantic theorem.
- `gLog?`, `MemImage.read`, `Program.fetch`, and `step` are noncomputable semantic interfaces.
  Array position `i` corresponds to field address `gpow i`. `FiniteField.val address` is not
  that position. Use verified logical indices from the execution representation or a verified
  executable lookup. Preserve bounds and address/index agreement.
- Local generation cannot independently choose globally balanced read counts. Keep their
  allocation with the execution-wide witness builder.

Deliver a semantic row-existence proof even if executable data-aware generation needs a
separate follow-up. Label a noncomputable constructor as such. Do not claim T2 from semantic
existence or from a constructor that is merely supplied all the finished row values again.
Record the exact remaining executable obligation rather than replacing it with a stronger
unexplained assumption. Do not change dependency pins as part of the specification repair.

## Proof and regression acceptance criteria

1. Each table exports the proposed functional specification and its explicit opcode
   characterization, with a proved projection back to `step`.
2. Soundness proves opcode and row bindings from the actual pulls. The five ordinary tables
   retain `Assumptions := True`; BLAKE2s retains its named compression boundary.
3. Semantic completeness is connected to the local completeness premise, and valid opcode
   steps have representing rows. Generated local witnesses are covered by the proof.
4. Positive fixtures exercise every table's `main` and returned successor, including JUMP's
   taken and untaken branches and all three DEREF modes. Where completeness needs a generated
   environment, establish the actual witness discipline rather than only proving standalone
   arithmetic equalities.
5. Negative tests use actual rows/environments: wrong opcode/operand bindings; changed XOR or
   MUL input limbs; a changed SET immediate; invalid DEREF flags; wrong JUMP witnesses; and a
   noncanonical BLAKE2s image cell. Connect them to the emitted operations and appropriate pull
   guarantees or residuals. Do not invent a result column for XOR or MUL.
6. The old-spec counterexamples below become rejection examples for the new specifications.
   In particular, the specification must detect incorrect read limbs even when `step` itself
   succeeds on the unchanged program and image.
7. Include a BLAKE2s boundary test with an incorrect but canonical output changed consistently
   in both row and image: bindings/local completeness can hold, while `Blake2sRelation` and
   the functional specification fail. This guards the distinction between binding and Flock.
8. Preserve the strengthened bytecode guarantee introduced in the reviewed commit. Returning
   to `fetch pc = decode entry` would permit both sides to be `none` and invalidate DEREF
   soundness.
9. Check emitted column/interaction behavior against the pin when introducing a generator or
   wrapper. The semantic specifications do not themselves prove physical column order, state
   emission, count updates, or Rust source correspondence.
10. Update the README and leanISA roadmap/status to describe the final contracts accurately.
    Run `#print axioms` on new public results and `./scripts/validate.sh`; stage only the
    intended paths so index-based hygiene checks include them.

Narrow `simp` sets where needed: the existing files document core BitVec simprocs firing on
`K`, and indiscriminate unfolding of concrete prover data can exhaust simplifier recursion.
Reuse the existing symbolic channel/limb lemmas and fixture read lemmas. Preserve repository
options and validation strength.

## Suggested implementation sequence

1. Implement XOR's named bindings/specification, the explicit XOR characterization, the step
   projection, and semantic completeness. Add the two specification regression cases first.
2. Apply the same interface to MUL and SET, then DEREF and JUMP. Review each theorem statement
   separately, especially mode/branch boundary cases.
3. Implement BLAKE2s with the explicit distinction between local bindings and compression.
4. Add row construction, use Clean for the auxiliary witnesses it can generate, and record any
   separately scoped executable data/index bridge.
5. Complete table-operation regression coverage, update the durable docs, and validate.

These changes contribute local constraint soundness/completeness (CC-S/CC-C) toward T1. A
proved executable row/witness builder contributes toward T2 within its stated input and
resource boundary. Global trace assembly, balanced buses, Flock enforcement, and proof-system
soundness remain obligations of their owning layers.

## Reproducible baseline proofs

The following block compiled with `lake env lean -E warning` against the reviewed commit.
Place it in a temporary file outside the repository and run it from the repository root after
building the test library. Its positive examples of weak `Spec` are evidence about the old
contract, and should intentionally stop compiling after the contract is strengthened. Port
their negations into the regression suite for the new contract.

```lean
import LeanerVMTests.Arithmetization.Tables
import Clean.Circuit.WitnessGeneration

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open LeanerVMTests.Arithmetization.Tables

namespace Task6Review

def bogusXor : XorRow K :=
  { xorRow with pc := gpow 2, oA := 0, oB := 0, oC := 0, vA := #v[0, 0, 0] }

theorem bogus_xor_satisfies_spec : xorTable.Spec bogusXor ⟨g * gpow 2, 1⟩ tabData := by
  show step (programOf tabData) (imageOf tabData).2 ⟨gpow 2, 1⟩ = some ⟨g * gpow 2, 1⟩
  rw [step_of_fetch_eq_some (r := ⟨gpow 2, 1⟩)
    (fetch_at 2 (.setConstant (gpow 6) (E.ofLimbs 7 8 9)))]
  simp only [execute, one_mul, read_at 6 #v[7, 8, 9]]
  decide +kernel

theorem bogus_xor_is_not_xor :
    (programOf tabData).fetch bogusXor.pc ≠ some (.xor bogusXor.oA bogusXor.oB bogusXor.oC) := by
  rw [show bogusXor.pc = gpow 2 from rfl,
    fetch_at 2 (.setConstant (gpow 6) (E.ofLimbs 7 8 9))]
  intro h
  cases h

theorem bogus_xor_bytecode_rejected :
    ¬ BytecodePull.Guarantees
      ⟨bogusXor.pc, bogusXor.rbc, Opcode.xor.code,
        #v[bogusXor.oA, bogusXor.oB, bogusXor.oC, 0, 0, 0, 0]⟩ tabData := by
  rintro ⟨ins, hfetch, hdec⟩
  rw [xor_entry, decode_entry, Option.some.injEq] at hdec
  subst hdec
  exact bogus_xor_is_not_xor hfetch

theorem xor_spec_ignores_row_values (r : XorRow K) (a : Vector K 3)
    (next : Regs K) (data : ProverData K) :
    xorTable.Spec { r with vA := a } next data ↔ xorTable.Spec r next data := Iff.rfl

def invalidDeref : DerefRow K := { derefRow with fpc := 1, ffp := 1 }

theorem invalid_deref_flags_satisfy_spec :
    derefTable.Spec invalidDeref ⟨g * gpow 3, 1⟩ tabData := by
  show step (programOf tabData) (imageOf tabData).2 ⟨gpow 3, 1⟩ = some ⟨g * gpow 3, 1⟩
  rw [step_of_fetch_eq_some (r := ⟨gpow 3, 1⟩) (fetch_at 3 (.deref (gpow 7) 1 (gpow 9) .pc))]
  simp only [execute, one_mul, mul_one, read_lit 7 (gpow 8) 0 0, Option.bind_eq_bind,
    Option.bind_some, guard, isInK_ofLimbs, ite_true, limb_ofLimbs, Matrix.cons_val_zero,
    read_lit 9 5 6 7, read_lit 8 (g ^ 2 * gpow 3) 0 0, derefSource, ofK_eq_ofLimbs]
  decide +kernel

theorem xor_assumptions_from_step (r : XorRow K) (data : ProverData K) (next : Regs K)
    (hfetch : (programOf data).fetch r.pc = some (.xor r.oA r.oB r.oC))
    (hA : (imageOf data).2.read (r.fp * r.oA) = some (E.ofLimbs r.vA[0] r.vA[1] r.vA[2]))
    (hB : (imageOf data).2.read (r.fp * r.oB) = some (E.ofLimbs r.vB[0] r.vB[1] r.vB[2]))
    (hstep : step (programOf data) (imageOf data).2 ⟨r.pc, r.fp⟩ = some next) :
    xorTable.ProverAssumptions r data default := by
  refine ⟨hfetch, hA, hB, ?_⟩
  rw [step_of_fetch_eq_some hfetch] at hstep
  simp only [execute, hA, hB, Option.bind_eq_bind, Option.bind_some] at hstep
  cases hc : (imageOf data).2.read (r.fp * r.oC) with
  | none => simp only [hc, Option.bind_none] at hstep; contradiction
  | some c =>
    simp only [hc, Option.bind_some, guard, Option.pure_def] at hstep
    split at hstep
    next heq => rw [heq, add_limbs]
    next => simp at hstep

theorem xor_witgen_creates_no_values :
    (xorTable.main (const xorRow)).witgen default #[] = #[] := rfl

#print axioms bogus_xor_satisfies_spec
#print axioms bogus_xor_bytecode_rejected
#print axioms invalid_deref_flags_satisfy_spec
#print axioms xor_assumptions_from_step
#print axioms xor_witgen_creates_no_values

end Task6Review
```
