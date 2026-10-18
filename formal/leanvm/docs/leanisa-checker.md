# Executable leanISA validation

The checker validates a fixed final image against the existing Lean ISA. It does not generate
memory, prove Rust correct, or check an executable proof verifier. The semantic reference
remains pinned to leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`, whose ISA and memory
semantics are those of the previous pin `a386121f84292f6fa663aaa3e570c15bc0240ea2`.

## Proved interfaces

The reference semantics (`gLog?`, `MemImage.read`, `Program.fetch`, `execute`, `step`, `run`,
`ValidExecution`) stays noncomputable and is what a reader audits. One computable carrier is
proved equal to it; its bodies may hold speedups and are not audited, only the equivalence
statements are.

- [`Spec/Isa.lean`](../LeanerVM/Spec/Isa.lean) writes the six instruction arms once, in
  `executeWith` over a named reader; `execute L r` is `executeWith L.read r`. The carrier
  instantiates the same arms with its own reader, so there is no second copy of the semantics.
- [`Executable.lean`](../LeanerVM/Semantics/Executable.lean) is the carrier. `addressIndex`
  tries an untrusted hint list first, accepting an index only after `g ^ i = a` has been
  checked, and otherwise scans the address space carrying `g ^ i` as a running product, one
  multiplication per candidate; `addressIndex_eq_gLog` says it equals the reference logarithm
  for every hint list. `stepChecked` is `executeWith` at that reader and equals `step`.
  `checkWithinFuel_eq_ok_iff` proves that success with count `n` within a budget is equivalent
  to a valid exact-length execution with `n ≤ fuel`; exhaustion makes no claim about larger
  budgets. `checkTrace` runs the bounded search with the announced count as its budget and
  requires exactly that count; `checkTrace_eq_true_iff` proves it accepts precisely
  `ValidExecution`, including memory caps, public words, the unexecuted sentinel and the final
  frame pointer, with no hypothesis and for every hint list. A `SentinelSafe` premise is
  unnecessary for semantic checking; it remains a separate premise of global constraint
  soundness.
- [`RunTrace.lean`](../LeanerVM/Semantics/RunTrace.lean) gives relational steps and ordered
  finite traces, equivalent to `run`. A failed step has no successor. The empty run has one
  state and zero transitions.

Hints are a parameter of every carrier function, never of a definition of the machine. A
suggested index is range checked and its generator power must match the requested address;
every miss falls back to the scan. Tests cover empty, incomplete, duplicate, incorrect and
out-of-range hints.

These deterministic semantic refinements support T1 and the T2 validation boundary. By
themselves, they prove neither global constraint soundness/completeness nor cryptographic
soundness.

## Running the checks

The regular gate includes all maintained Lean cases:

```sh
./scripts/validate.sh
```

Lean cases cover all six opcodes, invalid and aliased addresses, BLAKE cell canonicality, all
DEREF modes and their failed reads, wrong public input, early halting, a valid JUMP sentinel, and
fuel exhaustion.

## Remaining boundaries

Compiled `#guard` checks exercise the executable definitions. The refinement and preservation
theorems are kernel checked. Compiled evaluation remains a test boundary.

The scan is linear in the address space, so a read at a high or absent address costs one
field multiplication per candidate below it; this is not a performance result for large VMs.
A standalone native executable still encounters the pinned CompPoly `Fintype BF64` startup
issue recorded in the
[status](roadmap/leanisa-status.md); compiled evaluation within Lean works. The P2 native smoke
gate remains open. Changing dependencies to address it requires a separate drift review.

The checker does not validate access-count columns, combined M3/protocol resource bounds,
raw-bytecode verifier coverage, or an aggregation guest's artifact binding. Rust read-stability
correspondence remains outstanding. Passing these checks is not completion of the full leanISA
implementation-validation plan.
