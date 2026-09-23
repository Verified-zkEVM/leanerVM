# Executable leanISA validation

The checker validates a fixed final image against the existing Lean ISA. It does not generate
memory, prove Rust correct, or check an executable proof verifier. The semantic reference
remains pinned to leanVM `a386121f84292f6fa663aaa3e570c15bc0240ea2`. The optional Rust
regression lane separately tests `48a904208d682848dac0e18ef8b01ebfc40df9ad`; it does
not change that pin or claim coverage of every change between those revisions.

## Proved interfaces

- [`Executable.lean`](../LeanerVM/Semantics/Executable.lean) supplies exhaustive bounded-address
  search and the six instruction checks. `checkTrace_eq_true_iff` proves that exact checking
  accepts precisely `ValidExecution`, including memory caps, public words, exact step count,
  the unexecuted sentinel and final frame pointer. A `SentinelSafe` premise is unnecessary for
  semantic checking; it remains a separate premise of global constraint soundness.
- [`Checker.lean`](../LeanerVM/Semantics/Checker.lean) searches within a transition budget.
  `checkWithinFuel_eq_ok_iff` proves that success with count `n` is equivalent to a valid
  exact-length execution with `n ≤ fuel`. Exhaustion makes no claim about larger budgets.
- [`RunTrace.lean`](../LeanerVM/Semantics/RunTrace.lean) gives relational steps and ordered
  finite traces, equivalent to `run`. A failed step has no successor. The empty run has one
  state and zero transitions.
- [`TraceInput.lean`](../LeanerVM/Semantics/TraceInput.lean) preserves the entire finite export,
  checks its power-of-two memory shape and count accounting, and uses `sum(mainCounts)` as
  `Trace.steps`. `adapt_preserves` and `validateInput_eq_true_iff` specify these guarantees.
  Announced counts alone do not prove that the rows exist.
- [`FillerRows.lean`](../LeanerVM/Semantics/FillerRows.lean) accepts unordered row starts when
  every reference successor succeeds and the starting/successor multisets agree. This
  standalone interface does not take a main run or check memory/bytecode access-count columns
  or budgets.

[`ReadHints.lean`](../LeanerVM/Semantics/ReadHints.lean) accelerates high scratch-address reads
and instruction fetches.
Every suggested index is range checked and its generator power must match the requested
address. Every miss falls back to exhaustive search. Kernel-checked equalities show that hints
preserve the acceptance domain without a coverage assumption. Tests cover empty, incomplete,
duplicate, incorrect and out-of-range hints. The Rust lane supplies hints from touched memory
indices and row program counters solely for speed; these are not trusted evidence about access counts.

These deterministic semantic refinements support T1 and the T2 validation boundary. By
themselves, they prove neither global constraint soundness/completeness nor cryptographic
soundness.

## Running the checks

The regular gate includes all maintained Lean cases:

```sh
./scripts/validate.sh
```

For the source-pinned Rust regressions and actual Rust-to-Lean fixture checks:

```sh
python3 scripts/test-rust-contracts.py /path/to/leanVM
```

The Rust checkout must contain commit `48a904208d682848dac0e18ef8b01ebfc40df9ad`; its current
branch and working tree are not changed. Cargo and the dependencies from that revision's
`Cargo.lock` must be cached: the script uses `--locked --offline`. Builds go to a temporary
Cargo target directory, overridable with `--target-dir`. This optional external lane is not
part of the dependency-local validation gate.

The script archives that exact commit into a temporary directory, adds only a `cfg(test)`
module to inspect the private trace rows, and runs all 25 original library tests plus ten
maintained contract regressions. It preserves the archived lockfile. Seven fixtures export
actual typed instructions, all final-memory words, the original public input, per-opcode row
starts, main counts, final counts and total cycles. Adjacent identical instructions and zero
memory words are compressed losslessly in generated Lean data. Generated files are temporary,
not accepted source or proof certificates. Arrays are built by folds over exported data; long
generated mutable `do` blocks caused excessive elaboration time on the filler program.

The Lean diagnostic helper checks the public main run, actual row lengths/opcodes, the main
row multiset against replay, and every row attributed to filler with natural state balance:

| Fixture | Expected result |
| --- | --- |
| One-slot program | Zero main steps; sentinel not executed |
| Nonempty main, no fillers | One SET step; no filler rows |
| Stale read followed by a write | Rust succeeds; Lean rejects its final image |
| Unwritten zero XOR operands | Rust reports unconstrained reads; Lean accepts the final zero image |
| Two later XOR operand changes that cancel | Rust succeeds; Lean accepts the final image relation |
| Stale MUL operands followed by nonzero writes | Rust succeeds; Lean rejects its final image |
| Exact one-main-step/20-cycle fixture | One main step and nineteen separately checked filler rows |
| Filler fixture using total counts as main counts | Rejected for early halting |
| Missing closing JUMP, with accounting adjusted | Main image remains valid; complete export check rejects fillers |
| Corrupt total cycle count | Rejected by accounting |

The remaining Rust regressions reject a non-K JUMP destination even on an untaken branch,
reject sentinel arrival with the wrong frame pointer, and pin distinct non-Boolean BLAKE2s
flag words. Lean cases additionally cover all six opcodes, invalid and aliased addresses,
BLAKE cell canonicality, all DEREF modes and their failed reads,
wrong public input, early halting, a valid JUMP sentinel, and fuel exhaustion.

## Remaining boundaries

Compiled `#guard` checks exercise the executable definitions. The refinement and preservation
theorems are kernel checked. Foreign export generation and compiled evaluation remain test
boundaries; the tests are not proofs of Rust source or Rust's complete success domain.

Fallback address lookup is exhaustive and slow for large or absent addresses. Verified hints
make the concrete filler regression practical; this is not a performance result for large VMs.
A standalone native executable still encounters the pinned CompPoly `Fintype BF64` startup
issue recorded in the
[status](roadmap/leanisa-status.md); compiled evaluation within Lean works. The P2 native smoke
gate remains open. Changing dependencies to address it requires a separate drift review.

The row-export diagnostic does not yet validate access-count columns, combined M3/protocol
resource bounds, raw-bytecode verifier coverage, or an aggregation guest's artifact binding.
The semantic and Rust pins, typed-program domain, and regression coverage are described above.
Both padding/completeness constructions and Rust read-stability correspondence remain
outstanding. Passing these checks is not completion
of the full leanISA implementation-validation plan.
