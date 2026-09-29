Layer 1 should supply `idxColumn`, `idxColumnEval`, `bytecodeSlotColumn`, `bytecodeColumn`,
and `bytecodeColumnEval`, with readout and native-evaluation equalities against the actual
`Column` oracle. Prove the reusable `powerColumnValues` evaluation formula separately.
The named consumer is Layer 6's public contribution to `leaf_decomposition`; generic power
algebra remains a CompPoly migration candidate under the [ArkLib #900](https://github.com/Verified-zkEVM/ArkLib/issues/900) coordination issue.

Category A target: specification §6.5's index factorization and multilinear interpolation.
Category B target: §8.1 and `crates/lean_vm/src/leaf.rs:570-602,627-637` fix sixteen slots,
low instruction bits, high slot bits, opcode slot 3, and spare zeros. Reuse `Program` and
`encodeSlots` directly. This is new leanVM-b work, not a leanth port. Depends only on #18 at
`41b79b3`; direct dependencies are `Protocol.Field`, `Protocol.Multilinear`, and
`Arithmetization.Bytecode`.

Acceptance: arbitrary extension-field query points; two distinct public instructions;
`logSize = 0`; actual index and bytecode oracle evaluations; bit/slot reversal controls and
spare-slot zeros; direct-import client, focused tests, ordinary-toolchain full validation and
axiom audit pass. The public program is an input, and Rust execution correspondence is not
proved by these column equalities.

Tracks [#12](https://github.com/Verified-zkEVM/leanerVM/issues/12). Only this subset of Layer 1 is claimed; landing it does not complete the layer.
