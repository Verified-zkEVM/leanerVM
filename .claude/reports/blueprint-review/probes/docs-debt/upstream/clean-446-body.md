## Summary

- add indexed fixed columns whose row facts are available to Lean component soundness proofs and exported as Plonky3 preprocessed columns
- derive named `ProverData` from proof-committed component inputs, with consistency carried into component assumptions by construction
- add typed runtime prover inputs and interaction-driven preallocated tables; generated multiplicities remain derived from channel demand
- port FemtoCairo to a channel-based Flat AIR whose program and memory addresses are fixed while private memory values are supplied only at witness generation
- remove the legacy JSON interpreter and Lean-spawning backend tests in favor of direct generated Rust witness and AIR programs