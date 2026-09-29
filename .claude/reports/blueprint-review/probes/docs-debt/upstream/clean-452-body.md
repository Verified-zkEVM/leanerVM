## Problem

`BalancedInteractions` currently combines two different facts:

1. algebraic balance for every message; and
2. a side condition that the concrete interaction list has length smaller than the field characteristic.

`Ensemble.Statement` inherits that per-channel list-length condition through `BalancedChannels`. This is not representative of how a proof-system verifier establishes soundness: a verifier knows component trace heights and the static number of interaction operations per row, but it does not materialize or directly bound each semantic per-channel interaction list.

The no-wrap condition is necessary for the channel soundness theorems, but it should be derived from a verifier-checkable bound on the complete ensemble shape rather than appearing inside the definition of algebraic balance.

This is a follow-up to #446, whose Rust backend checks the corresponding global interaction-capacity bound when constructing the generated ensemble statement.

## Intended model

Trace shape should be part of the `EnsembleWitness`, just like its public input. It need not be stored redundantly: derive it from the lengths of the witness's component tables.

Define a conservative capacity from the witness shape:

```text
verifier interaction operations
+ Σ(component trace height × component interaction operations per row)
```

Equivalently, Lean can define the sum directly over the witness tables, using each table's length and component operation list.

The ensemble statement should require this capacity to be smaller than `ringChar F` (with the existing characteristic-zero alternative where applicable). Channel balance in the statement should otherwise be purely algebraic.

## Proposed changes

- Split algebraic balance from the no-wrap side condition currently bundled in `BalancedInteractions`.
- Derive component trace heights from `EnsembleWitness.tables`; do not add a second independently supplied shape that needs a consistency proof.
- Define `EnsembleWitness.interactionCapacity` (or an equivalently placed definition) from:
  - the verifier operation list;
  - each component table's height; and
  - the component's static interaction count per row.
- Add the global interaction-capacity bound directly to `Ensemble.Statement`.
- Prove that, for every channel:

  ```text
  (witness.interactionsWith channel).length ≤ witness.interactionCapacity
  ```

- Refactor channel consistency and VM/ordered-channel soundness lemmas so their required no-wrap fact is derived from the ensemble capacity bound.
- Update `FormalEnsemble` soundness plumbing and affected examples without weakening their specifications.
- Document that this generic Clean condition corresponds to the bound every backend verifier must check from committed trace metadata.

## Non-goals

- Power-of-two trace heights.
- Plonky3-specific proof metadata or APIs.
- Backend-specific maximum-height policies beyond the generic no-wrap requirement.
- A redundant shape field separate from the witness tables.

## Acceptance criteria

- `BalancedInteractions`/channel algebraic balance no longer receives an unexplained concrete-list length premise from the statement.
- `Ensemble.Statement` contains a verifier-checkable global interaction-capacity bound derived from witness table heights.
- The capacity bound implies every per-channel no-wrap condition needed by the existing soundness theorems.
- The witness has one authoritative source of component shape: its component tables.
- Flat AIR, ordered-channel, VM, Fibonacci, and FemtoCairo soundness proofs continue to build.
- The Lean capacity formula agrees with the metadata formula enforced by the generated Rust statement.
