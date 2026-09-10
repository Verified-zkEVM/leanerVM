# Architecture

## Current boundary

The repository begins with a Lean-only executable semantics. This is both the foundation of the
proof architecture and the reference implementation for later execution backends. The design
keeps the semantics independent of any native ABI while allowing optimized backends to be added
behind specified interfaces as the implementation stabilizes.

## Lean layers

```text
Parameters ──→ Semantics ──→ Arithmetization ──→ Protocol
                         └──→ Applications ────────┘
```

An arrow points from a lower layer to a layer allowed to depend on it.
`scripts/check-layers.sh` enforces the forbidden reverse edges on every validation run.

### Parameters

Owns concrete constants, encodings, layouts, and source bindings. Each binding records an
authoritative source and exact revision. It is the foundational production layer and must not
depend on semantics, applications, arithmetization, or protocol assembly. Versioned bindings also
identify the hash constructions used by that target; the current leanVM binding selects its
BLAKE2s constructions without making that selection permanent for future revisions.

### Semantics

Owns the ISA, state, memory, bytecode, transition relation, halting behavior, and pure
executable interpreter. It must not import arithmetization or protocol code.
Prefer generic machine definitions where practical; source-faithful leanVM semantics consume
the versioned constants and encodings owned by `Parameters`.

### Arithmetization

Owns tables, buses, witness generation, algebraic constraints, and refinements connecting
constraint satisfaction to executions in `Semantics`. Generic circuit and table machinery
should be upstreamed to Clean rather than duplicated here.

### Applications

Owns the recursive signature-aggregation guest specification, the exact guest program and
compiler or assembly boundary, and application-level correctness results. It may depend on
`Parameters` and `Semantics`, but not on the arithmetization or protocol layers. Create the
directory with its first concrete module rather than adding an empty placeholder.

### Protocol

Owns only leanVM-specific composition of upstream polynomial, oracle, commitment, and proof-
system components around the verified arithmetization. Generic theory belongs in CompPoly,
VCVio, or ArkLib.

The target-theorem ownership is:

| Target | Owning layer | Principal inputs |
| --- | --- | --- |
| T1 — arithmetization/ISA equivalence | `Arithmetization` | `Semantics` execution relation and concrete parameters |
| T2 — witness-generator correctness | `Arithmetization` | executable witness generation and T1 relations |
| T3 — exact guest correctness | `Applications` | guest specification, exact program, compiler boundary, and `Semantics` |
| T4 — base proof extraction/completeness | `Protocol` | proof-system components, T1, and T2 |
| T5 — recursive-verifier correctness | `Protocol` | verifier-in-circuit and deferred-claim discharge |
| T6 — recursion and CTE | `Protocol` | explicitly provisional extraction interfaces and topology results |
| T7 — end-to-end soundness | `Protocol` | T1–T6 and the exact application claim |
| T8 — end-to-end completeness | `Protocol` | interpreter, witness generator, prover, recursion, and root discharge |

## Verification coverage

leanerVM treats “verified zkVM” as the composition of named obligations, not as a single property.
The summary below separates specifications from implementations and makes the refinement and
consistency edges part of the result.

```text
+--------------------- SPECIFICATIONS (reference) --------------------------+
| S1  Recursive XMSS and SPHINCS aggregation specification                  |
| S2  leanVM ISA specification                                              |
| S3  Hint and VM hash/compression specifications                           |
| S4  Proof-system, transcript, and commitment-hash specifications          |
+---------------------------------------------------------------------------+
             :            proof and correspondence obligations
             v
+---------------------- IMPLEMENTATION (what runs) -------------------------+
|                                                                           |
| Aggregation guest source ....... S1: source-level functional correctness  |
|       |                                                                   |
|       | compile: semantics preservation (S1 claim => S2 execution)        |
|       v                                                                   |
| leanVM bytecode ................ S2: encoding and ISA conformance         |
|       |                                                                   |
|       | execute/generate: preserve program, input, and trace semantics    |
|       v                                                                   |
| Witness generator .............. executable witness construction          |
|       |                                                                   |
|       | WC: construct the intended satisfying assignment                  |
|       v                                                                   |
| Constraints, tables, and bus ... S2 + S3: CC-S, CC-C, BC, hints, VM hash  |
|       |                                                                   |
|       | prove: S4 completeness and statement/transcript binding           |
|       v                                                                   |
| Prover ......................... S4: prover implementation correspondence |
|       |                                                                   |
|       | emit: specified proof encoding                                    |
|       v                                                                   |
| Proof                                                                     |
|       |                                                                   |
|       | check: verifier implementation correspondence                     |
|       v                                                                   |
| Verifier ....................... S4: soundness extracts constraints       |
|       |                                                                   |
|       | embed: verifier-in-circuit equivalence                            |
|       v                                                                   |
| Recursive verifier ............ S2 + S4: recursive composition            |
|       |                                                                   |
|       | extract: CTE / topology bridge (provisional)                      |
|       v                                                                   |
| Expected aggregation claim ..... S1: end-to-end application meaning       |
|                                                                           |
+---------------------------------------------------------------------------+
```

*Summary verification stack for leanerVM. The reference specifications sit above the artifacts
that run. Artifact labels identify their reference specification; arrow labels name the
transformation and the preservation or correspondence result it requires. `CC-S` and `CC-C` are
the two directions between constraint assignments and S2 executions, `BC` composes their table,
bus, lookup, and memory relations, and `WC` connects executable witness construction to the
intended assignment. The final extraction arrow is provisional because T6 remains open.*

### Hash abstraction and the leanVM instance

Hash choice is a target parameter at the architectural level, but it is not adequately described
by one opaque `ByteArray → Digest` function. Keep the interfaces for the following roles explicit:

- the ISA compression or precompile operation, including its state, block, metadata, and output
  encodings;
- byte-string and Merkle hashing, including padding and tree/domain-separation rules;
- proof-system transcript absorption and challenge derivation; and
- application hashing, including the keyed or tweakable operations and truncation used by the
  signature schemes.

Generic definitions and lemmas should quantify only over the interfaces and properties they use.
Versioned target parameters then supply concrete inhabitants, and source-faithful capstone
theorems fix those inhabitants rather than claiming correctness for an unspecified hash.

The initial implementation should formalize the current BLAKE2s behavior directly. It need not
wait for a universal hash abstraction or carry unused configurability: introduce a shared
interface when a theorem is genuinely construction-independent or another target needs it, while
preserving the role boundaries above so that later replacement is local and reviewable.

At the current pinned leanVM revision, these roles are concretely tied together by BLAKE2s. The
ISA contains a BLAKE2s compression opcode, its table is enforced by a BLAKE2s-specific Flock
relation, and the transcript, Merkle, XMSS, SPHINCS, and aggregation code use BLAKE2s constructions.
Consequently, T1 and the implementation-correspondence results must continue to name their exact
BLAKE2s semantics and encodings. A SHA-3, BLAKE3, or other instance would be a new target requiring
new ISA, layout, constraint, protocol, and implementation correspondence where those artifacts
differ; it is not an enum change hidden behind the same theorem.

### Target theorem ladder

The verification effort should expose a short sequence of high-level theorems, not only local
lemmas. These are targets, not claims about the current scaffold. T1–T5 and T8 give intended
interfaces; T6 and therefore the unconditional form of T7 remain provisional while recursion
extraction is an open problem.

Fix an audited target revision `version`, its parameters, the exact compiled aggregation program
`aggregationProgram`, an expected external aggregation statement `expectedStatement`, and
internal public metadata `metadata` carrying the bound environment and deferred claims. Write
`PublicInput.encode metadata expectedStatement` for their two-cell public-input encoding. The
following proposed names use ordinary Lean application syntax and are intended to become precise
declarations as their owning modules are implemented:

- `ISA.ValidExecution version program publicInput trace`: `trace` is a finite, well-formed
  leanVM ISA execution of `program`, with an explicit ordered step sequence and full write-once
  memory image—not merely committed roots or unordered table rows—and with the required
  initial/final machine state and public boundary `publicInput`;
- `Constraints.SatisfiedBy version program publicInput assignment`: `assignment` satisfies every
  enabled-row constraint, all six table layouts, the memory/bytecode/state interactions, the
  global bus argument, instance bounds, and the BLAKE2s relation;
- `Constraints.AssignmentRepresents assignment trace`: the committed columns and interactions in
  `assignment` reconstruct `trace`;
- `Guest.AggregationPostcondition version expectedStatement childStatements`: one execution of
  the aggregation guest verifies its raw signatures, enforces coverage for `expectedStatement`,
  and accepts exactly `childStatements` with the required parent/child mapping;
- `Aggregation.ValidClaim version expectedStatement`: every XMSS and SPHINCS claim published by
  `expectedStatement` has the required valid-signature provenance, with the specified
  epoch/message grouping, coverage, and deduplication policy; and
- `FinalVerifier.AcceptsExpected version proof expectedStatement`: the versioned final verifier
  accepts `proof`, including native discharge of the root deferred claims, and the exposed signer
  statement equals the caller's `expectedStatement`. Its public input is recomputed as
  `PublicInput.encode (FinalProof.metadata proof) expectedStatement`, not supplied independently
  by the prover.

`FinalVerifier.AcceptsExpected` is intentionally stronger than calling leanVM's bare
`AggregateSignature::verify`: that method validates the statement carried by the object, whereas
the capstone must rule out acceptance for a different prover-selected statement.

The public theorem ladder is:

1. **T1 — arithmetization/ISA equivalence (`constraints_iff_isa`).** This consists of both
   directions, with auxiliary columns existentially quantified rather than identified with one
   particular generator:

   ```text
   constraintSoundness:
     Constraints.SatisfiedBy version program publicInput assignment →
       ∃ trace,
         Constraints.AssignmentRepresents assignment trace ∧
         ISA.ValidExecution version program publicInput trace

   constraintCompleteness:
     ISA.ValidExecution version program publicInput trace →
       ∃ assignment,
         Constraints.SatisfiedBy version program publicInput assignment ∧
         Constraints.AssignmentRepresents assignment trace
   ```

   The advertised equivalence is therefore between valid ISA traces and constraint assignments
   projecting to those traces. Its proof consumes the per-opcode, BLAKE2s, boundary, bus,
   lookup, bytecode, memory, padding, and interaction-count results; none may remain as an
   unlabelled axiom. Both directions are stated for well-formed programs: a named program-shape
   hypothesis (`WellFormedBytecode` in the leanISA roadmap: the sentinel slot is not a `JUMP`,
   and the fill blocks the prover pads tables with are present) is a hypothesis of each, since
   the constraint system enforces neither and the compiled guest satisfies both;
   [leanvm-target.md](leanvm-target.md) records why.

2. **T2 — witness-generator correctness (`witnessGen_correct`).** Whenever the executable
   interpreter produces `trace` and witness generation succeeds, its concrete `assignment`
   satisfies `Constraints.SatisfiedBy version program publicInput assignment` and
   `Constraints.AssignmentRepresents assignment trace`. Together with an explicit success/resource
   hypothesis, every supported execution is accepted by witness generation. This strengthens
   T1-C from existence of some assignment to correctness of the implementation actually used by
   the prover.

3. **T3 — exact guest correctness (`aggregationProgram_correct`).** Establish both the source
   boundary and the application claim:

   ```text
   compile aggregationGuestSource = aggregationProgram
   ISA.ValidExecution
       version
       aggregationProgram
       (PublicInput.encode metadata expectedStatement)
       trace →
     Guest.AggregationPostcondition
       version
       expectedStatement
       (Trace.childStatements trace)
   ```

   The first line may instead be replaced by a verified assembly proof for the pinned emitted
   bytecode. The second is deliberately a local guest postcondition: turning accepted child
   proofs into their transitive signature claims still requires T4–T6. It must cover raw XMSS and
   SPHINCS verification, child-statement mapping, coverage slots, overlaps, hints, statement
   hashing, termination, and the exact final boundary. A completeness companion constructs a
   terminating execution from well-formed aggregation inputs within the published caps.

4. **T4 — base proof extraction and completeness (`baseVerifier_extractsExecution`).** First
   prove the proof-system bridge

   ```text
   BaseVerifier.Accepts version proof program publicInput →
     except with probability baseError,
       ∃ assignment,
         Constraints.SatisfiedBy version program publicInput assignment
   ```

   then compose it with T1-S to obtain an ISA execution. The theorem must expose the component
   soundness/knowledge-soundness bounds, Fiat–Shamir or random-oracle model, commitment and hash
   assumptions, transcript/serialization agreement, and executable-verifier refinement. Its
   completeness dual composes T2 with the honest prover and records any failure/resource
   conditions.

5. **T5 — recursive-verifier correctness (`recursiveVerifier_iff`).** Constraint satisfaction
   for the verifier-in-circuit is equivalent to the specified base-verifier decision for every
   child statement. Program identity, public inputs, transcript data, and recursion parameters
   must agree. This theorem also proves that batching preserves the three deferred fixed-
   polynomial claims—stacked bytecode and Flock `A0`/`B0`—and that native root discharge closes
   every claim carried through the tree.

6. **T6 — recursion and CTE (provisional).** The exact theorem is an open research question, not
   a frozen signature. There is a gap between the two results we currently know how to formulate
   cleanly:

   - an **inner theorem** proving knowledge soundness of each concrete non-recursive SNARK in the
     random-oracle model, commonly with a straight-line extractor that reads the oracle
     transcript; and
   - an **outer topology theorem** showing that abstract extractors for the proof relations compose
     through the recursion tree into a global execution witness.

   The outer theorem may use `Recursion.ValidExecutionTree` as a provisional full-trace
   interface:

   ```text
   Recursion.ValidExecutionTree
       version aggregationProgram metadata expectedStatement shape tree ↔
     ISA.HasPublicBoundary
         (ExecutionTree.root tree)
         (PublicInput.encode metadata expectedStatement) ∧
       (∀ trace ∈ ExecutionTree.traces tree,
         ISA.ValidExecution
           version aggregationProgram (Trace.publicInput trace) trace) ∧
       Recursion.EdgesAreConsistent tree ∧
       Recursion.LeavesContainSignatureWitnesses tree
   ```

   This captures the desired output, following the game-based insight that CTE is knowledge
   soundness for a full-trace relation. It does **not** select the extraction model needed to prove
   it for leanVM. Recursive verification makes the relation itself query the random oracle, so
   connecting ROM knowledge soundness of the inner SNARKs to the outer theorem would require a
   suitable relativized notion. [Relativized SNARKs do not exist in the ROM in
   general](https://eprint.iacr.org/2024/728). Plain-model straight-line knowledge soundness is
   also incompatible with succinctness in general.

   Possible bridges—plain-model or relativized extraction assumptions, a NARK carrying outer
   queries, or rewinding with a bounded depth—are heuristics with materially different claims.
   None is selected by this architecture. They should be formalized as separate candidate
   interfaces and compared before T6 receives a final statement. In particular:

   - do not add a global axiom translating ROM knowledge soundness into plain-model knowledge
     soundness;
   - an idealized outer-topology theorem must expose its extraction assumption and must not be
     presented as concrete security of the instantiated recursive system;
   - a non-straight-line extractor needs a meaningful recursion-depth bound and a justified
     rewinding model; and
   - any candidate needs an explicit advantage sum, extractor runtime, oracle model, and
     well-foundedness argument. A bound on child arity alone does not bound depth.

   Independently of which bridge is chosen, the extracted leanVM witness should contain ordered
   `pc`/`fp` steps and the full memory image whose first two cells equal
   `PublicInput.encode metadata expectedStatement`; table openings,
   bus digests, or a final commitment alone are not a correct trace. Composing T3 over a valid
   extracted tree should establish `Aggregation.ValidClaim version expectedStatement` at its
   root.

7. **T7 — end-to-end soundness (`finalVerifier_endToEndSound`, target schema).** This is the
   desired leanVM analogue of the top-level zkVM theorem, strengthened with the concrete guest
   claim:

   ```text
   FinalVerifier.AcceptsExpected version proof expectedStatement →
     except with probability totalError,
       ∃ shape tree,
         Recursion.ValidExecutionTree
           version
           aggregationProgram
           (FinalProof.metadata proof)
           expectedStatement
           shape
           tree ∧
         ISA.ValidExecution
           version
           aggregationProgram
           (PublicInput.encode (FinalProof.metadata proof) expectedStatement)
           (ExecutionTree.root tree) ∧
         Aggregation.ValidClaim version expectedStatement
   ```

   Equivalently, for every admissible adversary, the probability of producing an accepted proof
   for the exact expected program and statement without such a tree and claim is at most
   `totalError`. Until the T6 bridge is resolved, this is a target schema. A conditional theorem
   may instantiate it from a clearly named recursion/extraction hypothesis, but it is not the
   final concrete security theorem. The eventual result exposes `version`, `aggregationProgram`,
   `PublicInput.encode`, all cryptographic assumptions and component error bounds, recursion caps,
   extractor model and running-time bound, and any trusted compiler or foreign-implementation
   bridge.

8. **T8 — end-to-end completeness (`finalProver_complete`).** Given valid raw signatures and/or
   valid child aggregates forming an allowed coverage tree for `expectedStatement`, plus explicit
   capacity and resource hypotheses, the interpreter, witness generator, prover, recursive
   aggregation, and root discharge construct `proof` satisfying
   `FinalVerifier.AcceptsExpected version proof expectedStatement`. This is a liveness theorem
   about the real pipeline, not merely satisfiability of an abstract constraint system.

The intended composition is:

```text
T1 constraints ⇔ ISA ─┬─ T2 concrete witness generation ─┐
                      └─ T3 exact guest ⇒ claim          │
T4 base proof ⇒ ISA ──→ T5 recursive verifier ──→ T6 recursion bridge (open)
                                                        │
                                      T7 soundness schema
                                      T8 end-to-end completeness
```

Component proofs can live with the definitions they justify. This ladder does not require an
empty end-to-end namespace before there is an implementation; it defines the interfaces that
must eventually compose.

### Recursive post-quantum signature aggregation guest

The primary guest is the recursive XMSS and SPHINCS aggregation program at the pinned leanVM
revision. Its functional specification must state at least:

- each non-empty XMSS group has one epoch and one message, epochs are strictly increasing, keys
  within a group are strictly sorted, and every published key signed that group's message at that
  epoch;
- each published SPHINCS `(key, message)` pair has a valid signature, with pairs sorted and
  deduplicated;
- raw signatures and verified child aggregates cover every published claim, including the
  child-to-parent XMSS group mapping and the permitted overlap/deduplication policy; and
- the public input binds the environment, complete signer-set digest, and deferred claims. A
  caller-level theorem must additionally pin the expected groups and SPHINCS claims rather than
  merely verifying a prover-selected statement.

The proof obligations are:

- prove functional correctness of the guest against that reviewed specification, covering raw
  signatures and recursively aggregated proofs;
- connect the source guest to leanVM bytecode through a certified or verified compiler, or verify
  the emitted assembly directly, following the style of
  [evm-asm](https://github.com/Verified-zkEVM/evm-asm);
- prove that termination of the exact guest on a well-formed public input implies the aggregation
  claim; and
- bind the final statement to the expected bytecode, public-input layout, environment digest,
  signer-set digest, deferred polynomial claims, and parameters, so a valid proof for another
  program or another claimed signer set cannot satisfy the theorem.

Guest correctness is separate from correctness of the general VM. The capstone needs both.

### Constraints and witness generation

- **Constraint soundness (CC-S):** satisfying the constraints implies that a corresponding
  execution of the leanVM ISA program exists.
- **Constraint completeness (CC-C):** every in-scope correct ISA execution gives rise to a
  satisfying constraint assignment.
- **Witness consistency (WC):** the executable witness generator produces the intended
  assignment and that assignment satisfies the constraints. If a converse is claimed, state the
  exact relation: auxiliary columns may admit satisfying witnesses not produced by one
  deterministic generator.
- **Bus, lookup, permutation, and memory correctness (BC):** per-table results compose into one
  consistent execution. This includes table well-formedness, correct lookup implementation,
  multiplicity and interaction-count bounds, memory consistency, and the proof-system argument
  used to enforce the interactions.
- **Hints:** every nondeterministic value that can affect the claim is checked by the guest and
  therefore enforced by the ISA constraints, or is constrained directly in the circuit.
  Supplying a hint must not provide an unchecked route to acceptance.
- **BLAKE2s opcode:** prove both directions of correctness for the Flock-enforced compression
  relation, including the chaining value, four message cells, result cells, byte counter, and
  finalization flags. Connect every optimized BLAKE2s implementation to the same specification.
  Any future precompile receives the analogous obligations.

### Proof system

- State the appropriate soundness or knowledge-soundness notion for every component and compose
  the component errors and assumptions into one overall bound. This includes polynomial and
  lookup protocols, commitments, Fiat–Shamir, and their composition; concrete parameter bounds
  should agree with the methodology represented by
  [soundcalc-lean](https://github.com/symbolicsoft/soundcalc-lean).
- Relate the executable verifier to the protocol specification, including serialization,
  transcript order, domain separation, challenge derivation, statement binding, and rejection
  behavior.
- Prove completeness of the abstract prover and test or verify completeness of the executable
  prover, where implementation failures and resource bounds make it non-trivial.
- Specify each hash role through its exact interface and connect every implementation used by the
  prover, verifier, transcript, Merkle commitments, and guest to the appropriate specification.
  Record the exact collision, preimage, or random-oracle assumptions consumed by higher-level
  theorems. The current leanVM target instantiates these roles with its precise BLAKE2s
  constructions; generic lemmas must not erase their different encodings or domain separation.

Zero knowledge is not an initial target. If added, its component definitions, transforms, error
accounting, implementation correspondence, and composition require the same treatment rather
than being inferred from soundness.

### Recursion

Recursion is a separate layer with repeated obligations, not a consequence of the base verifier:

- prove both directions of constraint correctness for the verifier-in-circuit relative to the
  executable verifier specification;
- bind every inner proof to the intended statement, public inputs, program identity or guest
  verification key, transcript, and recursion parameters;
- compose knowledge soundness and error bounds through the recursion tree without silently
  assuming independent, straight-line, or relativized extractors;
- provide the public decreasing measure or invariant that makes recursive extraction
  well-founded; and
- develop candidate **correct-trace extractability (CTE)** statements around the provisional T6
  relation, including complete ordered executions and full memory. The outer topology developed
  in [lean-vanillaVM](https://github.com/b-wagn/lean-vanillavm) is useful here, but its abstract
  extractor assumptions must not be conflated with the separate ROM proof for leanVM's concrete
  proof system.
- account for the three fixed-polynomial claims that recursion defers: stacked bytecode and the
  two Flock matrices. Prove that recursive batching preserves them and that the root's native
  discharge closes every carried claim.

### Capstone result

T7 and T8 are the audit target: a small public theorem surface rather than a claim assembled by
consumers from internal lemmas. The soundness proof should compose:

```text
FinalVerifier.AcceptsExpected version proof expectedStatement
  ⇒ except with totalError, T4–T6 extract a globally consistent tree of satisfying assignments
  ⇒ T1 maps every assignment to a valid leanVM execution of aggregationProgram
  ⇒ T3 gives the local guest postcondition at every node
  ⇒ induction over the tree establishes
     Aggregation.ValidClaim version expectedStatement at the root.
```

The result must expose its total error bound, cryptographic assumptions, fixed program identity,
public-input interpretation
`PublicInput.encode (FinalProof.metadata proof) expectedStatement`, parameter/source revisions,
and trusted compiler or implementation bridges. The T8 completeness direction connects valid
aggregation inputs and
honest execution through witness generation and proving to final verifier acceptance. Supporting
lemmas remain auditable, but consumers should not need to reconstruct the security claim by
composing dozens of internal theorems themselves.

## Execution and validation paths

```text
Pinned Rust leanVM ←── differential tests ──→ Executable Lean semantics
                                                   │
                                      specified execution interfaces
                                                   ├──→ Lean native/C
                                                   ├──→ Rust FFI
                                                   ├──→ CUDA kernels
                                                   └──→ domain-specific compiler
```

The executable Lean semantics is the common behavioral reference. The native/C path is the
baseline implementation produced by Lean's compiler and is itself a performance target. Rust
FFI and CUDA are optimized implementations of narrow interfaces, not alternative definitions of
VM behavior. A future domain-specific compiler must have explicit source and target semantics and
state which transformations are proved semantics-preserving.

Differential testing compares observable behavior against a pinned Rust leanVM revision. It can
find disagreements and prevent regressions, but does not by itself prove the Rust source correct.
A later Rust-verification effort should connect a stable Rust semantic boundary to the Lean model
and record the compiler, runtime, and foreign-code assumptions that remain trusted.

## Tests

Tests are downstream of every production layer and are never imported by `LeanerVM/`.
Executable Lean tests run through `lake test`. Add:

- small-step examples for the interpreter;
- boundary and malformed-input cases;
- witness/constraint mutation tests;
- differential vectors against authoritative implementations; and
- non-vacuity examples for configurations and certificates.

## Performance backend contract

Add a native or generated-code boundary when all of these are present:

1. a profiled performance target or a concrete implementation-validation need;
2. a pure Lean specification or reference implementation;
3. a documented ownership, error, and memory model;
4. shared workloads and differential tests covering normal and adversarial inputs;
5. benchmarks that separate compilation, setup, transfer, and execution costs; and
6. a CI lane isolated from the proof-only library.

Optimize Lean's native C output before or alongside foreign backends so it remains a meaningful
baseline. Rust FFI follows when a Lean caller needs a measured fast path and the ABI can be
specified. CUDA follows when profiling identifies a stable parallel kernel boundary. A
domain-specific compiler additionally requires source/target semantics, validation fixtures, and
a clear preservation-proof plan.
