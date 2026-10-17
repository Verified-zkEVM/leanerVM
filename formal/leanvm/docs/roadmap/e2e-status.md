# Status: end-to-end soundness and completeness of the deployed verifier

Branch `e2e/rom-knowledge-soundness`, built on the open stack #86–#99, #82/#83 and #67, at leanVM
`a0ca7858f2533ce51abdc20bb635c007e19b26b3`. Design: [e2e-rom-design.md](e2e-rom-design.md).
Every theorem below depends only on `propext`, `Classical.choice`, `Quot.sound` (`#print axioms`,
locked in the tests).

## The front page

The statements are in [`LeanerVM/Spec/`](../../LeanerVM/Spec/README.md), which imports nothing
else from the repository: the fields, BLAKE2s, the ISA (`Isa.lean`: `Program`, `PublicInput`,
`Trace`, `ValidExecution`, `SentinelSafe`, `HasFillBlocks`), the verifier (`Verifier.lean`, with
the WHIR and Flock constants and the Fiat–Shamir transcript), and `Statement.lean`, which states
`KnowledgeSoundness` and `Completeness` as propositions, the extractor and the honest prover
existentially quantified. [`LeanerVM/Protocol/LeanVM.lean`](../../LeanerVM/Protocol/LeanVM.lean)
proves them (`knowledgeSoundness_holds`, `completeness_holds`) with an explicit extractor and
honest prover:

* `verifier H prog input proof : m Bool`: the verifier, for a hash function `H : Bytes → m Digest`
  in any monad; `verify` is the BLAKE2s instance (`m = Id`), the deployed verifier, and the
  knowledge-soundness experiment runs the same `verifier` with `H` a random-oracle query;
* `knowledgeSoundness`: against an adversary of at most `Q` queries that outputs a statement (a
  program and a public input) and a proof, all chosen after querying the oracle,
  `Pr[accepted ∧ SentinelSafe prog ∧ the extracted execution is not a valid execution of prog on
  input] ≤ soundnessError Q` (`Breaks`), with
  `soundnessError Q = (Q + 13213)·(2^-128 + 5·(Q + 13213)/2^256)`. `SentinelSafe` (the program's
  last instruction is not a `JUMP`) is the one condition soundness needs. The extractor returns
  an execution (`Trace`): the memory image the proof commits to, run until it halts;
* `soundnessError_le`: at most `2^-63` for `Q ≤ 2^64`;
* `completeness`: for a valid execution of at most `2^19` steps, a memory of at most `2^23` words
  and a bytecode of at most `2^23` instructions, of a program carrying the fill blocks
  (`HasFillBlocks`, the one trace of padding in a statement: the deployed prover pads its tables
  with blocks the compiler appends to the bytecode), at a rate `1 ≤ ρ ≤ 4`, the honest prover
  (`honestProver`), run as the adversary of the same random-oracle experiment with a fuel of
  `fuel` nonces per proof of work, makes the verifier reject with probability at most
  `completenessError fuel = Q·((1 - 2^-17)^fuel + Q/2^256)`,
  `Q = 13216 + 13210·(2^27 + fuel + 1)`;
* `completenessError_le`: below `2^-128` at `fuel = 2^25`.

The size bounds trade against each other (`Complete.exists_admissible_witness_of_budget`:
`8·2^κ + 2^logSize + 356·2^n ≤ 2^28` for `2^n` steps); `2^20` steps never fit the deployed
`MAX_MU = 28`, whatever the program (the BLAKE2S table's Flock region alone would have `2^28`
rows).

## The verifier the theorems are about

`verifier` is `LeanerVM.Protocol.Verifier.verifyWith`. The whole verifier is one file,
[`LeanerVM/Spec/Verifier.lean`](../../LeanerVM/Spec/Verifier.lean), in the sections of
`verifier.py` (about 1700 lines against the Python's 1433). It is the compiled
reading of `leanVmProgram`, a transcription of `python-verifier/verifier.py` at the pin in the
verifier language `Compile/Prog.lean` (read, sample, grind, commit, query): the Fiat–Shamir chain
with proof of work and Merkle openings. The random-oracle side is the same program,
`verifierComp_leanVm` (`Verifier/Cost.lean`), which makes at most `13213` queries.

**Running it.** `lake exe leanvm-verify bytecode public_input stream merkle_openings`
(`cli/LeanvmVerify.lean`) runs `verify` compiled, on the four files the Rust prover writes. It
checks a real Rust proof in about 0.3–0.7 s and 100 MB: the field (`Spec/Fast/FieldWords.lean`,
`Spec/Fast/CubicExt.lean`) and BLAKE2s (`Spec/Fast/Hash.lean`) are swapped for word-level
code by `@[csimp]` theorems, so the verifier's definitions are the readable ones and the compiler
runs proven-equal code.

**Evidence that it is the deployed verifier** (test evidence, not proof):

* the pure helpers against the Python, and a full replay of a Python mock prover's transcript
  (`tests/LeanerVMTests/Protocol/Verifier/`, drivers in `scripts/verifier-mock/`);
* three proofs of the Rust prover at the pin (`tests/fixtures/verifier/`, from
  `scripts/export-verifier-fixtures-rust.sh`), accepted;
* differential fuzzing against the deployed Rust verifier (`scripts/fuzz-verifier.py`,
  `scripts/rust-verifier-cli/`): structured and seeded random mutations of every phase's
  scalars, the roots, the nonces, the Merkle openings, the public input and the bytecode, the
  same verdict required of both verifiers. 28,800 cases in all, no difference, no Rust panic:
  * on the three committed fixtures, 8400 cases (seeds 1–4); seed 3 runs in about 3 minutes at
    8 jobs: `python3 -I scripts/fuzz-verifier.py tests/fixtures/verifier
    --mutations 2000 --seed 3 --jobs 8`;
  * on a corpus of 68 honest Rust proofs (`scripts/export-verifier-fixtures-rust.sh
    <out> --corpus`: every program of leanVM's compiler test suite that declares its public
    input, and the chain at 16, 1000 and 5000 steps, each at the four rates), 20,400 cases (seed
    5, 300 per proof): both verifiers accept the 68 honest proofs and reject the 20,332 mutations,
    which reach 32 distinct Rust rejection reasons (Merkle, every GKR layer, the table sumcheck,
    the public input, Flock, ring switching, WHIR, proof of work, the announced sizes, the file
    lengths); about 11 minutes at 8 jobs.

## Soundness (`LeanerVM/Protocol/EndToEnd/Sound/Statements.lean`)

In the random-oracle model for BLAKE2s-256 on byte strings (VCVio's `randomOracle`), against any
adversary making at most `Q_A` queries and outputting a statement and a proof:

* `leanVm_knowledge`: the verifier accepts while the extractor (reading the announced sizes and
  the stack's commitment off the oracle's answers, then picking a stack of the Johnson list
  satisfying the relation; a classical choice) returns no stack satisfying `M3Holds` for the
  adversary's statement with probability at most `(Q_A + 13213)·(2^-128 + failBound)`
  (`failBound`: `(4 + k)·N/2^256` with `k = 1` common seeding step);
* `leanVm_execution`: the same bound for "accepts, the program is `SentinelSafe`, and the
  extracted witness represents no valid execution" (through the adaptor and
  `constraintSoundness`); the front page's `knowledgeSoundness` is this statement;
* `leanVm_bound_le`: for `Q_A ≤ 2^64` the bound is at most `2^-63`.

**Chosen statements.** The random-oracle theorem (`Compile/Rom/Sound.lean`, `romSound`) takes a
family of seedings (`Seeds`, `Compile/Rom/Log.lean`), one per statement, over one verifier program
and one doom certificate. The decoder recognizes the seed of any statement of the family by the
input that completes its seeding (`rootAt`): the last seeding input, computed through answers
without collisions, names the statement (`Seeds.inj`). For leanVM the program is `anyProgram`
(read the statement's bytecode length and words and the public input's lanes, then run its
verifier program), the root of a statement is that history of reads (`stmtHistory`, prefix-free:
`stmt_eq_of_prefix`), and the certificate `anyCert` is `leanVmCert` of the statement past its
root. The family needs `bytecodeWords_injective` and `publicDigest_injective`. A fixed statement
is the special case of an adversary that outputs it.

The per-query error `2^-128` is certified: every group of challenges of the deployed opening
escapes with probability at most `2^-128` after its proof of work, at all 56 admissible (stack
size, rate) pairs (`Whir/Params/Deployed.lean`, a kernel-checked certificate table over ArkLib's
proved Johnson-range MCA). The margin is thin: the weakest shape is `(μ, R) = (15, 2)` at about
`2^-128.16`, and `2^-129` is not reachable with the deployed query table. The front phases'
groups are below `2^-134` (the bus fingerprint group, `L₀·4·2^μBus/|E|` with `μBus ≤ 38`; the
others below `2^-150`).

The fold group is proved with the row-union factor `(2·listMax + 2^(ℓ−1)·mcaMax)/|E|`. Annex B at
the pin states the smaller `2L/|E| + ε` (`lem:fold-list`, citing Jo, ePrint 2026/891, Thm 4.4),
under which 25 of the 56 query counts were lowered (`b977f5fa`); the table certifies the lowered
counts under the larger, proved bound, so the Annex's bound is not used.

**No open input.** The theorems take no hypothesis beyond the adversary's query bound (and
well-formed bytecode). The deployed computations of every phase are proved equal to the analysed
protocol's: the bus and the table sumcheck (`Front/TableFidLeanIsa*.lean`), the public input,
Flock and ring switching (`Front/{Pub,Flock,Ring}*.lean`), the BLAKE2s circuit walk row for row
(`Front/WalkFaithful.lean`), and WHIR (`Whir/Sound/`).

## Completeness (`LeanerVM/Protocol/EndToEnd/Completeness.lean`)

* `leanVm_interactiveComplete`: from a witness with `SatisfiedBy` at admissible sizes and a valid
  rate, an honest strategy makes the verifier program accept against every challenge function;
* `leanVm_complete` (every hash function) and `leanVm_complete_blake2s` (the deployed `verify`):
  the compiled honest prover's proof is accepted whenever its proof-of-work searches find nonces
  below the fuel;
* `leanVm_complete_of_execution`: from a valid execution of well-formed bytecode that fits
  (`constraintCompleteness`).
* In ISA terms (`EndToEnd/Complete/Small.lean`): a valid execution of a program with the fill
  blocks (`HasFillBlocks`) that is small (`Trace.Small`: at most `2^19` steps, `2^23` words of
  memory, `2^23` instructions) has a witness at admissible sizes (`exists_admissible_witness`;
  the budget form `8·2^κ + 2^logSize + 356·2^n ≤ 2^28` for `2^n` steps is
  `exists_admissible_witness_of_budget`), and the honest proof of the execution (`honestProofOf`)
  exists when the proof-of-work searches succeed and is accepted (`complete_of_small`). The
  witness's heights come from `constraintCompleteness_heights`, which needs of the bytecode only
  its fill blocks.
* In the random-oracle model (`EndToEnd/Complete/Rom.lean`, `Compile/Rom/Complete.lean`): the
  honest prover is an oracle computation (`proveM`, equal to the pure prover at `Id`,
  `proveM_id`), run as the adversary of the soundness experiment. On every outcome where it
  returns a proof the verifier accepts (`simulateQ_id_of_look`, `runProof_prove`); it fails only
  at a proof-of-work search whose `fuel` nonces all fail, which a potential on the oracle's log
  bounds (`powPot`: each nonce fails with probability exactly `1 - 2^-17`, `avg_miss_eq`). The
  rejection probability is at most `Q·((1 - 2^-17)^fuel + Q/2^256)` (`romComplete`), and
  `(1 - 2^-b)^(2^b·k) ≤ 2^-k` (`missProb_pow_le`).

## Trust boundary

* BLAKE2s-256 is modelled as a random oracle; nothing is claimed about attacks using its code.
* The verifier is the Lean transcription of the Python verifier; its agreement with the Python
  and the Rust verifiers is test evidence (above).
* Knowledge extraction is information-theoretic (a classical choice in the Johnson list).
* A proof is the Python verifier's format, one full Merkle path per query. The Rust prover ships
  pruned paths, which `leanvm_core::cpu::verify` expands into these paths and checks more
  strictly; the expansion is not formalized, and the fuzzing exercises only the raw format.
* `SentinelSafe` is not checked by the verifier. leanVM's compiler always satisfies it (the last
  slot is padding); for hand-assembled bytecode whose last instruction is a `JUMP`, the deployed
  constraints accept runs that are not valid executions.
* The adversary is deterministic (`OracleComp` has no coins); randomized adversaries follow by
  averaging, not stated formally.

## Adversarial review (2026-10-16)

Six independent reviews of the formalization (the ISA against the specification and the Rust
executor; the front-page statements; the verifier against the Python and the Rust verifiers; the
random-oracle model and the bound; the trust base; the arithmetization) found no critical issue
and no input on which the Lean verifier and the deployed verifiers disagree. Fixed: a false claim
that the front phases' groups are below `2^-150` (the bus fingerprint group is about `2^-134`;
every group is still below `2^-128`), stale "blocked" notes in `Arithmetization/Statement.lean`,
two instruction docstrings, and the trust gates: the axiom audit now covers every declaration of
a first-party module whatever its namespace (the front page's `LeanVM.*`, the `@[csimp]` lemmas on
CompPoly's types), and the source policy also rejects `decide +native`, `set_option debug.*`,
`implemented_by`, `extern` and `addDecl`, and scans `cli/`. Open, in order of relevance:

1. **Pruned openings.** Prove that a pruned proof the deployed verifier accepts expands into a raw
   proof `verifier` accepts, so that the theorems cover the format the Rust prover ships. Kept
   out of scope for now: the statements are about the raw format.
2. **Adaptive soundness.** Done: the adversary chooses the program, the public input and the
   proof (`knowledgeSoundness`, above).
3. **Encodings against Rust.** `bytecodeWords` and `publicDigest` are checked against a
   hand-transcribed table only; a test against tables generated by the Rust `bytecode_table` and
   `public_input_bytes` would close the gap.
4. **Completeness.** Done without the proof-of-work hypothesis (probability at most
   `completenessError fuel`). Open: runs larger than `2^19` steps that the deployed parameters
   admit when they are not BLAKE2S-heavy (the budget form allows it).

## Findings along the way

* **Model fidelity (fixed)**: the Clean DEREF table flushed its memory reads in the order ptr,
  local, target; the deployed verifier uses ptr, target, local, which matters for the bus's leaf
  stacking. Fixed at the source (`Arithmetization/Tables/Deref.lean`).
* **Roadmap statements**: `no_row_at_sentinel` as written over `w.interactions` is false (the
  verifier's own sentinel pull); proved over the tables' rows. The blueprint's
  `constraintCompleteness` shape was already corrected by #82.
* **Own design**: a first `Spec.bind` rule double-counted returns outside doom (checked
  counterexample); fixed by folding the follower's lead into the potential. Three gaps of the ROM
  design note (groups without a squeeze, the root's own entry, seeding injectivity) were fixed
  as built.
* **Proof interface**: an intermediate hypothesis (`TableFidHyp`) quantified over bus reads with
  any number of fingerprint challenges and was false (with five, the Python's slot weights differ
  from the model's); the deployed verifier always draws four, which the bus specification now
  carries.
* **The bump to `127510d`** (from `a386121f`) changed the verifier, the layout and the parameter
  table; every proof was adapted and the certificate table re-derived. No soundness or
  completeness bug of the deployed verifier was found at either pin: the WHIR gluing order, the
  OOD and query ordering, the Flock walk (row for row), the public-input claims and the bus and
  table computations all match the analysed protocol.
