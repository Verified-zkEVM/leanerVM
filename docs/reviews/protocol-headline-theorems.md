# Review: the headline theorems and the MCA budget

> An archive of the review of commit `8ae0820` of the branch `docs/protocol-headline-theorems`
> ("name the random-oracle heuristic in the headline theorem, and settle MCA at Annex B's
> constant"), against its base `9595721`: names, paths and line numbers are those of `8ae0820`.
> The review was made by a fresh agent with the `adversarial-review` skill, before the pull
> request was opened. What is accepted from it is text of the
> [protocol blueprint](../roadmap/protocol-blueprint.md), which is the specification. Findings are
> numbered by severity, the hygiene points gathered as finding 12.

**Disposition**:

| Finding | Disposition |
| --- | --- |
| 1. the role-separation lemma as written is false: Merkle nodes are untagged 64-byte inputs with prover-chosen siblings | met: the lemma (`roles_separated`) says only what the tags and lengths separate; the Merkle compilation is proved on the one shared function; the ledger row and Layer 12's comparison with upstream say so; the Rust's "unable to alias" claim and its limit are recorded in `leanvm-target.md` |
| 2. `niError_le` used undefined `rounds` and `hashTerm`; the program-hash collision was unexplained | met: `rounds`, `verifierQueries` and `hashTerm` are defined in the sketch (numerals, and a quadratic term counting the verifier's queries too); the collision term is dropped with the reason (statement fixed outside the probability); a test `niError (2^64) ≤ 2^{−60}`; `niError_le` in the trust surface |
| 3. the deployed `η` were reproduced, not dumped | met: `scripts/dump-whir-eta-rust.sh` dumps them from the pinned Rust; `scripts/whir-mca-budget.py --rust-eta` finds all 224 bit-identical to the reproduction, with the same query counts; Layer 11, decision 35 and the record say "dumped" |
| 4. `A.IsQueryBound Q` is not a predicate at the pin, and a total bound charges coins | met: `HashQueryBound A Q := A.IsQueryBoundP (·.isRight) Q`, coins not charged, in every statement |
| 5. `δ : ℝ≥0∞` admits `⊤` | met: `δ : ℝ≥0`; Layer 13 says the theorem has content only for `δ < 1 − niError Q` and that the repository never supplies `δ` |
| 6. the honest prover as an `Adversary` was not constructible | met: `honestAdversary`, hashing through the oracle and returning the empty proof (rejected) out of fuel; test 37 is stated on it |
| 7. a degenerate `runRandom` would pass tests 36 and 37 | met: `runRandom` defined on VCVio's cached `randomOracle`; Layer 12's tests check a fresh answer uniform and a repeated one cached |
| 8. `verify_simulated` "by unfolding" needs a structural `verifyWith` | met: Layer 12 and test 38 say how it is proved and require `verifyWith` structurally recursive, with no `partial` definition |
| 9. the oracle's input lengths omitted the seed and the program hash | met: both are constants of the statement, computed by BLAKE2s outside the oracle |
| 10. citation drift | met: `whir_config.rs:624-633`, `:426-429`, the `pcs/src/` prefix |
| 11. `mcaConstant` is ArkLib's definition, not Annex B's text | met: a Layer 11 test unfolds it to Annex B's formula |
| 12. hygiene: `BcsSecurity` in `leanth-reuse.md`, unnamed lemmas in the holes table, `proof.sizes` undefined, Flock's security misdescribed, the per-adversary argument restated, an overlong line in `architecture.md`, a misplaced sentence in Scope, a layer number in the status | met: `bcsCompile_stateRestoration` named instead; `chain_randomOracle` and `roles_separated` named and bold; `Proof.sizes?` with `none` counted as rejection; "Flock's security (with the Flock roadmap's inhabitant)"; the engineers' section and `architecture.md` point to Layer 13; rewrapped; moved; Layer 12 |
| the observations | met where they asked for text: "the two stronger forms one would reach for"; the auditor's reading marked as a reading; Scope's T7 sentence aligned with `architecture.md`; the deprecated `Pr[p \| mx]` and the `SampleableType UInt32` instance noted in Layer 12; otherwise no change needed |

Docs-only change; files read in full: the changed blueprint sections (For zkVM engineers, Scope,
ArkLib contracts, the ledger, the picture, the holes, Layers 11–13, acceptance tests, Interfaces
and the trust-surface paragraph, Boundaries, Decisions), `docs/architecture.md` T4,
`docs/leanvm-target.md`'s new bullet, `docs/reviews/whir-mca-budget.md`,
`docs/roadmap/protocol-status.md`'s paragraph, `scripts/whir-mca-budget.py` (run: output
matches the record), the probe artifacts, ArkLib and VCVio at the pins, leanVM at `a386121f`.

Category A discipline: an expectation of the headline was written before the new text: knowledge soundness of the deployed `verify` for a fixed
`(prog, input)`, a `Q`-hash-query oracle adversary, a computable log-reading extractor to an
execution, a closed-form error that must be `< 1`, the ROM-to-BLAKE2s step as a per-adversary
hypothesis that is honest only if (a) an accepting adversary satisfies it, (b) the universal
form is shown false, (c) `δ` is finite; and the one-function problem (chain, grinding, Merkle
nodes and leaves share BLAKE2s; nodes carry no tag and path siblings are prover-chosen).

Target classification: T4, both directions, correctly stated in the blueprint and in
`architecture.md`. No code; no PR body to check.

## Pass A — Specification

No statement in the new text is vacuous or tautological. The design (the heuristic as a
per-adversary, per-event hypothesis; the transfer "two lines by design") is sound and is
presented honestly: the universal form is false (the replayer), the joint-distribution form is
false (any querying adversary), and the honest prover is a `δ = 0` inhabitant whose proof is
accepted (checked below). The only true forms are per adversary and per event; the blueprint
says so and says the content is the random-oracle theorem. The findings are about what the
sketches hide or leave undefined.

### Finding 1 (medium) — The role-separation lemma is false as described: the Merkle-node domain contains the chain's

`protocol-blueprint.md:1332-1334` (also the ledger row `:318`): "the chain, the Merkle nodes and
the grinding share one map, separated by their tags and the Merkle leaves by their length, so one
random function serves as independent oracles per role."

At the pin a Merkle node is `hash_pair(left, right) = BLAKE2s-256(left ‖ right)` on 64 bytes with
no tag (`fiat_shamir/src/merkle.rs:46-51`); in an authentication path `right` (or `left`) is a
raw prover-supplied `sibling_hashes` entry (`merkle.rs:89-92, 120`). A chain step is
`BLAKE2s-256(cv ‖ (c0, c1, c2, tag))` on 64 bytes (`fiat_shamir/src/lib.rs:18-24, 86, 96, 109,
119`). So every chain-domain string is also a node-domain string, and the verifier can be made to
compute a chain value as a node value by a sibling whose last word is `1`..`4`. Only the
grinding-vs-observe-vs-squeeze blocks are tag-separated, and only the leaves are
length-separated (and the seed block, `compress(iv, public_input)`, has no tag at all: `lib.rs:31-35`
says its position is its tag).

Failure scenario: an author states the lemma as domain disjointness or as "`H` restricted to the
roles is three independent random oracles", and it is unprovable; or states it with a
hypothesis excluding siblings with a tag in the last word, which `verify` does not check, so the
Merkle compilation theorem would be about a different verifier.

Fix (replace the bullet): "the *role-separation lemma*: the observe, squeeze, grinding-base and
grinding-nonce blocks are separated by the tag in lane 3, and the leaves from everything else by
their length. The Merkle nodes are not separated: a node is the map on an untagged 64-byte
string, and a path sibling is the prover's, so the node domain contains the chain's. The Merkle
compilation is therefore proved on the one shared function (an unqueried node value is uniform;
a collision costs `3(Q² + 1)/2^256`), and the lemma says only what the tags and lengths give."
Add to the ledger row's "Action here" the same qualification, and drop "as independent oracles
per role".

### Finding 2 (medium–low) — `niError`'s closed form has undefined names, so the auditor cannot see it is `< 1`

`protocol-blueprint.md:1283`: `theorem niError_le (Q) : niError Q ≤ (Q + rounds) / 2^128 +
hashTerm Q`. Neither `rounds` nor `hashTerm` is defined anywhere in the document (grep), and
the prose definition of `niError` (`:1318-1322`) adds "the program-hash collision", which is
not visible in `niError_le` and is unexplained for a theorem whose statement is fixed outside
the probability (a program-hash collision only matters when the adversary chooses the program).
The verifier's own queries under `runRandom` (one squeeze per round, and every Merkle node of
every opened path, thousands per proof) each carry a fresh-value event of `2^{−256}`; the text's
`3(Q² + 1)/2^256` for the Merkle compilation counts adversary queries, and nothing says the
verifier's are covered.

Failure scenario: `niError` is a definition in the trust surface (`:1689`); if `rounds` is
instantiated by the number of hash evaluations of the verifier rather than the number of
challenge rounds, or `hashTerm` absorbs a loose union bound, the headline can be true with
`niError Q ≥ 1` for practical `Q` and nobody is told.

Fix: in the Layer 12 sketch define both names and close the form:
`def rounds : ℕ -- the challenge rounds at the largest admissible sizes (a number, with a
#guard)`; `def hashTerm (Q) : ℝ≥0 := (c + 3) * (Q + verifierQueries)^2 / 2^256` (or whatever the
proofs need, but a closed form), and add to Layer 12's tests "`niError (2^64) ≤ 2^{−60}` by
`norm_num` on `niError_le`". Either delete "and the program-hash collision" from `:1321` or say
it is kept for the adaptive form T7 states.

### Finding 4 (low) — `A.IsQueryBound Q` is not a predicate at the pin and, read as the total bound, charges coin flips

Blueprint `:37, :1284, :1387, :1390`. VCVio at the pin has `IsQueryBound oa budget canQuery
cost` (four arguments, `QueryBound/Basic.lean:46`), `IsQueryBoundP oa p n` (`:222`, counts the
queries whose index satisfies `p`) and `IsTotalQueryBound oa n` (`:733`, counts every query).
`roSpec = unifSpec + hash`, so the adversary's coins are queries; the total bound would exclude
an adversary that flips more than `Q` coins, which weakens the theorem (not a vacuity, an
over-strengthening: the bound should depend on hash queries only).

Fix: write `(hQ : A.IsQueryBoundP (fun i => i.isRight) Q)` (or define
`abbrev HashQueries (A) (Q) := IsQueryBoundP A (·.isRight) Q`) and say in one clause that coins
are not charged.

### Finding 5 (low) — `δ : ℝ≥0∞` admits `⊤`, at which the headline says nothing

`:1384` `(δ : ℝ≥0∞)`. At `δ = ⊤` (or any `δ ≥ 1 − niError Q`) the hypothesis is trivially
satisfied and the conclusion `≤ niError Q + δ` is empty. The text says "Nothing here bounds
`δ`" (`:1437`) but does not say what that means for the reader. Fix: `(δ : ℝ≥0)` and one
sentence: "the theorem has content only for `δ < 1 − niError Q`; `δ` is the auditor's
estimate of how far BLAKE2s is from a random function for this adversary, and the repository
never supplies it."

### Finding 6 (low) — Test 37's witness needs the honest prover as an `Adversary`, which the sketch cannot build

`Adversary := OracleComp roSpec Proof` (`:1280`) and `proveWith … : m (Option Proof)` (`:1396`).
The honest prover run as an adversary must (i) hash through `query` (`proveWith (m :=
OracleComp roSpec) query …`), otherwise its leaf queries are not in the log and `extract` fails;
(ii) return a `Proof` on `none` (fuel exhausted), which must then be rejected for the `δ = 0`
claim `Pr[bad | runBlake2s] = 0` to hold. Neither is written. Fix: add
`def honestAdversary (fuel w ρ) : Adversary := do match ← proveWith query fuel F prog input w ρ
with | some p => pure p | none => pure ⟨[], []⟩` and state test 37 on it, with the one-line
argument that `⟨[], []⟩` is rejected (stream not consumed).

### Finding 7 (low) — A degenerate `runRandom` is not caught by tests 36–37

`runRandom` is in the trust surface (`:1689-1690`), as it should be: a `runRandom` answering
every query with a fixed value, or freshly without a cache, still passes test 36 (the stored
proof is rejected) and test 37 (`Pr[bad | runBlake2s] = 0` does not look at `runRandom`), and
would move all the content into `hRO`. Fix: define it by name in the sketch,
`def runRandom := simulateQ (liftCoins + (hashSpec).randomOracle) ∘ (·.run' ∅)` on VCVio's
`OracleSpec.randomOracle` (`QueryTracking/RandomOracle/Basic.lean:24-27`, cached uniform
sampling), and add a guard lemma to Layer 12's tests: a fresh hash query under `runRandom` is
uniform on `Vector UInt32 8` and a repeated one returns the cached value.

### Finding 8 (low) — `verify_simulated` "holds by unfolding" is only true for a structurally defined `verifyWith`

`:1294-1296, :1613`. Lean has no parametricity theorem, so `runBlake2s (verifyWith query …) =
pure (verify …)` is proved by pushing `simulateQ` through `verifyWith`'s body
(`simulateQ_bind`, `simulateQ_query`). That fails if `verifyWith` is `partial`, well-founded over
a measure, or uses `for` loops in a monad transformer the simp set does not know. Fix: one
clause in Layer 12: "`verifyWith` is structurally recursive (fuel from the stream length), so
`verify_simulated` is `simp [verifyWith, simulateQ_bind, …]`."

### Observations (no failure)

- `:1420` "every stronger form is false" overclaims; two natural stronger forms are shown false.
  Say "the universal form and the joint-distribution form are false".
- `:1433-1436` "An auditor reads it as: this adversary learns BLAKE2s values only by asking" is an
  interpretation, not the hypothesis; the hypothesis compares two probabilities of one event.
  Keep, but mark it as the reading, not the content.
- Scope `:185-187` says T7 states the adaptive form, while `architecture.md`'s T7 schema fixes
  `expectedStatement` (non-adaptive). Pre-existing; worth one line either way.
- Test 36's `niError 0` bound on the replayer under a random function is correct (from the ROM
  theorem at `Q = 0`, `extract` on the empty log is `none`) and loose (the true probability is
  about `2^{−256}`); fine.
- Test 37 is right: under BLAKE2s every proof the honest prover returns is accepted
  (`baseProver_complete`), its log holds every leaf and node of the level-0 tree, the honest
  word is in the list at distance 0 and satisfies `M3Holds` (`m3Holds_stackOf`), so `extractTrace`
  returns a valid execution and `Pr[bad] = 0` for every coin outcome.
- Non-adaptive vs adaptive is consistent across For zkVM engineers, Scope, Layers 12–13 and
  `architecture.md` T4 (statement outside the probability everywhere).
- Computability: `extract` (subset interpolation over `K`, membership decided on finite rows)
  and `M3Holds` (finite clauses over `E` with decidable equality) are computable as specified;
  `traceOf` is honestly flagged as a request with the `gLog?` obstacle named (`:1733-1739`).
  `mcaError`, `runRandom` and `Pr[…]` are noncomputable but are not extractors.
- Completeness statements claim no existence of a grinding nonce under BLAKE2s (`:1456-1459`);
  `baseProver_complete` is for every `H` in `Id`. Correct.

## Pass B — Fidelity (leanVM `a386121f`, ArkLib `7653a901`, VCVio at the pin)

Verified correct:
- Statement binding: `ProverState::new(digest_words(fs_seed(program)), digest_words(public_input))`
  then `announce_public` then the commitment, before any challenge (`cpu/mod.rs:556-560`,
  `:712-714`); `fs_seed` is `BLAKE2s("leanvm" ‖ len ‖ R1CS_DIGEST ‖ bytecode_hash)`
  (`cpu/mod.rs:82-94`). Matches the Pinned convention and the For-zkVM-engineers claim.
- Chain, grinding and nodes on 64-byte inputs: `compress` (`lib.rs:18-24`), `pow_bits_ok`
  (`:47-51`), `hash_pair` (`merkle.rs:46-51`). Tags `1..4` in lane 3 (`:36-39`).
- Leaves 512 bytes at level 0 (`INITIAL_FOLDING_FACTOR = 6`, `whir.rs:378` with
  `leaf_words = 2^6` K words) and 384 bytes at every later level (`SUBSEQUENT_FOLDING_FACTOR
  = 4`, `derive_ladder` always folds 4 while `n_running > RESIDUAL_MAX_LOG`, `whir_config.rs:279-280`;
  `whir.rs:467` leaf = `num_interleaved × 24` bytes). The residual is sent in the clear.
- `McaJohnson` sketch vs ArkLib: hypotheses `1 ≤ D`, `D ≤ n − 2`, `0 < η`, `√(D/n) + η ≤ 1`
  are exactly `mcaError_affineLine_johnson_le`'s (`Probability.lean:41-48`, with
  `johnsonAgreement = √(D/n) + η`, `FiniteBounds.lean:70-71`); the radius
  `1 − √(D/n) − η` is the theorem's; `domain : Fin n ↪ F`, `[Field F] [Fintype F]
  [SampleableType F]` match; dropping `min 1` is sound; the step from ArkLib's
  `johnsonExceptionCount n D ⌈(√ρ+η)·n⌉₊ η` to `johnsonComparisonEstimate` is
  `johnsonExceptionCount_le_comparisonEstimate` (`:849-854`) with `hthreshold` by `Nat.le_ceil`.
  `johnsonComparisonEstimate` (`:137-141`) is Annex B's `a` symbol for symbol (`θ = max ⌈√ρ/η⌉ 3`,
  `t_B = θ + ½`, `γ = 1 − √ρ − η` the radius, `ρ = D/n`; `b-polynomial-commitment-scheme.tex:176-186`).
  The fold term `2^{ℓ−1}·ε` is `thm:rbr`'s `2^{ℓ_i − j} ε_i` at `j = 1` (`:144`).
- `scripts/whir-mca-budget.py` runs (standard library only) and reproduces the record: 224
  levels, 0 query-table mismatches, 108/224 ceiling differences, least margin 128.185 bits
  (`(27, 3)` level 0), 143.162 with `E₀`, max float error 1.813 bits.
- `whir_config.rs:1014-1042` (the production-profile test) and `:426-429` (`reduced_rate`) are
  right; `transcript.rs:9-19` covers `Proof`; `lean_compiler/src/lib.rs:162` is the
  `Op::Set` fill; `cpu/mod.rs:82-124` and `fiat_shamir/src/lib.rs:18-174` are right.

### Finding 3 (low–medium) — The deployed `η` are reproduced, not dumped

`:1160` "the exact value of the Rust's double", `:1218`, decision 35 "`η` is the exact value
of the Rust's double". The record (`whir-mca-budget.md`, "Not verified") says the Rust was not
run and no pinned artifact carries `η`; the values are a Python re-implementation of the
search in doubles, pinned only by the query-count table (`py:910`), which does not determine
`η` to the ulp. Repository policy (the review skill's fidelity reference) is that constants are dumped
mechanically from the pinned source. An ulp difference can flip `⌈√ρ/η⌉` between `m` and
`m + 1` and move `a` by up to 1.81 bits (the record's own finding); at the least-margin level
the flip costs about 0.1 bits, so the verdict survives, but `Parameters/Whir.lean` would hold
values with no pinned source.

Fix: add `scripts/dump-whir-eta-rust.sh <checkout>` (the precedent is
`dump-leanisa-layout-rust.sh`) that prints each level's `eta.to_bits()` from
`WhirSecurityConfig::derive_config_with_log_inv_rate`, run it once, record the table in the
review, and have `ladder`'s test compare against it. Until then write "reproduced by
`scripts/whir-mca-budget.py` and pinned by the query table" in `:1160`, `:1218` and decision 35.

### Finding 9 (low) — The list of the oracle's input lengths is incomplete

`:115-117`: "The Fiat–Shamir chain, the Merkle nodes and the grinding call it on 64-byte
inputs, and the Merkle leaves on 384- or 512-byte ones." The seed also hashes a 78-byte string
(`fs_seed`, `cpu/mod.rs:82-94`: 6 + 8 + 32 + 32 bytes) and the program hash the stacked
bytecode table (`cpu/mod.rs:237-243`, `8 × |table|` bytes). Whether those two run through the
oracle (`FsState.seed … in m, given H`, `:1250`) or are constants of the statement decides
whether `runRandom` randomizes the seed; the model must say which. Fix: add "the seed on a
78-byte string and the program hash on the stacked bytecode table, both constants of the
statement, computed by `blake2sBytes` outside the oracle" (or the opposite, if the seed is to
go through `H`).

### Finding 10 (low) — Citation drift

`leanvm-target.md:227` and `whir-mca-budget.md` "The Rust's doubles": `johnson_eta_for_m` is
`whir_config.rs:624-633` (the body ends at `:633`; `:635-637` is the next function's comment).
`:1201` `reduced_rate` is `:426-429`. `leanvm-target.md:233` writes `whir_config.rs:1014-1042`
without the `pcs/src/` prefix the same bullet uses at `:227`.

### Finding 11 (low) — `mcaConstant` is ArkLib's definition, not Annex B's text

`:1177` `def mcaConstant … := johnsonComparisonEstimate n D η`. A pin bump that changes
ArkLib's definition changes leanVM's constant silently. Fix: add to Layer 11's tests
"`mcaConstant n D η = (2(θ + ½)^5 + 3(θ + ½)γρ)/(3·√ρ^3)·n + (θ + ½)/√ρ` with `θ = max ⌈√ρ/η⌉₊ 3`,
by unfolding", so the transcription of Annex B is the repository's and ArkLib's is checked
against it.

### Observations

- The `Pr[p | mx]` macro exists at the pin (`EvalDist/Defs/Basic.lean:113-114`) but `probEvent`
  is marked deprecated since 2026-09-13 ("use `𝒟[mx]`"). The sketches may need `𝒟[mx] {x | p x}`
  at the next VCVio bump; worth one line in the ledger.
- `SampleableType UInt32` has no instance in VCVio at the pin (the `Vector α n` instance
  exists); leanerVM supplies one as it did `instSampleableTypeK` (`Protocol/Field.lean:75`).
- `simulateQ`, `withQueryLog` (`LoggingOracle/Core.lean:496`), `QueryLog` (`Structures.lean:382`),
  `ProbComp`, `unifSpec`, `→ₒ`, `OracleSpec` `+`, `randomOracle`, `AffineLineGenerator`
  (`ProximityGenerator/Basic.lean:335`), `mcaError` (`:191`), `code` all exist at the pins.
- `Proof.sizes` (`:1288, :1375`) is used but `Proof` has only `stream` and `merkle`; name the
  decoder and its failure value (see finding 12).

## Pass C — Hygiene

- `docs/roadmap/leanth-reuse.md:255`: two references to `BcsSecurity`, a structure this change
  deletes. Replace by `bcsCompile_stateRestoration`.
- `:623` holes row "the random-oracle theorems" lists "the chain lemma, the role-separation
  lemma" without names; the table's rule is that a hole is built when its bold names are
  declared. Name them (for example `chain_isRandomOracleOnPrefixes`, `roles_separated`) and bold
  them.
- `:1288, :1375` `proof.sizes` is undefined; `decode prog s proof` takes `s`. Add
  `def Proof.sizes? : Proof → Option Sizes` to the Layer 12 sketch and say the event uses
  `s` from it with `none` counted as rejection.
- `:44-46` "Every step to it is proved in the random-oracle model: Flock's security, …" —
  Flock's security is interactive and #3's. Say "Every step to it is a theorem: Flock's security
  (#3's inhabitant), WHIR's correlated agreement (ArkLib), the Merkle compilation and the chain
  with proof of work (Layer 12, in the random-oracle model)".
- The per-adversary argument is restated four times (`:122-127`, `:1425-1439`, test 36,
  decision 34) plus `architecture.md:285-291`; the document's rule is one home per fact
  (`:1793`). Keep Layer 13 as the home, cut For zkVM engineers to two sentences and a link,
  and architecture to one sentence.
- `architecture.md:291` the appended sentence makes a 110-character line and runs "It is
  never an axiom." into "Its completeness dual …"; rewrap.
- `:195-196` the sentence about the extractor's computability sits under the "performance of
  the honest prover" out-of-scope bullet; move it to the heuristic bullet or to In scope.
- `protocol-status.md:640` points the round-by-round-to-plain step at Layer 13; the blueprint
  places it in Layer 12 (list-binding row). Pre-existing; one word.
- House style otherwise holds: no letter codes, names in words, history in the status file and
  the review record, the blueprint timeless. The new record and script are readable.
