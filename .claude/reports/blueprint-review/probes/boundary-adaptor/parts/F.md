
## F. `docs/architecture.md` validated against the blueprint and the code

The obligation map for the fourth target theorem (`architecture.md:261-275`, the "Proof
system" list `:446-462`, the ladder `:63-70`), item by item:

| Obligation (`architecture.md`) | In the blueprint | In the code at `b435631` | Verdict |
| --- | --- | --- | --- |
| the bridge "`BaseVerifier.Accepts … → except with probability baseError, ∃ assignment, Constraints.SatisfiedBy …`" (`:264-269`) | `verify_knowledgeSound` + `satisfiedBy_witnessOf` (`:1226-1227`, `:815-816`) | neither; `M3Holds`, `M3Rel`, `Refinement` built | consistent in content; the `version` parameter of the architecture is the pin recorded in prose, not a Lean argument |
| "then compose it with T1-S" (`:270`) | Layer 13 (`:1253-1254`) | `constraintSoundness` not stated | consistent, except that T1-S's hypothesis `WellFormedBytecode` (`architecture.md:224-228`) is dropped in the composed statement (finding 3) |
| expose "the component soundness/knowledge-soundness bounds, Fiat–Shamir or random-oracle model, commitment and hash assumptions, transcript/serialization agreement, and executable-verifier refinement" (`:270-273`) | `niError`, `FiatShamirSecurity`, `BcsSecurity`, `McaJohnson`, `verify_iff_compiled` (`:1218-1228`) | `piopError`, the two master theorems (`Compose.lean:149-185`) | the random-oracle model and the hash assumption are named as interfaces for the *compiled* protocol but the concrete `verify` uses BLAKE2s: the heuristic "BLAKE2s is the random oracle" is exposed nowhere (finding 3); the family composition over `s` is exposed nowhere (finding 6) |
| "Its completeness dual composes T2 with the honest prover and records any failure/resource conditions" (`:273-275`) | `baseProver_complete` composes T1-C, "witness generation (T2) … out of scope" (`:147-148`, `:1255-1256`); no resource condition | nothing built | **divergent**: T2 is replaced by an existence theorem, which does not yield the witness `prove` needs, and no resource condition is recorded although two are load-bearing (finding 4; `docs-debt.md` B.6 item 3) |
| "Relate the executable verifier to the protocol specification, including serialization, transcript order, domain separation, challenge derivation, statement binding, and rejection behavior" (`:453-455`) | Layer 12: `verify_iff_compiled`, the stream order, the tags, `FsState.seed`, total `verify` | nothing built | consistent; "statement binding" needs the injectivity of `prog ↦ bytecodeColumn prog` (B.2, item 1), unstated |
| "Prove completeness of the abstract prover and test or verify completeness of the executable prover" (`:456-457`) | `piop_perfectCompleteness`; `prove` "a specification that runs" (`:158`); the Rust prover by fixture only | `piop_perfectCompleteness` (conditional) | consistent; the executable (Rust) prover's completeness is evidence, not a theorem, as `architecture.md:530-533` allows |
| "T4 — base proof extraction/completeness: proof-system components, T1, and T2" (`:66`) | inputs: the components, T1; not T2 | | as above |
| `leanvm-target.md:123-124`: "T4: formal component notions, Fiat–Shamir assumptions, composed error bound, and verifier refinement"; "each [verifier implementation] accepts exactly the specified protocol and statement encoding" | the first is Layers 10-13; the second is the fixture plus `verify_iff_compiled` | | the Rust and Python verifiers do *not* accept exactly the specified protocol on the public-input check (status finding F18; `code-pubinput.md` G.2), so "exactly" is owed a lemma the blueprint assigns to Layer 12 |

Obligations of the map with no counterpart in the blueprint: T2 in the completeness dual;
the resource conditions; the random-oracle instantiation as an explicit hypothesis; the
statement-binding lemma. Blueprint layers that serve no obligation of T4: none (every layer
feeds `verify` or a theorem about it); three named declarations serve nothing on the chain and
are tests of non-vacuity or candidates for upstream: `witnessOf_stackOf` (E.2),
`Extractor.Straightline.map` (no possible consumer in this repository, E.6),
`piop_rbrKnowledgeSoundness_exists`.

One more point of the architecture the blueprint's T4 loses: "the extracted leanVM witness
should contain ordered `pc`/`fp` steps and the full memory image" (`architecture.md:332-335`,
for T6). The chain has it, `constraintSoundness` giving `AssignmentRepresents (witnessOf prog
s q) t` for the extracted `q`; `baseVerifier_extractsExecution` keeps only `∃ t,
ValidExecution prog input t` (`:1247-1248`), which is a language membership and needs no
extractor at all. Stating the pointwise theorem in the form "for the extractor's `q`, when it
satisfies `M3Holds`, `∃ t, AssignmentRepresents (witnessOf prog s q) t ∧ ValidExecution prog
input t`" costs nothing and is what recursion consumes (note 16).
