## Motivation

Hole P5 of the proof-system roadmap (#12): the public-input phase, specification §8.2. It ties the public statement to the committed memory, by checking that cells 0 and 1 of the memory columns hold the public words.

It is the first phase built on the spine with a challenge, a prover message, a verifier that can reject, and a nonzero error. So it also sets the proof pattern for the phases that follow (P1, P3, P7).

## What the phase does

The phase is §8.2 as the specification writes it, over the public lines of an abstract instance. A public line is a column together with the values its cells 0 and 1 must hold.

1. The verifier draws one challenge `r` in the extension field `E`.
2. The prover sends, as one message, the values it claims for the public columns at the point `(r, 0, …, 0)`, for the lines whose value is sent.
3. The verifier checks the message against the line through the statement's two cells, `(1 + r)·cell0 + r·cell1`, and rejects otherwise. The check fixes the length of the message too.
4. The verifier pools one claim per public line, after the claims of the earlier phases. The opening phase settles them.

For leanISA the lines are the three memory limbs. The prover sends `c_0, c_1` for the two low limbs, and the claim on the top limb is pooled with value `0` and no scalar.

Both halves are proved:

| Declaration | Statement |
| --- | --- |
| `publicInputComplete` | perfect completeness between the seams `Seam.table` and `Seam.pub` |
| `publicInputSecurity` | round-by-round knowledge soundness with the trivial extractor, at error `1/\|E\|` on the one challenge |

The error is one line's whatever the number of lines: a line whose cells differ from the statement's makes its claim a nonzero polynomial of degree one in `r`.

## What is in it

| Module | Content |
| --- | --- |
| `PublicInput.lean` | in the namespace `PublicInput`: `linePoint`, `eval₂Mle_linePoint`, `pSpec`, `error`, `lineValue`, `lineClaim`, `pooled`, `expectedValues`, `check`, `prover`, `verifier`, the verdict `verifier_verify`, `guarded`, `complete`, `extractor`, `stateFunction`, `rbr`; outside it `publicInputPhase`, `publicInputComplete`, `publicInputSecurity` |
| `Spine/Instance.lean`, `Spine/Toy.lean` | the field `PublicLine.sent` (next section) |
| `ToArkLib/GuardedVerdict.lean` | `Verifier.GuardedForm.of_probEvent_pos`, `Reduction.mem_support_run_of_guarded` |
| `ToArkLib/KeepOracles.lean` | `keepOracles`, `OracleVerifier.materializeOutput_of_keepOracles` |
| `ToVCVio/UniformSample.lean` | `probEvent_uniformSample_le_of_card_le`, `probEvent_uniformSample_le_of_subsingleton` |
| `ToArkLib/PassThrough.lean`, `ToArkLib/SendOracle.lean` | now use the shared lemmas; no statement changes |
| `docs/reviews/public-input-phase.md` | the adversarial review, with its dispositions |
| `docs/roadmap/protocol-blueprint.md`, `docs/roadmap/protocol-status.md` | Layer 8 as built; the status snapshot on `main` at `f4d858c` |

Paths are under `LeanerVM/Protocol/` unless they start with `docs/`.

The three generic modules name no protocol. Each replaces a proof the components would otherwise copy:

- **A guarded verifier.** ArkLib calls a verifier guarded when it is a Boolean check on the statement and the transcript followed by a deterministic verdict. If such a verifier can output a statement satisfying a predicate, its check passes and its verdict satisfies the predicate. Every outcome of a run is a run of the prover with the verdict, or a rejection. A component's two proofs start from these two facts.
- **Kept oracles.** The output oracles of a verifier are its input oracles. Every phase keeps the stack, so every phase uses it.
- **Uniform samples.** A predicate with at most `k` witnesses holds of a uniform sample with probability at most `k/|α|`.

The line identity `eval₂Mle_linePoint` stays in the phase module, since the point `(r, 0, …, 0)` is the protocol's choice. It is derived from Layer 1's selection identity `evalMle_append_boolVec`.

The bundle `publicInputPhase` is `noncomputable` for its error alone, a real number. The prover, the verifier, `check` and `pooled` are computable, and the compiled verifier reads those.

## The change to the spine

`PublicLine` gains one field, `sent : Bool`: whether the proof carries the value claimed for the line.

§8.2 sends two scalars for the two low limbs and none for the top limb. So which public columns have a value in the proof is part of the proof's format. As a parameter of the phase it was bound by no statement and no test: the prover, the verifier and the compiled verifier could each be given a different value (review finding A2). Declared with the line, it is read from one place.

It fixes the transcript and not the relation. `M3Holds` does not mention it, and both theorems hold for every choice.

## The specification's check and the deployed check

The theorems are about the specification's verifier. The pinned verifiers read the same transcript, one challenge and two scalars, and check one equation on the two public words, `c_0 + Y·c_1 = interp(pi_0, pi_1, r)` over `E` (`cpu/mod.rs:752-755`, `verifier.py:1400`). The specification checks one equation per limb.

The equations per limb imply the equation on the words. The converse fails, also on the true evaluations of `K`-valued columns, because they are evaluations at a point of `E`. With zero public words and limbs `[0, 1]` and `[1, 0]`, at `r = y/(1 + y)` the equation on the words holds and both equations per limb fail. A test pins this.

So the pinned verifiers accept transcripts this verifier rejects. For a given wrong stack each check has at most one bad challenge, not the same one, so each gives `1/|E|`. For the equation on the words this is argued on paper and not proved here: it is a lemma the compiled verifier (Layer 12) owes. Status finding F18.

## The review

`docs/reviews/public-input-phase.md`: the `adversarial-review` skill, run by an agent with no knowledge of the branch. The expectation of the phase was written from the specification before any Lean was read, and the Rust was opened last.

- **No theorem is wrong or vacuous.** Each of five wrong verifiers breaks a stated theorem.
- **Met on this branch:** a false sentence in the roadmap, which claimed the two checks of the previous section equivalent (B1); an output that dropped a claim on a short message (A1); the unbound parameter `sent` (A2); three proofs resting on the normal form `simp` happened to leave (C1); ten unprefixed public names (C2); a docstring with no pin (C3); citations (B2, B3).
- **Audit surface:** 35 public declarations to 23 in the phase module.
- **One point for the maintainer.** The claims are pooled at the values the verifier computes from the statement. They are the values sent whenever the check passes, so the verdict is that of a verifier pooling the sent values, and the module has one definition of the output.

The fixes were made after the review and have not themselves been reviewed adversarially.

## Sources and revisions

leanVM [`a386121f`](https://github.com/leanEthereum/leanVM/commit/a386121f84292f6fa663aaa3e570c15bc0240ea2): specification §8.2 (`08-end-to-end-protocol.tex:27-33`, and `:80-85` for the protocol's step), Lemma 3.8 (Schwartz-Zippel, `03-proving-primitives.tex:51`); `crates/lean_vm/src/cpu/mod.rs:745-755` and `:611-613`, `python-verifier/verifier.py:1400`, read after the phase was written. ArkLib `dca90385`, CompPoly `3468b38c`, Lean `v4.33.1`; no pin moves.

Everything here is Category A: written from the specification, nothing transcribed from the implementation.

## Layer ownership

All new public definitions are in `Protocol`. The phase is written over an abstract `I : M3Instance` and imports no leanISA module. The generic modules import ArkLib, VCVio and Mathlib only.

## Validation

```sh
./scripts/validate.sh        # exit 0; axiom audit: 3298 declarations, unexpected axioms: []
lake build LeanerVMTests.Protocol.PublicInput LeanerVMTests.Protocol.Spine
```

`#print axioms` on `publicInputPhase`, `publicInputComplete`, `publicInputSecurity`, `PublicInput.complete`, `PublicInput.rbr`, `PublicInput.stateFunction`, `PublicInput.verifier_verify`, `PublicInput.eval₂Mle_linePoint` and the theorems of the three generic modules: `propext, Classical.choice, Quot.sound`.

Tests (`tests/LeanerVMTests/Protocol/PublicInput.lean`) and the wrong reading each one excludes:

| Test | Excludes |
| --- | --- |
| the point `linePoint` is `(y, 0)`; a table of two variables on it against the line through entries 0 and 1, and at `(y, 1)` against the line through entries 2 and 3 | a point in the other bit order |
| on the toy, the line's value accepted; a wrong value, no value and an extra value rejected | a check that ignores the message or its length |
| on a stack whose cell 1 differs from the statement's, the true evaluation rejected at two challenges and accepted at `r = 0`; the pooled claim false, and true at `r = 0` | a bound that is not attained; a check that accepts a wrong stack |
| a claim received from the earlier phases stays first in the pool | a pool in the wrong order |
| three lines in the shape of the memory limbs: two values sent, three claims pooled; a wrong top cell passes the check and fails the third claim, and the first two claims alone accept it | a pool without the claim on the top limb |
| an instance that sends nothing: the empty message accepted, the claim still pooled | a claim pooled only for a sent line |
| at `r = y/(1 + y)` the equation on the words holds and the check per limb rejects | the two checks being taken for one |
| the phase in its slot of `Phases`, among four pass-through phases, and the master completeness theorem instantiated | a phase that does not fit the seams |

## Deployed behavior or repair

Neither. The theorems describe the verifier of the specification. The deployed verifiers check a weaker equation on the same transcript (above), and no theorem here is about them.

## Linked issues and pull requests

Dashboard #12, hole P5. This is a draft.

Built on Layer 1 (#59), whose selection identity it consumes. It touches no declaration of the open #39, #42 and #43.

The three generic modules are candidates for ArkLib and VCVio; no upstream issue is open for them yet.

Feeds the knowledge-soundness half of T4 through the slot `pub` of `Phases`: `leanVmPiop` composes the commit phase, the bus phase, the table sumcheck, this phase, the Flock phase and the opening phase.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
