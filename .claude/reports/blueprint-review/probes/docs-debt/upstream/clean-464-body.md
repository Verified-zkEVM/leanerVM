Opt-in **directed channels** with an **explicit balance model**, beside the legacy signed-multiplicity channels, so that ensemble soundness can be proved over fields of characteristic 2. Every legacy declaration keeps its statement; three legacy declarations lose an instance argument their proofs never needed (see Compatibility).

**Motivation.** Over a binary field such as `GF(2^64)` (leanerVM [#16](https://github.com/Verified-zkEVM/leanerVM/issues/16)), `-1 = 1`, so the sign of a multiplicity cannot tell a provider from a receiver, and `1 + 1 = 0`, so two unmatched sends cancel. The legacy relation `BalancedInteractions` guards against wrap-around with `length < ringChar F`, which in characteristic 2 admits at most one interaction per channel (`length_le_one_of_balancedInteractions_of_ringChar_eq_two`), so the legacy VM theorem holds there only vacuously. A capacity bound (Clean #452) is related; the model interface carries side conditions of that kind but none is added here.

## Design

| | Legacy (unchanged) | Directed (new, opt-in) |
| --- | --- | --- |
| Channel | `Channel`; `emit m msg`, `push`, `pull`, `pushIf`, `pullIf` | `DirectedChannel F Message`; `emit dir enabled msg`, `push`, `pull`, `pushIf`, `pullIf` |
| Direction | sign of the multiplicity: `-1` receive, other nonzero provide | a tag stored as the last raw message element (`Direction.tag`: `0` provide, `1` receive); the raw channel has arity `size Message + 1` |
| Multiplicity | signed weight | boolean activation gate; one enabled interaction is one bus event |
| Local contract | `Requirements := mult ≠ -1 → mult ≠ 0 → G`, `Guarantees := mult = -1 → G` | an active provider owes `G` and the gate; an active receiver may assume `G` (`pullIf`) or decline it (`emit .receive`); a disabled event owes and assumes nothing; a malformed tag fails the raw requirements |
| Verifier relation | LogUp: field sum zero per message and `length < ringChar F` (`BalanceModel.logUp`) | multiset: the active provided payloads are a permutation of the active received payloads, tag removed, no characteristic condition (`BalanceModel.multiset`) |
| Ensemble statements | `Ensemble.Statement`, `FormalEnsemble`, `SoundEnsemble`, `VmTables` | `Ensemble.StatementWith model`, `FormalEnsembleWith`, `SoundEnsembleWith`, `DirectedVmTables`; the model is always explicit, there is no default |

`assumeGuarantees` keeps its meaning (permission to use the guarantee locally) and is independent of the direction. The tag survives construction, subcircuit composition, evaluation, collection and JSON export without a new field on any public record. A directed interaction therefore serializes exactly like a legacy interaction with one more message element, and the bytes do not say which relation applies; the export protocol below records that beside them.

## What is added

**`Clean/Circuit/DirectedChannel.lean`.** `Direction` and `Direction.tag`; `DirectedChannel` and its erasure `toRaw` (`toRaw_inj`, `toRaw_ext_iff`); `DirectedInteraction` with `pushed`/`pushedIf`/`pulled`/`pulledIf` and `expose` for exposed channels; the operations with their `ExplicitCircuits` instances; and the local contract: `emittedValue_guarantees_iff`, `emittedValue_requirements_iff`, one lemma per operation (`pushedIf_requirements_iff`, `pushedIf_guarantees`, `pulledIf_guarantees_iff`, `pulledIf_requirements_iff`, `emitted_receive_guarantees`, `emitted_receive_requirements_iff`) and the two `enabled = 0` lemmas.

**`Clean/Air/Balance.lean`.** A field-free kernel shared by both readings: `Event` (payload, direction, activity), `PullsSupported`, `activeCount`, `CountBalanced`, `activePayloads`, with `pullsSupported_of_countBalanced`, `count_eq_of_countBalanced`, `countBalanced_of_perm_activePayloads` / `perm_activePayloads_of_countBalanced`, and the reversal argument `guarantees_of_requirements_of_count_eq`, all parametrized by a reading `view : α → Event F`. The legacy reading `Interaction.legacyEvent` takes the direction from the sign, with `pullsSupported_legacyEvent_of_balancedInteractions`, `countBalanced_legacyEvent_of_balancedInteractions` and `count_eq_of_balancedInteractions`. The legacy VM theorem `guarantees_of_requirements_of_requirements_of_guarantees` (and its `_of_mult_zero_iff` variant) becomes a wrapper over the kernel.

**`Clean/Air/BalanceModel.lean`.** `BalanceModel` packages the relation a verifier establishes on one channel, its side conditions, a `view` and the derivations of `PullsSupported` and `CountBalanced`. `BalanceModel.logUp` is `BalancedInteractions` (`logUp_balanced_iff`); `Interaction.directedEvent` is the directed reading and `BalanceModel.multiset` the permutation relation (`multiset_balanced_iff`, `multiset_unitEvent_iff`). `DirectedChannel.guarantees_of_requirements_of_requirements_of_guarantees` is the VM argument over any field. A model only fits the encoding it reads, so `RawChannel.ConsistentWith model` is the per-channel soundness obligation under a model (every `DirectedChannel` is consistent with `multiset`, every `Consistent` raw channel with `logUp`), and `BalanceModel.Reads model Ch` ties `logUp` to `Channel` and `multiset` to `DirectedChannel`. `EnsembleWitness.BalancedChannelsWith`, `Ensemble.StatementWith` / `SoundnessWith` / `CompletenessWith`, `FormalEnsembleWith` and `FormalEnsemble.withLogUp` are the model-aware statements; the `…_iff_…_logUp` lemmas show that the legacy notions are their LogUp instances.

**`Clean/Air/OrderedChannelWith.lean`.** The ordered-channel construction with the model as a parameter: `PartialBalancedChannelWith`, `SoundChannelsWith`, `TableSoundnessWith`, and `SoundEnsembleWith F model PublicIO` with `empty`, `addTable`, `addChannel` / `addFinishedChannel` (typed channels through `Reads`, so a channel of the wrong kind is a type error at the line that adds it), `addRawChannel` / `addFinishedRawChannel` (raw channels with a `ConsistentWith` instance), `markFinished`, `toFormal`, `toSoundEnsemble` and `SoundEnsemble.withLogUp`. The induction proofs duplicate those of `OrderedChannel.lean`; turning them into wrappers needs that file's definitions split from its theorems and is left for later.

**`Clean/Air/VmWith.lean`.** `DirectedVmTables` (every table receives and provides on the state channel under one gate its constraints make boolean; the verifier receives the final state and provides the initial one), `Ensemble.SoundVmChannelWith`, `SoundVmEnsembleWith` with `toFormal`, `verifier_guarantees_of_requirements_of_requirements_of_guarantees`, `addDirectedVm_soundVmChannelWith_of_soundChannelsWith` and the builder `SoundEnsembleWith.addVm`, the counterpart of `SoundEnsemble.addVm`.

**`Clean/Air/BusProtocol.lean`.** The bus export protocol, version 1: `ChannelLayout` (`signed` or `directed`), `ChannelSchema` (name, raw arity, layout; from `Channel.schema` and `DirectedChannel.schema`), `BusProtocol` (protocol name `clean-bus`, version `1`, the layout of the ensemble's balance model and its channel schemas; `WellFormed` is decidable), `BalanceModel.Protocol`, `BusProtocol.ofModel`, `ToJson` instances, and one theorem per clause of the directed layout (tag position, tag removal, gate, malformed tags) proved as a fact about the encoding, so that a backend implementing the schema enforces the relation the proofs assume.

**`Clean/Air/README.md`.** A section on the two channel contracts (operation tables for each kind), the backend relations, ensemble soundness per kind, the worked example and the export protocol.

**`Clean/Examples/FibonacciWithDirectedChannels.lean`.** The Fibonacci VM of `FibonacciWithChannels.lean` rebuilt on a directed state channel: `FibChannel` carries the guarantee `(x, y) = (fib n, fib (n + 1))` for some `n : ℕ` read into the field, `AddChannel` is an addition lookup channel with a one-row provider, `fibStep` is the gated step, `fibVerifier N` provides `(0, 0, 1)` and receives the state at index `N`, and `fibEnsemble N` is the ensemble under the multiset model. Theorems: `fibEnsemble_soundness` (over any field, the output is `(fib k, fib (k + 1))` for some `k` with `(k : F) = N`, so `N` fixes the index modulo the characteristic), `fibEnsemble_rejects_zero` (the output `(0, 0)` is rejected over every field and every `N`, since consecutive Fibonacci numbers are coprime), `fibEnsemble_one_step_over_F2` (`N = 1`, output `(1, 1)`, four interactions on the state channel and two on the addition channel), `fibEnsemble_three_steps_over_F2` (the same `N = 1` accepts the run `0 → 1 → 0 → 1` with output `(0, 1)`), and `legacy_rejects_every_run` (the legacy relation admits no witness of this ensemble over `F 2`, whatever `N`, because its verifier alone puts two interactions on the state channel).

**Tests** (`Clean/Air/Test/BusBalance.lean`, `Clean/Air/Test/BusBalanceEnsemble.lean`, registered in `Clean/Test.lean`): 39 theorems, 46 typechecking examples and 15 `#guard`s. They cover the legacy channel over `F 2` (`legacy_length_le_one_over_F2` and what it implies for a legacy prototype), the directed tag and local contract, counterexamples showing that each kernel hypothesis is needed, matching and mismatched model/channel pairings (both mismatches are wrong, and the typed builders reject them at the line that adds the channel), the directed reading of malformed tags and inactive events, the JSON pins (a directed interaction's JSON is that of a legacy interaction with one more element), a directed circuit carried through subcircuit composition to collected interactions, an ordered ensemble on a directed channel with an `F 2` witness, a directed VM built through `addVm` and `toFormal`, counterexamples for the hypotheses of the directed VM theorem, and the export-protocol pins.

## Compatibility

- Legacy public statements are unchanged: `Channel`, `Channel.toRaw`, `emit` / `push` / `pull` / `pushIf` / `pullIf`, `ChannelInteraction.Guarantees` / `Requirements`, `BalancedInteractions`, `exists_push_of_pull`, `one_ne_neg_one`, `RawChannel.Normal` / `Consistent`, `Statement`, `FormalEnsemble`, `SoundEnsemble` and its builders, `VmTables`, and the JSON of existing interactions; the tests pin the signatures and the JSON.
- The one change to legacy declarations: the instance argument `[Fact (ringChar F ≠ 2)]` is dropped from `guarantees_of_requirements_of_requirements_of_guarantees` and its `_of_mult_zero_iff` variant (`Balance.lean`), and from `verifier_guarantees_of_requirements_of_requirements_of_guarantees`, `addVm_soundVmChannel_of_soundChannels`, `SoundEnsemble.addVm` and its four projection lemmas (`Vm.lean`). In characteristic 2 the LogUp guard leaves at most one interaction on the channel, so the statements hold there without the hypothesis. Callers that obtain the instance by resolution are unaffected; a caller that passed it explicitly would drop it.
- `Ensemble.addTable_channels`, an `rfl` lemma, is added to `circuit_norm` in `FlatEnsemble.lean`.
- `FibonacciWithChannels.lean`, `OrderedChannel.lean` and `Vm.lean` build as before. sp1-lean has not been built against this branch.

## Out of scope

- Adoption of the directed path in leanerVM: a separate pull request in that repository.
- A capacity bound (#452) as a model side condition.
- Deriving the `OrderedChannelWith` induction from `OrderedChannel.lean` instead of duplicating it.

## Checks

On the head commit: `lake build --wfail` (1866 jobs) and `lake build CleanTests` (1765 jobs) green; no `sorry`, `axiom` or `native_decide` in the diff; the theorems of the example depend only on `propext`, `Classical.choice` and `Quot.sound`; `scripts/check-consecutive-empty-lines.py` clean on the changed files.

## Reviewing

Suggested reading order: the module docstring and `DirectedChannel.toRaw` in `Clean/Circuit/DirectedChannel.lean`, then `emittedValue_guarantees_iff` / `emittedValue_requirements_iff`; the kernel definitions and `guarantees_of_requirements_of_count_eq` in `Clean/Air/Balance.lean`; `BalanceModel`, `BalanceModel.multiset`, `RawChannel.ConsistentWith` and the directed VM theorem in `Clean/Air/BalanceModel.lean`; the `SoundEnsembleWith` builders in `Clean/Air/OrderedChannelWith.lean`; `DirectedVmTables` and `SoundEnsembleWith.addVm` in `Clean/Air/VmWith.lean`; `Clean/Air/BusProtocol.lean`; the example; the tests.

The 20 commits are review units, in this order:

| Commits | Content |
| --- | --- |
| `dbc16bf4`, `3f0996bd` | `DirectedChannel`, the kernel definitions, the `BalanceModel` record and the model-aware statements, the first tests; then malformed tags rejected, the JSON pin, a nested-subcircuit fixture |
| `7b4d4a2a`, `a70a6f9a`, `83f28efb`, `0f00cf91`, `bc0de6d8`, `ecba22d1` | the kernel theorems and legacy bridges, `logUp` / `multiset` / `directedEvent`, the reading tests, `RawChannel.ConsistentWith`, the dropped `[Fact (ringChar F ≠ 2)]`, `BalanceModel.Reads` |
| `ee0b84ac` | the directed local-contract lemmas |
| `c2fd237c`, `016bdcd9`, `711efa8b`, `dee89263`, `1f81d475` | the count adapter, `OrderedChannelWith`, `VmWith`, the ensemble tests, a review follow-up |
| `20e77970`, `8da2375f` | the export protocol, the README section |
| `7875acf9`, `0a41e630`, `286ebf17` | a counter VM example over a binary field and its follow-up, then the Fibonacci example that replaces it (its diagonal state made the fixed-step result trivially field-independent) |
| `a1938ad5` | comment-only: module docs and docstrings shortened to the library's style |

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
