# Dossier `gt-opening-compile`: the opening phase and the compilation (WHIR, Merkle trees, Fiat–Shamir, the proof object, the executable verifier)

Task `gt-opening-compile` of the blueprint review. Written 2026-09-29/30. Ground truth is leanVM
at `a386121f` (specification tex `doc/leanvm/body/`, Rust `crates/`, Python
`python-verifier/verifier.py`); the object of review is leanerVM `main` at `b435631` (the
blueprint `docs/roadmap/protocol-blueprint.md` and the Lean under `LeanerVM/Protocol/`, both
cited at that revision; the blueprint's line numbers are those of `b435631`, which the current
checkout `144c5aa` shifts by +4 after its line 168). ArkLib is cited at the old pin `dca90385`
unless a revision is named; `7653a901` is the new pin (the commit read as `origin/main` on
2026-09-29). Abbreviations for citations: `08` = `08-end-to-end-protocol.tex`, `03` =
`03-proving-primitives.tex`, `04` = `04-committing-the-witness.tex`, `B` =
`b-polynomial-commitment-scheme.tex`, `A` = `a-ring-switching.tex`; `whir.rs`, `whir_config.rs`,
`stack_open.rs`, `merkle.rs` (pcs) are under `crates/pcs/src/`; `fs/lib.rs`, `fs/transcript.rs`,
`fs/merkle.rs` under `crates/fiat_shamir/src/`; `mod.rs` is `crates/lean_vm/src/cpu/mod.rs`,
`pcs.rs` is `crates/lean_vm/src/pcs.rs`; `py` is the Python verifier; `bp` the blueprint.

Sibling dossiers cited rather than re-derived: `gt-flock-ring` (ring switching: serves the bit
witness only, no message, no check, six challenges, first power of `λ`), `gt-table-pub` (the
claim pool: 5 bus, 104 table, 3 public-input point claims, 113 powers of `λ`; Theorem B.7
`thm:rbr` is the specification's only round-by-round theorem), `gt-bus` (the setup checks
B1–B17, the admissibility finding G4, the canonical-encoding finding G9), `lib-arklib` (ArkLib
states no Fiat–Shamir or BCS security theorem at either pin; its G.4, G.2), `literature` (the
Fiat–Shamir error formula, A.3; the Johnson regime, C.2–C.3; list decoding and extraction, G.2).

## 0. Summary

**What was examined.** The deployed opening (§8.5 "Opening", `stack_open.rs`, `pcs.rs`,
`verifier.py:1356-1362`) and the deployed WHIR (Annex B; `whir.rs`, `whir_config.rs`,
`whir_induce.rs`; `verifier.py:900-1087`), the Merkle trees (`pcs/merkle.rs`, `fs/merkle.rs`),
the Fiat–Shamir chain and proof object (`fs/lib.rs`, `fs/transcript.rs`, `mod.rs:82-178,
711-779`), BLAKE2s (`primitives/src/hash.rs`); the blueprint's headline, conventions, ledger,
Layer 0 and Layers 10–13, acceptance tests, interfaces and boundaries; the Lean at `b435631`
(`Field.lean`, `Spine/Seams.lean`, `Spine/Compose.lean`, `ClaimWeights.lean`); ArkLib's
`OracleInterface`, `FiatShamir/Basic.lean`, `BCS/Basic.lean`, `Commitments/Functional/Basic.lean`,
`Security/Implications.lean`, `CapacityBounds.lean` at both pins, and pull requests #848 and
#469 (#627 is an issue, not a pull request). Two Lean probes ran on 2026-09-29 against the old
pin (section H); a scratch port of the Rust parameter derivation reproduces the Python query
table (section F).

**Conclusions.**

1. **There is no sumcheck between `λ` and WHIR.** After the one batching challenge `λ`, the
   prover's next message is the first round polynomial of WHIR's own sumcheck on
   `Σ_x q(x)·W_λ(x) = C_λ` (`stack_open.rs:452-461` → `whir.rs:1324-1326`; `py:1362, 1012`).
   The `μ` sumcheck rounds that reduce the weighted claim are WHIR's, interleaved with its level
   commitments, out-of-domain samples, grinding, queries and per-level batchings; the running
   claim changes at every level and the protocol ends on one equation, never on an evaluation of
   `q̃` at a point. The blueprint's Layer 10 (a `μ`-round sumcheck on `W_λ·q` and a final
   evaluation query) followed by Layer 11's "WHIR in place of the evaluation oracle" describes a
   protocol with `2μ` sumcheck rounds and an evaluation message that leanVM does not send.
   **Recommendation (ii)**: give the stack the inner-product oracle interface (a query is a
   `Weight μ`, the answer `Σ_w W(w)·q(w)`), the idealization of Definition 3.13; the opening phase
   is then "`λ`, then one weighted query", with the specification's transcript, and WHIR realizes
   that one query. It typechecks against ArkLib at the pin (probe `InnerProductOracle.lean`);
   no built phase queries the oracle, so nothing built breaks. Section A.
2. **The three non-interactive theorems are not well formed as sketched** (section E).
   `baseVerifier_extractsExecution` takes a probability over nothing (its hypothesis is a
   deterministic equation), concludes an existential (soundness, not knowledge), and quantifies
   over no adversary and no query budget; `verify_iff_compiled` applies ArkLib's
   `Verifier.fiatShamir` to an oracle verifier whose messages are the stack and the codewords
   in the clear (no `decode : Proof → messages` exists), omits the Merkle compilation, the
   grinding checks and the prover-chosen sizes; `verify_knowledgeSound`'s three interfaces
   cannot be inhabited by any theorem of ArkLib at either pin, and even if they were, four
   steps would still be missing: the list-binding compilation (the ideal oracle is one `q`,
   the commitment binds to a list), round-by-round ⇒ state-restoration, the hash-chain
   instantiation of the ideal challenge oracle, and grinding. Perfect completeness does **not**
   survive the transform: the honest prover's grinding search is a search, and the Lean
   `prove` must be partial or fuelled.
3. **The numbers** (section F). At the caps with the stacking window the blueprint's own
   phase errors sum to about `2^{-160}` (ring switching dominates; the `(α, β)` term is
   `≤ 2^{-162}`), so `piopError_le` holds with the window and is false at the per-log caps
   (agreeing with `gt-bus` D.4/G4). The deployed parameter set claims **128 bits round by
   round in the Johnson list-decoding regime, provable given [BCHKS25] Theorem 4.6**, of which
   17 bits at every query round come from grinding (queries close `111` bits); the Johnson list
   bound at level 0 is `L_0 ≤ 110` to `396` over the supported sizes and up to `2^20` at the
   deepest levels; the per-fold mutual-correlated-agreement term sits at `128.2` bits at
   `μ = 28, ρ = 1/2`. The blueprint's `niError` ("the round-by-round maximum times the query
   bound plus the grinding-adjusted WHIR terms") has no term for the list factor `L_0` on
   every oracle-protocol challenge, none for the hash, none for the prover's choice of sizes,
   and states the grinding adjustment without a model; `Σ piopError < 2^{-150}` says nothing
   about the deployed security level, which the query rounds set.
4. **The hidden assumption of the oracle model** (section G): the ideal oracle is one
   `K`-valued table; the deployed commitment is a Merkle root of a `K`-valued interleaved word
   that need not be a codeword and is close to up to `L_0` codewords of a code over `E`. Every
   codeword within radius `γ < 1 − ρ` of a `K`-valued word is `K`-valued (a two-line argument
   from the agreement bound; not in the specification), so the list consists of `K`-valued
   multilinears of the right size and the relation `M3Holds` applies to each; what the
   compilation must then prove is that some member of the list satisfies every pooled claim
   and that the oracle protocol's errors, multiplied by `L_0`, are what a cheating prover pays.
5. **WHIR, Merkle and Fiat–Shamir as deployed** (sections B, C, D): the level schedule
   differs from Protocol B.1 in four ways the blueprint does not record (per-claim "intro"
   round polynomials sent before the level's `λ_i`, grinding, the level-0 lane relayout
   `f(u, x) = q(x, u)`, the last round message omitted); the code is Reed–Solomon over `E`
   with a domain in `K` in the novel basis on `x^c`, with the level-0 word `K`-valued; the
   query counts of the Python table are exactly the Rust's floating-point search (reproduced);
   the Merkle tree hashes leaves and nodes with the same BLAKE2s-256 and no domain separation;
   the chain seeds, absorbs, squeezes and grinds as the blueprint's *Fiat–Shamir* row says;
   the Python verifier reads the raw (unpruned) proof the Rust verifier emits and, run
   standalone, accepts level-0 leaves whose absent lanes are nonzero (soundness-neutral).
   The checks are enumerated in section D with their sources and the cheating proof each
   prevents.

**Findings by severity** (section I): critical: none that makes a stated leanerVM theorem
wrong today, since none of Layers 10–13 is built; **major**: the opening phase's transcript
(A); `verify_iff_compiled` not statable as sketched (E.4); `baseVerifier_extractsExecution`
and `verify_knowledgeSound` not well formed (E.1, E.2); the list-binding compilation is a
missing theorem, not a consequence of the three interfaces (E.3, G); perfect completeness does
not survive grinding (E.5); `niError` incomplete (F); the blueprint's `whirOpen` batches a
second time and its `encode` is `K`-only (B); **minor**: `encode_column_weight` is an
existence statement every linear map satisfies (B); the proof object's Merkle format is
unspecified between the pruned wire form and the raw form (C); the level-0 relayout, the
"intro" messages, the omitted last round message and the two per-level checks are not in the
blueprint (B); the status's finding F9 is false at the pin (D, agreeing with `gt-bus` G5 and
`gt-flock-ring` 8.10); `ladder`'s `Level` lacks the analysis parameter `η` (B); `#627` is an
issue, not a pull request (E.2); **notes**: the upper per-log caps are implied by the stacking
window (D); the Rust's own security accounting includes the list factor only for the ring
switching degree (F).

---

## A. The opening, as deployed

### A.1 From a pooled claim to a weighted claim on the stack

A pooled claim is `P̃_i(ζ) = c` on one column; through the stacking selectors it is
`Σ_w W(w)·q̃(w) = c` with `W(w) = eq((ζ, sel_i), w)` (`04:14-18`; `08:97`: "Each pooled claim is
one evaluation of a column at a point, its value already supplied; via the stacking selectors
(§4.1) it becomes a weighted sum `Σ_w W_j(w) q̃(w) = c_j` over the stacked witness. (The
ring-switched claim arrives already in this form, its weight supported on the `q_flock`
region.)").

| Step | Specification | Rust | Python |
| --- | --- | --- | --- |
| A column claim becomes a slot claim | `08:97`; `04:14-18` | `mod.rs:790-814` `slot_claims`: `SlotClaim::Point { offset, low_point, value }` for a committed column, `SlotClaim::Strided { offset, slot, stride_log, point, value }` for a BLAKE2S value limb ("virtual", routed to `q_flock`) | `py:520-522` `ColumnClaim.on_stack`: `point = layout.placements[column].stack_point(self.point, layout.stack_log)`; `Placement.stack_point` (`py:295-297`) inserts the selector bits around the point, the low bits for a strided limb |
| The weight of a point claim | `04:18` `W(w) = eq((ζ, sel_i), w)` | `stack_open.rs:294-303` `stack_claim_eq_at`: `eq(low_point, x[..n]) · ∏_k (sel_k ? x_k : 1 + x_k)` with `sel = offset >> n`; `stack_open.rs:305-323` the strided form `eq(slot bits, x[..stride]) · eq(point, x[stride..block]) · eq(sel, x[block..])` | `py:522` `lambda x: eq_eval(point, x)` on the full stack point |
| The ring-switched claim's weight | `08:91`, `A:46` `W(u) = Φ(eq(r, u))` on `q_flock`, lifted by its selector | `stack_open.rs:45-48` `b(x) = eq(sel, x_hi) · Σ_i λ^i·MLE(rs_eq_ind_i)(x_lo) + Σ_j λ^(n_rs+j)·eq(claim_j, x)`; verifier `stack_open.rs:530-546` | `py:1411-1412` `ringswitch = (lambda x: qflock.eq_above(x) * ringswitch_weight(x[: qflock.variables]), ringswitch_target)` |

The verifier never materializes a weight: it evaluates the batched weight's extension once, at
WHIR's terminal point (`stack_open.rs:529-548` "Evaluate the lifted weight once, at the terminal
sumcheck point"; `py:1362`, `py:1079`). That is what "MLE-friendly" (`03:113`) buys.

### A.2 The batching challenge `λ` and the assignment of its powers

| Step | Specification | Rust | Python |
| --- | --- | --- | --- |
| When `λ` is drawn | `08:98` "drawn after every claim value is bound" | `stack_open.rs:397-400`: after the six ring-switching map challenges (`stack_open.rs:394`), `let lambdas = powers(ps.sample(), ring.claims.len() + point_claims.len());` with the comment "Nothing is observed first: every claim value reached the caller through a binding stream read"; verifier `stack_open.rs:518` | `py:1361` `scales = powers(transcript.sample(), len(claims))`, after `ring_switch` drew its six (`py:1343`) |
| Which claim takes which power | `08:98` "Claim `j` takes the weight `λ^{j−1}`, the ring-switched claim first and the pooled column claims after" | `stack_open.rs:401` `let (lambdas_rs, lambdas_pd) = lambdas.split_at(ring.claims.len());` — the ring-switched claims take `λ^0, …`, the point claims the rest in `finish_claims` order (`mod.rs:656-667`: bus, table, public input) | `py:1413` `[ringswitch, *(c.on_stack(layout) for c in claims)]` with `claims = [*bus.claims, *table_sumcheck_claims, *public]` (`py:1395, 1402`) |
| Number of claims | `J` (`08:98`) | `1 + 112 = 113` (one ring-switched claim, `mod.rs:767`; the pool per `gt-table-pub` A.3) | same |
| The batched target | `08:99` `C_λ = Σ_j λ^{j−1} c_j` | `stack_open.rs:521-527` (verifier), `:413-415, 257, 285` (prover) | `py:1362` `dot(scales, values)` |
| The batched weight | `08:99` `W_λ = Σ_j λ^{j−1} W_j`, "the verifier evaluating `W_λ` itself" | `stack_open.rs:531-546` `eval_b_at` | `py:1362` `lambda point: dot(scales, [weight(point) for weight in weights])` |

The three sources agree on every row (the sibling dossier `gt-flock-ring` §6 gives the ring
switching; `gt-table-pub` A.3 the pool). `powers` starts at `λ^0` in both implementations
(`whir_induce.rs:99-107`; `py:186-188`), matching `λ^{j−1}` for `j = 1`.

### A.3 What runs after `λ`: the question settled

**Specification.** `08:99`: "Fold the `J` claims into `W_λ = Σ_j λ^{j−1} W_j` and
`C_λ = Σ_j λ^{j−1} c_j`, and run the inner-product PCS opening on `Σ_w W_λ(w) q̃(w) = C_λ`
(Annex B), the verifier evaluating `W_λ` itself. This one opening discharges every pooled claim;
there is no separate reduction sumcheck." Annex B's `Open` takes `J_0 ≥ 1` weighted claims and
its level-0 step 1 is "(batch) V sends `λ ← E`; the batched claim is
`(W, σ_0) := (Σ_t λ^{t−1} W_t, Σ_t λ^{t−1} c_t)`" (`B:108-110`): §8.5's `λ` **is** Protocol
B.1's level-0 batching challenge, with `J_0 = J`. Its step 2 is the level's sumcheck,
`ℓ_0` rounds (`B:111`).

**Rust.** `stack_open.rs:452-461` hands `(stack, b_stack, target)` to
`recursive_prover_with_basis` ("One WHIR over the full stack against the combined claim"). Its
first act (`whir.rs:1324-1326`):

```rust
    let (mut sc_prover, start_msg) =
        sumcheck_span.in_scope(|| SumcheckProver::new(witness, b_initial, target, lane_block));
    send_msg(ps, start_msg, target);
```

`send_msg` transmits a round polynomial (`whir.rs:509-511`). Then, `whir.rs:1328-1334`, six
times: sample `r_j`, fold, send the next round polynomial. Only after that is the first
recursive root sent (`whir.rs:1358` `ps.add_root(&wtns_1.root());`). The verifier mirrors it:
`whir.rs:2087-2090` `let mut t_r = target; let Some(mut running_quad) = recv_quad(vs, t_r)`,
`:2100` `replay_fold_rounds(vs, initial_k, …)`, `:2104` `vs.next_root()`.

**Python.** `py:1362` calls `verify_whir(transcript, stack_log, log_inv_rate, dot(scales, values),
root, …)`, whose first read is `py:1012` `running_quad = transcript.sumcheck_round_poly(3,
target)`, then `py:1017-1024` the fold rounds, then `py:1034` the next root.

**So:** in the deployed protocol there is **no sumcheck between `λ` and WHIR**; the first
message after `λ` is WHIR's first round polynomial. The sumcheck rounds that reduce the
weighted claim are **WHIR's own**: `μ = 6 + Σ_i k_i + n_res` rounds in all (`whir_config.rs:748-751`
"initial_k + Σ k (L1+) + yr_log_n = log_n"), interleaved with the level roots, the
out-of-domain samples, the grinding nonces, the query positions and the per-level batching
challenges. The running claim is not `Σ W_λ·q` throughout: at every level the out-of-domain
claim and the query-consistency claim are glued into it with powers of that level's `λ_i`
(`whir.rs:1131-1154` `glue_pending`, verifier `:1681-1701` `batch_level_claims`; `py:1058-1063`),
and the protocol closes on one equation `weight · f̃_final(ρ_tail) = t_r` (`whir.rs:2308`;
`py:1082-1083`), where `weight` is `W̃_λ` at the rotated terminal point plus every glued weight
(`whir.rs:2264-2307`). There is never an evaluation of `q̃` at a point; `q` is folded, and
the folds are committed.

### A.4 What the blueprint specifies instead

- Layer 10 (`bp:1112-1114`): `openingPhase (μ) (J) … (pSpec := V_to_P : E ; sumcheck (W_λ · q)
  rounds ; the final evaluation query)`, error "`(J − 1)/|E|` on `λ`, `2/|E|` per round". The
  section is titled "the claim pool, the opening sumcheck, and the oracle protocol" (`bp:1101`),
  and the scope says "the claim pool and the opening sumcheck, as ArkLib reductions"
  (`bp:127`).
- Layer 11 (`bp:1173`): `whirOpen (params) : OracleReduction … (StmtIn := Fin J → WeightedClaim
  μ) …`, "stated exactly as Protocol B.1: batch, `ℓ_i` sumcheck rounds, commit, …" (`bp:1185`).
- Layer 12 (`bp:1214-1215`): "The compiled oracle protocol: WHIR in place of the evaluation
  oracle. `def leanVmIopp … (OStmtIn := codeword oracles)`".
- Convention *The oracle* (`bp:317`): "`OracleInterface` query `Vector E μ_stack` and answer
  `eval₂Mle q`"; Layer 0 (`bp:637-642`) and the built instance
  (`LeanerVM/Protocol/Field.lean:102-106` at `b435631`, quoted in H.1).

Read together, the compiled verifier of the blueprint runs `λ`, a `μ`-round sumcheck on
`W_λ·q` (two coefficients a round), receives a value `v = q̃(ρ)`, checks
`W̃_λ(ρ)·v` against the running claim, then runs `whirOpen` on the one claim `(eq(ρ, ·), v)`
— which, "stated exactly as Protocol B.1", starts with its own level-0 batching challenge
(`J_0 = 1`) and its own `μ`-round sumcheck. That transcript has one extra challenge, `μ` extra
round polynomials and one extra scalar, and is not leanVM's: a `verify` that is "the Fiat–Shamir
compilation of that oracle verifier" (`bp:27-29`) cannot accept a Rust proof, and
`verify_iff_compiled` (`bp:1218-1221`) is false for every proof the pinned prover emits.

This is the divergence the brief names (§7). It is **an error of the blueprint**, introduced
by the choice of the evaluation interface at Layer 0: with an evaluation oracle, the only way
to discharge a weighted claim in the ideal model is to reduce it to an evaluation, and the
extra sumcheck follows.

### A.5 The alternatives

**(i) Keep the evaluation oracle and the extra sumcheck; owe a theorem relating the two
protocols.** The ideal-model theorems stay as they are, but `verify` can no longer be the
Fiat–Shamir compilation of the oracle verifier (A.4). The theorem owed would be: "the
compiled protocol *with* the extra sumcheck and WHIR on an evaluation claim is secure ⇒ the
deployed protocol is secure". No such implication exists between two protocols with different
transcripts; each must be proved on its own, so the security of `verify` would rest on a WHIR
theorem for weighted claims anyway (Theorem B.7 is stated for `J_0` weighted claims), and the
opening sumcheck of Layer 10 would be proved and never used. Rejected.

**(ii) The inner-product oracle interface.** A query is a weight `W : Weight μ`, the answer is
`Σ_w W(w)·q(w)`: the idealization of Definition 3.13 (`03:112-118`: "An *inner-product
commitment scheme* commits to `g` and later proves any such claim … An evaluation claim
`g̃(r) = c` is the case `W = eq(r, ·)`"). The opening phase is then "`λ`, then one weighted query
at `W_λ` compared with `C_λ`", a one-challenge component with error `(J − 1)/|E|` and no
sumcheck; WHIR realizes the one query. Checked at the pins (probe `InnerProductOracle.lean`,
section H.1, exit 0 on 2026-09-29 against ArkLib `dca90385`):

- ArkLib's `OracleInterface` is a class with a query type and an answer function
  (`OracleInterface.lean:55-57` at `dca90385`: `class OracleInterface (Message : Type u) where
  Query : Type v; toOC : OracleContext Query (ReaderM Message)`); `Weight μ` is a structure in
  `Type` (`Spine/Seams.lean:103-109` at `b435631`), so `Query := Weight n` is accepted and the
  answer is `W.pair q` (`Seams.lean:112-113`).
- The evaluation query is the special case `eqWeight p`, by the built lemma `eqWeight_pair`
  (`ClaimWeights.lean:51-54` at `b435631`): the current `evalOracle_answer` becomes a corollary.
- ArkLib's functional commitment scheme over this interface has for opening statement
  `(commitment, weight, value)` (`Commitments/Functional/Basic.lean:62-64` at `dca90385`, copied
  in the probe): it is an inner-product commitment scheme, which is what Layer 11 must
  instantiate ("`Commitment.Scheme` … The commitment interface WHIR's commit and open
  instantiate", `bp:249`).
- The opening verifier "read `λ`, query at `W_λ`, compare with `C_λ`" is an `OracleVerifier`
  over `ProtocolSpec 1` with `keepOracles` (probe, `openVerifier`).

Consequences, layer by layer:

| Where | Change |
| --- | --- |
| Layer 0 (`Field.lean`) | replace `evalOracle` by the inner-product instance; `Weight` (and `Weight.pair`) move below `Field.lean` (today they are in `Spine/Seams.lean`, above it); `evalOracle_answer` becomes `answer q (eqWeight p) = eval₂Mle …`. The only consumers of `OracleInterface.answer` on a `Column` at `b435631` are three theorems on verifier-computed columns (`FixedColumns.lean:59-61, 97-99, 113-115`) and the tests (`tests/LeanerVMTests/Protocol/Field.lean:30-44`); the former are restated with `eval₂Mle`, since the index and bytecode columns are never oracles. Convention *The oracle* (`bp:317`) and Layer 0 (`bp:637-642`) change accordingly |
| The spine | nothing in the types: `TheOracle I`, `Seam.flock`, `Seam.done`, `Phases.opening : Phase.Def I (I.Stmt × FlockOut I) Unit` stay. No built phase queries the oracle (the public-input verifier queries only its own message, `PublicInput.lean:222-231` at `b435631`), so no built proof changes |
| Layer 10 | the opening phase is the batching component alone (hole G3, `bp:600`): schedule `V_to_P : E`, verifier = batch, query, compare; error `(J − 1)/|E|`; knowledge state function "some pooled claim is false of `q`" before `λ`, "the batched claim is false of `q`" after, with the query making the verdict; completeness by linearity of `Weight.pair`. `2/|E|` per round leaves Layer 10 (those rounds are WHIR's and carry `2L_i/|E| + 2^{ℓ_i − j}ε_i`, Theorem B.7). The title and `bp:127` lose "the opening sumcheck" |
| Layer 11 | `whirOpen` takes the `J` weighted claims and **its level-0 batching challenge is the opening phase's `λ`**: the compilation replaces the whole opening phase by `whirOpen`, not the query alone. `encode` must be over `E` as well as `K` (section B) |
| Layer 12 | `leanVmIopp = commit' ⟫ bus ⟫ table ⟫ pub ⟫ flock ⟫ whirOpen`, where `commit'` sends the level-0 codeword (an interleaved `K`-valued word with position queries) and the front `bus … flock` is the spine's; then the Merkle compilation, then Fiat–Shamir with grinding (section E) |
| Layer 13 | unchanged in shape; its hypotheses change with section E |

**(iii) End the oracle protocol at the pool.** Drop the opening phase from the oracle protocol:
the composed reduction ends with output statement `I.Stmt × FlockOut I` and output relation
`Seam.flock`, and the compilation appends `whirOpen` there. Same transcript as (ii), same
compile theorem; it changes the master theorems' shape (`Seam.done` becomes `Seam.flock`,
five phases instead of six) and leaves the stack's oracle interface unused, which misleads
(an interface that is never queried says nothing). Acceptable; (ii) is preferred because it
keeps the spine's statements and makes the ideal object the specification names.

**Recommendation: (ii).** It is the specification's own object (`03:112-118`, `B:4` "we commit
to a `K`-valued multilinear, and opening claims are in `E`"), it matches ArkLib's
`Commitment.Scheme` without adaptation, it makes `verify_iff_compiled` statable with leanVM's
transcript, and it removes a `μ`-round sumcheck from the trusted surface of Layer 10.

### A.6 Negative results

Checked and agreeing across the three sources: the moment of `λ` (after the six ring-switching
challenges, before any WHIR message); the power of each claim; `J = 113`; the batched target
and weight; that the verifier evaluates `W̃_λ` exactly once. Checked: the spine's
`WeightedClaim.Holds` (`Seams.lean:123-124`) is `Σ_w W(w)·q(w) = c` over the cube with `q`
lifted by `ofK`, the specification's `⟨W, g⟩ = c` (`03:115`); and `Weight.mle_eq` ties the
verifier's evaluator to the cube values, which is what "MLE-friendly" needs. No finding on the
pool's translation into weighted claims.

---

## E. Are the blueprint's non-interactive theorems well formed?

The four sketches (`bp:1218-1227`, `bp:1247-1250` at `b435631`):

```lean
theorem verify_iff_compiled (prog input proof) :
    verify prog input proof = true ↔
      ∃ s, s.Admissible prog ∧ (Verifier.fiatShamir (leanVmIopp prog s input flock).verifier …)
        accepts (decode s proof) under the BLAKE2s challenge oracle
structure FiatShamirSecurity where …   -- rbr knowledge soundness of the IOPP ⇒ knowledge soundness of its FS compilation in the ROM, error Q · max_i ε_i
structure BcsSecurity where …          -- Merkle-compiled oracles: extraction from collision resistance / ROM
theorem verify_knowledgeSound (fs : FiatShamirSecurity) (bcs : BcsSecurity) (mca : McaJohnson) (flock) :
    … knowledge soundness of `verify` with error niError s Q
theorem baseVerifier_extractsExecution (fs bcs mca flock) (h : verify prog input proof = true) :
    except with probability niError, ∃ t, ValidExecution prog input t
theorem baseProver_complete (hfill : HasFillBlocks prog) (h : ValidExecution prog input t) :
    verify prog input (prove prog input (witness of t)) = true
```

They are read here as statements to be written in Lean. Two library objects are introduced
first. A **random oracle** is a function drawn uniformly from all functions of a fixed domain
and range, to which every party has query access only; a theorem "in the random-oracle model"
(ROM) is a probability statement over that draw, against adversaries that make at most `Q`
queries. ArkLib's **Fiat–Shamir transform** (`Verifier.fiatShamir`, `FiatShamir/Basic.lean:129-136`
at `dca90385`, verbatim in probe H.2) turns an interactive `Verifier` into a
`NonInteractiveVerifier` whose one message is the tuple of all prover messages, and which
obtains each challenge by querying a *challenge oracle* `fsChallengeOracle StmtIn pSpec`
(`ProtocolSpec/Basic.lean:849-854`) at the pair (statement, messages so far)
(`challengeOracleInterfaceSR`, `:830-834`: "`Query := StmtIn × pSpec.MessagesUpTo i.1.castSucc`").
That oracle is an `OracleSpec`; any deterministic function of the same signature is a
`QueryImpl` for it, so a concrete hash chain can be plugged in by `simulateQ` (probe H.2,
`runWithChain`).

### E.1 `baseVerifier_extractsExecution`, and what a well-formed statement looks like

**As sketched, it has no probability space.** `verify prog input proof = true` is a decidable
proposition about three fixed values: `verify` is "a total, computable function of `(prog,
input, proof)` to `Bool`" (`bp:326`) and BLAKE2s is a fixed function. "Except with probability
`niError`" then quantifies over nothing: for fixed `(prog, input, proof)` the conclusion
`∃ t, ValidExecution prog input t` is either true or false, and no randomness makes the
hypothesis probabilistic. The same defect is in the source it transcribes, T4 in
`docs/architecture.md:264-269` ("`BaseVerifier.Accepts version proof program publicInput → except
with probability baseError, ∃ assignment, …`"), whose next sentence asks for what the sketch
omits: "The theorem must expose the component soundness/knowledge-soundness bounds, Fiat–Shamir
or random-oracle model, commitment and hash assumptions" (`architecture.md:271-273`).

**As sketched, it is soundness, not knowledge soundness.** The conclusion is an existential
over traces. Knowledge soundness names an extractor that outputs the witness; the blueprint's
own doctrine (`bp:96-103`, acceptance test 24) insists on a named, computable extractor for the
oracle protocol, and then discards it at the last step. Since `ValidExecution` is not what an
extractor can output (`bp:96-99` says so), the right shape is: the extractor outputs a stack
`q`; `witnessOf q` satisfies `SatisfiedBy` except with the error; `constraintSoundness` (T1)
then gives the trace. The knowledge statement is about the first step; the existential is its
corollary.

**What the randomness is over, and what the adversary is.** In the ROM the verifier is
`verify^H`, `verify` with the compression function `H : {0,1}^512 → {0,1}^256` (the primitive of
`fs/lib.rs:18-24`, "`f(a, b) = BLAKE2s(a‖b)`", used for the chain, the grinding and every Merkle
node and leaf, `fs/merkle.rs:40-51`) left as an oracle. The adversary `A^H` is a `Q`-query
oracle algorithm that outputs `(prog, input, proof)` (adaptively: leanVM's statement includes
the program, whose hash seeds the chain, `mod.rs:82-93`, and the sizes are the prover's,
`mod.rs:118-124`). The probability is over `H` (and `A`'s coins). A well-formed statement:

```text
theorem verify_knowledgeSound (Q : ℕ) (A : Adversary H Q) :
  Pr_H [ let (prog, input, proof, log) ← A^H ;           -- log: A's queries to H and the answers
         verify^H prog input proof = true ∧
         ¬ SatisfiedBy prog input (witnessOf (extract prog input proof log)) ]
    ≤ niError Q
theorem baseVerifier_extractsExecution (Q) (A) :
  Pr_H [ … verify^H prog input proof = true ∧ ¬ ∃ t, ValidExecution prog input t ] ≤ niError Q
```

with `extract` a **straight-line** extractor: it reads the Merkle leaves of the level-0
commitment off the query log (every leaf the prover can open was hashed, so it is in the log
except with the collision/preimage term), list-decodes the word to its `≤ L_0` nearby
codewords (section G), and returns the member that satisfies `M3Holds`, or a default. The
second theorem follows from the first by `satisfiedBy_witnessOf` and `constraintSoundness`
pointwise. Two further features of the deployed object a faithful statement carries:

- **the sizes are the adversary's.** `verify` dispatches on the eight announced sizes
  (`mod.rs:144-149`), so it is the union over admissible `s` of the members of a protocol
  family; a bound proved per member (per `s`) transfers to the union only by an argument
  about how `A`'s `Q` queries split among members (they do, since a query to the chain seeded
  and then fed the sizes belongs to one `s`); `niError` must be uniform in `s` or take the
  maximum. Acceptance test 21 (`bp:1326-1328`) records the dispatch and not this obligation.
- **the program enters the chain by its hash.** `iv = BLAKE2s("leanvm" ‖ len ‖ R1CS_DIGEST ‖
  bytecode_hash)` (`mod.rs:82-93`): two programs with the same `bytecode_hash` share every
  challenge, so the statement binds the program only up to a BLAKE2s collision, a term of
  `niError`.

**The random-oracle heuristic.** `verify` is a function; `verify^H` is a family. The only
theorem provable is about `verify^H` with `H` random; the sentence "BLAKE2s's compression
function is that `H`" is the **random-oracle heuristic**, a non-formal step to be named as such
in Layer 13 and in `docs/architecture.md` (which already has the words "Fiat–Shamir or
random-oracle model" but files them under "must expose", not under "assumed"). It cannot be a
Lean hypothesis (it is false for any fixed function, since an adversary may hard-wire it) and it
cannot be an axiom (`AGENTS.md`); the theorem about `verify` itself, with BLAKE2s fixed, is the
instantiation `H := blake2sCompress` of the definitions only (`verify = verify^blake2sCompress`,
by `rfl`), never of the security theorem. The same holds of the Merkle side (collision
resistance of BLAKE2s-256 is the second thing the heuristic buys).

### E.2 The three assumed interfaces: what each must state to be true and strong enough

Ground on ArkLib, both pins (`lib-arklib` G.4 established it; re-verified here at `dca90385`
and `7653a901`): `fiatShamir_completeness` is admitted and stated for the constant challenge
oracle (`FiatShamir/Basic.lean:163-173`); soundness after Fiat–Shamir is a `TODO` (`:175`);
round-by-round ⇒ state-restoration is commented out (`Security/Implications.lean:230-254`, and
the commented statement has the wrong error, `∑ i, rbrError i`, where a state-restoration bound
must depend on the query budget); state-restoration ⇒ plain knowledge soundness is admitted
(`:305-313`); `BCSTransform` is commented out (`BCS/Basic.lean:59-63, 79-82`);
`Commitment.extractability` has `False` for its body (`Commitments/Functional/Basic.lean:250-255`).
The pull requests the tracker names: #469 (open since 2026-04-19, "statements of Section 5" of
[CO25], the duplex-sponge Fiat–Shamir, no security proof) and #848 (open, stacked on #469,
"prove Theorems 6.1 and 6.2"); **#627 is an issue, not a pull request** (a design for the BCS
transform, 2026-07-10), whose staged plan says: "Full ROM/state-restoration soundness
inheritance is deliberately **out of scope** and will be fenced as a named open statement".

**`McaJohnson`.** What it must state: [BCHKS25] Theorem 4.6 as Annex B quotes it
(`B:176-185`, `thm:mca-johnson`): for the Reed–Solomon code of block length `n` and reduced
rate `ρ = (k−1)/n`, every radius `δ < 1 − √ρ`, every two-row word `C`, the probability over
`s ← E` that `C_s` agrees with the code on a set of `(1−δ)n` columns on which `C` does not
agree with the interleaved code is at most `a/|E|`, `a` the explicit expression in
`m = max(⌈√ρ/(1−√ρ−δ)⌉, 3)`. ArkLib states exactly this, admitted, at both pins:

```lean
-- ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean:203-219 (dca90385; 7653a901 has the
-- same statement)
theorem rs_mcaError_le_in_johnson_range
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    (_hk : 1 < k) (_hδ_pos : 0 < δ)
    (_hδ :
        (δ : ℝ) <
          1 - ((((k - 1 : ℕ) : ℝ) / Fintype.card ι) ^ ((1 : ℝ) / 2))) :
    mcaError (AffineLineGenerator F) (ReedSolomon.code domain k) (δ : ℝ) ≤
      ENNReal.ofReal
        (let n : ℝ := Fintype.card ι
         let ρ : ℝ := (k - 1 : ℕ) / n
         let m : ℝ := max ⌈(ρ ^ ((1 : ℝ) / 2)) /
           (1 - ρ ^ ((1 : ℝ) / 2) - δ)⌉ 3
         ((2 * (m + 1/2) ^ 5 + 3 * (m + 1/2) * δ * ρ)
            / (3 * ρ ^ ((3 : ℝ) / 2)) * n
          + (m + 1/2) / ρ ^ ((1 : ℝ) / 2))
           / (Fintype.card F : ℝ)) := by
  sorry -- ABF26-T4.12; external admit [BCHKS25 Thm 4.6].
```

Instantiated at `F := E` and `domain` the additive subspace of `K ⊂ E` (`B:90, 302`), for the
affine line `u_0 + s·u_1`, which Annex B's footnote (`B:158`) converts to the fold
`(1−s)u_0 + s·u_1` in characteristic two. It is a statement of mathematics, not about protocols,
so quantifying it universally (over `ι`, `F`, `domain`, `k`, `δ`) is right and true if the
theorem is; its consumer is Lemma B.8 (`lem:fold-list`), through the `2^{ℓ−1}` union of rows.
Strong enough: yes, it is the only coding-theoretic input Theorem B.7 uses (`B:140-152`). Its
witness obligation is the preprint's theorem (the `literature` dossier, C.3, notes the two
readings of the constant `m`; the printed one, the larger error, is what both Annex B and ArkLib
state). Well formed.

**`FiatShamirSecurity`.** As the comment states it — "rbr knowledge soundness of the IOPP ⇒
knowledge soundness of its FS compilation in the ROM, error `Q · max_i ε_i`" — it is a
universally quantified claim over IOPPs and is **false**: (a) an IOPP's messages are oracles;
its Fiat–Shamir compilation hashes commitments, not oracles, and the compiled error carries a
hash term (the `literature` dossier, A.3 item 2: `3.5·t²/2^λ` in [CY24] Theorem 25.2.1,
`3(Q²+1)/2^κ` in [BGKTTZ23] Theorem 3.15); (b) leanVM's compilation grinds 17 bits at every
query round, which no theorem in the literature covers (A.3 item 3) and which changes the
error from `Q·max ε_i` to `(t + k)·max_i 2^{−b_i}ε_i` at best; (c) the hash-chain construction
(`fs/lib.rs:85-99`, a state ratcheted by `H`) is neither ArkLib's per-round oracle keyed by the
whole prefix nor [CO25]'s permutation sponge, so a theorem about either applies only through a
further "chain is as good as the ideal oracle" lemma (collision term `Q²/2^256`). What ArkLib is
about to offer (#848, `SingleSalt.lean:973-993` at its head `1c5c5bd7`,
`single_salt_fiat_shamir_knowledge_soundness`) takes **state-restoration** knowledge soundness of
a plain `Verifier` with coins, for the challenge oracle `fsChallengeOracle (StmtIn × Salt) pSpec`
implemented by lazy uniform sampling (`srChallengeQueryImpl'`), and concludes adaptive NARG
knowledge soundness with the same error; it has no BCS side, no grinding, and needs
round-by-round ⇒ state-restoration, which is not stated anywhere. To be true and strong enough
the interface must be stated for **this** construction: (1) a public-coin interactive argument
`V^H` (the Merkle-compiled protocol, section E.3) that is state-restoration knowledge sound
against `Q`-query provers in the ROM with error `ε_sr(Q)`, (2) the hash chain of `fs/lib.rs`
with `H` random, (3) the named ground rounds with their bits `b_i`, and conclude adaptive
knowledge soundness of the chain-compiled NARG with error `ε_sr(Q) + c·Q²/2^256`; and the
grinding must be inside `ε_sr` as "a query to `H` at a ground round costs `2^{b_i}` queries in
expectation". None of this exists in Lean; the honest interface names the literature and the
gap (A.3: "a new assumption to name").

**`BcsSecurity`.** As the comment states it ("Merkle-compiled oracles: extraction from
collision resistance / ROM") it names a property with no error and no object. At the pin
nothing can inhabit it, and #627's plan excludes the ROM inheritance it would need. To be true
and strong enough: for the IOP `C` of section E.3 (oracle messages: the level-0 `K`-word and
the deeper `E`-words, all with position queries), the Merkle compilation of `pcs/merkle.rs` and
`fs/merkle.rs` (leaf = BLAKE2s of the row image, node = BLAKE2s of the two children, fixed
height and fixed leaf width) in the ROM preserves state-restoration knowledge soundness, with
the straight-line extractor that reads every committed leaf off the query log, up to
`3(Q²+1)/2^256` ([BGKTTZ23] Theorem 3.15's hash term; [CY24] Theorem 25.2.1). Its hypothesis
must include that the verifier fixes the leaf width and the tree height from public data
(section D, checks M2–M7): that is what makes leaf/node confusion impossible without domain
separation.

Two interfaces the blueprint does not list and that the theorem needs:

- **round-by-round ⇒ state-restoration** knowledge soundness, with error `Q_i·ε_i` summed over
  rounds or `Q·max_i ε_i` ([CY24] Theorem 31.2.1/31.3.1: `(t + k)·max_i ε_i`; the `literature`
  dossier A.3 item 1); commented out in ArkLib (`Implications.lean:230-254`) with the wrong error.
- **the list-binding compilation** of E.3, which is not an upstream theorem at all.

### E.3 From WHIR's list soundness to extraction of one `q`

**What Theorem B.7 gives.** Round-by-round **soundness** (Definition B.2, `B:74-84`, an
invariant on partial transcripts with an escape probability per verifier message) for the
relation `R_open = {(C⁽⁰⁾, {(W_t, c_t)}) : ∃ U ∈ L_{γ_0}(C⁽⁰⁾), ⟨W_t, g_U⟩ = c_t ∀ t}`
(`B:133-136`), where `L_{γ_0}(C⁽⁰⁾)` is the set of interleaved codewords within radius `γ_0` of
the committed word, of size at most `L_0 = 1/(2η_0√ρ_0)` (`B:137`). Its start invariant is
"every `U ∈ L_{γ_0}(C⁽⁰⁾)` violates at least one of the `J_0` claims" (`B:218`). No extractor
is named: it is soundness for a language, in the IOP model (the oracles `C⁽ⁱ⁾` are read at
queried columns only; the prover is unbounded).

**What the master theorem gives.** `piop_rbrKnowledgeSoundness` (`Spine/Compose.lean:172-177` at
`b435631`) is ArkLib's worst-case round-by-round knowledge soundness for `piopExtractor`, whose
first step reads the stack `q` off the commit message (`commitExtractor`, `Compose.lean:58-59`),
with a knowledge state function whose `toFun_full` property says (`Security/RoundByRound.lean:186-189`
at `dca90385`): if the verifier can output a statement in `relOut` with witness `witOut`, the
state is true at the full transcript. Everything is relative to **one** `q`.

**The step "Layer 12 turns list binding into extraction of the one `q`"** (`bp:1190`,
acceptance test 11, `bp:1296-1299`) is a theorem about the composed IOP, and it can be stated:

Let `Front` be the spine's prefix `commit ⟫ bus ⟫ table ⟫ pub ⟫ flock`, whose verifier never
queries the oracle (true of the built phases; a requirement on the others under (ii)), with
worst-case round-by-round knowledge soundness from `M3Rel` to `Seam.flock` at errors `ε_i`
(the composition of the first four fields of `Phases.Security`). Let `Front'` be `Front` with
the commit message's type replaced by an interleaved `K`-word `w` (the level-0 codeword, with
position queries) and the statement carried unchanged; since the front's verifier never reads
the oracle, `Front'`'s verifier is `Front`'s. Let `C := Front' ⟫ whirOpen` (the level-0 batching
of `whirOpen` being the opening phase's `λ`). Then:

> **List-binding compilation.** `C` is worst-case round-by-round knowledge sound for `M3Rel`
> with extractor `E(w, τ) :=` the first `g ∈ Λ(w)` with `M3Holds input g` (else a default),
> where `Λ(w) = {g_U : U ∈ L_{γ_0}(w)}`, and per-challenge errors `L_0·ε_i` at the front's
> challenges and Theorem B.7's at WHIR's. Its knowledge state function is: after `w`, "no
> `g ∈ Λ(w)` satisfies `M3Holds`"; inside the front, "for every `g ∈ Λ(w)`, the front's state at
> `(g, τ)` is false" (the front's state function evaluated with `g` in place of the commit
> message); at the seam this reads "for every `g ∈ Λ(w)` some pooled claim is false of `g`",
> which is `∉ R_open` and Theorem B.7's start invariant; then Theorem B.7's invariant.

Proof shape: the front's `toFun_next` and `toFun_full` transfer pointwise (each `g` is a
transcript of `Front`); the escape probability of a front challenge is bounded by the union over
`Λ(w)` of the front's worst-case bound, which is per transcript and therefore per `g`
(`rbrKnowledgeSoundnessWorstCaseWith`, `RoundByRound.lean:553-568`: a bound for every statement,
every round, every partial transcript); the seam step needs `toFun_full` of the front's state
function in the contrapositive: state false at the front's last transcript ⇒ the verifier's
output claims are not all true of `g`. That is exactly why the spine's *worst-case* form is the
right one (the averaged `rbrKnowledgeSoundness` would not union-bound). What it needs and does
not have: Theorem B.7 in Lean (hole K1); the lemma that every member of `Λ(w)` is `K`-valued
and of the right size (section G); a generic "state functions indexed by a finite set" lemma
(union bound; ArkLib has none); and the identification of the front's oracle-free verifier with
`Front'`'s (a cast of `OracleReduction`, which ArkLib #383's `Cast.lean` is about). The
extractor is computable as a definition (enumerate the codewords of the finite code; Lean has no
cost model, `bp:102-103`), and efficient in the literature's sense through Guruswami–Sudan,
which Lean need not implement.

This theorem is where the factor `L_0` enters `niError` (section F), and it is the missing
fourth ingredient of `verify_knowledgeSound`: neither `FiatShamirSecurity`, `BcsSecurity` nor
`McaJohnson` contains it, and the sentence "`verify_knowledgeSound` extracts the member"
(`bp:1299`) assigns it to a theorem whose sketched hypotheses cannot prove it.

### E.4 `verify_iff_compiled`

"Unconditional: it is about two definitions" (`bp:1231-1232`) is right in kind and wrong in
the definitions named.

1. **`Verifier.fiatShamir` takes a `Verifier`, not an `OracleVerifier`**, and an oracle verifier
   becomes one only through `OracleVerifier.toVerifier` (`Basic.lean:490-496` at `dca90385`;
   probe H.2 prints its type), whose statement is `StmtIn × (∀ i, OStmtIn i)` and whose
   transcript holds the oracle messages **in the clear**: `(leanVmIopp …).verifier.toVerifier`
   has the level-0 word (`2^{μ−6}·2^6` elements of `K`) and every deeper codeword as messages,
   and `fsChallengeOracle` would hash them whole. No `decode : Proof → messages` exists: a proof
   holds roots and opened rows (`fs/transcript.rs:9-12`), from which no codeword is recoverable.
   The right-hand side must be the Fiat–Shamir compilation of the **Merkle-compiled**
   interactive verifier, whose messages are the roots, the scalars, the grinding nonces and
   the openings; ArkLib has no such compilation (`BCSTransform` commented out), so Layer 12 must
   define it (`bcsCompile`) before it can state the theorem.
2. **The challenge oracle can be the chain.** Probe H.2 shows the mechanism: a function
   `chain : (i) → StmtIn × MessagesUpTo i → Challenge i` is a `QueryImpl (fsChallengeOracle …) Id`,
   and `simulateQ` runs the compiled verifier under it to an `Option StmtOut`. leanVM's chain is
   such a function once the statement is `(input)` with `(prog, s)` as parameters of the family
   (the chain's seed depends on `prog` through `iv`, `mod.rs:82-93`, and its first eight absorbs
   are the sizes, `mod.rs:118-124`) and the messages are absorbed in the wire encoding (one
   coefficient of each round polynomial dropped, `fs/transcript.rs:63-71`, `:289-309`; a root as
   two scalars, `fs/merkle.rs:14-20`; the Merkle openings **not absorbed**, `fs/transcript.rs:225-228`
   "Not absorbed: its binding is the Merkle structure itself"). A challenge that is several
   squeezes (`α ∈ E^4`, the query positions by chunking, `whir.rs:1175-1193`) is one `Challenge i`
   of a product type, or several rounds.
3. **The grinding checks are not in the right-hand side.** The nonce at each query round is a
   prover message (absorbed with tag 4, `fs/lib.rs:118-120`), and the verifier's check
   `pow_bits_ok(pow_base(cv), nonce, 17)` (`fs/lib.rs:47-51, 165-174`) reads the **chain state**
   `cv`, which an ArkLib `Verifier` does not see: its `verify` takes the statement and the full
   transcript (`Basic.lean:248-250`). Either the interactive verifier recomputes the chain from
   the transcript (definable, since the chain is a function of statement and messages; it then
   depends on `H` and is no longer an IOP verifier), or `verify_iff_compiled`'s right-hand side
   is a conjunction "the compiled verifier accepts ∧ every grinding check passes", the second
   conjunct being about the chain. The sketch has neither.
4. **`∃ s, s.Admissible prog`** is right in shape (the family is indexed by the sizes; the proof
   carries them as its first eight scalars) provided `Admissible` is the verifier's whole
   predicate (`gt-bus` G4: the stacking window and the rate window included).
5. **The equation is a definition, not a theorem, if `verify` is defined as the right-hand
   side.** The blueprint wants `verify` "written from §8.5 before `cpu/mod.rs:711-779` is opened"
   (`bp:1216`) and the theorem to "pin the shape" (`bp:1277`, `:1302`, `:1316`, `:1328`). That is
   only a check if the two sides are written independently; then the theorem is provable by
   unfolding (`rfl`-like), and its value is the review of the two definitions.

Statable form (with (ii) and the corrections above):

```text
theorem verify_iff_compiled (prog input proof) :
    verify prog input proof = true ↔
      ∃ s, s.Admissible prog ∧ ∃ msgs, decode prog s proof = some msgs ∧
        runWithChain (bcsCompile (leanVmIopp prog s)).verifier (blake2sChain prog s) input msgs
          = some () ∧ grindingChecks prog s msgs = true
```

### E.5 Completeness

"Perfect completeness survives the transform without any assumption" (`bp:1256-1257`) is false
for the deployed transform, for two reasons of different weight.

**Grinding.** The honest prover's grind is a search: `fs/lib.rs:126-155` `grind_pow` loops over
nonces `0, 1, 2, …` "until" `pow_bits_ok` (`loop { … break n }` at `:132-138`, and the parallel
form at `:139-151`), with no bound. For a fixed state `cv` there is no theorem that a `u64`
nonce (or any nonce) with `compress(pow_base(cv), nonce ‖ 4)[0] ≡ 0 mod 2^17` exists; in the
ROM the search fails with probability `(1 − 2^{−17})^{2^64}`, not zero; with BLAKE2s fixed the
statement "for every reachable `cv` a nonce exists" is a conjecture about BLAKE2s. So
`prove prog input w` in Lean is either partial (`Option Proof`, returning `none` when a fuelled
search fails) or takes the nonces as an argument, and `baseProver_complete` is
`prove … = some proof → verify … proof = true` (or "for every choice of nonces that passes").
"Without any assumption" must go; the assumption is the success of the search, and it is
harmless only because it is checked by running the prover.

**Phases complete up to an error.** `Phases.Complete` demands `perfectCompleteness` of every
phase (`Compose.lean:94-104`; `Component.Complete.complete` is `perfectCompleteness`,
`lib-arklib` G.2). If any phase were complete only up to an error, `Phases.Complete` would be
uninhabitable and `baseProver_complete`, an equation, unprovable. The blueprint's acceptance
test 20 (`bp:1323-1325`) says Flock has an exceptional challenge; `gt-flock-ring` §4 and finding
8.4 settle it: the *protocol* is perfectly complete (no verifier takes an inverse; the derived
coefficient `c_0 = claim + r·(c_1 + …)` is right at every `r`, `fs/transcript.rs:297-302`), and
the exceptional point belongs to the pinned Rust prover's shortcut (`zerocheck.rs:117`). So the
Lean honest prover can be perfectly complete phase by phase, and the composition
(`Reduction.seqCompose_perfectCompleteness_of_pure`, `bp:242`) applies; `lib-arklib` G.2's
proposal of an error field in `Component.Complete` remains the right insurance, and with it
"survives the transform" becomes "with the sum of the phases' errors, plus the grind".

**What does survive.** With the chain deterministic, an honest proof that the interactive
verifier accepts on the chain's challenges is accepted by `verify`: that is a statement about
two definitions (the interactive run with challenges supplied by the chain equals the
compiled run), true by unfolding, and the grinding is the only randomness left in the honest
prover.

---

## F. The numbers

### F.1 The blueprint's `piopError_le` and acceptance test 23

`piopError_le (hs : s.Admissible prog) : Σ i, piopError s i ≤ 2^40/|E| + flockError` (`bp:1130`);
test 23: "at the caps, `Σ piopError < 2^{-150}` plus Flock's `< 2^{-183}`" (`bp:1331-1332`).
Evaluated with the blueprint's own per-phase charges, at the largest admissible instance. The
sizes are bounded by the stacking window, `μ_stack ≤ 28` (`mod.rs:174-176`, `pcs.rs:51`): every
column has at most `2^28` entries, so `κ_mem ≤ 26`, `τ_j ≤ 24`, and the bus depth is
`μ_bus ≤ 28` (the Python layout code run over a covering grid of sizes finds `28` as the
maximum, at `κ_mem = 16, τ = (0, 0, 23, 0, 23, 3), κ_bc = 26`, scratch `bus_depth.py`, section H.3;
`gt-bus` D.4 proves `μ_bus ≤ 28` by counting). The table sumcheck has `B = 2` constraints in
all (`py:836-851`: only JUMP has constraints, `n_constraints = 2`; `xi_powers = powers(xi,
n_constraints + 3)`, `py:1391`), `τ_max ≤ 24`, and `J = 113`.

| Phase, charge (blueprint) | Where | Value at the maximum, as a multiple of `1/|E|` |
| --- | --- | --- |
| bus, `4·2^{μ_bus}` on `(α, β)` | `bp:974` | `2^30` |
| bus, GKR: `(nside − 1)` per combiner, `5` per round, `2` per pair | `bp:941-942` | `≈ 14 layers × 14 ≈ 2^7.6` |
| zerocheck escape, `τ_max` per constraint | `bp:1001-1003` | `48` |
| table, `(B + 2)` on `ξ`, `3` per round | `bp:994` | `4 + 72` |
| public input, `1` | `bp:1027` | `1` |
| Flock, `(4·k_batch + 163) + 2^32` | `bp:1085` | `≈ 2^32` |
| opening (Layer 10 as sketched), `(J − 1)` on `λ`, `2` per round | `bp:1114` | `112 + 56` |
| **sum** | | `≈ 1.25·2^32 ≈ 2^{32.3}`, that is `≈ 2^{-159.7}` |

So under the window `piopError_le` holds with a margin of `2^8`, and the interactive error of
the oracle protocol is about `2^{-160}`, dominated by ring switching's `2^32/|E|` (which test 23
leaves out of "Flock's `< 2^{-183}`": `gt-flock-ring` 8.8). At the per-log caps without the
window (`κ_mem = τ_j = 32`), `μ_bus = 38` (scratch run, `stack_log 41 bus depth 38`) and the
`(α, β)` term alone is `4·2^38 = 2^40`, so the bound is false there, as `gt-bus` D.4/G4 found.
The statement is only true if `Admissible` contains the window.

**What it measures.** `Σ piopError` is the *interactive* error of the *oracle* protocol (the sum
over challenges, `bp:318`). It is not the quantity that governs the deployed security: after
Fiat–Shamir the governing quantity is the largest per-challenge error (`B:84`, `whir_config.rs:25-27`),
and the deployed challenges with the largest errors are WHIR's, which the oracle protocol does
not contain. `2^{-150}` is therefore a fact about a sub-protocol, of no consequence for the
128-bit claim.

### F.2 What the deployed parameters claim, and in which regime

`SECURITY_BITS = 128` (`whir_config.rs:38`; `lean_vm/src/lib.rs:69`) is a **round-by-round**
target: "every verifier-challenge transition must have conditional failure probability at most
`2^-SECURITY_BITS`" (`whir_config.rs:36-37`), "the Fiat–Shamir error per random-oracle query is
the MAX of the entries, not their sum" (`:25-27`), "not a claim that the sum of all interactive
failure probabilities is bounded" (`:404-407`). The regime is **Johnson list decoding with an
explicit slack**, provable given [BCHKS25] Theorem 4.6 (`:314-337`: "That analysis is always the
Johnson radius with explicit slack `eta` … WITH out-of-domain binding"; `analysis_version`
`"bchks25_thm_4_6_exact_reduced_rate_row_union_optimized_eta"`, `:961`); no capacity conjecture,
no unique-decoding fallback in production (`udr_queries` is `#[cfg(test)]`, `:175-180`).

The per-level parameters are the output of a floating-point search (`optimize_johnson_level`,
`:639-707`) over the theorem parameter `m ≥ 3`, minimizing the query count subject to four
per-level bounds; the Python tabulates the resulting query counts (`py:910`). A scratch port of
the search (section H.3, `whir_params.py`) **reproduces the Python table exactly** for all
`μ ∈ [15, 28]` and `ρ ∈ {1, …, 4}` (the ladder geometry, the rates and the query counts), so
the blueprint's `ladder_queries_eq : (ladder 15 1).map (·.queries) = [223, 55]` (`bp:1165`) is the
right pin and the Rust and the Python agree. What the search yields, at three sizes:

| `μ`, `ρ` | level | fold | rate | `m` | `η` | `γ` | Johnson list bound `L ≤ 1/(2η√ρ)` | queries | OOD | fold (MCA) bits | query bits (+17 grind) | OOD bits | list-unioned algebraic bits |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 15, 1/2 | 0 | 6 | 1/2 | 395 | 0.00179 | 0.292 | 396 | 223 | 0 | 132.9 | 111.0 | 179.5 | 152.4 |
| | 1 | 4 | 1/16 | 306 | 0.00080 | 0.753 | 2527 | 55 | 1 | 133.2 | 111.0 | 167.2 | 149.7 |
| 28, 1/2 | 0 | 6 | 1/2 | 110 | 0.00643 | 0.286 | 110 | 228 | 0 | 129.2 | 111.0 | 180.4 | 154.2 |
| | 1 | 4 | 1/16 | 81 | 0.00309 | 0.747 | 648 | 56 | 1 | 129.8 | 111.0 | 169.9 | 151.7 |
| | 2 | 4 | 1/128 | 46 | 0.00192 | 0.910 | 2944 | 32 | 1 | 130.4 | 111.0 | 165.8 | 149.5 |
| | 3 | 4 | 1/1024 | 8 | 0.00390 | 0.965 | 4100 | 23 | 1 | 139.2 | 111.1 | 165.2 | 149.0 |
| | 4 | 4 | 2^-13 | 4 | 0.00274 | 0.986 | 16644 | 18 | 1 | 140.2 | 111.4 | 161.6 | 147.0 |
| | 5 | 4 | 2^-16 | 5 | 0.00068 | 0.996 | 218453 | 14 | 1 | 134.7 | 111.2 | 154.9 | 143.3 |
| 28, 1/16 | 0 | 6 | 1/16 | 27 | 0.00926 | 0.741 | 216 | 57 | 0 | 131.7 | 111.0 | 179.4 | 153.3 |

(the residual is 5 variables at `μ = 15` and 2 at `μ = 28`; "bits" is `−log₂` of the bound;
the columns are `whir_config.rs`'s `paper_johnson_log_a` (`:484-490`, Theorem 4.6's `a` times
the row union `2^{ℓ−1}` of Lemma B.8), `paper_per_query_bits × queries` (`:494-498`),
`paper_ood_bits` (`:600-608`) and `johnson_algebraic_bits` (`:556-568`)).

Reading: (1) the **query rounds** are the weakest: `(1 − γ)^t ≈ 2^{-111}` at every level, by
design (`:57-60`: "the query count only needs to close the remaining `SECURITY_BITS − 17`
bits"), the other 17 bits being the proof of work ground before the positions are sampled; (2)
the **fold challenges** sit at `128.2` to `146` bits (the mutual-correlated-agreement term, with
the `2^{ℓ−1}` row union; the search stops at the first `m` that clears 128, `:664-665`); (3) the
Johnson list bound is **`L_0 ≤ 396` at level 0** (`2^{8.6}`, at `μ = 15`) down to `110` at
`μ = 28`, and grows to `2^{17.7}` at the deepest levels; (4) the algebraic checks "unioned over
the list" (`:537-555`: the batch polynomial's degree and the ring switching's `2^{31}+…`,
times `L_i`) sit at `143` to `154` bits — this is the **only** place the Rust multiplies an
oracle-protocol error by the list size; the bus's `4·2^{μ_bus}` is not unioned
(`leaf.rs:108-118`, `soundness_degree_bound` has no `L`): with `L_0 ≤ 2^{8.6}` and
`μ_bus ≤ 28` it would still clear 128 (`192 − 30 − 8.6 = 153`), so the omission is not a
vulnerability at these parameters, but it is an omission of the same kind the blueprint makes.

### F.3 `niError` against this

`niError` "is the round-by-round maximum times the query bound plus the grinding-adjusted WHIR
terms" (`bp:1234-1235`). Set against F.2 and the `literature` dossier's A.3:

- the "round-by-round maximum" of the oracle protocol is `≈ 2^{-160}` (F.1); of the compiled
  protocol it is `2^{-111}` at every query round before grinding and `2^{-128.2}` at the worst
  fold. "Plus the grinding-adjusted WHIR terms" acknowledges that the maximum is elsewhere but
  gives no formula; the phrase "grinding-adjusted" has no theorem behind it (A.3 item 3), and the
  adjustment is multiplicative on a per-round error (`2^{-17}·2^{-111}`), not additive;
- the factor `L_0` on every oracle-protocol challenge (E.3, section G) is absent; numerically
  benign (`2^{-160+8.6}`), structurally load-bearing;
- the hash term (`Q²/2^256`-type) is absent; numerically it is what caps the 128 bits at a
  256-bit digest (A.3 item 2);
- the prover's choice of sizes (E.1) is absent.

**Does the blueprint's bound mean something at the deployed parameters?** `Σ piopError <
2^{-150}` is a true statement about the ideal-oracle protocol at admissible sizes and says
nothing about `verify`'s security level, which is set by the query rounds at 111 bits of
information-theoretic soundness plus 17 bits of work, in the Johnson regime, conditional on
Theorem 4.6. A `niError` that could carry leanVM's claim would read, per random-oracle query,
`max( L_0·max_front ε_i , max_fold(2L_i/|E| + 2^{ℓ_i−j}a_i/|E|) , max_query 2^{-b}(1−γ_i)^{t_i} ,
… )` times `(Q + rounds)`, plus the hash term, and it would be a statement about the ROM
construction of E.2, not about the oracle protocol.

---

## G. The oracle model's hidden assumption

In the oracle protocol the prover's first message is `q : Column μ`, a table of `2^μ` values of
`K`, and the verifier reads it only through the interface (evaluation queries today, weighted
queries under (ii)); the extractor reads it whole (`commitExtractor`). The compiled protocol
replaces `q` by a Merkle root. For the compiled protocol to inherit the oracle protocol's
security, the commitment must provide:

1. **binding to a `K`-valued table of size `2^μ`** — the object `M3Holds` is about (`M3Rel I`
   is on `Column I.μ`, `Spine/Instance.lean` at `b435631`; the bus's fingerprints, the counts, the
   packing of `q_flock` all use that the entries are in `K`);
2. **weighted openings over `E`** — the pooled claims have weights and values in `E` (`03:113`);
3. an **extractor** that recovers the table from what the adversary did, straight-line.

What the deployed WHIR provides:

- **A `K`-valued word, not a codeword.** The root commits (up to collisions) to a leaf image per
  position: `2^6` words of 8 bytes at level 0 (`whir.rs:331-345`, `pcs/merkle.rs:144-192`), and
  every 8-byte pattern is an element of `K` (`K = F_2[x]/(x^64 + …)`, `A:8`; `F64(u64)`), so the
  committed object is an interleaved word `w ∈ K^{2^6 × n_0}` by encoding, with no check that any
  row is a codeword: **proximity, not membership** (`B:4` "our PCS is only list binding";
  `B:70-72` Definition B.1). The verifier supplies the zero prefix of the absent lanes
  (`fs/merkle.rs:53-58`, `whir.rs:2125-2132` with `row_words = n_lanes`), so `w`'s rows past
  `n_lanes` are zero in the Rust's proof format (section C for the Python's).
- **A list, over `E`.** Theorem B.7 binds the prover to `Λ(w) = {g_U : U ∈ L_{γ_0}(w)}`, the
  interleaved codewords of `RS[E, dom_0, 2^{κ_0}]` within radius `γ_0` (`B:137`), of size at
  most `L_0` (F.2: `110` to `396`). A priori these are `E`-valued multilinears; the relation
  needs `K`-valued ones. **They are `K`-valued** (my argument; the specification does not say
  it): write `E = K ⊕ K·y ⊕ K·y²` and a row `U_u = U⁽⁰⁾_u + y·U⁽¹⁾_u + y²·U⁽²⁾_u`. The
  encoder's generator matrix is `K`-valued (the novel basis evaluated at points of `dom ⊂ K`,
  `B:302-306`, "a `K`-valued message gives a `K`-valued word"), so each coordinate projection
  `U⁽ʲ⁾_u` is a codeword of `RS[K, dom_0, 2^{κ_0}]`. On the agreement set `A`, `|A| ≥ (1−γ_0)n_0
  > ρ_0 n_0 = 2^{κ_0}` (since `γ_0 < 1 − √ρ_0 ≤ 1 − ρ_0`), `U_u = w_u ∈ K`, so `U⁽¹⁾_u` and
  `U⁽²⁾_u` vanish on more than `2^{κ_0} − 1` points and are zero; `U = U⁽⁰⁾`. So every member of
  `Λ(w)` is `K`-valued, of `μ` variables after the relayout `f(u, x) = q(x, u)` (`B:380`), with
  zero rows where `w` has them. This lemma belongs to Layer 11 or 12 and is a hypothesis of the
  list-binding compilation (E.3); without it the extracted witness has the wrong type.
- **Openings over `E` of weighted claims**: provided, that is Theorem B.7's relation.
- **Extraction**: from the query log (the leaves) and list decoding, as in E.3; in the Johnson
  regime the list is small and Guruswami–Sudan finds it; in Lean, enumeration suffices.

**The assumption, stated.** The master theorems assume the verifier's oracle *is* one table
`q`. The commitment gives a set `Λ(w)` of at most `L_0` tables, fixed when the root is sent,
among which the prover may choose after seeing challenges. The security of the compiled
protocol is the master theorem applied to every member at once, with a union bound: the
per-challenge errors of every phase before the opening are multiplied by `L_0`, the extractor
is "list-decode, then select the member that satisfies `M3Holds`", and the opening's job is to
show that some member satisfies every pooled claim (Theorem B.7's relation `R_open`, `B:133-136`;
acceptance test 11, `bp:1296-1299`, has the right words). The Rust's own accounting states the
same in one place ("the opening's own evaluation claim sits at a post-commit random point, so
at most one list member matches it except with `L·μ/|F|`", `whir_config.rs:593-599`) and Flock
in another (the `literature` dossier A.3 item 4, [BRW26] Remark 11). Neither the specification
(§8.4 is `TODO`, `08:44-46`), nor the blueprint's `verify_knowledgeSound`, nor any of its three
interfaces contains it; the sentence "Layer 12 turns list binding into extraction of the one `q`
that satisfies every pooled claim" (`bp:1190`) names the step without the theorem.

---

## B. WHIR, Merkle trees and the parameters, as deployed

Note on citations: the leanVM working tree was moved off the pin on 2026-09-30 09:42 (its
reflog: `pull: Fast-forward`, then `checkout: moving from main to
feat/drop-prover-public-input-challenge`; HEAD `248da071`), not by this review. Every line
cited below was read on 2026-09-29 while HEAD was `a386121f`, and the ones quoted were
re-verified on 2026-09-30 with `git show a386121f:<path>`; the scratch scripts of section H
read a copy of the pinned `verifier.py` extracted the same way.

### B.1 The message schedule per level

Notation: `μ` the stack's log-size; `k_0 = 6` the initial fold (`whir_config.rs:67`), `k_i = 4`
after (`:68`), the residual `n_res ≤ 5` (`:86`); `r` the number of recursive levels
(`level_steps`); `t_i` the query count of level `i`; `z` an out-of-domain point.

| # | Message | Specification, Protocol B.6 (`B:100-123`) | Rust prover (`whir.rs`) / verifier (`whir.rs`, succinct) | Python (`py:1006-1087`) |
| --- | --- | --- | --- | --- |
| 0 | `V→P` `λ` (level-0 batching), `J_0 = 113` claims | step 1 at `i = 0` (`B:110`) | outside WHIR: `stack_open.rs:400` / `:518` (A.2) | `py:1361` |
| 1 | `P→V` `h_1`: round polynomial of `Σ_x q(x)·W_λ(x) = C_λ` (2 scalars: `c_0, c_2`; `c_1` derived) | step 2, `j = 1` (`B:111`) | `:1324-1326` / `:2087-2090` | `:1012` |
| 2 | 6 × (`V→P` `r_j`; `P→V` next round polynomial), the **lane fold** on the stack's top 6 coordinates | step 2, `j = 1..ℓ_0` (`B:111-112`); the row index is the stack's most significant `ℓ_0` coordinates, `f(u, x) := q(x, u)` (`B:380`) | `:1328-1334` / `:2100` (`replay_fold_rounds`, `:1641-1655`); the point is rotated by 6 at the end, `:2297-2306` | `:1017-1024`; rotation `:1078-1079` |
| 3 | `P→V` root of `f⁽¹⁾` (2 scalars), the fold `f⁽¹⁾ = q̃(r_1..r_6, ·)`, `E`-valued, interleaved `2^4` lanes | step 3(a) (`B:115`) | `:1340-1358` / `:2104` | `:1034` |
| 4 | OOD: `V→P` `z ∈ E^{μ−6}` (`μ − 6` squeezes); `P→V` `y` (1 scalar); `P→V` intro round polynomial for the claim `(eq(z, ·), y)` (2 scalars) | step 3(b) (`B:116`): `z`, `y`; **no intro message** | `send_ood`, `:1201-1208` / `replay_ood`, `:1670-1675`; count `ood_samples[1] = 1` (`whir_config.rs:677-684`, test `:1032-1034`) | `:1035-1037` |
| 5 | `P→V` grinding nonce (1 raw scalar); `V` checks 17 bits | **absent** | `:1366` / `:2117` (`grind_check`, `fs/transcript.rs:314-323`); `QUERY_GRINDING_BITS = 17` (`whir_config.rs:60`) | `:1039` |
| 6 | `V→P` `t_0` positions in `[0, 2^{μ−6+ρ})`, by chunking squeezes | step 3(c): "`t_i` i.i.d. columns" (`B:117`) | `sample_queries_ordered`, `:1175-1193`: `⌊192/d⌋` `d`-bit chunks per squeeze, duplicates kept / `:2122` | `:943-951`, `:1041` |
| 7 | `V→P` `λ_0`, the level's batching challenge | step 1 at `i = 1` (`B:110`), **after** step 3(d)'s claims are formed | `:1373` / `:2123` | `:1044` |
| 8 | `P→V` Merkle openings of level 0 at the positions (rows of `n_lanes` words + one octopus), **not absorbed** | step 3(c): "it reads `C⁽ⁱ⁾[·, x_q]`" (`B:117`) | `hint_merkle`, `:1380` / `recv_level_rows`, `:2125-2135` (`fs/transcript.rs:263-279`) | `:1049-1050` (raw paths) |
| 9 | `P→V` intro round polynomial for the query batch (2 scalars), with claim `enforced_sum_0 = Σ_q λ_0^q·⟨row_q, eq(r_lane, ·)⟩` computed by `V` from the openings | step 3(d): the `t_i` consistency claims `(W_{x_q}, c_q)` with `c_q = C_fold[x_q]` (`B:117-118`); **no intro message**, the batch's `h_1` is sent after `λ` | `:1405-1406` / `:2140-2144` (`induce_sumcheck_enforced_sum`, `whir_induce.rs:203-218`) | `:1051, 1057` |
| 10 | `V` glues: running quad `+= λ_0·quad_ood + λ_0²·quad_query`, claim `t_r += λ_0·y + λ_0²·enforced_sum` | step 1 at level 1: `(W, σ_0) := (Σ λ^{t−1} W_t, …)` with the order residual, OOD, queries (`B:118`, `:110`) | `glue_pending`, `:1131-1154` / `batch_level_claims`, `:1681-1701` | `:1058-1063` |
| 11 | level `i ≥ 1`: 4 × (`V→P` `r`; `P→V` round polynomial); then as 3–10 with `t_i`, the leaf `3·2^4` words | steps 2–3 (`B:111-119`) | `:1420-1425, 1509-1560` / `:2191-2194, 2311-2384` | `:1017-1063` (loop) |
| 12 | last level: after its 4 folds, `P→V` `f_final` (`2^{n_res}` scalars in the clear); grind; `V→P` `t_last` positions; `V→P` `λ_last`; openings; intro; glue; then `n_res` × (`V→P` `r`; `P→V` round polynomial **except after the last `r`**) | step 4 (`B:120`): `f_final`, queries, `λ`, `ν_L` rounds, "`V` closes by evaluating `f̃_final`"; no intro; nothing said about the last message | `:1431-1476` / `:2197-2262` | `:1031-1032, 1065-1074` |
| 13 | terminal check `weight · f̃_final(ρ_tail) = t_r` with `weight = W̃_λ(ρ rotated) + Σ_levels β_i·(induced weight of the level's queries at ρ) + Σ_ood β·eq(z, ρ)` | the closing check of step 4 (`B:120`), the consistency claims being `⟨W_{x_q}, f_final⟩` (`B:120`, Lemma `lem:colweight`) | `:2264-2308` / `induce_sumcheck_evaluate_at_residual`, `whir_induce.rs:228-293` | `:1075-1083`, `_induced_weight`, `:971-989` |

The two verifiers agree with each other message for message (checked by walking
`recursive_verifier_with_basis_succinct` and `verify_whir` side by side; the Python is a
transcription of the Rust). Against Protocol B.6 the deployed schedule differs in four ways:

1. **Per-claim intro messages before the batching challenge.** The spec sends, after `λ_i`, one
   round polynomial `h_1` of the batched claim (`B:111`). The Rust sends a round polynomial *per
   claim* — the residual's (the last fold message), the OOD claim's (`:1206`) and the query
   batch's (`:1406`) — before or after `λ_i` is drawn, and both sides form the batched `h_1` by
   linearity (`RoundQuad::fold`, `:548-554`). Equivalent claims, more prover messages, and two
   verifier challenges in a row (`λ_i` then `r_1`) with no prover message between them: a
   round-by-round analysis must charge `λ_i` and `r_1` as consecutive challenges, which Theorem
   B.7 already does (its batching row and its fold row are separate). Soundness-neutral;
   transcript-relevant.
2. **Grinding.** 17 bits at every level, including the last, ground after the level's root (or
   `f_final`) and before its positions (`whir_config.rs:57-60, 335-336`); `bits = 0` would still
   read a canonical zero nonce (`fs/lib.rs:165-174`). Not in Annex B (the status's S12 records
   it).
3. **The lane relayout.** Level 0 folds the stack's *top* six coordinates (the lane index), the
   later levels the low coordinates of the current fold; the verifier rotates the terminal point
   left by 6 before evaluating `W̃_λ` (`whir.rs:2297-2306`, `py:1079`). Annex B states it only
   in "Optimizations" (`B:380`). The blueprint's Layer 11 says `whirOpen` is "stated exactly as
   Protocol B.1" (`bp:1185`) and nowhere mentions the relayout; a `verify` without it evaluates
   `W̃_λ` at the wrong point and rejects every Rust proof.
4. **The last round message is omitted** (`whir.rs:1471-1475`, `:2256-2261`; `py:1073-1074`):
   the verifier's last running claim is checked directly against `f̃_final`, so the message that
   would carry it is redundant.

Also: the OOD count is one per level `≥ 1` and zero at level 0 (`whir_config.rs:677-684`, `:829-841`;
`whir.rs:1261-1265` "L0 takes no OOD sample"), as Annex B (`B:105` "No OOD sample is taken") and
the blueprint (`bp:1186-1187`) say.

### B.2 The code

- **Field and domain.** Reed–Solomon over `E` with the evaluation domain an `F_2`-subspace of
  `K` (`B:54`, `B:90`); the level-0 word is `K`-valued because the message is (`B:306`; the
  codeword buffer is `ArenaVec<F64>`, `whir.rs:293`, `:364`); deeper levels are `E`-valued
  (`ArenaVec<F192>`, `:397`) encoded with `K` twiddles by the mixed product
  (`whir.rs:17-19`, `whir_ntt_ext.rs`).
- **Basis.** The novel polynomial basis of Lin–Chung–Han on the standard basis `e_c = x^c` of
  `K` (`B:278`, `B:301-306`): `whir_induce.rs:19-21` "Standard basis only (`v_i = x^i = F64(1 <<
  i)`)", `eval_sk_at_vks` (`:32-52`) and `normalized_sks_at` (`:56-67`, `Ŵ_i(x) = s_i(x)/s_i(v_i)`,
  the spec's `Ŵ_i := W_i/W_i(e_i)`, `B:299`); the Python `_subspace_roots` (`py:962-968`). A
  position `q ∈ [0, 2^{κ+ρ})` is the domain point `F64(q)` (`whir_induce.rs:163`, `py:983`), the
  spec's `x_v = Σ_c v_c e_c` (`B:357`). The message is read directly as novel-basis coefficients
  (`B:306`; the encoder is the additive NTT, `ntt::AdditiveNttF64::standard`, `whir.rs:372-373`).
- **The column weight** the verifier evaluates: `Π_k (1 + p_k·(1 + Ŵ_k(q)))`
  (`whir_induce.rs:220-224`, `py:971-977`) — Lemma `lem:colweight`'s `Π((1 + r_i) + r_i Ŵ_i(x))`
  (`B:312`) in characteristic two. Agrees.
- **Rates.** Level 0: `ρ_0 = 2^{−ρ}` with `ρ ∈ [1, 4]` chosen by the prover and announced
  (`whir_config.rs:41-55`, `mod.rs:123, 149, 167`); then the rate exponent grows by
  `k_0 − 3 = 3` after the initial fold and by `k_i − 1 = 3` after each later fold
  (`whir_config.rs:73-78, 298-311`; `py:929`). Block lengths `2^{κ_i + ρ_i}`, all `≤ 2^{28}`,
  within `κ + ρ ≤ 64` (`B:90`).
- **The ladder.** Folds `[6, 4, 4, …]` until at most 5 variables remain (`derive_ladder`,
  `whir_config.rs:260-296`; `py:924-932`): 2 levels and a residual of 5 at `μ = 15`, 6 levels
  and a residual of 2 at `μ = 28`.

### B.3 The parameters

`SECURITY_BITS = 128`, `LOG_INV_RATE_0 = 1`, `MIN/MAX_LOG_INV_RATE = 1/4`, `QUERY_GRINDING_BITS =
17`, `INITIAL_FOLDING_FACTOR = 6`, `SUBSEQUENT_FOLDING_FACTOR = 4`, `RS_DOMAIN_INITIAL_REDUCTION_FACTOR
= 3`, `RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR = 1`, `RESIDUAL_MAX_LOG = 5` (`whir_config.rs:38-86`);
`MIN_MU = 15`, `MAX_MU = 28` (`pcs.rs:49-51`); the Python's copies `py:900-908`. The query counts
per level come from the search of `whir_config.rs:639-707` (F.2) and are tabulated in
`py:910` for every `(ρ, μ)`; the scratch port reproduces the table (H.3). The blueprint's
parameter block (`bp:1157-1165`) lists the six constants and `ladder … -- fold, rate exponent,
queries per level` with `ladder_queries_eq` against `py:910`: right, with two gaps: (a) the
analysis parameter `η_i` (or `m_i`) per level is not a field of `Level`, yet `whirError params`
(`bp:1175`) is a function of `γ_i = 1 − √ρ_i − η_i` and `L_i = 1/(2η_i√ρ_i)`; a Lean `whirError`
needs the `η_i` as data (any admissible value proves the theorem; the Rust's are the
floating-point optimum, `whir_config.rs:624-633`), and acceptance of "128 bits" needs the
specific ones; (b) the OOD count (1 from level 1) and the grinding bits per level are parameters
too.

### B.4 The Merkle trees and the encodings

- **Tree.** Binary, `2^k` leaves, flat layout (`pcs/merkle.rs:11-18`); leaf hash =
  BLAKE2s-256 of the leaf bytes (`fs/merkle.rs:38-41`), node = BLAKE2s-256 of the 64 bytes
  `left ‖ right` (`:44-51`); **no domain separation** between leaves and nodes. Safe because the
  verifier fixes the height (`open`, `fs/merkle.rs:174`: `height = num_leaves.trailing_zeros()`,
  `num_leaves` a function of the announced sizes) and the leaf width (`row_words`, `leaf_words`,
  `:139-148`); a node's 64-byte preimage can only be presented as a leaf of a tree whose height
  the verifier does not accept.
- **Leaf images.** Level 0: `2^6` words of 8 bytes (512 bytes) per position, lane-**descending**,
  the absent lanes a zero prefix supplied by the verifier (`whir.rs:331-345`,
  `pcs/merkle.rs:144-192`, `fs/merkle.rs:53-58`); the words are little-endian `u64`s
  (`fs/merkle.rs:60-67`). Deeper levels: `2^4` elements of `E` as `3·2^4 = 48` words, 384 bytes
  (`whir.rs:461-467`, `ext_row_words`, `:1211-1213`; `py:1049`, `_ext_row`, `:938-940`). The
  comment `whir.rs:393-395` says "one Merkle leaf of `num_interleaved * 16` bytes"; the code
  hashes `num_interleaved * size_of::<F192>() = 24·num_interleaved` bytes (`:463`); the comment is
  stale (a finding against the source, note).
- **Digests on the stream.** A 32-byte digest travels as two scalars, each two little-endian
  words in the low limbs and a zero third limb (`hash_to_scalars`, `fs/merkle.rs:14-20`;
  `py:216-219`); reading rejects a nonzero third limb (`scalars_to_hash`, `:26-36`;
  `py:222-224`).
- **Wire format.** One phase per level: the rows at the *distinct, sorted* positions and one
  "octopus" of siblings (`PrunedMerklePaths`, `fs/merkle.rs:78-92`, `prune`, `:101-136`); the
  verifier rebuilds every path, refuses a missing or surplus sibling, a wrong row count or
  width, an out-of-range position, a root mismatch (`open`, `:163-235`). The raw form
  (`RawMerklePath`, `:246-264`: full leaf image plus full sibling path, one per query,
  duplicates repeated) is what an accepting Rust verifier *emits* (`into_raw_proof`,
  `fs/transcript.rs:198-203`; `mod.rs:702-704, 777`) and what the Python and the recursion guest
  consume (`py:392-404`; the test harness `crates/lean_vm/tests/verifiers/python_verifier.rs:50-80`
  writes it out).

### B.5 What Annex B's soundness theorem says, and on what it rests

Theorem B.7 (`B:139-152`, `thm:rbr`): the scheme is `L_0`-list binding (Definition B.4,
`B:70-72`) and its opening has **round-by-round soundness** (Definition B.5, `B:74-84`) for the
relation `R_open` (`B:133-136`), with the per-message errors of the table `B:141-150`. The model
is the interactive oracle proof: the oracles `C⁽ⁱ⁾` are read at queried columns, the challenges
are uniform, the prover unbounded; the extractor is not named (soundness for a language).
Inputs: the Johnson bound, proved in the annex (`B:391-414`); mutual correlated agreement up to
the Johnson bound, Theorem B.9 (`B:176-185`), quoted from [BCHKS25] Theorem 4.6 and external;
Lemma B.10 (`B:189-198`) turns it into "folding preserves lists" with the `2^{ℓ−1}` union of rows;
Lemma B.11 (`B:200-206`) is the out-of-domain separation. Fiat–Shamir is one sentence (`B:84`).

### B.6 The blueprint's Layer 11 set against it

| Blueprint (`bp:1150-1193`) | Ground truth | Judgement |
| --- | --- | --- |
| `whirOpen (params) : OracleReduction … (StmtIn := Fin J → WeightedClaim μ) (OStmtIn := codeword oracles)`, "stated exactly as Protocol B.1: batch, `ℓ_i` sumcheck rounds, commit, one out-of-domain sample from level 1 on, `t_i` queries, and the final plaintext level" | Protocol B.6 (numbered on the section counter, `preamble/theorems.tex:4, 12`) with the four deployed differences of B.1 | the input type is right (J weighted claims; under (ii) its level-0 batch is the opening phase's `λ`, section A). The relayout, the intro messages and the omitted last message must be pinned as Category B for `verify` to accept Rust proofs; grinding is Layer 12's. "Protocol B.1", "Theorem B.2", "Definition B.1" (`bp:1187`), "Lemma B.7" (`bp:1170`), "Annex B.3" (`bp:278`), "(Annex B.4)" (`bp:1172`) are not the pinned numbers (Protocol B.6, Theorem B.7, Definition B.4, Lemma B.14, §B.5, §B.3); cite labels |
| `whirOpen_rbrSoundness (mca : McaJohnson) : … (whirError params) -- Theorem B.2, per message`; "Its soundness is *round-by-round soundness for the list relation* `relopen`, not knowledge soundness" | Theorem B.7 as read in B.5 | right in kind; `whirError` needs the `η_i` (B.3); the errors are `(J_i − 1)L_i/|E|`, `2L_i/|E| + 2^{ℓ_i−j}ε_i`, `C(L_i,2)μ_i/|E|`, `(1 − γ_i)^{t_i}`, `t_{r−1}/|E|`, `2/|E|` — Layer 10's "`2/|E|` per round" is the tail's value, wrong for the fold rounds (section A) |
| `encode (κ R : ℕ) : Column κ → (Fin (2^(κ+R)) → K) -- additive NTT on the K basis` | the encoder is `Enc : E^{cube} → E^{dom}`, `K`-valued on `K`-valued messages (`B:54, 306`); every level past 0 encodes an `E`-valued message (`whir.rs:419-485`) | **too narrow**: `encode` over `K` serves level 0 only; the deeper levels need the same encoder over `E` (or over any `K`-algebra), and the `K`-valuedness of level 0 is a lemma about it |
| `theorem encode_column_weight (x) : ∃ W_x : Weight κ, ∀ f, encode κ R f x = ⟨W_x, f⟩ -- Lemma B.7` | Lemma B.14 (`B:309-315`): `W_x(u) = Π_i Ŵ_i(x)^{u_i}` and `W̃_x(r) = Π_i ((1 + r_i) + r_i Ŵ_i(x))`, which the verifier computes (`whir_induce.rs:220-224`) | **near-vacuous as stated**: every linear map `K^{2^κ} → K` is an inner product with some cube table, and `Weight` is inhabited by `⟨row, evalMle row, rfl⟩`, so the existential is true of any linear `encode` and says nothing about the novel basis. What Layer 11 needs is the *definition* `columnWeight x : Weight κ` with the closed-form `mle` and the theorem `encode κ R f x = (columnWeight x).pair f`, since `verify` evaluates that closed form |
| `merkleRoot : List (Vector K leafWords) → Digest`, `merkleVerify : Digest → ℕ → Vector K leafWords → Path → Bool`, `blake2sBytes` | B.4 | `merkleVerify` is the raw path (`RawMerklePath::root`, `fs/merkle.rs:252-264`), not the wire's pruned octopus; which one `Proof.merkle : List MerklePaths` (`bp:1209-1211`) holds decides which proofs `verify` accepts (section C). The leaf image order (lane-descending, zero prefix) and the two leaf widths are not stated |
| Tests: `encode` against CompPoly's additive NTT at `κ = 3`; `merkleVerify` on four leaves; honest `whirOpen` at `μ = 4`, rate `1/2`; the parameter tables against `py:910` | | the honest run at `μ = 4` cannot use the production ladder (`derive_ladder` needs `μ > 6` and two levels, `whir_config.rs:266-267, 291-293`; the Rust's tests fall back to `default_config`, `:196-224`); say which shape the toy uses |

---

## C. Fiat–Shamir and the proof object, as deployed

§8.4 of the specification is `TODO` (`08:44-46`); §8.5's "Setup" says only "The Fiat-Shamir
initial state (§8.4) is seeded by the public input, the bytecode and Flock's BLAKE2s R1CS
matrices" (`08:55`). **The Rust is the only source**; the Python is a transcription of it and is
checked against it below (every row agrees unless marked).

### C.1 The chain

| Element | Rust (`fs/lib.rs`) | Python (`py`) |
| --- | --- | --- |
| The primitive `compress(a, b)` on two 256-bit halves | `:18-24`: `BLAKE2s(a ‖ b)` over 64 bytes, the words little-endian — i.e. the RFC compression `F(PARAM_IV, a ‖ b, t = 64, f0 = 1)` from the unkeyed parameter state (`primitives/src/hash.rs:83-87, 209-224`); the chain state is the *first half of the message*, never a BLAKE2s chaining value | `:341-343` `compress(left, right) = blake2s(le bytes of the 8 words)` |
| Tags, lane 3 of the right half | `:36-39`: observe `1`, squeeze `2`, grinding base `3`, grinding nonce `4`; the seeding block has no tag, "its position is its tag" (`:31-35`) | `:335-338` |
| Seed | `cv_0 = compress(iv, public_input)` (`:69-73`); `iv = BLAKE2s("leanvm" ‖ len(R1CS_DIGEST) as u64 LE ‖ R1CS_DIGEST ‖ bytecode_hash)` as four words (`mod.rs:82-93`, `:712`); `public_input` as its four low words, the third limbs dropped (`mod.rs:99-106`) | `:1366-1369`, `:349` |
| Observe `x ∈ E` | `cv ← compress(cv, (x.c0, x.c1, x.c2, 1))` (`:85-87`) | `:353-354` |
| Squeeze | `out ← compress(cv, (0, 0, 0, 2))`; `cv ← out`; challenge `= (out_0, out_1, out_2)` (`:95-99`): the challenge is 192 of the 256 state bits | `:356-358` |
| Grinding base | `compress(cv, (0, 0, 0, 3))`, not written to the state (`:108-110`) | `:380` |
| Nonce bound | `cv ← compress(cv, (nonce.c0, nonce.c1, nonce.c2, 4))` (`:118-120`), on both sides, **also when the check fails** (`:165-174`; status F13) | `:382` |
| Grinding predicate | low `bits` bits of `compress(base, (nonce, 4))[0]` are zero; `bits = 0` accepts only `nonce = 0` (`:47-51`, `:165-174`) | `:381` |
| The honest grind | smallest `u64` nonce, unbounded search (`:126-155`) | not the verifier's |

The blueprint's row *Fiat–Shamir* (`bp:325`) states the tags, the seed and "one squeeze yields
one `E` challenge (three low words)" correctly. It does not say that the step is
`BLAKE2s-256(cv ‖ block)` with `cv` in the *message* and the RFC chaining value fixed at the
parameter state; Layer 12's `FsState.observe … -- lane 3 = 1` (`bp:1204`) and the leanISA row
"`compress` (Layer 1): the compression the transcript, Merkle hashing and the Flock circuit
share" (`bp:216`) invite `F(cv, x ‖ tag, …)` with `cv` as chaining value, which is a different
function. Category B; the transcription must say `hash64 (cv ++ x ++ tag) = compress iv64
(cv ++ x ++ tag) 64 true false` in leanISA's `compress`'s terms (`LeanerVM/Semantics/Blake2s.lean:105`
at `b435631`).

### C.2 The proof object and the stream order

`Proof<M = PrunedMerklePaths> { stream: Vec<F192>, merkle: Vec<M> }` (`fs/transcript.rs:9-12`);
`RawProof = Proof<RawMerklePath>` (`:19`) is what the Rust verifier emits after accepting
(`:198-203`) and what the Python reads (`py:322-330`: a byte file of 24-byte scalars and a byte
file of leaf words followed by sibling digests, no lengths). The blueprint's `Proof` (`bp:1209-1211`:
`stream : List E`, `merkle : List MerklePaths`) cites `transcript.rs:9-19`, which defines both;
`merkleVerify … Path` (`bp:1182`) is the raw shape; the fixture "a proof dumped from the pinned
Rust prover" (`bp:1237-1238`) — the prover emits the pruned form (`ps.into_proof()`, `:138-143`),
the verifier the raw one. Which one `verify` takes is unspecified, and they are not equivalent
as sets of accepted byte strings: (a) the raw form repeats a row for a duplicated position and
carries every sibling, the pruned form dedups and shares (`fs/merkle.rs:69-76, 101-136`);
(b) at level 0 the pruned form carries `n_lanes` words per row and the verifier supplies the
zero prefix (`fs/merkle.rs:53-58`; `whir.rs:2130-2131`), while the raw form carries the full
64-word image (`py:1049`: `lanes if level == 0 else 3 * lanes`) and **the Python does not check
that the prefix is zero**: run standalone on an adversarial raw proof it accepts a commitment
whose absent lanes are nonzero (soundness-neutral, section D, check M2; a divergence in accepted
sets nonetheless). A choice must be made and named: the pruned wire format is "what the Rust
prover emits"; the raw one is what the recursion guest verifies.

The stream, in order (`mod.rs:711-769`; the phases' internals are in the sibling dossiers):

| # | Scalars read (`P→V`, each absorbed as read) | Squeezes (`V→P`) | Source |
| --- | --- | --- | --- |
| 1 | seed | — | `mod.rs:712` |
| 2 | 8: `κ_mem, τ_0..τ_5, ρ` | — | `mod.rs:144-149`; `py:1372` |
| 3 | 2: the commitment root | — | `mod.rs:714`, `pcs.rs:136-138`; `py:1382` |
| 4 | bus: 2 roots; per GKR layer the round polynomials and children | `α` (4), `β`, per layer the combiners and the two combination challenges; then 5 boundary evaluations read | `gt-bus` A.3–A.4 |
| 5 | table sumcheck: `τ_max` round polynomials (3 scalars each), then 104 column values | `ξ`, then `τ_max` challenges | `gt-table-pub` A.1 |
| 6 | 2: `c_0, c_1` | `r_pi` first | `mod.rs:745-749`; `py:1398-1399` |
| 7 | Flock: zerocheck and lincheck messages | their challenges | `gt-flock-ring` §2.2 |
| 8 | — | 6 ring-switching challenges | `stack_open.rs:394`/`:513`; `py:1343` |
| 9 | — | `λ` | `stack_open.rs:400`/`:518`; `py:1361` |
| 10 | WHIR: as B.1 rows 1–13; Merkle phases on the side channel, one per level | as B.1 | `whir.rs:2087-2308`; `py:1006-1087` |
| 11 | `vs.finish()`: the stream and the phase list fully consumed | — | `mod.rs:769`, `fs/transcript.rs:213-219`; `py:1414` |

What is absorbed before each challenge is therefore: everything read from the stream before it
(including the grinding nonces, with tag 4) and every earlier squeeze (which ratchets the state),
and **nothing else**: the Merkle openings are never absorbed (`fs/transcript.rs:225-228`), the
derived coefficient of a round polynomial is never absorbed (`:56-62` "Binding it would add
nothing"), the table sumcheck's target is never sent (`gt-table-pub`), the program enters
through its hash and the public input through its four low words at the seed. A challenge is
a function of (statement, sizes, all scalars so far, the count of squeezes so far).

### C.3 The encoding of round polynomials

`add_round_poly(coeffs, eq)` sends every coefficient but one, "constant first" (`fs/transcript.rs:56-71`):
with `eq = false` it drops `c_1`, with `eq = true` it drops `c_0`. `next_round_poly(n, claim, eq)`
(`:289-309`) reads the others in index order, derives the missing one — `c_1 = claim + Σ_{i≥2} c_i`
for a plain round (`h(0) + h(1) = claim` in characteristic two), `c_0 = claim + r·Σ_{i≥1} c_i`
for a round whose `eq` factor `r` the verifier holds — and binds the read ones. The Python
`sumcheck_round_poly` (`py:406-413`) is the same. WHIR's rounds are plain and quadratic: two
scalars `(c_0, c_2)` per round (`whir.rs:509-522`; `py:1012`). The blueprint's row *Sumcheck
messages* (`bp:315`) and acceptance test 8 (`bp:1287-1289`: "`decode` reconstructs `c_1`") state
this for the table sumcheck; `RoundPoly.decode (d) (claim) (eq? : Option E)` (`bp:1212`) has the
right signature. Consequence for the oracle protocol: the round identity is not a check in the
deployed verifier (`gt-bus` B15, `gt-table-pub` "three and none on the wire"); the oracle
protocol's explicit check is what `decode` makes true by construction.

### C.4 The blueprint's Layer 12 set against it

| Blueprint | Judgement |
| --- | --- |
| `FsState` with `seed`, `observe`, `sample`, `grind` (`bp:1202-1206`) | right shape; `grind (bits) (nonce) : FsState → Bool × FsState` must bind the nonce whether or not the check passes (`fs/lib.rs:165-174`), and `compress` must be the 64-byte hash (C.1) |
| `Proof` (`bp:1209-1211`) | which Merkle format (C.2) |
| `RoundPoly.decode` (`bp:1212`) | right |
| `verify … phase by phase in the stream order of the conventions` (`bp:1230`) | the conventions' rows do not give the WHIR-internal order (B.1) nor the Merkle side channel |
| `verify_iff_compiled` (`bp:1218-1221`) | section E.4 |
| Tests: six mutations, "a flipped stream scalar in each phase, a wrong Merkle sibling" (`bp:1238-1239`) | add: a nonce that fails the grind; a nonzero third limb in a root; a nonzero upper limb in a size; an extra trailing scalar; an extra sibling; a level-0 row of the wrong width (`gt-bus` G9 asks for three of these) |
