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
