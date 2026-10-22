# End-to-end security of leanVM aggregation — framework (final, converged)

(History: `e2e-security-history/v1.md` … `v7.md`, each recording what its review round found. Paper:
Chiesa–Guan–Samocha–Yogev, "Security bounds for proof-carrying data from straightline extractors",
ePrint 2023/1646;
repo `lean_vm`; guest
`.leanvm/crates/rec_aggregation/guests/lean_ethereum.py` at `leanvm-rev`.)
Review rounds: 1 (4 reviews, 4 fatal), 2 (3, fatal), 3 (3, fatal), 4 (3, no fatal), 5 (2: one
"converged", one red team with text-level serious items only), 6 (1: one serious accounting item,
no fatal), 7 (1: converged, minor items only, applied here).

## 0. The claim
Random-oracle model, one byte-level oracle H : Bytes → Digest shared by all parties. A static set of
n_x leanXMSS and n_s leanSPHINCS honest keys, signed by the deterministic Lean signers through
signing oracles that enforce no leaf reuse (leanXMSS `Valid`, `LeanXmss.Security`) and
`signatureLimit` per key (leanSPHINCS, endpoint `Sphincs.Lifetimes.requestedSecurity`); every returned
signature re-verified with visible queries. For every adversary with coins whose VISIBLE hash queries (its own, re-verifications, and V_I's —
V_I running under a query budget Bud fixed before the game, e.g. 2^80) number ≤ Q_v, making S_x, S_s
signing requests, with E the explicit extractor (reads only the final visible log vis_final and Π):
  Pr[ V_I^H accepts a root statement s and either
      (forgery) s's leanXMSS (resp. leanSPHINCS) claim list contains (pk_j, m) for an honest key j of
        that scheme, and no request for m to signer j was answered; or
      (DA) for a root DA claim (r, v), E(vis_final, Π) outputs no codeword rows R (1 ≤ |R| ≤ 1024, rows
        of length 2^15, as in `Witness.Opens`) such that every hash of
        `commitCodewordsWith (daHash (look vis_final)) pc pr R` is answered by vis_final and equals r, and
        `vectorDigestOf r = vectorDigest (membershipVector r)` is answered by vis_final and equals v ]
  ≤ κ_V°(Q_v) + κ_batch(Q_v) + (Q_v+1)²/2^193 + ε_signer + (n_x+n_s)·(Q_v + Q_sig′ + c)/2^127 + ε_DA,
with closed forms:
  κ_V°(q) = (q+13213)(2^-128 + 5(q+13213)/2^256);  κ_batch(q) ≤ (q+QV_b)(3/|E| + failBound), |E| = 2^192;
  ε_DA ≈ Q_v·14/2^192 (`checker_sound`; the root precedes the challenge chain by `lt_of_rootOf`, the
    root being observed as two 16-byte halves);
  κ_batch's failBound = (4 + |seed steps|)·N/2^256 and QV_b = the batching program's query bound
    (`batchQueryBound`, Guest/Batch/Rom.lean);
  ε_signer ≤ Q_v·(3+2)/2^128 + (S·2^8.1)³/2^258.6 (k ≤ 2 except 3-collisions among the ≈ S·2^8.1
            128-bit halves actually revealed in signatures)
            + Q_v·Q_sig/2^255 (Hit, HiddenPredict, HiddenCollide) + n·2^45/2^256 (Format)
            + n·Q/2^256 (GuessS) + n/2^128 (constant-prefixed transcript starts) + n²/2^128 (key
            coincidences in the simulation);
  c = the maximal cost of the scheme game's final verify;
  Q_sig = the honest signers' total cost in the joint game (keygens + signings, worst case:
    2^23.7 / 2^34 per keygen, 2^33 / 2^34.3 per signature for leanXMSS / leanSPHINCS);
  Q_sig′ = the cost charged in reduction j = key j's keygen + its S_j signings. Reduction j answers
    every oracle input attributable to another honest key i ≠ j itself, by lazy sampling with private
    coins (free in `countedOracle`, `unifFwdImpl`): the P_i‖…-prefixed inputs, the seed derivations
    "leanXMSS"/"leanSPHINCS"‖S_0^i, and the parameter derivation 0‖param‖S_i (both schemes prefix every
    other input with P‖A); it forwards P_j-prefixed inputs and everything else. A perfect simulation of
    a random function, failing only if the owned set meets key j's hidden inputs: P_i = P_j, P_i = 0^16
    (the parameter inputs' prefix), P_i equal to the first 16 bytes of a seed input of key j, or seeds
    of distinct keys coincide (≈ 3(n−1)/2^128 per reduction, ≈ n²/2^128 in total, added to ε_signer). Repeated leanSPHINCS requests are answered from the reduction's cache
    (`Seeded.sign` is deterministic) or counted as the single-key log counts them (`log.length`).
No factor in the number of nodes or depth beyond Q_v; note Q_v includes V_I's queries, i.e. under §5
the adversary's own proving work, which grows with the tree.
Deployed security level (bits) ≈ min( 127 − log₂(n_x+n_s) − log₂(Q_v + max_j Q_sig′_j + c),
                                     ≈126 − log₂ Q_v,  193 − 2·log₂(Q_v+1),
                                     −log₂ ε_signer ),
ε_signer being dominated by the others at deployed parameters (its largest terms ≈ 5Q_v/2^128 and
(S·2^8.1)³/2^258.6). Examples: one slot, Q_v = 2^64, 2^20 keys: ≈ 2^-43. Lifetime, 2^20 validators ×
2^24 slots (S ≈ 2^44; S_j ≤ 2^24, which for leanSPHINCS needs the `full` or `pruned20` parameter
sets): forgery term ≈ 2^20·(Q_v + 2^58.3)/2^127, i.e. ≈ 2^-48.7 for Q_v ≤ 2^58 and ≈ 2^-43 at
Q_v = 2^64; every other lifetime term ≤ 2^-67; termination caps at 193 − 2·log₂Q_v.
(leanXMSS costs re-derived in review: keygen ≈ 2^23.7, signature ≈ 2^33.01; leanSPHINCS constants
2^34 / 2^34.3 to be re-derived when written up.)

Heuristic (single, outside Lean): §5.

## 1. Decisions
D1 byte-level H (not ideal compression). D2 deployed guest bytecode and proof format unchanged.
D3 V° = `verifyExecution` with the bytecode value `.computed` and the Flock terminal `require`
   (Verifier.lean:1990) deleted; deferred acceptance with a true bytecode claim ⇒ V°; deployed ⇒ V°.
   `OuterChecks°` = DA vector digests ∧ bytecode part of `DeferredClaim.Holds`.
D4 standard-chain rule over the executed BLAKE2S instructions of the decoded image (canonical cells;
   padding/inactive rows excluded); TableOK^H: every standard chain of x ends at H(x); precheck:
   reject active non-final rows with distinct inputs and equal outputs (bounds chain enumeration;
   honest pass).
D5 constants as parameters: batching start s0, DA padding (pc, pr) via `commitCodewordsWith`;
   `NodeRel`'s seed `fiatShamirIvWith H`; `paddingInstance` concrete (bus-pinned, inactive).
   Constants-audit lemma: baked digests enter only as data (IV/MD_FINAL as chaining value and
   metadata, s0 as a Fiat–Shamir start, pads as leaves, `paddingInstance` on inactive rows), never
   compared with a chain output.
   Precheck "distinct" = distinct row INPUTS with equal outputs (identical multi-block hashes repeat).
D6 every bad event is one event over the visible log, charged per visible query.
D7 claims are the root statement's, in the claim list of their scheme (both schemes' keys are
   16+16 bytes: consumers must check a claim's scheme); followed down `Holder.child` (finite by T3) to `.direct`; DA
   pairs are copied down unchanged (`cover_da_root`), so the root's pinned vector covers them.
   "Backed" never mentions a row count (deployed padding = H(zero) collides with a zero row).

## 2. V_I (algorithm; non-succinct; not flattening; budget B)
Idealized proof Π = (s, π, M, F), M: roots ↦ level-0 words, F: roots ↦ the frames the decoder
reads (E2E-5, §7). V_I^H(s, Π), fuel-bounded, rejecting once
Bud queries are used (Bud fixed before the game; Bud only makes QV uniform, it adds no term — every
V_I query is a visible query charged in κ_V°'s failBound):
1. PI₀ := statementDigest^H(seed^H, s); require V°^H(guest, PI₀, π) and OuterChecks°^H(s).
2. N := closure of {(guest, PI₀, π)} under: q ∈ Cand(M(r(π))) with M3Holds°(x, q), child (s_c, f_c, π_c)
   of decode_{F(r(π))}(image q) ⇒ (guest, statementDigest^H(seed^H, s_c), π_c) ∈ N.
3. For every ν ∈ N: M(r(π)) defined, well shaped, MerkleRoot^H(M(r(π))) = r(π); for every
   q ∈ Cand(M(r(π))) with M3Holds°(x, q): precheck and TableOK^H(activeRows q).
Completeness for exact codewords: thr = ⌈johnsonAgreement·n⌉ > √(Dn) ≥ √2·D ⇒ unique candidate.
Noisy words admitted (proximity soundness stays inside the theorem).

## 3. Honest-signer game, visible log, events
Visible log = first visible occurrences in time order (adversary's queries, re-verifications, V_I's);
signers' queries hidden, counted in Q_sig. Extraction and consistency read the final visible log
vis_final (forged-signature chain rows become visible only through V_I's TableOK queries, so T4 is
evaluated on vis_final; V_I's fresh queries are charged like any visible query — no separate bridge
beyond the budget term).
Engine: the VCVio potential engine extended with (1) coins forwarded (lookup none, record id, not
counted), (2) hidden fresh queries (visible state unchanged), (3) state-changing visible hits on hidden
entries (not lazy steps), (4) a stopped potential Φ′ = Φ(vis)·1[¬Bad] with "appending a non-record,
non-failing entry leaves pot unchanged", and a separate bound on Pr[Bad] via per-scheme deferred-sampling
game hops (sampling the output bits the signer never read: upper half of truncated hashes; all but
bits 128–153 of leanSPHINCS grinding attempts, conditioned on ¬Landed).
Bad = LateReveal ∨ Hit ∨ Format ∨ HiddenPredict ∨ HiddenCollide ∨ GuessS (generically: a hidden
entry, when it becomes visible, is a `BadEntry` for the visible log before it — including the
seeding-predecessor clause, Log.lean:156-160):
- LateReveal: a visible input references (chunk 0/32, `RootOf`) the output of a hidden entry made
  visible later; ≈ Q·(3+k)/2^128 with k the number of hidden entries sharing 128 known bits; chain-start
  derivations (fully revealed when both digits are 0) are covered by GuessS (their input contains S).
- Hit: a visible FS/PoW/DA-challenge query answered from a hidden signer entry (inputs separated by
  their first bytes: H-output state / s0 / DA label vs P‖A).
- Format: a revealed scheme entry parses as a leanVM record (64/80/96-byte overlaps) ≈ n·2^45/2^256.
- HiddenPredict: a hidden fresh answer equals a chunk of an earlier visible input, later revealed:
  Q_hidden·2Q/2^256. HiddenCollide: hidden/visible output collisions. GuessS: ≈ Q/2^256 per key.

## 4. Theorem chain (Lean)
T1 universal KS for V° and the bytecode-only batching (cache form, from `final_ineq`), in the engine
   of §3.
T2 guest in cache form over a `HashModel` typeclass: consistent table ⇒ `NodeRelWith look_vis`
   (signatures/DA "answered and true" via Option runs), children accepted by
   `verifyDeferredWith look_vis`.
T3 termination: rank = log index of the statement-bytes entry; child edge via `RootOf`+¬Fail,
   `lt_of_chunk`, ¬Pred96; term (Q_v+1)²/2^193.
T4 aggregate knowledge on vis_final: V_I accepts ⇒ every root claim reaches a direct witness valid
   ("answered and true") under vis_final, and every root DA claim has E's codeword rows, except
   κ_V° + κ_batch + T3 term + ε_signer + ε_DA.
T5 no forgery: per honest key a black-box reduction to `LeanXmss.Security.leanXmss_security` /
   `Sphincs.Lifetimes.requestedSecurity` (lemmas: Option-run = lazy-oracle run of the monad-generic
   `Concrete.verify`; Digest ≃ BitVec 256 transport via `blake2sBits`'s bijection, also in T2/T4's
   lookups; key generations commute; repeated XMSS leaf refused without forwarding; leanSPHINCS
   `Params` from `requestedSecurity`, deterministic `Seeded.sign`, `keygenFromSeed`); hybrid over keys
   (union bound; reduction j self-simulates the other keys' oracle inputs, §0);
   DA leg with its own ROM proof (`checker_sound`, NTT lemma `membershipVector = dual`,
   DA `BadEntry` clause).
T6-det completeness (non-vacuity): for every H and every honest witness tree within limits, an explicit
   honest I(H) prover's output is accepted by V_I^H, under the good events "every PoW search finds a nonce
   within fuel" and "the matrix-batching weights are not both zero", and the hypothesis that V_I's
   queries on the honest tree are ≤ Bud. Prover: BLAKE2S outputs filled by a
   stateful rule (fresh never-issued intermediates recorded with their prefix; finals H(prefix‖tail);
   other rows fresh unrecorded); Flock round messages sumcheck-consistent (the prover
   picks vA, vB, vC), true slices (ring switching binds
   them); child `matrixValue` hinted to close the in-circuit terminal; matrix batching closed by
   `a_star`/`b_star`; root matrix claim dropped. Needs gen° (the Flock-region generator writing all 18
   limbs into their slots, `slots_gen°` unconditional) and the guest's completeness under H.
T7′ sanity: deployed checks accept, M covers every reached root, every reached candidate satisfying
   M3Holds° also satisfies the full `aux`, no two active non-final rows with distinct inputs have equal
   compression outputs, V_I's cost ≤ Bud ⇒ V_I^{BLAKE2s} accepts.

## 5. Heuristic, stated
Concrete refutable conjecture (signatures only): for every adversary against the deployed
`verifyAggregate` with honest signers, making ≤ Q_v BLAKE2s compression evaluations itself and in the
verifier (in-circuit included) and S_x, S_s signing requests (signers' cost Q_sig′ as in §0),
Pr[the root statement contains a claim (pk_j, m) for an honest key j of its scheme with no answered
request for m] ≤ the §0 bound (without the DA term). DA is not in the conjecture: under fixed BLAKE2s
an existential "unbacked root" is near-never true and a knowledge form is not refutable; a DA
statement for the deployed system, if wanted, is a falsifiable consistency game (after acceptance the
adversary answers cell-sampling queries against r and wins if its openings are inconsistent with every
codeword matrix, or two reconstructions differ — leanDA's position/code binding).
Scope: (a) BLAKE2s ≈ RO natively, (b) Fiat–Shamir for in-circuit-verified proofs, (c) Flock's R1CS +
batched matrix claims ≈ oracle-consistent rows, (d) in-circuit chains ≈ visible queries.
KRS-type attacks: no challenge is squeezed before `commitStack` (Verifier.lean:2114, stack committed
once in full: self-prediction needs a hash fixed point); `fs_seed` is pinned (statement digest, outer
verifier, copied to children); the program is pinned by the batched bytecode claim; in-circuit
batching is ordinary FS over prover inputs. Caveats: CGH04, BBHMR19, the paper's "formally distinct"
(§1.1.2, §2.3); static corruption only (the union-bound form extends to adaptive corruption except the
hidden-S events).
Unconditional today, without the heuristic: the root-level statement `aggregate_sound_outer` (validity
under concrete BLAKE2s with a classical extractor; NOT a no-forgery statement).

## 6. Work packages (estimates from rounds 2–4)
W0 build split, HashModel, `…With` spec (1.5–2.5k) · W1 Flock-blind KS for V° (3–5k) · W2 B2/B1 over
HashModel for soundness AND completeness (2–3k + ~330 files threading) · W3 Option run layer (2–4k) ·
W4 B1 consumers (2–4k) · W5 universal corollaries, T3 (2.5–4k) · W6 bytecode-only batching, constant
start (1k) · C5 chain lemma (0.6–1k) · V_I + budget (1–2k) · E engine extension + signer events
(4–8k) · E reductions, transport, hybrid with self-simulated other keys (2.5–5k) · E5 DA ROM proof incl. NTT (3–7k) · T6-det (6–13k,
shares W2) · T7′ (1–2k) · constants audit (0.3k) · assembly (1.5–2.5k).
Total ≈ 35–65k lines. Critical path: W0 → W2 → W3 → C5/W5 → T4 → T5; T6-det in parallel after W2.

## 7. Decisions taken during implementation
The W-decisions change how a work package is realised, not what is proved; the E2E-decisions change
the statement, each with its reason.
- **W0-1 (generic definitions in new modules).** The hash- and semantics-generic definitions live in
  new modules that import the deployed ones — `Spec/IsaWith.lean` (`BlakeSem`, `blakeDeployed`,
  `blakeFree`, `executeWithB`, `runB`, `ValidExecutionB`), `Spec/NodeWith.lean` (the `…With`
  digests, signature verification, batching from a start state, `NodeRelWith`), `Spec/DaWith.lean`,
  `Spec/Ideal/*` — with bridge lemmas to the deployed definitions (`validExecutionB_deployed`,
  `statementDigestWith_id`, `batchWith_id`, `commitCodewordsWith_id`, … mostly `rfl`), instead of
  redefining the deployed ones as abbreviations of generic ones. Why: the deployed `Spec/Isa.lean`
  and `Spec/Node.lean` are imported by ~2,500 modules; adding beside them rebuilds nothing and keeps
  every existing theorem and test unchanged, which is the plan's intent.
- **W0-2 (DA transcription).** LeanDA's algorithms are pure in the hash; their monadic forms
  (needed for "every hash answered by the log") are transcribed in `Spec/DaWith.lean` with the
  padding digests as parameters (D5), proved equal to LeanDA's at `Id` and the deployed padding.
  `lean_da`'s algorithms are unchanged (`LeanDa/Dual.lean` adds the NTT lemma E5 needs).
- **W0-3 (where the statement lives).** `V_I` needs the Johnson-list candidates (Protocol), the
  leanISA constraints (Arithmetization) and the guest's decoder (Guest), which `Spec` may not
  import. The parts expressible in `Spec` are there (`Spec/Ideal/Blind.lean`: V°;
  `Spec/Ideal/Table.lean`: rows, standard chains, `TableOK`; later the game and the forgery event);
  the composed statement of `aggregate_no_forgery` is a definitions-only module above them.
- **W0-4 (build split).** `Guest/ExpTables.lean` holds `B1.ExpTables`, so the shared check context
  `Glob` (and through it the 375 kernel-checked `Guest/Checked` files and the generated data) no
  longer imports the guest's proofs (`B1`, `Value/Hash`, `Value/Cells`, `Value/FiatShamir`).
- **W0-5 (the hash model).** `Guest/Value/HashModel.lean`: a `HashModel` has the `BLAKE2S`
  relation `sem`, an *answered* hash `H : List UInt8 → Option Digest` (deployed: `some ∘
  blake2sBytes`; oracle: the log's lookup), a prefix relation and four laws: checked cells are
  canonical (the guest reads range facts off `BLAKE2S`), the empty prefix is the IV, a non-final
  block extends a prefix, and a prefix's final block gives `H x = some d` with the output the
  digest's cells. One answered hash (rather than a total hash and a "known" predicate) makes the
  guest's conclusions the `…With` statements at `M.H` directly (`NodeRelWith`).
- **E2E-1 (all queries charged; the visible-only accounting deferred).** The first theorem charges
  every oracle query: the adversary's, the honest signers' (keygens and signatures) and V_I's, in
  one logged random oracle (`LeanVM/E2E/Statement.lean`, `hashQuery`). So T1–T4 and E5 run in the
  existing potential engine (`LeanVM/Protocol/ToVCVio/Rom/`) with the signers as part of the
  query-bounded computation, the extractor reads the oracle's whole final log, and the game needs
  no hidden queries, no re-verification and none of §3's bad events (LateReveal, Hit, Format,
  HiddenPredict, HiddenCollide, GuessS); the per-key reductions of T5 are as designed (key j's
  inputs forwarded, the other keys' self-simulated), with their n²/2^128 simulation term. The
  bound becomes §0's with `Q = Q_v + Q_sig` in κ_V°, κ_batch, the termination term and ε_DA.
  Why: the engine extension of §3 (stopped potential, deferred-sampling game hops per scheme) is
  the largest and riskiest package (4–8k lines) and buys only the difference between Q_v and
  Q_v + Q_sig. Per slot that difference is negligible (Q_sig ≈ 2^20 · 2^33 = 2^53 against
  Q_v = 2^64); over a lifetime (Q_sig ≈ 2^77) the termination term (Q+1)²/2^193 weakens from
  about 2^-65 to about 2^-39, above the forgery term's 2^-43. The visible-only accounting,
  with §0's sharper bound, stays a later strengthening on top of the same chain (package W-vis:
  §3's engine extension, re-verification, an extractor of the visible log).
- **E2E-2 (the statement's module, and what it fixes).** `LeanVM/E2E/Statement.lean` defines V_I
  (`idealVerify`, a monad-generic algorithm on `fuel` nodes), the game (`gameComp`, an oracle
  computation over coins and the hash, run against `Rom.loggedRO` by `game`) and the events
  (`Forged`, `DaBacked`, `Breaks`). Codewords are stated as `LeanDa.encodeRow`'s range (lean_da's
  `rsCode`), a signing request as a leaf index and a message, and the DA padding digests are the
  deployed constants (`deployedPads`, D5). The closed-form error and `aggregate_no_forgery` itself
  are added to this module when the chain is proved, the error at the constants the proofs give
  (E5's DA term, for one: `Q · (14/2^192 + 4Q/2^256)`).
- **W1-1 (the blind instance).** V°'s certificate reuses the deployed bus, table and public-input
  phase specifications at `leanIsaWith F prog s none` (`Front/InstanceWith.lean`), the leanISA
  instance with no Flock region, whose `aux` holds of every stack; at the deployed region it is
  `leanIsaInstance` by `rfl`. The leanISA facts behind those specifications were generalized over
  the region (rather than the instance dropped from them: the bus's types are indexed by the
  instance, so the deployed facts do not carry over by unfolding). Flock and ring switching are
  phases that keep the doom on the earlier claims at no error (`Spec.keep`).
- **W2-1 (the guest's semantics: parallel `…B` modules).** The B2 soundness chain has generic
  copies over `S : BlakeSem` (`Guest/CoreB`, `LogicB`, `ExecB`, `CoreLocB`, `CheckSoundB`,
  `SoundB`), each recovering the deployed one at `blakeDeployed` (`relB_deployed`, …), instead of
  `Core`/`Logic`/`Exec`/`CheckSound` made generic in place. Why: those modules are imported by the
  generated kernel-checked families (1,770 modules of 2–5 GB); an in-place edit rebuilds them all,
  the copies rebuild B1 only. A function free of `BLAKE2S` has its deployed relation under every
  semantics (`relB_iff_rel_of_freeOn`), so its B1 lemmas carry over unchanged. The plan for the
  rest of B1 is `w2-guest-model.md`.
- **W6-1 (the constant start, the bytecode part).** The batching's start `s0` is data (D5), no
  oracle answer, and the random-oracle theorem's decoder starts a chain only at a seeding's last
  answer (`Seeds.first_len`): a constant start is never decoded, and an answer equal to `s0` (a
  collision with a constant the adversary knows) is not in `Fail`. So the batching leg reads the
  log as the one where the label's hash is `s0` (`startLog s0 ℓ`, `LeanVM/E2E/Batch.lean`: the
  entry `(batchLabel, s0)` first, the log's own label entries dropped), which agrees with the log
  on every chain input and whose failure adds exactly the collisions with `s0`; the deployed
  seedings `batchSeeds` then apply unchanged. The program certified (`bytecodeAny`,
  `LeanVM/E2E/Batch/Prog.lean`) is the batching cut after the bytecode's sumcheck, its final
  check against the bytecode's own value: the bytecode side is sound alone (separate lambdas,
  separate sumcheck), and the cut program reads no final value, so every hash it makes is one
  `batchWith` makes. The potential `batchPot` covers every batching instance (child counts below
  `2^64 - 1`) at once; `κ_batch` is `Q · (2/|E| + 4(Q+1)/2^256)` (the batching's queries are the
  game's, E2E-1; no `QV_b`).
- **E2E-3 (V_I's decoder).** The deployed decoder `End.decode` locates each callee's witness at
  the first memory frame whose code holds under the *deployed* semantics; under another `BLAKE2S`
  semantics the frame a located call ran at can differ, so T2 cannot hold with `decode` (found by
  W2's Main/End assembly). V_I decodes a candidate with `End.decodeB (tableSem rows)`
  (`Guest/EndKnowB.lean`): the same hash-free decoder with frames chosen under the candidate's
  own table semantics, which is the oracle model's (`HashModel.oracle`), and `decode` again at
  the deployed semantics (`decodeB_deployed`). T2 is `guest_knowledge_model` with this decoder.
  (Refined by E2E-5: V_I decodes at the frames the idealized proof names, `End.decodeAt`.)
- **W5-1 (T3's measure and event).** The rank of a node is the log index of the entry answering
  its statement digest. A child's digest is observed by the parent's batching as two halves; the
  entry observing the second completes it as a root (`RootOf`, `lt_of_rootOf`), and the chain's
  later entries follow (`lt_of_chunk`, `ChainLE`), to the matrices' sumcheck, whose last
  challenge is the parent's last deferred matrix coordinate. The parent's statement bytes carry
  it at the fixed offset `predOffset bytecode` (byte 1296 for the guest, by
  `DeferredClaim.Shaped`); the event `Pred o ℓ` (an input carrying, at offset `o`, the 24 bytes
  of the challenge of the same or a later entry's answer) is T3's bad event, of probability at
  most `Q (Q + 1) / 2^193` (`LeanVM/E2E/Termination.lean`, `prEvent_game_pred_le`), with the
  potential `ind Pred + Σ_{|ℓ| ≤ k < Q} (k + 1)/|E|`. V_I's closure needs no change: an
  accepted closure finished, and its `done` skip only shares checked nodes (`closure_checked`).
  T4 (`LeanVM/E2E/Knowledge.lean`, `aggregate_knowledge_cache`) takes W2's callee facts at the
  log's oracle models as a hypothesis and the cache form of V_I's acceptance
  (`idealVerify (look ℓ) … = some true`); the step from the game's own run of V_I (against
  `budgetedQuery`) to that form is not yet proved.
- **T6-1 (the guest's completeness over a model; T6-det's size).** The guest's completeness under
  the honest table semantics cannot be transferred from the deployed one: a BLAKE2s execution's
  chains end at `blake2sBytes`, not at the oracle, and no fixed compression function chains to an
  arbitrary `H` on every string (pigeonhole on prefixes). So it is re-proved over a *completeness
  model* (`CompModel`, `LeanVM/E2E/Complete/Model.lean`), the dual of W2's `HashModel`: it builds
  the rows of every answered string. This puts T6-det at about 32–50k lines rather than §6's
  6–13k (plan and decomposition: `t6-completeness.md`). Two findings on V_I there, each fixed by
  a decision below: E2E-4 (a good event, distinct honest commitment roots) and E2E-5 (the
  idealized proof names the decoder's frames).
- **T6-2 (L17 as a count on the node's log).** T6-det's limits carried L17 as `NodeSupport`, an
  existential: some list `D` of fewer than `2^64` block prefixes on which the node's checks,
  answered there alone, still hold. It is now reduced to a plain count on a defined log:
  `nodeLog H s w` (`LeanVM/E2E/Complete/NodeLog.lean`) runs the node's `…With` checks (statement
  digest, children's digests and deferring verifiers, the held signatures, the DA openings, the
  batching) in a logging monad, and `nodeSupport_of_count` gives `NodeSupport` from
  `(prefixesOf (nodeLog H s w)).length < 2^64`; `HonestTree.WithinLimits'` and
  `idealVerify_complete''` (`TreeLog.lean`) state T6-det with that count in place of the field.
  **The count is now a theorem** (`l17-count.md`): `nodeLog_count_lt`
  (`LeanVM/E2E/Complete/Count/Node.lean`) proves it from `End.Limits s w` and the node relation
  `NodeRelWith (some ∘ H)`. A string of at most 64 bytes has no block prefix, and every
  Fiat–Shamir step, proof of work, Merkle node and batching step hashes exactly 64 bytes, so the
  count is that of the long strings only: the statements' lists and cells, the leaves a child's
  deferring verifier opens (at most 368, of at most 192 words: `LeafBound`, a cost predicate on the
  verifier language, `Count/Prog.lean`, `Count/Whir.lean`), the signatures' fixed-size queries
  (`Count/Xmss.lean`, `Count/Sphincs.lean`) and the DA openings (`Count/Da.lean`). The sum is below
  `2^38`. `Limits.stream` and `Limits.stackLog` are not needed; the DA openings' shapes and the
  deferred claims' cells come from the node relation, which holds at every node of a valid honest
  tree (`nodeRel_honest`). So `idealVerify_complete_final` (`Count/Final.lean`) is T6-det under
  `HonestTree.WithinLimitsBudget`: the deployed limits and budget, with no count.
- **E2E-4 (distinct honest roots).** `nodeStep` finds a node's word by its stack root, first match;
  for an `H` making two honest stack roots of different shapes equal, V_I takes the wrong word and
  rejects, so T6-det as designed is false. T6-det adds the good event `RootsInj ip` (the idealized
  proof's roots name one word each), of probability one minus the honest tree's collision
  probability under the random oracle. V_I is unchanged.
- **E2E-5 (V_I decodes at the frames Π names).** An idealized proof also names frames
  (`IdealProof.frames : E × E → String → List E → Option ℕ`, by the node's stack root, the callee
  and its argument words); V_I's `nodeStep` decodes a candidate with
  `End.decodeAt (tableSem rows) (ip.frames r)` (`Guest/EndKnowB.lean`): a located call at the
  named frame when the callee's code holds there under the table semantics, else at the first
  such frame (`Located.frameOfB S fr`, `Located/BasicB.lean`). Why: the first frame is not
  provably the honest call's frame (no frame below it may satisfy the callee's whole body on the
  same words, a property of the whole honest memory), so the honest prover could not show V_I
  follows its children's proofs (`t6-completeness.md` §2.2). T2 holds unchanged in substance:
  every decoded witness comes from a frame where the callee's code holds (`frameDecB_spec`), so
  `guest_knowledge_model_at` holds for `decodeAt M.sem fr` at every `fr` (the `Located/*B`
  decoders take the chooser as a parameter), and `guest_knowledge_model` is its corollary for
  `decodeB S = decodeAt S (fun _ _ ↦ none)`, which is `decode` at the deployed semantics
  (`decodeB_deployed`). The open callee `open_stacked` of `GuestHypsM` is stated at the openings
  decoded at every chooser; at the deployed model that is `wOL_spec`'s proof at the named frames
  (`wOLB_spec_deployed`). T4 uses T2 at the chooser `ip.frames r` of the node's root; T6's
  `nodeStep_honest` takes the chooser the idealized proof names for the honest node's root.
- **T5-1 (T5 through the schemes' multi-user games).** T5 (`LeanVM/E2E/NoForgery.lean`,
  `aggregate_no_forgery`) reduces to `LeanXmss.MultiUser.HasMultiUserSecurity` and, for any `ε`,
  `Sphincs.Security.Multi.HasMultiUserBound n_s ε`, one adversary per scheme (`Reduction/Xmss.lean`,
  `Reduction/Sphincs.lean`) instead of §4's hybrid over keys: the multi-user games already count
  every hash call (E2E-1) and absorb the self-simulation of the other keys. Each reduction runs
  the whole game in the schemes' world (`toW`: a digest as 256 bits, `digestBits_bijective`),
  delegating its scheme's key generations and signatures to the multi-user game; its run, the
  signing log forgotten, is the game's (`map_xPrefix`; for leanSPHINCS in distribution: the
  multi-user game draws all seeds and generates its keys first, and computations commute in the
  lazy random oracle, `romRun_bind_comm`, `romRun_sKeygenAll`). Three points of the realisation:
  (1) **the bridge** (`Bridge.lean`, `game_accepted`): V_I's run against `budgetedQuery` accepting
  is its `Option` run by the final log accepting, via a two-monad closure of V_I
  (`Rel.lean`, `rel_idealVerify`); (2) **V_I's trace**: a reduction does not see its scheme's
  signer and key-generation queries, so the forged claim's signature must be valid under what it
  sees; V_I runs recorded (`Reduction/Record.lean`, `gameRec`, its marginal the game), and T4 at
  the trace (`KnowledgeSub.lean`, `aggregate_knowledge_sub`: T2 at the oracle models of both the
  trace and the final log) gives every root signature claim a signature valid under V_I's own
  queries, which the multi-user game's final verification then answers from its cache; (3) **the
  transport** (`evalDistEq_run_toW`): the logged oracle's run, its final log read as a cache, is
  the schemes' lazy random oracle's in distribution, so the bad events are bounded on the ordered
  log and the reductions' wins on the cache. The reductions' budgets are the game's `Q` plus one
  final verification (`hasHashQueryBound_xAdv`, `…_sAdv`; leanXMSS's verification makes at most
  `xmssVerifyBound` queries, `Reduction/VerifyBound.lean`). The closed form `noForgeryError` is
  `aggBadError Q + (q/2^127 + n_x²/2^127 + q²/2^252)|_{q = Q + c_x} + ε(max 1 (Q + c_s))`, `Q` the
  game's queries (`isQueryBoundP_gameComp`); the DA term is in `aggBadError`. It lives in
  `NoForgery.lean`, not in `Statement.lean`, whose definitions T5 uses unchanged.
- **T7-1 (T7′'s hypotheses).** `idealVerify_blake2s` (`LeanVM/E2E/Sanity.lean`) is T7′ for the
  deployed guest, V_I run in `Id` at `blake2sBytes`, from the outer verifier's acceptance
  (`Node.verifyAggregate guest s ip.proof`). It keeps four hypotheses on the nodes V_I reaches
  (`Reached`), none given by the deployed checks: the idealized proof's words cover their roots
  (`WordsCover`), their candidates satisfy Flock's R1CS (`CandidatesAux`), their tables pass the
  precheck (`TablesPrecheck`), and a size of nodes bounds the closure within the fuel
  (`FuelBounds`, §4's "cost ≤ Bud" in fuel form). None is on the frames: T2 holds at every frame
  chooser, so every child V_I decodes, whatever `ip.frames` names, has a proof the deferring
  verifier accepts with BLAKE2s, hence the head `nodeStep` reads. The table check's enumeration
  is finite without a hypothesis: a chain's non-final rows carry distinct counters, and their
  metadata cells are among the at most `2^32` memory words.
- **E2E-6 (W-vis: no visible log; T3 restricted to non-hidden entries).** Two changes to §3,
  both for W-vis. The plan is `w-vis.md`.

  *§3 is false at T3.* T4 on the visible log needs T3's event `Pred` to be rare on `vis_final`.
  It is not.
  - `Pred o ℓ` (`Termination.lean`) predicts `eBytes (challengeOf u)`. `challengeOf` reads digest
    words `0..5`, the bytes `0..23` (`Verifier.lean:473`).
  - Both schemes keep `truncateHash`, the low 128 bits of the little-endian `digestBits`, which
    are the bytes `0..15`. So every truncated value a signature or public key reveals gives limbs
    0 and 1 of the challenge of a hidden entry's answer; only limb 2 (64 bits) is unknown.
  - Attack:
    1. Request a leanXMSS signature σ2 whose authentication path contains a node `N` of the
       path of a later signature σ1. `N`'s entry (`P‖A‖left‖right`, from key generation) is
       hidden, its bytes `0..15` known.
    2. Make a visible query on a statement input carrying, at the guest's offset `o = 1296`,
       `N`'s two known limbs and a guess of the third.
    3. Make `N`'s entry visible: request σ1 (re-verification makes its path visible) or
       recompute the path.
  - In `vis_final` the guessing input precedes `N`'s entry, so `Pred o vis_final` holds with
    probability `2^-64` per guess, about one for `Q_v = 2^64`.
  - Re-verification at signing does not prevent it: σ2 is returned before σ1 is requested, and
    `N`'s entry becomes visible only with σ1.
  - §3's `Bad` (a revealed entry being a `BadEntry`) does not cover T3. §3's stopped potential
    needs "appending a non-record entry leaves the potential unchanged", which `predPot` does not
    satisfy: its event is about every entry's answer.

  The fix: `PredS keys o ℓ`, `Pred` with the predictor and the predicted entry both outside the
  hidden class `Hid keys` (`Vis/Shape.lean`: an honest key's `P‖A`-prefixed input, or a
  key-generation derivation). Its potential pays `(cnt+1)/2^192` at a non-hidden fresh query and
  nothing at a hidden one, so T3's term is `Q_v (Q_v + 1)/2^193`. T3 is re-proved for `PredS`
  (`rank_lt_of_child_vis`): the parent's statement input and the last batching challenge are
  chain inputs whose first 32 bytes are earlier answers, outside `InPfx keys` unless the format
  event `FormatT` holds.

  *Route B replaces §3's visible log and its events.*
  - The bad events stay on the oracle's full log, in sampling order, as in E2E-1.
  - Queries are charged by the class of their input. Non-hidden fresh queries, at most
    `qH + budget = Q_v` of them, pay the existing rates. Hidden fresh queries, which include every
    signer and key-generation query, pay only the failure rates (`~Q/2^256`).
  - Every decoder (T1's, W6's, E5's) recognises a record by its first 32 bytes, an earlier
    record's answer. A hidden input is therefore a record only if a record answered a hidden
    prefix: the format event `FormatI`, of rate `(n·2^64 + 1)/2^256` per query. §3's stopped
    potential `Φ·1[¬FormatI]` carries this.
  - Not needed any more: re-verification, reveals, LateReveal, Hit, HiddenPredict,
    HiddenCollide, GuessS, and the per-scheme deferred-sampling hops.
  - The extractor reads only V_I's own trace (`gameRec`), a sub-log of `vis_final`: T4 runs T2 at
    the trace's oracle model, DA openings included, and the full log serves only the bad events.
    This is stronger than §0's statement and meets the O-SNARK concern of §3.
  - Why: route A (§3 with this fix) needs the visible log, reveals and per-scheme
    deferred-sampling hops, about 10–17k lines, for a weaker extraction statement. Route B is
    about 6–10k lines including T5's per-key hybrid.
  - The forgery term is §0's per-key form, through a hybrid over keys with the other keys
    self-simulated (`w-vis.md`, P7).
  - What does not follow §0's constants: the failures of hidden queries add
    `5 Q_sig (2 Q_v + Q_sig)/2^256` (§3 ignored hidden–hidden collisions; `Fail` counts them),
    and each reduction forwards the other keys' two derivations. `w-vis.md` §6 lists every
    difference.
- **E2E-7 (W-vis: DA charged at E5's full rate on hidden queries; fix B).** E2E-6 charged a
  hidden fresh query only the failure rates. For T1's and W6's decoders this holds: a hidden
  input is a record only under `FormatI`. For E5's DA decoder it does not hold, and the bound
  `daPotStop_step_hid` (DA potential unchanged at a hidden query, up to `4(|ℓ|+1)/2^256`) is false.
  - Counterexample shape: a DA anchor completed by a hidden query after a hidden entry answering
    a hidden prefix. A hidden entry's answer is the first 32 bytes of a later hidden input (an
    authentication-path parent, or a chain step). That later hidden query is the one that
    completes the anchor, so the DA potential jumps at a hidden query. `FormatI` does not cover
    this, since the prefix is hidden, not a record.
  - Fix B: DA is charged at E5's full per-query rate on every fresh query, hidden or not
    (`daPotStop_step`, `Vis/DaDecoder.lean`). T1 and W6 keep the class split.
  - Cost: the DA term is `Q·14/2^192`, with `Q = Q_v + Q_sig` all of the game's hash queries,
    instead of §0's `Q_v·14/2^192`. The extra `Q_sig·14/2^192` is below `2^-120` for
    `Q_sig ≤ 2^68` (`w-vis.md` §6).
- **E2E-8 (V_I reads a node's word and frames by the node; proposed by T6-prob, decided by the
  user).** An idealized proof gives words and frames by node `ν = (pi, π)`
  (`IdealProof.words : List (Node × Word)`, `IdealProof.frames : Node → Frames`); `nodeStep ν`
  reads `ip.word ν` and `ip.frames ν`, everything else unchanged. Why (`t6-prob.md` §1.5): with
  root-keyed lookups, G3 (`RootsInj`) cannot be bounded in probability. Two honest nodes whose
  stacks are one word at one stack height under different sizes share a root, hence the frames V_I
  reads, while their executions differ; two honest nodes with one stack and different witnesses
  carry different frames. Both are deterministic for a choice of executions the prover's
  specification allows, and excluding them needs an analysis of the whole honest memory image (as
  for E2E-5). Keyed by node, honest subtrees with one node share their proof (sizes, rate, root);
  the honest prover gives each node the word and frames of its smallest subtree, V_I steps every
  honest node to that representative's children, and the closure accepts by the size measure: no
  good event on roots remains (E2E-4's event stays a hypothesis of T6-det only). Soundness: a
  root-keyed idealized proof is a node-keyed one with the same behaviour, so V_I accepts more and
  the soundness theorems are strengthened; each word is still checked against its own node's root.
  (Alternative, not proposed: frames keyed by root and sizes, words by root, keeping a
  root-collision event.)
- **T6-3 (T6-prob's formulation).** (a) The trees are a query-bounded generator's outputs, valid
  and within the limits at every hash agreeing with the oracle's log of its run (`ValidGen`): a
  fixed tree's validity is an event of the hash, since its signatures and openings are made with
  the oracle. (b) The honest prover is an oracle computation (`honestProverComp`) whose choices of
  execution, sizes, stack and frames are made from the answers of the node's log (`execOf`), its
  fresh claims read off V°'s run (`freshRun`), not by `Classical.choice` over types depending on
  the whole hash, which may depend on the answers at its own grinds and its parent's challenges. (c) The oracle is
  the lazy `Rom.loggedRO`. (d) The good events become events of the run: a proof-of-work search
  exhausted (`powPot`, as `romComplete`) and an inner node's matrix weights vanishing (a doom
  potential, `2^-192` per challenge); V_I's acceptance is asked at every hash agreeing with the
  final log, so V_I's queries are not counted. Plan and statements: `t6-prob.md`.

## 8. Status: what is proved
**The end theorem, fully instantiated** (`LeanVM/E2E/Deployed.lean`, pinned in `LeanVM.lean` at
Lean's three axioms). The game is generic in the leanSPHINCS parameter set (`[Sphincs.Params]`):
key generation and signing depend on the subtree height `b`, verification does not, and the
deployed guest only verifies. So there is one theorem per proved set,
`aggregate_no_forgery_deployed_full` (`b = 26`), `…_pruned20`, `…_pruned14`, `…_pruned13`,
`…_pruned12` (the Rust test signers' kept height), `…_pruned10`, `…_pruned8`. For `n_x` leanXMSS and
`n_s` leanSPHINCS honest keys, V_I's budget `budget`, and every adversary `A` making at most `qH` hash
queries, `sX` leanXMSS and `sS` leanSPHINCS signing requests (its only hypotheses, with the
arithmetic side condition `Q + 384 < 2^126`):

    Pr[ game guest fuel budget A : Breaks ] ≤ closedError Q n_x n_s,
    Q = 13,434,881 n_x + csk_b n_s + qH + 8,630,239,197 sX + css_b sS + budget,
    closedError Q n_x n_s =
        Q (2^-128 + 5Q/2^256) + Q (2/2^192 + 4(Q+1)/2^256)          -- T1 (V°, the log's failures), W6 (batching)
      + Q (14/2^192 + 4Q/2^256) + Q(Q+1)/2^193                      -- E5 (DA), T3 (termination)
      + (Q+384)/2^127 + n_x²/2^127 + (Q+384)²/2^252                 -- leanXMSS multi-user, at Q + c_x
      + n_s (Q+686)/2^127                                           -- leanSPHINCS multi-user, at Q + c_s

`Breaks`: V_I accepts a root statement with a claim of an honest key no request to its signer
answered, or a DA claim the oracle's final log does not back (E2E-1: every query is charged, so `Q`
includes the honest signers' work). `closedError_eq_num` writes the bound as one fraction
`closedNum Q n_x n_s / 2^256`.

**§0's goal is proved: `ε(Q_v)` with the visible accounting, up to explicit deviations** (W-vis,
`w-vis.md`; decisions E2E-6 and E2E-7; `LeanVM/E2E/Vis/EndFinal.lean`, `LeanVM/E2E/Vis/Deployed.lean`,
pinned in `LeanVM.lean` at Lean's three axioms). `aggregate_no_forgery_vis` assumes 127 bits of
single-key security for leanXMSS and leanSPHINCS, the honest costs, and the adversary's query bounds:
`qH` hash queries, `sX`/`sS` signing requests per scheme, `sXk`/`sSk` per key. Under these it bounds
a break at V_I's own trace (`BreaksVis`: an accepted root statement with a forged claim of an honest
key, or a DA claim the trace does not back):

    Pr[ gameRec guest fuel budget A : BreaksVis ] ≤ sec0ErrorGame … ≤ eps0Game … + deltaGame …,

`Q_v = qH + budget` the visible queries. `eps0` is §0's bound term by term: `κ_V°(Q_v)`,
`κ_batch(Q_v)`, `(Q_v+1)²/2^193`, `ε_signer`, `(n_x+n_s)(Q_v + Q_sig′ + c)/2^127` and `ε_DA`.
`delta` collects the deviations, each with its reason in `w-vis.md` §6:
- the hidden queries' failure terms;
- E5's `4Q_v²/2^256`;
- DA on hidden queries, `Q_sig·14/2^192` (E2E-7);
- the format event;
- the forwarded derivations, `n·2n/2^127`;
- the extra key coincidences, `n²/2^128 + n·Q_k²/2^256`.

The bound is a theorem; nothing in it is estimated. The extractor reads only V_I's trace, so the
event is stronger than `Breaks`: `aggregate_no_forgery_vis_game` states today's `Breaks` in `game`
at the same bound.

The deployed instances use lean_xmss's `leanXmss_has_127_bits_of_classical_security` and
lean_sphincs's `Lifetimes.full_bits`, …, at every proved parameter set
(`aggregate_no_forgery_vis_deployed_full`, `…_pruned20`, …, `…_pruned8`, with `…_game` and
`…_eps0` forms). Their only hypotheses are the query bounds. The values at `n_x = n_s = 2^20`:

| point | proved bound | today's `closedError` |
| --- | --- | --- |
| one slot: `Q_v ≤ 2^64`, `2^20` requests per scheme and per key (`…_one_slot_full`, `…_pruned20`) | `≤ 2^-42 + 2^-51` (`≈ 2^-42`) | `≈ 2^-43.0` |
| lifetime: `Q_v ≤ 2^64`, `2^44` per scheme, `2^24` per key (`…_lifetime_full`, `…_pruned20`) | `≤ 2^-41` (`≈ 2^-41.97`) | `≈ 2^-28.07` |
| lifetime against §0 (`…_lifetime_full_eps0`) | `≤ ε(Q_v) + 2^-84 + 2^-86 + 2^-91` | |
| leanXMSS keys only, lifetime, `Q_v ≤ 2^64` (`…_lifetime_xmss`) | `≤ 2^-42` (`≈ 2^-43`) | `≈ 2^-39` |
| leanXMSS keys only, lifetime, `Q_v ≤ 2^56` (`…_lifetime_xmss_56`) | `≤ 2^-49` | `≈ 2^-39` |

The two families hold for the same event (`Breaks`), and the smaller bound applies. At one slot,
today's is about twice smaller: the per-key hybrid pays `n_x·Q_v/2^127` for leanXMSS, where
leanXMSS's multi-user theorem pays `Q/2^127` once. Over a lifetime the visible bound wins by
about `2^14`. The deviations matter little: `deltaFwd` alone is `2^-84` at the lifetime point, the rest is
below `2^-85`.

**The constants** (proved worst-case `IsTotalQueryBound`s, `Reduction/XmssBound.lean`,
`Reduction/SphincsBound.lean`, `Reduction/VerifyBound.lean`):

| | leanXMSS | leanSPHINCS at `b` | `b = 26` | `b = 20` |
| --- | --- | --- | --- | --- |
| key generation | `13,434,881` (lean_xmss's exact `keygenQueries`) | `1 + 226·2^b + 2(26−b)` (lean_sphincs's `keygenCost + 1`) | `15,166,603,265` | `236,978,189` |
| signature | `2^33 + 40,304,605` | `2^33 + 118,387 + Σ_{l<26} (l<b ? 226·2^l − 1 : 1)` | `23,756,655,991` | `8,827,030,915` |
| verification | `384` | `686` | | |

(the other sets: `csk = 3,702,809 / 1,851,419 / 925,725 / 231,457 / 57,893` and
`css = 8,593,755,535 / 8,591,904,145 / 8,590,978,451 / 8,590,284,183 / 8,590,110,619` at
`b = 14 / 13 / 12 / 10 / 8`). A signature is dominated by its two `2^32`-attempt searches (the
randomizer grinding and the WOTS counter, both worst case), and at `b = 26` by the path's
`226 · 2^26`.

**The leanSPHINCS term.** `closedError` uses `n_s q / 2^127`, which every proved bound is at most
(`Multi.multiBound` is a minimum with it; `multiBound_le`). `aggregate_no_forgery_deployed_full_sharp`
and `…_pruned20_sharp` keep the per-key bound `Multi.multiBound` itself (lean_sphincs `PROOF.md`,
"Several keys", by an evaluation Lean does not check: about `q (1.75 + 0.002 n_s)/2^128` at
`b = 26`, `q (1.87 + 0.0036 n_s)/2^128` at `b = 20`, so about 1000 and 560 times smaller for large
`n_s`), with the other terms as above.

**One slot** (`aggregate_no_forgery_one_slot_full`, `…_pruned20`): `n_x = n_s = 2^20`,
`qH + budget ≤ 2^64`, `sX, sS ≤ 2^20` give `Pr[Breaks] ≤ 2^-42` (the closed form is about
`2^-43.0` there, its leanSPHINCS term `n_s Q/2^127`; §0's estimate `≈ 2^-43`).

**The chain.** `aggregate_no_forgery_closed` (`LeanVM/E2E/NoForgeryClosed.lean`) is
`aggregate_no_forgery` (T5-1) with the costs proved, for any parameter set and any leanSPHINCS bound
`≤ n_s q/2^127`; `aggregate_no_forgery` assembles T1, W6, T3, E5 and T4 (`aggBadError`) with the two
reductions. T6-det is `Complete.idealVerify_complete_det` (`LeanVM/E2E/Complete/DecodeFinal.lean`):
V_I accepts the honest prover's idealized proof of any valid honest tree within the limits, on the
good events G1–G3 (`PowFound`, `WeightsNonzero`, `RootsInjAt`). The guest's completeness over every
completeness model (`guestCompleteModel : GuestCompleteModel`, L2) is proved, so it is no longer a
hypothesis: the executions (`guestCompleteModelExec`) and the decoding (`DecodeHonest`: the children's
count, statements and proofs read back off the honest memory at the frames the honest prover names,
E2E-5) by the layers of `t6-completeness.md`. L17, the count of the node's hashed strings, is a theorem
(`nodeLog_count_lt`, T6-2), so the final form `Complete.idealVerify_complete_final`
(`LeanVM/E2E/Complete/Count/Final.lean`) asks only the deployed limits and budget at every node
(`WithinLimitsBudget`). The hypotheses are satisfiable together (`Complete/Witness.lean`,
`hyps_wTree`, `idealVerify_complete_wTree`; `Count/FinalWitness.lean`, `hyps_final_wTree`,
`idealVerify_complete_final_wTree`): a leaf holding one leanXMSS claim directly, at a constant `H`,
meets all of them, its budget evaluated by the kernel.
**T6-prob** (`t6-prob.md`, decisions E2E-8 and T6-3): completeness with no good event as a
hypothesis. `Complete.idealVerify_complete_rom` (`LeanVM/E2E/Complete/Rom/End.lean`, pinned in
`LeanVM.lean`): for every generator of valid honest trees within the limits (`ValidGen`) making at
most `QG` queries, the honest prover's (at most `QP`), a valid rate and a proof-of-work fuel
`pfuel ≤ 2^64`, the honest prover of the random-oracle model outputs a statement with the tree's
claims whose idealized proof V_I accepts at every hash agreeing with the oracle's log, except with
probability `completeError (QG + QP) pfuel = Q((1 − 2^-17)^pfuel + Q/2^256) + Q(2^-192 +
4(Q + 1)/2^256)`, `Q = QG + QP`; `QP ≤ size · nodeQueries pfuel` (about `2^42` per node at
`pfuel = 2^25`). Not vacuous: the honest leanXMSS leaf generator, error at most `2^-124`
(`idealVerify_complete_rom_xmssLeaf`).
T7′ is `Sanity.idealVerify_blake2s`. Not proved: the heuristic of §5 relating V_I to the deployed
`verifyAggregate`.
