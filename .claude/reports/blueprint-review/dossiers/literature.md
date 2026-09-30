# Dossier: the literature and comparable verification efforts (task "literature")

Written 2026-09-29/30 for the adversarial review of the proof-system blueprint of leanerVM.
Object of the review: leanerVM `main` at `b435631` (blueprint cited from
`git show b435631:docs/roadmap/protocol-blueprint.md`, 1549 lines); leanVM at the pin `a386121f`
(`/home/scaraven/Documents/leanEthereum/leanVM`). Library citations name their revision: ArkLib
`dca90385` (the pin of `b435631`) and `7653a901` (the pin after the Lean 4.34.1 upgrade, `144c5aa`).
No Lean was run for this dossier; no tracked file was edited; nothing was posted.

Every source below was downloaded and read as text (`curl` + `pdftotext`) unless it is marked
**unverified**; the local text copies are under
`.claude/reports/blueprint-review/probes/literature/src/` (git-ignored). Quotations are verbatim
from those copies. "Opened" means I read the passage quoted, not only the abstract.

## Summary

**Examined.** The Fiat–Shamir/BCS literature (CCHLRR18, BCS16, CMS19, the Chiesa–Yogev book,
BGKTTZ23, CO25, ABF26), the attacks on Fiat–Shamir (KRS25, Fen26), WHIR and proximity gaps (ACFY25,
BCHKS25, Hab25, ABF26, the 2025-2026 counterexamples), the arithmetization references (M3, Thaler,
Gruen), the Lean libraries at both pins, the obligation outline arXiv:2607.23752, seven comparable
zkVM verification efforts, and the security advisories of Plonky3, SP1, RISC Zero, OpenVM. Checked
against the blueprint at `b435631`, leanVM's Annex B, `whir_config.rs` and `fiat_shamir/src/` at
`a386121f`.

**Conclusions.**
1. The blueprint's "after Fiat–Shamir the largest bound is what a random-oracle query buys" is right
   at its core ([CY24] Thms 31.2.1/31.3.1: `(t + k)·max_i ε_i`; [BGKTTZ23] Thm 3.15: `Q·ε_rbr`), but
   `niError` as sketched lacks the hash term (`3.5·t²/2^256`), the list-size factor `L_0` of a
   list-binding commitment, and a model of grinding; no published theorem covers Fiat–Shamir with
   proof of work for multi-round IOPs, and leanVM's query rounds reach 128 bits only with it.
2. leanVM's PCS regime (Johnson with slack, [BCHKS25] Theorem 4.6) is the right, provable one: the
   capacity conjectures are refuted ([CS25], [KKH26]) and at exactly the Johnson radius the bound
   fails in characteristic 2 ([BCHKS25] Cor. 1.7). Annex B states Theorem 4.6 exactly as printed
   (checked term by term). Caveat: a single-version preprint whose proof of Theorem 4.6 is a sketch.
3. The known diagonalization attacks ([KRS25], [Fen26]) do not apply to leanVM's structure (statement
   in the seed, trace committed before any challenge, GKR only for grand products), although the VM
   computes its own Fiat–Shamir hash natively; a random-oracle theorem says nothing beyond that, and
   is classical (quadratic loss against quantum adversaries), which the blueprint does not say.
4. The blueprint's cut (a relation `M3Holds` on the one committed column, an adaptor to leanISA's
   trace relation) is sound practice: every other effort (SP1, OpenVM, Pico, ZisK, S-two) stops at a
   trace relation and assumes or plans the proof-system half; only SP1 has a plan, and it asks for
   the same thing (an extractor delivering an exact natural-number balance). Characteristic 2
   forces combinatorial balance, which the blueprint has.
5. "ABF26" = Arnon, Boneh, Fenzi, *Open Problems in List Decoding and Correlated Agreement*, ePrint
   2026/680; its Definition A.5 bounds the extractor's time, ArkLib's definition does not. The
   obligation outline arXiv:2607.23752 is Kolozyan, Sorger, Hicks, Chaliasos (2026); leanerVM's
   T1–T8 refine its CC-S/PS/VC/CC-C/WC/PC, but no T-theorem covers the deployed verifier (VC).

**Findings by severity.**
- *Major*: the Fiat–Shamir interface omits grinding and cannot state leanVM's claim (A.4); the
  compiled error omits the list-size factor (A.4); the upstream Fiat–Shamir/BCS theorems are about
  other constructions than leanVM's one-map BLAKE2s chain (E.6); the proof of work is the one
  verifier check no planned theorem or mutation makes load-bearing (G.5).
- *Minor*: hash-collision term missing (A.4); "computable" is not "efficient" (A.4); misattributed
  and mistitled references (A.4); the scope of the random-oracle assumption is not stated (B.4);
  Thaler chapter citation (D.3); the obligation outline is not attributed (E.6); the theorem is
  classical (G.5).
- *Notes*: [BCHKS25] Thm 4.6 is a preprint with a sketched proof; three readings of its constant
  exist, leanVM and ArkLib use the safe printed one (C.4); the verification literature is almost
  entirely constraint-level (F.3); a stale comment in the pinned Rust on level-0 grinding (G.1).

## A. Round-by-round (knowledge) soundness, and what it buys after Fiat–Shamir

### A.1 What the blueprint and leanVM say

- Blueprint (`b435631`), lines 61-66: "**round-by-round knowledge soundness**, the standard form
  since [CCHLRR19]: an invariant on partial transcripts that a cheating prover can only escape
  when a fresh verifier challenge lands badly, with an error bound per challenge. Summing the
  bounds gives the interactive error; after Fiat–Shamir the largest bound is what a random-oracle
  query buys the adversary. The knowledge part is *straight-line*: an extractor reads the witness
  off the oracles, no rewinding."
- Blueprint line 1224: `structure FiatShamirSecurity where …   -- rbr knowledge soundness of the
  IOPP ⇒ knowledge soundness of its FS compilation in the ROM, error Q · max_i ε_i`; lines
  1234-1235: "`niError` is the round-by-round maximum times the query bound plus the
  grinding-adjusted WHIR terms".
- leanVM specification, `doc/leanvm/body/b-polynomial-commitment-scheme.tex:84`: "Interactive
  soundness error is then at most $\sum_i \varepsilon_i$. After Fiat--Shamir, it is
  $\max_i \varepsilon_i$ per random-oracle query~\cite{CCHLRR19,BCS16}." Section 8.4 of the
  specification, "Fiat Shamir instanciation", is `TODO` (`08-end-to-end-protocol.tex:44-46`).
- leanVM Rust, `crates/pcs/src/whir_config.rs:26-27`: "the Fiat--Shamir error per random-oracle
  query is the MAX of the entries, not their sum"; `:36-38` `SECURITY_BITS: usize = 128` ("every
  verifier-challenge transition must have conditional failure probability at most
  `2^-SECURITY_BITS`"); `:57-60` `QUERY_GRINDING_BITS: usize = 17` ("ground after the level
  commitment and before its query positions are sampled, so the query count only needs to close
  the remaining `SECURITY_BITS - 17` bits"); `:404-407` "This is an RBR target, not a claim that
  the sum of all interactive failure probabilities is bounded by `2^-target_security_bits`."
- leanVM's Fiat–Shamir primitive (`crates/fiat_shamir/src/lib.rs:9-24, 60-110`): `f(a, b) =
  BLAKE2s(a‖b)` on 64 bytes, "*exactly* the VM's `Blake2s` opcode"; a 256-bit chaining value,
  absorb with tag 1 in lane 3, squeeze with tag 2 whose first three 64-bit words are the `E`
  challenge; grinding with tags 3 and 4 on the same `f`. Merkle digests are 32-byte BLAKE2s
  (`crates/fiat_shamir/src/merkle.rs:7` `pub type Hash = [u8; 32];`), leaves and inner nodes
  hashed by the same function, unsalted.

### A.2 Annotated bibliography

**[CCHLRR18] R. Canetti, Y. Chen, J. Holmgren, A. Lombardi, G. N. Rothblum, R. D. Rothblum,
*Fiat-Shamir From Simpler Assumptions*, Cryptology ePrint Archive 2018/1004 (received
2018-10-22, revised 2018-10-23). https://eprint.iacr.org/2018/1004.** Status: current as the
full version; its conference form is [CCHLRRW19]. Opened (verified).
Statements used:
- Definition 5.3 (Round-by-Round Soundness): a deterministic, not necessarily efficient `State(x, τ)`
  with (1) `x ∉ L ⇒ State(x, ∅) = reject`; (2) "If State(x, τ) = reject for a transcript prefix τ,
  then for every potential prover message α, it holds that Pr_{β←V(x,τ|α)}[State(x, τ|α|β) =
  accept] ≤ ε(n)"; (3) a rejected full transcript is rejected by `V`.
- Proposition 5.4: round-by-round soundness error ε implies standard soundness error `r·ε`
  ("By a union bound over the error in all of the rounds").
- Theorem 5.8: Fiat–Shamir with an `R_State`-correlation-intractable hash family is adaptively
  sound for a round-by-round sound interactive proof. This is a **standard-model** result (no
  random oracle, no error formula in the query count).
- §2.1: "Negligible round-by-round soundness readily implies state restoration soundness for a
  polynomial number of rewinds."
Relevance: this is where round-by-round *soundness* is defined; round-by-round *knowledge*
soundness is not in it (it is [CMS19], below). The blueprint's "the standard form since
[CCHLRR19]" is right for soundness only.

**[CCHLRRW19] R. Canetti, Y. Chen, J. Holmgren, A. Lombardi, G. N. Rothblum, R. D. Rothblum,
D. Wichs, *Fiat-Shamir: From Practice to Theory*, STOC 2019, pp. 1082-1090,
doi:10.1145/3313276.3316380.** Status: current. **Unverified**: the ACM PDF returned HTTP 403;
bibliographic data from the ACM Digital Library listing (search result) and from leanVM's
`doc/leanvm/refs.bib`; the content was read in [CCHLRR18].
Relevance: the reference the blueprint and the specification cite. **The blueprint's reference
list gets its authors wrong** (see finding "Misattributed and mistitled references" in A.4).

**[Hol19] J. Holmgren, *On Round-By-Round Soundness and State Restoration Attacks*, Cryptology
ePrint Archive 2019/1261. https://eprint.iacr.org/2019/1261.** Opened (verified).
Theorem 1.1: "if Π is sound against state restoration attacks, then Π is round-by-round sound";
Theorem 1.2: there is a Π "unsound against state restoration attacks, but FS_RO[Π] is secure".
Relevance: the two notions are equivalent asymptotically; neither is necessary for FS security in
the ROM. Background only.

**[BCS16] E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive Oracle Proofs*, TCC 2016-B;
Cryptology ePrint Archive 2016/116 (version of 2016-02-10). https://eprint.iacr.org/2016/116.**
Status: current; its bounds are restated and sharpened in [CY24]. Opened (verified, §1 only).
Theorem 1.2 (IOP → NIROP): a public-coin IOP with state restoration soundness `s_sr(x, b)`
compiles to a non-interactive random-oracle proof with soundness `s_sr(x, m) + O(m² 2^{-λ})`
(`m` the number of oracle queries, `λ` the security parameter), preserving proof of knowledge.
Theorem 1.5: for a `k`-round IOP, `s_sr(x, b)` lies between `C(b, k+1)·s(x)·(1 − o(1))` and
`C(b, k+1)·s(x)`. Relevance: plain (summed) soundness of an IOP says almost nothing after
Fiat–Shamir for many rounds; only a per-round (state-restoration or round-by-round) bound gives a
linear loss in the query count. This is the reason the blueprint's master theorem must be
round-by-round and not only its summed corollary.

**[CMS19] A. Chiesa, P. Manohar, N. Spooner, *Succinct Arguments in the Quantum Random Oracle
Model*, TCC 2019; Cryptology ePrint Archive 2019/834 (version of 2020-01-14).
https://eprint.iacr.org/2019/834.** Opened (verified).
- Definition 8.3 (state function: empty transcript `0`; a prover move cannot change `0` to `1`;
  a full transcript with state `0` is rejected).
- Definition 8.4 (round-by-round soundness error ε, "[CCHLRR18] adapted to IOP").
- Definition 8.5: "An IOP (P, V) for a relation R has round-by-round knowledge error κ if there
  exists a polynomial-time extractor E and state function state such that for all x and every
  transcript tr where the verifier is about to move and state(x, tr) = 0, if Pr_m[state(x, tr‖m) =
  1] > κ then (x, E(x, tr)) ∈ R." (§8.3: "round-by-round knowledge (introduced in this work)").
- Theorem 8.6: the BCS construction has soundness `O(t²ε + t³/2^λ)` and extraction probability
  `Ω(μ − t²κ − t³/2^λ)` against quantum attackers making `t − O(q log ℓ)` queries.
Relevance: the origin of round-by-round *knowledge* soundness, with a **polynomial-time,
straight-line** extractor that sees only the instance and the transcript.

**[CY24] A. Chiesa, E. Yogev, *Building Cryptographic Proofs from Hash Functions*, 2024; PDF
compiled 2026-03-25, 475 pp., https://snargsbook.org (PDF at
`github.com/hash-based-snargs-book`).** Status: current (living book). Opened (verified).
- Definition 31.1.2: round-by-round soundness errors `(ε_i^rbr)_{i∈[k]}`, one per round, and a
  single error `ε^rbr` bounding them all.
- Claim 31.1.3: standard soundness `≤ Σ_i ε_i^rbr ≤ k·ε^rbr`. Claim 31.1.7: the same for
  knowledge.
- Definition 31.1.6: round-by-round knowledge errors with "a polynomial-time extractor"; "the
  extractor only needs the IOP strings sent by the prover in the transcript" (straight-line).
- Theorem 31.2.1: state-restoration soundness `ε^sr(s, n, t) ≤ (t + k)·ε^rbr(n)`.
- Theorem 31.3.1: straight-line state-restoration knowledge soundness `κ^sr(s, n, t) ≤ (t +
  k)·κ^rbr(n)` (stated for "a public-coin IP"; the chapter's text says the material is written for
  IOPs).
- Theorem 25.2.1 (BCS soundness): `ε_ARG(λ, n, t) ≤ ε^sr(λ + s_FS, n, t) +
  κ^mm_MT(λ, (l_i), t, t+1) + t²/2^λ`, and `κ^mm_MT + t²/2^λ ≤ 3.5·t²/2^λ` if
  `t ≥ 2·(log l + 1)·l`.
- Theorem 26.1.1 (BCS knowledge soundness, rewinding, with extraction time); §28.3.2 for the
  straight-line case: `κ_ARG(λ, n, t) ≤ κ^sr(λ + s_FS, n, t) + 3.5·t²/2^λ`; κ bits of worst-case
  security need `λ = 3κ + 3`, of average-case security `λ = 2κ + 3`.
- §27 (p. 310): "The GKR protocol ... satisfies round-by-round soundness [CCHLRR18]"; "The
  FRI, STIR, WHIR protocols ... satisfy round-by-round soundness [BGKTTZ23; ACFY24; ACFY25]."
- The book has no treatment of proof-of-work grinding (no occurrence of "grinding" or "proof of
  work" in the text).
Relevance: the reference for the exact non-interactive error. It is also the reference ArkLib's
Fiat–Shamir file says it follows (`ArkLib/OracleReduction/FiatShamir/Basic.lean:31` at both
`dca90385` and `7653a901`: "Our formalization mostly follows the treatment in the Chiesa-Yogev
textbook.").

**[BGKTTZ23] A. R. Block, A. Garreta, J. Katz, J. Thaler, P. R. Tiwari, M. Zając, *Fiat-Shamir
Security of FRI and Related SNARKs*, ASIACRYPT 2023; Cryptology ePrint Archive 2023/1071 (last of
7 revisions 2024-03-05; PDF dated 2024-02-15). https://eprint.iacr.org/2023/1071.** Opened
(verified).
- Definition 3.13 (round-by-round knowledge, doomed-set form, polynomial-time `Ext(i, x, τ, m)`).
- Theorem 3.15 ("[BCS16, CMS19, COS20]"): for `Q`-query adversaries and a random oracle with
  `κ`-bit outputs, the BCS compilation has "adaptive soundness error `ε_fs(x, Q, κ) =
  Q·ε_rbr(x) + 3(Q² + 1)/2^κ` and adaptive knowledge error `ε_fs−k(x, Q, κ) = Q·ε_rbr−k(x) +
  3(Q² + 1)/2^κ`"; against quantum adversaries `Θ(Q·ε_fs)`.
Relevance: the most compact statement of the formula the blueprint sketches, and the model for
leanVM-style (FRI/WHIR) analyses: `ε_rbr` is a single bound on every round, i.e. the maximum.

**[CO25] A. Chiesa, M. Orrù, *A Fiat–Shamir Transformation From Duplex Sponges*, TCC 2025;
Cryptology ePrint Archive 2025/536 (PDF of 2026-03-27). https://eprint.iacr.org/2025/536.**
Opened (verified).
Theorem 1 (informal) and Theorems 6.1, 6.2: for the duplex-sponge transformation over an ideal
permutation, `ε_NARG(t) ≤ ε^sr_IP(t) + 25t²/|Σ|^c` (plus a decoding-bias term), and likewise for
(straight-line) knowledge soundness; §2.3: indifferentiability of the sponge "is insufficient for
establishing the knowledge soundness and zero knowledge of a non-interactive argument".
Relevance: the analysis ArkLib's `DuplexSponge` folder targets (its security is admitted at the
pin, blueprint ledger entry "Fiat–Shamir and BCS", line 263). **leanVM does not use a duplex
sponge**: its transcript is a Merkle–Damgård chain of the 64-byte BLAKE2s compression with tags,
so neither [CO25] nor ArkLib's basic transform (which queries one random oracle on
`(statement, all messages so far)`, `ArkLib/OracleReduction/FiatShamir/Basic.lean:91` at both
pins) is literally leanVM's construction; the closest textbook object is the hash chain of the
BCS construction in [CY24] Construction 25.1.1 with `f` modelled as a random oracle. Binary
fields avoid [CO25]'s decoding-bias term: `E` challenges are 192 uniform bits of the digest and
query indices are powers of two.

**[ABF26] G. Arnon, D. Boneh, G. Fenzi, *Open Problems in List Decoding and Correlated
Agreement*, Cryptology ePrint Archive 2026/680 (PDF of 2026-07-06; the ePrint listing says the
July update added an MCA lower bound). https://eprint.iacr.org/2026/680.** Opened (verified).
This is the "ABF26" whose "Definition A.5" ArkLib cites for its knowledge state function
(`ArkLib/OracleReduction/Security/RoundByRound.lean:158` at `dca90385`, `:159` at `7653a901`;
ArkLib `blueprint/src/references.bib:519-525`: "Manuscript, accompanying the Ethereum Foundation
Proximity Prize"). Statements:
- Definition A.4 (knowledge state function from `R̃` to `R̃'`): empty transcript: `State = 1` iff
  `(x, y, w) ∈ R̃`; a prover move cannot turn `0` into `1` **for the same witness `w`**; full
  transcript: `State = 1` **iff** the verifier outputs `(x', y')` with `(x', y', w) ∈ R̃'`.
- Definition A.5 (round-by-round knowledge soundness of an interactive oracle reduction, errors
  `(ε_1, …, ε_k)`, extraction times `(et_1, …, et_k)`): a deterministic extractor `E_rbr` running
  in time `et_i` with `Pr_{ρ_i}[∃w : State(x, y, tr, E_rbr(x, y, tr‖ρ_i, w)) = 0 ∧
  State(x, y, tr‖ρ_i, w) = 1] ≤ ε_i`; it cites [BCFW25] for the notion.
Relevance: ArkLib's docstring states the two deliberate differences (its `extractMid` may change
the witness across a prover move; its full-transcript clause is one direction only). A third
difference matters here: A.5 (like [CMS19] and [CY24]) **bounds the extractor's running time**,
while ArkLib's `KnowledgeStateFunction` and `rbrKnowledgeSoundnessWorstCaseWith`
(`RoundByRound.lean:164-189, 553-570` at `dca90385`) do not; ArkLib's own docstring on
`toRoundByRoundOfRel` (`:103-117`) says a classical choice "does not establish the
extraction-time bounds present in algorithmic formulations of round-by-round knowledge
soundness". The blueprint's substitute is "computable" (acceptance test 24, lines 1333-1340):
see finding "Computable is not efficient" below.

**[BCFW25] B. Bünz, A. Chiesa, G. Fenzi, W. Wang, *Linear-Time Accumulation Schemes*, TCC
2025; Cryptology ePrint Archive 2025/753 (last of 4 revisions 2026-06-18).** **Unverified**
(listing only): cited by [ABF26] as the source of round-by-round knowledge soundness for
interactive oracle reductions with relaxed relations.

**[Riv26] M. Rivain, *AES-Based Grinding for MPC-in-the-Head Signatures*, Cryptology ePrint
Archive 2026/1625 (received 2026-08-06).** Abstract read only (**body unverified**): it
"formalize[s] the notion of grinding scheme together with a protocol-agnostic security notion"
and proves a bound `(4/3)·ε·Q_E/2^w` in the ideal-cipher and random-oracle models. Relevance: the
only recent formal treatment of grinding I found; it is for MPC-in-the-Head signatures, not for
multi-round IOPs. I found **no published theorem** that states round-by-round soundness with
per-round proof-of-work as a Fiat–Shamir compilation result for multi-round IOPs; the WHIR paper
[ACFY25] and Flock [BRW26] use grinding in their parameter choices without such a theorem
(negative result of a search, not proof of absence).

### A.3 Synthesis: is "round-by-round maximum times the query bound" the right formula?

The core of the blueprint's sentence is right, and so is leanVM's "MAX, not sum": for a
`t`-query adversary, the textbook bound is linear in `t` times the largest per-round error. The
formula as the blueprint writes it (`Q · max_i ε_i`, "plus the grinding-adjusted WHIR terms") is
incomplete in four ways, each of which the Lean interface has to carry.

1. **Multiplier.** [CY24] Theorems 31.2.1 and 31.3.1 give `(t + k)·max_i ε_i` (`k` the number of
   rounds), [BGKTTZ23] Theorem 3.15 gives `Q·ε_rbr`. Immaterial numerically, but the interface
   statement should name the one it assumes.
2. **The hash term.** Every ROM compilation theorem adds a collision/extraction term for the hash
   chain and the Merkle trees: `3.5·t²/2^λ` ([CY24] Thm 25.2.1, §28.3.2) or `3(Q²+1)/2^κ`
   ([BGKTTZ23] Thm 3.15). With BLAKE2s-256 (`λ = 256`), [CY24] §28.3.2 asks `λ = 2κ + 3 = 259`
   for `κ = 128` bits of average-case security, so the 256-bit digest gives slightly under 128
   bits by the textbook bound; and a per-round error of exactly `2^-128` (leanVM's
   `SECURITY_BITS`) gives, with the `(t + k)` factor and the hash term, about `2^125.8` in the
   `t/ε` sense at `t = 2^128` (my arithmetic from the two theorems). This is the usual convention
   ("128-bit round-by-round target"), but a Lean theorem that states `niError` must contain the
   term, not only `Q · max ε_i`. The blueprint puts the hash side in `BcsSecurity`
   ("extraction from collision resistance / ROM", line 1225) without an error term.
3. **Grinding is outside every theorem cited.** The query rounds of leanVM's WHIR have
   interactive error `(1 − γ_i)^{t_i}` ≈ `2^-111` (the Rust closes `128 − 17` bits by queries,
   `whir_config.rs:57-60`); the 128-bit claim relies on the 17-bit proof of work bound into the
   chain (`lib.rs:30-51, 126-178`). [CY24], [BGKTTZ23], [BCS16], [CMS19] and [CO25] compile
   protocols without proof of work. In the ROM the natural statement is that the effective error
   of a ground round `i` is `2^{-b_i}·ε_i` per query (each attempt at that challenge costs `2^{b_i}`
   oracle queries in expectation); [Riv26] proves a bound of this shape for signatures only. So
   the blueprint's interface line "error Q · max_i ε_i" (line 1224) **cannot deliver leanVM's
   128-bit claim**: with the query rounds' `2^-111` in the maximum it gives about 111 bits. The
   interface must state Fiat–Shamir *with* proof of work at named rounds, with error
   `(t + k)·max_i 2^{-b_i}·ε_i + hash term`, and the IOP must expose which challenge is ground.
   No source proves that statement for multi-round IOPs; it is a new assumption to name.
4. **The list-size factor.** leanVM's PCS takes no out-of-domain sample at commitment and is only
   list binding (Annex B, `b-polynomial-commitment-scheme.tex:4`: "we do not use out-of-domain
   (OOD) sampling at commitment, so our PCS is only list binding"). The master theorems are
   proved in the ideal oracle model, where the oracle is one polynomial `q`. In the compiled
   protocol the committed word has up to `L_0 = 1/(2η_0√ρ_0)` nearby codewords (Annex B,
   Theorem `thm:johnson-interleaved`), and the prover may steer toward any of them after each
   challenge, so every oracle-protocol challenge error preceding the point where the claims pin
   one member is multiplied by `L_0` (union bound over the list). Flock states this directly
   ([BRW26] Remark 11: dropping the initial OOD sample costs "the outer protocol ... increasing
   its soundness error by a factor of the list size L (security follows from a union bound over
   the nearby codewords)"); leanVM's Rust accounts for it only as one term, "the opening's own
   evaluation claim sits at a post-commit random point, so at most one list member matches it
   except with `L·μ/|F|`" (`whir_config.rs:593-599`), which is neither in the specification nor
   in the blueprint's `niError`. Numerically this is benign at `|E| = 2^192` (my estimate, from
   the formula of Annex B and the Rust's search for `η_0`, is `L_0` around `2^7` to `2^10`;
   **unverified**, the Rust's `validate()` would print it), but the composition theorem
   "ideal-oracle round-by-round knowledge soundness + list-binding WHIR ⇒ compiled knowledge
   soundness" is the step that introduces it, and neither the specification (§8.4 is `TODO`),
   nor ArkLib, nor the blueprint states it.

What the blueprint gets right and should keep: the master theorems are round-by-round, not only
summed (required by [BCS16] Theorem 1.5); the error is per challenge (`pSpec.ChallengeIdx → ℝ≥0`,
matching [CY24] Definition 31.1.2); the extractor is straight-line and reads the oracle, matching
[CMS19] Definition 8.5 and [CY24] Definition 31.1.6, which is what makes the knowledge part
survive BCS without rewinding ([CY24] §28.3.2).

### A.4 Findings of this section

**Finding: the Fiat–Shamir interface omits grinding, so it cannot state leanVM's claim.**
Severity: major. Classification: an error of the blueprint.
Evidence: blueprint line 1224 (`error Q · max_i ε_i`); leanVM `whir_config.rs:57-60` (17 bits of
query grinding), `lib.rs:30-51, 126-178` (grinding in the chain); none of [CY24], [BGKTTZ23],
[BCS16], [CMS19], [CO25] covers proof of work.
Proposed change. As it stands (line 1224): "`structure FiatShamirSecurity where … -- rbr
knowledge soundness of the IOPP ⇒ knowledge soundness of its FS compilation in the ROM, error Q ·
max_i ε_i`". Proposed: "`structure FiatShamirSecurity where … -- for the BLAKE2s chain with the
compression modelled as a random oracle with 256-bit output: rbr knowledge soundness of the IOPP
with errors ε_i, and b_i bits of proof of work bound before challenge i, ⇒ straight-line
knowledge soundness of the compiled verifier against t-query provers with error (t + k) · max_i
2^{-b_i} ε_i + 3.5 t²/2^256 ([CY24] Thm 31.3.1 and §28.3.2; the proof-of-work factor is an
assumption no published theorem covers)`". And at lines 1234-1235: replace "the round-by-round
maximum times the query bound plus the grinding-adjusted WHIR terms" by "`(t + k)` times the
largest grinding-adjusted per-challenge error of the compiled protocol (oracle-protocol errors
multiplied by the list size `L_0`, WHIR's errors as in Annex B Theorem `thm:rbr`), plus the
hash-collision term". Reason: without the proof-of-work factor, the query rounds' `2^-111`
dominates and the Lean statement would certify about 111 bits where leanVM claims 128.

**Finding: the compiled error omits the list-size factor of a list-binding commitment.**
Severity: major (a statement the blueprint needs is missing; numerically benign). Classification:
an error of the blueprint (and a gap in the specification, whose §8.4 is `TODO`).
Evidence: A.3 item 4. Proposed change: add to Layer 12 a named composition lemma, "for a
list-binding PCS with list bound `L_0` and no commitment-time OOD sample, each challenge of the
oracle protocol drawn before the claims pin a unique list member contributes `L_0 · ε_i`
(union over the list); the pinning step contributes the pair bound `C(L_0, 2)·μ/|E|` (Annex B
Lemma `lem:ood`)", and carry `L_0` into `niError`. Reason: the ideal-oracle master theorems do
not see the list; the compilation does.

**Finding: the hash-collision term is missing from `niError`.** Severity: minor. Classification:
an error of the blueprint. Evidence: A.3 item 2. Proposed change: state `BcsSecurity` with its
error term (`3.5·t²/2^256` for BLAKE2s-256 digests and chain, under [CY24] Theorem 25.2.1's
condition `t ≥ 2(log l + 1)l`, or [BGKTTZ23]'s `3(Q²+1)/2^256`), and say in the blueprint that
the 256-bit digest yields just under 128 bits of average-case security by [CY24] §28.3.2.

**Finding: "computable" is not "efficient".** Severity: minor (for T4 as stated) / note.
Evidence: [CMS19] Def. 8.5, [CY24] Def. 31.1.6 and [ABF26] Def. A.5 require a polynomial-time
(or time-bounded) extractor; ArkLib's definitions do not (`RoundByRound.lean:103-117` at
`dca90385`); the blueprint's acceptance test 24 (lines 1333-1340) enforces "computable". The
oracle-protocol extractor `piopExtractor` reads `q` off the oracle (linear time), so nothing is
wrong there; but after compilation the extractor must recover `q` from the committed word by
list decoding (Layer 12: "extracts the member", line 1299), and a computable brute-force decoder
satisfies "computable" while being exponential. For T4 as stated in the blueprint ("except with
probability niError, ∃ t, ValidExecution prog input t", line 1248) soundness suffices, so this
does not weaken T4; it matters for any claim of *knowledge* soundness after compilation and for
recursion (T6). Proposed change: in acceptance test 24, say "computable, and for the compiled
extractor, an efficient list decoder (Guruswami–Sudan) is named as the intended implementation;
Lean does not measure running time, so knowledge soundness of `verify` is claimed only in the
information-theoretic sense".

**Finding: misattributed and mistitled references.** Severity: minor. Classification: an error of
the blueprint. Evidence: blueprint lines 1530-1537 at `b435631`:
- "A. Chiesa, Y. Cheng, M. Holmgren, A. Lombardi, R. Rothblum, R. Rothblum, *Fiat–Shamir: from
  practice to theory* (CCHLRR19)". Correct: R. Canetti, Y. Chen, J. Holmgren, A. Lombardi, G. N.
  Rothblum, R. D. Rothblum, D. Wichs, STOC 2019 (key CCHLRRW19); the full version without Wichs is
  ePrint 2018/1004 (leanVM's `refs.bib` has the STOC authors right).
- "B. Nazarov, *Ligerito* (NA25)". Correct: A. Novakovic, G. Angeris, *Ligerito: A Small and
  Concretely Fast Polynomial Commitment Scheme*, ePrint 2025/1187 (leanVM `refs.bib`).
- "*Mutual correlated agreement up to the Johnson bound* (BCHKS25)". Correct: E. Ben-Sasson, D.
  Carmon, U. Haböck, S. Kopparty, S. Saraf, *On Proximity Gaps for Reed–Solomon Codes*, ePrint
  2025/2055 (the theorem used is its Theorem 4.6, "List correlated agreement, up to Johson
  bound" [sic]).
- "round-by-round knowledge soundness, the standard form since [CCHLRR19]" (line 62): round-by-round
  knowledge soundness is from [CMS19] Definition 8.5.
Proposed change: replace the entries by the BibTeX of this dossier's last section.

## B. The limits of the random-oracle model for this kind of protocol

### B.1 Annotated bibliography

**[KRS25] D. Khovratovich, R. D. Rothblum, L. Soukhanov, *How to Prove False Statements:
Practical Attacks on Fiat-Shamir*, CRYPTO 2025 (venue as cited by [Fen26]); Cryptology ePrint
Archive 2025/118 (last of 2 revisions 2025-12-11). https://eprint.iacr.org/2025/118.** Status:
current. Opened (verified).
- The attacked protocol `Π_{comm,d}` (§1.1.1, §2.1): GKR for a depth-`d` arithmetic circuit `C`
  chosen by the prover, plus a multilinear PCS on the witness `w` only; the first challenge is
  `r = h(⟨C⟩, comm(w), x, y)` (the *strong* transform: the circuit digest is hashed, §1.2
  "In this work we consider the strong variant").
- Theorem 1 (Basic Attack): "Let F be a finite field, comm an MLPCS over F computable by a depth
  d_comm arithmetic circuit and h a hash function computable by a depth d_h arithmetic circuit.
  Then, for every d ≥ d_comm + d_h + O(1) the FS_h(Π_{comm,d}) protocol is not adaptively
  sound." The attacking circuit computes the commitment and the Fiat–Shamir hash of its own
  transcript.
- Theorem 2 (Extended Attack): for any admissible circuit `C` and output `y*`, a functionally
  equivalent `C*` of depth `d + d_comm + O(d_h log ℓ)` with an accepting proof that `C*` outputs
  `y*`.
- Remark 3: "The GKR protocol is sometimes used to prove correctness of very specific and simple
  circuits, especially in the context of lookup arguments ..., in particular grand product
  arguments [Tha13]. Since these functionalities have a canonical representation, which is
  extremely simple, our attack does not seem to be applicable in this setting."
- §5 (Conclusions and Mitigations): "the GKR-based protocol, in contrast to other protocols in
  the literature, has the key property that the prover does not commit to the full computation
  trace ... the fact that the computation is not committed to also enables our attack";
  countermeasures: make the circuit family unable to compute the hash (depth, degree), or commit
  to intermediate values; [AY25]'s proof-of-work transform; "whether or not they are actually
  secure is an open question." Footnote 4: Expander (Polyhedra) introduced mitigations
  (`PolyhedraZK/Expander` pull request 184; **not opened**).
Relevance: the reference attack. Its three preconditions are (i) the statement (circuit) is
chosen adaptively by the prover after the hash is fixed, (ii) the proof system can prove
statements about computations that evaluate the Fiat–Shamir hash and the commitment, (iii) the
computation's internal values are not committed before the challenge, so the circuit can
"know" its own challenge without a fixed point.

**[Fen26] G. Fenzi, *How to prove more false statements: Fiat–Shamir limitations on (generated)
R1CS*, Cryptology ePrint Archive 2026/1838 (PDF of 2026-09-09).
https://eprint.iacr.org/2026/1838.** Status: current, preprint. Opened (verified, §1).
- Construction 1 (adaptive FS: `ρ_i := h(i, x, m_1, …, m_i)`); Definition 2 (a verifier is
  "semantic" and "fooled by delayed statement choice" if the prover can fix its messages
  round by round and pick an unsatisfiable generated statement `φ := Bind(x, ρ_1, …, ρ_k)` only
  after all challenges); Theorem 2: such a verifier's Fiat–Shamir compilation "is not adaptively
  sound for any sufficiently efficient hash function h".
- Abstract: the attacks "generalize to a wide class of protocols: any protocol in which a cheating
  prover can prepare an accepting transcript before the statement is bound"; variants of Spartan
  and Aurora for R1CS qualify; mitigation: "deriving the Fiat–Shamir challenges from the
  generated statement, rather than from the program that generates it, provably reduces the
  soundness of the compiled protocol to that of the underlying protocol for the non-generated
  relation" (Theorem 5.5, not read). §1.2 recommends "caution and careful audits in any setting
  in which such computations are fully or partially under the control of third parties (e.g.
  when compiling user code, automatic precompiles, AI-generated circuits, and similar)".
Relevance: extends the KRS precondition (iii) from "uncommitted wires" to "statement bound after
the transcript", which is the question to ask of a zkVM whose program is chosen by the prover.

**[AY25] G. Arnon, E. Yogev, *Towards a White-Box Secure Fiat-Shamir Transformation*, CRYPTO
2025 (major revision); Cryptology ePrint Archive 2025/329 (last of 2 revisions 2025-06-30).**
Abstract read only (**body unverified**): a Fiat–Shamir variant (XFS) combining Fiat–Shamir with a
new proof of work, "that aims to defend against a broad family of attacks". [KRS25] §5 says its
model "fails to capture our attack".

**[DMWG23] Q. Dao, J. Miller, O. Wright, P. Grubbs, *Weak Fiat-Shamir Attacks on Modern Proof
Systems*, IEEE S&P 2023; Cryptology ePrint Archive 2023/691.** Read by the earlier helper of this
task (notes in `probes/literature/G-notes.md`), not re-read by me: weak Fiat–Shamir (statement not
hashed) breaks adaptive knowledge soundness; 36 of about 75 surveyed repositories used it.
Relevance: the "strong" transform (statement in the first hash) is necessary even in the ROM;
[KRS25] and [Fen26] show it is not sufficient outside the ROM.

### B.2 Does leanVM fall in the scope of these attacks?

Facts at the pin:
- The statement is bound before any prover message: the chaining value starts at
  `compress(iv, public_input)` with `iv` the BLAKE2s of `"leanvm" ‖ len ‖ R1CS_DIGEST ‖
  bytecode_hash` (`crates/lean_vm/src/cpu/mod.rs:78-93`; `crates/fiat_shamir/src/lib.rs:60-74`:
  "the whole statement is bound before anything is sampled"). The bytecode *is* the statement (the
  verifier evaluates the bytecode multilinear itself, specification §8.5 "Bus" item 4), so there
  is no generation step between what is hashed and what is checked: [Fen26]'s mitigation holds by
  construction.
- The whole trace is committed before the first challenge: specification §8.5 "Commitment"
  (`08-end-to-end-protocol.tex:59-64`: every column, the memory limbs, the counts and Flock's
  packed witness are stacked into `q` and committed) precedes "Bus" (the first challenges `α`,
  `β`). KRS precondition (iii) fails: a guest program that wanted to predict its own challenges
  would have to compute the Merkle root of a stack that contains its own execution, a fixed point
  of BLAKE2s.
- GKR in leanVM is the grand-product GKR over leaves that are fingerprints of committed columns
  (specification §8.5 "Bus"), the case [KRS25] Remark 3 sets aside.
- KRS precondition (ii) holds by design: the Fiat–Shamir primitive is "*exactly* the VM's
  `Blake2s` opcode" (`lib.rs:9-24`) so that "a zkDSL program replays it with one `blake2s(...)`
  per step", which is what recursion needs (`cpu/mod.rs:78-81`: "a recursion guest carries the
  INNER program's IV in its public input"). The program is chosen by the prover (adaptive
  setting).

Conclusion (inference, not a theorem): leanVM satisfies (i) and (ii) and fails (iii) and the
[Fen26] precondition, so neither known attack applies. Its design follows every mitigation the
two papers name except the one that would cost recursion (making the circuit unable to compute
the hash). No published result says that a protocol outside these preconditions is secure with
a concrete hash; [KRS25] §5: "while we do not know attacks for protocols that do not satisfy
these properties, this does not mean that such attacks do not exist."

### B.3 What a random-oracle theorem does and does not say about this deployment

A Lean theorem of the blueprint's Layer 12-13 shape ("knowledge soundness of `verify` with error
`niError`", conditional on `FiatShamirSecurity`) says: *if* the 64-byte BLAKE2s map were a random
function, every prover making `t` queries to it would be caught except with probability
`niError(t)`. It does not say that the BLAKE2s-instantiated verifier is sound: there is no known
reduction from Fiat–Shamir soundness to collision resistance or any other standard property of
BLAKE2s, and the diagonalization attacks of [KRS25] and [Fen26] are, by construction, outside
the model (they use the code of `h`). Two consequences for the report:
1. The report should call T4's first half "sound in the random-oracle model for the BLAKE2s
   compression" and list the idealization as part of the trusted surface, not as a lemma to come.
   The blueprint lists Fiat–Shamir among "three named upstream results ... that ArkLib does not
   yet prove" (lines 28-30), which reads as if a proof would remove the assumption; the ROM step
   can be proved, but the model itself stays an assumption about BLAKE2s.
2. Recursion (T5, T6; out of the blueprint's scope, line 149) is where the model is weakest: the
   outer proof is about a computation that evaluates `h`. The architecture's classification of T6
   as an open research target is consistent with the literature.

### B.4 Findings of this section

**Finding: the blueprint does not state the scope of its random-oracle assumption.** Severity:
minor. Classification: an error of the blueprint (omission). Evidence: blueprint lines 28-30,
89-94, 153-157 at `b435631` name Fiat–Shamir as an ArkLib result to come, with no sentence on
what a ROM theorem cannot cover. Proposed change: after line 94 ("What is not attempted here:
..."), add: "The non-interactive theorems are in the random-oracle model for the 64-byte BLAKE2s
map that the chain, the Merkle trees and the grinding share. They do not cover attacks that use
the code of BLAKE2s ([KRS25], [Fen26]). leanVM binds the whole statement before the first
challenge and commits the whole trace before the first challenge, so the known attacks do not
apply; no theorem says more." Reason: the report's limitations section needs the exact scope, and
a reader of the blueprint should not believe that ArkLib's future theorem removes the idealization.

**Negative result.** I checked the three preconditions of [KRS25] and the one of [Fen26] against
the pinned Rust (`cpu/mod.rs:78-93`, `lib.rs:9-24, 60-74`) and the specification's step order
(`08-end-to-end-protocol.tex:55-73`); the statement binding and the commit-before-challenge order
hold at the pin. What would falsify this: a phase in which the prover sends a message that
depends on data not yet committed and that the verifier later treats as part of the statement.
None exists in §8.5 as I read it (the announced sizes are observed into the chain before the
commitment, `cpu/mod.rs:108-124`).

## C. WHIR, proximity gaps, and the regime leanVM claims

### C.1 Annotated bibliography

**[ACFY25] G. Arnon, A. Chiesa, G. Fenzi, E. Yogev, *WHIR: Reed–Solomon Proximity Testing with
Super-Fast Verification*, EUROCRYPT 2025; Cryptology ePrint Archive 2024/1586 (revised
2024-11-21; the ePrint listing still says "Preprint").** Opened (verified).
- Definition 4.5 (constrained Reed–Solomon code `CRS[F, L, m, ŵ, σ]`: codewords whose message
  `f̂` satisfies `Σ_{b∈{0,1}^m} ŵ(f̂(b), b) = σ`), Definition 4.6 (several constraints). This is
  how WHIR proves weighted inner-product claims `⟨W, f⟩ = c` (weight `ŵ(Z, X) = Z·W(X)`); §6.3.3:
  with `ŵ = Z·eq(z, ·)` "WHIR natively yields a multilinear polynomial commitment".
- Definition 4.9 (proximity generator with mutual correlated agreement, "MCA"); Lemma 4.10 and
  Corollary 4.11 (MCA holds in the unique-decoding regime, error `(ℓ−1)·2^m/(ρ·|F|)`).
- Conjecture 4.12: item 1, MCA "up to the Johnson bound" with error
  `(ℓ−1)·2^{2m}/(|F|·(2·min{1−√ρ−δ, √ρ/20})^7)`; item 2, MCA "up to capacity".
- Theorem 5.2: WHIR is an IOPP with round-by-round soundness errors `ε^fold`, `ε^out`, `ε^shift`,
  `ε^fin` **under the hypothesis** that the generator has MCA with bound `B*` and error `err*`
  and that the codes are `(ℓ, δ)`-list decodable.
- §6 parameter configurations: "(WHIR-UD) Unique Decoding"; "(WHIR-JB) Johnson Bound ... assume
  Item 1 in Conjecture 4.12 holds"; "(WHIR-CB) Capacity Bound ... assume Item 2"; each targets
  round-by-round error `2^{-λ}` with 256-bit hash output and uses proof of work.
Relevance: at publication, WHIR's list-decoding regime was conditional on a conjecture. Item 1
has since been proved ([BCHKS25] Theorem 4.6, [Hab25]); item 2 has been **disproved** ([CS25]).
leanVM does not use [ACFY25]'s theorem: it proves its own round-by-round theorem for a variant
(Annex B Theorem `thm:rbr`: no OOD sample at level 0, interleaved first level à la Ligerito,
weighted claims batched by powers of one challenge, plaintext final level).

**[BCHKS25] E. Ben-Sasson, D. Carmon, U. Haböck, S. Kopparty, S. Saraf, *On Proximity Gaps for
Reed–Solomon Codes*, Cryptology ePrint Archive 2025/2055 (one version, received 2025-11-06;
"Preprint").** Opened (verified). This is the paper the blueprint and Annex B cite as
"BCHKS25, Theorem 4.6".
- Theorem 1.5 (correlated agreement up to the Johnson radius): for `C = RS[F_q, D, k]`,
  `ρ = k/n` ("not the rate of the code, but off-by-1/n from it"), `γ ∈ (0, 1−√ρ)`,
  `η = 1−√ρ−γ`, `m = max(⌈√ρ/(2η)⌉, 3)`: if `|{z : Δ(u_0 + z·u_1, C) ≤ γ}| > a` with
  `a = [2(m+½)^5 + 3(m+½)γρ]/(3ρ^{3/2})·n + (m+½)/√ρ`, then `Δ([u_0, u_1], C²) ≤ γ`.
- **Theorem 4.6 ("List correlated agreement, up to Johson bound")**: for `C = RS_k[F_q, D, k]`
  of dimension `k+1`, `ρ = k/n` "the slightly reduced rate", any `u_0, …, u_M : D → F_q` and
  `γ ∈ (0, 1−√ρ)`, the set `E` of `z` for which some `A ⊂ D`, `|A| ≥ (1−γ)n`, has
  `(u_0 + z u_1 + … + z^M u_M)|_A ∈ C|_A` but `[u_0, …, u_M]|_A ∉ C^{M+1}|_A` satisfies
  `|E| ≤ M·([2(m+½)^5 + 3(m+½)γρ]/(3ρ^{3/2})·n + (m+½)/√ρ)` with
  `m = max(⌈√ρ/(1−√ρ−γ)⌉, 3)`. The paper's argument for it is a paragraph ("The proof of Theorem
  4.6 generalizes Section 3.2 as follows ..."), and §4.3 says a proof of MCA up to Johnson "is
  discussed in [Hab25]".
- Theorem 1.6 and Corollary 1.7 (negative): "for all `F_q` of characteristic 2" there are RS
  codes over `F_2`-linear subspace domains (the additive-NTT setting) with `δ = 15/16` for which
  proximity gaps at exactly the Johnson radius need `n^{2(1−ε)}` exceptional `z`: the linear
  bound of Theorem 1.5 is tight and stops at the Johnson radius.
- Theorem 1.9: beyond the list-decoding radius, proximity gaps with small loss need `a ≥ q/(2n)`.
Relevance: the single coding-theory input of leanVM's PCS analysis. Status: preprint, one
version, proof of Theorem 4.6 sketched.

**[Hab25] U. Haböck, *A note on mutual correlated agreement for Reed–Solomon codes*, Cryptology
ePrint Archive 2025/2110 (PDF of 2025-11-17, 7 pp.).** Opened (verified). Abstract: "We outline
how to generalize the Guruswami-Sudan list decoder analysis from [BCIKS20] in order to obtain a
'global' proximity gap, called mutual correlated agreement". Theorem 2: MCA up to
`γ = 1 − (1 + 1/(2m))√ρ` with `|E| ≤ (ℓ^7/3)·(ρn)^2`, `ℓ = (m+½)/√ρ` (quadratic in `n`). Remark:
"We have let the proof circulate in the community for about a year ... A more verbose update
incorporating the improvements from [BCH+25] will be posted thereafter." (No such update found
on ePrint; **unverified** negative.)
Relevance: the only written argument for MCA up to Johnson besides [BCHKS25]'s sketch; it gives
the quadratic bound, not the linear one leanVM uses.

**[ABF26]** (see A.2). Table 1 (July 2026) lists "`δ = J(δ_min(C)) − η`: `ε_mca(C, δ) ≤
n·poly(1/η)/|F|` [BCHKS25; Hab25; BCGM25; BCIKS20]" as known, and "`δ ≈ δ_min(C) − Ω(1/log n)`:
`ε_mca(C, δ) ≥ n^{Ω(1)}/|F|` [BCHKS25; KKH26; CGHLL26; Kam26], for a large enough F". Theorem 4.12
restates [BCHKS25] Theorem 4.6 **with the parameter `m = max(⌈√ρ⁺/(2η)⌉, 3)`**, the tighter
one of Theorem 1.5, not the printed `⌈√ρ/η⌉` (see finding "Three readings of the constant
in Theorem 4.6" below). Theorem 4.18 ([CS25] Theorem 3) and Theorem 4.19 ([BCHKS25] Corollary
1.7): "Note that the above theorem holds for fields of characteristic 2."

**[CS25] E. Crites, A. Stewart, *On Reed–Solomon Proximity Gaps Conjectures*, Cryptology ePrint
Archive 2025/2046 (revised 2025-12-19).** Abstract read (**body unverified**): "we prove that
the following conjectures are false: 1. The correlated agreement up-to-capacity conjecture of
[BCIKS20] (J. ACM'23), 2. The mutual correlated agreement up-to-capacity conjecture of WHIR, 3.
The list-decodability up-to-capacity conjecture of DEEP-FRI". Its Theorem 3 (as restated in
[ABF26] Theorem 4.18) bounds the CA error from below for RS codes whose domain lies in a subfield
`B ⊆ F`, which is leanVM's situation (domain in `K`, code over `E`); the bound bites only near
`H_{|B|}(δ) ≳ 1 − ρ`, i.e. near `δ ≈ 1/2` at rate `1/2`, far above leanVM's radius
`γ < 1 − √(1/2) ≈ 0.293` (my arithmetic).

**[KKH26] D. Krachun, S. Kazanin, U. Haböck, *Failure of proximity gaps close to capacity*,
Cryptology ePrint Archive 2026/782 (revised 2026-04-24).** Abstract read: for RS codes over
multiplicative subgroups of prime fields, at `θ = 1 − ρ − η`, `η = Θ_ρ(1/log n)`, an affine line
not entirely `θ`-close with `2^{Ω_ρ(1/η)}` close points. **[Kam26]** A. Kambiré, *Proximity Gaps
Conjecture Fails Near Capacity over Prime Fields*, arXiv:2604.09724 (2026): reference data from
[ABF26]'s bibliography only (**unverified**).

**[GG25] R. Goyal, V. Guruswami, *Optimal Proximity Gaps for Subspace-Design Codes and (Random)
Reed-Solomon Codes*, ePrint 2025/2054 (revised 2026-03-24); [BCGM25] S. Bordage, A. Chiesa, Z.
Guan, I. Manzur, *All Polynomial Generators Preserve Distance with Mutual Correlated Agreement*,
ePrint 2025/2051, CCC 2026; [Jo26] S. Jo, *Reed–Solomon Mutual Correlated Agreement Beyond the
Johnson Radius*, ePrint 2026/1432 (revised 2026-08-19); [DKT26] Q. Dao, S. D. Kominers, J.
Thaler, *Reed-Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs*,
ePrint 2026/2056 (received 2026-09-16).** Abstracts read only (**bodies unverified**). The
2026 positive results beyond Johnson are for random RS codes or subspace-design codes ([GG25]),
integer steps beyond the exact Johnson boundary at fixed reciprocal-integer rates ([Jo26]), or
"beyond Johnson, they require sufficiently large field characteristic" ([DKT26]), which excludes
characteristic 2. None of them is needed by leanVM's parameters.

**The Proximity Prize.** Ethereum Foundation, https://proximityprize.org/ (read 2026-09-29):
"$1,000,000 in awards to researchers who resolve the grand challenges" (the largest `δ*` with MCA
error at most `2^-128`, and the list-decoding analogue, for rates 1/2 to 1/16); submissions by
"11:59 pm UTC on December 31, 2027"; no award reported. The accompanying manuscript is [ABF26].
The Ethereum Foundation blog post of 2026-08-20 on the "better.codes" challenge was seen in
search results only (**unverified**).

**[DP24] B. E. Diamond, J. Posen, *Polylogarithmic Proofs for Multilinears over Binary Towers*,
EUROCRYPT 2026, doi:10.1007/978-3-032-25336-1_1; Cryptology ePrint Archive 2024/504 (last of 9
revisions 2026-05-14).** Abstract read (**body unverified**): introduces "ring-switching", a
sumcheck-based compiler from a large-field multilinear PCS to one over the ground field. leanVM
Annex B follows it for the additive NTT (`b-polynomial-commitment-scheme.tex:4, 90`) and Annex A
for ring switching.

**[LCH14] S.-J. Lin, W.-H. Chung, Y. S. Han, *Novel Polynomial Basis and Its Application to
Reed-Solomon Erasure Codes*, FOCS 2014, pp. 316-325, doi:10.1109/FOCS.2014.41; arXiv:1404.3458.**
Bibliographic data from dblp and the ACM listing (search results); content **not opened**. The
novel basis and additive FFT that Annex B §B.4 re-proves (Lemmas `lem:subspace`, `lem:chain`,
Proposition `prop:ntt`).

**[NA25] A. Novakovic, G. Angeris, *Ligerito: A Small and Concretely Fast Polynomial Commitment
Scheme*, Cryptology ePrint Archive 2025/1187 (2025-06-24).** Abstract read: "a small and
practically fast polynomial commitment and inner product scheme"; "any linear code for which the
rows of the generator matrix can be efficiently evaluated can be used". Annex B line 4: "The two
schemes coincide when WHIR is instantiated with interleaved codes and Ligerito with the
Reed--Solomon codes described here."

**[BRW26] B. Bünz, R. D. Rothblum, W. Wang, *Flock: Fast Proving for Batch Boolean
Computations*, Cryptology ePrint Archive 2026/1329 (received 2026-06-28, revised 2026-09-19; PDF
dated 2026-09-19, i.e. after the leanVM pin of 2026-09-03).** Opened (verified, §5 and Appendix
C). §5: "We target 100-bits of security by default ... the underlying IOP has round-by-round
soundness error [CCH+18] at most `2^{-100}` (unconditionally – without relying on any unproven
conjectures)"; PCS = Ligerito "extend[ed] ... to the list-decoding regime (see Appendix C)", "up
to the Johnson bound [BCI+23, BCH+25], together with interleaving stability [Jo26], in
combination with a small amount of grinding". Appendix C.3: "We sketch the opening phase's
soundness analysis"; Theorem 8 ("MCA up to Johnson bound, adapted from [BCH+25, Theorem 4.6]")
with `μ = max(⌈√ρ/(2η)⌉, 3)`; Lemma 9 ("MCA commutes with list decoding", error `ε`, "Follows
from [Jo26] and [ACFY25, Lemma 4.13]"); Remark 11 (no OOD sample at the initial commitment costs
the outer protocol a factor `L`).

### C.2 What leanVM claims, and against which theorem

- Regime: Johnson list decoding with explicit slack, **provable, not conjectured**: Annex B
  opening (`b-polynomial-commitment-scheme.tex:4`: "with a round-by-round soundness analysis in
  the Johnson list-decoding regime"); Theorem `thm:rbr` (`:139-152`) with the per-message errors
  batching `(J_i − 1)L_i/|E|`, fold `2L_i/|E| + 2^{ℓ_i−j} ε_i`, OOD `C(L_i, 2)·μ_i/|E|`, query
  `(1 − γ_i)^{t_i}`, final batch `t_{r−1}/|E|`, tail `2/|E|`; `whir_config.rs:314-337` ("That
  analysis is always the Johnson radius with explicit slack `eta` ... The MCA theorem
  (`thm:mca-johnson` = BCHKS25 Thm 4.6)"); `analysis_version` example
  `"ben_sasson_2025_thm_4_6"` (`:409-412`; the production derivation sets `"bchks25_thm_4_6_exact_reduced_rate_row_union_optimized_eta"`, `:961`).
- The MCA statement Annex B uses (`:176-185`, Theorem `thm:mca-johnson`) is [BCHKS25] Theorem 4.6
  with `M = 1`, the same event and the same bound, including the printed parameter
  `m = max(⌈√ρ/η⌉, 3)`; the "slightly reduced rate" `ρ = (k−1)/n` is handled explicitly (Annex B:
  "[BCHKS25] parametrize by the degree bound `k − 1`, not the dimension `k`"; Rust
  `reduced_rate`, `whir_config.rs:421-429`). The char-2 conversion from the affine line to the
  fold `(1−s)u_0 + s u_1` is argued in Annex B's footnote (`:158`). I checked the formula term by
  term against the PDF: they agree.
- ArkLib's admitted theorem at both pins (`ArkLib/Data/CodingTheory/ProximityGap/
  CapacityBounds.lean:180-222` at `7653a901`, `rs_mcaError_le_in_johnson_range`, `sorry --
  ABF26-T4.12; external admit [BCHKS25 Thm 4.6].`) states the same printed bound for the affine
  line and says: "The multiplicity `m` is the source's printed, deliberately loose choice; the
  source's own proof ... supports the tighter `m = ⌈√ρ/(2·(1-√ρ-δ))⌉` ... The admit stays pinned
  to the printed statement".
- Not used: WHIR's conjectures ([ACFY25] Conjecture 4.12), any capacity-regime conjecture, the
  unique-decoding theorem (Annex B `:174`: "We record Theorem~\ref{thm:mca-udr} only for
  comparison").
- 128-bit target per verifier message, with 17 bits of grinding on the query rounds (A.1).

### C.3 Synthesis

1. **What is proved about WHIR.** [ACFY25] proves round-by-round soundness of WHIR as an IOPP for
   constrained RS codes, unconditionally in the unique-decoding regime and conditionally on its
   Conjecture 4.12 in the list-decoding regime. The Johnson half of that conjecture is now a
   theorem ([BCHKS25] Theorem 4.6; [Hab25] Theorem 2 with a quadratic bound), with the caveat
   that both are preprints and the linear-in-`n` bound that leanVM's parameters use is argued in
   a paragraph. The capacity half is false ([CS25], [KKH26]). [ABF26] (July 2026) treats the
   Johnson-range bound as established.
2. **leanVM's claimed regime is the right one**: the only provable list-decoding regime, with an
   explicit slack `η > 0`, which also stays clear of the characteristic-2 counterexamples at
   exactly the Johnson radius ([BCHKS25] Corollary 1.7, which applies to `F_2`-subspace
   domains such as leanVM's) and of the subfield lower bounds of [CS25].
3. **The soundness proof leanVM relies on is its own Annex B**, not a published theorem: the
   variant (no OOD at level 0, weighted claims, the `2^{ℓ−1}` row union of Lemma `lem:fold-list`,
   the final plaintext level) is analysed only there and, for its Ligerito cousin, sketched in
   [BRW26] Appendix C. The blueprint's Layer 11 statement (`whirOpen_rbrSoundness (mca :
   McaJohnson) : … (whirError params) -- Theorem B.2, per message`, line 1175) formalizes Annex B's
   theorem, which is the right target. A Lean proof of it would be the first complete,
   machine-checked proof of this variant.
4. **Three readings of the constant in Theorem 4.6** exist: the printed `⌈√ρ/η⌉` ([BCHKS25],
   leanVM Annex B and Rust, ArkLib's admit), and `⌈√ρ/(2η)⌉` ([ABF26] Theorem 4.12, [BRW26]
   Theorem 8; ArkLib's docstring says the source's proof supports it). The printed one is the
   larger error bound, so leanVM and ArkLib are on the safe side; a proof in Lean of the printed
   statement suffices. `whir_config.rs:460-465, 1004-1005` record the same discrepancy with Flock.
5. **WHIR as a PCS for weighted claims**: [ACFY25] Definitions 4.5-4.6 (constrained codes)
   are the published form; Annex B works directly with weighted claims `⟨W_t, g_U⟩ = c_t` and
   MLE-friendly column weights (Lemma `lem:colweight`). The blueprint's `WeightedClaim` and
   `encode_column_weight` (Layer 11, lines 1170-1173) follow Annex B.
6. **Binary fields.** The proximity-gap theorems are stated for RS codes over any finite field
   and any domain `D ⊆ F_q` ([BCHKS25] Theorems 1.5, 4.6), so the additive-NTT domain in `K` and
   the code over `E` are covered; the novel basis is only an encoding choice (Annex B
   Definition `def:enc`: "The message is read *directly* as novel-basis coefficients").

### C.4 Findings of this section

**Finding: the one coding-theory input is a preprint theorem with a sketched proof.** Severity:
note (for the report's trusted-surface section). Classification: not a divergence; a fact about
the assumption. Evidence: [BCHKS25] §4.3 (one-paragraph argument for Theorem 4.6, single ePrint
version of 2025-11-06, "Preprint"); [Hab25] (an "outline", quadratic bound). Proposed change:
the blueprint's out-of-scope item (lines 153-155) and the interface `McaJohnson` (line 1176-1177)
should say "a preprint theorem whose proof is sketched ([BCHKS25] §4.3; full argument for the
quadratic bound in [Hab25]); peer review pending as of 2026-09", so that the report's trusted
surface does not present it as settled mathematics. A Lean proof would change that status.

**Finding: three readings of the constant in Theorem 4.6.** Severity: note. Classification: none
needed (leanVM follows the printed, weaker bound). Evidence: C.3 item 4. Proposed change: none to
the blueprint; the report should record that `McaJohnson` must be stated with the printed
parameter (as ArkLib's admit is) and that Flock's paper quotes a stronger bound than the printed
theorem.

**Negative result.** I compared, term by term, Annex B Theorem `thm:mca-johnson`
(`b-polynomial-commitment-scheme.tex:176-185`) and the Rust's `paper_thm_ca_johnson_log_a`
docstring (`whir_config.rs:431-444`) with [BCHKS25] Theorem 4.6 (PDF of 2025-11-06, §4.3) at
`M = 1`: the event, the numerator, the parameter `m` and the reduced rate agree. I did not check
the Rust's arithmetic of the bound or its `η` search.

## D. The arithmetization and its arguments

### D.1 Annotated bibliography

**[M3] Irreducible, *Multi-Multiset Matching (M3)*, Binius documentation,
https://www.binius.xyz/basics/binius-v0/m3/ and `/definition` (undated web pages, read
2026-09-30).** Opened (definition page, via a fetch summary). "A *channel* is simply an abstract,
stateful bidirectional 'receptacle' of data, which features a fixed width and type signature";
each flushing rule names "An ordered sequence of columns ... A channel. A direction (*push* or
*pull*)"; "To be *balanced* entails simply that its pushes exactly match its pulls. That is, the
respective *multisets* of its pushed and pulled elements (i.e., ignoring order, but counting
multiplicity) are equal." No soundness statement or error bound on these pages. Status: the
pages describe "binius-v0"; Binius has since moved to Binius64 ([BRW26] §1 compares Flock with
"Binius64, the prior state of the art"), so this is a historical design document.
Relevance: M3 balance is a **combinatorial** multiset equality, which is what the blueprint's
`M3Holds` states ("the pushed and pulled bus tuples read out of `q` are the same multiset",
line 71) and what leanISA's `BalancedPair` counts in ℕ. It is not a field identity; in
characteristic 2 a field-valued multiplicity sum (LogUp, Clean's `BalancedInteractions`) cannot
express it (brief §7; compare the prime-field guards in F below).

**[Tha22] J. Thaler, *Proofs, Arguments, and Zero-Knowledge*, Foundations and Trends in Privacy
and Security 4(2-4), 2022; author's PDF of 2023-07-18,
https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf.** Opened (verified; the PDF has
minor stream errors but extracts). Statements used:
- Proposition 4.1 (sum-check): soundness error `δ_s ≤ v·d/|F|` for a `v`-variate polynomial of
  degree at most `d` in each variable.
- §4.5.2 (reducing several evaluations of one polynomial to one), §4.6 (GKR).
- §6.6.2 ("Ensuring Memory Consistency via Fingerprinting", pp. 98-99): Blum et al.'s offline
  memory checking reduces memory consistency to multiset equality; permutation-invariant
  fingerprint `p_a(x) := ∏_{i=1}^m (a_i − x)`, equality of multisets tested at a random point,
  error `m/|F|`; each (location, value) pair first injected into `F`.
- §5.2: the "grinding attack" on Fiat–Shamir: an interactive protocol with 60 bits of security
  falls to about `2^60` hash evaluations after compilation; "the interactive protocol should be
  configured to well over 80 bits of statistical or interactive" security.
Relevance: the grand product is Thaler's fingerprint with a random linear combination `π_α` of
the tuple coordinates as the injection. The blueprint's acceptance test 1 (line 1266-1268:
"`π_α` is multilinear in `α : E^4`, so a leaf has total degree 4 in `(α, β)` and Theorem 5.1's
error is `4·2^μ/|E|`") is Schwartz–Zippel applied to the difference of the two products of
`2^μ` factors `β − π_α(t)`: if `π_α(t)` is the multilinear extension of the 16-coordinate tuple
evaluated at `α ∈ E^4`, each factor has total degree 4 in `(α, β)`, the difference of products
has total degree at most `4·2^μ`, hence the error (the degree bookkeeping against the
specification's Theorem 5.1 belongs to the gt-bus dossier; I did not re-check it). The
blueprint cites "Thaler, chapter 4, for GKR and grand products" (line 1538); grand products via
fingerprints are in §6.6.2, not chapter 4.

**[BEGKN94] M. Blum, W. Evans, P. Gemmell, S. Kannan, M. Naor, *Checking the Correctness of
Memories*, Algorithmica 12(2-3):225-244, 1994.** Not opened (bibliographic data from leanVM's
`refs.bib`, which the specification cites for memory checking). The origin of offline memory
checking.

**[Tha13] J. Thaler, *Time-Optimal Interactive Proofs for Circuit Evaluation*, CRYPTO 2013.**
Not opened; cited by [KRS25] Remark 3 as the source of GKR for grand products. **[SL20] S. Setty,
J. Lee, *Quarks: Quadruple-efficient transparent zkSNARKs*, ePrint 2020/1275; [STW24] S. Setty,
J. Thaler, R. Wahby, *Unlocking the lookup singularity with Lasso*, EUROCRYPT 2024, ePrint
2023/1216; [PH23] S. Papini, U. Haböck, *Improving logarithmic derivative lookups using GKR*,
ePrint 2023/1284 (last revised 2025-02-20).** Abstracts read only (**bodies unverified**). Quarks
introduced the grand-product argument over a committed tree; Lasso proves grand products with
GKR ([Tha13]); [PH23] is the fractional-sum (LogUp) GKR. None is characteristic-2-specific; LogUp
needs characteristic larger than the number of lookups, grand products do not.

**Radix-4 GKR.** I found no paper; the arity-four product tree appears in implementation
trackers (`worldfnd/BitZ` issues 107 and 129, search results only, **unverified**) and in
leanerVM's own issue #46. The blueprint's description (layer schedule "for odd `μ` the root layer
is radix 2 and the rest radix 4", acceptance test 17, line 1314-1316) is transcribed from the
Rust (`crates/lean_vm/src/gkr.rs`), Category B; the soundness of a 4-ary layer is the sumcheck
bound for a degree-5 round polynomial (`eq · Q00 · Q10 · Q01 · Q11`) plus the combiner
challenges, which is elementary but has no published statement to cite.

**[Gru24] A. Gruen, *Some Improvements for the PIOP for ZeroCheck*, Cryptology ePrint Archive
2024/108 (2024-01-24).** Opened (verified, §3). §3.1 "Sending less data": "P can simply not send
`v_{i+1}(1)` and let V fill in this value via `v_{i+1}(1) = v_i − v_{i+1}(0)`"; §3.2: factor the
known `eq` weight out of the round polynomial, so that `deg v'_i = deg_X v_i − 1`, with the
modified check `(1 − α_i)v'_{i+1}(0) + α_i v'_{i+1}(1) = v'_i`, which "improves both the
efficiency and security of the protocol" (soundness in its §A.3, not read). Relevance: the
blueprint's acceptance test 8 ("Degree three, three scalars ... `decode` reconstructs `c_1`",
line 1287-1289) and `RoundPoly.decode (d) (claim) (eq? : Option E)` (line 1212) are these two
tweaks; the per-round error is `d/|E|` for the plain form and, by the same root-counting argument on
`v'` of degree `d − 1`, `(d − 1)/|E|` for the eq-factored form (my inference; Gruen's §A.3 not
read), so a Lean statement with `3/|E|` per table round is safe for either.

**[DT24] Q. Dao, J. Thaler, *Constraint-Packing and the Sum-Check Protocol over Binary Tower
Fields*, ePrint 2024/1038 (revised 2024-07-11).** Abstract read (**body unverified**): the
zerocheck `g(x) = eq(r, x)·p(x)` with `p` over a small field and `r` from a large extension;
cited by the leanVM specification.

**[HJRRR25] T. Hemo, K. Jue, E. Rabinovich, G. Roh, R. D. Rothblum, *Jagged Polynomial
Commitments (or: How to Stack Multilinears)*, EUROCRYPT 2026 (minor revision); ePrint 2025/917
(revised 2026-04-13).** Abstract read (**body unverified**): commits to all of a zkVM's tables as
one polynomial. Annex B `:387` cites it as the way to avoid leanVM's remaining padding inside the
stack. Relevance: the published analogue of the blueprint's one-column stack `q`.

**[BRW26] Flock** (see C.1). The local source for the Flock phase is the specification's Annex C
at the pin; the paper's version of 2026-09-19 postdates the pin (2026-09-03) and should not be
used to judge faithfulness. Its §5 claim "round-by-round soundness error ... at most `2^{-100}`
(unconditionally ...)" targets 100 bits, leanVM targets 128 (`whir_config.rs:38`).

### D.2 Synthesis

- **Multiset equality, not a field identity.** M3 and the memory-checking literature state
  balance as equality of multisets. The grand product reduces it to a polynomial identity in the
  multiset challenge `β`, which is sound in every characteristic (factorization of
  `∏(β − a_i)`), whereas LogUp-style sums of multiplicities are sound only when the field
  characteristic exceeds the total multiplicity; in characteristic 2 they collapse to parity.
  leanVM's choice of grand products is forced by its field, and the blueprint's combinatorial
  `M3Holds` is the right relation to extract.
- **Error of the fingerprinted product.** The combined bound is Schwartz–Zippel on the
  difference of the two products as a polynomial in `(α, β)`; the review should check the degree
  bookkeeping in the gt-bus dossier rather than here.
- **Zerocheck at a recycled point.** I found no published analysis of reusing the GKR's final
  point `ζ` as the zerocheck point. The standard argument is coordinate-wise: each coordinate of
  `ζ` is a fresh uniform challenge drawn after `q` is committed, and a nonzero multilinear
  `Σ_x eq(ζ, x)·C(x)` survives each coordinate except with probability `1/|E|`, which can be
  charged to the GKR round that draws that coordinate. The blueprint's acceptance test 6 (lines
  1281-1283) does exactly this ("The state function of Layer 7 charges the zerocheck to Layer 6's
  challenges"). A Lean proof would be the first written statement of it that I know of.
- **Gruen's tweaks** change the wire format and slightly improve the per-round error; the
  blueprint follows the Rust's encoding (Category B), which is right.

### D.3 Findings of this section

**Finding: the blueprint's citation for grand products points to the wrong chapter.** Severity:
minor. Classification: an error of the blueprint. Evidence: line 1538 ("J. Thaler, *Proofs,
arguments, and zero-knowledge*, chapter 4, for GKR and grand products"); the multiset
fingerprint is [Tha22] §6.6.2; GKR is §4.6. Proposed change: "J. Thaler, *Proofs, Arguments, and
Zero-Knowledge* (2022): Proposition 4.1 (sum-check), §4.6 (GKR), §6.6.2 (multiset equality by
fingerprinting); [Tha13] and [STW24] for GKR-based grand products."

**Negative result.** The blueprint's references for the arithmetization (M3, Thaler, Gruen via
the specification) match what the specification's `refs.bib` cites; I found no published source
that the blueprint should have used and did not (radix-4 GKR and point recycling have none).

## E. The Lean libraries, and the obligation outline

Revisions: ArkLib `dca90385` (pin at `b435631`) and `7653a901` (pin after `144c5aa`); VCVio
`a4232d08`, CompPoly `572f9973`, Clean `42fe4b26` (the new pins, read in `.lake/packages/`).

### E.1 ArkLib

**What is published.** No paper (search on 2026-09-30 found none; **unverified negative**). The
primary sources are the repository (https://github.com/Verified-zkEVM/ArkLib), its blueprint
(`blueprint/src/`), its wiki (`docs/wiki/`) and a use-case page on lean-lang.org (search result,
not opened). The README at `7653a901` describes the design: "An **IOR** (called
`OracleReduction` in our formalization) is an interactive protocol between a prover and a
verifier to reduce a relation `R_1` on some public statement & private witness to another
relation `R_2`"; "The verifier may *not* see the messages sent by the prover in the clear, but can
make oracle queries to these messages using a specified oracle interface"; IORs compose
sequentially and "lift" into larger contexts; then "the **(interactive) BCS transform**" and "the
**Fiat-Shamir transform** ... We will formalize the **duplex-sponge** version of Fiat-Shamir". Its
section "Active Formalizations" is dated "last updated: 7 August 2025".

**Round-by-round knowledge soundness in ArkLib** (same text at both pins; line numbers at
`dca90385`, `+1` to `+8` at `7653a901`). An `Extractor.RoundByRound` (`RoundByRound.lean:77-86`)
carries intermediate witness types `WitMid`, a map `extractMid` from the witness after round
`m+1` to the witness before it, and `extractOut` from the output witness; a
`KnowledgeStateFunction` (`:164-189`) is a predicate on (round, statement, partial transcript,
intermediate witness) that holds initially exactly on the input relation, is preserved backwards
across prover moves through `extractMid`, and holds at the end whenever the verifier can output a
statement in the output relation. `rbrKnowledgeSoundnessWorstCaseWith` (`:553-570`):

```lean
def rbrKnowledgeSoundnessWorstCaseWith
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (WitMid : Fin (n + 1) → Type)
    (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∀ stmtIn : StmtIn,
  ∀ i : pSpec.ChallengeIdx,
  ∀ transcript : Transcript i.1.castSucc pSpec,
    Pr[fun challenge =>
      ∃ witMid,
        ¬ kSF i.1.castSucc stmtIn transcript
          (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
          kSF i.1.succ stmtIn (transcript.concat challenge) witMid
      | $ᵗ (pSpec.Challenge i)] ≤ rbrKnowledgeError i
```

In words: for every statement, every challenge round and every partial transcript before it, the
probability over a uniform challenge that some witness makes the state true after the challenge
while the extracted witness does not make it true before is at most that round's error. This is
[ABF26] Definition A.5 with the differences ArkLib's docstring lists (`:154-163`), without A.5's
time bound, and in the worst-case-over-prefixes form (stronger than the averaged
`rbrKnowledgeSoundness`, `:416-436`). It matches [CY24] Definition 31.1.6 except that the
extractor may use intermediate witnesses and is not required to be polynomial-time.

**Fiat–Shamir and BCS in ArkLib.** The basic transform queries a challenge oracle on the input
statement and all messages so far (`FiatShamir/Basic.lean:91` at both pins: `query (spec :=
fsChallengeOracle StmtIn pSpec) ⟨⟨j, hDir⟩, ⟨stmtIn, messages⟩⟩`), i.e. the *strong* transform
by construction; the file's docstring says "State-restoration (knowledge) soundness implies
(knowledge) soundness" is to be shown and that it "mostly follows the treatment in the
Chiesa-Yogev textbook". At `7653a901` the `FiatShamir/` folder still contains 18 occurrences of
`sorry` and `BCSTransform` is commented out (`ArkLib/OracleReduction/BCS/Basic.lean:59, 79-81`),
consistent with the blueprint's ledger entry for Fiat–Shamir and BCS (line 263).

**Coding theory in ArkLib.** `rs_mcaError_le_in_johnson_range` (`ArkLib/Data/CodingTheory/
ProximityGap/CapacityBounds.lean:203` at both pins) is admitted (`sorry -- ABF26-T4.12; external
admit [BCHKS25 Thm 4.6].`) with the printed constant; see C.2.

Relevance: the blueprint's master theorems use exactly this definition (blueprint line 239 at
`b435631`), which is the right notion (per-challenge error, straight-line extractor). What the
definition does not give is an efficiency bound, and what ArkLib does not give yet is any
compilation theorem; the construction ArkLib's compilation will target (basic FS on the full
prefix, then a duplex sponge) is not leanVM's (a BLAKE2s chain with tags; see A.2 [CO25] and the
finding in E.6).

### E.2 VCVio

**[TDWHH26] D. Tuma, Q. Dao, J. Waters, A. Hicks, N. Hopper, *VCVio: Verified Cryptography in
Lean via Oracle Effects and Handlers*, Cryptology ePrint Archive 2026/899 (revised
2026-05-10).** Abstract read (**body unverified**): "a computation with oracle access is the free
monad over the polynomial functor determined by the oracle specification, exposing its
interaction history as an explicit syntax tree. Caching, logging, reprogramming, and seed
pre-sampling become handler combinators; rewinding reduces to deterministic transcript replay";
a relational program logic built on Loom. README at `a4232d08`: `OracleComp`, `ProbComp`,
`evalDist`, `simulateQ` ("implementations of random oracles, query logging, reductions"), and
transforms "like Fiat-Shamir and Fischlin". Relevance: ArkLib's probabilities (`Pr[… | …]`,
`$ᵗ`) are VCVio's; the brief (§8) records that VCVio's probability API changed between the two
pins, so any statement quoted from the leanerVM bridges must name its revision.

### E.3 CompPoly

No paper found (**unverified negative**). README at `572f9973`: "A formally verified library for
computable polynomial operations over finite fields and general rings", with `CMvPolynomial`,
`CMlPolynomial`/`CMlPolynomialEval` ("computable multilinear polynomials represented either by
monomial-basis coefficients or by evaluations over `{0,1}^n`"), `CPolynomial`, `CBivariate`, each
with a ring equivalence to the Mathlib type. Relevance: the carrier of the stacked column and its
evaluation (blueprint Layer 1).

### E.4 Clean

**[Del25] G. Dell'Immagine, *Introducing Clean, a formal verification DSL for ZK circuits in
Lean4*, zkSecurity blog, 2025, https://blog.zksecurity.xyz/posts/clean/** (cited by [KSHC26];
**not opened**). Repository https://github.com/Verified-zkEVM/clean at `42fe4b26` (commit of
2026-09-29). Definitions (`Clean/Circuit/Formal.lean:158-185` at `42fe4b26`): circuit
`Soundness` = for every environment and every input satisfying `Assumptions`, if the constraints
hold then `Spec input output` and the operations' `Requirements` hold; `Completeness` = for every
honest prover environment using the default witness generators, assumptions imply that the
constraints hold. For ensembles of tables (`Clean/Air/FlatEnsemble.lean`, at `42fe4b26`):

```lean
def Statement (ens : Ensemble F PublicIO) (publicInput : PublicIO F) : Prop :=
  ∃ witness : EnsembleWitness ens,
    witness.publicInput = publicInput ∧
    witness.Constraints ∧
    witness.BalancedChannels
```

with the docstring "TODO: we currently assume a proof system that already provides us with the
fact that the total interaction length doesn't overflow (as part of `BalancedChannels`)", and
`Ensemble.Soundness ens Assumptions Spec := ∀ publicInput, Assumptions publicInput →
ens.Statement publicInput → Spec publicInput`. Relevance: `Ensemble.Statement` is Clean's version
of the hand-off from the arithmetization to the proof system: a relation on a *trace* (rows per
table) with field-valued channel balance. The blueprint's adaptor (`satisfiedBy_witnessOf`,
`m3Holds_stackOf`) targets leanISA's `SatisfiedBy`, which states balance combinatorially
(`BalancedPair`, counted in ℕ) because Clean's field balance is vacuous in characteristic 2 (brief
§7); the Clean docstring's "the proof system provides the interaction-length bound" assumption
has no meaning in characteristic 2, where no length bound makes a field sum of multiplicities
faithful.

### E.5 The obligation outline: arXiv 2607.23752v1

**[KSHC26] A. Kolozyan, T. Sorger, A. Hicks, S. Chaliasos, *ZKP Security Tools and Verification:
Coverage, Effectiveness, Adoption, and Challenges*, arXiv:2607.23752v1 [cs.CR], 26 July 2026, 14
pp.** https://arxiv.org/abs/2607.23752. Status: v1, preprint. Opened (verified, §VI in full).
Affiliations: MPI-SP, KTH, Ethereum Foundation, University of Athens & zkSecurity.

Its obligation hierarchy (§VI-A, "Verification goals"): "Verifying a zkVM means establishing
end-to-end soundness and completeness guarantees".
- *Soundness* "depends on the constraints, the proof system, and the verifier: the witness
  generator and prover are untrusted", and splits into: **CC-S** "Constraint correctness,
  soundness direction ... Every witness satisfying the constraints corresponds to an execution of
  the ISA (constraints ⇒ ISA), checked against a reference specification", the same for each
  precompile; **PS** "Proof-system soundness. The cryptographic argument prevents a malicious
  prover from forging a proof of a false statement that an honest verifier would accept, for some
  security parameter (e.g., 128 bits)"; **VC** "Verifier correctness. The verifier rejects invalid
  proofs. The verifier used for recursive aggregation carries the same obligation, but is
  implemented via constraints". The guest program is "a mostly separate concern".
- *Completeness* splits into **CC-C** (ISA ⇒ constraints), **WC** "Witness-constraint
  consistency. The witness generator produces a satisfying witness for every execution", and
  **PC** "Prover completeness. The prover produces a proof the verifier accepts. Likewise for the
  recursion prover".
- §VI-B classifies model creation as extraction (E), translation through a compiler IR (T),
  hand-written model (M: "Model-implementation correspondence must be established separately,
  typically by testing rather than formal equivalence") and correctness by construction (CbC:
  "Clean ... follows this route and proves both CC and WC"), and describes the TCB as the
  verification target (model–code gap, reference specification) plus the tools, including "the
  theorem statements themselves: a proof of a vacuous or misstated theorem passes the kernel while
  establishing nothing".
- §VI-C (gaps): "No zkVM has end-to-end formal verification"; "the witness generator, the
  lookup/permutation arguments, the proof-system backend, and the on-chain verifier remain largely
  unverified"; "Shifted complexity ... lookup arguments ... end-to-end verification must then also
  cover the lookup argument's specification, its underlying cryptography, and the well-formedness
  of its tables"; ArkLib and VCVio "aim to formalize" the building blocks, "Bridging such a library
  with production-grade implementations has not yet been done"; "The best verified verifier
  result so far targeted ZKsync Era ... and proved only that the on-chain verifier contract matches
  a specification for which no soundness properties have been verified [48]".
- Table V: proof-system soundness by hand-written model in "Lean (ArkLib, VCVio)"; verifier
  correctness by hand-written model in "EasyCrypt" [48].

**Comparison with the eight target theorems** (`docs/architecture.md` at `b435631`, lines 63-70,
203-380):

| [KSHC26] | leanerVM | Comment |
| --- | --- | --- |
| CC-S, CC-C | T1 `constraints_iff_isa` (both directions, lines 203-228) | Same split; leanerVM adds the named program-shape hypothesis `WellFormedBytecode`. |
| CC for precompiles | inside T1 ("BLAKE2s opcode", lines 441-445) | Same obligation, leanVM's one precompile. |
| WC | T2 `witnessGen_correct` (lines 230-236) | Same. |
| PS | T4 first half, `baseVerifier_extractsExecution` (lines 261-273) | T4 is stated as extraction of `SatisfiedBy` and composed with T1; the paper's PS is plain soundness. leanerVM's T4 bundles PS with the refinement of the *Lean* executable verifier. |
| VC | T4's "executable-verifier refinement" (line 273) and T5 for the recursive verifier | The paper's VC for the *deployed* (Rust, Python, on-chain) verifier has no T-theorem in leanerVM: it is covered by differential tests (blueprint Layer 12 tests), i.e. the paper's category (M) with correspondence "by testing". |
| PC | T4's completeness dual (`baseProver_complete`) and T8 | For the Lean honest prover, a specification; the paper's PC concerns the running prover. |
| (none) | T3 exact guest correctness | The paper treats the guest as "a mostly separate concern"; leanerVM makes it a theorem because the application (signature aggregation) is fixed. |
| (none) | T6 recursion extraction (open), T7/T8 end-to-end | The paper does not discuss knowledge extraction through recursion; leanerVM names it as open research, consistent with B.3. |
| TCB of tools, statements as TCB | AGENTS.md guardrails (axiom audit, non-vacuity reviews) | Matched in practice, not in `architecture.md`'s obligation list. |

Conclusions: the eight theorems refine the paper's six goals (CC-S, CC-C, PS, VC, WC, PC); the
main difference is that leanerVM states PS as knowledge extraction into the arithmetization's
relation (which is what makes recursion possible later) and does not claim VC for the deployed
verifier. The paper's warning about "shifted complexity" applies directly to the bus: leanerVM
splits it into a combinatorial part inside T1 (`BalancedPair`) and a cryptographic part inside T4
(the bus phase), which is sound practice provided the relation `M3Holds` carries exactly the
combinatorial balance that T1 consumes (see F).

### E.6 Findings of this section

**Finding: the upstream Fiat–Shamir and BCS theorems will be about other constructions than
leanVM's chain.** Severity: major (the interface cannot be discharged by "the upstream theorem" as
the blueprint plans). Classification: a deviation forced by an upstream library, to be recorded
with its workaround. Evidence: blueprint ledger entry for Fiat–Shamir and BCS (line 263: "Named
interfaces `FiatShamirSecurity` and `BcsSecurity` with the upstream theorem as witness
obligation") and `verify_iff_compiled` ("`Verifier.fiatShamir (leanVmIopp …).verifier …` accepts
… under the BLAKE2s challenge oracle", lines 1218-1221); ArkLib's basic transform queries one
random oracle on `(statement, all messages)` and its planned efficient transform is a duplex
sponge (README at `7653a901`); [CY24] Construction 25.1.1 uses `2k` independent random oracles
(one per round for the chain, one per Merkle tree); leanVM uses **one** 64-byte map `f =
BLAKE2s(a‖b)` for the chain (tags 1-4 in lane 3), the Merkle inner nodes (`hash_pair`, untagged,
`merkle.rs:44-51`) and the grinding, with a Merkle–Damgård chaining value; [CO25] §2.3 shows that
indifferentiability arguments do not transfer knowledge soundness. So the random-oracle theorem
that discharges `FiatShamirSecurity` has to be proved for leanVM's chain (or a refinement lemma
from the chain with `f` a random oracle to ArkLib's prefix oracle has to be proved, which is not a
standard result), and `BcsSecurity` has to handle one oracle shared by the chain and the Merkle
nodes with untagged node inputs. Proposed change: in the ledger entry (line 263) replace "with the
upstream theorem as witness obligation" by "with witness obligations the upstream theorems do not
discharge as stated: ArkLib's transforms use a random oracle on the full prefix (basic) or a
duplex sponge, and the textbook BCS analysis ([CY24] Construction 25.1.1, Theorem 25.2.1) uses
independent oracles per role; leanVM uses one BLAKE2s map for the chain, the Merkle nodes and the
grinding. The chain lemma (a Merkle–Damgård chain of a random 64-byte map, tagged absorb/squeeze
blocks, as a random oracle on transcript prefixes for the purposes of state-restoration
soundness) and the role-separation lemma are owed here." I did not analyse whether a
cross-role input (a Merkle node whose 64-byte input is also a valid chain block) can be
exploited; it is at least a proof obligation. **Unverified**: whether a later ArkLib revision
(after `7653a901`) provides a chain-based transform.

**Finding: the obligation outline is not attributed.** Severity: minor. Classification: an error
of the documentation (outside the blueprint). Evidence: `docs/architecture.md` at `b435631` uses
the labels CC-S, CC-C, WC (lines 101, 128, 426-433) that [KSHC26] §VI-A defines (arXiv v1 of
2026-07-26), and does not cite it (`git grep 2607.23752` finds nothing); the owner names it as the
source. AGENTS.md asks to "Preserve license notices and human attribution for substantially
derived material". Proposed change: add to `docs/architecture.md`, before the verification-coverage
diagram: "The obligation labels CC-S, CC-C, WC follow Kolozyan, Sorger, Hicks, Chaliasos, *ZKP
Security Tools and Verification*, arXiv:2607.23752 (2026), §VI-A; leanerVM adds BC, T3, T6."

**Negative result.** ArkLib's round-by-round definitions, the `KnowledgeStateFunction` docstring,
the basic Fiat–Shamir query and the admitted MCA theorem are textually unchanged between
`dca90385` and `7653a901` (checked with `git show <rev>:<path>`; line numbers shift by at most 8).

## F. Comparable verification efforts, and where they cut between arithmetization and proof system

Method. A helper of this task (stopped by the owner before it finished) read the SP1, OpenVM and
Pico sources and left notes in `probes/literature/F-notes.md`. I re-checked the load-bearing
quotations myself with `gh api` (GET only) and `curl` (marked "re-checked"); the rest of those
notes is marked "helper's notes". Everything after Pico is my own reading.

### F.1 The efforts

**SP1 (Succinct), `succinctlabs/sp1-lean` ("SP1Clean").** Branch `dtumad/v1.0-release`, head
`eb6f44b9` (2026-08-12); `main` head of 2026-06-26 per the helper. Predecessor: Nethermind +
Succinct, *Formal Verification of SP1 Hypercube*, 2025-10-09, https://blog.succinct.xyz/nethermind-lean/
(helper's notes), whose stated assumptions included "the SP1 lookup bus ... [is] correct; and the
proof system underpinning SP1 is correct" and "permutation constraints: interpreted as trivially
true" (helper's notes, from the Nethermind blog of 2025-05-21).
- Verified: 25 instruction chips as Clean circuits proved equal to the constraints extracted from
  the Rust, against the Lean Sail RV64 model; a machine-level theorem `supported_core_native_sound`
  (helper's notes).
- Hand-off (re-checked): a relation on traces. The exact extracted-AIR relation requires, per row,
  that every extracted `assertZero` polynomial vanishes, plus `Balance.Valid`, whose docstring
  reads (`SP1Clean/Faithful/CoreAIR.lean:240-250` on `dtumad/v1.0-release`): "Exact local
  interaction relation supplied by the LogUp/GKR knowledge extractor. This is deliberately an
  equality of canonical natural multiplicities, not merely a field-valued sum. A modular equality
  can wrap at the field characteristic and is not by itself enough to recover an execution
  multiset. ArkLib's interaction-argument theorem must extract this stronger fact (with its own
  error term and trace/multiplicity bounds)." The proof-system boundary
  (`SP1Clean/FormalModel/Verifier.lean:3-7`, re-checked): "AIR soundness and verifier knowledge
  soundness are different theorems ... ArkLib owns the second notion"; at `:64` "At the audited
  ArkLib revision, `knowledgeSoundness` uses `WitIn` both as the extractor's result and" the
  prover's input, so the plan widens the relation with `knowledgeSoundness_relIn_mono` (`:74-85`).
- Proof system: not verified ("This repository does not claim that verifier acceptance
  deterministically implies an execution without cryptographic assumptions and an error bound",
  README per the helper).
- Problems met: Cody Gunton (EF), *On Formal Verification and a Bug in SP1 Hypercube*,
  2026-05-20, https://zkevm.ethereum.foundation/blog/sp1-fv (helper's notes; also cited as [76]
  by [KSHC26]): a real JALR bug missed because a proof carried a hypothesis `h_valid_pc` that "can
  be proved from constraints on newest sp1 branch" and could not; a vacuous SLTI proof; wrong
  specifications for two loads. The independent audit of 2026-08-12 (helper's notes) asks to name
  separately "raw proof acceptance, algebraic/commitment openings, and the extracted
  exact-natural witness relation", and flags that the witness shape did not bind the proof
  system's domain sizes ("otherwise padding/domain mismatches can fall between executable
  verifier agreement and AIR refinement").

**OpenVM, `openvm-org/openvm-fv`** (Nethermind; last commit 2026-07-15 per the helper). Nethermind,
*Formal Verification of the OpenVM RISC-V zkVM — Technical Report*, dated 2026-02-01, `REPORT.pdf`
in the repository (re-checked, downloaded 2026-09-30).
- Verified: all RV32IM opcodes against a Lean Sail model, execution and memory consistency of the
  RV32IM chips; soundness only.
- Assumed (re-checked, report lines 133-134): "I1: correctness of the theory and implementation of
  the OpenVM lookup argument and bus interaction mechanism; I2: correctness of the theory and
  implementation of the proof system utilised by OpenVM".
- Hand-off (re-checked): per-row theorems over a trace; the LogUp side is cut out: "As the
  permutation trace (that is, the trace in the extension field) is only used in these circuits for
  the constraints generated to enforce interactions, the extractor takes all generated constraint
  expressions and converts any that reference the permutation trace into comments" (report
  §3.1.5, line 843-845). Bus balance is a field sum per payload, made faithful by the hypothesis
  `h_len_bus : (...).length < BB_prime` (line 247) and the paper fact "(E4) the verifier enforces
  that there are less than BB_prime overall interactions" (line 312).

**Pico (Brevis), `NethermindEth/pico-fv`** (created 2026-02-11, pushed 2026-06-11; re-checked).
Nethermind report dated 2026-06-10 (helper's notes). Verified: every RV32IM and RV64IM opcode's
chip against Sail; "For each opcode, the equivalence theorem states: under the chip's row
constraints, bus assumptions, and program well-formedness, executing one Sail step of the
corresponding instruction produces the same post-state as applying the chip's emitted CPU-bus
operations" (README, re-checked). Assumptions I1-I4 as for OpenVM. Problems: "The 13 RV64IM
soundness bugs found during the formalisation" (README line 91, re-checked), almost all
under-constrained columns, several of them columns that are only sent on a bus (helper's notes).

**ZisK (Polygon), `eth-act/zisk-fv`** (created 2026-04-20, pushed 2026-09-23; read by me). README:
"While the work has identified bugs in ZisK v0.17.0, the formal proofs should not be taken as
providing any assurances about security of ZisK's RV64IM implementation." Claim
(`trust/trusted-base.md`): "every state transition accepted by the modeled ZisK RV64IM circuits is
a valid RISC-V state transition", with the Sail and circuit extractions trusted; "Exact channel
balance, static lookup membership, fixed/public trace schemas, and full source-to-model trace
construction remain distinct proof obligations". Uses Aeneas to extract the Rust lowering.
Hand-off: an accepted trace (constraints hold, channels balanced), no proof system.

**Verified-zkEVM `riscv-zkvm`** (created 2026-08-25; read by me): a Lean extraction of the Sail
RISC-V specification, a computable RV64IM model and 51 per-instruction equivalence theorems, serving
`evm-asm`. An ISA-specification layer; no arithmetization or proof system.

**StarkWare.** [AGGLNST26] J. Avigad, A. Ganor, L. Goldberg, D. Levit, O. Nir, Y. Seginer, A.
Titelman, *Formal verification of the S-two AIR*, arXiv:2606.04311 (2026-06-03). Opened (§2-5).
Lean 4; soundness of the AIR encoding of Cairo for the S-two (circle STARK) prover; the proof
system itself is not verified. Hand-off (§2.3): "the conclusion of the soundness theorem only
assumes that, • each component's polynomial constraints hold of the associated table, • the logup
polynomials are satisfied with respect to the relevant uses and yields, and • the chosen 'random'
value lies outside the small bad set." They verified the LogUp lemma (§5.1, "Note that the equality
stated in the lemma is between field elements, not integers. To interpret these sums as counts, we
have to be careful and make sure the sum does not exceed the characteristic of the field"), and did
not model "the general mechanisms that collect all the lookups ... The assumption that these aspects
of the code are correct is reflected in the hypotheses of our soundness theorem" (§2.4). Earlier: J.
Avigad, L. Goldberg, D. Levit, Y. Seginer, A. Titelman, *A verified algebraic representation of
Cairo program execution*, arXiv:2109.14534 (v1 2021-09-29; authors and title from the arXiv
listing; the CPP 2022 venue is from the literature and **unverified**; not opened). The S-two paper
[AGGLNST26] is its successor for the current prover.

**The EF zkEVM formal verification project.** https://verified-zkevm.org (read 2026-09-30: "zkEVM
Formal Verification Project", mission to accelerate "the application of formal verification
methods to zkEVMs"; grant applications open; no track details rendered). G. Kadianakis, *Shipping
an L1 zkEVM #2: The Security Foundations*, Ethereum Foundation blog, 2025-12-18,
https://blog.ethereum.org/2025/12/18/zkevm-security-foundations (read via a fetch summary):
milestones "100-bit provable security (as estimated by soundcalc)" by end of May 2026 and
"128-bit provable security (as estimated by soundcalc)" with "Formal security argument for
recursion soundness" by end of 2026; "many STARK-based zkEVMs today rely on unproven mathematical
conjectures". soundcalc (`ethereum/soundcalc`, pushed 2026-09-21; README read): "soundcalc
estimates the security level of the *interactive oracle proof (IOP)* ... for the notion of
round-by-round soundness ... security levels are shown for each round, and the total security level
is the minimum of all these levels"; it refers to [GMW25] for why the minimum corresponds
"(roughly)" to the non-interactive level and to [CDHZ26] for the quantum case.

**RISC Zero.** Veridise, *RISC Zero's zkVM security: how Veridise enabled provable & continuous ZK
security*, 2025-03-27 (read via a fetch summary): determinism (absence of under-constrained
signals) of the Keccak accelerator and "a significant portion" of the R0VM 2.0 RISC-V circuit, with
Picus; circuits only. **Jolt.** C. Kwan, Q. Dao, J. Thaler, *Verifying Jolt zkVM lookup semantics*,
FC 2025 (ACL2; reference from [KSHC26] [24], not opened). **ZKsync.** Nethermind, *We verified the
verifier: a first for zero-knowledge proof systems*, 2025-09-02 (read via a fetch summary): the
on-chain Yul verifier proved "honest" against an abstract verifier model in EasyCrypt;
"This effort did not verify soundness of the proof system itself". **Isabelle/STARK.** D. Marmsoler,
*Isabelle/STARK: A Formalization of zk-STARK in Isabelle/HOL*, arXiv:2608.01965 (v. 2026-09-22),
abstract read: "mechanized query-bounded soundness for a STARK-style protocol", a concrete bound
`2^{-137}` for a toy statement in "a classical, field-valued random-oracle model", explicitly
"not an unrestricted 137-bit work-factor guarantee" and not covering "knowledge extraction,
quantum-query security or correctness of a deployed bit-hash implementation". The only mechanized
end-to-end hash-based proof-system soundness result I found; a fixed toy statement.

**Clean** (E.4): `Ensemble.Statement` = ∃ witness with constraints and field-balanced channels.

### F.2 Synthesis: is the blueprint's cut sound practice?

What the others hand across: **a relation on a trace** (rows of field elements per table, per-row
polynomial constraints, and a bus/lookup condition), never a relation on a committed polynomial.
They differ in how the bus condition is stated: assumed (OpenVM I1, Pico I1, SP1 generation 1),
a field sum made faithful by a length guard below the characteristic (OpenVM `h_len_bus`, S-two's
LogUp lemma, Clean's `BalancedInteractions`), or an exact equality of natural counts that the
proof system's extractor must deliver (SP1 generation 2, `Balance.Valid`). None of them has a
verified proof system on the other side of the cut; the one plan that exists (SP1) wants an ArkLib
knowledge extractor into its trace relation, with an error term, trace and multiplicity bounds.

The blueprint makes the same cut and adds the missing half. leanISA's `SatisfiedBy` is the trace
relation (like SP1's exact-AIR relation, with combinatorial balance `BalancedPair` in ℕ); the
proof system extracts `M3Holds I input q`, a relation on the one committed column; the adaptor
(`witnessOf`, `satisfiedBy_witnessOf`, `m3Holds_stackOf`) maps between them. This is sound
practice, and it is what the SP1 audit asked for (three relations named separately: acceptance,
openings, extracted witness relation). It is also forced by the field: in characteristic 2 no
length guard makes a field sum of multiplicities count, so balance must be combinatorial on both
sides (D.2), which the blueprint does.

Problems others met at this cut, and what to check in leanerVM (the checks belong to the other
dossiers; I list them as literature-derived test cases):
1. **Field sum versus multiset** (SP1 `BalanceMod`, OpenVM `h_len_bus`, S-two §5.1): check that
   `M3Holds`'s balance clause and leanISA's `BalancedPair` are the same combinatorial statement,
   and that the grand-product error covers the multiset, not a sum.
2. **Extractor typing** (SP1 `Verifier.lean:64`, ArkLib `knowledgeSoundness` uses `WitIn` as both
   the prover's input and the extractor's output): the blueprint's adaptor composes the extractor
   with `witnessOf` through `Refinement.map_option_valid` (blueprint line 1253); the same obstacle,
   a different workaround; check it at `7653a901`.
3. **Sizes and padding not bound** (SP1 audit, "padding/domain mismatches can fall between
   executable verifier agreement and AIR refinement"): the blueprint puts announced sizes in the
   statement and `Admissible` in `verify_iff_compiled` (lines 1218-1221); check that `M3Holds`
   ties every table's rows to the announced heights.
4. **Empty or inactive tables making constraints vacuous** (SP1 `WellShaped`: "permitting an empty
   active trace here would make all of its row constraints and interactions vacuous", helper's
   notes): check how `M3Holds` treats a table of height 0 or a table whose selector is 0.
5. **Columns only sent on a bus** (Pico MRW-1, SR-3): a column constrained only by its bus tuple is
   constrained only as far as the bus relation is extracted exactly; another reason the
   combinatorial balance must be extracted and not assumed.
6. **False or vacuous hypotheses in the per-row proofs** (SP1 JALR `h_valid_pc`, SLTI): the review's
   non-vacuity criterion; the blueprint's master theorems are conditional on `Phases.Security`,
   whose inhabitation is the analogous risk.
7. **Preprocessed data smuggling soundness** (SP1's `PreprocessedBinding` "exposes only those
   matrices—not main rows or semantic claims—so a PCS/ArkLib adapter cannot smuggle execution
   soundness through the commitment premise", helper's notes): the leanVM analogue is the bytecode
   multilinear and the Flock matrices, which the verifier evaluates itself (blueprint line
   1235-1236, `settleFixedClaims`); the same discipline applies.

### F.3 Findings of this section

**Negative result (the cut).** No effort I found cuts the arithmetization from the proof system at
a polynomial relation on a committed oracle, because none has built the proof-system half; the
blueprint's two-relation design with an adaptor is consistent with the only published plan (SP1)
and with the obligations of [KSHC26]. I found no literature reason to change the cut.

**Finding: the verification literature for zkVMs is almost entirely constraint-level; claims about
the proof system in the report must be phrased relative to that baseline.** Severity: note.
Evidence: F.1 (every effort except Isabelle/STARK stops at the trace relation or assumes the bus and
the proof system); [KSHC26] §VI-C "No zkVM has end-to-end formal verification". Proposed use: the
report can state that leanerVM's master theorems, once proved, would be the first mechanized
round-by-round knowledge-soundness proof of a deployed zkVM's oracle protocol, and must say at the
same time that the compilation (WHIR, Merkle, Fiat–Shamir) remains assumed.

## G. Other things a reviewer should know in September 2026

### G.1 Soundness regimes and the 128-bit target

- **Provable versus conjectured.** The EF's L1 zkEVM milestones ask for "128-bit provable
  security (as estimated by soundcalc)" by the end of 2026 (G. Kadianakis, EF blog, 2025-12-18;
  B-sources above); "provable" means no proximity-gap or list-decoding conjecture. The capacity
  conjectures have been refuted ([CS25], [KKH26], [Kam26]; C.1), and at exactly the Johnson radius
  the linear bound fails in characteristic 2 ([BCHKS25] Corollary 1.7). leanVM's WHIR sits in the
  Johnson regime with slack and cites a theorem, so it is in the "provable" class, modulo the
  preprint status of [BCHKS25] Theorem 4.6 (C.4).
- **What "128 bits" means.** soundcalc's figure is the minimum over rounds of the round-by-round
  errors of the IOP (README of `ethereum/soundcalc`, pushed 2026-09-21: "the total security level
  is the minimum of all these levels"), which matches leanVM's `SECURITY_BITS` ("every
  verifier-challenge transition", `whir_config.rs:36-38`). The non-interactive level in the ROM
  is that figure minus `log(t + k)` for a `t`-query adversary, minus the hash term ([CY24] Thm
  31.3.1, §28.3.2), i.e. "128 bits of work factor" in the `t/ε` sense, slightly less by the
  constants (A.3). soundcalc cites [GMW25] (A. Garreta, N. Mohnblatt, B. Wagner, *A Simplified
  Round-by-round Soundness Proof of FRI*, ePrint 2025/1993, TCC 2026; abstract read) for this
  correspondence; its changelog records that version 2 "fixes a mistake in the state function for
  the folding rounds", a reminder that paper round-by-round proofs of folding protocols have
  needed corrections.
- **Quantum adversaries.** The leanVM specification motivates the design by post-quantum security
  (`01-introduction.tex:4`: elliptic curves "do not survive a quantum computer"). In the quantum
  random-oracle model the loss is quadratic: [CMS19] Theorem 8.6 gives `O(t²ε + t³/2^λ)`;
  [BGKTTZ23] Theorem 3.15 `Θ(Q·ε_fs)`; A. Chiesa, Z. Di, Z. Hu, Y. Zheng, *How to Prove
  Post-Quantum Security for Succinct Non-Interactive Reductions*, ePrint 2025/2166 (EUROCRYPT 2026;
  abstract read) extends this to reductions and shows that "(classical) round-by-round security
  implies post-quantum state-restoration security". A 128-bit round-by-round target therefore
  gives about 64 bits against a quantum adversary by these bounds. Neither the blueprint nor
  `docs/architecture.md` at `b435631` mentions the quantum model (`git show b435631:…| grep -i
  quantum` finds nothing), so the report must not present the Lean theorem as post-quantum
  security.
- **Grinding** is where the target is met on the query rounds (17 bits per level; A.3 item 3). A
  stale comment in the pinned Rust says the opposite for level 0: `crates/pcs/src/whir.rs:1210`
  "Query-phase PoW grinding for L0 (0 bits in the production profile; ...)", while the production
  derivation and its tests set every level to `QUERY_GRINDING_BITS`
  (`whir_config.rs:915, 1017`; `whir.rs:2231` `assert!(pc.grinding_bits.iter().all(|&b| b ==
  QUERY_GRINDING_BITS))`). The blueprint's `queryGrindingBits : ℕ := 17` (line 1163) follows the
  code; the discrepancy is inside leanVM (for the ground-truth dossiers).

### G.2 The list-decoding regime and knowledge extraction

In the Johnson regime a committed word can be close to up to `L` codewords, so a commitment is
list binding, and an extractor must produce *one* list member that satisfies *all* claims
(Annex B Definition `def:listbinding`, `b-polynomial-commitment-scheme.tex:70-72`). The blueprint
handles this correctly in spirit (acceptance test 11, "Joint list binding", lines 1296-1299;
Layer 12 "extracts the member"). Two literature facts sharpen it: (i) MCA is exactly the property
that makes folding preserve lists ([ABF26] §1: CA alone "does not let us prove properties of the
messages encoded by these close-by codewords. For that we need MCA"; Annex B Lemma
`lem:fold-list`); (ii) without an out-of-domain sample at commitment, the outer protocol pays the
list size ([BRW26] Remark 11; A.4). The extractor is information-theoretic in Lean (Lean has no
cost model), which suffices for T4's existential conclusion (A.4 "Computable is not efficient").

### G.3 Known bugs in deployed verifiers, and which theorem would catch them

Sources: GitHub security advisories read with `gh api repos/<repo>/security-advisories` on
2026-09-30 (summary, date, text; "re-checked"), and the stopped helper's notes
(`probes/literature/G-notes.md`, "helper's notes", sources opened by the helper). The theorem
shapes: **(a)** round-by-round knowledge soundness of the oracle protocol in Lean (the master
theorems); **(b)** `verify_iff_compiled`, the refinement of the Lean `verify` to the compiled
oracle verifier; **(c)** the assumed interfaces `FiatShamirSecurity`, `BcsSecurity`,
`McaJohnson`; **(d)** differential tests of the Lean `verify` against Rust-produced proofs, with
mutations; **(e)** nothing formal links the Lean `verify` to the deployed Rust and Python
verifiers.

| Class | Instances (date; source) | (a) | (b) | (c) | (d) |
| --- | --- | --- | --- | --- | --- |
| Fiat–Shamir omission: a value is not absorbed before the challenge that binds it | Frozen Heart in PlonK/Bulletproofs/Girault (Trail of Bits, 2022-04-13); Plonky3 GHSA-vrmm-4mm5-38vm "Purported opened values not included in transcript" (2025-01-27) and SP1 GHSA-c873-wfhp-wx5m (2025-01-15); SP1 GHSA-8m24-3cfx-9fjw "Insufficient observation of cumulative sum" (2024-11-08); Stwo-Cairo public-memory IDs (zkSecurity, 2025-08-06); zkLighter GKR inputs/outputs (zkSecurity, 2024-01-22); Linea/gnark last challenge GHSA-7p92-x423-vwj6 (2023-10-16); Solana ZK ElGamal (2025-04, 2025-06) (helper's notes; the Plonky3 and SP1 advisories re-checked) | no: the oracle protocol has no transcript | yes for the **Lean** verifier, if the compiled model is a strong transform (statement and every message before each challenge), as ArkLib's basic transform is (`FiatShamir/Basic.lean:91`) | a weak transform would make (c) an assumption of a false statement ([DMWG23]); state (c) for the strong, adaptive transform | detects Lean/Rust divergence; an omission shared by both is invisible to honest-proof tests and to ordinary mutations |
| Non-injective transcript encoding | Plonky3 GHSA-vj64-rjf3-w3v7 "MultiField32Challenger: transcript malleability and challenge entropy loss" (2026-05-15; re-checked); Plonky3 GHSA-3g92-f9ch-qjcm sponge padding (2026-04-16; re-checked) | no | only if the chain's encoding is part of the compiled model (it is Category B in the blueprint) | the chain lemma of E.6 must assume injectivity; leanVM's fixed-width, tagged blocks and binary-field squeezes (`lib.rs:30-110`) avoid both instances by construction | transcript conformance vectors (absorbed blocks and squeezed values, step by step) would catch drift |
| Missing check in the commitment's verifier (FRI/WHIR final degree, sizes) | Plonky3 GHSA-f69f-5fx9-w9r9 "Missing final polynomial degree check in FRI verifier" (2025-06-03; also unrandomized roll-in; re-checked), propagated as SP1 GHSA-6248-228x-mmvh; Plonky3 GHSA-m23j-cj9m-ppg9 "Missing size checks in FRI verifier" (2025-03-28; "a proof with an invalid shape could cause it to skip checks"; re-checked) | yes if WHIR is modelled (Layer 11): a Lean `whirOpen` without the final check cannot prove `whirOpen_rbrSoundness` | yes for the Lean verifier | `McaJohnson` is not involved | a mutation per check (final plaintext level, query count, path length) is needed; honest proofs never exercise a missing check |
| Statement and public-value binding | SP1 GHSA-6248-228x-mmvh: the Rust verifier did not check `vk_root` (2025-06-03; re-checked); OpenVM GHSA-w82q-w67c-67wv non-canonical app commitments accepted (2026-06-26; re-checked); leanVM itself: the Rust and Python verifiers check one combined equation on the two public words where the specification checks per limb (brief §7) | yes for the check as the oracle protocol states it (the public-input phase proves the per-limb check) | yes for the Lean verifier | n/a | the only evidence about the deployed verifiers; a *reverse* mutation (a proof the Rust accepts and the specification rejects) exposes a weaker deployed check, as the per-limb case shows |
| Shape binding between two views of the same sizes | SP1 GHSA-63x8-x938-vx33 "V6 Recursion Circuit Row-Count Binding Gap" (2026-04-11; re-checked): row counts hashed into the commitment and prefix sums used for evaluation were separate witnesses; OpenVM GHSA-j9m2-fxc5-fr82 recursion permutation check (2026-05-15; re-checked) | partly: sizes are parameters of the protocol family (acceptance test 21) | yes: `verify_iff_compiled` quantifies `∃ s, s.Admissible prog` over one `s` used for layout and checks | n/a | mutations of the announced sizes |
| Under-constrained arithmetization, including bus-invariant columns | RISC Zero GHSA-g3qg-6746-3mg9 (2025-06-18; re-checked); OpenVM GHSA-fh29-29h9-qm9h `is_valid` not boolean "breaks the invariants needed for LogUp soundness" (2026-05-15; re-checked); OpenVM GHSA-396x-v8w4-9x82 Merkle rows below the leaf (2026-06-26; re-checked); Pico's 13 gaps; SP1 JALR (F.1) | no | no | no | no: this is T1 (CC-S), not the proof system; the proof system's job is to extract exactly the relation T1 consumes (count nonzero, `R_c ≠ 0`, acceptance test 3) |
| Grinding not checked or checked with the wrong bits | no advisory found in the advisory lists of Plonky3, SP1, RISC Zero, OpenVM, Jolt and Stwo read on 2026-09-30 (the last two returned none) | no: grinding is outside the oracle protocol | only if the compiled model contains proof of work | only if (c) models proof of work (A.4); otherwise a Lean `verify` that skips the check still satisfies every planned theorem, with a weaker certified bound | a wrong-nonce mutation; not among the six mutations the blueprint lists (lines 1238-1239) |
| Diagonalization (KRS) | [KRS25] on GKR with uncommitted wires (Expander mitigated); [Fen26] on generated R1CS | no | no | outside the ROM by construction | no; structural argument only (B.2) |
| Recursion verifier diverging from the native one | SP1 V6 row count; SP1 `vk_root`; OpenVM native recursion (all re-checked) | — | — | — | T5, out of the blueprint's scope |

### G.4 Synthesis: keeping the Lean verifier from drifting away from the deployed one

1. **Make every verifier check load-bearing in some theorem, and test the ones that are not.**
   The owner's requirement (a missing or weak check must leave knowledge soundness or completeness
   unprovable) holds for checks inside the oracle protocol; it fails for checks outside it: the
   proof-of-work predicate, canonical-encoding checks on the stream (for example `scalars_to_hash`
   rejecting a nonzero third limb, `crates/fiat_shamir/src/merkle.rs:22-37`), Merkle path lengths.
   For these, (b) and (c) must include them, or (d) must carry one mutation per check.
2. **One mutation per verifier check, in both directions.** Forward: each mutation must be
   rejected by the Lean `verify` (and should be by Rust and Python). Reverse: construct transcripts
   that the specification rejects and run the Rust and Python verifiers on them; any acceptance is
   a deployed check weaker than the specification (the per-limb public-input case is such an
   instance). The blueprint's six mutations (lines 1238-1239) do not cover the grinding nonce, the
   final plaintext level, the query count, the announced sizes, or canonical encodings.
3. **Transcript conformance vectors.** Record, for a dumped proof, the sequence of absorbed blocks
   and squeezed challenges; compare Lean and Rust step by step. This catches encoding drift of the
   Plonky3 MultiField32 kind, which an end-to-end accept/reject test can miss.
4. **Three implementations.** leanVM ships a Python verifier; differential testing Lean ↔ Rust ↔
   Python triangulates which one drifted.
5. **Pin and re-run.** [KSHC26] §VI-C: "Guarantees not checked on every commit silently decay";
   the fixture tests must name the leanVM revision they were dumped from and be regenerated on pin
   bumps.

### G.5 Findings of this section

**Finding: the proof of work is the one verifier check no planned theorem makes load-bearing.**
Severity: major. Classification: an error of the blueprint (the planned interfaces and tests leave
a check that leanVM's 128-bit claim depends on outside every theorem and every mutation). Evidence:
G.3 row "Grinding"; A.4 first finding; blueprint lines 1224 and 1238-1240. Proposed change: (i) the
A.4 change to `FiatShamirSecurity`; (ii) in Layer 12's tests, replace "each of six mutations (a
flipped stream scalar in each phase, a wrong Merkle sibling) rejected" by "each of the following
mutations rejected: a flipped stream scalar in each phase, a wrong Merkle sibling, a wrong grinding
nonce at each ground level, a truncated Merkle path, a nonzero third limb in a digest half, an
announced size above its cap; and, in the reverse direction, each transcript the specification
rejects is also run through the Rust and Python verifiers".

**Finding: the Lean theorem is classical.** Severity: minor. Classification: an omission of the
blueprint. Evidence: G.1 "Quantum adversaries". Proposed change: add to the blueprint's scope
section (after line 157): "Security against quantum adversaries (the quantum random-oracle model,
[CMS19], ePrint 2025/2166) is out of scope; the classical bound does not transfer (the loss is
quadratic in the query count)."

## BibTeX

Entries marked `note = {... unverified ...}` were not opened (bibliographic data from a listing,
a citing paper or a search result). Keys follow this dossier.

```bibtex
@misc{CCHLRR18,
  author       = {Ran Canetti and Yilei Chen and Justin Holmgren and Alex Lombardi and Guy N. Rothblum and Ron D. Rothblum},
  title        = {Fiat-Shamir From Simpler Assumptions},
  howpublished = {Cryptology {ePrint} Archive, Paper 2018/1004},
  year         = {2018},
  url          = {https://eprint.iacr.org/2018/1004},
  note         = {Definition 5.3, Proposition 5.4, Theorem 5.8}
}
@inproceedings{CCHLRRW19,
  author    = {Ran Canetti and Yilei Chen and Justin Holmgren and Alex Lombardi and Guy N. Rothblum and Ron D. Rothblum and Daniel Wichs},
  title     = {Fiat-Shamir: From Practice to Theory},
  booktitle = {Proceedings of the 51st Annual {ACM} {SIGACT} Symposium on Theory of Computing ({STOC} 2019)},
  pages     = {1082--1090},
  year      = {2019},
  doi       = {10.1145/3313276.3316380},
  note      = {Publisher PDF not opened (HTTP 403); content read in ePrint 2018/1004}
}
@misc{Hol19,
  author       = {Justin Holmgren},
  title        = {On Round-By-Round Soundness and State Restoration Attacks},
  howpublished = {Cryptology {ePrint} Archive, Paper 2019/1261},
  year         = {2019},
  url          = {https://eprint.iacr.org/2019/1261}
}
@inproceedings{BCS16,
  author    = {Eli Ben-Sasson and Alessandro Chiesa and Nicholas Spooner},
  title     = {Interactive Oracle Proofs},
  booktitle = {Theory of Cryptography ({TCC} 2016-B)},
  year      = {2016},
  note      = {Full version: Cryptology ePrint Archive, Paper 2016/116; Theorems 1.2 and 1.5},
  url       = {https://eprint.iacr.org/2016/116}
}
@inproceedings{CMS19,
  author    = {Alessandro Chiesa and Peter Manohar and Nicholas Spooner},
  title     = {Succinct Arguments in the Quantum Random Oracle Model},
  booktitle = {Theory of Cryptography ({TCC} 2019)},
  year      = {2019},
  note      = {Full version: Cryptology ePrint Archive, Paper 2019/834; Definitions 8.3--8.5, Theorem 8.6},
  url       = {https://eprint.iacr.org/2019/834}
}
@book{CY24,
  author    = {Alessandro Chiesa and Eylon Yogev},
  title     = {Building Cryptographic Proofs from Hash Functions},
  year      = {2024},
  url       = {https://snargsbook.org},
  note      = {Version compiled 2026-03-25; Definitions 31.1.2, 31.1.6; Theorems 25.2.1, 26.1.1, 31.2.1, 31.3.1; Section 28.3.2}
}
@inproceedings{BGKTTZ23,
  author    = {Alexander R. Block and Albert Garreta and Jonathan Katz and Justin Thaler and Pratyush Ranjan Tiwari and Micha{\l} Zaj{\k{a}}c},
  title     = {{Fiat-Shamir} Security of {FRI} and Related {SNARKs}},
  booktitle = {Advances in Cryptology -- {ASIACRYPT} 2023},
  year      = {2023},
  note      = {Full version: Cryptology ePrint Archive, Paper 2023/1071 (revised 2024-03-05); Definition 3.13, Theorem 3.15},
  url       = {https://eprint.iacr.org/2023/1071}
}
@inproceedings{CO25,
  author    = {Alessandro Chiesa and Michele Orr{\`u}},
  title     = {A {Fiat--Shamir} Transformation From Duplex Sponges},
  booktitle = {Theory of Cryptography ({TCC} 2025)},
  series    = {LNCS},
  volume    = {16268},
  pages     = {452--474},
  year      = {2025},
  note      = {Full version: Cryptology ePrint Archive, Paper 2025/536 (PDF of 2026-03-27); Theorems 6.1, 6.2; LNCS data from arXiv:2607.23752, reference 73},
  url       = {https://eprint.iacr.org/2025/536}
}
@misc{ABF26,
  author       = {Gal Arnon and Dan Boneh and Giacomo Fenzi},
  title        = {Open Problems in List Decoding and Correlated Agreement},
  howpublished = {Cryptology {ePrint} Archive, Paper 2026/680},
  year         = {2026},
  url          = {https://eprint.iacr.org/2026/680},
  note         = {Version of 2026-07-06; Definitions A.3--A.5, Theorem 4.12, Table 1}
}
@misc{BCFW25,
  author       = {Benedikt B{\"u}nz and Alessandro Chiesa and Giacomo Fenzi and William Wang},
  title        = {Linear-Time Accumulation Schemes},
  howpublished = {Cryptology {ePrint} Archive, Paper 2025/753},
  year         = {2025},
  url          = {https://eprint.iacr.org/2025/753},
  note         = {TCC 2025; not opened (unverified content)}
}
@misc{Riv26,
  author       = {Matthieu Rivain},
  title        = {{AES}-Based Grinding for {MPC}-in-the-Head Signatures},
  howpublished = {Cryptology {ePrint} Archive, Paper 2026/1625},
  year         = {2026},
  url          = {https://eprint.iacr.org/2026/1625},
  note         = {Abstract read only}
}
@inproceedings{KRS25,
  author    = {Dmitry Khovratovich and Ron D. Rothblum and Lev Soukhanov},
  title     = {How to Prove False Statements: Practical Attacks on {Fiat-Shamir}},
  booktitle = {Advances in Cryptology -- {CRYPTO} 2025},
  year      = {2025},
  note      = {Full version: Cryptology ePrint Archive, Paper 2025/118 (revised 2025-12-11); Theorems 1, 2, Remark 3, Section 5; venue as cited by ePrint 2026/1838},
  url       = {https://eprint.iacr.org/2025/118}
}
@misc{Fen26,
  author       = {Giacomo Fenzi},
  title        = {How to prove more false statements: {Fiat--Shamir} limitations on (generated) {R1CS}},
  howpublished = {Cryptology {ePrint} Archive, Paper 2026/1838},
  year         = {2026},
  url          = {https://eprint.iacr.org/2026/1838},
  note         = {Version of 2026-09-09; Definition 2, Theorem 2}
}
@misc{AY25,
  author       = {Gal Arnon and Eylon Yogev},
  title        = {Towards a White-Box Secure {Fiat-Shamir} Transformation},
  howpublished = {Cryptology {ePrint} Archive, Paper 2025/329},
  year         = {2025},
  url          = {https://eprint.iacr.org/2025/329},
  note         = {CRYPTO 2025 (major revision); abstract read only}
}
@inproceedings{DMWG23,
  author    = {Quang Dao and Jim Miller and Opal Wright and Paul Grubbs},
  title     = {Weak {Fiat-Shamir} Attacks on Modern Proof Systems},
  booktitle = {IEEE Symposium on Security and Privacy (S\&P) 2023},
  year      = {2023},
  note      = {Cryptology ePrint Archive, Paper 2023/691; read by a helper of this task, not re-read},
  url       = {https://eprint.iacr.org/2023/691}
}
@inproceedings{ACFY25,
  author    = {Gal Arnon and Alessandro Chiesa and Giacomo Fenzi and Eylon Yogev},
  title     = {{WHIR}: {Reed--Solomon} Proximity Testing with Super-Fast Verification},
  booktitle = {Advances in Cryptology -- {EUROCRYPT} 2025},
  year      = {2025},
  note      = {Full version: Cryptology ePrint Archive, Paper 2024/1586 (revised 2024-11-21); Definitions 4.5, 4.9, Conjecture 4.12, Theorem 5.2},
  url       = {https://eprint.iacr.org/2024/1586}
}
@misc{BCHKS25,
  author       = {Eli Ben-Sasson and Dan Carmon and Ulrich Hab{\"o}ck and Swastik Kopparty and Shubhangi Saraf},
  title        = {On Proximity Gaps for {Reed--Solomon} Codes},
  howpublished = {Cryptology {ePrint} Archive, Paper 2025/2055},
  year         = {2025},
  url          = {https://eprint.iacr.org/2025/2055},
  note         = {Single version, 2025-11-06; Theorems 1.3, 1.5, 1.6, 4.6, Corollaries 1.4, 1.7}
}
@misc{Hab25,
  author       = {Ulrich Hab{\"o}ck},
  title        = {A note on mutual correlated agreement for {Reed--Solomon} codes},
  howpublished = {Cryptology {ePrint} Archive, Paper 2025/2110},
  year         = {2025},
  url          = {https://eprint.iacr.org/2025/2110},
  note         = {Version of 2025-11-17; Theorem 2}
}
@misc{CS25,
  author       = {Elizabeth Crites and Alistair Stewart},
  title        = {On {Reed--Solomon} Proximity Gaps Conjectures},
  howpublished = {Cryptology {ePrint} Archive, Paper 2025/2046},
  year         = {2025},
  url          = {https://eprint.iacr.org/2025/2046},
  note         = {Abstract read only}
}
@misc{KKH26,
  author       = {Dmitry Krachun and Stepan Kazanin and Ulrich Hab{\"o}ck},
  title        = {Failure of proximity gaps close to capacity},
  howpublished = {Cryptology {ePrint} Archive, Paper 2026/782},
  year         = {2026},
  url          = {https://eprint.iacr.org/2026/782},
  note         = {Abstract read only}
}
@misc{Kam26,
  author       = {Antonio Kambir{\'e}},
  title        = {Proximity Gaps Conjecture Fails Near Capacity over Prime Fields},
  howpublished = {arXiv:2604.09724},
  year         = {2026},
  url          = {https://arxiv.org/abs/2604.09724},
  note         = {Reference data from ePrint 2026/680 only; unverified}
}
@misc{GG25,
  author       = {Rohan Goyal and Venkatesan Guruswami},
  title        = {Optimal Proximity Gaps for Subspace-Design Codes and (Random) {Reed-Solomon} Codes},
  howpublished = {Cryptology {ePrint} Archive, Paper 2025/2054},
  year         = {2025},
  url          = {https://eprint.iacr.org/2025/2054},
  note         = {Abstract read only}
}
@misc{BCGM25,
  author       = {Sarah Bordage and Alessandro Chiesa and Ziyi Guan and Ignacio Manzur},
  title        = {All Polynomial Generators Preserve Distance with Mutual Correlated Agreement},
  howpublished = {Cryptology {ePrint} Archive, Paper 2025/2051},
  year         = {2025},
  url          = {https://eprint.iacr.org/2025/2051},
  note         = {CCC 2026; abstract read only}
}
@misc{Jo26,
  author       = {Sunghyeon Jo},
  title        = {{Reed--Solomon} Mutual Correlated Agreement Beyond the {Johnson} Radius},
  howpublished = {Cryptology {ePrint} Archive, Paper 2026/1432},
  year         = {2026},
  url          = {https://eprint.iacr.org/2026/1432},
  note         = {Abstract read only}
}
@misc{DKT26,
  author       = {Quang Dao and Scott Duke Kominers and Justin Thaler},
  title        = {{Reed-Solomon} Codes Beyond {Johnson}: Efficient Decoding and Smaller Cryptographic Proofs},
  howpublished = {Cryptology {ePrint} Archive, Paper 2026/2056},
  year         = {2026},
  url          = {https://eprint.iacr.org/2026/2056},
  note         = {Abstract read only}
}
@inproceedings{BCIKS20,
  author    = {Eli Ben-Sasson and Dan Carmon and Yuval Ishai and Swastik Kopparty and Shubhangi Saraf},
  title     = {Proximity Gaps for {Reed--Solomon} Codes},
  booktitle = {Proceedings of the 61st Annual {IEEE} Symposium on Foundations of Computer Science ({FOCS} 2020)},
  pages     = {900--909},
  year      = {2020},
  note      = {Reference data from ePrint 2026/680; not opened}
}
@inproceedings{DP24,
  author    = {Benjamin E. Diamond and Jim Posen},
  title     = {Polylogarithmic Proofs for Multilinears over Binary Towers},
  booktitle = {Advances in Cryptology -- {EUROCRYPT} 2026},
  year      = {2026},
  doi       = {10.1007/978-3-032-25336-1_1},
  note      = {Cryptology ePrint Archive, Paper 2024/504 (last revised 2026-05-14); abstract read only},
  url       = {https://eprint.iacr.org/2024/504}
}
@inproceedings{LCH14,
  author    = {Sian-Jheng Lin and Wei-Ho Chung and Yunghsiang S. Han},
  title     = {Novel Polynomial Basis and Its Application to {Reed-Solomon} Erasure Codes},
  booktitle = {Proceedings of the 55th Annual {IEEE} Symposium on Foundations of Computer Science ({FOCS} 2014)},
  pages     = {316--325},
  year      = {2014},
  doi       = {10.1109/FOCS.2014.41},
  note      = {arXiv:1404.3458; bibliographic data from dblp and ACM listings; not opened}
}
@misc{NA25,
  author       = {Andrija Novakovic and Guillermo Angeris},
  title        = {Ligerito: A Small and Concretely Fast Polynomial Commitment Scheme},
  howpublished = {Cryptology {ePrint} Archive, Paper 2025/1187},
  year         = {2025},
  url          = {https://eprint.iacr.org/2025/1187},
  note         = {Abstract read only}
}
@misc{BRW26,
  author       = {Benedikt B{\"u}nz and Ron D. Rothblum and William Wang},
  title        = {Flock: Fast Proving for Batch Boolean Computations},
  howpublished = {Cryptology {ePrint} Archive, Paper 2026/1329},
  year         = {2026},
  url          = {https://eprint.iacr.org/2026/1329},
  note         = {Revised 2026-09-19 (after the leanVM pin); Section 5, Appendix C.3, Theorem 8, Lemma 9, Remark 11}
}
@misc{GMW25,
  author       = {Albert Garreta and Nicolas Mohnblatt and Benedikt Wagner},
  title        = {A Simplified Round-by-round Soundness Proof of {FRI}},
  howpublished = {Cryptology {ePrint} Archive, Paper 2025/1993},
  year         = {2025},
  url          = {https://eprint.iacr.org/2025/1993},
  note         = {TCC 2026 (minor revision); abstract and changelog read only}
}
@misc{CDHZ26,
  author       = {Alessandro Chiesa and Zijing Di and Zihan Hu and Yuxi Zheng},
  title        = {How to Prove Post-Quantum Security for Succinct Non-Interactive Reductions},
  howpublished = {Cryptology {ePrint} Archive, Paper 2025/2166},
  year         = {2025},
  url          = {https://eprint.iacr.org/2025/2166},
  note         = {EUROCRYPT 2026 (major revision); abstract read only}
}
@misc{M3,
  author       = {{Irreducible}},
  title        = {Multi-Multiset Matching ({M3})},
  howpublished = {Binius documentation, \url{https://www.binius.xyz/basics/binius-v0/m3/definition}},
  note         = {Undated web page, read 2026-09-30}
}
@book{Tha22,
  author    = {Justin Thaler},
  title     = {Proofs, Arguments, and Zero-Knowledge},
  series    = {Foundations and Trends in Privacy and Security},
  volume    = {4},
  number    = {2--4},
  year      = {2022},
  url       = {https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf},
  note      = {Author PDF of 2023-07-18; Proposition 4.1, Sections 4.6, 5.2, 6.6.2}
}
@article{BEGKN94,
  author  = {Manuel Blum and William S. Evans and Peter Gemmell and Sampath Kannan and Moni Naor},
  title   = {Checking the Correctness of Memories},
  journal = {Algorithmica},
  volume  = {12},
  number  = {2--3},
  pages   = {225--244},
  year    = {1994},
  note    = {Reference data from leanVM refs.bib; not opened}
}
@inproceedings{Tha13,
  author    = {Justin Thaler},
  title     = {Time-Optimal Interactive Proofs for Circuit Evaluation},
  booktitle = {Advances in Cryptology -- {CRYPTO} 2013},
  year      = {2013},
  note      = {Cited by ePrint 2025/118, Remark 3; not opened}
}
@misc{SL20,
  author       = {Srinath Setty and Jonathan Lee},
  title        = {Quarks: Quadruple-efficient transparent {zkSNARKs}},
  howpublished = {Cryptology {ePrint} Archive, Paper 2020/1275},
  year         = {2020},
  url          = {https://eprint.iacr.org/2020/1275},
  note         = {Abstract read only}
}
@misc{STW24,
  author       = {Srinath Setty and Justin Thaler and Riad Wahby},
  title        = {Unlocking the lookup singularity with {Lasso}},
  howpublished = {Cryptology {ePrint} Archive, Paper 2023/1216},
  year         = {2023},
  url          = {https://eprint.iacr.org/2023/1216},
  note         = {EUROCRYPT 2024; abstract read only}
}
@misc{PH23,
  author       = {Shahar Papini and Ulrich Hab{\"o}ck},
  title        = {Improving logarithmic derivative lookups using {GKR}},
  howpublished = {Cryptology {ePrint} Archive, Paper 2023/1284},
  year         = {2023},
  url          = {https://eprint.iacr.org/2023/1284},
  note         = {Abstract read only}
}
@misc{Gru24,
  author       = {Angus Gruen},
  title        = {Some Improvements for the {PIOP} for {ZeroCheck}},
  howpublished = {Cryptology {ePrint} Archive, Paper 2024/108},
  year         = {2024},
  url          = {https://eprint.iacr.org/2024/108},
  note         = {Sections 3.1, 3.2}
}
@misc{DT24,
  author       = {Quang Dao and Justin Thaler},
  title        = {Constraint-Packing and the Sum-Check Protocol over Binary Tower Fields},
  howpublished = {Cryptology {ePrint} Archive, Paper 2024/1038},
  year         = {2024},
  url          = {https://eprint.iacr.org/2024/1038},
  note         = {Abstract read only}
}
@misc{HJRRR25,
  author       = {Tamir Hemo and Kevin Jue and Eugene Rabinovich and Gyumin Roh and Ron D. Rothblum},
  title        = {Jagged Polynomial Commitments (or: How to Stack Multilinears)},
  howpublished = {Cryptology {ePrint} Archive, Paper 2025/917},
  year         = {2025},
  url          = {https://eprint.iacr.org/2025/917},
  note         = {EUROCRYPT 2026 (minor revision); abstract read only}
}
@misc{TDWHH26,
  author       = {Devon Tuma and Quang Dao and James Waters and Alexander Hicks and Nicholas Hopper},
  title        = {{VCVio}: Verified Cryptography in {Lean} via Oracle Effects and Handlers},
  howpublished = {Cryptology {ePrint} Archive, Paper 2026/899},
  year         = {2026},
  url          = {https://eprint.iacr.org/2026/899},
  note         = {Abstract read only}
}
@misc{Del25,
  author       = {G. Dell'Immagine},
  title        = {Introducing {Clean}, a formal verification {DSL} for {ZK} circuits in {Lean4}},
  howpublished = {zkSecurity blog, \url{https://blog.zksecurity.xyz/posts/clean/}},
  year         = {2025},
  note         = {Reference data from arXiv:2607.23752, reference 57; not opened}
}
@misc{KSHC26,
  author        = {Arman Kolozyan and Tom Sorger and Alexander Hicks and Stefanos Chaliasos},
  title         = {{ZKP} Security Tools and Verification: Coverage, Effectiveness, Adoption, and Challenges},
  year          = {2026},
  eprint        = {2607.23752},
  archivePrefix = {arXiv},
  primaryClass  = {cs.CR},
  url           = {https://arxiv.org/abs/2607.23752},
  note          = {Version 1, 2026-07-26; Section VI}
}
@misc{AGGLNST26,
  author        = {Jeremy Avigad and Anat Ganor and Lior Goldberg and David Levit and Ohad Nir and Yoav Seginer and Alon Titelman},
  title         = {Formal verification of the {S-two} {AIR}},
  year          = {2026},
  eprint        = {2606.04311},
  archivePrefix = {arXiv},
  url           = {https://arxiv.org/abs/2606.04311},
  note          = {Sections 2--5}
}
@misc{AGLST21,
  author        = {Jeremy Avigad and Lior Goldberg and David Levit and Yoav Seginer and Alon Titelman},
  title         = {A verified algebraic representation of {Cairo} program execution},
  year          = {2021},
  eprint        = {2109.14534},
  archivePrefix = {arXiv},
  url           = {https://arxiv.org/abs/2109.14534},
  note          = {CPP 2022 venue unverified; not opened}
}
@misc{Mar26,
  author        = {Diego Marmsoler},
  title         = {{Isabelle/STARK}: A Formalization of {zk-STARK} in {Isabelle/HOL}},
  year          = {2026},
  eprint        = {2608.01965},
  archivePrefix = {arXiv},
  url           = {https://arxiv.org/abs/2608.01965},
  note          = {Version of 2026-09-22; abstract read only}
}
@misc{Kob26,
  author       = {Nadim Kobeissi},
  title        = {Verification Theatre: False Assurance in Formally Verified Cryptographic Libraries},
  howpublished = {Cryptology {ePrint} Archive, Paper 2026/192},
  year         = {2026},
  url          = {https://eprint.iacr.org/2026/192},
  note         = {Abstract read only}
}
@misc{Gun26,
  author       = {Cody Gunton},
  title        = {On Formal Verification and a Bug in {SP1} Hypercube},
  howpublished = {Ethereum Foundation zkEVM blog, \url{https://zkevm.ethereum.foundation/blog/sp1-fv}},
  year         = {2026},
  note         = {2026-05-20; read by a helper of this task, not re-read}
}
@misc{Kad25,
  author       = {George Kadianakis},
  title        = {Shipping an {L1} {zkEVM} \#2: The Security Foundations},
  howpublished = {Ethereum Foundation blog, \url{https://blog.ethereum.org/2025/12/18/zkevm-security-foundations}},
  year         = {2025},
  note         = {2025-12-18; read via a fetch summary}
}
@misc{soundcalc,
  author       = {{Ethereum Foundation}},
  title        = {soundcalc: a universal soundness calculator across hash-based {zkEVMs} and security regimes},
  howpublished = {\url{https://github.com/ethereum/soundcalc}},
  year         = {2026},
  note         = {README read 2026-09-30 (repository pushed 2026-09-21)}
}
@misc{ProximityPrize,
  author       = {{Ethereum Foundation}},
  title        = {The Proximity Prize},
  howpublished = {\url{https://proximityprize.org/}},
  year         = {2026},
  note         = {Read 2026-09-29}
}
@techreport{NethermindOpenVM26,
  author      = {{Nethermind}},
  title       = {Formal Verification of the {OpenVM} {RISC-V} {zkVM} --- Technical Report},
  institution = {Nethermind},
  year        = {2026},
  note        = {Dated 2026-02-01; REPORT.pdf in \url{https://github.com/openvm-org/openvm-fv}}
}
@misc{SP1Lean,
  author       = {{Succinct Labs}},
  title        = {sp1-lean ({SP1Clean})},
  howpublished = {\url{https://github.com/succinctlabs/sp1-lean}},
  year         = {2026},
  note         = {Branch dtumad/v1.0-release at eb6f44b9 (2026-08-12)}
}
@misc{PicoFV,
  author       = {{Nethermind}},
  title        = {pico-fv: Formal verification of the {Brevis} {Pico} {zkVM}},
  howpublished = {\url{https://github.com/NethermindEth/pico-fv}},
  year         = {2026},
  note         = {Pushed 2026-06-11}
}
@misc{ZiskFV,
  author       = {{eth-act}},
  title        = {zisk-fv: {Lean} 4 formal verification of {RISC-V} compliance of {ZisK}},
  howpublished = {\url{https://github.com/eth-act/zisk-fv}},
  year         = {2026},
  note         = {Pushed 2026-09-23}
}
@misc{RiscvZkvm,
  author       = {{Verified-zkEVM}},
  title        = {riscv-zkvm: {Lean} extraction of the {Sail} {RISC-V} specification for verified {zkVM} projects},
  howpublished = {\url{https://github.com/Verified-zkEVM/riscv-zkvm}},
  year         = {2026}
}
@misc{Veridise25,
  author       = {{Veridise}},
  title        = {{RISC} {Zero}'s {zkVM} Security: How {Veridise} Enabled Provable \& Continuous {ZK} Security},
  howpublished = {\url{https://veridise.com/blog/audit-insights/risc-zeros-zk-vm-security-how-veridise-enabled-risc-zero-to-achieve-provable-continuous-zk-security/}},
  year         = {2025},
  note         = {2025-03-27; read via a fetch summary}
}
@misc{NethermindZKsync25,
  author       = {{Nethermind}},
  title        = {We verified the verifier: a first for zero-knowledge proof systems},
  howpublished = {\url{https://www.nethermind.io/blog/we-verified-the-verifier-a-first-for-zero-knowledge-proof-systems}},
  year         = {2025},
  note         = {2025-09-02; read via a fetch summary}
}
@inproceedings{KDT25,
  author    = {C. Kwan and Q. Dao and J. Thaler},
  title     = {Verifying {Jolt} {zkVM} Lookup Semantics},
  booktitle = {Financial Cryptography and Data Security ({FC} 2025)},
  series    = {LNCS},
  volume    = {15751},
  year      = {2025},
  note      = {Reference data from arXiv:2607.23752, reference 24; not opened}
}
@misc{ArkLib,
  author       = {{Verified-zkEVM}},
  title        = {{ArkLib}: Formally Verified Arguments of Knowledge in {Lean}},
  howpublished = {\url{https://github.com/Verified-zkEVM/ArkLib}},
  note         = {Revisions dca90385 and 7653a901}
}
@misc{Clean,
  author       = {{Verified-zkEVM}},
  title        = {Clean: {Lean} circuit {DSL}},
  howpublished = {\url{https://github.com/Verified-zkEVM/clean}},
  note         = {Revision 42fe4b26}
}
@misc{CompPoly,
  author       = {{Verified-zkEVM}},
  title        = {{CompPoly}},
  howpublished = {\url{https://github.com/Verified-zkEVM/CompPoly}},
  note         = {Revision 572f9973}
}
```
