# End-to-end ROM knowledge soundness: design of the compilation theorem

Local working note for the branch `e2e/rom-knowledge-soundness`. It fixes the architecture of the
end-to-end theorem and, in detail, the random-oracle argument that turns a doom certificate of
a verifier program (`LeanerVM/Protocol/Compile/Prog.lean`) into a bound on the compiled verifier
(`LeanerVM/Spec/Verifier.lean`, Part 2).

## The chain of theorems

```text
ValidExecution prog input t                                   (Semantics)
   ▲  constraintSoundness (leanISA Layers 9-10)
SatisfiedBy prog input w                                      (Arithmetization)
   ▲  satisfiedBy_witnessOf (the adaptor, #98)
M3Holds (leanIsaInstance F prog s) input q                    (Protocol, ideal model)
   ▲  list-binding + front phases' rbr knowledge soundness (ArkLib kSF, #95)
      + WHIR rbr soundness (Annex B, deployed variant)
Cert (leanVmProgram ...)  : a doom certificate of the DSL program whose doom after the
                            first commitment is "no codeword in the Johnson list of the
                            committed word decodes to a stack satisfying M3Holds"
   ▲  romSound (this note)
Pr_H[ verify^H accepts ∧ the extracted word has no good list member ] ≤ N·δ
```

The deployed verifier is `Compile.runProof blake2sBytes (leanVmProgram ...)`, a transcription of
`python-verifier/verifier.py` at leanVM `127510d1`; the theorem is about the same program with
`H` a random oracle.

## The random-oracle model

* One oracle `H : Bytes → Digest` (BLAKE2s-256 as a random oracle on byte strings of any length):
  the chain steps and Merkle nodes are its 64-byte inputs, the leaves its 384- and 512-byte
  inputs, the seeding its other inputs.
* Lazy sampling with an ordered log `ℓ : List (Bytes × Digest)` (fresh queries in order); the
  bridge to VCVio's `randomOracle` is proved once (`ToVCVio/Rom/`).
* The experiment: the adversary `A` (an `OracleComp (Bytes →ₒ Digest) Proof`, at most `Q_A`
  queries), then the verifier on its output (at most `Q_V` queries, a function of the program's
  size), sharing the log. `N = Q_A + Q_V`.
* The engine (`ToVCVio/Rom/`): for `Φ : log → ENNReal` with `Φ [] = 0` and
  `E_u[Φ(ℓ ++ [(t,u)])] ≤ Φ ℓ + δ` for every fresh `t`, `Pr[ev] ≤ N·δ` for every event with
  `ev → Φ(final log) ≥ 1`.

## Decoding a log

Scan the log in order. Everything below is a function of a log prefix.

* **Seed.** The seed computation is a fixed chain of queries from the statement (leanVM:
  `ivpre = "leanvm" ‖ len ‖ R1CS_DIGEST ‖ H(bytecode)`, `iv = H(ivpre)`, `seed = H(iv ‖ pi)`). The
  seed state is its result read off the log, when present.
* **Chain states.** A digest `d` with a decoded block history `bs`: the seed with `[]`; and
  `u` with `bs ++ [blk]` for a log entry `(digestBytes d ++ blk, u)` with `|blk| = 32` and `d`
  decoded with `bs`. Under no-failure (below) a digest has at most one decoding.
* **Program position.** Follow the program along the blocks: at `read` a block `(x, 1)`
  continues with `read x`; at `sample` the block `(0, 2)` continues with `sample (challengeOf u)`
  where `u` is the step's output; at `grind b` the block `(n, 4)` continues with `grind b`; at
  `commit ht w` two blocks `(x0, 1)`, `(x1, 1)` continue with `commit ht w W` where `W` is the
  word extracted for the root `digestOfScalars (x0, x1)` (none: off-program); at `query i ps`
  the program continues with the rows of the extracted word (no block is consumed). A block the
  program does not expect makes the state *off-program*. On-program states carry their IOP
  history `h` (a `Reachable` history of the program) and their node `P.after h`.
* **Word extraction.** For a root `r`, height `ht`, width `w`: position `p` is read by walking
  down from `r`, at depth `j` taking the unique log input `x` with output the current digest,
  requiring `|x| = 64` and splitting it into `left ‖ right`, going right iff bit `ht − 1 − j` of
  `p` is set; at the bottom the unique input with the leaf digest must have `8·w` bytes and is
  parsed into `w` words. Any missing step gives the zero row of width `w`. Extracted words are
  well shaped.
* **PoW bases.** A log entry `(digestBytes d ++ (0,3)-block, b)` with `d` on-program at a
  `grind` node makes `b` the base of `d`; the entry `(digestBytes b ++ (n,4)-block, v)` is the
  proof of work of the pair `(d, n)`, valid iff `powOk bits n v`.

## Failure

A fresh entry `(t, u)` appended to `ℓ` *fails* if `u` is

* the output of an entry of `ℓ` (collision), or
* a 32-byte aligned chunk (offset 0 or 32) of an input of `ℓ` or of `t` itself (prediction of a
  referenced digest), or
* a root decoded in `ℓ` (the two halves absorbed at a commitment), or one of the seed's
  intermediate digests' inputs.

`Fail ℓ` holds if some entry failed with respect to its prefix. The number of excluded values
at a step is at most `c · (|ℓ| + 1)` for a small constant `c`, so a step fails with probability
at most `c·(|ℓ|+1)/2^256`.

Consequences under `¬ Fail`:

* decodings are unique and stable: an entry appended later never changes the decoding of an
  earlier digest, nor the word extracted for a root already absorbed (any change would need a
  later output equal to a referenced digest);
* an accepted compiled run is an on-program chain path whose openings equal the extracted
  words' rows (a mismatch climbs two different inputs to one root: a collision or a
  prediction).

## The potential

`Φ ℓ := if Fail ℓ then 1 else min 1 (Σ_g term g)`, the sum over *group instances* `g`:

* **Plain groups.** An on-program state `s` at a boundary history `h₀` with `D h₀`, whose node is
  `sample`/`query`, and which is not a `grind` boundary: the instance exists once the first
  squeeze `s ‖ (0,2)` is in the log; its term is `esc D h p` at the deepest decoded state of the
  group's (linear) chain of squeezes.
* **Proof-of-work groups.** For an on-program state `d` at a `grind b` node with `D` at its
  history and each nonce `n` for which the state query `d ‖ (n,4)` or the proof of work
  `base(d) ‖ (n,4)` is in the log: term `ρ · e`, where `ρ = 2^-b` if the proof of work is not in
  the log and `1`/`0` by `powOk` if it is, and `e` is `esc D h p` at the deepest state of the
  group that starts after the nonce (its prospective value `esc D h₀ p₀ ≤ ε h₀` before the first
  squeeze).
* Groups from boundaries outside `D` contribute nothing.

## The step inequality

For `ℓ` with `¬ Fail ℓ` and a fresh `t`: `E_u[Φ(ℓ ++ [(t,u)])] ≤ Φ ℓ + δ` with
`δ = max_h ε_eff h + c(N+1)/2^256`, `ε_eff h = 2^-(grindBits h) · ε h`. Cases on `t`:

1. a squeeze from the deepest state of a group: the term is a martingale (`esc` at a `sample`
   node is the average of its children, and `challengeOf u` is uniform on `E` for uniform `u`);
   at a group start the term appears with mean `esc D h₀ p₀ ≤ ε h₀` (times `ρ` for a
   proof-of-work group);
2. a nonce absorption `d ‖ (n,4)`: creates the pair's term with value `2^-b·esc D h₀ p₀` if the
   proof of work is unrevealed, else changes nothing;
3. a proof of work `base(d) ‖ (n,4)`: `ρ` goes from `2^-b` to `powOk`, mean `2^-b`; creates the
   term with mean `2^-b · esc D h₀ p₀` if it did not exist;
4. a prover move at a doomed state (read, commit halves): doom is kept (the certificate), no
   term changes;
5. anything else (Merkle hashing, base queries, seeding, off-program steps): no term changes.

The failure case contributes at most `c(|ℓ|+1)/2^256` (`Φ ≤ 1`).

## The final inequality

If the compiled verifier accepts, `¬ Fail`, and the extracted history of its run passes through
a boundary in `D`, then `Φ ≥ 1`: the run's final history is not in `D` (`Cert.final`), prover
moves keep `D`, so some group of the run left `D`, and that group's term is `1` (its chain is
complete in the log, its proof of work, if any, was checked).

## The leanVM certificate

* Before the first commitment: `D` is false.
* After the first commitment `W₀`: `D` iff no interleaved codeword in the Johnson list of
  `W₀` (radius `γ₀`) decodes to a stack `q` with `M3Holds (leanIsaInstance F prog s) input q`,
  where `s` are the announced sizes; then, through the front phases, "every list member is
  doomed for the front's ArkLib knowledge state function"; then the WHIR invariant.
* Knowledge: the extractor reads `W₀` off the log (word extraction at the root of the run), and
  returns the stack of the list member satisfying `M3Holds`, if any; `¬ D` after the first
  commitment means one exists. Then `witnessOf` (the adaptor) and `constraintSoundness` give
  the execution.

## The deployed WHIR and its round-by-round invariant

The deployed opening (`verify_whir`, `verifier.py:1008-1100`) differs in shape from Annex B's
Protocol: there is one running sumcheck over all `μ` variables, and each level's new claims
(the out-of-domain claim and the batched consistency claims) are *glued* into the running round
polynomial with powers of the level's `λ`, each with its own "intro" round polynomial, instead
of starting a fresh batched sumcheck. The analysis follows Annex B's proof of Theorem rbr with
that change.

Notation: variables in sumcheck order; level `i` binds `ℓ_i` variables; its oracle `O⁽ⁱ⁾` has
`2^ℓ_i` lanes (the first `ℓ_i` variables still free) and columns in the domain of the code
`C_i = RS[E, D_i, 2^κ_i]` (`κ_i` the variables left after the level, rate `2^-R_i`, encoder
`Enc_i` in the novel basis, message bit `k` = the `k`-th remaining variable). Level 0's lanes are
the stack's six *high* coordinates (`f(u, x) = q(x, u)`, hence the rotated terminal point and the
reversed level-0 rows). `L_{i,j} = List_{γ_i}(O⁽ⁱ⁾_{s≤j})`, the Johnson list of the oracle folded
by the level's first `j` challenges; `g_V` the multilinear a list member decodes to.

Invariant at each boundary (the doom predicate on the WHIR part of a history):

* `A(i, j)` (after fold `j` of level `i`, and after the round polynomial that follows it):
  every `V ∈ L_{i,j}` violates the running claim `(W_{i,j}, σ_{i,j})`.
* after the commitment of `O⁽ⁱ⁺¹⁾`: `A(i, ℓ_i)` (now about `c = O⁽ⁱ⁾_s`, one word).
* after the out-of-domain value `y` and its intro polynomial, and after the nonce: `A(i, ℓ_i)`
  and the members of `L_{i+1,0}` are pairwise distinct at `z`.
* after the query/`λ` group and the query intro polynomial: `A(i+1, 0)` for the glued claim
  `W' + λ·eq(z,·) + λ²·Σ_q λ^q W⁽ⁱ⁾_{x_q}`, `σ' + λ·y + λ²·Σ_q λ^q c_q`
  (final level: `λ`, `λ^{1+q}`, no out-of-domain claim).
* final level, after `f_final`: `A(r−1, ℓ)` with `f_final` fixed; after its query group: `f_final`
  violates the glued claim; in the tail: `f_final` violates the running claim, which the
  terminal check refutes.

Group escapes (each a sum over the group's challenges):

* fold `s_j`: `2·L_i/|E| + 2^{ℓ_i−j}·ε_mca,i` (two distinct quadratics agree at ≤ 2 points;
  fold-list lemma from ArkLib's `mcaError_affineLine_johnson_le`);
* out-of-domain point: `C(L_{i+1}, 2)·κ_i/|E|`;
* query positions and `λ` (after 17 bits of proof of work): `(1−γ_i)^{t_i} + (t_i+1)·L_{i+1}/|E|`
  (final level: `(1−γ)^t + t/|E|`, no list: `f_final` is sent);
* tail round: `2/|E|`.

The level-0 batching is the opening's `ρ` (`verify_stacked_opening`), sampled right after the
ring-switching challenges, so it shares their group: `L₀ ×` (ring-switching errors) +
`(J−1)·L₀/|E|`. A list member at level 0 is `K`-valued: its limbs 1 and 2 are codewords
agreeing with the `K`-valued word's zero limbs on more than `2^κ₀ − 1` points.

## The front phases

The front (bus, table sumcheck, public input, Flock with ring switching) keeps its ArkLib proofs:
for each phase `X`, `Phase.Security` gives a knowledge state function `kSF^X` and a worst-case
per-challenge bound. With `S^X_m(stmt, q, tr) := ∃ w, kSF^X_m stmt tr w` (the stack `q` is the
phase's oracle statement), the doom on the front part of a history is
`∀ U ∈ L_{0,0}, ¬ S^X_m(stmt_X, g_U, decode_X(prefix))`, `stmt_X` the output of the earlier phases'
verdicts on their decoded transcripts. Prover moves keep it (`toFun_next`), a challenge escapes it
with probability at most `L₀ · ε^X_m`, and the phases chain through the seams (`toFun_full` of `X`,
`toFun_empty` of the next). The work is the decoding `decode_X` of the DSL program's reads and
samples into the phase's ArkLib transcript, and the equality of the DSL program's checks with the
phase's guarded verifier on decoded transcripts.

## As built (corrections to the note above)

* `romSound` (`Compile/Rom/Sound.lean`) is the theorem: for a certificate with
  `2^-min(grindBits h, 64) · ε h ≤ εmax`, an adversary of `Q_A` queries and a verifier of `Q_V`,
  `Pr[accept ∧ Doomed] ≤ (Q_A + Q_V)·(εmax + (4 + k)(Q_A + Q_V)/2^256)`, `k` the seeding steps,
  on VCVio's `randomOracle`.
* A plain group's term is created at the entry that creates its boundary state (a scalar, the
  second root half, the seed), not at the first squeeze: a group with no squeeze (openings only)
  would otherwise escape without a term.
* The root rule also excludes the new entry's own input; seeding steps are injective
  (`prefix ++ digestBytes d ++ suffix`).
* The proof-of-work discount is `2^-min(b, 64)`: `powOk` tests one 64-bit word.
* Specifications (`Compile/Spec.lean`) fold the follower's lead into the potential
  (`retDoom`); a first formulation charged it through a return probability in `bound`, which
  double-counted returns outside doom and made `Spec.bind` false.
