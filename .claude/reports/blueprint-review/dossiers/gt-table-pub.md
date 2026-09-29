# Dossier `gt-table-pub`: the table sumcheck and the public-input check

Ground truth at the pin `a386121f`, then the blueprint and the spine set against it.
Object reviewed: leanerVM `main` at `b435631`. Libraries: ArkLib `dca90385`, CompPoly `3468b38c`
(both read under `.lake/packages/`).

## 0. Summary

**Examined, in full unless a range is given.** Specification `03-proving-primitives.tex`,
`04-committing-the-witness.tex`, `05-arithmetization.tex`, `06-bus-interactions.tex`,
`07-instruction-tables.tex`, `08-end-to-end-protocol.tex`; the statement of the round-by-round
theorem in `b-polynomial-commitment-scheme.tex:127-152`. Rust `constraints.rs`, `tables.rs`,
`colval.rs`, `cpu/mod.rs`, `cpu/layout.rs`, `pcs.rs`, `fiat_shamir/src/transcript.rs`;
`leaf.rs:1-170, 270-951`; `gkr.rs:328-430`; `hash_flock.rs:1-118`;
`crates/pcs/src/stack_open.rs:70-115, 473-543`. Python `verifier.py:1-900, 1300-1439`. The
recursion guest `crates/rec_aggregation/guests/aggregate.py:1655-1691` (not named in the task;
found by search, it is a third executable verifier). Blueprint and status in full; the tracker's
hole comment (read with `gh api`, nothing posted). Lean `Spine/{Instance,Seams,Phase,Compose,Toy}`,
`PublicInput.lean`, `Padding.lean`, the tests `Spine.lean` and `PublicInput.lean`; ArkLib
`OracleReduction/Security/RoundByRound.lean:60-230, 500-590`. Two Lean probes, both built
(section 9).

**Conclusions.**

1. **Table sumcheck: the three sources agree on the transcript** (one challenge `ξ`, `τ_max`
   rounds of three field elements, one final message of 104 field elements, one final check, a
   derived target). The round consistency equation is not a check in either verifier: the wire
   omits the linear coefficient and the verifier derives it.
2. **Public input: the specification disagrees with every executable verifier.** §8.2 writes one
   equation per limb; the Rust verifier, the Python verifier and the recursion guest check one
   combined equation `c₀ + y·c₁ = (1+r)·w₀ + r·w₁` in `E`. The combined check accepts `|E|` pairs
   `(c₀, c₁)` per challenge, the per-limb check one. Both have knowledge error `1/|E|`. All three
   sources pool the top-limb claim `mem₂(r,0,…,0) = 0` with no scalar sent.
3. **The blueprint's conventions for the table sumcheck match the ground truth** (variable
   order, joining round, padding, degree, `ξ` powers, derived target, pool order). Its errors
   `(B+2)/|E|` on `ξ` and `3/|E|` per round are correct and tight; the specification's batching
   term `(B+ν_side)/|E|` is loose by one.
4. **The spine's slot for the table sumcheck cannot be filled by the deployed verifier.**
   `Seam.bus` admits statements of shapes the deployed protocol never sees (any number of linear
   claims, terms of one table at unrelated points, terms on any table of the instance, and a
   degree clause on the statement alone). Completeness and round-by-round knowledge soundness are
   owed on all of them. They hold only for a generalized sumcheck whose verifier carries guards
   that leanVM has not, and whose error on `ξ` is otherwise unbounded.
5. **The blueprint does not say which tables the sumcheck ranges over.** Its leanISA instance
   makes the six shared columns tables of the instance; leanVM's sumcheck ranges over the six
   opcode tables only. Read literally, Layer 7 has more rounds and a longer final message than
   leanVM.
6. **The zerocheck point recycling costs `τ_max/|E|` once, not per constraint**, and nothing at
   all in a round-by-round state function that is a conjunction with the GKR's. The blueprint
   over-charges it and places it inconsistently.

**Findings by severity** (full entries in section 8).

| Severity | Finding |
| --- | --- |
| critical | none |
| major | The bus seam admits statements the deployed table sumcheck cannot serve |
| major | The table sumcheck's tables are not distinguished from the instance's other tables |
| major | The public-input phase proves a check no executable verifier runs, and the debt is assigned to a layer that cannot pay it |
| minor | The round message: four coefficients and a check in the oracle protocol, three and none on the wire; the owed lemma is not stated |
| minor | The zerocheck escape is over-charged, and charged in three different ways |
| minor | Layer 7's sketch and the tracker's signature predate the spine; one theorem is a placeholder |
| minor | Layer 9's sketch makes the eighteen limb claims an input of Flock |
| minor | Two status findings are wrong at the pin (the round message "at four nodes"; "the Python verifier omits the caps") |
| minor | The tracker's text for the public-input phase is stale |
| note | The specification's batching error is loose by one; it gives no error for the recycled point; it does not say which coefficient is dropped |
| note | Stale comments in the Rust on the round message |
| note | The spine's slot does not pin the protocol: a phase that reads the whole oracle fills it |

## 1. Notation

`K = GF(2^64)`, `E = GF(2^192) = K[y]/(y³+y+1)`. Six opcode tables `t = 0..5` in the order
XOR, MUL_NATIVE, SET_CONSTANT, DEREF, JUMP, BLAKE2S, of log-heights `τ_t` and widths
`n_t = 15, 15, 8, 15, 14, 37` (sum **104**). `τ_max = max_t τ_t` (at least 3: the BLAKE2S table
has `τ_5 ≥ 3`). `B = Σ_t (number of constraints of t) = 2` (JUMP's two; every other table has
none). Three *sides* `s = 0, 1, 2`: push, pull, count. `ζ ∈ E^{μ_bus}` is the terminal point of
the bus phase's GKR. `totals_s` (the specification's `rem_s`) is what the tables owe side `s`.
`B^s_t` is table `t`'s bus form for side `s`, a polynomial of degree at most 2 in the columns of
`t` with coefficients in `E`.

Widths, from `tables.rs`: `arith::N = 15` (`:455`), `set::N = 8` (`:537`), `deref::N = 15`
(`:608`), `jump::N = 14` (`:711`), `blake2st::N = 37` (`:862`); Python `TABLE_WIDTHS`
(`verifier.py:823-834, 852`); specification §7 column lists (`07-instruction-tables.tex:12, 30,
58, 78, 99, 122`), which give the same counts (BLAKE2S: 19 stacked columns plus the 18 limbs).

## 2. Part A. The transcript, as deployed

### A.1 Table sumcheck

| # | Step | Specification | Rust | Python |
| --- | --- | --- | --- | --- |
| T0 | What precedes: the bus phase's last prover message is the five boundary evaluations (`mem₀, mem₁, mem₂`, `cntfin_mem` at `ζ_{<κ_mem}`; `cntfin_bc` at `ζ_{<κ_bc}`) | `08:70` "For their committed columns the prover sends one evaluation each" | `leaf.rs:909-920` (`decompose_verify`), order fixed by `cpu/layout.rs:361-395` | `verifier.py:552-557` |
| T1 | **Challenge** `ξ ← E` (one element), drawn after T0 | `08:75` "Samples and sends the batch challenge ξ∈E"; `05:145` | `cpu/mod.rs:726` `let zc_xi = vs.sample();` (prover `:590`) | `verifier.py:1389` |
| T2 | **Powers.** Constraint `i` (0-based) of table `t` takes `ξ^{o_t+i}`, `o_t` the number of constraints of the tables before `t`; side `s` takes `ξ^{B+s}`, shared by every table. For leanVM: `ξ⁰ → b + v_cond·w`, `ξ¹ → v_cond·(b+1)`, `ξ², ξ³, ξ⁴ →` push, pull, count | `05:145`; `08:75` "a disjoint range per table; the last ν_side weight the bus forms, one per side and shared by every table" | `constraints.rs:74-82` (`xi_offsets`), `:254-255, 281`; `cpu/mod.rs:413-422` (`xi_form_base`, `xi_form_pows`); `tables.rs:70-74` | `verifier.py:1390-1392`, `:621-623`, `:798-800` |
| T3 | **Target, derived, never sent**: `T = Σ_s ξ^{B+s}·totals_s` | `05:151-155` "the verifier computing the right side itself"; `08:76` "against the target the verifier derived from the three leaf claims" | `cpu/mod.rs:735` | `verifier.py:1393` |
| T4 | **Number of rounds** `τ_max`, the maximum over the six opcode tables | `05:145, 155`; `08:76` | `constraints.rs:250` `airs.iter().map(\|a\| a.tau).max()` | `verifier.py:607` `max(table_log_heights)` |
| T5 | **Round `j = 0..τ_max−1` binds variable `m = τ_max−1−j`** (highest first). **Prover message**: three elements of `E`, the coefficients `c₀, c₂, c₃` of the cubic `h_j`, in that order | `05:155` "Rounds bind X_{τmax−1} first"; `08:76` "the round check pins one of the four coefficients (§3), so a round costs three E-elements" (which coefficient: not said) | prover `constraints.rs:164, 191-194` (`add_round_poly(&h, false)`); encoding `transcript.rs:63-71` (`fixed = 1`) | `verifier.py:409` "The transcript contains c0, c2, c3" |
| T6 | **Verifier computation**: `c₁ := claim + c₂ + c₃`, so that `h_j(0)+h_j(1) = claim` holds by construction. No rejection path | `03:84` states it as a check, `03:110` as the reason one coefficient is not sent | `transcript.rs:289-309`; `constraints.rs:267` | `verifier.py:409-410` |
| T7 | **Challenge** `r_m ← E` after the round message; `claim := h_j(r_m)` | `03:84` | `constraints.rs:268-270` | `verifier.py:424-426` |
| T8 | **Joining and padding.** Table `t` is active in the round binding `m` iff `τ_t > m`, that is from round `τ_max − τ_t` on. Verifier's weight: `w_t := ∏_{m<τ_t}(1+ζ_m+r_m) · ∏_{τ_t ≤ m < τ_max} r_m` | `05:146-150, 155` | `constraints.rs:271-274` | `verifier.py:609-614` |
| T9 | **Final prover message**: for `t = 0..5` in order, `n_t` elements: the value of every column of `t`, the eighteen BLAKE2S limbs included, at `r_{<τ_t} = (r_0,…,r_{τ_t−1})`. 104 elements, no challenge in between | `08:77` "The prover sends one value per column of every table" | `constraints.rs:224-238` (prover), `:279-280` (verifier); `cpu/mod.rs:378` `n_cols: table.n_committed_columns()` | `verifier.py:619-620` |
| T10 | **Final check**: `Σ_t w_t·(Σ_i ξ^{o_t+i}·C_{t,i}(e_t) + Σ_s ξ^{B+s}·B^s_t(e_t)) = claim`, else reject | `08:77` "checks that they reproduce the sumcheck's final value" | `constraints.rs:277-290` (`Error::FinalMismatch`); summand `cpu/mod.rs:380-383` | `verifier.py:616-625` |
| T11 | **Claims pooled**: for `t`, then for local column `c`: column `base_t + c`, point `r_{<τ_t}`, value `e_{t,c}` | `08:77` "the column values then enter the claim pool, T_j's at ρ_{<τ_j}" | `cpu/mod.rs:428-441` (`constraint_claims`) | `verifier.py:624` |
| T12 | **The eighteen limbs**: their claims are in the pool at their place (BLAKE2S local columns 9 to 26) and are *located* on `q_flock`: low 8 coordinates frozen to the slot's bits, then the point, then `q_flock`'s selector | `08:77` "live in q_flock, not the stack, so their claims route there"; `07:120-122` | `cpu/mod.rs:447-453, 790-814` (`SlotClaim::Strided`); `tables.rs:394-413`; `hash_flock.rs:96-115` | `verifier.py:847-850, 886-894`; `:295-297` |

Counts: the prover sends `3·τ_max + 104` elements; the verifier draws `1 + τ_max` challenges.

Verbatim, the Rust verifier's loop and final check (`constraints.rs:261-291`):

```rust
    let mut claim = target;
    let mut chi = vec![F192::ZERO; n];
    for j in 0..n {
        let m = n - 1 - j;
        // `h(0)` is derived from the running claim rather than transmitted, so
        // the round-consistency check it used to enable holds by construction.
        let h = vs.next_round_poly(4, claim, None).map_err(|_| Error::Truncated)?;
        let rk = vs.sample();
        chi[m] = rk;
        claim = poly_eval(&h, rk);
        let eq_k = F192::ONE + zeta[m] + rk;
        for (t, air) in airs.iter().enumerate() {
            weights[t] *= if air.tau > m { eq_k } else { rk };
        }
    }

    let mut acc = F192::ZERO;
    let mut claims = Vec::with_capacity(airs.len());
    for (t, air) in airs.iter().enumerate() {
        let evals = vs.next_scalars(air.n_cols).map_err(|_| Error::Truncated)?;
        let w = &pows[offsets[t]..offsets[t] + air.n_constraints];
        acc += weights[t] * (air.eval)(w, &evals);
        claims.push(Claims {
            chi: chi[..air.tau].to_vec(),
            evals,
        });
    }
    if acc != claim {
        return Err(Error::FinalMismatch);
    }
    Ok(claims)
```

and the decoding (`transcript.rs:289-302`): with `eq = None`, `fixed = 1`, the three transmitted
coefficients are read into indices 0, 2, 3 and `coeffs[fixed] = claim + sum_from(2)`.

### A.2 Public input

| # | Step | Specification | Rust | Python |
| --- | --- | --- | --- | --- |
| P0 | Precondition: each public word has top limb 0 | `08:29` "two 192-bit words (with top limb 0)"; no check stated | type `[F192; 2]`; `read_public` rejects `half.c2 != 0` with `CpuError::PublicInput` (`cpu/mod.rs:141-143`) | by type: `Digest` is 32 bytes, `halves()` builds `E(w0, w1)` (`verifier.py:204-219`) |
| P1 | **Challenge** `r ← E`, after the 104 values of T9 | `08:83` | `cpu/mod.rs:745` (prover `:610`) | `verifier.py:1398` |
| P2 | **Prover message**: two elements `c₀, c₁` | `08:29, 84` | `cpu/mod.rs:746-749` (prover `:611-618`) | `verifier.py:1399` |
| P3 | **Check** | per limb: `c_ℓ = (1+r)·mem[g⁰]_ℓ + r·mem[g¹]_ℓ`, `ℓ ∈ {0,1}` (`08:29-32`) | combined: `c₀ + y·c₁ = interp(pi₀, pi₁, r)` (`cpu/mod.rs:752-755`) | combined, the same (`verifier.py:1400`) |
| P4 | **Claims pooled**: `mem₀, mem₁, mem₂` at `(r, 0, …, 0)` with values `c₀, c₁, 0`; no scalar for the third | `08:84` "pools them, with 0 for the top limb" | `cpu/mod.rs:746` (array initialised to zero, two entries read), `:674-682` (`bind_pi_claim`) | `verifier.py:1399, 1401-1402` |

### A.3 The claim pool, in order

| Rank | Claims | Number | Source |
| --- | --- | --- | --- |
| first power of `λ` | the ring-switched claim on `q_flock` | 1 | `08:98`; `stack_open.rs:518-519`; `verifier.py:1413` |
| then | bus: `mem₀, mem₁, mem₂, cntfin_mem` at `ζ_{<κ_mem}`, `cntfin_bc` at `ζ_{<κ_bc}` | 5 | `cpu/mod.rs:663`; `verifier.py:555-557, 1395` |
| then | table sumcheck: T11, of which 18 strided on `q_flock` | 104 | `cpu/mod.rs:664`; `verifier.py:1395` |
| then | public input: P4 | 3 | `cpu/mod.rs:665`; `verifier.py:1402` |

`finish_claims` (`cpu/mod.rs:656-667`) is the one place the order is fixed in the Rust. The pool
has 112 point claims and the batch 113 powers of `λ`.

### A.4 Disagreements between the three sources

| Subject | Disagreement | Which the blueprint follows |
| --- | --- | --- |
| The public-input check (P3) | The specification checks two equations; the Rust, the Python and the recursion guest check one. Section 7 | the specification |
| The round consistency equation (T6) | The specification lists "every sumcheck's rounds" among the checks (`08:100`); in both verifiers it holds by construction and cannot reject | neither: its oracle protocol sends four coefficients and checks (section 4, item 7) |
| Which coefficient is omitted (T5) | The specification does not say; both verifiers omit the linear coefficient `c₁` | the verifiers (acceptance test 8) |
| The batching error | The specification charges `(ν_side + B)/|E|` (`05:155`); its own Corollary 3.7 gives `(ν_side + B − 1)/|E|`. The code states none | neither: `(B+2)/|E|`, the tight value |
| Order of JUMP's columns | The specification lists `w, b` before the counts (`07:99`); both verifiers put them last (`tables.rs:689-711`; `verifier.py:826`). The listing is not presented as an order | the verifiers, through leanISA (`leanisa-blueprint.md:611-612`: "`Row` is the table's column list in the Rust's order") |
| Guard `zeta.len() < n` | Rust only (`constraints.rs:251-253`). Unreachable: every table has at least three push blocks, so `μ_bus ≥ τ_max + 1` | not modelled; nothing to model |
| Comments in the Rust | `constraints.rs:24` says the round polynomial "is sent WHOLE, at four nodes"; `:265-266` says "`h(0)` is derived". The code sends three *coefficients* and derives `c₁`; `h(0) = c₀` is transmitted (`transcript.rs:63-71`) | the code; but the status repeats "four nodes" (finding in section 8) |

No other disagreement found. Checked and agreeing: the moment of every challenge; the power
assignment; the three sides and their order (`leaf.rs:610-622`; `verifier.py:570-574`); the
variable order and the weights; the order of the 104 values (column lists compared entry by
entry, `tables.rs:436-863` against `verifier.py:823-834`); the slot of each limb
(`hash_flock.rs:85-115` against `verifier.py:847-850`: `cv` 0 to 3, `out` 4 to 7, `m` 10 to 17,
metadata 18, 19); the pool order.

## 3. Part B. The checks, enumerated

"Deferred" means: the check is a claim entering the pool, enforced by the opening.

### B.1 Table sumcheck

| Check | Specification | Rust | Python | Without it, accepted although outside the relation |
| --- | --- | --- | --- | --- |
| **Round message present** (stream long enough) | implicit | `constraints.rs:267` → `Error::Truncated` | `verifier.py:364` | not a soundness check: a format check |
| **Round polynomial of degree at most 3** | `05:155` | structural: the message is three coefficients | structural | with messages of unbounded degree the per-round error `3/|E|` becomes `D/|E|`; at `D ≥ |E|−1` a prover sends a polynomial agreeing with the true round polynomial everywhere but at 0 and fixes the sum there |
| **Round consistency** `h_j(0)+h_j(1) = claim` | `03:84`; `08:100` | by construction (`transcript.rs:296-302`) | by construction (`verifier.py:409-410`) | in a protocol sending four coefficients and not checking: any witness. The prover sends arbitrary polynomials and, in the last round, the true last round polynomial along the challenges drawn; the final check passes with the true column values. Example: a JUMP row with `v_cond = 1, b = 0` (branch not taken on a nonzero condition) |
| **Target derived from the leaf claims** (no transmitted target) | `05:151-155`; `08:76` | `cpu/mod.rs:728-735` | `verifier.py:1393` | with a transmitted target: the prover sends the true sum of `F`. Nothing then ties the tables' share of the bus to the GKR leaf claims: a committed XOR row whose memory flush is not what the bus trees were built from is accepted. The Rust says so (`cpu/mod.rs:733-734`: "A transmitted target would be a free value in its own check") |
| **Constraints in the summand** (the terms `ξ^{o_t+i}·C_{t,i}`, contributing 0 to the target) | `05:133-136, 146-150` | `cpu/mod.rs:380-383`; `tables.rs:725-730` | `verifier.py:621` | a witness violating a JUMP identity: `v_cond = 1, w = 1, b = 0`. The state push `b·v_pc + b·g·pc + g·pc` then falls through; the bus balances; the execution skipped a jump the program takes |
| **Distinct powers of `ξ` per constraint** | `05:145` | `constraints.rs:74-82` | `verifier.py:621-623` | with equal weights, the same row: `C₁ = b + v_cond·w = 1` and `C₂ = v_cond·(b+1) = 1` cancel in characteristic 2 |
| **Bus forms in the summand, powers shared across tables** | `05:138-143` | `cpu/mod.rs:374, 404-422` | `verifier.py:622` | without the forms: the tables' columns are tied to the bus by nothing. With one power per table and side, the target does not factor through `totals_s` and the per-table shares would have to be sent, free values in their own check |
| **The point is `ζ`, drawn after the commitment** | `05:132` | `cpu/mod.rs:739` (`&bus.point`); order of `pcs::read_commitment` (`:714`) before the bus | `verifier.py:1382-1385, 1394` | with a point fixed before the commitment: commit a column whose constraint extension vanishes at `ζ_{<τ}` and nowhere else on the cube |
| **Final message present** | implicit | `constraints.rs:280` → `Truncated` | `verifier.py:364` | format |
| **Final check** (T10) | `08:77` | `constraints.rs:288-290` → `FinalMismatch` | `verifier.py:625` | any witness: the prover sends the true column values and arbitrary rounds |
| **The 104 column claims hold** (deferred) | `08:77, 97-99` | `cpu/mod.rs:664, 768` | `verifier.py:1395, 1413` | the prover sends column values chosen to pass the final check, unrelated to the commitment |
| **The eighteen limb claims are claims on `q_flock`'s slots** (deferred, located by T12) | `08:77`; `07:120` | `cpu/mod.rs:798-806` | `verifier.py:886-894` | if the limbs were columns of their own: memory words read by BLAKE2S rows unrelated to the words Flock proves the compression of; any digest can be "computed" |

### B.2 Public input

| Check | Specification | Rust | Python | Without it, accepted although outside the relation |
| --- | --- | --- | --- | --- |
| **Top limb of the public words is 0** (P0) | a precondition | `cpu/mod.rs:141-143` → `CpuError::PublicInput` | by type | the transcript binds four lanes (`digest_words`, `cpu/mod.rs:99-106`), so two statements differing in a top limb would share a transcript (`:139-140`) |
| **Two scalars present** | implicit | `cpu/mod.rs:748` → `CpuError::Transcript` | `verifier.py:364` | format |
| **The line** (P3) | per limb | combined | combined | with no line check: any cells 0 and 1. The prover sends the true evaluations; every claim holds; the public input is bound to nothing |
| **Claims on `mem₀, mem₁`** (deferred) | `08:33, 84` | `cpu/mod.rs:674-682` | `verifier.py:1402` | the prover sends the line's values whatever the memory holds |
| **Claim `mem₂(r,0,…,0) = 0`** (deferred; no scalar) | `08:84` | `cpu/mod.rs:746, 674-682` | `verifier.py:1399, 1402` | a memory whose cell `g⁰` holds `w₀ + y²·t`, `t ≠ 0`. The two low limbs pass the line. The proof attests an execution on a word that is not the public word |

**The top limb, source by source.** All three pool the claim with value 0 and send nothing for
it. The recursion guest does the same (`aggregate.py:1688-1689`:
`claim_pool[GEN ** claim_idx] = 0`). A public word with a nonzero top limb: excluded by the
specification's definition; rejected by the Rust verifier before any message is read (the Rust
prover only `debug_assert!`s it, `cpu/mod.rs:552-555`); not expressible in the Python, nor in
leanISA, whose `PublicInput` is four lanes of `K` (`LeanerVM/Semantics/Memory.lean:101-110`), so
the Rust's rejection has no counterpart to model.

### B.3 Around the two phases

The stream is fully consumed (`cpu/mod.rs:769`, `vs.finish()`; `verifier.py:1414`): trailing
scalars reject. Every 192-bit pattern is an element of `E`, so stream scalars have no
canonicity check (`verifier.py:104-106` requires 24 bytes).

## 4. Part C. The blueprint set against it

Lean objects used below. A `CMvPolynomial n K` is CompPoly's computable polynomial in `n`
variables over `K`. A `Column n` is a table of `2^n` values in `K`; its *extension* at a point
of `E^n` is `eval₂Mle`. The spine's claims, copied from `LeanerVM/Protocol/Spine/Seams.lean`:

```lean
structure VirtualTerm (I : M3Instance) where
  /-- The weight of the term in the sum. -/
  weight : E
  /-- The table. -/
  j : Fin I.ntab
  /-- The polynomial of the row. -/
  poly : CMvPolynomial (I.width j) K
  /-- The point the virtual table is extended to. -/
  point : Vector E (I.τ j)
```
(`:71-79`)
```lean
structure LinearClaim (I : M3Instance) where
  /-- The terms. -/
  terms : List (VirtualTerm I)
  /-- The claimed value. -/
  value : E
```
(`:91-95`)
```lean
structure BusOut (I : M3Instance) where
  /-- The linear claims. -/
  linear : List (LinearClaim I)
  /-- The column claims. -/
  columns : List (ColumnClaim I)

/-- What the table sumcheck hands on: column claims only. -/
structure TableOut (I : M3Instance) where
  /-- The column claims. -/
  columns : List (ColumnClaim I)
```
(`:130-139`)
```lean
def bus := of I fun (s : I.Stmt × BusOut I) q ↦ (∀ c ∈ s.2.linear, c.Holds q) ∧
  (∀ c ∈ s.2.linear, ∀ t ∈ c.terms, t.poly.totalDegree ≤ I.d) ∧
  (∀ c ∈ s.2.columns, c.Holds q) ∧ I.PublicLinesHold s.1 q ∧ I.aux q

/-- After the table sumcheck: every column claim holds, and what it did not touch. -/
def table := of I fun (s : I.Stmt × TableOut I) q ↦
  (∀ c ∈ s.2.columns, c.Holds q) ∧ I.PublicLinesHold s.1 q ∧ I.aux q
```
(`:175-181`)

and the slot, from `LeanerVM/Protocol/Spine/Compose.lean:77-78`:

```lean
  /-- The table sumcheck: from linear claims to column claims (§5.5). -/
  table : Phase.Def I (I.Stmt × BusOut I) (I.Stmt × TableOut I)
```

### C.1 Item by item

| # | Ground truth | Blueprint counterpart | Verdict |
| --- | --- | --- | --- |
| 1 | `ξ` after the boundary evaluations (T1) | Layer 7 `pSpec := V_to_P : E ; …` (`:989`) | matches |
| 2 | Power assignment (T2) | conventions, row *Table sumcheck* (`:323`); acceptance test 9 | matches for leanISA. Over the spine's types the assignment is "the position of a claim in `BusOut.linear`", which nothing states: finding *bus seam* |
| 3 | Target derived (T3) | row *Table sumcheck*; `tableSummand_target` (`:990`) | matches |
| 4 | `τ_max` over the six opcode tables (T4) | Layer 7 `Virtual E τ_max (Σ_j width_j) 3` (`:987`), over the tables of `I` | **does not match** once the instance has the shared columns as tables (Layer 3, `:836-839`): finding *sumcheck tables* |
| 5 | Highest variable first; joining round (T5, T8) | row *Table sumcheck*; acceptance test 16 | matches |
| 6 | Padding by `∏_{k ≥ τ_t} X_k` (T8) | `Padding.lean`: `padHigh`, `sumCube_padHigh`, `evalMle_padHigh` (`:60-73`); acceptance test 7 | matches. `evalMle_padHigh` gives the factor `∏ s[b]`, the Rust's `rk` of `constraints.rs:273` |
| 7 | Three coefficients on the wire, `c₁` derived, no round check (T5, T6) | row *Sumcheck messages* (`:315`): "the oracle protocol sends all of them. Dropping one is the *encoding* of Layer 12" | **deviation, declared**: a message of four coefficients and a check leanVM has not. Finding *round message* |
| 8 | Final message of 104 values (T9) | Layer 7 `P_to_V : Fin (Σ width) → E` (`:989`) | matches for the six tables; see item 4 |
| 9 | Final check (T10) | Layer 7, "the formula reproduces the final value" (`:997-998`) | matches |
| 10 | Claims and their order (T11, A.3) | row *Claim pool order* (`:324`); `PublicInput.pooled` appends after `s.2.columns` (`PublicInput.lean:127-128`) | matches |
| 11 | The limbs as strided claims (T12) | Layer 3, "The layout has two readers" (`:841-848`); the spine's `Layout` admits it | matches. Layer 9's sketch does not: finding *limb claims and Flock* |
| 12 | `r` after the 104 values; two scalars (P1, P2) | `PublicInput.pSpec` (`PublicInput.lean:99`); `PublicLine.sent` | matches (one message of two elements; the chain absorbs them one by one either way) |
| 13 | The check (P3) | per limb: `check` is `decide (cs = expectedValues I s.1 r)` (`PublicInput.lean:136-137`) | **deviation, declared** (status finding F18; Layer 8, `:1053-1062`): the specification's, not the verifiers'. Finding *public-input check* |
| 14 | Pooled values are the scalars *sent* (P4) | `lineClaim` pools `lineValue`, the value the verifier computes (`PublicInput.lean:119-124`) | equal under the per-limb check; **not** under the combined check, where the sent pair may be `(L₀ + y·δ, L₁ + δ)`. A phase for the deployed check must pool what was sent |
| 15 | Third claim with value 0 (P4) | three lines, the third with cells `0, 0` and `sent := false` (`:335`, `:834-836`); acceptance test 10; test `PublicInput.lean:176-180` | matches |
| 16 | Three sides: push, pull, count | the spine's `Side` has `push \| pull` (`Instance.lean:51-54`); counts are `I.counts`; the count form is one more linear claim | expressible; the phrase "three bus sides" of row *Table sumcheck* has no type behind it in the spine |
| 17 | Errors | Layer 7 (`:994`), Layer 8 (`:1027`), row *Seams* (`:333`) | section 5 |

### C.2 Layer 7's sketch against the spine as built

| | Layer 7 (`:986-995`) with Layer 6's `BusOut` (`:960-964`) | The spine as built |
| --- | --- | --- |
| Input statement | `BusOut` = `ζ : Fin μ_bus → E`, `rem : Fin 3 → E`, `pool : List Claim`, `α`, `β` | `I.Stmt × BusOut I`, `BusOut I` = `linear`, `columns` |
| The public input | absent | threaded through every seam |
| The point `ζ` | a field | absent; one point per term |
| The bus forms | recomputed by the table verifier from `α, β, ζ` and the leaf layout | data: terms with weights in `E` |
| The zerocheck claims | implicit (the instance's constraints at `ζ`) | data: one linear claim each, if the bus phase emits them |
| The three values | `rem` | the `value` of three linear claims |
| Output | `BusOut × ColumnClaims` (keeps `ζ, rem, α, β`) | `I.Stmt × TableOut I` (column claims only) |
| `tableSumcheck_relOut_implies_constraints` | `(∀ j C, C̃_j(ζ_{<τ_j}) = 0 → …) -- see below` | no counterpart; the statement is a placeholder |

The tracker's hole comment has a third signature, `tableSumcheck I (S : Sumcheck.Def) :
Phase.Def I (BusOut I) (TableOut I) (tableSpec I) (Seam.bus I) (Seam.table I)` with
`tableSummand I ζ ξ α β rem`: the spine has no `tableSpec` and `Phase.Def` takes no relation.

**Which to keep.** Neither as it stands. Layer 7's needs `α, β` and the selectors of the leaf
stack, which the abstract instance does not carry. The spine's is too general (section 6).
leanVM's own seam is between the two, the Rust's `BusVerify` (`leaf.rs:849-860`):

```rust
pub struct BusVerify {
    pub claims: Vec<ColumnClaim>,
    pub bytecode_claims: Vec<BytecodeClaim>,
    pub count_root: F192,
    /// The GKR point ζ, reused as the table sumcheck's eq point.
    pub point: Vec<F192>,
    /// `forms[side][table]`, for the zerocheck to settle.
    pub forms: [Vec<BusForm>; 3],
    /// Per side, what the tables' blocks owe its leaf claim: `Ṽ₀(ζ)` less the
    /// framework blocks' decomposition. Derived here, pinned by the batch's target.
    pub totals: [F192; 3],
}
```

one point, the forms as data per side and table, one value per side, the column claims. Keep
from the spine: the public input threaded, the output reduced to column claims, `α, β` and the
leaf layout private to the bus phase. Take from leanVM: the point in the statement and the
forms indexed by side and table (proposed change in section 8).

## 5. Part D. The errors

### D.1 What is stated

| Term | Specification | Blueprint |
| --- | --- | --- |
| batching by `ξ` | `(ν_side + B)/|E|` (`05:155`, citing Corollary 3.7) | `(B + 2)/|E|` on `ξ` (`:994`) |
| each round | `3/|E|`, `3·τ_max` in all (`05:155`, citing Fact 3.8) | `3/|E|` per round (`:994`) |
| the recycled point | none. `05:132`: sound "as long as it results from uniform sampling occurring after the table columns are committed" | row *Seams* (`:333`): "`1/|E|` per coordinate per constraint", in the bus phase. Layer 7 (`:1001-1003`): "charged to the `(α, β)` and GKR challenges of Layer 6 … as an extra `τ_max/|E|` per constraint". Layer 6 (`:973-975`): `busError` "is `4·2^μ_bus/|E|` on the `(α, β)` message plus `gkrError 3 μ_bus`", no such term. Acceptance test 6 (`:1283`): "The state function of Layer 7 charges the zerocheck to Layer 6's challenges" |
| public input | `1/|E|` (`08:33`) | `1/|E|` on the one challenge (`:1027`) |

The specification has no round-by-round statement for these phases: its only one is Theorem
B.2, for the opening (`b-polynomial-commitment-scheme.tex:139-152`), with the remark that the
round-by-round error "is the maximum of these entries over all rounds".

### D.2 The table sumcheck, worked

Let the input carry `k` claims `Σ(claim c) = v_c`, `c = 0..k−1` (deployed: `k = B + 3`), with
true sums `s_c` and `δ_c = v_c − s_c`. State function:

- *before `ξ`*: every `δ_c = 0`;
- *after `ξ`*: `D(ξ) = 0`, `D(X) = Σ_c δ_c X^c`. If some `δ_c ≠ 0`, `D` is nonzero of degree at
  most `k − 1`: at most `k − 1` roots. **Error on `ξ`: `(k−1)/|E| = (B+2)/|E|`.** Tight: `D` may
  have `k − 1` distinct roots.
- *after the challenge of round `j`*: the running claim is the true partial sum at the
  challenges drawn. If false before the round, the message `h_j` (whose `h_j(0)+h_j(1)` is the
  running claim, by check or by construction) differs from the true round polynomial `H_j`;
  both have degree at most 3. **Error per round: `3/|E|`.** Tight.
- *after the final message*: the verifier accepts and every column claim holds. If the running
  claim is not `F(r)`, values passing the final check are not the true values, so some column
  claim is false. **No error on a prover message.**

Verdict: the blueprint's two terms are correct, tight, and on the right challenges. The
specification's `(ν_side + B)` is an upper bound one too large.

### D.3 The recycled point, settled

**Which challenges are `ζ`.** The last GKR layer is radix 4 (`μ_bus ≥ 16`). Its sumcheck has
`μ_bus − 2` rounds, challenges `x_0, …, x_{μ_bus−3}`; then the children are sent; then two
challenges `(low, high)`; and `ζ = (low, high, x_0, …, x_{μ_bus−3})` (`gkr.rs:414-426`:
`point = vec![low_challenge, high_challenge]; point.extend_from_slice(&round_point);`;
`verifier.py:451-454`: `point = [*y, *x]`). So `ζ_0, ζ_1` are drawn last and `ζ_{2+i} = x_i`.
Table `t` uses `ζ_{<τ_t}`. Neither `α` nor `β` is a coordinate of `ζ`.

**Lemma.** Let `P` be a multilinear polynomial over `E`, and let some of its variables be fixed
so that the restriction `P'` is not identically zero. Fix one more variable `X_k` to a uniform
`a ∈ E`. The restriction becomes identically zero for at most one `a`.
*Proof.* `P' = A + X_k·B` with `A, B` free of `X_k`, not both zero. If `B = 0` no `a` works.
Otherwise pick a monomial with a nonzero coefficient `b` in `B`, and `a'` its coefficient in `A`:
`a' + a·b = 0` has one solution. ∎

**State function for the zerocheck.** `Z(prefix)`: for every constraint `C_{t,i}`, the extension
`C̃_{t,i}` with the coordinates of `ζ_{<τ_t}` drawn so far substituted is identically zero.
Before the last GKR layer, `Z` is "every constraint vanishes on every row". At the end, `Z` is
"every `C̃_{t,i}(ζ_{<τ_t}) = 0`", which the output's zerocheck claims imply. A prover message
does not change `Z`.

**Per challenge.** If `Z` is false, some `C̃_{t,i}` has a nonzero restriction. `Z` becomes true
only if *that one* becomes zero: by the lemma, probability at most `1/|E|` on `x_i` for
`i + 2 < τ_max`, zero on `x_i` for `i + 2 ≥ τ_max` (no table has that coordinate), and at most
`2/|E|` on the pair `(low, high)`. **In total `τ_max/|E|`, once for all constraints**: the event
"every claim is true although some constraint is violated" is contained in "the first violated
constraint's extension vanishes at `ζ`"; no union over the constraints is taken.

**In the bus phase's state function.** That function is a conjunction `G ∧ Z`, `G` the state of
the grand products and the boundary claims. For a fixed prefix, either `G` is false (and must
flip) or `G` is true and `Z` is false (and must flip). So the error of a challenge is
`max(ε_G, ε_Z)`, not the sum. On the rounds of the last layer `ε_G = 5/|E| ≥ 1/|E|`; on the
last pair `ε_G = 2/|E| ≥ 2/|E|`. **The recycled point adds nothing to `busError`**, per
challenge or in the sum, when the state function is the conjunction. Layer 6's formula, which
has no zerocheck term, is then the right one, and the word "extra" of Layer 7 and of row
*Seams* is not needed.

Verdict on the blueprint: an upper bound, so not wrong; loose by the factor `B` and by the
addition; attributed to `(α, β)`, which do not carry it; stated three ways. Under the spine it
can only be the bus phase's: a phase's state function charges that phase's challenges, so
acceptance test 6's "the state function of Layer 7" cannot be meant literally.

### D.4 The public input

Per limb: a line whose cells differ from the statement's by `(a, c) ∈ K²`, not both zero, is
hit when `(1+r)·a + r·c = 0`, one `r` at most. Several wrong lines need one `r` for all. Error
`1/|E|`, attained (test `PublicInput.lean:106-110`). Combined: section 7. Correct, tight, on the
one challenge.

## 6. Part E. Can the real table sumcheck fill the spine's slot?

What the slot demands. ArkLib's round-by-round knowledge soundness, in the form the spine uses
(`RoundByRound.lean:553-568`, ArkLib `dca90385`), quantifies over every input statement:

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

A *knowledge state function* (`:164-189`) is a predicate on partial transcripts that is the
input relation on the empty transcript (`toFun_empty`, an `iff`), that a prover message cannot
turn from false to true (`toFun_next`), and that is true on every full transcript on which the
verifier outputs a statement in the output relation (`toFun_full`). The error is a function of
the challenge alone, fixed with the phase (`Component.Def.err`). Here the oracle `q` is part of
the input statement and the witness is `Unit`.

**Consequence used three times below.** If for some statement outside the input seam a prover
makes the verifier accept with an output inside the output seam with probability `p`, then
`Σ_i err i ≥ p`: the state is false at the start, true at the end of those runs, and flips only
on challenges.

### E.1 Is the deployed sumcheck a protocol on such general statements?

No. The deployed verifier takes one point `ζ`, one form per side and table, three values, and
reads the constraints off the instance. `Seam.bus` admits four things it does not handle.

**(a) A clause on the statement alone, which the verifier must then check.** The degree clause
does not mention `q`. Probe (section 9): on the toy, the stack `q0` with columns `[1,1]`,
`[1,1]`, `[0,0]` satisfies `M3Holds toy 0`; the statement with the single claim "the term `X₂³`
at the point `0` sums to `0`" is true of `q0`, its public line holds, and it is outside
`Seam.bus toy` by the degree clause alone. On that statement the summand is identically zero:
a verifier that does not inspect degrees accepts the all-zero run with true column claims, with
probability 1. So a table verifier must compute `totalDegree` of every term it is handed and
reject above `I.d`. The deployed verifiers have no such check and no such input. In the composed
protocol the guard never fires.

**(b) Any number of linear claims: the error on `ξ` is unbounded over the seam.** Take `k`
claims, each one term with the constant polynomial `1` (degree 0), weight 1: true sum 1. Give
claim `c` the value `1 + δ_c` with `Σ δ_c X^c = ∏_{i<k−1}(X + a_i)` for distinct `a_i ∈ E`. The
statement is outside the seam, and at each of the `k − 1` roots the batched target is the true
batched sum, after which the honest prover wins. So `err ξ ≥ (k−1)/|E|` for every `k` the
verifier accepts. With `err ξ = (B+2)/|E|` the verifier must reject more than `B + 3` claims.
The probe exhibits a list of 1000 true claims on the toy, which has one constraint and one
flush.

**(c) Terms of one table at unrelated points.** The probe's claim `twoPoints` has two terms of
table 0, at the points `0` and `1`, and is inside the seam (each clause evaluated). The
deployed verifier computes one factor `∏(1+ζ_m+r_m)` per table. Completeness on `twoPoints`
needs one factor per term.

**(d) Terms on any table of the instance.** With Layer 3's instance (the second finding of
section 8), a term may sit on the memory's table, of log-height `κ_mem ≥ 16`. A sumcheck
of `τ_max` rounds, `τ_max` the maximum over the opcode tables, cannot fold it when
`τ_max < κ_mem`.

**What the abstract phase would have to be.** Over the seam as built: a generalized sumcheck.
Draw `ξ`; give the claim at position `c` of `linear` the power `ξ^c`; run `max_j τ_j` rounds
over *every* table of `I` with
`F = Σ_c ξ^c Σ_{t ∈ c} t.weight · eq(t.point, X_{<τ_{t.j}}) · t.poly(columns) · ∏_{k ≥ τ_{t.j}} X_k`;
send every column of every table; the verifier guards the degree and the number of claims and
computes one `eq` factor per term. Its schedule depends on `I` alone, so it is a legitimate
`Phase.Def`, and its round polynomials have degree `I.d + 1`.

**Does it have the deployed transcript on the honest path?** Only if three more things hold,
none of which the blueprint states: the bus phase emits exactly `B` zerocheck claims in table
order and then the three forms in the order push, pull, count; the rounds and the final message
range over the opcode tables only; and the guards are shown dead in the composition so that
`verify` may omit them.

**Should `Seam.bus` carry the shape instead?** Yes. It is the question the degree bound already
answered once (decision 14), and the degree bound is its smallest instance. Better than a
clause: put the shape in the *type* of the statement, so that there is nothing to check
(proposed change, section 8). A clause on the statement alone is a guard in the verifier; a
type is not.

### E.2 The eighteen limbs as `ColumnClaim`s

A limb is column `⟨5, 9 + i⟩` of the instance's shape, of log-height `τ_5`. Its claim is an
ordinary `ColumnClaim` with `point : Vector E τ_5`. `ColumnClaim.Holds` reads the column
through `I.layout.read` (`Seams.lean:66-67`, `Instance.lean:160`), so everything rests on the
layout: for a limb, `read q c` is the slot's entries `q_flock[256·x + slot_i]`, `x < 2^{τ_5}`,
and `extend c z = (bits of slot_i on 8 coordinates, z, selector of q_flock)`. The spine's
`Layout` is a reading law and admits it (`Instance.lean:68-81`). This is the deployed routing
(T12). Nothing between the table sumcheck and the opening treats these claims apart:
`cpu/mod.rs:788-789`, "No downstream special-casing: it folds into the one opening like every
other point claim."

In particular **Flock does not consume them**: the Rust's Flock verifier takes no claim
(`cpu/mod.rs:765`, `verify_reduction(n_blocks, &mut vs)`), and the spine's Flock slot passes the
column claims on. Layer 9's sketch says otherwise (finding *limb claims and Flock*).

### E.3 The output, and knowledge soundness back to the bus seam

On the honest path `TableOut.columns` is the input's `columns` (the five boundary claims)
followed by the 104 claims of T11. The input's column claims must be carried: a phase that
drops them forgets a false boundary claim.

Knowledge soundness from `Seam.table` back to `Seam.bus`, for the generalized phase with its
guards. A statement outside `Seam.bus` has: a false column claim, false lines or false `aux`
(the output is outside `Seam.table` whatever happens: error 0); or a term above the degree, or
too many claims (rejected: error 0); or a false linear claim (D.2). **Error `(k_max − 1)/|E|`
on `ξ`, `(I.d + 1)/|E|` per round, nothing else**, with `k_max` the largest number of claims
the verifier accepts. For leanVM: `4/|E|` and `3/|E|`, in all `(4 + 3·τ_max)/|E|`.

The argument is on paper. Layer 4's generic sumcheck is not built, and ArkLib's single-round
bound is admitted at the pin (the blueprint's ledger row on sumcheck).

### E.4 What the deployed phase needs and the spine's types cannot express

1. **One point.** No `ζ` in the statement; the verifier would have to recover it from the terms
   and reject when they disagree.
2. **The sumcheck's tables.** `M3Instance` does not distinguish the tables the sumcheck ranges
   over.
3. **The order of the powers.** A `List` has an order, but no convention fixes which claim is
   where; acceptance test 9 is stated on Layer 7's `rem`, which the spine has not.
4. **A bound on the number of claims**, needed for a fixed error.
5. **The wire's round message** (three coefficients): section 8, finding *round message*.
6. **Faithfulness itself.** In the ideal oracle model a verifier may query `q` anywhere. A
   "phase" with no message, whose verifier reads `q` on the whole cube and decides every claim,
   fills the slot with both proofs and error zero. The master theorems hold for it. Nothing in
   the spine's types separates it from leanVM's sumcheck: that rests on the phase's definition
   being reviewed against section 2, and on Layer 12's `verify_iff_compiled` with its fixture.

Expressible without change: forms with coefficients in `E` (terms with a weight in `E` and a
polynomial over `K`); the constant `β·Σ_b eq(sel_b, ζ_hi)` (a term with the constant polynomial
1); the count side (one more linear claim); the final check (CompPoly `3468b38c` has
`CMvPolynomial.eval₂` and `aeval`, `CompPoly/Multivariate/CMvPolynomial.lean:133`,
`Operations.lean:130`); the strided limbs.

## 7. Part F. Public input, ground truth

**Specification** (`08-end-to-end-protocol.tex:29-33`):

```tex
The public input is the first two memory cells $\mem[\gen^{0}],\mem[\gen^{1}]$, two $192$-bit words (with top limb $0$) both parties know. The verifier samples $r_m\in\E$, the prover sends $c_0,c_1$ claiming $c_\ell=\mle{\mem_\ell}(r_m,0,\dots,0)$, and the verifier checks
\[
  c_\ell\;\qeq\;(1+r_m)\,\mem[\gen^{0}]_\ell+r_m\,\mem[\gen^{1}]_\ell,\qquad \ell\in\{0,1\}.
\]
Both sides are degree one in $r_m$, so a limb disagreeing with the public words survives with probability at most $1/|\E|$ (Lemma~\ref{lem:sz}). The claims $c_0$, $c_1$ are discharged to the PCS.
```

**Rust** (`cpu/mod.rs:745-756`):

```rust
    let r_pi = vs.sample();
    let mut pi_limbs = [F192::ZERO; 3];
    for v in &mut pi_limbs[..2] {
        *v = vs.next_scalar().map_err(CpuError::Transcript)?;
    }
    // The two claimed evaluations must sit on the public-input line, the top
    // limb's being zero (§sec:e2e-pi).
    let want = primitives::multilinear::interp(l.pi[0], l.pi[1], r_pi);
    if pi_limbs[0] + F192::Y * pi_limbs[1] != want {
        return Err(CpuError::PublicInput);
    }
    let slots = finish_claims(&l, bus.claims, &table_claims, r_pi, pi_limbs);
```

with `interp(lo, hi, t) = lo + t * (lo + hi)` (`primitives/src/multilinear.rs:39-41`) and
`Y = (0, 1, 0)` (`primitives/src/field/gf2_64x3.rs:44`).

**Python** (`verifier.py:1398-1402`):

```python
    public_challenge = transcript.sample()
    public_limbs = (*transcript.next_scalars(2), ZERO)
    require(poly_eval(public_limbs, Y) == multilinear_eval(public_input.halves(), [public_challenge]), "public input check failed")
    public_point = (public_challenge, *[ZERO] * (layout.placements[MEMORY_0].variables - 1))
    claims.extend(ColumnClaim(column, public_point, value) for column, value in zip((MEMORY_0, MEMORY_1, MEMORY_2), public_limbs))
```

**Recursion guest** (`crates/rec_aggregation/guests/aggregate.py:1672-1688`):

```python
    # ---- public-input binding claim: MEM as ONE logical E-column ----
    # The VM's bind_pi_claim makes a SINGLE E-claim at [rm, 0..]:
    #   MEM(rm) = interp(pi_0, pi_1, rm) = pi_0 + rm*(pi_0 + pi_1)
    # over the E-valued public input (no lane splitting, no Frobenius). Both
    # public words have a zero top limb, so that limb's evaluation is zero at
    # every rm; only the two low ones ride the stream and must reassemble it:
    # MEM = v_lo + Y*v_hi (doc sec:e2e-pi).
    fs, rm = squeeze(fs)
    mem = pi_0 + rm * (pi_0 + pi_1)
    fs, mem_lo, cursor = fs_next(fs, cursor)
    fs, mem_hi, cursor = fs_next(fs, cursor)
    assert mem == mem_lo + mem_hi * Y_TOWER
    claim_pool[GEN ** claim_idx] = mem_lo
    claim_idx += 1
    claim_pool[GEN ** claim_idx] = mem_hi
    claim_idx += 1
    claim_pool[GEN ** claim_idx] = 0
```

**Which transcripts each accepts.** Write `w_i = w_{i,0} + y·w_{i,1}` for the public words and
`L_ℓ(r) = (1+r)·w_{0,ℓ} + r·w_{1,ℓ}`, elements of `E`. Then
`interp(w_0, w_1, r) = L_0(r) + y·L_1(r)`.

| | Accepts `(r, c₀, c₁)` iff | Pairs per `r` |
| --- | --- | --- |
| Specification | `c₀ = L_0(r)` and `c₁ = L_1(r)` | 1 |
| Rust, Python, guest | `c₀ + y·c₁ = L_0(r) + y·L_1(r)` | `|E| = 2^192`: the pairs `(L_0(r) + y·δ, L_1(r) + δ)`, `δ ∈ E` |

The first implies the second. Not conversely: `c₀, c₁` are elements of `E`, so the independence
of `1, y` over `K` says nothing of them.

**With the pooled claims true of a committed memory.** Let the cells differ from the public
words by `a_ℓ` (cell 0) and `c_ℓ` (cell 1), in `K`. The true evaluations pass

- the per-limb check iff `(1+r)·a_ℓ + r·c_ℓ = 0` for `ℓ = 0` and `ℓ = 1`;
- the combined check iff `(1+r)·A + r·C = 0`, `A = a_0 + y·a_1`, `C = c_0 + y·c_1`.

If the memory is wrong, `(A, C) ≠ (0, 0)` because `1, y` are independent over `K`, and
`A + r·(A + C) = 0` has at most one solution (`A + C = 0` forces `A = 0`, then `C = 0`). So the
combined check has knowledge error `1/|E|` too. The bad challenges differ: with
`a_0 = 1, c_0 = 0, a_1 = 1, c_1 = 1 + g` the per-limb check has none (limb 0 needs `r = 1`,
limb 1 needs `r = g⁻¹`) and the combined check has `r = (1+y)/(1+y·g)`. The status's example
(zero words, limbs `[0,1]` and `[1,0]`, `r = y/(1+y)`) is checked by
`tests/LeanerVMTests/Protocol/PublicInput.lean:182-210`; I re-derived it by hand.

**Is the Rust's public input two words of `E` or of 128 bits?** By type two words of `E`
(`[F192; 2]`, `Layout.pi`, `cpu/layout.rs:83`). By what the verifier accepts, two words of 128
bits: `read_public` rejects a nonzero top limb, and the transcript is seeded with four lanes.

**Which is the deployed protocol.** The combined check. Three executable verifiers at the pin
run it, the recursion guest among them, and the guest's comment states the intent ("MEM as ONE
logical E-column"). The specification's §8.2 is the outlier. An honest Rust proof passes both:
the Rust prover sends `L_0(r), L_1(r)` (`cpu/mod.rs:611-613`).

## 8. Findings

### The bus seam admits statements the deployed table sumcheck cannot serve
**Severity: major.** Evidence: section 6, E.1; the probe of section 9; ArkLib's definition
quoted in section 6.
**Classification: an error of the blueprint.** The seam is more general than any phase with
leanVM's transcript and leanVM's checks can serve. `Phase.Complete` and `Phase.Security` for the
deployed verifier against `Seam.bus` as built cannot be proved: they need guards (degree, number
of claims, one point per table, tables of the sumcheck) that the deployed verifier has not.
**Proposed change.**
- *As it stands* (blueprint `:481`, `:487-489`, `:560-563`, `:565-574`; `Seams.lean:71-95,
  130-134, 175-177`): `BusOut I` is `linear : List (LinearClaim I)`, `columns`; "The seams carry
  *claims*, not challenges … which is what lets the table sumcheck consume any list of linear
  claims without knowing the bus."
- *As proposed*: the statement has leanVM's shape, the Rust's `BusVerify`.
  ```lean
  /-- A polynomial of the row of table `j` within the degree bound. -/
  abbrev M3Instance.RowPoly (I) (j) := {p : CMvPolynomial (I.width j) K // p.totalDegree ≤ I.d}
  /-- A bus form of table `j`: a combination of row polynomials with weights in `E`. -/
  abbrev M3Instance.Form (I) (j) := List (E × I.RowPoly j)
  structure BusOut (I : M3Instance) where
    point   : Vector E I.τmax                       -- ζ_{<τ_max}
    forms   : Fin 3 → (j : I.SumcheckTable) → I.Form j   -- push, pull, count
    totals  : Fin 3 → E
    columns : List (ColumnClaim I)
  ```
  `Seam.bus`: every constraint of every sumcheck table has extension zero at `point_{<τ_j}`; for
  every side, the forms' extensions at `point_{<τ_j}` sum to `totals`; every column claim holds;
  the public lines; `aux`. The prose becomes: "The bus seam carries the point the bus phase
  ended at, since the table sumcheck runs at it (§5.5); `α, β` and the leaf layout stay inside
  the bus phase, which hands on the forms it built."
- *Reason*: the phase is then leanVM's, with error `(B+2)/|E|` for `B` read off `I`, and its
  verifier has no check leanVM has not. The degree bound moves from a clause to a type.
- *Alternative, smaller*: keep the types and add to `Seam.bus` the clauses "at most `B + 3`
  linear claims", "the terms of a table share their point and the points are prefixes of one
  vector", "terms sit on sumcheck tables"; state in Layer 7 that the verifier checks them and
  the degree, and in Layer 12 that the four guards are dead in the composition.

### The table sumcheck's tables are not distinguished from the instance's other tables
**Severity: major.** Evidence: blueprint `:836-839`, "The stack columns that belong to no
opcode table (`mem_0, mem_1, mem_2`, `cntfin_mem`, `cntfin_bc`, `q_flock` …) are tables of the
instance with no constraints and no flushes"; Layer 7 `:987-989`, `τ_max` and `Σ_j width_j`
over the instance; ground truth T4 and T9. With `κ_mem ≥ 16` every leanISA instance would have
at least 16 rounds and 110 final values; leanVM has `τ_max` rounds (as few as 3) and 104.
**Unverified**: `leanIsaInstance` is not built; this is a reading of the blueprint's text.
**Classification: an error of the blueprint** (an omission).
**Proposed change.**
- *As it stands* (row *Table sumcheck*, `:323`): "Variables bound highest first; table `j` joins
  at round `τ_max − τ_j`; …"
- *As proposed*: prepend "The sumcheck ranges over the tables that have a constraint, a flush or
  a count column (`I.SumcheckTable`; for leanISA the six opcode tables, never the tables of the
  shared columns); `τ_max` is the largest log-height among them and the final message has one
  value per column of each, in table order then column order." Add `SumcheckTable` (a decidable
  predicate on `Fin I.ntab`, derived from `constraints`, `flushes`, `counts`) to the spine, and
  an acceptance test: on an instance with a taller table of no constraint and no flush, the
  number of rounds is the smaller height.
- *Reason*: the schedule is Category B; a longer one rejects every Rust proof.

### The public-input phase proves a check no executable verifier runs, and the debt is assigned to a layer that cannot pay it
**Severity: major.** Evidence: section 7. New to the record: the recursion guest has the
combined check too (`aggregate.py:1683`).
**Classification: a deliberate deviation** (decision 15; status finding F18). It owes a theorem:
round-by-round knowledge soundness of the verifier that checks the combined equation and pools
the scalars sent. The blueprint says "Layer 12 owes it" (`:1062`). Layer 12 is the compilation.
The combined check is a different *oracle verifier*; `verify_knowledgeSound` is derived from the
oracle protocol `verify` compiles; so either `verify` has the per-limb check and is not the
deployed verifier (it rejects proofs the Rust accepts), or it has the combined check and the
oracle protocol must have it, with its `Phase.Security`.
**Proposed change.**
- *As it stands* (`:1060-1062`): "So the pinned verifiers accept transcripts this verifier
  rejects, their knowledge soundness at `1/|E|` is a lemma of its own, and Layer 12 owes it."
- *As proposed*: "So the pinned verifiers accept transcripts this verifier rejects. Layer 8 has
  a second phase for them, `publicInputPhaseWords`: the same schedule; the check
  `Σ_ℓ y^ℓ·c_ℓ = Σ_ℓ y^ℓ·lineValue_ℓ(r)` over the lines whose value is sent, at most three; the
  claims pooled at the values *sent*. Its `Phase.Security` from `Seam.table` to `Seam.pub` has
  error `1/|E|`: the state after the challenge is 'the true evaluations pass the check and
  every pooled claim holds', and a wrong memory gives `A + r·(A + C) = 0` with
  `(A, C) ≠ (0, 0)` by the independence of `1, y, y²` over `K`. The leanISA protocol and
  `verify` use this phase; the per-limb phase is kept as the specification's."
- *Reason*: three verifiers against one paragraph; the master theorem must be about the
  verifier that is deployed. The discrepancy is also a finding against the specification, to
  report to leanVM when reporting is allowed.

### The round message: four coefficients and a check in the oracle protocol, three and none on the wire
**Severity: minor.** Evidence: T5, T6; blueprint `:315`.
**Classification: a deliberate deviation.** It owes a lemma the blueprint does not state.
"Inverted by the running claim" holds only on messages that pass the round check; and ArkLib's
`Verifier.fiatShamir` of a protocol with four-coefficient messages derives the challenge from
four coefficients, where leanVM's chain absorbs three (`transcript.rs:303-307`). So
`verify_iff_compiled` as sketched (`:1218-1221`) needs a challenge oracle defined on the
*encoded* message, and `FiatShamirSecurity` must be stated for that oracle.
**Proposed change**, one of:
- make the wire's message the oracle protocol's (three coefficients, the verifier derives the
  fourth, no round check): the compilation is then literal and one check leaves the audit;
- or keep row *Sumcheck messages* and add: "Layer 4 proves the transport: if a verifier `V`
  reading messages `m` is round-by-round knowledge sound and `dec` is injective from wire
  messages onto the messages passing `V`'s round check, commuting with the challenges, then
  `V ∘ dec` is, at the same error, with the state function `state ∘ dec`."

### The zerocheck escape is over-charged, and charged in three different ways
**Severity: minor.** Evidence: D.1, D.3; the tracker's hole comment for the bus phase repeats
"`1/|E|` per coordinate per constraint".
**Proposed change.**
- *As it stands* (`:333`): "… is charged in the bus phase, coordinate by coordinate as ζ is
  drawn, `1/|E|` per coordinate per constraint …"
- *As proposed*: "… is carried by the bus phase's state function as one more conjunct, 'every
  constraint extension, restricted to the coordinates of ζ drawn so far, is identically zero',
  which a coordinate makes true with probability at most `1/|E|`, whatever the number of
  constraints. The coordinates of ζ are the challenges of the last GKR layer (its rounds, then
  its combination pair), whose own errors are at least that, so `busError` has no term for it."
- Layer 7 (`:1000-1003`): replace "it is charged to the `(α, β)` and GKR challenges of Layer 6,
  where `ζ` is drawn, as an extra `τ_max/|E|` per constraint" by "it is the bus phase's
  (Layer 6), and costs `τ_max/|E|` at most, once". Acceptance test 6 (`:1283`): "The state
  function of Layer 6 carries the zerocheck."

### Layer 7's sketch and the tracker's signature predate the spine
**Severity: minor.** Evidence: C.2. `tableSumcheck_relOut_implies_constraints` (`:991-992`) has
no statement. **Proposed change**: rewrite the sketch on the spine's names,
`def tableSumcheck (I) : Phase.Def I (I.Stmt × BusOut I) (I.Stmt × TableOut I)`,
`tableSumcheckComplete`, `tableSumcheckSecurity`, with `tableSummand I (s : BusOut I) (ξ : E)`;
delete the placeholder (what it meant is the bus phase's zerocheck conjunct).

### Layer 9's sketch makes the eighteen limb claims an input of Flock
**Severity: minor** (for whoever reviews Layer 9). Evidence: E.2; blueprint `:1078-1081`,
`reduction … (StmtIn := ColumnClaims) … (StmtOut := WeightedClaim)`, "`relIn` … the eighteen
column claims are true of `limbColumns`, and aux". In leanVM Flock's reduction takes no claim
and the limb claims are opened with the others. The spine's Flock slot is right.

### Two status findings are wrong at the pin
**Severity: minor.**
- *The round message.* Status, finding F6: "the table round polynomial is a cubic sent whole,
  four nodes, three wire scalars (`constraints.rs:187-194, 267`)". The wire carries
  coefficients, not values at nodes (`constraints.rs:191-194`; `transcript.rs:56-71`: "Send one
  sumcheck round polynomial, as its COEFFICIENTS, constant first"). The phrase copies a stale
  comment (`constraints.rs:24`). Proposed: "a cubic, three of its four coefficients on the wire
  (`c₀, c₂, c₃`)".
- *The caps in the Python verifier.* Status, finding F9: "the Python verifier omits the caps
  `log_mem ∈ [16, 32]`, `τ_j ≤ 32`, the bytecode power-of-two bound and `τ_BLAKE2S ≥ 3`". At the
  pin it has them (`verifier.py:857-864`):
  ```python
    log_bytecode = log2_strict(len(bytecode)) - BUS_BITS
    require(
        16 <= log_memory <= 32
        and all(0 <= log_height <= 32 for log_height in table_log_heights)
        and table_log_heights[OP_BLAKE2S] >= 3
        and 0 <= log_bytecode <= 32,
        "invalid announced table sizes",
    )
  ```
  called from `verify_execution` at `:1378`; `log2_strict` requires a power of two (`:252-254`).
  Outside the two phases of this dossier; recorded because a later part enumerates checks.
  Proposed: retire F9.

### The tracker's text for the public-input phase is stale
**Severity: minor.** The hole comment says of the phase "the prover sends nothing" and "the two
scalars are Layer 12's encoding to read and reconcile"; the phase merged with the prover sending
the values (decision 15). Text to draft only; nothing was posted.

### Notes
- **The specification's batching error** `(ν_side + B)/|E|` is one too large (D.2).
- **The specification gives no error for the recycled point** and no round-by-round statement
  for the table sumcheck or the public input (D.1).
- **The specification does not say which coefficient is omitted**; §3's "a zerocheck round on a
  degree-`d` cofactor therefore costs `d` field elements" (`03:110`) does not apply to the table
  sumcheck, which sends the cubic (`08:76`), because the waiting tables' line `Y·u` is not a
  multiple of the `eq` factor (`constraints.rs:20-26`).
- **The order of the columns inside a table** fixes the order of the 104 values, the ties of the
  stack and the powers of `λ`. The protocol blueprint does not cite it; the leanISA blueprint
  does (`leanisa-blueprint.md:611-612`). Whether leanISA's tables have the Rust's order, the two
  witnessed columns `w, b` of JUMP last, was not checked here.
- **Perfect completeness without exceptional challenges** (acceptance test 20) holds of both
  phases: the verifier's weights are products of `1 + ζ_m + r_m` and `r_m`, the derivation of
  `c₁` is a sum; the only inverse in the prover is of the constant `g + g²`
  (`primitives/src/multilinear.rs:233-241`).
- **Faithfulness is not in the slot's type** (E.4, item 6).

## 9. Probes

Both built with no error and no output. Command, from the repository root:

```sh
flock .claude/reports/blueprint-review/logs/lean.lock \
  lake env lean .claude/reports/blueprint-review/probes/gt-table-pub/SeamBusShape.lean; echo "exit=$?"
# exit=0
flock .claude/reports/blueprint-review/logs/lean.lock \
  lake env lean .claude/reports/blueprint-review/probes/gt-table-pub/SeamBusMember.lean; echo "exit=$?"
# exit=0
```

`SeamBusShape.lean`:

```lean
import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Protocol.Spine.Seams
import LeanerVM.Protocol.Spine.Compose

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Toy CompPoly CPoly

namespace Probe

/-- Columns `[1, 1]`, `[1, 1]`, `[0, 0]`: an honest stack of the toy at statement `0`. -/
def q0 : Column 3 := ⟨#v[1, 1, 1, 1, 0, 0, 0, 0]⟩

#guard M3Holds toy (0 : K) q0

/-- The cubic term `X₂³` at the point `0`, weight one. -/
def cubicTerm : VirtualTerm toy :=
  ⟨1, 0, CMvPolynomial.X 2 * CMvPolynomial.X 2 * CMvPolynomial.X 2, #v[0]⟩

/-- The value of the cubic term on `q0`. -/
def cubicValue : E := cubicTerm.eval q0

-- The claim "the cubic term sums to 0" is true of `q0` ...
#guard cubicValue == 0

def cubicClaim : LinearClaim toy := ⟨[cubicTerm], 0⟩

def cubicSum : E := (cubicClaim.terms.map fun t ↦ t.eval q0).sum

#guard cubicSum == cubicClaim.value

-- ... the public line holds of `q0` at statement `0` (the toy's `aux` is `True`) ...
#guard toy.PublicLinesHold (0 : K) q0

-- ... and the statement is outside the bus seam all the same: only the degree clause fails.
example (o : ∀ i, TheOracle toy i) :
    ((((0 : K), (⟨[cubicClaim], []⟩ : BusOut toy)), o), ()) ∉ Seam.bus toy := fun h ↦
  absurd (h.2.1 _ (List.mem_singleton_self _) _ (List.mem_singleton_self _)) (by decide +kernel)

/-- The toy's constraint at the point `0`. -/
def termAt0 : VirtualTerm toy :=
  ⟨1, 0, CMvPolynomial.X 2 * CMvPolynomial.X 2 - CMvPolynomial.X 2, #v[0]⟩

/-- The same constraint at the point `1`: a different point for the same table. -/
def termAt1 : VirtualTerm toy :=
  ⟨1, 0, CMvPolynomial.X 2 * CMvPolynomial.X 2 - CMvPolynomial.X 2, #v[1]⟩

def v0 : E := termAt0.eval q0
def v1 : E := termAt1.eval q0

#guard v0 == 0
#guard v1 == 0

/-- One linear claim with two terms of the same table at two different points. -/
def twoPoints : LinearClaim toy := ⟨[termAt0, termAt1], 0⟩

def twoPointsSum : E := (twoPoints.terms.map fun t ↦ t.eval q0).sum

#guard twoPointsSum == twoPoints.value

-- The points differ: no single `ζ` has both as its prefix of length `τ = 1`.
#guard termAt0.point.toList ≠ termAt1.point.toList

/-- A thousand copies of a true claim: the seam puts no bound on the number of linear claims,
while the toy has one constraint and one flush. -/
def manyClaims : List (LinearClaim toy) := List.replicate 1000 ⟨[termAt0], 0⟩

#guard manyClaims.length = 1000
#guard (toy.constraints 0).length = 1
#guard (toy.flushes 0).length = 1

end Probe
```

`SeamBusMember.lean` (each clause of the seam on `twoPoints`, as propositions):

```lean
import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Protocol.Spine.Seams

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Toy CompPoly CPoly

namespace Probe

def q0 : Column 3 := ⟨#v[1, 1, 1, 1, 0, 0, 0, 0]⟩

def termAt0 : VirtualTerm toy :=
  ⟨1, 0, CMvPolynomial.X 2 * CMvPolynomial.X 2 - CMvPolynomial.X 2, #v[0]⟩
def termAt1 : VirtualTerm toy :=
  ⟨1, 0, CMvPolynomial.X 2 * CMvPolynomial.X 2 - CMvPolynomial.X 2, #v[1]⟩
def twoPoints : LinearClaim toy := ⟨[termAt0, termAt1], 0⟩

instance (q : Column toy.μ) (c : LinearClaim toy) : Decidable (c.Holds q) :=
  inferInstanceAs (Decidable (_ = _))

-- Every clause of the seam, evaluated.
#guard twoPoints.Holds q0
#guard ∀ t ∈ twoPoints.terms, t.poly.totalDegree ≤ toy.d
#guard toy.PublicLinesHold (0 : K) q0

end Probe
```

What the probes establish: the membership facts. What they do not: that a verifier accepts.
That step is the argument of E.1, on paper, since no table phase is built.

## 10. Not verified, and what would verify it

| Claim | Status | What would verify it |
| --- | --- | --- |
| The Rust and Python verifiers behave as read | read, not run | running both on a dumped proof and on the mutations of B.1, B.2 |
| The errors of D.2, D.3 and E.3 | paper arguments | Layer 4's sumcheck and the bus phase's `Security`, with the conjunct of D.3 |
| The finding on the sumcheck's tables | a reading of Layer 3's text | `leanIsaInstance`, when built |
| The combined check has error `1/|E|` | paper argument (section 7); one instance tested in the repository | the second phase proposed in section 8 |
| leanISA's tables have the Rust's column order | not checked | comparing `LeanerVM/Arithmetization/Tables/*.lean` with `tables.rs:436-863` |
| leanth's `ZerocheckClaim` pattern, which row *Seams* cites | not read (private, background only) | — |
