# Dossier gt-flock-ring: the BLAKE2s validity phase (Flock) and ring switching

Ground truth at the pin `a386121f`, then the blueprint set against it.
leanerVM `main` at `b435631`; ArkLib pin `dca90385` (read in `.lake/packages/Arklib/`), ArkLib
`origin/main` at `7653a901` (fetched 2026-09-29, 347 commits past the pin).

Paths of the ground truth are relative to `/home/scaraven/Documents/leanEthereum/leanVM`:
specification `doc/leanvm/body/` (written `c-flock:`, `a-ring:`, `03:`, `04:`, `07:`, `08:` for
`c-flock-protocol.tex`, `a-ring-switching.tex`, `03-proving-primitives.tex`,
`04-committing-the-witness.tex`, `07-instruction-tables.tex`, `08-end-to-end-protocol.tex`),
Rust `crates/…`, Python `python-verifier/verifier.py` (written `verifier.py:`). "Blueprint" is
`docs/roadmap/protocol-blueprint.md`, "status" is `docs/roadmap/protocol-status.md`.

Notation: `k_batch` is the log of the number of BLAKE2s compressions (the log-height `τ` of the
`BLAKE2S` table), `k_bool = 14 + k_batch` the number of variables of the bit witness `z`,
`n_flock = k_bool − 6 = 8 + k_batch` the number of variables of the packed witness `q_flock`.

---

## 1. Summary

**Examined.** In full: the specification's Annex C (Flock), Annex A (ring switching), §3, §4,
§7.6, §8.5; the Rust crate `flock` (`hash.rs`, `zerocheck.rs`, `lincheck.rs` to line 1400,
`gf2.rs`, `witness.rs`, `verifier.rs`, `reduction_tests.rs`, the head of
`zerocheck/multilinear.rs` and of `zerocheck/univariate_skip_optimized.rs`), `hash_flock.rs`,
`cpu/mod.rs`, `lean_vm/src/pcs.rs`, `pcs/src/{ring_switch,stack_open,tensor_algebra,pack}.rs`,
`fiat_shamir/src/transcript.rs`, `primitives/src/multilinear.rs`; the Flock, ring-switching,
layout and stacked-opening parts of the Python verifier; the blueprint's Layers 3, 9, 10, 12,
conventions, spine, acceptance tests and boundaries; the status; issue #3 (body and both
comments) and the Flock section of the tracker's hole comment; the spine as built
(`Instance`, `Seams`, `Phase`, `Compose`, `ToArkLib/Component`); ArkLib's `RingSwitching/` at
the pin and on `origin/main`. Three probes were run (section 9).

**Conclusions.**

1. **The three sources agree on the transcript of the phase**, message for message and challenge
   for challenge (section 2). Flock commits nothing of its own: the only oracle is the stack
   `q`; every Flock message is a field element sent in the clear; the verifier queries nothing
   during the phase. The reduction has **one** equality check, the lincheck terminal identity.
   The disagreements found are omissions of the specification (constants, the circuit, the slot
   map, two caps), not contradictions.
2. **The spine's types fit the deployed phase; the blueprint's Layer 9 sketch does not.** The
   deployed Flock verifier reads *no* claim of the pool. The eighteen limb claims are never an
   input of Flock: they stay in the pool and are opened as evaluation claims on `q_flock`
   (strided). Layer 9's `FlockInterface`, with `StmtIn := ColumnClaims` (the eighteen claims)
   and `StmtOut := WeightedClaim`, drops them; with leanVM's verifier it has knowledge-soundness
   error 1.
3. **Perfect completeness of the Flock phase is attainable, and the blueprint misdescribes the
   obstacle.** No verifier takes an inverse. The inverse `(1 + r_eq)⁻¹` is taken by the *Rust
   prover* alone, which at `r_eq = 1` silently emits a proof the verifier rejects (no panic).
   The protocol of the specification, with a prover that sends the true coefficients, is
   perfectly complete. Acceptance test 20 files this under `flockError`, a knowledge-soundness
   error: a category mistake, and the spine has no place for a completeness error at all
   (`Component.Security extends Complete`, which is perfect completeness).
4. **`flockError_le` is right for a fixed committed polynomial**: `(4·k_batch + 163)/|E|` is
   Annex C.7's sum and matches the Rust's parameters term by term; `2^32/|E|` bounds the ring
   switching degree `2^31 + 2^15 + 2^7 + 2^3 + 2 + 1`. The hypothesis of the partially fixed
   zerocheck (the 128 equality weights of the seven fixed coordinates are independent over
   `F_2`) holds for the pinned constants (probe: rank 128).
5. **The auxiliary predicate is well defined only from the Rust.** The specification gives the
   R1CS abstractly (a circuit and the rule that turns it into `A_0, B_0`) and the counts of
   wires, not the BLAKE2s circuit, its wire positions, or the slot of each limb. The predicate
   must also contain the constant-one position: without it the all-zero block satisfies the
   R1CS and "the limb slots compress" is false.
6. **Ring switching in leanVM serves the bit witness only** (`F_2 → K`). Evaluation claims of
   `K`-valued columns at points of `E` need no ring switching: the commitment scheme is an
   inner-product scheme "over `K`, opened over `E`". ArkLib's `RingSwitching/Packing` is a
   different protocol (Diamond–Posen: a carrier message, a batching vector, a relocation
   sumcheck, error `κ/|L|`), with completeness and soundness both admitted at the pin and on
   `origin/main`; no "profile" turns it into leanVM's.
7. **Today a reader of the master theorems trusts everything about Flock**: nothing named
   `FlockInterface`, `FlockWitnessGen`, `limbColumns` or `flockError` exists in Lean, the only
   instance built has `aux := True`, and on it a Flock phase that checks nothing is knowledge
   sound at error zero (probe). Issue #3 records "Flock F0 has not started".

**Findings by severity** (section 8 gives evidence, classification and the proposed change).

| Severity | Finding |
| --- | --- |
| major | The Flock interface of Layer 9 consumes the limb claims and emits one claim; leanVM's Flock reads no claim and the limb claims are opened |
| major | The slot map of the limb columns is placed inside the Flock interface, so the instance and the interface each need the other |
| major | The Flock phase cannot be written over an abstract instance: the instance gives it only an opaque predicate |
| major | Acceptance test 20 files a completeness failure under a soundness error, and attributes to the protocol an inverse that only the Rust prover takes |
| minor | Knowledge soundness is bundled with perfect completeness |
| minor | The auxiliary predicate must include the constant-one position |
| minor | Flock is listed as written from the specification; its circuit, layout and constants exist only in the Rust and the Python |
| minor | The Flock error quoted in acceptance test 23 leaves out ring switching |
| minor | The ledger row on ring switching suggests a missing profile; ArkLib's construction is another protocol |
| minor | The status file's finding that the Python verifier omits the caps is false at the pin |
| minor | The executable verifier needs the Flock phase's definition, which no roadmap has started |
| note | The pinned Rust prover of Flock is not perfectly complete |
| note | The error for a fixed committed polynomial is not the error after compilation (list size) |
| note | The Fiat–Shamir seed binds a constant that cannot be recomputed at the pin |
| note | Stale comments in the Rust on what binds the counter and the flags |
| note | A weighted claim carries the 2^μ cube values of its weight |

No finding is critical: no Lean theorem about Flock exists yet that could be wrong or vacuous.
The four major findings are all in text that the Flock roadmap will build from.

---

## 2. Section A: the transcript, as deployed

### 2.1 What is committed

Nothing in this phase. The bit witness `z` was committed in the commit phase, packed 64 bits to a
`K` element, as the region `q_flock` of the one stack `q`.

| | Specification | Rust | Python |
| --- | --- | --- | --- |
| `z` is packed into `q_flock`, a region of the stack | `c-flock:30` "The resulting multilinear $\qflock$ … is committed as one region of the stack"; `08:60` | `hash_flock.rs:3-5` "committed as a column in leanVM's ONE stacked `F64` witness …, with no separate flock commitment"; `cpu/layout.rs:25` `QFLOCK = 5` | `verifier.py:633`, `:879-880` |
| Packing: bit `i` of word `u` is `z(i, u)`, coefficient of `x^i` | `a-ring:13-16` `q_flock(u) = Σ_i Q_i(u) x^i` | `pcs/src/pack.rs:1-2` "least significant bit first"; `hash_flock.rs:187-197` | (verifier only) |
| No other oracle, no other commitment | `c-flock:264` "the PCS proves the claims opened on $\qflock$" | `flock/src/lib.rs:6-13`; `cpu/mod.rs:564-571` | `verifier.py:1404-1413` |

The vectors `a = A z` and `b = B z` are never committed and never opened: only `z` is
(`c-flock:18`, `hash.rs:592-593` "No c buffer. Since `C = I`, `c == z`").

### 2.2 The messages, in order

`P →` is a prover message, `V →` a verifier challenge, `V:` a verifier computation. All values
are in `E`. Counts are per proof.

| # | Step | Specification | Rust (verifier unless said) | Python |
| --- | --- | --- | --- | --- |
| 1 | `V:` seven fixed coordinates `r_0..r_6` = `φ_8(0xf7), φ_8(0x53), φ_8(0xb5), g_0^{2^j}/(1+g_0^{2^j})`, `j<4` | `c-flock:54` (value of `g_0` not given: "where $g_0\in\E$ is public") | `zerocheck.rs:51-58`; `univariate_skip_optimized.rs:65, 79-101`; `g_0` at `:104-106` | `verifier.py:1095-1100` |
| 2 | `V →` `n_flock − 7 = k_batch + 1` coordinates `r_7..`, before any Flock message | `c-flock:55`, `:173` | `zerocheck.rs:362` `equality_tail(m, \|n\| vs.sample_vec(n))` | `verifier.py:1139` |
| 3 | `P →` `P` on the coset `H' = φ_8(64..127)`: 64 values | `c-flock:62` "The prover sends $P\|_{\skipcoset}$, $64$ values" | `zerocheck.rs:365` (prover `:185-187`) | `verifier.py:1142` |
| 4 | `V →` `z_skip` | `c-flock:64` | `zerocheck.rs:366` | `verifier.py:1143` |
| 5 | `V:` `v_P`, the value at `z_skip` of the interpolant of the 64 received values and **64 assumed zeros** on `H`; no check | `c-flock:62-67` | `zerocheck.rs:378`; `zerocheck/multilinear.rs:129-138` | `verifier.py:1144` |
| 6 | `n_flock` rounds. `P →` two coefficients `c_1, c_2` of the quadratic cofactor `G_i`; `V:` `c_0 := claim + r_i·(c_1 + c_2)`; `V →` `χ_i`; `V:` `claim := G_i(χ_i)`. Low variable first. No check | `c-flock:69` ("with Gruen's eq-factor optimization"); `03:110` | `zerocheck.rs:397-405`; `fiat_shamir/src/transcript.rs:289-309` (prover `zerocheck.rs:116-123`) | `verifier.py:1147`, `:406-413`, `:420-427` |
| 7 | `P →` `v_a, v_b`; `V:` `v_c := R_zc + v_a·v_b` (never sent, never checked) | `c-flock:69-73` "is what *defines* $v_c$: both sides solve it rather than transmit it" | `zerocheck.rs:421-423` | `verifier.py:1148-1149` |
| 8 | `V →` `α_lc`; `V:` target `v_a + α v_b + α² v_c + α³` | `c-flock:112-118` | `lincheck.rs:1179`, `:1199-1203` | `verifier.py:1155`, `:1162` |
| 9 | 8 rounds. `P →` two coefficients `c_0, c_2` of the quadratic; `V:` `c_1 := claim + c_2`; `V →` challenge; high variable first, so the point `χ'_in` is the challenges reversed | `c-flock:122` | `lincheck.rs:1205-1211`, `:1218-1219` (prover `:1085-1107`) | `verifier.py:1163`, `:1169` |
| 10 | `P →` `s_0..s_63`, claimed `s_i = z̃(i, χ'_in, χ_out)` | `c-flock:124` | `lincheck.rs:1214` (prover `:1113-1115`) | `verifier.py:1168` |
| 11 | `V:` **check** the terminal identity `R_lc = e_row^T (A_0 + α B_0) w_col + α²·eq(χ_in, χ'_in)·Σ_i ϖ_i(z_skip) s_i + α³·eq(χ'_in, 8)·s_0`; reject otherwise | `c-flock:126-133`, `:150` | `lincheck.rs:1233-1256`, error `ConsistencyFailed`, surfaced as `CpuError::Blake2s` at `cpu/mod.rs:765`; the matrix term is `hash.rs:361-389` (`bilinear_walk`) | `verifier.py:1170-1176` `require(terminal == r_lc, …)`; matrix term `:1180-1301` |
| 12 | `V →` six challenges `f_0..f_5` (ring switching) | `a-ring:104`; `08:91` | `stack_open.rs:513`; `ring_switch.rs:160-162` | `verifier.py:1343` |
| 13 | `V:` target `T = Σ_i x^i Φ(s_i)`; the weight is `W(u) = Φ(eq(r, u))` on the `q_flock` region, `r = (χ'_in, χ_out)`. No message, no check | `a-ring:44-46`, `:104-110` | `stack_open.rs:521-524`; `ring_switch.rs:555-557` (through the transposed columns, `tensor_algebra.rs:42-71`, and `build_coordinate_weights`, `ring_switch.rs:133-144`) | `verifier.py:1345-1347` |
| 14 | (opening) `V →` `λ`; the ring-switched claim takes `λ^0`, the pooled claims the next powers | `08:98` | `stack_open.rs:518-527` | `verifier.py:1361`, `:1413` |
| 15 | (opening, last step) `V:` evaluates `W̃` at the final point `r'` | `a-ring:150-154`: `Σ_k c_k ∏_n (1 + r_n^{2^k} + r'_n)` | `stack_open.rs:530-546`; `ring_switch.rs:597-617` (`eval_rs_eq`, the tensor-algebra algorithm of Diamond–Posen) | `verifier.py:1324-1335`, `:1412` (the closed form) |

Counts, checked against `reduction_tests.rs:166-168` and by the probe of section 9.3: the
reduction (steps 3 to 10) puts `64 + 2·n_flock + 2 + 16 + 64 = 162 + 2·k_batch` scalars on the
stream (168 at `k_batch = 3`); steps 2 to 12 draw `(k_batch + 1) + 1 + n_flock + 1 + 8 + 6 =
2·k_batch + 25` challenges.

Steps 12 and 13 are "BLAKE2s validity, step 2" in the specification (`08:91`) and the first
lines of the opening function in the Rust (`open_batch_mixed_whir_stacked`,
`verify_opening_batch_mixed_whir_stacked`). The transcript position is the same.

### 2.3 Values derived, never transmitted

`v_P` (step 5); `c_0` of each of the `n_flock` zerocheck rounds (step 6); `v_c` (step 7); the
lincheck target (step 8); `c_1` of each of the 8 lincheck rounds (step 9); `T` (step 13). The
`s_i` are sent once, by the lincheck, and reused by ring switching
(`stack_open.rs:113-116` "this layer reads nothing off the stream").

### 2.4 The eighteen limb claims

They are produced by the table sumcheck, routed to the opening, and never seen by Flock.

| | Specification | Rust | Python |
| --- | --- | --- | --- |
| The table sumcheck sends one value per column of every table, the eighteen limb columns included | `08:77` "The prover sends one value per column of every table" | `cpu/mod.rs:428-441` (`for c in 0..table.n_committed_columns()`, 37 for `BLAKE2S`, `tables.rs:866-868`, `:862`) | `verifier.py:620` (`table.width`), `:827-834` |
| A limb claim at `z` becomes a claim on `q_flock` with the low 8 coordinates frozen to the slot | `08:77` "their claims route there"; `07:122`. The selector is **not described** (§4.1 has aligned blocks only, `04:10-18`) | `cpu/mod.rs:790-814` `SlotClaim::Strided { offset, slot, stride_log: SLOT_STRIDE_LOG, point, value }`; `stack_open.rs:84-97`, `:305-323`; `hash_flock.rs:223` (`= 14 − 6 = 8`) | `verifier.py:884-894` `Placement(kappa, offsets[QFLOCK] + limbs[column], QFLOCK_SLOT_BITS)`; `:295-302` |
| Slot of each limb | not given | `hash_flock.rs:87-115`: `cv` 0..3, `out` 4..7, message 10..17, metadata 18, 19 | `verifier.py:847-850` (same) |
| The Flock verifier takes no claim | `c-flock:170-179` (the summary has no input claim) | `cpu/mod.rs:765` `verify_reduction(n_blocks, &mut vs)`; `hash_flock.rs:282-284` | `verifier.py:1405` `verify_flock(log_n, transcript)` |
| The limb claims enter the opening batch with every other pooled claim | `08:97-99` | `cpu/mod.rs:756, 768` (`slots`), `stack_open.rs:525-527` | `verifier.py:1395, 1413` |

### 2.5 What leaves the phase

One family of 64 slice claims at one point, turned by ring switching into **one weighted claim**
`⟨W, q⟩ = T` whose weight is supported on the `q_flock` region (lifted to the stack by the
region's selector: `stack_open.rs:41-48`, `verifier.py:1412`), plus the pool unchanged.

### 2.6 Disagreements between the three sources

None on a message, a challenge, an order or a formula. I checked in particular: the order of
binding of the round coefficients (`transcript.rs:293-307` reads then binds in index order,
`verifier.py:409-413` binds as it reads: the same sequence); the index of the constant position
(`512 = 0 + 8·64`, so `s_0·eq(χ'_in, 8)`: `c-flock:131`, `lincheck.rs:1240` with
`hash.rs:146`, `verifier.py:1174` with `:642`); the row and column weight layouts
(`lincheck.rs:832-837, 1234`, `verifier.py:1159, 1170`); the two circuit walks line by line
(`hash.rs:295-359` with `gf2.rs:109-154` against `verifier.py:1180-1295`; offsets 0, 61, 92, 153
in both); the ring switching stages and coefficients (`a-ring:104-117`,
`ring_switch.rs:85, 147-156`, `verifier.py:1314-1321, 1345`); the two forms of the target
(`Σ_w Φ(b_w)·t_w` in the Rust, `Σ_i x^i Φ(s_i)` in the specification and the Python: equal by
`F_2`-linearity, and the Rust tests it, `ring_switch.rs:683-705`).

The differences are all of one kind: **the specification is silent where the two verifiers
agree**. They are collected in the finding "Flock is listed as written from the
specification…" (section 8.7).

---

## 3. Section B: the checks, enumerated

The phase has one equality check and a set of derivations that replace checks. A Lean verifier
that receives what the deployed one derives must check it; each row says what a verifier
without it would accept.

| Check | Specification | Rust | Python | Protects | Accepted without it |
| --- | --- | --- | --- | --- | --- |
| **Lincheck terminal identity** (step 11) | `c-flock:126-133`; `:270` "it is the only thing that checks anything" | `lincheck.rs:1252-1256` | `verifier.py:1176` | Everything upstream: `v_a, v_b, v_c` are the values of `a, b, z` at the point; the constant position; the link between the `s_i` and the matrices | Any `q_flock`. The prover commits limb slots with a wrong digest and zeros elsewhere, sends arbitrary messages at steps 3, 6, 7, 9 and the **true** `s_i`; ring switching and the opening accept, since the `s_i` are true of `q` |
| **Zeros assumed on `H`** (step 5): the verifier interpolates with 64 zeros, it does not receive them | `c-flock:62` | `multilinear.rs:133-137` | `verifier.py:1144` | This is where `a·b + c = 0` is imposed | If the 64 values on `H` were read from the prover: the prover sends the true `P` of a witness violating the R1CS; every later step is honest and passes |
| **`c_0` derived** in each zerocheck round (step 6), equivalently the round check `c_0 + r_i(c_1 + c_2) = claim` | `03:110`, `c-flock:69` | `transcript.rs:296-302` | `verifier.py:411-413` | The chain from `v_P` to `R_zc` | With `c_0` free: the prover ignores `v_P`, runs an honest sumcheck of the true (nonzero) sum, ends at true `v_a, v_b, v_c` |
| **`v_c` derived** (step 7), equivalently the check `R_zc = v_a v_b + v_c` | `c-flock:70-73` | `zerocheck.rs:423` | `verifier.py:1149` | The link between the zerocheck and the lincheck | With `v_c` sent and unchecked: true `v_a, v_b, v_c` of a violating witness pass the lincheck; the zerocheck constrains nothing |
| **The `α³` term** in the target (step 8) and in the terminal identity (step 11) | `c-flock:23-28`, `:112-118`, `:131` | `lincheck.rs:1202, 1240` | `verifier.py:1162, 1174` | `z(512, t) = 1` for every compression | The all-zero block: every row of the R1CS is homogeneous, so `z_t = 0` satisfies it (`hash.rs:1176-1183` "homogeneous rows accept zero without the pin"). The limb slots are then zero: the statement "the compression of the zero input under the zero chaining value is zero" is accepted |
| **`c_1` derived** in each lincheck round (step 9), equivalently `c_1 + c_2 = claim` | `03:110` | `transcript.rs:298-299` | `verifier.py:409-410` | The chain from the target to `R_lc` | With `c_1` free: the prover runs the sumcheck of the true inner product of a wrong witness; the target is never compared |
| **`T` computed by the verifier** from the `s_i` (step 13) | `a-ring:45` | `stack_open.rs:522-524` | `verifier.py:1346` | The `s_i` are the slices of the committed `q_flock` | With `T` sent: the terminal identity is one linear equation in 64 unknowns; the prover picks `s` satisfying it for any witness and sends the true `⟨W, q⟩` |
| **The weighted claim enters the batch** (step 14) | `08:98-99` | `stack_open.rs:522-524` | `verifier.py:1413` | the same | the same |
| **The limb claims enter the batch** as claims on `q_flock` | `08:77, 97` | `cpu/mod.rs:798-806`, `stack_open.rs:525-527` | `verifier.py:892, 1413` | The limbs the bus used are the words Flock proved | A `q_flock` of valid but unrelated compressions, and limb values chosen to balance the memory bus: a forged digest in memory |
| **The size floor** `τ_BLAKE2S ≥ 3` and the cap `≤ 32` | cap only, `06-bus-interactions.tex:80`; **the floor is absent** | `cpu/mod.rs:161-166` | `verifier.py:860-861` | The layout: `q_flock` has at least `2^3` blocks (`hash.rs:283-286`), and the limb columns share its instance cube | Nothing unsound is known: the mathematics needs no floor (the zerocheck needs `k_bool ≥ 13`, `zerocheck.rs:354`, always true). A Lean verifier without it accepts size announcements the deployed ones reject |
| **The stream is consumed** | `08:100` (implicit) | `cpu/mod.rs:769` | `verifier.py:1414` | No trailing data | Malleable proofs |
| Shape checks inside the reduction | none | `lincheck.rs:1151-1176`, `zerocheck.rs:354-356` | none | Internal consistency; they cannot fail on the deployed path (`hash.rs:990-1008` passes constants) | nothing |

Not a run-time check, and load-bearing: **the seven fixed coordinates have `F_2`-independent
equality weights** (`03:95-100`, used at `c-flock:278`). The Rust asserts it in a unit test
(`univariate_skip_optimized.rs:920-960`); the probe of section 9.3 recomputes it with the Python
field: rank 128.

---

## 4. Section C: completeness at the exceptional challenge

### 4.1 What happens at `r_eq = 1`

**The verifiers take no inverse.** Both derive the untransmitted coefficient by a
multiplication:

```rust
// crates/fiat_shamir/src/transcript.rs:297-302
        coeffs[fixed] = match eq {
            // `c1 + … + cd = claim`, summing the transmitted ones from `c2`.
            None => claim + sum_from(2),
            // `c0 + r·(c1 + … + cd) = claim`, and every `ci` above `c0` was read.
            Some(r) => claim + r * sum_from(1),
        };
```

(`verifier.py:411-413` is the same.) The Lagrange weights of the univariate skip divide by a
constant only (`primitives/src/multilinear.rs:181-186, 194-213`). I searched every `.inv()` of
`crates/{flock,pcs,lean_vm,fiat_shamir}/src` and `primitives/src/multilinear.rs`: the only one
whose argument depends on a challenge is the prover's, below. The others are constants
(`univariate_skip_optimized.rs:96-99, 114`, `multilinear.rs:185, 237`), domain points
(`pcs/src/ntt.rs:50`, `whir_induce.rs:112`), witness generation (`tables.rs:795, 984`,
`cpu/execute.rs`) or tests.

**The Rust prover takes one**, to avoid computing `G(0)`:

```rust
// crates/flock/src/zerocheck.rs:116-123
fn send_round(ps: &mut impl Transmitter, claim: F192, r_eq: F192, g1: F192, g_inf: F192, chis: &mut Vec<F192>) -> F192 {
    let g0 = (claim + r_eq * g1) * (F192::ONE + r_eq).inv();
    ps.add_round_poly(&[g0, g0 + g1 + g_inf, g_inf], true);
    let chi = ps.sample();
    chis.push(chi);
    // G(X) = G(0)·(1+X) + G(1)·X + G(inf)·X·(1+X).
    g0 + chi * (g0 + g1 + (F192::ONE + chi) * g_inf)
}
```

and the inverse of zero is zero, by contract: `gf2_64x3.rs:137` "Multiplicative inverse:
`self^(2^192 − 2)`. `ZERO.inv() == ZERO`."

At `r_eq = 1` the true claim is `(1 + 1)·G(0) + 1·G(1) = G(1)`: it carries no information on
`G(0)`. The prover computes `g0 = (G(1) + G(1))·0 = 0`, sends `c_1 = G(1) + G(∞)` (wrong unless
`G(0) = 0`) and the right `c_2`. The verifier derives `c_0 = claim + c_1 + c_2 = 0`. Prover and
verifier hold the same next claim, and it is not `G(χ)`; it differs by `G(0)·(1 + χ)`. The
error propagates through the remaining rounds into the derived `v_c`. The lincheck prover then
starts from the true inner product (`lincheck.rs:1090`
`let mut running = inner_product_ext(&comb_vec, &z_vec)`), the verifier from the target built on
the wrong `v_c`; the two running claims differ by `α²·δ·∏ r_t ≠ 0` at the end, and the terminal
identity fails.

| Question | Answer |
| --- | --- |
| Does the honest prover fail? | The Rust prover does: it emits a proof that does not verify. It does not notice |
| Does the verifier reject, panic, or accept? | It rejects, at the lincheck terminal identity (`CpuError::Blake2s(Lincheck(ConsistencyFailed))`). No panic on either side |
| Which challenges? | The `k_batch + 1` sampled equality coordinates `r_7, …` only. The seven fixed ones are not 1 (probe 9.3), so rounds 0 to 6 are safe |
| Probability | at most `(k_batch + 1)/|E| ≤ 33/2^192`, times the chance that `G(0) ≠ 0` |
| Is it the protocol's? | No. A prover that sends the true `c_1, c_2` is accepted at `r_eq = 1`: the verifier's `c_0 = claim + r(c_1 + c_2)` is then the true `G(0)` for every `r`. The specification never mentions an inverse (`c-flock:69`, `03:110`) |

This is derived by reading, and confirmed on a model of the two formulas over the pinned Python
field (probe 9.2: at `r_eq = 1` the Rust formulas give the true next claim in 0 cases of 200,
the true coefficients in 200 of 200). It was **not** executed in Rust: the challenge comes from
the Fiat–Shamir chain and cannot be set, and adding a test to the pinned checkout is outside the
rules of this review. What would verify it: a unit test calling `send_round` with
`r_eq = F192::ONE` and `next_round_poly` on its output.

### 4.2 The spine's hypothesis

ArkLib states completeness of a reduction (an honest prover and a verifier, with input and
output relations) with an error, and *perfect* completeness as error zero:

```lean
-- .lake/packages/Arklib/ArkLib/OracleReduction/Security/Basic.lean:101-104 (ArkLib dca90385)
/-- A reduction satisfies **perfect completeness** if it satisfies completeness with error `0`. -/
def perfectCompleteness (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) : Prop :=
  completeness init impl relIn relOut reduction 0
```

The spine packages a phase as a `Component.Def` (the reduction, its schedule, its error per
challenge), a `Component.Complete` and a `Component.Security`:

```lean
-- LeanerVM/Protocol/ToArkLib/Component.lean:76-85
structure Complete (D : Def StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut)) where
  /-- The prover's final output makes no oracle query. -/
  outputPure : D.red.prover.OutputIsPure
  /-- The verifier is a Boolean check followed by a pure verdict. -/
  guarded : D.red.toReduction.verifier.GuardedForm
  /-- Perfect completeness. -/
  complete : ∀ {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)),
    D.red.perfectCompleteness init impl relIn relOut
```

```lean
-- LeanerVM/Protocol/ToArkLib/Component.lean:90-93
structure Security (D : Def StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    extends Complete D relIn relOut where
```

```lean
-- LeanerVM/Protocol/Spine/Compose.lean:101-102 and 120-121
  flock : Phase.Complete I P.flock (Seam.pub I) (Seam.flock I)
  flock : Phase.Security I P.flock (Seam.pub I) (Seam.flock I)
```

Three consequences.

1. **The deployed phase can meet the hypothesis**, provided its Lean honest prover is the
   mathematical one (it sends the coefficients of the true round polynomial). Its verifier is
   the deployed verifier unchanged. So `piop_perfectCompleteness` is not vacuous for the real
   protocol.
2. **A Lean prover transcribed from `send_round` cannot meet it.** Issue #3 plans for exactly
   that reading: "check exceptional challenges, including leanVM's `(1+r_eq)⁻¹` at `r_eq=1`; do
   not silently change sampling", and gate F4 "its exceptional-challenge completeness
   conditions". With such a prover `Phase.Complete … P.flock …` is false, `Phases.Complete` and
   `Phases.Security` have no inhabitant, and **both** master theorems are vacuous for leanVM,
   the knowledge-soundness one included, since `Security extends Complete`.
3. **"Inside `flockError`" is a category mistake.** `flockError` is the `err` of the phase, the
   probability per challenge that the knowledge state goes from false to true
   (`Component.lean:65-66` "The knowledge error charged to each challenge"). A failure of the
   honest prover is not a soundness event; no bound on `err` says anything about it, and the
   spine's `Complete` has no error to put it in.

### 4.3 The options

| Option | Cost | Verdict |
| --- | --- | --- |
| Keep perfect completeness; the Flock phase's honest prover sends the true coefficients; record the Rust prover's defect as a finding against the source | none in the spine | **Recommended.** It is the specification's protocol. The deviation is from the Rust *prover*, not from any verifier, so `verify` still accepts Rust proofs |
| Give `Component.Complete` an error and sum it | ArkLib proves the composition at the pin: `OracleReduction.append_completeness_of_guarded_verifiers` gives `ε₁ + ε₂` (`Composition/Sequential/OracleCompleteness.lean:39-53`, no `sorry` in the file) | Available if #3 insists on the deployed prover. It makes every phase carry a number that is zero for all but one |
| A verifier that samples again | changes the transcript | Rejected: no deployed verifier does it |
| A statement restricted to non-exceptional challenges | a side condition in the master theorem | Unnecessary: the verifier has no exceptional challenge |

---

## 5. Section D: the blueprint's interface set against the ground truth

### 5.1 Which interface to keep, and whether the deployed phase fits

The blueprint gives two. Layer 9 (blueprint `:1075-1086`):

```lean
structure FlockInterface (I : M3Instance) where
  reduction : OracleReduction []ₒ (StmtIn := ColumnClaims) (OStmtIn := fun _ : Unit ↦ Column μ) Unit
      (StmtOut := WeightedClaim) (OStmtOut := fun _ : Unit ↦ Column μ) Unit pSpecFlock
  limbColumns : Column μ → Fin 18 → Column (s.τ 5)      -- the limbs: strided slots of q_flock
  relIn : Set _   -- the eighteen column claims are true of `limbColumns`, and aux (Flock's R1CS)
  relOut : Set _  -- the weighted claim holds for q
```

and the spine, as built:

```lean
-- LeanerVM/Protocol/Spine/Seams.lean:146-151
/-- What the Flock phase hands on: the claim pool the opening phase batches. -/
structure FlockOut (I : M3Instance) where
  /-- The column claims, to be weighted through the layout. -/
  columns : List (ColumnClaim I)
  /-- The weighted claims, ring switched. -/
  weighted : List (WeightedClaim I)
```

```lean
-- LeanerVM/Protocol/Spine/Seams.lean:183-188
/-- After the public-input phase: every column claim holds, and the auxiliary predicate. -/
def pub := of I fun (s : I.Stmt × PubOut I) q ↦ (∀ c ∈ s.2.columns, c.Holds q) ∧ I.aux q

/-- After the Flock phase: every pooled claim holds. -/
def flock := of I fun (s : I.Stmt × FlockOut I) q ↦
  (∀ c ∈ s.2.columns, c.Holds q) ∧ ∀ c ∈ s.2.weighted, c.Holds q
```

**Keep the spine's.** Against the deployed phase (section 2.4):

| Question | Deployed | Spine | Layer 9 |
| --- | --- | --- | --- |
| Input statement | the size `k_batch`; **no claim** is read | the whole pool, which the verifier may ignore | the eighteen limb claims |
| Are claims consumed? | none: the pool is kept as it is | `FlockOut.columns` can be the input's | the eighteen claims vanish |
| Output | the pool, and one weighted claim | `columns` and `weighted` | one weighted claim |
| Knowledge soundness | false input claim ⇒ false output claim (it is handed on); `¬aux` ⇒ the weighted claim is false except with the error | provable | **not provable**: take `q` with a valid `q_flock` and limb claims with wrong values; `relIn` fails, the deployed verifier never reads the claims, the honest transcript is accepted and `relOut` holds: error 1 |

A reduction of Layer 9's shape could be made sound only by folding the eighteen claims into the
weighted claim with a fresh challenge, which leanVM does not do. The tracker repeats Layer 9's
reading (hole comment, section P6: "`FlockInterface.relIn` carries the strong `aux` … and the
eighteen column claims are true of `limbColumns`").

The single weighted claim is `⟨W, q⟩ = T` with `T = Σ_{i<64} x^i·Φ(s_i)` and
`W(x_lo, x_hi) = eq(sel_{q_flock}, x_hi)·Φ(eq((χ'_in, χ_out), x_lo))`.

Two remarks on the fit.

- The spine's `Layout` (`Instance.lean:73-81`) has a reading law and no stacking law, so it
  admits a column read from the *low* index of another; the limb columns can be ordinary
  columns of the instance. Layer 1 has only the high-index selection
  (`ToCompPoly/Multilinear.lean:342` `evalMle_append_boolVec`; its docstring, `:50-51`:
  "slicing on the low index is a different, strided selection"). The low-index identity is a
  generic lemma still to be written, with nothing of Flock in it.
- The Flock verifier queries nothing, has one check followed by a pure verdict, and its prover's
  output is pure: the two side fields of `Component.Complete` are met.

### 5.2 The numbers of `flockError_le`

Derived, for a fixed committed `q`. Annex C.7 (`c-flock:280-284`) sums
`16 + 3 + k_batch + (n_flock − 7) + 127 + 2·n_flock = 4·k_batch + 163` with
`n_flock = 8 + k_batch`. Term by term, with the challenge that pays for it:

| Term | Source | Rust parameter | Charged to |
| --- | --- | --- | --- |
| `n_flock − 7 = k_batch + 1` | partially fixed zerocheck, `03:95-100`, `c-flock:278` | `N_INNER = 7`, `zerocheck.rs:48`; `K_SKIP = 6`, `:47`; `K_LOG = 14`, `hash.rs:105` | the sampled coordinates of `r`, `1/|E|` each |
| `127` | two polynomials of degree below 128 agree at `z_skip`, `c-flock:278` | 128 nodes, `multilinear.rs:132-137` | `z_skip` |
| `2·n_flock` | quadratic cofactor, `n_flock` rounds | `next_round_poly(3, …)`, `zerocheck.rs:399-401` | `χ_i`, `2/|E|` each |
| `k_batch` | the constant position at a random `χ_out`, `c-flock:274` | `Z_CONST_POS = 512`, `hash.rs:146` | the last `k_batch` of the `χ_i`, `1/|E|` more each |
| `3` | degree three in `α_lc`, `c-flock:272-274` | `lincheck.rs:1199-1202` | `α_lc` |
| `16` | 8 quadratic rounds, `c-flock:270` | `K_LOG − K_SKIP = 8`, `hash.rs:992` | the lincheck challenges, `2/|E|` each |
| `< 2^32` | `a-ring:120-128` | `RING_SWITCH_SOUNDNESS_DEGREE = 2^31 + 2^15 + 2^7 + 2^3 + 2 + 1`, `ring_switch.rs:80-81` | `f_p`, `2^{2^{5−p} − 1}/|E|` each: `2^31, 2^15, 2^7, 8, 2, 1` |

The largest single term is `2^31/|E|`, on `f_0`. The bound needs three facts that are
obligations of the Flock roadmap and appear nowhere in the blueprint: the `F_2`-independence of
the 128 fixed weights (true: probe 9.3); that `x` has 64 distinct conjugates over `F_2` and that
`1, y^{2^k}, y^{2^{k+1}}` is a `K`-basis of `E` (`a-ring:80-96`); that the 64 coefficients `c_k`
are distinct monomials (`a-ring:118`; tested in the Rust, `ring_switch.rs:711-760`).

Two cautions: acceptance test 23 quotes a different number (finding 8.8), and after compilation
the error is multiplied by a list size (finding 8.13).

### 5.3 The auxiliary predicate

**Is it well defined from the specification?** Partly.

| Ingredient | In the specification | Where it is fixed |
| --- | --- | --- |
| The R1CS `a(u)b(u) + c(u) = 0`, `A = I ⊗ A_0`, `B = I ⊗ B_0`, `C = I` | yes, `c-flock:8-21` | |
| The constant position: `z(512, t) = 1` for every `t` | yes, `c-flock:23-28` | |
| How a circuit gives `A_0, B_0` | yes, `c-flock:187-218` (Definition of a circuit; the row sets `S^A_w, S^B_w`) | |
| **The BLAKE2s circuit**: the wires, their order, the adders, the position of each committed wire | **no**: only the counts, `c-flock:150` ("896 free inputs, the constant, 256 committed ⊕ wires …, and 14,720 ∧ wires") | `hash.rs:40-64` (layout), `:295-359` (`forward_walk`), `gf2.rs:109-154` (the two adders), `hash.rs:139-162`; mirrored in `verifier.py:1180-1295` |
| The bits and their packing | yes, `c-flock:30`, `a-ring:13-16` | |
| **The slot of each of the eighteen limbs** | **no** (`07:120` names the limbs) | `hash_flock.rs:82-115`; `verifier.py:845-850` |
| `k_batch = τ_BLAKE2S` | implicit | `cpu/mod.rs:721, 763`; `verifier.py:1405` |

The counts agree with the Rust: `896 = 256 + 512 + 128` (`hash.rs:43-51`),
`14,720 = 80 × 184` (`hash.rs:123, 129`).

**What the predicate must say.** For every `t < 2^{k_batch}`, writing `z_t` for the `2^14` bits
of block `t` read from the `2^8` words `q_flock[t·2^8 + w]`, bit `i` of word `w` being
`z_t(64w + i)`:

```text
(∀ k < 2^14, ⟨A_0(k,·), z_t⟩ · ⟨B_0(k,·), z_t⟩ = z_t(k))   ∧   z_t(512) = 1
```

The second conjunct is not optional (section 3, the `α³` row). The blueprint and the docstring
of the field say only "Flock's R1CS holds" (finding 8.6).

**The limb slots and the wires.** A limb is one packed word: limb slot `w` of compression `t` is
the `K` element `q_flock[t·2^8 + w]`, its 64 bits the wires `64w .. 64w + 63` of block `t`
(`hash_flock.rs:119-126`: a 64-bit limb is two little-endian 32-bit BLAKE2s words). The chaining
value is wires 0..255, the output 256..511, the constant 512, the message 640..1151, the counter
1152..1215, the two flags 1216..1279, and the 14,720 products 1280..15999 (`hash.rs:43-53`).

**Can the phase's knowledge soundness return it?** Yes. The witness of a phase is trivial and
the oracle is the stack, so "returning `aux`" is a statement about the committed `q`: if `aux q`
fails, the weighted claim is false except with the error. That is Annex C.7 and Annex A.3 read
forwards. `aux` is decidable (a finite check), as the spine requires.

**Is "`aux` ⇒ the limb slots compress" a theorem to expect?** Yes. It is the functional
correctness of a circuit with 14,720 AND gates: a ripple-carry adder
(`gf2.rs:102-122`), a fused three-operand adder (`gf2.rs:124-154`), eighty `G` functions, the
finalization. It needs: the circuit as a Lean definition (a transcription of `forward_walk`);
leanISA's `compress` (Layer 1); one lemma per adder; the constant position, to turn the
homogeneous rows `a·z(512) = z` of the free inputs and of the output into `a = z`. Its converse,
for completeness, is the correctness of the witness generator
(`hash.rs:594-684`). Once both are proved the *definition* of `aux` leaves the trusted surface:
soundness concludes with `compress`, completeness starts from it. What remains is fidelity of
the matrices to the deployed verifier, which only a Rust-produced proof accepted by `verify` can
test.

### 5.4 How the limb columns are read

The blueprint's Layer 3 (`:841-848`): "a claim on a limb column at `z` is the claim on `q_flock`
at the point whose low eight coordinates are frozen to the slot's bits and whose high
coordinates are `z`". **Verified**, in the Rust and the Python (section 2.4): the full point is
`(slot bits, z, selector of q_flock)`,

```rust
// crates/pcs/src/stack_open.rs:305-323
        StackClaim::Strided {
            offset,
            slot,
            stride_log,
            point,
            ..
        } => {
            let mut e = F192::ONE;
            for (k, &xi) in x[..*stride_log].iter().enumerate() {
                e *= if (slot >> k) & 1 == 1 { xi } else { F192::ONE + xi };
            }
            let block_vars = stride_log + point.len();
            e *= eq_eval(point, &x[*stride_log..block_vars]);
            let sel = offset >> block_vars;
            for (k, &xi) in x[block_vars..].iter().enumerate() {
                e *= if (sel >> k) & 1 == 1 { xi } else { F192::ONE + xi };
            }
            e
        }
```

with `stride_log = 8` and `point` of length `τ_BLAKE2S`. The specification states the routing
(`08:77`) and not the selector.

### 5.5 What the Flock verifier needs that is not in `M3Instance`

| Public datum | Used for | In the blueprint |
| --- | --- | --- |
| The circuit (`A_0, B_0` through the forward walk) | the matrix term of the terminal identity | "evaluated natively inside `verify` through … `settleFixedClaims`" (`:1235-1236`); no owner for the transcription |
| Which column of the instance is `q_flock`, and `k_batch` | the ring switching point and selector; the number of rounds | **nowhere**: `aux` is an opaque predicate (finding 8.3) |
| `φ_8`: the images of the polynomial basis of `F_2[x]/(x^8+x^4+x^3+x+1)` in `K` | the nodes of the univariate skip | not mentioned. `phi8_tower.rs:15-24`, `verifier.py:1092` |
| `0xf7, 0x53, 0xb5` and `g_0` | the fixed coordinates | `g_0` is "#3's to transcribe" (`:1447-1448`) |
| `R1CS_DIGEST` | the Fiat–Shamir seed | convention *Fiat–Shamir* (`:325`); no owner |
| The floor `τ_BLAKE2S ≥ 3` | the caps | `minLogRowsBlake2s` (`:217`), tested (`:867`) |

None of these belongs in `M3Instance`, except the second. The constants are Category B
(transcribed), and belong in `LeanerVM/Parameters/`.

---

## 6. Section E: ring switching

**What Annex A proves.** A reduction from 64 claims `s_i = Q̃_i(r)`, one per bit polynomial, at
one point `r ∈ E^{n_flock}`, to one weighted claim on the packed polynomial:
`Σ_u Φ(eq(r, u))·q_flock(u) = Σ_i x^i Φ(s_i)`, for a random `F_2`-linear map `Φ : E → E` built
from six challenges by `a_{p+1} = a_p + f_p·a_p^{2^{2^{5−p}}}` (`a-ring:30-47, 104-110`).
Completeness is the identity `a-ring:33-41`. Soundness: a nonzero error leaves a nonzero
polynomial of total degree below `2^32` in `f_0..f_5`, so the error is below `2^32/2^192 =
2^{-160}` (`a-ring:120-128`). It gives the closed form of the weight's extension
(`a-ring:150-154`).

**What the Rust does.** The same reduction with the same six stages
(`ring_switch.rs:85, 147-156`). It computes the target on the transposed view
(`Σ_w Φ(b_w)·t_w`, `ring_switch.rs:555-557`) and the weight's extension by the tensor-algebra
recursion of Diamond–Posen (`ring_switch.rs:597-617`) where the specification and the Python use
the Frobenius closed form. The values are equal. No message, no check.

**Whom it serves.** The `q_flock` bit witness only.

- `04:26-28`: "Committing to booleans via Ring-Switching".
- `a-ring:4`: "transforming a PCS for $\K$ into a PCS for $\Ftwo$".
- `stack_open.rs:9-19` distinguishes "point claims … plain multilinear evaluations" from
  "ring-switched claims … bit-MLE evaluation claims on the packed sub-block `q_flock`".
- `cpu/mod.rs:767` builds one ring-switched claim; `stack_open.rs:490` asserts at least one.

**The two fields, and the bridge.** The committed polynomial is over `K = GF(2^64)`; the opening
points, weights and targets are in `E = GF(2^192)`. The bridge for ordinary claims is the
commitment scheme itself, not ring switching:

- `03:117`: "The commitment is over $\K$, the opening over $\E$. An evaluation claim
  $\mle{g}(r)=c$ is the case $W=\eq(r,\cdot)$".
- `b-polynomial-commitment-scheme.tex:125`: "At level $0$ that summand pairs an $\E$-valued
  weight with the $\K$-valued $f$; every later level is $\E$ throughout."
- `lean_vm/src/pcs.rs:24-26`: "The base-field commitment only shrinks the level-0 symbols to 8
  bytes; every random ingredient is sampled from `E`".

This is what the blueprint's oracle models: `evalOracle` answers `eval₂Mle q (algebraMap K E)`
at a point of `E^μ` (blueprint `:638-642`). No finding.

**ArkLib.** `RingSwitchingProfile` is ArkLib's data for a *packing* ring switch: a small ring
`B`, a large ring `L` free of rank `2^κ` over `B` with a basis, and a carrier ring `A` with two
embeddings of `L`, in which the checks are computed:

```lean
-- .lake/packages/Arklib/ArkLib/ProofSystem/RingSwitching/Packing/Profile.lean:91-102 (dca90385)
structure RingSwitchingProfile (B L : Type*) (κ : ℕ)
    [CommRing B] [CommRing L] [Algebra B L] where
  /-- rank-`2^κ` `B`-basis of `L`. -/
  basis : Basis (Fin κ → Fin 2) B L
  /-- pack/trace carrier; Binius `L ⊗[K] L`, Hachi `R_q` (`= L`). The batching wire type. -/
  A : Type*
  [commRingA : CommRing A]
  [algLA : Algebra L A]
  /-- column embedding `L → A`; Binius `α ↦ α ⊗ 1`, Hachi `id`. -/
  φ₀ : L →+* A
  /-- row embedding `L → A`; Binius `α ↦ 1 ⊗ α`, Hachi the automorphism `σ₋₁`. -/
  φ₁ : L →+* A
```

The protocol built on it is Diamond–Posen's: the prover sends a carrier element, the verifier a
batching vector in `L^κ`, then `ℓ'` rounds of a relocation sumcheck, then an evaluation claim
handed to a multilinear commitment scheme over `L` (`Packing/Spec.lean:56-66, 97-101`,
`Packing/General.lean:16-34`); the batching error is `κ/|L|`
(`Packing/BatchingPhase.lean:246-253`).

| | ArkLib `Packing` | leanVM |
| --- | --- | --- |
| Rings | one large ring `L` for packing and opening, rank `2^κ` over `B` | packing ring `K` (rank 64 over `F_2`), opening field `E` (rank 192 over `F_2`, 3 over `K`): "rectangular" |
| Carrier | `L ⊗_B L`, sent by the prover | `K ⊗_{F_2} E`; its element is the 64 `s_i`, already sent by the lincheck |
| Batching | a vector of `κ` challenges, error `κ/|L|` | a linear map from six challenges, error `< 2^32/|E|` |
| After batching | a relocation sumcheck, then an evaluation claim | nothing: the weighted claim goes to the inner-product scheme |
| Proofs | admitted | none in Lean |

At the pin the `Packing` files hold 14 `sorry`: `BatchingPhase.lean` 4 (lines 329, 331, 347,
370: the knowledge state function, `batchingReduction_perfectCompleteness`,
`batchingOracleVerifier_rbrKnowledgeSoundness`), `SumcheckPhase.lean` 8, `General.lean` 2 (lines
222, 226, inside `fullOracleVerifier_rbrKnowledgeSoundness`). On `origin/main` (`7653a901`) the
counts per file are the same; the two commits to the folder since the pin are #894 and #896 (the
coordinate repair). Nothing named Flock or built on Frobenius maps exists under
`ArkLib/ProofSystem` on `origin/main` (`git grep`). ArkLib #383 and #893 are open
(`gh`, 2026-09-29).

**What the blueprint assumes.** That ring switching is inside the Flock interface and ends in
one weighted claim, at `2^32/|E|`: faithful. Its ledger row (`:267`) reads as if a profile were
the missing piece (finding 8.9).

---

## 7. Section F: ownership and trust

### 7.1 What a reader of the master theorems trusts about Flock today

As built, the master theorems are over an abstract instance and conditional on `Phases.Complete`
and `Phases.Security`. Nothing of Flock exists in Lean beyond the field `aux`, the structure
`FlockOut` and the seam `Seam.flock`:
`grep -rn "FlockInterface\|FlockWitnessGen\|limbColumns\|flockError" LeanerVM/ tests/` returns
nothing.

| # | Trusted | Why | Discharged by (issue #3's gates) |
| --- | --- | --- | --- |
| 1 | That the leanISA instance's `aux` is the R1CS with the constant position, on the bits of `q_flock` | `leanIsaInstance` does not exist; the one instance built has `aux := fun _ ↦ True` (`Spine/Toy.lean:110`) | the adaptor (hole I2) with F2 "Preserve the constant-one wire" and F8 "leanVM lane: exact BLAKE2s compression" |
| 2 | "`aux` ⇒ every `BLAKE2S` row compresses" (`Blake2sRowsValid`, `Arithmetization/Statement.lean:301-302`) | the adaptor's `satisfiedBy_witnessOf` needs it | F2 "Prove both directions of R1CS lowering", F8, F9 "both directions of the hash-call/trace linkage" |
| 3 | The witness generator and its correctness | `stackOf`, `m3Holds_stackOf` | F2 "pure witness-generator correctness", F8 |
| 4 | The Flock phase's definition: schedule, prover, verifier, circuit walk | `Phases.flock` | F3, F4, F5; F2 "forward/transpose circuit-walk equivalence" |
| 5 | Its perfect completeness | `Phases.Complete.flock`, and `Phases.Security.flock` through `extends` | F3, F4 (see section 4: the prover must not be the Rust's) |
| 6 | Its round-by-round knowledge soundness and the bound | `Phases.Security.flock`, `flockError_le` | F3 (baseline), F4 (skip, fixed weights), F5 (ring switching, "leanVM's rectangular/Frobenius instance its own contracts and parameter proof") |
| 7 | The independence of the 128 fixed weights | the bound | F1 "pinned equality-weight certificate" |
| 8 | The constants `φ_8`, `0xf7, 0x53, 0xb5`, `g_0`, `R1CS_DIGEST`, the slot map | fidelity to the deployed verifier | F0, F1; no owner for `R1CS_DIGEST` and the slot map |

Issue #3, status of 2026-09-16: "**Flock F0 has not started.**" and "All F0–F9 implementation
gates below are open."

### 7.2 Could a check be dropped without a theorem failing?

**Today, every check of the phase.** The probe of section 9.1 builds, on the toy instance, a
Flock phase with no message, no challenge and no check, and proves
`Phase.Security toy noCheckFlock (Seam.pub toy) (Seam.flock toy)` from the kernel's three axioms
only. That is what an opaque `aux` permits: the master theorems constrain the Flock verifier
exactly as much as the instance's predicate does.

**Once the holes are filled**, the protection is a chain of two theorems, and each check is
caught by one of them:

| Check dropped | Caught by | Condition |
| --- | --- | --- |
| The terminal identity, a derivation of section 3, the computation of `T` | `Phase.Security.flock`: unprovable against an `aux` that is the R1CS | the adaptor's `satisfiedBy_witnessOf` is proved, which forces `aux` to be at least that strong |
| The `α³` term | If `aux` omits the constant position the phase is provable without the term, and `satisfiedBy_witnessOf` fails on the all-zero block. If `aux` has it, `Phase.Security.flock` fails | the adaptor is proved |
| The limb claims in the batch | the table sumcheck's and the opening's `Security`, through the seams | the limb columns are columns of the instance |
| The weighted claim in the batch | the opening's `Security` from `Seam.flock` | |
| The floor `τ_BLAKE2S ≥ 3` | **no theorem.** Only the test of Layer 3 (blueprint `:867`) | |
| `R1CS_DIGEST` in the seed | **no theorem.** Only a Rust-produced proof accepted by `verify` | the fixture exists |

So the requirement "a missing check leaves a master theorem unprovable" holds for this phase
**if and only if** the adaptor's soundness theorem is proved without an assumption on `aux`.
Until then the final statements take a Flock structure as an argument
(`verify_knowledgeSound (fs) (bcs) (mca) (flock)`, blueprint `:1226`), and a conditional theorem
whose hypothesis has no inhabitant says nothing; the repository's own rule is "Give load-bearing
configuration and certificate types concrete inhabitants" (`AGENTS.md`).

---

## 8. Findings

### 8.1 The Flock interface of Layer 9 consumes the limb claims and emits one claim; leanVM's Flock reads no claim and the limb claims are opened

**Severity: major.** Evidence: sections 2.4 and 5.1. **Classification: an error of the
blueprint**, to be fixed; the spine is faithful, Layer 9 and the tracker's section P6 are not.

Passage as it stands (blueprint `:1075-1092`): the structure quoted in section 5.1, and
"`relIn` carries the strong auxiliary predicate of Layer 3 … `limbColumns` is the strided
reader of Layer 3".

Passage as proposed (a sketch in the blueprint's style, not compiled):

```lean
/-- What the Flock roadmap supplies: the phase at the spine's seams, for an instance that says
where the packed witness is (`FlockRegion`, Layer 3). -/
structure FlockPhase (I : M3Instance) (R : FlockRegion I) where
  phase : Phase.Def I (I.Stmt × PubOut I) (I.Stmt × FlockOut I)
  security : Phase.Security I phase (Seam.pub I) (Seam.flock I)   -- completeness included
  err_le : ∑ i, phase.err i ≤ (4 * R.kBatch + 163) / |E| + 2 ^ 32 / |E|
```

with the text: "The verifier reads no claim of the pool. It hands the column claims on
unchanged, the eighteen limb claims among them (`cpu/mod.rs:790-814`: they are opened as
evaluation claims on `q_flock`), and adds one weighted claim, the ring-switched one. The
schedule is: `k_batch + 1` challenges; 64 values; one challenge; `8 + k_batch` rounds of two
values and one challenge; two values; one challenge; 8 rounds of two values and one challenge;
64 values; six challenges." Reason: soundness of the sketch as written fails with error 1.

### 8.2 The slot map of the limb columns is placed inside the Flock interface, so the instance and the interface each need the other

**Severity: major** (cannot be stated as written). Evidence: blueprint `:846-848`
"`leanIsaInstance.layout` combines the two, the slot map being #3's
`FlockInterface.limbColumns` (Layer 9)", and `:1077` `structure FlockInterface (I : M3Instance)`.
The instance's `layout` field needs a value of a structure that takes the instance as its
parameter. The slot map is eighteen numbers (`hash_flock.rs:96-115`) and a generic identity on
multilinear tables. **Classification: an error of the blueprint.**

Proposed: (a) `blake2sLimbSlot : Fin 18 → Fin 256` in `LeanerVM/Parameters/` (Category B:
`hash_flock.rs:87-115`, cross-checked with `verifier.py:847-850`); (b) the low-index selection
identity next to `evalMle_append_boolVec` in `ToCompPoly/Multilinear.lean`, generic (a table of
`m + k` variables evaluated at `boolVec j ++ z` is its low-index slice evaluated at `z`); (c)
Layer 3 builds the strided reader from the two; (d) `limbColumns` is deleted from Layer 9 and
from the tracker's sections I2 and P6. The boundary paragraph with leanISA (`:1439-1441`)
becomes "reconciled by the instance's layout".

### 8.3 The Flock phase cannot be written over an abstract instance: the instance gives it only an opaque predicate

**Severity: major** (cannot be stated as written). Evidence:

```lean
-- LeanerVM/Protocol/Spine/Instance.lean:143-148
  /-- What the Flock phase proves of the committed region it owns, beyond the polynomial
  checks: the statement its honest prover can convince the verifier of, so it names the
  committed witness (Flock's R1CS on `q_flock`), never only a consequence of it. -/
  aux : Column μ → Prop
  /-- The auxiliary predicate is decidable, so that the relation is. -/
  decAux : DecidablePred aux
```

Layer 9 is "module, over `I`" (blueprint `:1072`), and convention *The wall* (`:331`) lists the
modules allowed to know leanISA; the Flock phase is not among them. But a phase that knows only
`I.aux : Column μ → Prop` cannot name the column, the number of compressions or the relation it
is to prove; the sketch itself reaches for `s.τ 5`, a leanISA size. For an abstract `I` the only
phases one can write are those of the probe. **Classification: an error of the blueprint**
(a design gap the spine left open).

Proposed (sketch): Layer 3 supplies, and Layer 9 takes,

```lean
/-- Where the packed witness of the BLAKE2s circuit sits, and what `aux` says of it. -/
structure FlockRegion (I : M3Instance) where
  col : I.ColumnId                        -- the column q_flock
  kBatch : ℕ                              -- log₂ of the number of compressions
  height : I.κ col = 8 + kBatch           -- 2^8 packed words per compression, low coordinates
  aux_iff : ∀ q, I.aux q ↔ Flock.Holds kBatch (I.column q col)   -- R1CS and constant position
```

`Flock.Holds` is the Flock roadmap's predicate on a packed column and mentions no instance. The
toy keeps `aux := True` and has no `FlockRegion`. The wall stands: the phase imports nothing
from the arithmetization.

### 8.4 Acceptance test 20 files a completeness failure under a soundness error, and attributes to the protocol an inverse that only the Rust prover takes

**Severity: major.** Evidence: section 4. **Classification: an error of the blueprint.**

Passage as it stands (blueprint `:1323-1325`):

> 20. **Perfect completeness needs no exceptional-challenge clause** in Layers 4–8 and 10: no
> inverse of a challenge is taken. Flock's `(1 + r_eq)⁻¹` at `r_eq = 1` is #3's, inside
> `flockError`. Witness: `piop_perfectCompleteness` has no side condition on challenges.

Passage as proposed:

> 20. **Perfect completeness needs no exceptional-challenge clause, in any phase.** No verifier
> takes the inverse of a challenge: the untransmitted coefficient of a round polynomial is
> `claim + r·(c_1 + … + c_d)` (`transcript.rs:296-302`). Every honest prover, Flock's included,
> sends the coefficients of the true round polynomial. The pinned Rust prover of Flock does
> not: it derives `G(0) = (claim + r·G(1))·(1 + r)⁻¹` (`zerocheck.rs:116-118`), and at `r = 1`
> emits a proof its verifier rejects. That is a completeness defect of the implementation, of
> probability at most `(k_batch + 1)/|E|`; it is recorded in `docs/leanvm-target.md` and is no
> part of `flockError`, a knowledge-soundness error. Witness: `Phase.Complete` is perfect
> completeness; the Flock phase's test runs the round at `r = 1` with `G(0) ≠ 0`, accepted for
> the true coefficients and rejected for the derived ones.

The same sentence must reach issue #3, whose text plans "exceptional-challenge completeness
conditions" (draft for the tracker only; nothing was posted).

### 8.5 Knowledge soundness is bundled with perfect completeness

**Severity: minor** (avoidable coupling; it is what turns 8.4 into a threat to the soundness
theorem). Evidence: `Component.lean:90-93` (`Security … extends Complete`); the composition uses
only the guard of the first verifier:

```lean
-- LeanerVM/Protocol/ToArkLib/Component.lean:182-184
  rbr := fun init impl ↦ rbrKnowledgeSoundnessWorstCaseWith_of_eq _
    (Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first S₁.guarded
      (S₁.kSF init impl) (S₂.kSF init impl) (S₁.rbr init impl) (S₂.rbr init impl))
```

**Classification: a deliberate deviation** of the spine from ArkLib's separate statements, whose
reason (one structure per hole) does not need the coupling. Proposed: a structure
`Component.Guarded` with `outputPure` and `guarded`; `Complete` and `Security` both extend it;
`piop_rbrKnowledgeSoundness` then holds for a protocol whose completeness is unproved or
imperfect. Convention *Holes* (`:332`) changes from "`X.Security` (perfect completeness, and
round-by-round knowledge soundness …)" to "`X.Security` (the guard, and round-by-round knowledge
soundness …)".

### 8.6 The auxiliary predicate must include the constant-one position

**Severity: minor** (imprecise wording on a load-bearing definition). Evidence: `c-flock:23-28`
"We also enforce the position $512$ of every block to be $1$ (preventing the all-zero witness)";
`hash.rs:1172-1183`; against blueprint `:850-851` "`aux q` says that Flock's R1CS holds of the
bits packed into the `q_flock` region", status `:239-240`, `Instance.lean:24-25, 143-145`. Read
literally, `aux` holds of the zero region and the lemma "`aux` ⇒ the limb slots compress" is
false. **Classification: an error of the blueprint** (of wording).

Proposed, everywhere the phrase occurs: "`aux q` says that, for every compression, the bits
packed into the `q_flock` region satisfy Flock's R1CS **and hold 1 at the constant position
512** (Annex C.1, equations (flock:eq:r1cs) and (flock:eq:const-one))". Add to the acceptance
tests: "**The constant position is part of the predicate.** The zero block satisfies the R1CS
and is no compression. Witness: `aux` fails on the zero region."

### 8.7 Flock is listed as written from the specification; its circuit, layout and constants exist only in the Rust and the Python

**Severity: minor.** Evidence: blueprint `:192` "Flock | A, owned by #3 | specification Annex C;
`crates/flock/src/`". What the specification does not contain, with the place that fixes it:

| Missing from the specification | Fixed by |
| --- | --- |
| The BLAKE2s circuit and the position of each wire | `hash.rs:40-64, 139-162, 295-359`; `gf2.rs:23-31, 109-154`; `verifier.py:1180-1295` |
| The slot of each limb | `hash_flock.rs:87-115`; `verifier.py:847-850` |
| The selector of a limb claim (a low-index selection; §4.1 has aligned blocks only) | `stack_open.rs:84-97`; `verifier.py:288-302` |
| `g_0` ("is public", `c-flock:54`) | `univariate_skip_optimized.rs:104-106`; `verifier.py:1095` |
| `φ_8`: which of the eight embeddings, and the modulus of `F_{2^8}` (`c-flock:35`) | `gf2_8.rs:13`; `phi8_tower.rs:15-24`; `verifier.py:1092` |
| `k_batch = τ_BLAKE2S` | `cpu/mod.rs:721, 763`; `verifier.py:1405` |
| The floor `τ_BLAKE2S ≥ 3` (`06-bus-interactions.tex:80` has the caps only) | `cpu/mod.rs:162-166`; `hash.rs:283-286`; `verifier.py:861` |
| The wording "live in $\qflock$, not the stack" (`08:77`): `q_flock` is a region of the stack | `cpu/layout.rs:17-25` |

**Classification: a deviation forced by the source** (the specification is incomplete); the
blueprint follows the Rust, rightly, and should say so. Proposed row: "Flock: protocol and
errors | A, owned by #3 | specification Annex A, Annex C" and a second row "Flock: the BLAKE2s
circuit, wire positions, limb slots, `φ_8`, the fixed coordinates, `R1CS_DIGEST` | B |
`crates/flock/src/{hash,gf2}.rs`, `zerocheck/univariate_skip_optimized.rs:65, 104-106`,
`primitives/src/field/phi8_tower.rs:15-24`, `lean_vm/src/hash_flock.rs:87-115`;
`verifier.py:847-850, 1092-1100, 1180-1295`". Each omission is a line for
`docs/leanvm-target.md` and for a report to leanVM (drafted here only).

### 8.8 The Flock error quoted in acceptance test 23 leaves out ring switching

**Severity: minor.** Blueprint `:1331-1332`: "`Σ piopError < 2^{-150}` plus Flock's
`< 2^{-183}`". `2^{-183}` is `(4·k_batch + 163)/|E|` alone (`c-flock:282`); `flockError_le`
(`:1085`) adds `2^32/|E| = 2^{-160}`, which dominates by a factor `2^23`. Proposed: "plus the
Flock phase's, below `2^{-183} + 2^{-160}`, the second term being ring switching's". The
convention *Errors* wants the closed form next to the theorem: give `flockError` per challenge
as in the table of section 5.2.

### 8.9 The ledger row on ring switching suggests a missing profile; ArkLib's construction is another protocol

**Severity: minor.** Blueprint `:267`: "A9 ring switching packing leaves | `RingSwitching/Packing`
leaves are `sorry`, and no `GF(2) → GF(2^64)` profile". Evidence: section 6. With every leaf
proved and a profile for `F_2 ⊂ K`, ArkLib's reduction would still send a carrier element, run a
relocation sumcheck, have the point in `K` and the error `κ/|L|`. **Classification: an error of
the blueprint** (of description). Proposed row: "A9 ring switching | ArkLib's `Packing` is
Diamond–Posen's interactive reduction (carrier message, batching vector, relocation sumcheck),
14 `sorry` at the pin and on `main`; leanVM's is rectangular (`K ⊗ E`), batches by a linear map
from six challenges and hands a weighted claim to the commitment scheme | Layer 9 | New work of
#3 (its gate F5); at most the tensor algebra is shared".

### 8.10 The status file's finding that the Python verifier omits the caps is false at the pin

**Severity: minor** (stale text; it asks for a report upstream that would be wrong). Status
`:316-319`: "F9 the Python verifier omits the caps `log_mem ∈ [16, 32]`, `τ_j ≤ 32`, the
bytecode power-of-two bound and `τ_BLAKE2S ≥ 3` (`verifier.py:1372-1379` …)". At the pin:

```python
# python-verifier/verifier.py:857-864
    log_bytecode = log2_strict(len(bytecode)) - BUS_BITS
    require(
        16 <= log_memory <= 32
        and all(0 <= log_height <= 32 for log_height in table_log_heights)
        and table_log_heights[OP_BLAKE2S] >= 3
        and 0 <= log_bytecode <= 32,
        "invalid announced table sizes",
    )
```

and `log2_strict` requires a power of two (`verifier.py:252-254`). The lines were introduced by
`14fbca8f`, an ancestor of the pin. Proposed: delete the finding from the status. (It touches
this task through the floor on `τ_BLAKE2S`; the other caps belong to another dossier.)

### 8.11 The executable verifier needs the Flock phase's definition, which no roadmap has started

**Severity: minor** (planning). Every proof carries a Flock transcript: the floor is 8
compressions (`hash.rs:283-286`), so the fixture of Layer 12, "a proof dumped from the pinned
Rust prover … accepted by `verify`" (blueprint `:1237-1238`), cannot pass before a Lean Flock
verifier exists, with the circuit walk and the constants. Hole K3 lists "S (schedules, phase
`Def`s)" among what it consumes (`:614`); the Flock `Def` is "the inhabitant is #3's" (`:609`),
and #3's first gate has not started. Proposed: split hole P6 as every other phase is split. The
definition with its completeness (the schedule of finding 8.1, the verifier, the circuit walk
transcribed, the constants in `Parameters`, an honest run on a toy circuit) is a hole that can
be taken now and tested against the Python verifier's walk; the security stays #3's. State in
hole K3 that its fixture waits on it.

### 8.12 The pinned Rust prover of Flock is not perfectly complete

**Severity: note** (a finding against the source, for `docs/leanvm-target.md`). Evidence:
section 4.1, probe 9.2. The Lean honest prover **deliberately deviates** from the Rust prover;
the reason is that the specification's protocol is perfectly complete and the Rust's shortcut is
not; the theorem it owes is `baseProver_complete` for the Lean `prove` (not for the Rust), and
the fixture "a Rust-produced proof is accepted" is unaffected, the verifiers being the same.

### 8.13 The error for a fixed committed polynomial is not the error after compilation

**Severity: note**, for the dossier on the compiled verifier. The commitment is list binding
only (`b-polynomial-commitment-scheme.tex:4`), so `c-flock:264` "The commitment determines
$\qflock$" holds up to a list. The Rust's parameter analysis multiplies the ring switching
degree by the list size: `whir_config.rs:540-541` "A degree-`d` identity test unioned over a
Johnson list of size `L` fails with probability at most `dL/|F|`", and `:564-567`. Annex A's
`2^{-160}` and the blueprint's `flockError` have no such factor, which is right in the ideal
oracle model; `niError` (blueprint `:1234-1235`) must have it, for every challenge of every
phase. Issue #3 names the obligation ("Joint candidate lists").

### 8.14 The Fiat–Shamir seed binds a constant that cannot be recomputed at the pin

**Severity: note** (extends the status's F14). `08:55` says the seed covers "Flock's BLAKE2s
R1CS matrices". The Rust binds `R1CS_DIGEST`, of which `hash.rs:259-275` says: "baked as an
opaque constant … That recipe needed the materialized matrices, which this module no longer
builds … To recompute it, check out the last commit that still had `build_matrices`". The Python
copies the bytes (`verifier.py:629`). The constant is Category B and has no owner in the
blueprint; no theorem depends on its value.

### 8.15 Stale comments in the Rust on what binds the counter and the flags

**Severity: note.** `cpu/mod.rs:568-570` and `:619-621` say "bytecode binds the counter and
flags". The table reads the metadata cell from memory (`tables.rs:904-907` "The metadata rides
the memory bus like every other operand"), as the specification says (`07:120, 135`). No effect
on the protocol; the Lean should cite the table.

### 8.16 A weighted claim carries the 2^μ cube values of its weight

**Severity: note**, for the dossier on the opening. `Weight` (`Seams.lean:103-109`) has the
field `onCube : CMlPolynomialEval E μ`, a vector of `2^μ` elements of `E`. The Flock verifier's
output statement contains one. As a specification this is fine; as a function that runs it
builds a table of `2^μ` values (`μ` up to 28) that no deployed verifier builds
(`ring_switch.rs:63-66`). The field `mle_eq`, for the ring switching weight, is the boxed
identity of `a-ring:150-154`, owed by the Flock roadmap.

---

## 9. Probes

All under `.claude/reports/blueprint-review/probes/gt-flock-ring/`.

### 9.1 `NoCheckFlock.lean`: a Flock phase that checks nothing is knowledge sound when `aux` is trivial

Command, from the repository root:
`flock .claude/reports/blueprint-review/logs/lean.lock lake env lean .claude/reports/blueprint-review/probes/gt-flock-ring/NoCheckFlock.lean`

```lean
import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Protocol.Spine.Compose

namespace GtFlockRingProbe

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Toy CompPoly CPoly OracleComp

/-- A Flock phase that does nothing: the column claims are handed on, no weighted claim. -/
def noCheckFlock : Phase.Def toy (toy.Stmt × PubOut toy) (toy.Stmt × FlockOut toy) :=
  Phase.passThrough toy fun p ↦ (p.1, ⟨p.2.columns, []⟩)

/-- (1) It has the spine's `Phase.Security` from `Seam.pub` to `Seam.flock`. -/
def noCheckFlockSecurity : Phase.Security toy noCheckFlock (Seam.pub toy) (Seam.flock toy) :=
  Phase.passThroughSecurity toy _ (fun _ _ h ↦ ⟨h.1, by simp⟩) (fun _ _ h ↦ ⟨h.1, trivial⟩)

#print axioms noCheckFlockSecurity

/-- Its error is zero at every challenge (there is none). -/
example : noCheckFlock.n = 0 := rfl

/-- The toy with a nontrivial auxiliary predicate: cell 7 of the stack is `1`. -/
abbrev toyAux : M3Instance :=
  { toy with aux := fun q ↦ q.values.get 7 = 1, decAux := fun _ ↦ inferInstance }

/-- (2) For it, "the output seam reflects into the input seam" fails for the do-nothing phase:
the honest toy stack has cell 7 equal to `0`. -/
example : ¬ (∀ (s : toyAux.Stmt × PubOut toyAux) (o : ∀ i, TheOracle toyAux i),
    (((s.1, (⟨s.2.columns, []⟩ : FlockOut toyAux)), o), ()) ∈ Seam.flock toyAux →
      ((s, o), ()) ∈ Seam.pub toyAux) := by
  intro h
  have h' := h ((1 : K), ⟨[]⟩) (fun _ ↦ honest) ⟨by simp, by simp⟩
  have h7 : honest.values.get 7 = 1 := h'.2
  revert h7
  decide +kernel

end GtFlockRingProbe
```

Output (exit status 0):

```text
'GtFlockRingProbe.noCheckFlockSecurity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Part (2) shows only that this route to `Security` closes when `aux` has content; it does not
show that no other proof exists.

### 9.2 `req_one.py`: one zerocheck round at `r_eq = 1`

A model of the two formulas of section 4.1 over the field arithmetic of the pinned Python
verifier, imported read-only. Command: `python3 -B …/probes/gt-flock-ring/req_one.py`.

```python
import importlib.util, random, sys

sys.dont_write_bytecode = True   # the pinned checkout must stay untouched

spec = importlib.util.spec_from_file_location(
    "verifier", "/home/scaraven/Documents/leanEthereum/leanVM/python-verifier/verifier.py")
v = importlib.util.module_from_spec(spec); sys.modules["verifier"] = v; spec.loader.exec_module(v)
E, ONE, ZERO = v.E, v.ONE, v.ZERO

def inv0(x):            # Rust: F192::inv, ZERO.inv() == ZERO
    return x ** (2**192 - 2)

def rnd(rng):
    return E(rng.getrandbits(64), rng.getrandbits(64), rng.getrandbits(64))

def run(r, rng):
    c0, c1, c2 = rnd(rng), rnd(rng), rnd(rng)           # the true cofactor G
    G = lambda x: c0 + c1 * x + c2 * x * x
    g1, ginf = G(ONE), c2
    claim = (ONE + r) * G(ZERO) + r * g1                  # the true incoming claim
    # Rust prover, send_round:
    g0 = (claim + r * g1) * inv0(ONE + r)
    wire = (g0 + g1 + ginf, ginf)                         # c1, c2 as transmitted (c0 is not sent)
    chi = rnd(rng)
    prover_next = g0 + chi * (g0 + g1 + (ONE + chi) * ginf)
    # verifiers, next_round_poly with eq = Some(r): c0 := claim + r (c1 + c2)
    d0 = claim + r * (wire[0] + wire[1])
    verifier_next = v.poly_eval([d0, wire[0], wire[1]], chi)
    # a prover that sends the true coefficients c1, c2 (no inverse):
    e0 = claim + r * (c1 + c2)
    verifier_next_true = v.poly_eval([e0, c1, c2], chi)
    return (prover_next == verifier_next, verifier_next == G(chi), verifier_next_true == G(chi), c0 != ZERO)

rng = random.Random(20260929)
for name, r in (("r_eq random", rnd(rng)), ("r_eq = 1", ONE)):
    out = [run(r, rng) for _ in range(200)]
    print(name,
          "| Rust prover and verifier agree:", all(o[0] for o in out),
          "| their next claim is the true G(chi):", sum(o[1] for o in out), "/ 200",
          "| with the true coefficients sent, the verifier's next claim is G(chi):", sum(o[2] for o in out), "/ 200")
```

Output (exit status 0):

```text
r_eq random | Rust prover and verifier agree: True | their next claim is the true G(chi): 200 / 200 | with the true coefficients sent, the verifier's next claim is G(chi): 200 / 200
r_eq = 1 | Rust prover and verifier agree: True | their next claim is the true G(chi): 0 / 200 | with the true coefficients sent, the verifier's next claim is G(chi): 200 / 200
```

### 9.3 `fixed_weights_rank.py`: the fixed coordinates

Command: `python3 -B …/probes/gt-flock-ring/fixed_weights_rank.py`.

```python
import importlib.util, sys

sys.dont_write_bytecode = True   # the pinned checkout must stay untouched
spec = importlib.util.spec_from_file_location(
    "verifier", "/home/scaraven/Documents/leanEthereum/leanVM/python-verifier/verifier.py")
v = importlib.util.module_from_spec(spec); sys.modules["verifier"] = v; spec.loader.exec_module(v)
E, ONE = v.E, v.ONE

a = list(v.FIXED_CHALLENGES)
assert len(a) == 7
print("fixed coordinates equal to 1:", sum(x == ONE for x in a))
print("fixed coordinates equal to 0:", sum(x == v.ZERO for x in a))

rows = []
for b in range(1 << 7):
    w = ONE
    for i, ai in enumerate(a):
        w = w * (ai if (b >> i) & 1 else ONE + ai)
    rows.append(int(w.c0) | (int(w.c1) << 64) | (int(w.c2) << 128))

rank = 0
basis = []
for r in rows:
    for p in basis:
        r = min(r, r ^ p)
    if r:
        basis.append(r); basis.sort(reverse=True); rank += 1
print("rank over F_2 of the 128 equality weights:", rank)

D = sum(2 ** (s - 1) for s in v.RING_MAP_SHIFTS)
print("ring-switching degree 2^31+2^15+2^7+2^3+2+1 =", D, "< 2^32:", D < 2 ** 32)
for k in (3, 32):
    print(f"k_batch={k}: 4k+163 = {4*k+163}; stream scalars of the reduction = {64 + 2*(8+k) + 2 + 16 + 64}; challenges = {(k+1)+1+(8+k)+1+8+6}")
```

Output (exit status 0):

```text
fixed coordinates equal to 1: 0
fixed coordinates equal to 0: 0
rank over F_2 of the 128 equality weights: 128
ring-switching degree 2^31+2^15+2^7+2^3+2+1 = 2147516555 < 2^32: True
k_batch=3: 4k+163 = 175; stream scalars of the reduction = 168; challenges = 31
k_batch=32: 4k+163 = 291; stream scalars of the reduction = 226; challenges = 89
```

---

## 10. Negative results

Checked, no issue found.

- **The transcript**: fifteen steps, three sources, no disagreement (section 2.6).
- **The blueprint's description of the strided limb claims** (`:841-846`): matches
  `stack_open.rs:84-97, 305-323` and `verifier.py:892, 295-302`.
- **Convention *Claim pool order*** (`:324`): the ring-switched claim first, then the bus
  claims, the table claims, the three public-input claims; matches `cpu/mod.rs:656-667`,
  `stack_open.rs:400-401, 518-527`, `verifier.py:1413`, `08:98`.
- **The Fiat–Shamir seed of the conventions** (`:325`): `"leanvm" ‖ len ‖ R1CS_DIGEST ‖
  bytecodeHash`; matches `cpu/mod.rs:82-93` and `verifier.py:1366-1368`.
- **The strong reading of `aux`** (status decision 12): right. The Flock prover needs the wires
  in `q`; a predicate on the limb slots alone has no honest prover. The docstrings of
  `Instance.lean` now carry the strong reading (`:23-26, 143-145`); the earlier review had left
  that edit open.
- **The order of the phases** `pub ⟫ flock ⟫ opening`: matches `cpu/mod.rs:745-768` and
  `verifier.py:1397-1413`.
- **The numbers `4·k_batch + 163` and `2^32`**: derived (section 5.2).
- **`Blake2sRowsValid`** (`Arithmetization/Statement.lean:301-302`) is what the adaptor must
  reach; with `k_batch = τ_BLAKE2S` and the floor of 8 rows, blocks and rows correspond one to
  one, so there is no padding block to account for in the relation.

## 11. Not verified, and what would verify it

| Statement | Status | What would verify it |
| --- | --- | --- |
| The Rust prover's behaviour at `r_eq = 1` | read, and modelled (probe 9.2); not executed | a Rust unit test on `send_round` and `next_round_poly` |
| `R1CS_DIGEST` is the digest of the matrices | not checked; not recomputable at the pin | the commit the Rust's comment points to |
| The Rust circuit computes BLAKE2s | not checked by me; the Rust tests it (`hash.rs:1121-1170`) | the theorem of section 5.3 |
| `lincheck.rs` beyond line 1400, `zerocheck/multilinear.rs` beyond line 330, `univariate_skip*.rs` beyond line 200 (prover kernels and tests) | not read | none of it is on the verifier's path (`hash.rs:983-1016`) |
| The WHIR part of the opening (what follows `λ`) | out of this task | the dossier on the opening |
| The recursive verifier's hint `M_lc` (`c-flock:152-158`) | out of scope (the blueprint's verifier is the native one) | |
| The three sketches of section 8 (`FlockPhase`, `FlockRegion`, `Component.Guarded`) | proposals, not compiled | writing them |

## 12. Note on the rules of the session

The first run of probe 9.2 imported the pinned `verifier.py` without disabling bytecode, and
Python wrote `python-verifier/__pycache__/verifier.cpython-313.pyc` into the leanVM checkout (a
git-ignored path; no tracked file changed, `git status` stayed clean). I removed that file and
the directory it created, set `sys.dont_write_bytecode` in both Python probes, and ran them
again with `python3 -B`. The checkout is at `a386121f` with no untracked or ignored file left.
