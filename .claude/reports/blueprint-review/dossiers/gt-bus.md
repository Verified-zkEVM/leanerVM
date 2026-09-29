# Dossier `gt-bus`: the setup, the commitment and the bus phase

Ground truth at the pin `a386121f`, then the blueprint and the spine set against it.

Revisions this dossier speaks about: leanVM `a386121f84292f6fa663aaa3e570c15bc0240ea2` (checkout
clean, `git status` empty); leanerVM `main` at `b435631`; ArkLib at the pin `dca90385`
(`.lake/packages/Arklib/`); CompPoly at the pin `3468b38c`. Nothing here is about an upstream
`main`.

Citation shorthand. Specification files are under `doc/leanvm/body/`: `03:` is
`03-proving-primitives.tex`, `04:` is `04-committing-the-witness.tex`, `05:` is
`05-arithmetization.tex`, `06:` is `06-bus-interactions.tex`, `08:` is
`08-end-to-end-protocol.tex`, `B:` is `b-polynomial-commitment-scheme.tex`. Rust files are under
`crates/lean_vm/src/`: `mod.rs` is `cpu/mod.rs`, `layout.rs` is `cpu/layout.rs`; `fs/` is
`crates/fiat_shamir/src/`. `py:` is `python-verifier/verifier.py`. `bp:` is
`docs/roadmap/protocol-blueprint.md`, `st:` is `docs/roadmap/protocol-status.md`, in leanerVM.
The number after the colon is the line.

## Summary

**Examined.** In full: the specification sections 3, 4, 5, 6 and 8 and the round-by-round
definition and theorem of Annex B; the Rust verifier and prover from the seed to the end of the
bus phase (`cpu/mod.rs`, `leaf.rs`, `gkr.rs`, `cpu/layout.rs`, `witness.rs`, `tables.rs`,
`pcs.rs`, `fiat_shamir/src/{lib,transcript,merkle}.rs`); the Python verifier's corresponding
functions; the blueprint (conventions, the spine, Layers 3 to 7 and 10, the acceptance tests);
the status file; the tracker's hole comment; the spine as built (`Instance`, `Seams`, `Phase`,
`Compose`, `Toy`, `ToArkLib/Component`); ArkLib's round-by-round definitions at the pin. Two
probes were run: a Python probe that drives the pinned Python verifier's own GKR function
(message counts, the order of `ζ`, an honest prover written from the specification, a verifier
with one check removed), and a Lean probe on the spine (three instances).

**Conclusions.**

1. The three sources agree on the transcript of the setup, the commitment and the bus phase, up
   to omissions of the specification (it does not mention the announced rate, the `BLAKE2S`
   floor, the stacking window, the canonical encodings, the last unused combiner) and the prose
   order of the two roots. The Rust and the Python verifier accept the same transcripts in these
   phases; no divergence between them was found (section A.6).
2. The real bus phase **can** fill the spine's slot `bus`: its output is expressible as a
   `BusOut I` (five linear claims and five column claims for leanVM), perfect completeness holds,
   and a knowledge state function exists with per-challenge errors `4·2^μ/|E|` on `(α, β)`,
   `2/|E|` on a combiner, `4/|E|` on a sumcheck round, `1/|E|` on a combination challenge. The
   zerocheck escape costs nothing extra: it is a maximum with the GKR's own error on the last
   layer's challenges, not a sum (section D and E.2).
3. It cannot fill it **the way the blueprint says**. Four things in the blueprint are wrong or
   cannot be built as written: the GKR layer sumcheck (degree and error, the verifier's running
   claim); the number of combiners; the generic GKR of Layer 5, whose input oracles are the leaf
   tables, which cannot be appended in a phase whose one oracle is the stack, and whose state
   function cannot carry the zerocheck clause; and the admissibility predicate, which must
   contain the stacking window and the rate window and is equated with a predicate that has
   neither.
4. One finding of the status file is false at the pin: the Python verifier does check the four
   caps the status says it omits (`py:857-864`). It must not be reported upstream.
5. No theorem or definition of the spine as built is wrong or vacuous in what concerns the bus
   (negative result, section E.5). Two edge cases of the abstract instance need a hypothesis the
   spine does not have; leanVM's instance meets both.

**Findings by severity** (full text in section G).

| # | Name | Severity |
| --- | --- | --- |
| G1 | The GKR layer sumcheck is the normalized one: the blueprint gives it the wrong degree, the wrong error and no definition | major |
| G2 | One combiner more than layers: the last is drawn and never used | major |
| G3 | The generic GKR of Layer 5 cannot be appended in the bus phase, and cannot carry the zerocheck clause | major |
| G4 | The admissibility predicate: the stacking window and the rate window | major |
| G5 | The status file's finding on the Python verifier's caps is false | major (of the status) |
| G6 | The zerocheck escape is charged in four different ways, none tight, one to the wrong challenge | minor |
| G7 | The order of the leaf stacks is nowhere stated, and the spine's `tuples` has the opposite order | minor |
| G8 | Orders the blueprint leaves open: the two roots, the boundary evaluations, the linear claims | minor |
| G9 | The canonical-encoding checks and the consumption check are absent from the blueprint | minor |
| G10 | Two side conditions a bus phase over an abstract instance needs | minor |
| G11 | The sketch of Layer 6 and the tracker's bus section are stale, and the invariant they name is not one | minor |
| G12 | The binary layer's combination challenge has no error assigned | minor |
| G13 | The status file's finding on the one bus root misreads the pinned specification | minor |
| G14 | Citation drift | minor |
| G15 | Disagreements between the three sources (seven, none a divergence of the two verifiers) | note |
| G16 | The table phase must know which tables it opens | note |
| G17 | The specification gives no round-by-round analysis of the bus phase | note |

---

## A. The transcript, as deployed

### A.1 Notation and sizes

- `K = GF(2^64)`, `E = GF(2^192)`; every stream element is one element of `E` (24 bytes).
- Announced: `κ_mem` (memory log-size), `τ_0 … τ_5` (log-heights of `XOR, MUL, SET, DEREF, JUMP,
  BLAKE2S`), `ρ` (the rate exponent `log_inv_rate`). Public: the program, of `2^κ_bc`
  instructions, and the public input, two words.
- `μ_stack`: log-size of the committed stack. `μ` (written `μ_bus` where confusion is possible):
  depth of the three leaf trees of the bus, `μ = ⌈log₂ N_push⌉` with
  `N_push = 1 + 2^κ_mem + 2^κ_bc + Σ_j nfl_j · 2^τ_j`, where `nfl = (5, 5, 3, 5, 5, 11)` is the
  number of flush pairs of each table (`tables.rs:483-495, 548-561, 633-643, 731-751, 873-908`).
  For leanVM `17 ≤ μ ≤ 28` (the lower bound from `κ_mem ≥ 16`; the upper from `μ_stack ≤ 28`,
  section D.4).
- The count side has `ncnt = (4, 4, 2, 4, 4, 10)` blocks per table, 28 in all
  (`tables.rs:479-482, 544-547, 629-632, 718-721, 869-872`).

### A.2 Setup and commitment

`P→V` is a prover message (a read of the stream, bound into the Fiat–Shamir state as it is
read, `fs/transcript.rs:283-287`), `V` a verifier computation or check, `V→P` a challenge (one
squeeze of the chain per element of `E`, `fs/lib.rs:95-99`).

| # | Step | Specification | Rust | Python |
| --- | --- | --- | --- | --- |
| S0 | `V`: seed the chain with `compress(iv, public input)`, `iv = BLAKE2s("leanvm" ‖ len ‖ R1CS_DIGEST ‖ bytecode_hash)` | `08:55` "seeded by the public input, the bytecode and Flock's BLAKE2s R1CS matrices"; §8.4 is `TODO` (`08:44-46`) | `mod.rs:82-93`, `mod.rs:712`; `fs/lib.rs:69-73` | `py:1366-1369`, `py:347-351` |
| S1 | `P→V`: 8 elements: `κ_mem`, `τ_0 … τ_5`, `ρ`, each a small integer in the low limb | `08:55` "The prover sends the memory log-size `κ_mem` and the six table log-heights `τ_j`" (no `ρ`) | prover `mod.rs:118-124`; verifier `mod.rs:144-149` | `py:1372-1376` |
| S2 | `V`: each announced element has its two upper limbs zero | absent | `mod.rs:133-135` `if word.c1 != 0 \|\| word.c2 != 0 { return Err(CpuError::PublicInput) }` | `py:1373` |
| S3 | `V`: each public word has its third limb zero | `08:29` "two 192-bit words (with top limb 0)" | `mod.rs:141-143` | by type: the input is a 32-byte `Digest` (`py:204-219`) |
| S4 | `V`: the caps (section B, checks B4 to B9) | `06:80`, `06:86`, `06:90` | `mod.rs:157-170` | `py:857-864`, `py:1377` |
| S5 | `V`: derive the layouts (the stack, the three leaf stacks) | `08:55` "derives the layout of every stack (PCS and GKR leaves)" | `mod.rs:171`, `layout.rs:328-427`, `witness.rs:67-102` | `py:856-895`, `py:506-511` |
| S6 | `V`: the stacking window `15 ≤ μ_stack ≤ 28` | absent | `mod.rs:174-176`; `pcs.rs:49, 51` | `py:1379`; `py:907-908` |
| C1 | `P→V`: the commitment, a Merkle root as 2 elements (two 128-bit halves) | `08:60-61` "sends its commitment" | prover `pcs.rs:118-119`, `mod.rs:560-562`; verifier `mod.rs:714`, `pcs.rs:136-138`, `fs/transcript.rs:97-99` | `py:1382` |
| C2 | `V`: both halves of the root have a zero third limb | absent | `fs/merkle.rs:26-29` (`NonCanonicalEncoding`) | `py:223` |

No challenge is drawn before the root is read (`pcs.rs:93-96` "bind its root into the
transcript, before any challenge is sampled"; the first `sample` is `leaf.rs:876`).

### A.3 The bus phase

| # | Step | Specification | Rust | Python |
| --- | --- | --- | --- | --- |
| U0 | `V`: structural assertions on the leaf layouts (panics, not rejections) | absent | `leaf.rs:875`, `leaf.rs:123-146` | absent |
| U1 | `V→P`: `α_0, α_1, α_2, α_3` then `β`: five squeezes, no message between them | `08:67`; `05:22`, `05:28` | `leaf.rs:876`, `leaf.rs:882` | `py:542`, `py:544` |
| U2 | `P→V`: 2 elements, the bus root `R` then the count root `R_c` | `08:68` "Sends the count root `R_c` and one bus root `R`" (prose order reversed) | prover `gkr.rs:272-276`; verifier `gkr.rs:364-367` | `py:434`, `py:437` |
| U3 | `V→P`: the first combiner `λ` | `05:91` | `gkr.rs:369` | `py:435` |
| U4 | The batched GKR (A.4): messages, challenges and one check per layer | `05:61-95`, `08:69` | `gkr.rs:373-427` | `py:439-455` |
| U5 | `V`: `R_c ≠ 0` (evaluated after the GKR) | `06:78`, `08:69`, `08:100` | `leaf.rs:884-889` (`Error::ZeroCount`) | `py:546` |
| U6 | `P→V`: 5 elements, the evaluations of `mem_0, mem_1, mem_2, cntfin_mem` at `ζ_{<κ_mem}` and of `cntfin_bc` at `ζ_{<κ_bc}`, in that order | `08:70` "For their committed columns the prover sends one evaluation each"; `05:111` | verifier `leaf.rs:909-920`, `leaf.rs:428-439`, `leaf.rs:548-550`; prover `leaf.rs:500-529` | `py:552-557` |
| U7 | `V`: computes, per side, the public part of the leaf claim (selectors, constants, index column, bytecode column, the five evaluations, the padding) and **derives** what the tables owe, `rem_s`; builds the tables' bus forms. No check. | `08:70`; `05:105-123` | `leaf.rs:389-461`, `leaf.rs:921-924` | `py:559-590` |

After U7 the table sumcheck starts with the challenge `ξ` (`mod.rs:726`, `py:1389`). Nothing of
the bus phase is sent after U6.

**Element counts** (checked by the probe of section H.1 against the pinned Python function, for
`μ = 0 … 12`):

| Message | Elements of `E` |
| --- | --- |
| announced sizes | 8 |
| commitment root | 2 |
| roots | 2 |
| GKR | `μ² + 4μ`, plus 1 if `μ` is odd |
| boundary evaluations | 5 |
| **total, seed to end of bus** | `μ² + 4μ + 17` (+1 if `μ` is odd) |

| Challenge | Squeezes |
| --- | --- |
| `α`, `β` | 5 |
| GKR, `μ` even | `μ²/4 + μ + 1` |
| GKR, `μ` odd | `3 + ((μ−1)/2)² + 3(μ−1)/2` |

### A.4 The GKR in full detail

Both verifiers run the same loop (`gkr.rs:358-430`, `py:433-457`). State: the list `values`
of three claimed values (initially `(R, R, R_c)`), the point `point` (initially empty), the
combiner `λ`, the level `layer` (initially `μ`; the root is level `μ`, the leaves level 0).

**Radix and parity.** While `layer > 0`: if `layer` is odd the step is one binary level, else
two levels at once (`gkr.rs:377`, `py:442`). `layer` is odd only at the first iteration, when
`μ` is odd (`gkr.rs:378` `debug_assert_eq!(round_count, 0, "only the root-most layer may be
binary")`). Specification: `05:85`.

**One iteration, radix 4** (`layer` even, `k = μ − layer` rounds):

1. `V`: `claim := values[0] + λ·values[1] + λ²·values[2]` (`gkr.rs:376`, `poly_eval` low degree
   first, `primitives/src/multilinear.rs:245-247`; `py:443`). The three trees, in the order
   push, pull, count, are batched by the powers `1, λ, λ²` (`05:91-94`).
2. `k` sumcheck rounds. Round `t` (`t = 0 … k−1`) uses the coordinate `point[t]` as its
   equality factor:
   - `P→V`: **4 elements**, the coefficients `c_1, c_2, c_3, c_4` of a polynomial `h` of degree 4
     (`gkr.rs:319-326`; read at `gkr.rs:399-401` `next_round_poly(5, claim, Some(equality_point))`;
     `py:445` with `count = 2**step + 1 = 5`).
   - `V`: **derives** `c_0 := claim + point[t]·(c_1 + c_2 + c_3 + c_4)`
     (`fs/transcript.rs:297-302` "`c0 + r·(c1 + … + cd) = claim`, and every `ci` above `c0` was
     read"; `py:411-413`). This is the round identity `(1 + r)·h(0) + r·h(1) = claim` solved for
     `c_0`. **There is no round check to fail**: it holds by construction.
   - `V→P`: `χ_t`; `claim := h(χ_t)` (`gkr.rs:402-404`, `py:424-426`).

   `h` is the **cofactor**: the honest `h_t(Y) = Σ_x eq(point_{>t}, x) · Σ_s λ^s ·
   ∏_{a,b} Ṽ^s_{layer−2}(a, b, χ_{<t}, Y, x)`, without the factor `eq(point[t], Y)` and without
   the factors `eq(point[u], χ_u)` of the earlier rounds. The running claim is the value of the
   cofactor, never multiplied by an equality factor (the "normalized" form of `gkr.rs:4-5`
   "Its normalized eq-trick sumcheck has degree four").
3. `P→V`: **12 elements**, the four children of each tree at the point, tree by tree
   (`gkr.rs:406-409`, `py:447`).
4. `V` **check**: `claim = Σ_s λ^s · ∏_{c<4} children[s][c]`, **with no equality factor**
   (`gkr.rs:410-413` `LayerMismatch`; `py:448-449`).
5. `V→P`: `u_0` then `u_1` (`gkr.rs:414-415`, `py:451`). `values[s] := ` the bilinear
   interpolation of the four children, `u_0` on the low child bit and `u_1` on the high one
   (`gkr.rs:416-422`; `py:452`).
6. `V→P`: a new combiner `λ` (`gkr.rs:423`, `py:453`).
7. `point := (u_0, u_1, χ_0, …, χ_{k−1})` (`gkr.rs:424-425`, `py:454`); `layer := layer − 2`.

**One iteration, binary** (`layer = μ` odd, no round): `P→V` 6 elements, two children per
tree; check `claim = Σ_s λ^s · left_s · right_s`; `V→P` `u`; `values[s] := (1+u)·left_s +
u·right_s`; `V→P` a new `λ`; `point := (u)` (`gkr.rs:377-395`, `py:442-455` with `step = 1`).

**The last combiner is never used.** Step 6 runs in every iteration, the last included, where
`layer` then becomes 0 and the loop ends. So the number of combiners is the number of layers
plus one, and the last squeeze changes the state of the chain before `ξ` is drawn and enters no
computation (`gkr.rs:423` then `gkr.rs:429`; `py:453` then `py:457`). The probe confirms it: at
`μ = 4` the GKR draws 9 challenges and `ζ` is draws 6, 7, 4, 5; draw 8 is unused.

**How `ζ` is assembled.** `ζ` is the `point` after the last iteration (`layer = 2`,
`k = μ − 2`): `ζ = (u_0, u_1, χ_0, …, χ_{μ−3})`. Every coordinate of `ζ` is a challenge of the
**last** layer; no challenge of an earlier layer is a coordinate of `ζ`. In time order the last
layer draws `χ_0, …, χ_{μ−3}` (which become `ζ_2, …, ζ_{μ−1}`), then `u_0 = ζ_0`, then
`u_1 = ζ_1`, then the unused combiner. Coordinate 0 is the lowest bit of the leaf index: the
Rust test `radix_four_roundtrip_at_even_and_odd_depths` (`gkr.rs:479-508`) asserts
`proved.values[lane] == mle_eval_e(&leaves[lane], &proved.point)` with `mle_eval_e` folding
`point[0]` over adjacent pairs (`gkr.rs:436-447`), and the probe checks the same against the
pinned Python. For `μ = 1`, `ζ = (u)`; for `μ = 0` there is no layer and `ζ` is empty.

Table of the probe (H.1): `ζ_k` is the draw of that number, counting the GKR's draws from 0.

| `μ` | `ζ_0, ζ_1, ζ_2, …` | draws |
| --- | --- | --- |
| 2 | 1, 2 | 4 |
| 3 | 4, 5, 3 | 7 |
| 4 | 6, 7, 4, 5 | 9 |
| 5 | 10, 11, 7, 8, 9 | 13 |
| 8 | 22, 23, 16, …, 21 | 25 |

**How the three trees share challenges.** Entirely: one `point`, one sequence of `χ`, one pair
`(u_0, u_1)` per layer; the three are told apart only by the power of `λ`. The count tree is
shallower; it is padded with leaves `1` to the depth of the bus trees (`leaf.rs:879-881`
`count_lay.mu = push_lay.mu`; `py:540`, `py:578-579`, where the selector of a count block is
extended by zero bits to the length of `ζ`).

### A.5 The leaf stacks and the decomposition

**Blocks, in index order** (`layout.rs:349-415`; `py:537-540`, `py:866-876`). Push side: the
state boundary `κ = 0`, `(sep_ST, g⁰, g⁰)`; the memory seed `κ = κ_mem`,
`(sep_MEM, idx, 1, mem_0, mem_1, mem_2)`; the bytecode seed `κ = κ_bc`,
`(sep_BC, idx, 1, P_3, …, P_10)`; then for each table in order each of its pushes, `κ = τ_j`.
Pull side: the state boundary `(sep_ST, g^{2^κ_bc − 1}, g⁰)` (`layout.rs:335, 355-358`); the
memory finalization with `cntfin_mem` in place of `1`; the bytecode finalization with
`cntfin_bc`; then the tables' pulls. Count side: for each table in order, one block per count
column, a single coordinate (`layout.rs:412-414`). **The three blocks no table owns come
first.**

**Placement.** Largest first at aligned offsets, ties by index (`witness.rs:67-79`
`order.sort_by(|&a, &b| kappas[b]….cmp(…).then(a.cmp(&b)))`, called by `leaf.rs:149-156`;
`py:305-311`). `sel_b = offset_b >> κ_b`, its bits low first (`leaf.rs:407-411`; `py:299-302`).
The depth is `⌈log₂ Σ_b 2^κ_b⌉` with **no floor** (`leaf.rs:153`), unlike the witness stack
(`witness.rs:97`).

**Leaves.** Row `z` of block `b` holds `β + Σ_i eq(α, i)·c_{b,i}(z)` (`leaf.rs:226-260`;
characteristic 2), the weights `eq(α, bits of i)`, bit `k` of `i` against `α_k`
(`leaf.rs:89-98`). The count side runs at `α = 0`, `β = 0`, so its leaf is the count cell
(`leaf.rs:606-622`; `py:573`). Padding leaves are `1` (`leaf.rs:222-224`, `gkr.rs:61, 114`).

**Decomposition** (U7). With `ζ_lo = ζ_{<κ_b}`, `ζ_hi = ζ_{≥κ_b}`, `w_b = eq(sel_b, ζ_hi)`:

- a block no table owns contributes `w_b·(β + Σ_i eq(α, i)·v_i)` where `v_i` is the constant,
  the index column's extension `∏_k (1 + ζ_k(1 + g^{2^k}))` (`primitives/src/field/mod.rs:105-113`,
  `py:271-278`; `06:97-100`), the extension of the public bytecode column, or the value the
  prover sent for a committed column (`leaf.rs:440-457`). A committed column already valued at
  the same point is not sent again (`leaf.rs:466-471`), which is why U6 has 5 elements and not 8;
- a block of table `j` contributes nothing to the check: it is accumulated into the form of
  `(side, j)`, coefficient `w_b·eq(α, i)` on coordinate `i` and `w_b·β` on the constant
  (`leaf.rs:416-423`, `leaf.rs:367-382`; `py:582-587`);
- the padding contributes `1 + Σ_b w_b` over all the blocks of the side (`leaf.rs:459-460`;
  `py:589`; `05:107`);
- `rem_s := Ṽ^s_0(ζ) + (public part + padding)` (`leaf.rs:921-924` "What the tables owe this
  side: DERIVED, never read"; `py:590`).

The Rust evaluates the eight bytecode columns one by one (`leaf.rs:453`); the Python evaluates
the stacked bytecode table once at `(ζ_{<κ_bc}, α)` (`py:566`), as `08:70` writes it. The two
are equal when the stacked table is zero outside slots 3 to 10 (see G15, item 6).

### A.6 Disagreements between the three sources

Recorded as finding G15 (seven items). In short: no disagreement between the Rust and the
Python verifier on what is accepted in these phases; the specification is silent on seven
points the verifiers fix, and its prose names the two roots in the other order.

---

## B. The checks, enumerated

"Attack" is a prover or committed witness that the verifier **without** the check accepts and
that lies outside the intended relation. Where the check does not protect soundness this is
said: inventing an attack would be padding.

| # | Check | Specification | Rust | Python | Protects | Attack without it |
| --- | --- | --- | --- | --- | --- | --- |
| B1 | The stream holds every element read (truncation) | absent | `mod.rs:132` (`Transcript`), `gkr.rs:359, 381, 401, 408` (`Truncated`), `leaf.rs:549` (`Truncated`), `fs/transcript.rs:184-188` | `py:363-367` | totality of the verifier | none: a verifier that read past the end would fail to run, not accept |
| B2 | Announced sizes: upper limbs zero | absent | `mod.rs:133-135` | `py:1373` | one encoding per size (the layout uses the low limb only, the chain binds all three) | none on soundness: the same layout and the same statement; `2^128` encodings of each proof. It matters to the recursion guest, which does arithmetic on the sizes |
| B3 | Public words: third limb zero | `08:29` | `mod.rs:141-143` | by type | the seed binds only the two low limbs of each word (`mod.rs:99-106`), so two statements would share one transcript | a proof for the words `(a, b)` replayed for `(a + c·y², b)`: the chain is the same. The public-input phase still rejects it except with probability `1/|E|`, the memory columns being `K`-valued, so this is defence in depth (unverified beyond this argument; the public-input phase is another dossier's) |
| B4 | The program has a power-of-two length, at most `2^32` | `06:90` | `mod.rs:158-159` | `py:857`, `py:862` (`log2_strict`, `0 ≤ log_bytecode ≤ 32`) | the statement's shape; the read bound | see B6 |
| B5 | `16 ≤ κ_mem ≤ 32` | `06:86` | `mod.rs:160`; `mod.rs:51-52` | `py:859` | upper: the read bound; lower: the guest's range checks assume at least `2^16` cells (`mod.rs:45-50`) | upper: see B6. Lower: none on the relation's soundness; a smaller memory makes honest range checks fail |
| B6 | `τ_j ≤ 32` | `06:80` | `mod.rs:161`; `mod.rs:60` | `py:860` | Lemma 6.2 (`06:51-57`): fewer than `2^64 − 1` reads | with `2^64 − 1` reads of one pair `(a, v)` that is no entry of the array, counts `g⁰, g¹, …, g^{2^64−2}`: the pulled counts and the pushed counts `g·c` are the same multiset, every count is nonzero, the bus balances, and the read is wrong. A mathematical counterexample, not a feasible one. Given B9 the three upper caps are implied (`μ_stack ≤ 28` forces `τ_j ≤ 24`, `κ_mem ≤ 26`, `κ_bc ≤ 28`); they are checked first because the layout shifts by them (`witness.rs:76`) |
| B7 | `τ_BLAKE2S ≥ 3` | absent | `mod.rs:162-166` | `py:861` | Flock runs on at least `2^3` instances (`flock/src/hash.rs:283-286`), so its claim is on `2^(3+8)` words, while the block `q_flock` has `2^(τ_5+8)` (`layout.rs:155`) | not constructed. Without the check the ring-switched claim covers a window larger than `q_flock`'s block, overlapping its neighbours in the stack. **Unverified**: a test of a verifier without the cap at `τ_5 = 2` would settle whether a proof is accepted |
| B8 | `1 ≤ ρ ≤ 4` | absent | `mod.rs:167`; `pcs/src/whir_config.rs:44-55` | `py:1377` | the WHIR parameters exist | none here: the opening's parameters are derived from `ρ` |
| B9 | `15 ≤ μ_stack ≤ 28` | absent | `mod.rs:174-176` | `py:1379` | the sizes WHIR is configured and tested for (`pcs.rs:179-188`). The lower bound never fires: `μ_stack` is floored at 15 (`witness.rs:97`, `py:890`) | none here: the opening's |
| B10 | The root's halves have a zero third limb | absent | `fs/merkle.rs:26-29` | `py:223` | one encoding per root | none on soundness |
| B11 | Layout facts, asserted: `push.mu = pull.mu`, `count.mu ≤ push.mu`, at most 16 coordinates, `soundness_bits(μ) ≥ 128` | absent | `leaf.rs:130-145` (`assert!`, a panic) | absent | the verifier's own arithmetic | none: they are functions of the announced sizes and hold for every size that passes B4 to B9 |
| B12 | **One root for both sides** | `08:68-69`, `08:100` "the one bus root for both sides" | structural: one element read into two slots, `gkr.rs:364-367` | structural, `py:434, 437` | balance | with two roots and no comparison: any unbalanced stack. Concretely, an honest stack with one cell of `mem_0` changed at an address that is read: seed and finalization agree with each other, the reads carry the old value |
| B13 | **`R_c ≠ 0`** | `06:78`, `08:69` | `leaf.rs:887-889` | `py:546` | every read count nonzero | a read of any `(a, v)` with count `0`: it pulls `(sep, a, 0, v)` and pushes `(sep, a, g·0, v)`, the same tuple. The bus balances, the honest `R_c` is `0`. The stack has a read of a value no cell holds |
| B14 | **The layer check**, once per layer (`⌈μ/2⌉` checks) | implicit in `05:75, 83` | `gkr.rs:384-386`, `gkr.rs:411-413` (`LayerMismatch`) | `py:449` | the chain from the roots to the leaf claims | run by the probe (H.1): for an unbalanced bus the prover announces any `R`, passes the layers above the unchecked one by solving their one equation for one child, and sends the **true** children at the unchecked layer. The weakened verifier accepts with true leaf claims; the full verifier rejects at that layer |
| B15 | The round identity of the layer sumcheck | `03:79-85`, `03:110` | not a check: `c_0` is derived, `fs/transcript.rs:297-302` | not a check, `py:411-413` | in a protocol that sends all five coefficients, the link between a round and the running claim | in such a protocol without the check: the prover sends the true cofactor whatever the claim; every later check is then about true values, and any root is accepted |
| B16 | `ζ` has at least `τ_max` coordinates | absent | `constraints.rs:250-253` (start of the table sumcheck) | absent | the zerocheck point exists | none: a function of the announced sizes; every table has a flush, so `μ > τ_max` |
| B17 | The stream and the openings are fully consumed (end of the proof) | absent | `mod.rs:769`; `fs/transcript.rs:213-219` | `py:1414`; `py:415-417` | one encoding per proof | none on soundness |

Nothing is checked at U6 and U7: a wrong boundary evaluation is caught by the opening, a wrong
`rem_s` by the table sumcheck's final check. Rejections of these phases in the Rust are
therefore `CpuError::PublicInput`, `CpuError::Transcript`, `Error::Truncated`,
`Error::ZeroCount`, `GkrError::Truncated`, `GkrError::LayerMismatch` (`mod.rs:303-313`,
`leaf.rs:75-81`, `gkr.rs:17-21`).

---

## C. The blueprint set against it

Objects of the spine used below, once. An **`M3Instance`** (`Spine/Instance.lean:119-148`) is
the data the verifier reads about an arithmetization: tables with log-heights `τ` and widths,
per table its constraint polynomials and its flushes (a side and sixteen coordinate polynomials
over `K`), a degree bound `d`, its count columns, a list of boundary blocks, the layout of the
columns in the stack, the public lines, an auxiliary predicate. **`M3Holds I input q`**
(`:219-220`) is the relation on the stack `q`. A **`Phase.Def I StmtIn StmtOut`**
(`Spine/Phase.lean:37-38`) is an ArkLib oracle reduction (an honest prover and a verifier, with
a fixed schedule of messages and challenges) whose one oracle, before and after, is the stack,
bundled with one error per challenge. **`Phase.Complete`** and **`Phase.Security`** are its
perfect completeness and its round-by-round knowledge soundness between two **seam relations**.
The bus slot is

```lean
-- LeanerVM/Protocol/Spine/Compose.lean:76, 96, 115
  bus : Phase.Def I I.Stmt (I.Stmt × BusOut I)
  bus : Phase.Complete I P.bus (Seam.commit I) (Seam.bus I)
  bus : Phase.Security I P.bus (Seam.commit I) (Seam.bus I)
```

| Item | Blueprint counterpart | Match | Classification and change |
| --- | --- | --- | --- |
| S0 seed | row *Fiat–Shamir* (`bp:325`) | yes | — |
| S1 announced sizes | `Sizes` (`bp:795-798`, with `logInvRate`); not a message of the oracle protocol: the instance is indexed by them (`bp:316`, acceptance test 21) | form differs | **deliberate deviation**, to keep. Reason: an oracle's type cannot depend on a message. It owes: the compiled verifier absorbs the 8 elements before the root (acceptance test 12 says so), and `verify_knowledgeSound` bounds the error uniformly over admissible sizes |
| S2, C2, B17 canonical encodings, consumption | none | **absent** | G9 |
| S3 | by type (`Statement.lean:72-73`) | yes | — |
| S4, S6 caps and windows | `Sizes.Admissible` (`bp:800-801`), row *Stacks* "`μ_stack ∈ [15, 28]`" | **inconsistent** | G4 |
| C1 commitment | the commit phase sends the stack itself as the oracle (`Compose.lean:55-56`) | form differs | **deliberate deviation** (the ideal oracle model); Layers 11 and 12 owe the compilation |
| U0 assertions | row *Verifier shape* (`bp:326`): "theorems about the layout, not branches of `verify`" | yes | **deliberate deviation**, to keep. It owes four lemmas about `leanIsaInstance` (B11); none is listed in Layer 3. Proposed: add them to Layer 3's list |
| U1 `(α, β)` | Layer 6 `V_to_P : (Fin 4 → E) × E` (`bp:959`) | yes (one message for five squeezes; Layer 12's encoding) | — |
| U2 roots | Layer 6 `P_to_V : E × E`; acceptance test 4 | order not stated | G8 |
| U3, U4 combiners | row *GKR* "A fresh combiner `λ` per layer" (`bp:321`) | **no**: one more | G2 |
| U4 radix, parity | row *GKR*, acceptance test 17 | yes | — |
| U4 round message, running claim, final check | row *GKR* "Layer sumcheck messages have degree 5 …", row *Sumcheck messages* (`bp:315`), Layer 4 (`bp:898-901`) | **no** | G1 |
| U4 combination challenges | row *GKR* "two combination challenges after each radix-4 layer" | yes; the binary layer's one is not mentioned | G12 |
| U4 `ζ` | row *GKR* "end at one `ζ`" | yes, order not stated | G8 |
| U5 `R_c ≠ 0` | Layer 6 (`bp:973`), acceptance test 3, clause `CountsNonzero` | yes | — |
| B12 one root | Layer 6, acceptance test 4, clause `Balanced` | yes | — |
| U6 boundary evaluations | Layer 6 `P_to_V : boundary evaluations`; row *Claim pool order* (`bp:324`) | order and deduplication not stated | G8 |
| U7 derived `rem_s`, forms | `LinearClaim` with `VirtualTerm`s (`Seams.lean:71-99`), `bp:565-574` | yes (E.1) | — |
| A.5 count tree | row *Count tree* (`bp:320`), acceptance test 18 | yes | — |
| A.5 padding | row *Bus*, acceptance test 2 | yes | — |
| A.5 order of the leaf stacks | none (the row *Stacks* is about the witness stack) | **absent** | G7 |
| A.5 fingerprint | row *Bus* (`bp:319`), acceptance test 1 | yes | — |
| B14 layer check | Layer 5 test "a leaf changed after the root is sent rejected" | yes | — |
| B15 round identity | row *Sumcheck messages*: the oracle protocol sends every coefficient and checks | form differs | **deliberate deviation**, to keep. It owes `RoundPoly.decode` (Layer 12) and the lemma that the decoded message passes the check. Correct only once G1 is fixed: the polynomial sent is the cofactor |
| error of `(α, β)` | `busError` (`bp:974`) `4·2^μ_bus/|E|` | yes | — |
| error of the GKR | `gkrError` (`bp:940-942`) | not tight; one case missing | G1, G12 |
| zerocheck escape | row *Seams* (`bp:333`); Layer 6 (`bp:974`); Layer 7 (`bp:1000-1003`); tracker P2 | four versions | G6 |
| Layer 6 sketch as a whole | `bp:954-979` | stale against the spine | G11 |
| Layer 5 `gkr` | `bp:930-937` | does not compose | G3 |

Acceptance tests of the task, against the ground truth: 1 (degree 4, `05:58`), 2, 3, 4, 15, 17
and 18 state what the pinned sources do. Test 5 is about the arithmetization. Test 18's clause
"the leaf layout, and so `ζ`, differ" is loose: a different count stack changes the count
side's selectors, not `ζ`'s length (the depth is the push side's); after Fiat–Shamir every
later challenge differs anyway. Test 21 is the deviation of S1. Test 28 is right and its
condition is incomplete (G10).

---

## D. The errors

### D.1 What the specification states

- Theorem 5.1 (`05:36-38`): the product check has "soundness error `4·2^μ/|E|`", over the joint
  draw of `(α, β) ∈ E⁵`; proof by Lemma 5.2 and Corollary 3.9 on polynomials of total degree at
  most `4·2^μ` (`05:58`). Lemma 5.2's proof is `TODO` (`05:50-52`).
- Fact 3.10 (`03:79-85`): sumcheck on a polynomial of individual degree `d` in `κ` rounds,
  error `dκ/|E|`.
- Definition 3.11 (`03:87-93`): zerocheck at a random point, `κ/|E|`.
- §3 "Two savings on a round message" (`03:110`): "A zerocheck round on a degree-`d` cofactor
  therefore costs `d` field elements."
- **No error is stated for the GKR**, neither per challenge nor in total (`05:61-95`), and none
  for the recycled zerocheck point beyond "as long as it results from uniform sampling occurring
  after the table columns are committed" (`05:132`).
- The only round-by-round statements are in Annex B: Definition B.x "RBR soundness, informal"
  (`B:74-82`) and the theorem "RBR soundness" (`B:139-152`), both about the opening. §3 has no
  round-by-round theorem. §8.5 cites the theorem once, for the opening's `λ` (`08:98`).

### D.2 What the Rust asserts

`leaf.rs:108-118`: a degree bound `(N_TUPLE_BITS + 1)·2^μ + 8·(μ + 1)²`, that is
`5·2^μ + 8(μ+1)²`, turned into bits as `192 − bitlength`, and asserted to be at least
`SECURITY_BITS = 128` (`leaf.rs:142-145`, `lib.rs` "`pub const SECURITY_BITS: u32 = 128`"). The
test `bus_soundness_tracks_depth_only` (`leaf.rs:945-950`) has it hold up to `μ = 61`. It is a
bound on the **sum** of the errors, conservative twice: `5` where the total degree is `4`, and
`8(μ+1)²` where the GKR's sum is `μ² + 2` (D.3). No grinding in these phases
(`assert_grinding_unnecessary`). The Python verifier asserts nothing.

### D.3 The round-by-round argument, worked out

Fix the statement of the bus phase, which in ArkLib's model is the pair `(input, q)`: the
verifier's view of a phase is an ArkLib `Verifier` whose input statement is
`StmtIn × (∀ i, OStmtIn i)`, the oracle data included (`Component.lean:93-94`), so a state
function may speak of `q`. ArkLib's **knowledge state function**
(`.lake/packages/Arklib/ArkLib/OracleReduction/Security/RoundByRound.lean:164-188`) is a
predicate `toFun m stmtIn transcript witMid` on partial transcripts with three laws: at the
empty transcript it is the input relation; it cannot become true by a prover message; if the
verifier can output a statement in the output relation, it is true at the full transcript.
**Round-by-round knowledge soundness in the worst case**
(`rbrKnowledgeSoundnessWorstCaseWith`, `:553-569`) says that for every prefix and every
challenge index, the probability over the fresh challenge that the predicate goes from false
to true is at most the error of that challenge. Here every witness type is `Unit`.

Notation. `L^1, L^2, L^3`: the push, pull and count leaf tables of `q` at `(α, β)`, padded with
`1`; `Ṽ^s_i` the extension of level `i` of tree `s`. `W` is `PublicLinesHold ∧ aux`. For a set
`T` of coordinates of `ζ` already drawn, `Z(T)` says: for every table `j` and constraint `C`,
the extension of the table `x ↦ C(row x)`, with its variables in `T ∩ [0, τ_j)` set to their
drawn values, is the zero polynomial in the others. `Z(∅)` is `ConstraintsVanish` (a multilinear
is zero iff its table is); `Z(all)` is "every `C̃_{j,i}(ζ_{<τ_j}) = 0`".

| After | State (true = the prover has not lost) | Error of the challenge, tight |
| --- | --- | --- |
| nothing | `Z(∅) ∧ Balanced ∧ CountsNonzero ∧ W`, that is `M3Holds` | |
| `(α, β)` | `Z(∅) ∧ ∏L^1 = ∏L^2 ∧ CountsNonzero ∧ W` | `4·2^μ/|E|` (Lemma 5.2, total degree `4N`, `N ≤ 2^μ`) |
| roots `R, R_c` | `Z(∅) ∧ W ∧ R = ∏L^1 ∧ R = ∏L^2 ∧ R_c = ∏L^3 ∧ R_c ≠ 0` | prover message: true here implies true before |
| a combiner `λ` | `… ∧ Σ_s λ^s v_s = Σ_s λ^s Ṽ^s_i(point)` | `2/|E|`: a nonzero polynomial of degree 2 in `λ` |
| message `h'` of round `t` | `… ∧ h' = h_t` (the true cofactor) `∧` the round identity | prover message |
| `χ_t` | `… ∧ h'(χ_t) = h_t(χ_t)` | **`4/|E|`**: `h' ≠ h_t`, both of degree at most 4 |
| children | `… ∧` the layer check `∧` every child is the true value | prover message: the check and a false claim leave a false child |
| `u_0` | the six half-interpolations are true | `1/|E|` |
| `u_1` | the three values are `Ṽ^s_{i−2}(u_0, u_1, χ)` | `1/|E|` |
| in the last layer, each of `χ_t`, `u_0`, `u_1` | the same, with `Z(T)` for `T` enlarged by the coordinate just drawn | `max(above, 1/|E|)`, so `4/|E|`, `1/|E|`, `1/|E|` |
| the last combiner | unchanged (the three values are true separately) | `0` |
| boundary evaluations | checks `∧ Z(all) ∧ W ∧` the five column claims `∧` the three bus forms equal `rem_s` | prover message: by the leaf decomposition (`05:106-108`), true forms and true evaluations give true leaf claims |

Three points need an argument.

*The sumcheck round is `4`, not `5`.* The running claim is the cofactor's value. If the claim
before round `t` is false, the prover's `h'`, which satisfies the round identity with the false
claim (by derivation in the deployed encoding, by the check in a protocol that sends `c_0`),
differs from the true cofactor, which satisfies it with the true claim. Two distinct
polynomials of degree at most 4 agree on at most 4 points. The bound is reached: take
`h' = h_t + a·∏_{i<4}(Y − ρ_i)` with the `ρ_i` distinct and `a` fitted to the identity. `5`
would be the error of a different verifier, which keeps the equality factors in its running
claim and multiplies them into the final check: there, `eq(point[t], χ_t) = 0`, that is
`χ_t = 1 + point[t]`, zeroes the claim and is a fifth bad challenge. The deployed verifiers
never form that product (A.4, step 4).

*The zerocheck escape is a maximum, not a sum, and is `1/|E|` whatever the number of
constraints.* The state is a conjunction `A ∧ Z`. At a fixed prefix, either `A` is false before
the challenge, and then the probability that `A ∧ Z` is true after is at most `A`'s error; or
`A` is true and `Z(T)` false, and then some constraint's partial extension `p` is nonzero: write
`p = p_0 + X_k·p_1`; `p_0 + ζ_k·p_1` is the zero polynomial for at most one `ζ_k` (if `p_1 = 0`
for none, if not by one nonzero coefficient of `p_1`). Several violated constraints must all
vanish at once, so the bound is the smallest of theirs, not their sum. If `k ≥ τ_j` the
polynomial does not change. Hence on every coordinate of `ζ` the error is
`max(error of the GKR, 1/|E|)`, which is the error of the GKR.

*The state is definable because every coordinate of `ζ` is drawn in the last layer, one
challenge per coordinate* (A.4). The order in time, `ζ_2, …, ζ_{μ−1}, ζ_0, ζ_1`, is immaterial:
`Z(T)` is defined for any set `T`.

**Sum over the bus phase** (for the interactive error), `μ` even:
`4·2^μ + 2 + Σ_{k=0,2,…,μ−2} (4k + 1 + 1 + 2) − 2 = 4·2^μ + μ²`, over `|E|`. With the
blueprint's numbers: `4·2^μ + 5μ²/4 − μ/2 + 2`, plus whichever zerocheck charge is meant.

### D.4 What the blueprint charges, judged

| Charge | Source | Correct | Tight | Right challenge |
| --- | --- | --- | --- | --- |
| `4·2^μ_bus/|E|` on `(α, β)` | `bp:974`, `bp:924-926` | yes (Theorem 5.1) | within a factor 2 (`N` against `2^μ`) | yes |
| `(nside − 1)/|E|` per combiner | `bp:941` | yes | yes | yes; the last combiner needs `0` and the blueprint has no last combiner (G2) |
| `5/|E|` per sumcheck round | `bp:941-942` | an upper bound | **no**, `4/|E|` | yes |
| `2/|E|` per combination pair | `bp:942` | yes as one challenge in `E²` | yes | yes; the binary layer's single challenge is unassigned (G12) |
| zerocheck, "`1/|E|` per coordinate per constraint" | `bp:333`, tracker P2 | an upper bound | **no**: no factor per constraint, and a maximum with the GKR's error | yes |
| zerocheck, "charged to the `(α, β)` and GKR challenges … an extra `τ_max/|E|` per constraint" | `bp:1001-1003` | an upper bound | no | **no**: `(α, β)` is drawn before any coordinate of `ζ` |
| zerocheck, nothing | `bp:974` (`busError` = the `(α, β)` term plus `gkrError`) | **yes**, by the maximum | — | — |

**The numeric bound.** `piopError_le` (`bp:1130`) claims `Σ piopError ≤ 2^40/|E| + flockError`.
At the per-logarithm caps alone (`κ_mem = κ_bc = τ_j = 32`), `N_push = 36·2^32 + 1`, so
`μ_bus = 38` and the `(α, β)` term **alone** is `4·2^38/|E| = 2^40/|E|`: the bound is then
false, every other term being positive. With the stacking window it holds with room:
`N_push − 1 < Σ_stack 2^κ ≤ 2^28` (each table has more committed columns, `15, 15, 8, 15, 14,
19`, than flush pairs, `5, 5, 3, 5, 5, 11`; memory has 4 columns for 1 block), so
`μ_bus ≤ 28` and the term is at most `2^30/|E|`. So the bound depends on finding G4.

---

## E. Can the real bus phase fill the spine's slot?

### E.1 The output statement, as a `BusOut I`

```lean
-- LeanerVM/Protocol/Spine/Seams.lean:71-79, 91-95, 130-134
structure VirtualTerm (I : M3Instance) where
  weight : E
  j : Fin I.ntab
  poly : CMvPolynomial (I.width j) K
  point : Vector E (I.τ j)
structure LinearClaim (I : M3Instance) where
  terms : List (VirtualTerm I)
  value : E
structure BusOut (I : M3Instance) where
  linear : List (LinearClaim I)
  columns : List (ColumnClaim I)
```

(`CMvPolynomial n K` is CompPoly's computable polynomial in `n` variables over `K`. A term's
value is its weight times the multilinear extension, at its point, of the table
`x ↦ poly(row x)`; a linear claim says the terms' values sum to `value`,
`Seams.lean:82-99`.)

For an instance `I` and a transcript with challenges `α, β`, final point `ζ`, final values
`v_1, v_2, v_3` and boundary evaluations `e`, the deployed verifier's output is:

**Linear claims**, `B + 3` of them, in the order the table sumcheck gives its powers of `ξ`
(`mod.rs:404-422`; `05:145`):

1. for each table `j` in order and each constraint `C` of it in order: one term
   `(1, j, C, ζ_{<τ_j})`, value `0`. For leanVM `B = 2`: the two `JUMP` identities
   `b + cond·w` and `cond·(b + 1)` (`tables.rs:70-74, 722-724`).
2. push: for each table block `b` of table `j` on the push side and each coordinate `i` with a
   nonzero polynomial, the term `(eq(sel_b, ζ_{≥τ_j})·eq(α, i), j, c_{b,i}, ζ_{<τ_j})`, and one
   term `(eq(sel_b, ζ_{≥τ_j})·β, j, 1, ζ_{<τ_j})`; value
   `rem_1 = v_1 + F_1 + 1 + Σ_{b on the side} eq(sel_b, ζ_hi)`, `F_1` the blocks no table owns
   (A.5). 34 table blocks for leanVM.
3. pull: the same on the pull side, value `rem_2`.
4. count: for each count column `c` of table `j`, the term `(eq(sel_b, ζ_{≥τ_j}), j, X_c,
   ζ_{<τ_j})`; value `rem_3 = v_3 + 1 + Σ_b eq(sel_b, ζ_hi)`. 28 terms for leanVM.

**Column claims**, 5 for leanVM, in stream order: `(mem_0, ζ_{<κ_mem}, e_1)`,
`(mem_1, ·, e_2)`, `(mem_2, ·, e_3)`, `(cntfin_mem, ζ_{<κ_mem}, e_4)`,
`(cntfin_bc, ζ_{<κ_bc}, e_5)`.

The deployed forms have coefficients in `E` (`leaf.rs:275-281`); each is an `E`-multiple of a
coordinate polynomial over `K`, so the list of terms says the same. `α`, `β` and `ζ` do not
travel: they are inside the weights and the points, as `BusVerify` hands on forms, totals and
the point (`leaf.rs:849-860`). **Everything the deployed phase emits is expressible.**

### E.2 Completeness and knowledge soundness

**Perfect completeness holds.** From `M3Holds I input q`: the constraints vanish, so every
zerocheck claim holds at every point; `Balanced` is a permutation, so the two products are one
element and the honest prover has a single `R` to send (the Rust prover asserts it,
`gkr.rs:273`); `CountsNonzero` gives `R_c ≠ 0`, a product of nonzero elements of a field; the
GKR's honest messages pass every layer check, no inverse of a challenge being taken; the bus
forms hold with the derived `rem_s` by the leaf decomposition; the public lines and `aux` are
untouched. The degree conjunct of `Seam.bus` holds by `flushes_degree` and
`constraints_degree`, **provided `1 ≤ d` when there is a count column** (G10).

**Round-by-round knowledge soundness can hold**, with the state function and the errors of
D.3. The points the task names:

- *`CountsNonzero` against `R_c ≠ 0`.* Exact, no probability: `R_c` equal to the true product
  of the count leaves, nonzero, is every cell nonzero (the padding is `1`). The probability is
  the GKR's, for `R_c` being the true product.
- *`Balanced` against the equality of two products.* `List.Perm` of the tuple lists is equality
  of the multisets (`Instance.lean:201`); Lemma 5.2 makes unequal multisets unequal polynomials
  in `K[A_0, …, A_3, X]`; the error is the `(α, β)` challenge's. The lemma holds (the factors
  `X − π_A(t)` are monic of degree 1 in `X` over the unique factorization domain `K[A]`, and
  `t ↦ π_A(t)` is injective, `π_A(t)` being the multilinear with values `t_i`).
- *The bound on the number of tuples.* `N ≤ 2^μ_bus` by the layout. The bound of Lemma 6.2,
  fewer than `2^64 − 1` reads, is not the proof system's: it is a hypothesis of lookup
  correctness, used by `constraintSoundness` through the caps.
- *The padding leaves.* `1` in the three trees; they change no product and enter the leaf claim
  through the term `1 + Σ_b w_b`.
- *Which count columns enter.* `I.counts j` for every `j`: the tables' read counts. leanISA's
  `CountsNonzero` quantifies over the same cells ("every read pull of the six tables",
  `Arithmetization/Statement.lean:240-243`).
- *Do the zerocheck claims belong in the bus phase's output?* Yes. The table sumcheck batches
  them with the bus forms under `ξ`, so they are part of its input relation; and the
  randomness that makes them meaningful is `ζ`'s, drawn in the bus phase, so no later challenge
  can be charged for them.
- *Is the state function definable?* Yes (D.3).

**Where it fails as the blueprint plans it**: finding G3. The state function above is one
state function for the whole phase; it is not the GKR's state function with something added
afterwards.

### E.3 The boundary blocks

```lean
-- LeanerVM/Protocol/Spine/Instance.lean:86-98
inductive Coord (S : Shape) (κ : ℕ)
  | const (c : K)
  | known (col : Column κ)
  | committed (c : S.ColumnId) (h : S.τ c.1 = κ)
structure BoundaryBlock (S : Shape) where
  κ : ℕ
  side : Side
  coords : Vector (Coord S κ) 16
```

Every block of leanVM that no table owns is expressible (`layout.rs:354-395`):

| Block | Side | `κ` | Coordinates |
| --- | --- | --- | --- |
| state, initial | push | 0 | `const g⁰, const g⁰, const g⁰`, then `const 0` |
| state, final | pull | 0 | `const g⁰, const g^(2^κ_bc − 1), const g⁰`, then `const 0` |
| memory seed | push | `κ_mem` | `const g¹, known idx, const 1, committed mem_0, mem_1, mem_2` |
| memory finalization | pull | `κ_mem` | `const g¹, known idx, committed cntfin_mem, committed mem_0, mem_1, mem_2` |
| bytecode seed | push | `κ_bc` | `const g², known idx, const 1, known P_3 … P_10` |
| bytecode finalization | pull | `κ_bc` | `const g², known idx, committed cntfin_bc, known P_3 … P_10` |

The framework blocks of the Rust use only `Const`, `Index`, `Col`, `Public`
(`leaf.rs:442-454`, the other cases `unreachable!`). **Dependence**: on the program (the final
program counter `layout.rs:335`, the eight bytecode columns `layout.rs:343`) and on the
announced sizes (the height of the index columns); **never on the public input** (the public
words enter only the public-input phase, `mod.rs:745-755`). The spine allows exactly this:
`boundary` is a field of the instance, and the instance is `leanIsaInstance prog s`. An
arithmetization whose boundary depended on the public statement could not be written; leanVM
at the pin is not one.

Two remarks for the adaptor, outside this task. The committed columns of these blocks must be
columns of tables of the instance, which the blueprint provides (tables without constraints or
flushes, `bp:836-839`). And leanISA's memory and bytecode blocks are Clean tables whose rows
hold the index and the program's columns as cells (`Statement.lean:272-293`), so the instance is
not `Ensemble.toM3` of the ensemble: those cells become `Coord.known`.

### E.4 What cannot be expressed, and what is required in excess

Cannot be expressed, or is not data of the instance:

1. **The layout of the three leaf stacks.** `M3Instance` has the layout of the witness stack
   and none for the leaves. It is derivable, and the derivation must be the deployed one (G7).
2. **Which tables the table sumcheck opens** (G16).
3. Nothing else: the forms, the claims, the count side at `α = β = 0`, the virtual limb columns
   of `BLAKE2S` (columns of their table, read through the layout) are expressible.

Required by the spine and absent from leanVM: nothing that matters. `Seam.bus` admits
statements the deployed bus phase never emits, for instance claims of one table at unrelated
points (probe H.2, part 3). That is a burden on the table phase's completeness, not on the bus
phase; a table phase written over the terms' own points meets it (G16).

### E.5 Negative result on the spine as built

Checked, with no finding: `M3Instance.tuples` takes every row of every flush of the side and
every row of every boundary block of the side (`Instance.lean:174-186`), as the deployed leaves
do; `Balanced` is a permutation of lists of 16-tuples, separator included; `CountsNonzero`
ranges over every cell of every listed column; `Seam.commit` is `M3Holds` of the oracle
(`Seams.lean:171`, `Iff.rfl` in the tests); `Seam.bus` carries the public lines and `aux`
through. The toy's tests make each clause fail alone
(`tests/LeanerVMTests/Protocol/Spine.lean:26-82`). The probe H.2 builds three more instances on
the same definitions.

---

## F. The status file's findings, re-verified

| Finding of the status | Verdict | Evidence |
| --- | --- | --- |
| One scalar root for push and pull (F3, `st:309-310`) | **true of the Rust and the Python**; the specification says the same, so it is no divergence (G13) | `gkr.rs:362-367` "One root for both balancing trees, so their equality is structural"; `py:434, 437`; `08:68-69` |
| The count tree holds the tables' count columns only (F11, `st:321-322`) | **true** | `layout.rs:412-414` `for &c in table.count_columns() { count_blocks.push(blk(kappa, vec![Col(base + c)])); }`; `layout.rs:187`; `py:733-735, 875-876`. `MFCNT` and `BFCNT` appear only in the pull side (`layout.rs:377, 395`) |
| Blocks of equal size in the stack: the shared columns first (F17, `st:330`) | **true** | `witness.rs:70` `.then(a.cmp(&b))`; `layout.rs:13-26` (`MEM_LO = 0 … QFLOCK = 5`), `layout.rs:41-46` (tables after `N_SHARED`); `py:308`, `py:880-882` |
| The caps and the stacking bound `μ ∈ [15, 28]` (F15, `st:327-328`) | **true** | `mod.rs:157-176`; `pcs.rs:49, 51`; `py:857-864, 907-908, 1379` |
| The Python verifier omits four caps (F9, `st:316-318`, `st:164`) | **false at the pin** (G5) | `py:857-864` |
| Padding leaves `1`, stack padding `0` | **true** | `leaf.rs:222-224` `values.resize(explicit, F192::ONE)`, `gkr.rs:61, 114`; `witness.rs:152` `pad.fill(F64::ZERO)`; `05:20`, `05:103`, `04:8-10` |

---

## G. Findings

### G1. The GKR layer sumcheck is the normalized one: the blueprint gives it the wrong degree, the wrong error and no definition

**Severity**: major. **Classification**: an error of the blueprint.

**Evidence.** The deployed round message is the cofactor of degree 4, four elements on the
wire, `c_0` derived through the equality factor; the running claim is the cofactor's value; the
layer's final check has no equality factor (A.4; `gkr.rs:399-404, 410-413`;
`fs/transcript.rs:297-302`; `py:411-413, 445, 449`). The probe's honest prover, written to that
reading, is accepted by the pinned Python verifier (H.1). The table sumcheck is the other
variant: the whole cubic is sent, `c_1` derived, and the verifier multiplies the equality
factors into its final check (`constraints.rs:267` `next_round_poly(4, claim, None)`,
`:271-274`; `py:608-614`).

The blueprint:

- `bp:321`: "Layer sumcheck messages have degree 5 (eq × four multilinears); the round check is
  on the cofactor (Gruen)."
- `bp:315`: "A round polynomial travels as its coefficient list, low degree first, of length
  `d + 1`; the oracle protocol sends all of them. Dropping one is the *encoding* of Layer 12."
- `bp:898-901`: the eq-weighted variant has "`eq(ζ_{<τ_j}, ·)` as an explicit factor whose
  evaluation at `r` the verifier computes itself (so `d` counts the cofactor plus one)".
- `bp:941-942`: "`5/|E|` to each sumcheck round". Tracker, hole G5: "degree-5 round
  polynomials".

Read literally, a message of degree 5 has six coefficients and five on the wire, where the Rust
has four: a verifier built so rejects every Rust proof. Read with Layer 4's variant, the
verifier multiplies the equality factors in, which is a different verifier from the deployed
one (it accepts when `χ_t = 1 + point[t]`, whatever the children). Layer 12's
`RoundPoly.decode (d) (claim) (eq? : Option E)` (`bp:1212`) knows both encodings; Layers 4 and 5
define only one protocol.

**Proposed change.**

- `bp:321`, as it stands: "Layer sumcheck messages have degree 5 (eq × four multilinears); the
  round check is on the cofactor (Gruen)." As proposed: "The layer sumcheck is normalized: the
  prover's message in round `t` is the cofactor `h_t`, of degree 4 (the four children's lines
  multiplied, summed against the equality kernel of the coordinates not yet bound), five
  coefficients; the verifier checks `(1 + r_t)·h(0) + r_t·h(1)` against the running claim,
  `r_t` the coordinate of the layer's point; the new running claim is `h(χ_t)`; the layer's
  final check compares the running claim with `Σ_s λ^s ∏ children`, with no equality factor
  (`gkr.rs:399-413`). The table sumcheck is not normalized (`constraints.rs:267-274`)."
- Layer 4: define the two variants by name, the plain one (error `d/|F|`, `d` the degree of the
  polynomial sent, the verifier evaluating the equality factors at the end) and the normalized
  one (error `d_c/|F|`, `d_c` the degree of the cofactor).
- `bp:941-942` and the tracker: "`4/|E|` to each sumcheck round".

Reason: faithfulness of the wire format and of the verdict; the error is then tight.

### G2. One combiner more than layers: the last is drawn and never used

**Severity**: major (by the brief's definition: the blueprint omits a challenge the verifiers
draw; the fix is one sentence). **Classification**: an error of the blueprint.

**Evidence.** `gkr.rs:369` (before the loop) and `gkr.rs:391, 423` (at the end of every
iteration, the last included); `py:435, 453`. Probe H.1: the GKR draws `μ²/4 + μ + 1`
challenges for even `μ`, and `ζ` never contains the last. The specification has "at every
layer a combiner" (`05:91`). The blueprint: "A fresh combiner `λ` per layer" (`bp:321`), and
Layer 5 "a fresh `λ` per layer … exactly as pinned" (`bp:940-941`).

In the oracle model a challenge nobody uses is harmless. After Fiat–Shamir it is a squeeze
that changes the chain's state (`fs/lib.rs:95-99`), so `ξ` and everything after depend on it.

**Proposed change.** `bp:321`, as it stands: "A fresh combiner `λ` per layer". As proposed: "A
combiner `λ` is drawn after the roots and after every layer, the last layer included; that last
one is used by nothing and its error is `0` (`gkr.rs:369, 423`)." Add the message count of
section A.3 to acceptance test 17.

### G3. The generic GKR of Layer 5 cannot be appended in the bus phase, and cannot carry the zerocheck clause

**Severity**: major. **Classification**: an error of the blueprint; the first half is also a
deviation an upstream library forces.

**Evidence.** Layer 5's component (`bp:930-937`):

```lean
def gkr (nside μ : ℕ) : OracleReduction []ₒ
    (StmtIn := Fin nside → E)                                    -- the claimed roots
    (OStmtIn := fun _ : Fin nside ↦ ETable μ) Unit               -- the leaf tables
    (StmtOut := (Fin μ → E) × (Fin nside → E))                   -- ζ and the leaf claims Ṽ₀ˢ(ζ)
    (OStmtOut := fun _ : Fin nside ↦ ETable μ) Unit …
```

Its oracles are the leaf tables. A phase's one oracle is the stack
(`Phase.lean:37-38`), and two components are appended only when the output oracles of the first
are the input oracles of the second (`Component.lean:143-149`, `Def.append`). The leaf tables
are functions of the stack and of `(α, β)`; carrying a reduction along such a map is ArkLib's
context lifting, whose completeness and knowledge-soundness theorems are admitted at the pin:

```lean
-- .lake/packages/Arklib/ArkLib/OracleReduction/LiftContext/Reduction.lean:355-365, 542-560
theorem liftContext_completeness …  := by … sorry
theorem liftContext_rbr_knowledgeSoundness … := by … sorry
```

The blueprint's ledger says of them "Not consumed: statements are shaped so that no lens is
needed" (`bp:262`). The holes table has the bus phase consume G5 and G6 (`bp:606`), and the
tracker writes `busPhase I (G : Gkr.Def)`.

Second half. The bus phase's state function must turn `ConstraintsVanish` into the claims at
`ζ` while the coordinates of `ζ` are drawn, which is inside the GKR's last layer (D.3). ArkLib's
appended state function is made of the components' own
(`Verifier.KnowledgeStateFunction.appendGuarded`); a clause that is constant can be framed
around a component, a clause that changes with the component's challenges cannot. So the
security of a GKR that knows nothing of the constraints does not give the bus phase's.

**Proposed change.** Restate Layer 5's component over a context, with riders:

```lean
-- proposed shape (Layer 5); S, OStmt arbitrary
def gkr (nside μ : ℕ) (leaves : S → (∀ i, OStmt i) → Fin nside → ETable μ)
    (riders : S → (∀ i, OStmt i) → List (Σ τ, ETable τ)) :
    Component.Def (S × (Fin nside → E)) OStmt Unit
                  (S × Vector E μ × (Fin nside → E)) OStmt Unit
-- relIn : the roots are the products of `leaves s o`, and every rider table is zero
-- relOut: the leaf claims hold at ζ, and every rider's extension vanishes at ζ_{<τ}
-- err   : 2/|E| per combiner (0 for the last), 4/|E| per round, 1/|E| per combination challenge
```

and say in Layer 6 that the bus phase is `[(α, β); roots] ⟫ gkr ⟫ [boundary evaluations]` with
`leaves` the three leaf tables of the stack and `riders` the constraint tables. Replace
`bp:262`'s "no lens is needed" by the reason this shape needs none. The workaround is retired
when ArkLib proves the lifting theorems **and** offers a way to run a rider on a component's
challenges; the first alone does not give the second half.

### G4. The admissibility predicate: the stacking window and the rate window

**Severity**: major. **Classification**: an error of the blueprint (three of its statements
cannot hold together).

**Evidence.** The verifiers reject `μ_stack ∉ [15, 28]` and `ρ ∉ [1, 4]` (B8, B9). The
blueprint:

- `bp:800-801`: "`def Sizes.Admissible (prog : Program) (s : Sizes) : Prop -- the caps;
  decidable`" and "`theorem admissible_iff_caps : s.Admissible prog ↔ (Caps w ∧ Sizes.ofWitness
  w = some s)`".
- leanISA's `Caps` has neither window: "(7) the WHIR rate (`:167`) and (8) the stacked size
  `mu ∈ [MIN_MU, MAX_MU]` (`:174-176`) are parameters of the commitment, left to the protocol
  layer" (`Arithmetization/Statement.lean:79-81`; the structure is at `:250-263`).
- `bp:1218-1220`: `verify_iff_compiled` quantifies "`∃ s, s.Admissible prog ∧ …`".
- `bp:1130`: `piopError_le (hs : s.Admissible prog) : Σ i, piopError s i ≤ 2^40/|E| + flockError`.

If `Admissible` is the caps alone, `verify_iff_compiled` is false (the Rust rejects sizes that
are admissible) and `piopError_le` is false at the caps (D.4). If it contains the windows,
`admissible_iff_caps` is false. Besides, `Sizes.ofWitness w` cannot produce `logInvRate`, which
no witness determines, and `Caps w` has the conjunct `well_shaped`, which is no property of
sizes.

**Proposed change.** `bp:800-801`, as proposed:

```lean
def Sizes.Admissible (prog : Program) (s : Sizes) : Prop   -- decidable; read_public, mod.rs:157-176
  -- κ_mem ∈ [16, 32] ∧ ∀ j, τ j ≤ 32 ∧ 3 ≤ τ 5 ∧ logInvRate ∈ [1, 4] ∧ μ_stack prog s ≤ 28
theorem caps_of_admissible (hs : s.Admissible prog) (hw : Sizes.heightsOf w = s.heights)
    (hd : WellShapedData w.data) : Caps w
```

with `Sizes.ofWitness` returning the heights only. Layer 3's tests: add `μ_stack = 29` and
`logInvRate = 5` rejected. State in `piopError_le`'s comment that the bound uses
`μ_bus ≤ 28`, a lemma of Layer 3 (`N_push ≤ Σ_stack 2^κ`).

### G5. The status file's finding on the Python verifier's caps is false

**Severity**: major, of the status file. **Classification**: an error of the status.

**Evidence.** `st:316-318`: "F9 the Python verifier omits the caps `log_mem ∈ [16, 32]`,
`τ_j ≤ 32`, the bytecode power-of-two bound and `τ_BLAKE2S ≥ 3` (`verifier.py:1372-1379` versus
`cpu/mod.rs:158-170`): a divergence between the two verifiers, soundness-relevant, to report
upstream." `st:164`: "Finding F9 … is still to be reported to leanVM."

At the pin, `py:1378` calls `build_layout`, which begins:

```python
# python-verifier/verifier.py:856-864 at a386121f
def build_layout(bytecode: Sequence[K], log_memory: int, table_log_heights: Sequence[int]) -> Layout:
    log_bytecode = log2_strict(len(bytecode)) - BUS_BITS
    require(
        16 <= log_memory <= 32
        and all(0 <= log_height <= 32 for log_height in table_log_heights)
        and table_log_heights[OP_BLAKE2S] >= 3
        and 0 <= log_bytecode <= 32,
        "invalid announced table sizes",
    )
```

`log2_strict` requires a power of two (`py:252-254`). The check was introduced by commit
`14fbca8f`, an ancestor of the pin (`git merge-base --is-ancestor 14fbca8f a386121f`). The Rust
itself says so: "The other two verifiers reject it here too (`python-verifier`,
`guests/aggregate.py`)" (`mod.rs:165`). The status read lines 1372 to 1379 and not the function
they call.

**Proposed change.** Delete F9 from `st:316-318` and the line `st:164`; nothing is to be
reported upstream. Correct the memory of the earlier reviews that cite it.

### G6. The zerocheck escape is charged in four different ways, none tight, one to the wrong challenge

**Severity**: minor (every version is an upper bound, so none makes a false theorem; the
definition of `busError` is nevertheless undetermined). **Classification**: an error of the
blueprint.

**Evidence.** `bp:333` (row *Seams*): "charged in the bus phase, coordinate by coordinate as ζ
is drawn, `1/|E|` per coordinate per constraint". `bp:974`: "`busError` is `4·2^μ_bus/|E|` on
the `(α, β)` message plus `gkrError 3 μ_bus`", no zerocheck term. `bp:1001-1003`: "charged to
the `(α, β)` and GKR challenges of Layer 6, where `ζ` is drawn, as an extra `τ_max/|E|` per
constraint". Tracker P2: the second plus the first. `(α, β)` is drawn before the roots are
sent; no coordinate of `ζ` exists then (A.4).

**Proposed change.** One definition, in Layer 6, replacing the three passages:
"`busError`: `4·2^μ_bus/|E|` on `(α, β)`; on the GKR's challenges, `gkrError`. The zerocheck
escape adds nothing: on each coordinate of `ζ` (the last layer's round challenges and its two
combination challenges) the state is the conjunction of the GKR's and of 'every constraint's
extension, partially evaluated, is zero', and a conjunction escapes with the larger of the two
probabilities, the second being `1/|E|` whatever the number of constraints." Row *Seams*: drop
"per constraint"; Layer 7: drop "the `(α, β)` and".

### G7. The order of the leaf stacks is nowhere stated, and the spine's `tuples` has the opposite order

**Severity**: minor. **Classification**: an error of the blueprint (an omission of a
transcribed convention).

**Evidence.** The deployed order puts the three blocks no table owns first, then the tables'
(A.5; `layout.rs:354-410`; `py:507`, "the blocks no table owns, stacked first", `py:499`). Ties
between equal sizes go by that index, so whenever a table's height equals `κ_mem` or `κ_bc` the
order decides the offsets, the selectors, and so the verdict. The blueprint states the rule for
the witness stack only (`bp:322`); for the leaves it cites files (`bp:196`). The spine lists the
table tuples first:

```lean
-- LeanerVM/Protocol/Spine/Instance.lean:185-186
def tuples (q : Column I.μ) (s : Side) : List (Vector K 16) :=
  I.flushTuples q s ++ I.boundaryTuples q s
```

which is immaterial to `Balanced` (a permutation) and a trap for whoever derives the leaf
layout from it. This is the same kind of finding as the status file's F17 on the witness stack.

**Proposed change.** A new row of the pinned conventions: "Leaf stacks | Per side, the blocks
in index order are the boundary blocks of that side in the order of `I.boundary` (state,
memory, bytecode for leanVM), then for each table in order its flushes of that side in order;
the count side has, for each table in order, one block per count column in the order of
`I.counts`. Stacked largest first at aligned offsets, ties by that index, no floor on the depth
(`layout.rs:354-415`, `leaf.rs:149-156`). The depth of the three trees is the push side's." And
a guard in Layer 6's tests on sizes with `τ_j = κ_mem`.

### G8. Orders the blueprint leaves open: the two roots, the boundary evaluations, the linear claims

**Severity**: minor. **Classification**: an error of the blueprint (omissions of transcribed
conventions).

**Evidence and proposed change**, each a clause to add to Layer 6:

- the roots message is `(R, R_c)`, the bus root first (`gkr.rs:274-275`, `py:434`), against the
  specification's prose order;
- the boundary evaluations are sent in the order in which the sides (push, pull), their blocks
  and their coordinates first name a committed column, a column already valued at the same
  point being skipped (`leaf.rs:428-439, 466-471`); for leanVM `mem_0, mem_1, mem_2,
  cntfin_mem, cntfin_bc`;
- `BusOut.linear` lists the zerocheck claims table by table, then push, pull, count, which is
  the order the table phase gives its powers of `ξ` (`bp:323`; E.1);
- `ζ = (u_0, u_1, χ_0, …, χ_{μ−3})` of the last layer (A.4).

### G9. The canonical-encoding checks and the consumption check are absent from the blueprint

**Severity**: minor. **Classification**: an error of the blueprint (omission).

**Evidence.** Checks B2, B10, B17. The blueprint has no word on them (a search for
"canonical", "upper limb", "consumed" finds only the public word of acceptance test 10). The
status lists the Rust's rejections as "four predicates plus truncations" (`st:319-320`),
without `NonCanonicalEncoding` and `NotFullyConsumed`. None protects soundness; without them
`verify` accepts streams the Rust rejects, and `verify` is specified as the verifier "the Rust
prover's proofs are checked against". Layer 12's six mutations (`bp:1238-1239`) exercise none.

**Proposed change.** Layer 12: list the three checks among `verify`'s, with their source lines;
add three mutations (a nonzero upper limb in an announced size, a nonzero third limb in a half
of the root, one element appended to the stream).

### G10. Two side conditions a bus phase over an abstract instance needs

**Severity**: minor. **Classification**: an error of the blueprint (the spine's instance admits
instances no bus phase of the deployed shape serves; leanVM's is not one).

**Evidence** (probe H.2, parts 1 and 2).

1. With `d = 0` and a count column, `M3Holds` is inhabited and the count form's one polynomial,
   `X_c`, has total degree 1: a statement carrying it is outside `Seam.bus`, whose second
   conjunct is `t.poly.totalDegree ≤ I.d` (`Seams.lean:176`). Completeness of a bus phase that
   emits the count form fails on that instance.
2. A table with a constraint and no flush, no count column and no boundary block of its height
   is not on the bus: the trees have depth 0, `ζ` has no coordinate, and the table's zerocheck
   point needs `τ_j`. The Rust guards the inequality at the start of the table sumcheck
   (`constraints.rs:250-253`).

**Proposed change.** Either two fields of `M3Instance`, `one_le_d : 1 ≤ d` and
`constrained_on_bus : ∀ j, constraints j ≠ [] → τ j ≤ μ_bus`, or two hypotheses of the bus
phase, stated in Layer 6; and acceptance test 28 to name the first.

### G11. The sketch of Layer 6 and the tracker's bus section are stale, and the invariant they name is not one

**Severity**: minor. **Classification**: an error of the blueprint (text the spine superseded).

**Evidence.** `bp:954-979` has `StmtIn := Unit`, a `BusOut` with fields `ζ, rem, pool, α, β`,
a `relOut` with "count root ≠ 0" and without the zerocheck claims, the public lines and `aux`,
and a `LeafLayout prog s` that nothing defines; the spine has `I.Stmt`, `BusOut` with `linear`
and `columns`, and `Seam.bus`. The tracker's P1 has `Phase.Def I Unit (BusOut I) (busSpec I)
(M3Holds I) (Seam.bus I)` and cites "specification (5.4)", which does not exist (`st:303`).
`bp:975-977`: "The knowledge state function's invariant after `(α, β)` is 'the pushed and
pulled multisets of `q` differ, or some count is zero, or a boundary claim is false'". After
`(α, β)` the first clause must be "the two products at `(α, β)` differ": if the multisets
differ and the products collide, the prover is honest from there on and no later challenge can
be charged. And no boundary claim exists before the last message.

**Proposed change.** Replace the code block of Layer 6 by the slot's types (section C) and the
schedule `V_to_P (α, β) ; P_to_V (R, R_c) ; the GKR's ; P_to_V the boundary evaluations`;
replace the sentence on the invariant by the table of D.3.

### G12. The binary layer's combination challenge has no error assigned

**Severity**: minor. **Classification**: an error of the blueprint (omission). `gkrError`
(`bp:941-942`) names combiners, rounds and pairs; for odd `μ` the first layer has one
combination challenge (`gkr.rs:387`), whose error is `1/|E|`. Proposed: "`1/|E|` to each
combination challenge (two per radix-4 layer, one for the binary layer)".

### G13. The status file's finding on the one bus root misreads the pinned specification

**Severity**: minor. **Classification**: an error of the status. `st:289-290`: "S11 §8.5 lists
the bus roots as 'the count root `R_c` and one bus root `R`' but does not say the push and pull
roots are one scalar". It does: "one `R` for both sides is the balance check" (`08:69`) and
"the one bus root for both sides" (`08:100`). F3 is an agreement of the three sources, not a
divergence. Proposed: delete S11; reword F3 as a convention.

### G14. Citation drift

**Severity**: minor. `bp:197` cites `leaf.rs:664-668` for the count blocks: those lines are the
signature of `prove_balance`; the count side is `leaf.rs:606-622`. `bp:601` has "Lemma 5.1"
for the multiset lemma, which is Lemma 5.2 (Theorem 5.1 is the product check, `05:36-48`), as
Layer 5 itself writes. The tracker's P1 has "specification (5.4)".

### G15. Disagreements between the three sources

**Severity**: note. The blueprint follows the Rust on each, rightly.

1. The announced rate `ρ` is sent with the sizes (`mod.rs:123, 149`; `py:1376`); `08:55` names
   seven announced values.
2. The order of the roots: `08:68` names `R_c` first; the stream has `R` first.
3. The seed: `08:55` has "Flock's BLAKE2s R1CS matrices"; the Rust hashes one constant naming
   the circuit (`mod.rs:66-93`). (The status's F14.)
4. Checks of the verifiers the specification does not mention: B2, B7, B8, B9, B10, B16, B17.
5. The combiner after the last layer (G2); `05:91` has one per layer.
6. The Python verifier takes the program as the stacked table of `16·2^κ_bc` words and
   evaluates it whole (`py:566, 857`); it does not check that slots 0 to 2 and 11 to 15 are
   zero. The Rust builds the eight columns from the instructions (`layout.rs:229-309`). The two
   agree on every table that is a program's; the Python's statement space is larger. Not a
   soundness matter: the table is the public statement.
7. The Rust's bound for the fingerprint is `5·2^μ` (`leaf.rs:110`), the specification's
   `4·2^μ` (`05:37`); and "every count column" (`06:78`) against the tables' read counts. The
   Rust's assertions B11 have no counterpart in the Python.

### G16. The table phase must know which tables it opens

**Severity**: note, for the dossier on the table sumcheck. The deployed sumcheck has
`τ_max = max` over the six tables (`constraints.rs:250`, `py:607`) and opens every column of
those six and no other (`mod.rs:344-351`). In the instance the shared columns are tables too,
of log-height `κ_mem ≥ 16`; a table phase taking its number of rounds from every table of `I`
has a different transcript. The criterion "has a constraint, a flush or a count column" is
derivable and must be written down.

### G17. The specification gives no round-by-round analysis of the bus phase

**Severity**: note. D.1. `gkrError` and the zerocheck charge are the blueprint's own analysis;
the specification cannot be cited for them, and the Rust asserts only a coarse sum.

---

## H. Probes

### H.1 The GKR, against the pinned Python verifier

Directory `.claude/reports/blueprint-review/probes/gt-bus/`. `pinned_verifier.py` is a copy of
`python-verifier/verifier.py` at the pin (sha256
`28018d8c63cc9399d5751630ca59bf06d3c833b673949fe38102f65a04d83634` for both files; the copy
avoids writing a bytecode cache into the leanVM checkout). Command, from that directory:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 gkr_probe.py      # Python 3.13.1
```

Source, `gkr_probe.py`:

```python
import random
import sys
from functools import reduce
from operator import mul

sys.dont_write_bytecode = True
import pinned_verifier as pv  # noqa: E402

E, ZERO, ONE = pv.E, pv.ZERO, pv.ONE


class FakeTranscript(pv.Transcript):
    """The pinned transcript with the hash chain replaced by a seeded generator.

    Every other method (next_scalar, next_scalars, samples, sumcheck_round_poly) is the pinned one."""

    def __init__(self, stream, seed):
        self.proof = pv.Proof(tuple(stream), b"")
        self.stream_offset = 0
        self.opening_offset = 0
        self.rng = random.Random(seed)
        self.drawn = []  # every challenge, in the order drawn

    def observe(self, value):
        pass

    def sample(self):
        c = E(self.rng.getrandbits(64), self.rng.getrandbits(64), self.rng.getrandbits(64))
        self.drawn.append(c)
        return c


class ZeroStream(tuple):
    """An endless stream of zeros (for counting)."""

    def __len__(self):
        return 10**9

    def __getitem__(self, i):
        return ZERO


def count(mu):
    t = FakeTranscript([], seed=mu)
    t.proof = pv.Proof(ZeroStream(), b"")
    root_c, point, values = pv.verify_gkr_grand_products(mu, t)
    # which draw is each coordinate of zeta
    where = [next(i for i, c in enumerate(t.drawn) if c is z) for z in point]
    return t.stream_offset, len(t.drawn), where


def scalars_formula(mu):
    return 2 + (mu * mu + 4 * mu + (1 if mu % 2 else 0) if mu > 0 else 0)


def challenges_formula(mu):
    if mu == 0:
        return 1
    if mu % 2 == 0:
        return 1 + mu * mu // 4 + mu
    m = mu - 1  # after the binary layer: layers with 1, 3, ..., mu-2 rounds
    return 1 + 2 + (m // 2) ** 2 + 3 * (m // 2)


# ---------------------------------------------------------------- honest prover (spec 5.3)


def poly_mul(p, q):
    out = [ZERO] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] = out[i + j] + a * b
    return out


def poly_add(p, q):
    n = max(len(p), len(q))
    p = p + [ZERO] * (n - len(p))
    q = q + [ZERO] * (n - len(q))
    return [a + b for a, b in zip(p, q)]


def layers_of(leaves, mu):
    """layers[i] has 2^(mu-i) nodes; node x of layer i is the product of nodes 2x, 2x+1 of layer i-1."""
    layers = [list(leaves)]
    for _ in range(mu):
        prev = layers[-1]
        layers.append([prev[2 * x] * prev[2 * x + 1] for x in range(len(prev) // 2)])
    return layers


def prove(trees, mu, seed, skip_layer=None, lie_root=None):
    """The honest prover of the batched GKR, three trees, one root for the first two.

    `lie_root`, `skip_layer`: the cheating prover of part B. It announces `lie_root` for the first
    two trees; above `skip_layer` it sends round polynomials and children that pass every check of
    that layer (one equation, solved for one child); at `skip_layer` it sends the TRUE children."""
    t = FakeTranscript([], seed)  # draws the same challenges as the verifier will
    stream = []
    layers = [layers_of(tr, mu) for tr in trees]
    roots = [ly[mu][0] for ly in layers]
    shared = roots[0] if lie_root is None else lie_root
    stream += [shared, roots[2]]
    values = [shared, shared, roots[2]]
    lam = t.sample()
    point = []
    layer = mu
    while layer > 0:
        step = 1 if layer % 2 else 2
        width = 1 << step
        k = len(point)
        claim = pv.poly_eval(values, lam)
        # child tables: tabs[s][c][n] = layer-below node c + width * n
        tabs = [[[ly[layer - step][c + width * n] for n in range(1 << k)] for c in range(width)] for ly in layers]
        eq = pv.eq_kernel(point)  # eq(point, n), LSB first
        chis = []
        cheating_here = lie_root is not None and (skip_layer is None or layer >= skip_layer)
        for j in range(k):
            half = 1 << (k - j - 1)
            # the cofactor h_j(Y): the eq weight of coordinate j is factored out
            eq_rest = pv.eq_kernel(point[j + 1 :])
            h = [ZERO]
            for s in range(3):
                acc = [ZERO]
                for x in range(half):
                    term = [eq_rest[x]]
                    for c in range(width):
                        a, b = tabs[s][c][2 * x], tabs[s][c][2 * x + 1]
                        term = poly_mul(term, [a, a + b])  # (1+Y) a + Y b
                    acc = poly_add(acc, term)
                h = poly_add(h, [lam**s * co for co in acc])
            h = h + [ZERO] * (width + 1 - len(h))
            stream += h[1:]  # c0 is derived by the verifier from the running claim
            r = point[j]
            if cheating_here:
                derived0 = claim + r * E.sum(h[1:])
                hh = [derived0] + h[1:]
            else:
                hh = h
                assert h[0] + r * E.sum(h[1:]) == claim, "honest round identity"
            chi = t.sample()
            chis.append(chi)
            claim = pv.poly_eval(hh, chi)
            for s in range(3):
                for c in range(width):
                    tb = tabs[s][c]
                    tabs[s][c] = [tb[2 * x] + chi * (tb[2 * x] + tb[2 * x + 1]) for x in range(half)]
        children = [[tabs[s][c][0] for c in range(width)] for s in range(3)]
        if lie_root is not None and layer != skip_layer and cheating_here:
            # pass this layer's check with a false claim: solve the one equation for one child
            p1 = reduce(mul, children[1])
            p2 = reduce(mul, children[2])
            need0 = claim + lam * p1 + lam * lam * p2
            children[0] = [need0] + [ONE] * (width - 1)
        for s in range(3):
            stream += children[s]
        y = t.samples(step)
        values = [pv.multilinear_eval(ch, y) for ch in children]
        lam = t.sample()
        point = [*y, *chis]
        layer -= step
    return stream, roots


def rand_e(rng):
    return E(rng.getrandbits(64), rng.getrandbits(64), rng.getrandbits(64))


def honest_run(mu, seed):
    rng = random.Random(1000 + seed)
    push = [rand_e(rng) for _ in range(1 << mu)]
    pull = push[:]
    rng.shuffle(pull)  # the same multiset: the bus balances
    cnt = [rand_e(rng) for _ in range(1 << mu)]
    stream, roots = prove([push, pull, cnt], mu, seed)
    t = FakeTranscript(stream, seed)
    root_c, point, values = pv.verify_gkr_grand_products(mu, t)
    assert t.stream_offset == len(stream)
    assert root_c == roots[2]
    for leaves, v in zip([push, pull, cnt], values):
        assert v == pv.multilinear_eval(leaves, point), "leaf claim is the extension at zeta"
    return True


def verify_without_layer_check(depth, transcript, skipped):
    """`verify_gkr_grand_products` of the pinned verifier, verbatim, with the check of one layer removed."""
    shared, count_ = transcript.next_scalar(), transcript.next_scalar()
    combiner = transcript.sample()
    point = []
    values = (shared, shared, count_)
    layer = depth
    while layer > 0:
        step = 1 if layer % 2 else 2
        claim = pv.poly_eval(values, combiner)
        x, claim = pv.sumcheck(transcript, claim, 2**step + 1, point)
        children = [transcript.next_scalars(2**step) for _ in range(3)]
        products = [reduce(mul, child) for child in children]
        if layer != skipped:
            pv.require(claim == pv.poly_eval(products, combiner), f"GKR layer {layer}")
        y = transcript.samples(step)
        values = [pv.multilinear_eval(child, y) for child in children]
        combiner = transcript.sample()
        point = [*y, *x]
        layer -= step
    return count_, tuple(point), (values[0], values[1], values[2])


def attack(mu, skipped, seed):
    """An UNBALANCED bus: the pull tree is not a permutation of the push tree."""
    rng = random.Random(2000 + seed)
    push = [rand_e(rng) for _ in range(1 << mu)]
    pull = [rand_e(rng) for _ in range(1 << mu)]
    cnt = [rand_e(rng) for _ in range(1 << mu)]
    lie = rand_e(rng)
    stream, roots = prove([push, pull, cnt], mu, seed, skip_layer=skipped, lie_root=lie)
    assert roots[0] != roots[1]
    # the full verifier rejects
    try:
        pv.verify_gkr_grand_products(mu, FakeTranscript(stream, seed))
        full = "ACCEPTED"
    except pv.VerificationError as e:
        full = f"rejected ({e})"
    # the verifier without the check of layer `skipped` accepts, with TRUE leaf claims
    t = FakeTranscript(stream, seed)
    _, point, values = verify_without_layer_check(mu, t, skipped)
    true_leaf = all(v == pv.multilinear_eval(lv, point) for lv, v in zip([push, pull, cnt], values))
    return full, true_leaf


if __name__ == "__main__":
    print("mu  scalars(read) formula  challenges formula  zeta_k = draw number (0-based, draws of the GKR only)")
    for mu in range(0, 13):
        s, c, where = count(mu)
        assert s == scalars_formula(mu), (mu, s, scalars_formula(mu))
        assert c == challenges_formula(mu), (mu, c, challenges_formula(mu))
        print(f"{mu:2d}  {s:6d} {scalars_formula(mu):8d}  {c:6d} {challenges_formula(mu):8d}   {where}   total draws {c}")
    for mu in range(1, 6):
        for seed in range(2):
            honest_run(mu, seed)
    print("honest prover: accepted by the pinned verifier for mu = 1..5; leaf values = extensions at zeta")
    for mu, skipped in [(4, 4), (4, 2), (5, 5), (5, 4), (5, 2)]:
        full, true_leaf = attack(mu, skipped, seed=7)
        print(f"unbalanced bus, mu={mu}, check of layer {skipped} removed: full verifier {full}; "
              f"weakened verifier accepts, leaf claims true: {true_leaf}")
```

Output (exit status 0). The scalar counts include the two roots.

```text
mu  scalars(read) formula  challenges formula  zeta_k = draw number (0-based, draws of the GKR only)
 0       2        2       1        1   []   total draws 1
 1       8        8       3        3   [1]   total draws 3
 2      14       14       4        4   [1, 2]   total draws 4
 3      24       24       7        7   [4, 5, 3]   total draws 7
 4      34       34       9        9   [6, 7, 4, 5]   total draws 9
 5      48       48      13       13   [10, 11, 7, 8, 9]   total draws 13
 6      62       62      16       16   [13, 14, 9, 10, 11, 12]   total draws 16
 7      80       80      21       21   [18, 19, 13, 14, 15, 16, 17]   total draws 21
 8      98       98      25       25   [22, 23, 16, 17, 18, 19, 20, 21]   total draws 25
 9     120      120      31       31   [28, 29, 21, 22, 23, 24, 25, 26, 27]   total draws 31
10     142      142      36       36   [33, 34, 25, 26, 27, 28, 29, 30, 31, 32]   total draws 36
11     168      168      43       43   [40, 41, 31, 32, 33, 34, 35, 36, 37, 38, 39]   total draws 43
12     194      194      49       49   [46, 47, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45]   total draws 49
honest prover: accepted by the pinned verifier for mu = 1..5; leaf values = extensions at zeta
unbalanced bus, mu=4, check of layer 4 removed: full verifier rejected (GKR layer 4: children do not match the sumcheck); weakened verifier accepts, leaf claims true: True
unbalanced bus, mu=4, check of layer 2 removed: full verifier rejected (GKR layer 2: children do not match the sumcheck); weakened verifier accepts, leaf claims true: True
unbalanced bus, mu=5, check of layer 5 removed: full verifier rejected (GKR layer 5: children do not match the sumcheck); weakened verifier accepts, leaf claims true: True
unbalanced bus, mu=5, check of layer 4 removed: full verifier rejected (GKR layer 4: children do not match the sumcheck); weakened verifier accepts, leaf claims true: True
unbalanced bus, mu=5, check of layer 2 removed: full verifier rejected (GKR layer 2: children do not match the sumcheck); weakened verifier accepts, leaf claims true: True
```

What it supports: the counts of A.3; the last draw unused and the order of `ζ` (A.4, G2); the
normalized reading of the round (G1), since a prover that sends the cofactor's coefficients
`c_1 … c_4` is accepted and its leaf values are the extensions of the leaves at the returned
point, low bit first; the attack of B14. Limits: the challenges are not the BLAKE2s chain's;
the Rust verifier was read, not run.

### H.2 Three instances on the spine

Command, from the root of leanerVM (`main` at `b435631`, built by the orchestrator):

```sh
flock .claude/reports/blueprint-review/logs/lean.lock \
  lake env lean .claude/reports/blueprint-review/probes/gt-bus/BusSeam.lean
```

Output: none, exit status 0. A control copy with the false guard
`#guard M3Holds Probe.flushless () Probe.notBits` appended fails with "did not evaluate to
`true`", and `#print axioms Probe.x0_degree` gives `[propext, Classical.choice, Quot.sound]`:
the guards are live.

Source, `BusSeam.lean`:

```lean
import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Protocol.Spine.Compose

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Toy CompPoly CPoly

namespace Probe

instance {I : M3Instance} (q : Column I.μ) (c : LinearClaim I) : Decidable (c.Holds q) :=
  inferInstanceAs (Decidable ((c.terms.map fun t ↦ t.eval q).sum = c.value))

/-- The count column as a polynomial of a row of width one has total degree above zero. -/
theorem x0_degree : ¬ ((CMvPolynomial.X 0 : CMvPolynomial 1 K).totalDegree ≤ 0) := by
  decide +kernel

/-- The Boolean constraint on a row of width one has total degree at most two. -/
theorem bool_degree : (CMvPolynomial.X 0 * CMvPolynomial.X 0 - CMvPolynomial.X 0 :
    CMvPolynomial 1 K).totalDegree ≤ 2 := by
  decide +kernel

/-! ## 1. Degree bound zero with a count column -/

abbrev countOnly : M3Instance where
  toShape := ⟨1, fun _ ↦ 1, fun _ ↦ 1⟩
  Stmt := Unit
  constraints := fun _ ↦ []
  flushes := fun _ ↦ []
  d := 0
  constraints_degree := fun _ _ h ↦ absurd h List.not_mem_nil
  flushes_degree := fun _ _ h ↦ absurd h List.not_mem_nil
  counts := fun _ ↦ [0]
  boundary := []
  μ := 1
  layout := ⟨fun q _ ↦ q, fun _ z ↦ z, fun _ _ _ ↦ rfl⟩
  publicLines := fun _ ↦ []
  aux := fun _ ↦ True
  decAux := fun _ ↦ inferInstance

def ones : Column 1 := ⟨#v[1, 1]⟩

#guard M3Holds countOnly () ones

/-- The count form's one polynomial, the count column itself, is above the bound. -/
example : ¬ ((CMvPolynomial.X 0 : CMvPolynomial 1 K).totalDegree ≤ countOnly.d) := x0_degree

/-- So a bus statement carrying the count form is outside the bus seam. -/
example (w v : E) (p : Vector E 1) (o : ∀ i, TheOracle countOnly i) :
    ((((), (⟨[⟨[⟨w, 0, CMvPolynomial.X 0, p⟩], v⟩], []⟩ : BusOut countOnly)), o), ()) ∉
      Seam.bus countOnly := fun h ↦
  absurd (h.2.1 _ (List.mem_singleton_self _) _ (List.mem_singleton_self _)) x0_degree

/-! ## 2. A constraint on a table that is not on the bus -/

abbrev flushless : M3Instance where
  toShape := ⟨1, fun _ ↦ 2, fun _ ↦ 1⟩
  Stmt := Unit
  constraints := fun _ ↦ [CMvPolynomial.X 0 * CMvPolynomial.X 0 - CMvPolynomial.X 0]
  flushes := fun _ ↦ []
  d := 2
  constraints_degree := fun _ C h ↦ by rw [List.mem_singleton.mp h]; exact bool_degree
  flushes_degree := fun _ _ h ↦ absurd h List.not_mem_nil
  counts := fun _ ↦ []
  boundary := []
  μ := 2
  layout := ⟨fun q _ ↦ q, fun _ z ↦ z, fun _ _ _ ↦ rfl⟩
  publicLines := fun _ ↦ []
  aux := fun _ ↦ True
  decAux := fun _ ↦ inferInstance

def bits : Column 2 := ⟨#v[0, 1, 1, 0]⟩
def notBits : Column 2 := ⟨#v[0, 1, 2, 0]⟩

#guard M3Holds flushless () bits
#guard ¬ M3Holds flushless () notBits
-- No tuple on either side, no count cell: the three trees of the bus are empty.
#guard (flushless.tuples bits .push).length = 0
#guard (flushless.tuples bits .pull).length = 0
#guard (flushless.counts 0).length = 0

/-! ## 3. The bus seam does not tie the points of its claims together -/

def pointA : Vector E 1 := #v[y]
def pointB : Vector E 1 := #v[y + 1]

/-- The toy's zerocheck claim, at `pointA`. -/
def zeroA : LinearClaim toy :=
  ⟨[⟨1, 0, CMvPolynomial.X 2 * CMvPolynomial.X 2 - CMvPolynomial.X 2, pointA⟩], 0⟩

/-- The same claim at another point. -/
def zeroB : LinearClaim toy :=
  ⟨[⟨1, 0, CMvPolynomial.X 2 * CMvPolynomial.X 2 - CMvPolynomial.X 2, pointB⟩], 0⟩

#guard pointA.toList ≠ pointB.toList
#guard zeroA.Holds honest
#guard zeroB.Holds honest

/-- Both claims, at their two points, are one statement of the bus seam. -/
example (h : toy.PublicLinesHold (1 : K) honest) (hA : zeroA.Holds honest)
    (hB : zeroB.Holds honest) :
    ((((1 : K), (⟨[zeroA, zeroB], []⟩ : BusOut toy)), fun _ ↦ honest), ()) ∈ Seam.bus toy := by
  refine ⟨?_, ?_, ?_, h, trivial⟩
  · intro c hc
    rcases List.mem_pair.mp hc with rfl | rfl
    · exact hA
    · exact hB
  · intro c hc t ht
    rcases List.mem_pair.mp hc with rfl | rfl <;>
      (rw [List.mem_singleton.mp ht]; decide +kernel)
  · intro c hc
    exact absurd hc List.not_mem_nil

#guard toy.PublicLinesHold (1 : K) honest

end Probe
```

What it supports: G10 (parts 1 and 2) and E.4 (part 3). What it does not: that no bus phase at
all serves `countOnly` (one with a single count block could emit a column claim); the finding
is about the phase of the deployed shape.

---

## I. Not done, unverified, and contradictions with the brief

- **Not run**: the Rust verifier and prover (read only). The equality of the Rust and Python
  verdicts on these phases is by reading both, line by line, not by a differential test; the
  repository's own tests compare them (`docs/leanvm-target.md:66`).
- **Unverified**: the attack of B7 (the `BLAKE2S` floor); the claim under B3 that the
  public-input phase rejects a public word with a nonzero third limb; the numbering of the
  specification's theorem-like environments (taken from the blueprint's usage, consistent with
  the order of the environments in the tex; the class file was not read).
- **Not examined**: Fiat–Shamir beyond the order of absorption and squeezing; the opening; the
  table sumcheck beyond what the seam needs; the recursion guest.
- **The brief**, §7, says the Python verifier's behaviour on the caps is as the status states
  nowhere explicitly; but the task asks to re-verify "the Python verifier omitting four caps",
  and that finding is false (G5). The brief's statement that the round-by-round theorem is in
  §3 of the specification does not hold: it is in Annex B (`B:139-152`) and is about the
  opening only (D.1).
