# Verification of dossier gt-flock-ring: citations and quotations checked against the sources

Task: verify-gt-flock-ring. Dossier under check:
`.claude/reports/blueprint-review/dossiers/gt-flock-ring.md` (1172 lines, read-only).
Ground truth: leanVM at `a386121f` (`/home/scaraven/Documents/leanEthereum/leanVM`); leanerVM
tracked files as `main` at `b435631`; ArkLib pin `dca90385` in `.lake/packages/Arklib/`.

Revisions: the leanerVM checkout now contains `main` at `144c5aa` (brief §8); every leanerVM file
was read at `b435631` with `git show`, every ArkLib file at `dca90385` with `git show` in
`.lake/packages/Arklib` (now checked out at `7653a901`). leanVM unchanged at `a386121f`.

## 1. Summary

**Checked**: every citation of sections 8, 4, 3, 2, 5, 6 and 7 of the dossier (and the few in
section 10 that overlap them): about **381 citations** (348 inline `file:line` citations, 13
code-block headers, about 20 citations of issue #3, the tracker's hole comment, `AGENTS.md`,
commits and repository searches). Each was opened at the cited lines; quotations were compared
verbatim; claims were compared with what the source says there.

| Verdict | Count |
| --- | --- |
| `OK` | 375 |
| `WRONG LINE` | 1 |
| `MISQUOTED` | 3 |
| `NOT SUPPORTED` | 2 |
| `COULD NOT CHECK` | 0 |

**Every citation that is not `OK`, with its correction:**

1. Dossier line 296, code block header `ArkLib/OracleReduction/Security/Basic.lean:101-104
   (ArkLib dca90385)`: **WRONG LINE**. The quoted docstring and `def perfectCompleteness` are
   lines **102-105** at `dca90385` (100-103 at `7653a901`). Text verbatim.
2. Line 164, `cpu/mod.rs:790-814`, quoted as `` `SlotClaim::Strided { offset, slot, stride_log:
   SLOT_STRIDE_LOG, point, value }` ``: **MISQUOTED** (abbreviated). Actual, lines 799-805:
   `pcs::SlotClaim::Strided { offset: l.placements[QFLOCK].offset, slot, stride_log:
   crate::hash_flock::SLOT_STRIDE_LOG, point: c.point.clone(), value: c.value, }`.
3. Line 166, `verifier.py:1405` quoted as `` `verify_flock(log_n, transcript)` ``: **MISQUOTED**.
   Line 1405 is `verify_flock(BLAKE2S_R1CS_LOG_SIZE + layout.table_log_heights[OP_BLAKE2S],
   transcript)`; `verify_flock(log_n: int, transcript: Transcript)` is the signature at `:1304`.
4. Line 949, `cpu/mod.rs:568-570` said to read "bytecode binds the counter and flags":
   **MISQUOTED**. Lines 568-570 read "…counter and flags bind through bytecode"; the quoted
   words are at `:619-620` only (the second citation on that line, which is `OK`).
5. Line 116, `c-flock:18` for "`a = Az` and `b = Bz` are never committed and never opened: only
   `z` is": **NOT SUPPORTED**. Line 18 only defines `a`, `b`, `c = z`; the commitment of `z`
   alone is `c-flock:30` (and, in the Rust, `cpu/mod.rs:560-562`).
6. Line 116, `hash.rs:592-593` for the same claim: **NOT SUPPORTED** (partial). The quotation
   "No c buffer. Since `C = I`, `c == z`" is verbatim, but it supports only `c = z`.

None of the six changes a conclusion or a finding of the dossier.

**Independent checks (section 3): all eight agree with the dossier.** The Flock verifier reads no
pooled claim and the 18 limb claims go to the opening as strided `q_flock` claims; the reduction
has one rejecting equality (the lincheck terminal identity), every other value is derived; the
only challenge-dependent `.inv()` in the searched code is the prover's `(F192::ONE +
r_eq).inv()` (`zerocheck.rs:117`), and `ZERO.inv() == ZERO` by contract and by construction;
the verifier derives the missing coefficient by a multiplication; the stream count is `162 +
2·k_batch` (and `2·k_batch + 25` challenges); ring switching sends nothing, checks nothing and
draws six challenges; Annex C requires position 512 of every block to be 1 and the blueprint
never mentions it; ArkLib's `RingSwitching/Packing/` has 14 `sorry` at `dca90385` (4, 8, 2),
the same at `7653a901`. Both Python probes of the dossier were rerun and reproduce its outputs.

**Doubtful points that are not citation errors (section 4)**, the ones that matter: the
dossier's sentence "The verifiers take no inverse" (line 227, and conclusion 3) is literally
false, since both verifiers invert constants (it should say "no inverse of a challenge-dependent
value", as its proposed acceptance test 20 already does); its inverse inventory omits
`pcs/src/ntt/additive_ntt_f64.rs:26` (a constant); ArkLib's composition of completeness errors
carries side hypotheses the dossier's option table omits; the Rust calls the `τ_BLAKE2S ≥ 3`
floor "the lincheck floor" (`hash.rs:281-282`), which the dossier's "the mathematics needs no
floor" does not address; the dossier's head names `dca90385` "the pin", which is now the old pin.


## 2. Table of rows (filled as checked; the summary in section 1 is written last)

Column "L" is the dossier's line. Verdicts: `OK`, `WRONG LINE`, `MISQUOTED`, `NOT SUPPORTED`,
`COULD NOT CHECK`. Paths: spec files under `doc/leanvm/body/`, Rust under `crates/`.

### 2.1 Specification citations

| L | Citation | Claim | Verdict |
| --- | --- | --- | --- |
| 111 | `c-flock:30` | "The resulting multilinear $\qflock$ … is committed as one region of the stack" | OK (verbatim with ellipsis) |
| 111 | `08:60` | `q_flock` stacked into `q` | OK |
| 112 | `a-ring:13-16` | `q_flock(u) = Σ_i Q_i(u) x^i` | OK (formula at :15) |
| 113 | `c-flock:264` | "the PCS proves the claims opened on $\qflock$" | OK (verbatim) |
| 116 | `c-flock:18` | `a`, `b` never committed or opened, only `z` | NOT SUPPORTED as cited: `:18` only defines `a=Az`, `b=Bz`, `c=Cz=z`; it says nothing about what is committed. That only `z` is committed is `c-flock:30` ("The prover commits to $z$ by packing …") |
| 125 | `c-flock:54` | fixed coordinates; "where $g_0\in\E$ is public" | OK (verbatim) |
| 126 | `c-flock:55`, `:173` | remaining coordinates sampled | OK |
| 127 | `c-flock:62` | "The prover sends $P\|_{\skipcoset}$, $64$ values" | OK (verbatim; `\|` is Markdown escaping) |
| 128 | `c-flock:64` | `z_skip` sampled | OK |
| 129 | `c-flock:62-67` | `v_P` from 64 values and 64 assumed zeros | OK |
| 130 | `c-flock:69`; `03:110` | "with Gruen's eq-factor optimization"; round check pins one coefficient | OK (verbatim) |
| 131 | `c-flock:69-73` | "is what *defines* $v_c$: both sides solve it rather than transmit it" | OK (verbatim, `\emph` rendered as italics) |
| 132 | `c-flock:112-118` | `α_lc` and the target with `α³` | OK |
| 133 | `c-flock:122` | 8 rounds, challenges in reverse order | OK |
| 134 | `c-flock:124` | `s_0..s_63` sent | OK |
| 135 | `c-flock:126-133`, `:150` | terminal identity; its matrix and `c` terms | OK |
| 136 | `a-ring:104`; `08:91` | six challenges `f_0..f_5`; ring switching is BLAKE2s validity step 2 | OK |
| 137 | `a-ring:44-46`, `:104-110` | target `T = Σ x^i Φ(s_i)`, weight `Φ(eq(r,u))` | OK |
| 138 | `08:98` | `λ`, ring-switched claim first | OK |
| 139 | `a-ring:150-154` | boxed closed form of `W̃(r')` | OK |
| 146 | `08:91` | "BLAKE2s validity, step 2" | OK |
| 163 | `08:77` | "The prover sends one value per column of every table" | OK (verbatim) |
| 164 | `08:77`; `07:122`; `04:10-18` | "their claims route there"; limbs committed in `q_flock`; §4.1 aligned blocks only | OK (verbatim; §4.1 indeed has only aligned high-index selection) |
| 166 | `c-flock:170-179` | the protocol summary has no input claim | OK |
| 167 | `08:97-99` | pooled claims enter the batch | OK |
| 180 | `c-flock:131` | `s_0·eq(χ'_in, 8)` | OK |
| 184 | `a-ring:104-117` | stages and coefficients | OK |
| 203 | `c-flock:126-133`; `:270` | "it is the only thing that checks anything" | OK (verbatim) |
| 204 | `c-flock:62` | zeros assumed on `H` | OK |
| 205 | `03:110`, `c-flock:69` | `c_0` derived | OK |
| 206 | `c-flock:70-73` | `v_c` defined | OK |
| 207 | `c-flock:23-28`, `:112-118`, `:131` | the constant position and `α³` | OK |
| 208 | `03:110` | `c_1` derived (round check) | OK |
| 209 | `a-ring:45` | verifier computes `T` | OK |
| 210 | `08:98-99` | the weighted claim enters the batch | OK |
| 211 | `08:77, 97` | limb claims enter the batch | OK |
| 212 | `06-bus-interactions.tex:80` | caps only, floor absent | OK (line 80 has the caps; `grep` of all of `doc/leanvm/body/` finds no floor on `τ_BLAKE2S`) |
| 213 | `08:100` | stream consumed "(implicit)" | OK (line 100 lists the checks; nothing about trailing data, as the dossier says) |
| 217 | `03:95-100`; `c-flock:278` | partially fixed zerocheck; used for the fixed coordinates | OK |
| 281 | `c-flock:69`, `03:110` | the specification never mentions an inverse | OK (`grep -i 'inver\|\^{-1}\|inv'` on `c-flock`, `03`, `a-ring` returns nothing) |
| 430 | `c-flock:280-284` | `(16+3+k_batch+(n_flock−7)+127+2n_flock)/\|E\| = (4k_batch+163)/\|E\|` | OK |
| 436 | `03:95-100`, `c-flock:278` | `(n_flock−7)/\|E\|` | OK |
| 437 | `c-flock:278` | `127/\|E\|` | OK |
| 439 | `c-flock:274` | `k_batch/\|E\|` for the constant position | OK |
| 440 | `c-flock:272-274` | degree 3 in `α_lc`, `3/\|E\|` | OK |
| 441 | `c-flock:270` | `16/\|E\|` for 8 quadratic rounds | OK |
| 442 | `a-ring:120-128` | degree `< 2^32` | OK |
| 447 | `a-ring:80-96` | 64 distinct conjugates of `x`; `{1, y^{2^k}, y^{2^{k+1}}}` a `K`-basis | OK (basis at :88, conjugates at :96) |
| 448 | `a-ring:118` | 64 distinct monomials `c_k` | OK |
| 459 | `c-flock:8-21` | R1CS, `A = I⊗A_0`, `C = I` | OK |
| 460 | `c-flock:23-28` | `z(512, t) = 1` | OK |
| 461 | `c-flock:187-218` | definition of a circuit; row sets | OK |
| 462 | `c-flock:150` | "896 free inputs, the constant, 256 committed ⊕ wires …, and 14,720 ∧ wires" | OK (verbatim with ellipsis) |
| 463 | `c-flock:30`, `a-ring:13-16` | packing | OK |
| 464 | `07:120` | names the eighteen limbs | OK |
| 535 | `08:77` | routing stated, selector not | OK |
| 558 | `a-ring:30-47, 104-110` | the reduction and the map | OK |
| 559 | `a-ring:33-41` | completeness identity | OK |
| 561 | `a-ring:120-128` | `2^32/2^192 = 2^{-160}` | OK |
| 562 | `a-ring:150-154` | closed form | OK |
| 572 | `04:26-28` | "Committing to booleans via Ring-Switching" | OK (section title at :26) |
| 573 | `a-ring:4` | "transforming a PCS for $\K$ into a PCS for $\Ftwo$" | OK (verbatim) |
| 582 | `03:117` | "The commitment is over $\K$, the opening over $\E$. An evaluation claim $\mle{g}(r)=c$ is the case $W=\eq(r,\cdot)$" | OK (verbatim) |
| 584 | `b-polynomial-commitment-scheme.tex:125` | "At level $0$ that summand pairs an $\E$-valued weight with the $\K$-valued $f$; every later level is $\E$ throughout." | OK (verbatim) |
| 825 | `c-flock:23-28` | "We also enforce the position $512$ of every block to be $1$ (preventing the all-zero witness)" | OK (verbatim, line 23) |
| 848 | `c-flock:54` | `g_0` "is public" | OK |
| 849 | `c-flock:35` | `φ_8` named without choice of embedding or modulus | OK (line 35: "the subfield embedding, with a byte interpreted in the polynomial basis"; no modulus given) |
| 851 | `06-bus-interactions.tex:80` | caps only | OK |
| 852 | `08:77` | "live in $\qflock$, not the stack" | OK (verbatim) |
| 866 | `c-flock:282` | `< 2^{-183}` | OK |
| 930 | `b-polynomial-commitment-scheme.tex:4`; `c-flock:264` | list binding only; "The commitment determines $\qflock$" | OK (line 4: "so our PCS is only list binding"; :264 verbatim) |
| 940 | `08:55` | "Flock's BLAKE2s R1CS matrices" | OK (verbatim) |
| 951 | `07:120, 135` | the bus binds the metadata | OK (:120 "the memory interactions via the bus bind all four"; :135 the metadata read) |
| 961 | `a-ring:150-154` | the boxed identity | OK |

### 2.2 Rust and Python citations (leanVM `a386121f`)

`hash.rs` is `crates/flock/src/hash.rs` throughout. `multilinear.rs` is ambiguous in the dossier:
at lines 204 and 437 it means `crates/flock/src/zerocheck/multilinear.rs` (the only file where
those lines fit), at line 244 `crates/primitives/src/multilinear.rs`. Both readings were checked.

| L | Citation | Claim | Verdict |
| --- | --- | --- | --- |
| 111 | `hash_flock.rs:3-5` | "committed as a column in leanVM's ONE stacked `F64` witness …, with no separate flock commitment" | OK (verbatim with ellipsis) |
| 111 | `cpu/layout.rs:25` | `QFLOCK = 5` | OK |
| 111 | `verifier.py:633`, `:879-880` | `QFLOCK` column; its log size | OK |
| 112 | `pcs/src/pack.rs:1-2` | "least significant bit first" | OK (line 2) |
| 112 | `hash_flock.rs:187-197` | bit `i` at position `i`, word for word | OK |
| 113 | `flock/src/lib.rs:6-13` | `q_flock` inside the one stacked commitment | OK |
| 113 | `cpu/mod.rs:564-571` | single PCS, `q_flock` always a column of `w.q` | OK |
| 113 | `verifier.py:1404-1413` | no other oracle | OK |
| 116 | `hash.rs:592-593` | "No c buffer. Since `C = I`, `c == z`" | NOT SUPPORTED (partial): the quotation is verbatim (bold markers dropped), but it supports `c = z` only, not "`a`, `b` never committed" (the function at :594 builds `a` and `b` buffers for the prover). The claim is true (the only commitment is `w.q`, `cpu/mod.rs:560-562`), but neither citation on line 116 states it |
| 125 | `zerocheck.rs:51-58`; `univariate_skip_optimized.rs:65, 79-101`; `:104-106` | fixed coordinates; `g_0` | OK |
| 125 | `verifier.py:1095-1100` | `FIXED_CHALLENGES` | OK |
| 126 | `zerocheck.rs:362` | `equality_tail(m, \|n\| vs.sample_vec(n))` | OK (verbatim) |
| 126 | `verifier.py:1139` | sampled coordinates | OK |
| 127 | `zerocheck.rs:365`; prover `:185-187`; `verifier.py:1142` | 64 values | OK |
| 128 | `zerocheck.rs:366`; `verifier.py:1143` | `z_skip` | OK |
| 129 | `zerocheck.rs:378`; `zerocheck/multilinear.rs:129-138`; `verifier.py:1144` | `v_P` with 64 assumed zeros | OK |
| 130 | `zerocheck.rs:397-405`; `fiat_shamir/src/transcript.rs:289-309`; prover `zerocheck.rs:116-123` | `n_flock` rounds, `c_0` derived | OK |
| 130 | `verifier.py:1147`, `:406-413`, `:420-427` | same in Python | OK |
| 131 | `zerocheck.rs:421-423`; `verifier.py:1148-1149` | `v_c := R_zc + v_a·v_b` | OK |
| 132 | `lincheck.rs:1179`, `:1199-1203`; `verifier.py:1155`, `:1162` | `α`, target with `α³` | OK |
| 133 | `lincheck.rs:1205-1211`, `:1218-1219`, prover `:1085-1107`; `verifier.py:1163`, `:1169` | 8 rounds, `c_0, c_2` sent, reversal | OK |
| 134 | `lincheck.rs:1214`, prover `:1113-1115`; `verifier.py:1168` | `s_0..s_63` | OK |
| 135 | `lincheck.rs:1233-1256`; `cpu/mod.rs:765`; `hash.rs:361-389` | terminal identity, `ConsistencyFailed`, `CpuError::Blake2s`, `bilinear_walk` | OK (`WalkLincheckCircuit::bilinear_form` returns `Some(bilinear_walk(alpha, u, w))`, `hash.rs:566-567`) |
| 135 | `verifier.py:1170-1176`, `:1180-1301` | `require(terminal == r_lc, …)`; matrix term | OK |
| 136 | `stack_open.rs:513`; `ring_switch.rs:160-162`; `verifier.py:1343` | six challenges | OK |
| 137 | `stack_open.rs:521-524`; `ring_switch.rs:555-557`; `tensor_algebra.rs:42-71`; `ring_switch.rs:133-144`; `verifier.py:1345-1347` | the target | OK |
| 138 | `stack_open.rs:518-527`; `verifier.py:1361`, `:1413` | `λ`, ring-switched claim first | OK |
| 139 | `stack_open.rs:530-546`; `ring_switch.rs:597-617`; `verifier.py:1324-1335`, `:1412` | weight evaluation | OK |
| 141 | `reduction_tests.rs:166-168` | stream count | OK (gives the zerocheck part `ell + 2·n_mlv + 2`; the lincheck part `2·8 + 64` is implicit at :169, :177) |
| 155 | `stack_open.rs:113-116` | "this layer reads nothing off the stream" | OK (verbatim, line 115) |
| 163 | `cpu/mod.rs:428-441` | `for c in 0..table.n_committed_columns()` | OK (verbatim, line 432) |
| 163 | `tables.rs:866-868`, `:862` | 37 columns for `BLAKE2S` | OK (`N = 37`) |
| 163 | `verifier.py:620`, `:827-834` | `table.width`; the BLAKE2S columns | OK |
| 164 | `cpu/mod.rs:790-814` | `SlotClaim::Strided { offset, slot, stride_log: SLOT_STRIDE_LOG, point, value }` | MISQUOTED (abbreviated; substance right). Actual, lines 799-805: `pcs::SlotClaim::Strided { offset: l.placements[QFLOCK].offset, slot, stride_log: crate::hash_flock::SLOT_STRIDE_LOG, point: c.point.clone(), value: c.value, }` |
| 164 | `stack_open.rs:84-97`, `:305-323`; `hash_flock.rs:223` | strided claim; `SLOT_STRIDE_LOG = K_LOG − LOG_PACKING` | OK |
| 164 | `verifier.py:884-894`, `:295-302` | `Placement(kappa, offsets[QFLOCK] + limbs[column], QFLOCK_SLOT_BITS)` | OK (verbatim, line 892) |
| 165 | `hash_flock.rs:87-115`; `verifier.py:847-850` | slot map: `cv` 0..3, `out` 4..7, message 10..17, metadata 18, 19 | OK (both) |
| 166 | `cpu/mod.rs:765`; `hash_flock.rs:282-284` | `verify_reduction(n_blocks, &mut vs)` | OK |
| 166 | `verifier.py:1405` | `verify_flock(log_n, transcript)` | MISQUOTED: line 1405 reads `verify_flock(BLAKE2S_R1CS_LOG_SIZE + layout.table_log_heights[OP_BLAKE2S], transcript)`; `verify_flock(log_n: int, transcript: Transcript)` is the signature at `:1304`. Substance right |
| 167 | `cpu/mod.rs:756, 768`; `stack_open.rs:525-527`; `verifier.py:1395, 1413` | limb claims in the batch | OK |
| 173 | `stack_open.rs:41-48`; `verifier.py:1412` | the selector lift | OK |
| 178 | `transcript.rs:293-307` | reads, then binds in index order | OK |
| 179 | `verifier.py:409-413` | binds as it reads | OK |
| 180-181 | `lincheck.rs:1240` with `hash.rs:146`; `verifier.py:1174` with `:642` | constant position 512 | OK |
| 182 | `lincheck.rs:832-837, 1234`; `verifier.py:1159, 1170` | row and column weight layouts | OK |
| 183 | `hash.rs:295-359` with `gf2.rs:109-154`; `verifier.py:1180-1295` | the walks; offsets 0, 61, 92, 153 | OK (`G_ADD_C1 = 61`, `G_ADD3_A2 = 92`, `G_ADD_C2 = 153` by `hash.rs:159-162` with `gf2.rs:26-31`; Python `gate_base + 61/92/153`, lines 1276-1280) |
| 185 | `ring_switch.rs:85, 147-156`; `verifier.py:1314-1321, 1345` | stages and coefficients | OK |
| 187 | `ring_switch.rs:683-705` | the Rust tests the equality of the two target forms | OK |
| 203 | `lincheck.rs:1252-1256`; `verifier.py:1176` | the check | OK |
| 204 | `multilinear.rs:133-137` (zerocheck) ; `verifier.py:1144` | zeros assumed | OK (file name ambiguous, see head of this table) |
| 205 | `transcript.rs:296-302`; `verifier.py:411-413` | `c_0` derived | OK |
| 206 | `zerocheck.rs:423`; `verifier.py:1149` | `v_c` derived | OK |
| 207 | `lincheck.rs:1202, 1240`; `verifier.py:1162, 1174` | the `α³` term | OK |
| 207 | `hash.rs:1176-1183` | "homogeneous rows accept zero without the pin" | OK (verbatim, line 1180) |
| 208 | `transcript.rs:298-299`; `verifier.py:409-410` | `c_1` derived | OK |
| 209-210 | `stack_open.rs:522-524`; `verifier.py:1346`, `:1413` | `T` computed; weighted claim in the batch | OK |
| 211 | `cpu/mod.rs:798-806`; `stack_open.rs:525-527`; `verifier.py:892, 1413` | limb claims in the batch | OK |
| 212 | `cpu/mod.rs:161-166`; `verifier.py:860-861` | cap 32 (`MAX_LOG_ROWS = 32`, `cpu/mod.rs:60`) and floor | OK |
| 212 | `hash.rs:283-286` | at least `2^3` blocks | OK |
| 212 | `zerocheck.rs:354` | the zerocheck needs `k_bool ≥ 13` | OK (`m < K_SKIP + N_INNER = 13` rejected; `m = K_LOG + n_blocks_log`, `hash.rs:728-730`) |
| 213 | `cpu/mod.rs:769`; `verifier.py:1414` | stream consumed | OK |
| 214 | `lincheck.rs:1151-1176`; `zerocheck.rs:354-356`; `hash.rs:990-1008` | shape checks; constants passed | OK |
| 218 | `univariate_skip_optimized.rs:920-960` | unit test of `F_2`-independence | OK (the test runs 920-961) |
| 231-238 | code block `crates/fiat_shamir/src/transcript.rs:297-302` | derivation by multiplication | OK (verbatim) |
| 240 | `verifier.py:411-413` | same | OK |
| 241 | `primitives/src/multilinear.rs:181-186, 194-213` | Lagrange weights divide by a constant only | OK |
| 244 | `univariate_skip_optimized.rs:96-99, 114`; `multilinear.rs:185, 237` (primitives) | constant inverses | OK |
| 245 | `pcs/src/ntt.rs:50`; `whir_induce.rs:112` | domain-point inverses | OK (`ntt.rs:50` a twiddle; `whir_induce.rs:112` inverts `s_k(v_k)`, a function of the size only) |
| 245 | `tables.rs:795, 984`; `cpu/execute.rs` | witness generation | OK (`execute.rs:319, 562, 607`) |
| 251-259 | code block `crates/flock/src/zerocheck.rs:116-123` | `send_round` | OK (verbatim) |
| 262 | `gf2_64x3.rs:137` | "Multiplicative inverse: `self^(2^192 − 2)`. `ZERO.inv() == ZERO`." | OK (verbatim; `crates/primitives/src/field/gf2_64x3.rs`) |
| 270 | `lincheck.rs:1090` | `let mut running = inner_product_ext(&comb_vec, &z_vec)` | OK (verbatim) |
| 436 | `zerocheck.rs:48`, `:47`; `hash.rs:105` | `N_INNER = 7`, `K_SKIP = 6`, `K_LOG = 14` | OK |
| 437 | `multilinear.rs:132-137` (zerocheck) | 128 nodes | OK |
| 438 | `zerocheck.rs:399-401` | `next_round_poly(3, …)` | OK |
| 439 | `hash.rs:146` | `Z_CONST_POS = 512` | OK |
| 440 | `lincheck.rs:1199-1202` | degree 3 in `α` | OK |
| 441 | `hash.rs:992` | `K_LOG − K_SKIP = 8` | OK |
| 442 | `ring_switch.rs:80-81` | `RING_SWITCH_SOUNDNESS_DEGREE` | OK |
| 448 | `ring_switch.rs:711-760` | distinct monomials tested | OK |
| 462 | `hash.rs:40-64`, `:295-359`, `:139-162`; `gf2.rs:109-154`; `verifier.py:1180-1295` | circuit, layout, walks | OK |
| 464 | `hash_flock.rs:82-115`; `verifier.py:845-850` | slot map | OK |
| 465 | `cpu/mod.rs:721, 763`; `verifier.py:1405` | `k_batch = τ_BLAKE2S` | OK |
| 467 | `hash.rs:43-51` | `896 = 256 + 512 + 128` | OK |
| 468 | `hash.rs:123, 129` | `14,720 = 80 × 184` | OK |
| 483 | `hash_flock.rs:119-126` | a limb is two little-endian 32-bit words | OK |
| 485 | `hash.rs:43-53` | wire positions | OK |
| 494 | `gf2.rs:102-122`; `gf2.rs:124-154` | the two adders | OK |
| 499 | `hash.rs:594-684` | the witness generator | OK |
| 512-532 | code block `crates/pcs/src/stack_open.rs:305-323` | strided weight | OK (verbatim) |
| 543 | `phi8_tower.rs:15-24`; `verifier.py:1092` | `φ_8` basis | OK |
| 565-567 | `ring_switch.rs:85, 147-156`, `:555-557`, `:597-617` | same six stages; transposed target; tensor-algebra weight | OK |
| 574 | `stack_open.rs:9-19` | "point claims … plain multilinear evaluations", "ring-switched claims … bit-MLE evaluation claims on the packed sub-block `q_flock`" | OK (verbatim with ellipses) |
| 576 | `cpu/mod.rs:767`; `stack_open.rs:490` | one ring-switched claim; asserted `n_rs > 0` | OK |
| 586 | `lean_vm/src/pcs.rs:24-26` | "The base-field commitment only shrinks the level-0 symbols to 8 bytes; every random ingredient is sampled from `E`" | OK (verbatim) |
| 717 | `cpu/mod.rs:790-814` | limb claims opened as claims on `q_flock` | OK |
| 729 | `hash_flock.rs:96-115` | eighteen numbers | OK |
| 733 | `hash_flock.rs:87-115`; `verifier.py:847-850` | slot map | OK |
| 790 | `transcript.rs:296-302` | `claim + r·(c_1 + … + c_d)` | OK |
| 792 | `zerocheck.rs:116-118` | `G(0) = (claim + r·G(1))·(1 + r)⁻¹` | OK (formula at :117) |
| 827 | `hash.rs:1172-1183` | the all-zero test | OK |
| 845 | `hash.rs:40-64, 139-162, 295-359`; `gf2.rs:23-31, 109-154`; `verifier.py:1180-1295` | circuit fixed by the Rust and Python | OK |
| 846 | `hash_flock.rs:87-115`; `verifier.py:847-850` | slot map | OK |
| 847 | `stack_open.rs:84-97`; `verifier.py:288-302` | the strided selector | OK |
| 848 | `univariate_skip_optimized.rs:104-106`; `verifier.py:1095` | `g_0` | OK |
| 849 | `gf2_8.rs:13`; `phi8_tower.rs:15-24`; `verifier.py:1092` | modulus `x^8+x^4+x^3+x+1`; `φ_8` | OK |
| 850 | `cpu/mod.rs:721, 763`; `verifier.py:1405` | `k_batch = τ_BLAKE2S` | OK |
| 851 | `cpu/mod.rs:162-166`; `hash.rs:283-286`; `verifier.py:861` | the floor | OK |
| 852 | `cpu/layout.rs:17-25` | `q_flock` in the same stack | OK |
| 858-860 | `zerocheck/univariate_skip_optimized.rs:65, 104-106`; `primitives/src/field/phi8_tower.rs:15-24`; `lean_vm/src/hash_flock.rs:87-115`; `verifier.py:847-850, 1092-1100, 1180-1295` | proposed Category B row | OK (all exist and hold what is claimed) |
| 890-900 | code block `python-verifier/verifier.py:857-864` | the caps and the floor in Python | OK (verbatim) |
| 902 | `verifier.py:252-254` | `log2_strict` requires a power of two | OK |
| 903 | commit `14fbca8f` | introduced the caps line; ancestor of the pin | OK (`git log -S'table_log_heights[OP_BLAKE2S] >= 3'` gives `14fbca8f`; `git merge-base --is-ancestor 14fbca8f a386121f` succeeds) |
| 909 | `hash.rs:283-286` | floor of 8 compressions | OK |
| 932-933 | `whir_config.rs:540-541`, `:564-567` | "A degree-`d` identity test unioned over a Johnson list of size `L` fails with probability at most `dL/\|F\|`" | OK (verbatim) |
| 941 | `hash.rs:259-275` | "baked as an opaque constant … That recipe needed the materialized matrices, which this module no longer builds … To recompute it, check out the last commit that still had `build_matrices`" | OK (verbatim with ellipses) |
| 944 | `verifier.py:629` | Python copies the digest bytes | OK |
| 949 | `cpu/mod.rs:568-570` | "bytecode binds the counter and flags" | MISQUOTED: lines 568-570 read "Message, chaining-value, and output words bind through the memory bus; counter and flags bind through bytecode." The quoted words are at `:619-620` only. Substance (a stale comment) right |
| 949 | `cpu/mod.rs:619-621` | "bytecode binds the counter and flags" | OK (lines 619-620) |
| 950 | `tables.rs:904-907` | "The metadata rides the memory bus like every other operand" | OK (verbatim) |
| 960 | `ring_switch.rs:63-66` | the verifier never materializes the weight | OK |

### 2.3 leanerVM citations (read at `b435631` with `git show b435631:<path>`)

The checkout now holds `main` at `144c5aa` merged in (brief §8); every row below was read at
`b435631`, the revision the dossier cites. "bp" is `docs/roadmap/protocol-blueprint.md`.

| L | Citation | Claim | Verdict |
| --- | --- | --- | --- |
| 307-318 | code block `LeanerVM/Protocol/ToArkLib/Component.lean:76-85` | `Component.Complete` | OK (verbatim) |
| 321-326 | code block `Component.lean:90-93` | `Security … extends Complete` | OK (verbatim) |
| 329-332 | code block `Spine/Compose.lean:101-102 and 120-121` | the `flock` fields | OK (the two code lines are 102 and 121; 101 and 120 are their docstrings) |
| 348 | `Component.lean:65-66` | "The knowledge error charged to each challenge" | OK (verbatim) |
| 367-376 | bp `:1075-1086` | the `FlockInterface` sketch | OK (the block reproduces lines 1077-1082 verbatim; it omits the docstring 1075-1076 and the fields 1083-1085, without saying so) |
| 381-388 | code block `Spine/Seams.lean:146-151` | `FlockOut` | OK (verbatim) |
| 391-398 | code block `Seams.lean:183-188` | `Seam.pub`, `Seam.flock` | OK (verbatim) |
| 411-412 | hole comment, section P6 | "`FlockInterface.relIn` carries the strong `aux` … and the eighteen column claims are true of `limbColumns`" | OK (comment 5833669972, lines 105-107 of its body, verbatim with ellipsis; `updated_at` 2026-09-28) |
| 419 | `Instance.lean:73-81` | `Layout`: a reading law, no stacking law | OK (docstring :71-72 "It is a reading law, not a stacking law") |
| 422 | `ToCompPoly/Multilinear.lean:342`; `:50-51` | `evalMle_append_boolVec`; "slicing on the low index is a different, strided selection" | OK (verbatim) |
| 506 | bp `:841-848` | "a claim on a limb column at `z` is the claim on `q_flock` at the point whose low eight coordinates are frozen to the slot's bits and whose high coordinates are `z`" | OK (verbatim, 843-845) |
| 541 | bp `:1235-1236` | "evaluated natively inside `verify` through … `settleFixedClaims`" | OK |
| 544 | bp `:1447-1448` | `g_0` "#3's to transcribe" | OK |
| 545 | bp `:325` | Fiat–Shamir convention names `R1CS_DIGEST` | OK |
| 546 | bp `:217`; `:867` | `minLogRowsBlake2s`; test rejects `τ_BLAKE2S = 2` | OK |
| 590 | bp `:638-642` | `evalOracle` answers `eval₂Mle q (algebraMap K E)` | OK |
| 636 | bp `:267` | ledger row A9 | OK |
| 648-649 | `grep … FlockInterface\|FlockWitnessGen\|limbColumns\|flockError` over `LeanerVM/ tests/` | returns nothing | OK (`git grep` at `b435631`: no hit) |
| 653 | `Spine/Toy.lean:110` | `aux := fun _ ↦ True` | OK |
| 654 | `Arithmetization/Statement.lean:301-302` | `Blake2sRowsValid` | OK |
| 682 | bp `:867` | the floor's only test | OK |
| 688 | bp `:1226` | `verify_knowledgeSound (fs) (bcs) (mca) (flock)` | OK |
| 690 | `AGENTS.md` | "Give load-bearing configuration and certificate types concrete inhabitants" | OK (verbatim, line 84 at `b435631`) |
| 701-703 | bp `:1075-1092` | "`relIn` carries the strong auxiliary predicate of Layer 3 … `limbColumns` is the strided reader of Layer 3" | OK (verbatim with ellipsis, 1088-1092) |
| 725-727 | bp `:846-848`; `:1077` | "`leanIsaInstance.layout` combines the two, the slot map being #3's `FlockInterface.limbColumns` (Layer 9)"; `structure FlockInterface (I : M3Instance)` | OK (verbatim) |
| 737 | bp `:1439-1441` | "reconciled by `FlockInterface.limbColumns`" | OK |
| 745-752 | code block `Spine/Instance.lean:143-148` | `aux`, `decAux` | OK (verbatim) |
| 754 | bp `:1072`; `:331` | "module, over `I`"; the wall's list of exceptions | OK (Flock is not among the exceptions) |
| 757 | bp `:1080` (not cited by line) | `s.τ 5` in the sketch | OK |
| 780-784 | bp `:1323-1325` | acceptance test 20, quoted in full | OK (verbatim) |
| 805; 809-813 | `Component.lean:90-93`; code block `Component.lean:182-184` | `extends Complete`; composition uses `S₁.guarded` only | OK (verbatim). Note: the composed `Security` still sets `toComplete := S₁.toComplete.append S₂.toComplete` (line 176), which is the coupling the finding is about |
| 819 | bp `:332` | "`X.Security` (perfect completeness, and round-by-round knowledge soundness …)" | OK (verbatim) |
| 827-828 | bp `:850-851`; status `:239-240`; `Instance.lean:24-25, 143-145` | "`aux q` says that Flock's R1CS holds of the bits packed into the `q_flock` region" and the same in status and docstrings | OK (verbatim; none mentions position 512) |
| 840 | bp `:192` | "Flock \| A, owned by #3 \| specification Annex C; `crates/flock/src/`" | OK (verbatim) |
| 865; 867 | bp `:1331-1332`; `:1085` | "`Σ piopError < 2^{-150}` plus Flock's `< 2^{-183}`"; `flockError_le` | OK (verbatim) |
| 874 | bp `:267` | ledger row A9, quoted | OK (verbatim) |
| 887-888 | status `:316-319` | "F9 the Python verifier omits the caps …" | OK (verbatim) |
| 910-912 | bp `:1237-1238`; `:614`; `:609` | the fixture; K3 consumes "S (schedules, phase `Def`s)"; "the inhabitant is #3's" | OK |
| 935 | bp `:1234-1235` | `niError` | OK |
| 956 | `Seams.lean:103-109` | `onCube : CMlPolynomialEval E μ` | OK |
| 1137-1139 (section 10) | bp `:324` | claim pool order | OK (checked though outside the assigned sections) |


### 2.4 ArkLib citations (pin `dca90385`, read with `git show dca90385fb40dd5eb8da9145da6348ed17f5cd8b:<path>` in `.lake/packages/Arklib`, whose checkout is now `7653a901`)

| L | Citation | Claim | Verdict |
| --- | --- | --- | --- |
| 296-301 | code block `ArkLib/OracleReduction/Security/Basic.lean:101-104 (ArkLib dca90385)` | `perfectCompleteness` is completeness with error 0 | WRONG LINE: at `dca90385` the four quoted lines are **102-105** (docstring 102, `def` 103-104, body 105); at `7653a901` they are 100-103. Text verbatim |
| 357 | `Composition/Sequential/OracleCompleteness.lean:39-53`; "no `sorry` in the file" | `append_completeness_of_guarded_verifiers` gives `ε₁ + ε₂` | OK (theorem 39-52; `grep -c sorry` = 0). Note it has side hypotheses (`hSeam`, and the second reduction complete from every shared state, `∀ s, R₂.completeness (pure s) …`) that the dossier does not mention |
| 597-610 | code block `Packing/Profile.lean:91-102 (dca90385)` | `RingSwitchingProfile` | OK (verbatim) |
| 614 | `Packing/Spec.lean:56-66, 97-101` | carrier message then batching vector; the full spec | OK |
| 615 | `Packing/General.lean:16-34` | batching, relocation sumcheck, downstream opening | OK |
| 616 | `Packing/BatchingPhase.lean:246-253` | error `κ/\|L\|` | OK |
| 626-629 | `sorry` counts and lines | `BatchingPhase` 4 (329, 331, 347, 370), `SumcheckPhase` 8, `General` 2 (222, 226) | OK. Lines 329, 331 are in `batchingKnowledgeStateFunction` (`toFun_next`, `toFun_full`), 347 in `batchingReduction_perfectCompleteness`, 370 in `batchingOracleVerifier_rbrKnowledgeSoundness`; 222, 226 in `fullOracleVerifier_rbrKnowledgeSoundness` (declared at 185). `SumcheckPhase`: 178, 289, 307, 409, 478, 480, 499, 640. Each of the three files also has one docstring line containing the word `sorry` (74, 34, 70), rightly not counted |
| 629-631 | same counts at `7653a901`; commits #894 and #896 | | OK (identical counts; lines shift by one in `BatchingPhase`: 328, 330, 346, 369; `git log dca90385..7653a901 -- …/Packing/` gives exactly `958c23b99` (#894) and `d831d6b85` (#896)) |
| 631-632 | no Flock or Frobenius under `ArkLib/ProofSystem` at `7653a901` | | OK (`git grep -i flock`, `git grep -i frobenius`: no hit) |
| 632-633 | ArkLib #383 and #893 open | | OK (`gh`, 2026-09-30: both `OPEN`) |
| 5 | `7653a901` is 347 commits past the pin | | OK (`git rev-list --count`) |

### 2.5 Issue #3 (read with `gh issue view 3`, body updated 2026-09-29T22:52Z)

Every quotation the dossier takes from issue #3 is in its body verbatim: "Flock F0 has not
started" (line 29, under "Historical status — 2026-09-16"), "All F0–F9 implementation gates below
are open" (97), "check exceptional challenges, including leanVM's `(1+r_eq)⁻¹` at `r_eq=1`; do not
silently change sampling" (144), "exceptional-challenge completeness conditions" (F4, 114),
"Preserve the constant-one wire", "Prove both directions of R1CS lowering", "pure
witness-generator correctness", "forward/transpose circuit-walk equivalence" (F2, 112), "leanVM
lane: exact BLAKE2s compression" (F8, 118; the issue writes "leanVM lane:" after "Reference lane:
…", lower-case "lane" as the dossier has it), "both directions of the hash-call/trace linkage"
(F9, 119), "rectangular/Frobenius instance its own contracts and parameter proof" (F5),
"pinned equality-weight certificate" (F1), "Joint candidate lists" (141). All OK. The body now
opens with a "Paper comparison — 2026-09-29" paragraph (line 15); the dossier's "status of
2026-09-16" is the section the issue itself calls historical.

## 3. Independent checks (read from the sources, not from the dossier's reasoning)

**3.1 The Flock verifier takes no claim of the pool; the eighteen limb claims go to the opening
as strided claims on `q_flock`. Agree.**
Rust: `cpu/mod.rs:756` builds `slots = finish_claims(…)` (every pooled claim); `:765` calls
`crate::hash_flock::verify_reduction(n_blocks, &mut vs)`, whose only inputs are the block count
and the stream; `hash_flock.rs:282-284` forwards to `setup_for(n_blocks).verify_reduction(vs)`;
`hash.rs:983-1016` runs `zerocheck::verify(self.m(), vs)` and `lincheck::verify(self.m(), K_LOG,
K_SKIP, &WalkLincheckCircuit, &x_ab, zc_claim.a_eval, zc_claim.b_eval, zc_claim.c_eval, vs)`:
constants, its own zerocheck outputs, the stream. `slots` reappears only at `:768`
(`pcs::verify(&mut vs, &slots, &ring, …)`). Python: `verify_flock(log_n, transcript)`
(`verifier.py:1304-1308`), called at `:1405` with the size only; the pooled `claims` go straight
to `verify_stacked_opening` at `:1413`. Routing: `cpu/mod.rs:790-814` turns every column claim
whose column is a BLAKE2S value column (`blake2s_value_slot`, `:447-453`, over
`tables::BLAKE2S_VALUE_COLS`, an array of exactly 18 entries at `tables.rs:394`) into
`pcs::SlotClaim::Strided { offset: l.placements[QFLOCK].offset, slot, stride_log:
SLOT_STRIDE_LOG, … }`; its weight is `stack_open.rs:305-323`. Python does the same through
`Placement(kappa, offsets[QFLOCK] + limbs[column], QFLOCK_SLOT_BITS)` (`verifier.py:884-894`).

**3.2 Exactly one equality check can reject; everything else is derived. Agree.**
Every exit of the Flock verifier path: `zerocheck.rs:354-356` (`LogNTooSmall`, a size check,
unreachable since `m = 14 + n_blocks_log ≥ 17`); `lincheck.rs:1151-1176` (four shape errors on
constants); transcript truncation errors from `next_scalars`/`next_round_poly`/`next_scalar`;
and `lincheck.rs:1252-1256` `ConsistencyFailed`, the only comparison of values. The derived
values: `v_P` (`zerocheck.rs:378`), `c_0` of each zerocheck round and `c_1` of each lincheck round
(`transcript.rs:297-302`), `v_c` (`zerocheck.rs:423`), the lincheck target (`lincheck.rs:1202`),
`T` (`stack_open.rs:522-524`). `hash.rs:983-1016`, `x_ab_of` (`:822-828`), `reduction_claim`
(`:833-840`) and `ring_switch_verify` (`:801-808`) add no check. In `stack_open.rs:505-512` the
opening returns `false` only when the slices are absent or not 64 long (shape). Python: the only
`require` in `verify_flock_zerocheck`, `verify_flock_lincheck` and `ring_switch` is
`verifier.py:1176`.

**3.3 The only challenge-dependent inverse is the prover's `(F192::ONE + r_eq).inv()`; `ZERO.inv()
== ZERO`. Agree, with one omission in the dossier's list.**
`grep -rn '\.inv()'` over `crates/{flock,pcs,lean_vm,fiat_shamir}/src` (recursively) and
`crates/primitives/src/multilinear.rs` returns 19 lines:

| Place | Argument | Class |
| --- | --- | --- |
| `flock/src/zerocheck.rs:117` | `1 + r_eq`, `r_eq` a sampled equality coordinate for rounds 7.. | **prover, challenge-dependent** |
| `flock/src/zerocheck.rs:703` | a fixed `t` | test (module starts at `:435`) |
| `flock/src/zerocheck/univariate_skip_optimized.rs:96-99, 114` | functions of the constant `γ` | constant |
| `primitives/src/multilinear.rs:185`, `:237` | product of `φ_8` nodes; `g + g²` | constant |
| `pcs/src/ntt.rs:50` | NTT twiddle `s_at_root` | domain constant |
| `pcs/src/ntt/additive_ntt_f64.rs:26` | subspace-polynomial normaliser `row[0]` of a basis | domain constant (**not listed by the dossier**) |
| `pcs/src/whir_induce.rs:112` | `s_k(v_k)`, a function of the size only (`:28-51`) | domain constant |
| `pcs/src/ring_switch.rs:1068` | a weight in a forgery test | test (module starts at `:619`) |
| `lean_vm/src/tables.rs:795`, `:984` | batch inverse; `cond` of a JUMP row | witness generation |
| `lean_vm/src/cpu/execute.rs:319`, `:562`, `:607` | execution | witness generation |

No other inversion: there is no `Div` impl on the fields in `primitives/src`, no exponentiation
in the scope other than `g.pow(·)` in execution, and the verifier's Lagrange weights
(`lagrange_weights_naive`, `primitives/src/multilinear.rs:330-334`, used by
`lincheck.rs:833, 1246`) go through `lagrange_weights` with the constant denominator
`window_denominator`. The contract: `gf2_64x3.rs:137` "`ZERO.inv() == ZERO`"; the implementation
(`:144-152`) computes `m = φ(x)·φ²(x)`, which is 0 at 0, and `F64::inv` (`gf2_64.rs:42-68`, same
contract) is an Itoh–Tsujii power, 0 at 0; no panic. Every round of the zerocheck prover goes
through `send_round` (`zerocheck.rs:223` for round 0, `:288` for the others), so the exceptional
case covers every sampled coordinate. Python: `E.inv` (`verifier.py:168-170`) **raises** on zero
("division by zero in GF(2^192)"), a contract different from the Rust's, but the Python inverts
only constants (`:1099`, `:1110`) and nonzero-guarded subspace roots (`:980`).

**3.4 The untransmitted coefficient is derived by a multiplication. Agree.**
`transcript.rs:297-302`: `Some(r) => claim + r * sum_from(1)`, `None => claim + sum_from(2)`.
Python `verifier.py:411-413`: `[claim + eq_factor * E.sum(tail), *tail]`. The prover side,
`add_round_poly(coeffs, eq)` (`transcript.rs:63-71`), omits index 0 when `eq` and index 1
otherwise, matching.

**3.5 The Flock reduction puts `162 + 2·k_batch` scalars on the stream. Agree.**
Verifier reads, in order: 64 (`zerocheck.rs:365`); `n_mlv = m − 6 = 8 + k_batch` rounds of two
(`:397-405`, `next_round_poly(3, …, Some)` reads indices 1, 2); two (`:421-422`); 8 rounds of two
(`lincheck.rs:1205-1211`, `next_round_poly(3, …, None)` reads indices 0, 2); 64
(`lincheck.rs:1214`). Nothing else between (`hash.rs:990-1008`). Total `64 + 2(8 + k_batch) + 2 +
16 + 64 = 162 + 2·k_batch`; 168 at `k_batch = 3`. Challenges: `k_batch + 1` (`zerocheck.rs:362`),
1, `8 + k_batch`, 1 (`lincheck.rs:1179`), 8, and 6 for ring switching: `2·k_batch + 25`. Rerun of
the dossier's `fixed_weights_rank.py` (below) prints the same numbers.

**3.6 Ring switching sends no message, makes no check, draws six challenges. Agree.**
`stack_open.rs:502-514`: the slices come from the caller ("nothing is read here"), then
`ring_switch::sample_map_challenges(vs)`, which is `std::array::from_fn(|_| ch.sample())` over
`COMPOSITION_SHIFTS.len() = 6` (`ring_switch.rs:85, 160-162`); then `λ` and the target
(`:518-527`); no comparison until WHIR. `hash_flock`/`hash.rs:801-808` only packages the claim.
Python: `transcript.samples(len(RING_MAP_SHIFTS))` (`verifier.py:1343`), no read, no `require`
(`:1338-1347`).

**3.7 Annex C requires position 512 of every block to be 1; the blueprint's description of the
auxiliary predicate does not mention it. Agree.**
`c-flock:23-26`: "We also enforce the position $512$ of every block to be $1$ (preventing the
all-zero witness)", equation `flock:eq:const-one`, "for every $t\in\cube{\kbatch}$"; `:28` "This
second condition is enforced by lincheck". Blueprint at `b435631`: `:850-861` and `:1088-1089`
say "Flock's R1CS holds of the bits packed into the `q_flock` region (Annex C.1, §4.2)";
`grep -n -i '512\|constant-one\|constant one\|constant position\|const-one\|constant wire\|all-zero'`
over the whole blueprint finds nothing relevant (one hit, line 745, is about the public-input
point). The status (`:239-240`) and `Instance.lean` (`:23-26`, `:143-145`) say the same. One
nuance the dossier does not state: the blueprint's citation "Annex C.1" does point at the
subsection that contains both conditions, so the omission is of wording, not of reference.

**3.8 `sorry` in `ArkLib/ProofSystem/RingSwitching/Packing/` at the pin `dca90385`. Agree:
14.** `BatchingPhase.lean` 4, `SumcheckPhase.lean` 8, `General.lean` 2, `Prelude.lean`,
`Profile.lean`, `Spec.lean` 0 (lines in section 2.4). Same counts at `7653a901`.

**Reruns.** With `PYTHONDONTWRITEBYTECODE=1 python3 -B`, the dossier's two Python probes
(`probes/gt-flock-ring/fixed_weights_rank.py`, `req_one.py`) print exactly the outputs the dossier
records (rank 128; no fixed coordinate 0 or 1; `r_eq = 1`: 0/200 and 200/200). The leanVM
checkout stayed clean (`git status --short --ignored` empty). The probe sources equal the
dossier's listings except for their header docstrings, which the dossier drops. The Lean probe
(`NoCheckFlock.lean`) was not rerun (brief §8: no Lean in this checkout).

## 4. Other things noticed while checking (not citation verdicts)

1. **"The verifiers take no inverse" (dossier line 227; conclusion 3, line 49, "No verifier
   takes an inverse") is literally false.** The Rust verifier path inverts constants:
   `zerocheck::verify` calls `equality_tail` (`zerocheck.rs:362`), which calls
   `medium_challenges` (`univariate_skip_optimized.rs:96-99`, four `.inv()`), and
   `interpolate_at_z_combined` → `lagrange_eval` → `window_denominator` (`.inv()`,
   `primitives/src/multilinear.rs:185`); the Python verifier divides at `verifier.py:1099` and
   inverts at `:1110`. The dossier's own next paragraph lists these. The accurate sentence, which
   the dossier's proposed acceptance test 20 (line 788) already uses, is "no verifier takes the
   inverse of a value that depends on a challenge".
2. **The inverse inventory omits `crates/pcs/src/ntt/additive_ntt_f64.rs:26`** (normalisation
   of subspace-polynomial rows of a basis: a domain constant). It does not change the conclusion.
3. **Python and Rust disagree on the inverse of zero**: Rust returns 0 (`gf2_64x3.rs:137`,
   `gf2_64.rs:42`), Python raises (`verifier.py:168-170`). Harmless on the verifier path (only
   constants and guarded roots are inverted), but it matters for anyone modelling the prover's
   `send_round` with the Python field: the dossier's probe 9.2 rightly uses `x ** (2**192 - 2)`,
   not `E.inv`.
4. **Line 116**: the claim "`a = Az` and `b = Bz` are never committed and never opened: only `z`
   is" is true (the only commitment is `pcs::commit(&mut ps, &w.q, …)`, `cpu/mod.rs:560-562`, and
   `a`, `b` are not columns of the layout), but neither cited line states it (section 2.1, 2.2).
5. **The floor `τ_BLAKE2S ≥ 3`** (dossier section 3, "Nothing unsound is known: the mathematics
   needs no floor"): the Rust names it "the lincheck floor of `n_blocks_log ≥ 3` (`n_outer ≥ 8`)"
   (`hash.rs:281-282`). The lincheck *verifier* has no such check (`lincheck.rs:1151-1176`
   compares lengths only), so the floor is a constraint of the prover's layout; the dossier does
   not quote this comment. What in the lincheck prover needs `n_outer ≥ 8` was not checked.
6. **Option "give `Component.Complete` an error"** (dossier section 4.3): ArkLib's
   `append_completeness_of_guarded_verifiers` (`OracleCompleteness.lean:39-52` at `dca90385`)
   also needs `hSeam` (the first prover's output is pure, or the second protocol starts with a
   prover message) and the completeness of the second reduction from *every* shared state
   (`∀ s : σ, R₂.completeness (pure s) …`). The dossier states only the sum `ε₁ + ε₂`.
7. **Finding "Knowledge soundness is bundled with perfect completeness"** (8.5): the composed
   `Security` also builds `toComplete := S₁.toComplete.append S₂.toComplete`
   (`Component.lean:176` at `b435631`), so the proposed `Component.Guarded` split must also give
   `Security.append` a completeness-free path; the dossier's code excerpt (182-184) shows only
   the `rbr` field.
8. **Two more stale Rust comments**, of the kind of finding 8.15: `zerocheck.rs:389-390` says
   "The prover sends `(G(1), G(∞))`", but the stream carries the coefficients `c_1 = G(0) + G(1) +
   G(∞)` and `c_2 = G(∞)` (`zerocheck.rs:118` with `transcript.rs:63-71`); `hash_flock.rs:8-9`
   speaks of "the reduction's two tower-field claims", while one ring-switched claim is built
   (`cpu/mod.rs:767`, `hash.rs:801-808`).
9. **Revisions**: the dossier's head (lines 4-5) calls `dca90385` "the ArkLib pin (read in
   `.lake/packages/Arklib/`)". Since the merge of `144c5aa` the pin is `7653a901` and that
   directory holds it. Every ArkLib fact the dossier gives for `dca90385` was confirmed with
   `git show dca90385…:<path>`; the `sorry` counts are the same at `7653a901`, so conclusion 6
   ("admitted at the pin and on `origin/main`") holds at both the old and the new pin, with the
   `BatchingPhase` line numbers shifted by one (328, 330, 346, 369) at the new one.
10. **Ambiguous file name** `multilinear.rs` (lines 204, 244, 437): two different files; say
    `zerocheck/multilinear.rs` or `primitives/src/multilinear.rs`.
11. **Partial code excerpts** presented under a wider range: the `FlockInterface` block
    (dossier 369-376, cited `:1075-1086`) reproduces 1077-1082 only; the `Compose.lean` block
    (330-331, cited `101-102 and 120-121`) shows the two code lines without their docstrings.
    Both verbatim as far as they go.

