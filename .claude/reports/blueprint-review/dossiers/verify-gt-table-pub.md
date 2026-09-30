# Verification of dossier `gt-table-pub` (citations and quotations)

Task `verify-gt-table-pub`. Dossier checked (read-only):
`.claude/reports/blueprint-review/dossiers/gt-table-pub.md` (987 lines). Sources: leanVM at
`a386121f` (`/home/scaraven/Documents/leanEthereum/leanVM`), leanerVM tracked files at `b435631`,
ArkLib `dca90385` and CompPoly `3468b38c` (read with `git show` from the package object stores; the
package checkouts are now at newer pins). No Lean run, no build.

Complete. Sections: revision note, 1 summary, 2 rows, 3 independent checks, 4 other observations.

## Note on revisions (read first)

- leanVM checkout at `a386121f84292f6fa663aaa3e570c15bc0240ea2`, clean (`git status` empty).
- **The leanerVM checkout moved during the pause.** `HEAD` is now `8d3ea7d` ("Merge branch 'main'
  into docs/protocol-blueprint-review"), which brings in `144c5aa` (Lean 4.34.1 upgrade, #61). 59
  tracked files under `LeanerVM/`, `docs/`, `tests/` now differ from `b435631`, among them
  `docs/roadmap/protocol-blueprint.md` (+5/−1), `LeanerVM/Protocol/PublicInput.lean`,
  `LeanerVM/Protocol/Spine/Instance.lean`. This contradicts the brief ("tracked files identical to
  `main` at `b435631`") and the coordinator's "nothing else changed". Every leanerVM citation below
  was therefore checked against `git show b435631:<path>` (copies saved read-only under
  `probes/verify-gt-table-pub/b435631/`), not against the working tree.

## 1. Summary

**Checked: 301 individual citations** (a `file:line` or `file:line-line`, with its quotation when
there is one), in 135 rows below, covering sections 8, 7, 3, 2, 5, 6, 4 and also 1 and 9 of the
dossier. Every quoted Rust, Python, tex and Lean block was compared character by character with
the source (whitespace and line breaks ignored).

| Verdict | Count |
| --- | --- |
| OK | 294 |
| WRONG LINE | 2 |
| MISQUOTED | 0 |
| NOT SUPPORTED | 4 |
| COULD NOT CHECK | 1 |

**Every citation that is not `OK`, with its correction:**

1. Dossier line 176 (A.4, row "The batching error"): "its own Corollary 3.7". **NOT SUPPORTED**
   (numbering). The corollary `cor:idtest` is at `03-proving-primitives.tex:67`. All numbered
   environments share the theorem counter, numbered within the section
   (`doc/leanvm/preamble/theorems.tex:4-12`: `\newtheorem{theorem}{Theorem}[section]`, the others
   `[theorem]`). §3 has five definitions (`03:4, 8, 12, 17, 26`), then `fact:eq` (3.6, `:30`),
   `lem:kbasis` (3.7, `:43`), `lem:sz` (3.8, `:51`), `cor:idtest` (**3.9**, `:67`), `fact:sumcheck`
   (**3.10**, `:79`). So it is Corollary 3.9, not 3.7. Only the number is wrong; the mathematics
   (`(ν_side + B − 1)/|E|` from a degree bound of `ν_side + B − 1` in `ξ`) is right. Not confirmed
   by compiling (the PDF is from an earlier revision and may not be cited).
2. Dossier line 359 (D.1): "citing Corollary 3.7". **NOT SUPPORTED**, same correction: Corollary
   3.9 (`cor:idtest`, `03:67`). `05:155` itself is correct.
3. Dossier line 360 (D.1): "citing Fact 3.8". **NOT SUPPORTED**: `fact:sumcheck` is Fact **3.10**
   (`03:79`). (3.8 is the Schwartz–Zippel lemma, `03:51`.)
4. Dossier lines 364-365 (D.1): "Theorem B.2, for the opening
   (`b-polynomial-commitment-scheme.tex:139-152`)". Lines and the quotation ("is the maximum of
   these entries over all rounds", `:151`) are right. The number is **NOT SUPPORTED**: Annex B's
   numbered environments are `def:interleaved` (B.1, `:56`), `fact:fold-decode` (B.2, `:60`),
   `thm:johnson-interleaved` (B.3, `:64`), `def:listbinding` (B.4, `:70`), `def:rbr` (B.5, `:74`),
   `fig:protocol` (B.6, `:100`), `thm:rbr` (**B.7**, `:139`). So it is Theorem B.7 (`thm:rbr`).
   Better: cite it by its label `thm:rbr`, which is how `08:98` refers to it.
5. Dossier line 177 (A.4, row "Order of JUMP's columns"): `leanisa-blueprint.md:611-612` for
   "`Row` is the table's column list in the Rust's order". **WRONG LINE**: the phrase runs over
   lines **612-613** (at `b435631`; 611 is "Each table is a `GeneralFormalCircuit K Row Regs`, …").
6. Dossier line 849 (section 8, Notes): the same citation `leanisa-blueprint.md:611-612`. **WRONG
   LINE**, should be `:612-613`.
7. Dossier lines 859-868 (section 9): both probes "built with no error and no output",
   `# exit=0`. **COULD NOT CHECK**: no Lean may be run (brief §8: the checkout was merged with
   Lean 4.34.1 and `lake env lean` fails with "incompatible header"), and no log of those runs is
   kept under `logs/` (only `lake-build-main.log` and the lock). What was checked: the two probe
   sources reproduced in the dossier are byte-identical to
   `probes/gt-table-pub/SeamBusShape.lean` and `probes/gt-table-pub/SeamBusMember.lean` (`diff`
   empty). They use only the numerals `0` and `1` in `K`, so the change of meaning of numerals at
   the new CompPoly pin (brief §8) does not affect them; whether they still elaborate on the new
   pins is unknown.

No citation was found misquoted. All the load-bearing quotations (the Rust verifier loop
`constraints.rs:261-291`, the public-input checks `cpu/mod.rs:745-756`, `verifier.py:1398-1402`,
`aggregate.py:1672-1688`, `leaf.rs:849-860`, the tex `08:29-33`, ArkLib
`RoundByRound.lean:553-568` at `dca90385`, the Lean `Seams.lean`/`Compose.lean` blocks at
`b435631`) are verbatim.

## 2. The rows

Conventions: "bp" is `docs/roadmap/protocol-blueprint.md` at `b435631`; `03:`… are the
specification files as in the dossier; Rust paths are under `crates/lean_vm/src/` unless given in
full; "L" is the dossier's line; "n" is the number of individual citations in the row. Lean files
of leanerVM were read with `git show b435631:<path>`; ArkLib with
`git -C .lake/packages/Arklib show dca90385…:<path>`; CompPoly with
`git -C .lake/packages/CompPoly show 3468b38c…:<path>`.

### Section 8 (findings)

| # | L | Citation | Claim | n | Verdict |
| --- | --- | --- | --- | --- | --- |
| 1 | 691 | bp `:481` | `BusOut I` is `linear`, `columns` | 1 | OK |
| 2 | 691 | bp `:487-489` | `Seam.bus` sketch (claims, degree, lines, aux) | 1 | OK |
| 3 | 691-694 | bp `:560-563` | quote "The seams carry *claims*, not challenges … without knowing the bus." | 1 | OK (the elided text is on 561-562) |
| 4 | 691 | bp `:565-574` | the linear-claim and degree paragraph | 1 | OK |
| 5 | 691-692 | `Seams.lean:71-95, 130-134, 175-177` | `VirtualTerm`, `LinearClaim`, `BusOut`, `Seam.bus` | 3 | OK |
| 6 | 720-722 | bp `:836-839` | quote "The stack columns that belong to no opcode table (… `q_flock` …) are tables of the instance with no constraints and no flushes" | 1 | OK (the "…" replaces "; `cpu/layout.rs:13-26`") |
| 7 | 722 | bp `:987-989` | Layer 7 takes `τ_max` and `Σ_j width_j` over the instance | 1 | OK |
| 8 | 728-729 | bp `:323` | quote "Variables bound highest first; table `j` joins at round `τ_max − τ_j`; …" | 1 | OK |
| 9 | 741 | `aggregate.py:1683` | the guest checks the combined equation | 1 | OK (`assert mem == mem_lo + mem_hi * Y_TOWER`) |
| 10 | 744 | bp `:1062` | "Layer 12 owes it" | 1 | OK |
| 11 | 750-751 | bp `:1060-1062` | quote "So the pinned verifiers accept … and Layer 12 owes it." | 1 | OK (sentence on 1061-1062, inside the range) |
| 12 | 765 | bp `:315` | row *Sumcheck messages* | 1 | OK |
| 13 | 769 | `transcript.rs:303-307` | the chain absorbs the three transmitted coefficients | 1 | OK (`if i != fixed { self.bind(c) }`) |
| 14 | 770 | bp `:1218-1221` | `verify_iff_compiled` sketch | 1 | OK |
| 15 | 781-782 | tracker hole comment | repeats "`1/|E|` per coordinate per constraint" | 1 | OK (comment line 67; read with `gh api`, last updated 2026-09-28) |
| 16 | 784-785 | bp `:333` | quote "… is charged in the bus phase, coordinate by coordinate as ζ is drawn, `1/|E|` per coordinate per constraint …" | 1 | OK |
| 17 | 791-792 | bp `:1000-1003` | quote "it is charged to the `(α, β)` and GKR challenges of Layer 6, where `ζ` is drawn, as an extra `τ_max/|E|` per constraint" | 1 | OK (verbatim, 1001-1003) |
| 18 | 793 | bp `:1283` | acceptance test 6, "The state function of Layer 7 charges the zerocheck to Layer 6's challenges" | 1 | OK (1282-1283) |
| 19 | 797 | bp `:991-992` | `tableSumcheck_relOut_implies_constraints` is a placeholder | 1 | OK |
| 20 | 804-806 | bp `:1078-1081` | `reduction … (StmtIn := ColumnClaims) … (StmtOut := WeightedClaim)`; `relIn` "the eighteen column claims are true of `limbColumns`, and aux" | 1 | OK |
| 21 | 811-812 | status F6 | quote "the table round polynomial is a cubic sent whole, four nodes, three wire scalars (`constraints.rs:187-194, 267`)" | 1 | OK (status `:312-313` at `b435631`) |
| 22 | 813 | `constraints.rs:191-194` | the wire carries coefficients | 1 | OK (`tri_coeffs`, `h` in coefficients, `add_round_poly(&h, false)`) |
| 23 | 813-814 | `transcript.rs:56-71` | quote "Send one sumcheck round polynomial, as its COEFFICIENTS, constant first" | 1 | OK (line 56) |
| 24 | 815 | `constraints.rs:24` | the stale comment "sent WHOLE, at four nodes" | 1 | OK |
| 25 | 817-818 | status F9 | quote "the Python verifier omits the caps `log_mem ∈ [16, 32]`, `τ_j ≤ 32`, the bytecode power-of-two bound and `τ_BLAKE2S ≥ 3`" | 1 | OK (status `:316-317`) |
| 26 | 819-829 | `verifier.py:857-864` | the caps in `build_layout` (quoted) | 1 | OK (verbatim) |
| 27 | 830 | `verifier.py:1378` | `build_layout` called from `verify_execution` | 1 | OK |
| 28 | 830 | `verifier.py:252-254` | `log2_strict` requires a power of two | 1 | OK |
| 29 | 835-836 | tracker hole comment | "the prover sends nothing"; "the two scalars are Layer 12's encoding to read and reconcile" | 1 | OK (comment lines 93-94, 97) |
| 30 | 843-844 | `03:110` | quote "a zerocheck round on a degree-`d` cofactor therefore costs `d` field elements" | 1 | OK |
| 31 | 845 | `08:76` | the table sumcheck sends the cubic (three elements a round) | 1 | OK |
| 32 | 846 | `constraints.rs:20-26` | the waiting tables' line is not a multiple of the eq factor | 1 | OK |
| 33 | 849 | `leanisa-blueprint.md:611-612` | "`Row` is the table's column list in the Rust's order" | 1 | **WRONG LINE**: `:612-613` |
| 34 | 853-854 | `primitives/src/multilinear.rs:233-241` | the prover's inverse of `g + g²` | 1 | OK (`tri_coeffs`, `(g + g * g).inv()` at 237) |

### Section 7 (public input, ground truth)

| # | L | Citation | Claim | n | Verdict |
| --- | --- | --- | --- | --- | --- |
| 35 | 584-592 | `08:29-33` | the tex of §8.2 (quoted) | 1 | OK (verbatim) |
| 36 | 594-609 | `cpu/mod.rs:745-756` | the Rust verifier's public-input step (quoted) | 1 | OK (verbatim) |
| 37 | 611 | `primitives/src/multilinear.rs:39-41` | `interp(lo, hi, t) = lo + t * (lo + hi)` | 1 | OK |
| 38 | 612 | `primitives/src/field/gf2_64x3.rs:44` | `Y = (0, 1, 0)` | 1 | OK (`pub const Y: Self = Self { c0: 0, c1: 1, c2: 0 };`) |
| 39 | 614-622 | `verifier.py:1398-1402` | the Python step (quoted) | 1 | OK (verbatim) |
| 40 | 624-644 | `aggregate.py:1672-1688` | the guest step (quoted) | 1 | OK (verbatim) |
| 41 | 669-670 | `tests/LeanerVMTests/Protocol/PublicInput.lean:182-210` | the status's example is tested | 1 | OK (at `b435631`: zero words, limbs `[0,1]`, `[1,0]`, `rStar = y / (1 + y)`) |
| 42 | 672-673 | `cpu/layout.rs:83` | `Layout.pi : [F192; 2]` | 1 | OK |
| 43 | 679 | `cpu/mod.rs:611-613` | the Rust prover sends `L_0(r), L_1(r)` | 1 | OK (`interp_k` of the low and high limbs) |

### Section 3 (the checks)

| # | L | Citation | Claim | n | Verdict |
| --- | --- | --- | --- | --- | --- |
| 44 | 196 | `constraints.rs:267`; `verifier.py:364` | round message missing → `Truncated` / "proof stream exhausted" | 2 | OK |
| 45 | 197 | `05:155` | individual degree 3 | 1 | OK |
| 46 | 198 | `03:84`; `08:100`; `transcript.rs:296-302`; `verifier.py:409-410` | the round check stated in §3, listed in §8.5, holding by construction in both verifiers | 4 | OK |
| 47 | 199 | `05:151-155`; `08:76`; `cpu/mod.rs:728-735`; `verifier.py:1393`; quote `cpu/mod.rs:733-734` | target derived; "A transmitted target would be a free value in its own check" | 5 | OK (quote on 733) |
| 48 | 200 | `05:133-136, 146-150`; `cpu/mod.rs:380-383`; `tables.rs:725-730`; `verifier.py:621` | constraints in the summand | 4 | OK |
| 49 | 201 | `05:145`; `constraints.rs:74-82`; `verifier.py:621-623` | distinct powers per constraint | 3 | OK |
| 50 | 202 | `05:138-143`; `cpu/mod.rs:374, 404-422`; `verifier.py:622` | bus forms in the summand, shared powers | 3 | OK |
| 51 | 203 | `05:132`; `cpu/mod.rs:739`, `:714`; `verifier.py:1382-1385, 1394` | the point is `ζ`, after the commitment | 5 | OK |
| 52 | 204 | `constraints.rs:280`; `verifier.py:364` | final message missing → `Truncated` | 2 | OK |
| 53 | 205 | `08:77`; `constraints.rs:288-290`; `verifier.py:625` | final check | 3 | OK |
| 54 | 206 | `08:77, 97-99`; `cpu/mod.rs:664, 768`; `verifier.py:1395, 1413` | the 104 claims are pooled and opened | 6 | OK |
| 55 | 207 | `08:77`; `07:120`; `cpu/mod.rs:798-806`; `verifier.py:886-894` | limb claims are strided claims on `q_flock` | 4 | OK |
| 56 | 213 | `cpu/mod.rs:141-143`; `cpu/mod.rs:99-106`; `:139-140` | top limb rejected; transcript binds four lanes; the comment on two statements sharing a transcript | 3 | OK |
| 57 | 214 | `cpu/mod.rs:748`; `verifier.py:364` | two scalars present | 2 | OK |
| 58 | 216 | `08:33, 84`; `cpu/mod.rs:674-682`; `verifier.py:1402` | claims on `mem₀, mem₁` | 4 | OK |
| 59 | 217 | `08:84`; `cpu/mod.rs:746, 674-682`; `verifier.py:1399, 1402` | claim `mem₂(r,0,…,0) = 0`, no scalar | 5 | OK |
| 60 | 220-221 | `aggregate.py:1688-1689` | `claim_pool[GEN ** claim_idx] = 0` | 1 | OK (on 1688) |
| 61 | 223 | `cpu/mod.rs:552-555` | the prover only `debug_assert!`s the top limb | 1 | OK |
| 62 | 224 | `LeanerVM/Semantics/Memory.lean:101-110` | `PublicInput` is four lanes of `K` | 1 | OK (unchanged at `HEAD`) |
| 63 | 229-231 | `cpu/mod.rs:769`; `verifier.py:1414`; `verifier.py:104-106` | stream fully consumed; 24-byte scalars | 3 | OK |

### Section 2 (the transcript)

| # | L | Citation | Claim | n | Verdict |
| --- | --- | --- | --- | --- | --- |
| 64 | 92 | `08:70` (quoted); `leaf.rs:909-920`; `cpu/layout.rs:361-395`; `verifier.py:552-557` | the five boundary evaluations | 4 | OK |
| 65 | 93 | `08:75` (quoted); `05:145`; `cpu/mod.rs:726` (quoted); prover `:590`; `verifier.py:1389` | `ξ` drawn after them | 5 | OK |
| 66 | 94 | `05:145`; `08:75` (quoted); `constraints.rs:74-82, 254-255, 281`; `cpu/mod.rs:413-422`; `tables.rs:70-74`; `verifier.py:1390-1392, 621-623, 798-800` | power assignment; JUMP's two identities in the order `b + v_cond·w`, `v_cond·(b+1)` | 10 | OK |
| 67 | 95 | `05:151-155` (quoted); `08:76` (quoted); `cpu/mod.rs:735`; `verifier.py:1393` | target derived | 4 | OK |
| 68 | 96 | `05:145, 155`; `08:76`; `constraints.rs:250` (quoted); `verifier.py:607` (quoted) | `τ_max` rounds | 5 | OK |
| 69 | 97 | `05:155` (quoted); `08:76` (quoted); `constraints.rs:164, 191-194`; `transcript.rs:63-71`; `verifier.py:409` (quoted) | variable order; message `c₀, c₂, c₃` | 6 | OK |
| 70 | 98 | `03:84`; `03:110`; `transcript.rs:289-309`; `constraints.rs:267`; `verifier.py:409-410` | `c₁` derived, no rejection | 5 | OK |
| 71 | 99 | `03:84`; `constraints.rs:268-270`; `verifier.py:424-426` | challenge after the message; `claim := h(r)` | 3 | OK |
| 72 | 100 | `05:146-150, 155`; `constraints.rs:271-274`; `verifier.py:609-614` | joining, padding, weights | 4 | OK |
| 73 | 101 | `08:77` (quoted); `constraints.rs:224-238, 279-280`; `cpu/mod.rs:378` (quoted); `verifier.py:619-620` | final message, one value per column | 5 | OK |
| 74 | 102 | `08:77` (quoted); `constraints.rs:277-290`; `cpu/mod.rs:380-383`; `verifier.py:616-625` | final check | 4 | OK |
| 75 | 103 | `08:77` (quoted); `cpu/mod.rs:428-441`; `verifier.py:624` | claims pooled by table then column | 3 | OK |
| 76 | 104 | `08:77` (quoted); `07:120-122`; `cpu/mod.rs:447-453, 790-814`; `tables.rs:394-413`; `hash_flock.rs:96-115`; `verifier.py:847-850, 886-894, 295-297` | the eighteen limbs, strided on `q_flock` | 9 | OK |
| 77 | 108-142 | `constraints.rs:261-291` | the Rust verifier loop (quoted) | 1 | OK (verbatim) |
| 78 | 144-145 | `transcript.rs:289-302` | `fixed = 1`, indices 0, 2, 3 read, `coeffs[fixed] = claim + sum_from(2)` | 1 | OK |
| 79 | 151 | `08:29` (quoted); `cpu/mod.rs:141-143`; `verifier.py:204-219` | top limb 0 | 3 | OK |
| 80 | 152 | `08:83`; `cpu/mod.rs:745`, prover `:610`; `verifier.py:1398` | `r` drawn | 4 | OK |
| 81 | 153 | `08:29, 84`; `cpu/mod.rs:746-749`, prover `:611-618`; `verifier.py:1399` | two scalars | 5 | OK |
| 82 | 154 | `08:29-32`; `cpu/mod.rs:752-755`; `verifier.py:1400` | per-limb vs combined | 3 | OK |
| 83 | 155 | `08:84` (quoted); `cpu/mod.rs:746, 674-682`; `verifier.py:1399, 1401-1402` | three claims, values `c₀, c₁, 0` | 5 | OK |
| 84 | 161 | `08:98`; `stack_open.rs:518-519`; `verifier.py:1413` | ring-switched claim first | 3 | OK (`n_rs = 1`: `crates/flock/src/hash.rs:806`, `claims: vec![ring_claim(..)]`) |
| 85 | 162 | `cpu/mod.rs:663`; `verifier.py:555-557, 1395` | bus claims next | 3 | OK |
| 86 | 163 | `cpu/mod.rs:664`; `verifier.py:1395` | table claims next | 2 | OK |
| 87 | 164 | `cpu/mod.rs:665`; `verifier.py:1402` | public-input claims last | 2 | OK |
| 88 | 166 | `cpu/mod.rs:656-667` | `finish_claims` fixes the order | 1 | OK |
| 89 | 174 | `08:100` | "every sumcheck's rounds" among the checks | 1 | OK |
| 90 | 176 | `05:155`; "Corollary 3.7" | batching error; the corollary gives one less | 2 | `05:155` OK; **"Corollary 3.7" NOT SUPPORTED**: it is Corollary 3.9 (`cor:idtest`, `03:67`) |
| 91 | 177 | `07:99`; `tables.rs:689-711`; `verifier.py:826`; `leanisa-blueprint.md:611-612` | JUMP's `w, b` last in both verifiers; leanISA follows the Rust order | 4 | first three OK; **`leanisa-blueprint.md:611-612` WRONG LINE: `:612-613`** |
| 92 | 178 | `constraints.rs:251-253` | the `zeta.len() < n` guard | 1 | OK |
| 93 | 179 | `constraints.rs:24`, `:265-266`; `transcript.rs:63-71` | stale comments; the code sends coefficients | 3 | OK |
| 94 | 183-186 | `leaf.rs:610-622`; `verifier.py:570-574`; `tables.rs:436-863` vs `verifier.py:823-834`; `hash_flock.rs:85-115` vs `verifier.py:847-850` | sides order; column lists; limb slots agree | 6 | OK (column lists re-compared entry by entry, section 3 below) |

### Section 5 (the errors)

| # | L | Citation | Claim | n | Verdict |
| --- | --- | --- | --- | --- | --- |
| 95 | 359 | `05:155`; "Corollary 3.7"; bp `:994` | batching error `(ν_side + B)/|E|`; blueprint `(B+2)/|E|` | 3 | `05:155`, `:994` OK; **"Corollary 3.7" NOT SUPPORTED: Corollary 3.9** |
| 96 | 360 | `05:155`; "Fact 3.8"; bp `:994` | `3/|E|` per round | 3 | `05:155`, `:994` OK; **"Fact 3.8" NOT SUPPORTED: Fact 3.10** (`fact:sumcheck`, `03:79`) |
| 97 | 361 | `05:132` (quoted); bp `:333`; bp `:1001-1003` (quoted); bp `:973-975`; bp `:1283` (quoted) | the recycled point: nothing in the spec, three different charges in the blueprint, none in `busError` | 5 | OK |
| 98 | 362 | `08:33`; bp `:1027` | public input `1/|E|` | 2 | OK |
| 99 | 364-366 | "Theorem B.2", `b-polynomial-commitment-scheme.tex:139-152` (quoted remark) | the spec's only round-by-round statement is the opening's | 1 | lines, quote and claim OK (grep of the spec finds no other RBR statement); **"Theorem B.2" NOT SUPPORTED: Theorem B.7** (`thm:rbr`) |
| 100 | 392-394 | `gkr.rs:414-426` (quoted); `verifier.py:451-454` (quoted) | `ζ = (low, high, x_0, …)` | 2 | OK (but see section 4 below on "drawn last") |
| 101 | 435 | test `PublicInput.lean:106-110` | the bound `1/|E|` is attained | 1 | OK (`tests/LeanerVMTests/Protocol/PublicInput.lean` at `b435631`; accepted at `r = 0`) |

### Section 6 (can the real sumcheck fill the slot)

| # | L | Citation | Claim | n | Verdict |
| --- | --- | --- | --- | --- | --- |
| 102 | 441-460 | ArkLib `OracleReduction/Security/RoundByRound.lean:553-568` at `dca90385` | `rbrKnowledgeSoundnessWorstCaseWith` (quoted) | 1 | OK (verbatim, read with `git show dca90385…`; the package checkout is now at `7653a901`) |
| 103 | 462-466 | same file `:164-189`; `Component.Def.err` | the knowledge state function's three fields; the error is fixed with the phase | 2 | OK (`toFun_empty` an iff at 175-176, `toFun_next` 180-182, `toFun_full` 186-189; `err` at `ToArkLib/Component.lean:66` at `b435631`) |
| 104 | 531-533 | `Seams.lean:66-67`; `Instance.lean:160`; `Instance.lean:68-81` | `ColumnClaim.Holds` reads through `I.layout.read`; `Layout` is a reading law | 3 | OK |
| 105 | 537-538 | `cpu/mod.rs:788-789` (quoted) | "No downstream special-casing: it folds into the one opening like every other point claim." | 1 | OK |
| 106 | 540-541 | `cpu/mod.rs:765` (quoted) | Flock's verifier takes no claim | 1 | OK |
| 107 | 557-558 | bp ledger row on sumcheck | ArkLib's single-round bound is admitted at the pin | 1 | OK (bp `:259`; confirmed at `dca90385`: `ProofSystem/Sumcheck/Spec/SingleRound.lean:729-732` and `:1091-1094` are `sorry`) |
| 108 | 578-580 | CompPoly `CompPoly/Multivariate/CMvPolynomial.lean:133`; `Operations.lean:130` at `3468b38c` | `CMvPolynomial.eval₂`, `aeval` exist | 2 | OK (read with `git show 3468b38c…`; package now at `572f9973`) |

### Section 4 (the blueprint set against it)

| # | L | Citation | Claim | n | Verdict |
| --- | --- | --- | --- | --- | --- |
| 109 | 239-250 | `Seams.lean:71-79` | `VirtualTerm` (quoted) | 1 | OK (verbatim at `b435631`) |
| 110 | 251-258 | `Seams.lean:91-95` | `LinearClaim` (quoted) | 1 | OK |
| 111 | 259-271 | `Seams.lean:130-139` | `BusOut`, `TableOut` (quoted) | 1 | OK |
| 112 | 272-281 | `Seams.lean:175-181` | `Seam.bus`, `Seam.table` (quoted) | 1 | OK |
| 113 | 283-288 | `Compose.lean:77-78` | the `table` slot (quoted) | 1 | OK |
| 114 | 294 | bp `:989` | `pSpec := V_to_P : E ; …` | 1 | OK |
| 115 | 295 | bp `:323` | power assignment | 1 | OK |
| 116 | 296 | bp `:990` | `tableSummand_target` | 1 | OK |
| 117 | 297 | bp `:987`; `:836-839` | Layer 7 over the tables of `I`; shared columns are tables | 2 | OK |
| 118 | 299 | `Padding.lean:60-73`; `constraints.rs:273` | `padHigh`, `sumCube_padHigh`, `evalMle_padHigh`; the Rust's `rk` | 2 | OK |
| 119 | 300 | bp `:315` (quoted) | "the oracle protocol sends all of them. Dropping one is the *encoding* of Layer 12" | 1 | OK |
| 120 | 301 | bp `:989` | `P_to_V : Fin (Σ width) → E` | 1 | OK |
| 121 | 302 | bp `:997-998` | "the formula reproduces the final value" | 1 | OK |
| 122 | 303 | bp `:324`; `PublicInput.lean:127-128` | pool order; `pooled` appends after `s.2.columns` | 2 | OK |
| 123 | 304 | bp `:841-848` | "The layout has two readers" | 1 | OK |
| 124 | 305 | `PublicInput.lean:99`; `PublicLine.sent` | schedule; the field exists | 2 | OK (`sent : Bool` at `Spine/Instance.lean:112`, `b435631`) |
| 125 | 306 | `PublicInput.lean:136-137`; bp `:1053-1062` | per-limb `check`; declared deviation | 2 | OK |
| 126 | 307 | `PublicInput.lean:119-124` | `lineClaim` pools `lineValue` | 1 | OK |
| 127 | 308 | bp `:335`, `:834-836`; test `PublicInput.lean:176-180` | three lines, third with cells `0, 0`, not sent | 3 | OK (the tests' pooled values `[1, 1, 0]` are at 170-175; 176-180 show the wrong top cell caught by the third claim only) |
| 128 | 309 | `Instance.lean:51-54` | `Side` is `push \| pull` | 1 | OK |
| 129 | 310 | bp `:994`, `:1027`, `:333` | the stated errors | 3 | OK |
| 130 | 314 | bp `:986-995`, `:960-964` | Layer 7 and Layer 6's `BusOut` | 2 | OK |
| 131 | 323 | bp `:991-992` (quoted) | the placeholder `(∀ j C, C̃_j(ζ_{<τ_j}) = 0 → …) -- see below` | 1 | OK |
| 132 | 325-327 | tracker hole comment | third signature `tableSumcheck I (S : Sumcheck.Def) : Phase.Def I (BusOut I) (TableOut I) (tableSpec I) (Seam.bus I) (Seam.table I)`, `tableSummand I ζ ξ α β rem` | 1 | OK (comment line 80) |
| 133 | 331-346 | `leaf.rs:849-860` | `BusVerify` (quoted) | 1 | OK (verbatim) |

### Section 1 (notation) and section 9 (probes)

| # | L | Citation | Claim | n | Verdict |
| --- | --- | --- | --- | --- | --- |
| 134 | 81-84 | `tables.rs:455, 537, 608, 711, 862`; `verifier.py:823-834, 852`; `07:12, 30, 58, 78, 99, 122` | widths 15, 8, 15, 14, 37; the §7 column lists give the same counts | 13 | OK (spec counts: XOR/MUL 2+3+6+3+1 = 15, SET 2+1+3+1+1 = 8, DEREF 2+3+2+1+3+3+1 = 15, JUMP 2+3+3+1+1+3+1 = 14, BLAKE2S 2+7+9+1 = 19 plus 18 limbs) |
| 135 | 859-868 | probe runs `# exit=0` | both probes built | 1 | **COULD NOT CHECK** (no Lean allowed; sources identical to the probe files) |

Section 0's list of what was read (file ranges) makes no claim about the sources and is not
counted; every range named there exists in the files (`leaf.rs` has 951 lines,
`stack_open.rs` 859, `verifier.py` 1439, `aggregate.py` 3538).

## 3. The independent checks

Each was done by reading the pinned source directly, not the dossier's argument.

**1. Widths `15, 15, 8, 15, 14, 37` (sum 104), and the final message carries every column of
the six tables, the eighteen BLAKE2S limbs included. AGREE.**
- Rust: `tables.rs:455` `arith::N = 15` (used by both `Arith { is_xor: true }` and `false`,
  `tables.rs:356-363`), `:537` `set::N = 8`, `:608` `deref::N = 15`, `:711` `jump::N = 14`,
  `:862` `blake2st::N = 37`; each table's `n_committed_columns()` returns its `N`
  (`:476-478, 541-543, 626-628, 715-717, 866-868`). BLAKE2S's 37 include the 18 limb lanes
  (locals 9 to 26, `:846-851`); the doc comment says so outright (`tables.rs:827-830`: "They are
  listed in `n_committed_columns` … but `cpu` treats them as VIRTUAL").
- The final message: the verifier reads `air.n_cols` values per table (`constraints.rs:280`),
  `n_cols: table.n_committed_columns()` (`cpu/mod.rs:378`), so 37 for BLAKE2S; the prover sends
  every column of `cols[t]` (`constraints.rs:224-238`), where `cols[t]` comes from
  `table_spans()` = `(base, n_committed_columns())` (`cpu/mod.rs:344-349`). Total
  15+15+8+15+14+37 = 104.
- Python: `ARITH_COLUMNS` (15), `SET_COLUMNS` (8), `DEREF_COLUMNS` (15), `JUMP_COLUMNS` (14),
  `BLAKE2S_COLUMNS` (9 + 18 limbs + 10 counts = 37) at `verifier.py:823-834`,
  `TABLE_WIDTHS` at `:852`; the final message reads `table.width` values per table
  (`:620`), `width = len(self.columns)` (`:730-731`).
- Column order compared entry by entry: identical in the two verifiers for all six tables
  (JUMP: `pc, fp, o_c, o_d, o_f, v_cond, v_pc, v_fp, r_c, r_d, r_f, r_bc, w, b`,
  `tables.rs:689-711`, `verifier.py:826`; BLAKE2S limbs `m0..m3` at 9-16, `out` 17-20, `cv`
  21-24, `md` 25-26, counts 27-36, in both). Limb slots: locals 9-12 → slots 10-13, 13-16 →
  14-17, 17-20 → 4-7, 21-24 → 0-3, 25-26 → 18-19 (`tables.rs:394-413` with
  `hash_flock.rs:87-115`), the same as `BLAKE2S_SLOTS` (`verifier.py:847-850`).

**2. Two constraints in all (JUMP's), none in the other five tables. AGREE.**
Rust: `Table::n_constraints` defaults to 0 (`tables.rs:319-321`); the only override is JUMP's,
`2` (`:722-724`; a `grep` for `fn n_constraints` finds only these two); JUMP's identities
`b + cond·w` and `cond·(b+1)` weighted by `pows[0]`, `pows[1]` (`:70-74`). Python: `Table`'s
`constraints` defaults to `lambda _: ()` (`verifier.py:723`), only `jump` passes
`_jump_constraints` (`:841`), which returns two identities in the same order (`:798-800`).
Specification: "Constraints: none" for XOR, MUL_NATIVE, SET_CONSTANT, DEREF, BLAKE2S
(`07:13, 31, 59, 79, 123`), two for JUMP (`07:100`). Hence `B = 2` and `xi_form_base() = 2`
(`cpu/mod.rs:413-415`): the form powers are `ξ², ξ³, ξ⁴`.

**3. The round message carries `c₀, c₂, c₃`; the verifier derives `c₁`; no round check can
fail. AGREE.**
Prover: `ps.add_round_poly(&h, false)` with `h` four coefficients (`constraints.rs:193-194`);
`fixed = usize::from(!eq) = 1`, every index but 1 sent, in index order (`transcript.rs:63-71`).
Verifier: `vs.next_round_poly(4, claim, None)` (`constraints.rs:267`); `fixed =
usize::from(eq.is_none()) = 1`; indices 0, 2, 3 read raw, then `coeffs[1] = claim +
sum_from(2)` = `claim + c₂ + c₃`, then the three read values bound (`transcript.rs:289-309`).
Then `c₁+c₂+c₃ = claim`, i.e. `h(0)+h(1) = claim` identically; the only error path in the round
is `Truncated` (stream exhausted, `take_raw`, `:184-188`). Python: `constant, tail =
self.next_scalar(), self.next_scalars(count - 2)`, `return [constant, claim + E.sum(tail),
*tail]` (`verifier.py:409-410`), called with `count = 4` (`:608`). The only rejection of the
whole table sumcheck is the final check (`constraints.rs:288-290`, `verifier.py:625`).

**4. The number of rounds is the maximum log-height over the six opcode tables. AGREE.**
Rust: `n = airs.iter().map(|a| a.tau).max()` (`constraints.rs:250`), `airs` built from
`tables::tables()` zipped with `l.taus` (`cpu/mod.rs:361-369`), six entries (`N_TABLES = 6`,
`tables.rs:353`). Python: `n_rounds = max(table_log_heights)` (`verifier.py:607`), called with
`layout.table_log_heights` (`:1394`), the six announced heights (`:1375, 1378`). The shared
columns (`mem`, counts, `q_flock`) are not in either list.

**5. The target is derived by the verifier and never read from the stream. AGREE.**
Rust: `target = Σ_s form_pows[s]·bus.totals[s]` (`cpu/mod.rs:735`), passed as a parameter to
`constraints::verify`, which starts `let mut claim = target;` (`constraints.rs:261`) and reads
nothing before the first round message. `bus.totals[s] = framework + bus_gkr.values[s]`
(`leaf.rs:924`), with the comment "DERIVED, never read" (`:921-923`). Python: `target =
dot(form_powers, bus.totals)` (`verifier.py:1393`); `totals.append(tree_values[side] + known +
ones_padding)` (`:590`).

**6. The public-input check: one combined equation in all three executable verifiers; the
values pooled are the two scalars read and `0`. AGREE.**
- Rust (`cpu/mod.rs:745-756`): `r_pi = vs.sample()`; `pi_limbs = [F192::ZERO; 3]`, entries 0 and
  1 overwritten by `vs.next_scalar()`; `want = interp(l.pi[0], l.pi[1], r_pi)`; reject iff
  `pi_limbs[0] + F192::Y * pi_limbs[1] != want`; then `finish_claims(…, r_pi, pi_limbs)`, whose
  `bind_pi_claim` pools `limbs[col - MEM_LO]` on `MEM_LO, MEM_HI, MEM_TOP` at
  `(r, 0, …, 0)` (`:674-682`). So the pooled values are `c₀, c₁, 0`.
  `interp(lo, hi, t) = lo + t·(lo + hi)` over `E` (`primitives/src/multilinear.rs:39-41`), the
  characteristic-2 form of `(1−t)·lo + t·hi`; `l.pi : [F192; 2]` are the two public words
  (`cpu/layout.rs:81-83`). `Y = (c0, c1, c2) = (0, 1, 0)`, the element `y`
  (`primitives/src/field/gf2_64x3.rs:43-44`).
- Python (`verifier.py:1398-1402`): `public_limbs = (*transcript.next_scalars(2), ZERO)`; check
  `poly_eval(public_limbs, Y) == multilinear_eval(public_input.halves(), [public_challenge])`;
  pooled `zip((MEMORY_0, MEMORY_1, MEMORY_2), public_limbs)`. `poly_eval` is Horner, constant
  first (`:281-283`), so the left side is `c₀ + Y·c₁ + 0·Y²`; `Y = E(0, 1)` (`:183`);
  `multilinear_eval([h₀, h₁], [r]) = h₀·(1+r) + h₁·r` (`:240-245`) = `interp(h₀, h₁, r)`;
  `halves()` = `(E(w0, w1), E(w2, w3))` (`:216-219`).
- Recursion guest (`crates/rec_aggregation/guests/aggregate.py:1679-1689`): `rm = squeeze`,
  `mem = pi_0 + rm * (pi_0 + pi_1)` (= `interp`), two scalars `mem_lo`, `mem_hi`,
  `assert mem == mem_lo + mem_hi * Y_TOWER`, pool `mem_lo`, `mem_hi`, `0`. `Y_TOWER` is filled
  by the host as `dsl_u128(y_tower)` with the comment "Y = new(0,1,0)"
  (`crates/rec_aggregation/src/aggregation.rs:2477-2480`), i.e. `y`.
- So in all three: `interp = (1+r)·w₀ + r·w₁` over `E` on the two public words, `Y = y`, one
  equation `c₀ + y·c₁ = interp(w₀, w₁, r)`, and the pool `(c₀, c₁, 0)` on the three memory
  limbs at `(r, 0, …, 0)`. The specification's §8.2 (`08:29-32`) has one equation per limb.
  The Rust prover sends the per-limb values `interp_k` of limb 0 and of limb 1
  (`cpu/mod.rs:611-613`), which satisfy both.

**7. leanISA's `PublicInput` cannot represent a public word with a nonzero top limb. AGREE.**
`LeanerVM/Semantics/Memory.lean:101-110` at `b435631` (unchanged at `HEAD`):
`structure PublicInput where lanes : Fin 4 → K`; `word0 p := E.ofLimbs (p.lanes 0)
(p.lanes 1) 0`, `word1 p := E.ofLimbs (p.lanes 2) (p.lanes 3) 0`. The top limb is the literal
`0`; there is no field for it.

**8. The order of the claim pool and the place of the ring-switched claim. AGREE.**
`finish_claims` (`cpu/mod.rs:656-667`): `bus_claims`, then `constraint_claims(table_claims)`
(table by table, local column by column, `:428-441`), then `bind_pi_claim` (three), then
`slot_claims` maps each to a located claim **in the same order** (`:790-814`, a `map`). Both
prover (`:622`) and verifier (`:756`) call it. `pcs::verify` passes the list unchanged to
`verify_opening_batch_mixed_whir_stacked` (`crates/lean_vm/src/pcs.rs:161-170`), which draws
one challenge and takes `lambdas = powers(λ, n_rs + point_claims.len())`, split at `n_rs`: the
ring-switched claims take `λ⁰ … λ^{n_rs−1}`, the point claims the rest in order
(`crates/pcs/src/stack_open.rs:518-527`). `n_rs = 1`: `ring_switch_verify` builds
`claims: vec![ring_claim(claim, qflock_vars)]` (`crates/flock/src/hash.rs:801-807`), called at
`cpu/mod.rs:767`. So: ring-switched claim at `λ⁰`, then 5 bus claims, 104 table claims, 3
public-input claims: 112 point claims, 113 powers. The Python agrees
(`verifier.py:1395, 1402, 1413`, `[ringswitch, *(…claims)]`, `powers(…, len(claims))` at
`:1361`). The specification agrees (`08:98`: "the ring-switched claim first and the pooled
column claims after").

## 4. Other things noticed (not citation verdicts)

1. **Blueprint line numbers hold at `b435631` only.** At `HEAD` (`8d3ea7d`) the blueprint has
   two hunks against `b435631` (`git diff b435631 HEAD -- docs/roadmap/protocol-blueprint.md`):
   a new 4-line paragraph after line 51 ("The dependency API tables and signatures below record
   the original implementation baseline. …") and a rewritten conventions row *Module system*
   (`b435631:330`). So every blueprint line the dossier cites (all ≥ 315) is **+4 at `HEAD`**
   (e.g. row *Sumcheck messages* is `:319` at `HEAD`, Layer 7's sketch `:990-999`). The report
   should state that the citations are at `b435631`. This also contradicts brief §8, which says
   the blueprint "changed in its pins table only (6 lines)": neither hunk is a pins table; one is
   a new paragraph on the dependency baseline, the other the *Module system* convention
   ("ArkLib and Clean are both module libraries at the current pins …").
2. **"`ζ_0, ζ_1` are drawn last" (dossier line 394).** True of the coordinates of `ζ`, but not
   of the GKR's challenges: after `(low, high)` the verifier draws one more combiner, unused
   after the last layer (`gkr.rs:423` `lambda = vs.sample();`; `verifier.py:453`
   `combiner = transcript.sample()`). It is not a coordinate of `ζ`, so the argument of D.3 is
   unaffected; the phrase should read "are the last coordinates of `ζ` drawn".
3. **Two more stale comments in `constraints.rs`** beside the two the dossier lists (`:24`,
   `:265-266`): `:26` says the verifier checks "`h(0) + h(1) = claim`, then interpolate at the
   challenge" (there is neither a check nor an interpolation: coefficients are read and one is
   derived); `:257-260` says "Each round arrives as the round polynomial itself at `nd`" (it
   arrives as three coefficients, `transcript.rs:289-302`). They could join the dossier's note
   "Stale comments in the Rust on the round message".
4. **"Stream scalars have no canonicity check" (B.3, dossier line 230)** is right for the
   scalars of these two phases, but the stream is not check-free in general: the root's two
   scalars are decoded by `scalars_to_hash`, which rejects a non-canonical half
   (`transcript.rs:95-99`, `Error::NonCanonicalEncoding`), and the announced sizes must have
   zero high limbs (`cpu/mod.rs:133-135`; `verifier.py:1373`). A precision, not an error.
5. **The GKR layer round message (D.3, "`ε_G = 5/|E|`").** The last layer's rounds read
   `next_round_poly(5, claim, Some(equality_point))` (`gkr.rs:399-401`): five coefficients of a
   degree-4 cofactor, the eq factor applied by the verifier, so the full round polynomial has
   degree 5, consistent with the dossier's `5/|E|` and with the blueprint's row *GKR* ("degree 5
   (eq × four multilinears)"). The dossier's per-challenge errors in D.3 are its own
   inferences; I checked only that the degrees they rest on match the code.
6. **The tracker comment** (`issues/12#issuecomment-5833669972`) was re-read with `gh api`
   (GET only), `updated_at` 2026-09-28T14:28:11Z; the three quotations the dossier takes from it
   are there (its lines 67, 80, 93-97). A copy is at
   `probes/verify-gt-table-pub/tracker-hole-comment.md`.
7. **Library revisions.** The dossier's section 0 says it read ArkLib `dca90385` and CompPoly
   `3468b38c` "under `.lake/packages/`". Those directories now hold `7653a901` and `572f9973`
   (brief §8). The cited lines were re-checked at the old commits with `git show` from each
   package's object store and are correct there; a reader who opens `.lake/packages/` now sees
   the new revisions.
8. Nothing in the dossier was found to rely on the leanerVM working tree rather than on
   `b435631`: every Lean quotation matches `git show b435631:<path>`. (`PublicInput.lean` and
   `Spine/Instance.lean` differ at `HEAD`, by proofs and imports, per brief §8.)
