# Verification of the dossier `gt-bus` (task verify-gt-bus)

Every citation and quotation of `dossiers/gt-bus.md` (1490 lines) checked against its source:
leanVM at `a386121f` (`/home/scaraven/Documents/leanEthereum/leanVM`, clean), leanerVM at
`b435631` (read with `git show b435631:<path>`), ArkLib at `dca90385` (read with
`git -C .lake/packages/Arklib show dca90385:<path>`), the tracker's hole comment
(`issues/comments/5833669972`, read with `gh api`, last edited 2026-09-28T14:28Z, before the
dossier). No Lean was run; the dossier's Python probe was re-run from a scratch copy.

## 0. Environment note

The leanerVM checkout moved during this check: the branch is at `8d3ea7d`, which merges `main`
at `144c5aa` (Lean 4.34.1; ArkLib pin `dca90385` → `7653a901`, `.lake/packages/Arklib` now at
the new pin; the blueprint 1549 → 1553 lines). Brief section 8 records this. Nothing here was
read from the moved working tree: all leanerVM line numbers below are at `b435631`, all ArkLib
line numbers at `dca90385`.

## 1. Summary

**Citations checked: 314 rows** in sections G, B, A, F, D, E, C, the summary, H and I. A row
holds the references one dossier line gives for one claim: all the lines of one file, or the
parallel references to the specification, the Rust and the Python. The rows cover about 400
single `file:line` references and every verbatim quotation, code block and theorem number.

| Verdict | Rows |
| --- | --- |
| OK | 300 |
| WRONG LINE | 3 |
| MISQUOTED | 0 |
| NOT SUPPORTED | 9 |
| COULD NOT CHECK | 2 |

Line numbers and quotations are accurate almost everywhere. Every quotation marked OK was
found verbatim, ignoring whitespace and line breaks. Two cases had cosmetic gaps and were
still marked OK: an omitted `;` at `mod.rs:135`, and a quotation that runs one line past the
cited range (`st:316-318`, which ends at 319).

**Every citation that is not OK, with its correction:**

1. **Lemma number wrong (NOT SUPPORTED as numbered), dossier lines 295 and 570.** The dossier
   calls the invariant-count lemma (`06:51-57`) "Lemma 6.2". In section 6, Proposition 6.1
   (`06:9`) and Remark 6.2 (`06:30`) share the theorem counter
   (`doc/leanvm/preamble/theorems.tex:4-15`, `\newtheorem{remark}[theorem]{Remark}`), so the
   lemma is **Lemma 6.3** and "Lookup correctness" (`06:59`) is Theorem 6.4. Every other
   number the dossier gives was checked and is correct: Theorem 5.1, Lemma 5.2, Corollary 3.9,
   Fact 3.10, Definition 3.11, §8.4 and §8.5.
2. **Wrong commit (NOT SUPPORTED), dossier line 855-856.** The dossier says "The check was
   introduced by commit `14fbca8f`". It was not:
   - the parent `14fbca8f^` already has the same `require` at `verifier.py:922-930`, written
     with `BLAKE2S.opcode`;
   - `14fbca8f` only renamed that constant to `OP_BLAKE2S`;
   - `git log -S` dates the pieces: `"invalid announced table sizes"` with `16 <= log_memory
     <= 32` comes from `8a6e7750` ("python verifier", 2026-09-03), `0 <= log_bytecode <= 32`
     from `348ca455`, and the `BLAKE2S` floor from `5751a5c7`.

   All of these commits are ancestors of the pin, so the dossier's conclusion (the caps are
   checked at the pin, and the status's F9 is false) stands. Correction: "the check is present
   at the pin; it was assembled in `8a6e7750`, `348ca455` and `5751a5c7`, all ancestors of
   `a386121f`".
3. **WRONG LINE, dossier line 411: `Component.lean:93-94`.** Cited for "the verifier's input
   statement is `StmtIn × (∀ i, OStmtIn i)`". Line 93 is `extends Complete D relIn relOut
   where`, and line 94 is a docstring. The type appears at `ToArkLib/Component.lean:91`
   (`relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)`) and at `:98` (the extractor).
4. **WRONG LINE, dossier line 577: `Arithmetization/Statement.lean:240-243`.** Cited with the
   quotation "every read pull of the six tables". The phrase is in the docstring at `:235`
   ("Every read pull of the six tables …") and in the module docstring at `:66`. Lines 240-243
   hold the definition, which does say the same thing in Lean. Correction: `:235-243`.
5. **WRONG LINE (minor), dossier line 857-858: `mod.rs:165`.** The quotation "The other two
   verifiers reject it here too (`python-verifier`, `guests/aggregate.py`)" spans
   `mod.rs:164-165`. It is recorded here only because the brief asks for exactness.
6. **NOT SUPPORTED, dossier line 614: `leaf.rs:442-454`, "the other cases `unreachable!`".**
   The framework blocks do use only `Const`, `Index`, `Col` and `Public` (`layout.rs:346`,
   `use Coord::{Col, Const, Index, Public}`). But in the match at `leaf.rs:442-454`, `GCol` is
   handled (`:446`); only `Prod` and `Sum` are `unreachable!` (`:447-449`).
7. **NOT SUPPORTED (attribution; no line cited), dossier line 771-772.** The dossier calls
   `Verifier.KnowledgeStateFunction.appendGuarded` "ArkLib's appended state function". At the
   ArkLib pin `dca90385` no such declaration exists; the only `appendGuarded` there is the
   coordinate-wise special-soundness one (`CoordinateWiseSpecialSoundness/Escape.lean:288, 305`).
   The declaration is leanerVM's own, `LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean:474` at
   `b435631`, a port of ArkLib pull request #615. The substance holds: the definition is the
   components' own state functions spliced at the seam (`KnowledgeAppend.lean:21-26, 474-488`).
8. **NOT SUPPORTED as worded, dossier line 935-936.** The dossier says 'a search for
   "canonical", "upper limb", "consumed" finds only the public word of acceptance test 10'.
   The substance is right: no passage of the blueprint concerns canonical encodings or the
   consumption of the stream. The literal claim is not: "consumed" matches 13 other lines in
   the sense of "used by" (for example `bp:129, 146, 262`); "canonical" matches only
   `bp:1294`; "upper limb" matches nothing.
9. **NOT SUPPORTED in detail, dossier line 340.** The dossier says "the compiled verifier
   absorbs the 8 elements before the root (acceptance test 12 says so)". Test 12
   (`bp:1300-1302`) says "The sizes and the commitment root are observed before `α`"; it does
   not order the sizes before the root. The Rust does (`mod.rs:713-714`), so the fact is
   right; the citation does not carry it.
10. **NOT SUPPORTED (a figure inconsistent with the dossier's own computation), dossier
    line 404.** D.2 says "the GKR's sum is `μ² + 2` (D.3)", but D.3 (line 472) finds
    `4·2^μ + μ²` for the whole bus phase, that is `μ²` for the GKR with the last combiner
    charged 0. `μ² + 2` holds only if that combiner is charged `2/|E|`. The comparison with the
    Rust's `8(μ+1)²` is unaffected.
11. **NOT SUPPORTED (arithmetic), dossier line 473.** D.3 says "With the blueprint's numbers:
    `4·2^μ + 5μ²/4 − μ/2 + 2`". With the blueprint's `μ/2` combiners (one per layer, `bp:321,
    941`) the sum is `4·2^μ + 2·(μ/2) + 5·(μ²/4 − μ/2) + 2·(μ/2) = 4·2^μ + 5μ²/4 − μ/2`. The
    `+ 2` is the deployed extra combiner, which by G2 the blueprint does not have.
12. **COULD NOT CHECK (Lean not run, per brief section 8).** Three things rest on Lean runs:
    - the probe H.2's recorded output ("none, exit status 0");
    - the control copy's failure;
    - `#print axioms Probe.x0_degree` giving `[propext, Classical.choice, Quot.sound]`.

    The source `BusSeam.lean` is identical to the dossier's reproduction except for a leading
    module docstring the dossier omits. `BusSeamControl.lean` exists.

Items 10 and 11 are arithmetic, not citations; they are counted among the NOT SUPPORTED because
each cites a section as its support. Item 1 is two rows (dossier lines 295 and 570).

## 2. The rows

Shorthand as in the dossier. "L" is the line of `gt-bus.md`. Rows of one dossier line with
several citations of the same file for one claim are one row.

### Section G (findings)

| L | Citation | Claim | Verdict |
| --- | --- | --- | --- |
| 677 | `gkr.rs:399-404, 410-413` | round message, running claim, final check | OK |
| 677-678 | `fs/transcript.rs:297-302` | `c_0` derived | OK |
| 678 | `py:411-413, 445, 449` | same in Python | OK |
| 681 | `constraints.rs:267` `next_round_poly(4, claim, None)` | table sumcheck call | OK |
| 682 | `constraints.rs:271-274` | equality factors multiplied into weights | OK |
| 682 | `py:608-614` | Python table sumcheck | OK |
| 686-687 | `bp:321` quote "Layer sumcheck messages have degree 5 …" | blueprint row GKR | OK |
| 688-689 | `bp:315` quote | row Sumcheck messages | OK |
| 690-691 | `bp:898-901` quote | eq-weighted variant | OK |
| 692 | `bp:941-942` "`5/|E|` to each sumcheck round" | gkrError | OK |
| 692-693 | tracker hole G5 "degree-5 round polynomials" | tracker | OK (hole comment line 33) |
| 699 | `bp:1212` `RoundPoly.decode` | Layer 12 | OK |
| 711 | `gkr.rs:399-413`; `constraints.rs:267-274` | proposed text | OK |
| 724 | `gkr.rs:369`; `gkr.rs:391, 423` | combiner before loop, after each iteration | OK |
| 725 | `py:435, 453` | same | OK |
| 727 | `05:91` "at every layer a combiner" | spec | OK |
| 727 | `bp:321` "A fresh combiner `λ` per layer" | blueprint | OK |
| 728 | `bp:940-941` "a fresh `λ` per layer … exactly as pinned" | blueprint | OK |
| 731 | `fs/lib.rs:95-99` | a squeeze changes the chain state | OK |
| 735 | `gkr.rs:369, 423` | proposed text | OK |
| 743-751 | `bp:930-937` and code block | Layer 5 `gkr` | OK (code verbatim, `bp:930-934`) |
| 754 | `Phase.lean:37-38` | a phase's one oracle is the stack | OK |
| 755 | `Component.lean:143-149` `Def.append` | append needs matching oracles | OK |
| 760-762 | `LiftContext/Reduction.lean:355-365, 542-560` (dca90385) | both admitted | OK (`sorry` at 365, 560) |
| 765 | `bp:262` quote "Not consumed: … no lens is needed" | ledger A4 | OK |
| 766 | `bp:606` | bus phase consumes G5, G6 (and G4) | OK |
| 767 | tracker `busPhase I (G : Gkr.Def)` | tracker P1 | OK (hole comment line 66) |
| 771-772 | `Verifier.KnowledgeStateFunction.appendGuarded` as "ArkLib's" | attribution | NOT SUPPORTED (leanerVM's `ToArkLib/KnowledgeAppend.lean:474`, port of ArkLib #615; absent at `dca90385`) |
| 803-805 | `bp:800-801` quotes | `Sizes.Admissible`, `admissible_iff_caps` | OK |
| 806-808 | `Arithmetization/Statement.lean:79-81` quote; `:250-263` | Caps has neither window | OK |
| 809 | `bp:1218-1220` | `verify_iff_compiled` quantifies `∃ s, s.Admissible` | OK |
| 810 | `bp:1130` | `piopError_le` | OK |
| 821-822 | `mod.rs:157-176` (proposed comment) | read_public | OK |
| 835-838 | `st:316-318` quote | status F9 | OK (quote ends at 319) |
| 838 | `st:164` quote | status to-report line | OK |
| 840 | `py:1378` | calls `build_layout` | OK |
| 843-853 | `py:856-864` code | caps check | OK (verbatim) |
| 855 | `py:252-254` | `log2_strict` needs a power of two | OK |
| 855-856 | commit `14fbca8f` introduced the check | provenance | NOT SUPPORTED (present in `14fbca8f^`; origin `8a6e7750`, `348ca455`, `5751a5c7`; ancestry claim true) |
| 857-858 | `mod.rs:165` quote | Rust says Python rejects too | WRONG LINE (164-165) |
| 870-871 | `bp:333` quote | row Seams | OK |
| 871-872 | `bp:974` quote | busError | OK (974-975) |
| 872-874 | `bp:1001-1003` quote | Layer 7 charge | OK |
| 874 | tracker P2 | busError plus per-constraint charge | OK (hole comment line 67) |
| 891 | `layout.rs:354-410` | framework blocks first | OK |
| 891 | `py:507`; `py:499` quote "the blocks no table owns, stacked first" | Python | OK |
| 894 | `bp:322` | rule for witness stack only | OK |
| 894 | `bp:196` | leaf layouts cited by file | OK |
| 897-900 | `Instance.lean:185-186` code | `tuples` order | OK (verbatim) |
| 911 | `layout.rs:354-415`, `leaf.rs:149-156` | proposed row | OK |
| 921 | `gkr.rs:274-275`, `py:434` | roots `(R, R_c)` | OK |
| 925 | `leaf.rs:428-439, 466-471` | order and dedup of boundary evaluations | OK |
| 928 | `bp:323` | ξ powers order | OK |
| 935-936 | blueprint search for "canonical", "upper limb", "consumed" | finds only test 10 | NOT SUPPORTED as worded (see summary item 8) |
| 937 | `st:319-320` quote "four predicates plus truncations" | status F10 | OK |
| 940 | `bp:1238-1239` | six mutations | OK |
| 955 | `Seams.lean:176` | degree conjunct | OK |
| 960 | `constraints.rs:250-253` | ζ length guard | OK |
| 970 | `bp:954-979` | Layer 6 sketch fields | OK |
| 973-974 | tracker P1 `Phase.Def I Unit (BusOut I) (busSpec I) (M3Holds I) (Seam.bus I)`, "specification (5.4)" | tracker | OK (hole comment line 66) |
| 974 | `st:303` | (5.4) does not exist | OK |
| 975-977 | `bp:975-977` quote | invariant | OK |
| 988 | `bp:941-942` | gkrError names | OK |
| 989 | `gkr.rs:387` | binary layer's one challenge | OK |
| 994-996 | `st:289-290` quote | status S11 | OK |
| 996-997 | `08:69` quote; `08:100` quote | one root | OK |
| 1002 | `bp:197` cites `leaf.rs:664-668` | status of that citation | OK (`bp:197` at b435631 is the count-blocks row; `leaf.rs:659-667` is the signature, 668 its first line) |
| 1003 | `leaf.rs:606-622` | count side | OK |
| 1003 | `bp:601` "Lemma 5.1" | blueprint's numbering | OK |
| 1004 | `05:36-48` | Theorem 5.1 | OK (theorem at 36-38; the range also covers Lemma 5.2 at 40-48) |
| 1005 | tracker P1 "(5.4)" | tracker | OK |
| 1011 | `mod.rs:123, 149`; `py:1376` | rate announced | OK |
| 1012 | `08:55` | seven announced values | OK |
| 1013 | `08:68` | roots prose order | OK |
| 1014-1015 | `08:55` quote; `mod.rs:66-93` | seed | OK |
| 1019 | `py:566, 857` | stacked bytecode | OK |
| 1020 | `layout.rs:229-309` | Rust builds eight columns | OK |
| 1023 | `leaf.rs:110` | `5·2^μ` | OK |
| 1024 | `05:37`; `06:78` "every count column" | spec | OK |
| 1030 | `constraints.rs:250`; `py:607` | `τ_max` | OK |
| 1031 | `mod.rs:344-351` | every column of the six tables | OK |

### Section B (checks)

| L | Citation | Claim | Verdict |
| --- | --- | --- | --- |
| 290 | `mod.rs:132` | Transcript error | OK |
| 290 | `gkr.rs:359, 381, 401, 408` | Truncated | OK |
| 290 | `leaf.rs:549` | Truncated | OK |
| 290 | `fs/transcript.rs:184-188` | `ExceededStream` | OK |
| 290 | `py:363-367` | stream exhausted | OK |
| 291 | `mod.rs:133-135`; `py:1373` | upper limbs | OK |
| 292 | `08:29` | top limb 0 | OK |
| 292 | `mod.rs:141-143` | third limb | OK |
| 292 | `mod.rs:99-106` | seed binds two low limbs | OK |
| 293 | `06:90` | `κ_bc ≤ 32` | OK |
| 293 | `mod.rs:158-159` | power of two, ≤ 2^32 | OK |
| 293 | `py:857`, `py:862` | `log2_strict`, bound | OK |
| 294 | `06:86` | `16 ≤ κ_mem ≤ 32` | OK |
| 294 | `mod.rs:160`; `mod.rs:51-52` | memory window | OK |
| 294 | `py:859` | Python | OK |
| 294 | `mod.rs:45-50` | range-check bound | OK |
| 295 | `06:80` | table cap | OK |
| 295 | `mod.rs:161`; `mod.rs:60` | `τ_j ≤ 32` | OK |
| 295 | `py:860` | Python | OK |
| 295 | "Lemma 6.2 (`06:51-57`)" | invariant count lemma | NOT SUPPORTED as numbered: lines right, it is Lemma 6.3 |
| 295 | `witness.rs:76` | layout shifts by κ | OK |
| 296 | `mod.rs:162-166` | BLAKE2S floor | OK |
| 296 | `py:861` | Python | OK |
| 296 | `flock/src/hash.rs:283-286` | floor `n_blocks_log ≥ 3` | OK (imported as `n_blocks_log`, `lean_vm/src/hash_flock.rs:45`) |
| 296 | `layout.rs:155` | `q_flock` block `τ_5 + 8` | OK |
| 297 | `mod.rs:167` | rate | OK |
| 297 | `pcs/src/whir_config.rs:44-55` | `[1, 4]` | OK |
| 297 | `py:1377` | Python | OK |
| 298 | `mod.rs:174-176` | stacking window | OK |
| 298 | `py:1379` | Python | OK |
| 298 | `pcs.rs:179-188` | window test | OK |
| 298 | `witness.rs:97`; `py:890` | floor at 15 | OK |
| 299 | `fs/merkle.rs:26-29`; `py:223` | root halves | OK |
| 300 | `leaf.rs:130-145` | asserts | OK |
| 301 | `08:68-69`, `08:100` quote | one root | OK |
| 301 | `gkr.rs:364-367`; `py:434, 437` | structural | OK |
| 302 | `06:78`, `08:69` | `R_c ≠ 0` | OK |
| 302 | `leaf.rs:887-889`; `py:546` | check | OK |
| 303 | `05:75, 83` | layer check implicit | OK |
| 303 | `gkr.rs:384-386`, `gkr.rs:411-413`; `py:449` | layer check | OK |
| 304 | `03:79-85`, `03:110` | round identity | OK |
| 304 | `fs/transcript.rs:297-302`; `py:411-413` | derived | OK |
| 305 | `constraints.rs:250-253` | ζ length | OK |
| 306 | `mod.rs:769`; `fs/transcript.rs:213-219` | consumption | OK |
| 306 | `py:1414`; `py:415-417` | Python | OK |
| 311-312 | `mod.rs:303-313`, `leaf.rs:75-81`, `gkr.rs:17-21` | error enums | OK |

### Section A (transcript)

| L | Citation | Claim | Verdict |
| --- | --- | --- | --- |
| 93 | `tables.rs:483-495, 548-561, 633-643, 731-751, 873-908` | flush pairs | OK |
| 97 | `tables.rs:479-482, 544-547, 629-632, 718-721, 869-872` | count columns | OK |
| 102 | `fs/transcript.rs:283-287` | read and bind | OK |
| 103 | `fs/lib.rs:95-99` | one squeeze per element | OK |
| 107 | `08:55` quote; `08:44-46` | seed; §8.4 TODO | OK |
| 107 | `mod.rs:82-93`, `mod.rs:712`; `fs/lib.rs:69-73` | seed | OK |
| 107 | `py:1366-1369`, `py:347-351` | Python seed | OK |
| 108 | `08:55` quote | sizes | OK |
| 108 | `mod.rs:118-124`; `mod.rs:144-149` | prover, verifier | OK |
| 108 | `py:1372-1376` | Python | OK |
| 109 | `mod.rs:133-135` quote | upper limbs | OK (the `;` after `Err(...)` omitted) |
| 109 | `py:1373` | Python | OK |
| 110 | `08:29` quote | top limb 0 | OK |
| 110 | `mod.rs:141-143` | Rust | OK |
| 110 | `py:204-219` | `Digest` type | OK |
| 111 | `06:80`, `06:86`, `06:90` | caps | OK |
| 111 | `mod.rs:157-170` | caps | OK |
| 111 | `py:857-864`, `py:1377` | Python | OK |
| 112 | `08:55` quote | derives layouts | OK |
| 112 | `mod.rs:171`, `layout.rs:328-427`, `witness.rs:67-102` | layout | OK |
| 112 | `py:856-895`, `py:506-511` | Python | OK |
| 113 | `mod.rs:174-176`; `pcs.rs:49, 51` | window | OK |
| 113 | `py:1379`; `py:907-908` | Python | OK |
| 114 | `08:60-61` "sends its commitment" | spec | OK (at 60) |
| 114 | `pcs.rs:118-119`, `mod.rs:560-562` | prover | OK |
| 114 | `mod.rs:714`, `pcs.rs:136-138`, `fs/transcript.rs:97-99` | verifier | OK |
| 114 | `py:1382` | Python | OK |
| 115 | `fs/merkle.rs:26-29`; `py:223` | halves | OK |
| 117 | `pcs.rs:93-96` quote | root before challenges | OK (94-95) |
| 118 | `leaf.rs:876` | first sample | OK |
| 124 | `leaf.rs:875`, `leaf.rs:123-146` | assertions | OK |
| 125 | `08:67`; `05:22`, `05:28` | `(α, β)` | OK |
| 125 | `leaf.rs:876`, `leaf.rs:882`; `py:542`, `py:544` | draws | OK |
| 126 | `08:68` quote | roots, prose order | OK |
| 126 | `gkr.rs:272-276`; `gkr.rs:364-367` | prover, verifier | OK |
| 126 | `py:434`, `py:437` | Python | OK |
| 127 | `05:91`; `gkr.rs:369`; `py:435` | first combiner | OK |
| 128 | `05:61-95`, `08:69` | GKR | OK |
| 128 | `gkr.rs:373-427`; `py:439-455` | loop | OK |
| 129 | `06:78`, `08:69`, `08:100` | `R_c ≠ 0` | OK |
| 129 | `leaf.rs:884-889`; `py:546` | check | OK |
| 130 | `08:70` quote; `05:111` | boundary evaluations | OK |
| 130 | `leaf.rs:909-920`, `leaf.rs:428-439`, `leaf.rs:548-550`; `leaf.rs:500-529` | verifier, prover | OK |
| 130 | `py:552-557` | Python order | OK |
| 131 | `08:70`; `05:105-123` | decomposition | OK |
| 131 | `leaf.rs:389-461`, `leaf.rs:921-924`; `py:559-590` | derived `rem_s` | OK |
| 133 | `mod.rs:726`, `py:1389` | ξ next | OK |
| 156 | `gkr.rs:358-430`, `py:433-457` | same loop | OK |
| 161 | `gkr.rs:377`, `py:442` | parity | OK |
| 162-163 | `gkr.rs:378` quote | binary only first | OK |
| 163 | `05:85` | spec | OK |
| 167 | `gkr.rs:376`; `primitives/src/multilinear.rs:245-247`; `py:443` | claim | OK |
| 169 | `05:91-94` | powers of λ | OK |
| 173-174 | `gkr.rs:319-326`; `gkr.rs:399-401` quote; `py:445` | 4 elements | OK |
| 176-177 | `fs/transcript.rs:297-302` quote; `py:411-413` | `c_0` derived | OK |
| 179 | `gkr.rs:402-404`, `py:424-426` | χ and new claim | OK |
| 185 | `gkr.rs:4-5` quote | normalized, degree four | OK |
| 187 | `gkr.rs:406-409`, `py:447` | 12 children | OK |
| 189 | `gkr.rs:410-413`, `py:448-449` | check, no eq factor | OK |
| 190-192 | `gkr.rs:414-415`, `py:451`; `gkr.rs:416-422`, `py:452` | `u_0, u_1`, interpolation | OK |
| 193 | `gkr.rs:423`, `py:453` | new combiner | OK |
| 194 | `gkr.rs:424-425`, `py:454` | new point | OK |
| 198 | `gkr.rs:377-395`, `py:442-455` | binary layer | OK |
| 203 | `gkr.rs:423`, `gkr.rs:429`; `py:453`, `py:457` | last combiner unused | OK |
| 211-213 | `gkr.rs:479-508` "`proved.values[lane] == mle_eval_e(…)`" | test | OK (the source is `assert_eq!(proved.values[lane], mle_eval_e(&leaves[lane], &proved.point))`, line 497; paraphrased as `==`) |
| 213 | `gkr.rs:436-447` | `mle_eval_e` low bit first | OK |
| 229-230 | `leaf.rs:879-881` quote `count_lay.mu = push_lay.mu`; `py:540`, `py:578-579` | count tree padded | OK (quote at 881) |
| 234 | `layout.rs:349-415`; `py:537-540`, `py:866-876` | block order | OK |
| 238 | `layout.rs:335, 355-358` | final state | OK |
| 241 | `layout.rs:412-414` | count blocks | OK |
| 244-245 | `witness.rs:67-79` quote; `leaf.rs:149-156`; `py:305-311` | placement | OK |
| 246 | `leaf.rs:407-411`; `py:299-302` | selectors | OK |
| 247-248 | `leaf.rs:153`; `witness.rs:97` | no floor vs floor | OK |
| 250 | `leaf.rs:226-260` | leaf value | OK |
| 252 | `leaf.rs:89-98` | weights | OK |
| 253 | `leaf.rs:606-622`; `py:573` | count side at 0 | OK |
| 253 | `leaf.rs:222-224`, `gkr.rs:61, 114` | padding 1 | OK |
| 258-259 | `primitives/src/field/mod.rs:105-113`; `py:271-278`; `06:97-100` | index column | OK |
| 260 | `leaf.rs:440-457` | framework contribution | OK |
| 261 | `leaf.rs:466-471` | dedup | OK |
| 264 | `leaf.rs:416-423`, `leaf.rs:367-382`; `py:582-587` | forms | OK |
| 265-266 | `leaf.rs:459-460`; `py:589`; `05:107` | padding term | OK |
| 267-268 | `leaf.rs:921-924` quote; `py:590` | derived | OK |
| 270-271 | `leaf.rs:453`; `py:566`; `08:70` | bytecode evaluation | OK |

### Section F (status findings)

| L | Citation | Claim | Verdict |
| --- | --- | --- | --- |
| 660 | `st:309-310` | F3 | OK |
| 660 | `gkr.rs:362-367` quote; `py:434, 437`; `08:68-69` | one root | OK |
| 661 | `st:321-322` | F11 | OK |
| 661 | `layout.rs:412-414` quote; `layout.rs:187` | count blocks | OK |
| 661 | `py:733-735, 875-876` | Python | OK |
| 661 | `layout.rs:377, 395` | finalize counts on pull only | OK |
| 662 | `st:330` | F17 | OK |
| 662 | `witness.rs:70` quote; `layout.rs:13-26`; `layout.rs:41-46` | tie order | OK |
| 662 | `py:308`, `py:880-882` | Python | OK |
| 663 | `st:327-328` | F15 | OK |
| 663 | `mod.rs:157-176`; `pcs.rs:49, 51`; `py:857-864, 907-908, 1379` | caps, window | OK |
| 664 | `st:316-318`, `st:164` | F9 | OK |
| 664 | `py:857-864` | refutes F9 | OK |
| 665 | `leaf.rs:222-224` quote; `gkr.rs:61, 114` | leaves padded with 1 | OK |
| 665 | `witness.rs:152` quote | stack padded with 0 | OK |
| 665 | `05:20`, `05:103`, `04:8-10` | spec | OK |

### Section D (errors)

| L | Citation | Claim | Verdict |
| --- | --- | --- | --- |
| 382 | `05:36-38` quote | Theorem 5.1 | OK |
| 383-384 | Lemma 5.2, Corollary 3.9; `05:58` | proof | OK |
| 384 | `05:50-52` | proof TODO | OK |
| 385 | `03:79-85` | Fact 3.10 | OK |
| 387 | `03:87-93` | Definition 3.11 | OK |
| 388-389 | `03:110` quote | cofactor | OK |
| 390-391 | `05:61-95` | no GKR error | OK |
| 391-392 | `05:132` quote | recycling | OK |
| 394 | `B:74-82` | RBR definition | OK |
| 394-395 | `B:139-152` | RBR theorem, opening only | OK (no other RBR statement in the tex; `grep -i "round-by-round\|RBR"`) |
| 395 | `08:98` | cites theorem once | OK |
| 399 | `leaf.rs:108-118` | degree bound | OK |
| 401 | `leaf.rs:142-145`; `lib.rs` `pub const SECURITY_BITS: u32 = 128` | assertion | OK (`lean_vm/src/lib.rs:69`) |
| 402 | `leaf.rs:945-950` | to μ = 61 | OK |
| 404 | "the GKR's sum is `μ² + 2` (D.3)" | cross-reference | NOT SUPPORTED (D.3 gives `μ²`; see summary item 10) |
| 411 | `Component.lean:93-94` | input statement includes oracles | WRONG LINE (91 and 98) |
| 413-414 | `RoundByRound.lean:164-188` (dca90385) | knowledge state function | OK (164-189) |
| 417-418 | `:553-569` | worst-case RBR | OK (553-568) |
| 442 | `05:106-108` | decomposition | OK |
| 473 | "with the blueprint's numbers `… + 2`" | arithmetic | NOT SUPPORTED (see summary item 11) |
| 479 | `bp:974`, `bp:924-926` | `(α, β)` error | OK |
| 480 | `bp:941` | combiner error | OK |
| 481 | `bp:941-942` | 5 per round | OK |
| 482 | `bp:942` | pair error | OK |
| 483 | `bp:333`, tracker P2 | per-constraint charge | OK |
| 484 | `bp:1001-1003` | Layer 7 charge | OK |
| 485 | `bp:974` | no zerocheck term | OK |
| 487 | `bp:1130` | `piopError_le` | OK |

### Section E (the slot)

| L | Citation | Claim | Verdict |
| --- | --- | --- | --- |
| 502-514 | `Seams.lean:71-79, 91-95, 130-134` code | `VirtualTerm`, `LinearClaim`, `BusOut` | OK (docstrings omitted, code verbatim) |
| 519 | `Seams.lean:82-99` | term value, `Holds` | OK |
| 525 | `mod.rs:404-422`; `05:145` | ξ order | OK |
| 529 | `tables.rs:70-74, 722-724` | two JUMP identities | OK |
| 543 | `leaf.rs:275-281` | forms over `E` | OK |
| 546 | `leaf.rs:849-860` | `BusVerify` | OK |
| 553 | `gkr.rs:273` | prover asserts one root | OK |
| 566 | `Instance.lean:201` | `Balanced` is `Perm` | OK |
| 570 | "Lemma 6.2" | invariant count lemma | NOT SUPPORTED as numbered (Lemma 6.3) |
| 577 | `Arithmetization/Statement.lean:240-243` quote | CountsNonzero | WRONG LINE (quote at 235; definition 240-243) |
| 591-599 | `Instance.lean:86-98` code | `Coord`, `BoundaryBlock` | OK (docstrings omitted) |
| 602 | `layout.rs:354-395` | framework blocks | OK |
| 614 | `leaf.rs:442-454` "other cases `unreachable!`" | framework coordinates | NOT SUPPORTED in part (`GCol` handled at 446; only `Prod`/`Sum` unreachable) |
| 615 | `layout.rs:335`, `layout.rs:343` | depends on program | OK |
| 617 | `mod.rs:745-755` | public words only in the public-input phase | OK |
| 624 | `bp:836-839` | shared columns as tables | OK |
| 625 | `Arithmetization/Statement.lean:272-293` | index and program as cells | OK |
| 646 | `Instance.lean:174-186` | tuples | OK |
| 649 | `Seams.lean:171` | `Seam.commit` | OK |
| 651 | `tests/LeanerVMTests/Protocol/Spine.lean:26-82` | each clause fails alone | OK |

### Section C (blueprint set against it)

| L | Citation | Claim | Verdict |
| --- | --- | --- | --- |
| 318 | `Spine/Instance.lean:119-148` | `M3Instance` | OK |
| 322 | `:219-220` | `M3Holds` | OK |
| 324 | `Spine/Phase.lean:37-38` | `Phase.Def` | OK |
| 331-334 | `Compose.lean:76, 96, 115` code | bus slot | OK (verbatim) |
| 339 | `bp:325` | row Fiat–Shamir | OK |
| 340 | `bp:795-798`; `bp:316`; test 21 | sizes as parameters | OK |
| 340 | acceptance test 12 "says so" (8 elements before the root) | order | NOT SUPPORTED in detail (see summary item 9) |
| 342 | `Statement.lean:72-73` | by type | OK (`Arithmetization/Statement.lean`) |
| 343 | `bp:800-801`; row Stacks | admissibility | OK |
| 344 | `Compose.lean:55-56` | stack as oracle | OK |
| 345 | `bp:326` quote | verifier shape | OK |
| 346 | `bp:959` | `V_to_P` type | OK |
| 347 | test 4 | roots | OK |
| 348 | `bp:321` | combiners | OK |
| 349 | test 17 | radix | OK |
| 350 | `bp:315`, `bp:898-901` | round messages | OK |
| 353 | `bp:973`; test 3 | `R_c ≠ 0` | OK |
| 354 | test 4 | one root | OK |
| 355 | `bp:324` | claim pool order | OK |
| 356 | `Seams.lean:71-99`, `bp:565-574` | linear claims | OK |
| 357 | `bp:320`; test 18 | count tree | OK |
| 358 | test 2 | padding | OK |
| 360 | `bp:319`; test 1 | fingerprint | OK |
| 361 | Layer 5 test | leaf changed rejected | OK (`bp:946`) |
| 363 | `bp:974` | busError | OK |
| 364 | `bp:940-942` | gkrError | OK |
| 365 | `bp:333`, `bp:974`, `bp:1000-1003`, tracker P2 | four versions | OK |
| 366 | `bp:954-979` | Layer 6 sketch | OK |
| 367 | `bp:930-937` | Layer 5 `gkr` | OK |
| 369 | test 1, `05:58` | degree 4 | OK |
| 371-372 | test 18 quote "the leaf layout, and so `ζ`, differ" | loose | OK (`bp:1318-1319`) |

### Summary, H and I

| L | Citation | Claim | Verdict |
| --- | --- | --- | --- |
| 53 | `py:857-864` | Python checks the caps | OK |
| 1049 | sha256 `28018d8c…3634` | copy identical | OK (both files hash to it) |
| 1305-1328 | probe H.1 output | counts, draws, attack | OK (re-run 2026-09-30 from a scratch copy, Python 3.13.1, exit 0, output identical line for line) |
| 1058-1303 | H.1 source reproduced | full source | OK for the code; the file's 17-line leading docstring is not reproduced |
| 1345 | H.2 output "none, exit status 0" | probe | COULD NOT CHECK (no Lean, brief section 8) |
| 1345-1347 | control copy fails; `#print axioms` output | probe | COULD NOT CHECK (same) |
| 1352-1466 | H.2 source reproduced | full source | OK for the code; the file's 15-line leading docstring is not reproduced |
| 1478 | `docs/leanvm-target.md:66` | repository's own differential tests | OK |


## 3. Independent checks (read from the code, not from the dossier's reasoning)

All at leanVM `a386121f`. Rust paths are under `crates/lean_vm/src/` unless they are prefixed
`fiat_shamir/`, which is `crates/fiat_shamir/src/`.

**3.1 Stream elements per message: agree, every count.**

| Message | Elements | Where it is read |
| --- | --- | --- |
| roots | 2 | `gkr.rs:364-367`; `py:434` |
| radix-4 round | 4 | see below |
| radix-4 children | 12 | `gkr.rs:406-409`, `[[F192::ZERO; 4]; 3]`; `py:447` |
| binary-layer children | 6 | `gkr.rs:379-382`, `[[F192::ZERO; 2]; 3]`; `py:447` with `2**1` |
| boundary evaluations | 5 | see below |
| announced sizes | 8 | `mod.rs:144-149` (1 + 6 + 1); `py:1372`, `next_scalars(2 + len(TABLES))` |
| commitment root | 2 | `fiat_shamir/transcript.rs:97-99` via `pcs.rs:136-138`; `py:1382` |

- **Radix-4 round, 4 elements.** `gkr.rs:399-401` calls `next_round_poly(5, claim,
  Some(equality_point))`. With `eq = Some(_)`, `fiat_shamir/transcript.rs:291-295` sets
  `fixed = 0` and reads every other index, 4 in all. In Python, `py:445` passes
  `count = 2**2 + 1 = 5` and `py:412` reads `next_scalars(count - 1)`.
- **Boundary evaluations, 5.** The fresh columns are enumerated by `leaf.rs:428-439` with the
  deduplication of `:466-471`. On the push side the memory seed contributes `MEM_LO, MEM_HI,
  MEM_TOP` (`layout.rs:361-371`). On the pull side the memory finalization contributes
  `MFCNT` (the three memory limbs are already claimed at the same `ζ_{<κ_mem}`,
  `layout.rs:372-382`), and the bytecode finalization contributes `BFCNT` (`:395`). The state
  blocks carry constants only, the bytecode seed carries `Const`, `Index` and `Public` only,
  and every count block has an owner. Python reads the same five in the same order
  (`py:552-554`).
- **Totals.**
  - Even `μ`: the GKR sends `Σ_{k=0,2,…,μ−2}(4k + 12) = μ² + 4μ`.
  - Odd `μ`: `6 + Σ_{k=1,3,…,μ−2}(4k + 12) = μ² + 4μ + 1`.
  - Both agree with the dossier and with the re-run probe (`μ = 0 … 12`).

**3.2 A combiner is drawn after every layer, the last included, and the last is never used:
agree.**
- Rust verifier: `gkr.rs:391` (binary) and `:423` (radix 4) draw the combiner unconditionally
  at the end of the iteration. The loop then exits on `layer == 0` (`:374`) and returns
  `ProductTriple { roots, point, values }` (`:429`), which holds no `lambda`.
- Rust prover: the same, at `gkr.rs:302, 348`.
- Python: `py:453` draws the combiner and `py:457` returns `count, point, values`.
- Hand count at `μ = 4`: draw 0 is `λ`; the root layer draws `u` at 1 and 2 and `λ` at 3; the
  next layer draws `χ` at 4 and 5, `u` at 6 and 7, and `λ` at 8. So `ζ = (6, 7, 4, 5)` and
  draw 8 is unused, as the dossier says.

**3.3 The final point is `(u_0, u_1, χ_0, …)` of the last layer: agree.**
- Rust: `gkr.rs:424-425` (`point = vec![low_challenge, high_challenge];
  point.extend_from_slice(&round_point)`) replaces the point each iteration, and so does
  `py:454` (`point = [*y, *x]`).
- The binary layer sets `point = vec![challenge]` (`gkr.rs:392`).
- `u_0` weighs the low child bit (`gkr.rs:417-421` with `interp(lo, hi, t) = lo + t·(lo + hi)`,
  `primitives/src/multilinear.rs:39-41`).

**3.4 The GKR layer's final check has no equality factor; the table sumcheck's does: agree.**
- GKR: `gkr.rs:410-413` compares `claim` with `poly_eval(&products, lambda)`, the λ-combination
  of the products of the children, with no factor.
- The running claim is the cofactor's value, for three reasons:
  - `c_0` is derived through `r = point[t]` (`fiat_shamir/transcript.rs:297-302`);
  - the new claim is `poly_eval(&h, challenge)` (`gkr.rs:404`);
  - the prover's message factors out `eq(point[t], ·)`, since `equality = eq_table(&point[1..])`
    (`gkr.rs:312`) is shrunk each round (`:332`).
- Table sumcheck: `constraints.rs:271-274` multiplies `eq_k = 1 + ζ[m] + r_k`, or `r_k` for a
  table not yet joined, into `weights[t]`. `:282` multiplies `weights[t]` into the final value.
  `:288` compares.
- Python has the same split (`py:449` against `py:611-614, 622, 625`).

**3.5 The Python verifier checks the caps and the stacking window: agree.**
- Caps: `py:856-864`, every one of the four the status says is omitted. `log2_strict` at
  `py:857` enforces the power of two (`py:252-254`).
- Rate: `py:1377`.
- Stacking window: `py:1379`, with `MIN_STACKED_LOG = 15`, `MAX_STACKED_LOG = 28`
  (`py:907-908`), after `stack_log = max(15, total_log)` (`py:890`).
- The check is not new at the pin: it appears in `8a6e7750`, earlier than the dossier says
  (summary item 2).

**3.6 The Rust verifier rejects a public word with a nonzero third limb, and announced sizes
with nonzero upper limbs: agree.**
- Public words: `mod.rs:141-143`, `if public_input.iter().any(|half| half.c2 != 0) { return
  Err(CpuError::PublicInput); }`. This runs before any size is read (`:144`).
- Sizes: `mod.rs:133-135`, `if word.c1 != 0 || word.c2 != 0 { return
  Err(CpuError::PublicInput); }`, inside `read_size`, applied to all 8 sizes (`:144-149`).

**3.7 `nfl = (5, 5, 3, 5, 5, 11)` and `ncnt = (4, 4, 2, 4, 4, 10)`: agree.**
- Every `FlushBuilder` method adds exactly one push and one pull through `pair`
  (`tables.rs:121-124, 127-182`).
- Table order is `[XOR, MUL, SET, DEREF, JUMP, BLAKE2S]` (`tables.rs:355-364`).
- Flushes per table:
  - XOR and MUL (`Arith`, `:483-495`): `state_step`, `bytecode`, two `memory`, one
    `memory_coords`, so 5;
  - SET (`:548-561`): 3;
  - DEREF (`:633-643`): `state_step`, `bytecode`, `memory_k`, `memory_coords`, `memory`, so 5;
  - JUMP (`:731-751`): `state_derived`, `bytecode`, three `memory_k`, so 5;
  - BLAKE2S (`:873-908`): `state_step`, `bytecode`, nine `memory_128`, so 11.
  - Sum 34.
- Count columns: `[RA, RB, RC, RBC]` (`:479-482`, both arithmetic tables), `[R, RBC]`
  (`:544-547`), `[R1, R2, R3, RBC]` (`:629-632`), `[RC, RD, RF, RBC]` (`:718-721`), and ten
  for BLAKE2S (`:869-872`). Sum 28.
- Python gives the same flushes (`py:738-818`) and the same count columns (`py:733-735`, the
  `cnt*` columns of `py:823-834`).
- The committed widths the dossier uses in D.4 are also right: `15, 15, 8, 15, 14` at
  `tables.rs:455, 537, 608, 711`, and BLAKE2S `37 − 18 = 19` (`:862`, with the 18 virtual
  value columns of `BLAKE2S_VALUE_COLS`, `:394`).

**3.8 The numbers of D.4: agree.**
- At the per-logarithm caps, `N_push = 1 + 2^32 + 2^32 + 34·2^32 = 36·2^32 + 1`, so
  `μ_bus = 38` and `4·2^38 = 2^40`.
- The stack dominates the push leaves: for each table, its committed columns (15, 15, 8, 15,
  14, 19) outnumber its flush pairs (5, 5, 3, 5, 5, 11), and the memory has 4 columns for one
  push block. So `N_push ≤ Σ_stack 2^κ ≤ 2^μ_stack ≤ 2^28`.

## 4. Other things noticed while checking (not citations, or beyond them)

1. **"The whole cubic is sent, `c_1` derived" (dossier line 682) contradicts itself.** For the
   table sumcheck the wire carries three of the cubic's four coefficients, `c_0, c_2, c_3`, and
   the verifier derives `c_1`:
   - `fiat_shamir/transcript.rs:291-299` (`fixed = 1` when `eq` is `None`);
   - `py:409-410`;
   - the blueprint's acceptance test 8 (`bp:1287-1289`), "the wire carries three coefficients".

   The point the dossier makes (the table sumcheck is the plain variant, the GKR's the
   normalized one) is right. Proposed wording: "three of the cubic's four coefficients are
   sent, `c_1` derived".
2. **The implied caps of B6 are true but loose** (dossier line 295: "`μ_stack ≤ 28` forces
   `τ_j ≤ 24`, `κ_mem ≤ 26`, `κ_bc ≤ 28`"). Every column placed in the stack adds to the total,
   so the tight bounds are lower:
   - `κ_mem ≤ 25`: four memory columns at `κ_mem = 26` already fill `2^28`, and `q_flock`
     (at least `2^11`) and the table columns overflow it;
   - `κ_bc ≤ 27`;
   - `τ_BLAKE2S ≤ 19`: 19 columns plus `q_flock` at `2^(τ+8)`;
   - `τ_j ≤ 24` for the other tables is tight.

   Nothing in the dossier depends on the looser figures.
3. **The probe sources are not reproduced in full.** The brief (section 2) asks that every probe a
   conclusion rests on be reproduced "full source". The dossier's copies of `gkr_probe.py` and
   `BusSeam.lean` omit each file's leading docstring (17 and 15 lines of comment). The code is
   identical (`diff` shows only the docstrings and the fences).
4. **The probe H.1 is reproducible.** Re-run on 2026-09-30 from a scratch copy of
   `probes/gt-bus/` (sha256 of `pinned_verifier.py` equal to the pinned `verifier.py`), with
   `PYTHONDONTWRITEBYTECODE=1 python3 gkr_probe.py`. Exit 0, and the output is identical to the
   dossier's lines 1308-1327.
5. **The pinned Rust contradicts itself** (not a dossier error; for the orchestrator's G15-type
   list). The comment at `constraints.rs:265-266` says "`h(0)` is derived from the running
   claim rather than transmitted", but the call at `:267`, `next_round_poly(4, claim, None)`,
   transmits `c_0 = h(0)` and derives `c_1` (`fiat_shamir/transcript.rs:291, 299`). The comment
   is stale; the code and the Python agree with each other.
6. **The dossier's reading of the tracker holds today.** The hole comment was last edited
   2026-09-28T14:28Z. Every tracker quotation the dossier makes is present verbatim in the
   current text:
   - "degree-5 round polynomials" (G5, line 33);
   - `busPhase I (G : Gkr.Def) : Phase.Def I Unit (BusOut I) (busSpec I) (M3Holds I)
     (Seam.bus I)` and "specification (5.4)" (P1, line 66);
   - the P2 error, "`1/|E|` per coordinate per constraint" (line 67).
7. **No finding of the dossier is weakened by the corrections above.** The corrections are:
   Lemma 6.3 for 6.2, the commit provenance of the Python caps, two line numbers, the
   attribution of `appendGuarded`, and two pieces of arithmetic in D.2 and D.3. G5 (the status's
   F9 is false) stands, since the Python cap check is present at the pin whichever commit
   introduced it.
