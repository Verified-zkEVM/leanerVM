# Verification of the dossier `gt-opening-compile`: citations and quotations against the sources

Task `verify-gt-opening`, 2026-09-30. Dossier under check (read only, not edited):
`.claude/reports/blueprint-review/dossiers/gt-opening-compile.md`. Its line numbers are written
`D:<line>`. The sources were read as follows:

- leanVM at `a386121f84292f6fa663aaa3e570c15bc0240ea2`, file by file, with `git -C
  /home/scaraven/Documents/leanEthereum/leanVM show a386121f…:<path>`. The working tree is off the
  pin (HEAD `248da071`) and was not read for the pin.
- leanerVM (blueprint, status, `architecture.md`, Lean) at `b435631`, with `git show`.
- ArkLib at the old pin `dca90385` with `git -C .lake/packages/Arklib show dca90385…:<path>`, and
  at the new pin `7653a901` from the working tree of `.lake/packages/Arklib` (its HEAD is
  `7653a901`). ArkLib pull request #848's head `1c5c5bd7` was read from `../ArkLib`'s object store.
- GitHub metadata for ArkLib #469, #848 and #627, read only, with `gh … view`.

No Lean was run. One Python scratch script was run (section 4) to check the dossier's numeric
ranges. Nothing tracked was edited.

(Sections are appended as they are done; the summary is written last.)

## 2. The full table

One row per citation, or per group of citations on one dossier line that share a verdict.
Abbreviations as in the dossier: `08`, `03`, `04`, `06`, `A`, `B` are the pinned spec files;
`whir.rs`, `whir_config.rs`, `whir_induce.rs`, `stack_open.rs`, `pcs/merkle.rs` are under
`crates/pcs/src/`; `fs/lib.rs`, `fs/transcript.rs`, `fs/merkle.rs` under
`crates/fiat_shamir/src/`; `mod.rs` is `crates/lean_vm/src/cpu/mod.rs`; `py` is
`python-verifier/verifier.py`; `bp` the blueprint at `b435631`. Verdicts: `OK`, `WRONG LINE`,
`MISQUOTED`, `NOT SUPPORTED`, `COULD NOT CHECK`.

### 2.1 Section I (findings)

| # | D-line | Citation | Claim | Verdict | Correction or note |
| --- | --- | --- | --- | --- | --- |
| I1 | 1678 | `08:99` | one opening discharges every pooled claim, no separate reduction sumcheck | OK | |
| I2 | 1678 | `stack_open.rs:452-461` | one WHIR call on `(stack, b_stack, target)` | OK | comment at 450-451 |
| I3 | 1678 | `whir.rs:1324-1334` | WHIR's first act is its round polynomial, then six lane folds | OK | |
| I4 | 1678 | `py:1362, 1012` | Python calls `verify_whir`, whose first read is a round polynomial | OK | |
| I5 | 1681-1685 | `bp:1112-1114` (quoted block) | Layer 10 `openingPhase` schedule and error | OK | verbatim |
| I6 | 1693 | `bp:317` (quoted) | convention *The oracle* | OK | verbatim |
| I7 | 1696 | `bp:637-642` | Layer 0 `evalOracle` | OK | |
| I8 | 1698 | `bp:1214` (quoted) | "WHIR in place of the evaluation oracle" | OK | |
| I9 | 1700 | `bp:127` | scope names "the opening sumcheck" | OK | |
| I10 | 1707 | `Basic.lean:490-496` (dca90385) | `OracleVerifier.toVerifier` | OK | `ArkLib/OracleReduction/Basic.lean` |
| I11 | 1707 | `FiatShamir/Basic.lean:129-136` (dca90385) | `Verifier.fiatShamir` | OK | same lines at 7653a901 |
| I12 | 1707 | `BCS/Basic.lean:59-63` (dca90385) | `BCSTransform` commented out | OK | unchanged at 7653a901 |
| I13 | 1708 | `fs/transcript.rs:9-12` | `Proof { stream, merkle }` | OK | |
| I14 | 1708 | `fs/transcript.rs:225-228` | Merkle hints are not absorbed | WRONG LINE | the sentence "Not absorbed: its binding is the Merkle structure itself." is the doc comment at `fs/transcript.rs:223-224`; `hint_merkle` is 225-227. The claim is right. |
| I15 | 1708 | `fs/lib.rs:165-174` | the grind check reads the chain state and binds the nonce either way | OK | |
| I16 | 1712 | `bp:1218-1221, 1231-1232` | `verify_iff_compiled`; "unconditional: it is about two definitions" | OK | |
| I17 | 1724 | `bp:1247-1248`, `bp:326` | T4 sketch; `verify` total and computable to `Bool` | OK | |
| I18 | 1724, 1738 | `architecture.md:264-273`, `:264-269` | T4 text | OK | |
| I19 | 1727-1730 | `bp:1247-1248` (quoted) | `baseVerifier_extractsExecution` sketch | OK | verbatim |
| I20 | 1744 | `FiatShamir/Basic.lean:163-175` | completeness admitted; soundness a TODO | OK | identical lines at both pins |
| I21 | 1744 | `Implications.lean:230-254, 305-313` | rbr ⇒ state-restoration commented out; state-restoration ⇒ knowledge soundness admitted | OK at dca90385 | "at both pins" (D:1745) gives only old-pin lines: at 7653a901 the same text is at `Implications.lean:200-224` and `:275-283` |
| I22 | 1745 | `BCS/Basic.lean` | commented out at both pins | OK | no diff between the pins |
| I23 | 1745 | `Commitments/Functional/Basic.lean:250-255` "at both pins" | `extractability` body `False` | OK at dca90385 | at 7653a901 it is `:249-254`. Exact shape: `∃ _extractor, ∀ AuxState, ∀ _adversary, ∀ _prover, False`, with the real statement commented out below it |
| I24 | 1746 | `SingleSalt.lean:973-993` at #848's head `1c5c5bd7` | `single_salt_fiat_shamir_knowledge_soundness` | OK | `ArkLib/OracleReduction/FiatShamir/SingleSalt.lean` |
| I25 | 1746 | issue #627's plan | out-of-scope sentence | OK | `gh`: #627 is an issue (no pull request resolves); the sentence is verbatim (body line 29) |
| I26 | 1751-1755 | `bp:1223-1225` (quoted) | the two assumed interfaces | OK | verbatim |
| I27 | 1765-1766 | `bp:263`, `bp:614` | ledger A5, holes row K3 | OK | |
| I28 | 1774 | `B:4, 70-72, 133-137` | only list binding; Definition B.4; `R_open`; `L_0` | OK | |
| I29 | 1774 | `whir_config.rs:593-599` | the L0 union over the list, `L·μ/|F|` | OK | quotation verbatim at 596-598 |
| I30 | 1774, 1778 | `bp:1190`, `bp:1296-1299` | "Layer 12 turns list binding into extraction…"; test 11 | OK | |
| I31 | 1791, 1801 | `fs/lib.rs:126-155` | unbounded grind | OK | see check 6 |
| I32 | 1791 | `Compose.lean:94-104` | `Phases.Complete` | OK | |
| I33 | 1794 | `bp:1255-1257` (quoted) | "perfect completeness survives the transform without any assumption" | OK | verbatim |
| I34 | 1807 | `whir_config.rs:25-27, 36-38, 57-60, 537-568, 593-599` | round-by-round target, max per query, grinding, algebraic, L0 union | OK | |
| I35 | 1807, 1905 | `leaf.rs:108-118` | the bus bound has no list factor | OK | the Rust bound is `(N_TUPLE_BITS+1)·2^μ + 8(μ+1)² = 5·2^μ + …`, not the blueprint's `4·2^μ` (the dossier's "the bus's `4·2^{μ_bus}`" at D:743, 1905 names the blueprint's term) |
| I36 | 1810 | `bp:1234-1235` (quoted) | `niError` sentence | OK | |
| I37 | 1818 | `py:910` | query table | OK | |
| I38 | 1825 | `B:108-110`; `whir.rs:419-485`; `bp:1169, 1173, 1185` | level-0 batch; deeper E-valued encode; blueprint lines | OK | |
| I39 | 1828 | `B:306` | a `K`-valued message gives a `K`-valued word | OK | |
| I40 | 1832 | `B:309-315`; `whir_induce.rs:220-224` | Lemma B.14; the closed form | OK | |
| I41 | 1833 | `bp:1170` (quoted) | `encode_column_weight` | OK | verbatim |
| I42 | 1842-1843 | `fs/transcript.rs:9-19, 198-203`; `fs/merkle.rs:78-92, 246-264`; `py:392-404, 1049`; `python_verifier.rs:50-80` | the two Merkle forms | OK | the harness is `crates/lean_vm/tests/verifiers/python_verifier.rs` |
| I43 | 1856 | `whir.rs:2297-2306` | rotation of the terminal point | OK | |
| I44 | 1856-1857 | evidence B.1 for (b) "per-claim intro round polynomials for the OOD claim and the query batch, sent before the level's `λ_i`" | ordering | NOT SUPPORTED | only the OOD intro precedes `λ_i` (`whir.rs:1201-1208`, called at 1362/1528, before 1373/1534). The query-batch intro is sent **after** `λ_i`: prover `whir.rs:1373` then `1405-1406`; `1534` then `1558-1559`; `1439` then `1465-1466`; verifier `2123` then `2142`, `2331` then `2348`, `2211` then `2228`; Python `py:1044` then `1057`. The query batch's own claim even depends on `λ_i` (its weights are `power_weights(λ_i)`, `whir.rs:1374`). Same error in the summary, D:93-94 |
| I45 | 1863 | `whir_config.rs:624-707` | `η` search | OK | |
| I46 | 1869 | `preamble/theorems.tex:4, 12` | `protocol` shares the theorem counter, per section | OK | |
| I47 | 1870-1872 | the renumbering B.6, B.7, B.4, B.14, §B.5, §B.3 | Annex B numbers | OK | counted; see check 8 |
| I48 | 1870 via D:986 | "Definition B.1" at `bp:1187` | blueprint line | WRONG LINE | "(Definition B.1)" is at `bp:1188` |
| I49 | 1871-1872 | `bp:278`, `bp:1172` | "Annex B.3", "(Annex B.4)" | OK | |
| I50 | 1877 | `fs/lib.rs:18-24`; `hash.rs:83-87, 209-224`; `bp:216, 325, 1204` | the chain step is one 64-byte BLAKE2s | OK | `crates/primitives/src/hash.rs`; the one-compression statement is also the doc comment at `hash.rs:77-81` |
| I51 | 1891 | `py:856-864` | Python checks the caps | OK | `build_layout`, called at `py:1378` |
| I52 | 1893 | `protocol-status.md:316-319, 164` | status finding F9 | OK | |
| I53 | 1907-1908 | `whir.rs:393-395`, `:463` | stale leaf-size comment | OK | |

### 2.2 Section A (the opening as deployed)

| # | D-line | Citation | Claim | Verdict | Correction or note |
| --- | --- | --- | --- | --- | --- |
| A1 | 128, 136 | `04:14-18`, `08:97` (quoted) | a pooled claim becomes a weighted claim on the stack | OK | quotation of `08:97` verbatim up to TeX |
| A2 | 136 | `mod.rs:790-814` | `slot_claims`: `Point` and `Strided` | OK | |
| A3 | 136 | `py:520-522`, `py:295-297` | `on_stack`, `stack_point` | OK | |
| A4 | 137 | `04:18` | `W(w) = eq((ζ, sel_i), w)` | OK | |
| A5 | 137 | `stack_open.rs:294-303`, `:305-323` | `stack_claim_eq_at`, point and strided forms | OK | the point arm ends at 304 |
| A6 | 137 | `py:522` | `lambda x: eq_eval(point, x)` | OK | |
| A7 | 138 | `08:91`, `A:46` | ring-switched weight `Φ(eq(r, u))` | OK | |
| A8 | 138 | `stack_open.rs:45-48` | formula of `b(x)` | OK | formula at 46-47 |
| A9 | 138 | verifier `stack_open.rs:530-546`; `py:1411-1412` | lifted ring weight | OK | |
| A10 | 141-142 | `stack_open.rs:529-548` (quoted), `py:1362`, `py:1079`, `03:113` | the weight is evaluated once, at the terminal point | OK | |
| A11 | 148 | `08:98` (quoted) | `λ` drawn after every claim value is bound | OK | |
| A12 | 148 | `stack_open.rs:397-400` (quoted), `:394`, verifier `:518` | `λ` after the six map challenges | OK | six: `COMPOSITION_SHIFTS: [usize; 6]`, `crates/pcs/src/ring_switch.rs:85` |
| A13 | 148 | `py:1361`, `py:1343` | Python order | OK | `RING_MAP_SHIFTS` has six entries (`py:1314`) |
| A14 | 149 | `08:98` (quoted); `stack_open.rs:401`; `mod.rs:656-667`; `py:1413`, `py:1395, 1402` | ring claim first, pool after in `finish_claims` order | OK | |
| A15 | 150 | `mod.rs:767` | one ring-switched claim | OK | `mod.rs:767` is the call; the single claim is built at `crates/flock/src/hash.rs:801-808` (`claims: vec![ring_claim(…)]`) |
| A16 | 151 | `08:99`; `stack_open.rs:521-527`, `:413-415, 257, 285`; `py:1362` | batched target | OK | |
| A17 | 152 | `08:99`; `stack_open.rs:531-546`; `py:1362` | batched weight | OK | |
| A18 | 156 | `whir_induce.rs:99-107` | "`powers` starts at `λ^0`" | WRONG LINE | `whir_induce.rs:99-107` is `power_weights` (the per-query weights inside a level). The `powers` that `stack_open.rs:400, 518` call is `crates/primitives/src/field/mod.rs:51-61` (`[x^0, x^1, …]`). Both start at `λ^0`, so the claim holds |
| A19 | 156 | `py:186-188` | Python `powers` from `ONE` | OK | |
| A20 | 160-162 | `08:99` (quoted) | the §8.5 sentence | OK | verbatim |
| A21 | 163-167 | `B:108-110` (quoted), `B:111` | Annex B's `Open`; step 1 batch; step 2 sumcheck | OK | but D:165-166 calls it "Protocol B.1's level-0 batching challenge": the pinned number is Protocol B.6 (the dossier's own numbering elsewhere) |
| A22 | 169-170 | `stack_open.rs:452-461` (quoted comment) | one WHIR over the full stack | OK | comment at 450 |
| A23 | 171-177 | `whir.rs:1324-1326` (code block) | first act | OK | verbatim |
| A24 | 179 | `whir.rs:509-511`, `:1328-1334` | `send_msg`; six fold rounds | OK | `initial_k = INITIAL_FOLDING_FACTOR = 6` |
| A25 | 181 | `whir.rs:1358` (quoted) | first recursive root after the folds | OK | |
| A26 | 182-183 | `whir.rs:2087-2090` (quoted), `:2100`, `:2104` | verifier mirror | OK | |
| A27 | 185-187 | `py:1362`, `py:1012` (quoted), `py:1017-1024`, `py:1034` | Python mirror | OK | |
| A28 | 191 | `whir_config.rs:748-751` (quoted) | `initial_k + Σ k + yr_log_n = log_n` | OK | |
| A29 | 196 | `whir.rs:1131-1154`, `:1681-1701`; `py:1058-1063` | per-level glue | OK | |
| A30 | 197-199 | `whir.rs:2308`; `py:1082-1083`; `whir.rs:2264-2307` | terminal equation and weight | OK | |
| A31 | 204-208 | `bp:1112-1114`, `bp:1101`, `bp:127` | Layer 10 text | OK | |
| A32 | 209-210 | `bp:1173`, `bp:1185` (quoted) | Layer 11 text | OK | |
| A33 | 211 | `bp:1214-1215` (quoted) | Layer 12 text | OK | |
| A34 | 213-215 | `bp:317`, `bp:637-642`, `Field.lean:102-106` (b435631) | the evaluation oracle | OK | |
| A35 | 223-224 | `bp:27-29` (quoted), `bp:1218-1221` | "the Fiat–Shamir compilation of that oracle verifier" | OK | |
| A36 | 243 | `03:112-118` (quoted) | Definition 3.13 | OK | thirteenth numbered environment of section 3 |
| A37 | 251-252 | `OracleInterface.lean:55-57` at dca90385 (quoted) | the class | OK | verbatim; same lines at 7653a901 |
| A38 | 253-254 | `Spine/Seams.lean:103-109`, `:112-113` (b435631) | `Weight`, `Weight.pair` | OK | |
| A39 | 256 | `ClaimWeights.lean:51-54` (b435631) | `eqWeight_pair` | OK | |
| A40 | 258 | `Commitments/Functional/Basic.lean:62-64` at dca90385 | `Commitment.Opening` statement type | OK | same lines at 7653a901 |
| A41 | 261 | `bp:249` (quoted) | `Commitment.Scheme` row | OK | |
| A42 | 269 | `FixedColumns.lean:59-61, 97-99, 113-115`; `tests/…/Protocol/Field.lean:30-44` | "the only consumers of `OracleInterface.answer` on a `Column`" | NOT SUPPORTED (incomplete) | `git grep` at b435631 also finds `tests/LeanerVMTests/Protocol/FixedColumns.lean:32, 49, 76, 115` (four more uses of `OracleInterface.answer` on columns) and the reference in the docstring of `LeanerVM/Protocol/Stack.lean:18`. The recommendation is unaffected in kind, but the list of files to change is longer |
| A43 | 270 | `PublicInput.lean:222-231` (b435631) | the public-input verifier queries only its own message | OK | `queryValues` queries `[pSpec.Message]ₒ` only. "No built proof changes" is the dossier's inference: every type that mentions `[TheOracle I]ₒ` (for example `PublicInput.lean:242, 246, 261, 263`) elaborates against whichever `OracleInterface` instance is in scope, so the claim needs a build to confirm (unverified) |
| A44 | 271 | `bp:600` | hole G3, batching by powers | OK | |
| A45 | 284 | `03:112-118`, `B:4` (quoted) | spec's own object | OK | |
| A46 | 294-295 | `Seams.lean:123-124`; `03:115` | `WeightedClaim.Holds` is `⟨W, g⟩ = c` | OK | |

### 2.3 Section E (the non-interactive theorems)

| # | D-line | Citation | Claim | Verdict | Correction or note |
| --- | --- | --- | --- | --- | --- |
| E1 | 303-318 | `bp:1218-1227`, `bp:1247-1250` (code block) | the four sketches | OK | verbatim lines; the docstring line `bp:1223` is omitted from the block (quoted later at D:1751) |
| E2 | 324 | `FiatShamir/Basic.lean:129-136` (dca90385) | `Verifier.fiatShamir` | OK | |
| E3 | 328 | `ProtocolSpec/Basic.lean:849-854` (dca90385) | `fsChallengeOracle` | OK | alias of `srChallengeOracle` at 854 |
| E4 | 329 | `:830-834` (quoted) | `Query := StmtIn × pSpec.MessagesUpTo i.1.castSucc` | OK | |
| E5 | 338 | `bp:326` (quoted) | `verify` total, computable, to `Bool` | OK | |
| E6 | 342, 345 | `architecture.md:264-269`, `:271-273` (quoted) | T4 text | OK | verbatim |
| E7 | 349, 351 | `bp:96-103`, `bp:96-99` | doctrine on extractors | OK | |
| E8 | 357-358 | `fs/lib.rs:18-24` (quoted "`f(a, b) = BLAKE2s(a‖b)`") | the primitive | WRONG LINE (minor) | the quoted text is the doc comment at `fs/lib.rs:9`; `compress` is 18-24 |
| E9 | 357-359 | `fs/merkle.rs:40-51` | the one compression `H : {0,1}^512 → {0,1}^256` is "used for the chain, the grinding and every Merkle node and leaf" | NOT SUPPORTED for leaves | nodes are one 64-byte BLAKE2s-256 (`hash_pair`, 44-51), i.e. one compression. Leaves are BLAKE2s-256 of the whole leaf image, 512 bytes at level 0 and 384 bytes deeper (`hash_leaf`, 38-42; `hash_words`, 61-67): eight or six compressions, chained through BLAKE2s's own chaining value and counter, the last with `f0` set (`hash.rs:209-219`; `pcs/merkle.rs:150-155` relies on exactly that chaining value for the zero prefix). A random oracle for the single 64-byte compression does not model the leaf hash; a ROM statement needs either the iterated construction or a second oracle for leaves |
| E10 | 361-362, 388 | `mod.rs:82-93`, `mod.rs:118-124` | seed from the program hash; sizes announced | OK | |
| E11 | 382, 386 | `mod.rs:144-149`; `bp:1326-1328` | dispatch on the sizes; test 21 | OK | |
| E12 | 407 | `FiatShamir/Basic.lean:163-173`, `:175` | admitted; constant challenge oracle; TODO | OK | constant: the initial table is `fun ⟨i, _⟩ => default` (163-169) and `fsChallengeQueryImpl'` answers from the table without updating it (`ProtocolSpec/Basic.lean:910-914` at dca90385, `:879-883` at 7653a901). Same at both pins |
| E13 | 408-410 | `Security/Implications.lean:230-254` | commented out; error `∑ i, rbrError i` | OK at dca90385 | 200-224 at 7653a901. The commented theorems are about the protocol "with arbitrary added non-empty salts" (`addSalt`), which the dossier does not say |
| E14 | 411 | `:305-313`; `BCS/Basic.lean:59-63, 79-82` | SR ⇒ KS admitted; BCS commented out | OK at dca90385 | 275-283 at 7653a901; BCS unchanged |
| E15 | 412 | `Commitments/Functional/Basic.lean:250-255` | `extractability` has `False` for its body | OK | see I23 |
| E16 | 413-418 | #469, #848, #627 | open since 2026-04-19, "statements of Section 5"; #848 stacked on #469, "prove Theorems 6.1 and 6.2"; #627 an issue of 2026-07-10 | OK | `gh`: #469 base `main`, head `dsfs-section5`, created 2026-04-19; #848 base `dsfs-section5`, head `1c5c5bd7`; #627 created 2026-07-10, not a pull request. "No security proof" for #469 was not checked beyond its title |
| E17 | 420 | `B:176-185` | Theorem B.9 statement | OK | |
| E18 | 423-440 | ArkLib `CapacityBounds.lean:203-219` (code block) | `rs_mcaError_le_in_johnson_range`, admitted | OK | verbatim at dca90385; identical lines at 7653a901 |
| E19 | 448-449 | `B:90, 302`, `B:158` | domain; affine-line footnote | OK | |
| E20 | 452 | "Lemma B.8 (`lem:fold-list`)" | numbering | NOT SUPPORTED | `lem:fold-list` is Lemma **B.10**; B.8 is `thm:mca-udr` (check 8). Same error at D:731 |
| E21 | 453 | `B:140-152` | Theorem 4.6 is "the only coding-theoretic input Theorem B.7 uses" | OK with a caveat | the Johnson bound (`thm:johnson-interleaved`, B.3, proved at `B:391-414`) and Lemma B.11 (Schwartz–Zippel) are also inputs; Theorem B.9 is the only *external* one. The blueprint's own `bp:1176` says "the only coding-theory input" |
| E22 | 466 | `fs/lib.rs:85-99` | the chain ratchets a state through `H` | OK | |
| E23 | 469-474 | `SingleSalt.lean:973-993` at `1c5c5bd7` | takes state-restoration knowledge soundness of a plain `Verifier` with coins, for `fsChallengeOracle (StmtIn × Salt) pSpec`, concludes adaptive NARG knowledge soundness | OK | |
| E24 | 472 | "implemented by lazy uniform sampling (`srChallengeQueryImpl'`)" | how the challenge oracle is implemented | NOT SUPPORTED | `srChallengeQueryImpl'` answers from a function that `fsInit` produced ahead of time and never updates it (`fun ⟨i, t⟩ => fun f => pure (f ⟨i, t⟩, f)`, `ProtocolSpec/Basic.lean:1094-1098` at `1c5c5bd7`; ArkLib's own docstring: "the whole function is sampled ahead of time"). The distribution is whatever `fsInit` (a hypothesis) supplies; there is no lazy sampling |
| E25 | 501 | `Implications.lean:230-254` | commented with the wrong error | OK | see E13 |
| E26 | 506 | "Definition B.2, `B:74-84`" | round-by-round soundness | NOT SUPPORTED (number) | `def:rbr` is Definition **B.5** (B.2 is `fact:fold-decode`); the lines are right. D:973 has it right |
| E27 | 509-511 | `B:133-136`, `B:137`, `B:218` (quoted) | `R_open`, `L_0`, start invariant | OK | `B:218` is stated for level `i`; the quotation is its `i = 0` instance |
| E28 | 515-518 | `Spine/Compose.lean:172-177`, `Compose.lean:58-59` (b435631); `Security/RoundByRound.lean:186-189` (dca90385) | master theorem; `commitExtractor`; `toFun_full` | OK | |
| E29 | 522-523, 562 | `bp:1190`, `bp:1296-1299`, `bp:1299` | test 11 | OK | |
| E30 | 546 | `RoundByRound.lean:553-568` (dca90385) | `rbrKnowledgeSoundnessWorstCaseWith`: for every statement, round, transcript | OK | |
| E31 | 556 | `bp:102-103` | no cost model | OK | |
| E32 | 566 | `bp:1231-1232` | "unconditional: it is about two definitions" | OK | |
| E33 | 570 | `Basic.lean:490-496` (dca90385) | `toVerifier` has the oracles in the clear | OK | doc comment at 488-489 says so |
| E34 | 575 | `fs/transcript.rs:9-12` | a proof holds a stream and Merkle phases | OK | |
| E35 | 584-586 | `mod.rs:82-93`, `mod.rs:118-124`, `fs/transcript.rs:63-71`, `:289-309`, `fs/merkle.rs:14-20` | chain inputs and wire encoding | OK | |
| E36 | 587-588 | `fs/transcript.rs:225-228` (quoted) | openings not absorbed | WRONG LINE | quotation at 223-224 (see I14) |
| E37 | 589 | `whir.rs:1175-1193` | query positions by chunking | OK | |
| E38 | 592 | `fs/lib.rs:118-120` | nonce absorbed with tag 4 | OK | |
| E39 | 593 | `fs/lib.rs:47-51, 165-174` | the check reads the chain state | OK | |
| E40 | 595 | `Basic.lean:248-250` (dca90385) | `Verifier.verify : StmtIn → FullTranscript pSpec → …` | OK | |
| E41 | 604-605 | `bp:1216`, `bp:1277`, `:1302`, `:1316`, `:1328` | "written from §8.5 …"; tests that "pin the shape" | OK | |
| E42 | 621 | `bp:1256-1257` (quoted) | completeness sentence | OK | |
| E43 | 624-626 | `fs/lib.rs:126-155`, `:132-138`, `:139-151` | unbounded search | OK | see check 6 |
| E44 | 637 | `Compose.lean:94-104` | `Phases.Complete` demands perfect completeness | OK | `Component.Complete.complete` (`ToArkLib/Component.lean:83-84`) |
| E45 | 640 | `bp:1323-1325` | test 20 | OK | |
| E46 | 642 | `fs/transcript.rs:297-302` | `c_0` derived at every `r` | OK | |
| E47 | 643 | `zerocheck.rs:117` | the prover's inverse `(1 + r_eq)⁻¹` | OK | `crates/flock/src/zerocheck.rs:117` |
| E48 | 645 | `bp:242` | `Reduction.seqCompose_perfectCompleteness_of_pure` | OK | |

### 2.4 Section G (the hidden assumption)

| # | D-line | Citation | Claim | Verdict | Correction or note |
| --- | --- | --- | --- | --- | --- |
| G1 | 781 | `Spine/Instance.lean` (b435631, no line) | `M3Rel I` is on `Column I.μ` | OK | `Instance.lean:230` |
| G2 | 786 | `03:113` | weights and values in `E` | OK | |
| G3 | 792 | `whir.rs:331-345`, `pcs/merkle.rs:144-192` | level-0 leaf: `2^6` words of 8 bytes | OK | |
| G4 | 793 | `A:8` | `K = F_2[x]/(x^64 + …)` | OK | |
| G5 | 795-796 | `B:4` (quoted), `B:70-72` "Definition B.1" | list binding | OK for the lines; number wrong | `def:listbinding` is Definition **B.4** (the dossier itself says so at D:972, 986, 1870) |
| G6 | 797 | `fs/merkle.rs:53-58`, `whir.rs:2125-2132` | the verifier supplies the zero prefix, `row_words = n_lanes` | OK | `n_lanes` at 2130, `num_interleaved_0` at 2131 |
| G7 | 800 | `B:137` | list size `L_0` | OK | |
| G8 | 805 | `B:302-306` (quoted) | the generator is `K`-valued | OK | |
| G9 | 809 | `B:380` | relayout `f(u, x) = q(x, u)` | OK | |
| G10 | 801-802 | "of size at most `L_0` (F.2: `110` to `396`)" | range of `L_0` | NOT SUPPORTED | over the 56 supported `(μ, ρ)` the level-0 Johnson bound runs from 110 (μ = 28, ρ = 1/2) to **648** (μ = 20, ρ = 1/16); see check 10 |
| G11 | 822-823 | `B:133-136`, `bp:1296-1299` | `R_open`; test 11 | OK | |
| G12 | 825 | `whir_config.rs:593-599` (quoted) | the Rust's L0 accounting | OK | |
| G13 | 827 | `08:44-46` | §8.4 is `TODO` | OK | |
| G14 | 829 | `bp:1190` (quoted) | the list-binding sentence | OK | |
| G15 | 802-809 | the argument that every member of `Λ(w)` is `K`-valued | the dossier's own proof | OK (not a citation) | re-derived: the novel basis evaluated at points of `dom ⊆ K` is `K`-valued, so each `K`-coordinate of an `E`-codeword is a codeword of `RS[K, dom, 2^κ]`; on the agreement set, of size `≥ (1 − γ_0)n > √ρ_0·n ≥ ρ_0·n = 2^{κ_0}`, the `y` and `y²` coordinates vanish, so they are zero. Sound as written |

### 2.5 Section F (the numbers)

| # | D-line | Citation | Claim | Verdict | Correction or note |
| --- | --- | --- | --- | --- | --- |
| F1 | 661-662 | `bp:1130`, `bp:1331-1332` (quoted) | `piopError_le`; test 23 | OK | |
| F2 | 664 | `mod.rs:174-176`, `pcs.rs:51` | stacking window | OK | |
| F3 | 669-670 | `py:836-851`, `py:1391` | only JUMP has constraints, two; `xi_powers` | OK | `TABLES` is `py:836-843` (845-850 is `BLAKE2S_SLOTS`); two constraints per the probe's table print (D:1662) |
| F4 | 674 | `bp:974` → `2^30` | `4·2^28` | OK | |
| F5 | 675 | `bp:941-942` → "`≈ 14 layers × 14 ≈ 2^7.6`" | GKR charge at `μ_bus = 28` | NOT SUPPORTED (arithmetic; my count) | with radix-4 layers of 0, 2, …, 26 variables the layer sumchecks have `Σ_{j<14} 2j = 182` rounds, so `5·182 + 2·14 + 2·14 ≈ 966 ≈ 2^{9.9}`, not `≈ 196`. This is my reading of `bp:940-942`, not checked against a GKR implementation. Immaterial: the sum stays `≈ 1.25·2^32` |
| F6 | 676-680 | `bp:1001-1003`, `bp:994`, `bp:1027`, `bp:1085`, `bp:1114` | 48; 4 + 72; 1; `≈ 2^32`; 112 + 56 | OK | |
| F7 | 681-683 | sum `≈ 2^{32.3}` → `2^{-159.7}`; "margin of `2^8`" | arithmetic | OK; margin loose | `log₂(2^32 + 2^30 + ~10^3) = 32.32`. "Margin `2^8`" compares the whole sum with `2^40`; the bound's non-Flock part (`≈ 2^30`) sits `2^10` under `2^40` |
| F8 | 686-688 | scratch "`stack_log 41 bus depth 38`" | per-log caps | OK | as recorded (H.3, `bus_depth.py`; the probe uses `κ_bc = 28`, not 32) |
| F9 | 691-692 | `bp:318`, `B:84`, `whir_config.rs:25-27` | interactive error is the sum; FS error the max | OK | |
| F10 | 699 | `whir_config.rs:38`; `lean_vm/src/lib.rs:69` | `SECURITY_BITS = 128` | OK | |
| F11 | 700-707 | `whir_config.rs:36-37`, `:25-27`, `:404-407`, `:314-337`, `:961`, `:175-180` (quoted) | regime | OK | quotations verbatim (TeX dashes aside) |
| F12 | 709-711 | `:639-707`, `py:910` | the search; the table | OK | |
| F13 | 711-714 | scratch port reproduces `py:910`; `bp:1165` | reproduction | OK | re-run: identical output, `True` (check 10) |
| F14 | 716-726 | the table of per-level values at three sizes | port output | OK | matches the port's output line for line |
| F15 | 729-732 | `:484-490`, `:494-498`, `:600-608`, `:556-568` | column definitions | OK for the lines | "the row union `2^{ℓ−1}` of Lemma B.8" (D:731): `lem:fold-list` is Lemma **B.10** |
| F16 | 735 | `:57-60` (quoted) | queries close `SECURITY_BITS − 17` | OK | |
| F17 | 737 | "the fold challenges sit at `128.2` to `146` bits" | range | NOT SUPPORTED as a range over the supported sizes | over all 56 sizes: 128.19 (μ = 27, ρ = 1/8, level 0) to 148.68 (μ = 17, ρ = 1/4, level 2). The range quoted is that of the printed sample |
| F18 | 738 | "the search stops at the first `m` that clears 128, `:664-665`" | how `m` is chosen | NOT SUPPORTED (inverted) | `:662-666` **breaks at the first `m` whose MCA term fails** to clear 128 ("no later candidate can recover once the proximity-gap target fails"); among the `m` tried it keeps the one with the fewest queries (`:697`), which is the largest `m` still clearing 128. That is why the fold bits sit just above 128; the conclusion drawn is right, the description of the loop is not |
| F19 | 739-740 | "`L_0 ≤ 396` at level 0 (`2^{8.6}`, at `μ = 15`) down to `110` at `μ = 28`" | range | OK for `ρ = 1/2` only | over all rates `L_0` reaches 648 (μ = 20, ρ = 1/16), `2^{9.34}` |
| F20 | 741-742 | `:537-555` (quoted); "`143` to `154` bits" | algebraic checks unioned over the list | lines OK; range NOT SUPPORTED | the dossier's own H.3 output has 141.00 (μ = 28, ρ = 1/16, level 5) and 141.42 (μ = 28, ρ = 1/4, level 5); over all sizes 141.0 to 154.2 |
| F21 | 743-745 | `leaf.rs:108-118`; "`192 − 30 − 8.6 = 153`" | the bus term not unioned; still clears 128 | OK | with `L_0 ≤ 648` and the Rust's `5·2^28`: `192 − 30.3 − 9.3 ≈ 152`; the conclusion stands |
| F22 | 751 | `bp:1234-1235` | `niError` sentence | OK | |
| F23 | 77-78 (summary) | "`L_0 ≤ 110` to `396` over the supported sizes"; "`128.2` bits at `μ = 28, ρ = 1/2`" | numbers in the summary | NOT SUPPORTED | `L_0` ranges 110–648 over the supported sizes. The 128.2-bit fold term is at `μ = 28, ρ = 1/4` (level 5, 128.22; H.3 output) and the global minimum is 128.19 at `μ = 27, ρ = 1/8` (level 0); at `μ = 28, ρ = 1/2` the minimum is 129.15 |

### 2.6 Section B (WHIR, Merkle trees, parameters)

| # | D-line | Citation | Claim | Verdict | Correction or note |
| --- | --- | --- | --- | --- | --- |
| B1 | 837-841 | the note on the moved checkout | pinned objects intact | OK | confirmed: HEAD `248da071`; every file read here with `git show a386121f…` |
| B2 | 844-845 | `whir_config.rs:67`, `:68`, `:86` | `k_0 = 6`, `k_i = 4`, residual `≤ 5` | OK | |
| B3 | 848 | `B:100-123`, `py:1006-1087` | Protocol B.6; `verify_whir` | OK | |
| B4 | 850 | `B:110`; `stack_open.rs:400` / `:518`; `py:1361` | row 0 | OK | |
| B5 | 851 | `B:111`; `whir.rs:1324-1326` / `:2087-2090`; `py:1012` | row 1 | OK | two scalars: `send_msg` drops `c_1` (`whir.rs:509-511`, `fs/transcript.rs:63-71`) |
| B6 | 852 | `B:111-112`, `B:380`; `whir.rs:1328-1334` / `:2100`, `:1641-1655`, `:2297-2306`; `py:1017-1024`, `:1078-1079` | row 2 | OK | |
| B7 | 853 | `B:115`; `whir.rs:1340-1358` / `:2104`; `py:1034` | row 3 | OK | `f⁽¹⁾` interleaved `2^{level_ks[0]} = 2^4` |
| B8 | 854 | `B:116`; `send_ood` `:1201-1208` / `replay_ood` `:1670-1675`; `whir_config.rs:677-684`, test `:1032-1034`; `py:1035-1037` | row 4 | OK | |
| B9 | 855 | `whir.rs:1366` / `:2117`; `fs/transcript.rs:314-323`; `whir_config.rs:60`; `py:1039` | row 5 | OK | |
| B10 | 856 | `B:117`; `whir.rs:1175-1193` / `:2122`; `py:943-951`, `:1041` | row 6 | OK | |
| B11 | 857 | `B:110`; `whir.rs:1373` / `:2123`; `py:1044` | row 7 | OK | |
| B12 | 858 | `B:117`; `hint_merkle :1380` / `recv_level_rows :2125-2135`; `fs/transcript.rs:263-279`; `py:1049-1050` | row 8 | OK | |
| B13 | 859 | `B:117-118`; `whir.rs:1405-1406` / `:2140-2144`; `whir_induce.rs:203-218`; `py:1051, 1057` | row 9 | OK | |
| B14 | 860 | `B:118`, `B:110`; `glue_pending :1131-1154` / `batch_level_claims :1681-1701`; `py:1058-1063` | row 10 | OK | |
| B15 | 861 | `B:111-119`; `whir.rs:1420-1425, 1509-1560` / `:2191-2194, 2311-2384`; `py:1017-1063` | row 11 | OK | |
| B16 | 862 | `B:120`; `whir.rs:1431-1476` / `:2197-2262`; `py:1031-1032, 1065-1074` | row 12 | OK | |
| B17 | 863 | `B:120`; `whir.rs:2264-2308`; `whir_induce.rs:228-293`; `py:1075-1083`, `:971-989` | row 13 | OK | |
| B18 | 865-867 | "The two verifiers agree … message for message" | Python against the succinct Rust verifier | OK | walked both: same order, same reads |
| B19 | 869-873 | `B:111`; `:1206`, `:1406`; `RoundQuad::fold :548-554` | per-claim intro messages; batched `h_1` by linearity | OK | |
| B20 | 873-875 | "two verifier challenges in a row (`λ_i` then `r_1`) with no prover message between them" | transcript order | NOT SUPPORTED | between `λ_i` and the next fold challenge the prover sends the query batch's intro polynomial (two scalars, absorbed): prover `whir.rs:1373 → 1406 → 1421`, `1534 → 1559 → 1421`, `1439 → 1466 → 1469`; verifier `2123 → 2142 → 2191` (via `replay_fold_rounds`), `2331 → 2348 → 2191`, `2211 → 2228 → 2253`; Python `1044 → 1057 → 1020/1070`. The challenges that do follow one another with no prover message between are the query positions and `λ_i` (`whir.rs:1370 → 1373`, `2122 → 2123`; `py:1041 → 1044`) |
| B21 | 878-880 | `whir_config.rs:57-60, 335-336`; `fs/lib.rs:165-174` | 17 bits every level, after root, before positions | OK | see check 3 |
| B22 | 883-887 | `whir.rs:2297-2306`, `py:1079`, `B:380`, `bp:1185` | relayout | OK | but D:886 is a quotation of the blueprint's "Protocol B.1" (fine) |
| B23 | 888 | `whir.rs:1471-1475`, `:2256-2261`; `py:1073-1074` | last round message omitted | OK | |
| B24 | 892-894 | `whir_config.rs:677-684`, `:829-841`; `whir.rs:1261-1265` (quoted); `B:105` (quoted); `bp:1186-1187` | OOD counts | OK | |
| B25 | 899-902 | `B:54`, `B:90`, `B:306`; `whir.rs:293`, `:364`, `:397`, `:17-19`; `whir_ntt_ext.rs` | field, domain, buffers | OK | `crates/pcs/src/whir_ntt_ext.rs` exists at the pin |
| B26 | 904-909 | `B:278`, `B:301-306`, `B:299`, `B:357`, `B:306`; `whir_induce.rs:19-21` (quoted), `:32-52`, `:56-67`, `:163`; `py:962-968`, `py:983`; `whir.rs:372-373` | basis | OK | |
| B27 | 911-912 | `whir_induce.rs:220-224`, `py:971-977`, `B:312` | column weight | OK | the Python product is at `py:986` |
| B28 | 914-917 | `whir_config.rs:41-55`; `mod.rs:123, 149, 167`; `whir_config.rs:73-78, 298-311`; `py:929`; `B:90` | rates | OK | |
| B29 | 919-920 | `whir_config.rs:260-296`; `py:924-932` | ladder; shapes at 15 and 28 | OK | shapes confirmed by the port |
| B30 | 924-927 | `whir_config.rs:38-86`; `pcs.rs:49-51`; `py:900-908` | constants | OK | `RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR` is private (`const`, line 78) |
| B31 | 928-935 | `whir_config.rs:639-707`; `py:910`; `bp:1157-1165`; `bp:1175`; `whir_config.rs:624-633` | parameters and the blueprint block | OK | |
| B32 | 941-946 | `pcs/merkle.rs:11-18`; `fs/merkle.rs:38-41`, `:44-51`, `:174`, `:139-148` | tree; hashes; no domain separation; fixed height and width | OK | see check 5 |
| B33 | 948-951 | `whir.rs:331-345`; `pcs/merkle.rs:144-192`; `fs/merkle.rs:53-58`, `:60-67` | level-0 leaf image | OK | |
| B34 | 951-952 | `whir.rs:461-467`, `:1211-1213`; `py:1049`, `:938-940` | deeper leaves, 384 bytes | OK | |
| B35 | 953-955 | `whir.rs:393-395` (quoted), `:463` | stale comment | OK | |
| B36 | 956-959 | `fs/merkle.rs:14-20`, `:26-36`; `py:216-219`, `py:222-224` | digests on the stream | OK | |
| B37 | 960-968 | `fs/merkle.rs:78-92`, `:101-136`, `:163-235`, `:246-264`; `fs/transcript.rs:198-203`; `mod.rs:702-704, 777`; `py:392-404`; `python_verifier.rs:50-80` | wire and raw formats | OK | |
| B38 | 972-974 | `B:139-152`, `B:70-72`, `B:74-84`, `B:133-136`, `B:141-150` | Theorem B.7, Definitions B.4, B.5 | OK | |
| B39 | 977-980 | `B:391-414`, `B:176-185`, `B:189-198`, `B:200-206`, `B:84` | Johnson bound; B.9; B.10; B.11; FS sentence | OK | |
| B40 | 984-986 | `bp:1150-1193`; `preamble/theorems.tex:4, 12`; the blueprint's numbers at `bp:1187`, `bp:1170`, `bp:278`, `bp:1172` | Layer 11 against Annex B | OK except one line | "Definition B.1" is at `bp:1188` (I48) |
| B41 | 987 | Theorem B.7's error list | `(J_i − 1)L_i/|E|`, `2L_i/|E| + 2^{ℓ_i−j}ε_i`, `C(L_i,2)μ_i/|E|`, `(1 − γ_i)^{t_i}`, `t_{r−1}/|E|`, `2/|E|` | OK | `B:143-148` |
| B42 | 988 | `B:54, 306`; `whir.rs:419-485` | encoder over `E` | OK | |
| B43 | 989 | `B:309-315`; `whir_induce.rs:220-224` | Lemma B.14 | OK | |
| B44 | 990 | `fs/merkle.rs:252-264`; `bp:1209-1211` | raw path; `Proof.merkle` | OK | |
| B45 | 991 | `whir_config.rs:266-267, 291-293`, `:196-224` | toy `μ = 4` cannot use the production ladder | OK | the fallback selector is `test_configs_for`, `:232-244` |

### 2.7 Section C (Fiat–Shamir and the proof object)

| # | D-line | Citation | Claim | Verdict | Correction or note |
| --- | --- | --- | --- | --- | --- |
| C1 | 997-999 | `08:44-46`, `08:55` (quoted) | §8.4 `TODO`; the setup sentence | OK | |
| C2 | 1006 | `fs/lib.rs:18-24`; `hash.rs:83-87, 209-224`; `py:341-343` | the step is `BLAKE2s(a‖b)` over 64 bytes, the RFC compression from the parameter state; the chain state is the first half of the message | OK | see check 4 |
| C3 | 1007 | `fs/lib.rs:36-39`, `:31-35` (quoted); `py:335-338` | tags; "its position is its tag" | OK | |
| C4 | 1008 | `fs/lib.rs:69-73`; `mod.rs:82-93`, `:712`, `:99-106`; `py:1366-1369`, `:349` | seed | OK | "the third limbs dropped": they are dropped by `digest_words` after `read_public` rejects a nonzero one (`mod.rs:141-143`) |
| C5 | 1009-1011 | `fs/lib.rs:85-87`, `:95-99`, `:108-110`; `py:353-354`, `:356-358`, `:380` | observe, squeeze, grinding base | OK | |
| C6 | 1012 | `fs/lib.rs:118-120`, `:165-174`; `py:382` | nonce bound also when the check fails | OK | the Python binds, then `require` raises |
| C7 | 1013 | `fs/lib.rs:47-51`, `:165-174`; `py:381` | predicate; `bits = 0` accepts only `0` | OK | |
| C8 | 1014 | `fs/lib.rs:126-155` | smallest `u64`, unbounded | OK | |
| C9 | 1016-1021 | `bp:325`, `bp:1204`, `bp:216` | the blueprint's rows | OK | `bp:216` also says "the byte hasher … is the RFC 7693 wrapper over `compress` with the last-block flag only", which the dossier does not mention; its reading "invite `F(cv, …)`" is an inference |
| C10 | 1022-1024 | `LeanerVM/Semantics/Blake2s.lean:105` (b435631) | the proposed "`compress iv64 (cv ++ x ++ tag) 64 true false`" in leanISA's terms | line OK; proposal imprecise | `compress` takes `(h : Vector UInt32 8) (m : Vector UInt32 16) (t : UInt64) (f0 f1 : UInt32)`, the flags being `0xFFFFFFFF` when set (doc comment 102-104): `true false` does not typecheck against it, and `iv64` must be the parameter-folded IV (`PARAM_IV`, `hash.rs:81`), not the bare IV |
| C11 | 1028-1034 | `fs/transcript.rs:9-12`, `:19`, `:198-203`, `:138-143`; `py:322-330`; `bp:1209-1211`, `bp:1182`, `bp:1237-1238` | proof object; the blueprint's `Proof` | OK | |
| C12 | 1036-1043 | `fs/merkle.rs:69-76, 101-136`, `:53-58`; `whir.rs:2130-2131`; `py:1049` | pruned against raw; the Python does not check the zero prefix | OK | see check 9 |
| C13 | 1046-1060 | `mod.rs:711-769`, `:712`, `:144-149`, `:714`, `:745-749`, `:769`; `pcs.rs:136-138`; `stack_open.rs:394/:513`, `:400/:518`; `whir.rs:2087-2308`; `fs/transcript.rs:213-219`; `py:1372`, `:1382`, `:1398-1399`, `:1343`, `:1361`, `:1006-1087`, `:1414` | stream order | OK | |
| C14 | 1063-1066 | `fs/transcript.rs:225-228`, `:56-62` (quoted) | not absorbed | WRONG LINE for the first | `223-224` (I14); `:56-62` OK ("Binding it would add nothing" at 60) |
| C15 | 1072-1076 | `fs/transcript.rs:56-71`, `:289-309`; `py:406-413` | round-polynomial encoding | OK | |
| C16 | 1077-1081 | `whir.rs:509-522`; `py:1012`; `bp:315`, `bp:1287-1289`, `bp:1212` | WHIR rounds two scalars; blueprint rows | OK | |
| C17 | 1089-1094 | `bp:1202-1206`, `:1209-1211`, `:1212`, `:1230`, `:1218-1221`, `:1238-1239` | Layer 12 rows | OK | |

### 2.8 Section D (the checks)

| # | D-line | Citation | Claim | Verdict | Correction or note |
| --- | --- | --- | --- | --- | --- |
| D1 | 1110 | `08:55`; `mod.rs:167`; `whir_config.rs:48-55`, `:43-45`; `py:1377` | rate window | OK | |
| D2 | 1111 | `mod.rs:174-176`; `py:1379`; `pcs.rs:179-188` (quoted); `whir_config.rs:291-293`; `witness.rs:97`; `py:890` | stacking window | OK | |
| D3 | 1112 | `06:80, 86, 90`; `mod.rs:158-161`; `py:857-862`; `witness.rs:67-102`; `py:305-311` | per-log caps implied | OK | |
| D4 | 1120 | `fs/transcript.rs:184-188`; `py:363-367` | R1 | OK | |
| D5 | 1121 | `fs/merkle.rs:26-29`; `whir.rs:2104, 2311`; `py:222-224`, `:1034` | R2 | OK | |
| D6 | 1122 | `fs/transcript.rs:271`; `py:385-390` | R3 | OK | |
| D7 | 1123 | `fs/transcript.rs:213-219`; `mod.rs:769`; `py:415-417`, `:1414` | R4 | OK | |
| D8 | 1124 | `whir.rs:2198`; `py:1032` | R5 | OK | |
| D9 | 1130 | `whir.rs:2117, 2202, 2325`; `fs/lib.rs:47-51, 165-174`; `fs/transcript.rs:314-323`; `py:377-383`, `:1039` | G1 | OK | |
| D10 | 1131 | `fs/lib.rs:167-168`; `py:381` | G2 | OK | |
| D11 | 1133 | `fs/merkle.rs:163-235` | `open` | OK | |
| D12 | 1137 | `:139-141`; `py:395-403` | M1 | OK | |
| D13 | 1138 | `:141-148`; `whir.rs:2130-2131, 2213-2219`; `py:396`, `py:1049` | M2 | OK | |
| D14 | 1138 | `stack_open.rs:359-362`, `:497-500` | "every claim's weight is supported inside the placed columns" | NOT SUPPORTED by the second line | `:359-362` is the prover's assertion that every claim lies inside `stack.len()` (the committed lanes); `:497-500`, the verifier's, bounds claims only by the full cube `1 << log_n`, not by the placed columns. The fact holds by construction of the layout (`mod.rs:790-814` places every claim at a column's slot), which is the right citation |
| D15 | 1139-1141 | `:171-173`, `:176-178`, `:195, 197, 208`; `whir.rs:1189`; `py:400`, `py:950` | M3–M5 | OK | |
| D16 | 1142 | `:208`; `pcs.rs:136-138`; `py:402` | M6 | OK | |
| D17 | 1143 | `:174, 139-148`; `whir.rs:2084, 2213`; `py:393, 396` | M7 | OK | |
| D18 | 1149 | `fs/transcript.rs:297-299`; `py:409-410` | W1 | OK | both derive, neither checks |
| D19 | 1150 | `whir.rs:1672`; `py:1036-1037`; `whir_config.rs:329-333` (quoted) | W2 | OK | |
| D20 | 1151 | `whir.rs:2140, 2226, 2346`; `py:1051, 1057` | W3 | OK | |
| D21 | 1152 | `whir.rs:1131-1154`, `:1681-1701`; `py:1058-1063` | W4 | OK | |
| D22 | 1153 | `whir.rs:2264-2308`; `py:1075-1083` | W5 | OK | |
| D23 | 1154-1155 | `whir.rs:2188-2190, 2266-2268, 2280-2282, 2374-2384`, `:2064-2072` | W6, W7 | OK | |
| D24 | 1156 | `stack_open.rs:507-510`; `py:1346` | W8 | OK | |
| D25 | 1160-1168 | `08:100` (quoted); `bp:1216`; `bp:1238-1239` | closing list | OK | |
| D26 | 1172-1177 | `whir.rs:1175-1193`, `:2061-2066, 2084, 2213`; `py:943-951`, `:1040, 1048-1049`; `witness.rs:97`; `py:890` | negative results | OK | the largest `d` at the supported sizes is 26 (`μ − 6 + ρ ≤ 26`), so `⌊192/d⌋ ≥ 7`; "`d ≤ 28`, `≥ 6`" is a valid weaker bound |

### 2.9 Section H (probes), checked only for provenance

| # | D-line | Item | Verdict | Note |
| --- | --- | --- | --- | --- |
| H1 | 1196-1305 | `InnerProductOracle.lean` source in the dossier | OK | identical to `probes/gt-opening-compile/InnerProductOracle.lean` (diff) |
| H2 | 1319-1380 | `FiatShamirChain.lean` source | OK | identical to the probe file |
| H3 | 1307-1316, 1382-1394 | outputs "on 2026-09-29 (old pins) and on 2026-09-30 (new pins)" | new-pin run OK; old-pin run COULD NOT CHECK | `rerun-newpin.log` records both files, `exit=0`, output as quoted. No log of the 2026-09-29 old-pin run exists in the probe directory or `logs/` |
| H4 | 1401-1623 | `whir_params.py` output | OK | re-run on a copy in my scratchpad: output identical to the dossier's, table reproduced (`True`); `verifier_pinned.py` is byte-identical to `git show a386121f:python-verifier/verifier.py` |

