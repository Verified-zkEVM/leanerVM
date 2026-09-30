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

