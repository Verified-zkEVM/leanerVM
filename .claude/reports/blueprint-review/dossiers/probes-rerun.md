# Dossier `probes-rerun`: the review's Lean probes, run at the upgraded checkout

Checkout: branch `docs/protocol-blueprint-review` containing `main` at `144c5aa` (Lean 4.34.1;
ArkLib `7653a901`, CompPoly `572f9973`, Clean `42fe4b26`, VCVio `a4232d08`, Mathlib `v4.34.1`).
Build `lake build LeanerVM LeanerVMTests` finished `exit=0` at 09:59
(`logs/lake-build-144c5aa-full.log`). Every probe was run from the repository root, one at a
time, under the shared lock:

```text
flock .claude/reports/blueprint-review/logs/lean.lock lake env lean <file> > <file>.new.out 2>&1; echo "exit=$?" >> <file>.new.out
```

Old probe files and their old outputs are untouched; each adapted probe is a copy named
`<name>.v434.lean` next to the old one, and its output is `<name>.v434.lean.new.out`.

## Summary table

| # | Probe (at `144c5aa`, new pins) | Adaptation | Exit | Outcome |
| --- | --- | --- | --- | --- |
| 1.0 | public input: `Probe0Baseline` (control) | regenerated from the current module | 0 | agrees |
| 1.2 | public input: mutation 7a (wrong check, honest prover fixed) | regenerated; refutation lemmas on the new `Pr{…}[…]` | 1 (expected errors) | **differs in part**: `complete` fails at `decide_eq_true hmsg` and `not_complete` is proved (three axioms), as predicted; but `rbr` depends on `sorryAx` (its statement names the unchanged `stateFunction`, which fails at `toFun_full` as in every other mutation and is not added), where the dossier predicted it would compile |
| 1.3 | public input: mutation 8 (extra check) | same | 1 (expected errors) | **differs in part**: same pattern as 7a; `not_complete` proved; `rbr` depends on `sorryAx`, not "compiles" |
| 1.4 | public input: `ProbeWordsLemma` | none | 0 | agrees |
| 1.5 | public input: mutation 1 (control) | regenerated; `rbr'` on `prEvent_mono` | 1 (the one expected error) | agrees |
| 1.6 | public input: mutation 2 (control) | regenerated; `not_rbr` on `Pr{…}[…]` | 1 (the one expected error) | agrees |
| 1.7 | public input: `ProbeAnyCheck` (control) | regenerated | 0 | agrees |
| 1.8 | public input: mutations 4b and 6 | — | — | **could not run: never written** (argued on paper in `code-pubinput.md` C.12, C.13) |
| 2.1 | spine: `P2Relation` | `[0, 1, 2] : List K` → `[0, 1, K.ofBits 2]` | 0 | agrees |
| 2.2 | spine: `P3aSeams` | `2` in `K` → `K.ofBits 2` (cell, point, statement) | 0 | agrees |
| 2.3 | spine: `P5PassThrough` unchanged (control) | none | 1 | fails as expected of an unadapted probe (`(2 : K) = 0`; old `Pr[…]`) |
| 2.3 | spine: `P5PassThrough` adapted | `K.ofBits 2`; `Pr{…}[…]` | 0 | agrees (`no_security`, three axioms) |
| 2.4 | spine: `P4Junk` unchanged (control) | none | 0 | agrees |
| 3.1 | Layer 1: `ValuesProbe` | numerals ≥ 2 in `K` → `K.ofBits`; `·.toNat` → `·.toBitVec.toNat` | 0 | agrees (every guard against the pinned Python verifier's numbers) |
| 3.2 | Layer 1: `StridedProbe` | numerals → `K.ofBits` | 0 | agrees |
| 3.3 | Layer 1: `OffsetsProbe` | none | 0 | agrees |
| 3.4 | Layer 1: `DuplicatesProbe` | none | 0 | agrees |
| 4.1 | table/bus seam: `SeamBusShape` | none | 0 | agrees |
| 4.2 | table/bus seam: `SeamBusMember` | none | 0 | agrees |
| 5 | Flock: `NoCheckFlock` | none | 0 | agrees |
| 6.1 | Layer 0: `FieldFidelity` adapted | every word → `K.ofBits` | 1 (one `#synth`) | **the eleven reference products still agree**; differs in the instance lines: no leakage onto `BitVec 64` any more, `Fintype (BitVec 64)` no longer found, **`LawfulBEq E` now exists** |
| 6.1 | Layer 0: `FieldFidelity` unchanged (control) | none | 1 | fails as `lib-others.md` predicted (numerals as casts) |
| 6.2 | Layer 0: `SamplerDiamond2` | none | 1 | **differs**: `FinEnum K` has no instance; the second sampler, hence the diamond, no longer exists |
| 6.3 | Layer 0: `Layer0` | none | 0 | agrees (instance names and the class `SampleableType`'s fields print differently) |
| 7.1 | ArkLib: `NonVacuity` unchanged / adapted | adapted: `Pr{…}[…]`, `prEvent_eq_zero_iff` | 1 / 0 | adapted copy agrees |
| 7.2 | ArkLib: `Extractors` | none | 0 | agrees |
| 7.3 | ArkLib: `PlainReading` unchanged / adapted | adapted: `Pr{…}[…]` | 1 / 0 | adapted copy agrees (`prob_eval_zero_le_div` prints a new signature) |
| 7.4 | ArkLib: `AxiomsLeanerVM` | none | 0 | agrees, output byte-identical to the old one |

Every run took 3 to 23 s (54 s once, waiting for the lock); none approached the 15-minute
limit. No run was killed for memory.

**What differs from the dossiers' claims, in one place.**

1. `code-pubinput.md` C.10 and C.11 predicted that, for mutations 7a and 8, "`rbr` compiles (it
   never reads the check)". It does not: the unchanged `stateFunction` names the original
   `check` in its last round and fails at `toFun_full` exactly as C.2 records for every other
   mutation, so `rbr` is recorded with `sorryAx` in both. The predicted completeness
   failure and the refutation `not_complete` are confirmed for both.
2. Mutations 4b and 6 were never written; nothing could be run for them.
3. `lib-others.md`: at the new pins `LawfulBEq E` exists (`CompPoly.Extension.Ext.instLawfulBEq`),
   the instance leakage onto `BitVec 64` is gone, and the `K` sampler diamond no longer exists
   (`FinEnum K` is not found). Those statements of the dossier were about the old pin.
4. The old files `Probe7a.lean` and `Probe8.lean` were generated from the module after the merge
   (their copied text has the upgrade's proof changes), not from `b435631`'s module like the other
   old probes (1.1, item 3).

## 1. The public-input phase (`probes/code-pubinput/`)

**How the copies were regenerated.** The mutation scripts were copied unchanged to
`probes/code-pubinput/tools/v434/` (the originals in `tools/` are untouched), their `exec` paths
pointed at the copies, and each run of `tools/v434/mutate.py` reads the module as it is in the
working tree now, `LeanerVM/Protocol/PublicInput.lean` at `144c5aa` (checked: `git diff 144c5aa
HEAD -- LeanerVM/Protocol/PublicInput.lean` is empty, and the working tree has no change to it).
Where a script's search string names text the upgrade changed (`if_pos h` became `ite_eq_left h`
and so on), or its appended text uses an API the upgrade retired, the change is shown as a diff of
the script. The command for every probe of this section is the dossier's, with its two `-D`
options:

```text
flock .claude/reports/blueprint-review/logs/lean.lock lake env lean \
  -D autoImplicit=false -D relaxedAutoImplicit=false <file> > <file>.new.out 2>&1; echo "exit=$?" >> <file>.new.out
```

### 1.0 `Probe0Baseline.v434.lean` (the control)

Generated by `python3 .../tools/v434/mutate.py .../Probe0Baseline.v434.lean Probe0 .../tools/v434/m0.py`,
with a new edit file `tools/v434/m0.py` (no edit; the tail is the two `#print axioms` of the old
file). Diff of the probe against the current module (identical to the old probe's diff against the
old module):

```diff
53c53
< namespace LeanerVM.Protocol
---
> namespace LeanerVM.Protocol.Probe0
400c400,405
< end LeanerVM.Protocol
---
> end LeanerVM.Protocol.Probe0
> 
> open LeanerVM.Protocol.Probe0 in
> #print axioms publicInputSecurity
> open LeanerVM.Protocol.Probe0 in
> #print axioms publicInputComplete
```

Output (`Probe0Baseline.v434.lean.new.out`), 8 s:

```text
'LeanerVM.Protocol.Probe0.publicInputSecurity' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe0.publicInputComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```

Agrees with the dossier's recorded result (`code-pubinput.md` C.0).

### 1.1 The adaptations of the scripts, shared by every probe below

Three kinds of change, all forced by the upgrade:

1. Search strings that name the module's old text, and appended proofs that use the same
   lemmas, were moved to the module's new names (Lean 4.34.1 deprecates `if_pos`/`if_neg` for
   `ite_eq_left`/`ite_eq_right`; VCVio `a4232d08` retires `probEvent_mono` for
   `prEvent_mono _ _ _`, whose event no longer carries a support hypothesis, so `rintro r - ⟨…⟩`
   becomes `rintro r ⟨…⟩`). In every script (`m1.py m2.py m3a.py m3b.py m4a.py m5.py m7a.py
   m8.py anycheck.py weak.py`), by `sed`:

```text
s/if_pos/ite_eq_left/g; s/if_neg/ite_eq_right/g;
s/probEvent_mono ?_/prEvent_mono _ _ _ ?_/g; s/rintro r - ⟨_, hin, hout⟩/rintro r ⟨_, hin, hout⟩/g
```

   plus the `exec` paths pointed at `tools/v434/`. Collected over `m1 m2 m7a m8 anycheck`, the
   changed lines are (count, line):

```text
      2 -  refine le_trans (probEvent_mono ?_) (probEvent_uniformSample_le_of_subsingleton (α := E)
      2 +  refine le_trans (prEvent_mono _ _ _ ?_) (probEvent_uniformSample_le_of_subsingleton (α := E)
      2 -  rintro r - ⟨_, hin, hout⟩
      2 +  rintro r ⟨_, hin, hout⟩
      3 -  rw [if_pos hc]
      3 +  rw [ite_eq_left hc]
      2 -  verify_eq := fun ⟨s, o⟩ tr ↦ (verifier_verify I s o tr).trans (if_pos rfl).symm
      2 +  verify_eq := fun ⟨s, o⟩ tr ↦ (verifier_verify I s o tr).trans (ite_eq_left rfl).symm
      3 -  · rw [if_pos h, if_pos h]
      3 +  · rw [ite_eq_left h, ite_eq_left h]
      3 -  · rw [if_neg h, if_neg h]
      3 +  · rw [ite_eq_right h, ite_eq_right h]
```

2. The two refutation lemmas (`not_rbr`, `not_perfectCompleteness`, in `tools/lib.py`) were
   restated on VCVio's new probability API. At ArkLib `7653a901` a knowledge state function's
   `toFun_full` takes `Pr{let stmtOut ← OptionT.mk do …}[(stmtOut, witOut) ∈ relOut] > 0`
   (`ArkLib/OracleReduction/Security/RoundByRound.lean:187-191`), round-by-round knowledge
   soundness bounds `Pr{let challenge ← $ᵗ (pSpec.Challenge i)}[…]` (`:539-555`), and
   `Reduction.perfectCompleteness_eq_prob_one` states probability one in the `Pr{…}[…]` form
   (`ArkLib/OracleReduction/Security/Basic.lean:163-173`). The old `Pr[P | c]` still parses at
   VCVio `a4232d08` but means the deprecated `probEvent` (`VCVio/EvalDist/Defs/Basic.lean:97-115`),
   a different definition, so the old statements no longer match ArkLib's. The lemmas used:
   `OracleComp.OptionT.prEvent_mk_pos_iff` and `OracleComp.prEvent_eq_one_iff`
   (`VCVio/OracleComp/EvalDist/Measure.lean:362-364, 412-414`), the ones the repository's
   `ToArkLib/GuardedVerdict.lean` uses at `144c5aa`. Diff of `tools/lib.py` to
   `tools/v434/lib.py`:

```diff
@@ -53,20 +53,20 @@
           (default : Transcript 0 pSpec)) witMid := by
     intro r
     obtain ⟨hc, hout⟩ := hacc r
-    have hpos : Pr[fun stmtOut => (stmtOut, ()) ∈ relOut
-        | OptionT.mk do
+    have hpos : Pr{let stmtOut ← OptionT.mk do
             (simulateQ impl (V.run stmt (tr2 r (msg r)))).run'
-              (← (pure () : ProbComp Unit))] > 0 := by
+              (← (pure () : ProbComp Unit))}[(stmtOut, ()) ∈ relOut] > 0 := by
       have hv : V.run stmt (tr2 r (msg r)) = pure (G.out stmt (tr2 r (msg r))) := by
         have := G.verify_eq stmt (tr2 r (msg r))
-        rw [if_pos hc] at this
+        rw [ite_eq_left hc] at this
         exact this
       rw [hv]
-      change Pr[_ | OptionT.mk (do let st ← (pure () : ProbComp Unit); (simulateQ impl
-        (OptionT.run (pure (G.out stmt (tr2 r (msg r))) :
-          OptionT (OracleComp []ₒ) StmtOut))).run' st)] > 0
+      change Pr{let sample ← OptionT.mk (do
+        let st ← (pure () : ProbComp Unit)
+        (simulateQ impl (OptionT.run (pure (G.out stmt (tr2 r (msg r))) :
+          OptionT (OracleComp []ₒ) StmtOut))).run' st)}[(sample, ()) ∈ relOut] > 0
       rw [OptionT.run_pure, simulateQ_pure]
-      rw [gt_iff_lt, probEvent_pos_iff]
+      rw [gt_iff_lt, OracleComp.OptionT.prEvent_mk_pos_iff]
       refine ⟨G.out stmt (tr2 r (msg r)), ?_, hout⟩
       simp
     have hfull := kSF.toFun_full stmt (tr2 r (msg r)) () hpos
@@ -77,15 +77,15 @@
     intro h0
     exact hin ((kSF.toFun_empty stmt _).mpr h0)
   -- So the bad event has probability one.
-  have hone : Pr[fun challenge : E => ∃ witMid,
+  have hone : Pr{let challenge ← $ᵗ E}[∃ witMid,
       ¬ kSF (Fin.castSucc 0) stmt (default : Transcript 0 pSpec)
           (ext.extractMid 0 stmt
             (Transcript.concat (m := (0 : Fin 2)) challenge
               (default : Transcript 0 pSpec)) witMid) ∧
         kSF (Fin.succ 0) stmt (Transcript.concat (m := (0 : Fin 2)) challenge
-          (default : Transcript 0 pSpec)) witMid | $ᵗ E] = 1 := by
-    rw [probEvent_eq_one_iff]
-    exact ⟨by simp, fun r _ ↦ hall r⟩
+          (default : Transcript 0 pSpec)) witMid] = 1 := by
+    rw [OracleComp.prEvent_eq_one_iff]
+    exact fun r _ ↦ hall r
   have hle : (1 : ℝ≥0∞) ≤ ((ε ⟨0, rfl⟩ : ℝ≥0) : ℝ≥0∞) := hone ▸ hbound
   exact absurd (ENNReal.coe_lt_one_iff.mpr hε) (not_lt.mpr hle)
 
@@ -106,8 +106,9 @@
   have h1 := hc stmtIn witIn hin
   dsimp only at h1
   have hpos := lt_of_lt_of_eq (zero_lt_one' ℝ≥0∞) h1.symm
-  obtain ⟨x, hx, hev⟩ := probEvent_pos_iff.mp hpos
-  rw [OptionT.mem_support_iff, OptionT.run_mk, mem_support_bind_iff] at hx
+  rw [OracleComp.OptionT.prEvent_mk_pos_iff] at hpos
+  obtain ⟨x, hx, hev⟩ := hpos
+  rw [mem_support_bind_iff] at hx
   obtain ⟨s, _, hx⟩ := hx
   exact h (some x) (support_simulateQ_run'_subset _ _ s hx) x rfl hev
 
```

   A first version applied `(OracleComp.OptionT.prEvent_mk_pos_iff _ (fun x ↦ …)).mp hpos`
   in `not_perfectCompleteness`; it hit `(deterministic) timeout at whnf, maximum number of
   heartbeats (200000)` at the declaration. The `rw … at hpos` form above was checked in a
   scratch plain file (`probes/probes-rerun/RefuteScratch.lean`, the lemma alone, importing
   `LeanerVM.Protocol.ToArkLib.GuardedVerdict`: no error) and then used. No statement of either
   lemma changed except the probability notation.

3. The scripts `m7a.py` and `m8.py`: the old files `Probe7a.lean` and `Probe8.lean` on disk were
   **not** produced from the old module. Regenerating every old probe from `b435631`'s
   `PublicInput.lean` with the old scripts reproduces `Probe1NoCheck`, `Probe2TrustProver`,
   `Probe3a`, `Probe3b`, `Probe4a`, `Probe5` and `ProbeAnyCheck` byte for byte, but `Probe7a`
   and `Probe8` differ from the regenerated ones exactly in the five lines the upgrade changed in
   the module (`if_pos`→`ite_eq_left`, `if_neg`→`ite_eq_right`, `probEvent_mono`→`prEvent_mono`,
   `rintro r -`→`rintro r`): they were made from the module after the merge `8d3ea7d` (the
   dossier `code-pubinput.md` C.9 records the merge landing mid-work), with the old `lib.py`
   tails. This does not change what they test.

### 1.2 Mutation 7a: a wrong check (the cells swapped), the honest prover unchanged (`Probe7a.v434.lean`)

Generated by `mutate.py …/Probe7a.v434.lean Probe7a …/tools/v434/m7a.py`. Diff of the mutation
against the current module (the part before the appended tail; the tail is `TAIL` of
`tools/v434/m7a.py`: the refutation lemmas of 1.1 and the toy refutation quoted in
`code-pubinput.md` C.10, unchanged):

```diff
@@ -11,6 +11,7 @@
 public import LeanerVM.Protocol.Spine.Phase
 public import LeanerVM.Protocol.ToArkLib.GuardedVerdict
 public import LeanerVM.Protocol.ToArkLib.KeepOracles
+public import LeanerVM.Protocol.Spine.Toy
 import LeanerVM.Protocol.ToCompPoly.Multilinear
 import LeanerVM.Protocol.ToVCVio.UniformSample
 import Mathlib.Algebra.CharP.Two
@@ -50,7 +51,7 @@
 the specification's verifier.
 -/
 
-namespace LeanerVM.Protocol
+namespace LeanerVM.Protocol.Probe7a
 
 open LeanerVM.Parameters CompPoly OracleComp OracleSpec ProtocolSpec
 open scoped NNReal ENNReal
@@ -136,6 +137,15 @@
 def check (s : I.Stmt × TableOut I) (r : E) (cs : List E) : Bool :=
   decide (cs = expectedValues I s.1 r)
 
+
+/-- The values of the lines with their cells swapped: `(1 + r)·cell1 + r·cell0`. -/
+def swappedValues (input : I.Stmt) (r : E) : List E :=
+  ((I.publicLines input).filter (·.sent)).map fun l ↦ (1 + r) * ofK l.cell1 + r * ofK l.cell0
+
+/-- The wrong check: the message is the swapped values. -/
+def checkWrong (s : I.Stmt × TableOut I) (r : E) (cs : List E) : Bool :=
+  decide (cs = swappedValues I s.1 r)
+
 /-- A line's claim holds of the stack exactly when the line through the stack's two cells,
 evaluated at `r`, is the line through the statement's. -/
 private theorem lineClaim_holds_iff (q : Column I.μ) (r : E) (l : PublicLine I.toShape) :
@@ -230,7 +240,7 @@
     (I.Stmt × PubOut I) (TheOracle I) pSpec where
   verify := fun s chals ↦ do
     let cs ← liftM queryValues
-    if check I s (chals ⟨0, rfl⟩) cs then pure (pooled I s (chals ⟨0, rfl⟩)) else failure
+    if checkWrong I s (chals ⟨0, rfl⟩) cs then pure (pooled I s (chals ⟨0, rfl⟩)) else failure
   outputOracle := .inl (keepOracles (TheOracle I) pSpec)
 
 /-! ## The verifier's verdict -/
@@ -253,7 +263,7 @@
 theorem verifier_verify (s : I.Stmt × TableOut I) (o : ∀ i, TheOracle I i)
     (tr : pSpec.FullTranscript) :
     (verifier I).toVerifier.verify (s, o) tr =
-      if check I s (tr 0) (tr 1) then pure (pooled I s (tr 0), o) else failure := by
+      if checkWrong I s (tr 0) (tr 1) then pure (pooled I s (tr 0), o) else failure := by
   simp only [OracleVerifier.toVerifier]
   rw [OracleVerifier.materializeOutput_of_keepOracles _ rfl]
   simp only [verifier]
@@ -263,7 +273,7 @@
         OracleComp ([]ₒ + ([TheOracle I]ₒ + [pSpec.Message]ₒ)) (List E)) from
     (OracleComp.monadLift_liftM_OptionT _).symm]
   rw [simulateQ_optionT_bind_run, simulateQ_queryValues, pure_bind]
-  by_cases h : check I s (tr 0) (tr 1) = true
+  by_cases h : checkWrong I s (tr 0) (tr 1) = true
   · rw [ite_eq_left h, ite_eq_left h]
     rfl
   · rw [ite_eq_right h, ite_eq_right h]
@@ -271,7 +281,7 @@
 
 /-- The verifier is a check followed by a verdict, as data. -/
 def guarded : (verifier I).toVerifier.GuardedForm where
-  check := fun p tr ↦ check I p.1 (tr 0) (tr 1)
+  check := fun p tr ↦ checkWrong I p.1 (tr 0) (tr 1)
   out := fun p tr ↦ (pooled I p.1 (tr 0), p.2)
   verify_eq := fun ⟨s, o⟩ tr ↦ verifier_verify I s o tr
 
@@ -397,4 +407,168 @@
   rbr := PublicInput.rbr I
 
 end
-end LeanerVM.Protocol
+end LeanerVM.Protocol.Probe7a
+
+#print axioms LeanerVM.Protocol.Probe7a.PublicInput.verifier_verify
```

Output (`Probe7a.v434.lean.new.out`), 5 s:

```text
.claude/reports/blueprint-review/probes/code-pubinput/Probe7a.v434.lean:318:67: error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
.claude/reports/blueprint-review/probes/code-pubinput/Probe7a.v434.lean:356:4: error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
.claude/reports/blueprint-review/probes/code-pubinput/Probe7a.v434.lean:362:49: error(lean.unknownIdentifier): Unknown identifier `stateFunction`

Note: It is not possible to treat `stateFunction` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.
.claude/reports/blueprint-review/probes/code-pubinput/Probe7a.v434.lean:406:9: error(lean.unknownIdentifier): Unknown identifier `PublicInput.stateFunction`
'LeanerVM.Protocol.Probe7a.PublicInput.verifier_verify' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe7a.PublicInput.complete' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
.claude/reports/blueprint-review/probes/code-pubinput/Probe7a.v434.lean:414:14: error(lean.unknownIdentifier): Unknown constant `LeanerVM.Protocol.Probe7a.PublicInput.stateFunction`
'LeanerVM.Protocol.Probe7a.PublicInput.rbr' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe7a.PublicInput.not_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=1
```

Positions: `318:67` is `hmsg` in `have hc : (guarded I).check (s, o) pr.1 = true := decide_eq_true hmsg`
(in `complete`); `356:4` is `Verifier.GuardedForm.of_probEvent_pos (guarded I) init impl stmt tr _ h`,
the field `toFun_full` of the unchanged `stateFunction`; the later "unknown identifier" errors
are `rbr`, `publicInputSecurity` and the `#print axioms` naming `stateFunction`, which was not
added.

Result: **differs in part.** As the dossier predicted (`code-pubinput.md` C.10), `complete`
fails at `decide_eq_true hmsg` and the refutation `not_complete` (the mutated verifier is not
perfectly complete, for every initial state and implementation of the shared oracle) is proved
on the kernel's three axioms. Two differences: (a) the dossier predicted "`rbr` compiles (it
never reads the check)"; it does not (`rbr` is printed with `sorryAx`): the unchanged
`stateFunction` fails at `toFun_full`, as in every other mutation (`code-pubinput.md` C.2), because its last round names the original `check`,
and `rbr` is stated over `stateFunction`. (b) The two failures are reported as `maximum recursion
depth has been reached`, not as the `Type mismatch` the older probes printed; so the unchanged
`stateFunction` is not added at all (the old probes added it with `sorryAx`). Neither changes the
conclusion the dossier draws from 7a (completeness, against the fixed honest prover, is refuted).

### 1.3 Mutation 8: an extra check leanVM does not make (`Probe8.v434.lean`)

Generated by `mutate.py …/Probe8.v434.lean Probe8 …/tools/v434/m8.py`. Diff of the mutation
against the current module (before the tail; the tail is `TAIL` of `tools/v434/m8.py`: the
refutation lemmas of 1.1 and the toy refutation quoted in `code-pubinput.md` C.11, unchanged):

```diff
@@ -11,6 +11,7 @@
 public import LeanerVM.Protocol.Spine.Phase
 public import LeanerVM.Protocol.ToArkLib.GuardedVerdict
 public import LeanerVM.Protocol.ToArkLib.KeepOracles
+public import LeanerVM.Protocol.Spine.Toy
 import LeanerVM.Protocol.ToCompPoly.Multilinear
 import LeanerVM.Protocol.ToVCVio.UniformSample
 import Mathlib.Algebra.CharP.Two
@@ -50,7 +51,7 @@
 the specification's verifier.
 -/
 
-namespace LeanerVM.Protocol
+namespace LeanerVM.Protocol.Probe8
 
 open LeanerVM.Parameters CompPoly OracleComp OracleSpec ProtocolSpec
 open scoped NNReal ENNReal
@@ -136,6 +137,11 @@
 def check (s : I.Stmt × TableOut I) (r : E) (cs : List E) : Bool :=
   decide (cs = expectedValues I s.1 r)
 
+
+/-- The check with an extra condition: the first value of the message is nonzero. -/
+def checkExtra (s : I.Stmt × TableOut I) (r : E) (cs : List E) : Bool :=
+  check I s r cs && decide (cs.headD 0 ≠ 0)
+
 /-- A line's claim holds of the stack exactly when the line through the stack's two cells,
 evaluated at `r`, is the line through the statement's. -/
 private theorem lineClaim_holds_iff (q : Column I.μ) (r : E) (l : PublicLine I.toShape) :
@@ -230,7 +236,7 @@
     (I.Stmt × PubOut I) (TheOracle I) pSpec where
   verify := fun s chals ↦ do
     let cs ← liftM queryValues
-    if check I s (chals ⟨0, rfl⟩) cs then pure (pooled I s (chals ⟨0, rfl⟩)) else failure
+    if checkExtra I s (chals ⟨0, rfl⟩) cs then pure (pooled I s (chals ⟨0, rfl⟩)) else failure
   outputOracle := .inl (keepOracles (TheOracle I) pSpec)
 
 /-! ## The verifier's verdict -/
@@ -253,7 +259,7 @@
 theorem verifier_verify (s : I.Stmt × TableOut I) (o : ∀ i, TheOracle I i)
     (tr : pSpec.FullTranscript) :
     (verifier I).toVerifier.verify (s, o) tr =
-      if check I s (tr 0) (tr 1) then pure (pooled I s (tr 0), o) else failure := by
+      if checkExtra I s (tr 0) (tr 1) then pure (pooled I s (tr 0), o) else failure := by
   simp only [OracleVerifier.toVerifier]
   rw [OracleVerifier.materializeOutput_of_keepOracles _ rfl]
   simp only [verifier]
@@ -263,7 +269,7 @@
         OracleComp ([]ₒ + ([TheOracle I]ₒ + [pSpec.Message]ₒ)) (List E)) from
     (OracleComp.monadLift_liftM_OptionT _).symm]
   rw [simulateQ_optionT_bind_run, simulateQ_queryValues, pure_bind]
-  by_cases h : check I s (tr 0) (tr 1) = true
+  by_cases h : checkExtra I s (tr 0) (tr 1) = true
   · rw [ite_eq_left h, ite_eq_left h]
     rfl
   · rw [ite_eq_right h, ite_eq_right h]
@@ -271,7 +277,7 @@
 
 /-- The verifier is a check followed by a verdict, as data. -/
 def guarded : (verifier I).toVerifier.GuardedForm where
-  check := fun p tr ↦ check I p.1 (tr 0) (tr 1)
+  check := fun p tr ↦ checkExtra I p.1 (tr 0) (tr 1)
   out := fun p tr ↦ (pooled I p.1 (tr 0), p.2)
   verify_eq := fun ⟨s, o⟩ tr ↦ verifier_verify I s o tr
 
@@ -397,4 +403,174 @@
   rbr := PublicInput.rbr I
 
 end
-end LeanerVM.Protocol
+end LeanerVM.Protocol.Probe8
+
+#print axioms LeanerVM.Protocol.Probe8.PublicInput.verifier_verify
```

Output (`Probe8.v434.lean.new.out`), 4 s:

```text
.claude/reports/blueprint-review/probes/code-pubinput/Probe8.v434.lean:314:52: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Decidable (pr.1 1 = expectedValues I s.1 (pr.1 0))

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
.claude/reports/blueprint-review/probes/code-pubinput/Probe8.v434.lean:352:4: error: Type mismatch
  Verifier.GuardedForm.of_probEvent_pos (guarded I) init impl stmt tr (fun sample => (sample, x✝) ∈ Seam.pub I) h
has type
  (guarded I).check stmt tr = true ∧ ((guarded I).out stmt tr, x✝) ∈ Seam.pub I
but is expected to have type
  if h0 : ↑(Fin.last 2) = 0 then (stmt, ()) ∈ Seam.table I
  else
    if h1 : ↑(Fin.last 2) = 1 then ((pooled I stmt.1 (tr ⟨0, ⋯⟩), stmt.2), ()) ∈ Seam.pub I
    else check I stmt.1 (tr ⟨0, ⋯⟩) (tr ⟨1, ⋯⟩) = true ∧ ((pooled I stmt.1 (tr ⟨0, ⋯⟩), stmt.2), ()) ∈ Seam.pub I
'LeanerVM.Protocol.Probe8.PublicInput.verifier_verify' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe8.PublicInput.complete' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe8.PublicInput.stateFunction' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe8.PublicInput.rbr' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe8.PublicInput.not_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=1
```

Positions: `314:52` is `decide_eq_true hmsg` in `complete`'s
`have hc : (guarded I).check (s, o) pr.1 = true := decide_eq_true hmsg`; `352:4` is the field
`toFun_full` of the unchanged `stateFunction`.

Result: **differs in part.** As predicted (`code-pubinput.md` C.11), `complete` fails at the
same line as in 7a, and `not_complete` (the verifier with the extra check is not perfectly
complete, for every initial state and implementation of the shared oracle; the refutation's
argument holds for every prover, since `check` pins the message) is proved on the kernel's three
axioms. The dossier's "`rbr` compiles" does not hold: `rbr` depends on `sorryAx` because the
unchanged `stateFunction` fails at `toFun_full` (the same `Type mismatch` as `code-pubinput.md`
C.2), as for every other mutation. The failure message in `complete` is a missing `Decidable`
instance (the elaborator cannot read `hmsg` as a `decide` of the extra conjunct), not a type
mismatch; the location is the one predicted.

### 1.4 `ProbeWordsLemma.v434.lean` (the algebra of the deployed verifiers' combined check)

A plain file; no numeral other than `0` in `K`, no ArkLib or VCVio object. Copied unchanged
(`cp ProbeWordsLemma.lean ProbeWordsLemma.v434.lean`; empty diff). Output
(`ProbeWordsLemma.v434.lean.new.out`), 6 s:

```text
'WordsLemma.accepts_two_challenges' depends on axioms: [propext, Classical.choice, Quot.sound]
'WordsLemma.cells_eq_lanes' depends on axioms: [propext, Classical.choice, Quot.sound]
'WordsLemma.top_limb_zero_of_two_challenges' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```

Agrees with the dossier's recorded result (`code-pubinput.md` C.13): the three lemmas hold at
the new pins on the kernel's three axioms.

### 1.5 Control: mutation 1, no check, the lines' values pooled (`Probe1NoCheck.v434.lean`)

Generated by `mutate.py …/Probe1NoCheck.v434.lean Probe1 …/tools/v434/m1.py`. Diff of the
v434 probe against the old probe (the mutation itself is the one quoted in `code-pubinput.md`
C.3; what changed is only what the upgrade changed in the module, and the tail's `rbr'`):

```diff
@@ -268,7 +268,7 @@
 def guarded : (verifier I).toVerifier.GuardedForm where
   check := fun _ _ ↦ true
   out := fun p tr ↦ (pooled I p.1 (tr 0), p.2)
-  verify_eq := fun ⟨s, o⟩ tr ↦ (verifier_verify I s o tr).trans (if_pos rfl).symm
+  verify_eq := fun ⟨s, o⟩ tr ↦ (verifier_verify I s o tr).trans (ite_eq_left rfl).symm
 
 /-! ## Completeness -/
 
@@ -301,7 +301,7 @@
   obtain ⟨pr, hpr, rfl⟩ := Reduction.mem_support_run_of_guarded _ (guarded I) (s, o) witIn hx
   obtain ⟨hmsg, hout⟩ := prover_run_support I s o pr hpr
   have hc : (guarded I).check (s, o) pr.1 = true := rfl
-  rw [if_pos hc]
+  rw [ite_eq_left hc]
   exact ⟨_, rfl, pooled_mem_pub I s o hIn (pr.1 0), congrArg Prod.fst hout⟩
 
 /-! ## Knowledge soundness -/
@@ -354,10 +354,10 @@
     · rfl
     · exact absurd hi (by decide)
   subst hi0
-  refine le_trans (probEvent_mono ?_) (probEvent_uniformSample_le_of_subsingleton (α := E)
+  refine le_trans (prEvent_mono _ _ _ ?_) (probEvent_uniformSample_le_of_subsingleton (α := E)
     (fun r ↦ ((s, o), ()) ∉ Seam.table I ∧ ((pooled I s r, o), ()) ∈ Seam.pub I)
     fun r₁ r₂ h₁ h₂ ↦ bad_challenge_unique I s o h₁.1 h₁.2 h₂.2)
-  rintro r - ⟨_, hin, hout⟩
+  rintro r ⟨_, hin, hout⟩
   exact ⟨hin, hout⟩
 
 end PublicInput
@@ -440,10 +440,10 @@
     · rfl
     · exact absurd hi (by decide)
   subst hi0
-  refine le_trans (probEvent_mono ?_) (probEvent_uniformSample_le_of_subsingleton (α := E)
+  refine le_trans (prEvent_mono _ _ _ ?_) (probEvent_uniformSample_le_of_subsingleton (α := E)
     (fun r ↦ ((s, o), ()) ∉ Seam.table I ∧ ((pooled I s r, o), ()) ∈ Seam.pub I)
     fun r₁ r₂ h₁ h₂ ↦ bad_challenge_unique I s o h₁.1 h₁.2 h₂.2)
-  rintro r - ⟨_, hin, hout⟩
+  rintro r ⟨_, hin, hout⟩
   exact ⟨hin, hout⟩
 
 end PublicInput
```

Output (`Probe1NoCheck.v434.lean.new.out`), 4 s:

```text
.claude/reports/blueprint-review/probes/code-pubinput/Probe1NoCheck.v434.lean:341:4: error: Type mismatch
  Verifier.GuardedForm.of_probEvent_pos (guarded I) init impl stmt tr (fun sample => (sample, x✝) ∈ Seam.pub I) h
has type
  (guarded I).check stmt tr = true ∧ ((guarded I).out stmt tr, x✝) ∈ Seam.pub I
but is expected to have type
  if h0 : ↑(Fin.last 2) = 0 then (stmt, ()) ∈ Seam.table I
  else
    if h1 : ↑(Fin.last 2) = 1 then ((pooled I stmt.1 (tr ⟨0, ⋯⟩), stmt.2), ()) ∈ Seam.pub I
    else check I stmt.1 (tr ⟨0, ⋯⟩) (tr ⟨1, ⋯⟩) = true ∧ ((pooled I stmt.1 (tr ⟨0, ⋯⟩), stmt.2), ()) ∈ Seam.pub I
'LeanerVM.Protocol.Probe1.PublicInput.verifier_verify' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe1.publicInputComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe1.publicInputSecurity' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe1.publicInputSecurity'' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=1
```

Agrees with the dossier's recorded result (`code-pubinput.md` C.3): the one expected error at
the same position (`341:4`, the unchanged `stateFunction`'s `toFun_full`), and the repaired
`publicInputSecurity'` (a full `Phase.Security` of the verifier that checks nothing) on the
kernel's three axioms.

### 1.6 Control: mutation 2, no check, the prover's values pooled (`Probe2TrustProver.v434.lean`)

Generated by `mutate.py …/Probe2TrustProver.v434.lean Probe2 …/tools/v434/m2.py`. Diff of the
v434 probe against the old probe:

```diff
@@ -299,7 +299,7 @@
 def guarded : (verifier I).toVerifier.GuardedForm where
   check := fun _ _ ↦ true
   out := fun p tr ↦ (pooledFrom I p.1 (tr 0) (tr 1), p.2)
-  verify_eq := fun ⟨s, o⟩ tr ↦ (verifier_verify I s o tr).trans (if_pos rfl).symm
+  verify_eq := fun ⟨s, o⟩ tr ↦ (verifier_verify I s o tr).trans (ite_eq_left rfl).symm
 
 /-! ## Completeness -/
 
@@ -332,7 +332,7 @@
   obtain ⟨pr, hpr, rfl⟩ := Reduction.mem_support_run_of_guarded _ (guarded I) (s, o) witIn hx
   obtain ⟨hmsg, hout⟩ := prover_run_support I s o pr hpr
   have hc : (guarded I).check (s, o) pr.1 = true := rfl
-  rw [if_pos hc]
+  rw [ite_eq_left hc]
   have hpool : (guarded I).out (s, o) pr.1 = (pooled I s (pr.1 0), o) := by
     show (pooledFrom I s (pr.1 0) (pr.1 1), o) = (pooled I s (pr.1 0), o)
     rw [hmsg, pooledFrom_expected]
@@ -389,10 +389,10 @@
     · rfl
     · exact absurd hi (by decide)
   subst hi0
-  refine le_trans (probEvent_mono ?_) (probEvent_uniformSample_le_of_subsingleton (α := E)
+  refine le_trans (prEvent_mono _ _ _ ?_) (probEvent_uniformSample_le_of_subsingleton (α := E)
     (fun r ↦ ((s, o), ()) ∉ Seam.table I ∧ ((pooled I s r, o), ()) ∈ Seam.pub I)
     fun r₁ r₂ h₁ h₂ ↦ bad_challenge_unique I s o h₁.1 h₁.2 h₂.2)
-  rintro r - ⟨_, hin, hout⟩
+  rintro r ⟨_, hin, hout⟩
   exact ⟨hin, hout⟩
 
 end PublicInput
@@ -475,20 +475,20 @@
           (default : Transcript 0 pSpec)) witMid := by
     intro r
     obtain ⟨hc, hout⟩ := hacc r
-    have hpos : Pr[fun stmtOut => (stmtOut, ()) ∈ relOut
-        | OptionT.mk do
+    have hpos : Pr{let stmtOut ← OptionT.mk do
             (simulateQ impl (V.run stmt (tr2 r (msg r)))).run'
-              (← (pure () : ProbComp Unit))] > 0 := by
+              (← (pure () : ProbComp Unit))}[(stmtOut, ()) ∈ relOut] > 0 := by
       have hv : V.run stmt (tr2 r (msg r)) = pure (G.out stmt (tr2 r (msg r))) := by
         have := G.verify_eq stmt (tr2 r (msg r))
-        rw [if_pos hc] at this
+        rw [ite_eq_left hc] at this
         exact this
       rw [hv]
-      change Pr[_ | OptionT.mk (do let st ← (pure () : ProbComp Unit); (simulateQ impl
-        (OptionT.run (pure (G.out stmt (tr2 r (msg r))) :
-          OptionT (OracleComp []ₒ) StmtOut))).run' st)] > 0
+      change Pr{let sample ← OptionT.mk (do
+        let st ← (pure () : ProbComp Unit)
+        (simulateQ impl (OptionT.run (pure (G.out stmt (tr2 r (msg r))) :
+          OptionT (OracleComp []ₒ) StmtOut))).run' st)}[(sample, ()) ∈ relOut] > 0
       rw [OptionT.run_pure, simulateQ_pure]
-      rw [gt_iff_lt, probEvent_pos_iff]
+      rw [gt_iff_lt, OracleComp.OptionT.prEvent_mk_pos_iff]
       refine ⟨G.out stmt (tr2 r (msg r)), ?_, hout⟩
       simp
     have hfull := kSF.toFun_full stmt (tr2 r (msg r)) () hpos
@@ -499,15 +499,15 @@
     intro h0
     exact hin ((kSF.toFun_empty stmt _).mpr h0)
   -- So the bad event has probability one.
-  have hone : Pr[fun challenge : E => ∃ witMid,
+  have hone : Pr{let challenge ← $ᵗ E}[∃ witMid,
       ¬ kSF (Fin.castSucc 0) stmt (default : Transcript 0 pSpec)
           (ext.extractMid 0 stmt
             (Transcript.concat (m := (0 : Fin 2)) challenge
               (default : Transcript 0 pSpec)) witMid) ∧
         kSF (Fin.succ 0) stmt (Transcript.concat (m := (0 : Fin 2)) challenge
-          (default : Transcript 0 pSpec)) witMid | $ᵗ E] = 1 := by
-    rw [probEvent_eq_one_iff]
-    exact ⟨by simp, fun r _ ↦ hall r⟩
+          (default : Transcript 0 pSpec)) witMid] = 1 := by
+    rw [OracleComp.prEvent_eq_one_iff]
+    exact fun r _ ↦ hall r
   have hle : (1 : ℝ≥0∞) ≤ ((ε ⟨0, rfl⟩ : ℝ≥0) : ℝ≥0∞) := hone ▸ hbound
   exact absurd (ENNReal.coe_lt_one_iff.mpr hε) (not_lt.mpr hle)
 
@@ -528,8 +528,9 @@
   have h1 := hc stmtIn witIn hin
   dsimp only at h1
   have hpos := lt_of_lt_of_eq (zero_lt_one' ℝ≥0∞) h1.symm
-  obtain ⟨x, hx, hev⟩ := probEvent_pos_iff.mp hpos
-  rw [OptionT.mem_support_iff, OptionT.run_mk, mem_support_bind_iff] at hx
+  rw [OracleComp.OptionT.prEvent_mk_pos_iff] at hpos
+  obtain ⟨x, hx, hev⟩ := hpos
+  rw [mem_support_bind_iff] at hx
   obtain ⟨s, _, hx⟩ := hx
   exact h (some x) (support_simulateQ_run'_subset _ _ s hx) x rfl hev
 
```

Output (`Probe2TrustProver.v434.lean.new.out`), 5 s:

```text
.claude/reports/blueprint-review/probes/code-pubinput/Probe2TrustProver.v434.lean:160:32: warning: `if_true` has been deprecated: Use `ite_true` instead
.claude/reports/blueprint-review/probes/code-pubinput/Probe2TrustProver.v434.lean:162:52: warning: `if_false` has been deprecated: Use `ite_false` instead
.claude/reports/blueprint-review/probes/code-pubinput/Probe2TrustProver.v434.lean:376:4: error: Type mismatch
  Verifier.GuardedForm.of_probEvent_pos (guarded I) init impl stmt tr (fun sample => (sample, x✝) ∈ Seam.pub I) h
has type
  (guarded I).check stmt tr = true ∧ ((guarded I).out stmt tr, x✝) ∈ Seam.pub I
but is expected to have type
  if h0 : ↑(Fin.last 2) = 0 then (stmt, ()) ∈ Seam.table I
  else
    if h1 : ↑(Fin.last 2) = 1 then ((pooled I stmt.1 (tr ⟨0, ⋯⟩), stmt.2), ()) ∈ Seam.pub I
    else check I stmt.1 (tr ⟨0, ⋯⟩) (tr ⟨1, ⋯⟩) = true ∧ ((pooled I stmt.1 (tr ⟨0, ⋯⟩), stmt.2), ()) ∈ Seam.pub I
'LeanerVM.Protocol.Probe2.PublicInput.verifier_verify' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe2.PublicInput.complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe2.PublicInput.stateFunction' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe2.PublicInput.rbr' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Probe2.PublicInput.not_knowledgeSound' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=1
```

Agrees with the dossier's recorded result (`code-pubinput.md` C.6): the one expected error at
the same position (`376:4`), `complete` on the three axioms, and `not_knowledgeSound` (no
extractor, state function or error below one makes the verifier that pools the prover's values
unchecked round-by-round knowledge sound) on the three axioms. This run also exercises the
adapted `not_rbr` of 1.1. The two new warnings are Lean 4.34.1 deprecations (`if_true`,
`if_false`) inside the appended `claimsFrom_expected`.

### 1.7 Control: any message, any check (`ProbeAnyCheck.v434.lean`)

Generated by `mutate.py …/ProbeAnyCheck.v434.lean ProbeAny …/tools/v434/anycheck.py`. Diff of
the v434 probe against the old probe:

```diff
@@ -264,9 +264,9 @@
     (OracleComp.monadLift_liftM_OptionT _).symm]
   rw [simulateQ_optionT_bind_run, simulateQ_queryValues, pure_bind]
   by_cases h : check I s (tr 0) (tr 1) = true
-  · rw [if_pos h, if_pos h]
+  · rw [ite_eq_left h, ite_eq_left h]
     rfl
-  · rw [if_neg h, if_neg h]
+  · rw [ite_eq_right h, ite_eq_right h]
     rfl
 
 /-- The verifier is a check followed by a verdict, as data. -/
@@ -306,7 +306,7 @@
   obtain ⟨pr, hpr, rfl⟩ := Reduction.mem_support_run_of_guarded _ (guarded I) (s, o) witIn hx
   obtain ⟨hmsg, hout⟩ := prover_run_support I s o pr hpr
   have hc : (guarded I).check (s, o) pr.1 = true := decide_eq_true hmsg
-  rw [if_pos hc]
+  rw [ite_eq_left hc]
   exact ⟨_, rfl, pooled_mem_pub I s o hIn (pr.1 0), congrArg Prod.fst hout⟩
 
 /-! ## Knowledge soundness -/
@@ -359,10 +359,10 @@
     · rfl
     · exact absurd hi (by decide)
   subst hi0
-  refine le_trans (probEvent_mono ?_) (probEvent_uniformSample_le_of_subsingleton (α := E)
+  refine le_trans (prEvent_mono _ _ _ ?_) (probEvent_uniformSample_le_of_subsingleton (α := E)
     (fun r ↦ ((s, o), ()) ∉ Seam.table I ∧ ((pooled I s r, o), ()) ∈ Seam.pub I)
     fun r₁ r₂ h₁ h₂ ↦ bad_challenge_unique I s o h₁.1 h₁.2 h₂.2)
-  rintro r - ⟨_, hin, hout⟩
+  rintro r ⟨_, hin, hout⟩
   exact ⟨hin, hout⟩
 
 end PublicInput
@@ -451,9 +451,9 @@
     (OracleComp.monadLift_liftM_OptionT _).symm]
   rw [simulateQ_optionT_bind_run, simulateQ_queryValues, pure_bind]
   by_cases h : chk s (tr 0) (tr 1) = true
-  · rw [if_pos h, if_pos h]
+  · rw [ite_eq_left h, ite_eq_left h]
     rfl
-  · rw [if_neg h, if_neg h]
+  · rw [ite_eq_right h, ite_eq_right h]
     rfl
 
 def guardedG : (verifierG I chk).toVerifier.GuardedForm where
@@ -494,7 +494,7 @@
     show chk s (pr.1 0) (pr.1 1) = true
     rw [hmsg]
     exact hchk s (pr.1 0)
-  rw [if_pos hc]
+  rw [ite_eq_left hc]
   exact ⟨_, rfl, pooled_mem_pub I s o hIn (pr.1 0), congrArg Prod.fst hout⟩
 
 variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
@@ -534,10 +534,10 @@
     · rfl
     · exact absurd hi (by decide)
   subst hi0
-  refine le_trans (probEvent_mono ?_) (probEvent_uniformSample_le_of_subsingleton (α := E)
+  refine le_trans (prEvent_mono _ _ _ ?_) (probEvent_uniformSample_le_of_subsingleton (α := E)
     (fun r ↦ ((s, o), ()) ∉ Seam.table I ∧ ((pooled I s r, o), ()) ∈ Seam.pub I)
     fun r₁ r₂ h₁ h₂ ↦ bad_challenge_unique I s o h₁.1 h₁.2 h₂.2)
-  rintro r - ⟨_, hin, hout⟩
+  rintro r ⟨_, hin, hout⟩
   exact ⟨hin, hout⟩
 
 end PublicInput
```

Output (`ProbeAnyCheck.v434.lean.new.out`), 4 s:

```text
'LeanerVM.Protocol.ProbeAny.securityG' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.ProbeAny.noCheckNoMessage' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.ProbeAny.noCheckJunk' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.ProbeAny.swappedCheck' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.ProbeAny.specification' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```

Agrees with the dossier's recorded result (`code-pubinput.md` C.4), line for line.

### 1.8 Mutations 4b and 6: could not run, not written

The task lists mutation 4b (the deployed combined check with the prover's values pooled) and
mutation 6 (the claims pooled at a wrong point). Neither exists as a file: `code-pubinput.md`
C.12 says of 6 "Argued on paper; not written", and C.13 says of 4b that only its key lemma is
proved (that is `ProbeWordsLemma`, run in 1.4) and the phase itself is "Estimated at 120 lines;
**not written**". There is no `Probe4b*.lean`, `Probe6*.lean`, `tools/m4b.py` or `tools/m6.py`
under `probes/code-pubinput/`. Nothing was run for them; they stay unverified as the dossier
says. What would verify them is written in `code-pubinput.md` C.12 (a height-4 instance and
the two refutations) and C.13 (the state function and the case split).

## 2. The spine (`probes/code-spine/`)

The three probes that write numerals other than `0` and `1` in `K` (found with
`grep -ln "(2 : K)\|, 2\b" probes/code-spine/*.lean`: `P2Relation`, `P3aSeams`,
`P5PassThrough`) were copied to `.v434.lean` and every such numeral was rewritten as
`K.ofBits 2`, the encoded word the repository's adapted test uses (`LeanerVM/Parameters/Field.lean:75`
at `144c5aa`: `def K.ofBits (n : ℕ) : K := BF64.ofBitVec (BitVec.ofNat 64 n)`; the test
`tests/LeanerVMTests/Protocol/Spine.lean` at `144c5aa` writes `⟨#v[1, 1, 1, 1, K.ofBits 2, 0, 0, 0]⟩`
and `(K.ofBits 2 : K)`). `CMvPolynomial.X 2` (a variable index) is not a numeral in `K` and was
left. No probe of this directory imports `CompPoly.Multivariate.CMvPolynomial`, so no import
changed. Command, from the repository root (no `-D` option, as in `code-spine.md`'s appendix):

```text
flock .claude/reports/blueprint-review/logs/lean.lock lake env lean <file> > <file>.new.out 2>&1; echo "exit=$?" >> <file>.new.out
```

### 2.1 `P2Relation.v434.lean` (`M3Holds` on variants of the toy; the aliased layout)

The only numerals `2` in `K` are the three lists of the exhaustive check of `toyAlias`. At the
new pin `([0, 1, 2] : List K)` is `[0, 1, 0]`, so the unchanged check would test two values,
not three. Diff:

```diff
@@ -136,8 +136,8 @@
 -- `0, 1` in `{0, 1, 2}` satisfies it at a statement in `{0, 1, 2}`. On paper: balance forces
 -- cells `0, 1` to be `1, 1`, and the public line on column 2, now cells `0, 1`, forces cell 1
 -- to be `0`.
-#guard ([0, 1, 2] : List K).all fun a ↦ ([0, 1, 2] : List K).all fun b ↦
-  ([0, 1, 2] : List K).all fun s ↦
+#guard ([0, 1, K.ofBits 2] : List K).all fun a ↦ ([0, 1, K.ofBits 2] : List K).all fun b ↦
+  ([0, 1, K.ofBits 2] : List K).all fun s ↦
     decide (¬ M3Holds toyAlias s (⟨#v[a, b, 1, 1, 1, 0, 0, 0]⟩ : Column 3))
 
 end Probe
```

Output (`P2Relation.v434.lean.new.out`), 4 s:

```text
exit=0
```

Agrees with the dossier's recorded result (`code-spine.md` appendix: `exit=0`): every `#guard`
holds, including the exhaustive evidence that no stack with cells `0, 1` in
`{0, 1, K.ofBits 2}` satisfies `M3Holds toyAlias` at a statement in `{0, 1, K.ofBits 2}`.

### 2.2 `P3aSeams.v434.lean` (each seam on the toy: an inhabitant and near misses; the zerocheck escape)

At the new pin `ofK 2 = ofK 0 = 0`, so the unchanged `eTwo` would be the point `0` (not a point
outside `{0, 1}`), and the unchanged `badConstraint` would have column 2 `[0, 0]`, which is
Boolean. Diff:

```diff
@@ -80,7 +80,7 @@
 def eZero : E := 0
 def eOne : E := 1
 /-- A point of `E` outside `{0, 1}`: the image of `2 : K` (the polynomial `x`). -/
-def eTwo : E := ofK 2
+def eTwo : E := ofK (K.ofBits 2)
 
 /-- Column 0 of the honest stack is `[1, 1]`: its extension is `1` everywhere. -/
 def col0One : ColumnClaim toy := ⟨⟨0, 0⟩, #v[eTwo], eOne⟩
@@ -101,7 +101,7 @@
   ⟨[⟨eOne, 0, CMvPolynomial.X 2 * CMvPolynomial.X 2 * CMvPolynomial.X 2, #v[eZero]⟩], eOne⟩
 
 /-- The stack of the repository's test `badConstraint`: column 2 is `[2, 0]`, not Boolean. -/
-def badConstraint : Column 3 := ⟨#v[1, 1, 1, 1, 2, 0, 0, 0]⟩
+def badConstraint : Column 3 := ⟨#v[1, 1, 1, 1, K.ofBits 2, 0, 0, 0]⟩
 
 /-! ## The bus seam -/
 
@@ -120,12 +120,12 @@
 #guard ¬ toy.ConstraintsVanish badConstraint
 #guard ¬ zeroAt0.Holds badConstraint
 #guard zeroAt1.Holds badConstraint
-#guard busPred toy ((2 : K), ⟨[zeroAt1], [col0One]⟩) badConstraint
-#guard ¬ M3Holds toy (2 : K) badConstraint
+#guard busPred toy ((K.ofBits 2 : K), ⟨[zeroAt1], [col0One]⟩) badConstraint
+#guard ¬ M3Holds toy (K.ofBits 2 : K) badConstraint
 
 -- A bus statement with no claim holds of every stack whose public line holds: the seam does
 -- not say which claims are emitted.
-#guard busPred toy ((2 : K), ⟨[], []⟩) badConstraint
+#guard busPred toy ((K.ofBits 2 : K), ⟨[], []⟩) badConstraint
 
 /-! ## The table and public-input seams -/
 
```

Output (`P3aSeams.v434.lean.new.out`), 3 s:

```text
exit=0
```

Agrees with the dossier's recorded result (`code-spine.md` appendix: `exit=0`): every inhabitant
and near miss of the bus, table, public and Flock seams holds as recorded, and the zerocheck
escape (the bus seam holds of `badConstraint`, which is outside `M3Holds`) holds with
`badConstraint` and the statement written as `K.ofBits 2`.

*Check that the runs evaluate.* Because the runs are fast (3 to 8 s: the imports are the built
oleans), a scratch copy `probes/probes-rerun/SanityP3a.lean` (this file with two false guards
added before `end Probe`) was run; both were rejected:

```text
.claude/reports/blueprint-review/probes/probes-rerun/SanityP3a.lean:159:0: error: Expression
  decide ¬busPred toy (1, { linear := [zeroAt0, zeroAt1], columns := [col0One] }) honest
did not evaluate to `true`
.claude/reports/blueprint-review/probes/probes-rerun/SanityP3a.lean:160:0: error: Expression
  decide (busPred toy (K.ofBits 2, { linear := [zeroAt1], columns := [col0One] }) honest)
did not evaluate to `true`
exit=1
```

### 2.3 `P5PassThrough`: the pass-through bus phase has no `Phase.Security` on the toy

**(a) The unchanged copy, as a control** (`P5PassThrough.unchanged.v434.lean`, `cp` of the old
file; empty diff). Output (`P5PassThrough.unchanged.v434.lean.new.out`), 8 s:

```text
.claude/reports/blueprint-review/probes/code-spine/P5PassThrough.unchanged.v434.lean:26:68: error: Tactic `decide` failed for proposition
  ¬M3Holds toy 2 badConstraint
because its `Decidable` instance
  instDecidableNot
did not reduce to `isTrue` or `isFalse`.

Reduction got stuck at the `Decidable` instance
  match h :
    (↑(CMvPolynomial.eval (toy.row badConstraint ⟨0, ⋯⟩ ⟨0, ⋯⟩) constraint).1.toFin).beq
      ↑(Fin.Internal.ofNat (2 ^ 64) ⋯ 0) with
  | true => isTrue ⋯
  | false => isFalse ⋯
.claude/reports/blueprint-review/probes/code-spine/P5PassThrough.unchanged.v434.lean:50:14: warning: `probEvent` has been deprecated: VCVio retiring probability API: use `𝒟[mx] {x | p x}`
.claude/reports/blueprint-review/probes/code-spine/P5PassThrough.unchanged.v434.lean:58:11: warning: `probEvent` has been deprecated: VCVio retiring probability API: use `𝒟[mx] {x | p x}`
.claude/reports/blueprint-review/probes/code-spine/P5PassThrough.unchanged.v434.lean:64:42: error: Application type mismatch: The argument
  hpos
has type
  (probEvent
      (OptionT.mk
        ((simulateQ noImpl (Verifier.run stmt tr (Phase.passThrough toy dropAll).red.verifier.toVerifier)).run' ()))
      fun stmtOut => (stmtOut, ()) ∈ Seam.bus toy) >
    0
but is expected to have type
  𝒟[do
        let stmtOut ←
          OptionT.mk do
              let __do_lift ← pure ()
              (simulateQ noImpl (Verifier.run stmt tr (Phase.passThrough toy dropAll).red.verifier.toVerifier)).run'
                  __do_lift
        pure ((stmtOut, ()) ∈ Seam.bus toy)]
      {True} >
    0
in the application
  ksf.toFun_full stmt tr () hpos
'Probe.no_security' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
exit=1
```

Two independent failures, both caused by the upgrade: `bad_not_m3Holds` (line 26) no longer
holds by `decide +kernel` with `(2 : K)` (at the new pin `2 : K` is `0`, so `badConstraint`'s
column 2 is `[0, 0]`, which is Boolean; the kernel's reduction gets stuck rather than returning
`isFalse`, so this run does not itself show the proposition false), and the old `Pr[P | c]`
(the deprecated `probEvent`) no longer matches the event of ArkLib `7653a901`'s `toFun_full`
(line 64). `no_security` is therefore recorded with `sorryAx`. This is the expected behaviour
of an unadapted probe, not a result about the spine.

**(b) The adapted copy** (`P5PassThrough.v434.lean`): the numeral `2` in `K` written
`K.ofBits 2` wherever it is a cell or a statement, and the event restated in the new
`Pr{…}[…]` form with `OracleComp.OptionT.prEvent_mk_pos_iff`, as the repository's
`ToArkLib/GuardedVerdict.lean` does at `144c5aa`. Diff:

```diff
@@ -17,23 +17,23 @@
 namespace Probe
 
 /-- The test's stack `badConstraint`: column 2 is `[2, 0]`. -/
-def badConstraint : Column 3 := ⟨#v[1, 1, 1, 1, 2, 0, 0, 0]⟩
+def badConstraint : Column 3 := ⟨#v[1, 1, 1, 1, K.ofBits 2, 0, 0, 0]⟩
 
 /-- The statement map of `trivPhases.bus`: no claim. -/
 def dropAll (s : K) : K × BusOut toy := (s, ⟨[], []⟩)
 
 /-- Outside the relation. -/
-theorem bad_not_m3Holds : ¬ M3Holds toy (2 : K) badConstraint := by decide +kernel
+theorem bad_not_m3Holds : ¬ M3Holds toy (K.ofBits 2 : K) badConstraint := by decide +kernel
 
 /-- Inside the bus seam, with no claim. -/
 theorem bad_mem_bus :
-    ((dropAll 2, fun _ : Fin 1 ↦ badConstraint), ()) ∈ Seam.bus toy :=
+    ((dropAll (K.ofBits 2), fun _ : Fin 1 ↦ badConstraint), ()) ∈ Seam.bus toy :=
   ⟨by simp [dropAll], by simp [dropAll], by simp [dropAll], by decide +kernel, trivial⟩
 
 /-- The reflection hypothesis of `Phase.passThroughSecurity` is false at the bus seam. -/
 theorem not_reflects : ¬ ∀ (s : K) (o : ∀ i, TheOracle toy i),
     ((dropAll s, o), ()) ∈ Seam.bus toy → ((s, o), ()) ∈ Seam.commit toy := fun h ↦
-  bad_not_m3Holds (h 2 (fun _ ↦ badConstraint) bad_mem_bus)
+  bad_not_m3Holds (h (K.ofBits 2) (fun _ ↦ badConstraint) bad_mem_bus)
 
 /-- The empty implementation of the empty shared oracle. -/
 def noImpl : QueryImpl []ₒ (StateT Unit ProbComp) := fun t ↦ PEmpty.elim t
@@ -43,23 +43,25 @@
 theorem no_security (S : Phase.Security toy (Phase.passThrough toy dropAll) (Seam.commit toy)
     (Seam.bus toy)) : False := by
   have ksf := S.kSF (pure ()) noImpl
-  let stmt : K × ∀ i, TheOracle toy i := (2, fun _ ↦ badConstraint)
+  let stmt : K × ∀ i, TheOracle toy i := (K.ofBits 2, fun _ ↦ badConstraint)
   let tr : (Phase.passThrough toy dropAll).pSpec.FullTranscript := fun i ↦ Fin.elim0 i
   have htr : tr = (default : (Phase.passThrough toy dropAll).pSpec.Transcript 0) :=
     funext fun i ↦ Fin.elim0 i
-  have hpos : Pr[fun stmtOut ↦ (stmtOut, ()) ∈ Seam.bus toy | OptionT.mk do
+  have hpos : Pr{let stmtOut ← OptionT.mk do
       (simulateQ noImpl ((Phase.passThrough toy dropAll).red.verifier.toVerifier.run stmt
-        tr)).run' (← (pure () : ProbComp Unit))] > 0 := by
+        tr)).run' (← (pure () : ProbComp Unit))}[(stmtOut, ()) ∈ Seam.bus toy] > 0 := by
     have hrun : (Phase.passThrough toy dropAll).red.verifier.toVerifier.run stmt tr =
-        pure (dropAll 2, fun _ ↦ badConstraint) :=
-      Component.passThroughVerifier_toVerifier_run (TheOracle toy) dropAll 2
+        pure (dropAll (K.ofBits 2), fun _ ↦ badConstraint) :=
+      Component.passThroughVerifier_toVerifier_run (TheOracle toy) dropAll (K.ofBits 2)
         (fun _ ↦ badConstraint) tr
     rw [hrun]
-    change Pr[_ | OptionT.mk (do let st ← (pure () : ProbComp Unit); (simulateQ noImpl
-      (OptionT.run (pure (dropAll 2, fun _ : Fin 1 ↦ badConstraint)))).run' st)] > 0
+    change Pr{let sample ← OptionT.mk (do
+      let st ← (pure () : ProbComp Unit)
+      (simulateQ noImpl (OptionT.run (pure (dropAll (K.ofBits 2),
+        fun _ : Fin 1 ↦ badConstraint)))).run' st)}[(sample, ()) ∈ Seam.bus toy] > 0
     rw [OptionT.run_pure, simulateQ_pure]
-    rw [gt_iff_lt, probEvent_pos_iff]
-    refine ⟨(dropAll 2, fun _ ↦ badConstraint), ?_, bad_mem_bus⟩
+    rw [gt_iff_lt, OracleComp.OptionT.prEvent_mk_pos_iff]
+    refine ⟨(dropAll (K.ofBits 2), fun _ ↦ badConstraint), ?_, bad_mem_bus⟩
     simp
   have hfull := ksf.toFun_full stmt tr () hpos
   rw [htr] at hfull
```

Output (`P5PassThrough.v434.lean.new.out`), 3 s:

```text
'Probe.no_security' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```

Agrees with the dossier's recorded result (`code-spine.md` appendix: `'Probe.no_security'
depends on axioms: [propext, Classical.choice, Quot.sound]`, `exit=0`): at the new pins the type
`Phase.Security toy (Phase.passThrough toy dropAll) (Seam.commit toy) (Seam.bus toy)` is still
empty, with the counterexample stack `badConstraint` (column 2 `[K.ofBits 2, 0]`) at the
statement `K.ofBits 2`.

### 2.4 Control: `P4Junk.v434.lean` (five phases that check nothing, at declared error 1)

Copied unchanged (`cp P4Junk.lean P4Junk.v434.lean`; empty diff); it has no numeral other than
`0` and `1` in `K` and no probability event. Output (`P4Junk.v434.lean.new.out`), 3 s:

```text
.claude/reports/blueprint-review/probes/code-spine/P4Junk.v434.lean:99:8: warning: `if_pos` has been deprecated: Use `ite_eq_left` instead
'Probe.junkSecurity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Probe.piopError_junk' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```

Agrees with the dossier's recorded result (`code-spine.md` appendix): `junkSecurity` (an
inhabitant of `Phases.Security` of the toy by five phases that check nothing, each with one
wasted challenge at declared error `1`) and `piopError_junk` on the kernel's three axioms. The
one warning is Lean 4.34.1's deprecation of `if_pos` (line 99).

## 3. Layer 1 (`probes/code-layer1/`)

Command, from the repository root: the brief's (no `-D` option), as `code-layer1.md` section I
records for `OffsetsProbe` and `ValuesProbe`. (`DuplicatesProbe` and `StridedProbe` were run at
the old pin with the old Lean binary and a hand-made `LEAN_PATH`, `code-layer1.md` I; here all
four ran through `lake env lean`.)

### 3.1 `ValuesProbe.v434.lean` (Layer 1's definitions against numbers from the pinned Python verifier)

Every numeral other than `0` and `1` in `K` (the limbs given to `E.ofLimbs`, the tables, the
stack `arbitrary`, the table `short`, the points and the result `1935` of the padding check, the
expected lists) was rewritten as `K.ofBits n`, the same word it denoted at the old pin (the
expected values were produced by `values.py` from the pinned Python verifier and are unchanged).
One API change: at CompPoly `572f9973` `K` is a structure wrapping `BitVec 64`, so the old
`(·.toNat)` (which was `BitVec.toNat` when `K` was `BitVec 64`) is written `(·.toBitVec.toNat)`.
`gpow` (`LeanerVM/Parameters/Generator.lean:46` at `144c5aa`, `abbrev gpow (i : ℕ) : K := g ^ i`)
takes a natural exponent and was left. Diff:

```diff
@@ -24,13 +24,13 @@
 def answer {n : ℕ} (q : Column n) (z : Vector E n) : E := OracleInterface.answer q z
 
 /-- The point `ζ` of `values.py`. -/
-def zeta : Vector E 4 := #v[E.ofLimbs 3 1 0, E.ofLimbs 5 0 7, E.ofLimbs 2 2 2, E.ofLimbs 0 1 0]
+def zeta : Vector E 4 := #v[E.ofLimbs (K.ofBits 3) 1 0, E.ofLimbs (K.ofBits 5) 0 (K.ofBits 7), E.ofLimbs (K.ofBits 2) (K.ofBits 2) (K.ofBits 2), E.ofLimbs 0 1 0]
 
 /-- The point `α` of `values.py`. -/
-def alpha : Vector E 4 := #v[E.ofLimbs 9 0 1, E.ofLimbs 0 4 0, E.ofLimbs 6 6 0, E.ofLimbs 1 2 3]
+def alpha : Vector E 4 := #v[E.ofLimbs (K.ofBits 9) 0 1, E.ofLimbs 0 (K.ofBits 4) 0, E.ofLimbs (K.ofBits 6) (K.ofBits 6) 0, E.ofLimbs 1 (K.ofBits 2) (K.ofBits 3)]
 
 /-- `α` with its coordinates reversed. -/
-def alphaRev : Vector E 4 := #v[E.ofLimbs 1 2 3, E.ofLimbs 6 6 0, E.ofLimbs 0 4 0, E.ofLimbs 9 0 1]
+def alphaRev : Vector E 4 := #v[E.ofLimbs 1 (K.ofBits 2) (K.ofBits 3), E.ofLimbs (K.ofBits 6) (K.ofBits 6) 0, E.ofLimbs 0 (K.ofBits 4) 0, E.ofLimbs (K.ofBits 9) 0 1]
 
 /-! ## B.6 The bytecode column -/
 
@@ -43,7 +43,7 @@
   code i := match i.val with
     | 0 => .xor (gpow 1) (gpow 2) (gpow 3)
     | 1 => .mulNative (gpow 4) (gpow 5) (gpow 6)
-    | 2 => .setConstant (gpow 7) (E.ofLimbs 11 12 13)
+    | 2 => .setConstant (gpow 7) (E.ofLimbs (K.ofBits 11) (K.ofBits 12) (K.ofBits 13))
     | 3 => .deref (gpow 8) (gpow 9) (gpow 10) .pc
     | 4 => .deref (gpow 21) (gpow 22) (gpow 23) .fp
     | 5 => .deref (gpow 24) (gpow 25) (gpow 26) .cell
@@ -57,18 +57,18 @@
 
 #guard pyTable.length = 256
 -- All 256 cells: the encoding, the opcode values, the slot order and the cell order.
-#guard (bytecodeColumn prog16).values.toList.map (·.toNat) = pyTable
+#guard (bytecodeColumn prog16).values.toList.map (·.toBitVec.toNat) = pyTable
 
 /-- The oracle's answer at `(ζ, α)`. -/
 def bcAnswer : E := answer (bytecodeColumn prog16) (zeta ++ alpha)
 
 -- The evaluation the pinned verifier makes (`verifier.py:566`), and the native evaluator.
-#guard bcAnswer = E.ofLimbs 1219889995492 3571792677380 1279835512890
-#guard bytecodeColumnEval prog16 zeta alpha = E.ofLimbs 1219889995492 3571792677380 1279835512890
+#guard bcAnswer = E.ofLimbs (K.ofBits 1219889995492) (K.ofBits 3571792677380) (K.ofBits 1279835512890)
+#guard bytecodeColumnEval prog16 zeta alpha = E.ofLimbs (K.ofBits 1219889995492) (K.ofBits 3571792677380) (K.ofBits 1279835512890)
 -- Near miss: with `α` reversed the pinned verifier gets another value, and so does the oracle.
 #guard answer (bytecodeColumn prog16) (zeta ++ alphaRev) =
-  E.ofLimbs 1332010270628 4168742050444 1982034182034
-#guard bcAnswer ≠ E.ofLimbs 1332010270628 4168742050444 1982034182034
+  E.ofLimbs (K.ofBits 1332010270628) (K.ofBits 4168742050444) (K.ofBits 1982034182034)
+#guard bcAnswer ≠ E.ofLimbs (K.ofBits 1332010270628) (K.ofBits 4168742050444) (K.ofBits 1982034182034)
 
 /-- The opposite layout: slot bits low, instruction bits high. -/
 def wrongColumn (prog : Program) : Column (4 + prog.logSize) :=
@@ -86,7 +86,7 @@
 -- layout: cell `0 + 16 * 3` is instruction 0's opcode there, and slot 0 of instruction 3 here.
 #guard (bytecodeColumn prog16).values.toList[48]! = Opcode.xor.code
 #guard (wrongColumn prog16).values.toList[48]! = 0
-#guard (wrongColumn prog16).values.toList.map (·.toNat) ≠ pyTable
+#guard (wrongColumn prog16).values.toList.map (·.toBitVec.toNat) ≠ pyTable
 
 /-- What the bus phase needs and Layer 1 does not state: the program's share of a bytecode
 block is one evaluation of the bytecode column, the slots weighted by `eq(w, ·)`. -/
@@ -106,10 +106,10 @@
 
 /-! ## B.5 The index column -/
 
-#guard answer (idxColumn 4) zeta = E.ofLimbs 950617 874814 877803
-#guard idxColumnEval zeta = E.ofLimbs 950617 874814 877803
-#guard idxColumnEval (#v[E.ofLimbs 3 1 0, E.ofLimbs 5 0 7] : Vector E 2) = E.ofLimbs 109 29 108
-#guard (idxColumn 4).values.toList.map (·.toNat) = (List.range 16).map (2 ^ ·)
+#guard answer (idxColumn 4) zeta = E.ofLimbs (K.ofBits 950617) (K.ofBits 874814) (K.ofBits 877803)
+#guard idxColumnEval zeta = E.ofLimbs (K.ofBits 950617) (K.ofBits 874814) (K.ofBits 877803)
+#guard idxColumnEval (#v[E.ofLimbs (K.ofBits 3) 1 0, E.ofLimbs (K.ofBits 5) 0 (K.ofBits 7)] : Vector E 2) = E.ofLimbs (K.ofBits 109) (K.ofBits 29) (K.ofBits 108)
+#guard (idxColumn 4).values.toList.map (·.toBitVec.toNat) = (List.range 16).map (2 ^ ·)
 
 /-! ## B.2, B.3 Selectors and the two paddings -/
 
@@ -126,15 +126,15 @@
 /-- The tables `[1, 2, 3, 4]`, `[5, 6]`, `[7]`. -/
 def tables : blocks.Tables K :=
   show (b : Fin 3) → CMlPolynomialEval K (![2, 1, 0] b) from fun b ↦ match b with
-    | 0 => (#v[1, 2, 3, 4] : CMlPolynomialEval K 2)
-    | 1 => (#v[5, 6] : CMlPolynomialEval K 1)
-    | 2 => (#v[7] : CMlPolynomialEval K 0)
+    | 0 => (#v[1, (K.ofBits 2), (K.ofBits 3), (K.ofBits 4)] : CMlPolynomialEval K 2)
+    | 1 => (#v[(K.ofBits 5), (K.ofBits 6)] : CMlPolynomialEval K 1)
+    | 2 => (#v[(K.ofBits 7)] : CMlPolynomialEval K 0)
 
 /-- The tables over `E`. -/
 def tablesE : blocks.Tables E := fun b ↦ CMlPolynomialEval.map (algebraMap K E) (tables b)
 
 /-- The first three coordinates of `ζ`. -/
-def z3 : Vector E 3 := #v[E.ofLimbs 3 1 0, E.ofLimbs 5 0 7, E.ofLimbs 2 2 2]
+def z3 : Vector E 3 := #v[E.ofLimbs (K.ofBits 3) 1 0, E.ofLimbs (K.ofBits 5) 0 (K.ofBits 7), E.ofLimbs (K.ofBits 2) (K.ofBits 2) (K.ofBits 2)]
 
 /-- The selector weights, block by block. -/
 def weights : List E := (List.finRange 3).map fun b ↦ blocks.selectorWeight blocks_total_le b z3
@@ -144,42 +144,43 @@
   eval₂Mle (tables b) (algebraMap K E) (blocks.lowPoint blocks_total_le b z3)
 
 -- `eq(sel_b, ζ_hi)` as `Placement.eq_above` computes it (`verifier.py:299-302`).
-#guard weights = [E.ofLimbs 3 2 2, E.ofLimbs 6 8 8, E.ofLimbs 2 26 30]
-#guard blocksAt = [E.ofLimbs 46 11 42, E.ofLimbs 0 3 0, E.ofLimbs 7 0 0]
+#guard weights = [E.ofLimbs (K.ofBits 3) (K.ofBits 2) (K.ofBits 2), E.ofLimbs (K.ofBits 6) (K.ofBits 8) (K.ofBits 8), E.ofLimbs (K.ofBits 2) (K.ofBits 26) (K.ofBits 30)]
+#guard blocksAt = [E.ofLimbs (K.ofBits 46) (K.ofBits 11) (K.ofBits 42), E.ofLimbs 0 (K.ofBits 3) 0, E.ofLimbs (K.ofBits 7) 0 0]
 -- The witness stack (pad 0) and a leaf stack (pad 1) at `ζ`.
-#guard eval₂Mle (blocks.stackColumn tables 3).values (algebraMap K E) z3 = E.ofLimbs 38 3 34
-#guard evalMle (blocks.stackAt tablesE 3 1) z3 = E.ofLimbs 32 19 54
+#guard eval₂Mle (blocks.stackColumn tables 3).values (algebraMap K E) z3 = E.ofLimbs (K.ofBits 38) (K.ofBits 3) (K.ofBits 34)
+#guard evalMle (blocks.stackAt tablesE 3 1) z3 = E.ofLimbs (K.ofBits 32) (K.ofBits 19) (K.ofBits 54)
 -- The padding term of equation (2), `1 + Σ_b eq(sel_b, ζ_hi)` (`verifier.py:589`).
-#guard 1 + weights.sum = E.ofLimbs 6 16 20
-#guard (List.zipWith (· * ·) weights blocksAt).sum + (1 + weights.sum) = E.ofLimbs 32 19 54
+#guard 1 + weights.sum = E.ofLimbs (K.ofBits 6) (K.ofBits 16) (K.ofBits 20)
+#guard (List.zipWith (· * ·) weights blocksAt).sum + (1 + weights.sum) = E.ofLimbs (K.ofBits 32) (K.ofBits 19) (K.ofBits 54)
 -- Near misses: the wrong pad, and the padding term read as the constant 1.
-#guard evalMle (blocks.stackAt tablesE 3 0) z3 ≠ E.ofLimbs 32 19 54
-#guard (List.zipWith (· * ·) weights blocksAt).sum + 1 ≠ E.ofLimbs 32 19 54
+#guard evalMle (blocks.stackAt tablesE 3 0) z3 ≠ E.ofLimbs (K.ofBits 32) (K.ofBits 19) (K.ofBits 54)
+#guard (List.zipWith (· * ·) weights blocksAt).sum + 1 ≠ E.ofLimbs (K.ofBits 32) (K.ofBits 19) (K.ofBits 54)
 
 /-! ## B.7 A column claim as a weight -/
 
 /-- The claim's point on block 1, lifted. -/
-def lifted : Vector E 3 := blocks.extendPoint blocks_total_le (1 : Fin 3) #v[E.ofLimbs 3 1 0]
+def lifted : Vector E 3 := blocks.extendPoint blocks_total_le (1 : Fin 3) #v[E.ofLimbs (K.ofBits 3) 1 0]
 
 /-- A stack no honest prover commits. -/
-def arbitrary : Column 3 := ⟨#v[9, 8, 7, 6, 5, 4, 3, 2]⟩
+def arbitrary : Column 3 := ⟨#v[(K.ofBits 9), (K.ofBits 8), (K.ofBits 7), (K.ofBits 6), (K.ofBits 5), (K.ofBits 4), (K.ofBits 3), (K.ofBits 2)]⟩
 
-#guard lifted = #v[E.ofLimbs 3 1 0, 0, 1]
-#guard (eqWeight lifted).pair arbitrary = E.ofLimbs 6 1 0
-#guard (eqWeight lifted).mle #v[E.ofLimbs 1 1 0, E.ofLimbs 0 2 0, E.ofLimbs 7 0 0] =
-  E.ofLimbs 9 18 0
+#guard lifted = #v[E.ofLimbs (K.ofBits 3) 1 0, 0, 1]
+#guard (eqWeight lifted).pair arbitrary = E.ofLimbs (K.ofBits 6) 1 0
+#guard (eqWeight lifted).mle #v[E.ofLimbs 1 1 0, E.ofLimbs 0 (K.ofBits 2) 0, E.ofLimbs (K.ofBits 7) 0 0] =
+  E.ofLimbs (K.ofBits 9) (K.ofBits 18) 0
 -- Near miss: the selector bits reversed, `(1, 0)`, weigh cells 2 and 3.
-#guard (eqWeight (#v[E.ofLimbs 3 1 0, 1, 0] : Vector E 3)).pair arbitrary ≠ E.ofLimbs 6 1 0
+#guard (eqWeight (#v[E.ofLimbs (K.ofBits 3) 1 0, 1, 0] : Vector E 3)).pair arbitrary ≠ E.ofLimbs (K.ofBits 6) 1 0
 
 /-! ## B.4 Back-loaded padding -/
 
 /-- The table `[3, 5]` on one variable. -/
-def short : CMlPolynomialEval K 1 := #v[3, 5]
+def short : CMlPolynomialEval K 1 := #v[(K.ofBits 3), (K.ofBits 5)]
 
-#guard evalMle (padHigh short 2) ((#v[7] : Vector K 1) ++ (#v[11, 13] : Vector K 2)) = 1935
-#guard (padHigh short 2).toList = [0, 0, 0, 0, 0, 0, 3, 5]
+#guard evalMle (padHigh short 2) ((#v[(K.ofBits 7)] : Vector K 1) ++ (#v[(K.ofBits 11), (K.ofBits 13)] : Vector K 2)) =
+  K.ofBits 1935
+#guard (padHigh short 2).toList = [0, 0, 0, 0, 0, 0, (K.ofBits 3), (K.ofBits 5)]
 -- Near miss: padding on the low variables (front-loaded) is another table.
-#guard (padHigh short 2).toList ≠ [0, 0, 0, 3, 0, 0, 0, 5]
+#guard (padHigh short 2).toList ≠ [0, 0, 0, (K.ofBits 3), 0, 0, 0, (K.ofBits 5)]
 
 /-! ## C A layout need not separate its columns -/
 
@@ -187,7 +188,8 @@
 def aliased : Layout 3 (Fin 3) (fun _ ↦ 2) :=
   (blocks.layout blocks_total_le).comap (fun _ ↦ (0 : Fin 3)) (fun _ ↦ rfl)
 
-#guard (List.finRange 3).all fun c ↦ (aliased.read arbitrary c).values.toList = [9, 8, 7, 6]
+#guard (List.finRange 3).all fun c ↦ (aliased.read arbitrary c).values.toList =
+  [(K.ofBits 9), (K.ofBits 8), (K.ofBits 7), (K.ofBits 6)]
 
 /-! ## Axioms -/
 
```

Output (`ValuesProbe.v434.lean.new.out`), 23 s:

```text
'LeanerVM.Protocol.Blocks.unstack_eval₂' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Blocks.unstack_getElem' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Blocks.readColumn_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Blocks.layout' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Layout.comap' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Blocks.stack_eval_ambient' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Blocks.stack_eval_ambient_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Blocks.stackColumn_eval_ambient' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.sumCube_padHigh' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.evalMle_padHigh' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.ColumnClaim.holds_iff_weighted' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.eqWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.idxColumn_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.idxColumnEval_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.bytecodeColumn_answer_boolVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.bytecodeColumn_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.BlockClaim.isValid_iff_pairing' depends on axioms: [propext, Classical.choice, Quot.sound]
'Probe.bytecodeColumn_answer_slots' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```

Agrees with the dossier's recorded result (`code-layer1.md` I.4): every `#guard` holds at the
new pins (the bytecode column cell for cell against the transcription of the Rust encoder, the
oracle's and the native evaluator's answers against `verifier.py:566`, the index column, the
selector weights, both paddings, the lifted point, back-loaded padding, the aliased layout, and
every near miss), and the same eighteen declarations depend on the kernel's three axioms only.

### 3.2 `StridedProbe.v434.lean` (the strided selection identity Layer 1 lacks)

The theorem `evalMle_boolVec_append` is over an arbitrary commutative ring and unchanged; the
`#guard`s on the table `packed` used numerals `7, 10–13, 20–23` in `K`, rewritten as
`K.ofBits n`. Diff:

```diff
@@ -47,14 +47,15 @@
     exact absurd (Finset.mem_univ _) h
 
 /-- Slot 1 of four (two low bits) of an eight-cell table: cells 1 and 5. -/
-def packed : CMlPolynomialEval K 3 := #v[10, 11, 12, 13, 20, 21, 22, 23]
+def packed : CMlPolynomialEval K 3 := #v[K.ofBits 10, K.ofBits 11, K.ofBits 12, K.ofBits 13,
+  K.ofBits 20, K.ofBits 21, K.ofBits 22, K.ofBits 23]
 
-#guard (sliceLow (k := 2) (m := 1) packed (1 : Fin 4)).toList = [11, 21]
+#guard (sliceLow (k := 2) (m := 1) packed (1 : Fin 4)).toList = [K.ofBits 11, K.ofBits 21]
 -- The point `(slot bits 1, 0 | z)` reads the strided slice at `z`.
-#guard evalMle packed (#v[1, 0, 7] : Vector K 3) =
-  evalMle (#v[11, 21] : CMlPolynomialEval K 1) #v[7]
+#guard evalMle packed (#v[1, 0, K.ofBits 7] : Vector K 3) =
+  evalMle (#v[K.ofBits 11, K.ofBits 21] : CMlPolynomialEval K 1) #v[K.ofBits 7]
 -- Near miss: the aligned slice at high index 1 is cells 2 and 3, another column.
-#guard (slice (k := 1) (m := 2) packed (1 : Fin 4)).toList = [12, 13]
+#guard (slice (k := 1) (m := 2) packed (1 : Fin 4)).toList = [K.ofBits 12, K.ofBits 13]
 
 #print axioms evalMle_boolVec_append
 
```

Output (`StridedProbe.v434.lean.new.out`), 3 s:

```text
.claude/reports/blueprint-review/probes/code-layer1/StridedProbe.v434.lean:36:15: warning: `if_true` has been deprecated: Use `ite_true` instead
.claude/reports/blueprint-review/probes/code-layer1/StridedProbe.v434.lean:43:15: warning: `if_neg` has been deprecated: Use `ite_eq_right` instead
'Probe.evalMle_boolVec_append' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```

Agrees with the dossier's recorded result (`code-layer1.md` I.6): the identity is proved on the
kernel's three axioms and the three guards hold. The two warnings are Lean 4.34.1's
deprecations of `if_true`/`if_neg` inside the proof. This is also the first run of this probe
through `lake env lean` (the old run used the old binary and a hand-made `LEAN_PATH`).

### 3.3 `OffsetsProbe.v434.lean` (leanVM's `stack_offsets` against `Blocks.offset`/`Blocks.selector`)

Lists of `ℕ` only; copied unchanged (`cp`; empty diff). Output
(`OffsetsProbe.v434.lean.new.out`), 7 s:

```text
exit=0
```

Agrees with the dossier's recorded result (`code-layer1.md` I.2: `exit=0`, no output).

### 3.4 `DuplicatesProbe.v434.lean` (Layer 1 statements that are CompPoly's or each other's)

An arbitrary commutative ring and `ℕ` only; copied unchanged (`cp`; empty diff). Output
(`DuplicatesProbe.v434.lean.new.out`), 3 s:

```text
exit=0
```

Agrees with the dossier's recorded result (`code-layer1.md` I.5: `exit=0`, no output). So at
CompPoly `572f9973` `evalMle_lagrangeBasis` is still CompPoly's `eqTilde_eq_prod` up to the
order of factors (the probe's first `example` names `eqTilde_eq_prod`, `eqTilde` and
`eval_mle_eq_eval` and compiles), and the three in-layer duplicates still follow in one to
three lines. This is also the first run of this probe through `lake env lean`.

## 4. The table sumcheck and the bus seam (`probes/gt-table-pub/`)

Both probes use only the numerals `0` and `1` in `K` and `E` (`X 2` is a variable index) and
import `LeanerVM.Protocol.Spine.{Toy,Seams,Compose}`, which exist at `144c5aa`; copied unchanged
(`cp`; empty diffs). Command: the brief's, no `-D` option (as in `gt-table-pub.md` section 9).

### 4.1 `SeamBusShape.v434.lean` (the degree clause of `Seam.bus`, two points in one claim, no bound on the number of claims)

Output (`SeamBusShape.v434.lean.new.out`), 8 s:

```text
exit=0
```

Agrees with the dossier's recorded result (`gt-table-pub.md` section 9: no error, no output,
`exit=0`), including the `example` that the statement with the true cubic claim is outside
`Seam.bus` (by `decide +kernel` on the degree clause).

### 4.2 `SeamBusMember.v434.lean` (each clause of the seam on `twoPoints`)

Output (`SeamBusMember.v434.lean.new.out`), 4 s:

```text
exit=0
```

Agrees with the dossier's recorded result (`gt-table-pub.md` section 9: `exit=0`).

## 5. The Flock phase (`probes/gt-flock-ring/NoCheckFlock.v434.lean`)

Numerals `1` in `K`, `7` as an index of `Fin 8` (not a `K` numeral); imports
`LeanerVM.Protocol.Spine.{Toy,Compose}`. Copied unchanged (`cp`; empty diff). Command: the
brief's, no `-D` option. Output (`NoCheckFlock.v434.lean.new.out`), 4 s:

```text
'GtFlockRingProbe.noCheckFlockSecurity' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```

Agrees with the dossier's recorded result (`gt-flock-ring.md` 9.1): the do-nothing Flock phase
has `Phase.Security toy noCheckFlock (Seam.pub toy) (Seam.flock toy)` on the kernel's three
axioms, and part (2) (the reflection hypothesis fails on `toyAux`) compiles.

## 6. Library facts (`probes/lib-others/`)

Command: the brief's, no `-D` option (as in `lib-others.md` H). Outputs of the old runs are in
`<File>.out`; the old runs appended timing lines, these do not.

### 6.1 `FieldFidelity` (leanerVM's `K`, `E` against the Rust's reference vectors; numerals; instance leakage)

**(a) Adapted copy** (`FieldFidelity.v434.lean`). Every hexadecimal or decimal word in `K` (the
three base-field vectors, the reduction constant, the XOR check, the inverse check, the
forty-eight limbs of the extension vectors and the mutated limb, the generator's `2` and `4`,
and the numerals of the "bit patterns" section) was rewritten as `K.ofBits n`. The XOR check,
which at the old pin used `^^^` on `K = BitVec 64`, is written with `^^^` on the natural
numbers inside `K.ofBits` (the same 64-bit word, both operands being below `2^64`). The
`#check (2 : K)`, the `BitVec 64` section and the `#synth` lines are unchanged: they show how a
numeral and `BitVec 64` elaborate now. Diff:

```diff
@@ -11,37 +11,38 @@
 
 /-! ## Base field: the three `(a, b, a·b)` vectors of `gf2_64.rs:271-275` -/
 
-#guard (0x01090913877ed8ed : K) * 0x66ab35ac2768468f = 0x50c4519dc383744a
-#guard (0xa7715ae18f12a3b5 : K) * 0x05743059f43fa4f5 = 0xeb64cd9cd9cda6df
-#guard (0xbd3efb4705e79ddd : K) * 0x3aff618604de4ae0 = 0xc3d7a95fa9cb59bb
+#guard K.ofBits 0x01090913877ed8ed * K.ofBits 0x66ab35ac2768468f = K.ofBits 0x50c4519dc383744a
+#guard K.ofBits 0xa7715ae18f12a3b5 * K.ofBits 0x05743059f43fa4f5 = K.ofBits 0xeb64cd9cd9cda6df
+#guard K.ofBits 0xbd3efb4705e79ddd * K.ofBits 0x3aff618604de4ae0 = K.ofBits 0xc3d7a95fa9cb59bb
 -- a mutated product is rejected
-#guard (0x01090913877ed8ed : K) * 0x66ab35ac2768468f ≠ 0x50c4519dc383744b
+#guard K.ofBits 0x01090913877ed8ed * K.ofBits 0x66ab35ac2768468f ≠ K.ofBits 0x50c4519dc383744b
 -- the reduction constant: x^63 · x = x^64 = x^4 + x^3 + x + 1 = 0x1B
-#guard (0x8000000000000000 : K) * 0x2 = 0x1B
+#guard K.ofBits 0x8000000000000000 * K.ofBits 0x2 = K.ofBits 0x1B
 -- addition is XOR
-#guard (0x01090913877ed8ed : K) + 0x66ab35ac2768468f = 0x01090913877ed8ed ^^^ 0x66ab35ac2768468f
+#guard K.ofBits 0x01090913877ed8ed + K.ofBits 0x66ab35ac2768468f =
+  K.ofBits (0x01090913877ed8ed ^^^ 0x66ab35ac2768468f)
 -- inversion, and `0⁻¹ = 0` as in the Rust (`gf2_64.rs:42`, `:318`)
-#guard (0x01090913877ed8ed : K) * (0x01090913877ed8ed : K)⁻¹ = 1
+#guard K.ofBits 0x01090913877ed8ed * (K.ofBits 0x01090913877ed8ed)⁻¹ = 1
 #guard (0 : K)⁻¹ = 0
 
 /-! ## Extension: the four `(a, b, a·b, a·a)` vectors of `gf2_64x3.rs:991-1016` -/
 
-def a1 : E := E.ofLimbs 0x950e87d7f5606615 0x2c61275c9e6b6cf8 0x1f00bca0042db923
-def b1 : E := E.ofLimbs 0x6dbca290a9eab706 0x4c10a4fe30cffdda 0xf26fff4cc4fd394d
-def c1 : E := E.ofLimbs 0x888a0fc35abaf5f6 0x68a84cbc132b0649 0x9fdeaf613003cabe
-def s1 : E := E.ofLimbs 0x8fba131ad5d46b8c 0x1c170457f537a805 0x3632cc098ca15135
-def a2 : E := E.ofLimbs 0x6814a2bc786a6d2d 0xa26b351e6c8042c5 0x54760e7fbc051c6c
-def b2 : E := E.ofLimbs 0xd4c08880a5a4666d 0x29610ae0eed8f1e7 0xc34bd8e2fe5213e5
-def c2 : E := E.ofLimbs 0x2ad322ebf2f9043b 0x8ac800aa67154c80 0x6d0f76651d3c4d0c
-def s2 : E := E.ofLimbs 0xcf800ef2b83bb43a 0xefe1c6cd064dd44c 0x57dc5c7a60e2981b
-def a3 : E := E.ofLimbs 0x6c50afb6e9fb123d 0x6f28d015a2aa0b9d 0x4e385994ebac94af
-def b3 : E := E.ofLimbs 0x194f9545adba52ce 0xc675ce05588f882f 0x57de8c051d4b7ef2
-def c3 : E := E.ofLimbs 0xea6b9f9d23d4a1ff 0xd82aa6058c431457 0x5fd4d8fda2f1e74a
-def s3 : E := E.ofLimbs 0x8f30fe43aa05b396 0xe3593591eccd9efe 0x7c5a1b128788c51f
-def a4 : E := E.ofLimbs 0xd998efd82733e933 0x6df216c33f8f3201 0x11dc6f3fcb57d5d8
-def b4 : E := E.ofLimbs 0x8860a84722025e05 0x33176469aa6ef630 0x607507ebc5b864d7
-def c4 : E := E.ofLimbs 0xfa3a0d66cdfbc1b3 0xbd47bd3343aad307 0xdaf50186477f6a77
-def s4 : E := E.ofLimbs 0x69c8d8c24f416884 0x4b597d648a162147 0x95603a5d95c9512a
+def a1 : E := E.ofLimbs (K.ofBits 0x950e87d7f5606615) (K.ofBits 0x2c61275c9e6b6cf8) (K.ofBits 0x1f00bca0042db923)
+def b1 : E := E.ofLimbs (K.ofBits 0x6dbca290a9eab706) (K.ofBits 0x4c10a4fe30cffdda) (K.ofBits 0xf26fff4cc4fd394d)
+def c1 : E := E.ofLimbs (K.ofBits 0x888a0fc35abaf5f6) (K.ofBits 0x68a84cbc132b0649) (K.ofBits 0x9fdeaf613003cabe)
+def s1 : E := E.ofLimbs (K.ofBits 0x8fba131ad5d46b8c) (K.ofBits 0x1c170457f537a805) (K.ofBits 0x3632cc098ca15135)
+def a2 : E := E.ofLimbs (K.ofBits 0x6814a2bc786a6d2d) (K.ofBits 0xa26b351e6c8042c5) (K.ofBits 0x54760e7fbc051c6c)
+def b2 : E := E.ofLimbs (K.ofBits 0xd4c08880a5a4666d) (K.ofBits 0x29610ae0eed8f1e7) (K.ofBits 0xc34bd8e2fe5213e5)
+def c2 : E := E.ofLimbs (K.ofBits 0x2ad322ebf2f9043b) (K.ofBits 0x8ac800aa67154c80) (K.ofBits 0x6d0f76651d3c4d0c)
+def s2 : E := E.ofLimbs (K.ofBits 0xcf800ef2b83bb43a) (K.ofBits 0xefe1c6cd064dd44c) (K.ofBits 0x57dc5c7a60e2981b)
+def a3 : E := E.ofLimbs (K.ofBits 0x6c50afb6e9fb123d) (K.ofBits 0x6f28d015a2aa0b9d) (K.ofBits 0x4e385994ebac94af)
+def b3 : E := E.ofLimbs (K.ofBits 0x194f9545adba52ce) (K.ofBits 0xc675ce05588f882f) (K.ofBits 0x57de8c051d4b7ef2)
+def c3 : E := E.ofLimbs (K.ofBits 0xea6b9f9d23d4a1ff) (K.ofBits 0xd82aa6058c431457) (K.ofBits 0x5fd4d8fda2f1e74a)
+def s3 : E := E.ofLimbs (K.ofBits 0x8f30fe43aa05b396) (K.ofBits 0xe3593591eccd9efe) (K.ofBits 0x7c5a1b128788c51f)
+def a4 : E := E.ofLimbs (K.ofBits 0xd998efd82733e933) (K.ofBits 0x6df216c33f8f3201) (K.ofBits 0x11dc6f3fcb57d5d8)
+def b4 : E := E.ofLimbs (K.ofBits 0x8860a84722025e05) (K.ofBits 0x33176469aa6ef630) (K.ofBits 0x607507ebc5b864d7)
+def c4 : E := E.ofLimbs (K.ofBits 0xfa3a0d66cdfbc1b3) (K.ofBits 0xbd47bd3343aad307) (K.ofBits 0xdaf50186477f6a77)
+def s4 : E := E.ofLimbs (K.ofBits 0x69c8d8c24f416884) (K.ofBits 0x4b597d648a162147) (K.ofBits 0x95603a5d95c9512a)
 
 #guard a1 * b1 = c1
 #guard a1 * a1 = s1
@@ -52,7 +53,7 @@
 #guard a4 * b4 = c4
 #guard a4 * a4 = s4
 -- a mutated limb is rejected
-def c1' : E := E.ofLimbs 0x888a0fc35abaf5f6 0x68a84cbc132b0649 0x9fdeaf613003cabf
+def c1' : E := E.ofLimbs (K.ofBits 0x888a0fc35abaf5f6) (K.ofBits 0x68a84cbc132b0649) (K.ofBits 0x9fdeaf613003cabf)
 #guard a1 * b1 ≠ c1'
 -- the defining relation, as the Rust checks it (`gf2_64x3.rs:1026`)
 #guard y * y * y = y + 1
@@ -64,18 +65,18 @@
 
 /-! ## The generator -/
 
-#guard g = (2 : K)
-#guard g * g = (4 : K)
+#guard g = K.ofBits 2
+#guard g * g = K.ofBits 4
 
 /-! ## Numerals of `K` are bit patterns, not casts of natural numbers -/
 
 -- the numeral `2 : K` is the element `x`, and is not zero
-#guard (2 : K) ≠ 0
+#guard K.ofBits 2 ≠ 0
 -- whereas the cast of the natural number two is zero (characteristic two)
 #guard ((2 : ℕ) : K) = 0
 #guard (1 : K) + 1 = 0
-#guard (2 : K) ≠ ((2 : ℕ) : K)
-#guard (3 : K) = (2 : K) + 1
+#guard K.ofBits 2 ≠ ((2 : ℕ) : K)
+#guard K.ofBits 3 = K.ofBits 2 + 1
 -- the numeral elaborates through `BitVec`'s instance
 set_option pp.explicit true in
 #check (2 : K)
```

(The first attempt wrote `K.ofBits 0x01090913877ed8ed⁻¹`, which parses as an inverse of a
natural number; it was corrected to `(K.ofBits 0x01090913877ed8ed)⁻¹` before the run recorded
here.) Output (`FieldFidelity.v434.lean.new.out`), 5 s:

```text
@OfNat.ofNat K (nat_lit 2) (@instOfNatAtLeastTwo K (nat_lit 2) BF64.instNatCast ⋯) : K
8#64
(true, false)
15#64
@HAdd.hAdd (BitVec (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
  (BitVec (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
  (BitVec (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
  (@instHAdd (BitVec (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
    (@BitVec.instAdd (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))))
  u v : BitVec (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))
8#32
BitVec.instAdd
BitVec.instMul
BitVec.instAdd
.claude/reports/blueprint-review/probes/lib-others/FieldFidelity.v434.lean:102:0: error: failed to synthesize
  Fintype (BitVec 64)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
BF64.instLawfulBEq
CompPoly.Extension.Ext.instLawfulBEq
exit=1
```

**The eleven reference products still agree.** No `#guard` of the file fails: the three
base-field products of `gf2_64.rs:271-275`, the four products and four squares of
`gf2_64x3.rs:991-1016` (eleven reference products in all), the mutated product and the mutated
limb rejected, `x^63·x = 0x1B`, addition is XOR, `a·a⁻¹ = 1` in `K` and `E`, `0⁻¹ = 0`,
`y³ = y + 1`, `y` is the limb vector `(0, 1, 0)`, `g = K.ofBits 2`, `g·g = K.ofBits 4`, and the
words `K.ofBits 2 ≠ 0`, `K.ofBits 2 ≠ ((2 : ℕ) : K)`, `K.ofBits 3 = K.ofBits 2 + 1`.

**Differs from the recorded result, in the parts about instances** (`lib-others.md` H.2 and
B.3; the old output is `FieldFidelity.out`), all explained by CompPoly `572f9973` making `K` a
structure:

| Line | Old pin (`FieldFidelity.out`) | New pin (this run) |
| --- | --- | --- |
| `#check (2 : K)` | `@OfNat.ofNat K 2 (@BitVec.instOfNat 64 2)`: a `BitVec` literal | `@OfNat.ofNat K 2 (@instOfNatAtLeastTwo K 2 BF64.instNatCast ⋯)`: the characteristic-two cast |
| `#eval u + v` on `BitVec 64` | `6#64` (CompPoly's XOR leaked onto `BitVec 64`) | `8#64` (core's addition) |
| `#eval (u + v == 8, u + v == 6)` | `(false, true)` | `(true, false)` |
| `#eval u * v` | `15#64` | `15#64` |
| `#check u + v` | `BF64.instAdd` | `BitVec.instAdd` |
| `#synth Add (BitVec 64)`, `Mul (BitVec 64)` | `BF64.instAdd`, `BF64.instMul` | `BitVec.instAdd`, `BitVec.instMul` |
| `#synth Fintype (BitVec 64)` | `BF64.instFintype` | **error**: `failed to synthesize Fintype (BitVec 64)` (line 102) |
| `#synth LawfulBEq K` | `instLawfulBEq` | `BF64.instLawfulBEq` |
| `#synth LawfulBEq E` | **error** (line 103, a deliberate check: `E` had none) | `CompPoly.Extension.Ext.instLawfulBEq`: **`E` now has one** |

So at the new pins the instance leakage onto `BitVec 64` that `lib-others.md` records is gone,
and `LawfulBEq E`, which that dossier records as absent "at the pin", exists (both statements of
the dossier were about the old pin and stand there). The one error of this run is the
`#synth Fintype (BitVec 64)` line, which at the new pin has no leaked instance to find.

**(b) The unchanged copy, as a control** (`FieldFidelity.unchanged.v434.lean`, `cp`; empty
diff), to check the dossier's prediction (`lib-others.md` G, "the probe `FieldFidelity` at the
new pin would read `(0x01090913877ed8ed : K) * 0x66ab35ac2768468f = 0x50c4519dc383744a` as
`1 * 1 = 0` … and fail; its `#guard (2 : K) ≠ 0` would fail, `#guard ((2 : ℕ) : K) = 0` would
pass, `g = (2 : K)` would fail"). Output (`FieldFidelity.unchanged.v434.lean.new.out`), 6 s:

```text
.claude/reports/blueprint-review/probes/lib-others/FieldFidelity.unchanged.v434.lean:14:0: error: Expression
  decide (74600848310589677 * 7398065826397963919 = 5819866356501410890)
did not evaluate to `true`
.claude/reports/blueprint-review/probes/lib-others/FieldFidelity.unchanged.v434.lean:16:0: error: Expression
  decide (13636613004184755677 * 4251223801496226528 = 14111934185724402107)
did not evaluate to `true`
.claude/reports/blueprint-review/probes/lib-others/FieldFidelity.unchanged.v434.lean:18:0: error: Expression
  decide (74600848310589677 * 7398065826397963919 ≠ 5819866356501410891)
did not evaluate to `true`
.claude/reports/blueprint-review/probes/lib-others/FieldFidelity.unchanged.v434.lean:20:0: error: Expression
  decide (9223372036854775808 * 2 = 27)
did not evaluate to `true`
.claude/reports/blueprint-review/probes/lib-others/FieldFidelity.unchanged.v434.lean:22:55: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  HXor ℕ ℕ K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
.claude/reports/blueprint-review/probes/lib-others/FieldFidelity.unchanged.v434.lean:47:0: error: Expression
  decide (a1 * a1 = s1)
did not evaluate to `true`
.claude/reports/blueprint-review/probes/lib-others/FieldFidelity.unchanged.v434.lean:48:0: error: Expression
  decide (a2 * b2 = c2)
did not evaluate to `true`
.claude/reports/blueprint-review/probes/lib-others/FieldFidelity.unchanged.v434.lean:49:0: error: Expression
  decide (a2 * a2 = s2)
did not evaluate to `true`
.claude/reports/blueprint-review/probes/lib-others/FieldFidelity.unchanged.v434.lean:50:0: error: Expression
  decide (a3 * b3 = c3)
did not evaluate to `true`
.claude/reports/blueprint-review/probes/lib-others/FieldFidelity.unchanged.v434.lean:51:0: error: Expression
  decide (a3 * a3 = s3)
did not evaluate to `true`
.claude/reports/blueprint-review/probes/lib-others/FieldFidelity.unchanged.v434.lean:52:0: error: Expression
  decide (a4 * b4 = c4)
did not evaluate to `true`
.claude/reports/blueprint-review/probes/lib-others/FieldFidelity.unchanged.v434.lean:53:0: error: Expression
  decide (a4 * a4 = s4)
did not evaluate to `true`
.claude/reports/blueprint-review/probes/lib-others/FieldFidelity.unchanged.v434.lean:67:0: error: Expression
  decide (g = 2)
did not evaluate to `true`
.claude/reports/blueprint-review/probes/lib-others/FieldFidelity.unchanged.v434.lean:68:0: error: Expression
  decide (g * g = 4)
did not evaluate to `true`
.claude/reports/blueprint-review/probes/lib-others/FieldFidelity.unchanged.v434.lean:73:0: error: Expression
  decide (2 ≠ 0)
did not evaluate to `true`
.claude/reports/blueprint-review/probes/lib-others/FieldFidelity.unchanged.v434.lean:77:0: error: Expression
  decide (2 ≠ ↑2)
did not evaluate to `true`
@OfNat.ofNat K (nat_lit 2) (@instOfNatAtLeastTwo K (nat_lit 2) BF64.instNatCast ⋯) : K
8#64
(true, false)
15#64
@HAdd.hAdd (BitVec (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
  (BitVec (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
  (BitVec (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
  (@instHAdd (BitVec (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
    (@BitVec.instAdd (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))))
  u v : BitVec (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))
8#32
BitVec.instAdd
BitVec.instMul
BitVec.instAdd
.claude/reports/blueprint-review/probes/lib-others/FieldFidelity.unchanged.v434.lean:101:0: error: failed to synthesize
  Fintype (BitVec 64)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
BF64.instLawfulBEq
CompPoly.Extension.Ext.instLawfulBEq
exit=1
```

The prediction holds: the first product, `(2 : K) ≠ 0` and `g = (2 : K)` fail, and
`((2 : ℕ) : K) = 0` passes (line 75 is not in the error list). Of the eleven reference
products, nine fail (lines 14, 16, 47-53) and two pass spuriously, as the parity reading
predicts (line 15: odd·odd = odd; line 46, `a1 * b1 = c1`). The mutated-product guard (18), the
reduction constant (20), `g = 2` (67), `g * g = 4` (68), `(2 : K) ≠ 0` (73) and
`(2 : K) ≠ ((2 : ℕ) : K)` (77) fail; the XOR check (22) does not elaborate (`HXor ℕ ℕ K`); the
`#synth Fintype (BitVec 64)` line (101) fails as in (a). `(3 : K) = (2 : K) + 1` (78) passes
(`1 = 0 + 1`).

### 6.2 `SamplerDiamond2.v434.lean` (two samplers on `K`: the same term?)

No numeral; copied unchanged (`cp`; empty diff). Output (`SamplerDiamond2.v434.lean.new.out`),
9 s:

```text
instSampleableTypeK
.claude/reports/blueprint-review/probes/lib-others/SamplerDiamond2.v434.lean:15:40: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  FinEnum K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
.claude/reports/blueprint-review/probes/lib-others/SamplerDiamond2.v434.lean:18:53: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  FinEnum K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
exit=1
```

**Differs from the recorded result** (`lib-others.md`: both `example`s accepted, `exit=0`), for a
reason the upgrade explains: at CompPoly `572f9973` `K` is a structure, not `BitVec 64`, so
Mathlib's `FinEnum (BitVec n)` no longer applies to it, `FinEnum K` has no instance, and VCVio's
`FinEnum.SampleableType K` (the second sampler) cannot be formed. `#synth SampleableType K` still
finds leanerVM's `instSampleableTypeK`. The diamond the dossier examined does not exist at the
new pins; nothing was adapted, since there is no second sampler to compare with. (Not checked
here: whether some other route gives a second `SampleableType K`; `#synth` returns only the one
it finds first.)

### 6.3 `Layer0.unchanged.v434.lean` (Layer 0's instances, signatures, axioms, uniformity, oracle interface)

No numeral other than `0`, `1` and exponents; copied unchanged (`cp`; empty diff). Output
(`Layer0.unchanged.v434.lean.new.out`), 6 s:

```text
instSampleableTypeK
instSampleableTypeE
instSampleableTypeVector K 3
instSampleableTypeFinOfNeZeroNat (2 ^ 64)
instFintypeK
Extension.Ext.instFintype
instDecidableEqK
fun a b => Extension.Ext.instDecidableEq a b
evalOracle 3
instOracleInterfaceE
instOracleInterfaceListE
finEquivK : Fin (2 ^ 64) ≃ K
limbsEquiv : Vector K 3 ≃ E
instSampleableTypeK : SampleableType K
instSampleableTypeE : SampleableType E
card_E : Fintype.card E = 2 ^ 192
evalOracle : (n : ℕ) → OracleInterface (Column n)
evalOracle_answer : ∀ (n : ℕ) (q : Column n) (r : Vector E n),
  OracleInterface.answer q r = q.values.eval₂Mle (algebraMap K E) r
@probEvent_uniformSample_le_of_card_le : ∀ {α : Type} [inst : SampleableType α] [inst_1 : Fintype α] (p : α → Prop)
  [inst_2 : DecidablePred p] {k : ℕ},
  (Finset.filter p Finset.univ).card ≤ k →
    𝒟[do
          let sample ← $ᵗ α
          pure (p sample)]
        {True} ≤
      ↑(↑k / ↑(Fintype.card α))
@probEvent_uniformSample_le_of_subsingleton : ∀ {α : Type} [inst : SampleableType α] [inst_1 : Fintype α]
  (p : α → Prop),
  (∀ (a b : α), p a → p b → a = b) →
    𝒟[do
          let sample ← $ᵗ α
          pure (p sample)]
        {True} ≤
      ↑(1 / ↑(Fintype.card α))
NoOracle : Fin 0 → Type
OneOracle : Type → Fin 1 → Type
noOracle_eq : ∀ (o o' : (i : Fin 0) → NoOracle i), o = o'
class SampleableType (β : Type) : Type
number of parameters: 1
fields:
  SampleableType.selectElem : ProbComp β
  SampleableType.evalDist_selectElem_eq_uniform : ∀ [inst : MeasurableSpace β] [MeasurableSingletonClass β],
      𝒟[SampleableType.selectElem] = ProbabilityTheory.uniformOn Set.univ
constructor:
  SampleableType.mk {β : Type} (selectElem : ProbComp β)
    (evalDist_selectElem_eq_uniform :
      ∀ [inst : MeasurableSpace β] [MeasurableSingletonClass β], 𝒟[selectElem] = ProbabilityTheory.uniformOn Set.univ) :
    SampleableType β
@[instance_reducible] def LeanerVM.Protocol.evalOracle : (n : ℕ) → OracleInterface (Column n) :=
fun n =>
  { Query := Vector E n,
    toOC :=
      { spec := OracleSpec.ofFn fun x => E,
        impl := fun r => do
          let __do_lift ← read
          pure (__do_lift.values.eval₂Mle (algebraMap K E) r) } }
@[instance_reducible] def LeanerVM.Protocol.instSampleableTypeK : SampleableType K :=
SampleableType.ofEquiv finEquivK
@[instance_reducible] def LeanerVM.Protocol.instSampleableTypeE : SampleableType E :=
SampleableType.ofEquiv limbsEquiv
'LeanerVM.Protocol.finEquivK' depends on axioms: [propext]
'LeanerVM.Protocol.limbsEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.instSampleableTypeK' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.instSampleableTypeE' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.card_E' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.evalOracle' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.evalOracle_answer' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.instOracleInterfaceE' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.instOracleInterfaceListE' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.probEvent_uniformSample_le_of_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.probEvent_uniformSample_le_of_subsingleton' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LeanerVM.Protocol.noOracle_eq' depends on axioms: [Quot.sound]
'BF64.card_ext3' depends on axioms: [propext, Classical.choice, Quot.sound]
'BF64.card_bf64' depends on axioms: [propext, Classical.choice, Quot.sound]
'BF64.basePoly_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound]
'BF64.ext3Poly_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound]
'BF64.instField' depends on axioms: [propext, Classical.choice, Quot.sound]
'SampleableType.ofEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'probOutput_uniformSample' depends on axioms: [propext, Classical.choice, Quot.sound]
'probEvent_uniformSample' depends on axioms: [propext, Classical.choice, Quot.sound]
'CompPoly.CMlPolynomialEval.eval_mle_eq_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'CompPoly.CMlPolynomialEval.eval₂_mle_eq_eval₂' depends on axioms: [propext, Classical.choice, Quot.sound]
.claude/reports/blueprint-review/probes/lib-others/Layer0.unchanged.v434.lean:78:18: warning: `probOutput` has been deprecated: VCVio retiring probability API: use `𝒟[mx] {x}`
.claude/reports/blueprint-review/probes/lib-others/Layer0.unchanged.v434.lean:80:18: warning: `probOutput` has been deprecated: VCVio retiring probability API: use `𝒟[mx] {x}`
.claude/reports/blueprint-review/probes/lib-others/Layer0.unchanged.v434.lean:82:18: warning: `probOutput` has been deprecated: VCVio retiring probability API: use `𝒟[mx] {x}`
.claude/reports/blueprint-review/probes/lib-others/Layer0.unchanged.v434.lean:85:10: warning: `probFailure` has been deprecated: VCVio retiring probability API: use `1 - 𝒟[mx] Set.univ`
exit=0
```

**Agrees** with the dossier's recorded result (`lib-others.md` H.1: `exit=0`) in everything a
conclusion rests on: the same instances are found for `SampleableType K`, `SampleableType E`,
`SampleableType (Vector K 3)`, `SampleableType (Fin (2 ^ 64))`, `Fintype E`, `DecidableEq E` and
the three oracle interfaces; the same axioms for every declaration listed (the kernel's three,
`[propext]` for `finEquivK`, `[Quot.sound]` for `noOracle_eq`); every `example` of sections 4
and 5 compiles (uniformity of both samplers, `|E| = 2^192`, no failure, full support, the
samplers as images of the equivalences by `rfl`, the column's oracle interface, `ofK` is
`algebraMap K E`). **Differences in the printed text**, all from the upgrade: `Fintype K` is now
`instFintypeK` (was `BF64.instFintype`) and `DecidableEq K` is `instDecidableEqK` (was
`instDecidableEqBitVec`), both leanerVM's own at `144c5aa` (`LeanerVM/Parameters/Field.lean`);
the two counting bounds are printed in the new form `𝒟[do let sample ← $ᵗ α; pure (p sample)]
{True} ≤ …` (was `probEvent ($ᵗ α) p ≤ …`), the same bounds; VCVio's class `SampleableType` now
has the fields `selectElem` and `evalDist_selectElem_eq_uniform` (the sampler's distribution is
the uniform measure) instead of `mem_support_selectElem` and `probOutput_selectElem_eq`; and four
deprecation warnings for `Pr[= x | …]` and `Pr[⊥ | …]`.

## 7. ArkLib's definitions (`probes/lib-arklib/`)

Command: the brief's, no `-D` option (as in `lib-arklib.md`'s appendix). No probe of this
directory uses a numeral in `K`; the adaptations are to VCVio's new probability API only.

### 7.1 `NonVacuity` (non-vacuity of round-by-round knowledge soundness)

**(a) Unchanged copy** (`NonVacuity.unchanged.v434.lean`; it was first run as
`NonVacuity.v434.lean` and renamed with its output afterwards, so the paths inside the output
name the earlier file name; empty diff against the old file). Output
(`NonVacuity.unchanged.v434.lean.new.out`), 54 s (including the wait for the lock):

```text
.claude/reports/blueprint-review/probes/lib-arklib/NonVacuity.v434.lean:33:14: warning: `probEvent` has been deprecated: VCVio retiring probability API: use `𝒟[mx] {x | p x}`
.claude/reports/blueprint-review/probes/lib-arklib/NonVacuity.v434.lean:38:37: error: Application type mismatch: The argument
  Eq.symm h1
has type
  1 =
    𝒟[do
        let stmtOut ←
          OptionT.mk do
              let __do_lift ← init
              (simulateQ impl (Verifier.run false default acceptAll0)).run' __do_lift
        pure (stmtOut ∈ {t | (t, ()) ∈ relOut})]
      {True}
but is expected to have type
  1 =
    probEvent
      (OptionT.mk do
        let __do_lift ← init
        (simulateQ impl (Verifier.run false default acceptAll0)).run' __do_lift)
      fun t => (t, ()) ∈ relOut
in the application
  lt_of_lt_of_eq zero_lt_one (Eq.symm h1)
.claude/reports/blueprint-review/probes/lib-arklib/NonVacuity.v434.lean:39:46: error: Application type mismatch: The argument
  hacc
has type
  (probEvent
      (OptionT.mk do
        let __do_lift ← init
        (simulateQ impl (Verifier.run false default acceptAll0)).run' __do_lift)
      fun t => (t, ()) ∈ relOut) >
    0
but is expected to have type
  𝒟[do
        let stmtOut ←
          OptionT.mk do
              let __do_lift ← init
              (simulateQ impl (Verifier.run false default acceptAll0)).run' __do_lift
        pure ((stmtOut, ()) ∈ relOut)]
      {True} >
    0
in the application
  K.toFun_full false default () hacc
.claude/reports/blueprint-review/probes/lib-arklib/NonVacuity.v434.lean:75:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  probEvent ?m.60 ?m.61 = 0
in the target expression
  𝒟[do
        let challenge ← $ᵗ pSpec1.Challenge ⟨0, ⋯⟩
        pure
            (∃ witMid,
              ¬K.toFun (Fin.castSucc 0) false default
                    (E.extractMid 0 false (Transcript.concat challenge default) witMid) ∧
                K.toFun (Fin.succ 0) false (Transcript.concat challenge default) witMid)]
      {True} =
    0

ι : Type
oSpec : OracleSpec ι
σ : Type
init : ProbComp σ
impl : QueryImpl oSpec (StateT σ ProbComp)
W : Fin 2 → Type
E : Extractor.RoundByRound oSpec Bool Unit Unit pSpec1 W
K : Verifier.KnowledgeStateFunction init impl relIn relOut acceptAll1 E
h : Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut acceptAll1 W E K fun x => 0
h0 :
  𝒟[do
        let challenge ← $ᵗ pSpec1.Challenge ⟨0, ⋯⟩
        pure
            (∃ witMid,
              ¬K.toFun (Fin.castSucc 0) false default
                    (E.extractMid 0 false (Transcript.concat challenge default) witMid) ∧
                K.toFun (Fin.succ 0) false (Transcript.concat challenge default) witMid)]
      {True} =
    0
⊢ False
.claude/reports/blueprint-review/probes/lib-arklib/NonVacuity.v434.lean:134:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  probEvent ?m.35 ?m.36 = 0
in the target expression
  𝒟[do
        let challenge ← $ᵗ pSpec1.Challenge i
        pure
            (∃ witMid,
              ¬(checkBit_stateFunction init impl).toFun (↑i).castSucc s tr
                    (acceptAll1_extractor.extractMid (↑i) s (Transcript.concat challenge tr) witMid) ∧
                (checkBit_stateFunction init impl).toFun (↑i).succ s (Transcript.concat challenge tr) witMid)]
      {True} =
    0

ι : Type
oSpec : OracleSpec ι
σ : Type
init : ProbComp σ
impl : QueryImpl oSpec (StateT σ ProbComp)
s : Bool
i : pSpec1.ChallengeIdx
tr : Transcript (↑i).castSucc pSpec1
⊢ 𝒟[do
        let challenge ← $ᵗ pSpec1.Challenge i
        pure
            (∃ witMid,
              ¬(checkBit_stateFunction init impl).toFun (↑i).castSucc s tr
                    (acceptAll1_extractor.extractMid (↑i) s (Transcript.concat challenge tr) witMid) ∧
                (checkBit_stateFunction init impl).toFun (↑i).succ s (Transcript.concat challenge tr) witMid)]
      {True} =
    0
.claude/reports/blueprint-review/probes/lib-arklib/NonVacuity.v434.lean:163:15: warning: `probEvent` has been deprecated: VCVio retiring probability API: use `𝒟[mx] {x | p x}`
.claude/reports/blueprint-review/probes/lib-arklib/NonVacuity.v434.lean:171:37: error: Application type mismatch: The argument
  Eq.symm h1
has type
  1 =
    𝒟[do
        let stmtOut ←
          OptionT.mk do
              let __do_lift ← init
              (simulateQ impl (Verifier.run s tr V)).run' __do_lift
        pure (stmtOut ∈ {t | (t, w) ∈ Set.univ})]
      {True}
but is expected to have type
  1 =
    probEvent
      (OptionT.mk do
        let __do_lift ← init
        (simulateQ impl (Verifier.run s tr V)).run' __do_lift)
      fun t => (t, w) ∈ Set.univ
in the application
  lt_of_lt_of_eq zero_lt_one (Eq.symm h1)
.claude/reports/blueprint-review/probes/lib-arklib/NonVacuity.v434.lean:174:82: error: Application type mismatch: The argument
  hp
has type
  (probEvent
      (OptionT.mk do
        let __do_lift ← init
        (simulateQ impl (Verifier.run s tr V)).run' __do_lift)
      fun t => (t, w) ∈ Set.univ) >
    0
but is expected to have type
  𝒟[do
        let sample ←
          OptionT.mk do
              let __do_lift ← init
              (simulateQ impl (Verifier.run s tr V)).run' __do_lift
        pure (?m.185 sample)]
      {True} >
    0
in the application
  LeanerVM.Protocol.Verifier.GuardedForm.of_probEvent_pos G init impl s tr ?m.185 hp
'Probe.acceptAll0_no_stateFunction' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Probe.acceptAll1_not_sound_at_zero' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Probe.acceptAll1_sound_at_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Probe.checkBit_sound_at_zero' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Probe.full_iff_of_univ' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
exit=1
```

Every error is the old `Pr[P | c]` (VCVio's deprecated `probEvent`) meeting ArkLib `7653a901`'s
`Pr{…}[…]` statements, or the lemma `probEvent_eq_zero_iff` no longer matching them.

**(b) Adapted copy** (`NonVacuity.v434.lean`): the two events restated in the `Pr{…}[…]` form and
`probEvent_eq_zero_iff` replaced by `OracleComp.prEvent_eq_zero_iff`
(`VCVio/OracleComp/EvalDist/Measure.lean:370` at `a4232d08`: `Pr{let x ← mx}[p x] = 0 ↔ ∀ x ∈
support mx, ¬ p x`). ArkLib's `Verifier.guarded_accepting_of_mem`, which the probe uses, is now
stated in that form (`ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Guarded.lean:258-268`
at `7653a901`). Diff:

```diff
@@ -30,8 +30,9 @@
     (E : Extractor.RoundByRound oSpec Bool Unit Unit !p[] W) :
     IsEmpty ((acceptAll0 (oSpec := oSpec)).KnowledgeStateFunction init impl relIn relOut E) := by
   refine ⟨fun K => ?_⟩
-  have hacc : Pr[fun t => (t, ()) ∈ relOut | OptionT.mk do
-      (simulateQ impl ((acceptAll0 (oSpec := oSpec)).run false default)).run' (← init)] > 0 := by
+  have hacc : Pr{let t ← OptionT.mk do
+      (simulateQ impl ((acceptAll0 (oSpec := oSpec)).run false default)).run' (← init)}[
+        (t, ()) ∈ relOut] > 0 := by
     have h1 := Verifier.guarded_accepting_of_mem init impl (acceptAll0 (oSpec := oSpec))
       (fun _ _ => true) (fun _ _ => ()) (fun _ _ => by simp [acceptAll0]) false default rfl
       {t | (t, ()) ∈ relOut} (by simp [relOut])
@@ -72,7 +73,7 @@
   intro h
   have h0 := h false ⟨0, rfl⟩ (show Transcript (0 : Fin 2) pSpec1 from default)
   simp only [ENNReal.coe_zero, nonpos_iff_eq_zero] at h0
-  rw [probEvent_eq_zero_iff] at h0
+  rw [OracleComp.prEvent_eq_zero_iff] at h0
   refine h0 true (by rw [support_uniformSample]; trivial) ?_
   refine ⟨E.extractOut false _ (), ?_, acceptAll1_full init impl K false _⟩
   intro hk
@@ -131,7 +132,7 @@
       (fun _ => Unit) acceptAll1_extractor (checkBit_stateFunction init impl) (fun _ => 0) := by
   intro s i tr
   simp only [ENNReal.coe_zero, nonpos_iff_eq_zero]
-  rw [probEvent_eq_zero_iff]
+  rw [OracleComp.prEvent_eq_zero_iff]
   rintro c - ⟨w, h1, h2⟩
   exact h1 h2
 
@@ -160,8 +161,9 @@
     [∀ i, SampleableType (p.Challenge i)] {V : Verifier oSpec S T p} (G : V.GuardedForm) {W : Fin (n + 1) → Type}
     {E : Extractor.RoundByRound oSpec S WI WO p W}
     (F : S → p.FullTranscript → W (Fin.last n) → Prop) :
-    (∀ s tr w, Pr[fun t => (t, w) ∈ (Set.univ : Set (T × WO)) | OptionT.mk do
-        (simulateQ impl (V.run s tr)).run' (← init)] > 0 → F s tr (E.extractOut s tr w)) ↔
+    (∀ s tr w, Pr{let t ← OptionT.mk do
+        (simulateQ impl (V.run s tr)).run' (← init)}[(t, w) ∈ (Set.univ : Set (T × WO))] > 0 →
+        F s tr (E.extractOut s tr w)) ↔
       ∀ s tr w, G.check s tr = true → F s tr (E.extractOut s tr w) := by
   constructor
   · intro h s tr w hc
```

Output (`NonVacuity.v434.lean.new.out`), 11 s:

```text
'Probe.acceptAll0_no_stateFunction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Probe.acceptAll1_not_sound_at_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Probe.acceptAll1_sound_at_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Probe.checkBit_sound_at_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Probe.full_iff_of_univ' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```

Agrees with the dossier's recorded result (`NonVacuity.out`, line for line): at the new pins, the
accept-everything verifier with no round has no knowledge state function; with one challenge it
is not round-by-round knowledge sound at error `0` for any extractor and state function, and is
at error `1`; the verifier that checks the bit is at error `0`; and the last law of a knowledge
state function of a guarded verifier, with the output relation everything, says exactly "if the
check passes, the state holds at the extracted witness". All on the kernel's three axioms.

### 7.2 `Extractors.v434.lean` (what makes an extractor an algorithm; leanerVM's three extractors)

Copied unchanged (`cp`; empty diff): its only event is consumed through the repository's
`Verifier.GuardedForm.of_probEvent_pos`, which was restated at `144c5aa`. Output
(`Extractors.v434.lean.new.out`), 5 s:

```text
true
true
PUnit.unit
'Probe.chooser_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```

Agrees with the dossier's recorded result (`Extractors.out`, line for line): ArkLib's extractor
type still accepts a classical choice of witness (`chooser_sound`, error `0`, three axioms);
leanerVM's commit, public-input and composed extractors are compiled definitions (the `def`s
without `noncomputable` are accepted), and the commit extractor returns the stack that was sent.

### 7.3 `PlainReading` (the transcript-level reading of round-by-round knowledge soundness)

**(a) Unchanged copy** (`PlainReading.unchanged.v434.lean`, `cp`; empty diff). Output
(`PlainReading.unchanged.v434.lean.new.out`), 5 s:

```text
.claude/reports/blueprint-review/probes/lib-arklib/PlainReading.unchanged.v434.lean:44:17: warning: `probEvent` has been deprecated: VCVio retiring probability API: use `𝒟[mx] {x | p x}`
.claude/reports/blueprint-review/probes/lib-arklib/PlainReading.unchanged.v434.lean:45:2: error: Type mismatch
  Iff.rfl
has type
  ?m.65 ↔ ?m.65
but is expected to have type
  Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut V W E K ε ↔
    ∀ (s : StmtIn) (j : pSpec.ChallengeIdx) (pre : Transcript (↑j).castSucc pSpec),
      (probEvent ($ᵗ pSpec.Challenge j) fun c => c ∈ badSet K s j pre) ≤ ↑(ε j)
.claude/reports/blueprint-review/probes/lib-arklib/PlainReading.unchanged.v434.lean:59:0: warning: automatically included section variable(s) unused in theorem `Probe.state_imp`:
  [(i : pSpec.ChallengeIdx) → SampleableType (pSpec.Challenge i)]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [(i : pSpec.ChallengeIdx) → SampleableType (pSpec.Challenge i)] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
.claude/reports/blueprint-review/probes/lib-arklib/PlainReading.unchanged.v434.lean:95:12: warning: `probEvent` has been deprecated: VCVio retiring probability API: use `𝒟[mx] {x | p x}`
.claude/reports/blueprint-review/probes/lib-arklib/PlainReading.unchanged.v434.lean:99:58: error: Application type mismatch: The argument
  hacc
has type
  (probEvent
      (OptionT.mk do
        let __do_lift ← init
        (simulateQ impl (Verifier.run s tr V)).run' __do_lift)
      fun t => (t, wOut) ∈ relOut) >
    0
but is expected to have type
  𝒟[do
        let stmtOut ←
          OptionT.mk do
              let __do_lift ← init
              (simulateQ impl (Verifier.run s tr V)).run' __do_lift
        pure ((stmtOut, wOut) ∈ relOut)]
      {True} >
    0
in the application
  K.toFun_full s tr wOut hacc
'Probe.accept_imp_extract_or_bad' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Probe.rbr_iff_badSet' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'schwartz_zippel_counting' depends on axioms: [propext, Classical.choice, Quot.sound]
@schwartz_zippel_counting : ∀ {F : Type u_1} [inst : Field F] [inst_1 : DecidableEq F] {s : ℕ}
  (f : MvPolynomial (Fin s) F),
  f ≠ 0 →
    ∀ (S : Fin s → Finset F) (d m : ℕ),
      f.totalDegree ≤ d →
        0 < m →
          (∀ (i : Fin s), m ≤ (S i).card) →
            {x ∈ Fintype.piFinset S | (MvPolynomial.eval x) f = 0}.card * m ≤ d * ∏ i, (S i).card
@prob_eval_zero_le_div : ∀ {F : Type} [inst : Field F] {s : ℕ} {S : Fin s → Set F}
  [inst_1 : (i : Fin s) → Fintype ↑(S i)] [∀ (i : Fin s), Nonempty ↑(S i)]
  [inst_3 : SampleableType ((i : Fin s) → ↑(S i))] (f : MvPolynomial (Fin s) F),
  f ≠ 0 →
    ∀ (d m : ℕ),
      f.totalDegree ≤ d →
        0 < m →
          (∀ (i : Fin s), m ≤ (S i).toFinset.card) →
            𝒟[do
                  let x ← $ᵗ ((i : Fin s) → ↑(S i))
                  pure ((MvPolynomial.eval fun i => ↑(x i)) f = 0)]
                {True} ≤
              ↑d / ↑m
exit=1
```

Both errors are the old event notation against ArkLib `7653a901`'s `Pr{…}[…]`.

**(b) Adapted copy** (`PlainReading.v434.lean`): the two events restated. Diff:

```diff
@@ -41,7 +41,7 @@
 theorem rbr_iff_badSet (K : V.KnowledgeStateFunction init impl relIn relOut E)
     (ε : pSpec.ChallengeIdx → ℝ≥0) :
     V.rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut W E K ε ↔
-      ∀ s j pre, Pr[fun c => c ∈ badSet K s j pre | $ᵗ (pSpec.Challenge j)] ≤ ε j :=
+      ∀ s j pre, Pr{let c ← $ᵗ (pSpec.Challenge j)}[c ∈ badSet K s j pre] ≤ ε j :=
   Iff.rfl
 
 /-- Some verifier round before round `m` of the transcript has its challenge in the bad set of
@@ -92,8 +92,8 @@
 input relation, or some challenge of `tr` is in the bad set of the prefix before it. -/
 theorem accept_imp_extract_or_bad (K : V.KnowledgeStateFunction init impl relIn relOut E)
     (s : StmtIn) (tr : pSpec.FullTranscript) (wOut : WitOut)
-    (hacc : Pr[fun t => (t, wOut) ∈ relOut | OptionT.mk do
-      (simulateQ impl (V.run s tr)).run' (← init)] > 0) :
+    (hacc : Pr{let t ← OptionT.mk do
+      (simulateQ impl (V.run s tr)).run' (← init)}[(t, wOut) ∈ relOut] > 0) :
     (s, toInput E s (Fin.last n) tr (E.extractOut s tr wOut)) ∈ relIn ∨
       badSomewhere K s (Fin.last n) tr :=
   state_imp K s (Fin.last n) tr _ (K.toFun_full s tr wOut hacc)
```

Output (`PlainReading.v434.lean.new.out`), 6 s:

```text
.claude/reports/blueprint-review/probes/lib-arklib/PlainReading.v434.lean:59:0: warning: automatically included section variable(s) unused in theorem `Probe.state_imp`:
  [(i : pSpec.ChallengeIdx) → SampleableType (pSpec.Challenge i)]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [(i : pSpec.ChallengeIdx) → SampleableType (pSpec.Challenge i)] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Probe.accept_imp_extract_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound]
'Probe.rbr_iff_badSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'schwartz_zippel_counting' depends on axioms: [propext, Classical.choice, Quot.sound]
@schwartz_zippel_counting : ∀ {F : Type u_1} [inst : Field F] [inst_1 : DecidableEq F] {s : ℕ}
  (f : MvPolynomial (Fin s) F),
  f ≠ 0 →
    ∀ (S : Fin s → Finset F) (d m : ℕ),
      f.totalDegree ≤ d →
        0 < m →
          (∀ (i : Fin s), m ≤ (S i).card) →
            {x ∈ Fintype.piFinset S | (MvPolynomial.eval x) f = 0}.card * m ≤ d * ∏ i, (S i).card
@prob_eval_zero_le_div : ∀ {F : Type} [inst : Field F] {s : ℕ} {S : Fin s → Set F}
  [inst_1 : (i : Fin s) → Fintype ↑(S i)] [∀ (i : Fin s), Nonempty ↑(S i)]
  [inst_3 : SampleableType ((i : Fin s) → ↑(S i))] (f : MvPolynomial (Fin s) F),
  f ≠ 0 →
    ∀ (d m : ℕ),
      f.totalDegree ≤ d →
        0 < m →
          (∀ (i : Fin s), m ≤ (S i).toFinset.card) →
            𝒟[do
                  let x ← $ᵗ ((i : Fin s) → ↑(S i))
                  pure ((MvPolynomial.eval fun i => ↑(x i)) f = 0)]
                {True} ≤
              ↑d / ↑m
exit=0
```

Agrees with the dossier's recorded result (`PlainReading.out`) in what the conclusions rest on:
`rbr_iff_badSet` still holds by `Iff.rfl` (worst-case round-by-round knowledge soundness is, by
definition, "every bad set has probability at most the error of its round"), and the plain
reading `accept_imp_extract_or_bad` is proved on the kernel's three axioms; the unused-variable
warning is the same. **One printed signature differs:** ArkLib's `prob_eval_zero_le_div` (the
Schwartz–Zippel bound in probability form) now samples with `$ᵗ` under a
`SampleableType ((i : Fin s) → ↑(S i))` hypothesis and states the bound on VCVio's measure `𝒟`,
where at `dca90385` it sampled with `PMF.uniformOfFintype`; `schwartz_zippel_counting` is
unchanged.

### 7.4 `AxiomsLeanerVM.v434.lean` (`#print axioms` of the master theorems, the two built phases and the composition)

Copied unchanged (`cp`; empty diff). Command:
`flock .claude/reports/blueprint-review/logs/lean.lock lake env lean .claude/reports/blueprint-review/probes/lib-arklib/AxiomsLeanerVM.v434.lean > ….new.out 2>&1; echo "exit=$?" >> ….new.out`.
Output, verbatim (`AxiomsLeanerVM.v434.lean.new.out`), 3 s:

```text
'LeanerVM.Protocol.piop_perfectCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.piop_rbrKnowledgeSoundness' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.piop_rbrKnowledgeSoundness_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.commitSecurity' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.commitComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.publicInputSecurity' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.publicInputComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Component.Security.append' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Component.Complete.append' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Verifier.KnowledgeStateFunction.appendGuarded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LeanerVM.Protocol.Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LeanerVM.Protocol.piopExtractor' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.commitExtractor' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.PublicInput.extractor' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Component.sendExtractor' depends on axioms: [propext, Quot.sound]
'LeanerVM.Protocol.Phases.Security.toDef' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.Phases.Complete.toDef' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```

Agrees with the dossier's recorded result: `diff AxiomsLeanerVM.out AxiomsLeanerVM.v434.lean.new.out`
is empty. At `144c5aa` with ArkLib `7653a901`, CompPoly `572f9973`, VCVio `a4232d08`, the two
master theorems, the existential form, both halves of the commit and public-input phases, the
composition lemmas, the four extractors and the two `toDef`s depend on no axiom beyond Lean's
three (`sendExtractor` on two of them); no `sorryAx`.

## 8. Files written by this task

All under `.claude/reports/blueprint-review/`:

- `dossiers/probes-rerun.md` (this file).
- `probes/code-pubinput/tools/v434/` (copies of the mutation scripts, adapted as in 1.1, and
  the new `m0.py`); `probes/code-pubinput/{Probe0Baseline,Probe1NoCheck,Probe2TrustProver,Probe7a,Probe8,ProbeAnyCheck,ProbeWordsLemma}.v434.lean`
  with their `.new.out`.
- `probes/code-spine/{P2Relation,P3aSeams,P5PassThrough,P5PassThrough.unchanged,P4Junk}.v434.lean`
  with their `.new.out`.
- `probes/code-layer1/{ValuesProbe,StridedProbe,OffsetsProbe,DuplicatesProbe}.v434.lean` with
  their `.new.out`.
- `probes/gt-table-pub/{SeamBusShape,SeamBusMember}.v434.lean`,
  `probes/gt-flock-ring/NoCheckFlock.v434.lean`, with their `.new.out`.
- `probes/lib-others/{FieldFidelity,FieldFidelity.unchanged,SamplerDiamond2,Layer0.unchanged}.v434.lean`
  with their `.new.out`.
- `probes/lib-arklib/{NonVacuity,NonVacuity.unchanged,Extractors,PlainReading,PlainReading.unchanged,AxiomsLeanerVM}.v434.lean`
  with their `.new.out`.
- `probes/probes-rerun/RefuteScratch.lean` (the adapted `not_perfectCompleteness`, checked alone,
  1.1) and `probes/probes-rerun/SanityP3a.lean` (two false guards, 2.2); outputs quoted in the
  text, not saved.

No tracked file of any repository was changed; no checkout was moved; nothing was built or
committed.
