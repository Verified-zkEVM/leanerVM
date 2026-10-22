# W-vis: the end theorem with the visible queries `Q_v` (plan, route B)

Package W-vis of `e2e-security.md`. Decision E2E-1 deferred it; decision E2E-6 records the
route. Goal: the end theorem with §0's bound, in which every leanVM term is charged per visible
query `Q_v` and the forgery term is charged per key. Lean's three axioms only.

Checked against the code at `mumbai` `ba481b24`. P2a's definitions (`Vis/Shape.lean`) are
written and build. Every other signature below is the contract of its package. A package may add
hypotheses only by asking.

## 0. Summary

* **§3 is false at T3** (E2E-6). On the visible log, `Pred` has probability about `Q_v/2^64`,
  because the schemes reveal the low 16 of the 24 challenge bytes of hidden answers. Fixed in
  every route by `PredS`, which excludes hidden entries.
* **Route B** (approved) replaces §3's visible log:
  * the bad events run on the full log in sampling order;
  * a fresh query is charged by its input's class: non-hidden ones (at most `Q_v = qH + budget`)
    pay the existing rates, hidden ones (`Hid keys`, every signer query) pay failure rates only;
  * a stopped potential `Φ·1[¬FormatI]` handles the one format event;
  * the extractor reads V_I's trace, a sub-log of `vis_final`.
* **T5 per key (P7).** A hybrid over the `n_x + n_s` keys. Reduction `j` uses the single-key
  theorems and answers every other key's inputs from its own lazy oracle. Those inputs form a
  *static* class given key `j`'s parameter, so the simulation is perfect, with no GuessS. It is
  charged `Q_v + Q_sig′_j + c + 2n`.
* **The final theorem** `aggregate_no_forgery_vis` is bounded by `sec0Error`, §0's formula as a
  Lean definition with the constants the proofs give. §6 compares it with §0's prose, term by
  term.
* **Size:** about 6.5–11k lines. 4 helpers plus me; pairing in §5.

## 1. What changes with respect to §0/§3

| §3 / §0 item | Route B |
| --- | --- |
| hidden signer queries | the class `Hid keys` (`SchemeIn ∨ DerivShape`). Every signer and key-generation query is in it (P2b, P2c). Its fresh queries pay only failure rates. |
| visible log, `vis_final` | not built. The extractor reads V_I's trace `p.1.2` of `gameRec`, which is contained in `vis_final`. |
| re-verification | dropped. Not needed, and it would only add to `Q_v`. |
| coins forwarded, hidden fresh queries | kept (`Engine.lean`; P1's two-rate engine) |
| visible hits on hidden entries | not needed: the full log is in sampling order |
| stopped potential `Φ′ = Φ·1[¬Bad]` | kept, with `Bad = FormatI` |
| LateReveal, Hit, HiddenPredict, HiddenCollide, GuessS | not needed (§1.3 of the first version of this plan). GuessS also leaves T5, thanks to the static partition. |
| Format | `FormatI` (analysis) and `FormatT` (statement), rate `(n·2^64+1)/2^256` per query |
| T3 `Pred` on `vis_final` | false (E2E-6). Replaced by `PredS` on the full log. |
| T5 per key with self-simulation | P7 |

## 2. Interfaces fixed now (P2a, `LeanVM/E2E/Vis/Shape.lean`, builds)

```lean
def AddrOK (a : Bytes) : Prop := a.length = 16 ∧ a.drop 8 = List.replicate 8 0
def AddrShaped (x : Bytes) : Prop := 32 ≤ x.length ∧ AddrOK ((x.drop 16).take 16)
def paramPrefix : Bytes := List.replicate 16 0 ++ LeanXmss.fieldBytes (LeanXmss.keygenDomainFields .parameter)
def DerivShape (x : Bytes) : Prop :=
  (x.length = 40 ∧ LeanXmss.seedTag <+: x) ∨ (x.length = 43 ∧ Sphincs.seedTag <+: x) ∨
    (x.length = 64 ∧ paramPrefix <+: x)
def keyParams (keys : Keys nx ns) : List Bytes  -- bytesLE 16 of each secret key's parameter, xmss then sphincs
def SchemeIn (keys : Keys nx ns) (x : Bytes) : Prop := ∃ p ∈ keyParams keys, ∃ a, AddrOK a ∧ p ++ a <+: x
def Hid (keys : Keys nx ns) (x : Bytes) : Prop := SchemeIn keys x ∨ DerivShape x
def InPfx (keys : Keys nx ns) (d : Digest) : Prop :=
  (∃ p ∈ keyParams keys, ∃ a, AddrOK a ∧ digestBytes d = p ++ a) ∨ digestBytes d = paramPrefix
def FormatT (keys : Keys nx ns) (ℓ : Log) : Prop := ∃ e ∈ ℓ, ¬ Hid keys e.1 ∧ InPfx keys e.2
def FormatI (keys : Keys nx ns) (k0 : ℕ) (ℓ : Log) : Prop :=
  ∃ (i : ℕ) (hi : i < ℓ.length), k0 ≤ i ∧ ¬ DerivShape ℓ[i].1 ∧ InPfx keys ℓ[i].2
-- proved:
theorem not_addrShaped_ivPrefix_append (d : Bytes) : ¬ AddrShaped (ivPrefix ++ d)
theorem SchemeIn.addrShaped : SchemeIn keys x → AddrShaped x
theorem not_hid_ivPrefix_append (keys) (d : Digest) : ¬ Hid keys (ivPrefix ++ digestBytes d)
theorem not_hid_batchLabel (keys) : ¬ Hid keys LeanVM.Node.batchLabel
theorem not_hid_daLabel (keys) : ¬ Hid keys LeanDa.label
theorem FormatT.formatI (hkg : ∀ i (hi : i < ℓ.length), i < k0 → Hid keys ℓ[i].1) :
    FormatT keys ℓ → FormatI keys k0 ℓ
```

Still to add to P2a (mine):
* `not_inPfx_aggSeedD : ¬ InPfx keys Guest.B1.Main.aggSeedD`. Its bytes `24..31` come from the
  limb `4136606974476857268`; `digestAt` is `noncomputable`, so this goes through
  `digestOfScalars`.
* `not_hid_chainInput : ¬ InPfx keys c → ¬ Hid keys (digestBytes c ++ b)`, for `b` of length 32
  (also 16 for DA).
* `paramPrefix_eq_sphincs : paramPrefix = List.replicate 16 0 ++ Sphincs.fieldBytes (Sphincs.keygenDomainFields .parameter)`.
* E2E-6's obstruction as a lemma (cheap, no probability):

  ```lean
  theorem challengeOf_limbs_of_truncate {d d' : Digest}
      (h : LeanXmss.truncateHash (digestBits d) = LeanXmss.truncateHash (digestBits d')) :
      (challengeOf d).limb 0 = (challengeOf d').limb 0 ∧ (challengeOf d).limb 1 = (challengeOf d').limb 1
  ```

  A truncated value a signature reveals fixes two of the challenge's three limbs, so `Pred` on a
  visible log is a 64-bit guess. The probability statement stays in prose (E2E-6): formalising the
  attack's adversary costs more than it shows.

## 3. Packages and exact signatures

All files are new, under `LeanVM/E2E/Vis/`, namespace `LeanVM.E2E`, `variable {nx ns : ℕ}
[Sphincs.Params]` where needed. "≈" gives the expected size.

### P1 — two-rate engine and the keygen split (`Vis/Engine.lean`, ≈350–550)

```lean
/-- Charged by class: `p` fresh queries raise `Φ` by `δp`, other `q` ones by `δq`, the rest not
at all; `a` and `b` bound the `p`- and `q`-queries. -/
theorem prEvent_run_le_twoRate {ι : Type} {spec : OracleSpec.{0,0} ι}
    [∀ t, SampleableType (spec.Range t)] [∀ t, Fintype (spec.Range t)] {σ : Type}
    {lookup : σ → (t : spec.Domain) → Option (spec.Range t)} {record : σ → (t : spec.Domain) → spec.Range t → σ}
    {impl : QueryImpl spec (StateT σ ProbComp)} (himpl : IsLazySampler lookup record impl)
    (p q : ι → Prop) [DecidablePred p] [DecidablePred q] (hpq : ∀ t, p t → q t)
    {Φ : σ → ℝ≥0∞} {δp δq : ℝ≥0∞} (size : σ → ℕ) (N : ℕ)
    (hsize : ∀ s t u, lookup s t = none → size (record s t u) ≤ size s + 1)
    (hp : ∀ s t, size s < N → p t → lookup s t = none →
      (∑ u, Φ (record s t u)) / Fintype.card (spec.Range t) ≤ Φ s + δp)
    (hq : ∀ s t, size s < N → q t → ¬ p t → lookup s t = none →
      (∑ u, Φ (record s t u)) / Fintype.card (spec.Range t) ≤ Φ s + δq)
    (hfree : ∀ s t, ¬ q t → lookup s t = none →
      (∑ u, Φ (record s t u)) / Fintype.card (spec.Range t) ≤ Φ s)
    {α : Type} (oa : OracleComp spec α) (a b : ℕ) (ha : IsQueryBoundP oa p a) (hb : IsQueryBoundP oa q b)
    (s₀ : σ) (hs₀ : size s₀ + b ≤ N) (ev : α → σ → Prop)
    (hev : ∀ z ∈ support ((simulateQ impl oa).run s₀), ev z.1 z.2 → 1 ≤ Φ z.2) :
    Pr{let z ← (simulateQ impl oa).run s₀}[ev z.1 z.2] ≤ Φ s₀ + a * δp + b * δq

/-- The key-generation phase and the rest (V_I recorded). -/
noncomputable def keygenPhase : ProbComp ((Keys nx ns × SignState nx ns) × Log) :=
  (simulateQ gameImpl ((keygen : GameM nx ns (Keys nx ns)).run (SignState.init nx ns))).run []
noncomputable def restRec (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns)
    (keys : Keys nx ns) (st : SignState nx ns) : OracleComp GameSpec (GameOutcome nx ns × Log)
theorem gameRec_eq_keygen_bind (guest fuel budget A) :
    gameRec guest fuel budget A = keygenPhase >>= fun k ↦ (simulateQ gameImpl (restRec guest fuel budget A k.1.1 k.1.2)).run k.2
theorem restRec_keys : z ∈ support (restRec guest fuel budget A keys st) → z.1.keys = keys
/-- Conditioning on key generation: a bound for each reachable `(keys, st, ℓ_kg)`, averaged. -/
theorem prEvent_gameRec_le_of_phase (ev : ((GameOutcome nx ns × Log) × Log) → Prop) (B : (Keys nx ns × SignState nx ns) × Log → ℝ≥0∞)
    (h : ∀ k ∈ support keygenPhase, Pr{let z ← (simulateQ gameImpl (restRec guest fuel budget A k.1.1 k.1.2)).run k.2}[ev z] ≤ B k) :
    Pr{let p ← gameRec guest fuel budget A}[ev p] ≤ ∫⁻ k, B k ∂𝒟[keygenPhase]
```

The two budgets go through VCVio's generic `IsQueryBound` with an `ℕ × ℕ` budget. The joint bound
follows from the two `IsQueryBoundP` per path. `prEvent_gameRec_le_of_phase` is the composition
`run_simulateQ_bind`.

### P2b / P2c — scheme walks (`Vis/WalkXmss.lean` ≈300–500, `Vis/WalkSphincs.lean` ≈400–800)

```lean
/-- Every query of `oa` satisfies `P`. -/
abbrev QueriesSat {ι : Type} {spec : OracleSpec.{0,0} ι} {α : Type} (oa : OracleComp spec α)
    (P : ι → Prop) [DecidablePred P] : Prop := IsQueryBoundP oa (fun t ↦ ¬ P t) 0
/-- Prefixed by the parameter `P` and an address. -/
def ParamPrefixed (p : Bytes) (x : Bytes) : Prop := ∃ a, AddrOK a ∧ p ++ a <+: x
-- leanXMSS
theorem xmss_sign_queries (sk : LeanXmss.Seeded.SecretKey) (i : LeanXmss.LeafIndex) (m : LeanXmss.Message) :
    QueriesSat (LeanXmss.Seeded.sign sk i m : OracleComp LeanXmss.HashSpec _) (ParamPrefixed (LeanXmss.bytesLE 16 sk.parameter))
/-- Key generation: two derivations, then queries prefixed by the derived parameter, which the keys carry. -/
theorem xmss_keygen_queries (seed : LeanXmss.MasterSeed) :
    ∀ z ∈ support ((simulateQ (QueryImpl.ofLift _ _ |>.withLogging) (LeanXmss.Seeded.keygenFromSeed seed)).run),
      ∀ x ∈ z.2.map (·.1), DerivShape x ∨ ParamPrefixed (LeanXmss.bytesLE 16 z.1.2.parameter) x
theorem xmss_keygen_param (seed) : ∀ z ∈ support (LeanXmss.Seeded.keygenFromSeed seed), z.1.parameter = z.2.parameter
-- leanSPHINCS: the same three, `Sphincs.Seeded.sign`, `Sphincs.Seeded.keygenFromSeed`
theorem sphincs_sign_queries … ; theorem sphincs_keygen_queries … ; theorem sphincs_keygen_param …
-- the derivations: query counts for P7's budget
theorem xmss_keygen_deriv_count (seed) : IsQueryBoundP (LeanXmss.Seeded.keygenFromSeed seed) DerivShapeQ 2
theorem sphincs_keygen_deriv_count (seed) : IsQueryBoundP (Sphincs.Seeded.keygenFromSeed seed) DerivShapeQ 2
```

The logging form of `*_keygen_queries` may be replaced by any equivalent support statement that
P2d can use. Agree it with P2d.

### P2d — counts (`Vis/Count.lean`, ≈250–400)

```lean
def VisQ (keys : Keys nx ns) : GameSpec.Domain → Prop | .inl _ => False | .inr x => ¬ Hid keys x
def CostsP (P : GameSpec.Domain → Prop) [DecidablePred P] (c : ℕ) {α : Type} (x : GameM nx ns α) : Prop :=
  ∀ st, IsQueryBoundP (x.run st) P c
theorem keygenPhase_hid : ∀ k ∈ support (keygenPhase (nx := nx) (ns := ns)), ∀ e ∈ k.2, Hid k.1.1 e.1
theorem isQueryBoundP_restRec_vis (keys st) (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH) :
    IsQueryBoundP (restRec guest fuel budget A keys st) (VisQ keys) (qH + budget)
theorem isQueryBoundP_restRec (…as isQueryBoundP_gameComp…) :
    IsQueryBoundP (restRec guest fuel budget A keys st) IsHash ((qH + sX * cxs + sS * css) + budget)
```

### P3a — decoder invariant, T1 and W6 (`Vis/Decoder.lean`, ≈600–1100)

```lean
/-- The seeding is not hidden: every step with a nonempty prefix has a non-hidden input. -/
def SeedsNotHid (keys : Keys nx ns) {X : Type} (σ : Seeds X) : Prop :=
  ∀ a ∈ σ.steps, a.1 ≠ [] → ∀ d, ¬ Hid keys (Seed.input a d)
theorem seedsNotHid_leanVmSeeds (keys) : SeedsNotHid keys leanVmSeeds
theorem seedsNotHid_batchSeedsAll (keys) : SeedsNotHid keys batchSeedsAll
/-- **The invariant**: decoded digests are not hidden prefixes. -/
theorem decode_info_not_inPfx {X : Type} (σ : Seeds X) (P : Prog Bool) (hσ : SeedsNotHid keys σ)
    {ℓ : Log} {k0 : ℕ} (hkg : ∀ (i : ℕ) (hi : i < ℓ.length), i < k0 → Hid keys ℓ[i].1)
    (hF : ¬ FormatI keys k0 ℓ) : ∀ c, (decode σ P ℓ).info c ≠ none → ¬ InPfx keys c
/-- **The hidden step of T1's potential**, stopped at the format event. -/
theorem potStop_step_hid (D) {X} (σ : Seeds X) (P : Prog Bool) (hσ : SeedsNotHid keys σ) {ℓ : Log} {k0 : ℕ}
    (hkg : …) (hk0 : k0 ≤ ℓ.length) {t : Bytes} (ht : Hid keys t) (hfresh : t ∉ ℓ.map Prod.fst) :
    (∑ u, pot D σ P (ℓ ++ [(t, u)]) * ind (¬ FormatI keys k0 (ℓ ++ [(t, u)]))) / Fintype.card Digest ≤
      pot D σ P ℓ * ind (¬ FormatI keys k0 ℓ) + failBound σ ℓ.length
theorem batchPotStop_step_hid (s0 : Digest) (hs0 : ¬ InPfx keys s0) (bytecode : List K) … :
    (∑ u, batchPot s0 bytecode (ℓ ++ [(t, u)]) * ind (¬ FormatI keys k0 (ℓ ++ [(t, u)]))) / Fintype.card Digest ≤
      batchPot s0 bytecode ℓ * ind (¬ FormatI keys k0 ℓ) + ((4 * (ℓ.length + 2) : ℕ) : ℝ≥0∞) / Fintype.card Digest
/-- On the key-generation log, only failure. -/
theorem pot_le_of_allHid (hall : ∀ e ∈ ℓ, Hid keys e.1) (hσ) : pot D σ P ℓ ≤ ind (Fail σ ℓ)
theorem batchPot_le_of_allHid (hall) (hs0) : batchPot s0 bytecode ℓ ≤ ind (Fail batchSeedsAll (startLog s0 ℓ))
```

(`potStop_step_vis`, the non-hidden step, follows from `step_ineq` and needs nothing new; P6
writes it.)

### P3b — decoder invariant, E5 (`Vis/DaDecoder.lean`, ≈300–600)

Superseded by fix B (E2E-7): `daPotStop_step_hid` below is false. The DA step is charged at E5's
full rate on every fresh query (`daPotStop_step`).

```lean
theorem daPotStop_step_hid (pc : LeanDa.Digest) {ℓ : Log} {k0 : ℕ} (hkg) (hk0 : k0 ≤ ℓ.length)
    {t : Bytes} (ht : Hid keys t) (hfresh : t ∉ ℓ.map Prod.fst) :
    (∑ u, daPot pc (ℓ ++ [(t, u)]) * ind (¬ FormatI keys k0 (ℓ ++ [(t, u)]))) / Fintype.card Digest ≤
      daPot pc ℓ * ind (¬ FormatI keys k0 ℓ) + ((4 * (ℓ.length + 1) : ℕ) : ℝ≥0∞) / Fintype.card Digest
theorem daPot_le_of_allHid (pc) (hall : ∀ e ∈ ℓ, Hid keys e.1) : daPot pc ℓ ≤ ind (FailDA pc ℓ)
```

### P4 — T3 restricted (`Vis/Pred.lean`, ≈400–700)

```lean
def PredS (keys : Keys nx ns) (o : ℕ) (ℓ : Log) : Prop :=
  ∃ (i : ℕ) (hi : i < ℓ.length) (j : ℕ) (hj : j ≤ i), ¬ Hid keys ℓ[i].1 ∧
    ¬ Hid keys (ℓ[j]'(Nat.lt_of_le_of_lt hj hi)).1 ∧
    ((ℓ[j]'(Nat.lt_of_le_of_lt hj hi)).1.drop o).take 24 = eBytes (challengeOf ℓ[i].2)
noncomputable def cntV (keys : Keys nx ns) (ℓ : Log) : ℕ  -- the non-hidden entries (classical filter)
noncomputable def predPotS (keys : Keys nx ns) (o n : ℕ) (ℓ : Log) : ℝ≥0∞ :=
  ind (PredS keys o ℓ) + ((∑ k ∈ Finset.Ico (cntV keys ℓ) (cntV keys ℓ + n), (k + 1) : ℕ) : ℝ≥0∞) / 2 ^ 192
theorem predPotS_step_vis (ht : ¬ Hid keys t) (n) : (∑ u, predPotS keys o n (ℓ ++ [(t, u)])) / Fintype.card Digest ≤ predPotS keys o (n + 1) ℓ
theorem predPotS_step_hid (ht : Hid keys t) (n) : (∑ u, predPotS keys o n (ℓ ++ [(t, u)])) / Fintype.card Digest ≤ predPotS keys o n ℓ
theorem predPotS_mono (n) : predPotS keys o n ℓ ≤ predPotS keys o (n + 1) ℓ
theorem predPotS_of_allHid (hall : ∀ e ∈ ℓ, Hid keys e.1) (n) : predPotS keys o n ℓ = n * (n + 1) / 2 ^ 193
/-- T3's conclusion for the guest on a log (the interface P5 consumes). -/
def RankOK (ℓ : Log) : Prop :=
  ∀ {seed sd dd pi : Digest} {d : DeferredClaim} {cs : List ChildClaims} {h : BatchHints} {c : ChildClaims} {i p : ℕ},
    96 + 24 * (d.bytecodePoint.length + d.matrixPoint.length) = predOffset (bytecodeWords Guest.guest) →
    fiatShamirIvWith (look ℓ) (bytecodeWords Guest.guest) = some seed →
    look ℓ (stmtInput seed sd dd d) = some pi → d.matrixPoint ≠ [] →
    batchWith (look ℓ) Guest.B1.Main.aggSeedD cs h = some (some d) → c ∈ cs →
    ∀ (hi : i < ℓ.length) (hp : p < ℓ.length), ℓ[i].2 = c.publicInput → ℓ[p].2 = pi → i < p
theorem rankOK_of_pred (hf : ¬ Fail leanVmSeeds ℓ) (hP : ¬ Pred (predOffset (bytecodeWords Guest.guest)) ℓ) : RankOK ℓ
theorem not_inPfx_seed (hf : ¬ Fail leanVmSeeds ℓ) (hF : ¬ FormatT keys ℓ)
    (hs : fiatShamirIvWith (look ℓ) (bytecodeWords Guest.guest) = some seed) : ¬ InPfx keys seed
theorem rankOK_of_vis (hf : ¬ Fail leanVmSeeds ℓ) (hF : ¬ FormatT keys ℓ)
    (hP : ¬ PredS keys (predOffset (bytecodeWords Guest.guest)) ℓ) : RankOK ℓ
```

(`rankOK_of_vis` uses `not_inPfx_aggSeedD`, from P2a. Batching chain states lie outside `InPfx`
by induction from `s0`.)

### P5 — T4 at V_I's trace (`Vis/Knowledge.lean`, ≈500–850)

```lean
def AggBadV (keys : Keys nx ns) (ℓ : Log) : Prop :=
  1 ≤ pot anyCertBlind.D leanVmSeeds anyProgramBlind ℓ ∨ Fail leanVmSeeds ℓ ∨
    BatchBad Guest.B1.Main.aggSeedD (bytecodeWords Guest.guest) ℓ ∨ DaBad deployedPads.1 ℓ ∨
    PredS keys (predOffset (bytecodeWords Guest.guest)) ℓ ∨ FormatT keys ℓ
theorem heldDirectTrace_of_node {ℓK : Log} (hG) (hGK)
    (hT1 : ¬ 1 ≤ pot anyCertBlind.D leanVmSeeds anyProgramBlind ℓ) (hF : ¬ Fail leanVmSeeds ℓ)
    (hB : ¬ BatchBad Guest.B1.Main.aggSeedD (bytecodeWords Guest.guest) ℓ) (hrank : RankOK ℓ)
    (hsub : LookSub (look ℓK) (look ℓ)) (hseed) (hD) :
    ∀ n hn π st, … → HeldDirect ℓK st   -- signatures AND DA openings under ℓK
theorem daBacked_trace {pc pr : LeanDa.Digest} (h : ¬ DaBad pc ℓ) (hsub : LookSub (look ℓK) (look ℓ))
    {r v : Digest} {w : Da.Witness} (hw : w.OpensWith (look ℓK) pc pr r v)
    (hout : Da.vectorDigestOfWith (look ℓK) r = some (Da.toBytes v)) : DaBacked ℓK pc pr (r, v)
theorem aggregate_knowledge_trace {ℓ ℓK : Log} (hG : …ℓ…) (hGK : …ℓK…)
    (hT1 hF hB) (hDA : ¬ DaBad deployedPads.1 ℓ) (hrank : RankOK ℓ) (hsub : LookSub (look ℓK) (look ℓ))
    {ip : IdealProof} {fuel : ℕ} {s : NodeStatement} (hv : idealVerify (look ℓK) Guest.guest ip fuel s = some true) :
    (∀ c ∈ s.claims.xmss, ∃ σ, xmssVerifyWith (look ℓK) c.1 c.2 σ = some true) ∧
    (∀ c ∈ s.claims.sphincs, ∃ σ, sphincsVerifyWith (look ℓK) c.1 c.2 σ = some true) ∧
    ∀ c ∈ s.claims.da, DaBacked ℓK deployedPads.1 deployedPads.2 c
/-- On `gameRec`: a good log gives the trace the claims (P7 and P6 consume this). -/
theorem gameRec_knows (hG) {p} (hp : p ∈ support (gameRec Guest.guest fuel budget A)) (ha : p.1.1.accepted = true)
    (hbad : ¬ AggBadV p.1.1.keys p.2) : ClaimsKnownTrace p.1.2 p.1.1.statement
```

P5 states its theorems with `hrank : RankOK ℓ`, so it is independent of P4. P6 supplies
`rankOK_of_vis`.

### P7 — T5 per key, other keys self-simulated (`Vis/PerKey/*.lean`, ≈2.2–3.8k)

**The class reduction `j` keeps private** is static given key `j`'s parameter `pj`:

```lean
def PrivJ (pj : Bytes) (x : Bytes) : Prop := AddrShaped x ∧ ¬ DerivShape x ∧ ¬ pj <+: x
```

It contains every other key's `P_i‖A`-prefixed input, unless `P_i = P_j`; the reduction then
aborts (`KeyColl`). It contains no input the challenger ever makes: key `j`'s key generation,
signatures and final verification are `pj`-prefixed or `DerivShape` (P2b, P2c). So answering
`PrivJ pj` from a private lazy oracle and the rest from the challenger's oracle is *exactly* one
random oracle. There is no conflict and no GuessS. The other keys' derivations (`DerivShape`, two
per key) are forwarded and charged.

**Reduction `j`**, a single-key adversary (`LeanXmss.Security.Adversary`,
`Sphincs.Security.Adversary`):
1. receive `pk_j`;
2. generate the other keys with private seeds and the routed oracle;
3. (as built: no abort; the other keys' trees are private whatever their parameters, and the
   event `KeyCollAt` is excluded from the bound instead);
4. run `gameRest` (`Reduction/GameW.lean`) with V_I recorded and the routed oracle, answering
   other keys' signing requests itself. Key `j`'s requests go to the challenger, refused as the
   game refuses: a reused leaf, or past `signatureLimit`;
5. output a forged claim of key `j` with a signature valid under the trace (P5), chosen
   classically, as `XmssRed` does.

```lean
-- P7a  Vis/PerKey/Partition.lean (≈300–600): two lazy oracles on a static partition are one
theorem evalDistEq_run_partition (Pr : Bytes → Prop) [DecidablePred Pr] (oa : OracleComp OW α) :
    (fun z ↦ (z.1, mergeCache z.2.1 z.2.2)) <$> (simulateQ (routeImpl Pr) oa).run (∅, ∅) ≃ᵈ (simulateQ owImpl oa).run ∅
-- P7a  key coincidences in key generation (≈200–300)
def KeyColl (keys : Keys nx ns) : Prop := ∃ i j, i ≠ j ∧ (keyParams keys)[i]? = (keyParams keys)[j]?
theorem prEvent_keygenPhase_keyColl_le :
    Pr{let k ← keygenPhase (nx := nx) (ns := ns)}[KeyColl k.1.1] ≤ ((nx + ns) ^ 2 : ℕ) / 2 ^ 129 + Qkg ^ 2 / 2 ^ 256
-- P7b  Vis/PerKey/Xmss.lean, Vis/PerKey/Sphincs.lean (≈1.2–2.2k together): reductions, transport, counts
noncomputable def xRedJ (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) (j : Fin nx) : LeanXmss.Security.Adversary
noncomputable def sRedJ (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) (j : Fin ns) : Sphincs.Security.Adversary
def ForgedXAt (j : Fin nx) (z : GameOutcome nx ns) : Prop :=
  ∃ msg, ((z.keys.xmss j).1, msg) ∈ z.statement.claims.xmss ∧ ∀ e ∈ z.state.xlog j, e.1.2 = msg → e.2 = none
def ForgedSAt (j : Fin ns) (z : GameOutcome nx ns) : Prop  -- likewise
theorem prEvent_forgedXAt_le (hG) (j : Fin nx) :
    Pr{let p ← gameRec Guest.guest fuel budget A}[p.1.1.accepted = true ∧ ForgedXAt j p.1.1 ∧ ¬ AggBadV p.1.1.keys p.2 ∧ ¬ KeyColl p.1.1.keys] ≤
      LeanXmss.Security.forgeAdvantage (xRedJ Guest.guest fuel budget A j)
theorem hasHashQueryBound_xRedJ (hxk hxs hvx) (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hXk : ∀ pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk) :
    LeanXmss.Security.HasHashQueryBound (xRedJ Guest.guest fuel budget A j) (qH + budget + 2 * (nx + ns) + cxk + sXk * cxs + cx)
-- and prEvent_forgedSAt_le, hasHashQueryBound_sRedJ with the requests to key j bounded by `min sSk signatureLimit`
-- P7c  Vis/PerKey/Sum.lean (≈200–400): the hybrid
theorem prEvent_forged_le_perKey … :
    Pr{let p ← gameRec Guest.guest fuel budget A}[p.1.1.accepted = true ∧ Forged p.1.1 ∧ ¬ AggBadV p.1.1.keys p.2] ≤
      nx * (qx / 2 ^ 127) + ns * (qs / 2 ^ 127) + Pr[KeyColl]
  -- qx := qH + budget + 2(nx+ns) + cxk + sXk·cxs + cx, from `LeanXmss.LeanXmssSecurityStatement`;
  -- qs likewise, from `Sphincs.Security.Det.HasClassicalSecurityBitsDet 127` (`requestedSecurity`)
def AdvXmssAt (j : Fin nx) : (AdvSpec nx ns).Domain → Prop   -- signing requests to xmss key j
def AdvSphincsAt (j : Fin ns) : (AdvSpec nx ns).Domain → Prop
```

**As built (P7b, leanXMSS).** `PerKey/XmssChain.lean`:
```lean
theorem PerKeyX.prEvent_xWinAt_le (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) (j : Fin nx) :
    Pr{let p ← gameRec guest fuel budget A}[XWinAt j p.1.1 p.1.2 ∧ ¬ KeyCollAt p.1.1.keys (Fin.castAdd ns j)] ≤
      LeanXmss.Security.forgeAdvantage (xRedJ guest fuel budget A j)
```
`KeyCollAt keys idx` (`PerKey/Defs.lean`) is key `idx`'s parameter repeated or zero; P7d bounds it
by `2(nx+ns)/2^128 + (nx·cxk + ns·csk)²/2^256`. P7c turns `accepted ∧ ForgedXAt j ∧ ¬AggBadV` into
`XWinAt j` on `gameRec` (P5's knowledge at the trace).

**What is reused.**
* `World`: `toW`, `owImpl`, `logCache`, `evalDistEq_run_toW`.
* `Lift`: `tw_*`, `vector_mapM_replicate`.
* `GameW`: `gameRest`, `toW_gameCompRec`.
* `Commute`: `romRun_bind_comm`, to move key `j`'s generation first.
* `Count`: `count_le_of_isQueryBoundP`, `isQueryBoundP_simulateQ_toW`.
* `Record`, and the final lemmas of `XmssRed`/`SphincsRed`: `CacheTr`, `run_finishX`,
  `forgeAdvantage_eq` adapted to the single-key games.

The cost comes mostly from three things: the partition lemma; the reduction's view equalling the
game (key `j` first, then the routed oracle); and the reduction's worst-case count with the abort.
The existing multi-user reductions are about 1.4k lines for both schemes with the same transport.
Per-key adds the routing and the abort.

### P6 — assembly (`Vis/Bound.lean`, `Vis/NoForgery.lean`, `Vis/Deployed.lean`, tests, pins; ≈900–1400)

```lean
/-- §0's formula, with the constants the proofs give (§6 compares it with §0's prose). -/
noncomputable def sec0Error (Qv Q nx ns qx qs : ℕ) : ℝ≥0∞ :=
  -- κ_V°, κ_batch, ε_DA at Q_v, and T3
  Qv * (εLean + 2 / 2 ^ 192 + 14 / 2 ^ 192) + Qv * (Qv + 1) / 2 ^ 193 +
  -- ε_signer, route B: every query's failures, the format event, key coincidences
  Q * (failBound leanVmSeeds Q + 4 * (Q + 1) / 2 ^ 256 + 4 * Q / 2 ^ 256 +
    ((nx + ns) * 2 ^ 64 + 1) / 2 ^ 256) + ((nx + ns) ^ 2 : ℕ) / 2 ^ 129 + Q ^ 2 / 2 ^ 256 +
  -- forgery, per key
  nx * ((Qv + qx : ℕ) / 2 ^ 127) + ns * ((Qv + qs : ℕ) / 2 ^ 127)

theorem prEvent_gameRec_aggBadV_le … :
    Pr{let p ← gameRec Guest.guest fuel budget A}[AggBadV p.1.1.keys p.2] ≤ (the first three lines of sec0Error)
def BreaksVis (z : GameOutcome nx ns) (tr : Log) : Prop :=
  z.accepted = true ∧ (Forged z ∨ ∃ c ∈ z.statement.claims.da, ¬ DaBacked tr deployedPads.1 deployedPads.2 c)
/-- **No forgery, visible accounting, forgery per key.** -/
theorem aggregate_no_forgery_vis
    (hxmss1 : LeanXmss.LeanXmssSecurityStatement) (hsph1 : Sphincs.Security.Det.HasClassicalSecurityBitsDet 127)
    {cxk csk cxs css cx cs : ℕ} (hxk hsk hxs hss hvx hvs)  -- as aggregate_no_forgery
    (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS sXk sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX) (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hXk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk)
    (hSk : ∀ j pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Pr{let p ← gameRec Guest.guest fuel budget A}[BreaksVis p.1.1 p.1.2] ≤
      sec0Error (qH + budget) (nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget) nx ns
        (2 * (nx + ns) + cxk + sXk * cxs + cx) (2 * (nx + ns) + csk + sSk * css + cs)
theorem aggregate_no_forgery_vis_breaks … : Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤ sec0Error …
-- Vis/Deployed.lean: closedNum0 (one fraction), aggregate_no_forgery_vis_deployed_{full,pruned20,…,pruned8},
-- aggregate_no_forgery_vis_one_slot_full, aggregate_no_forgery_vis_lifetime_full (n_x = n_s = 2^20,
-- qH + budget ≤ 2^64, sXk, sSk ≤ 2^24, sX, sS ≤ 2^44: ≤ 2^-41), …_lifetime_xmss
```

## 4. Dependencies

* P2a is done and fixes the interface.
* Independent of each other: P1, P2b, P2c, P3a, P3b, P4, P5, P7a.
* P2d needs the statements of P2b and P2c. It may take them as hypotheses until they land.
* P7b/c need P1 (`gameRec_eq_keygen_bind`), P2b/c (walks), P5 (`gameRec_knows`) and P7a.
* P6 needs everything.
* Critical path: P3a → P6, and P7b → P6.

## 5. Proposed pairing

* **local-1 {P1, P5}**: the engine and T4 at the trace; both on E2E modules already built.
* **local-2 {P2d, P4}**: counts and T3.
* **h2-1 {P3a, P3b}**: the decoder invariants (Compile/Rom, Da). Highest risk.
* **h2-2 {P2b, P2c}**: the scheme walks (lean_xmss/lean_sphincs code), then P7a (the partition
  lemma and `KeyColl`) when done.
* **me**: P2a's remaining lemmas, P7b, P7c, P6, and E2E-6 (written in `e2e-security.md` §7, in
  this worktree).

Each helper builds single modules with `lake build LeanVM.E2E.Vis.<Mod>` under
`ulimit -v 40000000`. None needs the generated families. Each must check that its new top-level
names are unique across `lean_vm/LeanVM` before sending.

## 6. `sec0Error` against §0, term by term

| §0 term | `sec0Error` | difference, and why |
| --- | --- | --- |
| `κ_V°(Q_v) = (Q_v+13213)(2^-128 + 5(Q_v+13213)/2^256)` | linear part `Q_v·εLean`. Quadratic part inside `Q·failBound leanVmSeeds Q`. | The `+13213` was the batching program's queries (`QV_b`), now in the game's own count (W6-1). The quadratic part is over all queries `Q` (next row). |
| `κ_batch(Q_v)` | `Q_v·2/2^192`; `Q·4(Q+1)/2^256` | quadratic part over `Q` |
| `ε_DA ≈ Q_v·14/2^192` | `Q·14/2^192`; `Q·4Q/2^256` | **extra** `Q_sig·14/2^192` (E2E-7, fix B): DA is charged at E5's full rate on hidden queries too. Counterexample to the hidden-step bound: a DA anchor completed by a hidden query after a hidden entry answering a hidden prefix. Below `2^-120` for `Q_sig ≤ 2^68`. The quadratic part is over `Q`. |
| `(Q_v+1)²/2^193` | `Q_v(Q_v+1)/2^193` | none (smaller) |
| (E5's failures on visible queries) | `4Q_v²/2^256` inside `Q·4Q/2^256` | **extra** `4Q_v²/2^256` (`deltaDaVis`): §0's `ε_DA ≈` drops E5's quadratic failure term; `κ_V°` and `κ_batch` cover only T1's `5Q_v²` and W6's `4Q_v²`. |
| ε_signer: `Q_v·Q_sig/2^255` (HiddenCollide, HiddenPredict, Hit) | contained in `Q·(5Q + 8Q + 4)/2^256`, `Q = Q_v + Q_sig` | **extra** `≈ 13·Q_sig(2Q_v + Q_sig)/2^256`. `Fail` counts collisions and predictions among hidden entries, which §3 ignored; removing them would mean re-proving T1's `final_ineq`. Lifetime: `≈ 2^-97`. |
| ε_signer: `Q_v·5/2^128` (LateReveal), `n·Q/2^256` (GuessS) | none | not needed by route B |
| ε_signer: `(S·2^8.1)³/2^258.6` (3-collisions of revealed halves) | none | not needed (that was LateReveal's `k`) |
| ε_signer: `n·2^45/2^256` (Format) | `Q·((nx+ns)·2^64+1)/2^256` | charged per query (§0's had no `Q`), and over all `2^64` address shapes rather than the `2^45` the schemes use. Lifetime: `≈ 2^-94`. |
| ε_signer: `n/2^128` (constant-prefixed transcript starts) | none | static facts (`not_hid_ivPrefix_append`, `not_inPfx_aggSeedD`, the labels) |
| ε_signer: `n²/2^128` (key coincidences) | `n·(2n/2^128 + Q_k²/2^256)`, `Q_k = n_x·c_xk + n_s·c_sk` (P7d, per key `KeyCollAt`) | **extra** `n²/2^128 + n·Q_k²/2^256` (`deltaKeyColl`): each reduction pays its own key's coincidences (another key's parameter, or a zero one), `2n/2^128`; `Q_k²/2^256` covers a repeated derivation (`S_i = S_k`). Lifetime: `≈ 2^-86`. |
| `(n_x+n_s)(Q_v + Q_sig′ + c)/2^127` | `nx(Q_v + qx)/2^127 + ns(Q_v + qs)/2^127`, `qx = 2(nx+ns) + cxk + sXk·cxs + cx` | **extra** `2(n_x+n_s)` per reduction: the other keys' derivations are forwarded, not self-simulated. They are the only inputs of the other keys outside the static private class (`deltaFwd = n·2n/2^127`). Lifetime: exactly `2^-84` (`deltaFwd_lifetime`). |

`Vis/Closed.lean` (P6b) proves `sec0Error ≤ eps0 + delta` (`sec0ErrorGame_le`), `eps0` §0's bound
term by term and `delta` the deviations above, and evaluates them with the kernel
(`closedNum0`, `eps0Num`, `deltaNum`). The proved values, at `n_x = n_s = 2^20`, leanXMSS's costs
and leanSPHINCS's at `b = 26` or `b = 20`:

| point | `sec0Error` | `delta` | today's `closedError` |
| --- | --- | --- | --- |
| lifetime (`Q_v ≤ 2^64`, `s_X, s_S ≤ 2^44`, `s_Xk, s_Sk ≤ 2^24`) | `≤ 2^-41` (`≈ 2^-41.97`; `≤ 2^-42 + 2^-47`) | `≤ 2^-84 + 2^-86 + 2^-91` (`deltaFwd` alone is `2^-84`) | `≈ 2^-28.07` |
| one slot (`s_X, s_S, s_Xk, s_Sk ≤ 2^20`) | `≤ 2^-42 + 2^-51` (`≈ 2^-42`) | | `≈ 2^-43.0` |
| leanXMSS only (`n_s = 0`), lifetime, `Q_v ≤ 2^64` | `≤ 2^-42` (`≈ 2^-43`) | | `≈ 2^-39` |
| leanXMSS only, lifetime, `Q_v ≤ 2^56` | `≤ 2^-49` (`≈ 2^-49.4`) | | `≈ 2^-39` |

At one slot the visible bound is about twice today's: the hybrid pays `n_x·Q_v/2^127` for
leanXMSS, where leanXMSS's multi-user theorem pays `Q/2^127` once. The deployed end theorems
therefore keep today's `aggregate_no_forgery_deployed_*` and add the visible ones beside them,
for the same event; the better of the two applies. Over a lifetime the visible bound wins,
`2^-42` against `2^-28`.

## 7. Risks

1. **P3a's invariant over `decode`** (many decoder cases). The step part is prototyped
   (`step_eq_none_of_not_decoded`). Fallback: charge hidden queries at the full T1 rate, at the
   cost of an extra `Q·2^-128` (lifetime `2^-51`).
2. **P7's view equality.** Key `j` first (`romRun_bind_comm`), then the routed oracle; the
   reduction's abort must not change the non-abort runs. The partition is static, so no
   identical-until-bad argument is needed beyond the abort event `KeyColl`.
3. **P2c, leanSPHINCS's key generation** (forests, pruning, grinding loop). Any query outside
   `ParamPrefixed pj ∨ DerivShape` breaks P7's "the challenger never queries `PrivJ`" and P2d's
   counts. Mirror `SphincsBound.lean`.
4. **Static constants.** `aggSeedD`'s bytes need a lemma through `digestOfScalars`. If a constant
   fails its shape check, add a `P_j = c[0:16]` event, `n/2^128` per constant.
5. **The keygen split and the two-budget engine.** Medium and low respectively; the existing
   `Bridge`/`Record` patterns cover the split.
6. **Numerics.** With leanSPHINCS keys, the per-key term `n_s(Q_v + Q_sig′)/2^127 ≈ 2^-43` now
   replaces today's `n_s·Q/2^127 ≈ 2^-29` at lifetime. This is the main gain of W-vis together
   with T3's `2^-65`.
7. **Memory.** Keep each new module under about 3.5 GB.
