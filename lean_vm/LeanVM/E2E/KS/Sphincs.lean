/-
  LeanVM.E2E.KS.Sphincs

  The leanSPHINCS reduction of the deployed game (decision E2E-15): an adversary against
  leanSPHINCS's multi-user game that runs the deployed game before verification with the
  multi-user game's keys, signing oracles and hash, and outputs the known forgery's signature.
-/

module

public import LeanVM.E2E.KS.Trace
public import LeanVM.E2E.Reduction.Sphincs

/-!
# The leanSPHINCS reduction of the deployed game

**The adversary** (`kAdv`). Against `n_s` leanSPHINCS keys (`Sphincs.Security.Multi`), it receives
their public keys and runs the deployed game before verification (`pGame`) in the schemes' world:
it generates the leanXMSS keys itself, runs the adversary with its transcript recorded (`record`),
answers its coins, hash queries and leanXMSS requests as the game does, and its leanSPHINCS
requests with the multi-user game's signing oracle (`SphincsRed.advImplS`, the old reduction's).
There is no verifier to run: the known forgery (`KnownForgedS`) carries a signature valid under
the adversary's own transcript, and the reduction outputs it (`forgeryOfK`).

**Its run is the game's, in distribution** (`evalDistEq_kPrefix`), as in the old reduction: the
key generations commute in the schemes' lazy random oracle. **Its forgery passes the check**
(`run_finishK`): the transcript is answered by the game's final log (`pGame_trace`), so its
signature verifies against the multi-user game's final cache, and the forged message was never
answered for its key.

**The bound** (`prEvent_knownForgedS_le`): a known leanSPHINCS forgery is at most leanSPHINCS's
multi-user bound at the reduction's hash calls, the game's before verification and one final
verification's `686`.
-/

namespace LeanVM.E2E.KS

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open LeanVM.E2E OracleSpec OracleComp
open LeanVM.E2E.SphincsRed (RSpec liftR advImplS τS σS dummyKey dummySig sKeyLog SInv)
open LeanVM.E2E.XmssRed (CacheTr le_prEvent_bind_of_pure)
open scoped ENNReal

@[expose] public section

namespace SphincsKS

variable {nx ns : ℕ} [Sphincs.Params]

/-! ## The reduction -/

/-- **The reduction's run** with the leanSPHINCS public keys `spks`: the leanXMSS keys, then the
adversary with its transcript recorded, answered as the game does with the leanSPHINCS requests
forwarded; the outcome before verification (the leanSPHINCS secret keys dummies). -/
noncomputable def kCore (A : DAdversary nx ns) (spks : Fin ns → Sphincs.PublicKey) :
    OracleComp (RSpec ns) (POutcome nx ns) := do
  let xs ← liftR (LeanXmss.Concrete.sequenceFin fun _ : Fin nx ↦ LeanXmss.MultiUser.keygen)
  let keys : Keys nx ns := ⟨xs, fun j ↦ (spks j, dummyKey)⟩
  let q ← (simulateQ (advImplS keys)
    (record (A (fun j ↦ (keys.xmss j).1) (fun j ↦ (keys.sphincs j).1)))).run
      (SignState.init nx ns)
  pure ⟨keys, q.1.1.1, q.1.1.2, q.1.2, q.2⟩

/-- The outcome of a run of the reduction with the leanSPHINCS keys `sk`. -/
def fullOut (sk : Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey) (r : POutcome nx ns) :
    POutcome nx ns :=
  ⟨⟨r.keys.xmss, sk⟩, r.statement, r.proof, r.trace, r.state⟩

open Classical in
/-- **The reduction's forgery**: the known forgery's key, message and signature, a dummy if there
is none. -/
noncomputable def forgeryOfK [NeZero ns] (r : POutcome nx ns) :
    Sphincs.Security.Multi.Forgery ns :=
  if h : KnownForgedS r then ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose⟩
  else ⟨0, 0, dummySig⟩

/-- **The leanSPHINCS reduction of the deployed game**: the game before verification run with the
multi-user game's keys, signing oracles and hash; the known forgery's signature. -/
noncomputable def kAdv [NeZero ns] (A : DAdversary nx ns) :
    Sphincs.Security.Multi.Adversary ns where
  main spks := forgeryOfK <$> kCore A spks

/-! ## The reduction's run is the game's -/

/-- **With the leanSPHINCS keys fixed, the reduction's run is the rest of the game**: its
signing log forgotten, the leanXMSS keys, then the rest of the translated game at all the keys. -/
theorem map_kCore (A : DAdversary nx ns)
    (sk : Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey) :
    (fun p ↦ fullOut sk p.1) <$> (simulateQ (τS sk) (kCore A (fun j ↦ (sk j).1))).run =
      LeanXmss.Concrete.sequenceFin (fun _ : Fin nx ↦ LeanXmss.MultiUser.keygen) >>= fun xs ↦
        pRest A ⟨xs, sk⟩ := by
  have h := fst_map_run_simulateQ_writer' (τS sk) (kCore A (fun j ↦ (sk j).1))
  have hm : (fun p ↦ fullOut sk p.1) <$> (simulateQ (τS sk) (kCore A (fun j ↦ (sk j).1))).run =
      fullOut sk <$> (Prod.fst <$> (simulateQ (τS sk) (kCore A (fun j ↦ (sk j).1))).run) := by
    rw [Functor.map_map]
  rw [hm, h]
  change fullOut sk <$> simulateQ (σS sk) (kCore A (fun j ↦ (sk j).1)) = _
  unfold kCore pRest
  simp only [simulateQ_bind, SphincsRed.simulateQ_σS_liftR, simulateQ_pure, map_bind, map_pure]
  refine bind_congr fun xs ↦ ?_
  rw [QueryImpl.simulateQ_mapStateTBase_run, SphincsRed.mapStateTBase_advImplS, ←
    QueryImpl.simulateQ_mapStateTBase_run]
  rfl

/-- The multi-user game's run of the reduction, before the forgery's check: the seeds, the keys,
the reduction's run and the signing log. -/
noncomputable def kPrefix (A : DAdversary nx ns) :
    OracleComp OW ((Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey) × POutcome nx ns ×
      QueryLog (Sphincs.Security.Multi.SigningSpec ns)) := do
  let seeds ← (liftM (Sphincs.Security.Multi.sampleSeeds ns) : OracleComp OW _)
  let sk ← sLift (Sphincs.Security.Multi.keygenAll ns seeds)
  let p ← (simulateQ (τS sk) (kCore A (fun j ↦ (sk j).1))).run
  pure (sk, p.1, p.2)

/-- **The reduction's run has the game's distribution**: in the schemes' random oracle, its
outcome and final cache are distributed as the translated game's before verification. -/
theorem evalDistEq_kPrefix (A : DAdversary nx ns) :
    Prod.map (fun p ↦ fullOut p.1 p.2.1) id <$> romRun (kPrefix A) ∅ =ᵈ
      romRun (simulateQ toW (pGameComp A)) ∅ := by
  have h1 : Prod.map (fun p ↦ fullOut p.1 p.2.1) id <$> romRun (kPrefix A) ∅ =
      romRun ((liftM (Sphincs.Security.Multi.sampleSeeds ns) : OracleComp OW _) >>= fun seeds ↦
        sLift (Sphincs.Security.Multi.keygenAll ns seeds) >>= fun sk ↦
          LeanXmss.Concrete.sequenceFin (fun _ : Fin nx ↦ LeanXmss.MultiUser.keygen) >>= fun xs ↦
            pRest A ⟨xs, sk⟩) ∅ := by
    have h0 : (fun p ↦ fullOut p.1 p.2.1) <$> kPrefix A =
        (liftM (Sphincs.Security.Multi.sampleSeeds ns) : OracleComp OW _) >>= fun seeds ↦
          sLift (Sphincs.Security.Multi.keygenAll ns seeds) >>= fun sk ↦
            LeanXmss.Concrete.sequenceFin (fun _ : Fin nx ↦ LeanXmss.MultiUser.keygen) >>=
              fun xs ↦ pRest A ⟨xs, sk⟩ := by
      unfold kPrefix
      simp only [map_bind, map_pure]
      refine bind_congr fun seeds ↦ bind_congr fun sk ↦ ?_
      rw [← map_kCore, map_eq_bind_pure_comp]
      rfl
    rw [← h0]
    unfold romRun
    rw [simulateQ_map, StateT.run_map]
    rfl
  rw [h1, toW_pGameComp]
  refine EvalDistEq.trans (m' := ProbComp) (romRun_sKeygenAll _ ∅) ?_
  exact romRun_bind_comm _ _ (fun sk xs ↦ pRest A ⟨xs, sk⟩) ∅

/-! ## The reduction's signing log -/

/-- **The reduction's signing log in the multi-user game**: on every reachable run, the held
public keys are the multi-user game's, no leanSPHINCS log passes the limit, and each is the
multi-user log's part for its key. -/
theorem kCore_log (A : DAdversary nx ns)
    (sk : Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey) :
    ∀ p ∈ support ((simulateQ (τS sk) (kCore A (fun j ↦ (sk j).1))).run),
      (∀ j, (p.1.keys.sphincs j).1 = (sk j).1) ∧ SInv p.1.state ∧
        ∀ j, p.1.state.slog j = sKeyLog p.2 j := by
  intro p hp
  unfold kCore at hp
  simp only [simulateQ_bind, WriterT.run_bind', SphincsRed.run_simulateQ_τS_liftR, bind_map_left,
    mem_support_bind_iff, support_map, Set.mem_image] at hp
  obtain ⟨xs, -, q, ⟨a, ha, b, hb, rfl⟩, rfl⟩ := hp
  rw [QueryImpl.simulateQ_mapStateTBase_run] at ha
  have hinit : SInv (SignState.init nx ns) := fun j ↦ by simp [SignState.init]
  obtain ⟨hq1, hq2⟩ := SphincsRed.adv_sLog sk _ _ _ hinit a ha
  simp only [simulateQ_pure, WriterT.run_pure', support_pure, Set.mem_singleton_iff] at hb
  subst hb
  refine ⟨fun j ↦ rfl, fun j ↦ hq1 j, fun j ↦ ?_⟩
  have h2 := hq2 j
  simp only [SignState.init, List.nil_append] at h2
  simp only [Prod.map, id, h2, SphincsRed.sKeyLog_append]
  simp [sKeyLog]

/-! ## The reduction's win -/

/-- **The forgery's check in the multi-user game**: verify the forgery under the named key, and
judge it against the signing log. -/
noncomputable def finishK [NeZero ns]
    (p : (Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey) × POutcome nx ns ×
      QueryLog (Sphincs.Security.Multi.SigningSpec ns)) : OracleComp OW Bool := do
  let f := forgeryOfK p.2.1
  let verified ← sLift (Sphincs.Concrete.verify (p.1 f.key).1 f.message f.signature :
    OracleComp Sphincs.HashSpec Bool)
  return decide (Sphincs.Security.Multi.Valid p.2.2 f.key ∧
    ¬Sphincs.Security.Multi.Contains p.2.2 f) && verified

/-- **The multi-user game of the reduction** is its run, then the forgery's check. -/
theorem gameCore_kAdv [NeZero ns] (A : DAdversary nx ns) :
    (Sphincs.Security.Multi.gameCore (kAdv A) : OracleComp OW Bool) = kPrefix A >>= finishK := by
  have hmap : ∀ (keys : Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey)
      (X : OracleComp (RSpec ns) (POutcome nx ns)),
      (simulateQ (QueryImpl.ofLift Sphincs.OracleWorld (WriterT (QueryLog
          (Sphincs.Security.Multi.SigningSpec ns)) (OracleComp Sphincs.OracleWorld)) +
        Sphincs.Security.Multi.signingOracle keys) (forgeryOfK <$> X)).run =
      Prod.map forgeryOfK id <$> (simulateQ (QueryImpl.ofLift Sphincs.OracleWorld (WriterT
          (QueryLog (Sphincs.Security.Multi.SigningSpec ns)) (OracleComp Sphincs.OracleWorld)) +
        Sphincs.Security.Multi.signingOracle keys) X).run := by
    intro keys X
    have h := simulateQ_map (impl := QueryImpl.ofLift Sphincs.OracleWorld (WriterT (QueryLog
          (Sphincs.Security.Multi.SigningSpec ns)) (OracleComp Sphincs.OracleWorld)) +
        Sphincs.Security.Multi.signingOracle keys)
      (X : OracleComp (Sphincs.OracleWorld + Sphincs.Security.Multi.SigningSpec ns) _) forgeryOfK
    exact (congrArg WriterT.run h).trans (WriterT.run_map' _ _)
  unfold Sphincs.Security.Multi.gameCore kPrefix kAdv finishK
  dsimp only
  simp only [hmap, bind_assoc, pure_bind, bind_map_left]
  rfl

/-- `KnownForgedS` reads only the leanSPHINCS public keys. -/
theorem knownForgedS_fullOut {sk : Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey}
    {r : POutcome nx ns} (h : ∀ j, (r.keys.sphincs j).1 = (sk j).1) :
    KnownForgedS (fullOut sk r) ↔ KnownForgedS r := by
  simp only [KnownForgedS, fullOut, h]

/-- **The forgery's check passes** on a reachable run of the reduction with a known forgery, from
a cache holding the adversary's transcript. -/
theorem run_finishK [NeZero ns] {A : DAdversary nx ns}
    {y : ((Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey) × POutcome nx ns ×
      QueryLog (Sphincs.Security.Multi.SigningSpec ns)) × QueryCache LeanXmss.HashSpec}
    (hy : y.1 ∈ support (kPrefix A)) (hw : KnownForgedS (fullOut y.1.1 y.1.2.1))
    (hc : CacheTr y.2 y.1.2.1.trace) :
    (simulateQ owImpl (finishK y.1)).run' y.2 = pure true := by
  obtain ⟨⟨sk, r, log⟩, c⟩ := y
  simp only at hy hw hc ⊢
  unfold kPrefix at hy
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hy
  obtain ⟨seeds, -, sk', -, p, hp, rfl, rfl, rfl⟩ := hy
  obtain ⟨hkeys, hinv, hlog⟩ := kCore_log A sk p hp
  have hw' := (knownForgedS_fullOut hkeys).mp hw
  unfold finishK forgeryOfK
  simp only [hw', ↓reduceDIte]
  obtain ⟨-, hforged, hσ⟩ := hw'.choose_spec.choose_spec.choose_spec
  exact SphincsRed.run_finish_ofS hσ (hkeys _) hforged (hlog _) (hinv _) hc

/-! ## The reduction's bound -/

/-- **A known leanSPHINCS forgery is at most the reduction's multi-user advantage.** -/
theorem prEvent_knownForgedS_le_adv [NeZero ns] (A : DAdversary nx ns) :
    Pr{let z ← pGame A}[KnownForgedS z.1] ≤
      Sphincs.Security.Multi.forgeAdvantage (kAdv A) := by
  let F : POutcome nx ns × QueryCache LeanXmss.HashSpec → Prop :=
    fun o ↦ KnownForgedS o.1 ∧ CacheTr o.2 o.1.trace
  calc Pr{let z ← pGame A}[KnownForgedS z.1]
      = Pr{let o ← romRun (simulateQ toW (pGameComp A)) ∅}[F o] :=
        prEvent_pGame_eq A KnownForgedS
    _ = Pr{let o ← Prod.map (fun p ↦ fullOut p.1 p.2.1) id <$> romRun (kPrefix A) ∅}[F o] :=
        ((evalDistEq_kPrefix A).prEvent_eq F).symm
    _ = Pr{let y ← romRun (kPrefix A) ∅}[F (fullOut y.1.1 y.1.2.1, y.2)] := by
        rw [prEvent_map]; rfl
    _ ≤ Pr{let b ← romRun (kPrefix A) ∅ >>= fun y ↦
          (simulateQ owImpl (finishK y.1)).run' y.2}[b = true] := by
        refine le_prEvent_bind_of_pure _ _ (fun y : ((Fin ns → Sphincs.PublicKey ×
            Sphincs.Seeded.SecretKey) × POutcome nx ns ×
              QueryLog (Sphincs.Security.Multi.SigningSpec ns)) ×
            QueryCache LeanXmss.HashSpec ↦ F (fullOut y.1.1 y.1.2.1, y.2))
          fun y hy hF ↦ run_finishK (A := A) ?_ hF.1 hF.2
        have h1 : y.1 ∈ support ((simulateQ owImpl (kPrefix A)).run' ∅) := by
          rw [StateT.run'_eq, support_map]; exact ⟨y, hy, rfl⟩
        exact support_simulateQ_run'_subset _ _ _ h1
    _ = Sphincs.Security.Multi.forgeAdvantage (kAdv A) := by
        rw [SphincsRed.forgeAdvantage_eq, gameCore_kAdv, simulateQ_bind, StateT.run'_eq,
          StateT.run_bind, map_bind]
        simp only [StateT.run'_eq, map_bind]

/-! ## The reduction's hash calls -/

/-- **The reduction's multi-user game makes at most the game's hash queries before verification
and one final verification's.** -/
theorem isQueryBoundP_gameCore_kAdv [NeZero ns] (A : DAdversary nx ns) {qH sX sS : ℕ}
    (hA : DAdvBounds A qH sX sS) :
    IsQueryBoundP (Sphincs.Security.Multi.gameCore (kAdv A) : OracleComp OW Bool)
      IsHashW (preQueries nx ns qH sX sS + sphincsVerifyBound) := by
  rw [gameCore_kAdv]
  refine (isQueryBoundP_bind (n := ns * sphincsKeygenBound + (nx * xmssKeygenBound +
    (qH + sX * xmssSignBound + sS * sphincsSignBound) + 0)) (m := sphincsVerifyBound) ?_
    fun y _ ↦ ?_).mono (by unfold preQueries; omega)
  · unfold kPrefix
    refine (isQueryBoundP_bind (n := 0) (m := ns * sphincsKeygenBound + (nx * xmssKeygenBound +
      (qH + sX * xmssSignBound + sS * sphincsSignBound) + 0)) ?_ fun seeds _ ↦ ?_).mono
        (by omega)
    · rw [← simulateQ_toW_liftM]
      exact isQueryBoundP_simulateQ_toW _ 0 (isQueryBoundP_liftM_probComp _)
    · refine isQueryBoundP_bind (isQueryBoundP_sLift _ _ ?_) fun sk _ ↦ ?_
      · rw [keygenAll_eq_sequenceFin]
        exact isTotalQueryBound_sequenceFin _ _ fun i ↦ sphincsKeygenFromSeed_isTotalQueryBound _
      · refine isQueryBoundP_bind ?_ fun _ _ ↦ isQueryBoundP_pure _ _ _
        refine (isQueryBoundP_map_iff (p := IsHashW) _ (fun p ↦ fullOut sk p.1) _).mp ?_
        refine (congrArg (fun x ↦ IsQueryBoundP x IsHashW (nx * xmssKeygenBound +
          (qH + sX * xmssSignBound + sS * sphincsSignBound))) (map_kCore A sk)).mpr ?_
        refine isQueryBoundP_bind (isQueryBoundP_sequenceFin xmssKeygenBound _ fun _ ↦ ?_)
          fun xs _ ↦ isQueryBoundP_pRest hA _
        unfold LeanXmss.MultiUser.keygen
        refine (isQueryBoundP_bind (n := 0) (m := xmssKeygenBound) ?_ fun _ _ ↦
          isQueryBoundP_liftM_hash _ _ (keygenFromSeed_isTotalQueryBound _)).mono (by omega)
        rw [← simulateQ_toW_liftM]
        exact isQueryBoundP_simulateQ_toW _ 0 (isQueryBoundP_liftM_probComp _)
  · unfold finishK
    exact (isQueryBoundP_bind (n := sphincsVerifyBound) (m := 0)
      (isQueryBoundP_sLift _ _ (sphincsVerify_isTotalQueryBound _ _ _))
      fun _ _ ↦ by simp).mono (by omega)

/-- **The reduction's hash-call budget** in leanSPHINCS's multi-user game: the game's before
verification and one final verification's. -/
theorem hasHashQueryBound_kAdv [NeZero ns] (A : DAdversary nx ns) {qH sX sS : ℕ}
    (hA : DAdvBounds A qH sX sS) :
    Sphincs.Security.Multi.HasHashQueryBound (kAdv A)
      (preQueries nx ns qH sX sS + sphincsVerifyBound) := by
  intro result hr
  unfold Sphincs.Security.Multi.experiment at hr
  rw [StateT.run'_eq] at hr
  erw [support_map] at hr
  obtain ⟨r, hr, rfl⟩ := hr
  exact count_le_of_isQueryBoundP owImpl _ _ (isQueryBoundP_gameCore_kAdv A hA) ∅ r hr

end SphincsKS

/-! ## The bound -/

variable {nx ns : ℕ}

/-- **A known leanSPHINCS forgery in the deployed game** is at most leanSPHINCS's multi-user bound
`εs` at the game's hash evaluations before verification and one final verification's `686`. -/
theorem prEvent_knownForgedS_le [Sphincs.Params]
    {εs : ℕ → ℝ≥0∞} (hsph : Sphincs.Security.Multi.HasMultiUserBound ns εs)
    (A : DAdversary nx ns) {qH sX sS : ℕ} (hA : DAdvBounds A qH sX sS) :
    Pr{let z ← pGame A}[KnownForgedS z.1] ≤ εs (max 1 (preQueries nx ns qH sX sS + 686)) := by
  rcases Nat.eq_zero_or_pos ns with rfl | hns
  · refine le_trans (le_of_eq ?_) zero_le
    exact prEvent_eq_zero_of_forall_not _ _ fun z h ↦ by obtain ⟨j, -⟩ := h; exact j.elim0
  · have : NeZero ns := ⟨hns.ne'⟩
    refine (SphincsKS.prEvent_knownForgedS_le_adv A).trans (hsph _ (le_max_left _ _) _ ?_)
    intro r hr
    exact (SphincsKS.hasHashQueryBound_kAdv A hA r hr).trans (le_max_right _ _)

/-- **A known leanSPHINCS forgery at a bound `n q / 2^127`** (the form of `SphincsSet.multi`):
at most `n_s (q + 686) / 2^127`, `q` the game's hash evaluations before verification. -/
theorem prEvent_knownForgedS_le_rate [Sphincs.Params]
    (hsph : Sphincs.Security.Multi.HasMultiUserBound ns
      (fun q ↦ ns * ((q : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞))))
    (A : DAdversary nx ns) {qH sX sS : ℕ} (hA : DAdvBounds A qH sX sS) :
    Pr{let z ← pGame A}[KnownForgedS z.1] ≤
      (ns : ℝ≥0∞) * (((preQueries nx ns qH sX sS + 686 : ℕ) : ℝ≥0∞) /
        ((2 ^ 127 : ℕ) : ℝ≥0∞)) := by
  have hm : max 1 (preQueries nx ns qH sX sS + 686) = preQueries nx ns qH sX sS + 686 :=
    max_eq_right (by omega)
  have h := prEvent_knownForgedS_le hsph A hA
  rwa [hm] at h

end
end LeanVM.E2E.KS
