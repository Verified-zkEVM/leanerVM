/-
  LeanVM.E2E.KS.Xmss

  The leanXMSS reduction of the deployed game (decision E2E-15): an adversary against leanXMSS's
  multi-user game that runs the deployed game before verification with the multi-user game's
  keys, signing oracles and hash, and outputs the known forgery's signature.
-/

module

public import LeanVM.E2E.KS.Trace
public import LeanVM.E2E.Reduction.VerifyBound
public import LeanVM.E2E.NoForgery

/-!
# The leanXMSS reduction of the deployed game

**The adversary** (`xAdv`). Against `n_x` leanXMSS keys (`LeanXmss.MultiUser`), it receives their
public keys and runs the deployed game before verification (`pGameComp`) in the schemes' world:
it generates the leanSPHINCS keys itself, answers the recorded adversary's coins, hash queries and
leanSPHINCS requests as the game does, and its leanXMSS requests as the game does but with the
multi-user game's signing oracle in place of the signer (`XmssRed.advImplX`). It outputs, for a
known leanXMSS forgery (`KnownForgedX`: a claim `(pk_j, m)` of the root statement, no request to
key `j` for `m` answered, a signature valid under the adversary's own hash answers), that
signature under key `j` (`forgeryOf`, a classical choice).

**Its run is the game's** (`map_xPrefix`): with the multi-user game's keys generated first, the
reduction's run, its signing log forgotten, is the translation of `pGameComp`.

**It wins whenever the game has a known forgery** (`prEvent_knownForgedX_le_adv`): the
transcript is held by the schemes' random oracle (`prEvent_pGame_eq`), so the signature verifies
there, and the forged message was never signed by key `j` (`xCore_log`).

**The bound** (`prEvent_knownForgedX_le`): the reduction makes at most `preQueries + 384` hash
calls (the game's before verification and one leanXMSS verification), so leanXMSS's multi-user
security bounds a known leanXMSS forgery by `xmssMultiError n_x (preQueries + 384)`.
-/

namespace LeanVM.E2E.KS

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open LeanVM.E2E OracleSpec OracleComp
open LeanVM.E2E.XmssRed (RSpec liftR τX σX advImplX dummyKey dummySig XInv conv
  run_simulateQ_τX_liftR simulateQ_σX_liftR mapStateTBase_advImplX adv_xLog run_finish_of
  le_prEvent_bind_of_pure forgeAdvantage_eq CacheTr map_eq_bind_pure_comp')
open scoped ENNReal

@[expose] public section

variable {nx ns : ℕ} [Sphincs.Params]

/-! ## The reduction -/

/-- **The reduction's run** with the leanXMSS public keys `xpks`: the leanSPHINCS keys, then the
recorded adversary with the game's oracles, its leanXMSS requests forwarded. -/
noncomputable def xCore (A : DAdversary nx ns) (xpks : Fin nx → LeanXmss.PublicKey) :
    OracleComp (RSpec nx) (POutcome nx ns) := do
  let ss ← liftR (LeanXmss.Concrete.sequenceFin fun _ : Fin ns ↦ sKeygen)
  let keys : Keys nx ns := ⟨fun j ↦ (xpks j, dummyKey), ss⟩
  let q ← (simulateQ (advImplX keys)
    (record (A (fun j ↦ (keys.xmss j).1) (fun j ↦ (keys.sphincs j).1)))).run
      (SignState.init nx ns)
  pure ⟨keys, q.1.1.1, q.1.1.2, q.1.2, q.2⟩

/-- An outcome with the leanXMSS keys `mk` in place of the reduction's. -/
def withX (mk : Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey) (z : POutcome nx ns) :
    POutcome nx ns :=
  { z with keys := ⟨mk, z.keys.sphincs⟩ }

open Classical in
/-- **The reduction's forgery**: the known forgery's key, message and signature when there is one
(`KnownForgedX`), a dummy otherwise. -/
noncomputable def forgeryOf [NeZero nx] (z : POutcome nx ns) : LeanXmss.MultiUser.Forgery nx :=
  if h : KnownForgedX z then
    ⟨h.choose, ⟨h.choose_spec.choose, h.choose_spec.choose_spec.choose⟩⟩
  else ⟨0, ⟨0, dummySig⟩⟩

/-- **The leanXMSS reduction of the deployed game**: the game before verification run with the
multi-user game's keys, signing oracles and hash; the known forgery's signature. -/
noncomputable def xAdv [NeZero nx] (A : DAdversary nx ns) : LeanXmss.MultiUser.Adversary nx where
  main xpks := forgeryOf <$> xCore A xpks

/-! ## The reduction's run is the game's -/

/-- The multi-user game's run of the reduction, the keys generated first: the keys, the
reduction's run and the signing log. -/
noncomputable def xPrefix (A : DAdversary nx ns) :
    OracleComp OW ((Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey) × POutcome nx ns ×
      QueryLog (LeanXmss.MultiUser.SigningSpec nx)) := do
  let mk ← LeanXmss.Concrete.sequenceFin fun _ : Fin nx ↦ LeanXmss.MultiUser.keygen
  let p ← (simulateQ (τX mk) (xCore A (fun j ↦ (mk j).1))).run
  pure (mk, p.1, p.2)

/-- **The reduction's run is the game's.** With the multi-user game's keys generated first, the
reduction's run, its signing log forgotten and the keys put back, is the translation of the
deployed game before verification. -/
theorem map_xPrefix (A : DAdversary nx ns) :
    (fun p ↦ withX p.1 p.2.1) <$> xPrefix A = simulateQ toW (pGameComp A) := by
  have hL : ∀ mk : Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey,
      (fun p ↦ withX mk p.1) <$> (simulateQ (τX mk) (xCore A (fun j ↦ (mk j).1))).run =
        LeanXmss.Concrete.sequenceFin (fun _ : Fin ns ↦ sKeygen) >>= fun ss ↦
          pRest A ⟨mk, ss⟩ := by
    intro mk
    have h := fst_map_run_simulateQ_writer' (τX mk) (xCore A (fun j ↦ (mk j).1))
    have hm : (fun p ↦ withX mk p.1) <$> (simulateQ (τX mk) (xCore A (fun j ↦ (mk j).1))).run =
        withX mk <$> (Prod.fst <$> (simulateQ (τX mk) (xCore A (fun j ↦ (mk j).1))).run) := by
      rw [Functor.map_map]
    rw [hm, h]
    change withX mk <$> simulateQ (σX mk) (xCore A (fun j ↦ (mk j).1)) = _
    unfold xCore pRest
    simp only [simulateQ_bind, simulateQ_σX_liftR, simulateQ_pure, map_bind, map_pure]
    refine bind_congr fun ss ↦ ?_
    rw [QueryImpl.simulateQ_mapStateTBase_run, mapStateTBase_advImplX, ←
      QueryImpl.simulateQ_mapStateTBase_run]
    rfl
  rw [toW_pGameComp]
  unfold xPrefix
  simp only [map_bind, map_pure]
  refine bind_congr fun mk ↦ ?_
  refine (map_eq_bind_pure_comp' _
    (fun a : POutcome nx ns × QueryLog (LeanXmss.MultiUser.SigningSpec nx) ↦
      withX mk a.1)).trans ?_
  rw [hL]

/-! ## The reduction's signing log -/

/-- **The reduction's signing log in the multi-user game**: on every reachable run, the leanXMSS
public keys are the multi-user game's, the final leanXMSS logs have distinct leaves, and each is
the multi-user log's part for its key. -/
theorem xCore_log (A : DAdversary nx ns)
    (mk : Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey) :
    ∀ p ∈ support ((simulateQ (τX mk) (xCore A (fun j ↦ (mk j).1))).run),
      (∀ j, (p.1.keys.xmss j).1 = (mk j).1) ∧ XInv p.1.state ∧
        ∀ j, conv (p.1.state.xlog j) = LeanXmss.MultiUser.keyLog p.2 j := by
  intro p hp
  unfold xCore at hp
  simp only [simulateQ_bind, WriterT.run_bind', run_simulateQ_τX_liftR, bind_map_left,
    simulateQ_pure, WriterT.run_pure', mem_support_bind_iff, support_map, support_pure,
    Set.mem_image, Set.mem_singleton_iff] at hp
  obtain ⟨ss, -, _, ⟨a, ha, _, rfl, rfl⟩, rfl⟩ := hp
  rw [QueryImpl.simulateQ_mapStateTBase_run] at ha
  have hinit : XInv (SignState.init nx ns) := fun j ↦ by simp [SignState.init]
  obtain ⟨h1, h2⟩ := adv_xLog mk _ _ _ hinit a ha
  refine ⟨fun j ↦ rfl, h1, fun j ↦ ?_⟩
  have h2j := h2 j
  rw [show conv ((SignState.init nx ns).xlog j) = [] from rfl, List.nil_append] at h2j
  simpa [Prod.map] using h2j

/-! ## The reduction's win -/

/-- **The forgery's check in the multi-user game**: verify the forgery under the named key, and
judge it against that key's requests. -/
noncomputable def finishX [NeZero nx]
    (p : (Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey) × POutcome nx ns ×
      QueryLog (LeanXmss.MultiUser.SigningSpec nx)) : OracleComp OW Bool := do
  let f := forgeryOf p.2.1
  let verified ← liftM (LeanXmss.Concrete.verify (p.1 f.key).1 f.forgery.message
    f.forgery.signature : OracleComp LeanXmss.HashSpec Bool)
  return decide (LeanXmss.SigningTranscript.Valid (LeanXmss.MultiUser.keyLog p.2.2 f.key) ∧
    ¬LeanXmss.SigningTranscript.Contains (LeanXmss.MultiUser.keyLog p.2.2 f.key) f.forgery) &&
      verified

/-- **The multi-user game of the reduction** is its run, then the forgery's check. -/
theorem gameCore_xAdv [NeZero nx] (A : DAdversary nx ns) :
    LeanXmss.MultiUser.gameCore (xAdv A) = xPrefix A >>= finishX := by
  unfold LeanXmss.MultiUser.gameCore xPrefix xAdv finishX
  simp only [bind_assoc, pure_bind, simulateQ_map, WriterT.run_map', bind_map_left]
  rfl

/-- `KnownForgedX` reads only the leanXMSS public keys. -/
theorem knownForgedX_withX {mk : Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey}
    {z : POutcome nx ns} (h : ∀ j, (mk j).1 = (z.keys.xmss j).1) :
    KnownForgedX (withX mk z) ↔ KnownForgedX z := by
  simp only [KnownForgedX, withX, h]

/-- **The forgery's check passes** on a reachable run of the reduction with a known forgery,
from a cache holding the transcript. -/
theorem run_finishX [NeZero nx] {A : DAdversary nx ns}
    {y : ((Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey) × POutcome nx ns ×
      QueryLog (LeanXmss.MultiUser.SigningSpec nx)) × QueryCache LeanXmss.HashSpec}
    (hy : y.1 ∈ support (xPrefix A)) (hw : KnownForgedX (withX y.1.1 y.1.2.1))
    (hc : CacheTr y.2 y.1.2.1.trace) :
    (simulateQ owImpl (finishX y.1)).run' y.2 = pure true := by
  obtain ⟨⟨mk, r, log⟩, c⟩ := y
  simp only at hy hw hc ⊢
  unfold xPrefix at hy
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hy
  obtain ⟨mk', -, p, hp, rfl, rfl, rfl⟩ := hy
  obtain ⟨hkeys, hinv, hlog⟩ := xCore_log A mk p hp
  have hw' := (knownForgedX_withX (fun j ↦ (hkeys j).symm)).mp hw
  unfold finishX forgeryOf
  simp only [hw', ↓reduceDIte]
  obtain ⟨-, hforged, hσ⟩ := hw'.choose_spec.choose_spec.choose_spec
  exact run_finish_of hσ (hkeys _) hforged (hlog _) (hinv _) hc

/-- **The leanXMSS reduction of the deployed game.** A known leanXMSS forgery in the deployed
game before verification is at most as likely as the reduction's win in leanXMSS's multi-user
game. -/
theorem prEvent_knownForgedX_le_adv [NeZero nx] (A : DAdversary nx ns) :
    Pr{let z ← pGame A}[KnownForgedX z.1] ≤ LeanXmss.MultiUser.forgeAdvantage (xAdv A) := by
  let F : POutcome nx ns × QueryCache LeanXmss.HashSpec → Prop :=
    fun o ↦ KnownForgedX o.1 ∧ CacheTr o.2 o.1.trace
  calc Pr{let z ← pGame A}[KnownForgedX z.1]
      = Pr{let o ← romRun (simulateQ toW (pGameComp A)) ∅}[F o] := prEvent_pGame_eq A _
    _ = Pr{let y ← romRun (xPrefix A) ∅}[F (withX y.1.1 y.1.2.1, y.2)] := by
        rw [← map_xPrefix, romRun, simulateQ_map, StateT.run_map, prEvent_map]
    _ ≤ Pr{let b ← romRun (xPrefix A) ∅ >>= fun y ↦
          (simulateQ owImpl (finishX y.1)).run' y.2}[b = true] := by
        refine le_prEvent_bind_of_pure _ _ (fun y : ((Fin nx → LeanXmss.PublicKey ×
            LeanXmss.Seeded.SecretKey) × POutcome nx ns ×
              QueryLog (LeanXmss.MultiUser.SigningSpec nx)) × QueryCache LeanXmss.HashSpec ↦
            F (withX y.1.1 y.1.2.1, y.2))
          fun y hy hF ↦ run_finishX (A := A) ?_ hF.1 hF.2
        have h1 : y.1 ∈ support ((simulateQ owImpl (xPrefix A)).run' ∅) := by
          rw [StateT.run'_eq, support_map]; exact ⟨y, hy, rfl⟩
        exact support_simulateQ_run'_subset _ _ _ h1
    _ = LeanXmss.MultiUser.forgeAdvantage (xAdv A) := by
        rw [forgeAdvantage_eq, gameCore_xAdv, simulateQ_bind, StateT.run'_eq, StateT.run_bind,
          map_bind]
        simp only [StateT.run'_eq, map_bind]

/-! ## The reduction's hash calls -/

/-- **The reduction's multi-user game makes at most the game's hash queries before verification
and one leanXMSS verification's.** -/
theorem isQueryBoundP_gameCore_xAdv [NeZero nx] {A : DAdversary nx ns} {qH sX sS : ℕ}
    (hA : DAdvBounds A qH sX sS) :
    IsQueryBoundP (LeanXmss.MultiUser.gameCore (xAdv A)) IsHashW
      (preQueries nx ns qH sX sS + xmssVerifyBound) := by
  rw [gameCore_xAdv]
  refine isQueryBoundP_bind ?_ fun y _ ↦ ?_
  · have h2 := isQueryBoundP_simulateQ_toW _ _ (isQueryBoundP_pGameComp hA)
    rw [← map_xPrefix, isQueryBoundP_map_iff] at h2
    exact h2
  · unfold finishX
    exact (isQueryBoundP_bind (n := xmssVerifyBound) (m := 0)
      (isQueryBoundP_liftM_hash _ _ (verify_isTotalQueryBound _ _ _))
      fun _ _ ↦ by simp).mono (by omega)

/-- **The reduction's hash-call budget** in leanXMSS's multi-user game: the game's before
verification and one leanXMSS verification's. -/
theorem hasHashQueryBound_xAdv [NeZero nx] {A : DAdversary nx ns} {qH sX sS : ℕ}
    (hA : DAdvBounds A qH sX sS) :
    LeanXmss.MultiUser.HasHashQueryBound (xAdv A) (preQueries nx ns qH sX sS + 384) := by
  intro result hr
  unfold LeanXmss.MultiUser.experiment at hr
  rw [StateT.run'_eq] at hr
  erw [support_map] at hr
  obtain ⟨r, hr, rfl⟩ := hr
  have hv : xmssVerifyBound = 384 := by decide
  exact hv ▸ count_le_of_isQueryBoundP owImpl _ _ (isQueryBoundP_gameCore_xAdv hA) ∅ r hr

/-! ## The bound -/

/-- **A known leanXMSS forgery is at most leanXMSS's multi-user bound.** In the deployed game
before verification, against an adversary making at most `qH` hash queries, `sX` leanXMSS and
`sS` leanSPHINCS signing requests, if leanXMSS has its multi-user security and
`preQueries + 384 < 2^126`, a known leanXMSS forgery has probability at most
`xmssMultiError n_x (preQueries + 384)`. -/
theorem prEvent_knownForgedX_le (hxmss : LeanXmss.MultiUser.HasMultiUserSecurity)
    (A : DAdversary nx ns) {qH sX sS : ℕ} (hA : DAdvBounds A qH sX sS)
    (hq : preQueries nx ns qH sX sS + 384 < 2 ^ 126) :
    Pr{let z ← pGame A}[KnownForgedX z.1] ≤
      xmssMultiError nx (preQueries nx ns qH sX sS + 384) := by
  rcases Nat.eq_zero_or_pos nx with rfl | hnx
  · refine le_trans (le_of_eq ?_) zero_le
    exact prEvent_eq_zero_of_forall_not _ _ fun z h ↦ by obtain ⟨j, -⟩ := h; exact j.elim0
  · have : NeZero nx := ⟨hnx.ne'⟩
    exact (prEvent_knownForgedX_le_adv A).trans (hxmss nx _ hq _ (hasHashQueryBound_xAdv hA))

end
end LeanVM.E2E.KS
