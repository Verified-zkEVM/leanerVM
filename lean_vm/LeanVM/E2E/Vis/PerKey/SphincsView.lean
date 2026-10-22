/-
  LeanVM.E2E.Vis.PerKey.SphincsView

  W-vis, P7b: the per-key leanSPHINCS reduction's view. Its run under the single-key game's oracles
  and the class-routed game agree on every event that forces good keys.
-/

module

public import LeanVM.E2E.Vis.PerKey.XmssView
public import LeanVM.E2E.Vis.PerKey.SphincsKeygen

/-!
# The leanSPHINCS reduction's view (W-vis, P7b)

The leanSPHINCS counterpart of `Vis/PerKey/XmssView.lean`; key `j` is a leanSPHINCS key.

* `agreeOn_keysS`: the class-routed game's key generation (key `j` given) and the reduction's
  agree on keys where no other parameter is `pj` (`GoodKeysS`).
* `prEvent_viewS`: the class-routed game's run after key `j`, and the reduction's run under the
  game's oracles, give every event forcing good keys the same probability.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

namespace PerKeyS

open PerKeyX (XKey SKey withKeys prEvent_bind_congr_supp sequenceFin_slot_self
  map_route_gameRest_congr length_bytesLE16_s)

variable {nx ns : ℕ} [Sphincs.Params]

/-- **Good keys for reduction `j`**, leanSPHINCS key `j` being `kj'`: every other parameter is not
`pj`. -/
def GoodKeysS (pj : Bytes) (j : Fin ns) (kj' : SKey) (p : (Fin nx → XKey) × (Fin ns → SKey)) :
    Prop :=
  (∀ i, LeanXmss.bytesLE 16 (p.1 i).2.parameter ≠ pj) ∧
    ∀ i, (i = j → p.2 i = kj') ∧ (i ≠ j → Sphincs.bytesLE 16 (p.2 i).2.parameter ≠ pj)

/-- The class-routed game's key generation, leanSPHINCS key `j` given. -/
noncomputable def gKeysS (pj : Bytes) (j : Fin ns) (kj' : SKey) :
    PM ((Fin nx → XKey) × (Fin ns → SKey)) := do
  let xs ← LeanXmss.Concrete.sequenceFin fun _ : Fin nx ↦
    simulateQ (routeImpl (PrivJ pj)) (LeanXmss.MultiUser.keygen : OracleComp OW _)
  let ss ← LeanXmss.Concrete.sequenceFin fun i : Fin ns ↦
    if i = j then pure kj'
    else simulateQ (routeImpl (PrivJ pj)) (sKeygen : OracleComp OW _)
  pure (xs, ss)

/-- The reduction's key generation, under the game's oracles, leanSPHINCS key `j` given. -/
noncomputable def rKeysS (sk : Sphincs.Seeded.SecretKey) (pj : Bytes) (j : Fin ns) (kj' : SKey) :
    PM ((Fin nx → XKey) × (Fin ns → SKey)) := do
  let xs ← LeanXmss.Concrete.sequenceFin fun _ : Fin nx ↦ ΦJS sk (xKeygenRS pj)
  let ss ← LeanXmss.Concrete.sequenceFin fun i : Fin ns ↦
    if i = j then pure kj' else ΦJS sk (sKeygenRS pj)
  pure (xs, ss)

/-- **The two key generations agree on good keys.** -/
theorem agreeOn_keysS (sk : Sphincs.Seeded.SecretKey) (pj : Bytes) (hpj : pj.length = 16)
    (j : Fin ns) (kj' : SKey) :
    AgreeOn (GoodKeysS (nx := nx) pj j kj') (gKeysS pj j kj') (rKeysS sk pj j kj') := by
  -- the leanXMSS sequence
  have hx : AgreeOn (fun v : Fin nx → XKey ↦ ∀ i, LeanXmss.bytesLE 16 (v i).2.parameter ≠ pj)
      (LeanXmss.Concrete.sequenceFin fun _ : Fin nx ↦
        simulateQ (routeImpl (PrivJ pj)) (LeanXmss.MultiUser.keygen : OracleComp OW _))
      (LeanXmss.Concrete.sequenceFin fun _ : Fin nx ↦ ΦJS sk (xKeygenRS pj)) :=
    agreeOn_sequenceFin_at (fun (_ : Fin nx) (k : XKey) ↦ LeanXmss.bytesLE 16 k.2.parameter ≠ pj)
      _ _ fun _ ↦ agreeOn_xKeygenS sk pj hpj
  -- the leanSPHINCS sequence
  have hs : AgreeOn (fun v : Fin ns → SKey ↦ ∀ i,
        (i = j → v i = kj') ∧ (i ≠ j → Sphincs.bytesLE 16 (v i).2.parameter ≠ pj))
      (LeanXmss.Concrete.sequenceFin fun i : Fin ns ↦
        if i = j then pure kj'
        else simulateQ (routeImpl (PrivJ pj)) (sKeygen : OracleComp OW _))
      (LeanXmss.Concrete.sequenceFin fun i : Fin ns ↦
        if i = j then pure kj' else ΦJS sk (sKeygenRS pj)) := by
    refine agreeOn_sequenceFin_at (fun (i : Fin ns) (k : SKey) ↦ (i = j → k = kj') ∧
      (i ≠ j → Sphincs.bytesLE 16 k.2.parameter ≠ pj)) _ _ fun i ↦ ?_
    by_cases hij : i = j
    · simp only [hij, ↓reduceIte]
      exact AgreeOn.refl _ _
    · simp only [hij, ↓reduceIte]
      exact (agreeOn_sKeygenS sk pj hpj).mono fun k hk ↦ hk.2 hij
  unfold gKeysS rKeysS
  refine AgreeOn.trans (hx.bind_comb (GoodKeysS pj j kj') _ (fun a t ↦ (a, t))
    fun a t h ↦ h.1) ?_
  exact agreeOn_bind_congr _ _ _ fun a ↦ hs.bind_pure (GoodKeysS pj j kj') (fun t ↦ (a, t))
    fun t h ↦ h.2

/-- The game after leanSPHINCS key `j`'s generation: the other keys, then the rest, key `j` being
`kj`. -/
noncomputable def RJS (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) (j : Fin ns)
    (kj : SKey) : OracleComp OW (GameOutcome nx ns × Log) := do
  let xs ← LeanXmss.Concrete.sequenceFin fun _ : Fin nx ↦
    (LeanXmss.MultiUser.keygen : OracleComp OW _)
  let ss ← LeanXmss.Concrete.sequenceFin fun i : Fin ns ↦
    if i = j then pure kj else (sKeygen : OracleComp OW _)
  gameRest guest fuel budget A ⟨xs, ss⟩

/-- Key `j` replaced by `k` in a list of leanSPHINCS keys. -/
def updJS (j : Fin ns) (k : SKey) (v : Fin ns → SKey) : Fin ns → SKey :=
  fun i ↦ if i = j then k else v i

/-- LeanSPHINCS key `j` replaced by `k` in the keys. -/
def setJS (j : Fin ns) (k : SKey) (keys : Keys nx ns) : Keys nx ns :=
  ⟨keys.xmss, updJS j k keys.sphincs⟩

/-- An outcome whose keys have leanSPHINCS key `j` replaced. -/
def holeOutS (j : Fin ns) (k : SKey) (z : GameOutcome nx ns × Log) : GameOutcome nx ns × Log :=
  (withKeys (setJS j k z.1.keys) z.1, z.2)

/-- `ΦJS` of a key position. -/
theorem ΦJS_ite (sk : Sphincs.Seeded.SecretKey) {α : Type} (p : Prop) [Decidable p] (a : α)
    (x : RMs α) : ΦJS sk (if p then pure a else x) = if p then pure a else ΦJS sk x := by
  split
  · exact ΦJS_pure sk a
  · rfl

/-- The class-routed game's keys hold leanSPHINCS key `j`'s value. -/
theorem gKeysS_slot (pj : Bytes) (j : Fin ns) (kj' : SKey) (cp : QueryCache LeanXmss.HashSpec)
    (z : ((Fin nx → XKey) × (Fin ns → SKey)) × QueryCache LeanXmss.HashSpec)
    (hz : z ∈ support ((gKeysS pj j kj').run cp)) : z.1.2 j = kj' := by
  unfold gKeysS at hz
  rw [sequenceFin_slot_self j kj'] at hz
  simp only [bind_assoc, pure_bind, StateT.run_bind, mem_support_bind_iff, StateT.run_pure,
    support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨r, -, r', -, hz⟩ := hz
  rw [hz]
  simp

/-- The reduction's rest keeps its keys. -/
theorem ΦJS_restJS_keys (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns)
    (sk : Sphincs.Seeded.SecretKey) (pj : Bytes) (j : Fin ns) (keys : Keys nx ns)
    (cp : QueryCache LeanXmss.HashSpec) (z : XmssRed.BOut nx ns × QueryCache LeanXmss.HashSpec)
    (hz : z ∈ support ((ΦJS sk (restJS guest fuel budget A pj j keys)).run cp)) :
    z.1.1 = keys := by
  unfold restJS at hz
  simp only [ΦJS_bind, ΦJS_pure, StateT.run_bind, mem_support_bind_iff, StateT.run_pure,
    support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨r, -, r', -, hz⟩ := hz
  rw [hz]

omit [Sphincs.Params] in
/-- Replacing a position twice keeps the last. -/
theorem updJS_updJS (j : Fin ns) (k k' : SKey) (v : Fin ns → SKey) :
    updJS j k (updJS j k' v) = updJS j k v := by
  funext i; unfold updJS; split <;> rfl

omit [Sphincs.Params] in
/-- Replacing a position by its value is the identity. -/
theorem updJS_self (j : Fin ns) (v : Fin ns → SKey) : updJS j (v j) v = v := by
  funext i; unfold updJS; split <;> simp_all

/-- **The reduction's view.** The class-routed game after leanSPHINCS key `j` (key `j`'s secret
key replaced by the reduction's hole key) and the reduction's run under the game's oracles give
every event that forces good keys the same probability. -/
theorem prEvent_viewS (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns)
    (sk : Sphincs.Seeded.SecretKey) (pkj : Sphincs.PublicKey) (hsk : sk.parameter = pkj.parameter)
    (j : Fin ns) (ev : GameOutcome nx ns × Log → QueryCache LeanXmss.HashSpec →
      QueryCache LeanXmss.HashSpec → Prop)
    (hev : ∀ z cp c, ev z cp c → GoodKeysS (Sphincs.bytesLE 16 sk.parameter) j (pkj, holeKeyS pkj)
      (z.1.keys.xmss, z.1.keys.sphincs))
    (cp c : QueryCache LeanXmss.HashSpec) :
    Pr{let z ← romRun ((holeOutS j (pkj, holeKeyS pkj) <$> simulateQ (routeImpl
        (PrivJ (Sphincs.bytesLE 16 sk.parameter))) (RJS guest fuel budget A j (pkj, sk))).run cp) c}[
        ev z.1.1 z.1.2 z.2] =
      Pr{let z ← romRun ((outJS <$> ΦJS sk (sBodyJ guest fuel budget A j pkj)).run cp) c}[
        ev z.1.1 z.1.2 z.2] := by
  set pj := Sphincs.bytesLE 16 sk.parameter with hpjdef
  have hpj : pj.length = 16 := length_bytesLE16_s _
  have hpjk : pjOfS pkj = pj := by rw [pjOfS, hpjdef, hsk]
  set kj' : SKey := (pkj, holeKeyS pkj) with hkj'
  -- the continuations
  let G' : (Fin nx → XKey) × (Fin ns → SKey) → PM (GameOutcome nx ns × Log) := fun p ↦
    holeOutS j kj' <$> simulateQ (routeImpl (PrivJ pj))
      (gameRest guest fuel budget A ⟨p.1, updJS j (pkj, sk) p.2⟩)
  let k : (Fin nx → XKey) × (Fin ns → SKey) → PM (GameOutcome nx ns × Log) := fun p ↦
    (fun z ↦ (withKeys ⟨p.1, p.2⟩ z.1, z.2)) <$> simulateQ (routeImpl (PrivJ pj))
      (gameRest guest fuel budget A ⟨p.1, updJS j (pkj, sk) p.2⟩)
  let k' : (Fin nx → XKey) × (Fin ns → SKey) → PM (GameOutcome nx ns × Log) := fun p ↦
    outJS <$> ΦJS sk (restJS guest fuel budget A pj j ⟨p.1, p.2⟩)
  -- the game side is the keys, then `G'`
  have hL : holeOutS j kj' <$> simulateQ (routeImpl (PrivJ pj))
      (RJS guest fuel budget A j (pkj, sk)) = gKeysS pj j kj' >>= G' := by
    unfold RJS gKeysS
    simp only [simulateQ_bind, Xmss.simulateQ_sequenceFin, map_bind, bind_assoc, pure_bind, G']
    refine bind_congr fun xs ↦ ?_
    have hite : (fun i : Fin ns ↦ simulateQ (routeImpl (PrivJ pj))
        (if i = j then pure (pkj, sk) else (sKeygen : OracleComp OW _))) =
        fun i ↦ if i = j then pure (pkj, sk)
          else simulateQ (routeImpl (PrivJ pj)) (sKeygen : OracleComp OW _) := by
      funext i; split <;> simp
    rw [hite, ← sequenceFin_slot' j kj' (pkj, sk)]
    rfl
  -- the reduction side is the keys, then `k'`
  have hR : outJS <$> ΦJS sk (sBodyJ guest fuel budget A j pkj) = rKeysS sk pj j kj' >>= k' := by
    unfold sBodyJ rKeysS
    simp only [ΦJS_bind, morph_sequenceFin (isMorphism_ΦJS sk), ΦJS_ite, map_bind, bind_assoc,
      pure_bind, k', hpjk]
    rfl
  -- `G'` is `k` on the game's possible keys
  have hGk : Pr{let z ← romRun ((gKeysS pj j kj' >>= G').run cp) c}[ev z.1.1 z.1.2 z.2] =
      Pr{let z ← romRun ((gKeysS pj j kj' >>= k).run cp) c}[ev z.1.1 z.1.2 z.2] := by
    rw [romRun_pm_bind, romRun_pm_bind]
    refine prEvent_bind_congr_supp _ _ _ _ _ fun r hr ↦ ?_
    have hslot := gKeysS_slot pj j kj' cp r.1 (fst_mem_support_of_mem_romRun hr)
    have hG : G' r.1.1 = k r.1.1 := by
      refine map_route_gameRest_congr guest fuel budget A _ _ _ _ fun z hz ↦ ?_
      simp only [holeOutS, setJS, hz, updJS_updJS]
      rw [← hslot, updJS_self]
    rw [hG]
  rw [hL, hR, hGk]
  refine prEvent_eq_of_agreeOn (agreeOn_keysS sk pj hpj j kj') k k' (fun p hp ↦ ?_)
    (fun z ↦ (z.1.keys.xmss, z.1.keys.sphincs)) (fun p cp z hz ↦ ?_) (fun p cp z hz ↦ ?_) ev
    (fun z cp c he ↦ hev z cp c he) cp c
  · -- the continuations agree on good keys
    have hj : p.2 j = kj' := (hp.2 j).1 rfl
    have hs : ∀ i, i ≠ j → p.2 i = updJS j (pkj, sk) p.2 i := fun i hi ↦ by
      simp [updJS, hi]
    have hgood : GoodJS pj j (⟨p.1, updJS j (pkj, sk) p.2⟩ : Keys nx ns) :=
      ⟨hp.1, fun i hi ↦ by dsimp only; rw [← hs i hi]; exact (hp.2 i).2 hi⟩
    have h := map_ΦJS_restJS guest fuel budget A sk j ⟨p.1, p.2⟩ ⟨p.1, updJS j (pkj, sk) p.2⟩ hs
      rfl (by simp [updJS]) (by dsimp only; rw [hj]; simp [updJS, hkj']) hgood
    exact h.symm
  · -- `k` keeps its keys
    simp only [k, StateT.run_map, support_map, Set.mem_image] at hz
    obtain ⟨w, -, rfl⟩ := hz
    rfl
  · -- `k'` keeps its keys
    simp only [k', StateT.run_map, support_map, Set.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have := ΦJS_restJS_keys guest fuel budget A sk pj j ⟨p.1, p.2⟩ cp w hw
    simp only [outJS, this]

end PerKeyS

end
end LeanVM.E2E
