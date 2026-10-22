/-
  LeanVM.E2E.Vis.PerKey.SphincsCount

  W-vis, P7f: the per-key leanSPHINCS reduction's hash queries. In leanSPHINCS's single-key game
  it makes at most the adversary's hash queries, V_I's budget, two per other key, key `j`'s
  generation, `css` per signing request to key `j` and one final verification.
-/

module

public import LeanVM.E2E.Vis.PerKey.SphincsChain
public import LeanVM.E2E.Vis.PerKey.XmssCount

/-!
# The per-key leanSPHINCS reduction's query count (W-vis, P7f)

The leanSPHINCS counterpart of `Vis/PerKey/XmssCount.lean`, with the same costs (`CostR`): the
single-key game against reduction `j` is key `j`'s generation, then the reduction's run under the
challenger's oracles, then the final verification (`gameCore_sRedJ`). Under `ΦJS sk`, another
key's generation costs its two derivations, the adversary one per hash query and `css` per signing
request to key `j`, V_I its budget.

* `PerKeyS.hasHashQueryBound_sRedJ`: the reduction's budget in leanSPHINCS's single-key game
  (`Sphincs.Security.Det`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp

@[expose] public section

namespace PerKeyS

open PerKeyX (xPrefix' xTree keyOfTree sPrefix' sTree keyOfTreeS costR_xPrefix' costR_sPrefix')

variable {nx ns : ℕ} [Sphincs.Params]

/-- The schemes' leanSPHINCS key generation makes at most `csk` hash queries. -/
theorem isQueryBoundP_sKeygen_le {csk : ℕ}
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk) :
    IsQueryBoundP (sKeygen : OracleComp OW _) IsHashW csk := by
  unfold sKeygen
  exact (isQueryBoundP_bind (n := 0) (m := csk) (isQueryBoundP_liftM_probCompW _)
    fun seed _ ↦ isQueryBoundP_sLift _ _ (hsk seed)).mono (by omega)

/-- `ΦJS` of a simulation is the simulation by the images. -/
theorem ΦJS_simulateQ_run (sk : Sphincs.Seeded.SecretKey) {ι : Type} {spec : OracleSpec.{0, 0} ι}
    {σ : Type} (impl : QueryImpl spec (StateT σ RMs)) {α : Type} (oa : OracleComp spec α) (s : σ) :
    ΦJS sk ((simulateQ impl oa).run s) =
      (simulateQ (fun t ↦ stMap (fun {β : Type} (y : RMs β) ↦ ΦJS sk y) (impl t)) oa).run s := by
  have h1 := simulateQ_morph (isMorphism_stMap (σ := σ) (isMorphism_ΦJS sk)) impl oa
  have h2 := congrArg (fun x ↦ StateT.run x s) h1
  simp only [run_stMap] at h2
  exact h2.symm

/-- A class-routed computation, under the game's oracles, costs at most its hash queries. -/
theorem costR_ΦJS_rcS (sk : Sphincs.Seeded.SecretKey) (pj : Bytes) {α : Type}
    {oa : OracleComp OW α} {c : ℕ} (h : IsQueryBoundP oa IsHashW c) :
    CostR c (ΦJS sk (rcS pj oa)) := by
  rw [ΦJS_rcS]
  exact costR_route _ h

/-- A private computation, under the game's oracles, costs nothing. -/
theorem costR_ΦJS_rpS (sk : Sphincs.Seeded.SecretKey) {α : Type} (oa : OracleComp OW α) :
    CostR 0 (ΦJS sk (rpS oa)) := by
  rw [ΦJS_rpS]
  exact costR_route_all _ (fun _ ↦ trivial) oa

/-- **A leanXMSS key's generation costs its two derivations**: its tree is private. -/
theorem costR_ΦJS_xKeygenRS (sk : Sphincs.Seeded.SecretKey) (pj : Bytes) :
    CostR 2 (ΦJS sk (xKeygenRS pj)) := by
  rw [ΦJS_xKeygenRS]
  refine ((costR_xPrefix' pj).bind (c' := 0) fun m ↦ ?_).mono (by omega)
  unfold xTree keyOfTree
  exact ((costR_route_all _ (fun _ ↦ trivial) _).bind fun _ ↦ costR_pure _).mono (by omega)

/-- **Another leanSPHINCS key's generation costs its two derivations**: its tree is private. -/
theorem costR_ΦJS_sKeygenRS (sk : Sphincs.Seeded.SecretKey) (pj : Bytes) :
    CostR 2 (ΦJS sk (sKeygenRS pj)) := by
  rw [ΦJS_sKeygenRS]
  refine ((costR_sPrefix' pj).bind (c' := 0) fun m ↦ ?_).mono (by omega)
  unfold sTree keyOfTreeS
  exact ((costR_route_all _ (fun _ ↦ trivial) _).bind fun _ ↦ costR_pure _).mono (by omega)

/-- **The reduction's answers cost**: one per hash query, `css` per signing request to key `j`,
nothing for coins and the other keys' requests. -/
theorem costR_ΦJS_advImplJS {css : ℕ}
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (sk : Sphincs.Seeded.SecretKey) (pj : Bytes) (j : Fin ns) (keys : Keys nx ns)
    (t : (AdvSpec nx ns).Domain) (st : SignState nx ns) :
    CostR (if AdvHash t then 1 else if AdvSphincsAt j t then css else 0)
      ((stMap (fun {β : Type} (y : RMs β) ↦ ΦJS sk y) (advImplJS pj j keys t)).run st) := by
  rw [run_stMap]
  rcases t with (t | ⟨i, req⟩) | ⟨i, msg⟩
  · rw [advImplJS_inl_inl, StateT.run_mk]
    refine (costR_ΦJS_rcS sk pj (isQueryBoundP_tw_advImpl_inl_inl keys t st)).mono ?_
    split <;> omega
  · have hc : (if AdvHash (nx := nx) (ns := ns) (.inl (.inr (i, req))) then 1
        else if AdvSphincsAt (nx := nx) j (.inl (.inr (i, req))) then css else 0) = 0 := by
      simp [AdvHash, AdvSphincsAt]
    rw [hc, advImplJS_xmss, StateT.run_mk]
    exact costR_ΦJS_rpS sk _
  · by_cases hij : i = j
    · subst hij
      have hc : (if AdvHash (nx := nx) (ns := ns) (.inr (i, msg)) then 1
          else if AdvSphincsAt (nx := nx) i (.inr (i, msg)) then css else 0) = css := by
        simp [AdvHash, AdvSphincsAt]
      rw [hc, advImplJS_sphincs_self, run_sphincsFwdJ]
      split
      · rw [ΦJS_pure]
        exact (costR_pure _).mono (Nat.zero_le _)
      · rw [ΦJS_map, ΦJS_signQuery]
        exact (costR_liftM (isQueryBoundP_sLift _ _ (hss _ _))).map _
    · have hc : (if AdvHash (nx := nx) (ns := ns) (.inr (i, msg)) then 1
          else if AdvSphincsAt (nx := nx) j (.inr (i, msg)) then css else 0) = 0 := by
        simp [AdvHash, AdvSphincsAt, hij]
      rw [hc, advImplJS_sphincs_ne _ _ _ hij, StateT.run_mk]
      exact costR_ΦJS_rpS sk _

/-- **The adversary's phase costs** at most its hash queries and `css` per signing request to
key `j`. -/
theorem costR_ΦJS_adv {css : ℕ}
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (sk : Sphincs.Seeded.SecretKey) (pj : Bytes) (j : Fin ns) (keys : Keys nx ns) {α : Type}
    (oa : OracleComp (AdvSpec nx ns) α) {qH sSk : ℕ} (hH : IsQueryBoundP oa AdvHash qH)
    (hSk : IsQueryBoundP oa (AdvSphincsAt j) sSk) (st : SignState nx ns) :
    CostR (qH + sSk * css) (ΦJS sk ((simulateQ (advImplJS pj j keys) oa).run st)) := by
  rw [ΦJS_simulateQ_run]
  refine costR_simulateQ_run AdvHash (AdvSphincsAt j) css _ (fun t ht s ↦ ?_)
    (fun t ht hq s ↦ ?_) (fun t ht hq s ↦ ?_) oa hH hSk st
  · have h := costR_ΦJS_advImplJS hss sk pj j keys t s
    simpa [ht] using h
  · have h := costR_ΦJS_advImplJS hss sk pj j keys t s
    simpa [ht, hq] using h
  · have h := costR_ΦJS_advImplJS hss sk pj j keys t s
    simpa [ht, hq] using h

/-- **The reduction's run after the keys costs** the adversary's queries and V_I's budget. -/
theorem costR_ΦJS_restJS {css : ℕ}
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) (sk : Sphincs.Seeded.SecretKey)
    (pj : Bytes) (j : Fin ns) (keys : Keys nx ns) {qH sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hSk : ∀ pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    CostR (qH + sSk * css + (budget + 0)) (ΦJS sk (restJS guest fuel budget A pj j keys)) := by
  unfold restJS
  rw [ΦJS_bind]
  refine (costR_ΦJS_adv hss sk pj j keys _ (hH _ _) (hSk _ _) _).bind fun p ↦ ?_
  rcases p with ⟨sip, st⟩
  dsimp only
  rw [ΦJS_bind]
  refine (costR_ΦJS_rcS sk pj (isQueryBoundP_tw_viRec _ _ _ _ _ _)).bind fun q ↦ ?_
  rcases q with ⟨o, st'⟩
  dsimp only
  rw [ΦJS_pure]
  exact costR_pure _

/-- **The reduction's run costs** two per other key, the adversary's queries and V_I's budget. -/
theorem costR_ΦJS_sBodyJ {css : ℕ}
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) (sk : Sphincs.Seeded.SecretKey)
    (j : Fin ns) (pkj : Sphincs.PublicKey) {qH sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hSk : ∀ pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    CostR (qH + budget + 2 * (nx + ns) + sSk * css) (ΦJS sk (sBodyJ guest fuel budget A j pkj)) := by
  unfold sBodyJ
  rw [ΦJS_bind, morph_sequenceFin (isMorphism_ΦJS sk)]
  refine ((costR_sequenceFin (c := 2) _ fun _ ↦ costR_ΦJS_xKeygenRS sk _).bind
    (c' := ns * 2 + (qH + sSk * css + (budget + 0))) fun xs ↦ ?_).mono ?_
  · rw [ΦJS_bind, morph_sequenceFin (isMorphism_ΦJS sk)]
    refine (costR_sequenceFin (c := 2) _ fun i ↦ ?_).bind fun ss ↦
      costR_ΦJS_restJS hss guest fuel budget A sk _ j _ hH hSk
    split
    · rw [ΦJS_pure]
      exact (costR_pure _).mono (Nat.zero_le _)
    · exact costR_ΦJS_sKeygenRS sk _
  · rw [Nat.mul_add]
    omega

/-- **The single-key game against reduction `j` makes at most** key `j`'s generation, the
reduction's run and one final verification's hash queries. -/
theorem isQueryBoundP_gameCore_sRedJ {csk css cs : ℕ}
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk)
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (hvs : ∀ pk msg σ, IsTotalQueryBound
      (Sphincs.Concrete.verify pk msg σ : OracleComp Sphincs.HashSpec Bool) cs)
    (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) (j : Fin ns) {qH sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hSk : ∀ pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    IsQueryBoundP (Sphincs.Security.Det.gameCoreDet (sRedJ guest fuel budget A j) :
        OracleComp OW Bool) IsHashW
      (qH + budget + 2 * (nx + ns) + csk + sSk * css + cs) := by
  rw [gameCore_sRedJ]
  refine (isQueryBoundP_bind (isQueryBoundP_sKeygen_le hsk) fun kp _ ↦ ?_).mono
    (n := csk + ((qH + budget + 2 * (nx + ns) + sSk * css) + (cs + 0))) (by omega)
  unfold contJS
  refine isQueryBoundP_bind ?_ fun w _ ↦ ?_
  · have h := costR_ΦJS_sBodyJ hss guest fuel budget A kp.2 j kp.1 hH hSk ∅
    rw [ΦJS, run_stMap, simulateQ_σJS_eq, isQueryBoundP_map_iff] at h
    exact h
  · unfold finishJS
    exact isQueryBoundP_bind (isQueryBoundP_sLift _ _ (hvs _ _ _)) fun _ _ ↦ by simp

/-- **The per-key leanSPHINCS reduction's hash-call budget (P7f)** in leanSPHINCS's single-key
game: the adversary's hash queries `qH`, V_I's budget, two derivations per other key, key `j`'s
generation `csk`, `css` per signing request to key `j`, and one final verification `cs`. -/
theorem hasHashQueryBound_sRedJ {csk css cs : ℕ}
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk)
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (hvs : ∀ pk msg σ, IsTotalQueryBound
      (Sphincs.Concrete.verify pk msg σ : OracleComp Sphincs.HashSpec Bool) cs)
    (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) (j : Fin ns) {qH sSk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hSk : ∀ pkx pks, IsQueryBoundP (A pkx pks) (AdvSphincsAt j) sSk) :
    Sphincs.Security.Det.HasHashQueryBoundDet (sRedJ guest fuel budget A j)
      (qH + budget + 2 * (nx + ns) + csk + sSk * css + cs) := by
  intro result hr
  unfold Sphincs.Security.Det.experimentDet at hr
  rw [StateT.run'_eq] at hr
  erw [support_map] at hr
  obtain ⟨r, hr, rfl⟩ := hr
  exact count_le_of_isQueryBoundP owImpl _ _
    (isQueryBoundP_gameCore_sRedJ hsk hss hvs guest fuel budget A j hH hSk) ∅ r hr

end PerKeyS

end
end LeanVM.E2E
