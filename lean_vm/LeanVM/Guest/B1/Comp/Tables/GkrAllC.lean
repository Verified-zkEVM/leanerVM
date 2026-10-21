/-
  LeanVM.Guest.B1.Comp.Tables.GkrAllC

  `verify_bus_gkr` complete over a completeness model, from an answered run of the GKR phase,
  and the deployed completeness recovered at `CompModel.deployed`.
-/

module

public import LeanVM.Guest.B1.Comp.Tables.GkrHoldsC

/-!
# `verify_bus_gkr` over a completeness model

`verify_bus_gkr_relC`: on a memory holding an answered run's honest trace (`GkrTrace.OkM`,
`GkrMemC`) and the caller's words, `verify_bus_gkr` holds under the model's semantics of the
run's returns; `verify_bus_gkr_runC`: from the answered run itself (`exists_traceM`), on every
memory holding its trace's buffers.

At `CompModel.deployed` the total hash is BLAKE2s, every hash of a run is answered, and the
lemmas give the deployed ones: `gkr_loop10_of_comp`, `gkr_loop11_of_comp`, `gkr_holds_of_comp`
(`gkr_loop10`, `gkr_loop11`, `gkr_holds`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.E2E.Complete

@[expose] public section

section
variable {CM : CompModel} {T : GkrTrace} {μ : ℕ} {cv cv' : Digest} {xs : List E}
  {r : E × List E × List E}

set_option maxRecDepth 100000 in
/-- **`verify_bus_gkr` holds over a completeness model** on a memory holding an answered run's
honest trace and the caller's words, of the run's state, cursor and values. -/
theorem verify_bus_gkr_relC (hT : T.OkM CM.hm μ cv xs r cv') (hμ : μ < 33) {rd : Reader}
    {cur zeta layers rounds pts pb dsb rcy rct1 rct2 : E}
    (hM : GkrMemC CM.hm rd T μ cv cur layers rounds pts pb dsb) (hx : ReadsAt rd cur xs)
    (hz : ReadsAt rd zeta r.2.1) (hrc1 : LoadHolds rd (gen ^ μ) 0 rct1)
    (hrc2 : LoadHolds rd rcy 0 rct2) (hrck : word 4294967296 0 0 = gen ^ μ * rcy) :
    coreProgram.RelB CM.sem rd "verify_bus_gkr"
      [(digestScalars cv).1, (digestScalars cv).2, cur, gen ^ μ, zeta]
      ([(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ xs.length] ++ r.2.2) := by
  rw [relB_iff_sem find_vbg]
  exact ⟨_, by simp only [show Fn.params Data.core10 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl,
      List.map_cons, List.map_nil, vbgσT]; b1_look,
    gkr_holdsC hT hμ hM hx hz hrc1 hrc2 hrck⟩

/-- **`verify_bus_gkr` is complete over a completeness model on an answered run**: the run's
honest trace exists, and on every memory holding its buffers and the caller's words the function
holds of the run's returns. -/
theorem verify_bus_gkr_runC {depth : ℕ} (hrun : RunsToM CM.hm (gkrPhase depth) cv xs r cv')
    (hμ : depth < 33) :
    ∃ T : GkrTrace, T.OkM CM.hm depth cv xs r cv' ∧ ∀ {rd : Reader}
      {cur zeta layers rounds pts pb dsb rcy rct1 rct2 : E},
      GkrMemC CM.hm rd T depth cv cur layers rounds pts pb dsb → ReadsAt rd cur xs →
      ReadsAt rd zeta r.2.1 → LoadHolds rd (gen ^ depth) 0 rct1 → LoadHolds rd rcy 0 rct2 →
      word 4294967296 0 0 = gen ^ depth * rcy →
      coreProgram.RelB CM.sem rd "verify_bus_gkr"
        [(digestScalars cv).1, (digestScalars cv).2, cur, gen ^ depth, zeta]
        ([(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ xs.length] ++ r.2.2) := by
  obtain ⟨T, hT⟩ := exists_traceM hrun
  exact ⟨T, hT, fun hM hx hz h1 h2 h3 => verify_bus_gkr_relC hT hμ hM hx hz h1 h2 h3⟩

end

/-! ## At the deployed model -/

theorem l10cvT_hm_deployed (cvT : Digest) (es : ℕ → E) :
    ∀ i, l10cvT CompModel.deployed.hm cvT es i = l10cv cvT es i
  | 0 => rfl
  | i + 1 => by rw [l10cvT, l10cv, l10cvT_hm_deployed cvT es i]; rfl

theorem l10Ans_hm_deployed (cvT : Digest) (es : ℕ → E) (n : ℕ) :
    L10Ans CompModel.deployed.hm cvT es n := fun _ _ => rfl

theorem oddOkM_of {s s' : GkrState} {cv cv' : Digest} {oes : ℕ → E} (h : OddOk s s' cv cv' oes) :
    OddOkM CompModel.deployed.hm s s' cv cv' oes := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨rfl, l10Ans_hm_deployed _ _ _, rfl, ?_⟩
  simp only [l10cvT_hm_deployed]
  exact ⟨h1, h2, h3, h4⟩

theorem pairOkM_of {s s' : GkrState} {cv cv' : Digest} {ys : List E} {L : ℕ} {cl : ℕ → E}
    {cvr : ℕ → Digest} {wsr : ℕ → List E} {ch es : ℕ → E}
    (h : PairOk s s' cv cv' ys L cl cvr wsr ch es) :
    PairOkM CompModel.deployed.hm s s' cv cv' ys L cl cvr wsr ch es := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨rfl, h1, h2, fun r hr => ⟨(h3 r hr).1, runsToM_hm_deployed.mpr (h3 r hr).2⟩, h4,
    l10Ans_hm_deployed _ _ _, rfl, rfl, ?_⟩
  simp only [l10cvT_hm_deployed]
  exact ⟨h5, h6, h7, h8⟩

theorem GkrTrace.Ok.toM {T : GkrTrace} {μ : ℕ} {cv cv' : Digest} {xs : List E}
    {r : E × List E × List E} (h : T.Ok μ cv xs r cv') : T.OkM CompModel.deployed.hm μ cv xs r cv' :=
  ⟨h.hxs, h.hcnt, rfl, rfl, h.even, fun hs => oddOkM_of (h.odd hs),
    fun i hi => pairOkM_of (h.pair i hi), h.hlen, h.hr, h.hcv⟩

theorem GkrMem.toC {rd : Reader} {T : GkrTrace} {μ : ℕ} {cv : Digest}
    {cur layers rounds pts pb dsb : E} (h : GkrMem rd T μ cv cur layers rounds pts pb dsb) :
    GkrMemC CompModel.deployed.hm rd T μ cv cur layers rounds pts pb dsb :=
  ⟨h.pb, h.ds, h.lay0, h.lay, h.rnd, h.row⟩

section
variable {T : GkrTrace} {μ : ℕ} {cv cv' : Digest} {xs : List E} {r : E × List E × List E}

/-- `__loop10`'s deployed completeness on an honest memory (`gkr_loop10`), from the model's. -/
theorem gkr_loop10_of_comp (hT : T.Ok μ cv xs r cv') (hμ : μ < 33) {rd : Reader}
    {cur layers rounds pts pb dsb : E} (hM : GkrMem rd T μ cv cur layers rounds pts pb dsb)
    (hx : ReadsAt rd cur xs) (hm : 0 < μ / 2) :
    coreProgram.Rel rd "__loop10" [1, gen ^ (μ / 2), dsb, gen ^ μ, layers, rounds] [] := by
  rw [← relB_deployed]
  exact gkr_loop10C (CM := CompModel.deployed) hT.toM hμ hM.toC hx hm

/-- `__loop11`'s deployed completeness on an honest memory (`gkr_loop11`), from the model's. -/
theorem gkr_loop11_of_comp (hT : T.Ok μ cv xs r cv') {rd : Reader}
    {cur layers rounds pts pb dsb zeta : E} (hM : GkrMem rd T μ cv cur layers rounds pts pb dsb)
    (hz : ReadsAt rd zeta r.2.1) (hμ : μ < 33) (hm : 0 < μ) :
    coreProgram.Rel rd "__loop11" [1, gen ^ μ, zeta, pts * gen ^ (40 * (μ % 2 + μ / 2))] [] := by
  rw [← relB_deployed]
  exact gkr_loop11C (CM := CompModel.deployed) hT.toM hM.toC hz hμ hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `verify_bus_gkr`'s body, deployed (`gkr_holds`), from the model's. -/
theorem gkr_holds_of_comp (hT : T.Ok μ cv xs r cv') (hμ : μ < 33) {rd : Reader}
    {cur zeta layers rounds pts pb dsb rcy rct1 rct2 : E}
    (hM : GkrMem rd T μ cv cur layers rounds pts pb dsb) (hx : ReadsAt rd cur xs)
    (hz : ReadsAt rd zeta r.2.1) (hrc1 : LoadHolds rd (gen ^ μ) 0 rct1)
    (hrc2 : LoadHolds rd rcy 0 rct2) (hrck : word 4294967296 0 0 = gen ^ μ * rcy) :
    Stmt.HoldsList (coreProgram.Rel rd) rd (vbgσ zeta (digestScalars cv).1 (digestScalars cv).2 cur
      (gen ^ μ) layers rounds pts pb dsb rcy rct1 rct2 T.cnt⁻¹ T.x0 T.cnt (gen ^ (μ % 2))
      (gen ^ (μ / 2)) (cur * gen ^ gCur (μ % 2) (μ / 2)) (pts * gen ^ (40 * (μ % 2 + μ / 2)))
      ((T.P (μ / 2)).values.getD 0 0) ((T.P (μ / 2)).values.getD 1 0)
      ((T.P (μ / 2)).values.getD 2 0) cv (T.C (μ / 2)) T.oes) (Fn.body Data.core10) False
      (fun rs => rs = [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ xs.length] ++
        r.2.2) := by
  have h := gkr_holdsC (CM := CompModel.deployed) hT.toM hμ hM.toC hx hz hrc1 hrc2 hrck
  rw [show CompModel.deployed.sem = blakeDeployed from rfl, relB_deployed, holdsListB_deployed]
    at h
  exact h

end

end
end LeanVM.Guest.B1.VerifySub
