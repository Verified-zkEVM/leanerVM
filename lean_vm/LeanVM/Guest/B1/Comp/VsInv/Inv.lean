/-
  LeanVM.Guest.B1.Comp.VsInv.Inv

  A deferring verifier accepting over a completeness model's answered hash, within the deployed
  limits, has a run `verify_sub` completes on over the model: its data, its run record of the
  model's answers (`VsRunC.Ans`), the run over the model (`VsData.OkC`) and the tables' context
  (`VsData.TOk`).
-/

module

public import LeanVM.Guest.B1.Comp.VsInv.Tables
public import LeanVM.Guest.B1.Comp.VerifySub.Data
public import LeanVM.Guest.B1.Comp.Whir.StackedInvW

/-!
# The inversion of `verifyDeferredWith` over a completeness model

`vs_inversion` (`Inv6.lean`) over a `CompModel` `CM`: when the deferring verifier over the model's
answered hash accepts `π` for `pi` under `seed` and the claims `c`
(`verifyDeferredWith CM.H bytecode seed pi c π = some true`), with a stack log of at least 22 and
at most 8192 stream words, its run is a `VsData` `D` with a run record `R` of the model's answers
(`R.Ans CM D`: the seed's state, the announced words and the root absorbed, the bus's and the ring
map's squeezes, the batching challenge), within the deployed limits over the model
(`D.OkC CM bytecode R`, its phases' runs `RunsToM CM.hm`, `RunsWithM CM.hm`), with the tables'
context (`D.TOk`), its seed, public input, fixed claims (`R.fresh D = c`) and proof those
(`vs_inversionC`). The proof is `vs_inversion`'s at `RunsM CM.hm` (`VsInv/Run.lean`,
`VsInv/Phases.lean`, `VsInv/Tables.lean`); the chain's squeezes are named state by state
(`sqAllM_states`, `Comp/VerifySub/Bus.lean`), and the opening's point length is the stacked opening's over a total hash the
model agrees with (`whirOpen_point_lengthM`, by `os_whirLevelsOpen_lenW`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.E2E.Complete

@[expose] public section

variable {M : HashModel}

/-- **The terminal point has `μ` coordinates**, over the model (`whirOpen_point_length`): the
opening's run over the model is its run over a total hash the model agrees with. -/
theorem whirOpen_point_lengthM {Ht : Bytes → Digest} (hag : ∀ x d, M.H x = some d → d = Ht x)
    {μ r : ℕ} (hμ1 : 22 ≤ μ) (hμ2 : μ ≤ 28) (hr1 : 1 ≤ r) (hr2 : r ≤ 4)
    {target : E} {cv cv' : Digest} {xs : List E} {os : List Opening}
    {roots roots' : List (Digest × ℕ × ℕ)} {w : WhirEnd}
    (h : RunsWithM M (whirOpen μ r target) cv xs os roots w cv' roots') : w.point.length = μ := by
  have hr := (runsM_runsW hag _ (RunsWithM.runs h [] [])).1
  simp only [whirOpen] at hr
  obtain ⟨cfg, s1, h1, h2⟩ := os_inv_bindW hr
  have hok := osFoldSumOk_window μ (by omega) hμ1 r (by omega) hr1
  unfold osFoldSumOk at hok
  revert h1
  cases hd : deriveConfig μ r with
  | none => intro h1; cases h1
  | some c =>
    intro h1
    rw [hd] at hok
    simp only [Verifier.liftOption] at h1
    obtain ⟨rfl, rfl⟩ := os_inv_retW h1
    obtain ⟨q, s2, -, h3⟩ := os_inv_bindW h2
    exact os_whirLevelsOpen_lenW μ _ _ _ _ _ _ _ h3 (by simpa using hok)

/-- **The inversion over a completeness model**: an accepting deferred verifier over the model's
answered hash, within the deployed limits, runs as a `VsData` with a run record of the model's
answers, within the limits over the model. -/
theorem vs_inversionC {CM : CompModel} {bytecode : List K} (hb : bytecode.length = 2 ^ 22)
    {Ht : Bytes → Digest} (hag : ∀ x d, CM.H x = some d → d = Ht x)
    {seed pi : Digest} {c : FixedClaims} {π : Proof}
    (h : verifyDeferredWith CM.H bytecode seed pi c π = some true)
    (hlo : ∀ layout r, announced bytecode π.stream = some (layout, r) → 22 ≤ layout.stackLog)
    (hst : π.stream.length ≤ 8192) :
    ∃ (D : VsData) (R : VsRunC), R.Ans CM D ∧ D.OkC CM bytecode R ∧ D.TOk bytecode ∧
      D.seed = seed ∧ D.pi = pi ∧ R.fresh D = c ∧ D.proof = π := by
  obtain ⟨cv0, sF, h0, hrun, hsF, hoF⟩ := verifyDeferredWith_inv (M := CM.hm) h
  unfold deferredProgram at hrun
  obtain ⟨u, sE, hE, hret⟩ := RunsM.bind_inv hrun
  obtain ⟨-, rfl⟩ := RunsM.pure_inv hret
  rw [verifyExecution_split] at hE
  obtain ⟨lr, s1, h1, hE⟩ := RunsM.bind_inv hE
  obtain ⟨u2, s2, h2, hE⟩ := RunsM.bind_inv hE
  obtain ⟨alphas, s3, h3, hE⟩ := RunsM.bind_inv hE
  obtain ⟨beta, s4, h4, hE⟩ := RunsM.bind_inv hE
  obtain ⟨gr, s5, h5, hE⟩ := RunsM.bind_inv hE
  obtain ⟨bc, s6, h6, hE⟩ := RunsM.bind_inv hE
  obtain ⟨fl, s7, h7, hE⟩ := RunsM.bind_inv hE
  obtain ⟨rs, s8, h8, h9⟩ := RunsM.bind_inv hE
  have hann := vs_announcedM hb h1
  obtain ⟨logMem, rows, rate, rfl, e1s, e1c, e1o, e1r, hm1, hm2, hr1, hr2, hl, hrows, -, hs28⟩ :=
    vs_readSizes_invM hb h1
  have hs22 := hlo _ _ hann
  obtain ⟨x0, x1, root, hroot, e2s, e2c, e2o, e2r⟩ := vs_commitStack_invM h2
  have hx0 : x0 = (digestScalars root).1 := congrArg Prod.fst hroot
  have hx1 : x1 = (digestScalars root).2 := congrArg Prod.snd hroot
  subst hx0 hx1
  obtain ⟨hq3, hs3⟩ := RunsM.sampleN_inv h3
  rw [show busBits = 4 from rfl] at hq3
  obtain ⟨stB, hB0, hBs, hBe⟩ := sqAllM_states _ _ hq3
  simp only [Prod.mk.injEq] at hBe
  obtain ⟨rfl, hB4⟩ := hBe
  obtain ⟨cB, hcB, rfl, rfl⟩ := RunsM.sampleE_inv h4
  obtain ⟨xsG, e5s, e5o, e5r, hG⟩ := RunsM.qfree (qfree_gkrPhase _) h5
  obtain ⟨hg0, hgl, hgv⟩ := vs_gkr_invM h5
  obtain ⟨xsT, e6s, e6o, e6r, hT⟩ := RunsM.qfree (qfree_tablesSeg _ _ _ _ _ _ _) h6
  obtain ⟨hpt, -⟩ := vs_tables_invM h6
  obtain ⟨xsF, e7s, e7o, e7r, hF⟩ := RunsM.qfree (qfree_verifyFlock _ _) h7
  obtain ⟨zSkip, chi, rc, hfl, hchi, hrc, hsl, hz, hrow, hcol, -⟩ := vs_flock_invM h7
  obtain ⟨mcs, hq8, hs8, rfl⟩ := vs_ringSwitch_invM h8
  obtain ⟨stR, hR0, hRs, hRe⟩ := sqAllM_states _ _ hq8
  simp only [Prod.mk.injEq] at hRe
  obtain ⟨rfl, hR6⟩ := hRe
  unfold verifyStackedOpening at h9
  obtain ⟨lam, s9, h9a, h9⟩ := RunsM.bind_inv h9
  obtain ⟨cL, hcL, rfl, rfl⟩ := RunsM.sampleE_inv h9a
  rw [verifyWhir_split] at h9
  obtain ⟨w, s10, hw, hreq⟩ := RunsM.bind_inv h9
  obtain ⟨hacc, rfl⟩ := RunsM.require_inv hreq
  obtain ⟨xsW, osW, e10s, e10o, hW⟩ := RunsM.frame hw
  obtain ⟨chis, rm, hclen, hcl⟩ := vs_tablesSeg_claimsOkM hb hm1 hl hgl h6
  dsimp only at e1s e1c e1o e1r hann e5s e5o e5r hG e10s e10o hW
  have h8l : flockNumLincheckRounds = 8 := by decide
  have h6k : flockKSkip = 6 := by decide
  rw [h8l] at hfl hrc hrow
  subst hfl
  have e3o : s3.openings = s2.openings := by rw [hs3]
  have e3r : s3.roots = s2.roots := by rw [hs3]
  have e3s : s3.stream = s2.stream := by rw [hs3]
  have e8o : s8.openings = s7.openings := by rw [hs8]
  have e8r : s8.roots = s7.roots := by rw [hs8]
  have e8s : s8.stream = s7.stream := by rw [hs8]
  -- the openings and the roots
  have o9 : π.openings = osW := by
    rw [← List.append_nil osW, ← hoF, ← e10o, e8o, e7o, e6o, e5o, e3o, e2o, e1o]
  have r9 : s8.roots = [(root, stackShape (layoutOf bytecode logMem rows).stackLog rate)] := by
    rw [e8r, e7r, e6r, e5r, e3r, e2r, e1r]; rfl
  rw [← o9, r9] at hW
  -- the stream
  have hstream : π.stream = announce logMem rows rate ++ (digestScalars root).1 ::
      (digestScalars root).2 :: (xsG ++ (xsT ++ (xsF ++ xsW))) := by
    rw [e1s, e2s, ← e3s, e5s, e6s, e7s, ← e8s, e10s, hsF]
    simp
  have hpt' : gr.2.1.take 18 ++ (List.range 4).map (fun k ↦ challengeOf (stB (k + 1))) =
      c.bytecodePoint := by
    rw [← layoutOf_logBytecode hb logMem rows]; exact hpt
  have hlb := layout_bounds hb hl hs28
  refine ⟨⟨seed, pi, logMem, rows, rate, root, xsG, gr, s5.cv, xsT, bc.1, bc.2, s6.cv,
    gen ^ chis.length, c.bytecodeValue, rm, xsF, c.zSkip, c.alpha, c.matrixValue, chi, rc, c.slices,
    s7.cv, xsW, π.openings, w, sF.cv, sF.roots, chis⟩, ⟨cv0, s1.cv, s2.cv, stB, cB, stR, cL⟩,
    ⟨h0, e1c, e2c, hB0, hBs, (show sqCvM CM.hm (stB 4) = some cB by rw [← hB4]; exact hcB), hR0, hRs,
      (show sqCvM CM.hm (stR 6) = some cL by rw [← hR6]; exact hcL)⟩,
    ⟨hm1, hm2, hr1, hr2, hl, hlb.2, hs22, hs28, hlb.1, hG, hgl, hgv, ?_, ?_, ?_, ?_, hrc, hsl, ?_,
      ?_, ?_⟩, ?_, rfl, rfl, ?_, ?_⟩
  · intro ev hev rest os roots
    refine (vs_tables_invM (hT rest os roots)).2 ev ?_
    convert hev using 2
    all_goals first
      | rfl
      | (rw [← hpt']
         simp only [VsRunC.alphas, layoutOf_logBytecode hb])
  · have := congrArg List.length hcl.2.1
    simpa [claimColumns_length] using this
  · intro ev hev rest os roots
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hall⟩ := vs_flock_invM (hF rest os roots)
    exact hall ev (by rw [← hrow, ← hcol]; exact hev)
  · rw [hchi, h6k]
    simp only [VsData.tau, VsData.hs, blake2sR1csLogSize]
    simp [layoutOf, opBlake2s]
    omega
  · convert hW using 3
    all_goals simp [VsRunC.target, VsRunC.lam, VsRunC.mcs, mcsOf, ringSwitchClaim,
      ColumnClaim.onStack, Function.comp_def]
  · exact whirOpen_point_lengthM (M := CM.hm) hag hs22 hs28 hr1 hr2 hW
  · convert hacc using 1
    funext x
    simp only [stackWeight, ringSwitchClaim, List.length_cons, List.map_cons]
    rfl
  · exact VsData.TOk.of_claims hcl rfl (by
      simp only [VsData.stream, VsData.ann, VsData.x0, VsData.x1, VsData.tail]
      rw [← hstream]; exact hst) hclen
  · cases c with
    | mk bp bvv al zs rp cp sl mv =>
      simp only at hpt' hrow hcol
      subst hpt' hrow hcol
      rfl
  · simp only [VsData.proof, VsData.stream, VsData.ann, VsData.x0, VsData.x1, VsData.tail]
    rw [← hstream]

end
end LeanVM.Guest.B1.VerifySub
