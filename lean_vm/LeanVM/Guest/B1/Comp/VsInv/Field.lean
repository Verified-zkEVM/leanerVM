/-
  LeanVM.Guest.B1.Comp.VsInv.Field

  A child's proof accepted over a completeness model has a good run over the model: the
  `vs_inv` field of `B1CompHyps`, and the deployed inversion recovered at the deployed model.
-/

module

public import LeanVM.Guest.B1.Comp.VsInv.Caps
public import LeanVM.Guest.B1.Comp.VerifySub.Assemble
public import LeanVM.Guest.B1.Main.Callees
public import LeanVM.Guest.End
public import LeanVM.Guest.Value.NodeSome

/-!
# The good runs of `verify_sub` over a completeness model

`vs_invC`: the `vs_inv` field of `B1CompHyps CM` (`E2E/Complete/GuestModel.lean`) at any cap
agreement `CapOk` implied by `CapAgreesWith Ht` (the caps over the total hash `Ht` the model
agrees with). From `verifyDeferredWith CM.H End.bytecode seed pi fresh proof = some true`, the
announced stack log within `[22, 28]`, the stream within `Hints.streamCap` and the batches'
agreement over `Ht` (`BatchAgreesWith Ht`) along the deferring verifier's run over `Ht`: the
fixed claims are of the guest's shape (`freshShapedC`), and the run `D` with its run record `R`
of the model's answers is good, `R.Ans CM D ∧ D.OkC CM End.bytecode R ∧ D.TOk End.bytecode ∧
CapOk … R.cvL D.xsW D.os (R.target D)` (`VsGoodC CM CapOk D R`), of the given public input, seed,
fixed claims and proof (`vs_inversionC`, `deferredCapsC`). `vs_invC_capAgreesC` is it at the cap
agreement over the model `CapAgreesC CM`.

**At the deployed model** a run record of the model's answers is the deployed run's on every
value it names (`VsRunC.Ans.eq_ofD`), so a run over the deployed model is a deployed run
(`VsData.OkC.toOk_of_ans`), and `vs_inversion_of_comp` re-derives the deployed `vs_inversion`
from `vs_inversionC`; `vs_invC_deployed` is the field at the deployed model with `CapAgrees` and
the deployed run record `VsRunC.ofD D`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.E2E.Complete

@[expose] public section

/-! ## The fixed claims' shape -/

/-- An accepted run over the model has fixed claims of the guest's shape (`ea_freshShaped`). -/
theorem freshShapedC {CM : CompModel} {bytecode : List K} (hb : bytecode.length = 2 ^ 22)
    {D : VsData} {R : VsRunC} (hok : D.OkC CM bytecode R) : Main.FreshShaped (R.fresh D) := by
  have hd := depth_geC hb hok
  have hc := hok.chi_length
  have hr := hok.rcs_length
  have hs := hok.s_length
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (D.gr.2.1.take 18 ++ R.alphas).length = 22
    simp only [List.length_append, List.length_take, VsRunC.alphas_length]
    omega
  · show (D.chi.take 8).length = 8
    simp only [List.length_take]; omega
  · show D.rcs.reverse.length = 8
    simp only [List.length_reverse]; omega
  · exact hs

/-! ## The field -/

/-- **A child's accepted proof has a good run over the model** (the `vs_inv` field of
`B1CompHyps CM`, its good runs `VsGoodC CM CapOk` unfolded), at every cap agreement `CapOk` the
caps' agreement over `Ht` implies. -/
theorem vs_invC (CM : CompModel) (CapOk : ℕ → ℕ → Digest → Digest → List E → List Opening → E → Prop)
    (Ht : Bytes → Digest) (hag : ∀ x d, CM.H x = some d → d = Ht x)
    (hcap : ∀ μ r root cv xs os target, CapAgreesWith Ht μ r root cv xs os target →
      CapOk μ r root cv xs os target)
    (seed pi : Digest) (fresh : FixedClaims) (proof : Proof)
    (hlo : ∀ layout r, announced End.bytecode proof.stream = some (layout, r) →
      22 ≤ layout.stackLog ∧ layout.stackLog ≤ 28)
    (hst : proof.stream.length ≤ Hints.streamCap)
    (hver : verifyDeferredWith CM.H End.bytecode seed pi fresh proof = some true)
    (hbat : ∀ b ∈ queriesOfWith Ht (deferredProgram fresh End.bytecode pi)
        ⟨Ht (digestBytes seed ++ digestBytes pi), proof.stream, proof.openings, []⟩,
      BatchAgreesWith Ht b.1 b.2) :
    Main.FreshShaped fresh ∧ ∃ (D : VsData) (R : VsRunC),
      (R.Ans CM D ∧ D.OkC CM End.bytecode R ∧ D.TOk End.bytecode ∧
        CapOk (layoutOf End.bytecode D.logMem D.rows).stackLog D.rate D.root R.cvL D.xsW D.os
          (R.target D)) ∧
      D.pi = pi ∧ D.seed = seed ∧ R.fresh D = fresh ∧ D.proof = proof := by
  obtain ⟨D, R, hR, hok, htok, rfl, rfl, hfr, hpf⟩ := vs_inversionC End.bytecode_length hag hver
    (fun layout r h => (hlo layout r h).1) hst
  refine ⟨hfr ▸ freshShapedC End.bytecode_length hok, D, R, ⟨hR, hok, htok, hcap _ _ _ _ _ _ _ ?_⟩,
    rfl, rfl, hfr, hpf⟩
  refine deferredCapsC End.bytecode_length hag hR hok ?_
  rw [hfr]
  subst hpf
  exact hbat

/-- **The field at the caps' agreement over the model** (`CapAgreesC CM`). -/
theorem vs_invC_capAgreesC (CM : CompModel) (Ht : Bytes → Digest)
    (hag : ∀ x d, CM.H x = some d → d = Ht x) (seed pi : Digest) (fresh : FixedClaims)
    (proof : Proof)
    (hlo : ∀ layout r, announced End.bytecode proof.stream = some (layout, r) →
      22 ≤ layout.stackLog ∧ layout.stackLog ≤ 28)
    (hst : proof.stream.length ≤ Hints.streamCap)
    (hver : verifyDeferredWith CM.H End.bytecode seed pi fresh proof = some true)
    (hbat : ∀ b ∈ queriesOfWith Ht (deferredProgram fresh End.bytecode pi)
        ⟨Ht (digestBytes seed ++ digestBytes pi), proof.stream, proof.openings, []⟩,
      BatchAgreesWith Ht b.1 b.2) :
    Main.FreshShaped fresh ∧ ∃ (D : VsData) (R : VsRunC),
      (R.Ans CM D ∧ D.OkC CM End.bytecode R ∧ D.TOk End.bytecode ∧
        CapAgreesC CM (layoutOf End.bytecode D.logMem D.rows).stackLog D.rate D.root R.cvL D.xsW
          D.os (R.target D)) ∧
      D.pi = pi ∧ D.seed = seed ∧ R.fresh D = fresh ∧ D.proof = proof :=
  vs_invC CM (CapAgreesC CM) Ht hag (fun _ _ _ _ _ _ _ h => ⟨Ht, hag, h⟩) seed pi fresh proof hlo hst
    hver hbat

/-! ## At the deployed model -/

/-- **A run record of the deployed model's answers is the deployed run's** on every value it
names. -/
theorem VsRunC.Ans.eq_ofD {D : VsData} {R : VsRunC} (hR : R.Ans CompModel.deployed D) :
    R.alphas = D.alphas ∧ R.cvB = D.cvB ∧ R.mcs = D.mcs ∧ R.cvL = D.cvL := by
  have h0 := VsRunC.ans_ofD D
  have e0 : R.cv0 = D.cv0 := Option.some.inj (hR.cv0.symm.trans h0.cv0)
  have eA : R.cvA = obsAll D.cv0 D.ann := by
    have := hR.cvA
    rw [e0, obsAllM_hm_deployed] at this
    exact (Option.some.inj this).symm
  have e10 : R.cv10 = D.cv10 := by
    have := hR.cv10
    rw [eA, obsAllM_hm_deployed] at this
    exact (Option.some.inj this).symm
  have eB : ∀ k ≤ 4, R.stB k = sqCv^[k] D.cv10 := by
    intro k hk
    induction k with
    | zero => rw [hR.stB0, e10]; rfl
    | succ k ih =>
      have := hR.stB k (by omega)
      rw [ih (by omega), sqCvM_iterate_deployed] at this
      exact (Option.some.inj this).symm
  have eR : ∀ k ≤ 6, R.stR k = sqCv^[k] D.cvF := by
    intro k hk
    induction k with
    | zero => rw [hR.stR0]; rfl
    | succ k ih =>
      have := hR.stR k (by omega)
      rw [ih (by omega), sqCvM_iterate_deployed] at this
      exact (Option.some.inj this).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← VsRunC.alphas_ofD]
    simp only [VsRunC.alphas, VsRunC.ofD]
    refine List.map_congr_left fun k hk => ?_
    rw [eB (k + 1) (by simp at hk; omega)]
  · have := hR.cvB
    rw [eB 4 le_rfl] at this
    exact Option.some.inj (this.symm.trans h0.cvB)
  · rw [← VsRunC.mcs_ofD]
    simp only [VsRunC.mcs, mcsOf, VsRunC.ofD]
    refine List.map_congr_left fun k hk => ?_
    rw [eR (k + 1) (by simp at hk; omega)]
  · have := hR.cvL
    rw [eR 6 le_rfl] at this
    exact Option.some.inj (this.symm.trans h0.cvL)

/-- **A run over the deployed model is a deployed run.** -/
theorem VsData.OkC.toOk_of_ans {bytecode : List K} {D : VsData} {R : VsRunC}
    (hR : R.Ans CompModel.deployed D) (hok : D.OkC CompModel.deployed bytecode R) : D.Ok bytecode := by
  obtain ⟨ea, eB, em, eL⟩ := hR.eq_ofD
  have elam : R.lam = D.lam := by simp only [VsRunC.lam, VsData.lam, eL]
  have et : R.target D = D.target := by simp only [VsRunC.target, VsData.target, elam, em]
  have eb : R.beta = D.beta := by simp only [VsRunC.beta, VsData.beta, eB]
  exact
  { logMem_ge := hok.logMem_ge
    logMem_le := hok.logMem_le
    rate_ge := hok.rate_ge
    rate_le := hok.rate_le
    rows_length := hok.rows_length
    rows_log := hok.rows_log
    stack_ge := hok.stack_ge
    stack_le := hok.stack_le
    depth_lt := hok.depth_lt
    gkr := by rw [← eB]; exact runsToM_hm_deployed.mp hok.gkr
    point_length := hok.point_length
    values_length := hok.values_length
    tables := fun ev h => by
      rw [← ea, ← eb]
      exact runsToM_hm_deployed.mp (hok.tables ev (by rw [ea]; exact bytecodeAtM_deployed.mpr h))
    claims_length := hok.claims_length
    flock := fun ev h => runsToM_hm_deployed.mp (hok.flock ev (matricesAtM_deployed.mpr h))
    chi_length := hok.chi_length
    rcs_length := hok.rcs_length
    s_length := hok.s_length
    opening := by rw [← et, ← eL]; exact runsWithM_deployed.mp hok.opening
    open_point := hok.open_point
    accepts := by rw [← em, ← elam]; exact hok.accepts }

/-- **The deployed inversion, re-derived from the model's** (`vs_inversion` from `vs_inversionC`
at `CompModel.deployed`). -/
theorem vs_inversion_of_comp {bytecode : List K} (hb : bytecode.length = 2 ^ 22)
    {seed pi : Digest} {c : FixedClaims} {π : Proof} (h : verifyDeferred bytecode seed pi c π = true)
    (hlo : ∀ layout r, announced bytecode π.stream = some (layout, r) → 22 ≤ layout.stackLog)
    (hst : π.stream.length ≤ 8192) :
    ∃ D : VsData, D.Ok bytecode ∧ D.TOk bytecode ∧ D.seed = seed ∧ D.pi = pi ∧ D.fresh = c ∧
      D.proof = π := by
  have hv : verifyDeferredWith CompModel.deployed.H bytecode seed pi c π = some true := by
    rw [show CompModel.deployed.H = Value.someBlake from rfl, Value.verifyDeferredWith_some, h]
  obtain ⟨D, R, hR, hok, htok, hseed, hpi, hfr, hpf⟩ :=
    vs_inversionC (CM := CompModel.deployed) (Ht := blake2sBytes) hb
      (fun x d h => (Option.some.inj h).symm) hv hlo hst
  refine ⟨D, hok.toOk_of_ans hR, htok, hseed, hpi, ?_, hpf⟩
  rw [← hfr]
  simp only [VsRunC.fresh, VsData.fresh, hR.eq_ofD.1]

/-- **The field at the deployed model**: `CapAgrees` and the deployed run record `VsRunC.ofD D`,
from `vs_invC`. -/
theorem vs_invC_deployed (seed pi : Digest) (fresh : FixedClaims) (proof : Proof)
    (hlo : ∀ layout r, announced End.bytecode proof.stream = some (layout, r) →
      22 ≤ layout.stackLog ∧ layout.stackLog ≤ 28)
    (hst : proof.stream.length ≤ Hints.streamCap)
    (hver : verifyDeferredWith CompModel.deployed.H End.bytecode seed pi fresh proof = some true)
    (hbat : ∀ b ∈ queriesOfWith blake2sBytes (deferredProgram fresh End.bytecode pi)
        ⟨blake2sBytes (digestBytes seed ++ digestBytes pi), proof.stream, proof.openings, []⟩,
      BatchAgreesWith blake2sBytes b.1 b.2) :
    Main.FreshShaped fresh ∧ ∃ D : VsData,
      (VsRunC.Ans CompModel.deployed D (VsRunC.ofD D) ∧
        D.OkC CompModel.deployed End.bytecode (VsRunC.ofD D) ∧ D.TOk End.bytecode ∧
        CapAgrees (layoutOf End.bytecode D.logMem D.rows).stackLog D.rate D.root
          (VsRunC.ofD D).cvL D.xsW D.os ((VsRunC.ofD D).target D)) ∧
      D.pi = pi ∧ D.seed = seed ∧ (VsRunC.ofD D).fresh D = fresh ∧ D.proof = proof := by
  obtain ⟨hfs, D, R, ⟨hR, hok, htok, hcap⟩, hpi, hseed, hfr, hpf⟩ :=
    vs_invC CompModel.deployed (CapAgreesWith blake2sBytes) blake2sBytes
      (fun x d h => (Option.some.inj h).symm) (fun _ _ _ _ _ _ _ h => h) seed pi fresh proof hlo hst
      hver hbat
  obtain ⟨ea, -, em, eL⟩ := hR.eq_ofD
  have et : R.target D = D.target := by simp only [VsRunC.target, VsData.target, VsRunC.lam,
    VsData.lam, eL, em]
  refine ⟨hfs, D, ⟨VsRunC.ans_ofD D, (hok.toOk_of_ans hR).toOkC, htok, ?_⟩, hpi, hseed, ?_, hpf⟩
  · rw [VsRunC.cvL_ofD, VsRunC.target_ofD, ← eL, ← et]
    exact (capAgreesWith_blake2s _ _ _ _ _ _ _).mp hcap
  · rw [VsRunC.fresh_ofD, ← hfr]
    simp only [VsRunC.fresh, VsData.fresh, ea]

end
end LeanVM.Guest.B1.VerifySub
