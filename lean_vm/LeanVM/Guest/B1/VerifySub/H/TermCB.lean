/-
  LeanVM.Guest.B1.VerifySub.H.TermCB

  `check_opening_terminal` as `verify_sub`'s thirteenth callee on an honest child, within a bound.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.TermC
public import LeanVM.Guest.B1.Terminal.TermCompleteB

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-- The terminal's bound (`check_opening_terminal_completeAtB`'s). -/
def termBound (fs : String → ℕ) (Beqc K15 Bcs Brs : ℕ) : ℕ :=
  fs "check_opening_terminal" + 146 + 3 * Beqc + max (fs "__loop15") (32 * K15) +
    (fs "selector_tables" + 322) + 99 * Bcs + (fs "ring_switch_weight" + 2240 + Brs)

variable {fs : String → ℕ} {cert : String → V → ℕ}

set_option maxHeartbeats 4000000 in
/-- **The terminal is complete on an honest child within `termBound`**, entered on what
`certify_placement` and `open_stacked` return, its pure callees' words by hypotheses. -/
theorem term_completeB {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) {κ : ℕ} (hκ : 16 ≤ κ) (bs : List ℕ) (lpE sqE : ℕ)
    (pv : List (List E × Main.Layout))
    (ht : ((S.kids bs lpE sqE).getD 12 noKid pv).taken = true)
    {Beqc K15 Bcs Brs : ℕ} (hEqc : TotalLe coreProgram fs "eq_prefix_chain" fun _ => Beqc)
    (hL15 : TotalLeOn coreProgram fs "__loop15" LoopPre fun a => logG (a.getD 1 0) * K15)
    (hCs : ∀ κ' < 29, TotalLe coreProgram fs (Tables.lName "column_selector" κ') fun _ => Bcs)
    (hCsF : ∀ κ' < 29, fs (Tables.lName "column_selector" κ') ≤ Bcs)
    (hrs : ∀ c ≤ 34, TotalLeOn coreProgram fs "rs_eq_run" (fun a => a.getD 3 0 = gen ^ c)
      fun _ => Brs) :
    CompleteAtB fs cert κ ((S.kids bs lpE sqE).getD 12 noKid pv).f
      ((S.kids bs lpE sqE).getD 12 noKid pv).Lin ((S.kids bs lpE sqE).getD 12 noKid pv).args
      ((S.kids bs lpE sqE).getD 12 noKid pv).Out (termBound fs Beqc K15 Bcs Brs) := by
  have hok : S.termOk pv := @of_decide_eq_true _ (Classical.propDecidable _) ht
  have hLin : ((S.kids bs lpE sqE).getD 12 noKid pv).Lin =
      (ChildSegs.cpRes pv).2 ++ (ChildSegs.osRes pv).2 ++ S.termLin bs := by
    show @ite _ _ (Classical.propDecidable _) _ _ = _
    rw [@ite_pos' _ _ (Classical.propDecidable _) _ _ hok]
  obtain ⟨⟨e2, e120, e121, hr9, hL9⟩, ⟨pb, pb1, hr11, hL11⟩⟩ := hok
  have hargs : ((S.kids bs lpE sqE).getD 12 noKid pv).args =
      termArgs (vsTermB bs e2 e121 pb pb1) S.H.rm (gen ^ S.μ) (gen ^ S.H.n) (gen ^ S.logMem)
        (gen ^ S.τ) (S.lam ^ 141) S.w.inner S.w.residual S.w.target := by
    show [_, _, _, _, _, _, _, _, _, _, (ChildSegs.cpRes pv).1.getD 1 0,
      (ChildSegs.cpRes pv).1.getD 2 0, _, _, (ChildSegs.osRes pv).1.getD 1 0,
      (ChildSegs.osRes pv).1.getD 2 0, (ChildSegs.osRes pv).1.getD 3 0,
      (ChildSegs.osRes pv).1.getD 4 0, (ChildSegs.osRes pv).1.getD 0 0] = _
    rw [hr9, hr11]
    rfl
  rw [hLin, hargs, hL9, hL11]
  show CompleteAtB fs cert κ "check_opening_terminal" _ _ (Returns []) _
  have hμ := S.μ_bounds hbl
  have hpl := (S.runG' hbl).2.2.1
  obtain ⟨hok', -, -, -⟩ := S.H_run hbl
  have hsh := S.H_shape hbl
  have hbus : S.bus = S.H.busH := (Tables.vt_spec hok').2.1
  have hbp : S.bus.point = S.point := by rw [hbus]; rfl
  have hτ := S.τ_bounds hbl
  obtain ⟨-, hopl, hkpl, -, -⟩ := S.runK' hbl
  have hwl := S.w_point_length
  have hμs : S.μs ≤ 28 := S.hmu28
  refine check_opening_terminal_completeAtB κ (by omega) (vsTermB bs e2 e121 pb pb1) _
    (layout := S.layout) (bus := S.bus) (claims := S.claims) (out := ⟨qkeccak, S.op, S.word⟩)
    (lam := S.lam) (ringPoint := S.kpt) (coeffs := ringCoefficients S.rchs) (x := S.w.point)
    (nc := S.H.n) (by
      obtain ⟨t, ht, e⟩ := Tables.vt_n_ex hsh.hr
      have := hsh.hτ29 t ht
      unfold Tables.VtHonest.τ at e
      omega)
    rfl (fun rd _ hm ↦ ?_) (fun i hi ↦ ?_) (by rw [hbp, hpl]; omega) ?_ (S.fin hbl) hEqc hL15 hCs hCsF hrs
  · obtain ⟨h12, hT⟩ := Main.memL_append.mp hm
    obtain ⟨hC, hO⟩ := Main.memL_append.mp h12
    exact vsH_termPre hbl S bs hC
      (hO (pb, S.w.point ++ List.replicate (B1.Whir.pointCap - S.μs) 0) (by simp))
      (hO (pb1, S.w.point.map (1 + ·) ++ List.replicate (B1.Whir.pointCap - S.μs) 1) (by simp)) hT
  · have hτl : S.layout.tableLogHeights.getD opKeccak 0 = S.τ := by rw [S.hlayout]; rfl
    simp only [TermRegion, vsTermB, hbp, hpl, hτl] at hi
    have hcl : S.chis.length = S.H.n := S.chis_length
    have hzl : (zvW S.op S.kpt).length = 39 + (S.τ + 6) := by
      simp [zvW, hopl, hkpl]; omega
    rcases hi with h | h | h | h | h | h | h | h | h | h | h
    · exact regionL_of (q := (vb bs 7, S.point)) (by simp [ChildSegs.termLin]) h.1 (by simp [hpl]; omega)
    · exact regionL_of (q := (vb bs 10, S.chis)) (by simp [ChildSegs.termLin]) h.1 (by simp [hcl]; omega)
    · exact regionL_of (q := (vb bs 1, S.H.cplenW)) (by simp [ChildSegs.termLin]) h.1
        (by simp [Tables.VtHonest.cplenW]; omega)
    · exact regionL_of (q := (vb bs 15, lamW S.lam)) (by simp [ChildSegs.termLin]) h.1
        (by simp [lamW_length]; omega)
    · exact regionL_of (q := (e121, (stackOffsets (Tables.cpKs S.logMem S.hs)).1.map (gen ^ ·)))
        (by simp [Tables.cpOwn]) h.1
        (by simp [Tables.tb_stackOffsets_length, Tables.cpKs_length]; omega)
    · exact regionL_of (q := (e2, (Tables.cpKs S.logMem S.hs).map (gen ^ ·)))
        (by simp [Tables.cpOwn]) h.1 (by simp [Tables.cpKs_length]; omega)
    · exact regionL_of (q := (vb bs 11, zvW S.op S.kpt)) (by simp [ChildSegs.termLin]) h.1
        (by rw [hzl]; omega)
    · exact regionL_of (q := (vb bs 11, zvW S.op S.kpt)) (by simp [ChildSegs.termLin]) (by omega)
        (by rw [hzl]; omega)
    · exact regionL_of (q := (vb bs 14, ringCoefficients S.rchs)) (by simp [ChildSegs.termLin]) h.1
        (by simp [ringCoefficients, kBits]; omega)
    · exact regionL_of (q := (pb, S.w.point ++ List.replicate (B1.Whir.pointCap - S.μs) 0))
        (by simp) h.1 (by simp [hwl, B1.Whir.pointCap]; omega)
    · exact regionL_of (q := (pb1, S.w.point.map (1 + ·) ++ List.replicate (B1.Whir.pointCap - S.μs) 1))
        (by simp) h.1 (by simp [hwl, B1.Whir.pointCap]; omega)
  · have := Tables.VtHonest.vtH_hlen hok' hsh (by show 1 ≤ S.logMem; have := S.h16; omega)
    rw [S.hlayout]
    exact this

end
end LeanVM.Guest.B1.VerifySub
