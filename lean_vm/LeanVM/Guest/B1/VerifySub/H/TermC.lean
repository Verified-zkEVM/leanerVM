/-
  LeanVM.Guest.B1.VerifySub.H.TermC

  `check_opening_terminal` on an honest child: its precondition on the honest memory, and its
  placed completeness as `verify_sub`'s thirteenth callee.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.TermPre

/-!
# The terminal, honestly

`ChildSegs.termB`: the terminal's buffers (`zeta`, `chi`, `claim_cplen_g`, `lam_pool`,
`certify_placement`'s offsets and logs, `z_vals`, `c_table`, `open_stacked`'s points).
`vsH_termPre`: on a memory holding `certify_placement`'s buffers, `open_stacked`'s points and the
terminal's words of `verify_sub`'s buffers, `TermPre` holds of the honest child.
`term_complete`: the terminal, entered on what `certify_placement` and `open_stacked` return, is
`CompleteAtD`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

theorem readsAt_left {rd : Reader} {p : E} {xs ys : List E} (h : ReadsAt rd p (xs ++ ys)) :
    ReadsAt rd p xs := (Main.readsAt_append'.mp h).1

/-- The terminal's buffers. -/
def vsTermB (bs : List ℕ) (e2 e121 pb pb1 : ℕ) : TermBases :=
  ⟨vb bs 7, vb bs 10, vb bs 1, vb bs 15, e121, e2, vb bs 11, vb bs 14, pb, pb1⟩

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

theorem lamW_get (j : ℕ) (hj : j < 165)
    (hn : Tables.claimColumns.getD j 0 ∉ keccakOutputColumns) :
    (lamW S.lam).getD j 0 = S.lam ^ (1 + poolRank j) := by
  rw [lamW, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]
  simp only [hn, ↓reduceIte]

end ChildSegs

set_option maxHeartbeats 4000000 in
/-- **The terminal's precondition on an honest child.** -/
theorem vsH_termPre {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) (bs : List ℕ) {rd : Reader} {e2 e120 e121 pb pb1 : ℕ}
    (hcpo : Main.MemL rd (Tables.cpOwn S.logMem S.hs e2 e120 e121))
    (hpt : ReadsAt rd (ofK (gpow pb)) (S.w.point ++ List.replicate (B1.Whir.pointCap - S.μs) 0))
    (hpt1 : ReadsAt rd (ofK (gpow pb1))
      (S.w.point.map (1 + ·) ++ List.replicate (B1.Whir.pointCap - S.μs) 1))
    (ht : Main.MemL rd (S.termLin bs)) :
    TermPre rd S.layout S.bus S.claims ⟨qkeccak, S.op, S.word⟩ S.lam S.kpt (ringCoefficients S.rchs)
      S.w.point (termArgs (vsTermB bs e2 e121 pb pb1) S.H.rm (gen ^ S.μ) (gen ^ S.H.n)
        (gen ^ S.logMem) (gen ^ S.τ) (S.lam ^ 141) S.w.inner S.w.residual S.w.target) := by
  obtain ⟨hok, -, -, -⟩ := S.H_run hbl
  have hsh := S.H_shape hbl
  have hpl := (S.runG' hbl).2.2.1
  have hμ := S.μ_bounds hbl
  have hτ := S.τ_bounds hbl
  obtain ⟨-, hopl, hkpl, -, -⟩ := S.runK' hbl
  have hwl : S.w.point.length = S.layout.stackLog := S.w_point_length
  -- the terminal's words
  have hm : ∀ q ∈ S.termLin bs, ReadsAt rd (ofK (gpow q.1)) q.2 := ht
  have mZ : ReadsAt rd (ofK (gpow (vb bs 7))) S.point := hm (vb bs 7, S.point) (by simp [ChildSegs.termLin])
  have mC : ReadsAt rd (ofK (gpow (vb bs 10))) S.chis := hm (vb bs 10, S.chis) (by simp [ChildSegs.termLin])
  have mP : ReadsAt rd (ofK (gpow (vb bs 1))) S.H.cplenW := hm (vb bs 1, S.H.cplenW) (by simp [ChildSegs.termLin])
  have mL : ReadsAt rd (ofK (gpow (vb bs 15))) (lamW S.lam) := hm (vb bs 15, lamW S.lam) (by simp [ChildSegs.termLin])
  have mV : ReadsAt rd (ofK (gpow (vb bs 11))) (zvW S.op S.kpt) := hm (vb bs 11, zvW S.op S.kpt) (by simp [ChildSegs.termLin])
  have mT : ReadsAt rd (ofK (gpow (vb bs 14))) (ringCoefficients S.rchs) :=
    hm (vb bs 14, ringCoefficients S.rchs) (by simp [ChildSegs.termLin])
  -- `z_vals`
  have hopl39 : S.op.length ≤ 39 := by omega
  have mV' := Main.readsAt_append'.mp mV
  have mOp : ReadsAt rd (ofK (gpow (vb bs 11))) S.op := readsAt_left mV'.1
  have mKp : ReadsAt rd (ofK (gpow (vb bs 11)) * gen ^ qkeccakVarsCap) S.kpt := by
    have := mV'.2
    rwa [List.length_append, List.length_replicate, show S.op.length + (39 - S.op.length) = 39 by
      omega] at this
  -- `certify_placement`'s buffers
  have hcpOut : Tables.cpOut S.logMem S.hs
      [gen ^ Tables.stackTotal (columnKappas S.logMem Tables.guestLogBytecode S.hs),
        ofK (gpow e121), ofK (gpow e2)] (Tables.cpOwn S.logMem S.hs e2 e120 e121) :=
    ⟨e2, e120, e121, rfl, rfl⟩
  have hP := Tables.cp_out_ctx hcpOut hcpo
  have mK : ReadsAt rd (ofK (gpow e2)) ((Tables.cpKs S.logMem S.hs).map (gen ^ ·)) :=
    hcpo (e2, (Tables.cpKs S.logMem S.hs).map (gen ^ ·)) (by simp [Tables.cpOwn])
  have hK28 := committed_le28 hbl S.stack28
  -- the bus point
  have hbus : S.bus = S.H.busH := (Tables.vt_spec hok).2.1
  have hbp : S.bus.point = S.point := by rw [hbus]; rfl
  have hct := Tables.VtHonest.vtH_tctx hok hsh mZ mC mP
  rw [ChildSegs.H_point, hpl] at hct
  rw [S.hlayout] at hwl ⊢
  simp only [TermPre, termArgs, vsTermB]
  refine ⟨hct, ?_, fun c hc ↦ ?_, rfl, rfl, S.stack28, by show 1 ≤ S.logMem; have := S.h16; omega,
    S.h32, by rw [hbp, hpl]; omega, S.hs_length, S.hh29 hbl, rfl, rfl, fun j hj hn ↦ ?_,
    by rw [poolRank_end], trivial, by rw [hopl, Tables.qkeccakSlotBits_eq]; rfl, mOp,
    by rw [hkpl, Tables.qkeccakSlotBits_eq]; rfl, mKp, by simp [ringCoefficients, kBits],
    mT, hwl, ?_, ?_⟩
  · rw [logBytecode_eq hbl]; exact hP
  · obtain ⟨k, hk, hl⟩ : ∃ k, k = (Tables.cpKs S.logMem S.hs).getD c 0 ∧
        LoadHolds rd (ofK (gpow e2)) c (gen ^ k) := by
      refine ⟨_, rfl, ?_⟩
      have hcl : c < (Tables.cpKs S.logMem S.hs).length := by
        rw [Tables.cpKs, Tables.committedKappas_length _ (Tables.columnKappas_length _ _ _)]
        exact hc
      have := mK c (by simpa using hcl)
      rwa [List.getElem_map, ← List.getD_eq_getElem _ 0 hcl] at this
    refine ⟨k, ?_, hl⟩
    rw [hk]
    show (Tables.committedKappas (columnKappas S.logMem Tables.guestLogBytecode
      (Tables.tableHeightsOf S.rowsN))).getD c 0 < 29
    have := hK28 c hc
    omega
  · have := readsAt_getD' mL (k := j) (by rw [lamW_length]; exact hj)
    rwa [S.lamW_get j hj hn] at this
  · unfold padPoint
    rw [hwl, show termPointCap = B1.Whir.pointCap from rfl]
    rw [← S.hlayout]; exact hpt
  · unfold padPoint
    rw [hwl, show termPointCap = B1.Whir.pointCap from rfl, List.map_append, List.map_replicate,
      add_zero]
    rw [← S.hlayout]; exact hpt1

theorem regionL_of {L : Main.Layout} {q : ℕ × List E} (hq : q ∈ L) {i : ℕ} (h1 : q.1 ≤ i)
    (h2 : i < q.1 + q.2.length) : Main.RegionL L i := ⟨q, hq, h1, h2⟩

variable {fs : String → ℕ} {cert : String → V → ℕ}

set_option maxHeartbeats 4000000 in
/-- **The terminal is complete on an honest child**, entered on what `certify_placement` and
`open_stacked` return. -/
theorem term_complete {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) {κ : ℕ} (hκ : 16 ≤ κ) (bs : List ℕ) (lpE sqE : ℕ)
    (pv : List (List E × Main.Layout))
    (ht : ((S.kids bs lpE sqE).getD 12 noKid pv).taken = true) :
    CompleteAtD fs cert κ ((S.kids bs lpE sqE).getD 12 noKid pv).f
      ((S.kids bs lpE sqE).getD 12 noKid pv).Lin ((S.kids bs lpE sqE).getD 12 noKid pv).args
      ((S.kids bs lpE sqE).getD 12 noKid pv).Out := by
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
  show CompleteAtD fs cert κ "check_opening_terminal" _ _ (Returns [])
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
  refine check_opening_terminal_completeAt κ (by omega) (vsTermB bs e2 e121 pb pb1) _
    (layout := S.layout) (bus := S.bus) (claims := S.claims) (out := ⟨qkeccak, S.op, S.word⟩)
    (lam := S.lam) (ringPoint := S.kpt) (coeffs := ringCoefficients S.rchs) (x := S.w.point)
    (nc := S.H.n) (by
      obtain ⟨t, ht, e⟩ := Tables.vt_n_ex hsh.hr
      have := hsh.hτ29 t ht
      unfold Tables.VtHonest.τ at e
      omega)
    rfl (fun rd _ hm ↦ ?_) (fun i hi ↦ ?_) (by rw [hbp, hpl]; omega) ?_ (S.fin hbl)
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
