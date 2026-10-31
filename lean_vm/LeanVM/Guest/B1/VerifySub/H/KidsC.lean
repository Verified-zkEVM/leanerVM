/-
  LeanVM.Guest.B1.VerifySub.H.KidsC

  `verify_sub`'s callees on an honest child are complete, placed: each but the terminal from its
  own completeness theorem on the honest child's data.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Sec
public import LeanVM.Guest.B1.VerifySub.C.Callees

/-!
# The callees, complete

`vsH_tau22`: the `KECCAK` table's height is at most `22` (its slot column's log `τ + 6` is a
committed column's, at most the stack's log `≤ 28`). `kid_complete`: callee `j < 12` (all but the
terminal) is `CompleteAtD` on its words, given `verify_keccak`'s completeness (`VkCompleteAt`) and
`open_stacked`'s frame certificates (`OsFitsAt`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-- **An honest `KECCAK` height is at most `22`.** -/
theorem vsH_tau22 {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {logMem : ℕ}
    {rowsN : List ℕ} (hrl : rowsN.length = 6)
    (h28 : (Tables.layoutOf bytecode logMem rowsN).stackLog ≤ 28) :
    (Tables.tableHeightsOf rowsN).getD 5 0 ≤ 22 := by
  have hsl := tableHeights_length rowsN hrl
  rw [stackLog_eq hbl] at h28
  have hcl : 5 < (Tables.committedKappas (columnKappas logMem Tables.guestLogBytecode
      (Tables.tableHeightsOf rowsN))).length := by
    rw [Tables.committedKappas_length _ (Tables.columnKappas_length _ _ _)]; show 5 < 99; norm_num
  have := Tables.tb_le_log2Ceil_of_two_pow_le (Tables.tb_single_le_sum_map _ 5 hcl)
  have e : ((Tables.committedKappas (columnKappas logMem Tables.guestLogBytecode
      (Tables.tableHeightsOf rowsN))).map (2 ^ ·)).sum =
      Tables.stackTotal (columnKappas logMem 19 (Tables.tableHeightsOf rowsN)) := rfl
  rw [e, Tables.committedKappas_columnKappas logMem _ hsl,
    List.getD_eq_getElem _ _ (by simp; show 5 < 99; norm_num), List.getElem_map, List.getElem_range] at this
  simp [Tables.colKappaSrc, Tables.colKappaAdj] at this
  rw [List.getD_eq_getElem?_getD]
  omega

theorem x_canonical {x0 x1 : E} {root : Digest} (h : digestOfScalars (x0, x1) = some root) :
    IsCanonical128 x0 ∧ IsCanonical128 x1 := by
  unfold digestOfScalars at h
  split at h
  · rename_i hc; exact hc
  · simp at h

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

theorem s6_capOf (hbl : bytecode.length = 2 ^ 23) : S.s6.cap = S.H.s3.squeeze.2.cap := by
  obtain ⟨hok, -, -, -⟩ := S.H_run hbl
  exact (Tables.vt_spec hok).2.2.2

theorem root_cells : (digestScalars S.root) = (S.x0, S.x1) := digestScalars_digestOfScalars S.hroot

end ChildSegs

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`verify_sub`'s callees but the terminal are complete, placed.** -/
theorem kid_complete {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) {κ : ℕ} (hκ : 16 ≤ κ) (hrf : Lift.RunsFit fs cert)
    (hvk : VkCompleteAt fs cert κ)
    (hfits : ∀ μ r, 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 →
      OsFitsAt fs cert (B1.Whir.osCfg (B1.Whir.candidate μ r)))
    (bs : List ℕ) (lpE sqE : ℕ) {j : ℕ} (hj : j < 12) (pv : List (List E × Main.Layout)) :
    CompleteAtD fs cert κ ((S.kids bs lpE sqE).getD j noKid pv).f
      ((S.kids bs lpE sqE).getD j noKid pv).Lin ((S.kids bs lpE sqE).getD j noKid pv).args
      ((S.kids bs lpE sqE).getD j noKid pv).Out := by
  have hμ := S.μ_bounds hbl
  have hτ := S.τ_bounds hbl
  interval_cases j
  · exact gpw_completeAt κ [] (by have := S.hr4; omega)
  · exact gpw_completeAt κ [] (by have := S.h32; omega)
  · refine log2_L0_completeAt κ (by omega) _ lpE sqE (S.pushTotal_lt hbl) ?_
    show max 0 S.μ < 34; omega
  · exact ac_completeAt κ [] (x_canonical S.hroot).1
  · exact ac_completeAt κ [] (x_canonical S.hroot).2
  · obtain ⟨hrun, -, -, -⟩ := S.runG' hbl
    exact Tables.verify_bus_gkr_completeAt (by omega) (by omega) (by omega) hrun S.capS_carries
      (vcG bs) (vb bs 7)
  · obtain ⟨hok, -, -, -⟩ := S.H_run hbl
    exact Tables.verify_tables_completeAt (by omega) hok (S.H_shape hbl) (S.vtB bs sqE)
  · obtain ⟨hrun, -, -, -, hc6⟩ := S.runK' hbl
    have hf : S.s6.cap = capOf S.H.s3.perm := S.s6_capOf hbl
    exact hvk S.τ S.s6.cap S.chis S.outs S.xsK S.op S.kpt S.slices S.s7.cap S.word S.m0
      (S.cK bs) (vb bs 10) (vb bs 0 + 110) (vb bs 11) (vb bs 12) hτ.1 (by omega)
      (by rw [S.chis_length]; exact hτ.2.2) (S.lanes hbl).2.2 (by rw [hf]; rfl)
      (by rw [hf]; exact Tables.tb_capOf_canonical _) hc6 hrun
  · exact rst_completeAt κ (by have := (S.runK' hbl).2.2.2.1; exact this) S.rchs_length
  · exact Tables.certify_placement_completeAt fs cert (by omega) S.hs_length S.h32 (S.hh29 hbl)
      (by have := vsH_tau22 hbl S.hrowsL S.stack28; unfold ChildSegs.hs; omega) _ _
  · have hst : Tables.stackTotal S.kappas ≤ 2 ^ 28 := by
      have h28 := S.stack28
      rw [stackLog_eq hbl] at h28
      exact log2Ceil_le_iff.mp (by
        show log2Ceil (Tables.stackTotal (columnKappas S.logMem 19 (Tables.tableHeightsOf S.rowsN)))
          ≤ 28
        omega)
    refine log2_L15_completeAt κ (by omega) _ lpE sqE (by omega) ?_
    have : log2Ceil (Tables.stackTotal S.kappas) ≤ 28 := log2Ceil_le_iff.mpr hst
    omega
  · exact open_stacked_completeAtD S.μs S.rate S.hmu22 S.hmu28 S.hr1 S.hr4 fs cert κ hrf
      (hfits _ _ S.hmu22 S.hmu28 S.hr1 S.hr4) S.s8.perm S.root S.target _ S.xsW c.proof.openings
      S.w S.s' S.roots' S.runW S.nzW S.capsW [(S.cW bs, S.xsW)]
      (fun rd _ hm ↦ hm _ List.mem_cons_self)

end
end LeanVM.Guest.B1.VerifySub
