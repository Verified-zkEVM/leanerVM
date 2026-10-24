/-
  LeanVM.Guest.B1.VerifySub.H.TermPre

  `check_opening_terminal`'s precondition (`TermPre`) on an honest child, its claims' lengths and
  the WHIR terminal equation.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.TermCtx

/-!
# The terminal's precondition, honestly

`whir_point_length`: an accepted opening's terminal point has `μ` coordinates. `committed_le28`:
an honest child's committed columns' logs are at most `28`. `vsH_hlen`: every honest claim's point
has its column's number of variables. `vsH_fin`: the WHIR terminal equation (`ChildSegs.acc`).
`vsH_termPre`: on a memory holding `certify_placement`'s buffers, `open_stacked`'s points and the
terminal's words of `verify_sub`'s buffers, `TermPre` holds.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

/-- **An accepted opening's terminal point has `μ` coordinates.** -/
theorem whir_point_length {μ r : ℕ} (h1 : 22 ≤ μ) (h2 : μ ≤ 28) (h3 : 1 ≤ r) (h4 : r ≤ 4)
    {S : KState} {root : Digest} {target : E} {xs : List E} {os : List Opening}
    {w : B1.Whir.WhirEnd} {s' : Fs} {roots' : List (Digest × ℕ × ℕ)}
    (hrun : B1.Whir.RunsWith (B1.Whir.whirOpen μ r target) ⟨capOf S, []⟩ xs os
      [(root, B1.Whir.stackShape μ r)] w s' roots')
    (hnz : B1.Whir.NoZeroChallenge μ r target S xs os root) : w.point.length = μ := by
  have hm : B1.Whir.candidate μ r < 28 := by unfold B1.Whir.candidate; omega
  obtain ⟨cfg, hF, -, -⟩ := B1.Whir.candB_sound (B1.Whir.candB_all μ r h1 h2 h3 h4)
  have hs := (placedP_sound (placedP_all _ hm)).2.2.1
  obtain ⟨c0, c2, tr, -, hplen, hptC, -⟩ := B1.Whir.osBodyA_honest hF hs hrun hnz
  unfold B1.Whir.ptC at hptC
  rw [hplen] at hptC
  have := List.append_cancel_right hptC
  rw [← this, hplen]

/-- **An honest child's committed columns' logs are at most `28`.** -/
theorem committed_le28 {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {logMem : ℕ}
    {rowsN : List ℕ} (h28 : (Tables.layoutOf bytecode logMem rowsN).stackLog ≤ 28) :
    ∀ c < Tables.nCommittedCols, (Tables.committedKappas
      (columnKappas logMem Tables.guestLogBytecode (Tables.tableHeightsOf rowsN))).getD c 0 ≤ 28 := by
  rw [stackLog_eq hbl] at h28
  intro c hc
  have hcl : c < (Tables.committedKappas (columnKappas logMem Tables.guestLogBytecode
      (Tables.tableHeightsOf rowsN))).length := by
    rw [Tables.committedKappas_length _ (Tables.columnKappas_length _ _ _)]; exact hc
  have := Tables.tb_le_log2Ceil_of_two_pow_le (Tables.tb_single_le_sum_map _ c hcl)
  have e : ((Tables.committedKappas (columnKappas logMem Tables.guestLogBytecode
      (Tables.tableHeightsOf rowsN))).map (2 ^ ·)).sum =
      Tables.stackTotal (columnKappas logMem 19 (Tables.tableHeightsOf rowsN)) := rfl
  rw [e] at this
  omega

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

theorem km_eq (hbl : bytecode.length = 2 ^ 23) :
    S.km = (([⟨qkeccak, S.op, S.word⟩], S.kpt, S.slices), S.m0) := by
  have h := S.runK
  rw [S.hlayout, (S.lanes hbl).1, (S.lanes hbl).2.1, (S.H_run hbl).2.2.1] at h
  have hτ := S.τ_bounds hbl
  have hil : (S.chis.take S.τ).length = S.τ := by simp [S.chis_length]; omega
  obtain ⟨op', word', hk, -⟩ := keccakSeg_out h (S.runK' hbl).2.2.2.2 (by rw [hil]; omega) hil
  refine Prod.ext (Prod.ext ?_ rfl) rfl
  show S.km.1.1 = [⟨qkeccak, (S.km.1.1.headD default).point, (S.km.1.1.headD default).value⟩]
  rw [hk]; rfl

theorem w_point_length : S.w.point.length = S.μs :=
  whir_point_length S.hmu22 S.hmu28 S.hr1 S.hr4 S.runW S.nzW

/-- **The WHIR terminal equation**, on the honest child. -/
theorem fin (hbl : bytecode.length = 2 ^ 23) :
    (S.w.inner + stackWeight S.layout (openedClaims S.claims [⟨qkeccak, S.op, S.word⟩]) S.kpt
      (ringCoefficients S.rchs) S.lam S.w.point) * S.w.residual = S.w.target := by
  have h := S.acc
  rw [S.km_eq hbl] at h
  exact h

end ChildSegs

end
end LeanVM.Guest.B1.VerifySub
