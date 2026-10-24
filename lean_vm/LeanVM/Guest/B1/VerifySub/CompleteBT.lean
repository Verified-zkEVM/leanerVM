/-
  LeanVM.Guest.B1.VerifySub.CompleteBT

  `verify_sub` complete within its child's bound by a node whose callees are calls of their names
  within their bounds (`Budget.FlatShape`), `open_stacked` at the child's announced shape.
-/

module

public import LeanVM.Guest.B1.VerifySub.CompleteAll
public import LeanVM.Guest.B1.Terminal.KidsDepBP
public import LeanVM.Guest.ChildShape

/-!
# `verify_sub` by its callees' trees

`vsNames μ r`: the thirteen callees in call order (`vs_calls`), `open_stacked`'s candidate
`openName μ r`. `vsTs fs W Bvk μ r`: callee `j` a call of `vsNames μ r`'s `j`-th name within
`vsBsAt W Bvk μ r`'s `j`-th bound, `verify_tables`' and the terminal's within their weights at each
opcode (`vsPs W`: `vtWB`, `termWB`). `vsBoundAt W Bvk μ r = fs "verify_sub" + 9156 +
(vsBsAt W Bvk μ r).sum`. `vs_kidsDepBP`: the callees on an honest child, each within its bound by
a tree of its predicate.

`verify_sub_completeBT`: `verify_sub_completeB` within the child's own bound (its announced stack
log and rate, `childShape`), by a node of `Budget.FlatShape` for `vsTs`. `verify_sub_completeBT_fs`:
at `B2C.fs`, `verify_keccak` within `vkBound`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-- **`verify_sub`'s callees' names**, in call order (`vs_calls`). -/
def vsNames (μ r : ℕ) : List String :=
  ["g_power_of_word", "g_power_of_word", "log2_ceil_in_the_exponent__L0_L34", "assert_canonical",
    "assert_canonical", "verify_bus_gkr", "verify_tables", "verify_keccak", "ring_switch_target",
    "certify_placement", "log2_ceil_in_the_exponent__L15_L34", B1.Whir.openName μ r,
    "check_opening_terminal"]

/-- **`verify_sub`'s callees' predicates**: `verify_tables`' tree within `vtWB`, the terminal's
within `termWB`, at each opcode's weights. -/
noncomputable def vsPs {fs : String → ℕ} (W : VsWords fs) : List (Tree → Prop) :=
  [fun _ ↦ True, fun _ ↦ True, fun _ ↦ True, fun _ ↦ True, fun _ ↦ True, fun _ ↦ True,
    fun t ↦ ∀ op, Budget.WeighsLe coreProgram (W.ωv op) (vtWB W op) t,
    fun _ ↦ True, fun _ ↦ True, fun _ ↦ True, fun _ ↦ True, fun _ ↦ True,
    fun t ↦ ∀ op, Budget.WeighsLe coreProgram (W.ωv op) (termWB W op) t]

/-- **`verify_sub`'s callees' trees**: callee `j` a call of its name within its bound satisfying
its predicate. -/
noncomputable def vsTs (fs : String → ℕ) (W : VsWords fs) (Bvk μ r : ℕ) : List (Tree → Prop) :=
  namedP fs (vsNames μ r) (vsBsAt W Bvk μ r) (vsPs W)

/-- **`verify_sub`'s bound at one candidate.** -/
noncomputable def vsBoundAt {fs : String → ℕ} (W : VsWords fs) (Bvk μ r : ℕ) : ℕ :=
  fs "verify_sub" + 9156 + (vsBsAt W Bvk μ r).sum

theorem vs_names {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)
    (bs : List ℕ) (lpE sqE : ℕ) :
    List.Forall₂ (fun k n ↦ ∀ pv, (k pv).f = n) (S.kids bs lpE sqE) (vsNames S.μs S.rate) :=
  .cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl)
    (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl)
      (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl)
        (.cons (fun _ ↦ rfl) .nil))))))))))))

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem kidsDepBP_of {κ : ℕ} : ∀ (ks : List KidD) (Bs : List ℕ) (Ps : List (Tree → Prop)),
    ks.length = Bs.length → ks.length = Ps.length →
    (∀ j < ks.length, ∀ pv, ((ks.getD j noKid pv).taken = true →
        CompleteAtDTB fs cert κ (ks.getD j noKid pv).f (ks.getD j noKid pv).Lin
          (ks.getD j noKid pv).args (ks.getD j noKid pv).Out (Ps.getD j fun _ ↦ True) (Bs.getD j 0)) ∧
      ((ks.getD j noKid pv).taken = false → fs (ks.getD j noKid pv).f ≤ Bs.getD j 0)) →
    KidsDepBP fs cert κ ks Bs Ps
  | [], [], [], _, _, _ => trivial
  | [], _ :: _, _, h, _, _ => by simp at h
  | [], [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _, _ => by simp at h
  | _ :: _, _ :: _, [], _, h, _ => by simp at h
  | _ :: ks, _ :: Bs, _ :: Ps, hl, hl', h =>
    ⟨h 0 (by simp), kidsDepBP_of ks Bs Ps (by simpa using hl) (by simpa using hl')
      fun j hj ↦ h (j + 1) (by simp; omega)⟩

/-- **`verify_sub`'s callees on an honest child, each within its bound by a tree of its predicate**,
`open_stacked` within its candidate's. -/
theorem vs_kidsDepBP {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) {κ : ℕ} (hκ : 16 ≤ κ) (hrf : Lift.RunsFit fs cert)
    (hap : Lift.RunsApart cert) (W : VsWords fs) {Bvk : ℕ} (hvk : VkCompleteAtB fs cert κ Bvk)
    (bs : List ℕ) (lpE sqE : ℕ) :
    KidsDepBP fs cert κ (S.kids bs lpE sqE) (vsBsAt W Bvk S.μs S.rate) (vsPs W) := by
  refine kidsDepBP_of _ _ _ (by rw [ChildSegs.kids_length]; simp [vsBsAt])
    (by rw [ChildSegs.kids_length]; simp [vsPs]) fun j hj pv ↦ ?_
  have hj13 : j < 13 := by simpa [ChildSegs.kids_length] using hj
  have hμ := S.μ_bounds hbl
  have hτ := S.τ_bounds hbl
  have hfits := fun μ r h1 h2 h3 h4 ↦ osFitsAt_all fs cert hrf hap μ r h1 h2 h3 h4
  interval_cases j
  · exact ⟨fun _ ↦ (gpw_completeAtB κ [] (by have := S.hr4; omega) W.hg).toDTB, fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ (gpw_completeAtB κ [] (by have := S.h32; omega) W.hg).toDTB, fun h ↦ by cases h⟩
  · refine ⟨fun _ ↦ (log2_L0_completeAtB κ (by omega) _ lpE sqE (S.pushTotal_lt hbl) ?_).toDTB,
      fun h ↦ by cases h⟩
    show max 0 S.μ < 34; omega
  · exact ⟨fun _ ↦ (ac_completeAtB κ [] (x_canonical S.hroot).1 W.ha).toDTB, fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ (ac_completeAtB κ [] (x_canonical S.hroot).2 W.ha).toDTB, fun h ↦ by cases h⟩
  · obtain ⟨hrun, -, -, -⟩ := S.runG' hbl
    have hB : Tables.vbgBound fs W.K29 W.R W.K8 S.μ ≤ vbgMax fs W.K29 W.R W.K8 := by
      unfold vbgMax
      exact le_lmax (List.mem_map.2 ⟨S.μ, List.mem_range.2 (by omega), rfl⟩)
    exact ⟨fun _ ↦ (Tables.verify_bus_gkr_completeAtTB (by omega) (by omega) (by omega) hrun
      S.capS_carries (vcG bs) (vb bs 7) W.h29 W.hR1 W.hR2 W.h8).toCompleteAtB.toDTB.mono hB
      fun _ h ↦ h,
      fun h ↦ by cases h⟩
  · obtain ⟨hok, -, -, -⟩ := S.H_run hbl
    have hHμ : S.H.μ < 30 := by
      show S.point.length < 30
      rw [(S.runG' hbl).2.2.1]; omega
    have hn : S.H.n < 29 := by have := S.n_le hbl; omega
    have hB : fs "verify_tables" + S.H.sizes.sum + ((Tables.vtBs W.Kf W.Ksh (S.H.n * W.K10)).sum +
        Tables.ifFrames fs Tables.vtPre) ≤ vtMax fs W.Kf W.Ksh W.K10 := by
      rw [S.vt_sizes_sum]
      unfold vtMax
      exact le_lmax2 (vtBnd fs W.Kf W.Ksh W.K10) hHμ hn
    exact ⟨fun _ ↦ (Tables.verify_tables_completeAtTBW' (by omega) hok (S.H_shape hbl) (S.vtB bs sqE)
      W.Kf W.Ksh W.K10 W.hKf W.hsh W.h10 W.ωv W.Kvw W.Wss W.Kw10 W.hKvw W.hssw W.h10w).mono hB
      fun _ h ↦ h, fun h ↦ by cases h⟩
  · obtain ⟨hrun, -, -, -, hc6⟩ := S.runK' hbl
    have hf : S.s6.cap = capOf S.H.s3.perm := S.s6_capOf hbl
    exact ⟨fun _ ↦ hvk S.τ S.s6.cap S.chis S.outs S.xsK S.op S.kpt S.slices S.s7.cap S.word S.m0
      (S.cK bs) (vb bs 10) (vb bs 0 + 110) (vb bs 11) (vb bs 12) hτ.1 (by omega)
      (by rw [S.chis_length]; exact hτ.2.2) (S.lanes hbl).2.2 (by rw [hf]; rfl)
      (by rw [hf]; exact Tables.tb_capOf_canonical _) hc6 hrun |>.toDTB, fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ (rst_completeAtB κ (S.runK' hbl).2.2.2.1 S.rchs_length W.hl14).toDTB,
      fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ (Tables.certify_placement_completeAtB fs cert (by omega) S.hs_length S.h32
      (S.hh29 hbl) (by have := vsH_tau22 hbl S.hrowsL S.stack28; unfold ChildSegs.hs; omega) _
      _).toCompleteAtB.toDTB, fun h ↦ by cases h⟩
  · have hst : Tables.stackTotal S.kappas ≤ 2 ^ 28 := by
      have h28 := S.stack28
      rw [stackLog_eq hbl] at h28
      exact log2Ceil_le_iff.mp (by
        show log2Ceil (Tables.stackTotal (columnKappas S.logMem 19 (Tables.tableHeightsOf S.rowsN)))
          ≤ 28
        omega)
    have : log2Ceil (Tables.stackTotal S.kappas) ≤ 28 := log2Ceil_le_iff.mpr hst
    exact ⟨fun _ ↦ (log2_L15_completeAtB κ (by omega) _ lpE sqE (by omega) (by omega)).toDTB,
      fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ CompleteAtB.toDTB <| open_stacked_completeAtB S.μs S.rate S.hmu22 S.hmu28 S.hr1 S.hr4 fs cert κ
      W.Bnd W.Kr hrf (hfits _ _ S.hmu22 S.hmu28 S.hr1 S.hr4) W.hleaf
      (W.hloop _ _ S.hmu22 S.hmu28 S.hr1 S.hr4) S.s8.perm S.root S.target _ S.xsW c.proof.openings
      S.w S.s' S.roots' S.runW S.nzW S.capsW [(S.cW bs, S.xsW)]
      (fun rd _ hm ↦ hm _ List.mem_cons_self), fun h ↦ by cases h⟩
  · refine ⟨fun ht ↦ term_completeBW hbl S hκ _ lpE sqE pv ht W.hEqc W.hL15 W.hCs W.hCsF W.hrs
      W.ωv W.Weqc W.W15 W.Wst W.Wcs W.Wrsw W.hEqcW W.hStW W.hCsW W.h15W W.hrswW, fun _ ↦ ?_⟩
    show fs "check_opening_terminal" ≤ termBound fs W.Beqc W.K15 W.Bcs W.Brs
    unfold termBound
    omega


set_option maxHeartbeats 2000000 in
/-- **`verify_sub` is complete on every honest child within its own bound**, by a node whose
callees are calls of their names within their bounds, at the child's announced stack log and
rate. -/
theorem verify_sub_completeBT {bytecode : List K} (hbl : bytecode.length = 2 ^ 23)
    (hrf : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) (W : VsWords fs) {Bvk κ : ℕ}
    (hκ : 16 ≤ κ) (hvk : VkCompleteAtB fs cert κ Bvk) (seed : Digest) (c : Child)
    (lpE sqE outE : ℕ) (Lin : Main.Layout)
    (hmu : ∀ layout r, Verifier.announced bytecode c.proof.stream = some (layout, r) →
      Hints.muMin ≤ layout.stackLog)
    (hst : c.proof.stream.length ≤ Hints.streamCap)
    (hnz : Limits.verifyDeferredNZ bytecode seed (statementDigest seed c.statement) c.fresh
      c.proof = true)
    (hcaps : ∀ b ∈ Limits.queriesOf (deferredProgram c.fresh bytecode
      (statementDigest seed c.statement)) (Hints.childStart seed c), Limits.BatchAgrees b.1 b.2)
    (hexpL : ∀ q ∈ log2Lin lpE sqE, q ∈ Lin) (hout : (outE, fixedCells c.fresh) ∈ Lin) :
    CompleteAtDTB fs cert κ "verify_sub" Lin
      [(digestScalars (statementDigest seed c.statement)).1,
        (digestScalars (statementDigest seed c.statement)).2, (digestScalars seed).1,
        (digestScalars seed).2, ofK (gpow lpE), ofK (gpow sqE), ofK (gpow outE)] (Returns [])
      (Budget.FlatShape coreProgram "verify_sub"
        (vsTs fs W Bvk (childShape bytecode c).1 (childShape bytecode c).2))
      (vsBoundAt W Bvk (childShape bytecode c).1 (childShape bytecode c).2) := by
  obtain ⟨S⟩ := child_segments hbl seed c hmu hnz hcaps
  rw [childShape_of S.hann]
  obtain ⟨hkr, hkm, hσ⟩ := vs_obligations hbl S fs hκ hexpL hout
  have h := completeAt_flatDepRBP (fs := fs) (cert := cert) find_vs vs_not_loop κ Lin _ []
    (vs_body.trans vsT_splitPre) vs_cflat vs_caddrs vs_notIte (vsSizes S.μ) (fun _ ↦ S.ownW)
    (fun _ ↦ S.ownW_fits hbl hst)
    (fun fp ↦ S.kids (bases (fp + fs "verify_sub") (vsSizes S.μ)) lpE sqE)
    (vsNames S.μs S.rate) (vsBsAt W Bvk S.μs S.rate) (vsPs W) (fun _ ↦ vs_names S _ lpE sqE)
    (fun fp ↦ vs_kidsDepBP hbl S hκ hrf hap W hvk _ lpE sqE) hkr hkm hσ
  refine h.mono ?_ fun _ ht ↦ ht
  have := (S.μ_bounds hbl).2
  simp only [vsSizes, List.sum_cons, List.sum_nil, vsBoundAt, ChildSegs.μs]
  omega

/-- **`verify_sub` is complete within its own bound by its callees' trees** at the deployed frame
sizes, `verify_keccak` within `vkBound`. -/
theorem verify_sub_completeBT_fs {bytecode : List K} (hbl : bytecode.length = 2 ^ 23)
    {cert : String → V → ℕ} (hrf : Lift.RunsFit LeanVM.Guest.B2C.fs cert)
    (hap : Lift.RunsApart cert) (W : VsWords LeanVM.Guest.B2C.fs) {κ : ℕ} (hκ : 16 ≤ κ)
    (seed : Digest) (c : Child) (lpE sqE outE : ℕ) (Lin : Main.Layout)
    (hmu : ∀ layout r, Verifier.announced bytecode c.proof.stream = some (layout, r) →
      Hints.muMin ≤ layout.stackLog)
    (hst : c.proof.stream.length ≤ Hints.streamCap)
    (hnz : Limits.verifyDeferredNZ bytecode seed (statementDigest seed c.statement) c.fresh
      c.proof = true)
    (hcaps : ∀ b ∈ Limits.queriesOf (deferredProgram c.fresh bytecode
      (statementDigest seed c.statement)) (Hints.childStart seed c), Limits.BatchAgrees b.1 b.2)
    (hexpL : ∀ q ∈ log2Lin lpE sqE, q ∈ Lin) (hout : (outE, fixedCells c.fresh) ∈ Lin) :
    CompleteAtDTB LeanVM.Guest.B2C.fs cert κ "verify_sub" Lin
      [(digestScalars (statementDigest seed c.statement)).1,
        (digestScalars (statementDigest seed c.statement)).2, (digestScalars seed).1,
        (digestScalars seed).2, ofK (gpow lpE), ofK (gpow sqE), ofK (gpow outE)] (Returns [])
      (Budget.FlatShape coreProgram "verify_sub"
        (vsTs LeanVM.Guest.B2C.fs W vkBound (childShape bytecode c).1 (childShape bytecode c).2))
      (vsBoundAt W vkBound (childShape bytecode c).1 (childShape bytecode c).2) :=
  verify_sub_completeBT hbl hrf hap W hκ (verify_keccak_completeAtB_fs κ) seed c lpE sqE outE Lin
    hmu hst hnz hcaps hexpL hout

end
end LeanVM.Guest.B1.VerifySub
