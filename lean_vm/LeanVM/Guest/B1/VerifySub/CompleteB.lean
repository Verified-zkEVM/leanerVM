/-
  LeanVM.Guest.B1.VerifySub.CompleteB

  `verify_sub` is complete on every honest child within `vsBound` words: its frame, its own
  buffers and its thirteen callees' bounds, the callees' words facts (`VsWords`) and
  `verify_keccak`'s bounded completeness (`VkCompleteAtB`) assumed.
-/

module

public import LeanVM.Guest.B1.VerifySub.Complete
public import LeanVM.Guest.B1.VerifySub.H.TermCB
public import LeanVM.Guest.B1.Terminal.KidsDepB
public import LeanVM.Guest.B1.Ring.CompleteB
public import LeanVM.Guest.B1.Gkr.VbgB
public import LeanVM.Guest.B1.Tables.VtC.ABound
public import LeanVM.Guest.B1.Place.OsCandB
public import LeanVM.Guest.Budget.Bounded

/-!
# `verify_sub` within a bound

`VsWords fs`: the words facts of `verify_sub`'s callees' pure callees, at the frame sizes `fs`
(`TotalLe`, `TotalLeOn`), with their constants. `vsBs W Bvk`: the thirteen callees' bounds, in
call order — the maxima over the honest children's depths (`vbgMax`, `vtMax`, `osMax`) where a
callee's bound depends on them. `vsBound W Bvk = fs "verify_sub" + 9156 + (vsBs W Bvk).sum`: the
frame, the own buffers (at most `9127 + 29` words) and the callees.

`verify_sub_completeB`: on every honest child, `verify_sub` is `CompleteAtDTB … (fun _ ↦ True)
(vsBound W Bvk)`, by `completeAt_flatDepRB` with `vs_obligations` and the callees' bounded
completeness (`vs_kidsDepB`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-! ## The bounds -/

/-- The largest of a list. -/
def lmax (l : List ℕ) : ℕ := l.foldl max 0

theorem le_lmax {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ lmax l := (Tables.foldl_max_ge l 0).2 x h

theorem le_lmax2 (f : ℕ → ℕ → ℕ) {A B a b : ℕ} (ha : a < A) (hb : b < B) :
    f a b ≤ lmax ((List.range A).flatMap fun a ↦ (List.range B).map (f a)) :=
  le_lmax (List.mem_flatMap.2 ⟨a, List.mem_range.2 ha, List.mem_map.2 ⟨b, List.mem_range.2 hb, rfl⟩⟩)

/-- `verify_bus_gkr`'s bound over the depths below `30`. -/
@[irreducible] def vbgMax (fs : String → ℕ) (K29 R K8 : ℕ) : ℕ :=
  lmax ((List.range 30).map (Tables.vbgBound fs K29 R K8))

/-- `verify_tables`' bound at the bus depth `m` and the largest height `n`. -/
noncomputable def vtBnd (fs : String → ℕ) (Kf : String → ℕ) (Ksh K10 m n : ℕ) : ℕ :=
  fs "verify_tables" + (6604 + m + 9 * (n + 1)) +
    ((Tables.vtBs Kf Ksh (n * K10)).sum + Tables.ifFrames fs Tables.vtPre)

/-- `verify_tables`' bound over the depths below `30` and the heights below `29`. -/
@[irreducible] noncomputable def vtMax (fs : String → ℕ) (Kf : String → ℕ) (Ksh K10 : ℕ) : ℕ :=
  lmax ((List.range 30).flatMap fun m ↦ (List.range 29).map (vtBnd fs Kf Ksh K10 m))

/-- `open_stacked`'s bound over the candidates (stack logs below `29`, rates below `5`). -/
@[irreducible] noncomputable def osMax (fs Bnd Kr : String → ℕ) : ℕ :=
  lmax ((List.range 29).flatMap fun μ ↦ (List.range 5).map (osBosAt fs Bnd Kr μ))

/-- **`verify_sub`'s callees' words facts**, at the frame sizes `fs`: `g_power_of_word`'s and
`assert_canonical`'s (`Bg`, `Ba`), `verify_bus_gkr`'s loops and rounds (`K29`, `R`, `K8`),
`verify_tables`' callees (`Kf`, `Ksh`, `K10`), `ring_switch_target`'s loop (`B14`),
`open_stacked`'s leaves and residual loops (`Bnd`, `Kr`), the terminal's pure callees (`Beqc`,
`K15`, `Bcs`, `Brs`). -/
structure VsWords (fs : String → ℕ) : Type where
  Bg : ℕ
  hg : TotalLe coreProgram fs "g_power_of_word" fun _ ↦ Bg
  Ba : ℕ
  ha : TotalLe coreProgram fs "assert_canonical" fun _ ↦ Ba
  K29 : ℕ
  R : ℕ
  K8 : ℕ
  h29 : TotalLeOn coreProgram fs "__loop29" LoopPre (fun a ↦ logG (a.getD 1 0) * K29)
  hR1 : TotalLe coreProgram fs "gkr_rounds__L1" (fun _ ↦ R)
  hR2 : TotalLe coreProgram fs "gkr_rounds__L2" (fun _ ↦ R)
  h8 : TotalLeOn coreProgram fs "__loop8" LoopPre (fun a ↦ logG (a.getD 1 0) * K8)
  Kf : String → ℕ
  Ksh : ℕ
  K10 : ℕ
  hKf : ∀ g ∈ Tables.vtKidS, g ≠ "__loop10" → g ≠ "__loop9" → g ≠ "shared_selector_tables" →
    TotalLe coreProgram fs g (fun _ ↦ Kf g)
  hsh : TotalLeOn coreProgram fs "shared_selector_tables"
    (fun a ↦ ∃ n < 64, a.getD 5 0 = gen ^ n) (fun _ ↦ Ksh)
  h10 : TotalLeOn coreProgram fs "__loop10" LoopPre (fun a ↦ logG (a.getD 1 0) * K10)
  B14 : ℕ
  hl14 : TotalLeOn coreProgram fs "__loop14" (fun a ↦ a.getD 0 0 = 1) fun _ ↦ B14
  Bnd : String → ℕ
  Kr : String → ℕ
  hleaf : OsLeafBounds fs Bnd
  hloop : ∀ μ r, 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 →
    OsLoopBounds fs Kr (B1.Whir.osCfg (B1.Whir.candidate μ r))
  Beqc : ℕ
  K15 : ℕ
  Bcs : ℕ
  Brs : ℕ
  hEqc : TotalLe coreProgram fs "eq_prefix_chain" fun _ ↦ Beqc
  hL15 : TotalLeOn coreProgram fs "__loop15" LoopPre fun a ↦ logG (a.getD 1 0) * K15
  hCs : ∀ κ' < 29, TotalLe coreProgram fs (Tables.lName "column_selector" κ') fun _ ↦ Bcs
  hCsF : ∀ κ' < 29, fs (Tables.lName "column_selector" κ') ≤ Bcs
  hrs : ∀ c ≤ 34, TotalLeOn coreProgram fs "rs_eq_run" (fun a ↦ a.getD 3 0 = gen ^ c)
    fun _ ↦ Brs

/-- **The callees' bounds**, in call order (`vs_calls`). -/
noncomputable def vsBs {fs : String → ℕ} (W : VsWords fs) (Bvk : ℕ) : List ℕ :=
  [W.Bg, W.Bg, fs "log2_ceil_in_the_exponent__L0_L34" + 34 + (fs "verify_log2_ceil__L0_L34" + 35),
    W.Ba, W.Ba, vbgMax fs W.K29 W.R W.K8, vtMax fs W.Kf W.Ksh W.K10, Bvk,
    fs "ring_switch_target" + 18 + W.B14, fs "certify_placement" + [99, 99, 99].sum,
    fs "log2_ceil_in_the_exponent__L15_L34" + 34 + (fs "verify_log2_ceil__L15_L34" + 35),
    osMax fs W.Bnd W.Kr, termBound fs W.Beqc W.K15 W.Bcs W.Brs]

/-- **`verify_sub`'s bound**: its frame, its own buffers (`9127 + μ`, `μ ≤ 29`), its callees. -/
noncomputable def vsBound {fs : String → ℕ} (W : VsWords fs) (Bvk : ℕ) : ℕ :=
  fs "verify_sub" + 9156 + (vsBs W Bvk).sum

/-- **`verify_keccak`, placed, within `Bvk` words** (`VkCompleteAt` bounded). -/
def VkCompleteAtB (fs : String → ℕ) (cert : String → V → ℕ) (κ Bvk : ℕ) : Prop :=
  ∀ (τ : ℕ) (f chis outs xs op point slices cap' : List E) (word m0 : E)
    (curE chiE olE zvE slE : ℕ), 9 ≤ τ → τ ≤ 28 → τ ≤ chis.length → outs.length = 25 →
    f.length = 5 → AllCanonical f → (∃ sp, (⟨f, []⟩ : Fs).Carries sp) →
    RunsTo (keccakSeg τ (chis.take τ) outs) ⟨f, []⟩ xs
      (([⟨qkeccak, op, word⟩], point, slices), m0) ⟨cap', []⟩ →
    CompleteAtB fs cert κ "verify_keccak"
      [(curE, xs), (chiE, chis), (olE, outs), (zvE, op), (zvE + qkeccakVarsCap, point),
        (slE, slices)]
      (f ++ [ofK (gpow curE), gen ^ τ, ofK (gpow chiE), ofK (gpow olE), ofK (gpow zvE),
        ofK (gpow slE)])
      (Returns (cap' ++ [ofK (gpow curE) * gen ^ xs.length, word, m0])) Bvk

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-! ## The callees within their bounds -/

/-- **`g_power_of_word`, placed, within its words.** -/
theorem gpw_completeAtB (κ : ℕ) (Lin : Main.Layout) {n : ℕ} (hn : n < 2 ^ 6) {Bg : ℕ}
    (hg : TotalLe coreProgram fs "g_power_of_word" fun _ ↦ Bg) :
    CompleteAtB fs cert κ "g_power_of_word" Lin [eOfNat n] (Returns [gen ^ n]) Bg :=
  completeAt_of_rel_pureB (B := fun _ ↦ Bg) gpw_pure (List.mem_singleton_self _)
    (fun rd _ ↦ (g_power_of_word_holds rd [eOfNat n] [gen ^ n]).2
      (show ∃ m < 2 ^ 6, eOfNat n = eOfNat m ∧ [gen ^ n] = [gen ^ m] from ⟨n, hn, rfl, rfl⟩)) κ hg

/-- **`assert_canonical`, placed, within its words.** -/
theorem ac_completeAtB (κ : ℕ) (Lin : Main.Layout) {w : E} (hw : IsCanonical128 w) {Ba : ℕ}
    (ha : TotalLe coreProgram fs "assert_canonical" fun _ ↦ Ba) :
    CompleteAtB fs cert κ "assert_canonical" Lin [w] (Returns [0]) Ba :=
  completeAt_of_rel_pureB (B := fun _ ↦ Ba) ac_pure (List.mem_singleton_self _)
    (fun rd _ ↦ (assert_canonical_holds rd [w] [0]).2
      (show IsCanonical128 w ∧ [(0 : E)] = [0] from ⟨hw, rfl⟩)) κ ha

/-- Callees by position, each within its bound. -/
theorem kidsDepB_of {κ : ℕ} : ∀ (ks : List KidD) (Bs : List ℕ), ks.length = Bs.length →
    (∀ j < ks.length, ∀ pv, ((ks.getD j noKid pv).taken = true →
        CompleteAtB fs cert κ (ks.getD j noKid pv).f (ks.getD j noKid pv).Lin
          (ks.getD j noKid pv).args (ks.getD j noKid pv).Out (Bs.getD j 0)) ∧
      ((ks.getD j noKid pv).taken = false → fs (ks.getD j noKid pv).f ≤ Bs.getD j 0)) →
    KidsDepB fs cert κ ks Bs
  | [], [], _, _ => trivial
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | _ :: ks, _ :: Bs, hl, h =>
    ⟨h 0 (by simp), kidsDepB_of ks Bs (by simpa using hl) fun j hj ↦ h (j + 1) (by simp; omega)⟩

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- The largest height. -/
theorem n_le (hbl : bytecode.length = 2 ^ 23) : S.H.n ≤ 28 := by
  show (Tables.tableHeightsOf S.rowsN).foldl max 0 ≤ 28
  rcases Tables.foldl_max_mem (Tables.tableHeightsOf S.rowsN) 0 with h | h
  · omega
  · have := S.hh29 hbl _ h
    omega

/-- `verify_tables`' own buffers. -/
theorem vt_sizes_sum : S.H.sizes.sum = 6604 + S.H.μ + 9 * (S.H.n + 1) := by
  simp only [Tables.VtHonest.sizes, List.sum_append, List.sum_cons, List.sum_nil,
    List.sum_replicate, smul_eq_mul]
  omega

end ChildSegs

set_option maxHeartbeats 2000000 in
/-- **`verify_sub`'s callees on an honest child, each within its bound.** -/
theorem vs_kidsDepB {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) {κ : ℕ} (hκ : 16 ≤ κ) (hrf : Lift.RunsFit fs cert)
    (hap : Lift.RunsApart cert) (W : VsWords fs) {Bvk : ℕ} (hvk : VkCompleteAtB fs cert κ Bvk)
    (bs : List ℕ) (lpE sqE : ℕ) :
    KidsDepB fs cert κ (S.kids bs lpE sqE) (vsBs W Bvk) := by
  refine kidsDepB_of _ _ (by rw [ChildSegs.kids_length]; simp [vsBs]) fun j hj pv ↦ ?_
  have hj13 : j < 13 := by simpa [ChildSegs.kids_length] using hj
  have hμ := S.μ_bounds hbl
  have hτ := S.τ_bounds hbl
  have hfits := fun μ r h1 h2 h3 h4 ↦ osFitsAt_all fs cert hrf hap μ r h1 h2 h3 h4
  interval_cases j
  · exact ⟨fun _ ↦ gpw_completeAtB κ [] (by have := S.hr4; omega) W.hg, fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ gpw_completeAtB κ [] (by have := S.h32; omega) W.hg, fun h ↦ by cases h⟩
  · refine ⟨fun _ ↦ log2_L0_completeAtB κ (by omega) _ lpE sqE (S.pushTotal_lt hbl) ?_,
      fun h ↦ by cases h⟩
    show max 0 S.μ < 34; omega
  · exact ⟨fun _ ↦ ac_completeAtB κ [] (x_canonical S.hroot).1 W.ha, fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ ac_completeAtB κ [] (x_canonical S.hroot).2 W.ha, fun h ↦ by cases h⟩
  · obtain ⟨hrun, -, -, -⟩ := S.runG' hbl
    have hB : Tables.vbgBound fs W.K29 W.R W.K8 S.μ ≤ vbgMax fs W.K29 W.R W.K8 := by
      unfold vbgMax
      exact le_lmax (List.mem_map.2 ⟨S.μ, List.mem_range.2 (by omega), rfl⟩)
    exact ⟨fun _ ↦ (Tables.verify_bus_gkr_completeAtTB (by omega) (by omega) (by omega) hrun
      S.capS_carries (vcG bs) (vb bs 7) W.h29 W.hR1 W.hR2 W.h8).toCompleteAtB.mono le_rfl hB,
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
    exact ⟨fun _ ↦ (Tables.verify_tables_completeAtTB (by omega) hok (S.H_shape hbl) (S.vtB bs sqE)
      W.Kf W.Ksh W.K10 W.hKf W.hsh W.h10).toCompleteAtB.mono le_rfl hB, fun h ↦ by cases h⟩
  · obtain ⟨hrun, -, -, -, hc6⟩ := S.runK' hbl
    have hf : S.s6.cap = capOf S.H.s3.perm := S.s6_capOf hbl
    exact ⟨fun _ ↦ hvk S.τ S.s6.cap S.chis S.outs S.xsK S.op S.kpt S.slices S.s7.cap S.word S.m0
      (S.cK bs) (vb bs 10) (vb bs 0 + 110) (vb bs 11) (vb bs 12) hτ.1 (by omega)
      (by rw [S.chis_length]; exact hτ.2.2) (S.lanes hbl).2.2 (by rw [hf]; rfl)
      (by rw [hf]; exact Tables.tb_capOf_canonical _) hc6 hrun, fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ rst_completeAtB κ (S.runK' hbl).2.2.2.1 S.rchs_length W.hl14,
      fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ (Tables.certify_placement_completeAtB fs cert (by omega) S.hs_length S.h32
      (S.hh29 hbl) (by have := vsH_tau22 hbl S.hrowsL S.stack28; unfold ChildSegs.hs; omega) _
      _).toCompleteAtB, fun h ↦ by cases h⟩
  · have hst : Tables.stackTotal S.kappas ≤ 2 ^ 28 := by
      have h28 := S.stack28
      rw [stackLog_eq hbl] at h28
      exact log2Ceil_le_iff.mp (by
        show log2Ceil (Tables.stackTotal (columnKappas S.logMem 19 (Tables.tableHeightsOf S.rowsN)))
          ≤ 28
        omega)
    have : log2Ceil (Tables.stackTotal S.kappas) ≤ 28 := log2Ceil_le_iff.mpr hst
    exact ⟨fun _ ↦ log2_L15_completeAtB κ (by omega) _ lpE sqE (by omega) (by omega),
      fun h ↦ by cases h⟩
  · have hB : osBosAt fs W.Bnd W.Kr S.μs S.rate ≤ osMax fs W.Bnd W.Kr := by
      unfold osMax
      exact le_lmax2 (osBosAt fs W.Bnd W.Kr) (by have : S.μs ≤ 28 := S.hmu28; omega)
        (by have := S.hr4; omega)
    exact ⟨fun _ ↦ (open_stacked_completeAtB S.μs S.rate S.hmu22 S.hmu28 S.hr1 S.hr4 fs cert κ
      W.Bnd W.Kr hrf (hfits _ _ S.hmu22 S.hmu28 S.hr1 S.hr4) W.hleaf
      (W.hloop _ _ S.hmu22 S.hmu28 S.hr1 S.hr4) S.s8.perm S.root S.target _ S.xsW c.proof.openings
      S.w S.s' S.roots' S.runW S.nzW S.capsW [(S.cW bs, S.xsW)]
      (fun rd _ hm ↦ hm _ List.mem_cons_self)).mono le_rfl hB, fun h ↦ by cases h⟩
  · refine ⟨fun ht ↦ term_completeB hbl S hκ _ lpE sqE pv ht W.hEqc W.hL15 W.hCs W.hCsF W.hrs,
      fun _ ↦ ?_⟩
    show fs "check_opening_terminal" ≤ termBound fs W.Beqc W.K15 W.Bcs W.Brs
    unfold termBound
    omega

set_option maxHeartbeats 2000000 in
/-- **`verify_sub` is complete on every honest child within `vsBound W Bvk` words**, its callees'
words facts `W` and `verify_keccak`'s bounded completeness assumed. -/
theorem verify_sub_completeB {bytecode : List K} (hbl : bytecode.length = 2 ^ 23)
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
      (fun _ ↦ True) (vsBound W Bvk) := by
  obtain ⟨S⟩ := child_segments hbl seed c hmu hnz hcaps
  obtain ⟨hkr, hkm, hσ⟩ := vs_obligations hbl S fs hκ hexpL hout
  have h := completeAt_flatDepRB (fs := fs) (cert := cert) find_vs vs_not_loop κ Lin _ []
    (vs_body.trans vsT_splitPre) vs_cflat vs_caddrs vs_notIte (vsSizes S.μ) (fun _ ↦ S.ownW)
    (fun _ ↦ S.ownW_fits hbl hst)
    (fun fp ↦ S.kids (bases (fp + fs "verify_sub") (vsSizes S.μ)) lpE sqE) (vsBs W Bvk)
    (fun fp ↦ vs_kidsDepB hbl S hκ hrf hap W hvk _ lpE sqE) hkr hkm hσ
  refine (h.mono le_rfl ?_).toDTB
  have := (S.μ_bounds hbl).2
  simp only [vsSizes, List.sum_cons, List.sum_nil, vsBound]
  omega

end
end LeanVM.Guest.B1.VerifySub
