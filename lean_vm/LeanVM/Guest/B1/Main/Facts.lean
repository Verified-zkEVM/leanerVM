/-
  LeanVM.Guest.B1.Main.Facts

  What a run of `main`'s body gives (`MainFacts`), from its facts checked by evaluation, the
  digest family's statements and the loops'.
-/

module

public import LeanVM.Guest.B1.Main.Body

/-!
# `main`'s facts

`main_facts`: on a memory image, a run of `main`'s body (under `coreProgram.Rel`) gives
`MainFacts`: the counts as powers of `g` (`lg σ v`, the exponent of `σ (.n v)`) with their
bounds, the region sizes, the exponent tables, the declared lists' and the DA list's digests, the
signer set, the byte table, every raw signature's and every child's iteration, the direct DA
check, the running counts, the leaf's or the batching's deferred claim, and the statement's digest
in the public input cells.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

/-! ## Exponents -/

theorem gLog_gen_pow {e : ℕ} (he : e < 2 ^ 34) : gLog (gen ^ e) = e := by
  unfold gLog
  rw [gen_pow_eq_ofK, limb_ofK]
  simp only [Fin.isValue, Fin.val_zero, ↓reduceIte]
  rw [(gLog?_spec (κ := 34) (by norm_num) (i := ⟨e, he⟩)).mpr rfl]
  rfl

/-- The exponent of `main`'s value `v`. -/
noncomputable abbrev lg (σ : Val) (v : ℕ) : ℕ := gLog (σ (.n v))

theorem pow_lg {σ : Val} {v e : ℕ} (he : e < 2 ^ 34) (h : σ (.n v) = gen ^ e) :
    σ (.n v) = gen ^ lg σ v ∧ lg σ v = e := by
  have : lg σ v = e := by rw [lg, h, gLog_gen_pow he]
  exact ⟨by rw [this]; exact h, this⟩

/-! ## The facts -/

/-- **What a run of `main`'s body gives.** -/
structure MainFacts (rd : Reader) (σ : Val) : Prop where
  counts : ∀ v ∈ [0, 1, 2, 3, 4, 5], σ (.n v) = gen ^ lg σ v ∧ lg σ v ≤ 65535
  kids : σ (.n 6) = gen ^ lg σ 6 ∧ lg σ 6 ≤ 16
  direct : σ (.n 7) = gen ^ lg σ 7 ∧ lg σ 7 ≤ 1
  nda : σ (.n 40) = gen ^ lg σ 40 ∧ lg σ 40 ≤ 16
  daslots : σ (.n 50) = gen ^ (lg σ 40 + lg σ 41) ∧ lg σ 40 + lg σ 41 ≤ 257
  lxs : σ (.n 55) = gen ^ (lg σ 0 + lg σ 1)
  lss : σ (.n 56) = gen ^ (lg σ 3 + lg σ 4)
  total : σ (.n 58) = gen ^ (lg σ 0 + lg σ 1 + (lg σ 3 + lg σ 4) + (lg σ 40 + lg σ 41)) ∧
    lg σ 0 + lg σ 1 + (lg σ 3 + lg σ 4) + (lg σ 40 + lg σ 41) ≤ 65535
  exp : ExpTables rd (σ (.n 65)) (σ (.n 66))
  dalist : ClaimListOut rd (σ (.n 69)) (lg σ 40) [σ (.n 73), σ (.n 74)]
  xlist : ClaimListOut rd (σ (.n 77)) (lg σ 0) [σ (.n 81), σ (.n 82)]
  slist : ClaimListOut rd (σ (.n 80)) (lg σ 3) [σ (.n 83), σ (.n 84)]
  signers : AllCanonical [σ (.n 81), σ (.n 82), σ (.n 83), σ (.n 84)] ∧
    LoadHolds rd (σ (.n 116)) 0
      (digestScalars (keccak256 (cellsBytes [σ (.n 81), σ (.n 82), σ (.n 83), σ (.n 84)]))).1 ∧
    LoadHolds rd (σ (.n 116)) 1
      (digestScalars (keccak256 (cellsBytes [σ (.n 81), σ (.n 82), σ (.n 83), σ (.n 84)]))).2
  dacover : σ (.n 118) = σ (.n 117) * gen ^ (lg σ 0 + lg σ 1 + (lg σ 3 + lg σ 4))
  bytes : Sig.ByteBits rd (σ (.n 119))
  rawx : ∀ i < lg σ 2, RawXStep rd (σ (.n 55)) (σ (.n 117)) (σ (.n 77)) (gen ^ i)
  raws : ∀ j < lg σ 5, RawSStep rd (σ (.n 56)) (σ (.n 117)) (σ (.n 55)) (σ (.n 2)) (σ (.n 80))
    (σ (.n 119)) (gen ^ j)
  da : lg σ 7 = 1 →
    coreProgram.Rel rd "da_verify" [σ (.n 66)] [σ (.n 384), σ (.n 385), σ (.n 386), σ (.n 387)] ∧
    coreProgram.Rel rd "cover_da_root" [σ (.n 69), σ (.n 118), σ (.n 50), gen ^ (lg σ 2 + lg σ 5)]
      [σ (.n 384), σ (.n 385), σ (.n 386), σ (.n 387)]
  written0 : LoadHolds rd (σ (.n 409)) 0 (gen ^ (lg σ 2 + lg σ 5 + lg σ 7))
  children : ∀ c < lg σ 6, KidStep rd (σ (.n 409)) (σ (.n 77)) (σ (.n 117)) (σ (.n 55))
    (σ (.n 80)) (σ (.n 56)) (σ (.n 406)) (σ (.n 69)) (σ (.n 118)) (σ (.n 50)) (σ (.n 63))
    (σ (.n 64)) (σ (.n 394)) (σ (.n 65)) (σ (.n 66)) (σ (.n 400)) (gen ^ c)
  writtenN : LoadHolds rd (σ (.n 409)) (lg σ 6) (σ (.n 58))
  leaf : lg σ 6 = 0 → ∀ k < 23, LoadHolds rd (σ (.n 417)) k 0
  agg : lg σ 6 ≠ 0 → coreProgram.Rel rd "aggregate_claims"
    [σ (.n 6), σ (.n 394), σ (.n 400), σ (.n 406), σ (.n 417)] []
  own : coreProgram.Rel rd "statement_digest"
    [σ (.n 63), σ (.n 64), σ (.n 116), σ (.n 73), σ (.n 74), σ (.n 417)] [σ (.n 444), σ (.n 445)]
  pub : LoadHolds rd 1 0 (σ (.n 444)) ∧ LoadHolds rd 1 1 (σ (.n 445))

end
end LeanVM.Guest.B1.Main

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

set_option maxRecDepth 100000 in
theorem noRet_mDa : Stmt.noRetList mDa = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem noRet_mLeaf : Stmt.noRetList mLeaf = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem noRet_mAgg : Stmt.noRetList mAgg = true := by decide +kernel

theorem gen_pow_inj34 {a b : ℕ} (ha : a < 2 ^ 34) (hb : b < 2 ^ 34) (h : gen ^ a = gen ^ b) :
    a = b :=
  gen_pow_inj (by omega) (by omega) h

set_option maxRecDepth 100000 in
/-- **The facts of a run of `main`'s body**, on a memory image, given `exponent_tables`' statement
(B1-a). -/
theorem main_facts {rd : Reader} (hm : MemOk rd) (hexp : exponent_tables_Spec) {σ : Val}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ (Fn.body Data.core0) False (fun rs => rs = [])) :
    MainFacts rd σ := by
  rw [core0_shape] at h
  simp only [List.append_assoc, holdsList_append] at h
  have hP := pre_ok
  have hD := da_ok
  have hM := mid_ok
  have hL := leaf_ok
  have hQ := post_ok
  simp only [preOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hP
  simp only [daOk, Bool.and_eq_true] at hD
  simp only [midOk, Bool.and_eq_true] at hM
  simp only [leafOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hL
  simp only [postOk, Bool.and_eq_true] at hQ
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨pflat, prc⟩, prc6⟩, prc7⟩, prc40⟩, prc41⟩, prc50⟩, prc58⟩,
    pm50⟩, pm55⟩, pm56⟩, pm57⟩, pm58⟩, pexp⟩, pdl⟩, pxl⟩, psl⟩, psig⟩, pm118⟩, pbytes⟩, pl3⟩,
    pl4⟩, pa383⟩, pc382⟩ := hP
  obtain ⟨⟨⟨⟨⟨⟨⟨dflat, dver⟩, dm388⟩, dcov⟩, de1⟩, de2⟩, de3⟩, de4⟩ := hD
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨mflat, mm410⟩, mm411⟩, ml411⟩, ml5⟩, mm415⟩, ml416⟩, meq⟩, ma419⟩, mc418⟩ := hM
  obtain ⟨⟨⟨⟨lflat, lzero⟩, l420⟩, aflat⟩, acall⟩ := hL
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨qflat, qsd⟩, qc446⟩, ql447⟩, qe1⟩, qc448⟩, qc449⟩, qm450⟩, ql451⟩, qe2⟩ := hQ
  -- the blocks
  obtain ⟨hpre, h⟩ := holdsList_flat mPre (List.all_eq_true.mpr pflat) _ _ h
  simp only [Stmt.HoldsList] at h
  rw [holds_ite_noRet _ _ _ noRet_mDa rfl] at h
  obtain ⟨⟨-, hdz, -⟩, h⟩ := h
  obtain ⟨hmid, h⟩ := holdsList_flat mMid mflat _ _ h
  rw [holds_ite_noRet _ _ _ noRet_mLeaf noRet_mAgg] at h
  obtain ⟨⟨-, hlz, hln⟩, h⟩ := h
  obtain ⟨hpost, -⟩ := holdsList_flat mPost qflat _ _ h
  have atP := atoms_of_flat hpre
  have atM := atoms_of_flat hmid
  have atQ := atoms_of_flat hpost
  -- the counts
  have hc : ∀ v < 6, ∃ e ≤ 65535, σ (.n v) = gen ^ e :=
    fun v hv => rcConst_sound hm (by norm_num) word_gmax (prc v hv) atP
  have hcl : ∀ v < 6, σ (.n v) = gen ^ lg σ v ∧ lg σ v ≤ 65535 := fun v hv => by
    obtain ⟨e, he, hv'⟩ := hc v hv
    obtain ⟨h1, h2⟩ := pow_lg (by omega) hv'
    exact ⟨h1, by omega⟩
  obtain ⟨e6, he6, h6⟩ := rcConst_sound hm (by norm_num) word_g16 prc6 atP
  obtain ⟨e7, he7, h7⟩ := rcConst_sound hm (by norm_num) word_g1 prc7 atP
  obtain ⟨e40, he40, h40⟩ := rcConst_sound hm (by norm_num) word_g16 prc40 atP
  obtain ⟨e41, he41, h41⟩ := rcConst_sound hm (by norm_num) word_g257 prc41 atP
  obtain ⟨e50, he50, h50⟩ := rcConst_sound hm (by norm_num) word_g257 prc50 atP
  obtain ⟨e58, he58, h58⟩ := rcConst_sound hm (by norm_num) word_gmax prc58 atP
  obtain ⟨l6, r6⟩ := pow_lg (by omega) h6
  obtain ⟨l7, r7⟩ := pow_lg (by omega) h7
  obtain ⟨l40, r40⟩ := pow_lg (by omega) h40
  obtain ⟨l41, r41⟩ := pow_lg (by omega) h41
  have h50' : σ (.n 50) = gen ^ (lg σ 40 + lg σ 41) := by
    rw [isMul_sound pm50 atP, l40, l41, pow_add]
  have he50' : e50 = lg σ 40 + lg σ 41 := gen_pow_inj34 (by omega) (by omega) (h50.symm.trans h50')
  obtain ⟨c0, b0⟩ := hcl 0 (by omega)
  obtain ⟨c1, b1⟩ := hcl 1 (by omega)
  obtain ⟨c2, b2⟩ := hcl 2 (by omega)
  obtain ⟨c3, b3⟩ := hcl 3 (by omega)
  obtain ⟨c4, b4⟩ := hcl 4 (by omega)
  obtain ⟨c5, b5⟩ := hcl 5 (by omega)
  have h55 : σ (.n 55) = gen ^ (lg σ 0 + lg σ 1) := by rw [isMul_sound pm55 atP, c0, c1, pow_add]
  have h56 : σ (.n 56) = gen ^ (lg σ 3 + lg σ 4) := by rw [isMul_sound pm56 atP, c3, c4, pow_add]
  have h57 : σ (.n 57) = gen ^ (lg σ 0 + lg σ 1 + (lg σ 3 + lg σ 4)) := by
    rw [isMul_sound pm57 atP, h55, h56, ← pow_add]
  have h58' : σ (.n 58) = gen ^ (lg σ 0 + lg σ 1 + (lg σ 3 + lg σ 4) + (lg σ 40 + lg σ 41)) := by
    rw [isMul_sound pm58 atP, h57, h50', ← pow_add]
  have hT := gen_pow_inj34 (by omega) (by omega) (h58.symm.trans h58')
  -- the loops
  have hguard3 := guard_sound pl3 hpre
  have hguard4 := guard_sound pl4 hpre
  refine ⟨fun v hv => ?_, ⟨l6, by omega⟩, ⟨l7, by omega⟩, ⟨l40, by omega⟩, ⟨h50', by omega⟩, h55, h56,
    ⟨h58', by omega⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hcl _ (by omega)
  · -- the exponent tables
    have := call_of_flat hpre pexp
    exact (hexp rd _ _).mp this
  · have := da_list_digest_sound rd _ _ (call_of_flat hpre pdl)
    obtain ⟨n, hn, hng, hout⟩ := this
    rw [l40] at hng
    have := gen_pow_inj34 (by simp only [maxDaRoots] at hn; omega) (by omega) hng.symm
    rw [r40] at this ⊢
    rw [← this]
    exact hout
  · obtain ⟨n, hn, hng, hout⟩ := claim_list_digest_sound rd hm _ _ (call_of_flat hpre pxl)
    rw [c0] at hng
    have hn' : n < 1114112 := hn
    have := gen_pow_inj34 (by omega) (by omega) hng
    rwa [this]
  · obtain ⟨n, hn, hng, hout⟩ := claim_list_digest_sound rd hm _ _ (call_of_flat hpre psl)
    rw [c3] at hng
    have hn' : n < 1114112 := hn
    have := gen_pow_inj34 (by omega) (by omega) hng
    rwa [this]
  · exact pairHash_sound psig atP
  · rw [isMul_sound pm118 atP, h57]
  · intro v hv
    obtain ⟨hcv, hlv⟩ := pbytes v hv
    have := load_sound hlv atP
    rwa [const_sound hcv atP] at this
  · -- raw leanXMSS
    refine loop_sound (f := "__loop3") (ps := [σ (.n 2), σ (.n 55), σ (.n 117), σ (.n 77)])
      (N := σ (.n 2)) (B := RawXStep rd (σ (.n 55)) (σ (.n 117)) (σ (.n 77)))
      (by unfold ordG; omega) c2 (fun x hx => ?_) (fun hne => by simpa using hguard3 hne)
    obtain ⟨h1, h2⟩ := l3_step hm hx
    exact ⟨h1 _ _ _ _ rfl, h2⟩
  · -- raw leanSPHINCS
    refine loop_sound (f := "__loop4")
      (ps := [σ (.n 5), σ (.n 56), σ (.n 117), σ (.n 55), σ (.n 2), σ (.n 80), σ (.n 119)])
      (N := σ (.n 5))
      (B := RawSStep rd (σ (.n 56)) (σ (.n 117)) (σ (.n 55)) (σ (.n 2)) (σ (.n 80)) (σ (.n 119)))
      (by unfold ordG; omega) c5 (fun x hx => ?_) (fun hne => by simpa using hguard4 hne)
    obtain ⟨h1, h2⟩ := l4_step hm hx
    exact ⟨h1 _ _ _ _ _ _ _ rfl, h2⟩
  · -- the direct DA check
    intro h71
    have h383 : σ (.n 383) = 0 := by
      rw [add_sound pa383 atP, const_sound pc382 atP, word_gen, l7, h71, pow_one, e_add_self]
    obtain ⟨hdall, -⟩ := holdsList_flat mDa dflat _ _ (hdz h383)
    have atD := atoms_of_flat hdall
    refine ⟨call_of_flat hdall dver, ?_⟩
    have := call_of_flat hdall dcov
    simp only [List.map_cons, List.map_nil] at this
    rwa [isMul_sound dm388 atD, c2, c5, ← pow_add, ← assertEq_sound de1 atD,
      ← assertEq_sound de2 atD, ← assertEq_sound de3 atD, ← assertEq_sound de4 atD] at this
  · have := load_sound ml411 atM
    rwa [isMul_sound mm411 atM, isMul_sound mm410 atM, c2, c5, l7, ← pow_add, ← pow_add] at this
  · -- the children
    have hguard5 := guard_sound ml5 hmid
    refine loop_sound (f := "__loop5")
      (ps := [σ (.n 6), σ (.n 409), σ (.n 77), σ (.n 117), σ (.n 55), σ (.n 80), σ (.n 56),
        σ (.n 406), σ (.n 69), σ (.n 118), σ (.n 50), σ (.n 63), σ (.n 64), σ (.n 394), σ (.n 65),
        σ (.n 66), σ (.n 400)])
      (N := σ (.n 6)) (by unfold ordG; omega) l6 (fun x hx => ?_)
      (fun hne => by simpa using hguard5 hne)
    obtain ⟨h1, h2⟩ := l5_step hm hx
    exact ⟨h1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl, h2⟩
  · have := load_sound ml416 atM
    rw [isMul_sound mm415 atM, l6, assertEq_sound meq atM] at this
    have := (loadHolds_mul_gen_pow rd _ (lg σ 6) 0 _).mp this
    simpa using this
  · intro h60 k hk
    have h419 : σ (.n 419) = 0 := by
      rw [add_sound ma419 atM, const_sound mc418 atM, word_one, l6, h60, pow_zero, e_add_self]
    obtain ⟨hlall, -⟩ := holdsList_flat mLeaf (List.all_eq_true.mpr lflat) _ _ (hlz h419)
    have atL := atoms_of_flat hlall
    obtain ⟨hz, hl⟩ := lzero k hk
    have := load_sound hl atL
    rwa [const_sound hz atL, word_zero] at this
  · intro h60
    have h419 : σ (.n 419) ≠ 0 := by
      rw [add_sound ma419 atM, const_sound mc418 atM, word_one, l6]
      intro he
      have h2 : gen ^ 0 = gen ^ lg σ 6 := (pow_zero gen).trans (e_add_eq_zero_iff.mp he).symm
      exact h60 (gen_pow_inj34 (by omega) (by omega) h2).symm
    obtain ⟨haall, -⟩ := holdsList_flat mAgg (List.all_eq_true.mpr aflat) _ _ (hln h419)
    exact call_of_flat haall acall
  · exact call_of_flat hpost qsd
  · have l1 := load_sound ql447 atQ
    rw [const_sound qc446 atQ, word_one, assertEq_sound qe1 atQ] at l1
    have l2 := load_sound ql451 atQ
    rw [isMul_sound qm450 atQ, const_sound qc448 atQ, const_sound qc449 atQ, word_one, word_gen,
      one_mul, assertEq_sound qe2 atQ] at l2
    refine ⟨l1, ?_⟩
    have l2' : LoadHolds rd (1 * gen ^ 1) 0 (σ (.n 445)) := by rwa [one_mul, pow_one]
    have := (loadHolds_mul_gen_pow rd 1 1 0 _).mp l2'
    simpa using this

end
end LeanVM.Guest.B1.Main
