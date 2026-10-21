/-
  LeanVM.Guest.B1.Comp.FsBlocks

  The inline Fiat-Shamir blocks over a completeness model: each block holds under the model's
  semantics at the honest values when the model answers the block's string.
-/

module

public import LeanVM.Guest.B1.Comp.Basic
public import LeanVM.Guest.B1.FsBlocks

/-!
# The inline Fiat-Shamir blocks over a completeness model

The backward halves of `FsBlocks.lean`'s iffs over a `CompModel`: `holdsB_fsCompressT_comp`,
`holdsB_fsNextT_comp`, `holdsB_squeezeStateT_comp`, `holdsB_squeezeT_comp`. Each is the converse of
the W2 soundness lemma (`holdsB_fsCompressT`, …) at the model's answers `CM.hm`: the block's values
are the honest ones with the output the answered digest (`fsValsD`, `sqStateValsD`, `sqValsD`),
and its `BLAKE2S` row is the model's (`CompModel.check_one`). At `CompModel.deployed` each gives
the deployed backward direction (`holds_fsCompressT_of_comp`, …).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.E2E.Complete

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The rows -/

/-- **`fs_compress`'s row over a completeness model**: with the top limb pinned, the block of the
state `cv` and `x` checks from the IV to the answer of its bytes. -/
theorem fs_compress_comp (CM : CompModel) (cv : Digest) (x : E) {tag : ℕ} (htag : tag < 256)
    {d : Digest} (hd : CM.H (digestBytes cv ++ blockOf x tag) = some d) :
    CM.sem.check (fsBlock (digestScalars cv) x (ofK (x.limb 2)) (eOfNat tag)) ivCells.1 ivCells.2
      (digestScalars d).1 (digestScalars d).2 (metadataCell 64 true) := by
  have hc := fsBlock_canonical cv x tag
  rw [fsBlock_eq] at hc ⊢
  rw [← blockBytes_fs cv x htag] at hd
  exact CM.check_one hc hd

/-- **`squeeze_state`'s row over a completeness model**: the block of the state `cv` and the
zero scalar at `tag` checks from the IV to the answer of its bytes. -/
theorem squeeze_state_comp (CM : CompModel) (cv : Digest) {tag : ℕ} (htag : tag < 256)
    {d : Digest} (hd : CM.H (digestBytes cv ++ blockOf 0 tag) = some d) :
    CM.sem.check ![(digestScalars cv).1, (digestScalars cv).2, 0, y * eOfNat tag] ivCells.1
      ivCells.2 (digestScalars d).1 (digestScalars d).2 (metadataCell 64 true) := by
  rw [squeezeBlock_eq]
  rw [← blockBytes_fs cv 0 htag] at hd
  refine CM.check_one (fun i ↦ ?_) hd
  fin_cases i
  · exact (isCanonical128_digestScalars cv).1
  · exact (isCanonical128_digestScalars cv).2
  · rfl
  · rfl

/-! ## `fs_compress`, `obs`, `absorb_nonce`, `fs_next` -/

/-- **`fs_compress` over a completeness model** (TRIAGE #5; `obs` #6 at tag 1, `absorb_nonce` #10
at tag 4): the converse of `holdsB_fsCompressT`: from the state of `cv`, with the model answering
the absorb of `blockOf x tag` by `d`, the block holds at the values `fsValsD`. -/
theorem holdsB_fsCompressT_comp {CM : CompModel} (s0 s1 x : V) (b : ℕ) {tag : ℕ}
    (htag : tag < 256) {next : Prop} {kret : List E → Prop}
    (h : (∃ cv d, (σ s0, σ s1) = digestScalars cv ∧
        CM.H (digestBytes cv ++ blockOf (σ x) tag) = some d ∧
        ∀ k, 2 ≤ k → k < 14 → σ (.n (b + k)) = fsValsD (σ x) d tag k) ∧ next) :
    Stmt.HoldsListB CM.sem C rd σ (fsCompressT s0 s1 x b tag) next kret := by
  simp only [fsCompressT, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, true_and, word_eOfNat,
    word_yy, word_y_mul, word_iv0, word_iv1, word_md64]
  obtain ⟨⟨cv, d, hcv, hd, e⟩, hn⟩ := h
  have e2 : σ (.n (b + 2)) = ofK ((σ x).limb 2) := e 2 le_rfl (by omega)
  have e3 : σ (.n (b + 3)) = eOfNat tag := e 3 (by omega) (by omega)
  have e4 : σ (.n (b + 4)) = y * y := e 4 (by omega) (by omega)
  have e5 : σ (.n (b + 5)) = y * y * ofK ((σ x).limb 2) := e 5 (by omega) (by omega)
  have e6 : σ (.n (b + 6)) = σ x + y * y * ofK ((σ x).limb 2) := e 6 (by omega) (by omega)
  have e7 : σ (.n (b + 7)) = y * eOfNat tag := e 7 (by omega) (by omega)
  have e8 : σ (.n (b + 8)) = ofK ((σ x).limb 2) + y * eOfNat tag := e 8 (by omega) (by omega)
  have e9 : σ (.n (b + 9)) = Value.ivCells.1 := e 9 (by omega) (by omega)
  have e10 : σ (.n (b + 10)) = Value.ivCells.2 := e 10 (by omega) (by omega)
  have e11 : σ (.n (b + 11)) = metadataCell 64 true := e 11 (by omega) (by omega)
  have e12 : σ (.n (b + 12)) = (digestScalars d).1 := e 12 (by omega) (by omega)
  have e13 : σ (.n (b + 13)) = (digestScalars d).2 := e 13 (by omega) (by omega)
  refine ⟨e3, ⟨by rw [e2]; exact ofK_isInK _, by rw [e3]; exact eOfNat_isInK tag⟩, e4,
    by rw [e5, e4, e2], by rw [e6, e5], e7, by rw [e8, e7, e2], e9, e10, e11, ?_, hn⟩
  have hc := fs_compress_comp CM cv (σ x) htag hd
  rw [fsBlock] at hc
  rw [e6, e8, e9, e10, e11, e12, e13, show σ s0 = _ from congrArg Prod.fst hcv,
    show σ s1 = _ from congrArg Prod.snd hcv]
  exact hc

/-- **`fs_next` over a completeness model** (TRIAGE #7): the converse of `holdsB_fsNextT`. -/
theorem holdsB_fsNextT_comp {CM : CompModel} (s0 s1 cur : V) (j b : ℕ) {next : Prop}
    {kret : List E → Prop}
    (h : (LoadHolds rd (σ cur) j (σ (.n b)) ∧ ∃ cv d, (σ s0, σ s1) = digestScalars cv ∧
      obsCvM CM.hm cv (σ (.n b)) = some d ∧
        ∀ k, 2 ≤ k → k < 14 → σ (.n (b + 1 + k)) = fsValsD (σ (.n b)) d 1 k) ∧ next) :
    Stmt.HoldsListB CM.sem C rd σ (fsNextT s0 s1 cur j b) next kret := by
  obtain ⟨⟨hl, cv, d, hcv, hd, e⟩, hn⟩ := h
  exact ⟨hl, holdsB_fsCompressT_comp s0 s1 (.n b) (b + 1) (by decide) ⟨⟨cv, d, hcv, hd, e⟩, hn⟩⟩

/-! ## `squeeze_state`, `challenge_from_state`, `squeeze` -/

/-- **`squeeze_state` over a completeness model** (TRIAGE #8): the converse of
`holdsB_squeezeStateT`. -/
theorem holdsB_squeezeStateT_comp {CM : CompModel} (s0 s1 : V) (b : ℕ) {tag : ℕ}
    (htag : tag < 256) {next : Prop} {kret : List E → Prop}
    (h : (∃ cv d, (σ s0, σ s1) = digestScalars cv ∧
        CM.H (digestBytes cv ++ blockOf 0 tag) = some d ∧
        ∀ k, k < 7 → σ (.n (b + k)) = sqStateValsD d tag k) ∧ next) :
    Stmt.HoldsListB CM.sem C rd σ (squeezeStateT s0 s1 b tag) next kret := by
  simp only [squeezeStateT, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, word_y_mul, eOfNat_zero,
    mul_zero, word_iv0, word_iv1, word_md64]
  obtain ⟨⟨cv, d, hcv, hd, e⟩, hn⟩ := h
  have e0 : σ (.n b) = 0 := e 0 (by omega)
  have e1 : σ (.n (b + 1)) = y * eOfNat tag := e 1 (by omega)
  have e2 : σ (.n (b + 2)) = Value.ivCells.1 := e 2 (by omega)
  have e3 : σ (.n (b + 3)) = Value.ivCells.2 := e 3 (by omega)
  have e4 : σ (.n (b + 4)) = metadataCell 64 true := e 4 (by omega)
  have e5 : σ (.n (b + 5)) = (digestScalars d).1 := e 5 (by omega)
  have e6 : σ (.n (b + 6)) = (digestScalars d).2 := e 6 (by omega)
  refine ⟨e0, e1, e2, e3, e4, ?_, hn⟩
  rw [e0, e1, e2, e3, e4, e5, e6, show σ s0 = (digestScalars cv).1 from congrArg Prod.fst hcv,
    show σ s1 = (digestScalars cv).2 from congrArg Prod.snd hcv]
  exact squeeze_state_comp CM cv htag hd

/-- **`squeeze` over a completeness model** (TRIAGE #9, #4; `squeeze_step` #11): the converse of
`holdsB_squeezeT`. -/
theorem holdsB_squeezeT_comp {CM : CompModel} (s0 s1 : V) (b : ℕ) {next : Prop}
    {kret : List E → Prop}
    (h : (∃ cv d, (σ s0, σ s1) = digestScalars cv ∧ sqCvM CM.hm cv = some d ∧
        ∀ k, k < 14 → σ (.n (b + k)) = sqValsD d k) ∧ next) :
    Stmt.HoldsListB CM.sem C rd σ (squeezeT s0 s1 b) next kret := by
  rw [squeezeT, holdsListB_append]
  obtain ⟨⟨cv, d, hcv, hd, e⟩, hn⟩ := h
  refine holdsB_squeezeStateT_comp s0 s1 b (by decide)
    ⟨⟨cv, d, hcv, hd, fun k hk ↦ by rw [e k (by omega)]; interval_cases k <;> rfl⟩, ?_⟩
  simp only [challengeT, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, true_and, word_yy,
    Nat.add_assoc, Nat.reduceAdd]
  have e7 : σ (.n (b + 7)) = ofK ((digestScalars d).2.limb 0) := e 7 (by omega)
  have e8 : σ (.n (b + 8)) = (digestScalars d).2 + ofK ((digestScalars d).2.limb 0) :=
    e 8 (by omega)
  have e9 : σ (.n (b + 9)) = word 1 0 1 := e 9 (by omega)
  have e10 : σ (.n (b + 10)) =
      ((digestScalars d).2 + ofK ((digestScalars d).2.limb 0)) * word 1 0 1 := e 10 (by omega)
  have e11 : σ (.n (b + 11)) = y * y := e 11 (by omega)
  have e12 : σ (.n (b + 12)) = y * y * ofK ((digestScalars d).2.limb 0) := e 12 (by omega)
  have e13 : σ (.n (b + 13)) = challengeOf d := e 13 (by omega)
  have e5 : σ (.n (b + 5)) = (digestScalars d).1 := e 5 (by omega)
  have e6 : σ (.n (b + 6)) = (digestScalars d).2 := e 6 (by omega)
  refine ⟨by rw [e8, e6, e7], e9, by rw [e10, e8, e9], ⟨by rw [e7]; exact ofK_isInK _, ?_⟩, e11,
    by rw [e12, e11, e7], ?_, hn⟩
  · rw [e10, word_y_inv]
    exact ((split_iff _ _).mpr ⟨(isCanonical128_digestScalars _).2, rfl⟩).2
  · rw [e13, e12, e5, challenge_from_state_eq]

/-! ## At the deployed model -/

/-- The deployed backward direction of `holds_fsCompressT`, from the generic one. -/
theorem holds_fsCompressT_of_comp (s0 s1 x : V) (b : ℕ) {tag : ℕ} (htag : tag < 256)
    {next : Prop} {kret : List E → Prop}
    (h : (∃ cv, (σ s0, σ s1) = digestScalars cv ∧
        ∀ k, 2 ≤ k → k < 14 → σ (.n (b + k)) = fsVals (σ x) cv tag k) ∧ next) :
    Stmt.HoldsList C rd σ (fsCompressT s0 s1 x b tag) next kret := by
  rw [← holdsListB_deployed]
  obtain ⟨⟨cv, hcv, e⟩, hn⟩ := h
  exact holdsB_fsCompressT_comp (CM := CompModel.deployed) s0 s1 x b htag
    ⟨⟨cv, _, hcv, rfl, fun k hk1 hk2 ↦ by rw [e k hk1 hk2]; interval_cases k <;> rfl⟩, hn⟩

/-- The deployed backward direction of `holds_squeezeT`, from the generic one. -/
theorem holds_squeezeT_of_comp (s0 s1 : V) (b : ℕ) {next : Prop} {kret : List E → Prop}
    (h : (∃ cv, (σ s0, σ s1) = digestScalars cv ∧ ∀ k, k < 14 → σ (.n (b + k)) = sqVals cv k) ∧
        next) :
    Stmt.HoldsList C rd σ (squeezeT s0 s1 b) next kret := by
  rw [← holdsListB_deployed]
  obtain ⟨⟨cv, hcv, e⟩, hn⟩ := h
  exact holdsB_squeezeT_comp (CM := CompModel.deployed) s0 s1 b
    ⟨⟨cv, _, hcv, sqCvM_hm_deployed cv, fun k hk ↦ by rw [e k hk]; interval_cases k <;> rfl⟩, hn⟩

end
end LeanVM.Guest.B1
