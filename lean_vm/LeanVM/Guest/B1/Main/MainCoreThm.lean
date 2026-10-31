/-
  LeanVM.Guest.B1.Main.MainCoreThm

  `main_core`: what holds of `main`'s honest valuation.
-/

module

public import LeanVM.Guest.B1.Main.MainCore

/-!
# `main`'s honest valuation holds

The evaluated block's equations (`Fwd.ev_spec`) give the oracle's values and the products, sums
and constants the proof reads; the atoms hold block by block (`atoms_holds_stores`): the range
checks on the memory defined below `2^16` (`rc_side`), the reads of the last running count, the
published DA digest and the header, the equality checks on the honest words; then the stores:
the byte table, the first running count, the own DA digest (the checked claim's, by its chain
`chain_final`, or zeros) and the leaf's deferred claim.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd

@[expose] public section

set_option maxRecDepth 20000 in
/-- **`main`'s honest valuation holds** on a memory defined below `2^16` holding `main`'s words. -/
theorem main_core {rd : Reader} {m : MainIn} (hl : Sig.MemOK rd (2 ^ 16)) (hb : MainBounds m)
    (hm : MainMem rd m) : MVals rd (mσ rd m) m := by
  have hok := mainc_ok
  unfold mainCOk at hok
  simp only [Bool.and_eq_true, Option.isSome_iff_exists, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨⟨⟨c', hchk⟩, hcan1⟩, hcan2⟩, hcan3⟩, hcan4⟩, hside⟩ := hok
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = mσ rd m := ⟨_, rfl⟩
  rw [← hσ]
  have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
  obtain ⟨-, -, hgs⟩ := ev_spec rd (mOrc m) mFlatE [] hchk
  have hG : ∀ s ∈ mFlatE, GoodS rd mStores (mOrc m) σ s := fun s hs => by rw [hσ]; exact hgs s hs
  have hgA : ∀ a ∈ atomsIn mFlat, Good rd mStores (mOrc m) σ a := fun a ha =>
    hG _ (atom_mem_of_atomsIn' ha)
  -- the located values
  have hD : ∀ a ∈ mDefAtoms, Good rd mStores (mOrc m) σ a := by
    intro a ha
    obtain ⟨b, hb', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp mDefAtoms_ok a ha)
    rw [atomEqb_sound he]
    exact hG _ (atom_mem_of_atomsIn' hb')
  have horc : ∀ j ∈ mOrcIdx, σ (.n j) = mOrc m j := by
    intro j hj
    obtain ⟨s, hs, hv⟩ := mOrcIdx_defs j hj
    obtain ⟨s', hs', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp mOrcStmts_ok s hs)
    rw [← stmtEqb_sound he] at hv
    exact goodS_defs (hG s' hs') _ hv
  have hO : ∀ {j : ℕ}, j ∈ mOrcIdx → σ (.n j) = mOrc m j := fun hj => horc _ hj
  have gM : ∀ (d x y : ℕ), x < d → y < d → Atom.mul (.n d) (.n x) (.n y) ∈ mDefAtoms →
      σ (.n d) = σ (.n x) * σ (.n y) := fun d x y hx hy h => good_mul' hx hy (hD _ h)
  have gA : ∀ (d x y : ℕ), Atom.add (.n d) (.n x) (.n y) ∈ mDefAtoms →
      σ (.n d) = σ (.n x) + σ (.n y) := fun d x y h => hD _ h
  have gC : ∀ (d : ℕ) (c : E), Atom.const (.n d) c ∈ mDefAtoms → σ (.n d) = c :=
    fun d c h => hD _ h
  have one : ∀ d, Atom.const (.n d) (word 1 0 0) ∈ mDefAtoms → σ (.n d) = 1 := fun d h => by
    rw [gC d _ h, word_one]
  have two : ∀ d, Atom.const (.n d) (word 2 0 0) ∈ mDefAtoms → σ (.n d) = gen := fun d h => by
    rw [gC d _ h, word_gen]
  have gd : ∀ d x y e, Atom.const (.n x) (word 1 0 0) ∈ mDefAtoms →
      Atom.add (.n d) (.n x) (.n y) ∈ mDefAtoms → σ (.n y) = gen ^ e → σ (.n d) = 1 + gen ^ e :=
    fun d x y e hx hd hy => by rw [gA d x y hd, one x hx, hy]
  -- the counts
  have v0 : σ (.n 0) = gen ^ m.nlx := by rw [hO (by decide)]; rfl
  have v1 : σ (.n 1) = gen ^ m.nxd := by rw [hO (by decide)]; rfl
  have v2 : σ (.n 2) = gen ^ m.nrx := by rw [hO (by decide)]; rfl
  have v3 : σ (.n 3) = gen ^ m.nls := by rw [hO (by decide)]; rfl
  have v4 : σ (.n 4) = gen ^ m.nsd := by rw [hO (by decide)]; rfl
  have v5 : σ (.n 5) = gen ^ m.nrs := by rw [hO (by decide)]; rfl
  have v6 : σ (.n 6) = gen ^ m.nc := by rw [hO (by decide)]; rfl
  have v7 : σ (.n 7) = gen ^ m.nd := by rw [hO (by decide)]; rfl
  have v40 : σ (.n 40) = gen ^ (m.nlx + m.nxd) := by
    rw [gM 40 0 1 (by norm_num) (by norm_num) (by decide +kernel), v0, v1, pow_add]
  have v41 : σ (.n 41) = gen ^ (m.nls + m.nsd) := by
    rw [gM 41 3 4 (by norm_num) (by norm_num) (by decide +kernel), v3, v4, pow_add]
  have v42 : σ (.n 42) = gen ^ m.total := by
    rw [gM 42 40 41 (by norm_num) (by norm_num) (by decide +kernel), v40, v41, ← pow_add]; rfl
  have v52 : σ (.n 52) = gen ^ (4 * (m.nlx + m.nxd)) := by
    rw [gM 52 51 51 (by norm_num) (by norm_num) (by decide +kernel),
      gM 51 40 40 (by norm_num) (by norm_num) (by decide +kernel), v40, ← pow_add, ← pow_add]
    exact congrArg (HPow.hPow gen) (by ring)
  have v55 : σ (.n 55) = gen ^ (4 * (m.nls + m.nsd)) := by
    rw [gM 55 54 54 (by norm_num) (by norm_num) (by decide +kernel),
      gM 54 41 41 (by norm_num) (by norm_num) (by decide +kernel), v41, ← pow_add, ← pow_add]
    exact congrArg (HPow.hPow gen) (by ring)
  have vDa : σ (.n 334) = m.aDa := by rw [hO (by decide)]; simp [mOrc]
  have v409 : σ (.n 380) = m.a409 := by rw [hO (by decide)]; simp [mOrc]
  have vpick : σ (.n 387) = gen ^ m.pick := by rw [hO (by decide)]; simp [mOrc]
  have v333 : σ (.n 333) = gen ^ (2 * (m.nc + 1)) := by
    rw [gM 333 332 332 (by norm_num) (by norm_num) (by decide +kernel),
      gM 332 6 331 (by norm_num) (by norm_num) (by decide +kernel), v6,
      two 331 (by decide +kernel), ← pow_succ, ← pow_add]
    exact congrArg (HPow.hPow gen) (by ring)
  have v336 : σ (.n 336) = m.aDa * gen ^ (2 * m.nc) := by
    rw [gM 336 334 335 (by norm_num) (by norm_num) (by decide +kernel),
      gM 335 6 6 (by norm_num) (by norm_num) (by decide +kernel), vDa, v6, ← pow_add, two_mul]
  have v338 : σ (.n 338) = gen ^ m.nd + gen := by
    rw [gA 338 7 337 (by decide +kernel), v7, two 337 (by decide +kernel)]
  have v364 : σ (.n 364) = gen ^ (2 * m.nc) := by
    rw [gM 364 6 6 (by norm_num) (by norm_num) (by decide +kernel), v6, ← pow_add, two_mul]
  have v370 : σ (.n 370) = gen ^ (24 * m.nc) := by
    rw [gM 370 369 369 (by norm_num) (by norm_num) (by decide +kernel),
      gM 369 368 368 (by norm_num) (by norm_num) (by decide +kernel),
      gM 368 367 367 (by norm_num) (by norm_num) (by decide +kernel),
      gM 367 366 6 (by norm_num) (by norm_num) (by decide +kernel),
      gM 366 6 6 (by norm_num) (by norm_num) (by decide +kernel), v6, ← pow_add, ← pow_add,
      ← pow_add, ← pow_add, ← pow_add]
    exact congrArg (HPow.hPow gen) (by ring)
  have v376 : σ (.n 376) = gen ^ (24 * m.nc) := by
    rw [gM 376 375 375 (by norm_num) (by norm_num) (by decide +kernel),
      gM 375 374 374 (by norm_num) (by norm_num) (by decide +kernel),
      gM 374 373 373 (by norm_num) (by norm_num) (by decide +kernel),
      gM 373 372 6 (by norm_num) (by norm_num) (by decide +kernel),
      gM 372 6 6 (by norm_num) (by norm_num) (by decide +kernel), v6, ← pow_add, ← pow_add,
      ← pow_add, ← pow_add, ← pow_add]
    exact congrArg (HPow.hPow gen) (by ring)
  have v379 : σ (.n 379) = gen ^ (m.nc + 1) := by
    rw [gM 379 6 378 (by norm_num) (by norm_num) (by decide +kernel), v6,
      two 378 (by decide +kernel), pow_succ]
  have v381 : σ (.n 381) = gen ^ (m.nrx + m.nrs) := by
    rw [gM 381 2 5 (by norm_num) (by norm_num) (by decide +kernel), v2, v5, pow_add]
  have v385 : σ (.n 385) = m.a409 * gen ^ m.nc := by
    rw [gM 385 380 6 (by norm_num) (by norm_num) (by decide +kernel), v409, v6]
  have v389 : σ (.n 389) = gen ^ (m.nc + 1) := by
    rw [gM 389 6 388 (by norm_num) (by norm_num) (by decide +kernel), v6,
      two 388 (by decide +kernel), pow_succ]
  have v391 : σ (.n 391) = gen ^ m.nc := by
    rw [gM 391 389 390 (by norm_num) (by norm_num) (by decide +kernel), v389,
      gC 390 (word 9223372036854775821 0 0) (by decide +kernel), gen_pow_mul_ginv (by omega), Nat.add_sub_cancel]
  have v398 : σ (.n 398) = (gen ^ m.pick + gen ^ m.nc) * (gen ^ m.nd + 1) := by
    rw [gM 398 395 397 (by norm_num) (by norm_num) (by decide +kernel),
      gA 395 387 6 (by decide +kernel), gA 397 7 396 (by decide +kernel), vpick, v6, v7,
      one 396 (by decide +kernel)]
  have v401 : σ (.n 401) = m.aDa * gen ^ (2 * m.pick) := by
    rw [gM 401 334 400 (by norm_num) (by norm_num) (by decide +kernel),
      gM 400 387 387 (by norm_num) (by norm_num) (by decide +kernel), vDa, vpick, ← pow_add,
      two_mul]
  have v404 : σ (.n 404) = gen ^ m.nc + 1 := by
    rw [gA 404 6 403 (by decide +kernel), v6, one 403 (by decide +kernel)]
  have v433 : σ (.n 433) = 1 := one 433 (by decide +kernel)
  have v437 : σ (.n 437) = gen := by
    rw [gM 437 435 436 (by norm_num) (by norm_num) (by decide +kernel),
      one 435 (by decide +kernel), two 436 (by decide +kernel), one_mul]
  -- the reads
  have rdL : ∀ d p o v, Atom.load (.n d) (.n p) o ∈ mDefAtoms →
      Atom.load (.n d) (.n p) o ∉ mStoresL → LoadHolds rd (σ (.n p)) o v → σ (.n d) = v := by
    intro d p o v h hn hv
    rcases (hD _ h : Good rd mStores (mOrc m) σ (.load _ _ _)) with h | h
    · exact absurd (by rw [mStores_eq] at h; exact h) hn
    · rw [h, rdAt_of_load hv]
  have r386 : σ (.n 386) = gen ^ m.total :=
    rdL 386 385 0 _ (by decide +kernel) (by simp [mStoresL]) (by rw [v385]; exact hm.wN)
  have r429 : σ (.n 429) = (digestScalars m.dap).1 :=
    rdL 429 401 0 _ (by decide +kernel) (by simp [mStoresL]) (by
      rw [v401]; exact hm.dap 0 (by simp [digestCells]))
  have r430 : σ (.n 430) = (digestScalars m.dap).2 :=
    rdL 430 401 1 _ (by decide +kernel) (by simp [mStoresL]) (by
      rw [v401]; exact hm.dap 1 (by simp [digestCells]))
  have r434 : σ (.n 434) = (digestScalars m.sdg).1 :=
    rdL 434 433 0 _ (by decide +kernel) (by simp [mStoresL]) (by rw [v433]; exact hm.h0)
  have r438 : σ (.n 438) = (digestScalars m.sdg).2 :=
    rdL 438 437 0 _ (by decide +kernel) (by simp [mStoresL]) (by rw [v437]; exact hm.h1)
  -- the side conditions
  have hS : ∀ a ∈ atomsIn mFlat, a ∉ mStores → needsSide a = true →
      a.Holds rd σ ∨ Side rd mStores σ a := by
    intro a ha hnS hns
    right
    have hok := hside a ha
    rw [hns] at hok
    simp only [Bool.true_eq_false, false_or] at hok
    have hg := hgA a ha
    cases a with
    | rangeCheck x y t1 t2 k =>
      simp only [mSideOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨⟨hp, hx⟩, hk⟩, hlt⟩ := hok
      rw [hx, hk] at hg ⊢
      rw [hk] at hlt
      simp only [rcPairs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hp
      rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
          ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hg ⊢ <;> rw [h2] at hlt
      · exact rc_side hl v0 (by rw [gC 8 (word 9272771591053052074 0 0) (by decide +kernel), word_gmax]) hb.lx (by norm_num) hlt hg
      · exact rc_side hl v1 (by rw [gC 12 (word 9272771591053052074 0 0) (by decide +kernel), word_gmax]) hb.xd (by norm_num) hlt hg
      · exact rc_side hl v2 (by rw [gC 16 (word 9272771591053052074 0 0) (by decide +kernel), word_gmax]) hb.rx (by norm_num) hlt hg
      · exact rc_side hl v3 (by rw [gC 20 (word 9272771591053052074 0 0) (by decide +kernel), word_gmax]) hb.ls (by norm_num) hlt hg
      · exact rc_side hl v4 (by rw [gC 24 (word 9272771591053052074 0 0) (by decide +kernel), word_gmax]) hb.sd (by norm_num) hlt hg
      · exact rc_side hl v5 (by rw [gC 28 (word 9272771591053052074 0 0) (by decide +kernel), word_gmax]) hb.rs (by norm_num) hlt hg
      · exact rc_side hl v6 (by rw [gC 32 (word 65536 0 0) (by decide +kernel), word_g16]) hb.nc (by norm_num) hlt hg
      · exact rc_side hl v7 (by rw [gC 36 (word 2 0 0) (by decide +kernel), word_g1]) hb.nd (by norm_num) hlt hg
      · exact rc_side hl v42 (by rw [gC 43 (word 9272771591053052074 0 0) (by decide +kernel), word_gmax]) hb.total (by norm_num)
          hlt hg
      · exact rc_side hl vpick v391 hb.pick (by have := hb.nc; omega) hlt hg
    | load d p o =>
      simp only [mSideOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨hd, hp⟩, hl'⟩ := hok
      simp only [mLoadOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.mem_cons,
        Prod.mk.injEq, List.not_mem_nil, or_false] at hl'
      rw [hd, hp] at hnS ⊢
      simp only [Side]
      simp only [hnS, ↓reduceIte]
      rcases hl' with (((⟨e1, e2, rfl⟩ | ⟨e1, e2, rfl⟩ | ⟨e1, e2, rfl⟩ | ⟨e1, e2, rfl⟩ |
          ⟨e1, e2, rfl⟩) | hs) | hs) | hs
      · rw [e2, v385]; exact ⟨hm.wN.1, by rw [hm.wN.2]; rfl⟩
      · rw [e2, v401]
        have h := hm.dap 0 (by simp [digestCells])
        exact ⟨h.1, by rw [h.2]; rfl⟩
      · rw [e2, v401]
        have h := hm.dap 1 (by simp [digestCells])
        exact ⟨h.1, by rw [h.2]; rfl⟩
      · rw [e2, v433]; exact ⟨hm.h0.1, by rw [hm.h0.2]; rfl⟩
      · rw [e2, v437]; exact ⟨hm.h1.1, by rw [hm.h1.2]; rfl⟩
      all_goals exfalso; apply hnS; rw [mStores_eq]
      · obtain ⟨⟨e1, e2⟩, e3⟩ := hs
        rw [e1, e2]
        simp only [mStoresL, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inl (Or.inl (Or.inl ⟨o, e3, rfl⟩))
      · rcases hs with ⟨e1, e2, rfl⟩ | ⟨e1, e2, rfl⟩ | ⟨e1, e2, rfl⟩ | ⟨e1, e2, rfl⟩ |
          ⟨e1, e2, rfl⟩ <;> rw [e1, e2] <;> simp [mStoresL]
      · obtain ⟨e1, ⟨e3, e2⟩ | ⟨rfl, e2⟩⟩ := hs
        · rw [e1, e2]
          simp only [mStoresL, List.mem_append, List.mem_map, List.mem_range]
          exact Or.inl (Or.inr ⟨o, e3, rfl⟩)
        · rw [e1, e2]; simp [mStoresL]
    | assertEq x y =>
      simp only [mSideOk, decide_eq_true_eq, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
        or_false] at hok
      simp only [Side]
      rw [e_add_eq_zero_iff]
      rcases hok with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [r386, v42]
      · rw [v398, gC 399 (word 0 0 0) (by decide +kernel), word_zero]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb.nd with h | h
        · rw [h, pow_zero, show (1 : E) + 1 = 0 from e_add_eq_zero_iff.mpr rfl, mul_zero]
        · rw [hb.pickD h, show gen ^ m.nc + gen ^ m.nc = 0 from e_add_eq_zero_iff.mpr rfl,
            zero_mul]
      · rw [r434, hO (by decide)]; simp [mOrc]
      · rw [r438, hO (by decide)]; simp [mOrc]
    | _ => simp [mSideOk] at hok
  -- the stores' words
  have hbyte : ∀ v < 256, σ (.n (69 + v)) = word v 0 0 := by
    intro v hv
    obtain ⟨b, hb', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp mByte_ok v (List.mem_range.mpr hv))
    have := hG _ (atom_mem_of_atomsIn' hb')
    rw [← atomEqb_sound he] at this
    exact this
  have hleafc : ∀ k < 23, σ (.n (406 + k)) = 0 := by
    intro k hk
    obtain ⟨b, hb', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp mLeafC_ok k (List.mem_range.mpr hk))
    have := hG _ (atom_mem_of_atomsIn' hb')
    rw [← atomEqb_sound he] at this
    rw [show σ (.n (406 + k)) = word 0 0 0 from this, word_zero]
  have hzc : ∀ d, Atom.const (.n d) (word 0 0 0) ∈ atomsIn mDaZ → σ (.n d) = 0 := by
    intro d h
    have h' := atom_mem_of_atomsIn' h
    have hs : Stmt.atom (.const (.n d) (word 0 0 0)) ∈ mFlat := by
      clear * - h'; simp only [mFlat, List.mem_append]; tauto
    have := hgA _ (mem_atomsIn' hs)
    exact (show σ (.n d) = word 0 0 0 from this).trans word_zero
  -- the blocks
  have hsubF : ∀ {P : List Stmt}, (∀ s ∈ P, s ∈ mFlat) → ∀ a ∈ atomsIn P, a ∈ atomsIn mFlat :=
    fun hP a ha => mem_atomsIn' (hP _ (atom_mem_of_atomsIn' ha))
  obtain ⟨sB, sDa, sDaZ, sLf⟩ := mStoresIn
  have blk : ∀ {P : List Stmt} {A : List ℕ}, (∀ s ∈ P, s ∈ mFlat) →
      canonChk A (noStores P) = true → (∀ i ∈ A, IsCanonical128 (σ (.n i))) →
      ((∀ a ∈ atomsIn P, a ∉ mStores → a.Holds rd σ) → ∀ a ∈ atomsIn P, a ∈ mStores →
        a.Holds rd σ) → ∀ a ∈ atomsIn P, a.Holds rd σ := by
    intro P A hP hc hA hst
    have hsub := hsubF hP
    exact atoms_holds_stores (S := mStores) hidx hc (fun a ha => hgA a (hsub a ha)) hA
      (fun a ha hnS hns => hS a (hsub a ha) hnS hns) hst
  have hB1 : ∀ a ∈ atomsIn (mPre ++ mMid ++ mPost), a.Holds rd σ := by
    refine blk (A := []) (fun s hs => by
      clear * - hs; simp only [List.mem_append] at hs; simp only [mFlat, List.mem_append]; tauto)
      hcan1
      (by simp) (fun _ a ha haS => ?_)
    have := mem_storesIn sB ha haS
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at this
    rcases this with ⟨v, hv, rfl⟩ | rfl
    · show LoadHolds rd (σ (.n 68)) v (σ (.n (69 + v)))
      rw [hO (by decide), hbyte v hv]
      have := hm.bytes v (by simpa using hv)
      simpa [mOrc] using this
    · show LoadHolds rd (σ (.n 380)) 0 (σ (.n 381))
      rw [v409, v381]; exact hm.w0
  have mB1 : ∀ {P : List Stmt}, (∀ s ∈ P, s ∈ mPre ++ mMid ++ mPost) →
      ∀ a ∈ atomsIn P, a.Holds rd σ := fun hP a ha => hB1 a (mem_atomsIn' (hP _ (atom_mem_of_atomsIn' ha)))
  have hDa : m.nd = 1 → ∀ a ∈ atomsIn mDa, a.Holds rd σ := by
    intro h1
    obtain ⟨hl4, hcanR⟩ := hb.daR h1
    have hR : ∀ i ∈ [339, 340, 341, 342], σ (.n i) = m.daR.getD (i - 339) 0 := by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> rw [hO (by decide)] <;> simp [mOrc]
    have hRl : [σ (.n 339), σ (.n 340), σ (.n 341), σ (.n 342)] = m.daR := by
      rw [hR 339 (by simp), hR 340 (by simp), hR 341 (by simp), hR 342 (by simp)]
      match hd : m.daR, hl4 with
      | [a, b, c, d], _ => rfl
    refine blk (fun s hs => by clear * - hs; simp only [mFlat, List.mem_append]; tauto) hcan2
      (fun i hi => ?_)
      (fun h1' a ha haS => ?_)
    · rw [hR i hi]
      apply hcanR
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;>
        (rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
    · have hA' : ∀ b ∈ noStores mDa, b.Holds rd σ := fun b hb' =>
        h1' b (List.mem_filter.mp hb').1 (by simpa using (List.mem_filter.mp hb').2)
      obtain ⟨hsp, ho0, ho1⟩ := daSpec_ok
      obtain ⟨hd, -⟩ := chain_final hsp rfl hA' (pre := []) (n := 0) rfl
        (fun c => (cellsOfState_zero false c).symm)
      have hv : (daSpec.vals σ).take (daSpec.len / 16) =
          [σ (.n 339), σ (.n 340), σ (.n 341), σ (.n 342)] := by
        simp [daSpec, pairSpec, ChainSpec.vals, srcVal]
      rw [hv, List.nil_append, hRl, ho0, ho1] at hd
      have hown := hm.own
      simp only [MainIn.ownDa, h1, ↓reduceIte] at hown
      have := mem_storesIn sDa ha haS
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl
      · show LoadHolds rd (σ (.n 336)) 0 (σ (.n 349))
        have e := congrArg Prod.fst hd
        simp only at e
        rw [v336, e]; exact hown 0 (by simp [digestCells])
      · show LoadHolds rd (σ (.n 336)) 1 (σ (.n 350))
        have e := congrArg Prod.snd hd
        simp only at e
        rw [v336, e]; exact hown 1 (by simp [digestCells])
  have hDaZ : m.nd ≠ 1 → ∀ a ∈ atomsIn mDaZ, a.Holds rd σ := by
    intro h1
    refine blk (A := []) (fun s hs => by clear * - hs; simp only [mFlat, List.mem_append]; tauto)
      hcan3
      (by simp) (fun _ a ha haS => ?_)
    have hown := hm.own
    simp only [MainIn.ownDa, h1, ↓reduceIte] at hown
    obtain ⟨c0, c1⟩ := mDaZC_ok
    have z0 := hzc 362 (atomEqb_sound (List.any_eq_true.mp c0).choose_spec.2 ▸
      (List.any_eq_true.mp c0).choose_spec.1)
    have z1 := hzc 363 (atomEqb_sound (List.any_eq_true.mp c1).choose_spec.2 ▸
      (List.any_eq_true.mp c1).choose_spec.1)
    have := mem_storesIn sDaZ ha haS
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl
    · show LoadHolds rd (σ (.n 336)) 0 (σ (.n 362))
      rw [v336, z0]; exact hown 0 (by simp)
    · show LoadHolds rd (σ (.n 336)) 1 (σ (.n 363))
      rw [v336, z1]; exact hown 1 (by simp)
  have hLeaf : m.nc = 0 → ∀ a ∈ atomsIn mLeaf, a.Holds rd σ := by
    intro h0
    refine blk (A := []) (fun s hs => by clear * - hs; simp only [mFlat, List.mem_append]; tauto)
      hcan4
      (by simp) (fun _ a ha haS => ?_)
    have := mem_storesIn sLf ha haS
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at this
    rcases this with ⟨k, hk, rfl⟩ | rfl
    · show LoadHolds rd (σ (.n 402)) k (σ (.n (406 + k)))
      rw [hO (by decide), hleafc k hk]
      have := hm.leaf h0 k (by simp; omega)
      rw [List.getElem_append_left (by simp; omega), List.getElem_replicate] at this
      simpa [mOrc] using this
    · show LoadHolds rd (σ (.n 402)) 23 (σ (.n 405))
      rw [hO (by decide), hO (by decide)]
      have := hm.leaf h0 23 (by simp)
      simpa [mOrc] using this
  exact ⟨mB1 (by intro s hs; clear * - hs; simp only [List.mem_append]; tauto),
    mB1 (by intro s hs; clear * - hs; simp only [List.mem_append]; tauto),
    mB1 (by intro s hs; clear * - hs; simp only [List.mem_append]; tauto),
    hDa, hDaZ, hLeaf, horc, v40, v41, v42, v52, v55,
    gd 62 61 1 _ (by decide +kernel) (by decide +kernel) v1, one 63 (by decide +kernel),
    gd 65 64 4 _ (by decide +kernel) (by decide +kernel) v4, one 66 (by decide +kernel),
    gd 326 325 2 _ (by decide +kernel) (by decide +kernel) v2, one 327 (by decide +kernel),
    gd 329 328 5 _ (by decide +kernel) (by decide +kernel) v5, one 330 (by decide +kernel),
    v333, v336, v338, v364, v370, v376, v379, v381,
    gd 383 382 6 _ (by decide +kernel) (by decide +kernel) v6, one 384 (by decide +kernel),
    v385, v401, v404, r429, r430, v433, v437⟩

end
end LeanVM.Guest.B1.Main
