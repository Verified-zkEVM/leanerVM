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
checks on the memory defined below `2^16` (`rc_side`), the reads of the running count and the
header, the equality checks on the honest words, the nonzero check on a declared claim; then the
stores: the byte table, the first running count and the leaf's deferred claim.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd

@[expose] public section

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`main`'s honest valuation holds** on a memory defined below `2^16` holding `main`'s words. -/
theorem main_core {rd : Reader} {m : MainIn} (hl : Sig.MemOK rd (2 ^ 16)) (hb : MainBounds m)
    (hm : MainMem rd m) : MVals rd (mσ rd m) m := by
  have hok := mainc_ok
  unfold mainCOk at hok
  simp only [Bool.and_eq_true, Option.isSome_iff_exists, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨⟨⟨c', hchk⟩, hinv⟩, hcan1⟩, hcan2⟩, hcan3⟩, hside⟩ := hok
  have hhint : mFlat.getD 61 default = .atom (.hint (.inverse (.n 94) (.n 95))) := stmtEqb_sound hinv
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = mσ rd m := ⟨_, rfl⟩
  rw [← hσ]
  have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
  obtain ⟨-, -, hgs⟩ := ev_spec rd (mOrc m) mFlatE [] hchk
  have hG : ∀ s ∈ mFlatE, GoodS rd mStores (mOrc m) σ s := fun s hs => by rw [hσ]; exact hgs s hs
  -- the statements of `mFlat`
  have hmem : ∀ s ∈ mFlat, s ∈ mFlatE ∨ s = .atom (.hint (.inverse (.n 94) (.n 95))) := by
    intro s hs
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
    by_cases h61 : i = 61
    · subst h61
      right
      rw [← hhint, List.getD_eq_getElem _ _ hi]
    · exact Or.inl (List.mem_eraseIdx_iff_getElem.mpr ⟨i, hi, h61, rfl⟩)
  -- the located values
  have hD : ∀ a ∈ mDefAtoms, Good rd mStores (mOrc m) σ a := by
    intro a ha
    obtain ⟨b, hb', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp mDefAtoms_ok a ha)
    rw [atomEqb_sound he]
    exact hG _ (atom_mem_of_atomsIn' hb')
  have hgA : ∀ a ∈ atomsIn mFlat, Good rd mStores (mOrc m) σ a := by
    intro a ha
    rcases hmem _ (atom_mem_of_atomsIn' ha) with h | h
    · exact hG _ h
    · cases h
      have hne := hD (.assertNe (.n 94) (.n 95) (.n 96)) (by simp [mDefAtoms])
      exact hne.1
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
  -- the counts
  have v0 : σ (.n 0) = gen ^ m.nlx := by rw [hO (by decide)]; rfl
  have v1 : σ (.n 1) = gen ^ m.nxd := by rw [hO (by decide)]; rfl
  have v2 : σ (.n 2) = gen ^ m.nrx := by rw [hO (by decide)]; rfl
  have v3 : σ (.n 3) = gen ^ m.nls := by rw [hO (by decide)]; rfl
  have v4 : σ (.n 4) = gen ^ m.nsd := by rw [hO (by decide)]; rfl
  have v5 : σ (.n 5) = gen ^ m.nrs := by rw [hO (by decide)]; rfl
  have v6 : σ (.n 6) = gen ^ m.nc := by rw [hO (by decide)]; rfl
  have v7 : σ (.n 7) = gen ^ m.nd := by rw [hO (by decide)]; rfl
  have v40 : σ (.n 40) = gen ^ m.nda := by rw [hO (by decide)]; simp [mOrc]
  have v41 : σ (.n 41) = gen ^ m.ndd := by rw [hO (by decide)]; simp [mOrc]
  have v50 : σ (.n 50) = gen ^ (m.nda + m.ndd) := by
    rw [gM 50 40 41 (by norm_num) (by norm_num) (by simp [mDefAtoms]), v40, v41, pow_add]
  have v55 : σ (.n 55) = gen ^ (m.nlx + m.nxd) := by
    rw [gM 55 0 1 (by norm_num) (by norm_num) (by simp [mDefAtoms]), v0, v1, pow_add]
  have v56 : σ (.n 56) = gen ^ (m.nls + m.nsd) := by
    rw [gM 56 3 4 (by norm_num) (by norm_num) (by simp [mDefAtoms]), v3, v4, pow_add]
  have v57 : σ (.n 57) = gen ^ (m.nlx + m.nxd + (m.nls + m.nsd)) := by
    rw [gM 57 55 56 (by norm_num) (by norm_num) (by simp [mDefAtoms]), v55, v56, ← pow_add]
  have v58 : σ (.n 58) = gen ^ m.total := by
    rw [gM 58 57 50 (by norm_num) (by norm_num) (by simp [mDefAtoms]), v57, v50, ← pow_add]; rfl
  have v68 : σ (.n 68) = gen ^ (4 * (m.nda + m.ndd)) := by
    rw [gM 68 67 67 (by norm_num) (by norm_num) (by simp [mDefAtoms]),
      gM 67 50 50 (by norm_num) (by norm_num) (by simp [mDefAtoms]), v50, ← pow_add, ← pow_add]
    congr 1; ring
  have v76 : σ (.n 76) = gen ^ (4 * (m.nlx + m.nxd)) := by
    rw [gM 76 75 75 (by norm_num) (by norm_num) (by simp [mDefAtoms]),
      gM 75 55 55 (by norm_num) (by norm_num) (by simp [mDefAtoms]), v55, ← pow_add, ← pow_add]
    congr 1; ring
  have v79 : σ (.n 79) = gen ^ (4 * (m.nls + m.nsd)) := by
    rw [gM 79 78 78 (by norm_num) (by norm_num) (by simp [mDefAtoms]),
      gM 78 56 56 (by norm_num) (by norm_num) (by simp [mDefAtoms]), v56, ← pow_add, ← pow_add]
    congr 1; ring
  have v92 : σ (.n 92) = gen ^ (m.nlx + m.nls + m.nda) := by
    rw [gM 92 91 40 (by norm_num) (by norm_num) (by simp [mDefAtoms]),
      gM 91 0 3 (by norm_num) (by norm_num) (by simp [mDefAtoms]), v0, v3, v40, ← pow_add, ← pow_add]
  have v94 : σ (.n 94) = gen ^ (m.nlx + m.nls + m.nda) + 1 := by
    rw [gA 94 92 93 (by simp [mDefAtoms]), v92, gC 93 (word 1 0 0) (by simp [mDefAtoms]), word_one]
  have v117 : σ (.n 97) = m.a117 := by rw [hO (by decide)]; simp [mOrc]
  have v118 : σ (.n 98) = m.a117 * gen ^ (m.nlx + m.nxd + (m.nls + m.nsd)) := by
    rw [gM 98 97 57 (by norm_num) (by norm_num) (by simp [mDefAtoms]), v117, v57]
  have one : ∀ d, Atom.const (.n d) (word 1 0 0) ∈ mDefAtoms → σ (.n d) = 1 := fun d h => by
    rw [gC d _ h, word_one]
  have gd : ∀ d x y e, Atom.const (.n x) (word 1 0 0) ∈ mDefAtoms →
      Atom.add (.n d) (.n x) (.n y) ∈ mDefAtoms → σ (.n y) = gen ^ e → σ (.n d) = 1 + gen ^ e :=
    fun d x y e hx hd hy => by rw [gA d x y hd, one x hx, hy]
  have v383 : σ (.n 363) = gen ^ m.nd + gen := by
    rw [gA 363 7 362 (by simp [mDefAtoms]), v7, gC 362 (word 2 0 0) (by simp [mDefAtoms]), word_gen]
  have v388 : σ (.n 368) = gen ^ (m.nrx + m.nrs) := by
    rw [gM 368 2 5 (by norm_num) (by norm_num) (by simp [mDefAtoms]), v2, v5, pow_add]
  have v395 : σ (.n 375) = gen ^ (2 * m.nc) := by
    rw [gM 375 6 6 (by norm_num) (by norm_num) (by simp [mDefAtoms]), v6, ← pow_add, two_mul]
  have v396 : σ (.n 376) = gen ^ (3 * m.nc) := by
    rw [gM 376 375 6 (by norm_num) (by norm_num) (by simp [mDefAtoms]), v395, v6, ← pow_add]
    congr 1; ring
  have v399 : σ (.n 379) = gen ^ (24 * m.nc) := by
    rw [gM 379 378 378 (by norm_num) (by norm_num) (by simp [mDefAtoms]),
      gM 378 377 377 (by norm_num) (by norm_num) (by simp [mDefAtoms]),
      gM 377 376 376 (by norm_num) (by norm_num) (by simp [mDefAtoms]), v396, ← pow_add, ← pow_add,
      ← pow_add]
    congr 1; ring
  have v402 : σ (.n 382) = gen ^ (3 * m.nc) := by
    rw [gM 382 381 6 (by norm_num) (by norm_num) (by simp [mDefAtoms]),
      gM 381 6 6 (by norm_num) (by norm_num) (by simp [mDefAtoms]), v6, ← pow_add, ← pow_add]
    congr 1; ring
  have v405 : σ (.n 385) = gen ^ (24 * m.nc) := by
    rw [gM 385 384 384 (by norm_num) (by norm_num) (by simp [mDefAtoms]),
      gM 384 383 383 (by norm_num) (by norm_num) (by simp [mDefAtoms]),
      gM 383 382 382 (by norm_num) (by norm_num) (by simp [mDefAtoms]), v402, ← pow_add, ← pow_add,
      ← pow_add]
    congr 1; ring
  have v408 : σ (.n 388) = gen ^ (m.nc + 1) := by
    rw [gM 388 6 387 (by norm_num) (by norm_num) (by simp [mDefAtoms]), v6,
      gC 387 (word 2 0 0) (by simp [mDefAtoms]), word_gen, pow_succ]
  have v411 : σ (.n 391) = gen ^ (m.nrx + m.nrs + m.nd) := by
    rw [gM 391 390 7 (by norm_num) (by norm_num) (by simp [mDefAtoms]),
      gM 390 2 5 (by norm_num) (by norm_num) (by simp [mDefAtoms]), v2, v5, v7, ← pow_add, ← pow_add]
  have v409 : σ (.n 389) = m.a409 := by rw [hO (by decide)]; simp [mOrc]
  have v415 : σ (.n 395) = m.a409 * gen ^ m.nc := by
    rw [gM 395 389 6 (by norm_num) (by norm_num) (by simp [mDefAtoms]), v409, v6]
  have v419 : σ (.n 399) = gen ^ m.nc + 1 := by
    rw [gA 399 6 398 (by simp [mDefAtoms]), v6, one 398 (by simp [mDefAtoms])]
  have v446 : σ (.n 426) = 1 := one 426 (by simp [mDefAtoms])
  have v450 : σ (.n 430) = gen := by
    rw [gM 430 428 429 (by norm_num) (by norm_num) (by simp [mDefAtoms]), one 428 (by simp [mDefAtoms]),
      gC 429 (word 2 0 0) (by simp [mDefAtoms]), word_gen, one_mul]
  -- the side conditions
  have hS : ∀ a ∈ atomsIn mFlat, a ∉ mStores → needsSide a = true →
      a.Holds rd σ ∨ Side rd mStores σ a := by
    intro a ha hnS hns
    right
    have hok := hside a (by
      rcases hmem _ (atom_mem_of_atomsIn' ha) with h | h
      · exact mem_atomsIn' (List.mem_of_mem_eraseIdx h)
      · exact ha)
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
          ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hg ⊢ <;>
        rw [h2] at hlt
      · exact rc_side hl v0 (by rw [gC 8 (word 9272771591053052074 0 0) (by simp [mDefAtoms]), word_gmax]) hb.lx (by norm_num) hlt hg
      · exact rc_side hl v1 (by rw [gC 12 (word 9272771591053052074 0 0) (by simp [mDefAtoms]), word_gmax]) hb.xd (by norm_num) hlt hg
      · exact rc_side hl v2 (by rw [gC 16 (word 9272771591053052074 0 0) (by simp [mDefAtoms]), word_gmax]) hb.rx (by norm_num) hlt hg
      · exact rc_side hl v3 (by rw [gC 20 (word 9272771591053052074 0 0) (by simp [mDefAtoms]), word_gmax]) hb.ls (by norm_num) hlt hg
      · exact rc_side hl v4 (by rw [gC 24 (word 9272771591053052074 0 0) (by simp [mDefAtoms]), word_gmax]) hb.sd (by norm_num) hlt hg
      · exact rc_side hl v5 (by rw [gC 28 (word 9272771591053052074 0 0) (by simp [mDefAtoms]), word_gmax]) hb.rs (by norm_num) hlt hg
      · exact rc_side hl v6 (by rw [gC 32 (word 65536 0 0) (by simp [mDefAtoms]), word_g16]) hb.nc (by norm_num) hlt hg
      · exact rc_side hl v7 (by rw [gC 36 (word 2 0 0) (by simp [mDefAtoms]), word_g1]) hb.nd (by norm_num) hlt hg
      · exact rc_side hl v40 (by rw [gC 42 (word 65536 0 0) (by simp [mDefAtoms]), word_g16]) hb.nda (by norm_num) hlt hg
      · exact rc_side hl v41 (by rw [gC 46 (word 139298 0 0) (by simp [mDefAtoms]), word_g257]) hb.ndd (by norm_num)
          hlt hg
      · exact rc_side hl v50 (by rw [gC 51 (word 139298 0 0) (by simp [mDefAtoms]), word_g257]) hb.slots (by norm_num)
          hlt hg
      · exact rc_side hl v58 (by rw [gC 59 (word 9272771591053052074 0 0) (by simp [mDefAtoms]), word_gmax]) hb.total (by norm_num)
          hlt hg
    | load d p o =>
      simp only [mSideOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨hd, hp⟩, hl'⟩ := hok
      simp only [mLoadOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.mem_cons,
        Prod.mk.injEq, List.not_mem_nil, or_false] at hl'
      rw [hd, hp] at hnS ⊢
      simp only [Side]
      rw [ite_neg' hnS]
      rcases hl' with (((⟨e1, e2, rfl⟩ | ⟨e1, e2, rfl⟩ | ⟨e1, e2, rfl⟩) | hs) | hs) | hs
      · rw [e2, v415]; exact ⟨hm.wN.1, by rw [hm.wN.2]; rfl⟩
      · rw [e2, v446]; exact ⟨hm.h0.1, by rw [hm.h0.2]; rfl⟩
      · rw [e2, v450]; exact ⟨hm.h1.1, by rw [hm.h1.2]; rfl⟩
      all_goals exfalso; apply hnS; rw [mStores_eq]
      · obtain ⟨⟨e1, e2⟩, e3⟩ := hs
        rw [e1, e2]
        simp only [mStoresL, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inl (Or.inl (Or.inl ⟨o, e3, rfl⟩))
      · obtain ⟨⟨e1, e2⟩, rfl⟩ := hs
        rw [e1, e2]; simp [mStoresL]
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
      have rd447 : σ (.n 427) = (digestScalars m.sdg).1 := by
        have h := hD (.load (.n 427) (.n 426) 0) (by simp [mDefAtoms])
        rcases h with h | h
        · exact absurd (by rw [mStores_eq] at h; exact h) (by simp [mStoresL])
        · rw [h, v446, rdAt_of_load hm.h0]
      have rd451 : σ (.n 431) = (digestScalars m.sdg).2 := by
        have h := hD (.load (.n 431) (.n 430) 0) (by simp [mDefAtoms])
        rcases h with h | h
        · exact absurd (by rw [mStores_eq] at h; exact h) (by simp [mStoresL])
        · rw [h, v450, rdAt_of_load hm.h1]
      have rd416 : σ (.n 396) = gen ^ m.total := by
        have h := hD (.load (.n 396) (.n 395) 0) (by simp [mDefAtoms])
        rcases h with h | h
        · exact absurd (by rw [mStores_eq] at h; exact h) (by simp [mStoresL])
        · rw [h, v415, rdAt_of_load hm.wN]
      rcases hok with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩
      · rw [hO (by decide), hO (by decide)]; simp [mOrc]
      · rw [hO (by decide), hO (by decide)]; simp [mOrc]
      · rw [hO (by decide), hO (by decide)]; simp [mOrc]
      · rw [hO (by decide), hO (by decide)]; simp [mOrc]
      · rw [rd416, v58]
      · rw [rd447, hO (by decide)]; simp [mOrc]
      · rw [rd451, hO (by decide)]; simp [mOrc]
    | assertNe x i p =>
      simp only [mSideOk, decide_eq_true_eq] at hok
      subst hok
      simp only [Side]
      rw [v94]
      have h2 : m.nlx + m.nls + m.nda < 2 ^ 64 - 1 := by
        have := hb.lx; have := hb.ls; have := hb.nda; omega
      intro h0
      rw [add_comm] at h0
      exact one_add_ne' h2 hb.nz h0
    | _ => simp [mSideOk] at hok
  -- the stores
  have hcanD : ∀ i ∈ [81, 82, 83, 84], IsCanonical128 (σ (.n i)) := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> rw [hO (by decide)] <;> simp only [mOrc] <;>
      norm_num <;> first | exact (digestScalars_canonical _).1 | exact (digestScalars_canonical _).2
  have hbyte : ∀ v < 256, σ (.n (100 + v)) = word v 0 0 := by
    intro v hv
    obtain ⟨b, hb', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp mByte_ok v (List.mem_range.mpr hv))
    have := hG _ (atom_mem_of_atomsIn' hb')
    rw [← atomEqb_sound he] at this
    exact this
  have hleafc : ∀ k < 23, σ (.n (401 + k)) = 0 := by
    intro k hk
    obtain ⟨b, hb', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp mLeafC_ok k (List.mem_range.mpr hk))
    have := hG _ (atom_mem_of_atomsIn' hb')
    rw [← atomEqb_sound he] at this
    rw [show σ (.n (401 + k)) = word 0 0 0 from this, word_zero]
  have hstore : (∀ b ∈ atomsIn mPre, b ∉ mStores → b.Holds rd σ) → ∀ a ∈ mStoresL,
      (isLeafStore a = true → m.nc = 0) → a.Holds rd σ := by
    intro _ a ha hlf
    simp only [mStoresL, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_range] at ha
    rcases ha with (((⟨v, hv', rfl⟩ | rfl) | ⟨k, hk, rfl⟩) | rfl)
    · show LoadHolds rd (σ (.n 99)) v (σ (.n (100 + v)))
      rw [hO (by decide), hbyte v hv']
      have := hm.bytes v (by simpa using hv')
      simpa [mOrc] using this
    · show LoadHolds rd (σ (.n 389)) 0 (σ (.n 391))
      rw [v409, v411]; exact hm.w0
    · have h0 := hlf rfl
      show LoadHolds rd (σ (.n 397)) k (σ (.n (401 + k)))
      rw [hO (by decide), hleafc k hk]
      have := hm.leaf h0 k (by simp; omega)
      rw [List.getElem_append_left (by simp; omega), List.getElem_replicate] at this
      simpa [mOrc] using this
    · have h0 := hlf rfl
      show LoadHolds rd (σ (.n 397)) 23 (σ (.n 400))
      rw [hO (by decide), hO (by decide)]
      have := hm.leaf h0 23 (by simp)
      simpa [mOrc] using this
  -- the blocks
  have hsubF : ∀ {P : List Stmt}, (∀ s ∈ P, s ∈ mFlat) → ∀ a ∈ atomsIn P, a ∈ atomsIn mFlat :=
    fun hP a ha => mem_atomsIn' (hP _ (atom_mem_of_atomsIn' ha))
  have h1F : ∀ s ∈ mPre ++ mMid ++ mPost, s ∈ mFlat := fun s hs => by
    simp only [List.mem_append] at hs
    simp only [mFlat, List.mem_append]
    tauto
  have hB1 : ∀ a ∈ atomsIn (mPre ++ mMid ++ mPost), a.Holds rd σ := by
    have hsub := hsubF h1F
    refine atoms_holds_stores (S := mStores) hidx hcan1 (fun a ha => hgA a (hsub a ha)) hcanD
      (fun a ha hnS hns => hS a (hsub a ha) hnS hns) (fun h1 a ha haS => ?_)
    rw [mStores_eq] at haS
    refine hstore (fun b hb hbS => h1 b (mem_atomsIn' (by
      simp only [List.mem_append]; exact Or.inl (Or.inl (atom_mem_of_atomsIn' hb)))) hbS) a haS
      (fun hl' => ?_)
    have := List.all_eq_true.mp mNoLeafStore.1 a ha
    rw [hl'] at this
    exact absurd this (by decide)
  have hpre : ∀ a ∈ atomsIn mPre, a.Holds rd σ := fun a ha => hB1 a (mem_atomsIn' (by
    simp only [List.mem_append]; exact Or.inl (Or.inl (atom_mem_of_atomsIn' ha))))
  have hpreN : ∀ b ∈ atomsIn mPre, b ∉ mStores → b.Holds rd σ := fun b hb _ => hpre b hb
  have hDa : ∀ a ∈ atomsIn mDa, a.Holds rd σ := by
    have hsub := hsubF (P := mDa) (fun s hs => by simp only [mFlat, List.mem_append]; tauto)
    refine atoms_holds_stores (S := mStores) (A := []) hidx hcan2 (fun a ha => hgA a (hsub a ha))
      (by simp) (fun a ha hnS hns => hS a (hsub a ha) hnS hns) (fun _ a ha haS => ?_)
    rw [mStores_eq] at haS
    refine hstore hpreN a haS (fun hl' => ?_)
    have := List.all_eq_true.mp mNoLeafStore.2 a ha
    rw [hl'] at this
    exact absurd this (by decide)
  have hLeaf : m.nc = 0 → ∀ a ∈ atomsIn mLeaf, a.Holds rd σ := by
    intro h0
    have hsub := hsubF (P := mLeaf) (fun s hs => by simp only [mFlat, List.mem_append]; tauto)
    refine atoms_holds_stores (S := mStores) (A := []) hidx hcan3 (fun a ha => hgA a (hsub a ha))
      (by simp) (fun a ha hnS hns => hS a (hsub a ha) hnS hns) (fun _ a ha haS => ?_)
    rw [mStores_eq] at haS
    exact hstore hpreN a haS (fun _ => h0)
  exact ⟨hpre, fun a ha => hB1 a (mem_atomsIn' (by
      simp only [List.mem_append]; exact Or.inl (Or.inr (atom_mem_of_atomsIn' ha)))),
    fun a ha => hB1 a (mem_atomsIn' (by
      simp only [List.mem_append]; exact Or.inr (atom_mem_of_atomsIn' ha))),
    hDa, hLeaf, horc, v50, v55, v56, v57, v58, v68, v76, v79, v118, v388,
    by rw [gM 373 6 6 (by norm_num) (by norm_num) (by simp [mDefAtoms]), v6, ← pow_add, two_mul],
    v399, v405, v408, gd 71 70 50 _ (by simp [mDefAtoms]) (by simp [mDefAtoms]) v50,
    one 72 (by simp [mDefAtoms]), gd 86 85 1 _ (by simp [mDefAtoms]) (by simp [mDefAtoms]) v1,
    one 87 (by simp [mDefAtoms]), gd 89 88 4 _ (by simp [mDefAtoms]) (by simp [mDefAtoms]) v4,
    one 90 (by simp [mDefAtoms]), gd 357 356 2 _ (by simp [mDefAtoms]) (by simp [mDefAtoms]) v2,
    one 358 (by simp [mDefAtoms]), gd 360 359 5 _ (by simp [mDefAtoms]) (by simp [mDefAtoms]) v5,
    one 361 (by simp [mDefAtoms]), v383, gd 393 392 6 _ (by simp [mDefAtoms]) (by simp [mDefAtoms]) v6,
    one 394 (by simp [mDefAtoms]), v419, v415, v446, v450⟩

end
end LeanVM.Guest.B1.Main
