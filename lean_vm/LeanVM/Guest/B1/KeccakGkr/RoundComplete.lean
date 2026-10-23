/-
  LeanVM.Guest.B1.KeccakGkr.RoundComplete

  `keccak_round`, completely: an honest round record, coordinate, stream words and outputs in
  memory give its core IR relation.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.Round
public import LeanVM.Guest.B1.Fwd.Eval

/-!
# `keccak_round`, completely

`keccak_round_complete : keccak_round_complete_Spec`: the honest valuation is the body evaluated
(`Fwd.ev`) on the arguments; its loads read the record, the coordinate and the two stream words the
meaning holds, the hinted limbs are the words' (so the packed cells are canonical and the
`assert_in_k` checks see `K` words), and the stores (the challenge, the next record) write the
words the meaning holds, which `eqRound` computes as the body does.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

theorem round_chk : Fwd.chk 3 Data.core11.body = some 70 := by decide +kernel

theorem round_stores : storesOf 3 Data.core11.body =
    [.load (.n 54) (.n 2) 0, .load (.n 43) (.n 0) 1, .load (.n 44) (.n 0) 17,
      .load (.n 45) (.n 0) 33, .load (.n 46) (.n 0) 49, .load (.n 47) (.n 0) 65,
      .load (.n 59) (.n 0) 81, .load (.n 67) (.n 0) 97, .load (.n 69) (.n 0) 113] := by
  decide +kernel

theorem rdAt_of_load' {rd : Reader} {p : E} {k : ℕ} {v : E} (h : LoadHolds rd p k v) :
    rdAt rd p k = v := by
  unfold rdAt; rw [h.2]; rfl

theorem round_good (rd : Reader) (w : ℕ → E) (rec pp pt : E) :
    ∀ s ∈ Data.core11.body, GoodS rd (storesOf 3 Data.core11.body) w
      (Val.ofArgs (ev rd w [rec, pp, pt] Data.core11.body)) s :=
  (ev_spec rd w Data.core11.body [rec, pp, pt] round_chk).2.2

theorem five_of_length {l : List E} (h : l.length = 5) :
    ∃ a b c d e, l = [a, b, c, d, e] := by
  match l, h with
  | [a, b, c, d, e], _ => exact ⟨a, b, c, d, e, rfl⟩

/-- **`keccak_round` is complete**: an honest record, coordinate, stream words and outputs in
memory give its relation. -/
theorem keccak_round_complete : keccak_round_complete_Spec := by
  intro rd args rets hm
  match args, hm with
  | [rec, pp, pt], hm =>
  obtain ⟨hret, cap, cur, claim, scale, r, g1, g2, ⟨⟨hcl, hcap⟩, lcur, lcl, lsc⟩, hcan, lr, hxs,
    lc, ⟨⟨hcl', hcap'⟩, lcur', lcl', lsc'⟩⟩ := hm
  subst hret
  -- the capacity's five cells
  obtain ⟨c0, c1, c2, c3, c4, rfl⟩ := five_of_length hcl
  have L0 : LoadHolds rd rec 0 c0 := hcap 0 (by simp)
  have L16 : LoadHolds rd rec 16 c1 := hcap 1 (by simp)
  have L32 : LoadHolds rd rec 32 c2 := hcap 2 (by simp)
  have L48 : LoadHolds rd rec 48 c3 := hcap 3 (by simp)
  have L64 : LoadHolds rd rec 64 c4 := hcap 4 (by simp)
  have Lg1 : LoadHolds rd cur 0 g1 := hxs 0 (by simp)
  have Lg2 : LoadHolds rd cur 1 g2 := hxs 1 (by simp)
  -- the honest valuation and its equations
  have g := round_good rd (fun _ ↦ 0) rec pp pt
  have p0 := ev_params rd (fun _ ↦ 0) round_chk (l := [rec, pp, pt]) (i := 0) (by simp)
  have p1 := ev_params rd (fun _ ↦ 0) round_chk (l := [rec, pp, pt]) (i := 1) (by simp)
  have p2 := ev_params rd (fun _ ↦ 0) round_chk (l := [rec, pp, pt]) (i := 2) (by simp)
  rw [round_stores] at g
  generalize Val.ofArgs (ev rd (fun _ ↦ 0) [rec, pp, pt] Data.core11.body) = σ at g p0 p1 p2
  simp only [List.getD_cons_zero, List.getD_cons_succ] at p0 p1 p2
  simp only [Data.core11.body] at g
  simp only [List.forall_mem_cons] at g
  simp (config := {decide := true}) only [GoodS, Good, List.mem_cons, List.not_mem_nil,
    Atom.load.injEq, false_or, or_false, true_or, true_and, ↓reduceIte, List.length_cons,
    List.length_nil, Nat.reduceAdd, false_implies, implies_true, and_true] at g
  obtain ⟨e3, e4, e5, e6, e7, e8, e9, e10, l10, e14, e15, e16, e17, e18, e19, e20, l20, e24, e25,
    e26, e27, e28, e29, e30, e31, e32, e33, e34, k30, l36, e49, e50, e51, e52, e53, e54, e55, e56,
    e57, e58, e59, e60, e61, e62, e63, e64, e65, e66, e67, e68, e69⟩ := g
  rw [p0, rdAt_of_load' L0] at e3
  rw [p0, rdAt_of_load' L16] at e4
  rw [p0, rdAt_of_load' L32] at e5
  rw [p0, rdAt_of_load' L48] at e6
  rw [p0, rdAt_of_load' L64] at e7
  rw [p0, rdAt_of_load' (show LoadHolds rd rec 80 cur from lcur)] at e8
  rw [p1, rdAt_of_load' lr] at e9
  rw [e8, rdAt_of_load' Lg1] at e10
  rw [e8, rdAt_of_load' Lg2] at e20
  rw [p0, rdAt_of_load' (show LoadHolds rd rec 96 claim from lcl)] at e60
  rw [p0, rdAt_of_load' (show LoadHolds rd rec 112 scale from lsc)] at e68
  -- the two words, packed
  have v13 : σ (.n 13) = ofK ((σ (.n 10)).limb 2) := l10 2 (by norm_num)
  have v23 : σ (.n 23) = ofK ((σ (.n 20)).limb 2) := l20 2 (by norm_num)
  have i14 : IsInK (σ (.n 14)) := by rw [e14, word_eOfNat]; exact eOfNat_isInK _
  have i24 : IsInK (σ (.n 24)) := by rw [e24, word_eOfNat]; exact eOfNat_isInK _
  have hp1 : FsPackOk σ (.n 10) (10 + 1) dsObserve :=
    ⟨e14, by rw [v13]; exact ofK_isInK _, i14, e15, e16, e17, e18, e19⟩
  have hp2 : FsPackOk σ (.n 20) (20 + 1) dsObserve :=
    ⟨e24, by rw [v23]; exact ofK_isInK _, i24, e25, e26, e27, e28, e29⟩
  have c17 : IsCanonical128 (σ (.n 17)) := by
    rw [e17, e16, e15, v13]; exact (fsPackVals_canonical (σ (.n 10)) dsObserve).1
  have c27 : IsCanonical128 (σ (.n 27)) := by
    rw [e27, e26, e25, v23]; exact (fsPackVals_canonical (σ (.n 20)) dsObserve).1
  have s1 := fsNext_scalar hp1 c17
  have s2 := fsNext_scalar hp2 c27
  rw [e10] at s1
  rw [e20] at s2
  -- the permutation
  have cz : IsCanonical128 (word 0 0 0) := by
    rw [word_zero]; unfold IsCanonical128; exact limb_zero 2
  have hcanI : AllCanonical ([V.n 17, .n 19, .n 27, .n 29, .n 31, .n 32, .n 33, .n 34, .n 3, .n 4,
      .n 5, .n 6, .n 7].map σ) := by
    intro c hc
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hc
    have c19 : IsCanonical128 (σ (.n 19)) := by
      have := congrArg Prod.snd s1
      simp only at this
      rw [this]; exact (scalarCells_canonical g1 dsObserve).2
    have c29 : IsCanonical128 (σ (.n 29)) := by
      have := congrArg Prod.snd s2
      simp only at this
      rw [this]; exact (scalarCells_canonical g2 dsObserve).2
    have hc' : ∀ x ∈ [c0, c1, c2, c3, c4], IsCanonical128 x := hcan
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hc'
    obtain ⟨h0, h1, h2, h3, h4⟩ := hc'
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact c17
    · exact c19
    · exact c27
    · exact c29
    · rw [e31]; exact cz
    · rw [e32]; exact cz
    · rw [e33]; exact cz
    · rw [e34]; exact cz
    · rw [e3]; exact h0
    · rw [e4]; exact h1
    · rw [e5]; exact h2
    · rw [e6]; exact h3
    · rw [e7]; exact h4
  have hk : (Atom.keccak [.n 17, .n 19, .n 27, .n 29, .n 31, .n 32, .n 33, .n 34, .n 3, .n 4, .n 5,
      .n 6, .n 7] [.n 35, .n 36, .n 37, .n 38, .n 39, .n 40, .n 41, .n 42, .n 43, .n 44, .n 45,
      .n 46, .n 47] false false).Holds rd σ := keccakA_of rfl rfl hcanI (funext k30)
  -- the challenge
  obtain ⟨-, -, -, hout⟩ := keccak_outs hk
  have c36 : IsCanonical128 (σ (.n 36)) := by
    have := hout 1 (by norm_num)
    simp only [List.getD_cons_succ, List.getD_cons_zero] at this
    rw [this]; exact cellsOfState_canonical _ _ _
  have v48 : σ (.n 48) = ofK ((σ (.n 36)).limb 0) := l36 0 (by norm_num)
  have hch : ChallengeOk σ (.n 35) (.n 36) 48 := challengeOk_of_vals c36 fun i hi ↦ by
    interval_cases i
    · exact v48
    · show σ (.n 49) = σ (.n 36) + ofK ((σ (.n 36)).limb 0); rw [e49, v48]
    · exact e50
    · show σ (.n 51) = (σ (.n 36) + ofK ((σ (.n 36)).limb 0)) * word 1 0 1; rw [e51, e49, v48, e50]
    · exact e52
    · show σ (.n 53) = word 0 0 1 * ofK ((σ (.n 36)).limb 0); rw [e53, e52, v48]
    · show σ (.n 54) = σ (.n 35) + word 0 0 1 * ofK ((σ (.n 36)).limb 0); rw [e54, e53, e52, v48]
  set s : Fs := ⟨[c0, c1, c2, c3, c4], [(g1, dsObserve), (g2, dsObserve)]⟩ with hs
  have hin : [V.n 17, .n 19, .n 27, .n 29, .n 31, .n 32, .n 33, .n 34, .n 3, .n 4, .n 5, .n 6,
      .n 7].map σ = rateOf s.pend ++ s.cap := by
    rw [hs, rateOf_two, ← s1, ← s2]
    simp only [List.map_cons, List.map_nil, e31, e32, e33, e34, word_zero, e3, e4, e5, e6, e7,
      List.cons_append, List.nil_append]
  obtain ⟨hc54, hcapOut⟩ := squeeze_atom (rd := rd) hk hin hch
  simp only [List.drop, List.map_cons, List.map_nil] at hcapOut
  have habs : (⟨[c0, c1, c2, c3, c4], []⟩ : Fs).absorbAll [g1, g2] dsObserve = s := rfl
  simp only [eqRound, habs] at lc hcap' lcur' lcl' lsc'
  have h54 : σ (.n 54) = s.squeeze.1 := hc54
  have v67 : σ (.n 67) = (1 + (r + s.squeeze.1)) *
      (claim + (r + s.squeeze.1) * g1 + (r + s.squeeze.1 * s.squeeze.1) * g2) := by
    rw [e67, e57, e56, e66, e62, e65, e64, e63, e61, e55, e60, e9, e10, e20, h54, word_one]
  have v69 : σ (.n 69) = scale * (1 + (r + s.squeeze.1)) := by
    rw [e69, e68, e57, e56, e55, e9, h54, word_one]
  have v59 : σ (.n 59) = cur * gen ^ 2 := by rw [e59, e8, e58, word_gen_sq]
  have hcO : ∀ j (hj : j < 5), LoadHolds rd rec (1 + j * 16)
      ([σ (.n 43), σ (.n 44), σ (.n 45), σ (.n 46), σ (.n 47)][j]'(by simpa using hj)) := by
    intro j hj
    have := hcap' j (by rw [← hcapOut]; simpa using hj)
    simp only [krCap] at this
    convert this using 2
  -- the body holds
  refine (rel_iff_sem find_keccak_round _ _).mpr ⟨σ, ?_, ?_⟩
  · show [σ (.n 0), σ (.n 1), σ (.n 2)] = [rec, pp, pt]
    rw [p0, p1, p2]
  have ld : ∀ {d p : V} {off : ℕ} {pv dv : E}, σ p = pv → σ d = dv → LoadHolds rd pv off dv →
      (Atom.load d p off).Holds rd σ := by
    intro d p off pv dv hp hd h
    show LoadHolds rd (σ p) off (σ d)
    rw [hp, hd]; exact h
  show Stmt.HoldsList _ rd σ Data.core11.body False (fun rs ↦ rs = [])
  simp only [Data.core11.body, Stmt.HoldsList, Stmt.Holds]
  exact ⟨ld p0 e3 L0, ld p0 e4 L16, ld p0 e5 L32, ld p0 e6 L48, ld p0 e7 L64, ld p0 e8 lcur,
    ld p1 e9 lr, ld e8 e10 Lg1, trivial, e14, ⟨hp1.2.1, hp1.2.2.1⟩, e15, e16, e17, e18, e19, ld e8 e20 Lg2,
    trivial, e24, ⟨hp2.2.1, hp2.2.2.1⟩, e25, e26, e27, e28, e29, e30, e31, e32, e33, e34, hk, trivial, e49, e50,
    e51, ⟨hch.2.2.2.1, hch.2.2.2.2.1⟩, e52, e53, e54, ld p2 h54 lc, e55, e56, e57,
    ld p0 rfl (hcO 0 (by norm_num)), ld p0 rfl (hcO 1 (by norm_num)),
    ld p0 rfl (hcO 2 (by norm_num)), ld p0 rfl (hcO 3 (by norm_num)),
    ld p0 rfl (hcO 4 (by norm_num)), e58, e59, ld p0 v59 lcur', ld p0 e60 lcl, e61, e62, e63, e64,
    e65, e66, e67, ld p0 v67 lcl', ld p0 e68 lsc, e69, ld p0 v69 lsc', rfl⟩

end
end LeanVM.Guest.B1.VerifySub
