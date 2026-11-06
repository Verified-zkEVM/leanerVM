/-
  LeanVM.Guest.B1.Tables.VtC.ZTail

  `verify_tables`' statements `6251 ..< 6294`, completely: the public input's binding and the
  return.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.ZSetup

/-!
# The public input's binding, completely (G:2556-2569)

`vtZt_complete`: from the sponge `S2` after the table evaluations (its waiting word's cells and
its capacity), on canonical public words `pi_0, pi_1` and a pool holding the three binding
claims at `162 ..< 165`, the statements hold; `rm` is `S2`'s squeeze and the function returns the
sponge after it, the cursor `157` words past the rounds', `g^n`, the bytecode value and `rm`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The tail's statements evaluation alone does not settle. -/
noncomputable def zTRest : List Stmt := [
    .atom (.keccak [.n 5696, .n 5698, .n 2549, .n 2549, .n 2549, .n 2550, .n 2551, .n 2552, .n 5684, .n 5685, .n 5686, .n 5687, .n 5688] [.n 6818, .n 6819, .n 6820, .n 6821, .n 6822, .n 6823, .n 6824, .n 6825, .n 6826, .n 6827, .n 6828, .n 6829, .n 6830] false false),
    .atom (.assertInK (.n 6831) (.n 6834)),
    .atom (.assertInK (.n 6838) (.n 6841)),
    .atom (.assertInK (.n 6843) (.n 6846)),
    .atom (.load (.n 6850) (.n 15) 162),
    .atom (.load (.n 6853) (.n 15) 163),
    .atom (.load (.n 6854) (.n 15) 164)]

/-- What the tail gives: `rm`, the returned capacity, cursor, `g^n`, bytecode value, `rm` and
`col_eval_words` (the rounds' cursor). -/
def ZtOut (σ : Val) (S2 : Fs) : Prop :=
  σ (.n 6837) = S2.squeeze.1 ∧
    [σ (.n 6855), σ (.n 6856), σ (.n 6857), σ (.n 6858), σ (.n 6859)] = S2.squeeze.2.cap ∧
    σ (.n 6862) = σ (.n 2609) * gen ^ 157 ∧ σ (.n 6863) = σ (.n 2500) ∧
    σ (.n 6864) = σ (.n 581) ∧ σ (.n 6865) = S2.squeeze.1 ∧ σ (.n 6866) = σ (.n 2609)

set_option maxRecDepth 100000 in
/-- **Statements `6251 ..< 6294`, completely.** -/
theorem vtZt_complete {rd : Reader} {w : ℕ → E} {args : List E} (hl : args.length = 20) {S2 : Fs}
    (hSr : rateOf S2.pend =
      [vtσ rd w args (.n 5696), vtσ rd w args (.n 5698), 0, 0, 0, 0, 0, 0])
    (hSc : S2.cap = [vtσ rd w args (.n 5684), vtσ rd w args (.n 5685), vtσ rd w args (.n 5686),
      vtσ rd w args (.n 5687), vtσ rd w args (.n 5688)])
    (hcan : AllCanonical (rateOf S2.pend ++ S2.cap))
    (hc6 : IsCanonical128 (vtσ rd w args (.n 6))) (hc7 : IsCanonical128 (vtσ rd w args (.n 7)))
    (hp0 : LoadHolds rd (vtσ rd w args (.n 15)) 162 (multilinearEval
      [ofK ((vtσ rd w args (.n 6)).limb 0), ofK ((vtσ rd w args (.n 7)).limb 0)] [S2.squeeze.1]))
    (hp1 : LoadHolds rd (vtσ rd w args (.n 15)) 163 (multilinearEval
      [ofK ((vtσ rd w args (.n 6)).limb 1), ofK ((vtσ rd w args (.n 7)).limb 1)] [S2.squeeze.1]))
    (hp2 : LoadHolds rd (vtσ rd w args (.n 15)) 164 0) :
    (∀ s ∈ (vtPre.drop 6251).take 43, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) ∧
      ZtOut (vtσ rd w args) S2 := by
  have g : GoodL rd w (vtσ rd w args) zTail := vt_goodL hl 6251 zTail zTail_at
  have gk : Good rd vtSL w (vtσ rd w args) (.keccak [.n 5696, .n 5698, .n 2549, .n 2549, .n 2549,
      .n 2550, .n 2551, .n 2552, .n 5684, .n 5685, .n 5686, .n 5687, .n 5688] (lyOuts 6818) false
      false) := (vt_goodL (rd := rd) (w := w) hl 6251 [.atom (.keccak [.n 5696, .n 5698, .n 2549,
      .n 2549, .n 2549, .n 2550, .n 2551, .n 2552, .n 5684, .n 5685, .n 5686, .n 5687, .n 5688]
      (lyOuts 6818) false false)] (by decide +kernel)).1
  have gch : GoodL rd w (vtσ rd w args) (challengeT (.n 6818) (.n 6819) 6831) :=
    vt_goodL hl 6252 _ (by decide +kernel)
  have gz := vt_goodL (rd := rd) (w := w) hl 2607 [.atom (.const (.n 2549) (word 0 0 0)),
    .atom (.const (.n 2550) (word 0 0 0)), .atom (.const (.n 2551) (word 0 0 0)),
    .atom (.const (.n 2552) (word 0 0 0))] (by decide +kernel)
  have e := tbStmtsEqb_sound zTail_at
  have hlen42 : zTail.length = 43 := rfl
  suffices H : (∀ s ∈ zTRest, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) ∧
      ZtOut (vtσ rd w args) S2 by
    refine ⟨fun s hs => ?_, H.2⟩
    rw [← hlen42, ← e] at hs
    exact vt_block hl 6251 zTail zTail_at zTRest (by decide +kernel) H.1 s hs
  generalize vtσ rd w args = σ at *
  simp only [zTail, GoodL, GoodS, Good, fixNe, Nat.reduceLT, and_true, ↓reduceIte] at g
  obtain ⟨g6251, g6252, g6253, g6254, g6255, g6256, g6257, g6258, g6259, g6260, g6261, g6262, g6263, g6264, g6265, g6266, g6267, g6268, g6269, g6270, g6271, g6272, g6273, g6274, g6275, g6276, g6277, g6278, g6279, g6280, g6281, g6282, g6283, g6284, g6285, g6286, g6287, g6288, g6289, g6290, g6291, g6292, g6293⟩ := g
  simp only [GoodL, GoodS, Good, fixNe, tb_word_zero] at gz
  obtain ⟨hz0, hz1, hz2, hz3, -⟩ := gz
  -- the squeeze
  have hin : ([.n 5696, .n 5698, .n 2549, .n 2549, .n 2549, .n 2550, .n 2551, .n 2552, .n 5684,
      .n 5685, .n 5686, .n 5687, .n 5688] : List V).map σ = rateOf S2.pend ++ S2.cap := by
    rw [hSr, hSc]; simp [hz0, hz1, hz2, hz3]
  have k6251 : (Atom.keccak [.n 5696, .n 5698, .n 2549, .n 2549, .n 2549, .n 2550, .n 2551,
      .n 2552, .n 5684, .n 5685, .n 5686, .n 5687, .n 5688] (lyOuts 6818) false false).Holds rd σ :=
    z_keccak gk (by rw [hin]; exact hcan)
  obtain ⟨-, hPk, -⟩ := ly_keccak k6251
  rw [hin] at hPk
  have hch : ChallengeOk σ (.n 6818) (.n 6819) 6831 :=
    z_challenge gch
      (by rw [hPk 1 (by norm_num)]; exact cellsOfState_canonical _ _ _)
  have vrm : σ (.n 6837) = S2.squeeze.1 :=
    challengeT_value hch (hPk 0 (by norm_num)) (hPk 1 (by norm_num))
  -- the public words' limbs
  have l6 : σ (.n 6838) = ofK ((σ (.n 6)).limb 0) := by
    have := g6260 0 (by simp); simpa [limbAt] using this
  have l7 : σ (.n 6843) = ofK ((σ (.n 7)).limb 0) := by
    have := g6266 0 (by simp); simpa [limbAt] using this
  have h6 : σ (.n 6841) = ofK ((σ (.n 6)).limb 1) := by
    rw [g6263, g6261, g6262, word_y_inv, l6]; exact split_hi hc6
  have h7 : σ (.n 6846) = ofK ((σ (.n 7)).limb 1) := by
    rw [g6269, g6267, g6268, word_y_inv, l7]; exact split_hi hc7
  have i6256 : (Atom.assertInK (.n 6831) (.n 6834)).Holds rd σ := ⟨hch.2.2.2.1, hch.2.2.2.2.1⟩
  have i6264 : (Atom.assertInK (.n 6838) (.n 6841)).Holds rd σ := by
    rw [Atom.Holds, l6, h6]; exact ⟨ofK_isInK _, ofK_isInK _⟩
  have i6270 : (Atom.assertInK (.n 6843) (.n 6846)).Holds rd σ := by
    rw [Atom.Holds, l7, h7]; exact ⟨ofK_isInK _, ofK_isInK _⟩
  have s6275 : (Atom.load (.n 6850) (.n 15) 162).Holds rd σ := by
    show LoadHolds rd _ _ _
    have e : multilinearEval [ofK ((σ (.n 6)).limb 0), ofK ((σ (.n 7)).limb 0)] [S2.squeeze.1] =
        σ (.n 6850) := by
      rw [g6274, g6273, g6272, g6271, g6265, l6, l7, vrm]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD]
      ring
    rw [← e]; exact hp0
  have s6279 : (Atom.load (.n 6853) (.n 15) 163).Holds rd σ := by
    show LoadHolds rd _ _ _
    have e : multilinearEval [ofK ((σ (.n 6)).limb 1), ofK ((σ (.n 7)).limb 1)] [S2.squeeze.1] =
        σ (.n 6853) := by
      rw [g6278, g6277, g6276, h6, h7, vrm]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD]
      ring
    rw [← e]; exact hp1
  have s6281 : (Atom.load (.n 6854) (.n 15) 164).Holds rd σ := by
    show LoadHolds rd _ _ _
    rw [g6280, tb_word_zero]; exact hp2
  have hrest : ∀ s ∈ zTRest, VSH (coreProgram.Rel rd) rd σ s := by
    intro s hs
    simp only [zTRest, List.mem_cons, List.not_mem_nil, or_false] at hs
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl := hs
    · exact k6251
    · exact i6256
    · exact i6264
    · exact i6270
    · exact s6275
    · exact s6279
    · exact s6281
  refine ⟨hrest, vrm, ?_, ?_, g6290, g6291, by rw [g6292, vrm], g6293⟩
  · rw [g6282, g6283, g6284, g6285, g6286, hPk 8 (by norm_num), hPk 9 (by norm_num),
      hPk 10 (by norm_num), hPk 11 (by norm_num), hPk 12 (by norm_num)]
    rfl
  · rw [g6289, g6288, g6287, vtW157]

end
end LeanVM.Guest.B1.Tables
