/-
  LeanVM.Guest.B1.Tables.VtC.ZTail

  `verify_tables`' statements `10209 ..< 10251`, completely: the public input's binding and the
  return.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.ZSetup

/-!
# The public input's binding, completely (G:2294-2305)

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
    .atom (.keccak [.n 9416, .n 9418, .n 5872, .n 5872, .n 5872, .n 5873, .n 5874, .n 5875, .n 9404, .n 9405, .n 9406, .n 9407, .n 9408] [.n 11198, .n 11199, .n 11200, .n 11201, .n 11202, .n 11203, .n 11204, .n 11205, .n 11206, .n 11207, .n 11208, .n 11209, .n 11210] false false),
    .atom (.assertInK (.n 11211) (.n 11214)),
    .atom (.assertInK (.n 11218) (.n 11221)),
    .atom (.assertInK (.n 11223) (.n 11226)),
    .atom (.load (.n 11230) (.n 16) 162),
    .atom (.load (.n 11233) (.n 16) 163),
    .atom (.load (.n 11234) (.n 16) 164)]

/-- What the tail gives: `rm`, the returned capacity, cursor, `g^n`, bytecode value and `rm`. -/
def ZtOut (σ : Val) (S2 : Fs) : Prop :=
  σ (.n 11217) = S2.squeeze.1 ∧
    [σ (.n 11235), σ (.n 11236), σ (.n 11237), σ (.n 11238), σ (.n 11239)] = S2.squeeze.2.cap ∧
    σ (.n 11242) = σ (.n 5932) * gen ^ 157 ∧ σ (.n 11243) = σ (.n 5817) ∧
    σ (.n 11244) = σ (.n 2639) ∧ σ (.n 11245) = S2.squeeze.1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **Statements `10209 ..< 10251`, completely.** -/
theorem vtZt_complete {rd : Reader} {w : ℕ → E} {args : List E} (hl : args.length = 22) {S2 : Fs}
    (hSr : rateOf S2.pend =
      [vtσ rd w args (.n 9416), vtσ rd w args (.n 9418), 0, 0, 0, 0, 0, 0])
    (hSc : S2.cap = [vtσ rd w args (.n 9404), vtσ rd w args (.n 9405), vtσ rd w args (.n 9406),
      vtσ rd w args (.n 9407), vtσ rd w args (.n 9408)])
    (hcan : AllCanonical (rateOf S2.pend ++ S2.cap))
    (hc6 : IsCanonical128 (vtσ rd w args (.n 6))) (hc7 : IsCanonical128 (vtσ rd w args (.n 7)))
    (hp0 : LoadHolds rd (vtσ rd w args (.n 16)) 162 (multilinearEval
      [ofK ((vtσ rd w args (.n 6)).limb 0), ofK ((vtσ rd w args (.n 7)).limb 0)] [S2.squeeze.1]))
    (hp1 : LoadHolds rd (vtσ rd w args (.n 16)) 163 (multilinearEval
      [ofK ((vtσ rd w args (.n 6)).limb 1), ofK ((vtσ rd w args (.n 7)).limb 1)] [S2.squeeze.1]))
    (hp2 : LoadHolds rd (vtσ rd w args (.n 16)) 164 0) :
    (∀ s ∈ (vtPre.drop 10209).take 42, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) ∧
      ZtOut (vtσ rd w args) S2 := by
  have g : GoodL rd w (vtσ rd w args) zTail := vt_goodL hl 10209 zTail zTail_at
  have gk : Good rd vtSL w (vtσ rd w args) (.keccak [.n 9416, .n 9418, .n 5872, .n 5872, .n 5872,
      .n 5873, .n 5874, .n 5875, .n 9404, .n 9405, .n 9406, .n 9407, .n 9408] (lyOuts 11198) false
      false) := (vt_goodL (rd := rd) (w := w) hl 10209 [.atom (.keccak [.n 9416, .n 9418, .n 5872,
      .n 5872, .n 5872, .n 5873, .n 5874, .n 5875, .n 9404, .n 9405, .n 9406, .n 9407, .n 9408]
      (lyOuts 11198) false false)] (by decide +kernel)).1
  have gch : GoodL rd w (vtσ rd w args) (challengeT (.n 11198) (.n 11199) 11211) :=
    vt_goodL hl 10210 _ (by decide +kernel)
  have gz := vt_goodL (rd := rd) (w := w) hl 5194 [.atom (.const (.n 5872) (word 0 0 0)),
    .atom (.const (.n 5873) (word 0 0 0)), .atom (.const (.n 5874) (word 0 0 0)),
    .atom (.const (.n 5875) (word 0 0 0))] (by decide +kernel)
  have e := tbStmtsEqb_sound zTail_at
  have hlen42 : zTail.length = 42 := rfl
  suffices H : (∀ s ∈ zTRest, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) ∧
      ZtOut (vtσ rd w args) S2 by
    refine ⟨fun s hs => ?_, H.2⟩
    rw [← hlen42, ← e] at hs
    exact vt_block hl 10209 zTail zTail_at zTRest (by decide +kernel) H.1 s hs
  generalize vtσ rd w args = σ at *
  simp only [zTail, GoodL, GoodS, Good, fixNe, Nat.reduceLT, and_true, ↓reduceIte] at g
  obtain ⟨g10209, g10210, g10211, g10212, g10213, g10214, g10215, g10216, g10217, g10218, g10219, g10220, g10221, g10222, g10223, g10224, g10225, g10226, g10227, g10228, g10229, g10230, g10231, g10232, g10233, g10234, g10235, g10236, g10237, g10238, g10239, g10240, g10241, g10242, g10243, g10244, g10245, g10246, g10247, g10248, g10249, g10250⟩ := g
  simp only [GoodL, GoodS, Good, fixNe, tb_word_zero] at gz
  obtain ⟨hz0, hz1, hz2, hz3, -⟩ := gz
  -- the squeeze
  have hin : ([.n 9416, .n 9418, .n 5872, .n 5872, .n 5872, .n 5873, .n 5874, .n 5875, .n 9404,
      .n 9405, .n 9406, .n 9407, .n 9408] : List V).map σ = rateOf S2.pend ++ S2.cap := by
    rw [hSr, hSc]; simp [hz0, hz1, hz2, hz3]
  have k10209 : (Atom.keccak [.n 9416, .n 9418, .n 5872, .n 5872, .n 5872, .n 5873, .n 5874,
      .n 5875, .n 9404, .n 9405, .n 9406, .n 9407, .n 9408] (lyOuts 11198) false false).Holds rd σ :=
    z_keccak gk (by rw [hin]; exact hcan)
  obtain ⟨-, hPk, -⟩ := ly_keccak k10209
  rw [hin] at hPk
  have hch : ChallengeOk σ (.n 11198) (.n 11199) 11211 :=
    z_challenge gch
      (by rw [hPk 1 (by norm_num)]; exact cellsOfState_canonical _ _ _)
  have vrm : σ (.n 11217) = S2.squeeze.1 :=
    challengeT_value hch (hPk 0 (by norm_num)) (hPk 1 (by norm_num))
  -- the public words' limbs
  have l6 : σ (.n 11218) = ofK ((σ (.n 6)).limb 0) := by
    have := g10218 0 (by simp); simpa [limbAt] using this
  have l7 : σ (.n 11223) = ofK ((σ (.n 7)).limb 0) := by
    have := g10224 0 (by simp); simpa [limbAt] using this
  have h6 : σ (.n 11221) = ofK ((σ (.n 6)).limb 1) := by
    rw [g10221, g10219, g10220, word_y_inv, l6]; exact split_hi hc6
  have h7 : σ (.n 11226) = ofK ((σ (.n 7)).limb 1) := by
    rw [g10227, g10225, g10226, word_y_inv, l7]; exact split_hi hc7
  have i10214 : (Atom.assertInK (.n 11211) (.n 11214)).Holds rd σ := ⟨hch.2.2.2.1, hch.2.2.2.2.1⟩
  have i10222 : (Atom.assertInK (.n 11218) (.n 11221)).Holds rd σ := by
    rw [Atom.Holds, l6, h6]; exact ⟨ofK_isInK _, ofK_isInK _⟩
  have i10228 : (Atom.assertInK (.n 11223) (.n 11226)).Holds rd σ := by
    rw [Atom.Holds, l7, h7]; exact ⟨ofK_isInK _, ofK_isInK _⟩
  have s10233 : (Atom.load (.n 11230) (.n 16) 162).Holds rd σ := by
    show LoadHolds rd _ _ _
    have e : multilinearEval [ofK ((σ (.n 6)).limb 0), ofK ((σ (.n 7)).limb 0)] [S2.squeeze.1] =
        σ (.n 11230) := by
      rw [g10232, g10231, g10230, g10229, g10223, l6, l7, vrm]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD]
      ring
    rw [← e]; exact hp0
  have s10237 : (Atom.load (.n 11233) (.n 16) 163).Holds rd σ := by
    show LoadHolds rd _ _ _
    have e : multilinearEval [ofK ((σ (.n 6)).limb 1), ofK ((σ (.n 7)).limb 1)] [S2.squeeze.1] =
        σ (.n 11233) := by
      rw [g10236, g10235, g10234, h6, h7, vrm]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD]
      ring
    rw [← e]; exact hp1
  have s10239 : (Atom.load (.n 11234) (.n 16) 164).Holds rd σ := by
    show LoadHolds rd _ _ _
    rw [g10238, tb_word_zero]; exact hp2
  have hrest : ∀ s ∈ zTRest, VSH (coreProgram.Rel rd) rd σ s := by
    intro s hs
    simp only [zTRest, List.mem_cons, List.not_mem_nil, or_false] at hs
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl := hs
    · exact k10209
    · exact i10214
    · exact i10222
    · exact i10228
    · exact s10233
    · exact s10237
    · exact s10239
  refine ⟨hrest, vrm, ?_, ?_, g10248, g10249, by rw [g10250, vrm]⟩
  · rw [g10240, g10241, g10242, g10243, g10244, hPk 8 (by norm_num), hPk 9 (by norm_num),
      hPk 10 (by norm_num), hPk 11 (by norm_num), hPk 12 (by norm_num)]
    rfl
  · rw [g10247, g10246, g10245, vtW157]

end
end LeanVM.Guest.B1.Tables
