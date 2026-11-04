/-
  LeanVM.Guest.B1.Tables.Vt.Pi

  `verify_tables`' public input binding and its return: the challenge squeezed after the table
  evaluations, the three memory limbs' claims, and the returned capacity, cursor, round count,
  bytecode value and challenge.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Evals

/-!
# The public input's binding (G:2521-2532)

`vt_pi`: `rm` is the squeeze after the 157 evaluations; the public input's two words are
canonical, and the pool's last three claims are the lines through their limbs `0`, `1` at `rm`
and `0`; the function returns the sponge's capacity after the squeeze, the cursor `157` words
on, `g^n`, the bytecode value and `rm`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The sponge after the evaluations. -/
def vtEvalFs (σ : Val) : Fs := (⟨vtCapV σ 0, []⟩ : Fs).absorbAll (vtEvs σ) dsObserve

theorem vtW157 : word 174483046400 0 0 = gen ^ 157 := by
  rw [tb_word_eOfNat]
  show ofK (K.ofBits 174483046400) = gen ^ 157
  rw [gen_pow_eq_ofK, show K.ofBits 174483046400 = Parameters.addressOfIndex 157 by decide +kernel]

theorem vt_evalFs_eq {rd : Reader} {σ : Val} (h : VtH rd σ) :
    vtEvalFs σ = ⟨vtCapV σ 39, [(σ (.n (vtEvB 156)), dsObserve)]⟩ := by
  obtain ⟨h38, hp38⟩ := vt_evals_fs h 38 (by norm_num)
  have hr : vtEvs σ = (List.range 156).map (fun k ↦ σ (.n (vtEvB k))) ++
      [σ (.n (vtEvB 156))] := by
    show (List.range (156 + 1)).map _ = _
    rw [List.range_succ, List.map_append, List.map_singleton]
  have ht : (vtEvs σ).take (4 * (38 + 1)) = (List.range 156).map fun k ↦ σ (.n (vtEvB k)) := by
    rw [hr, List.take_left' (by simp)]
  rw [ht] at h38
  rw [vtEvalFs, hr, fs_absorbAll_append, h38, tb_absorbAll_full' _ (by simp [vtEvs]) _
    (by simp) (by simp), ← hp38]
  rfl

set_option maxRecDepth 10000 in
/-- **The public input's binding and the return.** -/
theorem vt_pi {rd : Reader} {σ : Val} (h : VtH rd σ) :
    σ (.n 6837) = (vtEvalFs σ).squeeze.1 ∧
      ((List.range 5).map fun k ↦ σ (.n (6855 + k))) = (vtEvalFs σ).squeeze.2.cap ∧
      σ (.n 6862) = σ (.n 2609) * gen ^ 157 ∧ σ (.n 6863) = σ (.n 2500) ∧
      σ (.n 6864) = σ (.n 581) ∧ σ (.n 6865) = σ (.n 6837) ∧ σ (.n 6866) = σ (.n 2609) ∧
      IsCanonical128 (σ (.n 6)) ∧ IsCanonical128 (σ (.n 7)) ∧
      LoadHolds rd (σ (.n 15)) 162 (multilinearEval [ofK ((σ (.n 6)).limb 0),
        ofK ((σ (.n 7)).limb 0)] [σ (.n 6837)]) ∧
      LoadHolds rd (σ (.n 15)) 163 (multilinearEval [ofK ((σ (.n 6)).limb 1),
        ofK ((σ (.n 7)).limb 1)] [σ (.n 6837)]) ∧
      LoadHolds rd (σ (.n 15)) 164 0 := by
  have z2 := h.atomAt 2607 (.const (.n 2549) (word 0 0 0)) (by decide +kernel)
  have z3 := h.atomAt 2608 (.const (.n 2550) (word 0 0 0)) (by decide +kernel)
  have z4 := h.atomAt 2609 (.const (.n 2551) (word 0 0 0)) (by decide +kernel)
  have z5 := h.atomAt 2610 (.const (.n 2552) (word 0 0 0)) (by decide +kernel)
  have k := h.atomAt 6251 (.keccak [.n 5696, .n 5698, .n 2549, .n 2549, .n 2549, .n 2550, .n 2551,
    .n 2552, .n 5684, .n 5685, .n 5686, .n 5687, .n 5688] (lyOuts 6818) false false)
    (by decide +kernel)
  obtain ⟨_, hch⟩ := h.sliceAt 6252 (challengeT (.n 6818) (.n 6819) 6831) (by decide +kernel)
  rw [holds_challengeT] at hch
  have a10218 := h.atomAt 6261 (.add (.n 6839) (.n 6) (.n 6838)) (by decide +kernel)
  have a10220 := h.atomAt 6262 (.const (.n 6840) (word 1 0 1)) (by decide +kernel)
  have a10221 := h.atomAt 6263 (.mul (.n 6841) (.n 6839) (.n 6840)) (by decide +kernel)
  have a10222 := h.atomAt 6264 (.assertInK (.n 6838) (.n 6841)) (by decide +kernel)
  have a10223 := h.atomAt 6265 (.copy (.n 6842) (.n 6838)) (by decide +kernel)
  have a10225 := h.atomAt 6267 (.add (.n 6844) (.n 7) (.n 6843)) (by decide +kernel)
  have a10226 := h.atomAt 6268 (.const (.n 6845) (word 1 0 1)) (by decide +kernel)
  have a10227 := h.atomAt 6269 (.mul (.n 6846) (.n 6844) (.n 6845)) (by decide +kernel)
  have a10228 := h.atomAt 6270 (.assertInK (.n 6843) (.n 6846)) (by decide +kernel)
  have a10229 := h.atomAt 6271 (.copy (.n 6847) (.n 6843)) (by decide +kernel)
  have a10230 := h.atomAt 6272 (.add (.n 6848) (.n 6842) (.n 6847)) (by decide +kernel)
  have a10231 := h.atomAt 6273 (.mul (.n 6849) (.n 6837) (.n 6848)) (by decide +kernel)
  have a10232 := h.atomAt 6274 (.add (.n 6850) (.n 6842) (.n 6849)) (by decide +kernel)
  have a10233 := h.atomAt 6275 (.load (.n 6850) (.n 15) 162) (by decide +kernel)
  have a10234 := h.atomAt 6276 (.add (.n 6851) (.n 6841) (.n 6846)) (by decide +kernel)
  have a10235 := h.atomAt 6277 (.mul (.n 6852) (.n 6837) (.n 6851)) (by decide +kernel)
  have a10236 := h.atomAt 6278 (.add (.n 6853) (.n 6841) (.n 6852)) (by decide +kernel)
  have a10237 := h.atomAt 6279 (.load (.n 6853) (.n 15) 163) (by decide +kernel)
  have a10238 := h.atomAt 6280 (.const (.n 6854) (word 0 0 0)) (by decide +kernel)
  have a10239 := h.atomAt 6281 (.load (.n 6854) (.n 15) 164) (by decide +kernel)
  have r0 := h.atomAt 6282 (.copy (.n 6855) (.n 6826)) (by decide +kernel)
  have r1 := h.atomAt 6283 (.copy (.n 6856) (.n 6827)) (by decide +kernel)
  have r2 := h.atomAt 6284 (.copy (.n 6857) (.n 6828)) (by decide +kernel)
  have r3 := h.atomAt 6285 (.copy (.n 6858) (.n 6829)) (by decide +kernel)
  have r4 := h.atomAt 6286 (.copy (.n 6859) (.n 6830)) (by decide +kernel)
  have c10245 := h.atomAt 6287 (.const (.n 6860) (word 174483046400 0 0)) (by decide +kernel)
  have m10246 := h.atomAt 6288 (.mul (.n 6861) (.n 2609) (.n 6860)) (by decide +kernel)
  have r5 := h.atomAt 6289 (.copy (.n 6862) (.n 6861)) (by decide +kernel)
  have r6 := h.atomAt 6290 (.copy (.n 6863) (.n 2500)) (by decide +kernel)
  have r7 := h.atomAt 6291 (.copy (.n 6864) (.n 581)) (by decide +kernel)
  have r8 := h.atomAt 6292 (.copy (.n 6865) (.n 6837)) (by decide +kernel)
  have r9 := h.atomAt 6293 (.copy (.n 6866) (.n 2609)) (by decide +kernel)
  simp only [Atom.Holds, tb_word_zero] at z2 z3 z4 z5 a10218 a10220 a10221 a10222 a10223 a10225
  simp only [Atom.Holds] at a10226 a10227 a10228 a10229 a10230 a10231 a10232
  simp only [Atom.Holds, tb_word_zero] at a10233 a10234 a10235 a10236 a10237 a10238 a10239
  simp only [Atom.Holds] at r0 r1 r2 r3 r4 c10245 m10246 r5 r6 r7 r8 r9
  -- the squeeze
  obtain ⟨hcan, hP, hC⟩ := ly_keccak k
  have e156 := tb_pack_cells (vt_eval h (k := 156) (by norm_num)).2.1
    (hcan _ (by rw [show vtEvB 156 + 7 = 5696 from rfl]; simp))
  have hin : ([.n 5696, .n 5698, .n 2549, .n 2549, .n 2549, .n 2550, .n 2551, .n 2552, .n 5684,
      .n 5685, .n 5686, .n 5687, .n 5688] : List V).map σ =
      rateOf (vtEvalFs σ).pend ++ (vtEvalFs σ).cap := by
    rw [vt_evalFs_eq h, rateOf_eq_cells _ (by simp)]
    simp only [List.map_cons, List.map_nil, pendCells, List.flatMap_cons, List.flatMap_nil,
      List.length_cons, List.length_nil, List.cons_append, List.nil_append, List.append_nil,
      z2, z3, z4, z5]
    rw [show vtEvB 156 + 7 = 5696 from rfl, show vtEvB 156 + 9 = 5698 from rfl] at e156
    rw [e156.1, e156.2]
    rfl
  rw [hin] at hP hC
  -- the public input's limbs
  rw [word_y_inv] at a10220 a10226
  rw [a10221, a10218, a10220] at a10222
  rw [a10227, a10225, a10226] at a10228
  obtain ⟨hc6, hl6⟩ := (split_iff _ _).mp a10222
  obtain ⟨hc7, hl7⟩ := (split_iff _ _).mp a10228
  have hh6 : σ (.n 6841) = ofK ((σ (.n 6)).limb 1) := by
    rw [a10221, a10218, a10220, hl6]; exact split_hi hc6
  have hh7 : σ (.n 6846) = ofK ((σ (.n 7)).limb 1) := by
    rw [a10227, a10225, a10226, hl7]; exact split_hi hc7
  refine ⟨challengeT_value hch.1 (hP 0 (by omega)) (hP 1 (by omega)), ?_, ?_, r6, r7, r8, r9, hc6,
    hc7, ?_, ?_, by rw [← a10238]; exact a10239⟩
  · show _ = capOf (permOf (rateOf (vtEvalFs σ).pend ++ (vtEvalFs σ).cap))
    rw [← hC]
    simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, lyCap, r0, r1, r2, r3, r4]
  · rw [r5, m10246, c10245, vtW157]
  · have e : multilinearEval [ofK ((σ (.n 6)).limb 0), ofK ((σ (.n 7)).limb 0)] [σ (.n 6837)] =
        σ (.n 6850) := by
      rw [a10232, a10231, a10230, a10229, a10223, ← hl6, ← hl7]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD]
      ring
    rw [e]; exact a10233
  · have e : multilinearEval [ofK ((σ (.n 6)).limb 1), ofK ((σ (.n 7)).limb 1)] [σ (.n 6837)] =
        σ (.n 6853) := by
      rw [a10236, a10235, a10234, ← hh6, ← hh7]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD]
      ring
    rw [e]; exact a10237

end
end LeanVM.Guest.B1.Tables
