/-
  LeanVM.Guest.B1.Tables.Vt.Pi

  `verify_tables`' public input binding and its return: the challenge squeezed after the table
  evaluations, the three memory limbs' claims, and the returned capacity, cursor, round count,
  bytecode value and challenge.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Evals

/-!
# The public input's binding (G:2301-2312)

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
  rw [gen_pow_eq_ofK, show K.ofBits 174483046400 = Parameters.gpow 157 by decide +kernel]

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
    σ (.n 11217) = (vtEvalFs σ).squeeze.1 ∧
      ((List.range 5).map fun k ↦ σ (.n (11235 + k))) = (vtEvalFs σ).squeeze.2.cap ∧
      σ (.n 11242) = σ (.n 5932) * gen ^ 157 ∧ σ (.n 11243) = σ (.n 5817) ∧
      σ (.n 11244) = σ (.n 2639) ∧ σ (.n 11245) = σ (.n 11217) ∧
      IsCanonical128 (σ (.n 6)) ∧ IsCanonical128 (σ (.n 7)) ∧
      LoadHolds rd (σ (.n 16)) 162 (multilinearEval [ofK ((σ (.n 6)).limb 0),
        ofK ((σ (.n 7)).limb 0)] [σ (.n 11217)]) ∧
      LoadHolds rd (σ (.n 16)) 163 (multilinearEval [ofK ((σ (.n 6)).limb 1),
        ofK ((σ (.n 7)).limb 1)] [σ (.n 11217)]) ∧
      LoadHolds rd (σ (.n 16)) 164 0 := by
  have z2 := h.atom 5194 (.const (.n 5872) (word 0 0 0)) (by decide +kernel)
  have z3 := h.atom 5195 (.const (.n 5873) (word 0 0 0)) (by decide +kernel)
  have z4 := h.atom 5196 (.const (.n 5874) (word 0 0 0)) (by decide +kernel)
  have z5 := h.atom 5197 (.const (.n 5875) (word 0 0 0)) (by decide +kernel)
  have k := h.atom 10209 (.keccak [.n 9416, .n 9418, .n 5872, .n 5872, .n 5872, .n 5873, .n 5874,
    .n 5875, .n 9404, .n 9405, .n 9406, .n 9407, .n 9408] (lyOuts 11198) false false)
    (by decide +kernel)
  obtain ⟨_, hch⟩ := h.slice 10210 (challengeT (.n 11198) (.n 11199) 11211) (by decide +kernel)
  rw [holds_challengeT] at hch
  have a10218 := h.atom 10219 (.add (.n 11219) (.n 6) (.n 11218)) (by decide +kernel)
  have a10220 := h.atom 10220 (.const (.n 11220) (word 1 0 1)) (by decide +kernel)
  have a10221 := h.atom 10221 (.mul (.n 11221) (.n 11219) (.n 11220)) (by decide +kernel)
  have a10222 := h.atom 10222 (.assertInK (.n 11218) (.n 11221)) (by decide +kernel)
  have a10223 := h.atom 10223 (.copy (.n 11222) (.n 11218)) (by decide +kernel)
  have a10225 := h.atom 10225 (.add (.n 11224) (.n 7) (.n 11223)) (by decide +kernel)
  have a10226 := h.atom 10226 (.const (.n 11225) (word 1 0 1)) (by decide +kernel)
  have a10227 := h.atom 10227 (.mul (.n 11226) (.n 11224) (.n 11225)) (by decide +kernel)
  have a10228 := h.atom 10228 (.assertInK (.n 11223) (.n 11226)) (by decide +kernel)
  have a10229 := h.atom 10229 (.copy (.n 11227) (.n 11223)) (by decide +kernel)
  have a10230 := h.atom 10230 (.add (.n 11228) (.n 11222) (.n 11227)) (by decide +kernel)
  have a10231 := h.atom 10231 (.mul (.n 11229) (.n 11217) (.n 11228)) (by decide +kernel)
  have a10232 := h.atom 10232 (.add (.n 11230) (.n 11222) (.n 11229)) (by decide +kernel)
  have a10233 := h.atom 10233 (.load (.n 11230) (.n 16) 162) (by decide +kernel)
  have a10234 := h.atom 10234 (.add (.n 11231) (.n 11221) (.n 11226)) (by decide +kernel)
  have a10235 := h.atom 10235 (.mul (.n 11232) (.n 11217) (.n 11231)) (by decide +kernel)
  have a10236 := h.atom 10236 (.add (.n 11233) (.n 11221) (.n 11232)) (by decide +kernel)
  have a10237 := h.atom 10237 (.load (.n 11233) (.n 16) 163) (by decide +kernel)
  have a10238 := h.atom 10238 (.const (.n 11234) (word 0 0 0)) (by decide +kernel)
  have a10239 := h.atom 10239 (.load (.n 11234) (.n 16) 164) (by decide +kernel)
  have r0 := h.atom 10240 (.copy (.n 11235) (.n 11206)) (by decide +kernel)
  have r1 := h.atom 10241 (.copy (.n 11236) (.n 11207)) (by decide +kernel)
  have r2 := h.atom 10242 (.copy (.n 11237) (.n 11208)) (by decide +kernel)
  have r3 := h.atom 10243 (.copy (.n 11238) (.n 11209)) (by decide +kernel)
  have r4 := h.atom 10244 (.copy (.n 11239) (.n 11210)) (by decide +kernel)
  have c10245 := h.atom 10245 (.const (.n 11240) (word 174483046400 0 0)) (by decide +kernel)
  have m10246 := h.atom 10246 (.mul (.n 11241) (.n 5932) (.n 11240)) (by decide +kernel)
  have r5 := h.atom 10247 (.copy (.n 11242) (.n 11241)) (by decide +kernel)
  have r6 := h.atom 10248 (.copy (.n 11243) (.n 5817)) (by decide +kernel)
  have r7 := h.atom 10249 (.copy (.n 11244) (.n 2639)) (by decide +kernel)
  have r8 := h.atom 10250 (.copy (.n 11245) (.n 11217)) (by decide +kernel)
  simp only [Atom.Holds, tb_word_zero] at z2 z3 z4 z5 a10218 a10220 a10221 a10222 a10223 a10225
  simp only [Atom.Holds] at a10226 a10227 a10228 a10229 a10230 a10231 a10232
  simp only [Atom.Holds, tb_word_zero] at a10233 a10234 a10235 a10236 a10237 a10238 a10239
  simp only [Atom.Holds] at r0 r1 r2 r3 r4 c10245 m10246 r5 r6 r7 r8
  -- the squeeze
  obtain ⟨hcan, hP, hC⟩ := ly_keccak k
  have e156 := tb_pack_cells (vt_eval h (k := 156) (by norm_num)).2.1
    (hcan _ (by rw [show vtEvB 156 + 7 = 9416 from rfl]; simp))
  have hin : ([.n 9416, .n 9418, .n 5872, .n 5872, .n 5872, .n 5873, .n 5874, .n 5875, .n 9404,
      .n 9405, .n 9406, .n 9407, .n 9408] : List V).map σ =
      rateOf (vtEvalFs σ).pend ++ (vtEvalFs σ).cap := by
    rw [vt_evalFs_eq h, rateOf_eq_cells _ (by simp)]
    simp only [List.map_cons, List.map_nil, pendCells, List.flatMap_cons, List.flatMap_nil,
      List.length_cons, List.length_nil, List.cons_append, List.nil_append, List.append_nil,
      z2, z3, z4, z5]
    rw [show vtEvB 156 + 7 = 9416 from rfl, show vtEvB 156 + 9 = 9418 from rfl] at e156
    rw [e156.1, e156.2]
    rfl
  rw [hin] at hP hC
  -- the public input's limbs
  rw [word_y_inv] at a10220 a10226
  rw [a10221, a10218, a10220] at a10222
  rw [a10227, a10225, a10226] at a10228
  obtain ⟨hc6, hl6⟩ := (split_iff _ _).mp a10222
  obtain ⟨hc7, hl7⟩ := (split_iff _ _).mp a10228
  have hh6 : σ (.n 11221) = ofK ((σ (.n 6)).limb 1) := by
    rw [a10221, a10218, a10220, hl6]; exact split_hi hc6
  have hh7 : σ (.n 11226) = ofK ((σ (.n 7)).limb 1) := by
    rw [a10227, a10225, a10226, hl7]; exact split_hi hc7
  refine ⟨challengeT_value hch.1 (hP 0 (by omega)) (hP 1 (by omega)), ?_, ?_, r6, r7, r8, hc6,
    hc7, ?_, ?_, by rw [← a10238]; exact a10239⟩
  · show _ = capOf (permOf (rateOf (vtEvalFs σ).pend ++ (vtEvalFs σ).cap))
    rw [← hC]
    simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, lyCap, r0, r1, r2, r3, r4]
  · rw [r5, m10246, c10245, vtW157]
  · have e : multilinearEval [ofK ((σ (.n 6)).limb 0), ofK ((σ (.n 7)).limb 0)] [σ (.n 11217)] =
        σ (.n 11230) := by
      rw [a10232, a10231, a10230, a10229, a10223, ← hl6, ← hl7]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD]
      ring
    rw [e]; exact a10233
  · have e : multilinearEval [ofK ((σ (.n 6)).limb 1), ofK ((σ (.n 7)).limb 1)] [σ (.n 11217)] =
        σ (.n 11233) := by
      rw [a10236, a10235, a10234, ← hh6, ← hh7]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD]
      ring
    rw [e]; exact a10237

end
end LeanVM.Guest.B1.Tables
