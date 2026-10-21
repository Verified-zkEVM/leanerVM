/-
  LeanVM.Guest.B1.Comp.Grind

  `grind_check` over a completeness model.
-/

module

public import LeanVM.Guest.B1.Comp.Opening
public import LeanVM.Guest.B1.Grind

/-!
# `grind_check` over a completeness model

The backward half of `grind_check_iff` over a `CompModel`: the base squeezed at tag 3 and the
nonce absorbed at tag 4, both answered by the model (`MeaningGrindCheckComp CM`: the digest the
model's in place of `gcDigest`), the two rows the model's (`holdsB_squeezeStateT_comp`,
`holdsB_fsCompressT_comp`), the lane's bits and their frame run as deployed; `__loop6` is free of
`BLAKE2S` (`freeOn_loop6`). `grind_check_comp`; at `CompModel.deployed` the deployed backward
direction (`grind_check_of_comp`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.E2E.Complete

@[expose] public section

theorem holdsB_gcBit {S : BlakeSem} {C : CallRel} {rd : Reader} {σ : Val} (i : ℕ)
    (kret : List E → Prop) :
    Stmt.HoldsListB S C rd σ (gcBit i) True kret ↔ GcBitOk σ i := by
  cases i <;> simp only [gcBit, GcBitOk, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true]

/-- **`grind_check(st0, st1, nonce, g^bits)` over a completeness model** (`MeaningGrindCheck`, the
squeeze and the absorb answered by the model, the digest checked the answer). -/
def MeaningGrindCheckComp (CM : CompModel) (rd : Reader) : List E → List E → Prop
  | [s0, s1, nonce, ng], rets =>
      rets = [] ∧ ∃ m < ordG, ng = gen ^ m ∧ ∃ cv base d, (s0, s1) = digestScalars cv ∧
        CM.H (digestBytes cv ++ blockOf 0 3) = some base ∧
        CM.H (digestBytes base ++ blockOf nonce 4) = some d ∧ powOk m nonce d = true ∧
        ∃ p, FrameBits rd p (kToNat ((digestScalars d).1.limb 0)) ∧ ∀ j < m, LoadHolds rd p j 0
  | _, _ => False

theorem meaningGrindCheckComp_deployed (rd : Reader) (args rets : List E) :
    MeaningGrindCheckComp CompModel.deployed rd args rets ↔ MeaningGrindCheck rd args rets := by
  match args with
  | [s0, s1, nonce, ng] =>
    simp only [MeaningGrindCheckComp, MeaningGrindCheck, CompModel.deployed, Option.some.injEq,
      gcDigest]
    constructor
    · rintro ⟨h1, m, hm, hN, cv, base, d, hcv, rfl, rfl, h⟩
      exact ⟨h1, m, hm, hN, cv, hcv, h⟩
    · rintro ⟨h1, m, hm, hN, cv, hcv, h⟩
      exact ⟨h1, m, hm, hN, cv, _, _, hcv, rfl, rfl, h⟩
  | [] | [_] | [_, _] | [_, _, _] | _ :: _ :: _ :: _ :: _ :: _ => exact Iff.rfl

/-- **`grind_check` is complete over a completeness model** (G:701-737). -/
theorem grind_check_comp {CM : CompModel} (rd : Reader) (args rets : List E)
    (h : MeaningGrindCheckComp CM rd args rets) :
    coreProgram.RelB CM.sem rd "grind_check" args rets := by
  obtain ⟨s0, s1, nonce, N, rfl⟩ : ∃ s0 s1 nonce N, args = [s0, s1, nonce, N] := by
    match args, h with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  obtain ⟨rfl, m, hm, hN, cv, B, D, hcv, hB, hD, hpow, p, ⟨hpK, hfr⟩, hloads⟩ := h
  rw [relB_iff_sem find_grind_check, core3_body,
    show Fn.params Data.core3 = [.n 0, .n 1, .n 2, .n 3] from rfl, gcBody]
  simp only [holdsListB_append, Stmt.HoldsListB]
  simp only [ite_holdsB_noRet (.n 5) [.atom (.const (.n 6) (word 0 0 0)),
    .atom (.assertEq (.n 2) (.n 6))] [] rfl rfl]
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, holdsB_canonicalLimbsT,
    range_flatten_holdsListB 64 gcBit (fun i => by cases i <;> rfl), holdsB_gcBit, List.map_cons,
    List.map_nil, word_one, word_zero, true_and]
  set o0 := (digestScalars D).1
  set L := kToNat (o0.limb 0)
  have hL : L < 2 ^ 64 := (o0.limb 0).toBitVec.isLt
  set τ := setl (setv (setv (setl (setv (setv (setl (Val.ofArgs [s0, s1, nonce, N]) 4
    [1, N + 1, 0, s0, s1]) 9 7 (sqStateValsD B 3)) 16 14 (fsValsD nonce D 4)) 30
    [ofK (o0.limb 0), o0 + ofK (o0.limb 0), word 1 0 1, ofK (o0.limb 1)]) 34 64
    (fun i => bitE (L.testBit i))) 98 189 (gcVals L)) 287 [p, 1, 1 + N, 1]
  have tb : ∀ i < 64, τ (.n (34 + i)) = bitE (L.testBit i) := fun i hi => by
    simp only [τ, setl, List.length_cons, List.length_nil]
    rw [set_n_lt (by omega), set_n_lt (by omega), set_n_in (by omega) (by omega),
      Nat.add_sub_cancel_left]
  have tg : ∀ t < 189, τ (.n (98 + t)) = gcVals L t := fun t ht => by
    simp only [τ, setl, List.length_cons, List.length_nil]
    rw [set_n_lt (by omega), set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
  have t28 : τ (.n 28) = o0 := by simp only [τ]; b1_look; rfl
  have t30 : τ (.n 30) = ofK (o0.limb 0) := by simp only [τ]; b1_look
  have t2 : τ (.n 2) = nonce := by simp only [τ]; b1_look
  have t5 : τ (.n 5) = N + 1 := by simp only [τ]; b1_look
  have t6 : τ (.n 6) = 0 := by simp only [τ]; b1_look
  have t287 : τ (.n 287) = p := by simp only [τ]; b1_look
  have hcall := (guarded_loop_iff (loop6_step rd N p)).mpr ⟨m, hm, hN, fun j hj => by
    rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact hloads j hj⟩
  have hfree := fun args rets => relB_iff_rel_of_freeOn (S := CM.sem) (rd := rd) freeOn_loop6
    (List.mem_singleton_self "__loop6") args rets
  refine ⟨τ, ?_, ?_, ?_, ⟨?_, fun h5 => ?_, fun _ => trivial⟩, ?_, ?_,
    holdsB_squeezeStateT_comp _ _ _ (show 3 < 256 by decide) ⟨⟨cv, B, ?_, hB, fun k hk => ?_⟩,
    holdsB_fsCompressT_comp _ _ _ _ (show 4 < 256 by decide) ⟨⟨B, D, ?_, ?_, fun k hk1 hk2 => ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_⟩, fun i hi => ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, trivial⟩⟩⟩
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look
  · rw [t5, hN]; exact isInK_add (gen_pow_isInK m) (by rw [← pow_zero gen]; exact gen_pow_isInK 0)
  · rw [t5, hN, e_add_eq_zero_iff, ← pow_zero gen] at h5
    have hm0 : m = 0 := gen_pow_inj (by omega) (by decide) h5
    subst hm0
    unfold powOk at hpow
    simp only [↓reduceIte, decide_eq_true_eq] at hpow
    have hn : nonce = 0 := by rw [eq_ofLimbs nonce, hpow.1, hpow.2.1, hpow.2.2, ← zero_eq_ofLimbs]
    rw [t6, t2, hn]
    exact ⟨rfl, add_zero 0, trivial⟩
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look; exact hcv
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look
    show ((digestScalars B).1, (digestScalars B).2) = _
    rw [Prod.mk.eta]
  · rw [t2]; exact hD
  · simp only [τ]; b1_look
  · rw [t28]; exact (isCanonical128_digestScalars _).1
  · rw [t30, t28]
  · simp only [τ]; b1_look; rfl
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look; rfl
  · cases i with
    | zero =>
      show τ (.n (34 + 0)) = τ (.n (34 + 0)) * τ (.n (34 + 0))
      rw [tb 0 hi, bitE_mul_self]
    | succ i =>
      have e1 := tb (i + 1) hi
      have e2 := tg (3 * i) (by omega)
      have e3 := tg (3 * i + 1) (by omega)
      have e4 := tg (3 * i + 2) (by omega)
      rw [gcVals_0] at e2
      rw [gcVals_1] at e3
      rw [gcVals_2] at e4
      rw [show 34 + (i + 1) = 35 + i by omega] at e1
      rw [show 98 + (3 * i + 1) = 99 + 3 * i by omega] at e3
      rw [show 98 + (3 * i + 2) = 100 + 3 * i by omega] at e4
      have ea : τ (.n (gcAcc i)) = gcAccV L i := by
        cases i with
        | zero => exact tb 0 (by omega)
        | succ i =>
          have := tg (3 * i + 2) (by omega)
          rw [gcVals_2, show 98 + (3 * i + 2) = 100 + 3 * i by omega] at this
          exact this
      refine ⟨by rw [e1, bitE_mul_self], e2, by rw [e3, e1, e2], by rw [e4, ea, e3, gcAccV]⟩
  · have e := tg 188 (by omega)
    rw [show (188 : ℕ) = 3 * 62 + 2 by rfl, gcVals_2, gcAccV_eq L 63 (by omega)] at e
    rw [show 98 + (3 * 62 + 2) = 286 by rfl] at e
    have hr := reconstruct_bits 0 hL
    simp only [Nat.zero_add, pow_zero, one_mul] at hr
    rw [e, t30, show (63 : ℕ) + 1 = 64 from rfl, hr, eOfNat192_of_lt hL]
    have : eOfNat L = ofK (o0.limb 0) := by rw [eOfNat, ofBits_kToNat]
    rw [this]
    exact e_add_self _
  · rw [t287]; exact hpK
  · intro k hk w hw
    rw [t287] at hw
    rw [gcRun_getElem, tb k (by rw [length_gcRun] at hk; exact hk)]
    exact hfr k (by rw [length_gcRun] at hk; exact hk) w hw
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look; exact hcall.1
  · simp only [τ]; b1_look
    exact fun h => (hfree _ _).mpr (hcall.2 h)

/-! ## At the deployed model -/

theorem grind_check_of_comp (rd : Reader) (args rets : List E) (h : MeaningGrindCheck rd args rets) :
    coreProgram.Rel rd "grind_check" args rets := by
  rw [← relB_deployed]
  exact grind_check_comp (CM := CompModel.deployed) rd args rets
    ((meaningGrindCheckComp_deployed rd args rets).mpr h)

end
end LeanVM.Guest.B1
