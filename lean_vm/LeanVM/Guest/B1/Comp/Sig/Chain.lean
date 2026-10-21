/-
  LeanVM.Guest.B1.Comp.Sig.Chain

  A WOTS+C chain step, the steps of a chain and a chain's walk, complete over a completeness
  model (`cStep_complete`, `cSteps_complete`, `cWalk_complete`).
-/

module

public import LeanVM.Guest.B1.Comp.CompletesB
public import LeanVM.Guest.B1.Comp.Sig.Values

/-!
# Chains over a completeness model

The deployed `Chain.lean` and `Walk.lean` completeness lemmas over a `CompModel`: the hash
outputs preset to the model's cells (`hcellC`, `chainFromC`, `tipPairC`), each step's cells
answered (`AnsCells`, `chainAns`, `tipAns`), the rows checked by `compress3_C`/`compress4_C`.
At `CompModel.deployed` they are the deployed lemmas (`cWalk_of_comp`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.E2E.Complete

@[expose] public section

variable {CM : CompModel} {C : CallRel} {rd : Reader}

/-! ## A step -/

/-- A step holds over the model at its constants, canonical cells and the model's answer
(`cStep_holds_iff.mpr`). -/
theorem cStep_holdsB_of (w : Wots) (σ : Val) (i s b : Nat) (v o0 o1 : V)
    (hmd : σ w.md = mdw (stepCount w.lx) true) (next : Prop) (kret : List E → Prop)
    (hk : if w.lx then σ (.n b) = word i 0 0 ∧ σ (.n (b + 1)) = iv0 ∧ σ (.n (b + 2)) = iv1
        else σ (.n b) = word (tw 1 + i * hiMul + s * stepMul) 0 0 ∧
          σ (.n (b + 1)) = σ w.idx + σ (.n b) ∧ σ (.n (b + 2)) = 0 ∧ σ (.n (b + 3)) = iv0 ∧
          σ (.n (b + 4)) = iv1)
    (hc : ∀ c ∈ stepCells w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i s (σ v), IsCanonical128 c)
    (ha : AnsCells CM (stepCells w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i s (σ v)))
    (ho : (σ o0, σ o1) = hcellC CM (stepCells w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i s (σ v)))
    (hn : next) : Stmt.HoldsListB CM.sem C rd σ (cStep w i s b v o0 o1) next kret := by
  unfold cStep
  cases hlx : w.lx
  · rw [hlx] at hmd
    simp only [hlx, Bool.false_eq_true, ↓reduceIte, stepCells, Wots.pp', Wots.idx'] at hk hc ha ho
    simp only [Bool.false_eq_true, ↓reduceIte, cst, addS, b2s, holdsListB_cons_atom, holdsListB_nil,
      Atom.HoldsB, word_zero, stepCount] at hmd ⊢
    obtain ⟨h0, h1, h2, h3, h4⟩ := hk
    refine ⟨h0, h1, h2, h3, h4, ?_, hn⟩
    rw [h3, h4, hmd, h2, h1, h0, word_eq_eOfNat, show σ o0 = _ from congrArg Prod.fst ho, show σ o1 = _ from congrArg Prod.snd ho]
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hc
    exact compress3_C hc ha
  · rw [hlx] at hmd
    simp only [hlx, ↓reduceIte, stepCells, Wots.pp', Wots.adr'] at hk hc ha ho
    simp only [↓reduceIte, cst, b2s, holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB,
      stepCount] at hmd ⊢
    obtain ⟨h0, h1, h2⟩ := hk
    refine ⟨h0, h1, h2, ?_, hn⟩
    rw [h1, h2, hmd, h0, word_eq_eOfNat, show σ o0 = _ from congrArg Prod.fst ho, show σ o1 = _ from congrArg Prod.snd ho]
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hc
    exact compress4_C hc ha

/-- **A step is complete over the model** (`cStep_complete`): its cells answered, the outputs
preset to the model's cells. -/
theorem cStep_comp {w : Wots} {σ : Val} {i s b : Nat} {v o0 o1 : V}
    (hw : w.Out b (b + stepSize w.lx)) (hv : Out b (b + stepSize w.lx) v)
    (ho0 : Out b (b + stepSize w.lx) o0) (ho1 : Out b (b + stepSize w.lx) o1)
    (hmd : σ w.md = mdw (stepCount w.lx) true) (hc : w.Canon σ) (hvc : IsCanonical128 (σ v))
    (ha : AnsCells CM (stepCells w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i s (σ v)))
    (ho : (σ o0, σ o1) = hcellC CM (stepCells w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i s (σ v))) :
    CompletesB CM.sem C rd b (b + stepSize w.lx) (cStep w i s b v o0 o1) σ (fun _ => True) := by
  have he := stepVal_ext w σ i s b
  obtain ⟨hpp, hadr, hidx, hmd'⟩ := hw.keep he
  refine ⟨stepVal w σ i s b, he, trivial, fun next kret hn => ?_⟩
  refine cStep_holdsB_of w _ i s b v o0 o1 (by rw [hmd', hmd]) next kret ?_ ?_ ?_ ?_ hn
  · rw [he.out hw.idx]
    exact stepVal_at w σ i s b
  · rw [hpp, hadr, hidx, he.out hv]; exact canonical_stepCells hc hvc
  · rw [hpp, hadr, hidx, he.out hv]; exact ha
  · rw [hpp, hadr, hidx, he.out hv, he.out ho0, he.out ho1]; exact ho

/-! ## The steps of a chain -/

/-- **The steps of a chain are complete over the model** (`cSteps_complete`). -/
theorem cSteps_comp {w : Wots} {i : Nat} {t0 t1 : V} :
    ∀ (m s b : Nat) (v : V) (σ : Val), w.Below b → (∃ k < b, v = .n k) →
      Out b (b + stepsSize w.lx m) t0 → Out b (b + stepsSize w.lx m) t1 →
      σ w.md = mdw (stepCount w.lx) true → w.Canon σ → IsCanonical128 (σ v) →
      chainAns CM w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i m s (σ v) →
      (σ t0, σ t1) = chainFromC CM w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i m s (σ v) →
      CompletesB CM.sem C rd b (b + stepsSize w.lx m) (cSteps w i t0 t1 m s b v) σ (fun _ => True)
  | 0, s, b, v, σ, hw, hv, ht0, ht1, hmd, hc, hvc, ha, ho => by
      simp only [stepsSize, Nat.mul_zero, Nat.zero_add] at *
      exact cStep_comp hw.out (out_of_lt hv) ht0 ht1 hmd hc hvc ha ho
  | m + 1, s, b, v, σ, hw, hv, ht0, ht1, hmd, hc, hvc, ha, ho => by
      have hsz : stepsSize w.lx (m + 1) = stepSize w.lx + 2 + stepsSize w.lx m := by
        simp only [stepsSize]; ring
      rw [hsz] at ht0 ht1 ⊢
      set h := hcellC CM (stepCells w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i s (σ v)) with hh
      set z := b + stepSize w.lx with hz
      let σ1 := Function.update (Function.update σ (.n z) h.1) (.n (z + 1)) h.2
      have he1' : Ext z (z + 2) σ σ1 :=
        (ext_update σ _ (by omega) (by omega)).comp (ext_update _ _ (by omega) (by omega))
      have he1 : Ext b (b + (stepSize w.lx + 2 + stepsSize w.lx m)) σ σ1 :=
        he1'.mono (by omega) (by omega)
      have hk1 := (hw.mono (show b ≤ z by omega)).keep he1'
      have hv1 : σ1 v = σ v := he1'.below (let ⟨k, hk, e⟩ := hv; ⟨k, by omega, e⟩)
      have hσ1z : σ1 (.n z) = h.1 := by simp [σ1]
      have hσ1z' : σ1 (.n (z + 1)) = h.2 := by simp [σ1]
      have hc1 : w.Canon σ1 := hc.congr hk1
      refine CompletesB.of_ext he1 ?_
      rw [cSteps, ← hz]
      refine CompletesB.append (m := z + 2) (P := fun σ' => σ' (.n z) = h.1) (by omega) (by omega)
        ?_ ?_ ?_
      · exact cStep_below (hw.mono (by omega)) (let ⟨k, hk, e⟩ := hv; ⟨k, by omega, e⟩)
          ⟨z, by omega, rfl⟩ ⟨z + 1, by omega, rfl⟩ (by omega)
      · have := (cStep_comp (CM := CM) (C := C) (rd := rd) (σ := σ1) (i := i) (s := s) (b := b) (v := v)
          (o0 := .n z) (o1 := .n (z + 1)) hw.out (out_of_lt hv)
          (out_of_ge ⟨z, by omega, rfl⟩) (out_of_ge ⟨z + 1, by omega, rfl⟩) (by rw [hk1.2.2.2, hmd]) hc1
          (by rw [hv1]; exact hvc) (by rw [hk1.1, hk1.2.1, hk1.2.2.1, hv1]; exact ha.1)
          (by rw [hσ1z, hσ1z', hk1.1, hk1.2.1, hk1.2.2.1, hv1])).withExt
        exact this.mono le_rfl (by omega) fun σ' hp => by rw [hp.2.apply (by omega), hσ1z]
      · intro σ' he' hp
        have heσ : Ext b (z + 2) σ σ' := (he1'.mono (by omega) le_rfl).comp he'
        have hk' := hw.keep heσ
        have ht0' : Out b (z + 2) t0 := ht0.mono le_rfl (by omega)
        have ht1' : Out b (z + 2) t1 := ht1.mono le_rfl (by omega)
        have := cSteps_comp m (s + 1) (z + 2) (.n z) σ' (hw.mono (by omega))
          ⟨z, by omega, rfl⟩ (ht0.mono (by omega) (by omega)) (ht1.mono (by omega) (by omega))
          (by rw [hk'.2.2.2, hmd]) (hc.congr hk') (by rw [hp]; exact (isCanonical128_hcellC _).1)
          (by rw [hk'.1, hk'.2.1, hk'.2.2.1, hp]; exact ha.2)
          (by rw [heσ.out ht0', heσ.out ht1', ho, chainFromC_succ, hk'.1, hk'.2.1, hk'.2.2.1, hp])
        rwa [show z + 2 + stepsSize w.lx m = b + (stepSize w.lx + 2 + stepsSize w.lx m) by omega]
          at this

/-! ## A chain's walk -/

/-- **A walk is complete over the model** (`cWalk_complete`): from the value `x`, its steps
answered, the tips preset to its end. -/
theorem cWalk_comp {w : Wots} {i d b : Nat} {t0 t1 : V} {σ : Val} (hw : w.Below b)
    (ht0 : Out b (b + walkSize w.lx d) t0) (ht1 : Out b (b + walkSize w.lx d) t1)
    (hmd : σ w.md = mdw (stepCount w.lx) true) (hc : w.Canon σ) {x : E} (hx : IsCanonical128 x)
    (ha : TipAnsC CM w σ i d x)
    (ho0 : σ t0 = (tipPairC CM w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i d x).1)
    (ho1 : d ≠ 3 → σ t1 = (tipPairC CM w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i d x).2) :
    CompletesB CM.sem C rd b (b + walkSize w.lx d) (cWalk w i d b t0 t1) σ (fun _ => True) := by
  unfold cWalk
  by_cases hd : d = 3
  · simp only [hd, ↓reduceIte, hintW]
    exact ⟨σ, Ext.refl _ _ _, trivial, fun next kret hn => ⟨trivial, hn⟩⟩
  · simp only [hd, ↓reduceIte, hintW]
    apply CompletesB.hint_cons
    rw [walkSize_eq _ hd] at ht0 ht1 ⊢
    let σ1 := Function.update σ (.n b) x
    have he1 : Ext b (b + 1) σ σ1 := ext_update σ x le_rfl (by omega)
    have hk := hw.keep he1
    refine CompletesB.of_ext (he1.mono le_rfl (by omega)) ?_
    have hx1 : σ1 (.n b) = x := by simp [σ1]
    have := cSteps_comp (CM := CM) (C := C) (rd := rd) (i := i) (t0 := t0) (t1 := t1) (2 - d) d (b + 1)
      (.n b) σ1 (hw.mono (by omega)) ⟨b, by omega, rfl⟩ (ht0.mono (by omega) (by omega))
      (ht1.mono (by omega) (by omega)) (by rw [hk.2.2.2, hmd]) (hc.congr hk) (by rw [hx1]; exact hx)
      (by rw [hk.1, hk.2.1, hk.2.2.1, hx1]; exact ha hd)
      (by
        rw [he1.out (ht0.mono le_rfl (by omega)), he1.out (ht1.mono le_rfl (by omega)), hk.1, hk.2.1,
          hk.2.2.1, ho0, ho1 hd, hx1]
        simp [tipPairC, hd])
    exact this.mono (by omega) (by omega) fun _ h => h

end
end LeanVM.Guest.B1.Sig
