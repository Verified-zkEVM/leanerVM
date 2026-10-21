/-
  LeanVM.E2E.Complete.DecodeVsAgree

  `verify_sub`'s child proof decoded from a valuation agreeing with the node on its named cells.
-/

module

public import LeanVM.Guest.B2C.NodeAgree
public import LeanVM.Guest.B2C.CplSem
public import LeanVM.Guest.B1.Comp.VerifySub.PlacedEq

/-!
# The child proof at an agreeing valuation

V_I's decoder reads `verify_sub`'s valuation at a frame of the memory (`Located.valAt`), which at
an honest frame agrees with the instance only on the cells its path names (`B2C.NodeAgree`).
`vsProofOf` reads nineteen values of the valuation (`vsProofVars`: the stream pointer, the eight
announced sizes and rate, the dispatched opening's call words), each named by every path of
`verify_sub`'s body (`vs_named`: the first ten loads of the straight prefix, `vs_own_loads`, and
the dispatch's call event, `vs_walk_ret`) at a cell of its frame. Hence:

* `vsProofOf_congr`: the decoded proof is the same at valuations agreeing on `vsProofVars`;
* `vsProofOf_of_agree`: at a valuation agreeing with a `verify_sub` node on its named cells, the
  decoded proof is the node's (and so are the opening's call words, `vsOpen_of_agree`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.B1 (stmtsEqb stmtsEqb_sound)

@[expose] public section

/-- The values `vsProofOf` reads of `verify_sub`'s valuation. -/
def vsProofVars : List V :=
  [.n 14, .n 15, .n 31, .n 46, .n 61, .n 76, .n 91, .n 106, .n 121, .n 1171, .n 1172, .n 1627,
    .n 419, .n 434, .n 726, .n 1648, .n 1649, .n 1650, .n 1651]

/-- The opening's call words at valuations agreeing on `vsProofVars`. -/
theorem vsOpen_congr {σ σ' : Val} (h : ∀ v ∈ vsProofVars, σ' v = σ v) :
    vsOpenArgs σ' = vsOpenArgs σ ∧ vsOpenRets σ' = vsOpenRets σ := by
  simp only [vsProofVars, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  simp only [vsOpenArgs, vsOpenRets, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, and_self]

/-- **The decoded proof at valuations agreeing on `vsProofVars`.** -/
theorem vsProofOf_congr (bytecode : List K) (rd : Reader) {σ σ' : Val}
    (wO : String → List E → List E → List Opening) (h : ∀ v ∈ vsProofVars, σ' v = σ v) :
    vsProofOf bytecode rd σ' wO = vsProofOf bytecode rd σ wO := by
  obtain ⟨ha, hr⟩ := vsOpen_congr h
  have hrows : vsRows σ' = vsRows σ := by
    unfold vsRows
    refine List.map_congr_left fun t ht => ?_
    have ht6 : t < 6 := List.mem_range.mp ht
    rw [h _ (by interval_cases t <;> decide)]
  have hlay : vsLayout bytecode σ' = vsLayout bytecode σ := by
    unfold vsLayout vsLogMem
    rw [hrows, h (.n 15) (by decide)]
  have hrate : vsRate σ' = vsRate σ := by
    unfold vsRate
    rw [h (.n 121) (by decide)]
  unfold vsProofOf vsStreamLen
  rw [hlay, hrate, ha, hr, h (.n 14) (by decide)]

/-! ## The values every path of `verify_sub` names -/

theorem coreOf_16 : coreOf 16 = Data.core15 := by
  have h1 : (coreOf 16).name = "verify_sub" := by decide +kernel
  have h := End.coreOf_find (j := 16) (by norm_num) (by decide)
  rw [h1, find_verify_sub] at h
  exact (Option.some.inj h).symm

/-- A dispatch is stuck or calls one of its callees. -/
theorem pick_cases (σ : Val) (x : V) (args rets : List V) :
    ∀ (j : ℕ) (fs : List String),
      pick σ x args rets j fs = .stuck ∨ ∃ f, pick σ x args rets j fs = .fall [.call f args rets]
  | _, [] => Or.inl rfl
  | j, f :: fs => by
      unfold pick
      split
      · exact Or.inr ⟨f, rfl⟩
      · exact pick_cases σ x args rets (j + 1) fs

/-- **`verify_sub`'s paths**: the straight prefix's events, the dispatched opening's call, the
straight suffix's events. -/
theorem vs_walk_ret {σ : Val} {es : List Memory.Ev} {vs : List V}
    (hw : walk σ (Fn.body Data.core15) = .ret es vs) :
    ∃ f, es = vsPre1.flatMap (slEvs σ) ++
      .call f [.n 1171, .n 1172, .n 1627, .n 419, .n 434, .n 726]
        [.n 1648, .n 1649, .n 1650, .n 1651] :: vsPost2.flatMap (slEvs σ) := by
  rw [core15_body, vsPre_eq, vsBody_split, List.append_assoc, List.cons_append,
    B1.walk_pre_straight σ _ vsPre1 vsPre1_straight, walk,
    walk_straight σ [] vsPost2 vsPost2_straight] at hw
  simp only [vsDisp, walk1] at hw
  rcases pick_cases σ (.n 1643) [.n 1171, .n 1172, .n 1627, .n 419, .n 434, .n 726]
    [.n 1648, .n 1649, .n 1650, .n 1651] 0 openNames with h | ⟨f, h⟩
  · rw [h] at hw
    simp [Out.seq, Out.pre] at hw
  · rw [h] at hw
    simp only [Out.seq, Out.pre, Out.ret.injEq] at hw
    exact ⟨f, by rw [← hw.1]; simp⟩

/-- An atom of the straight prefix is an event of every path. -/
theorem mem_vsPre1_of {a : Atom} {i : ℕ}
    (h : stmtsEqb [.atom a] ((vsPre.drop i).take 1) = true) (hi : i < 1926) :
    Stmt.atom a ∈ vsPre1 := by
  have h1 := stmtsEqb_sound h
  have h2 : Stmt.atom a ∈ (vsPre.drop i).take 1 := by rw [← h1]; exact List.mem_singleton_self _
  have h3 : (vsPre.drop i).take 1 = ((vsPre.take 1926).drop i).take 1 := by
    rw [List.drop_take, List.take_take]
    congr 1
    omega
  rw [h3] at h2
  have h4 := List.mem_of_mem_drop (List.mem_of_mem_take h2)
  unfold vsPre1
  rwa [← vsPre_eq]

theorem vsProofVars_cells :
    ∀ v ∈ vsProofVars, 2 ≤ B2C.cellJ 16 v ∧ B2C.cellJ 16 v < B2C.fsN 16 := by decide +kernel

theorem vsProofVars_own : ∀ v ∈ vsProofVars, v ∉ [.n 1171, .n 1172, .n 1627, .n 419, .n 434,
    .n 726, .n 1648, .n 1649, .n 1650, .n 1651] → v = .n 14 ∨ ∃ k < 8, v = .n (ownD k) := by
  decide

/-- **Every path of `verify_sub` names the values `vsProofOf` reads**, at cells of its frame. -/
theorem vs_named {σ : Val} {es : List Memory.Ev} {vs : List V}
    (hw : walk σ (coreOf 16).body = .ret es vs) :
    ∀ v ∈ vsProofVars, v ∈ B2C.namedOf (coreOf 16).params es vs ∧ 2 ≤ B2C.cellJ 16 v ∧
      B2C.cellJ 16 v < B2C.fsN 16 := by
  intro v hv
  refine ⟨?_, vsProofVars_cells v hv⟩
  rw [coreOf_16] at hw
  obtain ⟨f, rfl⟩ := vs_walk_ret hw
  by_cases ho : v ∈ [.n 1171, .n 1172, .n 1627, .n 419, .n 434, .n 726, .n 1648, .n 1649,
    .n 1650, .n 1651]
  · refine B2C.uses_named (e := Memory.Ev.call f [.n 1171, .n 1172, .n 1627, .n 419, .n 434, .n 726]
      [.n 1648, .n 1649, .n 1650, .n 1651]) (by simp) ?_
    simpa [Memory.Ev.uses] using ho
  · have hl : ∀ k < 8, Memory.Ev.atom (.load (.n (ownD k)) (.n 14) k) ∈
        vsPre1.flatMap (slEvs σ) ++ .call f [.n 1171, .n 1172, .n 1627, .n 419, .n 434, .n 726]
          [.n 1648, .n 1649, .n 1650, .n 1651] :: vsPost2.flatMap (slEvs σ) := fun k hk =>
      List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, mem_vsPre1_of (vs_own_loads k (by omega))
        (ownI_lt k (by omega)), by simp [slEvs]⟩)
    rcases vsProofVars_own v hv ho with rfl | ⟨k, hk, rfl⟩
    · exact B2C.uses_named (hl 0 (by norm_num)) (by simp [Memory.Ev.uses, atomUses])
    · exact B2C.uses_named (hl k hk) (by simp [Memory.Ev.uses, atomUses])

/-- **The child proof at a valuation agreeing with a `verify_sub` node** on its named cells. -/
theorem vsProofOf_of_agree {σ σ' : Val} {bufs : List ℕ} {ks : List Tree}
    (h : B2C.NodeAgree (.node "verify_sub" σ bufs ks) σ') {es : List Memory.Ev} {vs : List V}
    (hw : walk σ (coreOf 16).body = .ret es vs) (bytecode : List K) (rd : Reader)
    (wO : String → List E → List E → List Opening) :
    vsProofOf bytecode rd σ' wO = vsProofOf bytecode rd σ wO := by
  have hj : B2C.idxOf "verify_sub" = some 16 := by decide +kernel
  refine vsProofOf_congr bytecode rd wO fun v hv => ?_
  obtain ⟨hn, h2, h3⟩ := vs_named hw v hv
  exact h.eq hj hw hn h2 h3

/-- The opening's call words at a valuation agreeing with a `verify_sub` node. -/
theorem vsOpen_of_agree {σ σ' : Val} {bufs : List ℕ} {ks : List Tree}
    (h : B2C.NodeAgree (.node "verify_sub" σ bufs ks) σ') {es : List Memory.Ev} {vs : List V}
    (hw : walk σ (coreOf 16).body = .ret es vs) :
    vsOpenArgs σ' = vsOpenArgs σ ∧ vsOpenRets σ' = vsOpenRets σ := by
  have hj : B2C.idxOf "verify_sub" = some 16 := by decide +kernel
  refine vsOpen_congr fun v hv => ?_
  obtain ⟨hn, h2, h3⟩ := vs_named hw v hv
  exact h.eq hj hw hn h2 h3

end
end LeanVM.E2E.Complete
