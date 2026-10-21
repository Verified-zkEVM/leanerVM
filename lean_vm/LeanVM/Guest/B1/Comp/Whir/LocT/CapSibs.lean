/-
  LeanVM.Guest.B1.Comp.Whir.LocT.CapSibs

  The cap's siblings an opening's decoder reads: on the honest cap they are the opening's path above
  the cap's leaves; a reader agreeing with the honest memory on the cap's cells verify_merkle_cap
  loads reads them alike.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.LocT.Agree
public import LeanVM.Guest.B1.Comp.Whir.OsCapC

/-!
# The cap's siblings

`capSibs_honestW`: on a memory holding the honest cap (`osCapCellsW`), the cap's siblings from an
opening's cap leaf are the opening's path above the cap. `capSibs_congr`: readers agreeing on the
siblings' cells read the same siblings. `VmcCapLoads`: every valid tree of `verify_merkle_cap` loads
the cells of the children of the root and of every flagged node (the statement the Tables agent's
`vmc_capLoads` proves).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {Ht : Bytes → Digest} {depth cd : ℕ} {rt : Digest} {qs : List (ℕ × Opening)}

/-- The sibling of node `heapNode l` is `sibNode l`. -/
theorem capSib_heapNode {q l : ℕ} (hl : l < depth) : capSib (heapNode depth q l) = sibNode depth q l := by
  have hn := heapNode_succ (q := q) hl
  unfold capSib sibNode
  cases hb : q.testBit l
  · simp only [hb, Bool.toNat_false, Nat.add_zero, Bool.not_false, Bool.toNat_true] at hn ⊢
    rw [hn]; simp
  · simp only [hb, Bool.toNat_true, Bool.not_true, Bool.toNat_false, Nat.add_zero] at hn ⊢
    rw [hn]; simp

/-- **The honest cap's siblings are the opening's path** above level `l`. -/
theorem capSibs_honestW (h : OsCapOkW Ht depth cd rt qs) {rd : Reader} {cap : E}
    (hcap : ReadsAt rd cap (osCapCellsW Ht depth cd qs)) {a : ℕ × Opening} (ha : a ∈ qs) :
    ∀ hh l, l + hh = depth → depth - cd ≤ l →
      capSibs rd cap hh (heapNode depth a.1 l) = a.2.path.drop l := by
  have hq := h.pos a ha
  have hlen := h.len a ha
  intro hh
  induction hh with
  | zero =>
    intro l hl _
    rw [capSibs, List.drop_eq_nil_of_le (by omega)]
  | succ hh ih =>
    intro l hl hcl
    rw [capSibs, capSib_heapNode (by omega), os_heapNode_half (by omega), ih (l + 1) (by omega) (by omega)]
    have hs : sibNode depth a.1 l < 2 ^ (cd + 1) := by
      have h1 := os_heapNode_lt (depth := depth) hq (l := l + 1) (by omega)
      have h2 : 2 ^ (depth - (l + 1) + 1) ≤ 2 ^ cd := Nat.pow_le_pow_right (by decide) (by omega)
      unfold sibNode
      have := Bool.toNat_le (!a.1.testBit l)
      rw [pow_succ] at h1 h2 ⊢
      omega
    have hd := osCapD_eqW h ha (Or.inr ⟨l, by omega, rfl, rfl⟩)
    have hc := os_capCellW hcap hs
    rw [hd] at hc
    rw [capNode_eq hc, List.getD_eq_getElem _ _ (by omega)]
    exact (List.drop_eq_getElem_cons (by omega)).symm

/-- **Readers agreeing on the siblings' cells read the same siblings.** -/
theorem capSibs_congr {rd rd' : Reader} {cap : E} :
    ∀ hh c, (∀ i < hh, memAt rd' cap (2 * capSib (c / 2 ^ i)) = memAt rd cap (2 * capSib (c / 2 ^ i)) ∧
      memAt rd' cap (2 * capSib (c / 2 ^ i) + 1) = memAt rd cap (2 * capSib (c / 2 ^ i) + 1)) →
      capSibs rd' cap hh c = capSibs rd cap hh c
  | 0, _, _ => rfl
  | hh + 1, c, h => by
    rw [capSibs, capSibs, capSibs_congr hh (c / 2) fun i hi => by
      have := h (i + 1) (by omega)
      rwa [pow_succ', ← Nat.div_div_eq_div_mul] at this]
    have h0 := h 0 (by omega)
    simp only [pow_zero, Nat.div_one] at h0
    simp only [capNode, h0.1, h0.2]

/-- **Every valid tree of `verify_merkle_cap` loads the cells of the children of the root and of
every flagged node** (the Tables agent's `vmc_capLoads`). -/
def VmcCapLoads : Prop :=
  ∀ (S : BlakeSem) (cd : ℕ), 4 ≤ cd → cd ≤ 8 → ∀ (rd : Reader) (cap flags : E) (rets : List E) (t : Tree),
    t.name = "verify_merkle_cap__L" ++ toString cd → t.ValidB S coreProgram rd [cap, flags] rets → IsInK cap →
    IsInK flags → ∀ p, 1 ≤ p → p < 2 ^ cd → (p = 1 ∨ memAt rd flags p ≠ 0) → ∀ i < 4,
      (cap.limb 0 * Parameters.gpow (4 * p + i), memAt rd cap (4 * p + i)) ∈ t.loadEqns coreProgram

theorem heapNode_div_pow {q l : ℕ} : ∀ i, l + i ≤ depth → heapNode depth q l / 2 ^ i = heapNode depth q (l + i)
  | 0, _ => by simp
  | i + 1, h => by
    rw [pow_succ, ← Nat.div_div_eq_div_mul, heapNode_div_pow i (by omega), os_heapNode_half (by omega)]
    rfl

/-- **A reader satisfying `verify_merkle_cap`'s load equations reads the honest memory's cap
siblings** from a leaf whose climb's interior nodes are flagged. -/
theorem capSibs_agree {rd rd' : Reader} {cap flags : E} {tc : Tree}
    (hloads : ∀ p, 1 ≤ p → p < 2 ^ cd → (p = 1 ∨ memAt rd flags p ≠ 0) → ∀ i < 4,
      (cap.limb 0 * Parameters.gpow (4 * p + i), memAt rd cap (4 * p + i)) ∈ tc.loadEqns coreProgram)
    (hsr : Sat rd (tc.loadEqns coreProgram)) (hsat : Sat rd' (tc.loadEqns coreProgram)) {q : ℕ} (hq : q < 2 ^ depth)
    (hcdd : cd ≤ depth) (hflag : ∀ l, depth - cd < l → l < depth → memAt rd flags (heapNode depth q l) ≠ 0) :
    capSibs rd' cap cd (heapNode depth q (depth - cd)) = capSibs rd cap cd (heapNode depth q (depth - cd)) := by
  refine capSibs_congr cd _ fun i hi => ?_
  rw [heapNode_div_pow i (by omega), capSib_heapNode (by omega)]
  set p := heapNode depth q (depth - cd + i + 1) with hp
  have hp1 : 1 ≤ p := le_trans (Nat.one_le_two_pow) (os_heapNode_ge (depth := depth) (q := q))
  have hpc : p < 2 ^ cd := os_heapNode_cap hq (by omega) (by omega)
  have hpf : p = 1 ∨ memAt rd flags p ≠ 0 := by
    rcases Nat.lt_or_ge (depth - cd + i + 1) depth with hlt | hge
    · exact Or.inr (hflag _ (by omega) hlt)
    · left; rw [hp, show depth - cd + i + 1 = depth by omega]; exact os_heapNode_top hq
  have hs : sibNode depth q (depth - cd + i) = 2 * p + (!q.testBit (depth - cd + i)).toNat := rfl
  have hb := Bool.toNat_le (!q.testBit (depth - cd + i))
  have ag : ∀ k < 4, memAt rd' cap (4 * p + k) = memAt rd cap (4 * p + k) := fun k hk =>
    memAt_agree hsr hsat (hloads p hp1 hpc hpf k hk)
  rw [hs]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h0 | h1
  · rw [h0]
    exact ⟨by have := ag 0 (by omega); rwa [show 4 * p + 0 = 2 * (2 * p + 0) by ring] at this,
      by have := ag 1 (by omega); rwa [show 4 * p + 1 = 2 * (2 * p + 0) + 1 by ring] at this⟩
  · rw [h1]
    exact ⟨by have := ag 2 (by omega); rwa [show 4 * p + 2 = 2 * (2 * p + 1) by ring] at this,
      by have := ag 3 (by omega); rwa [show 4 * p + 3 = 2 * (2 * p + 1) + 1 by ring] at this⟩

/-- `verify_merkle_cap`'s specialization at the cap depth `cd ∈ 4 .. 8`. -/
def vmcName : ℕ → String
  | 4 => "verify_merkle_cap__L4"
  | 5 => "verify_merkle_cap__L5"
  | 6 => "verify_merkle_cap__L6"
  | 7 => "verify_merkle_cap__L7"
  | 8 => "verify_merkle_cap__L8"
  | _ => ""

theorem vmcName_eq {cd : ℕ} (h4 : 4 ≤ cd) (h8 : cd ≤ 8) : "verify_merkle_cap__L" ++ toString cd = vmcName cd := by
  interval_cases cd
  · rw [Nat.toString_eq_repr, Nat.repr_of_lt (by decide), show Nat.digitChar 4 = '4' from Nat.digitChar_eq_four.mpr rfl]
    decide
  · rw [Nat.toString_eq_repr, Nat.repr_of_lt (by decide), show Nat.digitChar 5 = '5' from Nat.digitChar_eq_five.mpr rfl]
    decide
  · rw [Nat.toString_eq_repr, Nat.repr_of_lt (by decide), show Nat.digitChar 6 = '6' from Nat.digitChar_eq_six.mpr rfl]
    decide
  · rw [Nat.toString_eq_repr, Nat.repr_of_lt (by decide), show Nat.digitChar 7 = '7' from Nat.digitChar_eq_seven.mpr rfl]
    decide
  · rw [Nat.toString_eq_repr, Nat.repr_of_lt (by decide), show Nat.digitChar 8 = '8' from Nat.digitChar_eq_eight.mpr rfl]
    decide

end
end LeanVM.Guest.B1
