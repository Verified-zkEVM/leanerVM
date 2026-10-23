/-
  LeanVM.Guest.B1.Selectors.LayoutBasic

  Layouts of words for B1-c's completeness: runs `(e, ws)` (word `j` at `g^(e + j)`), the memory
  holding them, and a reader that holds them, to evaluate a body on before the memory is known.
-/

module

public import LeanVM.Guest.B1.Fwd.Canon
public import LeanVM.Guest.B1.Tables.Basic

/-!
# Layouts

A layout is a list of runs `(e, ws)`: word `j` of `ws` at the address `g^(e + j)`. `MemLay rd L`:
the memory holds every run (`TbReadsAt` at `ofK (g^e)`). `layRd L`: a reader answering every
address of a run with one of its words (by choice); on a memory holding `L` it answers as the
memory does (`layRd_agree`). An honest body is evaluated on `layRd` of its inputs (`Fwd.ev`), and
its loads of them hold on every memory holding them (`load_of_layRd`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- Runs of words: word `j` of `(e, ws)` at `g^(e + j)`. -/
abbrev TLay : Type := List (ℕ × List E)

/-- The memory holds the layout. -/
def MemLay (rd : Reader) (L : TLay) : Prop := ∀ q ∈ L, TbReadsAt rd (ofK (gpow q.1)) q.2

theorem memLay_append {rd : Reader} {L L' : TLay} :
    MemLay rd (L ++ L') ↔ MemLay rd L ∧ MemLay rd L' := by
  simp only [MemLay, List.mem_append]
  exact ⟨fun h => ⟨fun q hq => h q (Or.inl hq), fun q hq => h q (Or.inr hq)⟩,
    fun h q hq => hq.elim (h.1 q) (h.2 q)⟩

theorem tb_addr_ofK (e j : ℕ) : (ofK (gpow e)).limb 0 * gpow j = gpow (e + j) := by
  rw [limb_ofK]; exact (pow_add _ _ _).symm

theorem tb_isInK_ofK (a : K) : IsInK (ofK a) := by
  simp [IsInK]

/-- An address of the layout. -/
def InLay (L : TLay) (a : K) : Prop := ∃ q ∈ L, ∃ j < q.2.length, a = gpow (q.1 + j)

open Classical in
/-- A reader holding the layout: an address of a run, one of its words there; else nothing. -/
noncomputable def layRd (L : TLay) : Reader := fun a =>
  if h : InLay L a then
    some ((Classical.choose h).2.getD (Classical.choose (Classical.choose_spec h).2) 0)
  else none

theorem memLay_read {rd : Reader} {L : TLay} (hm : MemLay rd L) {q : ℕ × List E} (hq : q ∈ L)
    {j : ℕ} (hj : j < q.2.length) : rd (gpow (q.1 + j)) = some (q.2.getD j 0) := by
  have := (hm q hq j hj).2
  rw [tb_addr_ofK] at this
  rw [this, List.getD_eq_getElem _ _ hj]

/-- **On a memory holding the layout, `layRd` answers its addresses as the memory does.** -/
theorem layRd_agree {rd : Reader} {L : TLay} (hm : MemLay rd L) {a : K} (ha : InLay L a) :
    layRd L a = rd a := by
  unfold layRd
  simp only [ha, ↓reduceDIte]
  obtain ⟨hqL, hex⟩ := Classical.choose_spec ha
  obtain ⟨hj, he⟩ := Classical.choose_spec hex
  conv_rhs => rw [he]
  exact (memLay_read hm hqL hj).symm

end
end LeanVM.Guest.B1.Tables
