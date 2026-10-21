/-
  LeanVM.E2E.Complete.Stack

  The stack of an execution under a semantics of canonical `BLAKE2S` rows (L3, L4 of
  `docs/roadmap/t6-completeness.md`): admissible sizes, a stack satisfying the leanISA relation
  without Flock with honest padding, whose candidate run V_I takes is the execution.
-/

module

public import LeanVM.E2E.Complete.Model
public import LeanVM.Arithmetization.CompletenessB.Theorem
public import LeanVM.Protocol.LeanIsa.CompleteB
public import LeanVM.Protocol.EndToEnd.Complete.Small

/-!
# The stack of an execution under the honest table

For an execution valid under a semantics `Sm` whose `BLAKE2S` rows are canonical (the honest
table's, `CompModel.chain`), of committed size at most `2^28` counted under `Sm`:

* `exists_admissible_witnessB` (L3): a witness satisfying the constraint statement without the
  compression (`constraintCompletenessB_rows`), over the execution's image, at sizes the verifier
  admits (`exists_admissible_witness` under `Sm`);
* `exists_stack_of_validB` (L3 + L4): the stack of that witness with the free Flock region
  (`stackOfG (genFree slots)`: every row's limbs at their slots) satisfies the relation without
  Flock with honest padding (`m3HonestBlind_stackOfG`), and V_I's candidate run of it
  (`candidateRun`) is the execution (`witnessOf_stackOfG`, `haltingRunB_of_validB`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Complete
open Air.Flat (EnsembleWitness)

@[expose] public section

variable {Sm : BlakeSem}

/-- **An admissible witness under a semantics, within the budget** (`exists_admissible_witness`
under `Sm`). -/
theorem exists_admissible_witnessB [Fact (Canonical Sm)] {prog : Program} {input : PublicInput}
    {t : Trace prog} (hv : ValidExecutionB Sm prog input t)
    (hbudget : t.committedSizeB Sm ≤ 2 ^ maxMu) :
    ∃ w s, SatisfiedByB prog input w ∧ ImageOf w t ∧ Sizes.ofWitness w = some s ∧
      s.Admissible prog := by
  have hcount : ∀ op, t.countB Sm op = runRowsB Sm t op := countB_eq_runRowsB hv.2
  have hheight : ∀ op, 2 ^ Nat.clog 2 (t.countB Sm op) ≤ t.committedSizeB Sm := by
    intro op
    have : 0 < 2 ^ prog.logSize := Nat.two_pow_pos _
    simp only [Trace.committedSizeB]
    cases op <;> omega
  have hcap : (2 : ℕ) ^ maxMu ≤ 2 ^ maxLogRows := Nat.pow_le_pow_right (by norm_num) (by decide)
  have hrows : ∀ op, runRowsB Sm t op ≤ 2 ^ maxLogRows := fun op ↦ by
    rw [← hcount]
    exact (Nat.le_pow_clog (by norm_num) _).trans (((hheight op).trans hbudget).trans hcap)
  obtain ⟨w, hw, hrep, hlen⟩ := constraintCompletenessB_rows hv hrows
  obtain ⟨s, hs⟩ := sizes_of_satisfiedByG hw
  refine ⟨w, s, hw, hrep, hs, ?_⟩
  obtain ⟨hpos, rfl⟩ := eq_of_ofWitness hs
  have hmem : (witnessSizes w hpos).logMem = t.κ := hrep.κ_eq
  have hr : ∀ j : Fin 6, (witnessSizes w hpos).rows j = t.countB Sm (tableOpcode j) := fun j ↦
    (hlen j).trans (hcount _).symm
  have htotal : (LeanIsa.blocks prog (witnessSizes w hpos)).total = t.committedSizeB Sm := by
    have e : tableOpcode 0 = .xor ∧ tableOpcode 1 = .mulNative ∧ tableOpcode 2 = .setConstant ∧
        tableOpcode 3 = .deref ∧ tableOpcode 4 = .jump ∧ tableOpcode 5 = .blake2s := by decide
    rw [blocks_total_eq, hmem, pow_add 2 8]
    simp only [Sizes.τ, hr, e, Trace.committedSizeB]
    ring
  refine ⟨?_, ?_, fun j ↦ (hr j).trans_le (by rw [hcount]; exact hrows _), ?_⟩
  · rw [hmem]
    exact hv.1.1
  · rw [hmem]
    exact hv.1.2.1
  · exact leanIsaμ_le_of_total_le (htotal ▸ hbudget)

/-- The free Flock region carries the deployed slots' limbs. -/
instance : Fact (SlotsOK Sound.F₀ (genFree Sound.F₀.slot)) :=
  ⟨slotsOK_genFree _ Blake2sFlock.slots_injective⟩

/-- **The stack of an execution under the honest table** (L3, L4): admissible sizes and a stack
satisfying the relation without Flock with honest padding whose candidate run is the execution. -/
theorem exists_stack_of_validB [Fact (Canonical Sm)] (hfree : ∀ b, Sm.row b → blakeFree.row b)
    {prog : Program} {input : PublicInput} {t : Trace prog} (hv : ValidExecutionB Sm prog input t)
    (hbudget : t.committedSizeB Sm ≤ 2 ^ 28) :
    ∃ (s : Sizes) (q : Column (leanIsaμ prog s)), s.Admissible prog ∧
      M3HoldsBlind (inst prog s) input q ∧ (inst prog s).PaddingHonest q ∧
      candidateRun prog s q = some t := by
  obtain ⟨w, s, hw, hrep, hs, hadm⟩ := exists_admissible_witnessB hv hbudget
  refine ⟨s, stackOfG (genFree Sound.F₀.slot) prog s w, hadm,
    (m3HonestBlind_stackOfG (F := Sound.F₀) hw hs).1, (m3HonestBlind_stackOfG (F := Sound.F₀) hw hs).2,
    ?_⟩
  have himg := (witnessOf_stackOfG (F := Sound.F₀) (gen := genFree Sound.F₀.slot) hw hs).2.2.2.2
  have hsig : imageOf w.data = ⟨t.κ, t.image⟩ := by
    obtain ⟨hκ, hi⟩ := hrep
    revert hκ hi
    generalize imageOf w.data = p
    obtain ⟨κ, img⟩ := p
    intro hκ hi
    simp only at hκ hi
    subst hκ
    exact image_sigma_eq rfl _ _ fun i ↦ hi i i.isLt
  unfold candidateRun
  rw [himg, hsig]
  exact haltingRunB_of_validB hfree hv

end
end LeanVM.E2E.Complete
