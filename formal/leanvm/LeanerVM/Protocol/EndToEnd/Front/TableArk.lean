/-
  LeanerVM.Protocol.EndToEnd.Front.TableArk

  The table sumcheck's components, read off as statements about their relations: the batching
  challenge's escape from the bus seam, the rounds' family, and the final values' hand-over to
  the table seam.
-/

module

public import LeanerVM.Protocol.EndToEnd.Front.BusSpec
public import LeanerVM.Protocol.TableSumcheck

/-!
# The table sumcheck's relations

`tableSumcheckSecurity` (`LeanerVM.Protocol.TableSumcheck`) appends three securities, the first
and the last written inline. This module states them as public objects on ArkLib's typed
framework from the same hypotheses (`xiSecurity`, `finalValuesSecurity`), and reads them as doom
transitions:

* `xi_escape`: the batching challenge `ξ` escapes doom on the bus seam with probability at most
  `L₀ · (B + 2) / |E|`;
* `tableFamily_sound`: the rounds' family (`Sumcheck.family` of `tableSummand`) is sound, its
  invariant being the side condition no challenge changes;
* `finalValues_keep`: values that pass the final check carry doom on the rounds' last stage to doom
  on the table seam at `tableOut`.
-/

namespace LeanerVM.Protocol.EndToEnd.Front

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Compile LeanerVM.Protocol.TableSumcheck
open CompPoly CMlPolynomialEval OracleComp OracleSpec
open scoped NNReal ENNReal

@[expose] public section

variable (I : M3Instance)

/-- The batching challenge's hypothesis: the true values, fixed before the challenge, are what a
challenge carrying a statement outside the bus seam into the rounds' input relation makes the
combined claim the combination of, and they differ from the claimed values. -/
theorem xi_batch (s : I.Stmt × BusOut I) (o : ∀ i, TheOracle I i) :
    ∃ a : Fin (I.B + 3) → E, ∀ w ρ, ((s, o), w) ∉ Seam.bus I →
      ((start I s ρ (powerBatch (claimed I s) ρ), o), w) ∈
        Sumcheck.relIn (tableSummand I) Sumcheck.unitWeights (side I) →
        a ≠ claimed I s ∧ powerBatch (claimed I s) ρ = powerBatch a ρ :=
  ⟨trueValues I s (theStack o), fun w ρ hin hout ↦ by
      cases w
      obtain ⟨hsum, hside⟩ := hout
      have hsum : powerBatch (claimed I s) ρ = powerBatch (trueValues I s (theStack o)) ρ :=
        hsum.trans (sum_tableSummand I (s, ρ) o)
      refine ⟨fun heq ↦ hin ?_, hsum⟩
      obtain ⟨hzero, htotals⟩ := (trueValues_eq_claimed_iff I s (theStack o)).mp heq
      exact ⟨hzero, htotals, hside⟩⟩

/-- The batching challenge's security, `tableSumcheckSecurity`'s first part, on the typed
framework. -/
def xiSecurity :
    Typed.Security (batchStepT I) (Seam.bus I)
      (Sumcheck.relIn (tableSummand I) Sumcheck.unitWeights (side I))
      (Typed.drawErrors E (((I.B + 3 - 1 : ℕ) : ℝ≥0) / (Nat.card E : ℝ≥0))) :=
  Typed.batchSecurity (xi_batch I)

/-- The error of the batching challenge over at most `L₀` candidates: `L₀ · (B + 2) / |E|`. -/
noncomputable def xiError (L₀ : ℕ) : ℝ≥0∞ :=
  L₀ * ((((I.B + 3 - 1 : ℕ) : ℝ≥0) / (Nat.card E : ℝ≥0) : ℝ≥0) : ℝ≥0∞)

open Classical in
/-- **The batching challenge escapes** doom on the bus seam with probability at most
`L₀ · (B + 2) / |E|`. -/
theorem xi_escape {L₀ : ℕ} {C : Set (∀ i, TheOracle I i)} (hfin : C.Finite)
    (hcard : C.ncard ≤ L₀) (s : I.Stmt × BusOut I) (hpre : RelDoom C (Seam.bus I) s) :
    (Fintype.card E : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun ξ ↦ ¬ RelDoom C
      (Sumcheck.relIn (tableSummand I) Sumcheck.unitWeights (side I))
      (start I s ξ (powerBatch (claimed I s) ξ))).card : ℝ≥0∞) ≤ xiError I L₀ :=
  draw_escape_le (xiSecurity I) hfin hcard hpre rfl

/-- The rounds' family. -/
noncomputable abbrev tableFamily : SumcheckRound.Family E (Data I) (TheOracle I) Unit 3 :=
  Sumcheck.family (tableSummand I) Sumcheck.unitWeights nodes (side I)

/-- The rounds' family is consistent (the summand has degree at most three in each variable). -/
theorem tableFamily_consistent (hd : I.d ≤ 2) : (tableFamily I).Consistent I.τmax :=
  (Sumcheck.family_honest (tableSummand I) Sumcheck.unitWeights nodes (side I)
    (tableSummand_degree I hd) nodes_injective).toConsistent

/-- The rounds' family is sound: its invariant is the side condition, which no challenge
changes. -/
theorem tableFamily_sound : (tableFamily I).Sound I.τmax :=
  fun _ _ _ _ h ↦ (Nat.card_eq_zero.mpr (Or.inl ⟨fun x ↦ h x.2⟩)).trans_le (Nat.zero_le 3)

/-- The final values' security, `tableSumcheckSecurity`'s last part. -/
def finalValuesSecurity :
    Typed.Security (Sumcheck.finalT (tableSummand I) (tableOut I))
      (SumcheckRound.rel (tableFamily I) I.τmax) (Seam.table I) (Typed.sayErrors _) :=
  Sumcheck.finalSecurityT (tableSummand I) Sumcheck.unitWeights nodes (side I) (tableOut I)
    fun s o w v h ↦ by
      cases w
      obtain ⟨hcols, hlines, haux⟩ := h
      simp only [tableOut, Vector.toList_append, List.mem_append] at hcols
      exact ⟨(finalClaims_holds_iff I ((s.1, o), ()) _ v).mp fun c hc ↦ hcols c (Or.inr hc),
        fun c hc ↦ hcols c (Or.inl hc), hlines, haux⟩

/-- **The final values keep doom**: values that pass the final check carry doom on the rounds'
last stage to doom on the table seam. -/
theorem finalValues_keep {C : Set (∀ i, TheOracle I i)}
    {s : SumcheckRound.Stmt (Data I) E I.τmax}
    (hpre : RelDoom C (SumcheckRound.rel (tableFamily I) I.τmax) s) (v : Vector E I.tableColumns)
    (hc : Sumcheck.finalCheck (tableSummand I) s v = true) :
    RelDoom C (Seam.table I) (tableOut I s v) :=
  say_keep (finalValuesSecurity I) hpre v hc

end
end LeanerVM.Protocol.EndToEnd.Front
