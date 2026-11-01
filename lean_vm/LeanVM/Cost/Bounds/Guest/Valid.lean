module

public import LeanVM.Guest.EndFinal
public import LeanVM.Guest.B1.Main.Facts
public import LeanVM.Cost.Decoder.Equations

/-!
# The guest decoder's counts on a valid execution

On a valid execution of the leanISA guest, the counts the compiled decoder reads off `main`'s
valuation (`mainVal rd`, `rd` the reader of the memory vector through the table of its addresses,
as the decoder's top `decTop` reads it) are the ones `main`'s range checks bound
(`B1.Main.main_facts`): at most `16` children, at most `65535` claims of each list and raw
signatures of each scheme, and at most `65535` slots of both regions together.

* `mainVal_valid`: the decoder's valuation is `main`'s at its frame (`valG t.memory 1 (certOf 1)`);
* `mainFacts_valid`: `main`'s facts (`MainFacts`) at that valuation;
* **`valid_counts`**: `ValidCounts discreteLogTables σ`, the counts read by `gLogD` in the tables
  built.
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Guest.B1 LeanVM.Guest.B1.Main LeanVM.Extraction.Fast LeanVM.Cost.Decoder

public section

/-- **The counts the decoder reads off `main`'s valuation `σ`**, in the logarithm's tables `D`,
small. -/
structure ValidCounts (D : DiscreteLogTables) (σ : Val) : Prop where
  kids : nKidsD D σ ≤ 16
  xClaims : gLogD D (σ (.n 0)) ≤ 65535
  sClaims : gLogD D (σ (.n 3)) ≤ 65535
  rawX : nRawXD D σ ≤ 65535
  rawS : nRawSD D σ ≤ 65535
  slots : lxSlotsD D σ + lsSlotsD D σ ≤ 65535

/-- The decoder's reader of a valid execution's memory is the memory's. -/
theorem memReader_valid {input : PublicInput} {t : Execution guest}
    (hv : ValidExecution guest input t) :
    memReader (powTable t.logMemorySize) (memoryVector t.memory) = t.memory.read := by
  have hκ : t.logMemorySize < 64 := by
    have := hv.1.2.1
    unfold maxLogMem at this
    omega
  rw [memReader_memoryVector, Located.readTable_powTable hκ]

/-- **The decoder's valuation is `main`'s at its frame** (`fp = 1`, `main`'s certificate). -/
theorem mainVal_valid {input : PublicInput} {t : Execution guest}
    (hv : ValidExecution guest input t) :
    mainVal (memReader (powTable t.logMemorySize) (memoryVector t.memory)) =
      valG t.memory 1 (certOf 1) := by
  rw [memReader_valid hv, mainVal_eq]
  rfl

/-- **`main`'s facts on a valid execution**, at the decoder's valuation. -/
theorem mainFacts_valid {input : PublicInput} {t : Execution guest}
    (hv : ValidExecution guest input t) :
    MainFacts (Located.RLg t.memory) t.memory.read
      (mainVal (memReader (powTable t.logMemorySize) (memoryVector t.memory))) := by
  rw [mainVal_valid hv]
  have hm : Digest.MemOk t.memory.read := ⟨t.logMemorySize, hv.1.1, hv.1.2.1, t.memory, rfl⟩
  exact main_facts (unfolds_of_V (Located.unfoldsV_replay End.b2SoundL hv))
    (Located.rlg_le_rel t.memory) hm exponent_tables_holds (End.mainBodyL_of End.b2SoundL hv).1

/-- The counts of `main`'s facts, read by `gLog`. -/
theorem validCounts_of {C : CallRel} {rd : Reader} {σ : Val} (MF : MainFacts C rd σ) :
    ValidCounts discreteLogTables σ := by
  have hc : ∀ v ∈ [0, 1, 2, 3, 4, 5], gLog (σ (.n v)) ≤ 65535 := fun v hv ↦ by
    rw [← lg_eq_gLog]; exact (MF.counts v hv).2
  have h0 := hc 0 (by simp)
  have h1 := hc 1 (by simp)
  have h3 := hc 3 (by simp)
  have h4 := hc 4 (by simp)
  have hk : gLog (σ (.n 6)) ≤ 16 := by rw [← lg_eq_gLog]; exact MF.kids.2
  have hx : gLog (σ (.n 40)) = lg σ 0 + lg σ 1 := by
    rw [MF.lxs, gLog_gen_pow (by rw [lg_eq_gLog, lg_eq_gLog]; omega)]
  have hs : gLog (σ (.n 41)) = lg σ 3 + lg σ 4 := by
    rw [MF.lss, gLog_gen_pow (by rw [lg_eq_gLog, lg_eq_gLog]; omega)]
  have ht := MF.total.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold nKidsD; rw [gLogD_tables]; exact hk
  · rw [gLogD_tables]; exact h0
  · rw [gLogD_tables]; exact h3
  · unfold nRawXD; rw [gLogD_tables]; exact hc 2 (by simp)
  · unfold nRawSD; rw [gLogD_tables]; exact hc 5 (by simp)
  · unfold lxSlotsD lsSlotsD; rw [gLogD_tables, hx, hs]; omega

/-- **On a valid execution of the guest, the counts the decoder reads are small**: at its
valuation `mainVal rd` of `main`'s frame, `rd` the reader of the memory vector (`decTop`'s), in
the logarithm's tables built. -/
theorem valid_counts {input : PublicInput} {t : Execution guest}
    (hv : ValidExecution guest input t) :
    ValidCounts discreteLogTables
      (mainVal (memReader (powTable t.logMemorySize) (memoryVector t.memory))) :=
  validCounts_of (mainFacts_valid hv)

end

end LeanVM.Cost.Bounds.Guest
