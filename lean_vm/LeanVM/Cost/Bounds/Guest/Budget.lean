module

public import LeanVM.Cost.Bounds.Guest.DecTop
public import LeanVM.Cost.Bounds.Decoder.EntryTable
public import LeanVM.Cost.Bounds.Decoder.PcTable
public import LeanVM.Cost.Bounds.Decoder.PreTable
public import LeanVM.Cost.Bounds.Decoder.PreTableShape
public import LeanVM.Cost.Bounds.Decoder.Cursor
public import LeanVM.Cost.Bounds.Decoder.ReplayLength
public import LeanVM.Cost.DecoderSpec

/-!
# Bounds on the guest decoder's prices: within the budget

**`decoderPriceWithinBudget : DecoderPriceWithinBudget`**: on every valid execution of the guest,
the decoder program's price is within `guestDecoderBudget` (`Statement/Theorems.lean`'s
`guestDecoderPrice`). The composition (`decTop_cost`, `Bounds/Guest/DecTop.lean`) at:

* the reader at `1472` (`readerClosure_cost`), the replay of at most `steps + 1` states
  (`replayStatesOf_length`);
* the entry table (`entryTableT_cost`) at the key exponent `guestDecoderTableExponent steps`, the
  precondition test (`preTestAt_cost_deployed`, its logarithms by `powBelow_cost` at
  `discreteLogWith_cost`), the pc table (`pcTableT_get_cost`, `pcTableT_getD_length`): per state
  `guestDecoderStateFilingPrice`;
* the frame map (`frameAt_cost`, calls of at most `16` words): `guestDecoderFramePrice`; the cursor's
  length (`cursorLength_cost`, value at most `2^32`), the witness (`frameWit_cost`);
* the tables: preconditions `12895` (`preTable_cost`), entries `17047343` (`pcTableT_cost`); the
  constant `topConstPrice` at most `guestDecoderWorstConstant + guestDecoderFrameFactor·F`
  (`topConst_le`).
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters LeanVM.Semantics
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Fast LeanVM.Extraction.Fast LeanVM.Guest.Located
open LeanVM.Node

public section

attribute [local instance] lexOrd

/-- The constant's linear form in the frame map's price. -/
theorem topConst_le (F : ℕ) :
    topConstPrice (decWitNPrice gLogPrice 1472 (1472 + 10993) (F + 7) (425014 + 4) (2 ^ 32)
      (dvFramePrice gLogPrice (F + 7))) ≤ guestDecoderWorstConstant + guestDecoderFrameFactor * F := by
  unfold topConstPrice framesPrice decStmtPrice decStmtAtPrice decWitNPrice decWitPrice
    decWitAtPrice decWitTabPrice kidsTPrice decKidPrice kidStmtPrice kidStmtAtPrice
    xmssHoldersTPrice sphincsHoldersTPrice regionTablePrice kidMaxPrice vsPiPrice vsMPrice
    vsAtPrice levelPrice levelAtPrice oqsPrice stepPrice iterPrice queryPrice posPrice
    queryAtPrice openingPrice dvFramePrice dvWitNAtPrice dvWitNRowsPrice gLogPrice
    guestDecoderWorstConstant guestDecoderFrameFactor
  omega

/-- The filing's price is the statement's. -/
theorem fileStatePrice_eq (e : ℕ) :
    fileStatePrice 8339 2 guestDecoderPreconditionPrice 1472 e + 15 =
      guestDecoderStateFilingPrice e := by
  unfold fileStatePrice fileOnePrice insertKeyPrice getKeyPrice wl limbsBelowTwoPow
    guestDecoderStateFilingPrice guestDecoderTableInsertPrice guestDecoderTableLookupPrice
    guestDecoderTableLimbs
  ring

/-- A frame lookup of at most `16` words, at most the statement's. -/
theorem frameAtPrice_le (e n : ℕ) (hn : n ≤ 16) :
    e * (17 + (67 * n + 89 + 9 * wl e) * (e + 2)) + 28 * n + 1472 + 11070 ≤
      guestDecoderFramePrice e := by
  unfold guestDecoderFramePrice guestDecoderTableLimbs wl limbsBelowTwoPow
  have h1 : 67 * n + 89 + 9 * ((e + 1) / 64 + 1) ≤ 67 * 16 + 89 + 9 * ((e + 1) / 64 + 1) := by omega
  have h2 := Nat.mul_le_mul_right (e + 2) h1
  have h3 := Nat.mul_le_mul_left e (Nat.add_le_add_left h2 17)
  omega

theorem tableExponent_spec (steps : ℕ) : 2 * (steps + 1) < 2 ^ guestDecoderTableExponent steps := by
  unfold guestDecoderTableExponent
  exact Nat.lt_log2_self

variable (P : MachineProgram)

set_option maxHeartbeats 2000000 in
/-- **On every valid execution of the guest, the decoder program's price is within its
budget.** -/
theorem decoderPriceWithinBudget : DecoderPriceWithinBudget := by
  unfold DecoderPriceWithinBudget decoderProgramPrice guestDecoderBudget guestDecoderPrice
  intro input t hv
  have hP := decoderProgram_includes
  have hκ : t.logMemorySize ≤ 32 := hv.1.2.1
  have hlen := replayStatesOf_length hv
  set states := Decoder.replayStatesOf (powTable t.logMemorySize) (powTable LeanVM.Guest.guest.logSize)
    LeanVM.Guest.guest (Decoder.memoryVector t.memory) with hstates
  set e := guestDecoderTableExponent t.steps
  have hn : 2 * states.length < 2 ^ e :=
    lt_of_le_of_lt (by omega) (tableExponent_spec t.steps)
  have hrd := readerClosure_runs decoderProgram (by includes) (Decoder.memoryVector t.memory)
  have hR := readerClosure_cost decoderProgram (by includes) hκ (Decoder.memoryVector t.memory)
  have hLg : ∀ x : K, machineCost decoderProgram Decoder.discreteLogWithC.costIdx
      [encodeValue discreteLogTables, encodeValue x] ≤ 402662 :=
    fun x ↦ discreteLogWith_cost decoderProgram (by includes) x
  have hB := powBelow_cost decoderProgram (by includes) discreteLogTables 402662 hLg
    discreteLogWith_lt
  have hpre : ∀ (j : ℕ) (fp : K), RunsApp decoderProgram
      (.closure Decoder.decTopStatesC.lam1.costIdx [encodeValue discreteLogTables,
        encodeValue preTable, encodeValue genPows, readerV t.logMemorySize (Decoder.memoryVector t.memory)]) [encodeValue j, encodeValue fp]
      (encodeValue (preTestAt discreteLogTables preTable genPows
        (Decoder.memReader (powTable t.logMemorySize) (Decoder.memoryVector t.memory)) j fp)) := fun j fp ↦
    RunsApp.of_spec (Decoder.decTopStatesC.lam1.costSpec decoderProgram (by includes)
      discreteLogTables preTable genPows _ _ hrd j fp)
  have hPr : ∀ (j : ℕ) (fp : K), j < 2 ^ 64 → appCost decoderProgram
      (.closure Decoder.decTopStatesC.lam1.costIdx [encodeValue discreteLogTables,
        encodeValue preTable, encodeValue genPows, readerV t.logMemorySize (Decoder.memoryVector t.memory)]) [encodeValue j, encodeValue fp] ≤
      guestDecoderPreconditionPrice := fun j fp hj ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
      List.nil_append, Decoder.decTopStatesC.lam1.costEq decoderProgram (by includes) _ _ _ _ _ hrd]
    have := preTestAt_cost_deployed decoderProgram (by includes) discreteLogTables _ _ hrd 1472 hR
      (402662 + 22) hB preTable preTable_shape genPows j hj fp
    unfold guestDecoderPreconditionPrice
    omega
  obtain ⟨hgood, hE⟩ := entryTableT_cost decoderProgram _ _ hrd 1472 hR _ _ hpre _ hPr e
    (by includes) Decoder.pcTableT 2 8339 pcTableT_getD_lt pcTableT_getD_length
    (fun k hk ↦ pcTableT_get_cost decoderProgram (by includes) k hk) states hn
  have hF : ∀ (k : ℕ) (a r : List E) (v : V), k < 2 ^ 64 → a.length + r.length ≤ 16 →
      machineCost decoderProgram Decoder.frameAtC.costIdx
        [encodeValue (Decoder.entryTableT Decoder.pcTableT
          (preTestAt discreteLogTables preTable genPows (Decoder.memReader (powTable t.logMemorySize) (Decoder.memoryVector t.memory)))
          states (Decoder.memReader (powTable t.logMemorySize) (Decoder.memoryVector t.memory))), readerV t.logMemorySize (Decoder.memoryVector t.memory), encodeValue k,
          encodeValue a, encodeValue r, encodeValue v] ≤ guestDecoderFramePrice e :=
    fun k a r v hk hl ↦ (frameAt_cost decoderProgram _ _ hrd 1472 hR (by includes) e _ hgood k hk
      a r v).trans (frameAtPrice_le e _ hl)
  have hσ : ∀ v : V, RunsApp decoderProgram
      (.closure Decoder.decTopStatesC.lam0.costIdx [readerV t.logMemorySize (Decoder.memoryVector t.memory)]) [encodeValue v]
      (encodeValue (Decoder.mainVal (Decoder.memReader (powTable t.logMemorySize) (Decoder.memoryVector t.memory)) v)) := fun v ↦
    RunsApp.of_spec (Decoder.decTopStatesC.lam0.costSpec decoderProgram (by includes) _ _ hrd v)
  have hS : ∀ v : V, appCost decoderProgram
      (.closure Decoder.decTopStatesC.lam0.costIdx [readerV t.logMemorySize (Decoder.memoryVector t.memory)]) [encodeValue v] ≤
        1472 + 10993 := fun v ↦ by
    rw [appCost_fn, List.cons_append, List.nil_append,
      Decoder.decTopStatesC.lam0.costEq decoderProgram (by includes) _ _ hrd]
    have := mainVal_cost decoderProgram (by includes) hrd hR v; omega
  have hW := frameWit_cost decoderProgram discreteLogTables (by includes) (by includes)
    (by includes) (gLog_bound decoderProgram (by includes)) readerTabs readerTabs_ok hrd hR hσ hS
    _ (guestDecoderFramePrice e) hF 425014
    (fun p q ↦ cursorLength_cost decoderProgram (by includes) discreteLogTables 402662 hLg
      discreteLogWith_lt p q)
    (fun p q ↦ cursorLenWith_le _ p q)
  have hT := decTop_cost decoderProgram hP LeanVM.Guest.guest hκ (Decoder.memoryVector t.memory) 12895 17047343 _ _
    (preTable_cost decoderProgram (by includes)).le (pcTableT_cost decoderProgram (by includes))
    hE hW
  have hc := topConst_le (guestDecoderFramePrice e)
  have hfs := fileStatePrice_eq e
  rw [← hstates] at hT
  have h1 := Nat.mul_le_mul_left (runnerStepPrice t.logMemorySize LeanVM.Guest.guest.logSize + 48) hlen
  have h2 := Nat.mul_le_mul_left
    (fileStatePrice 8339 2 guestDecoderPreconditionPrice 1472 e + 15) hlen
  rw [Nat.add_mul, ← hfs]
  omega

end

end LeanVM.Cost.Bounds.Guest
