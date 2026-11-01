module

public import LeanVM.Cost.Bounds.Guest.DecTop
public import LeanVM.Cost.Bounds.Decoder.EntryArray
public import LeanVM.Cost.Bounds.Decoder.PcTable
public import LeanVM.Cost.Bounds.Decoder.PreTable
public import LeanVM.Cost.Bounds.Decoder.PreTableShape
public import LeanVM.Cost.Bounds.Decoder.Cursor
public import LeanVM.Cost.Bounds.Decoder.ReplayLength
public import LeanVM.Cost.DecoderSpec
public import LeanVM.Cost.Bounds.Guest.BudgetIncludes
public import LeanVM.Cost.Bounds.Guest.Valid

/-!
# Bounds on the guest decoder's prices: within the budget

**`decoderPriceWithinBudget : DecoderPriceWithinBudget`**: on every valid execution of the guest,
the decoder program's price is within `guestDecoderBudget` (`Statement/Theorems.lean`'s
`guestDecoderPrice`). The composition (`decTop_cost`, `Bounds/Guest/DecTop.lean`) at:

* the reader at `1472` (`readerClosure_cost`), the replay of at most `steps + 1` states
  (`replayStatesOf_length`);
* the counts `main`'s range checks bound (`valid_counts`, `Bounds/Guest/Valid.lean`): at most
  `16` children, `65535` slots a region, `65535` declared claims a scheme (`CountsWithin`), and
  `da_verify`'s rows at most `1024` (`dvWitN_cost_1024`, on every input);
* the entry table, one sorted array (`entryArrayT_cost`) at the key exponent
  `guestDecoderEntryTableKeyExponent steps`, the precondition test (`preTestAt_cost_deployed`, its
  logarithms by `powBelow_cost` at `discreteLogWith_cost`), the pc table (`pcTableT_get_cost`,
  `pcTableT_getD_length`): per state within `guestDecoderStateFilingPrice`
  (`entryArrayStatePrice_le`);
* the frame map (`frameAtA_cost`, one binary search, calls of at most `16` words): within
  `guestDecoderFramePrice` (`frameAtAPrice_le`); the cursor's length (`cursorLength_cost`, value
  at most `2^32`), the witness (`frameWit_cost`);
* the tables: preconditions `12895` (`preTable_cost`), entries `17047343` (`pcTableT_cost`); the
  constant `topConstPrice` at most `144294535527556 + 99702868·F` (`2^47.04 + 2^26.57·F`,
  `topConst_valid_le`), the statement's `guestDecoderWorstMemoryWitnessPrice +
  guestDecoderWorstFrameLookupCount·F` (`topConst_le`).
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters LeanVM.Semantics
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Fast LeanVM.Extraction.Fast LeanVM.Guest.Located
open LeanVM.Node

public section

attribute [local instance] lexOrd

/-- The constant's linear form in the frame map's price, at a valid run's counts (`16` children,
`65535` slots a region, `65535` declared claims a scheme): `144294535527556 + 99702868·F`. -/
theorem topConst_valid_le (F : ℕ) :
    topConstPrice 65535 (decWitNPrice gLogPrice 1472 (1472 + 10993) (F + 7) (425014 + 4)
      (2 ^ 32) (dvFramePrice gLogPrice (F + 7)) 16 65535 65535) ≤
      144294535527556 + 99702868 * F := by
  unfold topConstPrice framesPrice decStmtPrice decStmtAtPrice decWitNPrice decWitPrice
    decWitAtPrice decWitTabPrice kidsTPrice decKidPrice kidStmtPrice kidStmtAtPrice
    xmssHoldersTPrice sphincsHoldersTPrice regionTablePrice kidMaxPrice vsPiPrice vsMPrice
    vsAtPrice levelPrice levelAtPrice oqsPrice stepPrice iterPrice queryPrice posPrice
    queryAtPrice openingPrice dvFramePrice dvWitNRowsPrice gLogPrice
  omega

/-- The constant is the statement's linear form. -/
theorem topConst_le (F : ℕ) :
    topConstPrice 65535 (decWitNPrice gLogPrice 1472 (1472 + 10993) (F + 7) (425014 + 4)
      (2 ^ 32) (dvFramePrice gLogPrice (F + 7)) 16 65535 65535) ≤
      guestDecoderWorstMemoryWitnessPrice + guestDecoderWorstFrameLookupCount * F := by
  unfold guestDecoderWorstMemoryWitnessPrice guestDecoderWorstFrameLookupCount
  exact topConst_valid_le F

/-- The sorted entry array's price per state, within the statement's filing price. -/
theorem entryArrayStatePrice_le (e : ℕ) (he : 1 ≤ e) :
    entryArrayStatePrice 8339 2 guestDecoderPreconditionPrice 1472 e + 9 ≤
      guestDecoderStateFilingPrice e := by
  unfold entryArrayStatePrice pairsStatePrice guestDecoderStateFilingPrice
    guestDecoderEntryTableInsertPrice guestDecoderEntryTableLookupPrice
    guestDecoderEntryTablePositionLimbs limbsBelowTwoPow
  have hw : wl e = (e + 1) / 64 + 1 := rfl
  rw [hw]
  generalize guestDecoderPreconditionPrice = Pr
  generalize (e + 1) / 64 + 1 = w
  have hX : (134 * 22 + 89 + 9 * w) * (e + 2) = 3037 * e + 6074 + 9 * (w * e) + 18 * w := by ring
  have hY : 17 + (134 * 22 + 89 + 9 * w) * (e + 2) ≤
      e * (17 + (134 * 22 + 89 + 9 * w) * (e + 2)) := Nat.le_mul_of_pos_left _ he
  have hZ : (2 * w + 40) * (e + 1) = 2 * (w * e) + 2 * w + 40 * e + 40 := by ring
  have hV : (3060 + 5 * w) * e = 3060 * e + 5 * (w * e) := by ring
  omega

/-- A frame lookup of at most `16` words on the sorted array, within the statement's. -/
theorem frameAtAPrice_le (e n : ℕ) (hn : n ≤ 16) (he : 1 ≤ e) :
    (67 * n + 89 + 9 * wl e) * (e + 2) + 28 * n + 1472 + 11056 ≤ guestDecoderFramePrice e := by
  unfold guestDecoderFramePrice guestDecoderEntryTablePositionLimbs limbsBelowTwoPow
  have hw : wl e = (e + 1) / 64 + 1 := rfl
  rw [hw]
  generalize (e + 1) / 64 + 1 = w
  have h1 : (67 * n + 89 + 9 * w) * (e + 2) ≤ (67 * 16 + 89 + 9 * w) * (e + 2) :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : (67 * 16 + 89 + 9 * w) * (e + 2) ≤ e * (17 + (67 * 16 + 89 + 9 * w) * (e + 2)) :=
    le_trans (Nat.le_add_left _ 17) (Nat.le_mul_of_pos_left _ he)
  omega

/-- The replay lists the initial state at least. -/
theorem replayStatesOf_length_pos (memT codeT : Array (ℕ × ℕ)) (prog : LeanVM.Semantics.Program)
    {κ : ℕ} (mem : Vector E (2 ^ κ)) : 1 ≤ (Decoder.replayStatesOf memT codeT prog mem).length := by
  unfold Decoder.replayStatesOf replayFuel
  rw [show (2 : ℕ) ^ 128 = (2 ^ 128 - 1) + 1 by norm_num, Decoder.statesVec]
  simp

theorem keyExponent_pos (steps : ℕ) : 1 ≤ guestDecoderEntryTableKeyExponent steps := by
  unfold guestDecoderEntryTableKeyExponent; omega

theorem tableExponent_spec (steps : ℕ) : 2 * (steps + 1) < 2 ^ guestDecoderEntryTableKeyExponent steps := by
  unfold guestDecoderEntryTableKeyExponent
  exact Nat.lt_log2_self

variable (P : MachineProgram)

/-- **On every valid execution of the guest, the decoder program's price is within its
budget.** -/
theorem decoderPriceWithinBudget : DecoderPriceWithinBudget := by
  unfold DecoderPriceWithinBudget decoderProgramPrice guestDecoderBudget guestDecoderPrice
  intro input t hv
  have hP := decoderProgram_includes
  have hκ : t.logMemorySize ≤ 32 := hv.1.2.1
  have hlen := replayStatesOf_length hv
  have hcv := valid_counts hv
  have hc : CountsWithin discreteLogTables (Decoder.mainVal
      (Decoder.memReader (powTable t.logMemorySize) (Decoder.memoryVector t.memory)))
      16 65535 65535 :=
    ⟨by norm_num, by norm_num, by norm_num, hcv.kids, by have := hcv.slots; omega,
      by have := hcv.slots; omega, hcv.xClaims, hcv.sClaims⟩
  set states := Decoder.replayStatesOf (powTable t.logMemorySize) (powTable LeanVM.Guest.guest.logSize)
    LeanVM.Guest.guest (Decoder.memoryVector t.memory) with hstates
  set e := guestDecoderEntryTableKeyExponent t.steps
  have hn : 2 * states.length < 2 ^ e :=
    lt_of_le_of_lt (by omega) (tableExponent_spec t.steps)
  have hrd := readerClosure_runs decoderProgram includes_budget_readerClosure (Decoder.memoryVector t.memory)
  have hR := readerClosure_cost decoderProgram includes_budget_readerClosure hκ (Decoder.memoryVector t.memory)
  have hLg : ∀ x : K, machineCost decoderProgram Decoder.discreteLogWithC.costIdx
      [encodeValue discreteLogTables, encodeValue x] ≤ 402662 :=
    fun x ↦ discreteLogWith_cost decoderProgram includes_budget_discreteLogWith x
  have hB := powBelow_cost decoderProgram includes_budget_powBelow discreteLogTables 402662 hLg
    discreteLogWith_lt
  have hpre : ∀ (j : ℕ) (fp : K), RunsApp decoderProgram
      (.closure Decoder.decTopStatesC.lam1.costIdx [encodeValue discreteLogTables,
        encodeValue preTable, encodeValue genPows, readerV t.logMemorySize (Decoder.memoryVector t.memory)]) [encodeValue j, encodeValue fp]
      (encodeValue (preTestAt discreteLogTables preTable genPows
        (Decoder.memReader (powTable t.logMemorySize) (Decoder.memoryVector t.memory)) j fp)) := fun j fp ↦
    RunsApp.of_spec (Decoder.decTopStatesC.lam1.costSpec decoderProgram includes_budget_preTestLam
      discreteLogTables preTable genPows _ _ hrd j fp)
  have hPr : ∀ (j : ℕ) (fp : K), j < 2 ^ 64 → appCost decoderProgram
      (.closure Decoder.decTopStatesC.lam1.costIdx [encodeValue discreteLogTables,
        encodeValue preTable, encodeValue genPows, readerV t.logMemorySize (Decoder.memoryVector t.memory)]) [encodeValue j, encodeValue fp] ≤
      guestDecoderPreconditionPrice := fun j fp hj ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
      List.nil_append, Decoder.decTopStatesC.lam1.costEq decoderProgram includes_budget_preTestLam _ _ _ _ _ hrd]
    have := preTestAt_cost_deployed decoderProgram includes_budget_preTestAt discreteLogTables _ _ hrd 1472 hR
      (402662 + 22) hB preTable preTable_shape genPows j hj fp
    unfold guestDecoderPreconditionPrice
    omega
  have he1 := keyExponent_pos t.steps
  have hpos := replayStatesOf_length_pos (powTable t.logMemorySize)
    (powTable LeanVM.Guest.guest.logSize) LeanVM.Guest.guest (Decoder.memoryVector t.memory)
  rw [← hstates] at hpos
  have hE := entryArrayT_cost decoderProgram _ _ hrd 1472 hR _ _ hpre _ hPr
    includes_budget_entryArrayT Decoder.pcTableT 2 8339 e pcTableT_getD_lt pcTableT_getD_length
    (fun k hk ↦ pcTableT_get_cost decoderProgram includes_budget_getPc k hk) states hn
  obtain ⟨hok, hsz⟩ := entryArrayT_ok (Decoder.memReader (powTable t.logMemorySize)
    (Decoder.memoryVector t.memory)) (preTestAt discreteLogTables preTable genPows
    (Decoder.memReader (powTable t.logMemorySize) (Decoder.memoryVector t.memory)))
    Decoder.pcTableT 2 pcTableT_getD_lt pcTableT_getD_length states
  have hF : ∀ (k : ℕ) (a r : List E) (v : V), k < 2 ^ 64 → a.length + r.length ≤ 16 →
      machineCost decoderProgram Decoder.frameAtAC.costIdx
        [encodeValue (Decoder.entryArrayT Decoder.pcTableT
          (preTestAt discreteLogTables preTable genPows (Decoder.memReader (powTable t.logMemorySize) (Decoder.memoryVector t.memory)))
          states (Decoder.memReader (powTable t.logMemorySize) (Decoder.memoryVector t.memory))), readerV t.logMemorySize (Decoder.memoryVector t.memory), encodeValue k,
          encodeValue a, encodeValue r, encodeValue v] ≤ guestDecoderFramePrice e :=
    fun k a r v hk hl ↦ (frameAtA_cost decoderProgram _ _ hrd 1472 hR includes_budget_frameAtA e _
      hok (by omega) k hk a r v).trans (frameAtAPrice_le e _ hl he1)
  have hσ : ∀ v : V, RunsApp decoderProgram
      (.closure Decoder.decTopStatesC.lam0.costIdx [readerV t.logMemorySize (Decoder.memoryVector t.memory)]) [encodeValue v]
      (encodeValue (Decoder.mainVal (Decoder.memReader (powTable t.logMemorySize) (Decoder.memoryVector t.memory)) v)) := fun v ↦
    RunsApp.of_spec (Decoder.decTopStatesC.lam0.costSpec decoderProgram includes_budget_mainValLam _ _ hrd v)
  have hS : ∀ v : V, appCost decoderProgram
      (.closure Decoder.decTopStatesC.lam0.costIdx [readerV t.logMemorySize (Decoder.memoryVector t.memory)]) [encodeValue v] ≤
        1472 + 10993 := fun v ↦ by
    rw [appCost_fn, List.cons_append, List.nil_append,
      Decoder.decTopStatesC.lam0.costEq decoderProgram includes_budget_mainValLam _ _ hrd]
    have := mainVal_cost decoderProgram includes_budget_mainVal hrd hR v; omega
  have hW := frameWit_cost decoderProgram discreteLogTables includes_budget_decWitN includes_budget_frameLam
    includes_budget_cursorLam (gLog_bound decoderProgram includes_budget_gLogD) readerTabs readerTabs_ok hrd hR hσ hS
    _ (guestDecoderFramePrice e) hF 425014
    (fun p q ↦ cursorLength_cost decoderProgram includes_budget_cursorLength discreteLogTables 402662 hLg
      discreteLogWith_lt p q)
    (fun p q ↦ cursorLenWith_le _ p q) hc
  have hT := decTop_cost decoderProgram hP LeanVM.Guest.guest hκ (Decoder.memoryVector t.memory) 12895 17047343 _ _
    (preTable_cost decoderProgram includes_budget_preTable).le (pcTableT_cost decoderProgram includes_budget_pcTableT)
    hE hW hc
  have hk := topConst_le (guestDecoderFramePrice e)
  have hfs := entryArrayStatePrice_le e he1
  rw [← hstates] at hT
  have h1 := Nat.mul_le_mul_left (runnerStepPrice t.logMemorySize LeanVM.Guest.guest.logSize + 48) hlen
  have h2 := Nat.mul_le_mul_left (guestDecoderStateFilingPrice e) hlen
  have h3 : entryArrayStatePrice 8339 2 guestDecoderPreconditionPrice 1472 e * states.length + 24 ≤
      guestDecoderStateFilingPrice e * states.length + 15 := by
    have := Nat.mul_le_mul_right states.length hfs
    nlinarith
  rw [Nat.add_mul]
  omega

end

end LeanVM.Cost.Bounds.Guest
