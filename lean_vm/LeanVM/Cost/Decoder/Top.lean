module

public import LeanVM.Cost.Decoder.EntryTable

/-!
# The guest decoder's compiled chain: the top

The decoder's top on the program, `κ` and the memory vector (`Ends.lean`'s input side), staged
point-free, each step a function of its own, each closure a partial application, each table built
once and passed down:

* `decTop prog κ mem`: the logarithm's tables (`discreteLogTables`), the preconditions
  (`Guest.Fast.preTable`, a literal), the generator's powers (`genPows`), the readers' tables
  (`Guest.Fast.readerTabs`), the table of entries (`pcTableT`), the address tables
  (`decoderTables`);
* `decTopTables`: the reader (`memReader memT mem`) and the replay (`replayStatesOf`);
* `decTopStates`: `main`'s valuation (`mainVal rd`) and the entry table (`entryTableT`,
  the precondition `preTestAt D T Pw rd`);
* `decTopFrames`: the witness (`decWitNStaged`, the frame map `frameAt table rd`, the cursor's
  length `cursorLength D`) and the decoding (`decoderOutput D`: the seed, the statement
  `decStmtD D`, `decodedOf`).

`TopEq.lean`: **`decTop_eq : decTop guest κ (memoryVector L) = End.decode L`**.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Located
open LeanVM.Guest.B1 LeanVM.Guest.Fast LeanVM.Extraction.Fast LeanVM.Node

attribute [local instance] lexOrd

@[expose] public section

/-- The decoding off `main`'s valuation and the entry table. -/
noncomputable def decTopFrames (D : DiscreteLogTables) (R : ReaderTabs) (rd : Reader) (σ : Val)
    (table : SortedMap CallKey K) : Decoded :=
  decoderOutput D σ rd (decWitNStaged D R σ rd (frameAt table rd) (cursorLength D))

/-- The decoding off the reader and the replayed states. -/
noncomputable def decTopStates (D : DiscreteLogTables) (T : Array (Option FnPre)) (Pw : Array E)
    (R : ReaderTabs) (pcT : SortedMap ℕ (List ℕ)) (rd : Reader) (states : List (Registers K)) :
    Decoded :=
  decTopFrames D R rd (mainVal rd) (entryTableT pcT (preTestAt D T Pw rd) states rd)

/-- The decoding off the address tables and the memory. -/
noncomputable def decTopTables (D : DiscreteLogTables) (T : Array (Option FnPre)) (Pw : Array E)
    (R : ReaderTabs) (pcT : SortedMap ℕ (List ℕ)) (tabs : Array (ℕ × ℕ) × Array (ℕ × ℕ))
    (prog : LeanVM.Semantics.Program) {κ : ℕ} (mem : Vector E (2 ^ κ)) : Decoded :=
  decTopStates D T Pw R pcT (memReader tabs.1 mem) (replayStatesOf tabs.1 tabs.2 prog mem)

/-- **The decoder's top**: the decoding of an execution of `prog`, its memory the vector `mem` of
`2^κ` words. -/
noncomputable def decTop (prog : LeanVM.Semantics.Program) (κ : ℕ) (mem : Vector E (2 ^ κ)) :
    Decoded :=
  decTopTables discreteLogTables preTable genPows readerTabs pcTableT (decoderTables prog κ) prog
    mem

/-! The baby-step tables' parts, under names of their own (the bounds name them). -/
cost_compile powPairsByC measure fun _ n _ _ ↦ n := powPairsBy
cost_compile babyTableC := babyTable
set_option maxRecDepth 100000 in
cost_compile discreteLogTablesC := discreteLogTables
set_option maxRecDepth 100000 in
cost_compile decTopFramesC := decTopFrames
set_option maxRecDepth 100000 in
cost_compile decTopStatesC := decTopStates
set_option maxRecDepth 100000 in
cost_compile decTopTablesC := decTopTables
set_option maxRecDepth 100000 in
cost_compile decTopC := decTop

end

end LeanVM.Cost.Decoder
