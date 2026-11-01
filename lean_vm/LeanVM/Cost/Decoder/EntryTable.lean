module

public import LeanVM.Cost.Decoder.Memory
public import LeanVM.Cost.Decoder.GuestTables
public import LeanVM.Guest.Fast.Decode

/-!
# The guest decoder's compiled chain: the replayed frame map, keyed by index

`Guest.Fast.frameVFastN pre states rd` (`Fast/Decode.lean`): the entry table of the replayed
states (`Located.entryTable`: from a call's key to the frame of the first state that entered its
callee, the precondition `pre` holding there), and each call's frame read through the callee's
certificate. Restated with the guest's tables (`GuestTables.lean`, literals of the program) and
staged:

* `pcTableT`: the functions entered at each pc, from `guestEntries` (computed once by the caller
  and passed: a closed constant compiled in place would be recomputed at each use);
* `entryKeyT`, `fileOne`, `fileStateT`, `entryTableT`: a state filed under the key of each
  function entered at its pc, by partial application, the argument and return counts from
  `guestArgCounts`, `guestRetCounts`;
* `frameAt table rd j args rets v`: the frame map, its last argument the value `v` (the frame map
  is the closure `frameAt table rd`), the cells from `guestLocs`.

`EntryTableEq.lean` proves them the definitions at the guest's tables.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Located
open LeanVM.Guest.Fast LeanVM.Extraction.Fast

attribute [local instance] lexOrd

@[expose] public section

/-- Function `j`'s entry filed at its entry pc's code. -/
def addEntry (m : SortedMap ℕ (List ℕ)) (j : ℕ) : SortedMap ℕ (List ℕ) :=
  addAt m (laneCode (gpow (guestEntries.getD j 0))) j

/-- **The functions entered at each pc** (`pcTable`), from the table of entries. -/
def pcTableT : SortedMap ℕ (List ℕ) := (List.range nFns).foldl addEntry .empty

/-- The key under which state `r`, at function `j`'s entry, files its frame (`entryKey`). -/
def entryKeyT (rd : Reader) (r : Registers K) (j : ℕ) : CallKey :=
  callKey j (wordsWith rd r.fp 2 (guestArgCounts.getD j 0))
    (wordsWith rd r.fp (2 + guestArgCounts.getD j 0) (guestRetCounts.getD j 0))

/-- State `r` filed under function `j`'s key, if `pre` holds (`fileState`'s step). -/
def fileOne (pre : ℕ → K → Bool) (rd : Reader) (r : Registers K) (m : SortedMap CallKey K)
    (j : ℕ) : SortedMap CallKey K :=
  if pre j r.fp then insertIfNew m (entryKeyT rd r j) r.fp else m

/-- State `r` filed under the key of each function entered at its pc (`fileState`). -/
def fileStateT (pcT : SortedMap ℕ (List ℕ)) (pre : ℕ → K → Bool) (rd : Reader)
    (m : SortedMap CallKey K) (r : Registers K) : SortedMap CallKey K :=
  (pcT.getD (laneCode r.pc) []).foldl (fileOne pre rd r) m

/-- **The entry table** of the states (`entryTable`). -/
def entryTableT (pcT : SortedMap ℕ (List ℕ)) (pre : ℕ → K → Bool) (states : List (Registers K))
    (rd : Reader) : SortedMap CallKey K :=
  states.foldl (fileStateT pcT pre rd) .empty

/-- The word of value `v` in function `j`'s frame at `fp`. -/
def frameWordAt (rd : Reader) (fp : K) (j : ℕ) (v : V) : E :=
  wordWith rd fp ((guestLocs.getD (canonIndex j) #[]).getD v.idx 0)

/-- **The frame map**, its last argument the value read: the call of function `canonIndex j`
looked up in the entry table, its frame's word of `v`; `0` if the call was not entered. -/
def frameAt (table : SortedMap CallKey K) (rd : Reader) (j : ℕ) (args rets : List E) (v : V) :
    E :=
  match table.get? (callKey (canonIndex j) args rets) with
  | some fp => frameWordAt rd fp j v
  | none => 0

set_option maxRecDepth 100000 in
cost_compile addEntryC := addEntry
set_option maxRecDepth 100000 in
cost_compile pcTableTC := pcTableT
set_option maxRecDepth 100000 in
cost_compile entryKeyTC := entryKeyT
set_option maxRecDepth 100000 in
cost_compile fileOneC := fileOne
set_option maxRecDepth 100000 in
cost_compile fileStateTC := fileStateT
set_option maxRecDepth 100000 in
cost_compile entryTableTC := entryTableT
set_option maxRecDepth 100000 in
cost_compile frameWordAtC := frameWordAt
set_option maxRecDepth 100000 in
cost_compile frameAtC := frameAt

end

end LeanVM.Cost.Decoder
