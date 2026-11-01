module

public import LeanVM.Guest.Fast.WhirTables
public import LeanVM.Guest.B1.Whir.InterfaceW

/-!
# `open_stacked`'s tables, checked

* `vsName k`: the frames `verify_sub`'s child proof reads, numbered: `open_stacked`'s 28
  specializations (`k < 28`), the 56 `opening_queries` specializations (`28 + j`) and their loop
  helpers (`84 + j`), in the order of `openingQueriesLoops`;
* `recOf c`: an `opening_queries` call of the template (`osQCalls`) in numbers; `callOK c`: its
  arguments and returns are cells, its callee is frame `28 + j` and its loop `84 + j`;
* `osWordsTab_eq`, `osCallsTab_eq`, `osCalls_ok`: the literal tables of `Fast/WhirTables.lean`
  are the template's, by kernel evaluation.
-/

namespace LeanVM.Guest.Fast

open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Whir

@[expose] public section

/-- The frames the child proof reader reads, numbered. -/
def vsName (k : ℕ) : String :=
  if k < 28 then openNames.getD k ""
  else if k < 84 then (openingQueriesLoops.map (·.1)).getD (k - 28) ""
  else (openingQueriesLoops.map (·.2.1)).getD (k - 84) ""

/-- A cell's number. -/
def vIdx (v : V) : ℕ := v.idx

/-- Whether a value is the cell of its number. -/
def isN (v : V) : Bool := v == .n v.idx

/-- The index of an `opening_queries` specialization in `openingQueriesLoops`. -/
def oqIdx (name : String) : ℕ := (openingQueriesLoops.map (·.1)).idxOf name

/-- An `opening_queries` call of the template, in numbers. -/
def recOf : ℕ × OsLv × String × List V × List V → OsCall
  | (lvl, lv, name, args, rets) =>
    ⟨(lvOq lvl lv).base, (lvOq lvl lv).I, (lvOq lvl lv).pd, (lvOq lvl lv).cd,
      lv.queries % 2 * (if lvl = 0 then 1 else 0), lv.queries / (1 + if lvl = 0 then 1 else 0),
      28 + oqIdx name, 84 + oqIdx name, lv.depth, args.map vIdx, rets.map vIdx⟩

/-- The call's arguments and returns are cells, its callee and its loop the frames `recOf`
numbers. -/
def callOK : ℕ × OsLv × String × List V × List V → Bool
  | (_, _, name, args, rets) =>
    args.all isN && rets.all isN && vsName (28 + oqIdx name) == name &&
      vsName (84 + oqIdx name) == oqLoopOf name

/-- Candidate `m`'s `opening_queries` calls. -/
def osCallsOf (m : ℕ) : List (ℕ × OsLv × String × List V × List V) :=
  osQCalls (osCfg m) 0 (osCfg m).levels (osHead (osCfg m)).2

theorem osWordsTab_eq : osWordsTab = (List.range 28).map fun m ↦ osWordsLen (osCfg m) := by
  decide +kernel

theorem osCallsTab_eq : osCallsTab = (List.range 28).map fun m ↦ (osCallsOf m).map recOf := by
  decide +kernel

theorem osCalls_ok : ((List.range 28).all fun m ↦ (osCallsOf m).all callOK) = true := by
  decide +kernel

end
end LeanVM.Guest.Fast
