/-
  LeanVM.Guest.B1.Opening.WalkDefs

  The walk obligations' definitions: the windows a query of `opening_queries` dispatches on, and
  their walk along the loop.
-/

module

public import LeanVM.Guest.B1.Bits.QueryWindowsT
public import LeanVM.Guest.WalkWindows

/-!
# The walk obligations, definitions (lean_ethereum.py:1312-1348, 1397-1421 at 9d8bce81)

`WinsAt`, `WinWalk`, `WinWalk2`, `OqMainWins`, over the windows' shape `qwN`, `qwWin`, are
defined in `Guest/WalkWindows.lean`, apart from B1, since the certificates' checker (`Glob`) and
the decoder's table checks read them; this module re-exports them with `QueryWindowsT`. Their
facts are `QueriesWalk`'s.
-/
