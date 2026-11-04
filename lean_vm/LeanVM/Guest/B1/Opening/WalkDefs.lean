/-
  LeanVM.Guest.B1.Opening.WalkDefs

  The walk obligations' definitions: the windows a query of `opening_queries` dispatches on, and
  their walk along the loop (light: the certificates' checker reads them).
-/

module

public import LeanVM.Guest.B1.Bits.QueryWindowsT

/-!
# The walk obligations, definitions (lean_ethereum.py:1295-1331, 1380-1404 at c4f4bc92)

`WinsAt`, `WinWalk`, `WinWalk2`, `OqMainWins`, over the windows' shape `qwN`, `qwWin`
(`QueryWindowsT`). Their facts are `QueriesWalk`'s.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

/-- The windows at `w` of a position of shape `(d, cd)`: window `i`, if read, is `g^e` with `e`
below `2^width`. -/
def WinsAt (rd : Reader) (d cd : ℕ) (w : E) : Prop :=
  ∀ i < qwN d cd, ∀ v, LoadHolds rd w i v → ∃ e < 2 ^ (qwWin d cd i).2, v = ofK (addressOfIndex e)

/-- **The walk of a deeper loop** from `x` to `N`: the window pointer `t[x·g^c]` of every
iteration still to run names windows. -/
def WinWalk (rd : Reader) (d cd : ℕ) (t x N : E) : Prop :=
  ∀ c : ℕ, (∀ c' ≤ c, x * gen ^ c' ≠ N) →
    ∀ w, LoadHolds rd (t * (x * gen ^ c)) 0 w → WinsAt rd d cd w

/-- **The walk of a level-0 loop** from `x` to `N`: the window pointers `(t·(x·g^c)²)[g^o]`,
`o = odd, odd + 1`, of every iteration still to run name windows. -/
def WinWalk2 (rd : Reader) (d cd odd : ℕ) (t x N : E) : Prop :=
  ∀ c : ℕ, (∀ c' ≤ c, x * gen ^ c' ≠ N) → ∀ o, odd ≤ o → o ≤ odd + 1 →
    ∀ w, LoadHolds rd (t * (x * gen ^ c) * (x * gen ^ c)) o w → WinsAt rd d cd w

/-- **`opening_queries`' obligation** on its window pointers `t` and `N = n_iters_g`: an odd
count's first query's windows, and the loop's walk from `1`. -/
def OqMainWins (rd : Reader) (d cd odd base : ℕ) (t N : E) : Prop :=
  (odd = 1 → ∀ w, LoadHolds rd t 0 w → WinsAt rd d cd w) ∧
    (if base = 1 then WinWalk2 rd d cd odd t 1 N else WinWalk rd d cd t 1 N)

end
end LeanVM.Guest.B1
