/-
  LeanVM.Guest.B1.Place.OsCallees

  The placed completeness `open_stacked` assumes of `decode_query_windows`.
  After mumbai's `B1/Whir/OsCallees.lean`.
-/

module

public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.B1.Opening.Meaning
public import LeanVM.Guest.B1.Merkle.Meaning
public import LeanVM.Guest.B1.Eq.Meaning
public import LeanVM.Guest.B1.Bits.Meaning
public import LeanVM.Guest.B1.Bits.QueryWindows
public import LeanVM.Guest.Lift.OsCallees

/-!
# `decode_query_windows`, placed

`qwRunL`: the frame run `wins` of `decode_query_windows__L{d}_L{cd}` (its cells `.n 5 .. .n 60`,
`qwRun`) holding the windows of the word `w`'s positions: position `j`'s `qwN d cd` windows
`g^qwVal d cd (qwPosOf d w j) i` from cell `j·qwN d cd` on. `OsDecodeAtD`: the callee, which stores
the positions and pointers into its own run in the caller's buffers and reads the window table
`tabs`, placed: at every frame pointer `fp`, on every memory where the caller's words (`Lin`,
holding the positions', pointers' and table's words, `RegPtrs`) hold the window table, the decoded
positions and the run's pointers, a tree of `fs name` words whose data holds the run.
Integration proves it (`Lift/Decode.lean`); `open_stacked`'s other callees are `OsCalleesRegD`
(`Lift/OsCallees.lean`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-- The windows of the positions of depth `d`, cap depth `cd`, of the word `w`, position after
position: `g^qwVal d cd (qwPosOf d w j) i`, `j < 192 / d`, `i < qwN d cd`. -/
def qwWinsOf (d cd : ℕ) (w : E) : List E :=
  ((List.range (192 / d)).map fun j ↦
    (List.range (qwN d cd)).map fun i ↦ gen ^ qwVal d cd (qwPosOf d w j) i).flatten

/-- `decode_query_windows`' frame run `wins` at `fp`: the windows of the word `w`'s positions at
the certificate's cell of the run's first value `.n 5` (`qwRun`). -/
def qwRunL (cert : String → V → ℕ) (name : String) (fp d cd : ℕ) (w : E) : Layout :=
  [(fp + cert name (.n 5), qwWinsOf d cd w)]

/-- **`decode_query_windows__L{d}_L{cd}`, placed, on disjoint layouts**: at every frame pointer
`fp`, on every memory where the caller's words `Lin` hold the window table at `tabs`, the decoded
positions at `pos` and the run's pointers `g^(fp + cert name (.n 5))·g^(j·qwN d cd)` at `ptrs`, a
tree of `fs name` words holds, its data holding the run `qwRunL`, its other words `Lown`, its
loads in its data or `Lin`. -/
def OsDecodeAtD (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (d cd : ℕ) (name : String) :
    Prop :=
  ∀ (w pos ptrs tabs : E) (Lin : Layout) (fp : ℕ),
    RegPtrs [(1, 192 / d), (2, 192 / d), (3, 128)] [w, pos, ptrs, tabs] (RegionL Lin) →
    (∀ rd, LowDef k rd → MemL rd Lin → WinTabs rd tabs ∧ ∀ j < 192 / d,
      LoadHolds rd pos j (eOfNat (qwPosOf d w j)) ∧
        LoadHolds rd ptrs j (ofK (addressOfIndex (fp + cert name (.n 5))) * gen ^ (j * qwN d cd))) →
    ∃ Lown : Layout, Within (qwRunL cert name fp d cd w ++ Lown) fp (fs name) ∧
      DisjL (qwRunL cert name fp d cd w ++ Lown) ∧
      ∀ rd, LowDef k rd → MemL rd (qwRunL cert name fp d cd w ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL (qwRunL cert name fp d cd w)) fp
          (fs name) name [w, pos, ptrs, tabs] []

end
end LeanVM.Guest.B1
