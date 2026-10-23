/-
  LeanVM.Guest.B1.Place.OsCallees

  The placed completeness `open_stacked` assumes of its callees, keccak's names and meanings.
  After mumbai's `B1/Whir/OsCallees.lean`.
-/

module

public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.B1.Opening.Meaning
public import LeanVM.Guest.B1.Merkle.Meaning
public import LeanVM.Guest.B1.Eq.Meaning
public import LeanVM.Guest.B1.Bits.Meaning
public import LeanVM.Guest.Lift.OsCallees

/-!
# `decode_query_bits`, placed

`dqRunL`: the frame run of the 192 bits of the word `w` at the certificate's cell. `OsDecodeAtD`:
`decode_query_bits__L{d}`, which stores pointers into its own frame run in the caller's buffer,
placed: at every frame pointer `fp`, on every memory where the caller's words (`Lin`, holding the
positions' and pointers' words, `RegPtrs`) hold the decoded positions and the run's pointers, a
tree of `fs name` words whose data holds the run. G7 proves it (`Lift/Decode.lean`,
`osDecodeRegAtD_holds`); `open_stacked`'s other callees are G7's `OsCalleesRegD`
(`Lift/OsCallees.lean`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-- `decode_query_bits`' frame run at `fp`: the 192 bits of the word `w` at the certificate's
cell of its first value `.n 3` (`dqRun`). -/
def dqRunL (cert : String → V → ℕ) (name : String) (fp : ℕ) (w : E) : Layout :=
  [(fp + cert name (.n 3), (List.range 192).map fun i => bitE ((eToNat w).testBit i))]

/-- **`decode_query_bits__L{d}`, placed, on disjoint layouts**: at every frame pointer `fp`, on
every memory where the caller's words `Lin` hold the decoded positions at `pos` and the run's
pointers `g^(fp + cert name (.n 3))·g^(j·d)` at `ptrs`, a tree of `fs name` words holds, its data
holding the run `dqRunL`, its other words `Lown`, its loads in its data or `Lin`. -/
def OsDecodeAtD (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (d : ℕ) (name : String) :
    Prop :=
  ∀ (w pos ptrs : E) (Lin : Layout) (fp : ℕ),
    RegPtrs [(1, 192 / d), (2, 192 / d)] [w, pos, ptrs] (RegionL Lin) →
    (∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / d,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * d)) % 2 ^ d)) ∧
        LoadHolds rd ptrs j (ofK (gpow (fp + cert name (.n 3))) * gen ^ (j * d))) →
    ∃ Lown : Layout, Within (dqRunL cert name fp w ++ Lown) fp (fs name) ∧
      DisjL (dqRunL cert name fp w ++ Lown) ∧
      ∀ rd, LowDef k rd → MemL rd (dqRunL cert name fp w ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL (dqRunL cert name fp w)) fp
          (fs name) name [w, pos, ptrs] []

end
end LeanVM.Guest.B1
