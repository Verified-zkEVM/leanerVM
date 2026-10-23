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

/-!
# `open_stacked`'s callees, placed

What `open_stacked`'s completeness takes of the callees other agents prove, in the uniform placed
form on disjoint layouts (`CompleteRelD`, `Memory/Uniform.lean`), each on its meaning:

* `opening_fold`, `assert_canonical`, `grind_check__L17` (returning fixed words);
* `opening_ood_point__L{n}`, `opening_final_message__L{n}`, `opening_row_weights__L{f}_L{r}`,
  `verify_merkle_cap__L{D}`, `fold_final_msg__L{n}` (their meanings read and check the caller's
  words);
* `decode_query_bits__L{d}`, which stores pointers into its own frame run in the caller's buffer,
  in an explicit form (`OsDecodeAtD`): at every frame pointer `fp`, a tree of `fs name` words whose
  data holds the run of the word's 192 bits at its certificate cell (`dqRunL`), on every memory
  where the caller's words hold the decoded positions and the run's pointers.

`opening_queries__L…` is not here: B1-b proves it (`OqCompleteD`, `Opening/QueriesPlaced*`).
`OsCalleesAtD` collects the others at the names the 28 configurations call.
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
    (∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / d,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * d)) % 2 ^ d)) ∧
        LoadHolds rd ptrs j (ofK (gpow (fp + cert name (.n 3))) * gen ^ (j * d))) →
    ∃ Lown : Layout, Within (dqRunL cert name fp w ++ Lown) fp (fs name) ∧
      DisjL (dqRunL cert name fp w ++ Lown) ∧
      ∀ rd, LowDef k rd → MemL rd (dqRunL cert name fp w ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL (dqRunL cert name fp w)) fp
          (fs name) name [w, pos, ptrs] []

/-- **The callees of `open_stacked` other than `opening_queries`, placed on disjoint layouts**,
at the names its configurations call. -/
structure OsCalleesAtD (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) : Prop where
  fold : CompleteRelD fs cert k "opening_fold" MeaningOpeningFold
  canonical : CompleteRelD fs cert k "assert_canonical" fun _ args rets =>
    MeaningAssertCanonical args rets
  grind : CompleteRelD fs cert k "grind_check__L17" fun _ args rets => MeaningGrindCheck 17 args rets
  ood : ∀ p ∈ oodPointNames, CompleteRelD fs cert k p.1 (MeaningOpeningOodPoint p.2)
  finalMsg : ∀ p ∈ finalMessageNames, CompleteRelD fs cert k p.1 (MeaningOpeningFinalMessage p.2)
  rowWeights4 : CompleteRelD fs cert k "opening_row_weights__L4_L0" (MeaningOpeningRowWeights 4 0)
  rowWeights6 : CompleteRelD fs cert k "opening_row_weights__L6_L1" (MeaningOpeningRowWeights 6 1)
  merkleCap : ∀ p ∈ merkleCapNames, CompleteRelD fs cert k p.1 (MeaningVerifyMerkleCap p.2)
  foldFinal : ∀ p ∈ foldFinalMsgNames, CompleteRelD fs cert k p.1 (MeaningFoldFinalMsg p.2)
  decode : ∀ p ∈ decodeQueryBitsNames, OsDecodeAtD fs cert k p.2 p.1

end
end LeanVM.Guest.B1
