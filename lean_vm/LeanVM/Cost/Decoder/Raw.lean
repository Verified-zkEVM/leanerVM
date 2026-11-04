module

public import LeanVM.Cost.Decoder.Signatures
import all LeanVM.Guest.B1.Main.Interface

/-!
# The guest decoder's compiled chain: the raw signatures

`decWit`'s parts of one entry: the raw leanXMSS and leanSPHINCS signature of mark `j`
(`rawXmssD`, `rawSphincsD`: the claim of the slot holding the mark and the signature at the
slot), the DA claim and matrix (`daWitness`), `aggregate_claims`' call words (`aggArgs`). Each
reads its logarithms by `gLogD D`, the logarithm's tables `D` given. Compiled off the regions'
tables (`xmssRawT`, `sphincsRawT`: the slot by one binary search, `slotIn`, then the claim and the
signature at the slot's address, `xmssRawAt`, `sphincsRawAt`), equal to `rawXmssD`, `rawSphincsD`
at the tables built (`xmssRawT_eq`, `sphincsRawT_eq`).
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main
open LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Extraction.Fast LeanVM.Guest.Fast

@[expose] public section

/-- The numbers of raw leanXMSS and leanSPHINCS signatures, of direct DA checks (`nRawX`,
`nRawS`, `nDirect`), the logarithm's tables `D` given. -/
def nRawXD (D : DiscreteLogTables) (σ : Val) : ℕ := gLogD D (σ (.n 2))
def nRawSD (D : DiscreteLogTables) (σ : Val) : ℕ := gLogD D (σ (.n 5))
def nDirectD (D : DiscreteLogTables) (σ : Val) : ℕ := gLogD D (σ (.n 7))

theorem nRawXD_tables : nRawXD discreteLogTables = nRawX := by
  funext σ; unfold nRawXD nRawX; rw [gLogD_tables]
theorem nRawSD_tables : nRawSD discreteLogTables = nRawS := by
  funext σ; unfold nRawSD nRawS; rw [gLogD_tables]
theorem nDirectD_tables : nDirectD discreteLogTables = nDirect := by
  funext σ; unfold nDirectD nDirect; rw [gLogD_tables]

/-- **The raw leanXMSS signature of mark `j`** (`rawXmss`). -/
noncomputable def rawXmssD (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wX : E → LeanXmss.Signature) (j : ℕ) : LeanXmssClaim × LeanXmss.Signature :=
  let s := slotOfD D rd σ 0 (lxSlotsD D σ) j
  (xmssAt rd (σ (.n 52)) s, wX (σ (.n 52) * gen ^ (4 * s)))

/-- **The raw leanSPHINCS signature of mark `n_raw_x + j`** (`rawSphincs`). -/
noncomputable def rawSphincsD (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wS : E → Sphincs.Signature) (j : ℕ) : LeanSphincsClaim × Sphincs.Signature :=
  let s := slotOfD D rd σ (lxSlotsD D σ) (lsSlotsD D σ) (nRawXD D σ + j)
  (sphincsAt rd (σ (.n 55)) s, wS (σ (.n 55) * gen ^ (4 * s)))

theorem rawXmssD_tables : rawXmssD discreteLogTables = rawXmss := by
  funext rd σ wX j; unfold rawXmssD rawXmss; rw [slotOfD_tables, lxSlotsD_tables]
theorem rawSphincsD_tables : rawSphincsD discreteLogTables = rawSphincs := by
  funext rd σ wS j; unfold rawSphincsD rawSphincs
  rw [slotOfD_tables, lxSlotsD_tables, lsSlotsD_tables, nRawXD_tables]

/-- The DA claim and matrix `da_verify` checks, if the node checks one. -/
noncomputable def daWitness (D : DiscreteLogTables) (σ : Val)
    (wD : List E → List E → LeanVM.Da.MatrixWitness) :
    Option (DaClaim × LeanVM.Da.MatrixWitness) :=
  if nDirectD D σ = 1 then
    some (dvClaim σ, wD [σ (.n 49)] [σ (.n 339), σ (.n 340), σ (.n 341), σ (.n 342)])
  else none

/-- The words of `aggregate_claims`' call. -/
def aggArgs (σ : Val) : List E := [σ (.n 6), σ (.n 365), σ (.n 371), σ (.n 377), σ (.n 398)]

cost_compile nRawXC := nRawXD
cost_compile nRawSC := nRawSD
cost_compile nDirectC := nDirectD
cost_compile scalarOfCellsC := LeanVM.Guest.B1.Da.scalarOfCells
cost_compile dvClaimC := dvClaim
cost_compile daWitnessC := daWitness
cost_compile aggArgsC := aggArgs

/-! ## The raw signatures, off the regions' tables

`rawXmssD` and `rawSphincsD` restated for the compiled chain: the slot holding a mark by `slotIn`
of the region's table (`regionTable`, built once by the caller; `slotIn_regionTable`), the slot's
address by a power in `K` (`mulK`), computed once. `xmssRawT_eq`, `sphincsRawT_eq`: at the tables
built they are `rawXmssD`, `rawSphincsD`. -/

/-- The raw leanXMSS signature at the address `p53 · a`: its slot's claim and `wX` there. -/
noncomputable def xmssRawAt (rd : Reader) (p53 : E) (wX : E → LeanXmss.Signature) (a : K) :
    LeanXmssClaim × LeanXmss.Signature :=
  (xmssAtK rd (p53.limb 0 * a), wX (mulK p53 a))

/-- **The raw leanXMSS signature of mark `j`** (`rawXmssD`), off the region's table `tm`, `ts`. -/
noncomputable def xmssRawT (rd : Reader) (p53 : E) (wX : E → LeanXmss.Signature)
    (tm ts : Array ℕ) (j : ℕ) : LeanXmssClaim × LeanXmss.Signature :=
  xmssRawAt rd p53 wX (Parameters.g ^ (4 * slotIn tm ts j))

/-- The raw leanSPHINCS signature at the address `p56 · a`. -/
noncomputable def sphincsRawAt (rd : Reader) (p56 : E) (wS : E → Sphincs.Signature) (a : K) :
    LeanSphincsClaim × Sphincs.Signature :=
  (sphincsAtK rd (p56.limb 0 * a), wS (mulK p56 a))

/-- **The raw leanSPHINCS signature of mark `nrx + j`** (`rawSphincsD`), off the region's table. -/
noncomputable def sphincsRawT (rd : Reader) (p56 : E) (wS : E → Sphincs.Signature)
    (tm ts : Array ℕ) (nrx j : ℕ) : LeanSphincsClaim × Sphincs.Signature :=
  sphincsRawAt rd p56 wS (Parameters.g ^ (4 * slotIn tm ts (nrx + j)))

theorem xmssRawT_eq (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wX : E → LeanXmss.Signature) (j : ℕ) :
    xmssRawT rd (σ (.n 52)) wX (lxTable D rd σ).1 (lxTable D rd σ).2 j = rawXmssD D rd σ wX j := by
  unfold xmssRawT xmssRawAt rawXmssD
  rw [slotIn_regionTable, mulK_gen_pow, ← xmssAt_eq_K]

theorem sphincsRawT_eq (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wS : E → Sphincs.Signature) (j : ℕ) :
    sphincsRawT rd (σ (.n 55)) wS (lsTable D rd σ).1 (lsTable D rd σ).2 (nRawXD D σ) j =
      rawSphincsD D rd σ wS j := by
  unfold sphincsRawT sphincsRawAt rawSphincsD
  rw [slotIn_regionTable, mulK_gen_pow, ← sphincsAt_eq_K]

cost_compile xmssRawAtC := xmssRawAt
cost_compile xmssRawC := xmssRawT
cost_compile sphincsRawAtC := sphincsRawAt
cost_compile sphincsRawC := sphincsRawT

end

end LeanVM.Cost.Decoder
