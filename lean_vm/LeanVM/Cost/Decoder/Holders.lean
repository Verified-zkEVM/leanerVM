module

public import LeanVM.Cost.Decoder.Signatures
import all LeanVM.Guest.B1.Main.Interface

/-!
# The guest decoder's compiled chain: the claims' holders

`decWit`'s parts of one entry: the holder of declared leanXMSS and leanSPHINCS claim `k`
(`xmssHolder`, `sphincsHolder`: by its slot's mark, a raw signature or the child the mark falls
in; staged, the mark and the count logarithms computed by the caller and the branch a function of
plain numbers, `xmssHolderAt`, `sphincsHolderAt`), the DA claim and matrix (`daWitness`),
`aggregate_claims`' call words (`aggArgs`). Each reads its logarithms by `gLogD D`, the
logarithm's tables `D` given.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main
open LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Extraction.Fast

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

/-- The holder of declared leanXMSS claim `k` at its slot's mark `e`, the raw signatures `n`
counted: a raw signature (`wX` at the slot) if `e < n`, else the child the mark falls in. -/
noncomputable def xmssHolderAt (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wX : E → LeanXmss.Signature) (k e n : ℕ) : ClaimHolder LeanXmss.Signature :=
  if e < n then .direct (wX (σ (.n 53) * gen ^ (4 * k))) else .child (kidOfStaged D rd σ e)

/-- **The holder of declared leanXMSS claim `k`**: its mark and the raw count (logarithms)
computed here and passed to `xmssHolderAt`, whose spec holds at every mark and count. -/
noncomputable def xmssHolder (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wX : E → LeanXmss.Signature) (k : ℕ) : ClaimHolder LeanXmss.Signature :=
  xmssHolderAt D rd σ wX k (markOfD D rd σ k) (nRawXD D σ)

/-- The holder of declared leanSPHINCS claim `k` at its slot's mark `e`, the raw signatures `n`
counted. -/
noncomputable def sphincsHolderAt (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wS : E → Sphincs.Signature) (k e n : ℕ) : ClaimHolder Sphincs.Signature :=
  if e < n then .direct (wS (σ (.n 56) * gen ^ (4 * k))) else .child (kidOfStaged D rd σ e)

/-- **The holder of declared leanSPHINCS claim `k`**, staged as `xmssHolder`. -/
noncomputable def sphincsHolder (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wS : E → Sphincs.Signature) (k : ℕ) : ClaimHolder Sphincs.Signature :=
  sphincsHolderAt D rd σ wS k (markOfD D rd σ (lxSlotsD D σ + k)) (nRawXD D σ + nRawSD D σ)

/-- The DA claim and matrix `da_verify` checks, if the node checks one. -/
noncomputable def daWitness (D : DiscreteLogTables) (σ : Val)
    (wD : List E → List E → LeanVM.Da.MatrixWitness) :
    Option (DaClaim × LeanVM.Da.MatrixWitness) :=
  if nDirectD D σ = 1 then
    some (dvClaim σ, wD [σ (.n 50)] [σ (.n 339), σ (.n 340), σ (.n 341), σ (.n 342)])
  else none

/-- The words of `aggregate_claims`' call. -/
def aggArgs (σ : Val) : List E := [σ (.n 6), σ (.n 365), σ (.n 371), σ (.n 377), σ (.n 402)]

cost_compile nRawXC := nRawXD
cost_compile nRawSC := nRawSD
cost_compile nDirectC := nDirectD
cost_compile xmssHolderAtC := xmssHolderAt
cost_compile xmssHolderC := xmssHolder
cost_compile sphincsHolderAtC := sphincsHolderAt
cost_compile sphincsHolderC := sphincsHolder
cost_compile dvClaimC := dvClaim
cost_compile daWitnessC := daWitness
cost_compile aggArgsC := aggArgs
end

end LeanVM.Cost.Decoder
