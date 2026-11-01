module

public import LeanVM.Cost.Decoder.Signatures
import all LeanVM.Guest.B1.Main.Interface

/-!
# The guest decoder's compiled chain: the claims' holders

`decWit`'s parts of one entry: the holder of declared leanXMSS and leanSPHINCS claim `k`
(`xmssHolder`, `sphincsHolder`: by its slot's mark, a raw signature or the child the mark falls
in; staged, the mark and the count logarithms computed by the caller and the branch a function of
plain numbers, `xmssHolderAt`, `sphincsHolderAt`), the DA claim and matrix (`daWitness`), `aggregate_claims`' call words (`aggArgs`).
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main
open LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-- The holder of declared leanXMSS claim `k` at its slot's mark `e`, the raw signatures `n`
counted: a raw signature (`wX` at the slot) if `e < n`, else the child the mark falls in. -/
noncomputable def xmssHolderAt (rd : Reader) (σ : Val) (wX : E → LeanXmss.Signature)
    (k e n : ℕ) : ClaimHolder LeanXmss.Signature :=
  if e < n then .direct (wX (σ (.n 53) * gen ^ (4 * k))) else .child (kidOf rd σ e)

/-- **The holder of declared leanXMSS claim `k`**: its mark and the raw count (logarithms)
computed here and passed to `xmssHolderAt`, whose spec holds at every mark and count. -/
noncomputable def xmssHolder (rd : Reader) (σ : Val) (wX : E → LeanXmss.Signature) (k : ℕ) :
    ClaimHolder LeanXmss.Signature :=
  xmssHolderAt rd σ wX k (markOf rd σ k) (nRawX σ)

/-- The holder of declared leanSPHINCS claim `k` at its slot's mark `e`, the raw signatures `n`
counted. -/
noncomputable def sphincsHolderAt (rd : Reader) (σ : Val) (wS : E → Sphincs.Signature)
    (k e n : ℕ) : ClaimHolder Sphincs.Signature :=
  if e < n then .direct (wS (σ (.n 56) * gen ^ (4 * k))) else .child (kidOf rd σ e)

/-- **The holder of declared leanSPHINCS claim `k`**, staged as `xmssHolder`. -/
noncomputable def sphincsHolder (rd : Reader) (σ : Val) (wS : E → Sphincs.Signature) (k : ℕ) :
    ClaimHolder Sphincs.Signature :=
  sphincsHolderAt rd σ wS k (markOf rd σ (lxSlots σ + k)) (nRawX σ + nRawS σ)

/-- The DA claim and matrix `da_verify` checks, if the node checks one. -/
noncomputable def daWitness (σ : Val) (wD : List E → List E → LeanVM.Da.MatrixWitness) :
    Option (DaClaim × LeanVM.Da.MatrixWitness) :=
  if nDirect σ = 1 then
    some (dvClaim σ, wD [σ (.n 50)] [σ (.n 339), σ (.n 340), σ (.n 341), σ (.n 342)])
  else none

/-- The words of `aggregate_claims`' call. -/
def aggArgs (σ : Val) : List E := [σ (.n 6), σ (.n 365), σ (.n 371), σ (.n 377), σ (.n 402)]

cost_compile nRawXC := nRawX
cost_compile nRawSC := nRawS
cost_compile lxSlotsC := lxSlots
cost_compile xmssHolderAtC := xmssHolderAt
cost_compile xmssHolderC := xmssHolder
cost_compile sphincsHolderAtC := sphincsHolderAt
cost_compile sphincsHolderC := sphincsHolder
cost_compile dvClaimC := dvClaim
cost_compile daWitnessC := daWitness
cost_compile aggArgsC := aggArgs
end

end LeanVM.Cost.Decoder
