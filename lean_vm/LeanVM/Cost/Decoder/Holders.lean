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
logarithm's tables `D` given. Compiled off the running maxima of the children's counts
(`xmssHolderT`, `sphincsHolderT`: the child by one binary search, `kidIn`), equal to
`xmssHolder`, `sphincsHolder` at the values the caller builds (`xmssHolderT_eq`,
`sphincsHolderT_eq`).
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
cost_compile dvClaimC := dvClaim
cost_compile daWitnessC := daWitness
cost_compile aggArgsC := aggArgs

/-! ## The holders, off the running maxima

`xmssHolder` and `sphincsHolder` restated for the compiled chain: the child a mark falls in by
`kidIn` of the running maxima `M` (`kidMax`, built once by the caller; `kidIn_kidMax`), the raw
count `n` and `main`'s words the loop reads (`cover`, the tables' pointers, `lx`) passed as values,
the slot's address by a power in `K` (`mulK`). `xmssHolderT_eq`, `sphincsHolderT_eq`: at the
values built they are `xmssHolder`, `sphincsHolder`. -/

/-- The holder of declared leanXMSS claim `k` at its slot's mark `e` (`xmssHolderAt`). -/
def xmssHolderM (p53 : E) (wX : E → LeanXmss.Signature) (M : Array ℕ) (k e n : ℕ) :
    ClaimHolder LeanXmss.Signature :=
  if e < n then .direct (wX (mulK p53 (Parameters.g ^ (4 * k)))) else .child (kidIn M e)

/-- **The holder of declared leanXMSS claim `k`** (`xmssHolder`): its mark read here. -/
noncomputable def xmssHolderT (D : DiscreteLogTables) (rd : Reader) (cover p53 : E)
    (wX : E → LeanXmss.Signature) (M : Array ℕ) (n k : ℕ) : ClaimHolder LeanXmss.Signature :=
  xmssHolderM p53 wX M k (gLogD D (cellAt rd cover k)) n

/-- The holder of declared leanSPHINCS claim `k` at its slot's mark `e` (`sphincsHolderAt`). -/
def sphincsHolderM (p56 : E) (wS : E → Sphincs.Signature) (M : Array ℕ) (k e n : ℕ) :
    ClaimHolder Sphincs.Signature :=
  if e < n then .direct (wS (mulK p56 (Parameters.g ^ (4 * k)))) else .child (kidIn M e)

/-- **The holder of declared leanSPHINCS claim `k`** (`sphincsHolder`): its mark, at slot
`lx + k` of the coverage table, read here. -/
noncomputable def sphincsHolderT (D : DiscreteLogTables) (rd : Reader) (cover p56 : E)
    (wS : E → Sphincs.Signature) (M : Array ℕ) (lx n k : ℕ) : ClaimHolder Sphincs.Signature :=
  sphincsHolderM p56 wS M k (gLogD D (cellAt rd cover (lx + k))) n

theorem xmssHolderT_eq (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wX : E → LeanXmss.Signature) (k : ℕ) :
    xmssHolderT D rd (σ (.n 67)) (σ (.n 53)) wX (kidMax D rd (σ (.n 380)) (nKidsD D σ))
      (nRawXD D σ) k = xmssHolder D rd σ wX k := by
  unfold xmssHolderT xmssHolderM xmssHolder xmssHolderAt
  rw [kidIn_kidMax, mulK_gen_pow]
  rfl

theorem sphincsHolderT_eq (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wS : E → Sphincs.Signature) (k : ℕ) :
    sphincsHolderT D rd (σ (.n 67)) (σ (.n 56)) wS (kidMax D rd (σ (.n 380)) (nKidsD D σ))
      (lxSlotsD D σ) (nRawXD D σ + nRawSD D σ) k = sphincsHolder D rd σ wS k := by
  unfold sphincsHolderT sphincsHolderM sphincsHolder sphincsHolderAt
  rw [kidIn_kidMax, mulK_gen_pow]
  rfl

cost_compile xmssHolderMC := xmssHolderM
cost_compile xmssHolderC := xmssHolderT
cost_compile sphincsHolderMC := sphincsHolderM
cost_compile sphincsHolderC := sphincsHolderT

end

end LeanVM.Cost.Decoder
