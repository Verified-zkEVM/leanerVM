module

public import LeanVM.Cost.Decoder.Holders
import all LeanVM.Guest.B1.Main.Interface

/-!
# The guest decoder's compiled chain: `decWit`, staged

`decWitStaged`: `B1.Main.decWit`'s fields, each list of holders through a function of one slot by
partial application (`Holders.lean`), the counts (logarithms) computed by the caller and passed to
`decWitAt`, the witness built by `nodeWitnessOf` from values, so that no heavy call sits under a
lambda or a `match` at the function's top level (the kernel does not check `decWit`'s spec compiled
as written: deep recursion, or over 40 GB); `Equations.lean`: `decWitStaged_eq : decWitStaged =
decWit`. The callees' witness functions are parameters (closures).
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main
open LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-- The children `0 … n - 1`. -/
noncomputable def kidsAt (rd : Reader) (σ : Val) (wV : List E → LeanVM.Protocol.Compile.Proof)
    (n : ℕ) : List Child :=
  (List.range n).map (decKid rd σ wV)

/-- The holders of declared leanXMSS claims `0 … n - 1`. -/
noncomputable def xmssHoldersAt (rd : Reader) (σ : Val) (wX : E → LeanXmss.Signature) (n : ℕ) :
    List (ClaimHolder LeanXmss.Signature) :=
  (List.range n).map (xmssHolder rd σ wX)

/-- The holders of declared leanSPHINCS claims `0 … n - 1`. -/
noncomputable def sphincsHoldersAt (rd : Reader) (σ : Val) (wS : E → Sphincs.Signature) (n : ℕ) :
    List (ClaimHolder Sphincs.Signature) :=
  (List.range n).map (sphincsHolder rd σ wS)

/-- A witness of its five fields. Compiled as a function of its own: the compiled caller passes
the fields as values, so the kernel never matches a field (the DA option) that is not a variable
against its encoding (doing so unfolds it, here down to a logarithm by search). -/
def nodeWitnessOf (c : List Child) (x : List (ClaimHolder LeanXmss.Signature))
    (s : List (ClaimHolder Sphincs.Signature)) (d : Option (DaClaim × LeanVM.Da.MatrixWitness))
    (h : BatchingHints) : NodeWitness :=
  ⟨c, x, s, d, h⟩

/-- The witness, the counts of children and of declared claims given. -/
noncomputable def decWitAt (σ : Val) (rd : Reader) (wX : E → LeanXmss.Signature)
    (wS : E → Sphincs.Signature) (wD : List E → List E → LeanVM.Da.MatrixWitness)
    (wV : List E → LeanVM.Protocol.Compile.Proof) (wA : List E → BatchingHints)
    (nk nx ns : ℕ) : NodeWitness :=
  nodeWitnessOf (kidsAt rd σ wV nk) (xmssHoldersAt rd σ wX nx) (sphincsHoldersAt rd σ wS ns)
    (daWitness σ wD) (wA (aggArgs σ))

/-- **The witness, staged**: `decWit`'s fields through `decWitAt`, the counts (logarithms)
computed here, each list through a function of one entry by partial application. -/
noncomputable def decWitStaged (σ : Val) (rd : Reader) (wX : E → LeanXmss.Signature)
    (wS : E → Sphincs.Signature) (wD : List E → List E → LeanVM.Da.MatrixWitness)
    (wV : List E → LeanVM.Protocol.Compile.Proof) (wA : List E → BatchingHints) : NodeWitness :=
  decWitAt σ rd wX wS wD wV wA (nKids σ) (gLog (σ (.n 0))) (gLog (σ (.n 3)))

cost_compile kidsAtC := kidsAt
cost_compile xmssHoldersAtC := xmssHoldersAt
cost_compile sphincsHoldersAtC := sphincsHoldersAt
cost_compile nodeWitnessOfC := nodeWitnessOf
cost_compile decWitAtC := decWitAt
cost_compile decWitC := decWitStaged

end

end LeanVM.Cost.Decoder
