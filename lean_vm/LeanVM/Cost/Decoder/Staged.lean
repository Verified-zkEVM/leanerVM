module

public import LeanVM.Cost.Decoder.Holders
import all LeanVM.Guest.B1.Main.Interface

/-!
# The guest decoder's compiled chain: `decWit`, staged

`decWitStaged`: `B1.Main.decWit`'s fields, each list of holders through a function of one slot by
partial application (`Holders.lean`), the counts (logarithms) computed by the caller and passed to
`decWitAt`, the witness built by `nodeWitnessOf` from values, so that no heavy call sits under a
lambda or a `match` at the function's top level (the kernel does not check `decWit`'s spec compiled
as written: deep recursion, or over 40 GB); `Equations.lean`: `decWitStaged_eq : decWitStaged
discreteLogTables = decWit`. The callees' witness functions are parameters (closures), the
logarithm's tables `D` a value.

The searches over the coverage table read tables built once here, by `decWitAt`, and passed to
`decWitTab` as values: the two regions' tables (`regionTable`) and the running maxima of the
children's counts (`kidMax`), with `main`'s words the loops read (`cover`, `written`, the tables'
pointers) and the counts. The children (`kidsT`) and holders (`xmssHoldersT`, `sphincsHoldersT`)
are those of `kidsAt`, `xmssHoldersAt`, `sphincsHoldersAt` (`kidsT_eq`, `xmssHoldersT_eq`,
`sphincsHoldersT_eq`).
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main
open LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Extraction.Fast LeanVM.Guest.Fast

@[expose] public section

/-- The children `0 … n - 1`. -/
noncomputable def kidsAt (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wV : List E → LeanVM.Protocol.Compile.Proof) (n : ℕ) : List Child :=
  (List.range n).map (decKidD D rd σ wV)

/-- The holders of declared leanXMSS claims `0 … n - 1`. -/
noncomputable def xmssHoldersAt (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wX : E → LeanXmss.Signature) (n : ℕ) : List (ClaimHolder LeanXmss.Signature) :=
  (List.range n).map (xmssHolder D rd σ wX)

/-- The holders of declared leanSPHINCS claims `0 … n - 1`. -/
noncomputable def sphincsHoldersAt (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wS : E → Sphincs.Signature) (n : ℕ) : List (ClaimHolder Sphincs.Signature) :=
  (List.range n).map (sphincsHolder D rd σ wS)

/-- A witness of its five fields. Compiled as a function of its own: the compiled caller passes
the fields as values, so the kernel never matches a field (the DA option) that is not a variable
against its encoding (doing so unfolds it, here down to a logarithm by search). -/
def nodeWitnessOf (c : List Child) (x : List (ClaimHolder LeanXmss.Signature))
    (s : List (ClaimHolder Sphincs.Signature)) (d : Option (DaClaim × LeanVM.Da.MatrixWitness))
    (h : BatchingHints) : NodeWitness :=
  ⟨c, x, s, d, h⟩

/-! ## Off the tables -/

/-- The children `0 … n - 1`, off the regions' tables. -/
noncomputable def kidsT (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wV : List E → LeanVM.Protocol.Compile.Proof) (w380 p53 p56 : E) (tx ts : Array ℕ × Array ℕ)
    (n : ℕ) : List Child :=
  (List.range n).map (decKidT D rd σ wV w380 p53 p56 tx ts)

/-- The holders of declared leanXMSS claims `0 … n - 1`, `nr` raw. -/
noncomputable def xmssHoldersT (D : DiscreteLogTables) (rd : Reader) (cover p53 : E)
    (wX : E → LeanXmss.Signature) (M : Array ℕ) (nr n : ℕ) :
    List (ClaimHolder LeanXmss.Signature) :=
  (List.range n).map (xmssHolderT D rd cover p53 wX M nr)

/-- The holders of declared leanSPHINCS claims `0 … n - 1`, `nr` raw (of both kinds). -/
noncomputable def sphincsHoldersT (D : DiscreteLogTables) (rd : Reader) (cover p56 : E)
    (wS : E → Sphincs.Signature) (M : Array ℕ) (lx nr n : ℕ) :
    List (ClaimHolder Sphincs.Signature) :=
  (List.range n).map (sphincsHolderT D rd cover p56 wS M lx nr)

theorem kidsT_eq (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wV : List E → LeanVM.Protocol.Compile.Proof) (n : ℕ) :
    kidsT D rd σ wV (σ (.n 380)) (σ (.n 53)) (σ (.n 56)) (lxTable D rd σ) (lsTable D rd σ) n =
      kidsAt D rd σ wV n :=
  List.map_congr_left fun c _ ↦ decKidT_eq D rd σ wV c

theorem xmssHoldersT_eq (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wX : E → LeanXmss.Signature) (n : ℕ) :
    xmssHoldersT D rd (σ (.n 67)) (σ (.n 53)) wX (kidMax D rd (σ (.n 380)) (nKidsD D σ))
      (nRawXD D σ) n = xmssHoldersAt D rd σ wX n :=
  List.map_congr_left fun k _ ↦ xmssHolderT_eq D rd σ wX k

theorem sphincsHoldersT_eq (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wS : E → Sphincs.Signature) (n : ℕ) :
    sphincsHoldersT D rd (σ (.n 67)) (σ (.n 56)) wS (kidMax D rd (σ (.n 380)) (nKidsD D σ))
      (lxSlotsD D σ) (nRawXD D σ + nRawSD D σ) n = sphincsHoldersAt D rd σ wS n :=
  List.map_congr_left fun k _ ↦ sphincsHolderT_eq D rd σ wS k

/-- The witness off the tables: `nk` children, `nx`, `ns` declared claims, `lx` leanXMSS slots,
`nrx`, `nrs` raw signatures, `main`'s words `cover`, `written` (`w380`), the tables' pointers,
the regions' tables `tx`, `ts` and the running maxima `M`. -/
noncomputable def decWitTab (D : DiscreteLogTables) (σ : Val) (rd : Reader)
    (wX : E → LeanXmss.Signature) (wS : E → Sphincs.Signature)
    (wD : List E → List E → LeanVM.Da.MatrixWitness)
    (wV : List E → LeanVM.Protocol.Compile.Proof) (wA : List E → BatchingHints)
    (nk nx ns lx nrx nrs : ℕ) (cover w380 p53 p56 : E) (tx ts : Array ℕ × Array ℕ)
    (M : Array ℕ) : NodeWitness :=
  nodeWitnessOf (kidsT D rd σ wV w380 p53 p56 tx ts nk) (xmssHoldersT D rd cover p53 wX M nrx nx)
    (sphincsHoldersT D rd cover p56 wS M lx (nrx + nrs) ns) (daWitness D σ wD) (wA (aggArgs σ))

/-- The witness, the counts given: the tables built here, once. -/
noncomputable def decWitAt (D : DiscreteLogTables) (σ : Val) (rd : Reader)
    (wX : E → LeanXmss.Signature) (wS : E → Sphincs.Signature)
    (wD : List E → List E → LeanVM.Da.MatrixWitness)
    (wV : List E → LeanVM.Protocol.Compile.Proof) (wA : List E → BatchingHints)
    (nk nx ns lx ls nrx nrs : ℕ) : NodeWitness :=
  decWitTab D σ rd wX wS wD wV wA nk nx ns lx nrx nrs (σ (.n 67)) (σ (.n 380)) (σ (.n 53))
    (σ (.n 56)) (regionTable D rd (σ (.n 67)) 0 lx) (regionTable D rd (σ (.n 67)) lx ls)
    (kidMax D rd (σ (.n 380)) nk)

/-- **The witness, staged**: `decWit`'s fields through `decWitAt`, the counts (logarithms)
computed here, each list through a function of one entry by partial application, the logarithm's
tables `D` given. -/
noncomputable def decWitStaged (D : DiscreteLogTables) (σ : Val) (rd : Reader)
    (wX : E → LeanXmss.Signature) (wS : E → Sphincs.Signature)
    (wD : List E → List E → LeanVM.Da.MatrixWitness)
    (wV : List E → LeanVM.Protocol.Compile.Proof) (wA : List E → BatchingHints) : NodeWitness :=
  decWitAt D σ rd wX wS wD wV wA (nKidsD D σ) (gLogD D (σ (.n 0))) (gLogD D (σ (.n 3)))
    (lxSlotsD D σ) (lsSlotsD D σ) (nRawXD D σ) (nRawSD D σ)

/-- **Off the tables, the witness is the unstaged lists'.** -/
theorem decWitStaged_eq_lists (D : DiscreteLogTables) (σ : Val) (rd : Reader)
    (wX : E → LeanXmss.Signature) (wS : E → Sphincs.Signature)
    (wD : List E → List E → LeanVM.Da.MatrixWitness)
    (wV : List E → LeanVM.Protocol.Compile.Proof) (wA : List E → BatchingHints) :
    decWitStaged D σ rd wX wS wD wV wA =
      nodeWitnessOf (kidsAt D rd σ wV (nKidsD D σ)) (xmssHoldersAt D rd σ wX (gLogD D (σ (.n 0))))
        (sphincsHoldersAt D rd σ wS (gLogD D (σ (.n 3)))) (daWitness D σ wD) (wA (aggArgs σ)) := by
  unfold decWitStaged decWitAt decWitTab
  rw [kidsT_eq, xmssHoldersT_eq, sphincsHoldersT_eq]

cost_compile kidsTC := kidsT
cost_compile xmssHoldersTC := xmssHoldersT
cost_compile sphincsHoldersTC := sphincsHoldersT
cost_compile nodeWitnessOfC := nodeWitnessOf
cost_compile decWitTabC := decWitTab
cost_compile decWitAtC := decWitAt
cost_compile decWitC := decWitStaged
end

end LeanVM.Cost.Decoder
