import LeanerVM.Protocol.Verify.Tables
import LeanerVMTests.Protocol.RustProof

/-!
# The verifier's table sumcheck and public input on the Rust proof

After the bus phase, the chain walk reads the table sumcheck (`ξ`, four rounds of three wire
coefficients, the 104 column values) and the public input (`r`, two values). The algebra on the
fixture: the table sumcheck's final check, the oracle verifier's `Sumcheck.finalCheck` of the
table summand at the leanISA instance, passes with the Python verifier's final claim
(`python-verifier/verifier.py:577-610`, traced at leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2`), and the deployed public-input check passes. Each
check rejects its mutation: a column value flipped, a round's wire coefficient flipped, a
missing column value, a public value flipped, a third public value.
-/

namespace LeanerVMTests.Protocol.VerifyTables

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol LeanerVM.Protocol.Blake2sHash
open LeanerVM.Protocol.LeanIsa LeanerVM.Protocol.Verify LeanerVMTests.Protocol.RustProof

/-- The fixture's wires up to the public input. -/
def wires (f : Fixture) (s : Sizes) : Except ReadError (BusWire × TableWire × PubWire) :=
  let I := leanVm f.prog s
  (((do
      let _ ← walkSetup (m := Id) blake2sBytes
      let b ← walkBus blake2sBytes I.μBus I.busClaims
      let t ← walkTables blake2sBytes I.τmax I.tableColumns
      let p ← walkPub blake2sBytes (PublicInput.sentCount I (I.publicLines f.input))
      return (b, t, p)).run'
    ⟨FsState.seed f.prog f.input, f.proof.stream, []⟩).run : Id _)

/-- The algebra up to the table sumcheck's output. -/
def tableOut (f : Fixture) (s : Sizes) (b : BusWire) (t : TableWire) :
    Option (PublicInput × TableOut (leanVm f.prog s)) := do
  tableStep (leanVm f.prog s) (← leanVmBus f.prog s f.input b) t

/-- The algebra up to the public input's output. -/
def pubOut (f : Fixture) (s : Sizes) (b : BusWire) (t : TableWire) (p : PubWire) :
    Option (PublicInput × PubOut (leanVm f.prog s)) := do
  pubStep (leanVm f.prog s) (← tableOut f s b t) p

/-- Both phases on the fixture's wires, the bus phase run once, the table and public wires
changed by each pair of `muts`: whether each passes. -/
def checks (muts : List ((TableWire → TableWire) × (PubWire → PubWire))) : List Bool :=
  let f := fx
  let s := sizes.1
  match wires f s with
  | .ok (b, t, p) =>
    match leanVmBus f.prog s f.input b with
    | none => []
    | some bo => muts.map fun (ft, fp) ↦
      ((tableStep (leanVm f.prog s) bo (ft t)).bind fun tb ↦
        pubStep (leanVm f.prog s) tb (fp p)).isSome
  | .error _ => []

#guard match wires fx sizes.1 with
  | .ok (_, t, p) => t.rounds.length == 4 && t.finals.length == 104 && p.values.length == 2
  | .error _ => false

-- The honest wires pass, and each mutation is rejected: a column value flipped, a round's wire
-- coefficient flipped, a missing column value, a public value flipped, a third public value.
#guard checks [(id, id),
    (fun t ↦ { t with finals := t.finals.modify 17 (· + 1) }, id),
    (fun t ↦ { t with rounds := t.rounds.modify 2 fun r ↦
      { r with wire := r.wire.modify 1 (· + 1) } }, id),
    (fun t ↦ { t with finals := t.finals.dropLast }, id),
    (id, fun p ↦ { p with values := p.values.modify 1 (· + 1) }),
    (id, fun p ↦ { p with values := p.values ++ [0] })] ==
  [true, false, false, false, false, false]

end LeanerVMTests.Protocol.VerifyTables
