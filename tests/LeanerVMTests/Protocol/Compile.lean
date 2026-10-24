import LeanerVM.Protocol.Compile.Tables
import LeanerVMTests.Protocol.RustProof

/-!
# The verifier's phases are the oracle verifiers' on the Rust proof

The chain walk reads the fixture's wires of the bus phase, the table sumcheck and the public
input. Each wire decodes to a transcript of its phase's oracle protocol, the dropped coefficients
rebuilt from the running claims (`busTr?`, `tableTr?`, `pubTr`), and each transcript carries its
wire back. The oracle verifiers accept the transcripts with the executable's outputs
(`busStep_eq`, `tableStep_eq`, `pubStep_eq`).

The decoding checks nothing: a descendant flipped in a layer of the grand product still decodes,
and the oracle verifier rejects the transcript, as the executable rejects the wire. A step that
skipped the layer's check would accept the wire, and `busStep_eq` would fail on it.
-/

namespace LeanerVMTests.Protocol.Compile

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol LeanerVM.Protocol.Blake2sHash
open LeanerVM.Protocol.LeanIsa LeanerVM.Protocol.Verify LeanerVM.Protocol.Compile
open LeanerVMTests.Protocol.RustProof

/-- The fixture's instance. -/
abbrev I : M3Instance := leanVm fx.prog sizes.1

/-- Its bus phase's conditions. -/
theorem hI : Bus.Conditions I := leanIsa_conditions _ fx.prog sizes.1

/-- The fixture's wires up to the public input. -/
def wires : Except ReadError (BusWire × TableWire × PubWire) :=
  (((do
      let _ ← walkSetup (readerOps (m := Id) blake2sBytes)
      let b ← walkBus (readerOps blake2sBytes) I.μBus I.busClaims
      let t ← walkTables (readerOps blake2sBytes) I.τmax I.tableColumns
      let p ← walkPub (readerOps blake2sBytes) (PublicInput.sentCount I (I.publicLines fx.input))
      return (b, t, p)).run'
    ⟨Deployed.seed fx.prog fx.input, fx.proof.stream, []⟩).run : Id _)

/-- A layer's descendant flipped. -/
def flipChild (b : BusWire) : BusWire :=
  { b with layers := b.layers.modify 3 fun l ↦
      { l with children := l.children.modify 1 (·.modify 2 (· + 1)) } }

/-- The bus phase on the fixture: the wire decodes, the oracle verifier accepts the transcript
with the executable's totals and columns, and the transcript carries the wire; with a flipped
descendant the wire still decodes, and both reject. -/
def busAgrees : Bool :=
  match wires with
  | .ok (b, _, _) =>
    match busTr? I fx.input b, busStep I hI fx.input b, busTr? I fx.input (flipChild b) with
    | some t, some o, some t' =>
      let o' := (busPhase I hI).front.out fx.input t
      (busPhase I hI).front.check fx.input t &&
        List.ofFn o'.2.totals == List.ofFn o.2.totals &&
        o'.2.columns.toList.map (·.value) == o.2.columns.toList.map (·.value) &&
        (busWireOf I t).alpha == b.alpha && (busWireOf I t).values == b.values &&
        ((busWireOf I t).layers.map fun l ↦ (l.rounds.map (·.wire), l.children, l.combos)) ==
          (b.layers.map fun l ↦ (l.rounds.map (·.wire), l.children, l.combos)) &&
        !(busPhase I hI).front.check fx.input t' && (busStep I hI fx.input (flipChild b)).isNone
    | _, _, _ => false
  | .error _ => false

#guard busAgrees

/-- The table sumcheck and the public input on the fixture: each wire decodes, the oracle
verifiers accept with the executable's outputs, and the transcripts carry the wires. -/
def tablesAgree : Bool :=
  match wires with
  | .ok (b, tw, pw) =>
    match busStep I hI fx.input b with
    | some bo =>
      match tableTr? I bo tw, tableStep I bo tw with
      | some t, some o =>
        let o' := (TableSumcheck.tableSumcheck I).front.out bo t
        (TableSumcheck.tableSumcheck I).front.check bo t &&
          o'.2.columns.toList.map (·.value) == o.2.columns.toList.map (·.value) &&
          (tableWireOf I t).rounds.map (·.wire) == tw.rounds.map (·.wire) &&
          (tableWireOf I t).finals == tw.finals &&
          (deployedPublicInputPhase I).front.check o (pubTr pw) &&
          (pubStep I o pw).isSome && (pubWireOf (pubTr pw)).values == pw.values
      | _, _ => false
    | none => false
  | .error _ => false

#guard tablesAgree

end LeanerVMTests.Protocol.Compile
