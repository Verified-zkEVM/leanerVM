import LeanerVM.Protocol.Compile.Bus
import LeanerVMTests.Protocol.RustProof

/-!
# The verifier's phases are the oracle verifiers' on the Rust proof

The chain walk reads the fixture's wire of the bus phase. It decodes to a transcript of the
phase's oracle protocol, the dropped coefficients rebuilt from the running claims (`busTr?`), and
the transcript carries its wire back. The oracle verifier of the bus phase accepts the transcript
with the executable's output (`busStep_eq`).

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

/-- The fixture's wire of the bus phase. -/
def busWire : Except ReadError BusWire :=
  (((do
      let _ ← walkSetup (readerOps (m := Id) blake2sBytes)
      walkBus (readerOps blake2sBytes) I.μBus I.busClaims).run'
    ⟨Deployed.seed fx.prog fx.input, fx.proof.stream, []⟩).run : Id _)

/-- A layer's descendant flipped. -/
def flipChild (b : BusWire) : BusWire :=
  { b with layers := b.layers.modify 3 fun l ↦
      { l with children := l.children.modify 1 (·.modify 2 (· + 1)) } }

/-- The bus phase on the fixture: the wire decodes, the oracle verifier accepts the transcript
with the executable's totals and columns, and the transcript carries the wire; with a flipped
descendant the wire still decodes, and both reject. -/
def busAgrees : Bool :=
  match busWire with
  | .ok b =>
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

end LeanerVMTests.Protocol.Compile
