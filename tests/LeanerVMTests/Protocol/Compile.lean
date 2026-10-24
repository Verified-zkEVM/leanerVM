import LeanerVM.Protocol.Compile.Flock
import LeanerVMTests.Protocol.RustProof

/-!
# The verifier's phases are the oracle verifiers' on the Rust proof

The chain walk reads the fixture's wires of the bus phase, the table sumcheck, the public input
and the Flock phase. Each wire decodes to a transcript of its phase's oracle protocol, the
dropped coefficients rebuilt from the running claims (`busTr?`, `tableTr?`, `pubTr`,
`flockTr?`), and each transcript carries its wire back. The oracle verifiers of the bus phase,
the table sumcheck and the public input accept their transcripts with the executable's outputs
(`busStep_eq`, `tableStep_eq`, `pubStep_eq`), and the opening claim is the pool batched by `λ`
(`openingClaim_eq`).

The decoding checks nothing: a descendant flipped in a layer of the grand product still decodes,
and the oracle verifier rejects the transcript, as the executable rejects the wire. A step that
skipped the layer's check would accept the wire, and `busStep_eq` would fail on it.

The Flock phase's transcript decodes and carries its wire. Its oracle verifier's lincheck check
walks the region's block R1CS (`BlockR1CS.rows`), `2^28` terms a matrix, which the executable
replaces by `blake2sRows` (`blake2sRows_eq`, `leanVmFlock_eq`); the check is not evaluated here.
-/

namespace LeanerVMTests.Protocol.Compile

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol LeanerVM.Protocol.Blake2sHash
open LeanerVM.Protocol.LeanIsa LeanerVM.Protocol.Verify LeanerVM.Protocol.Compile
open LeanerVMTests.Protocol.RustProof

/-- The fixture's instance. -/
abbrev I : M3Instance := leanVm fx.prog sizes.1

/-- Its bus phase's conditions. -/
theorem hI : Bus.Conditions I := leanIsa_conditions _ fx.prog sizes.1

/-- The fixture's wires up to the Flock phase. -/
def wires : Except ReadError (BusWire × TableWire × PubWire × FlockWire) :=
  (((do
      let _ ← walkSetup (readerOps (m := Id) blake2sBytes)
      let b ← walkBus (readerOps blake2sBytes) I.μBus I.busClaims
      let t ← walkTables (readerOps blake2sBytes) I.τmax I.tableColumns
      let p ← walkPub (readerOps blake2sBytes) (PublicInput.sentCount I (I.publicLines fx.input))
      let f ← walkFlock (readerOps blake2sBytes) (sizes.1.τ 5)
      return (b, t, p, f)).run'
    ⟨FsState.seed fx.prog fx.input, fx.proof.stream, []⟩).run : Id _)

/-- A layer's descendant flipped. -/
def flipChild (b : BusWire) : BusWire :=
  { b with layers := b.layers.modify 3 fun l ↦
      { l with children := l.children.modify 1 (·.modify 2 (· + 1)) } }

/-- The bus phase on the fixture: the wire decodes, the oracle verifier accepts the transcript
with the executable's totals and columns, and the transcript carries the wire; with a flipped
descendant the wire still decodes, and both reject. -/
def busAgrees : Bool :=
  match wires with
  | .ok (b, _, _, _) =>
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
  | .ok (b, tw, pw, _) =>
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

/-- The Flock phase and the opening claim on the fixture: the wire decodes and the transcript
carries it, a wire with a coefficient missing does not decode, and the opening claim's value is
the pool's values batched. -/
def flockDecodes : Bool :=
  match wires with
  | .ok (b, tw, pw, fw) =>
    match (busStep I hI fx.input b).bind (tableStep I · tw) |>.bind (pubStep I · pw) with
    | some po =>
      let r := flockRegion fx.prog sizes.1 Blake2sFlock.blake2sFlockSpec
      match flockTr? I r po fw,
          flockStep I r rfl blake2sRows po fw with
      | some t, some fo =>
        let w' := flockWireOf r.kBatch t
        w'.point == fw.point && w'.skip == fw.skip && w'.zskip == fw.zskip &&
          w'.zc.map (·.wire) == fw.zc.map (·.wire) && w'.ab == fw.ab && w'.alpha == fw.alpha &&
          w'.lin.map (·.wire) == fw.lin.map (·.wire) && w'.slices == fw.slices &&
          w'.ring == fw.ring &&
          (flockTr? I r po { fw with ring := fw.ring.dropLast }).isNone &&
          let lam : E := E.ofLimbs (K.ofBits 3) (K.ofBits 5) (K.ofBits 7)
          (openingClaim I fo lam).2 == powerBatch (Opening.values I fo) lam
      | _, _ => false
    | none => false
  | .error _ => false

#guard flockDecodes

end LeanerVMTests.Protocol.Compile
