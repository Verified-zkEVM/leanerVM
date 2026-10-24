import LeanerVM.Protocol.Compile.Flock
import LeanerVMTests.Protocol.RustProof

/-!
# The verifier's phases are the oracle verifiers' on the Rust proof

The chain walk reads the fixture's wires of the bus phase, the table sumcheck, the public input
and the Flock phase, once, and every check below runs on that one reading (`checks`). Each wire
decodes to a transcript of its phase's oracle protocol, the dropped coefficients rebuilt from the
running claims (`busTr?`, `tableTr?`, `pubTr`, `flockTr?`), and each transcript carries its wire
back. The oracle verifiers of the bus phase, the table sumcheck and the public input accept their
transcripts, with the executable's outputs where both are computed (`busStep_eq`,
`tableStep_eq`, `pubStep_eq`); each phase starts from the oracle verifier's verdict before it.

The decoding checks nothing; the mutations show that the checks are the verifiers'. A flipped
descendant of the grand product and a zero count root decode, and both verifiers reject. A
flipped wire coefficient of a table round decodes into a transcript that carries it, the
reconstruction absorbing the change into the dropped coefficient, and the table's final check
rejects it: the one place a wrong dropped index would show. With a public value missing both
verifiers reject. A Flock wire with a ring coefficient missing does not decode, and with a slice
flipped the executable rejects.

The Flock phase's oracle verifier's lincheck walks the region's block R1CS (`BlockR1CS.rows`),
`2^28` terms a matrix, which the executable replaces by `blake2sRows` (`blake2sRows_eq`,
`leanVmFlock_eq`); that check is evaluated on the executable's side only.
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

/-- The first round's first wire coefficient flipped. -/
def flipCoeff (w : TableWire) : TableWire :=
  { w with rounds := w.rounds.modify 0 fun r ↦ { r with wire := r.wire.modify 0 (· + 1) } }

/-- The bus phase on a wire that decodes: its oracle verifier rejects the transcript, and the
executable rejects the wire. -/
def busRejects (b : BusWire) : Bool :=
  match busTr? I fx.input b with
  | some t => !(busPhase I hI).front.check fx.input t && (busStep I hI fx.input b).isNone
  | none => false

/-- **The agreement on the fixture**, each check named, computed once; each phase starts from the
verdict before it. -/
def checks : List (String × Bool) :=
  match wires with
  | .error _ => [("the chain walk reads the wires", false)]
  | .ok (b, tw, pw, fw) =>
    let bf := (busPhase I hI).front
    match busTr? I fx.input b, busStep I hI fx.input b with
    | some t, some bo =>
      let bus := [
        ("bus: the oracle verifier accepts", bf.check fx.input t),
        ("bus: with the executable's totals",
          List.ofFn (bf.out fx.input t).2.totals == List.ofFn bo.2.totals),
        ("bus: and columns", (bf.out fx.input t).2.columns.toList.map (·.value) ==
          bo.2.columns.toList.map (·.value)),
        ("bus: the transcript carries the wire",
          (busWireOf I t).alpha == b.alpha && (busWireOf I t).count == b.count &&
            (busWireOf I t).values == b.values &&
            ((busWireOf I t).layers.map fun l ↦ (l.rounds.map (·.wire), l.children, l.combos)) ==
              (b.layers.map fun l ↦ (l.rounds.map (·.wire), l.children, l.combos))),
        ("bus: a flipped descendant decodes, both reject", busRejects (flipChild b)),
        ("bus: a zero count root decodes, both reject", busRejects { b with count := 0 })]
      let tf := (TableSumcheck.tableSumcheck I).front
      match tableTr? I bo tw, tableTr? I bo (flipCoeff tw) with
      | some tt, some tt' =>
        let tout := tf.out bo tt
        let table := [
          ("table: the oracle verifier accepts", tf.check bo tt),
          ("table: the transcript carries the wire",
            (tableWireOf I tt).xi == tw.xi &&
              (tableWireOf I tt).rounds.map (·.wire) == tw.rounds.map (·.wire) &&
              (tableWireOf I tt).finals == tw.finals),
          ("table: a flipped wire coefficient decodes and is carried, the oracle verifier rejects",
            (tableWireOf I tt').rounds.map (·.wire) == (flipCoeff tw).rounds.map (·.wire) &&
              !tf.check bo tt')]
        let pf := (deployedPublicInputPhase I).front
        let pw' : PubWire := { pw with values := pw.values.dropLast }
        let pub := [
          ("pub: the oracle verifier accepts", pf.check tout (pubTr pw)),
          ("pub: a value missing, both reject",
            !pf.check tout (pubTr pw') && (pubStep I tout pw').isNone)]
        let po := pf.out tout (pubTr pw)
        let r := flockRegion fx.prog sizes.1 Blake2sFlock.blake2sFlockSpec
        let flock := match flockTr? I r po fw with
          | some ft =>
            let w' := flockWireOf r.kBatch ft
            [("flock: the transcript carries the wire",
                w'.point == fw.point && w'.skip == fw.skip && w'.zskip == fw.zskip &&
                  w'.zc.map (·.wire) == fw.zc.map (·.wire) && w'.ab == fw.ab &&
                  w'.alpha == fw.alpha && w'.lin.map (·.wire) == fw.lin.map (·.wire) &&
                  w'.slices == fw.slices && w'.ring == fw.ring),
              ("flock: a ring coefficient missing does not decode",
                (flockTr? I r po { fw with ring := fw.ring.dropLast }).isNone),
              ("flock: a flipped slice, the executable rejects",
                (flockStep I r rfl blake2sRows po
                  { fw with slices := fw.slices.modify 0 (· + 1) }).isNone)]
          | none => [("flock: the wire decodes", false)]
        bus ++ table ++ pub ++ flock
      | _, _ => bus ++ [("table: the wires decode", false)]
    | _, _ => [("bus: the wire decodes and the executable accepts", false)]

#guard checks.all (·.2)

end LeanerVMTests.Protocol.Compile
