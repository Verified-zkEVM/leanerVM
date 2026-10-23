import LeanerVM.Protocol.Verify.Bus
import LeanerVMTests.Protocol.RustProof

/-!
# The verifier's bus phase on the Rust proof

The chain walk from the seed through the setup and the bus phase reads the fixture's stream and
squeezes the second verifier's challenges: the four fingerprint challenges `α` equal those
`python-verifier/verifier.py` draws on the same proof (traced at leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2`). The grand product's nine quaternary layers replay,
every layer's check passing, to the Python verifier's bus point `ζ`; the bus phase's output, the
oracle verifier's `Bus.busOut` at the leanISA instance, has the Python verifier's three totals
(`verify_bus_balance`). Each check rejects its mutation: a zero count root, a descendant flipped,
a round's wire coefficient flipped (the layer check fails), a changed root, a layer of another
shape than the depth fixes (a round more, a combination challenge fewer), a missing layer, and
a missing boundary value. The radices: one binary layer first at an odd depth.
-/

namespace LeanerVMTests.Protocol.VerifyBus

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol LeanerVM.Protocol.Blake2sHash
open LeanerVM.Protocol.LeanIsa LeanerVM.Protocol.Verify LeanerVMTests.Protocol.RustProof

/-- An element of `E` from its three limbs. -/
def e3 (a b c : ℕ) : E := E.ofLimbs (K.ofBits a) (K.ofBits b) (K.ofBits c)

#guard gkrRadices 18 == [2, 2, 2, 2, 2, 2, 2, 2, 2]
#guard gkrRadices 5 == [1, 2, 2]

/-- The bus phase's wire, read from the seed on the fixture's stream. -/
def busWire (f : Fixture) (s : Sizes) : Except ReadError BusWire :=
  (((do
      let _ ← walkSetup (m := Id) blake2sBytes
      walkBus blake2sBytes (leanVm f.prog s).μBus (leanVm f.prog s).busClaims).run'
    ⟨FsState.seed f.prog f.input, f.proof.stream, []⟩).run : Id _)

/-- The fixture, its sizes and its bus wire, read once. -/
def wire : BusWire :=
  match busWire fx sizes.1 with
  | .ok w => w
  | .error _ => ⟨[], 0, 0, 0, 0, [], []⟩

-- The Python verifier's `α` on this proof.
#guard wire.alpha == [e3 0x481890f000753252 0x514ddcf12eb65a03 0xda6cb672bc44f9e8,
  e3 0xddb1e5dbffa730b9 0xbb99e68574db4257 0xb28265259a16ed89,
  e3 0x9fde87fbd8c52327 0xa054f9ba6af7ee0b 0xa48fe6f696799bd3,
  e3 0x1b7bcb06e8966400 0xad63e96107ed4672 0x3a9030dd70515881]
#guard wire.layers.length == 9
#guard wire.layers.map (·.rounds.length) == [0, 2, 4, 6, 8, 10, 12, 14, 16]
#guard wire.count == e3 0x0006c6c006c6c000 0 0

/-- The grand product replayed from the roots, the layers of `wire` at depth 18. -/
def replay (layers : List GkrLayer) (shared : E := wire.shared) :
    Option (Σ n, Gkr.LayerStmt Unit E 3 n) :=
  replayGkr (gkrRadices 18) 0 ((), (#v[], ![shared, shared, wire.count])) wire.combiner layers

-- The Python verifier's bus point, its first three coordinates.
#guard match replay wire.layers with
  | some ⟨_, ℓ⟩ => ℓ.2.1.toList.length == 18 && ℓ.2.1.toList.take 3 ==
    [e3 0x4edd315f69a937de 0xa35a324df8bd9fb1 0xffe1eeb513c84ec8,
      e3 0xf23219f3500c3dbf 0xdbc2708b53371966 0x5ef55961e04fc53c,
      e3 0xfd8cb86eda6e49cf 0x30f73c0be8dc4ef8 0x05ec069509985420]
  | none => false

-- The bus phase's output has the Python verifier's totals.
#guard match leanVmBus fx.prog sizes.1 fx.input wire with
  | some o => List.ofFn o.2.totals ==
    [e3 0xb1ff1480a4a6124a 0x6973087749f86b01 0x1343f6dd8cc005ad,
      e3 0xc48599d6ee203a1a 0xb4b0d8f1d097d4fe 0x0b490b26341232e4,
      e3 0xcbb229d0f320232b 0x965cfb0a6991c845 0xb65d37c2481e2935]
  | none => false

/-! ## Each check rejects its mutation -/

/-- The wire with layer `i` changed. -/
def withLayer (i : ℕ) (f : GkrLayer → GkrLayer) : BusWire :=
  { wire with layers := wire.layers.modify i f }

-- A zero count root.
#guard (leanVmBus fx.prog sizes.1 fx.input { wire with count := 0 }).isNone
-- A descendant flipped: the layer's check fails.
#guard (replay (withLayer 3 fun l ↦
  { l with children := l.children.modify 1 (·.modify 2 (· + 1)) }).layers).isNone
-- A round's wire coefficient flipped: the decoded rounds miss the layer's check.
#guard (replay (withLayer 5 fun l ↦ { l with rounds := l.rounds.modify 0 fun r ↦
    { r with wire := r.wire.modify 0 (· + 1) } }).layers).isNone
-- The shared root changed.
#guard (replay wire.layers (wire.shared + 1)).isNone
-- A layer of another shape: a round more than its depth, a combination challenge fewer.
#guard (replay (withLayer 2 fun l ↦ { l with rounds := l.rounds ++ l.rounds.take 1 }).layers).isNone
#guard (replay (withLayer 4 fun l ↦ { l with combos := l.combos.dropLast }).layers).isNone
-- A layer missing.
#guard (replay wire.layers.dropLast).isNone
-- A boundary value missing.
#guard (leanVmBus fx.prog sizes.1 fx.input { wire with values := wire.values.dropLast }).isNone

end LeanerVMTests.Protocol.VerifyBus
