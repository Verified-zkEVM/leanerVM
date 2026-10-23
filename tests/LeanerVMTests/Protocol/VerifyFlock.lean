import LeanerVM.Protocol.Verify.Flock
import LeanerVMTests.Protocol.VerifyTables

/-!
# The verifier's Flock phase on the Rust proof

After the public input, the chain walk reads the Flock phase: the four drawn coordinates of the
zerocheck point (`2^3` compressions), the 64 skip values, `z_skip`, eleven zerocheck rounds of
two wire coefficients, `â, b̂`, `α`, eight lincheck rounds, the 64 slices and the six
ring-switching coefficients. The algebra on the fixture: the lincheck's terminal, one forward
walk of the BLAKE2s circuit (`blake2sRows`), equals the running claim, and the phase hands on
the column claims with the switched weighted claim, whose value is the Python verifier's
ring-switching target (`python-verifier/verifier.py:1336-1349`, traced at leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2`). Each check rejects its mutation: a slice flipped
(the terminal moves), a skip value flipped, a zerocheck round's coefficient flipped, `â`
flipped, a lincheck round's coefficient flipped, and a missing ring-switching coefficient.

**The walk against the circuit.** At column weights from a seed, `blake2sRows` agrees with the
rows of `blake2sCircuit`'s matrices, read off its gates entry by entry, at rows of every kind:
the constant, a chaining-value input, a message input, a counter input, an output bit, the first
majority, ripple and carry gates of a mixing step, a gate of the last step, and a padding row.
On GF(2) forms the walk's rows are the gates' forms at all `2^14` rows (`walkMismatches`). The
walk uses only `+` and `0`, so each of its rows at `E` is a sum of weights with natural
multiplicities, which characteristic two reduces to the form the walk returns on GF(2).
-/

namespace LeanerVMTests.Protocol.VerifyFlock

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol LeanerVM.Protocol.Blake2sHash
open LeanerVM.Protocol.LeanIsa LeanerVM.Protocol.Verify LeanerVMTests.Protocol.RustProof
open LeanerVMTests.Protocol.VerifyTables ProductCircuit Blake2sCircuit CompPoly

/-- An element of `E` from its three limbs. -/
def e3 (a b c : ℕ) : E := E.ofLimbs (K.ofBits a) (K.ofBits b) (K.ofBits c)

/-! ## The walk against the circuit -/

/-- Column weights from a seed, by a linear congruence on the limbs. -/
def weights (seed : ℕ) : CMlPolynomialEval E (Flock.kSkip + Flock.kIn) :=
  Vector.ofFn fun j ↦ e3 ((seed + 7919 * j.val) * 2654435761 % 2 ^ 64)
    ((seed * 31 + j.val) * 40503 % 2 ^ 64) ((j.val * j.val + seed) % 2 ^ 64)

/-- A form at the weights: the sum of the weights of its positions. -/
def formAt (L : Form (Flock.kSkip + Flock.kIn))
    (w : CMlPolynomialEval E (Flock.kSkip + Flock.kIn)) : E :=
  ∑ j : Fin (2 ^ (Flock.kSkip + Flock.kIn)), if L.getLsbD j then w[j] else 0

/-- Row `k` of the circuit's two matrices at the weights, read off its gates. -/
def circuitRow (k : Fin (2 ^ (Flock.kSkip + Flock.kIn)))
    (w : CMlPolynomialEval E (Flock.kSkip + Flock.kIn)) : E × E :=
  let g := blake2sCircuit.rowOf k
  (formAt g.a w, formAt g.b w)

/-- The rows the walk is checked at. -/
def sampleRows : List ℕ :=
  [512, 3, 700, 1160, 261, 1280, 1311, 1341, 1280 + 184 * 79 + 183, 16100]

#guard
  let w := weights 11
  let r := blake2sRows w
  sampleRows.all fun k ↦
    if h : k < 2 ^ (Flock.kSkip + Flock.kIn) then circuitRow ⟨k, h⟩ w == (r.1[k], r.2[k])
    else false

/-! ## The walk against the circuit, as forms -/

/-- A GF(2) linear form over the block's positions, `+` its XOR. -/
structure Gf2Form where
  /-- The positions with coefficient `1`. -/
  bits : Form (Flock.kSkip + Flock.kIn)

instance : Add Gf2Form := ⟨fun a b ↦ ⟨a.bits ^^^ b.bits⟩⟩

instance : Zero Gf2Form := ⟨⟨0⟩⟩

/-- The walk on forms: input `j` the form of position `j`, so row `k` of each side is the form
the walk sums there. -/
def walkForms : Array Gf2Form × Array Gf2Form :=
  blake2sRowsOf ((Array.range (2 ^ (Flock.kSkip + Flock.kIn))).map fun j ↦
    ⟨Form.var (pos j)⟩)

/-- The rows at which the walk's two forms are not the gates' (`rowOf`): none. -/
def walkMismatches (rows : List ℕ := List.range (2 ^ (Flock.kSkip + Flock.kIn))) : List ℕ :=
  let r := walkForms
  rows.filter fun k ↦
    let g := blake2sCircuit.rowOf (pos k)
    !((r.1.getD k 0).bits == g.a && (r.2.getD k 0).bits == g.b)

#guard walkMismatches == []

/-! ## The phase on the fixture -/

/-- The fixture's wires up to the Flock phase. -/
def flockWire (f : Fixture) (s : Sizes) : Except ReadError FlockWire :=
  let I := leanVm f.prog s
  (((do
      let _ ← walkSetup (readerOps (m := Id) blake2sBytes)
      let _ ← walkBus (readerOps blake2sBytes) I.μBus I.busClaims
      let _ ← walkTables (readerOps blake2sBytes) I.τmax I.tableColumns
      let _ ← walkPub (readerOps blake2sBytes) (PublicInput.sentCount I (I.publicLines f.input))
      walkFlock (readerOps blake2sBytes) (s.τ 5)).run'
    ⟨FsState.seed f.prog f.input, f.proof.stream, []⟩).run : Id _)

#guard match flockWire fx sizes.1 with
  | .ok w => w.point.length == 4 && w.zc.length == 11 && w.lin.length == 8 &&
    w.skip.length == 64 && w.slices.length == 64 && w.ring.length == 6
  | .error _ => false

/-- The Flock phase's algebra on the fixture, its wire changed by each of `fws`: the switched
claim's value for each, or `none`. -/
def flockValues (fws : List (FlockWire → FlockWire)) : List (Option E) :=
  let f := fx
  let s := sizes.1
  match wires f s, flockWire f s with
  | .ok (b, t, p), .ok w =>
    match pubOut f s b t p with
    | none => []
    | some po => fws.map fun fw ↦ do
      let w := fw w
      let fo ← flockStep (leanVm f.prog s) (flockRegion f.prog s Blake2sFlock.blake2sFlockSpec)
        rfl blake2sRows po w
      match fo.2.weighted.toList with
      | [c] => some c.value
      | _ => none
  | _, _ => []

/-- A round with its first wire coefficient flipped. -/
def flipRound (r : Round) : Round := { r with wire := r.wire.modify 0 (· + 1) }

-- The honest wire hands on the Python verifier's ring-switching target, and each mutation is
-- rejected: a slice, a skip value, a zerocheck round, `â`, a lincheck round, a missing
-- coefficient.
#guard flockValues [id,
    fun w ↦ { w with slices := w.slices.modify 9 (· + 1) },
    fun w ↦ { w with skip := w.skip.modify 5 (· + 1) },
    fun w ↦ { w with zc := w.zc.modify 3 flipRound },
    fun w ↦ { w with ab := w.ab.modify 0 (· + 1) },
    fun w ↦ { w with lin := w.lin.modify 6 flipRound },
    fun w ↦ { w with ring := w.ring.dropLast }] ==
  [some (e3 0x578bd01cf985cc5a 0x8e85bcf294c60233 0xe0c0c1a2f9ff485d),
    none, none, none, none, none, none]

end LeanerVMTests.Protocol.VerifyFlock
