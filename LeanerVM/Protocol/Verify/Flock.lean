/-
  LeanerVM.Protocol.Verify.Flock

  The executable verifier's Flock phase: the chain walk's reads of the zerocheck, the lincheck
  and the ring-switching coefficients, and the algebra on them, which replays the oracle
  verifier's steps and hands on the switched weighted claim.
-/

module

public import LeanerVM.Protocol.Verify.Tables
public import LeanerVM.Protocol.Flock
public import LeanerVM.Protocol.Verify.Blake2sWalk

/-!
# The Flock phase in the verifier

Written from Annex C and Annex A (the oracle verifier of `LeanerVM.Protocol.Flock`, the
components of `LeanerVM.Protocol.ToArkLib.Flock`) and transcribed for the stream order from the
pinned leanVM (`a386121f84292f6fa663aaa3e570c15bc0240ea2`): `crates/lean_vm/src/hash_flock.rs`
(`verify_reduction`, `ring_switch_verify`), `crates/flock/src/zerocheck.rs`,
`crates/flock/src/lincheck.rs`, `crates/pcs/src/stack_open.rs:500-512`, as the second verifier
writes them out (`python-verifier/verifier.py:1134-1350`).

**The walk** (`walkFlock`): the `nRand` drawn coordinates of the zerocheck point (after the seven
fixed ones); the 64 values of `P` on the coset of the skip domain; `z_skip`; the `m + κ`
normalized zerocheck rounds of a quadratic cofactor, two wire coefficients each (`c_0`
dropped), within-block coordinates first; `â, b̂`; the lincheck's `α`; its `m` plain rounds of a
quadratic, two wire coefficients each (`c_1` dropped); the 64 slices; the six ring-switching
coefficients.

**The algebra** (`flockStep`), step by step the oracle verifier's: the point (`Params.point`);
the claim `P(z_skip)` interpolated from the 64 assumed zeros and the values sent
(`Flock.skipClaim`); the zerocheck rounds decoded against the running claim with the point's
equality weights; `ĉ = â·b̂ − R` (`Flock.termNext`); the lincheck's claim
`v_a + α v_b + α² v_c + α³` (`Flock.alphaNext`); its rounds decoded; the check of the running claim
against the native terminal at the slices (`Flock.linCheck`, its terminal `flockTerminal` one
forward walk of the region's circuit, `BlockR1CS.rows`: the evaluation of the BLAKE2s matrices,
settled outside the step); the point it ends at
(`Flock.linNext`); and the switched weighted claim `⟨W, q⟩ = Σ_i g^i Φ(s_i)` lifted into the
stack (`Flock.ringWeight`, `Flock.ringTarget`, `FlockPhase.finish`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa CompPoly

@[expose] public section

namespace Verify

/-! ## The wire -/

/-- The Flock phase as read. -/
structure FlockWire where
  /-- The drawn coordinates of the zerocheck point. -/
  point : List E
  /-- `P` on the coset of the skip domain. -/
  skip : List E
  /-- The skip challenge. -/
  zskip : E
  /-- The zerocheck's rounds. -/
  zc : List Round
  /-- The terminal values `â, b̂`. -/
  ab : List E
  /-- The lincheck's batching challenge. -/
  alpha : E
  /-- The lincheck's rounds. -/
  lin : List Round
  /-- The slices. -/
  slices : List E
  /-- The ring-switching coefficients. -/
  ring : List E
  deriving Inhabited

/-! ## The walk -/

section Walk

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- The Flock phase's reads for `2 ^ k` compressions: `k + 1` drawn coordinates, `8 + k`
zerocheck rounds and `8` lincheck rounds (`flockParams`). -/
def walkFlock (k : ℕ) : Walk m FlockWire := do
  let point ← samples H (k + 1)
  let skip ← Reader.nextScalars H (2 ^ Flock.kSkip)
  let zskip ← Reader.sample H
  let zc ← readRounds H 2 (Flock.kIn + k)
  let ab ← Reader.nextScalars H 2
  let alpha ← Reader.sample H
  let lin ← readRounds H 2 Flock.kIn
  let slices ← Reader.nextScalars H (2 ^ Flock.kSkip)
  let ring ← samples H 6
  return ⟨point, skip, zskip, zc, ab, alpha, lin, slices, ring⟩

end Walk

/-! ## The algebra -/

variable (I : M3Instance)

/-- The lincheck's native terminal on the wire, for `2 ^ k` blocks of a circuit whose matrices
the walk `rows` evaluates (`Flock.linTerminalWith`; the region's own `BlockR1CS.rows`, or a
faster walk of the same matrices): at the skip challenge, the zerocheck's within-block point, the
lincheck's `α` and point (its challenges reversed, the variables bound highest first), and the
slices. -/
def flockTerminal (k : ℕ)
    (rows : CMlPolynomialEval E (Flock.kSkip + Flock.kIn) →
      CMlPolynomialEval E (Flock.kSkip + Flock.kIn) × CMlPolynomialEval E (Flock.kSkip + Flock.kIn))
    (w : FlockWire) : Option E := do
  let P := flockParams k
  let χ ← vec? (P.m + P.κ) (w.zc.map (·.chal))
  let p ← vec? P.m (w.lin.map (·.chal)).reverse
  let sv ← vec? (2 ^ P.s) w.slices
  return Flock.linTerminalWith rows P.nodes P.cpos w.zskip (lowVec χ) w.alpha p sv

/-- The Flock phase's algebra on its wire, on the instance's region `r`, with the lincheck's
native terminal `terminal` settled outside (`flockTerminal`): the oracle verifier's steps, and
the column claims handed on with the switched weighted claim. -/
def flockStep (r : FlockRegion I.toShape) (hr : I.flock = some r) (terminal : E)
    (s : I.Stmt × PubOut I) (w : FlockWire) : Option (I.Stmt × FlockOut I) := do
  let P := flockParams r.kBatch
  let v ← vec? P.nRand w.point
  let msg ← vec? (2 ^ P.s) w.skip
  let pt := P.point v
  let (claimZ, χ) ← replayRounds 2 (fun j ↦ pt[j]?) 0 (Flock.skipClaim P.nodes msg w.zskip) w.zc
  let χ ← vec? (P.m + P.κ) χ
  let ab ← vec? 2 w.ab
  let t := Flock.termNext (S := I.Stmt × PubOut I) ((s, pt, w.zskip), (χ, claimZ)) ab
  let st₀ := Flock.alphaNext t w.alpha
  let (claimL, c) ← replayRounds 2 (fun _ ↦ none) 0 st₀.2.2 w.lin
  let c ← vec? P.m c
  let sv ← vec? (2 ^ P.s) w.slices
  let st : SumcheckRound.Stmt (Flock.LinX (I.Stmt × PubOut I) E (P.m + P.κ)) E P.m :=
    (st₀.1, (c, claimL))
  if st.2.2 ≠ terminal then none
  let out := Flock.linNext P st sv
  let fs ← vec? 6 w.ring
  return FlockPhase.finish r hr out.1 (Flock.ringWeight P 5 (FlockPhase.lift r) out.2.1 fs)
    (Flock.ringTarget P 5 (algebraMap K E) g out.2.2 fs)

end Verify

end
end LeanerVM.Protocol
