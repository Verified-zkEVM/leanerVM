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
against the native terminal at the slices, `Flock.linCheck`'s expression on the statement with
the circuit's matrices evaluated by a supplied walk `rows` (`Flock.linTerminalWith`; the
verifier's is `blake2sRows`, equal to the region's block R1CS's walk of `2^28` terms a matrix by
`blake2sRows_eq`); the point it ends at (`Flock.linNext`); and the switched weighted claim
`⟨W, q⟩ = Σ_i g^i Φ(s_i)` lifted into the stack (`Flock.ringWeight`, `Flock.ringTarget`,
`FlockPhase.finish`).
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

variable {n : Type → Type} [Monad n] (ops : ChainOps n)

/-- The Flock phase's reads for `2 ^ k` compressions: `k + 1` drawn coordinates, `8 + k`
zerocheck rounds and `8` lincheck rounds (`flockParams`). -/
def walkFlock (k : ℕ) : n FlockWire := do
  let point ← samples ops (k + 1)
  let skip ← ops.nextScalars (2 ^ Flock.kSkip)
  let zskip ← ops.sample
  let zc ← readRounds ops 2 (Flock.kIn + k)
  let ab ← ops.nextScalars 2
  let alpha ← ops.sample
  let lin ← readRounds ops 2 Flock.kIn
  let slices ← ops.nextScalars (2 ^ Flock.kSkip)
  let ring ← samples ops 6
  return ⟨point, skip, zskip, zc, ab, alpha, lin, slices, ring⟩

end Walk

/-! ## The algebra -/

variable (I : M3Instance)

/-- The Flock phase's algebra on its wire, on the instance's region `r`, the circuit's matrices
evaluated by the walk `rows` (the region's own `BlockR1CS.rows`, or a faster walk of the same
matrices): the oracle verifier's steps, its lincheck check `Flock.linCheck` with
`Flock.linTerminalWith rows` for the region's walk, and the column claims handed on with the
switched weighted claim. -/
def flockStep (r : FlockRegion I.toShape) (hr : I.flock = some r)
    (rows : CMlPolynomialEval E (Flock.kSkip + Flock.kIn) →
      CMlPolynomialEval E (Flock.kSkip + Flock.kIn) × CMlPolynomialEval E (Flock.kSkip + Flock.kIn))
    (s : I.Stmt × PubOut I) (w : FlockWire) : Option (I.Stmt × FlockOut I) := do
  let P := flockParams r.kBatch
  let v ← RoundPoly.ofList? P.nRand w.point
  let msg ← RoundPoly.ofList? (2 ^ P.s) w.skip
  let pt := P.point v
  let (claimZ, χ) ← replayRounds 2 (fun j ↦ pt[j]?) 0 (Flock.skipClaim P.nodes msg w.zskip) w.zc
  let χ ← RoundPoly.ofList? (P.m + P.κ) χ
  let ab ← RoundPoly.ofList? 2 w.ab
  let t := Flock.termNext (S := I.Stmt × PubOut I) ((s, pt, w.zskip), (χ, claimZ)) ab
  let st₀ := Flock.alphaNext t w.alpha
  let (claimL, c) ← replayRounds 2 (fun _ ↦ none) 0 st₀.2.2 w.lin
  let c ← RoundPoly.ofList? P.m c
  let sv ← RoundPoly.ofList? (2 ^ P.s) w.slices
  let st : SumcheckRound.Stmt (Flock.LinX (I.Stmt × PubOut I) E (P.m + P.κ)) E P.m :=
    (st₀.1, (c, claimL))
  if st.2.2 ≠ Flock.linTerminalWith rows P.nodes P.cpos st.1.1.1.2.2 (lowVec st.1.1.2.1) st.1.2
      st.2.1.reverse sv then none
  let out := Flock.linNext P st sv
  let fs ← RoundPoly.ofList? 6 w.ring
  return FlockPhase.finish r hr out.1 (Flock.ringWeight P 5 (FlockPhase.lift r) out.2.1 fs)
    (Flock.ringTarget P 5 (algebraMap K E) g out.2.2 fs)

end Verify

end
end LeanerVM.Protocol
