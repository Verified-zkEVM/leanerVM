/-
  LeanerVM.Protocol.Verify.Tables

  The executable verifier's table sumcheck and public-input phases: the chain walk's reads and
  the algebra on them, which replays the oracle verifiers' checks and pools.
-/

module

public import LeanerVM.Protocol.Verify.Bus
public import LeanerVM.Protocol.TableSumcheck
public import LeanerVM.Protocol.PublicInput

/-!
# The table sumcheck and the public input in the verifier

Written from the specification (§5.5 and §8.2, the oracle verifiers of
`LeanerVM.Protocol.TableSumcheck` and `LeanerVM.Protocol.PublicInput`) and transcribed for the
stream order from the pinned leanVM (`a386121f84292f6fa663aaa3e570c15bc0240ea2`):
`crates/lean_vm/src/cpu/mod.rs:715-756` and `crates/lean_vm/src/constraints.rs:243-291`, as the
second verifier writes them out (`python-verifier/verifier.py:577-610, 1388-1402`).

**The table sumcheck.** The walk (`walkTables`) squeezes the batching challenge `ξ`, reads `τ_max`
plain rounds of a cubic, each three wire coefficients (`c_1` dropped) and a challenge, then one
value per column of each sumcheck table, table by table. The algebra (`tableStep`) is the oracle
verifier's: the target is the claimed values (zero for each constraint, then the three sides'
totals) batched by the powers of `ξ`, never sent; the rounds are decoded against the running
claim; the final check is `Sumcheck.finalCheck` of the table summand, the formula at the reversed
challenges (the variables are bound highest first); the output is `TableSumcheck.tableOut`.

**The public input.** The walk (`walkPub`) squeezes `r` and reads one value per sent public line
(two for leanVM). The algebra (`pubStep`) is the deployed verifier of the phase
(`PublicInput.deployedVerifier`), through its guarded form: one value per sent line and the check
on the words (`PublicInput.accepts` of `PublicInput.checkWords`, `cpu/mod.rs:752-755`), and the
claims pooled from the values sent (`PublicInput.verdict` of `PublicInput.pooledFrom`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa CompPoly

@[expose] public section

namespace Verify

/-! ## The wires -/

/-- The table sumcheck as read. -/
structure TableWire where
  /-- The batching challenge `ξ`. -/
  xi : E
  /-- The rounds, highest variable first. -/
  rounds : List Round
  /-- The values of the sumcheck tables' columns at the final point. -/
  finals : List E
  deriving Inhabited

/-- The public-input phase as read. -/
structure PubWire where
  /-- The challenge `r`. -/
  r : E
  /-- The values of the sent lines at `r`. -/
  values : List E
  deriving Inhabited

/-! ## The walks -/

section Walk

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- The table sumcheck's reads: `ξ`, `τmax` rounds of three wire coefficients, `nCols` values. -/
def walkTables (τmax nCols : ℕ) : Walk m TableWire := do
  let xi ← Reader.sample H
  let rounds ← readRounds H 3 τmax
  let finals ← Reader.nextScalars H nCols
  return ⟨xi, rounds, finals⟩

/-- The public-input phase's reads: `r`, then `nSent` values. -/
def walkPub (nSent : ℕ) : Walk m PubWire := do
  let r ← Reader.sample H
  let values ← Reader.nextScalars H nSent
  return ⟨r, values⟩

end Walk

/-! ## The algebra -/

variable (I : M3Instance)

/-- The table sumcheck's algebra on its wire: the derived target, the rounds decoded, the final
check of the oracle verifier, and its output. -/
def tableStep (s : I.Stmt × BusOut I) (w : TableWire) : Option (I.Stmt × TableOut I) := do
  let (claim, cs) ← replayRounds 3 (fun _ ↦ none) 0
    (powerBatch (TableSumcheck.claimed I s) w.xi) w.rounds
  let c ← RoundPoly.ofList? I.τmax cs
  let v ← RoundPoly.ofList? I.tableColumns w.finals
  let st : SumcheckRound.Stmt (TableSumcheck.Data I) E I.τmax := ((s, w.xi), (c, claim))
  if Sumcheck.finalCheck (TableSumcheck.tableSummand I) st v then
    some (TableSumcheck.tableOut I st v)
  else none

/-- The public-input phase's algebra on its wire: the deployed verifier's guarded form
(`PublicInput.deployedGuarded`), its check `accepts` of the words with one value per sent line
and its `verdict`, the claims pooled from the values sent. -/
def pubStep (s : I.Stmt × TableOut I) (w : PubWire) : Option (I.Stmt × PubOut I) :=
  if PublicInput.accepts I (PublicInput.checkWords I) s w.r w.values then
    some (PublicInput.verdict I (PublicInput.pooledFrom I) s w.r w.values)
  else none

end Verify

end
end LeanerVM.Protocol
