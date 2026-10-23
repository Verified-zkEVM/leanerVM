import LeanerVM.Protocol.Whir.Cached
import LeanerVMTests.Protocol.WhirOpen

/-!
# Differential tests of WHIR's cached prover

The cached prover of WHIR's opening is proved to run as the honest one
(`Component.Cached.run_eq`); these `#guard`s check the compiled code on the opening tests' chain
of two levels, at challenge sequences a xorshift draws.

* **The stored word.** The rows of `wordFast` (the lanes encoded by the additive transform) are
  `wordOf`'s at every position, on the first level's table.
* **The bound table.** The table bound on its lane coordinates to the fold point, renamed, is the
  folded table.
* **Runs.** The transcripts of the cached prover and of the honest one, at two seeds, are accepted
  by the verifier; the cached prover with the stack's word replaced by another's is rejected.
-/

namespace LeanerVMTests.Protocol.WhirCached

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Whir CompPoly CMlPolynomialEval
open OracleComp OracleSpec ProtocolSpec
open LeanerVMTests.Protocol.WhirOpenToy

/-- A xorshift step. -/
private def xs (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

/-- Uniform samples read off the words of a xorshift. -/
private def xsImpl : QueryImpl unifSpec (StateM UInt64) :=
  fun n st ↦ (Fin.ofNat (n + 1) st.toNat, xs st)

/-- Run a prover at the challenges a xorshift draws from `seed`. -/
private def runAt {S W S' W' : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)] (P : Prover []ₒ S W S' W' pSpec) (s : S) (w : W)
    (seed : UInt64) : pSpec.FullTranscript × S' × W' :=
  (simulateQ xsImpl
    (simulateQ (QueryImpl.add (fun t ↦ isEmptyElim t) challengeQueryImpl) (P.run s w))).run' seed

/-! ## The stored word and the bound table -/

#guard (List.finRange (2 ^ (κ0 + sh0.R))).all fun y ↦
  (wordFast sh0.ℓ κ0 sh0.R sh0.t f0).row y == (wordOf sh0.ℓ κ0 sh0.R sh0.t f0).row y

#guard castLanes (ProductSum.lowCache f0 sh0.ℓ r0) == foldTable f0 r0

/-! ## Runs -/

/-- Whether the verifier accepts a run of the cached or the honest prover at a seed, on the
statement and an oracle. -/
private def acceptsRun (cached : Bool) (seed : UInt64)
    (o : ∀ i, OneW sh0 κ0 i := oracle0) : Bool :=
  let tr := if cached then (runAt (whirOpenCached sh0 κ0 ladder).toProver (stmt0, o) stackQ seed).1
    else (runAt (whirOpen sh0 κ0 ladder).red.prover (stmt0, o) stackQ seed).1
  verifier.check (stmt0, o) tr

#guard [3, 5].all fun seed ↦ acceptsRun true seed && acceptsRun false seed

/-- The honest word of another table. -/
private def otherWord : ∀ i, OneW sh0 κ0 i := fun _ ↦
  wordOf sh0.ℓ κ0 sh0.R sh0.t (relayout (Vector.ofFn fun i ↦ stackQ[i] + 1))

#guard [3, 5].all fun seed ↦ !acceptsRun true seed otherWord

end LeanerVMTests.Protocol.WhirCached
