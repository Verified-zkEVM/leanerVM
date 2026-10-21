import LeanVM.E2E.Runs
import LeanXmss.Statement
import Sphincs.StatementDet

/-!
# Tests: answered runs and the schemes' verification

* The end lemmas rest on Lean's three axioms.
* **Answered runs are cached runs, on a toy computation.** Two queries a lookup answers, run with
  the lazy random oracle from a cache agreeing with it, return the lookup's result and keep the
  cache.
* **The counted form applies to the schemes' `countedOracle`**: the final verification of
  `LeanXmss.Security.gameCore` and of `Sphincs.Security.Det.gameCoreDet`, behind their counted
  oracle, returns `true` from a cache holding the log a valid signature is answered by.
-/

namespace LeanVMTests.E2E.Runs

open OracleComp OracleSpec LeanVM.E2E LeanVM.Node LeanVM.Protocol.Compile.Rom

/--
info: 'LeanVM.E2E.run_simulateQ_randomOracle_of_answered' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanVM.E2E.run_simulateQ_randomOracle_of_answered

/--
info: 'LeanVM.E2E.run_simulateQ_withAddCost_liftM_of_answered' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanVM.E2E.run_simulateQ_withAddCost_liftM_of_answered

/--
info: 'LeanVM.E2E.xmssVerifyWith_eq_simulateQ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanVM.E2E.xmssVerifyWith_eq_simulateQ

/--
info: 'LeanVM.E2E.sphincsVerifyWith_eq_simulateQ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanVM.E2E.sphincsVerifyWith_eq_simulateQ

/--
info: 'LeanVM.E2E.xmssVerifyWith_some_blake2s' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanVM.E2E.xmssVerifyWith_some_blake2s

/--
info: 'LeanVM.E2E.sphincsVerifyWith_some_blake2s' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanVM.E2E.sphincsVerifyWith_some_blake2s

/--
info: 'LeanVM.E2E.run_verify_of_xmssVerifyWith' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanVM.E2E.run_verify_of_xmssVerifyWith

/--
info: 'LeanVM.E2E.run_verify_of_sphincsVerifyWith' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanVM.E2E.run_verify_of_sphincsVerifyWith

/--
info: 'LeanVM.E2E.run_countedVerify_of_xmssVerifyWith' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanVM.E2E.run_countedVerify_of_xmssVerifyWith

/--
info: 'LeanVM.E2E.run_countedVerify_of_sphincsVerifyWith' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanVM.E2E.run_countedVerify_of_sphincsVerifyWith

/-! ## A toy computation -/

/-- Two queries, compared. -/
def toy : OracleComp BitsSpec Bool := do
  let a ← query (spec := BitsSpec) [1]
  let b ← query (spec := BitsSpec) [2]
  return a == b

/-- A lookup answering both points with `0`. -/
def toyLookup : QueryImpl BitsSpec Option := fun x ↦ if x = [1] ∨ x = [2] then some 0 else none

/-- A cache answering both points with `0`, and a third one. -/
def toyCache : QueryCache BitsSpec :=
  QueryCache.ofFn fun x ↦ if x = [1] ∨ x = [2] ∨ x = [3] then some 0 else none

/-- The lookup's run of the toy computation returns `true`. -/
example : simulateQ toyLookup toy = some true := by decide

/-- So the lazy random oracle, from the cache, returns `true` and keeps the cache. -/
example : (simulateQ BitsSpec.randomOracle toy).run toyCache = pure (true, toyCache) :=
  run_simulateQ_randomOracle_of_answered toyLookup toyCache
    (fun x u h ↦ by
      simp only [toyLookup] at h
      split_ifs at h with hx
      cases h
      rcases hx with rfl | rfl <;> decide)
    toy true (by decide)

/-! ## The schemes' counted oracle -/

/-- leanXMSS: the final verification of `gameCore`, behind `countedOracle`, from a cache holding
the log `ℓ` that answers a valid signature, returns `true`. -/
example (ℓ : Log) (c : QueryCache LeanXmss.HashSpec) (hc : CacheHas c (look ℓ))
    (pk : LeanXmss.PublicKey) (msg : LeanXmss.Message) (σ : LeanXmss.Signature)
    (h : xmssVerifyWith (look ℓ) pk msg σ = some true) :
    ∃ w, ((simulateQ LeanXmss.Security.countedOracle
      (liftM (LeanXmss.Concrete.verify pk msg σ : OracleComp LeanXmss.HashSpec Bool) :
        OracleComp LeanXmss.OracleWorld Bool)).run).run c = pure ((true, w), c) :=
  run_countedVerify_of_xmssVerifyWith _ _ hc h

/-- leanSPHINCS: the final verification of `gameCoreDet`, behind `countedOracle`, from a cache
holding the log `ℓ` that answers a valid signature, returns `true`. -/
example (ℓ : Log) (c : QueryCache Sphincs.HashSpec) (hc : CacheHas c (look ℓ))
    (pk : Sphincs.PublicKey) (msg : Sphincs.Message) (σ : Sphincs.Signature)
    (h : sphincsVerifyWith (look ℓ) pk msg σ = some true) :
    ∃ w, ((simulateQ Sphincs.Security.countedOracle
      (liftM (Sphincs.Concrete.verify pk msg σ : OracleComp Sphincs.HashSpec Bool) :
        OracleComp Sphincs.OracleWorld Bool)).run).run c = pure ((true, w), c) :=
  run_countedVerify_of_sphincsVerifyWith _ _ hc h

/-- The log's own cache holds it. -/
example (ℓ : Log) : CacheHas (bitsCache (look ℓ)) (look ℓ) := cacheHas_bitsCache _

end LeanVMTests.E2E.Runs
