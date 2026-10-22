import LeanVM.E2E.Vis.End

/-!
# Tests: W-vis P7c and P6, the hybrid and the end theorem's assembly

The break at V_I's trace (`BreaksVis`): it needs V_I's acceptance and a claim, an unbacked DA claim
is one at the empty trace, and a break against the final log is one at every trace it answers.
The hybrid over keys and the assembly up to `sec0ErrorGame` rest on Lean's three standard axioms
only.
-/

open LeanVM LeanVM.Node LeanVM.E2E LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom

section

variable {nx ns : ℕ} [Sphincs.Params]

-- no break without V_I's acceptance
example (z : GameOutcome nx ns) (tr : Log) (h : z.accepted = false) : ¬ BreaksVis z tr := by
  rintro ⟨ha, -⟩
  simp [h] at ha

-- no break on a root statement without claims
example (z : GameOutcome nx ns) (tr : Log) (hx : z.statement.claims.xmss = [])
    (hs : z.statement.claims.sphincs = []) (hd : z.statement.claims.da = []) : ¬ BreaksVis z tr := by
  rintro ⟨-, (⟨j, msg, hm, -⟩ | ⟨j, msg, hm, -⟩) | ⟨c, hc, -⟩⟩
  · simp [hx] at hm
  · simp [hs] at hm
  · simp [hd] at hc

-- an accepted DA claim is a break at the empty trace: the empty trace backs nothing
example (z : GameOutcome nx ns) (c : DaClaim) (ha : z.accepted = true)
    (hc : c ∈ z.statement.claims.da) : BreaksVis z [] := by
  refine ⟨ha, Or.inr ⟨c, hc, ?_⟩⟩
  rintro ⟨rows, -, -, -, -, hvd⟩
  simp [Da.vectorDigestOfWith, Da.membershipVectorWith, Da.membershipChallengesWith, Da.daHash,
    look, logLookup_nil] at hvd

-- a break against the final log is one at every trace it answers, the empty one included
example (z : GameOutcome nx ns) (ℓ : Log) (h : Breaks z ℓ) : BreaksVis z [] :=
  breaksVis_of_breaks (fun _ he ↦ absurd he List.not_mem_nil) h

end

/-- info: 'LeanVM.E2E.xWinAt_of_gameRec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.xWinAt_of_gameRec

/-- info: 'LeanVM.E2E.sWinAt_of_gameRec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sWinAt_of_gameRec

/-- info: 'LeanVM.E2E.prEvent_forged_le_perKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_forged_le_perKey

/-- info: 'LeanVM.E2E.daBacked_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.daBacked_mono

/-- info: 'LeanVM.E2E.prEvent_breaks_le_breaksVis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_breaks_le_breaksVis

/-- info: 'LeanVM.E2E.forged_of_breaksVis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.forged_of_breaksVis

/-- info: 'LeanVM.E2E.prEvent_breaksVis_le_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_breaksVis_le_of

/-- info: 'LeanVM.E2E.prEvent_breaksVis_le_sec0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_breaksVis_le_sec0
