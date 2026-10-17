/-
  LeanerVM.Protocol.EndToEnd.Front.BusComponent

  What a component's round-by-round knowledge soundness says about its relations, for the
  one-round components the front phases are built of: a checked message cannot carry a statement
  outside the input relation into the output relation, and a challenge does so with probability at
  most the component's error.
-/

module

public import LeanerVM.Protocol.ToArkLib.Component
public import LeanerVM.Protocol.ToArkLib.Schedule
public import LeanerVM.Protocol.ToArkLib.GuardedVerdict

/-!
# One-round components, read off their security

The front phases' securities (`busSecurity`, `tableSumcheckSecurity`) are appended from
one-round components: a prover message with a check (`Component.sendChecked`, schedule `say M`)
and a verifier challenge (`Component.sampleChallenge`, schedule `draw C`), with passes in
between. The verifier program reads the same messages and draws the same challenges, so its doom
can be stated on the components' relations instead of on transcripts, if each component's
security is read as a statement about its relations:

* `Security.say_in_of_out`: a message that passes the check and carries the statement into the
  output relation came from a statement in the input relation (the knowledge state function's
  last and first obligations, through its next-message obligation);
* `Security.draw_prEvent_le`: from a statement outside the input relation, the challenges that
  pass the check and carry it into the output relation have probability at most the error (the
  round-by-round bound at the empty prefix).

Both hold for any component with a front verifier and trivial witnesses, whatever its extractor
and state function; they use the shared oracle's trivial state.
-/

namespace LeanerVM.Protocol.EndToEnd.Front

open LeanerVM.Protocol OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

@[expose] public section

/-! ## A guarded verifier outputs its verdict -/

/-- If a guarded verifier's check passes and its verdict satisfies `P`, it outputs a statement
satisfying `P` with positive probability. The converse of
`Verifier.GuardedForm.of_prEvent_pos`. -/
theorem guarded_prEvent_pos {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn StmtOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    {V : Verifier oSpec StmtIn StmtOut pSpec} (G : V.GuardedForm) {σ : Type} (s₀ : σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (stmt : StmtIn) (tr : pSpec.FullTranscript)
    (P : StmtOut → Prop) (hc : G.check stmt tr = true) (hP : P (G.out stmt tr)) :
    Pr{let sample ← OptionT.mk do
      (simulateQ impl (V.run stmt tr)).run' (← (pure s₀ : ProbComp σ))}[P sample] > 0 := by
  have hv : V.run stmt tr = if G.check stmt tr then pure (G.out stmt tr) else failure :=
    G.verify_eq stmt tr
  rw [hv, ite_eq_left hc]
  change 0 < Pr{let sample ← OptionT.mk (do
    let st ← (pure s₀ : ProbComp σ)
    (simulateQ impl (OptionT.run (pure (G.out stmt tr)))).run' st)}[_]
  rw [OptionT.run_pure, simulateQ_pure]
  refine (OracleComp.OptionT.prEvent_mk_pos_iff _ _).mpr ⟨G.out stmt tr, ?_, hP⟩
  simp

/-! ## One-round transcripts -/

/-- The full transcript of a one-message schedule: the empty transcript, extended by the
message. -/
def sayTr {M : Type} (m : M) : (say M).FullTranscript :=
  (default : (say M).Transcript 0).concat (m := 0) m

/-- The full transcript of a one-challenge schedule: the empty transcript, extended by the
challenge. -/
def drawTr {C : Type} (c : C) : (draw C).FullTranscript :=
  (default : (draw C).Transcript 0).concat (m := 0) c

/-- The message of a one-message transcript. -/
@[simp] theorem sayTr_zero {M : Type} (m : M) : sayTr m 0 = m := by
  simp [sayTr]

/-- The challenge of a one-challenge transcript. -/
@[simp] theorem drawTr_zero {C : Type} (c : C) : drawTr c 0 = c := by
  simp [drawTr]

/-- The trivial oracle implementation of the empty shared oracle. -/
def emptyImpl : QueryImpl []ₒ (StateT Unit ProbComp) := fun q ↦ q.elim

section Components

variable {StmtIn StmtOut : Type} {ι : Type} {O : ι → Type} [∀ i, OracleInterface (O i)]

/-! ## A checked message -/

section Say

variable {M : Type} [∀ i, OracleInterface ((say M).Message i)]
  [∀ i, SampleableType ((say M).Challenge i)]
  {D : Component.Def StmtIn O Unit StmtOut O Unit (say M)}
  {relIn : Set ((StmtIn × ∀ i, O i) × Unit)} {relOut : Set ((StmtOut × ∀ i, O i) × Unit)}
  {ε : (say M).ChallengeIdx → ℝ≥0}

/-- **A checked message keeps the input relation's complement**: a message that passes a front
component's check and carries the statement into the output relation came from a statement in
the input relation. -/
theorem Security.say_in_of_out (S : Component.Security D relIn relOut ε) (F : Component.Front D)
    (s : StmtIn) (o : ∀ i, O i) (m : M) (hc : F.check s (sayTr m) = true)
    (hout : ((F.out s (sayTr m), o), ()) ∈ relOut) : ((s, o), ()) ∈ relIn := by
  let G : D.red.verifier.toVerifier.GuardedForm :=
    ⟨fun p tr ↦ F.check p.1 tr, fun p tr ↦ (F.out p.1 tr, p.2), F.verify_eq⟩
  let K := S.kSF (pure ()) emptyImpl
  have hpos :=
    guarded_prEvent_pos G () emptyImpl (s, o) (sayTr m) (fun x ↦ (x, ()) ∈ relOut) hc hout
  have hfull := K.toFun_full (s, o) (sayTr m) () hpos
  have h0 := K.toFun_next 0 rfl (s, o) (default : (say M).Transcript 0) m _ hfull
  have hin := (K.toFun_empty (s, o) _).mpr h0
  simpa using hin

end Say

/-! ## A challenge -/

section Draw

variable {C : Type} [∀ i, OracleInterface ((draw C).Message i)]
  [∀ i, SampleableType ((draw C).Challenge i)]
  {D : Component.Def StmtIn O Unit StmtOut O Unit (draw C)}
  {relIn : Set ((StmtIn × ∀ i, O i) × Unit)} {relOut : Set ((StmtOut × ∀ i, O i) × Unit)}
  {ε : (draw C).ChallengeIdx → ℝ≥0}

/-- **A challenge escapes with probability at most the error**: from a statement outside the
input relation, the challenges that pass a front component's check and carry the statement into
the output relation have probability at most the component's error. -/
theorem Security.draw_prEvent_le (S : Component.Security D relIn relOut ε)
    (F : Component.Front D) (s : StmtIn) (o : ∀ i, O i) (hin : ((s, o), ()) ∉ relIn) :
    Pr{let c ← $ᵗ ((draw C).Challenge ⟨0, rfl⟩)}[F.check s (drawTr c) = true ∧
      ((F.out s (drawTr c), o), ()) ∈ relOut] ≤ ε ⟨0, rfl⟩ := by
  let G : D.red.verifier.toVerifier.GuardedForm :=
    ⟨fun p tr ↦ F.check p.1 tr, fun p tr ↦ (F.out p.1 tr, p.2), F.verify_eq⟩
  let K := S.kSF (pure ()) emptyImpl
  refine le_trans (prEvent_mono _ _ _ fun c ⟨hc, hout⟩ ↦ ?_)
    (S.rbr (pure ()) emptyImpl (s, o) ⟨0, rfl⟩ (default : (draw C).Transcript 0))
  refine ⟨S.extractor.extractOut (s, o) (drawTr c) (), fun h0 ↦ hin ?_, ?_⟩
  · have := (K.toFun_empty (s, o) _).mpr h0
    simpa using this
  · exact K.toFun_full (s, o) (drawTr c) ()
      (guarded_prEvent_pos G () emptyImpl (s, o) (drawTr c) (fun x ↦ (x, ()) ∈ relOut) hc hout)

end Draw

end Components

end
end LeanerVM.Protocol.EndToEnd.Front
