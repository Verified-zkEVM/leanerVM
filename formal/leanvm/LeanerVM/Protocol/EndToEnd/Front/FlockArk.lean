/-
  LeanerVM.Protocol.EndToEnd.Front.FlockArk

  What the security of a single-challenge or single-message ArkLib component gives the verifier
  program's specification, whatever its extractor and knowledge state function: a challenge's
  escape average, and a message's reflection of the output relation into the input relation.
-/

module

public import LeanerVM.Protocol.EndToEnd.Front.PubEscape
public import LeanerVM.Protocol.ToArkLib.SampleChallenge
public import LeanerVM.Protocol.ToArkLib.SendChecked
public import LeanerVM.Protocol.ToArkLib.Refutation

/-!
# Component securities, read off

The front phases are built from two shapes of ArkLib component with a trivial witness:

* a checked challenge (`Component.sampleChallenge O E check f`): `sample_escape` turns any
  `Component.Security` of it at error `err` into "from a statement outside the input relation that
  passes the check, the challenge carries it into the output relation with average at most
  `err`". The proof reads the security's worst-case round-by-round bound at the empty prefix: the
  knowledge state function is the input relation before the challenge (`toFun_empty`) and holds
  after it wherever the verifier accepts into the output relation (`toFun_full`);
* a checked message (`Component.sendChecked O M honest check out`): `sendChecked_reflect` turns
  any security of it into "a message passing the check with its verdict in the output relation
  comes from a statement in the input relation" (`toFun_full`, then `toFun_next`, then
  `toFun_empty`).

These are the only facts the specifications of the verifier program use of the ArkLib phases, so
they rest on the phases' proved securities and nothing else.
-/

namespace LeanerVM.Protocol.EndToEnd.Front

open LeanerVM.Parameters LeanerVM.Protocol OracleComp OracleSpec ProtocolSpec
open scoped ENNReal NNReal

@[expose] public section

variable {ι : Type} {O : ι → Type} [∀ i, OracleInterface (O i)] {StmtIn StmtOut : Type}

/-- The empty oracle's implementation. -/
def noImpl : QueryImpl []ₒ (StateT Unit ProbComp) := fun x ↦ x.elim

/-- **A challenge's escape, from a component's security.** From a statement outside the input
relation that passes the check, the challenge carries it into the output relation with average at
most the component's error. -/
theorem sample_escape {check : StmtIn → Bool} {f : StmtIn → E → StmtOut}
    {relIn : Set ((StmtIn × ∀ i, O i) × Unit)} {relOut : Set ((StmtOut × ∀ i, O i) × Unit)}
    {err : (draw E).ChallengeIdx → ℝ≥0}
    (S : Component.Security (Component.sampleChallenge (W := Unit) O E check f) relIn relOut err)
    (s : StmtIn) (o : ∀ i, O i) (hin : ((s, o), ()) ∉ relIn) (hc : check s = true) :
    avgE (fun c ↦ indE (((f s c, o), ()) ∈ relOut)) ≤ err ⟨0, rfl⟩ := by
  rw [avgE_indE_eq_prEvent]
  let tr0 : (draw E).Transcript (0 : Fin 2) := fun i ↦ Fin.elim0 i
  have h := S.rbr (pure ()) noImpl (s, o) (⟨0, rfl⟩ : (draw E).ChallengeIdx) tr0
  refine le_trans (prEvent_mono _ _ _ fun c hc' ↦ ?_) h
  let K := S.kSF (pure ()) noImpl
  let tr : (draw E).FullTranscript := Transcript.concat (m := 0) c tr0
  have hfull := K.toFun_full (s, o) tr ()
    (Verifier.GuardedForm.prEvent_pos_of_check (Component.sampleGuarded O E check f)
      (pure ()) noImpl (s, o) tr (fun t ↦ (t, ()) ∈ relOut) hc hc')
  refine ⟨S.extractor.extractOut (s, o) tr (), fun h0 ↦ hin ?_, hfull⟩
  have hd : tr0 = default := funext fun i ↦ Fin.elim0 i
  have := (K.toFun_empty (s, o) _).mpr (hd ▸ h0)
  exact this

/-- **A message's reflection, from a component's security.** A message passing the check whose
verdict is in the output relation comes from a statement in the input relation. -/
theorem sendChecked_reflect {M : Type} {honest : (StmtIn × ∀ i, O i) × Unit → M}
    {check : StmtIn → M → Bool} {out : StmtIn → M → StmtOut}
    {relIn : Set ((StmtIn × ∀ i, O i) × Unit)} {relOut : Set ((StmtOut × ∀ i, O i) × Unit)}
    {err : (say M).ChallengeIdx → ℝ≥0}
    (S : Component.Security (Component.sendChecked (W := Unit) O M honest check out) relIn relOut
      err)
    (s : StmtIn) (o : ∀ i, O i) (msg : M) (hc : check s msg = true)
    (hout : ((out s msg, o), ()) ∈ relOut) : ((s, o), ()) ∈ relIn := by
  let K := S.kSF (pure ()) noImpl
  let tr : (say M).FullTranscript :=
    ProtocolSpec.Transcript.concat (m := 0) msg (default : (say M).Transcript 0)
  have hpos := Verifier.GuardedForm.prEvent_pos_of_check
    (Component.sendCheckedGuarded O M check out) (pure ()) noImpl (s, o) tr
    (fun t ↦ (t, ()) ∈ relOut) hc hout
  have hfull := K.toFun_full (s, o) tr () hpos
  have hnext := K.toFun_next 0 rfl (s, o) (default : (say M).Transcript 0) msg _ hfull
  exact (K.toFun_empty (s, o) _).mpr hnext

end
end LeanerVM.Protocol.EndToEnd.Front
