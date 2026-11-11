/-
  LeanerVM.Protocol.ToArkLib.AppendLazy

  ArkLib's instances of an appended schedule and its append of transcripts, compiled again after
  the `@[csimp]` theorems of `ToArkLib/TupleCompiledForms.lean`, which the pinned ArkLib compiled
  them before. Deleted with that file when the pin contains it.
-/

module

public import LeanerVM.Protocol.ToArkLib.TupleCompiledForms
public import ArkLib.OracleReduction.ProtocolSpec.SeqCompose

/-!
# Appended schedules, compiled again

ArkLib builds the `SampleableType` instance of a challenge of `pSpec₁ ++ₚ pSpec₂`, and the
`OracleInterface` instance of a message, with `Fin.fappend₂`, and appends transcripts with
`Fin.happend`. Compiled, both recurse on the length of the second schedule, and reading one entry
of a schedule built by prepending one round at a time takes time exponential in its length
(`Prover.run` of nine trivial sumcheck rounds took 261 s). `ToArkLib/TupleCompiledForms` makes
compiled code read them by one comparison with the seam, but only in code compiled after it, and
the pinned ArkLib compiled its instances and `FullTranscript.append` before.

The definitions below are ArkLib's, word for word, compiled here after those `@[csimp]` theorems;
the `@[csimp]` theorems below, each `rfl`, make compiled code run them in place of ArkLib's.
-/

namespace LeanerVM.Protocol

open ProtocolSpec

@[expose] public section

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- ArkLib's sampler of an appended schedule's challenges, compiled here. -/
@[instance_reducible]
def instSampleableTypeChallengeAppendRecompiled [h₁ : ∀ i, SampleableType (pSpec₁.Challenge i)]
    [h₂ : ∀ i, SampleableType (pSpec₂.Challenge i)] :
    ∀ i, SampleableType ((pSpec₁ ++ₚ pSpec₂).Challenge i) :=
  fun ⟨i, h⟩ => Fin.fappend₂ (A := Direction) (B := Type)
    (F := fun dir type => (h : dir = .V_to_P) → SampleableType type)
    (α₁ := pSpec₁.dir) (β₁ := pSpec₂.dir)
    (α₂ := pSpec₁.Type) (β₂ := pSpec₂.Type) (fun i h => h₁ ⟨i, h⟩) (fun i h => h₂ ⟨i, h⟩) i h

/-- Compiled code samples an appended schedule's challenges by one comparison with the seam. -/
@[csimp] theorem instSampleableTypeChallengeAppend_eq_recompiled :
    @ProtocolSpec.instSampleableTypeChallengeAppend =
      @instSampleableTypeChallengeAppendRecompiled :=
  rfl

/-- ArkLib's oracle interface of an appended schedule's messages, compiled here. -/
@[instance_reducible]
def instOracleInterfaceMessageAppendRecompiled [O₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
    [O₂ : ∀ i, OracleInterface (pSpec₂.Message i)] :
    ∀ i, OracleInterface ((pSpec₁ ++ₚ pSpec₂).Message i) :=
  fun ⟨i, h⟩ => Fin.fappend₂ (A := Direction) (B := Type)
    (F := fun dir type => (h : dir = .P_to_V) → OracleInterface type)
    (α₁ := pSpec₁.dir) (β₁ := pSpec₂.dir)
    (α₂ := pSpec₁.Type) (β₂ := pSpec₂.Type) (fun i h => O₁ ⟨i, h⟩) (fun i h => O₂ ⟨i, h⟩) i h

/-- Compiled code reads an appended schedule's message interfaces by one comparison with the
seam. -/
@[csimp] theorem instOracleInterfaceMessageAppend_eq_recompiled :
    @ProtocolSpec.instOracleInterfaceMessageAppend =
      @instOracleInterfaceMessageAppendRecompiled :=
  rfl

/-- ArkLib's append of transcripts, compiled here. -/
def appendRecompiled (T₁ : pSpec₁.FullTranscript) (T₂ : pSpec₂.FullTranscript) :
    (pSpec₁ ++ₚ pSpec₂).FullTranscript :=
  Fin.happend T₁ T₂

/-- Compiled code appends transcripts by one comparison with the seam. -/
@[csimp] theorem append_eq_appendRecompiled :
    @FullTranscript.append = @appendRecompiled :=
  rfl

end
end LeanerVM.Protocol
