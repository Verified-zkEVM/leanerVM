/-
  LeanerVM.Protocol.ToArkLib.AppendLazy

  The instances of an appended schedule (the challenges' samplers, the messages' oracle
  interfaces) read by one comparison with the seam: `Fin.fappend₂` without the eager walk of the
  second tuple, proved equal and substituted by `@[csimp]`. Candidate for ArkLib.
-/

module

public import ArkLib.OracleReduction.ProtocolSpec.SeqCompose
public import ArkLib.Data.Fin.Tuple.Lemmas

/-!
# Lazy instances of appended schedules

ArkLib builds the `SampleableType` instance of a challenge of `pSpec₁ ++ₚ pSpec₂`, and the
`OracleInterface` instance of a message, with `Fin.fappend₂`, which is defined by recursion on
the second schedule's length through `Fin.fconcat₂` and `Fin.fcons₂`. Compiled, that recursion
evaluates the first entry of the tuple at every step, so reading one entry of a schedule appended
on the right `k` times evaluates entries of the inner schedules over and over: the cost of one
challenge's sampler grows exponentially with `k`, and a prover run of `SumcheckRound.rounds`,
whose schedule is appended on the right once per round, does not finish past a dozen rounds.

`fappend₂Lazy` compares the index with the seam once and reads the entry of the side it falls
in (`fappend₂_eq_fappend₂Lazy`, from ArkLib's `Fin.fappend₂_left` and `Fin.fappend₂_right`).
The `@[csimp]` theorems `instSampleableTypeChallengeAppend_eq_lazy` and
`instOracleInterfaceMessageAppend_eq_lazy` substitute the lazy forms for ArkLib's two
instances in code compiled after them; they change no definition a theorem states.
-/

namespace LeanerVM.Protocol

open ProtocolSpec

@[expose] public section

universe u v w

/-- `Fin.fappend₂`, reading entry `i` by one comparison of `i` with the seam. -/
def fappend₂Lazy {A : Sort u} {B : Sort v} {F : A → B → Sort w} {m n : ℕ}
    {α₁ : Fin m → A} {β₁ : Fin n → A} {α₂ : Fin m → B} {β₂ : Fin n → B}
    (u : (i : Fin m) → F (α₁ i) (α₂ i)) (v : (i : Fin n) → F (β₁ i) (β₂ i)) :
    (i : Fin (m + n)) → F (Fin.vappend α₁ β₁ i) (Fin.vappend α₂ β₂ i) := fun i ↦
  if h : i.val < m then
    cast (congrArg₂ F (by rw [← Fin.vappend_left α₁ β₁ ⟨i.val, h⟩]; rfl)
      (by rw [← Fin.vappend_left α₂ β₂ ⟨i.val, h⟩]; rfl)) (u ⟨i.val, h⟩)
  else
    cast (congrArg₂ F
      (by rw [← Fin.vappend_right α₁ β₁ ⟨i.val - m, by omega⟩]
          exact congrArg _ (Fin.ext (by simp; omega)))
      (by rw [← Fin.vappend_right α₂ β₂ ⟨i.val - m, by omega⟩]
          exact congrArg _ (Fin.ext (by simp; omega)))) (v ⟨i.val - m, by omega⟩)

/-- The lazy append is `Fin.fappend₂`. -/
theorem fappend₂_eq_fappend₂Lazy : @Fin.fappend₂ = @fappend₂Lazy := by
  funext A B F m n α₁ β₁ α₂ β₂ u v i
  by_cases h : i.val < m
  · obtain ⟨j, rfl⟩ : ∃ j : Fin m, i = Fin.castAdd n j := ⟨⟨i.val, h⟩, Fin.ext rfl⟩
    rw [Fin.fappend₂_left, fappend₂Lazy, dite_eq_left h]
    rfl
  · obtain ⟨j, rfl⟩ : ∃ j : Fin n, i = Fin.natAdd m j :=
      ⟨⟨i.val - m, by omega⟩, Fin.ext (by simp; omega)⟩
    rw [Fin.fappend₂_right, fappend₂Lazy, dite_eq_right h]
    apply eq_of_heq
    refine (cast_heq _ _).trans ((?_ : HEq (v j) (v ⟨(Fin.natAdd m j).val - m, by
      simp⟩)).trans (cast_heq _ _).symm)
    exact congr_arg_heq v (Fin.ext (by simp))

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- ArkLib's sampler of an appended schedule's challenges, through `fappend₂Lazy`. -/
@[instance_reducible]
def instSampleableTypeChallengeAppendLazy [h₁ : ∀ i, SampleableType (pSpec₁.Challenge i)]
    [h₂ : ∀ i, SampleableType (pSpec₂.Challenge i)] :
    ∀ i, SampleableType ((pSpec₁ ++ₚ pSpec₂).Challenge i) :=
  fun ⟨i, h⟩ => fappend₂Lazy (A := Direction) (B := Type)
    (F := fun dir type => (h : dir = .V_to_P) → SampleableType type)
    (α₁ := pSpec₁.dir) (β₁ := pSpec₂.dir)
    (α₂ := pSpec₁.Type) (β₂ := pSpec₂.Type) (fun i h => h₁ ⟨i, h⟩) (fun i h => h₂ ⟨i, h⟩) i h

/-- Compiled code samples an appended schedule's challenges lazily. -/
@[csimp] theorem instSampleableTypeChallengeAppend_eq_lazy :
    @ProtocolSpec.instSampleableTypeChallengeAppend =
      @instSampleableTypeChallengeAppendLazy := by
  funext m n pSpec₁ pSpec₂ h₁ h₂ i
  obtain ⟨i, h⟩ := i
  simp only [ProtocolSpec.instSampleableTypeChallengeAppend,
    instSampleableTypeChallengeAppendLazy, fappend₂_eq_fappend₂Lazy]

/-- ArkLib's oracle interface of an appended schedule's messages, through `fappend₂Lazy`. -/
@[instance_reducible]
def instOracleInterfaceMessageAppendLazy [O₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
    [O₂ : ∀ i, OracleInterface (pSpec₂.Message i)] :
    ∀ i, OracleInterface ((pSpec₁ ++ₚ pSpec₂).Message i) :=
  fun ⟨i, h⟩ => fappend₂Lazy (A := Direction) (B := Type)
    (F := fun dir type => (h : dir = .P_to_V) → OracleInterface type)
    (α₁ := pSpec₁.dir) (β₁ := pSpec₂.dir)
    (α₂ := pSpec₁.Type) (β₂ := pSpec₂.Type) (fun i h => O₁ ⟨i, h⟩) (fun i h => O₂ ⟨i, h⟩) i h

/-- Compiled code reads an appended schedule's message interfaces lazily. -/
@[csimp] theorem instOracleInterfaceMessageAppend_eq_lazy :
    @ProtocolSpec.instOracleInterfaceMessageAppend =
      @instOracleInterfaceMessageAppendLazy := by
  funext m n pSpec₁ pSpec₂ O₁ O₂ i
  obtain ⟨i, h⟩ := i
  simp only [ProtocolSpec.instOracleInterfaceMessageAppend,
    instOracleInterfaceMessageAppendLazy, fappend₂_eq_fappend₂Lazy]

end
end LeanerVM.Protocol
