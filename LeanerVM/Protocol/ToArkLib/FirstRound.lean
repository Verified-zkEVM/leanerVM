/-
  LeanerVM.Protocol.ToArkLib.FirstRound

  The first round of a sequence of components: its knowledge state is the first component's, and
  an extractor whose first step decodes the first message returns the decoded witness.
  Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.Component
public import LeanerVM.Protocol.ToArkLib.ExtractIn

/-!
# The first round of a sequence

Two facts about a sequence of components read at its first rounds.

* `Component.Security.append_kSF_left`: up to the seam, the knowledge state function of a sequence
  is the first component's, on the first component's part of the transcript.
* `Extractor.RoundByRound.DecodesFirst E hn f`: the extractor's first step returns `q` whenever
  `f` reads `q` off the statement and the first message. The property passes from an extractor to
  its sequence with any other (`decodesFirst_append`), and an extractor that has it returns the
  decoded witness on every full transcript (`extractIn_eq_of_decodesFirst`): the fold of the steps
  ends with the first step. `ReadsFirst` of `LeanerVM.Protocol.ToArkLib.ExtractIn` is the case of
  an extractor that returns the message itself.

Nothing here transcribes a source.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

/-! ## The knowledge state up to the seam -/

namespace Component

/-- At the first round of two schedules in sequence, the type is the first schedule's. -/
theorem append_Type_zero {m n : ℕ} {p₁ : ProtocolSpec m} {p₂ : ProtocolSpec n}
    (h : 0 < m) : (p₁ ++ₚ p₂).«Type» ⟨0, by omega⟩ = p₁.«Type» ⟨0, h⟩ :=
  ProtocolSpec.append_Type_castAdd ⟨0, h⟩

variable {Stmt₁ Stmt₂ Stmt₃ Wit₁ Wit₂ Wit₃ : Type}
  {ι₁ ι₂ ι₃ : Type} {OStmt₁ : ι₁ → Type} {OStmt₂ : ι₂ → Type} {OStmt₃ : ι₃ → Type}
  [∀ i, OracleInterface (OStmt₁ i)] [∀ i, OracleInterface (OStmt₂ i)]
  [∀ i, OracleInterface (OStmt₃ i)]
  {m₁ m₂ : ℕ} {pSpec₁ : ProtocolSpec m₁} {pSpec₂ : ProtocolSpec m₂}
  [∀ i, OracleInterface (pSpec₁.Message i)] [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, OracleInterface (pSpec₂.Message i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {D₁ : Def Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁}
  {D₂ : Def Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂}
  {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)} {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
  {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}
  {ε₁ : pSpec₁.ChallengeIdx → ℝ≥0} {ε₂ : pSpec₂.ChallengeIdx → ℝ≥0}

/-- Up to the seam, the knowledge state function of a sequence is the first component's, on the
first component's part of the transcript. -/
theorem Security.append_kSF_left (S₁ : Security D₁ rel₁ rel₂ ε₁) (S₂ : Security D₂ rel₂ rel₃ ε₂)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    {k : Fin (m₁ + m₂ + 1)} (j : Fin (m₁ + 1)) (h : k.val = j.val)
    (s : Stmt₁ × ∀ i, OStmt₁ i) (tr : (pSpec₁ ++ₚ pSpec₂).Transcript k)
    (w : (S₁.append S₂).witMid k) :
    ((S₁.append S₂).kSF init impl).toFun k s tr w ↔
      (S₁.kSF init impl).toFun j s (Verifier.KnowledgeAppend.left tr j (by omega))
        (cast (Verifier.KnowledgeAppend.witness_left k j h) w) :=
  Verifier.KnowledgeAppend.state_left _ _ _ j h s tr w

end Component

/-! ## Extractors that decode the first message -/

namespace Extractor.RoundByRound

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn WitOut : Type} {n : ℕ}
  {pSpec : ProtocolSpec n} {WitMid : Fin (n + 1) → Type}

/-- The fold of the steps from a round above the first ends with the first step. -/
theorem foldMid_eq_extractMid_zero
    (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid) (s : StmtIn)
    (tr : pSpec.FullTranscript) :
    ∀ (m : ℕ) (hm : m + 1 ≤ n) (w : WitMid ⟨m + 1, Nat.lt_succ_of_le hm⟩),
      ∃ w₁ : WitMid (⟨0, Nat.lt_of_lt_of_le (Nat.succ_pos m) hm⟩ : Fin n).succ,
        foldMid E s tr (m + 1) hm w =
          E.extractMid ⟨0, Nat.lt_of_lt_of_le (Nat.succ_pos m) hm⟩ s
            (tr.take 1 (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le m)) hm)) w₁
  | 0, _, w => ⟨w, rfl⟩
  | m + 1, hm, w => foldMid_eq_extractMid_zero E s tr m (by omega) _

/-- The witness an extractor returns is its first step's, at some witness of round `1`. -/
theorem extractIn_heq_extractMid_zero
    (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid) (hn : 0 < n)
    (s : StmtIn) (tr : pSpec.FullTranscript) (w : WitOut) :
    ∃ w₁ : WitMid ⟨1, Nat.succ_lt_succ hn⟩,
      HEq (extractIn E s tr w) (E.extractMid ⟨0, hn⟩ s (tr.take 1 hn) w₁) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  obtain ⟨w₁, hw⟩ := foldMid_eq_extractMid_zero E s tr k le_rfl (E.extractOut s tr w)
  refine ⟨w₁, ?_⟩
  unfold extractIn
  refine (cast_heq _ _).trans ?_
  rw [hw]
  rfl

/-- The first step of two extractors in sequence is the first extractor's, on the transcript's
first message, up to the casts of the composed witness family and of the appended schedule. -/
theorem extractMid_zero_append {Stmt₂ Wit₂ Wit₃ : Type} {m : ℕ} {pSpec₂ : ProtocolSpec m}
    {WitMid₂ : Fin (m + 1) → Type}
    (E₁ : Extractor.RoundByRound oSpec StmtIn WitIn Wit₂ pSpec WitMid)
    (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂)
    (verify : StmtIn → pSpec.FullTranscript → Stmt₂) (hn : 0 < n) (s : StmtIn)
    (tr : Transcript ⟨1, by omega⟩ (pSpec ++ₚ pSpec₂))
    (w : (Fin.append (m := n + 1) WitMid (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) ⟨1, by omega⟩) :
    HEq ((E₁.append E₂ verify).extractMid ⟨0, by omega⟩ s tr w)
      (E₁.extractMid ⟨0, hn⟩ s
        (show pSpec.Transcript ⟨1, by omega⟩ from fun i ↦
          cast (ProtocolSpec.append_Type_castAdd (pSpec₁ := pSpec) (pSpec₂ := pSpec₂)
            ⟨i.val, by have := i.isLt; omega⟩) (tr ⟨i.val, by have := i.isLt; omega⟩))
        (cast (Extractor.wit_mid_append_left (WitMid₂ := WitMid₂)
          (⟨0, by omega⟩ : Fin (n + m)).succ ⟨1, by omega⟩ rfl) w)) := by
  simp only [Extractor.RoundByRound.append, dite_eq_left hn]
  exact cast_heq _ _

/-- The extractor's first step returns `q` whenever `f` reads `q` off the statement and the first
message. -/
def DecodesFirst (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (hn : 0 < n) (f : StmtIn → pSpec.«Type» ⟨0, hn⟩ → Option WitIn) : Prop :=
  ∀ s (tr : Transcript ⟨1, Nat.succ_lt_succ hn⟩ pSpec) w q,
    f s (tr ⟨0, Nat.zero_lt_one⟩) = some q → HEq (E.extractMid ⟨0, hn⟩ s tr w) q

/-- An extractor whose first step decodes the first message returns the decoded witness on every
full transcript. -/
theorem extractIn_eq_of_decodesFirst
    (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid) (hn : 0 < n)
    {f : StmtIn → pSpec.«Type» ⟨0, hn⟩ → Option WitIn} (hE : DecodesFirst E hn f) (s : StmtIn)
    (tr : pSpec.FullTranscript) (w : WitOut) (q : WitIn) (hq : f s (tr ⟨0, hn⟩) = some q) :
    extractIn E s tr w = q := by
  obtain ⟨w₁, hw₁⟩ := extractIn_heq_extractMid_zero E hn s tr w
  exact eq_of_heq (hw₁.trans (hE s _ w₁ q hq))

/-- The sequence of two extractors decodes the first message when the first extractor does. -/
theorem decodesFirst_append {Stmt₂ Wit₂ Wit₃ : Type} {m : ℕ} {pSpec₂ : ProtocolSpec m}
    {WitMid₂ : Fin (m + 1) → Type}
    (E₁ : Extractor.RoundByRound oSpec StmtIn WitIn Wit₂ pSpec WitMid)
    (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂)
    (verify : StmtIn → pSpec.FullTranscript → Stmt₂) (hn : 0 < n)
    {f : StmtIn → pSpec.«Type» ⟨0, hn⟩ → Option WitIn} (h₁ : DecodesFirst E₁ hn f) :
    DecodesFirst (E₁.append E₂ verify) (by omega) (fun s x ↦ f s
      (cast (ProtocolSpec.append_Type_castAdd (pSpec₁ := pSpec) (pSpec₂ := pSpec₂) ⟨0, hn⟩) x)) :=
  fun s tr w q hq ↦ (extractMid_zero_append E₁ E₂ verify hn s tr w).trans (h₁ s _ _ q hq)

end Extractor.RoundByRound

end
end LeanerVM.Protocol
