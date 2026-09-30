/-
  LeanerVM.Protocol.ToArkLib.ExtractIn

  The input witness a round-by-round extractor returns on a full transcript: the fold of its
  round steps from the output witness down to the first round. Candidate for ArkLib.
-/

module

public import ArkLib.OracleReduction.Composition.Sequential.Append.StateFunction

/-!
# The witness a round-by-round extractor returns

ArkLib's round-by-round extractor is a family of steps: `extractOut` turns the output witness
into the witness of the last round, and `extractMid m` turns the witness of round `m + 1` into
that of round `m`, reading the transcript up to round `m + 1`. `Extractor.RoundByRound.foldMid`
folds the steps from a round down to round `0` on the prefixes of a full transcript, and
`Extractor.RoundByRound.extractIn` is the fold from the output witness: the input witness the
extractor returns on that transcript. On a protocol with at least one round the fold ends with
the first round's step, applied to the fold down to round `1` (`foldMid_succ`). An extractor
whose first step returns the first message alone (`Extractor.RoundByRound.ReadsFirst`) thus
returns that message on every full transcript (`extractIn_heq_of_readsFirst`), and the property
passes from an extractor to its sequence with any other (`readsFirst_append`), since the first
round's step of the sequence is the first extractor's (`append_extractMid_zero_heq`).
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

@[expose] public section

namespace Extractor.RoundByRound

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn WitOut : Type} {n : ℕ}
  {pSpec : ProtocolSpec n} {WitMid : Fin (n + 1) → Type}

/-- The fold of the round steps from round `m` down to round `0`, each step reading the
transcript up to its round. -/
def foldMid (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid) (s : StmtIn)
    (tr : pSpec.FullTranscript) : (m : ℕ) → (hm : m ≤ n) → WitMid ⟨m, Nat.lt_succ_of_le hm⟩ →
      WitMid 0
  | 0, _, w => w
  | m + 1, hm, w =>
    foldMid E s tr m (Nat.le_of_succ_le hm) (E.extractMid ⟨m, hm⟩ s (tr.take (m + 1) hm) w)

/-- The input witness the extractor returns on a full transcript: the fold from the output
witness down to round `0`. -/
def extractIn (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid) (s : StmtIn)
    (tr : pSpec.FullTranscript) (w : WitOut) : WitIn :=
  cast E.eqIn (foldMid E s tr n le_rfl (E.extractOut s tr w))

/-- The fold of the round steps from round `k + 1` down to round `1`. -/
def foldToOne (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid) (s : StmtIn)
    (tr : pSpec.FullTranscript) : (k : ℕ) → (hk : k + 1 ≤ n) →
      WitMid ⟨k + 1, Nat.lt_succ_of_le hk⟩ →
        WitMid ⟨1, Nat.lt_succ_of_le (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le k)) hk)⟩
  | 0, _, w => w
  | k + 1, hk, w =>
    foldToOne E s tr k (Nat.le_of_succ_le hk) (E.extractMid ⟨k + 1, hk⟩ s (tr.take (k + 2) hk) w)

/-- The fold from a round above the first is the first round's step, on the transcript's first
message, applied to the fold down to round `1`. -/
theorem foldMid_succ (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (s : StmtIn) (tr : pSpec.FullTranscript) :
    (k : ℕ) → (hk : k + 1 ≤ n) → (w : WitMid ⟨k + 1, Nat.lt_succ_of_le hk⟩) →
      foldMid E s tr (k + 1) hk w =
        E.extractMid ⟨0, Nat.lt_of_lt_of_le (Nat.zero_lt_succ k) hk⟩ s
          (tr.take 1 (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le k)) hk))
          (foldToOne E s tr k hk w)
  | 0, _, _ => rfl
  | k + 1, hk, w =>
    foldMid_succ E s tr k (Nat.le_of_succ_le hk)
      (E.extractMid ⟨k + 1, hk⟩ s (tr.take (k + 2) hk) w)

end Extractor.RoundByRound

/-- The first round's step of two extractors in sequence, when the first has a round, is the
first extractor's step on the transcript's first message, up to the casts of the composed
witness family and of the appended schedule. -/
theorem Extractor.RoundByRound.append_extractMid_zero_heq {ι : Type} {oSpec : OracleSpec ι}
    {Stmt₁ Stmt₂ Wit₁ Wit₂ Wit₃ : Type} {m n : ℕ} {pSpec₁ : ProtocolSpec m}
    {pSpec₂ : ProtocolSpec n} {WitMid₁ : Fin (m + 1) → Type} {WitMid₂ : Fin (n + 1) → Type}
    (E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁)
    (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂) (hm : 0 < m) (s : Stmt₁)
    (tr : Transcript ⟨1, by omega⟩ (pSpec₁ ++ₚ pSpec₂))
    (w : (Fin.append (m := m + 1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) ⟨1, by omega⟩) :
    HEq ((E₁.append E₂ verify).extractMid ⟨0, by omega⟩ s tr w)
      (E₁.extractMid ⟨0, hm⟩ s
        (show pSpec₁.Transcript ⟨1, by omega⟩ from fun i ↦
          cast (ProtocolSpec.append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
            ⟨i.val, by have := i.isLt; omega⟩) (tr ⟨i.val, by have := i.isLt; omega⟩))
        (cast (Extractor.wit_mid_append_left (WitMid₂ := WitMid₂) (⟨0, by omega⟩ : Fin (m + n)).succ
          ⟨1, by omega⟩ rfl) w)) := by
  simp only [Extractor.RoundByRound.append, dite_eq_left hm]
  exact cast_heq _ _

namespace Extractor.RoundByRound

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn WitOut : Type} {n : ℕ}
  {pSpec : ProtocolSpec n} {WitMid : Fin (n + 1) → Type}

/-- The extractor's first step returns the transcript's first message, whatever the statement
and the witness it is given. -/
def ReadsFirst (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid) : Prop :=
  ∀ (h : 0 < n) (s : StmtIn) (tr : Transcript ⟨1, Nat.succ_lt_succ h⟩ pSpec)
    (w : WitMid (⟨0, h⟩ : Fin n).succ),
    HEq (E.extractMid ⟨0, h⟩ s tr w) (tr ⟨0, Nat.zero_lt_one⟩)

/-- An extractor whose first step reads the first message returns that message on every full
transcript of a protocol with a round, whatever the output witness. -/
theorem extractIn_heq_of_readsFirst (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec
      WitMid) (hE : ReadsFirst E) (hn : 0 < n) (s : StmtIn) (tr : pSpec.FullTranscript)
    (w : WitOut) : HEq (extractIn E s tr w) (tr ⟨0, hn⟩) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  unfold extractIn
  refine (cast_heq _ _).trans ?_
  rw [foldMid_succ]
  exact hE hn s _ _

/-- The sequence of two extractors reads the first message when the first extractor does and
has a round. -/
theorem readsFirst_append {Stmt₂ Wit₂ Wit₃ : Type} {m : ℕ} {pSpec₂ : ProtocolSpec m}
    {WitMid₂ : Fin (m + 1) → Type}
    (E₁ : Extractor.RoundByRound oSpec StmtIn WitIn Wit₂ pSpec WitMid)
    (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂)
    (verify : StmtIn → pSpec.FullTranscript → Stmt₂) (hn : 0 < n) (h₁ : ReadsFirst E₁) :
    ReadsFirst (E₁.append E₂ verify) :=
  fun _ s tr w ↦
    (append_extractMid_zero_heq E₁ E₂ verify hn s tr w).trans
      ((h₁ hn s _ _).trans (cast_heq _ _))

end Extractor.RoundByRound

/-- The first half of a transcript of two schedules in sequence, at a round, is the transcript
at that round, up to the cast of the schedule. -/
theorem FullTranscript.fst_heq {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    (T : FullTranscript (pSpec₁ ++ₚ pSpec₂)) (i : Fin m) :
    HEq (T.fst i) (T (Fin.castAdd n i)) := by
  unfold FullTranscript.fst
  exact cast_heq _ _

end
end LeanerVM.Protocol
