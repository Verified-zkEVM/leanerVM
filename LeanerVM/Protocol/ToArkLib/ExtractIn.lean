/-
  LeanerVM.Protocol.ToArkLib.ExtractIn

  The input witness a round-by-round extractor returns on a full transcript, read at the first
  round. Candidate for ArkLib.
-/

module

public import ArkLib.OracleReduction.Composition.Sequential.Append.GuardedRoundByRound

/-!
# The witness a round-by-round extractor returns

ArkLib folds a round-by-round extractor's steps backward along a transcript prefix
(`Extractor.RoundByRound.foldPrefix`). On a full transcript, from the output witness, the fold
is the input witness the extractor returns (`Extractor.RoundByRound.extractFull`), the value of
ArkLib's `foldExtractor`. On a protocol with at least one round the fold ends with the fold from
round `1`, on the transcript's first message (`foldPrefix_eq_foldPrefix_one`). An extractor
whose fold from round `1` returns the first message (`Extractor.RoundByRound.ReadsFirst`) thus
returns that message on every full transcript (`extractFull_heq_of_readsFirst`), and the
property passes from an extractor to its sequence with any other (`readsFirst_append`), since the
fold from round `1` of the sequence is the first extractor's (`append_foldPrefix_one`).
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

@[expose] public section

namespace Extractor.RoundByRound

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn WitOut : Type} {n : ℕ}
  {pSpec : ProtocolSpec n} {WitMid : Fin (n + 1) → Type}

/-- The input witness the extractor returns on a full transcript: the fold from the output
witness down to round `0`. -/
def extractFull (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid) (s : StmtIn)
    (tr : pSpec.FullTranscript) (w : WitOut) : WitIn :=
  E.foldPrefix s (Fin.last n) tr (E.extractOut s tr w)

/-- The fold from round `m + 1` is the fold from round `1`, on the transcript's first message,
at some witness of round `1`. -/
theorem foldPrefix_eq_foldPrefix_one
    (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid) (s : StmtIn) :
    ∀ (m : ℕ) (hm : m + 1 ≤ n) (tr : pSpec.Transcript ⟨m + 1, Nat.lt_succ_of_le hm⟩)
      (w : WitMid ⟨m + 1, Nat.lt_succ_of_le hm⟩),
      ∃ w₁ : WitMid ⟨1, Nat.lt_succ_of_le (Nat.le_trans (Nat.succ_le_succ m.zero_le) hm)⟩,
        E.foldPrefix s ⟨m + 1, _⟩ tr w =
          E.foldPrefix s ⟨1, _⟩ (fun i ↦ tr (Fin.castLE (Nat.succ_le_succ m.zero_le) i)) w₁
  | 0, _, _, w => ⟨w, rfl⟩
  | m + 1, hm, tr, w => by
    obtain ⟨w₁, h⟩ := foldPrefix_eq_foldPrefix_one E s m (by omega) (Fin.init tr)
      (E.extractMid ⟨m + 1, hm⟩ s tr w)
    exact ⟨w₁, (E.foldPrefix_succ s ⟨m + 1, hm⟩ tr w).trans h⟩

/-- The extractor's fold from round `1` returns the transcript's first message, whatever the
statement and the witness it is given. -/
def ReadsFirst (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid) : Prop :=
  ∀ (h : 0 < n) (s : StmtIn) (tr : Transcript ⟨1, Nat.succ_lt_succ h⟩ pSpec)
    (w : WitMid ⟨1, Nat.succ_lt_succ h⟩),
    HEq (E.foldPrefix s ⟨1, _⟩ tr w) (tr ⟨0, Nat.zero_lt_one⟩)

/-- An extractor whose fold from round `1` reads the first message returns that message on every
full transcript of a protocol with a round, whatever the output witness. -/
theorem extractFull_heq_of_readsFirst
    (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid) (hE : ReadsFirst E)
    (hn : 0 < n) (s : StmtIn) (tr : pSpec.FullTranscript) (w : WitOut) :
    HEq (extractFull E s tr w) (tr ⟨0, hn⟩) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  obtain ⟨w₁, h⟩ := foldPrefix_eq_foldPrefix_one E s k le_rfl tr (E.extractOut s tr w)
  exact (heq_of_eq h).trans (hE hn s _ w₁)

variable {Stmt₂ Wit₂ Wit₃ : Type} {m : ℕ} {pSpec₂ : ProtocolSpec m}
  {WitMid₂ : Fin (m + 1) → Type}

/-- The fold from round `1` of two extractors in sequence, when the first has a round, is the
first extractor's, on the first extractor's part of the transcript. -/
theorem append_foldPrefix_one
    (E₁ : Extractor.RoundByRound oSpec StmtIn WitIn Wit₂ pSpec WitMid)
    (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂)
    (verify : StmtIn → pSpec.FullTranscript → Stmt₂) (hn : 0 < n) (s : StmtIn)
    (tr : (pSpec ++ₚ pSpec₂).Transcript (Fin.castAdd m (⟨0, hn⟩ : Fin n)).succ)
    (w : (Fin.append (m := n + 1) WitMid (Fin.tail WitMid₂) ∘ Fin.cast (by omega))
      (Fin.castAdd m (⟨0, hn⟩ : Fin n)).succ) :
    (E₁.append E₂ verify).foldPrefix s _ tr w =
      E₁.foldPrefix s (⟨0, hn⟩ : Fin n).succ (tr.fstUpTo (⟨0, hn⟩ : Fin n).succ (by simp))
        (cast (Extractor.wit_mid_append_left (WitMid₂ := WitMid₂) _ _ rfl) w) :=
  congrArg (E₁.extractIn s)
    (eq_of_heq ((cast_heq _ _).trans (E₁.append_extractMid_castAdd E₂ verify _ s tr w)))

/-- The sequence of two extractors reads the first message when the first extractor does and
has a round. -/
theorem readsFirst_append
    (E₁ : Extractor.RoundByRound oSpec StmtIn WitIn Wit₂ pSpec WitMid)
    (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂)
    (verify : StmtIn → pSpec.FullTranscript → Stmt₂) (hn : 0 < n) (h₁ : ReadsFirst E₁) :
    ReadsFirst (E₁.append E₂ verify) :=
  fun _ s tr w ↦ (heq_of_eq (append_foldPrefix_one E₁ E₂ verify hn s tr w)).trans
    ((h₁ hn s _ _).trans (cast_heq _ _))

end Extractor.RoundByRound

end
end LeanerVM.Protocol
