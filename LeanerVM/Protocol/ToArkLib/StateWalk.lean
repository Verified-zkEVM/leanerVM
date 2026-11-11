/-
  LeanerVM.Protocol.ToArkLib.StateWalk

  A knowledge state function walked back along a full transcript, from its end to its start.
  Candidate for ArkLib.
-/

module

public import ArkLib.OracleReduction.Security.RoundByRound

/-!
# Walking a knowledge state function back

A knowledge state function true at the end of a full transcript stays true, for some witness,
at every earlier round, as long as no challenge of the transcript turns it from false to true:
at a prover message the state function's own `toFun_next` carries it back, and at a challenge
the hypothesis does, with the witness the extractor hands back
(`Verifier.KnowledgeStateFunction.exists_toFun_take_of_good`, on the transcript's prefix before
each challenge, `prefixBefore`, and the challenge, `challengeAt`). A challenge that does turn it
is the event round-by-round knowledge soundness bounds.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

public section

/-- The prefix of a full transcript before a challenge. -/
@[expose] def prefixBefore {n : ℕ} {pSpec : ProtocolSpec n} (tr : pSpec.FullTranscript)
    (i : pSpec.ChallengeIdx) : pSpec.Transcript i.1.castSucc :=
  tr.take i.1.val i.1.castSucc.is_le

/-- The challenge a full transcript carries at a challenge round. -/
@[expose] def challengeAt {n : ℕ} {pSpec : ProtocolSpec n} (tr : pSpec.FullTranscript)
    (i : pSpec.ChallengeIdx) : pSpec.Challenge i :=
  tr i.1

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ}
  {pSpec : ProtocolSpec n} {V : Verifier oSpec StmtIn StmtOut pSpec} {σ : Type}
  {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)} {relIn : Set (StmtIn × WitIn)}
  {relOut : Set (StmtOut × WitOut)} {WitMid : Fin (n + 1) → Type}
  {E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}
  (kSF : V.KnowledgeStateFunction init impl relIn relOut E)

/-- **A knowledge state function true at the end of a full transcript is true, for some
witness, at every round**, when no challenge of the transcript turns it from false to true:
past each challenge, the witness the extractor hands back keeps it true before the challenge. -/
theorem Verifier.KnowledgeStateFunction.exists_toFun_take_of_good (s : StmtIn)
    (full : pSpec.FullTranscript) {w : WitMid (Fin.last n)}
    (hw : kSF.toFun (Fin.last n) s full w)
    (hgood : ∀ (i : pSpec.ChallengeIdx) (w : WitMid i.1.succ),
      kSF.toFun i.1.succ s ((prefixBefore full i).concat (challengeAt full i)) w →
      kSF.toFun i.1.castSucc s (prefixBefore full i)
        (E.extractMid i.1 s ((prefixBefore full i).concat (challengeAt full i)) w))
    (m : Fin (n + 1)) : ∃ w', kSF.toFun m s (full.take m.val m.is_le) w' := by
  induction m using Fin.reverseInduction with
  | last => exact ⟨w, hw⟩
  | cast j ih =>
    obtain ⟨w', hw'⟩ := ih
    rw [show full.take j.succ.val j.succ.is_le =
      Transcript.concat (m := j) (full j) (full.take j.val j.castSucc.is_le) from
        Fin.take_succ_eq_snoc j.val j.isLt full] at hw'
    cases hd : pSpec.dir j with
    | P_to_V => exact ⟨_, kSF.toFun_next j hd s _ _ w' hw'⟩
    | V_to_P => exact ⟨_, hgood ⟨j, hd⟩ w' hw'⟩

end

end LeanerVM.Protocol
