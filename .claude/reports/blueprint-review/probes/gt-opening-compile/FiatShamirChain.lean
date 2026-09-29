/-
Probe (task gt-opening-compile): what does ArkLib's Fiat–Shamir transform take as the challenge
oracle, and can a concrete hash chain be plugged in?

`ArkLib/OracleReduction/FiatShamir/Basic.lean` is not compiled by the build of `main` (no leanerVM
module imports it), so `Verifier.fiatShamir` is copied verbatim from ArkLib `dca90385`,
`FiatShamir/Basic.lean:129-136`, with the section variables of `:68-70` made explicit. Everything
it uses (`NonInteractiveVerifier`, `fsChallengeOracle`, `Messages.deriveTranscriptFS`) is in
compiled modules.
-/
import ArkLib.OracleReduction.Security.Basic

open ProtocolSpec OracleComp OracleSpec

namespace Probe

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]

/-- Verbatim: the (slow) Fiat-Shamir transformation for the verifier. -/
def fiatShamirCopy (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (∀ i, pSpec.Message i) (oSpec + fsChallengeOracle StmtIn pSpec)
      StmtIn StmtOut where
  verify := fun stmtIn proof => do
    let messages : pSpec.Messages := proof 0
    let transcript ← (messages.deriveTranscriptFS (oSpec := oSpec) stmtIn)
    Option.getM (← (V.verify stmtIn transcript).run)

/-- The index of a challenge-oracle query: a round that is a challenge, with the statement and
the messages sent before it. -/
example : (fsChallengeOracle StmtIn pSpec).Domain
    = ((i : pSpec.ChallengeIdx) × (StmtIn × pSpec.MessagesUpTo i.1.castSucc)) := rfl

/-- A "hash chain" in the only form the transform can see: a function from the statement and the
messages so far to the challenge of each round. -/
abbrev Chain (StmtIn : Type) (pSpec : ProtocolSpec n) :=
  (i : pSpec.ChallengeIdx) → StmtIn × pSpec.MessagesUpTo i.1.castSucc → pSpec.Challenge i

/-- The chain as a deterministic implementation of the challenge oracle (no shared oracle). -/
def chainImpl (chain : Chain StmtIn pSpec) :
    QueryImpl ([]ₒ + fsChallengeOracle StmtIn pSpec) Id
  | .inl q => PEmpty.elim q
  | .inr ⟨i, t⟩ => chain i t

/-- The compiled verifier run under a concrete chain: a deterministic function of the statement
and of ALL the prover's messages. -/
def runWithChain (V : Verifier []ₒ StmtIn StmtOut pSpec) (chain : Chain StmtIn pSpec)
    (stmt : StmtIn) (messages : ∀ i, pSpec.Message i) : Option StmtOut :=
  (simulateQ (chainImpl chain) ((fiatShamirCopy V).verify stmt (fun | 0 => messages)).run).run

#check @runWithChain
#print axioms runWithChain

-- An oracle verifier is not a `Verifier`: it must be converted first, and the conversion's
-- statement and messages are the oracles in the clear.
#check @OracleVerifier.toVerifier

end Probe
