/-
  LeanerVM.Protocol.ToArkLib.Whir.Schedule

  The schedule of a WHIR level as a list of steps, with the instances of every suffix of the
  list. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.SendOracleBeside

/-!
# Schedules as lists of steps

A level of WHIR is a dozen rounds of different kinds: challenges, plain messages, the commitment
of a word, the sumcheck rounds. Instance search finds ArkLib's instances for the messages and
challenges of two schedules side by side only when the left one is not a literal, and then only
for schedules it has seen written (`Schedule`): a schedule built by `++ₚ` from a dozen parts
would need two named instances for each of its prefixes. `seqSpec steps` is the schedule of a
*list* of steps, built by recursion on the list (`seqSpec (a :: l) = a.spec ++ₚ seqSpec l`), and
`instOracleInterfaceSeq`, `instSampleableTypeSeq` give the instances of `seqSpec l` for every list
by recursion on it, the way `draws` and `roundsSpec` do for their counts. A component of one step
fits its place in the list, and a chain of components, right-nested, is a component at
`seqSpec` of the list of its steps.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

@[expose] public section

namespace Whir

/-- A step of a schedule: a plain message, a message queried as its own type, a challenge, a
run of challenges, or a run of sumcheck rounds of a given degree. The instances are data, so
that a step is matched by its constructor alone. -/
inductive Step : Type 1
  /-- One prover message of type `M`, read whole. -/
  | msg (M : Type)
  /-- One prover message of type `M`, queried through `M`'s oracle interface. -/
  | oracle (M : Type) (inst : OracleInterface M)
  /-- One verifier challenge of type `C`. -/
  | chal (C : Type) (inst : SampleableType C)
  /-- `k` verifier challenges of type `C`. -/
  | chals (C : Type) (inst : SampleableType C) (k : ℕ)
  /-- `m` sumcheck rounds of degree `d` over `C`. -/
  | rds (C : Type) (inst : SampleableType C) (d m : ℕ)
  /-- A step with no round: a verifier-side or prover-side step that sends nothing. -/
  | skip

/-- The number of rounds of a step. -/
def Step.n : Step → ℕ
  | .msg _ => 1
  | .oracle _ _ => 1
  | .chal _ _ => 1
  | .chals _ _ k => k
  | .rds _ _ _ m => roundsRounds m
  | .skip => 0

/-- The schedule of a step. -/
def Step.spec : (a : Step) → ProtocolSpec a.n
  | .msg M => say M
  | .oracle M _ => Component.sayO M
  | .chal C _ => draw C
  | .chals C _ k => draws C k
  | .rds C _ d m => roundsSpec C d m
  | .skip => !p[]

instance instOracleInterfaceSeqStep : (a : Step) → ∀ i, OracleInterface (a.spec.Message i)
  | .msg M => instOracleInterfaceSay M
  | .oracle M inst => @Component.instOracleInterfaceSayO M inst
  | .chal C _ => instOracleInterfaceDraw C
  | .chals C _ k => instOracleInterfaceDraws C k
  | .rds C _ d m => instOracleInterfaceRounds C d m
  | .skip => (inferInstance : ∀ i, OracleInterface ((!p[] : ProtocolSpec 0).Message i))

instance instSampleableTypeSeqStep : (a : Step) → ∀ i, SampleableType (a.spec.Challenge i)
  | .msg M => instSampleableTypeSay M
  | .oracle M _ => Component.instSampleableTypeSayO M
  | .chal C inst => @instSampleableTypeDraw C inst
  | .chals C inst k => @instSampleableTypeDraws C inst k
  | .rds C inst d m => @instSampleableTypeRounds C inst d m
  | .skip => (inferInstance : ∀ i, SampleableType ((!p[] : ProtocolSpec 0).Challenge i))

/-- The number of rounds of a list of steps. -/
def seqRounds : List Step → ℕ
  | [] => 0
  | a :: l => a.n + seqRounds l

/-- The schedule of a list of steps: the steps' schedules in sequence. -/
def seqSpec : (l : List Step) → ProtocolSpec (seqRounds l)
  | [] => !p[]
  | a :: l => a.spec ++ₚ seqSpec l

instance instOracleInterfaceSeq : (l : List Step) → ∀ i, OracleInterface ((seqSpec l).Message i)
  | [] => (inferInstance : ∀ i, OracleInterface ((!p[] : ProtocolSpec 0).Message i))
  | a :: l => msgAppend (instOracleInterfaceSeqStep a) (instOracleInterfaceSeq l)

instance instSampleableTypeSeq :
    (l : List Step) → ∀ i, SampleableType ((seqSpec l).Challenge i)
  | [] => (inferInstance : ∀ i, SampleableType ((!p[] : ProtocolSpec 0).Challenge i))
  | a :: l => chalAppend (instSampleableTypeSeqStep a) (instSampleableTypeSeq l)

end Whir

end

end LeanerVM.Protocol
