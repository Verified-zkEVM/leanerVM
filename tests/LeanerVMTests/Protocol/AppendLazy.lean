import LeanerVM.Protocol.ToArkLib.SumcheckRound
import LeanerVM.Protocol.Field
import LeanerVM.Protocol.ToArkLib.Oracles

/-!
# The lazy instances of appended schedules

The `@[csimp]` theorems of `LeanerVM.Protocol.ToArkLib.AppendLazy` read the challenge samplers and
the message interfaces of an appended schedule by one comparison with the seam. ArkLib's
`Fin.fappend₂`, compiled, evaluates entries of the inner schedules at every step, so that a prover
run of `SumcheckRound.rounds`, whose schedule is appended on the right once per round, grows about
fourteenfold per round. These guards run twenty and forty rounds through ArkLib's `Prover.run`,
and check that they draw the challenges that draws appended on the left draw.
-/

namespace LeanerVMTests.Protocol.AppendLazy

open LeanerVM.Parameters LeanerVM.Protocol OracleComp OracleSpec ProtocolSpec

/-- A xorshift step. -/
private def xs (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

/-- Uniform samples read off the words of a xorshift. -/
private def xsImpl : QueryImpl unifSpec (StateM UInt64) :=
  fun n st ↦ (Fin.ofNat (n + 1) st.toNat, xs st)

/-- Run a prover at the challenges a xorshift draws from `seed`. -/
private def runAt {S W S' W' : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)] (P : Prover []ₒ S W S' W' pSpec) (s : S) (w : W)
    (seed : UInt64) : pSpec.FullTranscript × S' × W' :=
  (simulateQ xsImpl
    (simulateQ (QueryImpl.add (fun t ↦ isEmptyElim t) challengeQueryImpl) (P.run s w))).run' seed

/-- No oracle. -/
private def noO : ∀ i, NoOracle i := fun i ↦ i.elim0

/-- `k` trivial sumcheck rounds: their schedule is appended on the right once per round. -/
private def trivialRounds (k : ℕ) :=
  SumcheckRound.rounds (F := E) (X := Unit) (O := NoOracle) (W := Unit) (d := 0)
    (fun _ _ _ ↦ #v[0]) (fun _ _ ↦ []) k k 0 (Nat.zero_add k)

/-- The challenges of `k` trivial rounds and of `k` draws appended on the left, at a seed. -/
private def drawn (k : ℕ) (seed : UInt64) : List E × List E :=
  ((runAt (trivialRounds k).red.prover (((), (#v[], 0)), noO) () seed).2.1.1.2.1.toList,
    (runAt (Component.drawPushes (S := Unit) (W := Unit) NoOracle E k).red.prover ((), noO) ()
      seed).2.1.1.2.toList)

#guard (drawn 20 7).1 == (drawn 20 7).2
#guard (drawn 40 9).1 == (drawn 40 9).2
#guard (drawn 40 9).1.length == 40

end LeanerVMTests.Protocol.AppendLazy
