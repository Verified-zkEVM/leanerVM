/-
  LeanerVM.Protocol.ToArkLib.RunCodec

  An honest prover run round by round in any monad, each message handed to an encoder and each
  challenge taken from a source in that monad, as a Fiat–Shamir prover runs; the encoders and
  sources of the schedules of `LeanerVM.Protocol.ToArkLib.Schedule`. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.AppendLazy
public import LeanerVM.Protocol.ToArkLib.StepSchedule
public import Batteries.Recycling.MonadSatisfying.Basic
public import ArkLib.OracleReduction.Security.Basic

/-!
# Running a prover against a source of challenges

ArkLib's `Prover.run` draws every challenge from the challenge oracle and keeps the messages in
the transcript. A non-interactive prover runs the same rounds against a transcript it writes: it
encodes each message as it is sent and derives each challenge from what it has written so far.
`RoundCodec w pSpec` is that wire for a schedule, in a monad `w`: an encoder for every message
round and a source for every challenge round. `Prover.runWith c P` runs `P` round by round as
`Prover.run` does (`Prover.runToRoundWith` is `Prover.runToRound`'s induction), each message
handed to `c.send` after it is computed and each challenge read from `c.draw` before it is
received; it returns the transcript and the prover's output.

Codecs compose as schedules do (`RoundCodec.append`, reading one side by one comparison with the
seam, as `LeanerVM.Protocol.ToArkLib.AppendLazy` does); there is one for each schedule built by
`LeanerVM.Protocol.ToArkLib.Schedule` from encoders of its messages and a source of its
challenges: `msg` for `say`, `chal` for `draw`, `chals` for `draws`, `round` and `rounds` for
sumcheck rounds, `step` for a grand-product layer and `gkr` for `gkrSpec`.

A prover of an oracle reduction with no shared oracle (`[]ₒ`) makes no query: its oracle
computations run in any monad (`runNoOracle`) and are pure (`runNoOracle_eq_pure`), with that
value as their one outcome (`support_eq_runNoOracle`); a verifier with no shared oracle that
returns a statement in `Id` outputs it with positive probability
(`Verifier.probEvent_pos_of_runNoOracle`).

**The run on given challenges.** `Prover.runWithChallenges ch` is the run whose challenge `i` is
`ch i`, deterministic. Three facts carry completeness from the oracle protocol to a run against a
wire:

* `runWith_eq_runWithChallenges`: whatever the wire, every run's transcript and output are the run
  on the transcript's own challenges (`SatisfiesM`, in any lawful monad);
* `simulateQ_run_eq_runWithChallenges`: ArkLib's `Prover.run`, the challenge oracle answered off a
  vector (`challengesImpl`), is the run on those challenges;
* `accepts_of_perfectCompleteness`: a perfectly complete reduction with no shared oracle accepts
  on every challenge vector: the verifier run on the transcript of the prover's run on any
  challenges returns a statement, the prover's, related to its output witness. The run on given
  challenges is reachable under uniform challenges (`mem_support_simulateQ_challenges`), and a
  probability-one event holds on every reachable outcome. So the verifier accepts any run equal to
  the run on its own challenges (`accepts_of_run`).
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

@[expose] public section

/-- The wire of a schedule in a monad `w`: each message round's encoder, each challenge round's
source. -/
structure RoundCodec (w : Type → Type) {n : ℕ} (pSpec : ProtocolSpec n) where
  /-- Write message `i`. -/
  send : (i : Fin n) → pSpec.dir i = .P_to_V → pSpec.Type i → w Unit
  /-- Read challenge `i`. -/
  draw : (i : Fin n) → pSpec.dir i = .V_to_P → w (pSpec.Type i)

namespace RoundCodec

variable {w : Type → Type}

/-- The empty schedule's wire. -/
def empty : RoundCodec w !p[] where
  send i := i.elim0
  draw i := i.elim0

/-- Two schedules side by side: a round is read by one comparison with the seam. -/
def append {m n : ℕ} {p₁ : ProtocolSpec m} {p₂ : ProtocolSpec n} (c₁ : RoundCodec w p₁)
    (c₂ : RoundCodec w p₂) : RoundCodec w (p₁ ++ₚ p₂) where
  send := fappend₂Lazy (A := Direction) (B := Type)
    (F := fun dir type ↦ dir = .P_to_V → type → w Unit) (α₁ := p₁.dir) (β₁ := p₂.dir)
    (α₂ := p₁.Type) (β₂ := p₂.Type) c₁.send c₂.send
  draw := fappend₂Lazy (A := Direction) (B := Type)
    (F := fun dir type ↦ dir = .V_to_P → w type) (α₁ := p₁.dir) (β₁ := p₂.dir)
    (α₂ := p₁.Type) (β₂ := p₂.Type) c₁.draw c₂.draw

/-- One message, written by `enc`. -/
def msg {M : Type} (enc : M → w Unit) : RoundCodec w (say M) where
  send | ⟨0, _⟩, _, x => enc x
  draw | ⟨0, _⟩, h => nomatch h

/-- One message of a literal schedule, written by `enc`. -/
def sendOne {M : Type} (enc : M → w Unit) : RoundCodec w ⟨!v[.P_to_V], !v[M]⟩ where
  send | ⟨0, _⟩, _, x => enc x
  draw | ⟨0, _⟩, h => nomatch h

/-- One challenge, read from `smp`. -/
def chal {C : Type} (smp : w C) : RoundCodec w (Protocol.draw C) where
  send | ⟨0, _⟩, h => nomatch h
  draw | ⟨0, _⟩, _ => smp

/-- `k` challenges, each read from `smp`. -/
def chals {C : Type} (smp : w C) : (k : ℕ) → RoundCodec w (draws C k)
  | 0 => empty
  | k + 1 => (chals smp k).append (chal smp)

/-- One sumcheck round: its polynomial written by `enc`, its challenge read from `smp`. -/
def round {C : Type} {d : ℕ} (enc : Vector C (d + 1) → w Unit) (smp : w C) :
    RoundCodec w (roundSpec C d) :=
  (msg enc).append (chal smp)

/-- `m` sumcheck rounds. -/
def rounds {C : Type} {d : ℕ} (enc : Vector C (d + 1) → w Unit) (smp : w C) :
    (m : ℕ) → RoundCodec w (roundsSpec C d m)
  | 0 => empty
  | m + 1 => (round enc smp).append (rounds enc smp m)

/-- One layer of a grand-product argument of radix `2 ^ ρ` at depth `m`: its combiner, its
rounds, the trees' values at the descendants written by `children`, and its combination
challenges. -/
def step {C : Type} {nside : ℕ} (ρ m : ℕ) (enc : Vector C (2 ^ ρ + 1) → w Unit)
    (children : (Fin nside → Vector C (2 ^ ρ)) → w Unit) (smp : w C) :
    RoundCodec w (stepSpec C nside ρ m) :=
  (((chal smp).append (rounds enc smp m)).append (msg children)).append (chals smp ρ)

/-- `k` layers of radix four from depth `m`. -/
def steps {C : Type} {nside : ℕ} (enc : Vector C (2 ^ 2 + 1) → w Unit)
    (children : (Fin nside → Vector C (2 ^ 2)) → w Unit) (smp : w C) :
    (k m : ℕ) → RoundCodec w (stepsSpec C nside k m)
  | 0, _ => empty
  | k + 1, m => (step 2 m enc children smp).append (steps enc children smp k (m + 2))

/-- The binary layer at the roots, when there is one. -/
def odd {C : Type} {nside : ℕ} (enc : Vector C (2 ^ 1 + 1) → w Unit)
    (children : (Fin nside → Vector C (2 ^ 1)) → w Unit) (smp : w C) :
    (r : ℕ) → RoundCodec w (oddSpec C nside r)
  | 0 => empty
  | _ + 1 => step 1 0 enc children smp

/-- The grand-product argument for trees of `2 ^ μ` leaves: the binary layer, the layers of radix
four, the last combiner. -/
def gkr {C : Type} {nside : ℕ} (μ : ℕ)
    (enc₁ : Vector C (2 ^ 1 + 1) → w Unit) (children₁ : (Fin nside → Vector C (2 ^ 1)) → w Unit)
    (enc₂ : Vector C (2 ^ 2 + 1) → w Unit) (children₂ : (Fin nside → Vector C (2 ^ 2)) → w Unit)
    (smp : w C) : RoundCodec w (gkrSpec C nside μ) :=
  ((odd enc₁ children₁ smp (μ % 2)).append (steps enc₂ children₂ smp (μ / 2) (μ % 2))).append
    (chal smp)

end RoundCodec

/-! ## The run -/

/-- An oracle computation with no oracle, run in any monad: it makes no query. -/
def runNoOracle {w : Type → Type} [Monad w] {α : Type} (oa : OracleComp []ₒ α) : w α :=
  simulateQ (fun t ↦ isEmptyElim t : QueryImpl []ₒ w) oa

namespace Prover

variable {w : Type → Type} [Monad w] {S W S' W' : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  (c : RoundCodec w pSpec) (P : Prover []ₒ S W S' W' pSpec)

/-- Round `j` from the transcript and the state before it: a message is computed, then written;
a challenge is read, then received. -/
def stepWith (j : Fin n) (tr : pSpec.Transcript j.castSucc) (st : P.PrvState j.castSucc) :
    w (pSpec.Transcript j.succ × P.PrvState j.succ) :=
  match hDir : pSpec.dir j with
  | .V_to_P => do
    let x ← c.draw j hDir
    let f ← runNoOracle (P.receiveChallenge ⟨j, hDir⟩ st)
    return ⟨tr.concat x, f x⟩
  | .P_to_V => do
    let r ← runNoOracle (P.sendMessage ⟨j, hDir⟩ st)
    c.send j hDir r.1
    return ⟨tr.concat r.1, r.2⟩

/-- Round `j` after the rounds before it (`Prover.processRound`). -/
def processRoundWith (j : Fin n)
    (cur : w (pSpec.Transcript j.castSucc × P.PrvState j.castSucc)) :
    w (pSpec.Transcript j.succ × P.PrvState j.succ) := do
  let r ← cur
  stepWith c P j r.1 r.2

/-- The rounds up to `i`, from the statement and the witness (`Prover.runToRound`). -/
def runToRoundWith (i : Fin (n + 1)) (stmt : S) (wit : W) :
    w (pSpec.Transcript i × P.PrvState i) :=
  Fin.induction (pure ⟨default, P.input (stmt, wit)⟩) (processRoundWith c P) i

/-- The rounds up to `j + 1`: round `j` after the rounds before it. -/
theorem runToRoundWith_succ (stmt : S) (wit : W) (j : Fin n) :
    runToRoundWith c P j.succ stmt wit =
      processRoundWith c P j (runToRoundWith c P j.castSucc stmt wit) := by
  simp only [runToRoundWith, Fin.induction_succ]

/-- **The run against a wire**: every round, each message written as it is sent and each
challenge read from the wire; the transcript and the prover's output (`Prover.run`). -/
def runWith (stmt : S) (wit : W) : w (pSpec.FullTranscript × S' × W') := do
  let r ← runToRoundWith c P (Fin.last n) stmt wit
  let out ← runNoOracle (P.output r.2)
  return ⟨r.1, out⟩

end Prover

/-! ## The run on given challenges -/

/-- The wire of given challenges, in `Id`: nothing is written, challenge `i` is read off the
vector. -/
def RoundCodec.ofChallenges {n : ℕ} {pSpec : ProtocolSpec n} (ch : pSpec.Challenges) :
    RoundCodec Id pSpec where
  send _ _ _ := pure ()
  draw i h := pure (ch ⟨i, h⟩)

/-- An oracle computation with no oracle is pure: its value is the one it returns in `Id`. -/
theorem runNoOracle_eq_pure {w : Type → Type} [Monad w] [LawfulMonad w] {α : Type}
    (oa : OracleComp []ₒ α) : runNoOracle (w := w) oa = pure (Id.run (runNoOracle oa)) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [runNoOracle]
  | query_bind t _ _ => exact isEmptyElim t

/-- An oracle computation with no oracle has one outcome: the value it returns in `Id`. -/
theorem support_eq_runNoOracle {α : Type} (oa : OracleComp []ₒ α) :
    support oa = {Id.run (runNoOracle oa)} := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [runNoOracle]
  | query_bind t _ _ => exact isEmptyElim t

/-- A verifier with no oracle whose run on a transcript returns `so` in `Id` outputs, under any
implementation and initial state, a statement satisfying every property of `so` with positive
probability. -/
theorem Verifier.probEvent_pos_of_runNoOracle {StmtIn StmtOut : Type} {n : ℕ}
    {pSpec : ProtocolSpec n} (V : Verifier []ₒ StmtIn StmtOut pSpec) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) (stmt : StmtIn)
    (tr : pSpec.FullTranscript) {so : StmtOut}
    (h : Id.run (runNoOracle (V.run stmt tr).run) = some so) (P : StmtOut → Prop) (hP : P so) :
    0 < Pr{let stmtOut ← OptionT.mk do (simulateQ impl (V.run stmt tr)).run' (← init)}[
      P stmtOut] := by
  rw [OptionT.prEvent_mk_simulateQ_run'_eq_one_of_support init impl _ _ fun o ho ↦ ?_]
  · exact one_pos
  rw [support_eq_runNoOracle, Set.mem_singleton_iff] at ho
  exact ⟨so, ho.trans h, hP⟩

namespace Prover

variable {S W S' W' : Type} {n : ℕ} {pSpec : ProtocolSpec n} (P : Prover []ₒ S W S' W' pSpec)

/-- **The run on given challenges**: challenge `i` is `ch i`, every message the prover's. -/
def runWithChallenges (ch : pSpec.Challenges) (stmt : S) (wit : W) :
    pSpec.FullTranscript × S' × W' :=
  Id.run (runWith (RoundCodec.ofChallenges ch) P stmt wit)

/-- The challenges a partial transcript holds are those of the vector `ch`. -/
def ChallengesAgree {i : Fin (n + 1)} (tr : pSpec.Transcript i) (ch : pSpec.Challenges) : Prop :=
  ∀ (j : pSpec.ChallengeIdx) (hj : j.1.val < i.val), ch j = tr ⟨j.1.val, hj⟩

/-- A run's rounds up to `i` from the statement and the witness: the run on every challenge vector
that agrees with the challenges it holds. -/
def IsRunTo (stmt : S) (wit : W) {i : Fin (n + 1)} (r : pSpec.Transcript i × P.PrvState i) :
    Prop :=
  ∀ ch : pSpec.Challenges, ChallengesAgree r.1 ch →
    Id.run (runToRoundWith (RoundCodec.ofChallenges ch) P i stmt wit) = r

/-- Agreeing with a transcript extended by one round is agreeing with the transcript. -/
theorem ChallengesAgree.of_concat {j : Fin n} {tr : pSpec.Transcript j.castSucc}
    {x : pSpec.Type j} {ch : pSpec.Challenges}
    (h : ChallengesAgree (tr.concat x : pSpec.Transcript j.succ) ch) : ChallengesAgree tr ch :=
  fun k hk ↦ (h k (by simp only [Fin.val_succ, Fin.val_castSucc] at hk ⊢; omega)).trans
    (eq_of_heq (Transcript.concat_apply_lt tr x k.1.val hk _))

/-- Agreeing with a transcript extended by a challenge is agreeing on that challenge. -/
theorem ChallengesAgree.last {j : Fin n} {tr : pSpec.Transcript j.castSucc}
    {x : pSpec.Type j} {ch : pSpec.Challenges} (hDir : pSpec.dir j = .V_to_P)
    (h : ChallengesAgree (tr.concat x : pSpec.Transcript j.succ) ch) : ch ⟨j, hDir⟩ = x :=
  (h ⟨j, hDir⟩ (by simp)).trans (eq_of_heq (Transcript.concat_apply_last tr x j.val rfl _))

variable {w : Type → Type} [Monad w] [LawfulMonad w] (c : RoundCodec w pSpec)

/-- Every run's rounds up to `i`, whatever the wire, are the run on its own challenges. -/
theorem runToRoundWith_isRunTo (stmt : S) (wit : W) (i : Fin (n + 1)) :
    SatisfiesM (IsRunTo P stmt wit) (runToRoundWith c P i stmt wit) := by
  induction i using Fin.induction with
  | zero => exact SatisfiesM.pure fun _ _ ↦ rfl
  | succ j ih =>
    rw [runToRoundWith_succ]
    refine SatisfiesM.bind_pre (ih.imp fun {r} hr ↦ ?_)
    obtain ⟨tr, st⟩ := r
    have key : ∀ ch, ChallengesAgree tr ch →
        Id.run (runToRoundWith (RoundCodec.ofChallenges ch) P j.succ stmt wit) =
          Id.run (stepWith (RoundCodec.ofChallenges ch) P j tr st) := fun ch hch ↦ by
      rw [runToRoundWith_succ, processRoundWith, show runToRoundWith (RoundCodec.ofChallenges ch) P
        j.castSucc stmt wit = pure (tr, st) from hr ch hch]
      rfl
    unfold stepWith
    split
    · rename_i hDir
      rw [runNoOracle_eq_pure]
      refine SatisfiesM.bind_pre (SatisfiesM.of_true fun x ↦ ?_)
      simp only [pure_bind]
      refine SatisfiesM.pure fun ch hch ↦ ?_
      rw [key ch hch.of_concat, stepWith]
      split
      · simp only [RoundCodec.ofChallenges, pure_bind, hch.last ‹_›]
        rfl
      · rename_i hDir'
        exact absurd (hDir'.symm.trans hDir) (by decide)
    · rename_i hDir
      rw [runNoOracle_eq_pure]
      simp only [pure_bind]
      refine SatisfiesM.bind_pre (SatisfiesM.of_true fun _ ↦ ?_)
      refine SatisfiesM.pure fun ch hch ↦ ?_
      rw [key ch hch.of_concat, stepWith]
      split
      · rename_i hDir'
        exact absurd (hDir'.symm.trans hDir) (by decide)
      · simp only [RoundCodec.ofChallenges, pure_bind]
        rfl

/-- **Every run against a wire is the run on its own challenges**: whatever the wire, the
transcript and the output the run returns are `runWithChallenges` at the transcript's
challenges. -/
theorem runWith_eq_runWithChallenges (stmt : S) (wit : W) :
    SatisfiesM (fun r ↦ r = runWithChallenges P r.1.challenges stmt wit)
      (runWith c P stmt wit) := by
  unfold runWith
  refine SatisfiesM.bind_pre ((runToRoundWith_isRunTo P c stmt wit (Fin.last n)).imp
    fun {r} hr ↦ ?_)
  rw [runNoOracle_eq_pure]
  simp only [pure_bind]
  refine SatisfiesM.pure ?_
  generalize hch : FullTranscript.challenges (pSpec := pSpec) r.1 = ch
  have h₀ := hr ch fun j _ ↦ by rw [← hch]; rfl
  show (r.1, Id.run (runNoOracle (P.output r.2))) = runWithChallenges P ch stmt wit
  rw [show runWithChallenges P ch stmt wit =
    ((Id.run (runToRoundWith (RoundCodec.ofChallenges ch) P (Fin.last n) stmt wit)).1,
      Id.run (runNoOracle (P.output
        (Id.run (runToRoundWith (RoundCodec.ofChallenges ch) P (Fin.last n) stmt wit)).2)))
    from rfl, h₀]


/-! ## The oracle run on given challenges -/

section Simulate

variable {r : Type → Type} [Monad r] [LawfulMonad r]

/-- The challenge oracle answered off a vector. -/
def challengesImpl (ch : pSpec.Challenges) :
    QueryImpl ([pSpec.Challenge]ₒ'challengeOracleInterface) r :=
  fun q ↦ (pure (ch q.1) : r (pSpec.Challenge q.1))

omit [LawfulMonad r] in
/-- Simulating an oracle computation with no oracle is running it. -/
theorem simulateQ_empty {α : Type} (oa : OracleComp []ₒ α) :
    simulateQ (fun t ↦ isEmptyElim t : QueryImpl []ₒ r) oa = runNoOracle oa :=
  rfl

/-- A challenge query answered off the vector. -/
theorem simulateQ_liftM_getChallenge (ch : pSpec.Challenges) (i : pSpec.ChallengeIdx) :
    simulateQ ((fun t ↦ isEmptyElim t : QueryImpl []ₒ r) + challengesImpl (r := r) ch)
      (liftM (pSpec.getChallenge i) : OracleComp ([]ₒ + [pSpec.Challenge]ₒ) _) = pure (ch i) := by
  rw [QueryImpl.simulateQ_add_liftM_right]
  exact (simulateQ_spec_query (challengesImpl ch) ⟨i, ()⟩).trans rfl

omit [LawfulMonad r] in
/-- ArkLib's round `j` binds the rounds before it. -/
theorem processRound_eq_bind (j : Fin n)
    (cur : OracleComp ([]ₒ + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × P.PrvState j.castSucc)) :
    Prover.processRound j P cur = cur >>= fun x ↦ Prover.processRound j P (pure x) := by
  simp only [Prover.processRound, pure_bind]

/-- ArkLib's rounds up to `i`, the challenge oracle answered off a vector, are the run on those
challenges. -/
theorem simulateQ_runToRound (ch : pSpec.Challenges) (stmt : S) (wit : W) (i : Fin (n + 1)) :
    simulateQ ((fun t ↦ isEmptyElim t : QueryImpl []ₒ r) + challengesImpl (r := r) ch)
        (P.runToRound i stmt wit) =
      pure (Id.run (runToRoundWith (w := Id) (RoundCodec.ofChallenges ch) P i stmt wit)) := by
  induction i using Fin.induction with
  | zero => simp [Prover.runToRound, runToRoundWith]
  | succ j ih =>
    rw [Prover.runToRound_succ, runToRoundWith_succ, processRound_eq_bind, simulateQ_bind, ih,
      pure_bind]
    unfold processRoundWith
    generalize runToRoundWith (RoundCodec.ofChallenges ch) P j.castSucc stmt wit = Y
    obtain ⟨tr, st⟩ := Y
    unfold Prover.processRound
    simp only [stepWith]
    split
    · rename_i hDir
      simp only [pure_bind, simulateQ_bind, QueryImpl.simulateQ_add_liftM_left,
        simulateQ_liftM_getChallenge, simulateQ_empty, simulateQ_pure]
      rw [runNoOracle_eq_pure (w := r)]
      simp only [pure_bind]
      split
      · rfl
      · rename_i hDir'
        exact absurd (hDir'.symm.trans hDir) (by decide)
    · rename_i hDir
      simp only [pure_bind, simulateQ_bind, QueryImpl.simulateQ_add_liftM_left, simulateQ_empty]
      rw [runNoOracle_eq_pure (w := r)]
      simp only [pure_bind]
      split
      · rename_i hDir'
        exact absurd (hDir'.symm.trans hDir) (by decide)
      · generalize Id.run (runNoOracle (P.sendMessage ⟨j, hDir⟩ st)) = Z
        obtain ⟨m, st'⟩ := Z
        simp only [simulateQ_pure]
        rfl

/-- **ArkLib's run, the challenge oracle answered off a vector, is the run on those challenges**:
pure, at `runWithChallenges`. -/
theorem simulateQ_run_eq_runWithChallenges (ch : pSpec.Challenges) (stmt : S) (wit : W) :
    simulateQ ((fun t ↦ isEmptyElim t : QueryImpl []ₒ r) + challengesImpl (r := r) ch)
        (P.run stmt wit) =
      pure (runWithChallenges P ch stmt wit) := by
  unfold Prover.run runWithChallenges runWith
  rw [simulateQ_bind, simulateQ_runToRound, pure_bind]
  generalize runToRoundWith (RoundCodec.ofChallenges ch) P (Fin.last n) stmt wit = Y
  obtain ⟨tr, st⟩ := Y
  simp only [simulateQ_bind, QueryImpl.simulateQ_add_liftM_left, simulateQ_empty]
  rw [runNoOracle_eq_pure (w := r)]
  simp only [pure_bind, simulateQ_pure]
  rfl

end Simulate

/-! ## Perfect completeness on every challenge vector -/

section Complete

omit [LawfulMonad w] in
/-- The run with the challenge oracle answered off a vector is reachable when the challenges are
drawn uniformly, from any state of the shared oracle. -/
theorem mem_support_simulateQ_challenges [∀ i, SampleableType (pSpec.Challenge i)] {σ α : Type}
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) (ch : pSpec.Challenges)
    (oa : OracleComp ([]ₒ + [pSpec.Challenge]ₒ) α) (s : σ) :
    Id.run (simulateQ ((fun t ↦ isEmptyElim t : QueryImpl []ₒ Id) + challengesImpl (r := Id) ch)
        oa) ∈
      support ((simulateQ (QueryImpl.addLift impl challengeQueryImpl :
        QueryImpl ([]ₒ + [pSpec.Challenge]ₒ) (StateT σ ProbComp)) oa).run' s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    rcases t with t | q
    · exact isEmptyElim t
    · simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr,
        QueryImpl.addLift_def, QueryImpl.liftTarget_apply, challengesImpl, challengeQueryImpl,
        StateT.run'_eq, StateT.run_bind, MonadAttach.support_map, MonadAttach.support_bind,
        Set.mem_image, Set.mem_iUnion, exists_prop]
      have h₁ := ih (ch q.1) s
      rw [StateT.run'_eq, MonadAttach.support_map] at h₁
      obtain ⟨x, hx, hx1⟩ := h₁
      refine ⟨x, ⟨(ch q.1, s), ?_, hx⟩, ?_⟩
      · show (ch q.1, s) ∈ support (($ᵗ pSpec.Challenge q.1) >>= fun a ↦ pure (a, s))
        exact MonadAttach.mem_support_bind.mpr
          ⟨ch q.1, mem_support_uniformSample _, MonadAttach.mem_support_pure.mpr rfl⟩
      · exact hx1

/-- An oracle computation with no oracle, lifted into a computation that may fail on any oracle,
is pure. -/
theorem liftM_noOracle {β : Type} (X : OracleComp []ₒ β) :
    (monadLift X : OptionT (OracleComp ([]ₒ + [pSpec.Challenge]ₒ)) β) =
      pure (Id.run (runNoOracle X)) := by
  induction X using OracleComp.inductionOn with
  | pure x => exact liftM_pure x
  | query_bind t _ _ => exact isEmptyElim t

/-- A reduction's run, the challenge oracle answered off a vector: the prover's run on those
challenges, then the verifier on its transcript. -/
theorem simulateQ_reduction_run {StmtIn WitIn StmtOut WitOut : Type}
    (R : Reduction []ₒ StmtIn WitIn StmtOut WitOut pSpec) (ch : pSpec.Challenges)
    (stmt : StmtIn) (wit : WitIn) :
    Id.run (simulateQ ((fun t ↦ isEmptyElim t : QueryImpl []ₒ Id) + challengesImpl (r := Id) ch)
        (R.run stmt wit).run) =
      (Id.run (runNoOracle (R.verifier.run stmt
        (runWithChallenges R.prover ch stmt wit).1).run)).map
          fun so ↦ (runWithChallenges R.prover ch stmt wit, so) := by
  unfold Reduction.run
  simp only [OptionT.run_bind, liftM, OptionT.run_monadLift, Option.elimM, bind_map_left,
    Option.elim, simulateQ_bind, monadLift_self, simulateQ_run_eq_runWithChallenges, pure_bind]
  rw [liftM_noOracle]
  simp only [OptionT.run_pure, simulateQ_pure]
  rcases Id.run (runNoOracle (R.verifier.run stmt (runWithChallenges R.prover ch stmt wit).1).run)
    with _ | so
  · rfl
  · rfl

/-- **A perfectly complete reduction accepts on every challenge vector**: on an input of the input
relation, the verifier run on the transcript of the prover's run on any challenges returns a
statement, which is the prover's and is related to the prover's output witness. -/
theorem accepts_of_perfectCompleteness [∀ i, SampleableType (pSpec.Challenge i)]
    {StmtIn WitIn StmtOut WitOut σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) {relIn : Set (StmtIn × WitIn)}
    {relOut : Set (StmtOut × WitOut)} (R : Reduction []ₒ StmtIn WitIn StmtOut WitOut pSpec)
    (h : R.perfectCompleteness init impl relIn relOut) {stmt : StmtIn} {wit : WitIn}
    (hin : (stmt, wit) ∈ relIn) (ch : pSpec.Challenges) :
    ∃ so, Id.run (runNoOracle (R.verifier.run stmt
        (runWithChallenges R.prover ch stmt wit).1).run) = some so ∧
      (so, (runWithChallenges R.prover ch stmt wit).2.2) ∈ relOut ∧
        (runWithChallenges R.prover ch stmt wit).2.1 = so := by
  have h₁ := (_root_.Reduction.perfectCompleteness_eq_prob_one (init := init) (impl := impl)).mp h
    stmt wit hin
  rw [OracleComp.OptionT.prEvent_mk_eq_one_iff] at h₁
  obtain ⟨s₀, hs₀⟩ := support_nonempty init
  have hmem := mem_support_simulateQ_challenges impl ch (R.run stmt wit).run s₀
  rw [simulateQ_reduction_run] at hmem
  obtain ⟨x, hx, hp⟩ := h₁ _ (MonadAttach.mem_support_bind.mpr ⟨s₀, hs₀, hmem⟩)
  rcases hv : Id.run (runNoOracle (R.verifier.run stmt
    (runWithChallenges R.prover ch stmt wit).1).run) with _ | so
  · rw [hv] at hx
    cases hx
  · rw [hv] at hx
    cases hx
    exact ⟨so, rfl, hp⟩

/-- **A perfectly complete reduction accepts a run on its own challenges**: on an input of the
input relation, the verifier accepts the transcript of any run of the prover equal to the run on
that transcript's challenges. -/
theorem accepts_of_run [∀ i, SampleableType (pSpec.Challenge i)]
    {StmtIn WitIn StmtOut WitOut σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) {relIn : Set (StmtIn × WitIn)}
    {relOut : Set (StmtOut × WitOut)} {R : Reduction []ₒ StmtIn WitIn StmtOut WitOut pSpec}
    (h : R.perfectCompleteness init impl relIn relOut) {stmt : StmtIn} {wit : WitIn}
    {r : pSpec.FullTranscript × StmtOut × WitOut}
    (hr : r = runWithChallenges R.prover r.1.challenges stmt wit) (hin : (stmt, wit) ∈ relIn) :
    ∃ so, Id.run (runNoOracle (R.verifier.run stmt r.1).run) = some so := by
  obtain ⟨so, h₁, -, -⟩ := accepts_of_perfectCompleteness init impl R h hin r.1.challenges
  rw [← hr] at h₁
  exact ⟨so, h₁⟩

end Complete

end Prover

end
end LeanerVM.Protocol
