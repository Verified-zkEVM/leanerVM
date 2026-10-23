/-
  LeanerVM.Protocol.ToArkLib.RunCodec

  An honest prover run round by round in any monad, each message handed to an encoder and each
  challenge taken from a source in that monad, as a Fiat–Shamir prover runs; the encoders and
  sources of the schedules of `LeanerVM.Protocol.ToArkLib.Schedule`. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.AppendLazy
public import LeanerVM.Protocol.ToArkLib.StepSchedule

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
computations run in any monad (`runNoOracle`).
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

/-- Round `j`, from the transcript and the state before it: a message is computed, then written;
a challenge is read, then received (`Prover.processRound`). -/
def processRoundWith (j : Fin n)
    (cur : w (pSpec.Transcript j.castSucc × P.PrvState j.castSucc)) :
    w (pSpec.Transcript j.succ × P.PrvState j.succ) := do
  let ⟨tr, st⟩ ← cur
  match hDir : pSpec.dir j with
  | .V_to_P => do
    let x ← c.draw j hDir
    let f ← runNoOracle (P.receiveChallenge ⟨j, hDir⟩ st)
    return ⟨tr.concat x, f x⟩
  | .P_to_V => do
    let ⟨msg, st'⟩ ← runNoOracle (P.sendMessage ⟨j, hDir⟩ st)
    c.send j hDir msg
    return ⟨tr.concat msg, st'⟩

/-- The rounds up to `i`, from the statement and the witness (`Prover.runToRound`). -/
def runToRoundWith (i : Fin (n + 1)) (stmt : S) (wit : W) :
    w (pSpec.Transcript i × P.PrvState i) :=
  Fin.induction (pure ⟨default, P.input (stmt, wit)⟩) (processRoundWith c P) i

/-- **The run against a wire**: every round, each message written as it is sent and each
challenge read from the wire; the transcript and the prover's output (`Prover.run`). -/
def runWith (stmt : S) (wit : W) : w (pSpec.FullTranscript × S' × W') := do
  let ⟨tr, st⟩ ← runToRoundWith c P (Fin.last n) stmt wit
  return ⟨tr, ← runNoOracle (P.output st)⟩

end Prover

end
end LeanerVM.Protocol
