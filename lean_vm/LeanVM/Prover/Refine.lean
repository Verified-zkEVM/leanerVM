/-
  LeanVM.Prover.Refine

  The statement's script runner is the specification's compiled honest prover: running a script
  against the verifier's program (`runFrom`, `runScript`) is the commit-once honest prover
  (`proveFromM`, `proveM`) of the strategy that replays the script, in every monad, for every
  hash and permutation.
-/

module

public import Statement.Prover.Run
public import Statement.LeanVmGuest
public import LeanVM.Protocol.Whir.Complete.Script
public import LeanVM.Protocol.Compile.Rom.Complete
public import LeanVM.Protocol.Verifier.Cost

/-!
# The runner is the specification's prover

`runFrom H F fuel P S sp cs` (`Statement/Prover/Run.lean`) carries the script's current node
`S : Option (Script β)`; the specification's honest prover `proveFromM H F (Strategy.ofScript Hs 0)
fuel P sp h cs` (`LeanVM/Protocol/Compile/Rom/Prover.lean`) carries the history `h` and replays
`Hs` along it (`Script.walk`). Both build each commitment's tree once (`buildTreeM`), read the
openings off it, and search nonces with `findNonceM`: they make the same calls in the same order.
Along a history whose walk ends at the runner's node (`Hs.walk h = S`), they are equal
(`runFrom_eq_proveFromM`): the runner's moves on a matching node are the replay's (`msgAt`,
`wordAt`), and off one (`0`, the empty rows) too.

* `runScript_eq_proveM`: from a seed, the runner's proof is the honest prover's, or the empty
  proof where it fails.
* `honestComp_ofScript`: the specification's honest prover of the random-oracle model
  (`Rom.honestComp`) of a script's replay is the seed (`seedWith`), then the runner, with every
  hash and permutation a query; `honestComp_ofScript_leanVm` at leanVM's seed and program.
* `simulateQ_runScript`, `simulateQ_seedRunScript`: answering the queries by any implementation
  is running with it; at Keccak-256 and Keccak-f[1600] (`Guest.Budget.keccakImpl`) the runner in
  `Id` (`atKeccak_seedRunScript`).
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Whir.Complete LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier
open OracleComp OracleSpec

@[expose] public section

/-! ## The runner's node is the replay's -/

namespace Script

variable {β : Type}

theorem msgAt_eq (Hs : Script β) (l : List Ev) : Hs.msgAt l = msgOf (Hs.walk l) := by
  unfold msgAt
  generalize Hs.walk l = o
  rcases o with _ | (_ | _ | _ | _ | _ | _) <;> rfl

theorem wordAt_eq (Hs : Script β) (l : List Ev) : Hs.wordAt l = wordOf (Hs.walk l) := by
  unfold wordAt
  generalize Hs.walk l = o
  rcases o with _ | (_ | _ | _ | _ | _ | _) <;> rfl

theorem afterSend_eq (S : Option (Script β)) (x : E) :
    afterSend S = S.bind fun H ↦ H.step (Ev.read x) := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> rfl

theorem afterSample_eq (S : Option (Script β)) (c : E) :
    afterSample c S = S.bind fun H ↦ H.step (Ev.sample c) := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> rfl

theorem afterGrind_eq (S : Option (Script β)) (b : ℕ) :
    afterGrind S = S.bind fun H ↦ H.step (Ev.grind b) := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> rfl

theorem afterCommit_eq (S : Option (Script β)) (ht w : ℕ) (W : Word) :
    afterCommit S = S.bind fun H ↦ H.step (Ev.commit ht w W) := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> rfl

theorem afterQuery_eq (S : Option (Script β)) (rows : List (List K)) :
    afterQuery rows S = S.bind fun H ↦ H.step (Ev.query rows) := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> rfl

end Script

/-- The replay's scalar at a history is the runner's at the walk's node. -/
theorem ofScript_msg {β : Type} (Hs : Script β) (h : List Ev) :
    (Strategy.ofScript Hs 0).msg h = Script.msgOf (Hs.walk h) := by
  show Hs.msgAt (h.drop 0) = _
  rw [List.drop_zero, Script.msgAt_eq]

/-- The replay's word at a history is the runner's at the walk's node. -/
theorem ofScript_word {β : Type} (Hs : Script β) (h : List Ev) :
    (Strategy.ofScript Hs 0).word h = Script.wordOf (Hs.walk h) := by
  show Hs.wordAt (h.drop 0) = _
  rw [List.drop_zero, Script.wordAt_eq]

/-! ## The bridge -/

section Bridge

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KState → m KState)

/-- **The runner is the specification's honest prover**: along a history whose walk through the
script ends at the runner's node, the run from there is the commit-once honest prover of the
script's replay, in every monad, for every hash and permutation. -/
theorem runFrom_eq_proveFromM (fuel : ℕ) {α β : Type} (Hs : Script β) :
    ∀ (P : Prog α) (S : Option (Script β)) (sp : Sponge) (h : List Ev) (cs : List Tree),
      Hs.walk h = S →
      runFrom H F fuel P S sp cs = proveFromM H F (Strategy.ofScript Hs 0) fuel P sp h cs := by
  intro P
  induction P with
  | ret a => intros; rfl
  | fail => intros; rfl
  | read k ih =>
    intro S sp h cs hw
    have hm := ofScript_msg Hs h
    rw [hw] at hm
    simp only [runFrom, proveFromM]
    rw [hm]
    congr 1; funext sp'; congr 1
    exact ih _ _ _ _ _ (by rw [Script.walk_append, hw, Script.afterSend_eq])
  | sample k ih =>
    intro S sp h cs hw
    simp only [runFrom, proveFromM]
    congr 1; funext r
    exact ih _ _ _ _ _ (by rw [Script.walk_append, hw, Script.afterSample_eq])
  | grind bits k ih =>
    intro S sp h cs hw
    simp only [runFrom, proveFromM]
    congr 1; funext o
    rcases o with _ | n
    · rfl
    · simp only
      congr 1; funext r; congr 1
      exact ih _ _ _ _ (by rw [Script.walk_append, hw, Script.afterGrind_eq _ bits])
  | commit ht w k ih =>
    intro S sp h cs hw
    have hm := ofScript_word Hs h
    rw [hw] at hm
    simp only [runFrom, proveFromM]
    rw [hm]
    congr 1; funext tree; congr 1; funext sp0; congr 1; funext sp1; congr 1
    exact ih _ _ _ _ (by rw [Script.walk_append, hw, Script.afterCommit_eq _ ht w])
  | query i ps k ih =>
    intro S sp h cs hw
    simp only [runFrom, proveFromM]
    split
    · rename_i _ hc
      rw [hc]
    · rename_i _ tree hc
      rw [hc]
      simp only
      congr 1
      exact ih _ _ _ _ _ (by rw [Script.walk_append, hw, Script.afterQuery_eq])

variable [LawfulMonad m]

/-- **From a seed**: the runner's proof is the honest prover's of the script's replay, the empty
proof where a proof of work fails. -/
theorem runScript_eq_proveM (P : Prog Bool) {β : Type} (Hs : Script β) (seed : KState)
    (fuel : ℕ) :
    runScript H F P Hs seed fuel =
      (fun r ↦ r.getD ⟨[], []⟩) <$> proveM H F P (Strategy.ofScript Hs 0) seed fuel := by
  unfold runScript proveM
  rw [runFrom_eq_proveFromM H F fuel Hs P (some Hs) ⟨seed, []⟩ [] [] rfl, map_bind]
  simp only [map_pure]

end Bridge

/-- **The specification's honest prover of a script's replay is the runner**, with every hash
and permutation a query: the seed, then the script run against the program. -/
theorem honestComp_ofScript (σ : Seed) (P : Prog Bool) {β : Type} (Hs : Script β) (fuel : ℕ) :
    Rom.honestComp σ P (Strategy.ofScript Hs 0) fuel = (do
      let seed ← σ.run queryH queryF
      runScript queryH queryF P Hs seed fuel) := by
  unfold Rom.honestComp
  congr 1; funext seed
  rw [runScript_eq_proveM, map_eq_bind_pure_comp]
  rfl

/-- **At leanVM's seed and program.** -/
theorem honestComp_ofScript_leanVm (bytecode : List K) (publicInput : Digest) {β : Type}
    (Hs : Script β) (fuel : ℕ) :
    Rom.honestComp (leanVmSeed bytecode publicInput) (leanVmProgram bytecode publicInput)
        (Strategy.ofScript Hs 0) fuel = (do
      let seed ← seedWith queryH queryF bytecode publicInput
      runScript queryH queryF (leanVmProgram bytecode publicInput) Hs seed fuel) := by
  rw [honestComp_ofScript, seedRun_leanVmSeed]

/-! ## Simulation -/

section Commute

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl HashSpec r)

/-- **The runner commutes with simulation.** -/
theorem simulateQ_runScript (P : Prog Bool) {β : Type} (Hs : Script β) (seed : KState)
    (fuel : ℕ) :
    simulateQ impl (runScript queryH queryF P Hs seed fuel) =
      runScript (implH impl) (implF impl) P Hs seed fuel := by
  rw [runScript_eq_proveM, runScript_eq_proveM, simulateQ_map, simulateQ_proveM]

/-- The seed commutes with simulation. -/
theorem simulateQ_seedWith (bytecode : List K) (publicInput : Digest) :
    simulateQ impl (seedWith queryH queryF bytecode publicInput) =
      seedWith (implH impl) (implF impl) bytecode publicInput := by
  rw [← seedRun_leanVmSeed, ← seedRun_leanVmSeed, simulateQ_seedRun]

/-- **The seed, then the runner, commute with simulation.** -/
theorem simulateQ_seedRunScript (bytecode : List K) (publicInput : Digest) (P : Prog Bool)
    {β : Type} (Hs : Script β) (fuel : ℕ) :
    simulateQ impl (do
        let seed ← seedWith queryH queryF bytecode publicInput
        runScript queryH queryF P Hs seed fuel) = (do
      let seed ← seedWith (implH impl) (implF impl) bytecode publicInput
      runScript (implH impl) (implF impl) P Hs seed fuel) := by
  rw [simulateQ_bind, simulateQ_seedWith]
  congr 1; funext seed
  exact simulateQ_runScript impl P Hs seed fuel

end Commute

/-- **The runner with Keccak**: answering the runner's queries with Keccak-256 and
Keccak-f[1600] (`Guest.Budget.keccakImpl`) is running it in `Id` with them. -/
theorem simulateQ_keccak_runScript (P : Prog Bool) {β : Type} (Hs : Script β) (seed : KState)
    (fuel : ℕ) :
    simulateQ Guest.Budget.keccakImpl (runScript queryH queryF P Hs seed fuel) =
      runScript (m := Id) keccak256 keccakF P Hs seed fuel :=
  simulateQ_runScript Guest.Budget.keccakImpl P Hs seed fuel

/-- The seed with Keccak. -/
theorem simulateQ_keccak_seedWith (bytecode : List K) (publicInput : Digest) :
    simulateQ Guest.Budget.keccakImpl (seedWith queryH queryF bytecode publicInput) =
      seedWith (m := Id) keccak256 keccakF bytecode publicInput :=
  simulateQ_seedWith Guest.Budget.keccakImpl bytecode publicInput

/-- **An honest prover that seeds and runs a script, with the deployed Keccak** (`atKeccak`), is
the runner in `Id` with Keccak-256 and Keccak-f[1600]. -/
theorem atKeccak_seedRunScript (A : HonestProver) {prog : Program} {input : PublicInput}
    {t : Trace prog} {ρ fuel : ℕ} {β : Type} (Hs : Script β)
    (hA : A prog input t ρ fuel = (do
      let seed ← seedWith queryH queryF (bytecodeWords prog) (publicDigest input)
      runScript queryH queryF (leanVmProgram (bytecodeWords prog) (publicDigest input)) Hs seed
        fuel)) :
    Guest.Budget.atKeccak A prog input t ρ fuel =
      runScript (m := Id) keccak256 keccakF
        (leanVmProgram (bytecodeWords prog) (publicDigest input)) Hs
        (seedWith (m := Id) keccak256 keccakF (bytecodeWords prog) (publicDigest input)) fuel := by
  unfold Guest.Budget.atKeccak
  rw [hA, simulateQ_seedRunScript]
  rfl

end

end LeanVM.Prover
