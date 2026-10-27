/-
  LeanerVM.Protocol.AdaptiveGame

  The random-oracle game in which the cheating prover chooses the statement: it outputs the
  program, the public input and the proof, and the verifier runs on the statement it chose.
-/

module

public import LeanerVM.Protocol.Replay

/-!
# The adaptive game

Category A. In the game of `LeanerVM.Protocol.RandomOracleGame` the program and the public input
are fixed before the prover runs. Here the prover (`AdaptiveAdversary`) outputs them with its
proof, after any number of hash queries, and the verifier runs on the statement it output
(`adaptiveGame`); a run records that statement beside the proof, the two logs and the verdict
(`AdaptiveRun`).

* `adaptiveGame_const`: for a prover whose statement is fixed, the adaptive game is the game on
  that statement.
* `mem_support_loggedGame_of_adaptive`: a run of the adaptive game is a run of the game on the
  statement the prover chose, for the prover that outputs only the proof, so that
  `Core.core_of_mem_support` applies to it at that statement.
* `mem_support_runBlake2s_adaptive`: a run under BLAKE2s is such a run, its joint log is
  consistent, and its verdict is `verify`'s.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash OracleComp OracleSpec Verify

@[expose] public section

/-! ## The game -/

/-- A cheating prover that chooses the statement: a computation on the hash oracle, with no
coins, that outputs a program, a public input and a proof. -/
abbrev AdaptiveAdversary : Type :=
  OracleComp hashSpec (Program × PublicInput × Proof PrunedMerklePaths)

/-- A run of the adaptive game: the run on the statement the prover chose, and that statement. -/
structure AdaptiveRun extends Run where
  /-- The program the prover chose. -/
  prog : Program
  /-- The public input the prover chose. -/
  input : PublicInput

/-- **The adaptive game**: the prover runs with its queries logged and outputs a statement and a
proof, then the verifier `V` runs on that statement and proof with its own queries logged. -/
def adaptiveGame (V : VerifierWith) (A : AdaptiveAdversary) : OracleComp hashSpec AdaptiveRun := do
  let p ← A.withQueryLog
  let q ← (V hashQuery p.1.1 p.1.2.1 p.1.2.2).withQueryLog
  return ⟨⟨p.1.2.2, p.2, q.2, q.1⟩, p.1.1, p.1.2.1⟩

/-! ## Its runs -/

/-- Logging a mapped computation logs it and maps its result. -/
private theorem withQueryLog_map {α β : Type} (f : α → β) (oa : OracleComp hashSpec α) :
    (f <$> oa).withQueryLog = (fun p ↦ (f p.1, p.2)) <$> oa.withQueryLog := by
  rw [map_eq_bind_pure_comp, withQueryLog_bind, map_eq_bind_pure_comp]
  simp only [Function.comp_apply, withQueryLog_pure, map_pure, Prod.map_apply, id_eq,
    List.append_nil]
  rfl

/-- **A prover with a fixed statement**: the adaptive game is the game on that statement. -/
theorem adaptiveGame_const (V : VerifierWith) (prog : Program) (input : PublicInput)
    (A : Adversary) :
    adaptiveGame V ((fun proof ↦ (prog, input, proof)) <$> A) =
      (fun g ↦ ⟨g, prog, input⟩) <$> loggedGame V prog input A := by
  simp [adaptiveGame, loggedGame, withQueryLog_map]

/-- **A run of the adaptive game** is a run of the game on the statement the prover chose, for
the prover that outputs only the proof. -/
theorem mem_support_loggedGame_of_adaptive {V : VerifierWith} {A : AdaptiveAdversary}
    {g : AdaptiveRun} (hg : g ∈ support (adaptiveGame V A)) :
    g.toRun ∈ support (loggedGame V g.prog g.input ((·.2.2) <$> A)) := by
  simp only [adaptiveGame, mem_support_bind_iff, mem_support_pure_iff] at hg
  obtain ⟨p, hp, q, hq, rfl⟩ := hg
  simp only [loggedGame, withQueryLog_map, mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨(p.1.2.2, p.2), by rw [support_map]; exact ⟨p, hp, rfl⟩, q, hq, rfl⟩

/-- **A run of the adaptive game under BLAKE2s** is a run, under BLAKE2s, of the game on the
statement the prover chose, for the prover that outputs only the proof. -/
private theorem mem_support_runBlake2s_of_adaptive {V : VerifierWith} {A : AdaptiveAdversary}
    {g : AdaptiveRun} (hg : g ∈ support (runBlake2s (adaptiveGame V A))) :
    g.toRun ∈ support (runBlake2s (loggedGame V g.prog g.input ((·.2.2) <$> A))) := by
  simp only [runBlake2s, adaptiveGame, simulateQ_bind, simulateQ_pure, mem_support_bind_iff,
    mem_support_pure_iff] at hg
  obtain ⟨p, hp, q, hq, rfl⟩ := hg
  simp only [runBlake2s, loggedGame, withQueryLog_map, simulateQ_bind, simulateQ_map,
    simulateQ_pure, mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨(p.1.2.2, p.2), by rw [support_map]; exact ⟨p, hp, rfl⟩, q, hq, rfl⟩

/-- **A run of the adaptive game under BLAKE2s** is a possible run of the game on the statement
the prover chose, its joint log is consistent, and its verdict is `verify`'s. -/
theorem mem_support_runBlake2s_adaptive {A : AdaptiveAdversary} {g : AdaptiveRun}
    (hg : g ∈ support (runBlake2s (adaptiveGame verifyWith A))) :
    g.toRun ∈ support (loggedGame verifyWith g.prog g.input ((·.2.2) <$> A)) ∧
      QueryLog.Consistent g.log ∧ g.ok = verify g.prog g.input g.proof :=
  mem_support_runBlake2s (mem_support_runBlake2s_of_adaptive hg)

end

end LeanerVM.Protocol
