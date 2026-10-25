import LeanDa.RpmCodeBinding
import PqDas.Target.Scheme
import Statement.LeanDa

/-!
# Completeness in the random-permutation model

LeanDA is perfectly complete for every permutation `π` of the Keccak state (indeed every function):
with the hash Keccak-256 over `π` (`keccakWith π`) and the membership challenges the deployed
duplex over `π`, every position of every message's honest commitment opens and verifies
(`leanDa_perfectlyComplete_rpm : PerfectlyCompleteRpm`).

The proof is a transfer of Benedikt Wagner's completeness proof (`PqDas.scheme_perfectlyComplete`).
For a fixed `π` the experiment flips no coin but the argument's setup: the verifier's oracle
programs, run against `π` (`permImpl π`), are their pure counterparts (`membershipChallengesM_map`,
`verifyCellM_map`, `verifyCellM_id`), so the committer and the verifier compute the same
challenges, and the verdict is the honest run's for those challenges. Wagner's proof shows that the
honest run verifies for every challenge (`PqDas.honest_verify`, the core of his proof), from the
completeness of the Merkle commitment (`merkleVC_perfectlyComplete`), of the membership test
(`checker_complete`) and of the argument.

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common PqDas
open scoped ENNReal

namespace LeanDa

/-! ## The challenges' sponge through a monad morphism -/

section Map

variable {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
  (φ : ∀ {α}, m α → n α) (hpure : ∀ {α} (a : α), φ (pure a) = pure a)
  (hbind : ∀ {α β} (x : m α) (f : α → m β), φ (x >>= f) = φ x >>= fun a ↦ φ (f a))
  (H : List UInt8 → m Digest) (P : Lanes → m Lanes)

include hpure hbind

theorem samplesM_map (k : ℕ) (s : Sponge) :
    φ (Sponge.samplesM P k s) = Sponge.samplesM (fun L ↦ φ (P L)) k s := by
  induction k generalizing s with
  | zero => exact hpure _
  | succ k ih => simp only [Sponge.samplesM, Sponge.sampleM, Sponge.duplexM, hbind, hpure, ih]

theorem absorbM_map (s : Sponge) (x : E) (tag : K) :
    φ (Sponge.absorbM P s x tag) = Sponge.absorbM (fun L ↦ φ (P L)) s x tag := by
  unfold Sponge.absorbM
  rw [hbind]
  split_ifs <;> simp only [Sponge.duplexM, hbind, hpure]

/-- **The challenges through a monad morphism**: the morphism of the challenges over `H` and `P`
is the challenges over their images. -/
theorem membershipChallengesM_map (root : Digest) :
    φ (membershipChallengesM H P root) =
      membershipChallengesM (fun a ↦ φ (H a)) (fun L ↦ φ (P L)) root := by
  simp only [membershipChallengesM, Sponge.fromLabelM, Sponge.newM, Sponge.observeM, hbind,
    hpure, absorbM_map φ hpure hbind, samplesM_map φ hpure hbind]

end Map

/-! ## The verifier's oracle programs against a fixed permutation -/

section Fixed

variable (π : KState → KState)

/-- The lanes' permutation of `π`. -/
def laneP (L : Lanes) : Lanes := stateToLanes (π (lanesToState L))

theorem simulateQ_permImpl_hR (a : List UInt8) :
    simulateQ (permImpl π) (hR a) = pure (keccakWith π a) := by
  rw [hR, hQuery, hq, simulateQ_liftM_query]
  rfl

theorem simulateQ_permImpl_pR (L : Lanes) :
    simulateQ (permImpl π) (pR L) = pure (laneP π L) := by
  rw [pR, lanePerm, fQuery, hq, simulateQ_map, simulateQ_liftM_query]
  rfl

theorem permImpl_pure {α : Type} (a : α) : simulateQ (permImpl π) (pure a) = pure a :=
  simulateQ_pure _ a

theorem permImpl_bind {α β : Type} (x : OracleComp Rom2 α) (f : α → OracleComp Rom2 β) :
    simulateQ (permImpl π) (x >>= f) =
      simulateQ (permImpl π) x >>= fun a ↦ simulateQ (permImpl π) (f a) :=
  simulateQ_bind _ x f

/-- **Against `π`, the challenges are the crate's over Keccak-256 and the lanes of `π`.** -/
theorem simulateQ_permImpl_membershipChallengesM (root : Digest) :
    simulateQ (permImpl π) (membershipChallengesM hR pR root) =
      pure (membershipChallenges (keccakWith π) (laneP π) root) := by
  rw [membershipChallengesM_map (fun x ↦ simulateQ (permImpl π) x) (permImpl_pure π)
    (permImpl_bind π)]
  simp only [simulateQ_permImpl_hR, simulateQ_permImpl_pR]
  rw [← membershipChallengesM_id]
  exact (membershipChallengesM_map (m := Id) (n := ProbComp) (fun x ↦ pure (Id.run x))
    (fun _ ↦ rfl) (fun _ _ ↦ rfl) _ _ root).symm

/-- **Against `π`, the opening's verification is `verifyCell` with Keccak-256 over `π`.** -/
theorem simulateQ_permImpl_verifyCellM (r : ℕ) (com : Digest) (p : Fin (r * 128)) (x : Cell)
    (τ : Opening) :
    simulateQ (permImpl π) (verifyCellM hR r com p x τ) =
      pure (verifyCell (keccakWith π) r com p x τ) := by
  rw [verifyCellM_map (fun x ↦ simulateQ (permImpl π) x) (permImpl_pure π) (permImpl_bind π)]
  simp only [simulateQ_permImpl_hR]
  rw [← verifyCellM_id]
  exact (verifyCellM_map (m := Id) (n := ProbComp) (fun x ↦ pure (Id.run x))
    (fun _ ↦ rfl) (fun _ _ ↦ rfl) _ r com p x τ).symm

end Fixed

/-! ## Completeness -/

/-- **LeanDA is perfectly complete in the random-permutation model, for every permutation**
(Benedikt Wagner's completeness, transferred). For a fixed `π` the experiment is the argument's
setup followed by the honest run for the challenges the deployed duplex over `π` draws, which
verifies for every challenge (`PqDas.honest_verify`). -/
theorem leanDa_perfectlyComplete_rpm : PerfectlyCompleteRpm := by
  intro r π Crs Proof ps hps msg p
  rw [OracleComp.prEvent_eq_one_iff]
  intro b hb
  simp only [completenessExpRpm, permImpl_bind, simulateQ_permImpl_membershipChallengesM,
    pure_bind, verifyRpm, simulateQ_permImpl_verifyCellM, permImpl_pure, support_bind,
    Set.mem_iUnion, support_pure, Set.mem_singleton_iff, exists_prop] at hb
  obtain ⟨crs, hcrs, rfl⟩ := hb
  exact honest_verify (code r) (merkleVC r (keccakWith π)) (checker r) ps
    (merkleVC_perfectlyComplete r _) (checker_complete r) hps (ckVC := ()) (by simp [merkleVC])
    hcrs msg p _

end LeanDa
