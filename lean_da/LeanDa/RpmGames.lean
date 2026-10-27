import LeanDa.RpmScheme
import Common.Rerun

/-!
# The games of the statement in the two-oracle form

`Statement/LeanDa.lean` states LeanDA's games with one oracle specification (`Common.KSpec`, on
lane states): the adversary and the verifier both query Keccak-256 and `π`, the verifier's sponge
calling `π` (`hK`, `pK`). Read on byte states (`Common.relabel`), each is the same game on byte
states (`posBindingGame_relabel`, …: `posBindingGameB`, `hKB`, `pKB`), with the same distribution
(`Common.runK_relabel`) and cost (`Common.isWeightBound_relabel`). The proofs take those in the
two-oracle form of `Common.rpmGame2`, the verifier's calls of the permutation direct calls `F`
(`hR`, `pR`, `LeanDa.Defs`), the form of the two-oracle transfer (`Common.keccak256_transfer2`).
`Common.toOne` turns a direct call into a `π` query, and each game on bytes is the two-oracle
game through it (`posBindingGameB_eq`, `codeBindingGameB_eq`, `ksGameB_eq`): the same run
(`runK_posBindingGame`, …) and the same cost (`isWeightBound_toOne_iff`, each query renamed to
one of the same cost).

The verifier's oracle programs are written for any monad, so they commute with a monad morphism
such as a simulation (`membershipChallengesM_map`, `verifyCellM_map`, `commitCellsM_map`,
`verifyRpm_map`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common PqDas

namespace LeanDa

/-! ## Oracle programs through a monad morphism -/

section Map

variable {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
  (φ : ∀ {α}, m α → n α) (hpure : ∀ {α} (a : α), φ (pure a) = pure a)
  (hbind : ∀ {α β} (x : m α) (f : α → m β), φ (x >>= f) = φ x >>= fun a ↦ φ (f a))
  (H : List UInt8 → m Digest) (P : Lanes → m Lanes)

include hpure hbind

theorem samplesM_map (k : ℕ) : ∀ s : Sponge,
    φ (Sponge.samplesM P k s) = Sponge.samplesM (fun L ↦ φ (P L)) k s := by
  induction k with
  | zero => intro s; exact hpure _
  | succ k ih =>
    intro s
    simp only [Sponge.samplesM, Sponge.sampleM, Sponge.duplexM, hbind, hpure, ih]

theorem duplexM_map (s : Sponge) : φ (Sponge.duplexM P s) = Sponge.duplexM (fun L ↦ φ (P L)) s := by
  simp only [Sponge.duplexM, hbind, hpure]

theorem absorbM_map (s : Sponge) (x : E) (tag : K) :
    φ (Sponge.absorbM P s x tag) = Sponge.absorbM (fun L ↦ φ (P L)) s x tag := by
  unfold Sponge.absorbM
  rw [hbind]
  split_ifs
  · simp only [duplexM_map φ hpure hbind, hpure]
  · simp only [hpure]

/-- **The challenges' sponge through a monad morphism.** -/
theorem membershipChallengesM_map (root : Digest) :
    φ (membershipChallengesM H P root) =
      membershipChallengesM (fun a ↦ φ (H a)) (fun L ↦ φ (P L)) root := by
  simp only [membershipChallengesM, Sponge.fromLabelM, Sponge.newM, Sponge.observeM, hbind,
    hpure, absorbM_map φ hpure hbind P, samplesM_map φ hpure hbind P, bind_assoc]

theorem walkM_map (idx : ℕ) (node : Digest) (path : List Digest) :
    φ (walkM H idx node path) = walkM (fun a ↦ φ (H a)) idx node path := by
  induction path generalizing idx node with
  | nil => exact hpure _
  | cons s rest ih =>
    simp only [walkM, hbind, ih]

theorem verifyCellM_map (r : ℕ) (com : Digest) (p : Fin (r * 128)) (x : Cell) (τ : Opening) :
    φ (verifyCellM H r com p x τ) = verifyCellM (fun a ↦ φ (H a)) r com p x τ := by
  simp only [verifyCellM, hbind, hpure, walkM_map φ hpure hbind]

theorem mapM_map {β γ : Type} (f : β → m γ) (l : List β) :
    φ (l.mapM f) = l.mapM fun b ↦ φ (f b) := by
  induction l with
  | nil => simp [hpure]
  | cons b l ih => simp only [List.mapM_cons, hbind, ih, hpure]

theorem merkleRootM_map (d : ℕ) : ∀ f : ℕ → m Digest,
    φ (merkleRootM H d f) = merkleRootM (fun a ↦ φ (H a)) d fun i ↦ φ (f i) := by
  induction d with
  | zero => intro f; rfl
  | succ d ih =>
    intro f
    simp only [merkleRootM, ih]
    congr 1
    funext i
    simp only [upM, hbind]

/-- **The commitment through a monad morphism.** -/
theorem commitCellsM_map {r : ℕ} (c : Fin (r * 128) → Cell) :
    φ (commitCellsM H c) = commitCellsM (fun a ↦ φ (H a)) c := by
  simp only [commitCellsM, rowRootM, colRootM, hbind, merkleRootM_map φ hpure hbind]
  congr 1
  congr 1; funext i; simp only [rowLeavesM, hbind, mapM_map φ hpure hbind]

/-- **The verification through a monad morphism.** -/
theorem verifyRpm_map (r : ℕ) {Crs Proof : Type}
    {rel : Unit × Digest × Challenges → (Fin (r * 128) → Cell) → Bool}
    (ps : Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof rel) (crs : Crs)
    (com : Digest × Proof) (p : Fin (r * 128)) (x : Cell) (τ : Opening) :
    φ (verifyRpm H P r ps crs com p x τ) =
      verifyRpm (fun a ↦ φ (H a)) (fun L ↦ φ (P L)) r ps crs com p x τ := by
  simp only [verifyRpm, hbind, hpure, membershipChallengesM_map φ hpure hbind,
    verifyCellM_map φ hpure hbind]

end Map

/-! ## Direct calls as `π` queries -/

/-- The verifier's oracles as those of the games on byte states: `F` a `π` query. -/
abbrev toK : QueryImpl Rom2 (OracleComp KSpecB) :=
  toOne (E := KRest) (C := KCap) ∘ₛ hfEmbed (Msg := List UInt8)

theorem toK_hR (a : List UInt8) : simulateQ toK (hR a) = hKB a := by
  simp [toK, hR, hQuery, hq]
  rfl

theorem toK_pR (L : Lanes) : simulateQ toK (pR L) = pKB L := by
  simp [toK, pR, pKB, lanePerm, fQuery, hq]
  rfl

/-- The verifier's programs through `toK` are those of the games on byte states. -/
theorem toK_verifyRpm (r : ℕ) {Crs Proof : Type}
    {rel : Unit × Digest × Challenges → (Fin (r * 128) → Cell) → Bool}
    (ps : Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof rel) (crs : Crs)
    (com : Digest × Proof) (p : Fin (r * 128)) (x : Cell) (τ : Opening) :
    simulateQ toK (verifyRpm hR pR r ps crs com p x τ) = verifyRpm hKB pKB r ps crs com p x τ := by
  rw [verifyRpm_map (fun x ↦ simulateQ toK x) (fun _ ↦ simulateQ_pure _ _)
    (fun _ _ ↦ simulateQ_bind _ _ _)]
  simp only [toK_hR, toK_pR]

theorem toK_commitCellsM {r : ℕ} (c : Fin (r * 128) → Cell) :
    simulateQ toK (commitCellsM hR c) = commitCellsM hKB c := by
  rw [commitCellsM_map (fun x ↦ simulateQ toK x) (fun _ ↦ simulateQ_pure _ _)
    (fun _ _ ↦ simulateQ_bind _ _ _)]
  simp only [toK_hR]

theorem toOne_advEmbed {α : Type} (X : OracleComp KSpecB α) :
    simulateQ (toOne (E := KRest) (C := KCap) ∘ₛ advEmbed (Msg := List UInt8)) X = X := by
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [simulateQ_query_bind]
    simp only [ih]
    rcases t with n | a | q <;> rfl

/-- **A two-oracle game through `toOne`**: the honest part, the adversary as it is, and the
verifier's part through `toK`. -/
theorem toOne_rpmGame2 {β γ δ : Type} (p : ProbComp β) (A : β → OracleComp KSpecB γ)
    (post : β → γ → OracleComp Rom2 δ) :
    simulateQ (toOne (E := KRest) (C := KCap)) (rpmGame2 (liftM p) A post) =
      (liftM p : OracleComp KSpecB β) >>= fun x ↦ A x >>= fun a ↦ simulateQ toK (post x a) := by
  simp only [rpmGame2, simulateQ_bind, ← QueryImpl.simulateQ_compose, toOne_advEmbed]
  rw [simulateQ_liftM_of_coins _ (fun n ↦ rfl)]

/-! ## The games -/

/-- **The cost of a game through `toOne`** is its cost in the two-oracle form: each query is
renamed to one of the same cost. -/
theorem isWeightBound_toOne_iff {α : Type} (D : OracleComp (dSpec2 (List UInt8) KDigest KState) α)
    (q : ℕ) :
    IsWeightBound (simulateQ (toOne (E := KRest) (C := KCap)) D) permCallsB q ↔
      IsWeightBound D permCalls2 q := by
  induction D using OracleComp.inductionOn generalizing q with
  | pure a => exact Iff.rfl
  | query_bind t k ih =>
    rw [simulateQ_query_bind, isWeightBound_query_bind_iff]
    rcases t with n | a | x | x
    · change IsWeightBound (liftM (KSpecB.query (.inl n)) >>= fun u ↦ simulateQ toOne (k u))
        permCallsB q ↔ _
      simp only [isWeightBound_query_bind_iff, permCallsB, permCalls2, ih]
      exact Iff.rfl
    · change IsWeightBound (liftM (KSpecB.query (.inr (.inl a))) >>= fun u ↦ simulateQ toOne (k u))
        permCallsB q ↔ _
      simp only [isWeightBound_query_bind_iff, permCallsB, permCalls2, ih]
      exact Iff.rfl
    · change IsWeightBound (liftM (KSpecB.query (.inr (.inr x))) >>= fun u ↦ simulateQ toOne (k u))
        permCallsB q ↔ _
      simp only [isWeightBound_query_bind_iff, permCallsB, permCalls2, ih]
      exact Iff.rfl
    · change IsWeightBound
        (liftM (KSpecB.query (.inr (.inr (.fwd x)))) >>= fun u ↦ simulateQ toOne (k u))
          permCallsB q ↔ _
      simp only [isWeightBound_query_bind_iff, permCallsB, permCalls2, ih]
      exact Iff.rfl

section Games

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Digest × Challenges → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof rel)
  (ext : Nark.Extractor (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof)

/-! ### The statement's oracles, read on byte states -/

theorem relabel_hK (a : List UInt8) : simulateQ relabel (hK a) = hKB a := by
  simp [hK, hKB, relabel]

theorem relabel_pK (x : Lanes) : simulateQ relabel (pK x) = pKB x := by
  simp [pK, pKB, relabel, lanePerm, lanesToState, LeanVM.Rpm.mapQ]
  rfl

theorem relabel_commitCellsM (c : Fin (r * 128) → Cell) :
    simulateQ relabel (commitCellsM hK c) = commitCellsM hKB c := by
  rw [commitCellsM_map (fun x ↦ simulateQ relabel x) (fun _ ↦ simulateQ_pure _ _)
    (fun _ _ ↦ simulateQ_bind _ _ _)]
  simp only [relabel_hK]

theorem relabel_verifyCellM (com : Digest) (p : Fin (r * 128)) (x : Cell) (τ : Opening) :
    simulateQ relabel (verifyCellM hK r com p x τ) = verifyCellM hKB r com p x τ := by
  rw [verifyCellM_map (fun x ↦ simulateQ relabel x) (fun _ ↦ simulateQ_pure _ _)
    (fun _ _ ↦ simulateQ_bind _ _ _)]
  simp only [relabel_hK]

theorem relabel_membershipChallengesM (root : Digest) :
    simulateQ relabel (membershipChallengesM hK pK root) = membershipChallengesM hKB pKB root := by
  rw [membershipChallengesM_map (fun x ↦ simulateQ relabel x) (fun _ ↦ simulateQ_pure _ _)
    (fun _ _ ↦ simulateQ_bind _ _ _)]
  simp only [relabel_hK, relabel_pK]

end Games

end LeanDa
