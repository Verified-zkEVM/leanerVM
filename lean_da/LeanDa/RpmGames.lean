import LeanDa.RpmScheme
import Common.Rerun

/-!
# The games of the statement in the two-oracle form

`Statement/LeanDa.lean` states LeanDA's games with one oracle specification (`Common.KSpec`):
the adversary and the verifier both query Keccak-256 and `π`, the verifier's sponge calling `π`
(`hK`, `pK`). The proofs take them in the two-oracle form of `Common.rpmGame2`, the verifier's
calls of the permutation direct calls `F` (`hR`, `pR`, `LeanDa.Defs`), the form of the
two-oracle transfer (`Common.keccak256_transfer2`). `Common.toOne` turns a direct call into a `π`
query, and each game is the two-oracle game through it (`posBindingGame_eq`, `codeBindingGame_eq`,
`ksGame_eq`): the same run (`runK_posBindingGame`, …) and the same cost (`isWeightBound_toOne_iff`,
each query renamed to one of the same cost).

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

/-- The verifier's oracles as the statement's: `F` a `π` query. -/
abbrev toK : QueryImpl Rom2 (OracleComp KSpec) :=
  toOne (E := KRest) (C := KCap) ∘ₛ hfEmbed (Msg := List UInt8)

theorem toK_hR (a : List UInt8) : simulateQ toK (hR a) = hK a := by
  simp [toK, hR, hQuery, hq]
  rfl

theorem toK_pR (L : Lanes) : simulateQ toK (pR L) = pK L := by
  simp [toK, pR, pK, lanePerm, fQuery, hq]
  rfl

/-- The verifier's programs through `toK` are the statement's. -/
theorem toK_verifyRpm (r : ℕ) {Crs Proof : Type}
    {rel : Unit × Digest × Challenges → (Fin (r * 128) → Cell) → Bool}
    (ps : Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof rel) (crs : Crs)
    (com : Digest × Proof) (p : Fin (r * 128)) (x : Cell) (τ : Opening) :
    simulateQ toK (verifyRpm hR pR r ps crs com p x τ) = verifyRpm hK pK r ps crs com p x τ := by
  rw [verifyRpm_map (fun x ↦ simulateQ toK x) (fun _ ↦ simulateQ_pure _ _)
    (fun _ _ ↦ simulateQ_bind _ _ _)]
  simp only [toK_hR, toK_pR]

theorem toK_commitCellsM {r : ℕ} (c : Fin (r * 128) → Cell) :
    simulateQ toK (commitCellsM hR c) = commitCellsM hK c := by
  rw [commitCellsM_map (fun x ↦ simulateQ toK x) (fun _ ↦ simulateQ_pure _ _)
    (fun _ _ ↦ simulateQ_bind _ _ _)]
  simp only [toK_hR]

theorem toOne_advEmbed {α : Type} (X : OracleComp KSpec α) :
    simulateQ (toOne (E := KRest) (C := KCap) ∘ₛ advEmbed (Msg := List UInt8)) X = X := by
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [simulateQ_query_bind]
    simp only [ih]
    rcases t with n | a | q <;> rfl

/-- **A two-oracle game through `toOne`**: the honest part, the adversary as it is, and the
verifier's part through `toK`. -/
theorem toOne_rpmGame2 {β γ δ : Type} (p : ProbComp β) (A : β → OracleComp KSpec γ)
    (post : β → γ → OracleComp Rom2 δ) :
    simulateQ (toOne (E := KRest) (C := KCap)) (rpmGame2 (liftM p) A post) =
      (liftM p : OracleComp KSpec β) >>= fun x ↦ A x >>= fun a ↦ simulateQ toK (post x a) := by
  simp only [rpmGame2, simulateQ_bind, ← QueryImpl.simulateQ_compose, toOne_advEmbed]
  rw [simulateQ_liftM_of_coins _ (fun n ↦ rfl)]

/-! ## The games -/

/-- **The cost of a game through `toOne`** is its cost in the two-oracle form: each query is
renamed to one of the same cost. -/
theorem isWeightBound_toOne_iff {α : Type} (D : OracleComp (dSpec2 (List UInt8) KDigest KState) α)
    (q : ℕ) :
    IsWeightBound (simulateQ (toOne (E := KRest) (C := KCap)) D) permCalls q ↔
      IsWeightBound D permCalls2 q := by
  induction D using OracleComp.inductionOn generalizing q with
  | pure a => exact Iff.rfl
  | query_bind t k ih =>
    rw [simulateQ_query_bind, isWeightBound_query_bind_iff]
    rcases t with n | a | x | x
    · change IsWeightBound (liftM (KSpec.query (.inl n)) >>= fun u ↦ simulateQ toOne (k u))
        permCalls q ↔ _
      simp only [isWeightBound_query_bind_iff, permCalls, permCalls2, ih]
      exact Iff.rfl
    · change IsWeightBound (liftM (KSpec.query (.inr (.inl a))) >>= fun u ↦ simulateQ toOne (k u))
        permCalls q ↔ _
      simp only [isWeightBound_query_bind_iff, permCalls, permCalls2, ih]
      exact Iff.rfl
    · change IsWeightBound (liftM (KSpec.query (.inr (.inr x))) >>= fun u ↦ simulateQ toOne (k u))
        permCalls q ↔ _
      simp only [isWeightBound_query_bind_iff, permCalls, permCalls2, ih]
      exact Iff.rfl
    · change IsWeightBound
        (liftM (KSpec.query (.inr (.inr (.fwd x)))) >>= fun u ↦ simulateQ toOne (k u)) permCalls q ↔ _
      simp only [isWeightBound_query_bind_iff, permCalls, permCalls2, ih]
      exact Iff.rfl

section Games

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Digest × Challenges → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof rel)
  (ext : Nark.Extractor (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof)

theorem posBindingGame_eq (A : PosBindingAdvRpm r Crs Proof) :
    posBindingGame r ps A = simulateQ (toOne (E := KRest) (C := KCap)) (posBindingGame2 r ps A) := by
  rw [posBindingGame2, toOne_rpmGame2]
  refine bind_congr fun crs ↦ bind_congr fun out ↦ ?_
  obtain ⟨com, p, x, τ, x', τ'⟩ := out
  simp only [posBindingPost, simulateQ_bind, simulateQ_pure, toK_verifyRpm]

theorem codeBindingGame_eq (A : CodeBindingAdvRpm r Crs Proof) :
    codeBindingGame r ps A =
      simulateQ (toOne (E := KRest) (C := KCap)) (codeBindingGame2 r ps A) := by
  rw [codeBindingGame2, toOne_rpmGame2]
  refine bind_congr fun crs ↦ bind_congr fun out ↦ ?_
  obtain ⟨com, opened⟩ := out
  simp only [codeBindingPost, simulateQ_bind, simulateQ_pure,
    mapM_map (fun x ↦ simulateQ toK x) (fun _ ↦ simulateQ_pure _ _) (fun _ _ ↦ simulateQ_bind _ _ _),
    toK_verifyRpm]

theorem ksGame_eq (B : KsAdvRpm Crs Proof) :
    ksGame r ps ext B = simulateQ (toOne (E := KRest) (C := KCap)) (ksGame2 r ps ext B) := by
  rw [ksGame2, toOne_rpmGame2]
  refine bind_congr fun crs ↦ bind_congr fun out ↦ ?_
  obtain ⟨stmt, proof⟩ := out
  simp only [ksPost, simulateQ_bind, simulateQ_pure, toK_commitCellsM]

theorem runK_posBindingGame (A : PosBindingAdvRpm r Crs Proof) :
    runK (posBindingGame r ps A) = posBindingExpRpm r ps A := by
  rw [posBindingGame_eq]; rfl

theorem runK_codeBindingGame (A : CodeBindingAdvRpm r Crs Proof) :
    runK (codeBindingGame r ps A) = codeBindingExpRpm r ps A := by
  rw [codeBindingGame_eq]; rfl

theorem runK_ksGame (B : KsAdvRpm Crs Proof) : runK (ksGame r ps ext B) = ksExpRpm r ps ext B := by
  rw [ksGame_eq]; rfl

theorem isWeightBound_posBindingGame (A : PosBindingAdvRpm r Crs Proof) (Q : ℕ) :
    IsWeightBound (posBindingGame r ps A) permCalls Q ↔
      IsWeightBound (posBindingGame2 r ps A) permCalls2 Q := by
  rw [posBindingGame_eq, isWeightBound_toOne_iff]

theorem isWeightBound_codeBindingGame (A : CodeBindingAdvRpm r Crs Proof) (Q : ℕ) :
    IsWeightBound (codeBindingGame r ps A) permCalls Q ↔
      IsWeightBound (codeBindingGame2 r ps A) permCalls2 Q := by
  rw [codeBindingGame_eq, isWeightBound_toOne_iff]

theorem isWeightBound_ksGame_iff (B : KsAdvRpm Crs Proof) (Q : ℕ) :
    IsWeightBound (ksGame r ps ext B) permCalls Q ↔ IsWeightBound (ksGame2 r ps ext B) permCalls2 Q := by
  rw [ksGame_eq, isWeightBound_toOne_iff]

end Games

end LeanDa
