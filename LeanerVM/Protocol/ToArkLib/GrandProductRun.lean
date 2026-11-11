/-
  LeanerVM.Protocol.ToArkLib.GrandProductRun

  The grand-product argument's verifier run on a transcript: a layer's run is its rounds' run, the
  check of the descendants and the interpolation at the combination challenges. Candidate for
  ArkLib, with `LeanerVM.Protocol.ToArkLib.GrandProduct`.
-/

module

public import LeanerVM.Protocol.ToArkLib.FrontRun
public import LeanerVM.Protocol.ToArkLib.GrandProduct

/-!
# Runs of the grand-product argument

A layer of the grand-product argument (`Gkr.layerStep`) reads a combiner, its sumcheck rounds,
the descendants of each tree and the combination challenges. Its verifier, run on a transcript
(`Component.Front.run`), combines the trees' claims by the powers of the combiner, runs the
rounds from the combined claim, checks the descendants against the rounds' final claim
(`Gkr.combineCheck`) and moves to the point of the combination challenges and the rounds'
challenges, each tree's descendants interpolated there (`Gkr.interpDone`):
`Gkr.run_layerStepFront`. The combination challenges alone are `Gkr.run_interpolateFront`.
`Gkr.eq_stepTr` splits a layer's transcript into its four parts.
-/

namespace LeanerVM.Protocol

open CompPoly CMlPolynomialEval OracleComp OracleSpec ProtocolSpec

@[expose] public section

namespace Gkr

section Split

variable {F : Type} {nside ρ m : ℕ}

/-- A transcript of a layer is its combiner, its rounds, its descendants and its combination
challenges. -/
theorem eq_stepTr (t : (stepSpec F nside ρ m).FullTranscript) :
    t = ((chalTr (t.fst.fst.fst 0) ++ₜ t.fst.fst.snd) ++ₜ msgTr (t.fst.snd 0)) ++ₜ t.snd := by
  rw [← eq_chalTr, ← eq_msgTr, FullTranscript.append_fst_snd, FullTranscript.append_fst_snd,
    FullTranscript.append_fst_snd]

/-- The transcript of `k + 1` layers of radix four: the first layer's, then the rest. -/
def stepsCons {k : ℕ} (t : (stepSpec F nside 2 m).FullTranscript)
    (t' : (stepsSpec F nside k (m + 2)).FullTranscript) :
    (stepsSpec F nside (k + 1) m).FullTranscript :=
  t ++ₜ t'

/-- A transcript of `k + 1` layers of radix four is the first layer's, then the rest. -/
theorem exists_eq_stepsCons {k : ℕ} (t : (stepsSpec F nside (k + 1) m).FullTranscript) :
    ∃ t₁ t₂, t = stepsCons t₁ t₂ :=
  ⟨_, _, (FullTranscript.append_fst_snd (pSpec₁ := stepSpec F nside 2 m)
    (pSpec₂ := stepsSpec F nside k (m + 2)) t).symm⟩

end Split

variable {F : Type} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F] [SampleableType F]
  {X : Type} {ι : Type} {O : ι → Type} [∀ i, OracleInterface (O i)] (nside : ℕ)

omit [Field F] [BEq F] [LawfulBEq F] [DecidableEq F] in
/-- The first `i` combination challenges append themselves to the statement. -/
theorem run_interpPrefixFront (ρ m : ℕ) :
    ∀ (i : ℕ) (s : InterpStmt X F nside m ρ 0) (f : Fin i → F),
      (interpPrefixFront (F := F) (X := X) (O := O) nside ρ m i).run s (chalsTr i f) =
        some (s.1, Vector.ofFn f)
  | 0, s, f => by
    refine congrArg some (Prod.ext rfl (Vector.ext fun j h ↦ absurd h (Nat.not_lt_zero j)))
  | i + 1, s, f => by
    erw [Component.Front.run_append]
    simp only [chalsTr, FullTranscript.append_fst, FullTranscript.append_snd]
    erw [run_interpPrefixFront ρ m i s, Option.bind_some, Component.run_sampleFront]
    rw [Vector.ofFn_succ (f := f)]
    rfl

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
/-- **The combination challenges** move to the layer statement at their point: the run on the
challenges `u` is `Gkr.interpDone` of the statement with `u`. -/
theorem run_interpolateFront :
    ∀ (ρ m : ℕ) (s : InterpStmt X F nside m ρ 0) (u : Vector F ρ),
      (interpolateFront (F := F) (X := X) (O := O) nside ρ m).run s (chalsTr ρ fun i ↦ u[i]) =
        some (interpDone nside ρ m (s.1, u))
  | 0, m, s, u => by
    have hs : s = (s.1, u) :=
      Prod.ext rfl (Vector.ext fun j h ↦ absurd h (Nat.not_lt_zero j))
    rw [hs]
    rfl
  | ρ' + 1, m, s, u => by
    erw [Component.Front.run_append]
    simp only [chalsTr, FullTranscript.append_fst, FullTranscript.append_snd]
    erw [run_interpPrefixFront nside (ρ' + 1) m ρ' s, Option.bind_some, Component.run_sampleFront]
    simp only [ite_true]
    congr 2
    refine Prod.ext rfl (Vector.ext fun j hj ↦ ?_)
    simp only [interpNext, Vector.getElem_push, Vector.getElem_ofFn, Fin.getElem_fin,
      Fin.val_castSucc, Fin.val_last]
    split
    · rfl
    · congr 1
      omega

variable (μ : ℕ) (leaves : X → (∀ i, O i) → Fin nside → CMlPolynomialEval F μ)

/-- **A layer's run**: the claims combined by the powers of the combiner `lam`, the rounds run
from the combined claim, the descendants `ch` checked against the rounds' final claim, and the
layer statement at the point of the combination challenges `u` and the rounds' challenges. -/
theorem run_layerStepFront (ρ m : ℕ) {S : Type} (inp : S → LayerStmt X F nside m) (s : S)
    (lam : F) (R : (roundsSpec F (2 ^ ρ) m).FullTranscript) (ch : Fin nside → Vector F (2 ^ ρ))
    (u : Vector F ρ) :
    (layerStepFront nside μ leaves ρ m inp).run s
        (((chalTr lam ++ₜ R) ++ₜ msgTr ch) ++ₜ chalsTr ρ fun i ↦ u[i]) =
      ((SumcheckRound.roundsFront (roundPoly nside μ leaves ρ m) (weights nside m) m m 0
          (Nat.zero_add m)).run ((inp s, lam), (#v[], powerBatch (inp s).2.2 lam)) R).bind
        fun st ↦ if combineCheck nside ρ m st ch then
          some (interpDone nside ρ m ((st.1.1.1, (st.2.1, ch)), u)) else none := by
  erw [Component.Front.run_append]
  simp only [FullTranscript.append_fst, FullTranscript.append_snd]
  erw [Component.Front.run_append]
  simp only [FullTranscript.append_fst, FullTranscript.append_snd]
  erw [Component.Front.run_append]
  simp only [FullTranscript.append_fst, FullTranscript.append_snd]
  change (((some ((inp s, lam), (#v[], powerBatch (inp s).2.2 lam))).bind fun s₁ ↦
      (SumcheckRound.roundsFront (roundPoly nside μ leaves ρ m) (weights nside m) m m 0
        (Nat.zero_add m)).run s₁ R).bind fun st ↦
      (if combineCheck nside ρ m st ch then some (childNext nside ρ m st ch) else none)).bind
      (fun c ↦ (interpolateFront (F := F) (X := X) (O := O) nside ρ m).run c
        (chalsTr ρ fun i ↦ u[i])) = _
  rw [Option.bind_some]
  rcases (SumcheckRound.roundsFront (roundPoly nside μ leaves ρ m) (weights nside m) m m 0
      (Nat.zero_add m)).run ((inp s, lam), (#v[], powerBatch (inp s).2.2 lam)) R with _ | st
  · rfl
  · simp only [Option.bind_some]
    cases combineCheck nside ρ m st ch
    · rfl
    · simp only [ite_true, Option.bind_some]
      exact run_interpolateFront nside ρ m _ u

/-- The run of `k + 1` layers of radix four: the first layer's, then the rest from its verdict. -/
theorem run_layerStepsFront_succ (k m : ℕ) (h : m + 2 * (k + 1) = μ) (ℓ : LayerStmt X F nside m)
    (t : (stepSpec F nside 2 m).FullTranscript)
    (t' : (stepsSpec F nside k (m + 2)).FullTranscript) :
    (layerStepsFront nside μ leaves (k + 1) m h).run ℓ (stepsCons t t') =
      ((layerStepFront nside μ leaves 2 m id).run ℓ t).bind fun ℓ' ↦
        (layerStepsFront nside μ leaves k (m + 2) (by omega)).run ℓ' t' := by
  rw [stepsCons]
  erw [Component.Front.run_append]
  simp only [FullTranscript.append_fst, FullTranscript.append_snd]

/-- **The grand product's run**: the binary layer, if there is one, the layers of radix four from
its verdict, and the last combiner, which changes nothing. -/
theorem run_gkrFront (s : X × (Fin nside → F)) (t₁ : (oddSpec F nside (μ % 2)).FullTranscript)
    (t₂ : (stepsSpec F nside (μ / 2) (μ % 2)).FullTranscript) (c : F) :
    (gkrFront nside μ leaves).run s ((t₁ ++ₜ t₂) ++ₜ chalTr c) =
      ((oddFront nside μ leaves (μ % 2) (Nat.le_of_lt_succ (Nat.mod_lt μ two_pos))).run s
        t₁).bind fun ℓ ↦
        (layerStepsFront nside μ leaves (μ / 2) (μ % 2) (Nat.mod_add_div μ 2)).run ℓ t₂ := by
  erw [Component.Front.run_append]
  simp only [FullTranscript.append_fst, FullTranscript.append_snd]
  erw [Component.Front.run_append]
  simp only [FullTranscript.append_fst, FullTranscript.append_snd]
  rcases (oddFront nside μ leaves (μ % 2) (Nat.le_of_lt_succ (Nat.mod_lt μ two_pos))).run s t₁
    with _ | ℓ
  · rfl
  · simp only [Option.bind_some]
    rcases (layerStepsFront nside μ leaves (μ / 2) (μ % 2) (Nat.mod_add_div μ 2)).run ℓ t₂
      with _ | ℓ'
    · rfl
    · rfl

end Gkr

end
end LeanerVM.Protocol
