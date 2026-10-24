/-
  LeanerVM.Protocol.ToArkLib.Flock.Run

  The Flock argument's verifier run on a transcript: the zerocheck's two runs of rounds, the
  lincheck's rounds, the lincheck's check of the slices, and the switched weighted claim. Candidate
  for ArkLib, with `LeanerVM.Protocol.ToArkLib.Flock.Reduction`.
-/

module

public import LeanerVM.Protocol.ToArkLib.FrontRun
public import LeanerVM.Protocol.ToArkLib.Flock.Reduction

/-!
# Runs of the Flock argument

A transcript of the Flock argument (`Flock.flock`, at the schedule `flockSchedule`) is its parts
in order (`Flock.trOf`, `Flock.exists_eq_trOf`): the point's drawn coordinates, the skip message,
`z_skip`, the zerocheck's within-block and batch rounds, `â, b̂`, `α`, the lincheck's rounds, the
slices and the ring-switching coefficients. Its verifier, run on such a transcript
(`Component.Front.run`), starts the zerocheck at `P(z_skip)` (`Flock.skipNext`), runs its two runs
of rounds, derives `ĉ` and the lincheck's claim (`Flock.termNext`, `Flock.alphaNext`), runs the
lincheck's rounds, checks the slices (`Flock.linCheck`) and hands on the switched weighted claim
(`Flock.ringWeight`, `Flock.ringTarget`): `Flock.run_flockFront`.
-/

namespace LeanerVM.Protocol

open CompPoly CMlPolynomialEval OracleComp OracleSpec ProtocolSpec SumcheckRound

@[expose] public section

namespace Flock

section Transcript

variable {F : Type} [Field F] (P : Params F) (s' : ℕ)

/-- A transcript of the Flock argument from its parts. -/
def trOf (v : Vector F P.nRand) (msg : Vector F (2 ^ P.s)) (zskip : F)
    (zcL : (roundsSpec F 2 P.m).FullTranscript) (zcH : (roundsSpec F 2 P.κ).FullTranscript)
    (ab : Vector F 2) (α : F) (lin : (roundsSpec F 2 P.m).FullTranscript)
    (sv : Vector F (2 ^ P.s)) (fs : Vector F (s' + 1)) :
    (flockSchedule F P.s P.m P.κ P.nRand s').FullTranscript :=
  chalsTr P.nRand (fun i ↦ v[i]) ++ₜ msgTr msg ++ₜ chalTr zskip ++ₜ zcL ++ₜ zcH ++ₜ msgTr ab ++ₜ
    chalTr α ++ₜ lin ++ₜ msgTr sv ++ₜ chalsTr (s' + 1) (fun i ↦ fs[i])

/-- A transcript of the Flock argument is the transcript of its parts. -/
theorem exists_eq_trOf (t : (flockSchedule F P.s P.m P.κ P.nRand s').FullTranscript) :
    ∃ v msg zskip zcL zcH ab α lin sv fs, t = trOf P s' v msg zskip zcL zcH ab α lin sv fs := by
  obtain ⟨t₉, t₁₀, rfl⟩ := exists_eq_append t
  obtain ⟨t₈, t₉', rfl⟩ := exists_eq_append t₉
  obtain ⟨t₇, t₈', rfl⟩ := exists_eq_append t₈
  obtain ⟨t₆, t₇', rfl⟩ := exists_eq_append t₇
  obtain ⟨t₅, t₆', rfl⟩ := exists_eq_append t₆
  obtain ⟨t₄, t₅', rfl⟩ := exists_eq_append t₅
  obtain ⟨t₃, t₄', rfl⟩ := exists_eq_append t₄
  obtain ⟨t₂, t₃', rfl⟩ := exists_eq_append t₃
  obtain ⟨t₁, t₂', rfl⟩ := exists_eq_append t₂
  obtain ⟨f, rfl⟩ := exists_eq_chalsTr P.nRand t₁
  obtain ⟨f', rfl⟩ := exists_eq_chalsTr (s' + 1) t₁₀
  refine ⟨Vector.ofFn f, t₂' 0, t₃' 0, t₄', t₅', t₆' 0, t₇' 0, t₈', t₉' 0, Vector.ofFn f', ?_⟩
  simp only [trOf, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
  rw [← eq_msgTr t₂', ← eq_chalTr t₃', ← eq_msgTr t₆', ← eq_chalTr t₇', ← eq_msgTr t₉']

end Transcript

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F] (P : Params F)
  {ι : Type} {O : ι → Type} [∀ i, OracleInterface (O i)] {W : Type}
  (C : BlockR1CS F (P.s + P.m))
  (z : (∀ i, O i) → Fin (2 ^ P.s) → CMlPolynomialEval F (P.m + P.κ))
  {S : Type} (side : S → (∀ i, O i) → Prop) (s' : ℕ)
  {K : Type} [CommRing K] (φ : K →+* F) (g : K) {μ : ℕ}
  (lift : Vector F (P.m + P.κ) → Vector F μ) {StmtOut : Type}
  (finish : S → Weight F μ → F → StmtOut)

/-- **The Flock argument's run**: the zerocheck's within-block and batch rounds from `P(z_skip)`,
the lincheck's rounds from its batched claim, the lincheck's check of the slices, and the switched
weighted claim handed on. -/
theorem run_flockFront (s : S) (v : Vector F P.nRand) (msg : Vector F (2 ^ P.s)) (zskip : F)
    (zcL : (roundsSpec F 2 P.m).FullTranscript) (zcH : (roundsSpec F 2 P.κ).FullTranscript)
    (ab : Vector F 2) (α : F) (lin : (roundsSpec F 2 P.m).FullTranscript)
    (sv : Vector F (2 ^ P.s)) (fs : Vector F (s' + 1)) :
    (flockFront P C z side s' φ g lift finish (W := W)).run s
        (trOf P s' v msg zskip zcL zcH ab α lin sv fs) =
      ((((roundsFront (zcFamily P C z side (W := W)).poly (zcFamily P C z side (W := W)).weight
          P.m P.m 0 (Nat.zero_add _)).run (skipNext P ((s, v), msg) zskip) zcL).bind fun stL ↦
        (roundsFront (zcFamily P C z side (W := W)).poly (zcFamily P C z side (W := W)).weight
          (P.m + P.κ) P.κ P.m rfl).run stL zcH).bind fun stH ↦
        (roundsFront (linFamily P C z side (W := W)).poly (linFamily P C z side (W := W)).weight
          P.m P.m 0 (Nat.zero_add _)).run (alphaNext (termNext stH ab) α) lin).bind fun st ↦
        if linCheck P C st sv then
          some (finish (linNext P st sv).1 (ringWeight P s' lift (linNext P st sv).2.1 fs)
            (ringTarget P s' φ g (linNext P st sv).2.2 fs))
        else none := by
  rw [trOf]
  erw [Component.Front.run_append]
  simp only [FullTranscript.append_fst, FullTranscript.append_snd]
  erw [Component.Front.run_append]
  simp only [FullTranscript.append_fst, FullTranscript.append_snd]
  erw [Component.Front.run_append]
  simp only [FullTranscript.append_fst, FullTranscript.append_snd]
  erw [Component.Front.run_append]
  simp only [FullTranscript.append_fst, FullTranscript.append_snd]
  erw [Component.Front.run_append]
  simp only [FullTranscript.append_fst, FullTranscript.append_snd]
  erw [Component.Front.run_append]
  simp only [FullTranscript.append_fst, FullTranscript.append_snd]
  erw [Component.Front.run_append]
  simp only [FullTranscript.append_fst, FullTranscript.append_snd]
  erw [Component.Front.run_append]
  simp only [FullTranscript.append_fst, FullTranscript.append_snd]
  erw [Component.Front.run_append]
  simp only [FullTranscript.append_fst, FullTranscript.append_snd]
  erw [Component.run_drawPushesFront O F]
  rw [Option.bind_some, ofFn_getElem_fin]
  erw [Component.run_sendCheckedFront O]
  simp only [ite_true, Option.bind_some]
  erw [Component.run_sampleFront O F]
  simp only [ite_true, Option.bind_some]
  rcases (roundsFront (zcFamily P C z side (W := W)).poly (zcFamily P C z side (W := W)).weight
      P.m P.m 0 (Nat.zero_add _)).run (skipNext P ((s, v), msg) zskip) zcL with _ | stL
  · rfl
  simp only [Option.bind_some]
  rcases (roundsFront (zcFamily P C z side (W := W)).poly (zcFamily P C z side (W := W)).weight
      (P.m + P.κ) P.κ P.m rfl).run stL zcH with _ | stH
  · rfl
  simp only [Option.bind_some]
  erw [Component.run_sendCheckedFront O]
  simp only [ite_true, Option.bind_some]
  erw [Component.run_sampleFront O F]
  simp only [ite_true, Option.bind_some]
  rcases (roundsFront (linFamily P C z side (W := W)).poly (linFamily P C z side (W := W)).weight
      P.m P.m 0 (Nat.zero_add _)).run (alphaNext (termNext stH ab) α) lin with _ | st
  · rfl
  simp only [Option.bind_some]
  erw [Component.run_sendCheckedFront O]
  by_cases hc : linCheck P C st sv = true
  · simp only [hc, ite_true, Option.bind_some]
    erw [Component.Front.run_append]
    simp only [chalsTr, FullTranscript.append_fst, FullTranscript.append_snd]
    erw [Component.run_drawPushesFront O F]
    rw [Option.bind_some]
    erw [Component.run_sampleFront O F]
    simp only [ite_true]
    rw [push_ofFn_castSucc]
  · simp [hc]

end Flock

end
end LeanerVM.Protocol
