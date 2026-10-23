/-
  LeanVM.Guest.B1.Opening.QueriesPlacedD2

  `opening_queries` is `CompleteAtD`, one statement for every shape.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlacedD0

/-!
# `opening_queries`, `CompleteAtD`, one statement

`OqCompleteD fs cert name loop s odd`: when the frames fit (`OqFits`), on the honest data of a
call (`N` iterations, the queries' positions, rows and siblings, the weights, the bit runs, the
caller's buffers in `Lin`, `OqLinReg`, `OqLinMem`), the specialization `name` (loop helper `loop`)
is `CompleteAtD`, returning the chain's end times `λ_n`. `oqCompleteD1`, `oqCompleteD0`: from a
specialization's facts (its bodies the templates).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- The frames fit a specialization's frame runs. -/
def OqFits (fs : String → ℕ) (cert : String → V → ℕ) (name loop : String) (s : Oq) (odd : ℕ) :
    Prop :=
  if s.base = 1 then OqFits1 fs cert name loop s odd else OqFits0 fs cert loop s

/-- **`opening_queries`, the specialization `name` of the shape `s`, `odd`, is `CompleteAtD`.** -/
def OqCompleteD (fs : String → ℕ) (cert : String → V → ℕ) (name loop : String) (s : Oq)
    (odd : ℕ) : Prop :=
  OqFits fs cert name loop s odd →
    ∀ (κ : ℕ) (Lin : Main.Layout) (N : ℕ) (ecap eflags eqp ewp : ℕ) (lam lamN : E) (w : ℕ → E)
      (eb qs : ℕ → ℕ) (rows : ℕ → List K) (sibs : ℕ → List Digest), N + 1 < ordG → lam ≠ 0 →
      (∀ k < oqCount odd s.base N, qs k < 2 ^ (s.pd + s.cd) ∧ (rows k).length = s.R ∧
        (sibs k).length = s.pd) →
      OqLinReg (RegionL Lin) s ecap eflags eqp ewp eb qs (oqCount odd s.base N) →
      (∀ rd, LowDef κ rd → MemL rd Lin →
        OqLinMem rd s (ofK (Parameters.gpow ecap)) (ofK (Parameters.gpow eflags))
          (ofK (Parameters.gpow ewp)) (ofK (Parameters.gpow eqp)) w eb qs rows sibs
          (oqCount odd s.base N)) →
      CompleteAtD fs cert κ name Lin
        [ofK (Parameters.gpow ecap), ofK (Parameters.gpow eflags), lam, lamN,
          ofK (Parameters.gpow eqp), ofK (Parameters.gpow ewp), gen ^ N]
        (Returns [oqChain odd s.base lam⁻¹ (fun k ↦ rowDot s.base s.I (rows k) w) N * lamN])

theorem find_name {f : String} {fn : Fn} (h : coreProgram.find? f = some fn) : fn.name = f := by
  unfold Program.find? at h
  have := List.find?_some h
  simpa using this

theorem loop1_true {s : Oq} {odd : ℕ} {loop : String} {fl : Fn}
    (hfl : coreProgram.find? loop = some fl) (hbl : fl.body = oqLoop1T s odd loop) :
    coreProgram.loop loop = true := by
  rw [Program.loop_of_find? hfl, Fn.loop, hbl, find_name hfl]
  simp [oqLoop1T]

theorem loop0_true {s : Oq} {loop : String} {fl : Fn}
    (hfl : coreProgram.find? loop = some fl) (hbl : fl.body = oqLoop0T s loop) :
    coreProgram.loop loop = true := by
  rw [Program.loop_of_find? hfl, Fn.loop, hbl, find_name hfl]
  simp [oqLoop0T]

/-- **A level-0 specialization is `CompleteAtD`.** -/
theorem oqCompleteD1 (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hb1 : s.base = 1) (hpd : 4 * s.pd ≤ 80) (hpd1 : 1 ≤ s.pd)
    (hcd : 2 ≤ s.cd) (hcd8 : s.cd ≤ 8) {odd : ℕ} (hodd : odd ≤ 1) {name loop : String} {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hbm : fm.body = oqMainT s odd loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T s odd loop) : OqCompleteD fs cert name loop s odd := by
  intro hfit κ Lin N ecap eflags eqp ewp lam lamN w eb qs rows sibs hN hlam hst hreg hmem
  have hQ : oqCount odd s.base N = odd + 2 * N := by simp [oqCount, hb1]
  simp only [OqFits, hb1, ↓reduceIte] at hfit
  rw [hQ] at hst hreg hmem
  exact oqMain1_completeAtD fs cert κ hs hb1 hpd hpd1 hcd hcd8 hodd hfm hpm hbm hfl hpl hbl
    (loop1_true hfl hbl) hfit hN hlam hst hreg hmem

/-- **A deeper specialization is `CompleteAtD`.** -/
theorem oqCompleteD0 (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hb0 : s.base = 0) (hpd : 4 * s.pd ≤ 80) (hpd1 : 1 ≤ s.pd)
    (hcd : 2 ≤ s.cd) (hcd8 : s.cd ≤ 8) {name loop : String} {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hbm : fm.body = oqMainT s 0 loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop0T s loop) : OqCompleteD fs cert name loop s 0 := by
  intro hfit κ Lin N ecap eflags eqp ewp lam lamN w eb qs rows sibs hN hlam hst hreg hmem
  have hQ : oqCount 0 s.base N = N := by simp [oqCount, hb0]
  simp only [OqFits, hb0, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte] at hfit
  rw [hQ] at hst hreg hmem
  exact oqMain0_completeAtD fs cert κ hs hb0 hpd hpd1 hcd hcd8 hfm hpm hbm hfl hpl hbl
    (loop0_true hfl hbl) hfit hN hlam hst hreg hmem

end
end LeanVM.Guest.B1
