/-
  LeanVM.Guest.B1.Opening.QueriesComplete6

  `opening_queries` is its meaning: the completeness direction from its start and its loop's
  iterations, and both directions together.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesComplete5

/-!
# `opening_queries` is complete (G:1246-1269, TRIAGE #40)

`oqMainA_complete`: the function's start holds at `μ = λ⁻¹`, the chain's pointer and, at an odd
count, the first query's honest values. `oqMain1_complete`, `oqMain0_complete`: from
`MeaningOpeningQueries`, the loop runs its `N` iterations (`guarded_loop_iff`,
`oqIter1_complete`, `oqIter0_complete`) and the function returns the chain's end times `λ_n`.
`oqMain1_iff`, `oqMain0_iff`: with the soundness direction, the relation is the meaning.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-- **The function's start holds** at `μ = λ⁻¹`, the chain at `ch`, and the values `1, 1 + N, 1`
then `rest` from `oqMK`; at an odd count when its first query opens and the chain starts at its
value times `μ`, at an even one when the chain starts at `0`. -/
theorem oqMainA_complete {s : Oq} (hs : s.RowShape) (hpd : 4 * s.pd ≤ 80) (hcd : 2 ≤ s.cd)
    (hcd8 : s.cd ≤ 8) {odd : ℕ} (hodd : odd ≤ 1) {cap flags lam lamN qptrs wp nG ch : E}
    (hlam : lam ≠ 0) (rest : List E)
    (h1 : odd = 1 → ∃ (bp : E) (q : ℕ) (r : List K) (d : E), LoadHolds rd qptrs 0 bp ∧
      q < 2 ^ (s.pd + s.cd) ∧ (∀ l < s.pd + s.cd, LoadHolds rd bp l (bitE (q.testBit l))) ∧
      QueryOpens rd s.base s.I (s.pd + s.cd) s.cd cap flags wp q r d ∧
      LoadHolds rd ch 0 (d * lam⁻¹))
    (h0 : odd ≠ 1 → LoadHolds rd ch 0 0) :
    ∃ σ : Val, [V.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6].map σ =
        [cap, flags, lam, lamN, qptrs, wp, nG] ∧ σ (.n 8) = lam⁻¹ ∧ σ (.n 11) = ch ∧
      (∀ o, σ (.n (oqMK s odd + o)) = ([word 1 0 0, word 1 0 0 + nG, word 1 0 0] ++ rest).getD o 0) ∧
      ∀ a, Stmt.atom a ∈ oqMainA s odd → a.Holds rd σ := by
  set tl : List E := [word 1 0 0, word 1 0 0 + nG, word 1 0 0] ++ rest with htl
  have mu1 : word 1 0 0 = lam⁻¹ * lam := by rw [word_one, inv_mul_cancel₀ hlam]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hodd with rfl | rfl
  · -- an even count: the chain starts at `0`
    have hk : oqMK s 0 = 13 := rfl
    let f : ℕ → E := fun i =>
      if i < 7 then [cap, flags, lam, lamN, qptrs, wp, nG].getD i 0
      else if i = 7 then word 1 0 0 else if i = 8 then lam⁻¹ else if i = 9 then word 2 0 0
      else if i = 10 then nG * word 2 0 0 else if i = 11 then ch else if i = 12 then word 0 0 0
      else tl.getD (i - 13) 0
    let σ : Val := fun w => f w.idx
    have ev : ∀ i, σ (.n i) = f i := fun _ => rfl
    have eT : ∀ o, σ (.n (oqMK s 0 + o)) = tl.getD o 0 := fun o => by
      rw [hk, ev]
      simp only [f, show ¬ 13 + o < 7 by omega, show 13 + o ≠ 7 by omega, show 13 + o ≠ 8 by omega,
        show 13 + o ≠ 9 by omega, show 13 + o ≠ 10 by omega, show 13 + o ≠ 11 by omega,
        show 13 + o ≠ 12 by omega, ↓reduceIte, Nat.add_sub_cancel_left]
    have eP : ∀ i < 7, σ (.n i) = [cap, flags, lam, lamN, qptrs, wp, nG].getD i 0 := fun i hi => by
      rw [ev]; simp only [f, hi, ↓reduceIte]
    have e7 : σ (.n 7) = word 1 0 0 := by rw [ev]; simp only [f]; simp
    have e8 : σ (.n 8) = lam⁻¹ := by rw [ev]; simp only [f]; simp
    have e9 : σ (.n 9) = word 2 0 0 := by rw [ev]; simp only [f]; simp
    have e10 : σ (.n 10) = nG * word 2 0 0 := by rw [ev]; simp only [f]; simp
    have e11 : σ (.n 11) = ch := by rw [ev]; simp only [f]; simp
    have e12 : σ (.n 12) = word 0 0 0 := by rw [ev]; simp only [f]; simp
    have t0 : σ (.n (oqMK s 0)) = word 1 0 0 := by simpa [htl] using eT 0
    have t1 : σ (.n (oqMK s 0 + 1)) = word 1 0 0 + nG := by simpa [htl] using eT 1
    have t2 : σ (.n (oqMK s 0 + 2)) = word 1 0 0 := by simpa [htl] using eT 2
    refine ⟨σ, rfl, e8, e11, eT, fun a ha => ?_⟩
    simp only [oqMainA, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    rcases ha with ((rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)) | (rfl | rfl | rfl)
    · exact e7
    · show σ (.n 7) = σ (.n 8) * σ (.n 2)
      rw [e7, e8, eP 2 (by omega)]; exact mu1
    · exact e9
    · show σ (.n 10) = σ (.n 6) * σ (.n 9)
      rw [e10, e9, eP 6 (by omega)]; rfl
    · trivial
    · exact e12
    · show LoadHolds rd (σ (.n 11)) 0 (σ (.n 12))
      rw [e11, e12, word_zero]; exact h0 (by decide)
    · exact t0
    · show σ (.n (oqMK s 0 + 1)) = σ (.n (oqMK s 0)) + σ (.n 6)
      rw [t1, t0, eP 6 (by omega)]; rfl
    · exact t2
  · -- an odd count: the first query
    obtain ⟨bp, q, r, d, hb, hq, hbits, ho, hc0⟩ := h1 rfl
    obtain ⟨w, sb, pp, hd, hok⟩ := QD.exists_of_opens hq ho
    set D : QD := ⟨s, 13, true, 0, r, w, q, sb, pp, cap, flags, rd⟩ with hD
    have hk : oqMK s 1 = D.z + 12 := by show oqEnd D.s D.b D.emit + 1 = _; rw [QD.end_eq D]
    obtain ⟨a1, a2, a3, a4, a5⟩ := D.places
    have hk1 := QD.k1_eq D
    set k := oqMK s 1 with hk'
    let f : ℕ → E := fun i =>
      if i < 7 then [cap, flags, lam, lamN, qptrs, wp, nG].getD i 0
      else if i = 7 then word 1 0 0 else if i = 8 then lam⁻¹ else if i = 9 then word 2 0 0
      else if i = 10 then nG * word 2 0 0 else if i = 11 then ch else if i = 12 then bp
      else if i < k - 1 then D.val i else if i = k - 1 then d * lam⁻¹
      else tl.getD (i - k) 0
    let σ : Val := fun w => f w.idx
    have ev : ∀ i, σ (.n i) = f i := fun _ => rfl
    have eP : ∀ i < 7, σ (.n i) = [cap, flags, lam, lamN, qptrs, wp, nG].getD i 0 := fun i hi => by
      rw [ev]; simp only [f, hi, ↓reduceIte]
    have eQ : ∀ i, D.b ≤ i → i < D.z + 11 → σ (.n i) = D.val i := fun i h1 h2 => by
      have : D.b = 13 := rfl
      rw [ev]
      simp only [f, show ¬ i < 7 by omega, show i ≠ 7 by omega, show i ≠ 8 by omega,
        show i ≠ 9 by omega, show i ≠ 10 by omega, show i ≠ 11 by omega, show i ≠ 12 by omega,
        show i < k - 1 by omega, ↓reduceIte]
    have eD : σ (.n (k - 1)) = d * lam⁻¹ := by
      have : D.b = 13 := rfl
      rw [ev]
      simp only [f, show ¬ k - 1 < 7 by omega, show k - 1 ≠ 7 by omega, show k - 1 ≠ 8 by omega,
        show k - 1 ≠ 9 by omega, show k - 1 ≠ 10 by omega, show k - 1 ≠ 11 by omega,
        show k - 1 ≠ 12 by omega, lt_irrefl, ↓reduceIte]
    have eT : ∀ o, σ (.n (k + o)) = tl.getD o 0 := fun o => by
      have : D.b = 13 := rfl
      rw [ev]
      simp only [f, show ¬ k + o < 7 by omega, show k + o ≠ 7 by omega, show k + o ≠ 8 by omega,
        show k + o ≠ 9 by omega, show k + o ≠ 10 by omega, show k + o ≠ 11 by omega,
        show k + o ≠ 12 by omega, show ¬ k + o < k - 1 by omega, show k + o ≠ k - 1 by omega,
        ↓reduceIte, Nat.add_sub_cancel_left]
    have hp := D.pad_of_emit rfl eQ
    obtain ⟨hA, hdot⟩ := D.query_complete (σ := σ) (bp := .n 12) (cap := .n 0) (flags := .n 1)
      (wp := .n 5) hs hpd hcd hcd8 (by rw [eP 5 (by omega)]; exact hok _ _ _) eQ hp.1 hp.2
      (by rw [show σ (.n 12) = bp from rfl]; exact hbits) (eP 0 (by omega)) (eP 1 (by omega))
    rw [← hd] at hdot
    have e7 : σ (.n 7) = word 1 0 0 := by rw [ev]; simp only [f]; simp
    have e8 : σ (.n 8) = lam⁻¹ := by rw [ev]; simp only [f]; simp
    have e9 : σ (.n 9) = word 2 0 0 := by rw [ev]; simp only [f]; simp
    have e10 : σ (.n 10) = nG * word 2 0 0 := by rw [ev]; simp only [f]; simp
    have e11 : σ (.n 11) = ch := by rw [ev]; simp only [f]; simp
    have t0 : σ (.n k) = word 1 0 0 := by simpa [htl] using eT 0
    have t1 : σ (.n (k + 1)) = word 1 0 0 + nG := by simpa [htl] using eT 1
    have t2 : σ (.n (k + 2)) = word 1 0 0 := by simpa [htl] using eT 2
    refine ⟨σ, rfl, e8, e11, eT, fun a ha => ?_⟩
    simp only [oqMainA, ↓reduceIte, List.mem_append] at ha
    rcases ha with (ha | ((ha | ha) | ha)) | ha
    · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl
      · exact e7
      · show σ (.n 7) = σ (.n 8) * σ (.n 2)
        rw [e7, e8, eP 2 (by omega)]; exact mu1
      · exact e9
      · show σ (.n 10) = σ (.n 6) * σ (.n 9)
        rw [e10, e9, eP 6 (by omega)]; rfl
      · trivial
    · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
      subst ha
      exact hb
    · exact hA a ha
    · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
      rcases ha with rfl | rfl
      · show σ (.n (k - 1)) = σ (.n (oqDot s 13)) * σ (.n 8)
        rw [eD, hdot, e8]
      · show LoadHolds rd (σ (.n 11)) 0 (σ (.n (k - 1)))
        rw [eD, e11]; exact hc0
    · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
      rcases ha with rfl | rfl | rfl
      · exact t0
      · show σ (.n (k + 1)) = σ (.n k) + σ (.n 6)
        rw [t1, t0, eP 6 (by omega)]; rfl
      · exact t2

/-- The function's end: with its start, the loop's call and the chain's end at `ch·g^N`, the body
holds and returns the chain's end times `λ_n`. -/
theorem oqMainT_complete {s : Oq} {odd : ℕ} {loop name : String} {fm : Fn}
    (hfm : coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hbm : fm.body = oqMainT s odd loop) {cap flags lam lamN qptrs wp nG ch hN : E} {m : ℕ}
    (hnG : nG = gen ^ m) (hNl : LoadHolds rd ch m hN) {σ : Val}
    (hp : [V.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6].map σ =
      [cap, flags, lam, lamN, qptrs, wp, nG])
    (h8 : σ (.n 8) = lam⁻¹) (h11 : σ (.n 11) = ch)
    (hT : ∀ o, σ (.n (oqMK s odd + o)) =
      ([word 1 0 0, word 1 0 0 + nG, word 1 0 0] ++ [ch * nG, hN, hN * lamN]).getD o 0)
    (hA : ∀ a, Stmt.atom a ∈ oqMainA s odd → a.Holds rd σ)
    (hK : IsInK (1 + nG))
    (hcall : 1 + nG ≠ 0 → coreProgram.Rel rd loop [1, nG, qptrs, cap, flags, wp, ch, lam⁻¹] []) :
    coreProgram.Rel rd name [cap, flags, lam, lamN, qptrs, wp, nG] [hN * lamN] := by
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, -⟩ := hp
  rw [rel_iff_sem hfm]
  refine ⟨σ, by rw [hpm]; simp [p0, p1, p2, p3, p4, p5, p6], ?_⟩
  rw [hbm, oqMainT, holdsList_append, holdsList_atoms (oqMainA_atoms s odd)]
  refine ⟨hA, ?_⟩
  set k := oqMK s odd
  have t1 : σ (.n (k + 1)) = 1 + nG := by simpa [word_one] using hT 1
  have t2 : σ (.n (k + 2)) = 1 := by simpa [word_one] using hT 2
  have t3 : σ (.n (k + 3)) = ch * nG := by simpa using hT 3
  have t4 : σ (.n (k + 4)) = hN := by simpa using hT 4
  have t5 : σ (.n (k + 5)) = hN * lamN := by simpa using hT 5
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
  refine ⟨by rw [t1]; exact hK, fun hne => ?_, ?_, ?_, ?_, ?_⟩
  · rw [t1] at hne
    rw [t2, p6, p4, p0, p1, p5, h11, h8]
    exact hcall hne
  · rw [t3, h11, p6]
  · rw [t3, t4, hnG, loadHolds_mul_gen_pow, Nat.add_zero]; exact hNl
  · rw [t5, t4, p3]
  · rw [t5]

/-- **`opening_queries` at level 0 is complete** (G:1246-1269): its meaning gives its relation. -/
theorem oqMain1_complete {s : Oq} (hs : s.RowShape) (hb1 : s.base = 1) (hpd : 4 * s.pd ≤ 80)
    (hcd : 2 ≤ s.cd) (hcd8 : s.cd ≤ 8) {odd : ℕ} (hodd : odd ≤ 1) {name loop : String} {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hbm : fm.body = oqMainT s odd loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T s odd loop)
    {cap flags lam lamN qptrs wp nG : E} {rets : List E}
    (h : MeaningOpeningQueries odd s.base s.I (s.pd + s.cd) s.cd rd
      [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    coreProgram.Rel rd name [cap, flags, lam, lamN, qptrs, wp, nG] rets := by
  obtain ⟨m, hm, hnG, hlam, bps, qs, rows, ds, hk, ch, hch, rfl⟩ := h
  have hcnt : oqCount odd s.base m = odd + 2 * m := by simp [oqCount, hb1]
  set mu := lam⁻¹ with hmu
  have hstep := oqLoop1_step (rd := rd) hfl hpl hbl [nG, qptrs, cap, flags, wp, ch, mu] rfl
  obtain ⟨hK, hcall⟩ := (guarded_loop_iff hstep).mpr ⟨m, hm, hnG, fun j hj => by
    rw [hpl]
    obtain ⟨a1, a2, a3, a4⟩ := hk (2 * j + odd) (by rw [hcnt]; omega)
    obtain ⟨b1, b2, b3, b4⟩ := hk (2 * j + odd + 1) (by rw [hcnt]; omega)
    have hv1 := hch (j + 1) (by omega)
    simp only [oqChain, hb1, ↓reduceIte] at hv1
    rw [show odd + 2 * j = 2 * j + odd by omega] at hv1
    have hv0 := hch j (by omega)
    rw [hb1] at hv0
    exact oqIter1_complete hs hpd hcd hcd8 a1 a2 a3 a4 b1 b2 b3 b4 hv0 hv1⟩
  obtain ⟨σ, hp, h8, h11, hT, hA⟩ := oqMainA_complete (rd := rd) hs hpd hcd hcd8 hodd
    (cap := cap) (flags := flags) (lamN := lamN) (qptrs := qptrs) (wp := wp) (nG := nG) (ch := ch)
    hlam [ch * nG, oqChain odd s.base mu ds m, oqChain odd s.base mu ds m * lamN]
    (fun h1 => by
      obtain ⟨a1, a2, a3, a4⟩ := hk 0 (by rw [hcnt]; omega)
      have := hch 0 (by omega)
      simp only [oqChain, h1, ↓reduceIte] at this
      exact ⟨_, _, _, _, a1, a2, a3, a4, this⟩)
    (fun h1 => by
      have := hch 0 (by omega)
      simpa only [oqChain, h1, ↓reduceIte] using this)
  exact oqMainT_complete hfm hpm hbm hnG (hch m le_rfl) hp h8 h11 hT hA hK hcall

/-- **`opening_queries` deeper is complete** (G:1246-1269, `base = 0`, `odd = 0`). -/
theorem oqMain0_complete {s : Oq} (hs : s.RowShape) (hb0 : s.base = 0) (hpd : 4 * s.pd ≤ 80)
    (hcd : 2 ≤ s.cd) (hcd8 : s.cd ≤ 8) {name loop : String} {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hbm : fm.body = oqMainT s 0 loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop0T s loop)
    {cap flags lam lamN qptrs wp nG : E} {rets : List E}
    (h : MeaningOpeningQueries 0 s.base s.I (s.pd + s.cd) s.cd rd
      [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    coreProgram.Rel rd name [cap, flags, lam, lamN, qptrs, wp, nG] rets := by
  obtain ⟨m, hm, hnG, hlam, bps, qs, rows, ds, hk, ch, hch, rfl⟩ := h
  have hcnt : oqCount 0 s.base m = m := by simp [oqCount, hb0]
  set mu := lam⁻¹ with hmu
  have hstep := oqLoop0_step (rd := rd) hfl hpl hbl [nG, qptrs, cap, flags, wp, ch, mu] rfl
  obtain ⟨hK, hcall⟩ := (guarded_loop_iff hstep).mpr ⟨m, hm, hnG, fun j hj => by
    rw [hpl]
    obtain ⟨a1, a2, a3, a4⟩ := hk j (by rw [hcnt]; exact hj)
    have hv1 := hch (j + 1) (by omega)
    simp only [oqChain, hb0, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte] at hv1
    have hv0 := hch j (by omega)
    rw [hb0] at hv0
    exact oqIter0_complete hs hpd hcd hcd8 a1 a2 a3 a4 hv0 hv1⟩
  obtain ⟨σ, hp, h8, h11, hT, hA⟩ := oqMainA_complete (rd := rd) hs hpd hcd hcd8 (odd := 0)
    (by decide) (cap := cap) (flags := flags) (lamN := lamN) (qptrs := qptrs) (wp := wp) (nG := nG)
    (ch := ch) hlam [ch * nG, oqChain 0 s.base mu ds m, oqChain 0 s.base mu ds m * lamN]
    (fun h1 => absurd h1 (by decide))
    (fun h1 => by
      have := hch 0 (by omega)
      simpa only [oqChain, h1, ↓reduceIte] using this)
  exact oqMainT_complete hfm hpm hbm hnG (hch m le_rfl) hp h8 h11 hT hA hK hcall

/-- **`opening_queries` at level 0 is its meaning** (G:1246-1269), the bit pointers pointing to
bits. -/
theorem oqMain1_iff {s : Oq} (hs : s.RowShape) (hb1 : s.base = 1) (hpd : 4 * s.pd ≤ 80)
    (hcd : 2 ≤ s.cd) (hcd8 : s.cd ≤ 8) {odd : ℕ} (hodd : odd ≤ 1) {name loop : String} {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hbm : fm.body = oqMainT s odd loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T s odd loop) :
    opening_queries_Spec name odd s.base s.I (s.pd + s.cd) s.cd :=
  fun _ _ _ _ _ _ _ _ _ hbits =>
    ⟨oqMain1_sound hs hb1 hcd hcd8 hodd hfm hpm hbm hfl hpl hbl hbits,
      oqMain1_complete hs hb1 hpd hcd hcd8 hodd hfm hpm hbm hfl hpl hbl⟩

/-- **`opening_queries` deeper is its meaning** (G:1246-1269), the bit pointers pointing to
bits. -/
theorem oqMain0_iff {s : Oq} (hs : s.RowShape) (hb0 : s.base = 0) (hpd : 4 * s.pd ≤ 80)
    (hcd : 2 ≤ s.cd) (hcd8 : s.cd ≤ 8) {name loop : String} {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hbm : fm.body = oqMainT s 0 loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop0T s loop) :
    opening_queries_Spec name 0 s.base s.I (s.pd + s.cd) s.cd :=
  fun _ _ _ _ _ _ _ _ _ hbits =>
    ⟨oqMain0_sound hs hb0 hcd hcd8 hfm hpm hbm hfl hpl hbl hbits,
      oqMain0_complete hs hb0 hpd hcd hcd8 hfm hpm hbm hfl hpl hbl⟩

end
end LeanVM.Guest.B1
