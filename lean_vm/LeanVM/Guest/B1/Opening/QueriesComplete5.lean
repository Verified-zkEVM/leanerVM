/-
  LeanVM.Guest.B1.Opening.QueriesComplete5

  The completeness of an iteration of `opening_queries`' loop: its queries open and the chain
  steps, so its atoms hold.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesComplete4

/-!
# A loop iteration, completeness

`oqIter1_complete` (level 0, two queries) and `oqIter0_complete` (deeper, one query) are the
converses of `oqIter1_sound` and `oqIter0_sound`: at `x = g^j`, with the bit pointers, the
queries' openings and the chain's words at `j` and `j + 1`, the iteration's body of atoms holds
(`AtomsBody`). The valuation: the parameters, the bit pointers' addresses, each query's honest
values (`QD.val`) and the chain step's.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-- **A level-0 iteration holds** at `x = g^j` (G:1253-1257) when its two queries open at the
positions the bit pointers `qptrs[2j + odd]`, `qptrs[2j + odd + 1]` spell, and the chain steps by
their values. -/
theorem oqIter1_complete {s : Oq} (hs : s.RowShape) (hpd : 4 * s.pd ≤ 80) (hcd : 2 ≤ s.cd)
    (hcd8 : s.cd ≤ 8) {odd j : ℕ} {N qptrs cap flags wp ch mu : E}
    {bp1 bp2 : E} {q1 q2 : ℕ} {r1 r2 : List K} {d0 d1 v : E}
    (hb1 : LoadHolds rd qptrs (2 * j + odd) bp1) (hq1 : q1 < 2 ^ (s.pd + s.cd))
    (hbits1 : ∀ l < s.pd + s.cd, LoadHolds rd bp1 l (bitE (q1.testBit l)))
    (ho1 : QueryOpens rd s.base s.I (s.pd + s.cd) s.cd cap flags wp q1 r1 d0)
    (hb2 : LoadHolds rd qptrs (2 * j + odd + 1) bp2) (hq2 : q2 < 2 ^ (s.pd + s.cd))
    (hbits2 : ∀ l < s.pd + s.cd, LoadHolds rd bp2 l (bitE (q2.testBit l)))
    (ho2 : QueryOpens rd s.base s.I (s.pd + s.cd) s.cd cap flags wp q2 r2 d1)
    (hv : LoadHolds rd ch j v) (hv1 : LoadHolds rd ch (j + 1) (((v + d0) * mu + d1) * mu)) :
    AtomsBody rd oqLoopParams (oqLoop1A s odd) [gen ^ j, N, qptrs, cap, flags, wp, ch, mu] := by
  obtain ⟨w1, sb1, pp1, hd0, hok1⟩ := QD.exists_of_opens hq1 ho1
  obtain ⟨w2, sb2, pp2, hd1, hok2⟩ := QD.exists_of_opens hq2 ho2
  set x : E := gen ^ j with hx
  set D1 : QD := ⟨s, 11, true, 0, r1, w1, q1, sb1, pp1, cap, flags, rd⟩ with hD1
  set D2 : QD := ⟨s, oqE1 s + 1, false, oqK1 11 s.R + s.D, r2, w2, q2, sb2, pp2, cap, flags, rd⟩
    with hD2
  have he1 : oqE1 s = D1.z + 11 := QD.end_eq D1
  have hc : oqC1 s = D2.z + 11 := QD.end_eq D2
  obtain ⟨a1, a2, a3, a4, a5⟩ := D1.places
  obtain ⟨b1, b2, b3, b4, b5⟩ := D2.places
  have hk1 := QD.k1_eq D1
  have hk2 := QD.k1_eq D2
  set e1 := oqE1 s with he1'
  set c := oqC1 s with hc'
  let cv : List E := [ch * x, v, v + d0, (v + d0) * mu, (v + d0) * mu + d1, ((v + d0) * mu + d1) * mu,
    ch * x, word 2 0 0, x * word 2 0 0, x * word 2 0 0 + N, word 2 0 0, x * word 2 0 0]
  let f : ℕ → E := fun i =>
    if i < 8 then [x, N, qptrs, cap, flags, wp, ch, mu].getD i 0
    else if i = 8 then qptrs * x
    else if i = 9 then qptrs * x * x
    else if i = 10 then bp1
    else if i < e1 then D1.val i
    else if i = e1 then bp2
    else if i < c then D2.val i
    else cv.getD (i - c) 0
  let σ : Val := fun w => f w.idx
  have ev : ∀ i, σ (.n i) = f i := fun _ => rfl
  have eP : ∀ i < 8, σ (.n i) = [x, N, qptrs, cap, flags, wp, ch, mu].getD i 0 := fun i hi => by
    rw [ev]; simp only [f, hi, ↓reduceIte]
  have e8 : σ (.n 8) = qptrs * x := by rw [ev]; simp only [f]; simp
  have e9 : σ (.n 9) = qptrs * x * x := by rw [ev]; simp only [f]; simp
  have e10 : σ (.n 10) = bp1 := by rw [ev]; simp only [f]; simp
  have eQ1 : ∀ i, D1.b ≤ i → i < D1.z + 11 → σ (.n i) = D1.val i := fun i h1 h2 => by
    have : D1.b = 11 := rfl
    rw [ev]
    simp only [f, show ¬ i < 8 by omega, show i ≠ 8 by omega, show i ≠ 9 by omega,
      show i ≠ 10 by omega, show i < e1 by omega, ↓reduceIte]
  have eE1 : σ (.n e1) = bp2 := by
    rw [ev]
    simp only [f, show ¬ e1 < 8 by omega, show e1 ≠ 8 by omega, show e1 ≠ 9 by omega,
      show e1 ≠ 10 by omega, lt_irrefl, ↓reduceIte]
  have eQ2 : ∀ i, D2.b ≤ i → i < D2.z + 11 → σ (.n i) = D2.val i := fun i h1 h2 => by
    have : D2.b = e1 + 1 := rfl
    rw [ev]
    simp only [f, show ¬ i < 8 by omega, show i ≠ 8 by omega, show i ≠ 9 by omega,
      show i ≠ 10 by omega, show ¬ i < e1 by omega, show i ≠ e1 by omega, show i < c by omega,
      ↓reduceIte]
  have eC : ∀ o, σ (.n (c + o)) = cv.getD o 0 := fun o => by
    have : D2.b = e1 + 1 := rfl
    rw [ev]
    simp only [f, show ¬ c + o < 8 by omega, show c + o ≠ 8 by omega, show c + o ≠ 9 by omega,
      show c + o ≠ 10 by omega, show ¬ c + o < e1 by omega, show c + o ≠ e1 by omega,
      show ¬ c + o < c by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  -- the queries
  have hp1 := D1.pad_of_emit rfl eQ1
  have hw : σ (.n 5) = wp := eP 5 (by omega)
  obtain ⟨hA1, hdot1⟩ := D1.query_complete (σ := σ) (bp := .n 10) (cap := .n 3) (flags := .n 4)
    (wp := .n 5) hs hpd hcd hcd8 (by rw [hw]; exact hok1 _ _ _) eQ1 hp1.1 hp1.2
    (by rw [e10]; exact hbits1) (eP 3 (by omega)) (eP 4 (by omega))
  obtain ⟨hA2, hdot2⟩ := D2.query_complete (σ := σ) (bp := .n e1) (cap := .n 3) (flags := .n 4)
    (wp := .n 5) hs hpd hcd hcd8 (by rw [hw]; exact hok2 _ _ _) eQ2 hp1.1 hp1.2
    (by rw [eE1]; exact hbits2) (eP 3 (by omega)) (eP 4 (by omega))
  rw [← hd0] at hdot1
  rw [← hd1] at hdot2
  refine ⟨σ, rfl, fun a ha => ?_⟩
  simp only [oqLoop1A, List.mem_append] at ha
  rcases ha with (((ha | ha) | ha) | ha) | ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    rcases ha with rfl | rfl | rfl
    · show σ (.n 8) = σ (.n 2) * σ (.n 0)
      rw [e8, eP 2 (by omega), eP 0 (by omega)]; rfl
    · show σ (.n 9) = σ (.n 8) * σ (.n 0)
      rw [e9, e8, eP 0 (by omega)]; rfl
    · show LoadHolds rd (σ (.n 9)) odd (σ (.n 10))
      rw [e9, e10, mul_assoc, hx, ← pow_add, ← two_mul, loadHolds_mul_gen_pow]
      exact hb1
  · exact hA1 a ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    subst ha
    show LoadHolds rd (σ (.n 9)) (odd + 1) (σ (.n e1))
    rw [e9, eE1, mul_assoc, hx, ← pow_add, ← two_mul, loadHolds_mul_gen_pow, ← Nat.add_assoc]
    exact hb2
  · exact hA2 a ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    have c0 := eC 0
    simp only [Nat.add_zero] at c0
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show σ (.n c) = σ (.n 6) * σ (.n 0)
      rw [c0, eP 6 (by omega), eP 0 (by omega)]; rfl
    · show LoadHolds rd (σ (.n c)) 0 (σ (.n (c + 1)))
      rw [c0, eC 1]
      show LoadHolds rd (ch * gen ^ j) 0 v
      rw [loadHolds_mul_gen_pow]; exact hv
    · show σ (.n (c + 2)) = σ (.n (c + 1)) + σ (.n (oqDot s 11))
      rw [eC 2, eC 1, hdot1]; rfl
    · show σ (.n (c + 3)) = σ (.n (c + 2)) * σ (.n 7)
      rw [eC 3, eC 2, eP 7 (by omega)]; rfl
    · show σ (.n (c + 4)) = σ (.n (c + 3)) + σ (.n (oqDot s (e1 + 1)))
      rw [eC 4, eC 3, hdot2]; rfl
    · show σ (.n (c + 5)) = σ (.n (c + 4)) * σ (.n 7)
      rw [eC 5, eC 4, eP 7 (by omega)]; rfl
    · show σ (.n (c + 6)) = σ (.n 6) * σ (.n 0)
      rw [eC 6, eP 6 (by omega), eP 0 (by omega)]; rfl
    · show LoadHolds rd (σ (.n (c + 6))) 1 (σ (.n (c + 5)))
      rw [eC 6, eC 5]
      show LoadHolds rd (ch * gen ^ j) 1 (((v + d0) * mu + d1) * mu)
      rw [loadHolds_mul_gen_pow]; exact hv1
    · exact eC 7
    · show σ (.n (c + 8)) = σ (.n 0) * σ (.n (c + 7))
      rw [eC 8, eC 7, eP 0 (by omega)]; rfl
    · show σ (.n (c + 9)) = σ (.n (c + 8)) + σ (.n 1)
      rw [eC 9, eC 8, eP 1 (by omega)]; rfl
    · exact eC 10
    · show σ (.n (c + 11)) = σ (.n 0) * σ (.n (c + 10))
      rw [eC 11, eC 10, eP 0 (by omega)]; rfl

/-- **A deeper iteration holds** at `x = g^j` (G:1258-1260) when its query opens at the position
the bit pointer `qptrs[j]` spells, and the chain steps by its value. -/
theorem oqIter0_complete {s : Oq} (hs : s.RowShape) (hpd : 4 * s.pd ≤ 80) (hcd : 2 ≤ s.cd)
    (hcd8 : s.cd ≤ 8) {j : ℕ} {N qptrs cap flags wp ch mu : E}
    {bp : E} {q : ℕ} {r : List K} {d v : E}
    (hb : LoadHolds rd qptrs j bp) (hq : q < 2 ^ (s.pd + s.cd))
    (hbits : ∀ l < s.pd + s.cd, LoadHolds rd bp l (bitE (q.testBit l)))
    (ho : QueryOpens rd s.base s.I (s.pd + s.cd) s.cd cap flags wp q r d)
    (hv : LoadHolds rd ch j v) (hv1 : LoadHolds rd ch (j + 1) ((v + d) * mu)) :
    AtomsBody rd oqLoopParams (oqLoop0A s) [gen ^ j, N, qptrs, cap, flags, wp, ch, mu] := by
  obtain ⟨w1, sb1, pp1, hd0, hok1⟩ := QD.exists_of_opens hq ho
  set x : E := gen ^ j with hx
  set D1 : QD := ⟨s, 10, true, 0, r, w1, q, sb1, pp1, cap, flags, rd⟩ with hD1
  have hc : oqC0 s = D1.z + 11 := QD.end_eq D1
  obtain ⟨a1, a2, a3, a4, a5⟩ := D1.places
  have hk1 := QD.k1_eq D1
  set c := oqC0 s with hc'
  let cv : List E := [ch * x, v, v + d, (v + d) * mu, ch * x, word 2 0 0, x * word 2 0 0,
    x * word 2 0 0 + N, word 2 0 0, x * word 2 0 0]
  let f : ℕ → E := fun i =>
    if i < 8 then [x, N, qptrs, cap, flags, wp, ch, mu].getD i 0
    else if i = 8 then qptrs * x
    else if i = 9 then bp
    else if i < c then D1.val i
    else cv.getD (i - c) 0
  let σ : Val := fun w => f w.idx
  have ev : ∀ i, σ (.n i) = f i := fun _ => rfl
  have eP : ∀ i < 8, σ (.n i) = [x, N, qptrs, cap, flags, wp, ch, mu].getD i 0 := fun i hi => by
    rw [ev]; simp only [f, hi, ↓reduceIte]
  have e8 : σ (.n 8) = qptrs * x := by rw [ev]; simp only [f]; simp
  have e9 : σ (.n 9) = bp := by rw [ev]; simp only [f]; simp
  have eQ1 : ∀ i, D1.b ≤ i → i < D1.z + 11 → σ (.n i) = D1.val i := fun i h1 h2 => by
    have : D1.b = 10 := rfl
    rw [ev]
    simp only [f, show ¬ i < 8 by omega, show i ≠ 8 by omega, show i ≠ 9 by omega,
      show i < c by omega, ↓reduceIte]
  have eC : ∀ o, σ (.n (c + o)) = cv.getD o 0 := fun o => by
    have : D1.b = 10 := rfl
    rw [ev]
    simp only [f, show ¬ c + o < 8 by omega, show c + o ≠ 8 by omega, show c + o ≠ 9 by omega,
      show ¬ c + o < c by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  have hp1 := D1.pad_of_emit rfl eQ1
  have hw : σ (.n 5) = wp := eP 5 (by omega)
  obtain ⟨hA1, hdot1⟩ := D1.query_complete (σ := σ) (bp := .n 9) (cap := .n 3) (flags := .n 4)
    (wp := .n 5) hs hpd hcd hcd8 (by rw [hw]; exact hok1 _ _ _) eQ1 hp1.1 hp1.2
    (by rw [e9]; exact hbits) (eP 3 (by omega)) (eP 4 (by omega))
  rw [← hd0] at hdot1
  refine ⟨σ, rfl, fun a ha => ?_⟩
  simp only [oqLoop0A, List.mem_append] at ha
  rcases ha with (ha | ha) | ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    rcases ha with rfl | rfl
    · show σ (.n 8) = σ (.n 2) * σ (.n 0)
      rw [e8, eP 2 (by omega), eP 0 (by omega)]; rfl
    · show LoadHolds rd (σ (.n 8)) 0 (σ (.n 9))
      rw [e8, e9, hx, loadHolds_mul_gen_pow, Nat.add_zero]
      exact hb
  · exact hA1 a ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    have c0 := eC 0
    simp only [Nat.add_zero] at c0
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show σ (.n c) = σ (.n 6) * σ (.n 0)
      rw [c0, eP 6 (by omega), eP 0 (by omega)]; rfl
    · show LoadHolds rd (σ (.n c)) 0 (σ (.n (c + 1)))
      rw [c0, eC 1]
      show LoadHolds rd (ch * gen ^ j) 0 v
      rw [loadHolds_mul_gen_pow]; exact hv
    · show σ (.n (c + 2)) = σ (.n (c + 1)) + σ (.n (oqDot s 10))
      rw [eC 2, eC 1, hdot1]; rfl
    · show σ (.n (c + 3)) = σ (.n (c + 2)) * σ (.n 7)
      rw [eC 3, eC 2, eP 7 (by omega)]; rfl
    · show σ (.n (c + 4)) = σ (.n 6) * σ (.n 0)
      rw [eC 4, eP 6 (by omega), eP 0 (by omega)]; rfl
    · show LoadHolds rd (σ (.n (c + 4))) 1 (σ (.n (c + 3)))
      rw [eC 4, eC 3]
      show LoadHolds rd (ch * gen ^ j) 1 ((v + d) * mu)
      rw [loadHolds_mul_gen_pow]; exact hv1
    · exact eC 5
    · show σ (.n (c + 6)) = σ (.n 0) * σ (.n (c + 5))
      rw [eC 6, eC 5, eP 0 (by omega)]; rfl
    · show σ (.n (c + 7)) = σ (.n (c + 6)) + σ (.n 1)
      rw [eC 7, eC 6, eP 1 (by omega)]; rfl
    · exact eC 8
    · show σ (.n (c + 9)) = σ (.n 0) * σ (.n (c + 8))
      rw [eC 9, eC 8, eP 0 (by omega)]; rfl

end
end LeanVM.Guest.B1
