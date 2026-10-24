/-
  LeanVM.Guest.B1.Opening.QueriesPlaced2

  The pointers an honest query loads through, and an iteration's honest valuation with its path's
  frame addresses given.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesComplete5
public import LeanVM.Guest.B1.Opening.QueriesPlaced1

/-!
# Pointers of an honest query; an iteration's valuation, its frame addresses given

`QD.ptr_level`, `QD.ptr_flag`, `QD.ptr_cap`, `QD.ptr_pp`: at the honest values a query loads its
path's children through `pp·g^(2b_l)`, its flag through `flags·g^Q` and its cap leaf through
`cap·g^(4Q + 2b_pd)` (`Q = q / 2^(pd+1)`), and its frame address is `pp`.

`oqIter1F`, `oqIter0F`: an iteration's honest values, from its queries' `QD`s (whose frame
addresses `pp` the placement chooses). `oqIter1_at`, `oqIter0_at`: its atoms hold, its tail's
guard and arguments, its frame addresses.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

namespace QD

variable (d : QD) {σ : Val}

theorem ptr_pp (hv : ∀ i, d.b ≤ i → i < d.z + 11 → σ (.n i) = d.val i) (hpd : 4 * d.s.pd ≤ 80) :
    σ (.n (d.ch + 4 * d.s.pd)) = d.pp := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := d.places
  rw [hv _ (by omega) (by omega), val_pre d (by omega)]
  simp [preV]

theorem ptr_level (hv : ∀ i, d.b ≤ i → i < d.z + 11 → σ (.n i) = d.val i) {l : ℕ}
    (hl : l < d.s.pd) :
    σ (.n (oqL0 d.ch + 17 * l + 2)) = d.pp * gen ^ (if d.q.testBit l then 2 else 0) := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := d.places
  rw [show oqL0 d.ch + 17 * l + 2 = d.ch + 83 + 17 * l + 2 by simp [oqL0],
    hv _ (by omega) (by omega), val_level d hl (by omega)]
  simp only [levelV, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte]
  rw [← bit_factor, QD.bit, word_five]
  ring

theorem ptr_flag (hv : ∀ i, d.b ≤ i → i < d.z + 11 → σ (.n i) = d.val i) (hcd : 2 ≤ d.s.cd)
    (hcd8 : d.s.cd ≤ 8) (hq : d.q < 2 ^ (d.s.pd + d.s.cd)) :
    σ (.n d.z) = d.flagsv * gen ^ (d.q / 2 ^ (d.s.pd + 1)) := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := d.places
  have hQlt : d.q / 2 ^ (d.s.pd + 1) < 2 ^ (d.s.cd - 1) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    calc d.q < 2 ^ (d.s.pd + d.s.cd) := hq
      _ = 2 ^ (d.s.cd - 1 + (d.s.pd + 1)) := by congr 1; omega
  rw [show d.z = d.z + 0 from rfl, hv _ (by omega) (by omega), val_capTail d (by omega)]
  simp only [capTailV, List.getD_cons_zero]
  rw [capQ_eq d _ (by omega), show d.s.cd - 2 + 1 = d.s.cd - 1 by omega, Nat.mod_eq_of_lt hQlt]

theorem ptr_cap (hv : ∀ i, d.b ≤ i → i < d.z + 11 → σ (.n i) = d.val i) (hcd : 2 ≤ d.s.cd)
    (hcd8 : d.s.cd ≤ 8) (hq : d.q < 2 ^ (d.s.pd + d.s.cd)) :
    σ (.n (d.z + 10)) = d.capv * gen ^ (4 * (d.q / 2 ^ (d.s.pd + 1)) +
      (if d.q.testBit d.s.pd then 2 else 0)) := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := d.places
  have hQlt : d.q / 2 ^ (d.s.pd + 1) < 2 ^ (d.s.cd - 1) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    calc d.q < 2 ^ (d.s.pd + d.s.cd) := hq
      _ = 2 ^ (d.s.cd - 1 + (d.s.pd + 1)) := by congr 1; omega
  have hqv : d.capQ (d.s.cd - 2) = gen ^ (d.q / 2 ^ (d.s.pd + 1)) := by
    rw [capQ_eq d _ (by omega), show d.s.cd - 2 + 1 = d.s.cd - 1 by omega, Nat.mod_eq_of_lt hQlt]
  rw [hv _ (by omega) (by omega), val_capTail d (by omega)]
  simp only [capTailV, List.getD_cons_succ, List.getD_cons_zero]
  rw [hqv, word_one, word_five, QD.bit, bit_factor, ← pow_add, mul_assoc, ← pow_add, mul_assoc,
    ← pow_add]
  congr 2; ring

end QD

/-! ## A level-0 iteration -/

/-- The chain step's values of a level-0 iteration. -/
def oqIter1C (x N ch mu v d0 d1 : E) : List E :=
  [ch * x, v, v + d0, (v + d0) * mu, (v + d0) * mu + d1, ((v + d0) * mu + d1) * mu,
    ch * x, word 2 0 0, x * word 2 0 0, x * word 2 0 0 + N, word 2 0 0, x * word 2 0 0]

/-- **A level-0 iteration's honest values**, from its arguments, its queries, their bit pointers
and the chain's word `v`. -/
def oqIter1F (s : Oq) (args : List E) (D1 D2 : QD) (bp1 bp2 v : E) (i : ℕ) : E :=
  let x := args.getD 0 0
  if i < 8 then args.getD i 0
  else if i = 8 then args.getD 2 0 * x
  else if i = 9 then args.getD 2 0 * x * x
  else if i = 10 then bp1
  else if i < oqE1 s then D1.val i
  else if i = oqE1 s then bp2
  else if i < oqC1 s then D2.val i
  else (oqIter1C x (args.getD 1 0) (args.getD 6 0) (args.getD 7 0) v
    (rowDot s.base s.I D1.row D1.w) (rowDot s.base s.I D2.row D2.w)).getD (i - oqC1 s) 0

variable {rd : Reader}

/-- **A level-0 iteration at its honest values**: at a valuation holding `oqIter1F` (its queries
`D1` at `11`, emitting the padding run, and `D2` after it), its atoms hold, its parameters are its
arguments, its tail's guard and arguments, its loads' pointers. -/
theorem oqIter1_at {s : Oq} (hs : s.RowShape) (hpd : 4 * s.pd ≤ 80) (hcd : 2 ≤ s.cd)
    (hcd8 : s.cd ≤ 8) {odd j : ℕ} {N qptrs cap flags wp ch mu : E}
    {r1 r2 : List K} {w1 w2 : ℕ → E} {q1 q2 : ℕ} {sb1 sb2 : List Digest} {pp1 pp2 : E}
    (hok1 : (⟨s, 11, true, 0, r1, w1, q1, sb1, pp1, cap, flags, rd⟩ : QD).Ok rd wp)
    (hok2 : (⟨s, oqE1 s + 1, false, oqK1 11 s.R + s.D, r2, w2, q2, sb2, pp2, cap, flags, rd⟩ :
      QD).Ok rd wp) {bp1 bp2 v : E}
    (hb1 : LoadHolds rd qptrs (2 * j + odd) bp1)
    (hbits1 : ∀ l < s.pd + s.cd, LoadHolds rd bp1 l (bitE (q1.testBit l)))
    (hb2 : LoadHolds rd qptrs (2 * j + odd + 1) bp2)
    (hbits2 : ∀ l < s.pd + s.cd, LoadHolds rd bp2 l (bitE (q2.testBit l)))
    (hv : LoadHolds rd ch j v)
    (hv1 : LoadHolds rd ch (j + 1) (((v + rowDot s.base s.I r1 w1) * mu +
      rowDot s.base s.I r2 w2) * mu))
    {σ : Val} (hσ : ∀ i, σ (.n i) = oqIter1F s [gen ^ j, N, qptrs, cap, flags, wp, ch, mu]
      ⟨s, 11, true, 0, r1, w1, q1, sb1, pp1, cap, flags, rd⟩
      ⟨s, oqE1 s + 1, false, oqK1 11 s.R + s.D, r2, w2, q2, sb2, pp2, cap, flags, rd⟩ bp1 bp2 v i) :
    oqLoopParams.map σ = [gen ^ j, N, qptrs, cap, flags, wp, ch, mu] ∧
      (∀ a, Stmt.atom a ∈ oqLoop1A s odd → a.Holds rd σ) ∧
      (∀ i, 11 ≤ i → i < oqE1 s → σ (.n i) =
        (⟨s, 11, true, 0, r1, w1, q1, sb1, pp1, cap, flags, rd⟩ : QD).val i) ∧
      (∀ i, oqE1 s + 1 ≤ i → i < oqC1 s → σ (.n i) =
        (⟨s, oqE1 s + 1, false, oqK1 11 s.R + s.D, r2, w2, q2, sb2, pp2, cap, flags, rd⟩ : QD).val i) ∧
      σ (.n 9) = qptrs * gen ^ j * gen ^ j ∧ σ (.n 10) = bp1 ∧ σ (.n (oqE1 s)) = bp2 ∧
      σ (.n (oqC1 s)) = ch * gen ^ j ∧ σ (.n (oqC1 s + 6)) = ch * gen ^ j ∧
      σ (.n (oqC1 s + 9)) = gen ^ j * gen + N ∧ σ (.n (oqC1 s + 11)) = gen ^ j * gen := by
  set D1 : QD := ⟨s, 11, true, 0, r1, w1, q1, sb1, pp1, cap, flags, rd⟩ with hD1
  set D2 : QD := ⟨s, oqE1 s + 1, false, oqK1 11 s.R + s.D, r2, w2, q2, sb2, pp2, cap, flags, rd⟩
    with hD2
  have he1 : oqE1 s = D1.z + 11 := QD.end_eq D1
  have hc : oqC1 s = D2.z + 11 := QD.end_eq D2
  obtain ⟨a1, a2, a3, a4, a5⟩ := D1.places
  obtain ⟨b1, b2, b3, b4, b5⟩ := D2.places
  have hk1 := QD.k1_eq D1
  have hk2 := QD.k1_eq D2
  have eP : ∀ i < 8, σ (.n i) = [gen ^ j, N, qptrs, cap, flags, wp, ch, mu].getD i 0 := fun i hi => by
    rw [hσ]; simp only [oqIter1F, hi, ↓reduceIte]
  have e8 : σ (.n 8) = qptrs * gen ^ j := by rw [hσ]; simp [oqIter1F]
  have e9 : σ (.n 9) = qptrs * gen ^ j * gen ^ j := by rw [hσ]; simp [oqIter1F]
  have e10 : σ (.n 10) = bp1 := by rw [hσ]; simp [oqIter1F]
  have eQ1 : ∀ i, D1.b ≤ i → i < D1.z + 11 → σ (.n i) = D1.val i := fun i h1 h2 => by
    have : D1.b = 11 := rfl
    rw [hσ]
    simp only [oqIter1F, show ¬ i < 8 by omega, show i ≠ 8 by omega, show i ≠ 9 by omega,
      show i ≠ 10 by omega, show i < oqE1 s by omega, ↓reduceIte]
  have eE1 : σ (.n (oqE1 s)) = bp2 := by
    rw [hσ]
    simp only [oqIter1F, show ¬ oqE1 s < 8 by omega, show oqE1 s ≠ 8 by omega,
      show oqE1 s ≠ 9 by omega, show oqE1 s ≠ 10 by omega, lt_irrefl, ↓reduceIte]
  have eQ2 : ∀ i, D2.b ≤ i → i < D2.z + 11 → σ (.n i) = D2.val i := fun i h1 h2 => by
    have : D2.b = oqE1 s + 1 := rfl
    rw [hσ]
    simp only [oqIter1F, show ¬ i < 8 by omega, show i ≠ 8 by omega, show i ≠ 9 by omega,
      show i ≠ 10 by omega, show ¬ i < oqE1 s by omega, show i ≠ oqE1 s by omega,
      show i < oqC1 s by omega, ↓reduceIte]
  have eC : ∀ o, σ (.n (oqC1 s + o)) = (oqIter1C (gen ^ j) N ch mu v
      (rowDot s.base s.I r1 w1) (rowDot s.base s.I r2 w2)).getD o 0 := fun o => by
    have : D2.b = oqE1 s + 1 := rfl
    rw [hσ]
    simp only [oqIter1F, show ¬ oqC1 s + o < 8 by omega, show oqC1 s + o ≠ 8 by omega,
      show oqC1 s + o ≠ 9 by omega, show oqC1 s + o ≠ 10 by omega,
      show ¬ oqC1 s + o < oqE1 s by omega, show oqC1 s + o ≠ oqE1 s by omega,
      show ¬ oqC1 s + o < oqC1 s by omega, ↓reduceIte, Nat.add_sub_cancel_left]
    rfl
  have hp1 := D1.pad_of_emit rfl eQ1
  have hw : σ (.n 5) = wp := eP 5 (by omega)
  obtain ⟨hA1, hdot1⟩ := D1.query_complete (σ := σ) (bp := .n 10) (cap := .n 3) (flags := .n 4)
    (wp := .n 5) hs hpd hcd hcd8 (by rw [hw]; exact hok1) eQ1 hp1.1 hp1.2
    (by rw [e10]; exact hbits1) (eP 3 (by omega)) (eP 4 (by omega))
  obtain ⟨hA2, hdot2⟩ := D2.query_complete (σ := σ) (bp := .n (oqE1 s)) (cap := .n 3)
    (flags := .n 4) (wp := .n 5) hs hpd hcd hcd8 (by rw [hw]; exact hok2) eQ2 hp1.1 hp1.2
    (by rw [eE1]; exact hbits2) (eP 3 (by omega)) (eP 4 (by omega))
  change σ (.n (oqDot s 11)) = rowDot s.base s.I r1 w1 at hdot1
  change σ (.n (oqDot s (oqE1 s + 1))) = rowDot s.base s.I r2 w2 at hdot2
  have c0 := eC 0
  simp only [Nat.add_zero] at c0
  refine ⟨?_, fun a ha => ?_, fun i h1 h2 => eQ1 i h1 (by omega), fun i h1 h2 => eQ2 i h1 (by omega), e9, e10, eE1, c0,
    by rw [eC 6]; rfl, by rw [eC 9]; simp [oqIter1C, word_gen], by rw [eC 11]; simp [oqIter1C, word_gen]⟩
  · simp only [oqLoopParams, List.map_cons, List.map_nil]
    rw [eP 0 (by omega), eP 1 (by omega), eP 2 (by omega), eP 3 (by omega), eP 4 (by omega),
      eP 5 (by omega), eP 6 (by omega), eP 7 (by omega)]
    rfl
  simp only [oqLoop1A, List.mem_append] at ha
  rcases ha with (((ha | ha) | ha) | ha) | ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    rcases ha with rfl | rfl | rfl
    · show σ (.n 8) = σ (.n 2) * σ (.n 0)
      rw [e8, eP 2 (by omega), eP 0 (by omega)]; rfl
    · show σ (.n 9) = σ (.n 8) * σ (.n 0)
      rw [e9, e8, eP 0 (by omega)]; rfl
    · show LoadHolds rd (σ (.n 9)) odd (σ (.n 10))
      rw [e9, e10, mul_assoc, ← pow_add, ← two_mul, loadHolds_mul_gen_pow]
      exact hb1
  · exact hA1 a ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    subst ha
    show LoadHolds rd (σ (.n 9)) (odd + 1) (σ (.n (oqE1 s)))
    rw [e9, eE1, mul_assoc, ← pow_add, ← two_mul, loadHolds_mul_gen_pow, ← Nat.add_assoc]
    exact hb2
  · exact hA2 a ha
  · set c := oqC1 s with hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
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
    · show σ (.n (c + 4)) = σ (.n (c + 3)) + σ (.n (oqDot s (oqE1 s + 1)))
      rw [eC 4, eC 3, hdot2]; rfl
    · show σ (.n (c + 5)) = σ (.n (c + 4)) * σ (.n 7)
      rw [eC 5, eC 4, eP 7 (by omega)]; rfl
    · show σ (.n (c + 6)) = σ (.n 6) * σ (.n 0)
      rw [eC 6, eP 6 (by omega), eP 0 (by omega)]; rfl
    · show LoadHolds rd (σ (.n (c + 6))) 1 (σ (.n (c + 5)))
      rw [eC 6, eC 5]
      show LoadHolds rd (ch * gen ^ j) 1 (((v + rowDot s.base s.I r1 w1) * mu +
        rowDot s.base s.I r2 w2) * mu)
      rw [loadHolds_mul_gen_pow]; exact hv1
    · exact eC 7
    · show σ (.n (c + 8)) = σ (.n 0) * σ (.n (c + 7))
      rw [eC 8, eC 7, eP 0 (by omega)]; rfl
    · show σ (.n (c + 9)) = σ (.n (c + 8)) + σ (.n 1)
      rw [eC 9, eC 8, eP 1 (by omega)]; rfl
    · exact eC 10
    · show σ (.n (c + 11)) = σ (.n 0) * σ (.n (c + 10))
      rw [eC 11, eC 10, eP 0 (by omega)]; rfl

/-! ## A deeper iteration -/

/-- The chain step's values of a deeper iteration. -/
def oqIter0C (x N ch mu v d : E) : List E :=
  [ch * x, v, v + d, (v + d) * mu, ch * x, word 2 0 0, x * word 2 0 0, x * word 2 0 0 + N,
    word 2 0 0, x * word 2 0 0]

/-- **A deeper iteration's honest values**, from its arguments, its query, its bit pointer and the
chain's word `v`. -/
def oqIter0F (s : Oq) (args : List E) (D : QD) (bp v : E) (i : ℕ) : E :=
  let x := args.getD 0 0
  if i < 8 then args.getD i 0
  else if i = 8 then args.getD 2 0 * x
  else if i = 9 then bp
  else if i < oqC0 s then D.val i
  else (oqIter0C x (args.getD 1 0) (args.getD 6 0) (args.getD 7 0) v
    (rowDot s.base s.I D.row D.w)).getD (i - oqC0 s) 0

/-- **A deeper iteration at its honest values.** -/
theorem oqIter0_at {s : Oq} (hs : s.RowShape) (hpd : 4 * s.pd ≤ 80) (hcd : 2 ≤ s.cd)
    (hcd8 : s.cd ≤ 8) {j : ℕ} {N qptrs cap flags wp ch mu : E}
    {r : List K} {w : ℕ → E} {q : ℕ} {sb : List Digest} {pp : E}
    (hok : (⟨s, 10, true, 0, r, w, q, sb, pp, cap, flags, rd⟩ : QD).Ok rd wp) {bp v : E}
    (hb : LoadHolds rd qptrs j bp)
    (hbits : ∀ l < s.pd + s.cd, LoadHolds rd bp l (bitE (q.testBit l)))
    (hv : LoadHolds rd ch j v)
    (hv1 : LoadHolds rd ch (j + 1) ((v + rowDot s.base s.I r w) * mu))
    {σ : Val} (hσ : ∀ i, σ (.n i) = oqIter0F s [gen ^ j, N, qptrs, cap, flags, wp, ch, mu]
      ⟨s, 10, true, 0, r, w, q, sb, pp, cap, flags, rd⟩ bp v i) :
    oqLoopParams.map σ = [gen ^ j, N, qptrs, cap, flags, wp, ch, mu] ∧
      (∀ a, Stmt.atom a ∈ oqLoop0A s → a.Holds rd σ) ∧
      (∀ i, 10 ≤ i → i < oqC0 s → σ (.n i) =
        (⟨s, 10, true, 0, r, w, q, sb, pp, cap, flags, rd⟩ : QD).val i) ∧
      σ (.n 8) = qptrs * gen ^ j ∧ σ (.n 9) = bp ∧
      σ (.n (oqC0 s)) = ch * gen ^ j ∧ σ (.n (oqC0 s + 4)) = ch * gen ^ j ∧
      σ (.n (oqC0 s + 7)) = gen ^ j * gen + N ∧ σ (.n (oqC0 s + 9)) = gen ^ j * gen := by
  set D1 : QD := ⟨s, 10, true, 0, r, w, q, sb, pp, cap, flags, rd⟩ with hD1
  have hc : oqC0 s = D1.z + 11 := QD.end_eq D1
  obtain ⟨a1, a2, a3, a4, a5⟩ := D1.places
  have hk1 := QD.k1_eq D1
  have eP : ∀ i < 8, σ (.n i) = [gen ^ j, N, qptrs, cap, flags, wp, ch, mu].getD i 0 := fun i hi => by
    rw [hσ]; simp only [oqIter0F, hi, ↓reduceIte]
  have e8 : σ (.n 8) = qptrs * gen ^ j := by rw [hσ]; simp [oqIter0F]
  have e9 : σ (.n 9) = bp := by rw [hσ]; simp [oqIter0F]
  have eQ1 : ∀ i, D1.b ≤ i → i < D1.z + 11 → σ (.n i) = D1.val i := fun i h1 h2 => by
    have : D1.b = 10 := rfl
    rw [hσ]
    simp only [oqIter0F, show ¬ i < 8 by omega, show i ≠ 8 by omega, show i ≠ 9 by omega,
      show i < oqC0 s by omega, ↓reduceIte]
  have eC : ∀ o, σ (.n (oqC0 s + o)) = (oqIter0C (gen ^ j) N ch mu v
      (rowDot s.base s.I r w)).getD o 0 := fun o => by
    have : D1.b = 10 := rfl
    rw [hσ]
    simp only [oqIter0F, show ¬ oqC0 s + o < 8 by omega, show oqC0 s + o ≠ 8 by omega,
      show oqC0 s + o ≠ 9 by omega, show ¬ oqC0 s + o < oqC0 s by omega, ↓reduceIte,
      Nat.add_sub_cancel_left]
    rfl
  have hp1 := D1.pad_of_emit rfl eQ1
  have hw : σ (.n 5) = wp := eP 5 (by omega)
  obtain ⟨hA1, hdot1⟩ := D1.query_complete (σ := σ) (bp := .n 9) (cap := .n 3) (flags := .n 4)
    (wp := .n 5) hs hpd hcd hcd8 (by rw [hw]; exact hok) eQ1 hp1.1 hp1.2
    (by rw [e9]; exact hbits) (eP 3 (by omega)) (eP 4 (by omega))
  change σ (.n (oqDot s 10)) = rowDot s.base s.I r w at hdot1
  have c0 := eC 0
  simp only [Nat.add_zero] at c0
  refine ⟨?_, fun a ha => ?_, fun i h1 h2 => eQ1 i h1 (by omega), e8, e9, c0,
    by rw [eC 4]; rfl, by rw [eC 7]; simp [oqIter0C, word_gen],
    by rw [eC 9]; simp [oqIter0C, word_gen]⟩
  · simp only [oqLoopParams, List.map_cons, List.map_nil]
    rw [eP 0 (by omega), eP 1 (by omega), eP 2 (by omega), eP 3 (by omega), eP 4 (by omega),
      eP 5 (by omega), eP 6 (by omega), eP 7 (by omega)]
    rfl
  simp only [oqLoop0A, List.mem_append] at ha
  rcases ha with (ha | ha) | ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    rcases ha with rfl | rfl
    · show σ (.n 8) = σ (.n 2) * σ (.n 0)
      rw [e8, eP 2 (by omega), eP 0 (by omega)]; rfl
    · show LoadHolds rd (σ (.n 8)) 0 (σ (.n 9))
      rw [e8, e9, loadHolds_mul_gen_pow, Nat.add_zero]
      exact hb
  · exact hA1 a ha
  · set c := oqC0 s with hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
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
      show LoadHolds rd (ch * gen ^ j) 1 ((v + rowDot s.base s.I r w) * mu)
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
