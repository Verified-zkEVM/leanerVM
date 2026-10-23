/-
  LeanVM.Guest.B1.Opening.QueriesLoop

  The loop helper of `opening_queries`: one iteration's queries and chain step.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesSound
public import LeanVM.Guest.B1.Common.Loops

/-!
# One iteration of `opening_queries`' loop (G:1259-1268)

* `oqQuery_bitLoads`: a query reads every bit of its position (`depth = pd + cd` of them);
  `bits_q`: bits read as `0`/`1` words are those of a position `q < 2^depth`.
* `oqIter1_sound`, `oqIter0_sound`: an iteration at `x = g^i` opens its queries at the bit
  pointers `qptrs[2i + odd]`, `qptrs[2i + odd + 1]` (level 0) or `qptrs[i]` (deeper), and steps
  the chain `chain[i + 1] = ((chain[i] + d0)·μ + d1)·μ` (or `(chain[i] + d)·μ`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## The bits of a position -/

/-- A query reads every bit of its position. -/
theorem oqQuery_bitLoads {s : Oq} (hcd : 2 ≤ s.cd) {bp cap flags wp : V} {b : ℕ} {emit : Bool}
    {pr : ℕ} (hA : ∀ a, Stmt.atom a ∈ oqQueryT s bp cap flags wp b emit pr → a.Holds rd σ) :
    ∀ l < s.pd + s.cd, ∃ w, LoadHolds rd (σ bp) l w := by
  obtain ⟨-, -, -, -, hPa, hC⟩ := oqQuery_pieces hA
  intro l hl
  by_cases h1 : l < s.pd
  · exact ⟨_, hPa _ (mem_oqPathT_level h1 (by simp [oqLevelT] :
      Stmt.atom (.load (.n (oqL0 (oqCh s b emit) + 17 * l)) bp l) ∈ _))⟩
  by_cases h2 : l = s.pd
  · subst h2
    exact ⟨_, hC _ (by simp [oqCapT] : Stmt.atom (.load (.n (oqCq s (oqCh s b emit) + 5 +
      6 * (s.cd - 2) + 6)) bp s.pd) ∈ _)⟩
  by_cases h3 : l = s.pd + 1
  · subst h3
    exact ⟨_, hC _ (by simp [oqCapT] : Stmt.atom (.load (.n (oqCq s (oqCh s b emit) + 1)) bp
      (s.pd + 1)) ∈ _)⟩
  obtain ⟨j, hj1, hj2, rfl⟩ : ∃ j, 1 ≤ j ∧ j ≤ s.cd - 2 ∧ l = s.pd + 1 + j :=
    ⟨l - s.pd - 1, by omega, by omega, by omega⟩
  exact ⟨_, hC _ (mem_oqCapT_bit hj1 hj2 (by simp [oqCapBitT] : Stmt.atom (.load
    (.n (oqCq s (oqCh s b emit) + 5 + 6 * (j - 1) + 1)) bp (s.pd + 1 + j)) ∈ _))⟩

/-- Bits read as `0`/`1` words are the bits of a position. -/
theorem bits_q {p : E} {D : ℕ} (hex : ∀ l < D, ∃ w, LoadHolds rd p l w)
    (hb : ∀ l < D, ∀ w, LoadHolds rd p l w → w = 0 ∨ w = 1) :
    ∃ q < 2 ^ D, ∀ l < D, LoadHolds rd p l (bitE (q.testBit l)) := by
  classical
  let w : ℕ → E := fun l => if h : l < D then Classical.choose (hex l h) else 0
  have hw : ∀ l (hl : l < D), LoadHolds rd p l (w l) := fun l hl => by
    simp only [w, hl, ↓reduceDIte]; exact Classical.choose_spec (hex l hl)
  refine ⟨bitsVal (fun l => decide (w l = 1)) D, bitsVal_lt _ _, fun l hl => ?_⟩
  rw [testBit_bitsVal, decide_eq_true hl, Bool.true_and]
  have hl' := hw l hl
  rcases hb l hl _ hl' with h | h
  · have e : bitE (decide (w l = 1)) = w l := by rw [h]; simp [bitE]
    rw [e]; exact hl'
  · have e : bitE (decide (w l = 1)) = w l := by rw [h]; simp [bitE]
    rw [e]; exact hl'

/-! ## One query, its bits read -/

/-- The padding run a query emits: `1, 0, 0, 0, 0`. -/
theorem oqPad_values {pr : ℕ} (hA : ∀ a, Stmt.atom a ∈ oqPadT pr → a.Holds rd σ) :
    σ (.n pr) = word 1 0 0 ∧ ∀ i < 4, σ (.n (pr + 1 + i)) = 0 := by
  refine ⟨hA _ (by simp [oqPadT] : Stmt.atom (.const (.n pr) (word 1 0 0)) ∈ _), fun i hi => ?_⟩
  interval_cases i
  · exact (hA _ (by simp [oqPadT] : Stmt.atom (.const (.n (pr + 1)) (word 0 0 0)) ∈ _)).trans word_zero
  · exact (hA _ (by simp [oqPadT] : Stmt.atom (.const (.n (pr + 2)) (word 0 0 0)) ∈ _)).trans word_zero
  · exact (hA _ (by simp [oqPadT] : Stmt.atom (.const (.n (pr + 3)) (word 0 0 0)) ∈ _)).trans word_zero
  · exact (hA _ (by simp [oqPadT] : Stmt.atom (.const (.n (pr + 4)) (word 0 0 0)) ∈ _)).trans word_zero

/-- **A query whose bit pointer points to bits** opens at the position the bits spell. -/
theorem oqQuery_sound_bits {s : Oq} (hs : s.RowShape) (hcd : 2 ≤ s.cd) (hcd8 : s.cd ≤ 8)
    {bp cap flags wp : V} {b : ℕ} {emit : Bool} {pr : ℕ}
    (hA : ∀ a, Stmt.atom a ∈ oqQueryT s bp cap flags wp b emit pr → a.Holds rd σ)
    (hpad : σ (.n (oqPr s b emit pr)) = word 1 0 0)
    (hz : ∀ i < 4, σ (.n (oqPr s b emit pr + 1 + i)) = 0)
    (hbool : ∀ l < s.pd + s.cd, ∀ w, LoadHolds rd (σ bp) l w → w = 0 ∨ w = 1) :
    ∃ q < 2 ^ (s.pd + s.cd), (∀ l < s.pd + s.cd, LoadHolds rd (σ bp) l (bitE (q.testBit l))) ∧
      QueryOpens rd s.base s.I (s.pd + s.cd) s.cd (σ cap) (σ flags) (σ wp) q (oqRow b s.R σ)
        (σ (.n (oqDot s b))) := by
  obtain ⟨q, hq, hbits⟩ := bits_q (oqQuery_bitLoads hcd hA) hbool
  exact ⟨q, hq, hbits, oqQuery_sound hs hcd hcd8 hA hpad hz hq hbits⟩

/-! ## The level-0 iteration -/

theorem oqLoop1A_mem_q1 {s : Oq} {odd : ℕ} {a : Atom}
    (h : Stmt.atom a ∈ oqQueryT s (.n 10) (.n 3) (.n 4) (.n 5) 11 true 0) :
    Stmt.atom a ∈ oqLoop1A s odd := by
  simp only [oqLoop1A, List.mem_append]; simp_all

theorem oqLoop1A_mem_q2 {s : Oq} {odd : ℕ} {a : Atom}
    (h : Stmt.atom a ∈ oqQueryT s (.n (oqE1 s)) (.n 3) (.n 4) (.n 5) (oqE1 s + 1) false
      (oqK1 11 s.R + s.D)) :
    Stmt.atom a ∈ oqLoop1A s odd := by
  simp only [oqLoop1A, List.mem_append]; simp_all

/-- **A level-0 iteration** at `x = g^i` (G:1260-1264): its two queries open at the positions the
bit pointers `qptrs[2i + odd]`, `qptrs[2i + odd + 1]` spell, and the chain steps by their
values. -/
theorem oqIter1_sound {s : Oq} (hs : s.RowShape) (hcd : 2 ≤ s.cd) (hcd8 : s.cd ≤ 8) {odd i : ℕ}
    (hA : ∀ a, Stmt.atom a ∈ oqLoop1A s odd → a.Holds rd σ) (hx : σ (.n 0) = gen ^ i)
    (hbool : ∀ k, k = 2 * i + odd ∨ k = 2 * i + odd + 1 → ∀ bp, LoadHolds rd (σ (.n 2)) k bp →
      ∀ l < s.pd + s.cd, ∀ w, LoadHolds rd bp l w → w = 0 ∨ w = 1) :
    ∃ (bp1 bp2 : E) (q1 q2 : ℕ) (r1 r2 : List K) (d0 d1 v : E),
      LoadHolds rd (σ (.n 2)) (2 * i + odd) bp1 ∧ q1 < 2 ^ (s.pd + s.cd) ∧
      (∀ l < s.pd + s.cd, LoadHolds rd bp1 l (bitE (q1.testBit l))) ∧
      QueryOpens rd s.base s.I (s.pd + s.cd) s.cd (σ (.n 3)) (σ (.n 4)) (σ (.n 5)) q1 r1 d0 ∧
      LoadHolds rd (σ (.n 2)) (2 * i + odd + 1) bp2 ∧ q2 < 2 ^ (s.pd + s.cd) ∧
      (∀ l < s.pd + s.cd, LoadHolds rd bp2 l (bitE (q2.testBit l))) ∧
      QueryOpens rd s.base s.I (s.pd + s.cd) s.cd (σ (.n 3)) (σ (.n 4)) (σ (.n 5)) q2 r2 d1 ∧
      LoadHolds rd (σ (.n 6)) i v ∧
      LoadHolds rd (σ (.n 6)) (i + 1) (((v + d0) * σ (.n 7) + d1) * σ (.n 7)) := by
  have p8 := hA _ (by simp [oqLoop1A] : Stmt.atom (.mul (.n 8) (.n 2) (.n 0)) ∈ _)
  have p9 := hA _ (by simp [oqLoop1A] : Stmt.atom (.mul (.n 9) (.n 8) (.n 0)) ∈ _)
  have p10 := hA _ (by simp [oqLoop1A] : Stmt.atom (.load (.n 10) (.n 9) odd) ∈ _)
  have pe1 := hA _ (by simp [oqLoop1A] : Stmt.atom (.load (.n (oqE1 s)) (.n 9) (odd + 1)) ∈ _)
  simp only [Atom.Holds] at p8 p9 p10 pe1
  have h9 : σ (.n 9) = σ (.n 2) * gen ^ (2 * i) := by rw [p9, p8, hx, mul_assoc, ← pow_add]; ring_nf
  rw [h9, loadHolds_mul_gen_pow] at p10 pe1
  -- the queries
  have hq1 := fun a h => hA a (oqLoop1A_mem_q1 (odd := odd) h)
  have hq2 := fun a h => hA a (oqLoop1A_mem_q2 (odd := odd) h)
  obtain ⟨-, -, hpd, -, -, -⟩ := oqQuery_pieces hq1
  obtain ⟨e1, z⟩ := oqPad_values (hpd rfl)
  obtain ⟨q1, hq1lt, hb1, ho1⟩ := oqQuery_sound_bits hs hcd hcd8 hq1 e1 z
    (hbool _ (Or.inl rfl) _ p10)
  obtain ⟨q2, hq2lt, hb2, ho2⟩ := oqQuery_sound_bits hs hcd hcd8 hq2 e1 z
    (hbool (2 * i + odd + 1) (Or.inr rfl) _
      (by rw [show 2 * i + odd + 1 = 2 * i + (odd + 1) by omega]; exact pe1))
  -- the chain
  set c := oqC1 s with hc
  have c0 := hA _ (by simp [oqLoop1A, ← hc] : Stmt.atom (.mul (.n c) (.n 6) (.n 0)) ∈ _)
  have c1 := hA _ (by simp [oqLoop1A, ← hc] : Stmt.atom (.load (.n (c + 1)) (.n c) 0) ∈ _)
  have c2 := hA _ (by simp [oqLoop1A, ← hc] :
    Stmt.atom (.add (.n (c + 2)) (.n (c + 1)) (.n (oqDot s 11))) ∈ _)
  have c3 := hA _ (by simp [oqLoop1A, ← hc] : Stmt.atom (.mul (.n (c + 3)) (.n (c + 2)) (.n 7)) ∈ _)
  have c4 := hA _ (by simp [oqLoop1A, ← hc] :
    Stmt.atom (.add (.n (c + 4)) (.n (c + 3)) (.n (oqDot s (oqE1 s + 1)))) ∈ _)
  have c5 := hA _ (by simp [oqLoop1A, ← hc] : Stmt.atom (.mul (.n (c + 5)) (.n (c + 4)) (.n 7)) ∈ _)
  have c6 := hA _ (by simp [oqLoop1A, ← hc] : Stmt.atom (.mul (.n (c + 6)) (.n 6) (.n 0)) ∈ _)
  have c7 := hA _ (by simp [oqLoop1A, ← hc] : Stmt.atom (.load (.n (c + 5)) (.n (c + 6)) 1) ∈ _)
  simp only [Atom.Holds] at c0 c1 c2 c3 c4 c5 c6 c7
  rw [c0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at c1
  rw [c6, hx, loadHolds_mul_gen_pow, c5, c4, c3, c2] at c7
  exact ⟨_, _, q1, q2, _, _, _, _, _, p10, hq1lt, hb1, ho1,
    by rw [show 2 * i + odd + 1 = 2 * i + (odd + 1) by omega]; exact pe1, hq2lt, hb2, ho2, c1, c7⟩

/-! ## The deeper iteration -/

theorem oqLoop0A_mem_q {s : Oq} {a : Atom}
    (h : Stmt.atom a ∈ oqQueryT s (.n 9) (.n 3) (.n 4) (.n 5) 10 true 0) :
    Stmt.atom a ∈ oqLoop0A s := by
  simp only [oqLoop0A, List.mem_append]; simp_all

/-- **A deeper iteration** at `x = g^i` (G:1265-1267): its query opens at the position the bit
pointer `qptrs[i]` spells, and the chain steps by its value. -/
theorem oqIter0_sound {s : Oq} (hs : s.RowShape) (hcd : 2 ≤ s.cd) (hcd8 : s.cd ≤ 8) {i : ℕ}
    (hA : ∀ a, Stmt.atom a ∈ oqLoop0A s → a.Holds rd σ) (hx : σ (.n 0) = gen ^ i)
    (hbool : ∀ bp, LoadHolds rd (σ (.n 2)) i bp →
      ∀ l < s.pd + s.cd, ∀ w, LoadHolds rd bp l w → w = 0 ∨ w = 1) :
    ∃ (bp : E) (q : ℕ) (r : List K) (d v : E),
      LoadHolds rd (σ (.n 2)) i bp ∧ q < 2 ^ (s.pd + s.cd) ∧
      (∀ l < s.pd + s.cd, LoadHolds rd bp l (bitE (q.testBit l))) ∧
      QueryOpens rd s.base s.I (s.pd + s.cd) s.cd (σ (.n 3)) (σ (.n 4)) (σ (.n 5)) q r d ∧
      LoadHolds rd (σ (.n 6)) i v ∧ LoadHolds rd (σ (.n 6)) (i + 1) ((v + d) * σ (.n 7)) := by
  have p8 := hA _ (by simp [oqLoop0A] : Stmt.atom (.mul (.n 8) (.n 2) (.n 0)) ∈ _)
  have p9 := hA _ (by simp [oqLoop0A] : Stmt.atom (.load (.n 9) (.n 8) 0) ∈ _)
  simp only [Atom.Holds] at p8 p9
  rw [p8, hx, loadHolds_mul_gen_pow, Nat.add_zero] at p9
  have hq := fun a h => hA a (oqLoop0A_mem_q h)
  obtain ⟨-, -, hpd, -, -, -⟩ := oqQuery_pieces hq
  obtain ⟨e1, z⟩ := oqPad_values (hpd rfl)
  obtain ⟨q, hqlt, hb, ho⟩ := oqQuery_sound_bits hs hcd hcd8 hq e1 z (hbool _ p9)
  set c := oqC0 s with hc
  have c0 := hA _ (by simp [oqLoop0A, ← hc] : Stmt.atom (.mul (.n c) (.n 6) (.n 0)) ∈ _)
  have c1 := hA _ (by simp [oqLoop0A, ← hc] : Stmt.atom (.load (.n (c + 1)) (.n c) 0) ∈ _)
  have c2 := hA _ (by simp [oqLoop0A, ← hc] :
    Stmt.atom (.add (.n (c + 2)) (.n (c + 1)) (.n (oqDot s 10))) ∈ _)
  have c3 := hA _ (by simp [oqLoop0A, ← hc] : Stmt.atom (.mul (.n (c + 3)) (.n (c + 2)) (.n 7)) ∈ _)
  have c4 := hA _ (by simp [oqLoop0A, ← hc] : Stmt.atom (.mul (.n (c + 4)) (.n 6) (.n 0)) ∈ _)
  have c5 := hA _ (by simp [oqLoop0A, ← hc] : Stmt.atom (.load (.n (c + 3)) (.n (c + 4)) 1) ∈ _)
  simp only [Atom.Holds] at c0 c1 c2 c3 c4 c5
  rw [c0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at c1
  rw [c4, hx, loadHolds_mul_gen_pow, c3, c2] at c5
  exact ⟨_, q, _, _, _, p9, hqlt, hb, ho, c1, c5⟩

end
end LeanVM.Guest.B1
