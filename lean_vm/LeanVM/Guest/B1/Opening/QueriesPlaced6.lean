/-
  LeanVM.Guest.B1.Opening.QueriesPlaced6

  `opening_queries`' loop, placed: its iterations one frame after another.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlaced5

/-!
# The loop, placed

`oqLoop1_relAtIn`, `oqLoop0_relAtIn`: the loop helper called at `g^j` with the bound `g^N`, placed
at `fp + j·fs loop`, its iteration `j'` at `fp + j'·fs loop` (a loop helper's tail call comes
first, right after its frame), is `RelAtIn` the caller's region `R`, of `(N - j + 1)·fs loop`
words, when every iteration's data holds (`OqIt1Ok`, `OqIt0Ok`: its queries' `QD.Ok` with the
frame addresses its placement gives, its bit pointers and bits, the chain, its region).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **What a level-0 iteration at `g^j`, placed at `fp`, needs**: its two queries honest with the
frame addresses its placement gives, their bit pointers and bits, the chain's step, and where it
reads the caller's words. -/
structure OqIt1Ok (rd : Reader) (R : ℕ → Prop) (cert : String → V → ℕ) (loop : String) (s : Oq)
    (odd fp j : ℕ) (qptrs cap flags wp ch mu : E) (r1 r2 : List K) (w1 w2 : ℕ → E) (q1 q2 : ℕ)
    (sb1 sb2 : List Digest) (bp1 bp2 v : E) : Prop where
  ok1 : (⟨s, 11, true, 0, r1, w1, q1, sb1,
    ofK (Parameters.gpow (fp + cert loop (.n (oqCh s 11 true)))), cap, flags, rd⟩ : QD).Ok rd wp
  ok2 : (⟨s, oqE1 s + 1, false, oqK1 11 s.R + s.D, r2, w2, q2, sb2,
    ofK (Parameters.gpow (fp + cert loop (.n (oqCh s (oqE1 s + 1) false)))), cap, flags, rd⟩ :
      QD).Ok rd wp
  b1 : LoadHolds rd qptrs (2 * j + odd) bp1
  bits1 : ∀ l < s.pd + s.cd, LoadHolds rd bp1 l (bitE (q1.testBit l))
  b2 : LoadHolds rd qptrs (2 * j + odd + 1) bp2
  bits2 : ∀ l < s.pd + s.cd, LoadHolds rd bp2 l (bitE (q2.testBit l))
  chv : LoadHolds rd ch j v
  chv1 : LoadHolds rd ch (j + 1) (((v + rowDot s.base s.I r1 w1) * mu + rowDot s.base s.I r2 w2) * mu)
  rq : ∀ e < 2, OqIn R ((qptrs * gen ^ j * gen ^ j).limb 0 * Parameters.gpow (odd + e))
  reg1 : OqQReg R s cap flags wp bp1 q1
  reg2 : OqQReg R s cap flags wp bp2 q2
  rc : ∀ e < 2, OqIn R ((ch * gen ^ j).limb 0 * Parameters.gpow e)

/-- **What a deeper iteration at `g^j`, placed at `fp`, needs.** -/
structure OqIt0Ok (rd : Reader) (R : ℕ → Prop) (cert : String → V → ℕ) (loop : String) (s : Oq)
    (fp j : ℕ) (qptrs cap flags wp ch mu : E) (r : List K) (w : ℕ → E) (q : ℕ)
    (sb : List Digest) (bp v : E) : Prop where
  ok : (⟨s, 10, true, 0, r, w, q, sb,
    ofK (Parameters.gpow (fp + cert loop (.n (oqCh s 10 true)))), cap, flags, rd⟩ : QD).Ok rd wp
  b : LoadHolds rd qptrs j bp
  bits : ∀ l < s.pd + s.cd, LoadHolds rd bp l (bitE (q.testBit l))
  chv : LoadHolds rd ch j v
  chv1 : LoadHolds rd ch (j + 1) ((v + rowDot s.base s.I r w) * mu)
  rq : OqIn R ((qptrs * gen ^ j).limb 0 * Parameters.gpow 0)
  reg : OqQReg R s cap flags wp bp q
  rc : ∀ e < 2, OqIn R ((ch * gen ^ j).limb 0 * Parameters.gpow e)

theorem gen_pow_guard {j N : ℕ} (hN : N < ordG) (hj : j + 1 ≤ N) :
    IsInK (gen ^ j * gen + gen ^ N) ∧ (gen ^ j * gen + gen ^ N ≠ 0 ↔ j + 1 < N) := by
  rw [← pow_succ]
  refine ⟨isInK_add (by rw [gen_pow_eq_ofK]; exact ofK_isInK _)
    (by rw [gen_pow_eq_ofK]; exact ofK_isInK _), ⟨fun h ↦ ?_, fun h he ↦ ?_⟩⟩
  · rcases Nat.lt_or_ge (j + 1) N with h' | h'
    · exact h'
    · exact absurd (by rw [show j + 1 = N by omega]; exact e_add_self _) h
  · have := gen_pow_inj (lt_of_lt_of_le (by omega) (le_of_lt hN)) hN (e_add_eq_zero_iff.mp he)
    omega

/-- **The level-0 loop, placed.** -/
theorem oqLoop1_relAtIn (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hpd : 4 * s.pd ≤ 80) (hpd1 : 1 ≤ s.pd) (hcd : 2 ≤ s.cd)
    (hcd8 : s.cd ≤ 8) {odd : ℕ} {loop : String} {fl : Fn}
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T s odd loop) (hlp : coreProgram.loop loop = true)
    {rd : Reader} {R : ℕ → Prop} {fp N : ℕ} (hN : N < ordG) {qptrs cap flags wp ch mu : E}
    {r1 r2 : ℕ → List K} {w1 w2 : ℕ → ℕ → E} {q1 q2 : ℕ → ℕ} {sb1 sb2 : ℕ → List Digest}
    {bp1 bp2 v : ℕ → E}
    (hit : ∀ j < N, OqIt1Ok rd R cert loop s odd (fp + j * fs loop) j qptrs cap flags wp ch mu
      (r1 j) (r2 j) (w1 j) (w2 j) (q1 j) (q2 j) (sb1 j) (sb2 j) (bp1 j) (bp2 j) (v j)) :
    ∀ j < N, RelAtIn coreProgram fs cert rd R (fun _ => False) (fp + j * fs loop)
      ((N - j + 1) * fs loop) loop [gen ^ j, gen ^ N, qptrs, cap, flags, wp, ch, mu] [] := by
  suffices h : ∀ n j, j + n + 1 = N → RelAtIn coreProgram fs cert rd R (fun _ => False)
      (fp + j * fs loop) ((N - j + 1) * fs loop) loop [gen ^ j, gen ^ N, qptrs, cap, flags, wp, ch, mu]
      [] from fun j hj ↦ h (N - j - 1) j (by omega)
  intro n
  induction n with
  | zero =>
    intro j hj
    have H := hit j (by omega)
    obtain ⟨hK, hne⟩ := gen_pow_guard (j := j) hN (by omega)
    have := oqIter1_relAtIn (m := fs loop) hP fs cert hs hpd hpd1 hcd hcd8 hfl hpl hbl hlp
      H.ok1 H.ok2 H.b1 H.bits1 H.b2 H.bits2 H.chv H.chv1 hK
      (by
        split
        · next h => exact absurd (hne.mp h) (by omega)
        · rfl) H.rq H.reg1 H.reg2 H.rc
    rw [show (N - j + 1) * fs loop = fs loop + fs loop by
      rw [show N - j = 1 by omega]; ring]
    exact this
  | succ n ih =>
    intro j hj
    have H := hit j (by omega)
    obtain ⟨hK, hne⟩ := gen_pow_guard (j := j) hN (by omega)
    have ht := ih (j + 1) (by omega)
    rw [show fp + (j + 1) * fs loop = fp + j * fs loop + fs loop by ring, pow_succ] at ht
    have := oqIter1_relAtIn (m := (N - (j + 1) + 1) * fs loop) hP fs cert hs hpd hpd1 hcd hcd8 hfl
      hpl hbl hlp H.ok1 H.ok2 H.b1 H.bits1 H.b2 H.bits2 H.chv H.chv1 hK
      (by
        split
        · exact ht
        · next h => exact absurd (hne.mpr (by omega)) h) H.rq H.reg1 H.reg2 H.rc
    rw [show (N - j + 1) * fs loop = fs loop + (N - (j + 1) + 1) * fs loop by
      rw [show N - j = N - (j + 1) + 1 by omega]; ring]
    exact this

/-- **The deeper loop, placed.** -/
theorem oqLoop0_relAtIn (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hpd : 4 * s.pd ≤ 80) (hpd1 : 1 ≤ s.pd) (hcd : 2 ≤ s.cd)
    (hcd8 : s.cd ≤ 8) {loop : String} {fl : Fn}
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop0T s loop) (hlp : coreProgram.loop loop = true)
    {rd : Reader} {R : ℕ → Prop} {fp N : ℕ} (hN : N < ordG) {qptrs cap flags wp ch mu : E}
    {r : ℕ → List K} {w : ℕ → ℕ → E} {q : ℕ → ℕ} {sb : ℕ → List Digest} {bp v : ℕ → E}
    (hit : ∀ j < N, OqIt0Ok rd R cert loop s (fp + j * fs loop) j qptrs cap flags wp ch mu
      (r j) (w j) (q j) (sb j) (bp j) (v j)) :
    ∀ j < N, RelAtIn coreProgram fs cert rd R (fun _ => False) (fp + j * fs loop)
      ((N - j + 1) * fs loop) loop [gen ^ j, gen ^ N, qptrs, cap, flags, wp, ch, mu] [] := by
  suffices h : ∀ n j, j + n + 1 = N → RelAtIn coreProgram fs cert rd R (fun _ => False)
      (fp + j * fs loop) ((N - j + 1) * fs loop) loop [gen ^ j, gen ^ N, qptrs, cap, flags, wp, ch, mu]
      [] from fun j hj ↦ h (N - j - 1) j (by omega)
  intro n
  induction n with
  | zero =>
    intro j hj
    have H := hit j (by omega)
    obtain ⟨hK, hne⟩ := gen_pow_guard (j := j) hN (by omega)
    have := oqIter0_relAtIn (m := fs loop) hP fs cert hs hpd hpd1 hcd hcd8 hfl hpl hbl hlp
      H.ok H.b H.bits H.chv H.chv1 hK (by
        split
        · next h => exact absurd (hne.mp h) (by omega)
        · rfl) H.rq H.reg H.rc
    rw [show (N - j + 1) * fs loop = fs loop + fs loop by
      rw [show N - j = 1 by omega]; ring]
    exact this
  | succ n ih =>
    intro j hj
    have H := hit j (by omega)
    obtain ⟨hK, hne⟩ := gen_pow_guard (j := j) hN (by omega)
    have ht := ih (j + 1) (by omega)
    rw [show fp + (j + 1) * fs loop = fp + j * fs loop + fs loop by ring, pow_succ] at ht
    have := oqIter0_relAtIn (m := (N - (j + 1) + 1) * fs loop) hP fs cert hs hpd hpd1 hcd hcd8 hfl
      hpl hbl hlp H.ok H.b H.bits H.chv H.chv1 hK
      (by
        split
        · exact ht
        · next h => exact absurd (hne.mpr (by omega)) h) H.rq H.reg H.rc
    rw [show (N - j + 1) * fs loop = fs loop + (N - (j + 1) + 1) * fs loop by
      rw [show N - j = N - (j + 1) + 1 by omega]; ring]
    exact this

end
end LeanVM.Guest.B1
