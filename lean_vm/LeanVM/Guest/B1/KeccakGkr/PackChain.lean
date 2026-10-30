/-
  LeanVM.Guest.B1.KeccakGkr.PackChain

  The pack rounds of a layer as the guest runs them: the loop's iterations, two rounds each,
  then with an odd count one `keccak_round`, are `packRunF` on the carried sponge.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.PackLoop
public import LeanVM.Guest.B1.KeccakGkr.Round
public import LeanVM.Guest.B1.KeccakGkr.LayerSpec

/-!
# The pack rounds (`keccak_layer`, G:2626-2668)

`keccak_layer` writes the record `rounds` (the capacity after the squeeze, the cursor past the
product, the product's value at `s`, the scale `1`), runs `__loop{30..33}` for `x2 = g^j`,
`j < ⌊y/2⌋` (`PackStep`: two rounds on the coordinates `2j`, `2j + 1`), with `y` odd one
`keccak_round` on the coordinate `y - 1`, and reads the record `rounds·g^(⌊y/2⌋ + odd)`.

* `packRunF_eqRound`: a round of `packRunF` is `eqRound`;
* `pack_chain`: the records chain into `packRunF` of the claim's point, the messages read from
  the cursor and the challenges stored at `point`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-- **A round of `packRunF` is `eqRound`** (`keccak_round`'s formulas). -/
theorem packRunF_eqRound (r g1 g2 v sc : E) (rs : List E) (ms : List (E × E)) (s : Fs) :
    packRunF (r :: rs) ((g1, g2) :: ms) v sc s =
      (((packRunF rs ms (eqRound s g1 g2 r v sc).2.1 (eqRound s g1 g2 r v sc).2.2.1
          (eqRound s g1 g2 r v sc).2.2.2).1.1,
        (packRunF rs ms (eqRound s g1 g2 r v sc).2.1 (eqRound s g1 g2 r v sc).2.2.1
          (eqRound s g1 g2 r v sc).2.2.2).1.2.1,
        (eqRound s g1 g2 r v sc).1 :: (packRunF rs ms (eqRound s g1 g2 r v sc).2.1
          (eqRound s g1 g2 r v sc).2.2.1 (eqRound s g1 g2 r v sc).2.2.2).1.2.2),
        (packRunF rs ms (eqRound s g1 g2 r v sc).2.1 (eqRound s g1 g2 r v sc).2.2.1
          (eqRound s g1 g2 r v sc).2.2.2).2) := by
  have e : (1 + r + (s.absorbAll [g1, g2] dsObserve).squeeze.1) *
      polyEval [v + r * sumE [g1, g2], g1, g2] (s.absorbAll [g1, g2] dsObserve).squeeze.1 =
      (eqRound s g1 g2 r v sc).2.1 := by
    simp only [eqRound, polyEval, sumE, List.foldl, List.foldr]
    ring
  have e' : sc * (1 + r + (s.absorbAll [g1, g2] dsObserve).squeeze.1) =
      (eqRound s g1 g2 r v sc).2.2.1 := by
    simp only [eqRound]
    ring
  simp only [packRunF]
  rw [e, e']
  rfl

/-- `packRunF` past its last round. -/
theorem packRunF_nil (v sc : E) (s : Fs) : packRunF [] [] v sc s = ((v, sc, []), s) := rfl

theorem loadHolds_rec_succ {rec : E} {j off : ℕ} {w : E} :
    LoadHolds rd (rec * gen ^ j) (1 + off) w ↔ LoadHolds rd (rec * gen ^ (j + 1)) off w := by
  rw [loadHolds_mul_gen_pow, loadHolds_mul_gen_pow, show j + (1 + off) = j + 1 + off by omega]

/-- `packRunF` over a prefix of rounds, then the rest. -/
theorem packRunF_append :
    ∀ (A rest : List E) (MA restM : List (E × E)) (v sc : E) (s : Fs), MA.length = A.length →
      packRunF (A ++ rest) (MA ++ restM) v sc s =
        (((packRunF rest restM (packRunF A MA v sc s).1.1 (packRunF A MA v sc s).1.2.1
            (packRunF A MA v sc s).2).1.1,
          (packRunF rest restM (packRunF A MA v sc s).1.1 (packRunF A MA v sc s).1.2.1
            (packRunF A MA v sc s).2).1.2.1,
          (packRunF A MA v sc s).1.2.2 ++ (packRunF rest restM (packRunF A MA v sc s).1.1
            (packRunF A MA v sc s).1.2.1 (packRunF A MA v sc s).2).1.2.2),
          (packRunF rest restM (packRunF A MA v sc s).1.1 (packRunF A MA v sc s).1.2.1
            (packRunF A MA v sc s).2).2)
  | [], rest, [], restM, v, sc, s, _ => by simp [packRunF_nil]
  | r :: A, rest, (g1, g2) :: MA, restM, v, sc, s, h => by
    have h' : MA.length = A.length := by simpa using h
    rw [List.cons_append, List.cons_append, packRunF_eqRound, packRunF_eqRound,
      packRunF_append A rest MA restM _ _ _ h']
    simp only [List.cons_append]
  | [], _, _ :: _, _, _, _, _, h | _ :: _, _, [], _, _, _, _, h => by simp at h

theorem capAt_unique {rec : E} {k : ℕ} {cap cap' : List E} (h : CapAt rd rec k krCap cap)
    (h' : CapAt rd rec k krCap cap') : cap = cap' := by
  apply List.ext_getElem (by rw [h.1, h'.1])
  intro j hj hj'
  exact loadHolds_unique (h.2 j hj) (h'.2 j hj')

theorem roundRec_unique {rec : E} {k : ℕ} {cap cap' : List E} {cur cur' cl cl' sc sc' : E}
    (h : RoundRec rd rec k cap cur cl sc) (h' : RoundRec rd rec k cap' cur' cl' sc') :
    cap = cap' ∧ cur = cur' ∧ cl = cl' ∧ sc = sc' :=
  ⟨capAt_unique h.1 h'.1, loadHolds_unique h.2.1 h'.2.1, loadHolds_unique h.2.2.1 h'.2.2.1,
    loadHolds_unique h.2.2.2 h'.2.2.2⟩

/-- A record written at offset `1` from `rec·g^j` is the record at `rec·g^(j+1)`. -/
theorem roundRec_succ {rec : E} {j : ℕ} {cap : List E} {cur cl sc : E}
    (h : RoundRec rd (rec * gen ^ j) 1 cap cur cl sc) :
    RoundRec rd (rec * gen ^ (j + 1)) 0 cap cur cl sc := by
  obtain ⟨⟨hl, hc⟩, h1, h2, h3⟩ := h
  refine ⟨⟨hl, fun i hi => ?_⟩, ?_, ?_, ?_⟩
  · have := hc i hi
    rw [show 1 + i * krCap = 1 + (0 + i * krCap) by omega, loadHolds_rec_succ] at this
    exact this
  · rw [show 0 + 5 * krCap = 5 * krCap by omega, ← loadHolds_rec_succ]; exact h1
  · rw [show 0 + 6 * krCap = 6 * krCap by omega, ← loadHolds_rec_succ]; exact h2
  · rw [show 0 + 7 * krCap = 7 * krCap by omega, ← loadHolds_rec_succ]; exact h3

theorem eqRound_pend (s : Fs) (g1 g2 r v sc : E) : (eqRound s g1 g2 r v sc).2.2.2 =
    ⟨(eqRound s g1 g2 r v sc).2.2.2.cap, []⟩ := rfl

/-- The four loop helpers: found, the loop body, five parameters. -/
theorem packLoop_fn {first odd : ℕ} (hf : first < 2) (ho : odd < 2) :
    ∃ fn : Fn, coreProgram.find? (packLoopName first odd) = some fn ∧
      fn.body = packLoopT (packLoopName first odd) ∧ fn.params = [V.n 0, .n 1, .n 2, .n 3, .n 4] := by
  interval_cases first <;> interval_cases odd
  · exact ⟨_, find_packLoop32, packLoop_body32, rfl⟩
  · exact ⟨_, find_packLoop33, packLoop_body33, rfl⟩
  · exact ⟨_, find_packLoop30, packLoop_body30, rfl⟩
  · exact ⟨_, find_packLoop31, packLoop_body31, rfl⟩

theorem gen_pow_ne_one {h : ℕ} (h0 : 0 < h) (hlt : h < ordG) : 1 + gen ^ h ≠ 0 := by
  intro e
  have : gen ^ h = gen ^ 0 := by rw [pow_zero]; exact (e_add_eq_zero_iff.mp e).symm
  have := gen_pow_inj (by unfold ordG at hlt; omega) (by decide) this
  omega

/-- The invariant after `j` iterations: the messages and challenges so far, the record `j`, and
`packRunF` of the first `2j` coordinates. -/
def PackInv (rd : Reader) (rec pt cur hv : E) (capS pts : List E) (j : ℕ) : Prop :=
  ∃ (msgs : List (E × E)) (chs cap : List E) (cl sc : E), msgs.length = 2 * j ∧
    chs.length = 2 * j ∧ ReadsAt rd cur (msgs.flatMap fun m ↦ [m.1, m.2]) ∧ ReadsAt rd pt chs ∧
    RoundRec rd (rec * gen ^ j) 0 cap (cur * gen ^ (4 * j)) cl sc ∧ AllCanonical cap ∧
    (packRunF (pts.take (2 * j)) msgs hv 1 ⟨capS, []⟩).1 = (cl, sc, chs) ∧
    (packRunF (pts.take (2 * j)) msgs hv 1 ⟨capS, []⟩).2 = ⟨cap, []⟩

theorem flatMap_pairs_length (msgs : List (E × E)) :
    (msgs.flatMap fun m ↦ [m.1, m.2]).length = 2 * msgs.length := by
  induction msgs with
  | nil => rfl
  | cons m ms ih => simp [List.flatMap_cons, ih]; ring

theorem packInv_zero {rec pt cur hv : E} {capS pts : List E} (h0 : RoundRec rd rec 0 capS cur hv 1)
    (hcan : AllCanonical capS) : PackInv rd rec pt cur hv capS pts 0 :=
  ⟨[], [], capS, hv, 1, rfl, rfl, readsAt_nil _ _, readsAt_nil _ _, by simpa using h0, hcan, rfl,
    rfl⟩

theorem gen_sq (j : ℕ) : (gen ^ j) ^ 2 = gen ^ (2 * j) := by rw [← pow_mul, mul_comm]

theorem take_two_more (pts : List E) {j : ℕ} (hj : 2 * j + 2 ≤ pts.length) :
    pts.take (2 * (j + 1)) = pts.take (2 * j) ++
      [pts[2 * j]'(by omega), pts[2 * j + 1]'(by omega)] := by
  rw [show 2 * (j + 1) = 2 * j + 2 by ring, List.take_add]
  congr 1
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.length_cons, List.length_nil] at h2
  interval_cases i <;> simp [List.getElem_take, List.getElem_drop]

/-- Two rounds of `packRunF`. -/
theorem packRunF_pair (r0 r1 g1 g2 g1' g2' v sc : E) (s : Fs) :
    packRunF [r0, r1] [(g1, g2), (g1', g2')] v sc s =
      (((eqRound (eqRound s g1 g2 r0 v sc).2.2.2 g1' g2' r1 (eqRound s g1 g2 r0 v sc).2.1
          (eqRound s g1 g2 r0 v sc).2.2.1).2.1,
        (eqRound (eqRound s g1 g2 r0 v sc).2.2.2 g1' g2' r1 (eqRound s g1 g2 r0 v sc).2.1
          (eqRound s g1 g2 r0 v sc).2.2.1).2.2.1,
        [(eqRound s g1 g2 r0 v sc).1, (eqRound (eqRound s g1 g2 r0 v sc).2.2.2 g1' g2' r1
          (eqRound s g1 g2 r0 v sc).2.1 (eqRound s g1 g2 r0 v sc).2.2.1).1]),
        (eqRound (eqRound s g1 g2 r0 v sc).2.2.2 g1' g2' r1 (eqRound s g1 g2 r0 v sc).2.1
          (eqRound s g1 g2 r0 v sc).2.2.1).2.2.2) := by
  rw [packRunF_eqRound, packRunF_eqRound, packRunF_nil]

/-- Two more rounds after a prefix. -/
theorem packRunF_two (A : List E) (MA : List (E × E)) (v sc : E) (s : Fs) {cl sc' : E}
    {chs cap : List E} (r0 r1 g1 g2 g1' g2' : E) (hA : MA.length = A.length)
    (hrun : (packRunF A MA v sc s).1 = (cl, sc', chs))
    (hcap : (packRunF A MA v sc s).2 = ⟨cap, []⟩) :
    (packRunF (A ++ [r0, r1]) (MA ++ [(g1, g2), (g1', g2')]) v sc s).1 =
        ((packRunF [r0, r1] [(g1, g2), (g1', g2')] cl sc' ⟨cap, []⟩).1.1,
          (packRunF [r0, r1] [(g1, g2), (g1', g2')] cl sc' ⟨cap, []⟩).1.2.1,
          chs ++ (packRunF [r0, r1] [(g1, g2), (g1', g2')] cl sc' ⟨cap, []⟩).1.2.2) ∧
      (packRunF (A ++ [r0, r1]) (MA ++ [(g1, g2), (g1', g2')]) v sc s).2 =
        (packRunF [r0, r1] [(g1, g2), (g1', g2')] cl sc' ⟨cap, []⟩).2 := by
  rw [packRunF_append _ _ _ _ _ _ _ hA, hrun, hcap]
  exact ⟨rfl, rfl⟩

/-- **An iteration extends the invariant.** -/
theorem packInv_succ {rec pp pt cur hv : E} {capS pts : List E} {j : ℕ}
    (hI : PackInv rd rec pt cur hv capS pts j) (hS : PackStep rd rec pp pt (gen ^ j))
    (hpp : ReadsAt rd pp pts) (hj : 2 * j + 2 ≤ pts.length) :
    PackInv rd rec pt cur hv capS pts (j + 1) := by
  obtain ⟨msgs, chs, cap, cl, sc, hml, hcl, hrm, hrc, hrec, -, hrun, hrcap⟩ := hI
  obtain ⟨cap', cur', cl', sc', r0, r1, g1, g2, g1', g2', hrec', hcan', hr0, hr1, hmsg, hS'⟩ := hS
  obtain ⟨rfl, hcur, rfl, rfl⟩ := roundRec_unique hrec hrec'
  obtain ⟨hst0, hst1, hnext⟩ := hS'
  rw [gen_sq, loadHolds_mul_gen_pow, Nat.add_zero] at hr0
  rw [gen_sq, loadHolds_mul_gen_pow] at hr1
  have e0 : pts[2 * j]'(by omega) = r0 := loadHolds_unique (hpp _ (by omega)) hr0
  have e1 : pts[2 * j + 1]'(by omega) = r1 := loadHolds_unique (hpp _ (by omega)) hr1
  rw [gen_sq] at hst0 hst1
  have h2 := packRunF_two _ _ _ _ _ r0 r1 g1 g2 g1' g2' (by simp [hml]; omega) hrun hrcap
  rw [packRunF_pair] at h2
  refine ⟨msgs ++ [(g1, g2), (g1', g2')], chs ++ [(eqRound ⟨cap, []⟩ g1 g2 r0 cl sc).1,
    (eqRound (eqRound ⟨cap, []⟩ g1 g2 r0 cl sc).2.2.2 g1' g2' r1
      (eqRound ⟨cap, []⟩ g1 g2 r0 cl sc).2.1 (eqRound ⟨cap, []⟩ g1 g2 r0 cl sc).2.2.1).1],
    (eqRound (eqRound ⟨cap, []⟩ g1 g2 r0 cl sc).2.2.2 g1' g2' r1
      (eqRound ⟨cap, []⟩ g1 g2 r0 cl sc).2.1 (eqRound ⟨cap, []⟩ g1 g2 r0 cl sc).2.2.1).2.2.2.cap,
    (eqRound (eqRound ⟨cap, []⟩ g1 g2 r0 cl sc).2.2.2 g1' g2' r1
      (eqRound ⟨cap, []⟩ g1 g2 r0 cl sc).2.1 (eqRound ⟨cap, []⟩ g1 g2 r0 cl sc).2.2.1).2.1,
    (eqRound (eqRound ⟨cap, []⟩ g1 g2 r0 cl sc).2.2.2 g1' g2' r1
      (eqRound ⟨cap, []⟩ g1 g2 r0 cl sc).2.1 (eqRound ⟨cap, []⟩ g1 g2 r0 cl sc).2.2.1).2.2.1,
    by simp [hml]; ring, by simp [hcl]; ring, ?_, ?_, ?_,
    by simp only [eqRound]; exact squeeze_cap_canonical _, ?_, ?_⟩
  · rw [List.flatMap_append, readsAt_append, flatMap_pairs_length, hml]
    refine ⟨hrm, ?_⟩
    rw [show 2 * (2 * j) = 4 * j by ring, hcur]
    simpa using hmsg
  · rw [readsAt_append, hcl]
    refine ⟨hrc, ?_⟩
    intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact hst0
    · exact hst1
  · have := roundRec_succ hnext
    rw [← hcur, mul_assoc, ← pow_add, show 4 * j + 4 = 4 * (j + 1) by ring] at this
    exact this
  · rw [take_two_more pts hj, e0, e1]
    exact h2.1
  · rw [take_two_more pts hj, e0, e1, h2.2, eqRound_pend]

/-- **The pack rounds**: the loop's records and, with `y` odd, `keccak_round`'s, chain into
`packRunF` of the claim's point `pts`, the messages read from the cursor and the challenges
stored at `point`; the last record (`rounds·y_last`) holds its result. -/
theorem pack_chain {first odd : ℕ} (hfirst : first < 2) (hoddlt : odd < 2)
    {rec pp pt hg yl cur hv curL vL scL : E} {capS pts capL : List E} {y : ℕ}
    (hy : y % 2 = odd) (hhg : hg = gen ^ (y / 2)) (hyl : yl = gen ^ (y / 2 + odd)) (hy32 : y < 32)
    (hpts : pts.length = y) (hpp : ReadsAt rd pp pts)
    (h0 : RoundRec rd rec 0 capS cur hv 1) (hcan : AllCanonical capS)
    (hloop : IsInK (1 + hg) ∧
      (1 + hg ≠ 0 → coreProgram.Rel rd (packLoopName first odd) [1, hg, rec, pp, pt] []))
    (hoddc : odd = 1 → coreProgram.Rel rd "keccak_round" [rec * hg, pp * hg ^ 2, pt * hg ^ 2] [])
    (hlast : RoundRec rd (rec * yl) 0 capL curL vL scL) :
    ∃ (msgs : List (E × E)) (chs : List E), msgs.length = y ∧
      ReadsAt rd cur (msgs.flatMap fun m ↦ [m.1, m.2]) ∧ ReadsAt rd pt chs ∧ chs.length = y ∧
      curL = cur * gen ^ (2 * y) ∧ (packRunF pts msgs hv 1 ⟨capS, []⟩).1 = (vL, scL, chs) ∧
      (packRunF pts msgs hv 1 ⟨capS, []⟩).2 = ⟨capL, []⟩ ∧ AllCanonical capL := by
  have hsteps : ∀ j < y / 2, PackStep rd rec pp pt (gen ^ j) := by
    intro j hj
    have hlt : y / 2 < ordG := by unfold ordG; omega
    have hne := gen_pow_ne_one (h := y / 2) (by omega) hlt
    obtain ⟨fn, hf, hb, hp⟩ := packLoop_fn hfirst hoddlt
    have hrel := hloop.2 (by rw [hhg]; exact hne)
    exact loop_sound (P := coreProgram) (f := packLoopName first odd) (ps := [hg, rec, pp, pt])
      (N := hg) (m := y / 2) (B := PackStep rd rec pp pt)
      (fun d x h' => packLoop_step hf hb hp d x hg rec pp pt h') hhg hlt 0
      (by rw [pow_zero]; exact hrel) j (Nat.zero_le _) hj
  have hinv : ∀ j ≤ y / 2, PackInv rd rec pt cur hv capS pts j := by
    intro j hj
    induction j with
    | zero => exact packInv_zero h0 hcan
    | succ j ih => exact packInv_succ (ih (by omega)) (hsteps j (by omega)) hpp (by omega)
  obtain ⟨msgs, chs, cap, cl, sc, hml, hcl, hrm, hrc, hrec, hcanc, hrun, hrcap⟩ :=
    hinv (y / 2) le_rfl
  rcases Nat.lt_or_ge odd 1 with h0' | h1'
  · -- even: the last record is record `y / 2`
    have hodd0 : odd = 0 := by omega
    subst hodd0
    rw [hyl, Nat.add_zero] at hlast
    obtain ⟨rfl, rfl, rfl, rfl⟩ := roundRec_unique hrec hlast
    have hy2 : 2 * (y / 2) = y := by omega
    rw [hy2, List.take_of_length_le (by omega)] at hrun hrcap
    refine ⟨msgs, chs, by omega, hrm, hrc, by omega, ?_, hrun, hrcap, hcanc⟩
    congr 2; omega
  · -- odd: one more round, `keccak_round` at `rounds·g^(y/2)`
    have hodd1 : odd = 1 := by omega
    subst hodd1
    obtain ⟨-, cap', cur', cl', sc', r, g1, g2, hrec', -, hr, hmsg, hst, hnext⟩ :=
      keccak_round_holds rd _ _ (hoddc rfl)
    rw [hhg] at hrec' hr hst hnext
    obtain ⟨rfl, hcur, rfl, rfl⟩ := roundRec_unique hrec hrec'
    rw [gen_sq, loadHolds_mul_gen_pow, Nat.add_zero] at hr
    rw [gen_sq] at hst
    have e0 : pts[2 * (y / 2)]'(by omega) = r := loadHolds_unique (hpp _ (by omega)) hr
    have hnext' := roundRec_succ hnext
    rw [hyl] at hlast
    obtain ⟨rfl, rfl, rfl, rfl⟩ := roundRec_unique hnext' hlast
    have htake : pts = pts.take (2 * (y / 2)) ++ [pts[2 * (y / 2)]'(by omega)] := by
      conv_lhs => rw [← List.take_of_length_le (show pts.length ≤ 2 * (y / 2) + 1 by omega)]
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
      simp
    refine ⟨msgs ++ [(g1, g2)], chs ++ [(eqRound ⟨cap, []⟩ g1 g2 r cl sc).1], by simp [hml]; omega,
      ?_, ?_, by simp [hcl]; omega, ?_, ?_, ?_, by simp only [eqRound]; exact squeeze_cap_canonical _⟩
    · rw [List.flatMap_append, readsAt_append, flatMap_pairs_length, hml]
      refine ⟨hrm, ?_⟩
      rw [show 2 * (2 * (y / 2)) = 4 * (y / 2) by ring, hcur]
      simpa using hmsg
    · rw [readsAt_append, hcl]
      exact ⟨hrc, fun k hk => by
        simp only [List.length_cons, List.length_nil] at hk
        interval_cases k; exact hst⟩
    · rw [← hcur, mul_assoc, ← pow_add]; congr 2; omega
    · rw [htake, e0, packRunF_append _ _ _ _ _ _ _ (by simp [hml]; omega), hrun, hrcap,
        packRunF_eqRound, packRunF_nil]
    · rw [htake, e0, packRunF_append _ _ _ _ _ _ _ (by simp [hml]; omega), hrun, hrcap,
        packRunF_eqRound, packRunF_nil, eqRound_pend]

end
end LeanVM.Guest.B1.VerifySub
