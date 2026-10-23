/-
  LeanVM.Guest.B1.Opening.QueriesW

  One query and one loop iteration of `opening_queries`, sound with their witnesses named.
-/

module

public import LeanVM.Guest.B1.Opening.Witness
public import LeanVM.Guest.B1.Opening.QueriesMain

/-!
# A query and an iteration, their witnesses named

`posOf_eq`: the bits a run holds spell the position. `oqSibsOf_eq`: children cells holding a
path's `pathCell`s give its siblings. `oqQuery_sound_s`, `oqQuery_sound_w`: one query is
`QueryOpensS` at its witness `oqQueryW`. `oqIter1_sound_w`, `oqIter0_sound_w`: a loop iteration's
queries are those of `oqIterOf`. `loopV_frames`: a guarded loop's iterations, under a call relation
unfolding at `V`, hold at the frames `V f (g^j :: ps) []`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## Reading words -/

theorem memRead_of_load {p : E} {off : ℕ} {v : E} (h : LoadHolds rd p off v) :
    memRead rd p off = v := by
  unfold memRead; rw [h.2]; rfl

theorem readN_of_readsAt {p : E} {xs : List E} (h : ReadsAt rd p xs) :
    readN rd p xs.length = xs := by
  apply List.ext_getElem (by simp [readN])
  intro i h1 h2
  simp only [readN, List.getElem_map, List.getElem_range]
  exact memRead_of_load (h i h2)

theorem bitE_eq_one (b : Bool) : decide (bitE b = 1) = b := by
  cases b <;> simp [bitE]

/-- **The bits a run holds spell the position.** -/
theorem posOf_eq {bp : E} {D q : ℕ} (hq : q < 2 ^ D)
    (h : ∀ l < D, LoadHolds rd bp l (bitE (q.testBit l))) : posOf rd bp D = q := by
  apply Nat.eq_of_testBit_eq
  intro l
  unfold posOf
  rw [testBit_bitsVal]
  by_cases hl : l < D
  · rw [memRead_of_load (h l hl), bitE_eq_one]; simp [hl]
  · simp only [hl, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hq
      (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

theorem digestOfCells_scalars (d : Digest) :
    digestOfCells (digestScalars d).1 (digestScalars d).2 = d := by
  unfold digestOfCells
  rw [Prod.mk.eta, digestOfScalars_digestScalars]
  rfl

/-- **Children cells holding a path's cells give its siblings.** -/
theorem oqSibsOf_eq {pd ch q : ℕ} {leaf : Digest} {sibs : List Digest} (hl : sibs.length = pd)
    (h : ∀ k < 4 * pd, σ (.n (ch + k)) = pathCell leaf q sibs k) :
    oqSibsOf pd ch q σ = sibs := by
  apply List.ext_getElem (by simp [oqSibsOf, hl])
  intro l h1 h2
  have hl' : l < pd := by simpa [oqSibsOf] using h1
  simp only [oqSibsOf, List.getElem_map, List.getElem_range]
  by_cases hb : q.testBit l
  · have e0 := h (4 * l) (by omega)
    have e1 := h (4 * l + 1) (by omega)
    simp only [hb, ↓reduceIte, Nat.add_zero]
    rw [show ch + 4 * l + 1 = ch + (4 * l + 1) by ring, e0, e1]
    unfold pathCell
    simp only [show 4 * l % 4 / 2 = 0 by omega, show 4 * l / 4 = l by omega,
      show (4 * l + 1) % 4 / 2 = 0 by omega, show (4 * l + 1) / 4 = l by omega, hb,
      ↓reduceIte, show 4 * l % 2 = 0 by omega, show (4 * l + 1) % 2 = 1 by omega,
      show (0 : ℕ) ≠ 1 by decide, one_ne_zero]
    rw [digestOfCells_scalars, List.getD_eq_getElem _ _ h2]
  · have e0 := h (4 * l + 2) (by omega)
    have e1 := h (4 * l + 2 + 1) (by omega)
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    rw [show ch + 4 * l + 2 = ch + (4 * l + 2) by ring,
      show ch + (4 * l + 2) + 1 = ch + (4 * l + 2 + 1) by ring, e0, e1]
    unfold pathCell
    simp only [show (4 * l + 2) % 4 / 2 = 1 by omega, show (4 * l + 2) / 4 = l by omega,
      show (4 * l + 2 + 1) % 4 / 2 = 1 by omega, show (4 * l + 2 + 1) / 4 = l by omega, hb,
      Bool.false_eq_true, ↓reduceIte, show (4 * l + 2) % 2 = 0 by omega,
      show (4 * l + 2 + 1) % 2 = 1 by omega, one_ne_zero]
    rw [digestOfCells_scalars, List.getD_eq_getElem _ _ h2]

/-! ## One query -/

/-- **One query is `QueryOpensS`** at its row and the siblings its children cells hold. -/
theorem oqQuery_sound_s {s : Oq} (hs : s.RowShape) (hcd : 2 ≤ s.cd) (hcd8 : s.cd ≤ 8)
    {bp cap flags wp : V} {b : ℕ} {emit : Bool} {pr : ℕ}
    (hA : ∀ a, Stmt.atom a ∈ oqQueryT s bp cap flags wp b emit pr → a.Holds rd σ)
    (hpad : σ (.n (oqPr s b emit pr)) = word 1 0 0)
    (hz : ∀ i < 4, σ (.n (oqPr s b emit pr + 1 + i)) = 0)
    {q : ℕ} (hq : q < 2 ^ (s.pd + s.cd))
    (hbits : ∀ l < s.pd + s.cd, LoadHolds rd (σ bp) l (bitE (q.testBit l))) :
    QueryOpensS rd s.base s.I (s.pd + s.cd) s.cd (σ cap) (σ flags) (σ wp) q (oqRow b s.R σ)
      (oqSibsOf s.pd (oqCh s b emit) q σ) (σ (.n (oqDot s b))) := by
  obtain ⟨hP, hD, -, hL, hPa, hC⟩ := oqQuery_pieces hA
  have hR2 : s.R % 2 = 0 := by rcases hs with ⟨hb, hI⟩ | ⟨hb, hI⟩ <;> simp [Oq.R, hb, hI]
  have hrl : (oqRow b s.R σ).length = s.R := by simp [oqRow]
  have hW := oqWord_sound hs hP hD
  obtain ⟨hw, hdot⟩ := oqDot_sound hs hD hW
  have hpk : ∀ j < s.ncells, σ (.n (oqPk b s.R j)) =
      E.ofLimbs ((oqRow b s.R σ).getD (2 * j) 0) ((oqRow b s.R σ).getD (2 * j + 1) 0) 0 :=
    fun j hj => by
      have hj' : j < s.R / 2 := hj
      rw [(oqPack_sound hP hj').2.2, getD_oqRow (by omega), getD_oqRow (by omega)]
      rfl
  have hleaf := oqLeaf_sound hs hL hpad hz (by simp [oqRow, Oq.ncells]; omega) hpk
  obtain ⟨sibs, hsl, hch, hlv, hnd⟩ := oqPath_sound hPa hpad hz
    (fun l hl => hbits l (by omega)) hleaf
  have hsib : oqSibsOf s.pd (oqCh s b emit) q σ = sibs := oqSibsOf_eq hsl hch
  rw [hsib]
  obtain ⟨hpp, hfr⟩ := oqPath_frame hPa
  obtain ⟨hflag, hc0, hc1⟩ := oqCap_sound hcd hcd8 hC hq (fun l h1 h2 => hbits l h2)
  unfold QueryOpensS
  rw [show s.pd + s.cd - s.cd = s.pd by omega]
  refine ⟨by rw [hrl]; rfl, hsl, oqW s b σ, σ (.n (oqCh s b emit + 4 * s.pd)),
    fun l hl => hw l (by simpa [Oq.lo] using hl), hpp, fun k hk x hx => ?_, fun l hl => ?_, ?_,
    ?_, hflag, ?_⟩
  · rw [hfr k hk x hx, hch k hk]
  · obtain ⟨hn, h0, h1⟩ := hlv l hl
    rw [show σ (.n (oqNode s (oqKL s b emit) (oqCh s b emit) l 0)) =
      (digestScalars (climbNode (hashWords (oqRow b s.R σ)) q sibs l)).1 by rw [← hn]] at h0
    rw [show σ (.n (oqNode s (oqKL s b emit) (oqCh s b emit) l 1)) =
      (digestScalars (climbNode (hashWords (oqRow b s.R σ)) q sibs l)).2 by rw [← hn]] at h1
    exact ⟨h0, h1⟩
  · rw [show σ (.n (oqNode s (oqKL s b emit) (oqCh s b emit) s.pd 0)) =
      (digestScalars (climbD (hashWords (oqRow b s.R σ)) q sibs)).1 by rw [← hnd]] at hc0
    exact hc0
  · rw [show σ (.n (oqNode s (oqKL s b emit) (oqCh s b emit) s.pd 1)) =
      (digestScalars (climbD (hashWords (oqRow b s.R σ)) q sibs)).2 by rw [← hnd]] at hc1
    exact hc1
  · rw [hdot, rowDot_eq]
    congr 1

/-- What a query establishes of its witness `w`: its position below `2^(pd + cd)`, the bit run at
`bp` spelling it, and `QueryOpensS` at its row and siblings. -/
def QueryW (rd : Reader) (s : Oq) (cap flags wp bp : E) (w : QW) (d : E) : Prop :=
  w.1 < 2 ^ (s.pd + s.cd) ∧ (∀ l < s.pd + s.cd, LoadHolds rd bp l (bitE (w.1.testBit l))) ∧
    QueryOpensS rd s.base s.I (s.pd + s.cd) s.cd cap flags wp w.1 w.2.1 w.2.2 d

/-- **A query whose bit pointer points to bits** is sound at its witness `oqQueryW`. -/
theorem oqQuery_sound_w {s : Oq} (hs : s.RowShape) (hcd : 2 ≤ s.cd) (hcd8 : s.cd ≤ 8)
    {bp cap flags wp : V} {b : ℕ} {emit : Bool} {pr : ℕ}
    (hA : ∀ a, Stmt.atom a ∈ oqQueryT s bp cap flags wp b emit pr → a.Holds rd σ)
    (hpad : σ (.n (oqPr s b emit pr)) = word 1 0 0)
    (hz : ∀ i < 4, σ (.n (oqPr s b emit pr + 1 + i)) = 0)
    (hbool : ∀ l < s.pd + s.cd, ∀ w, LoadHolds rd (σ bp) l w → w = 0 ∨ w = 1) :
    QueryW rd s (σ cap) (σ flags) (σ wp) (σ bp) (oqQueryW s rd (σ bp) b emit σ)
      (σ (.n (oqDot s b))) := by
  obtain ⟨q, hq, hbits⟩ := bits_q (oqQuery_bitLoads hcd hA) hbool
  have e : posOf rd (σ bp) (s.pd + s.cd) = q := posOf_eq hq hbits
  unfold oqQueryW
  rw [e]
  exact ⟨hq, hbits, oqQuery_sound_s hs hcd hcd8 hA hpad hz hq hbits⟩

/-! ## The iterations -/

/-- **A level-0 iteration** at `x = g^i`, its two queries at their witnesses. -/
theorem oqIter1_sound_w {s : Oq} (hs : s.RowShape) (hcd : 2 ≤ s.cd) (hcd8 : s.cd ≤ 8) {odd i : ℕ}
    (hA : ∀ a, Stmt.atom a ∈ oqLoop1A s odd → a.Holds rd σ) (hx : σ (.n 0) = gen ^ i)
    (hbool : ∀ k, k = 2 * i + odd ∨ k = 2 * i + odd + 1 → ∀ bp, LoadHolds rd (σ (.n 2)) k bp →
      ∀ l < s.pd + s.cd, ∀ w, LoadHolds rd bp l w → w = 0 ∨ w = 1) :
    ∃ v : E,
      LoadHolds rd (σ (.n 2)) (2 * i + odd) (σ (.n 10)) ∧
      QueryW rd s (σ (.n 3)) (σ (.n 4)) (σ (.n 5)) (σ (.n 10)) (oqQueryW s rd (σ (.n 10)) 11 true σ)
        (σ (.n (oqDot s 11))) ∧
      LoadHolds rd (σ (.n 2)) (2 * i + odd + 1) (σ (.n (oqE1 s))) ∧
      QueryW rd s (σ (.n 3)) (σ (.n 4)) (σ (.n 5)) (σ (.n (oqE1 s)))
        (oqQueryW s rd (σ (.n (oqE1 s))) (oqE1 s + 1) false σ) (σ (.n (oqDot s (oqE1 s + 1)))) ∧
      LoadHolds rd (σ (.n 6)) i v ∧
      LoadHolds rd (σ (.n 6)) (i + 1) (((v + σ (.n (oqDot s 11))) * σ (.n 7) +
        σ (.n (oqDot s (oqE1 s + 1)))) * σ (.n 7)) := by
  have p8 := hA _ (by simp [oqLoop1A] : Stmt.atom (.mul (.n 8) (.n 2) (.n 0)) ∈ _)
  have p9 := hA _ (by simp [oqLoop1A] : Stmt.atom (.mul (.n 9) (.n 8) (.n 0)) ∈ _)
  have p10 := hA _ (by simp [oqLoop1A] : Stmt.atom (.load (.n 10) (.n 9) odd) ∈ _)
  have pe1 := hA _ (by simp [oqLoop1A] : Stmt.atom (.load (.n (oqE1 s)) (.n 9) (odd + 1)) ∈ _)
  simp only [Atom.Holds] at p8 p9 p10 pe1
  have h9 : σ (.n 9) = σ (.n 2) * gen ^ (2 * i) := by rw [p9, p8, hx, mul_assoc, ← pow_add]; ring_nf
  rw [h9, loadHolds_mul_gen_pow] at p10 pe1
  have hq1 := fun a h => hA a (oqLoop1A_mem_q1 (odd := odd) h)
  have hq2 := fun a h => hA a (oqLoop1A_mem_q2 (odd := odd) h)
  obtain ⟨-, -, hpd, -, -, -⟩ := oqQuery_pieces hq1
  obtain ⟨e1, z⟩ := oqPad_values (hpd rfl)
  have pe1' : LoadHolds rd (σ (.n 2)) (2 * i + odd + 1) (σ (.n (oqE1 s))) := by
    rw [show 2 * i + odd + 1 = 2 * i + (odd + 1) by omega]; exact pe1
  have w1 := oqQuery_sound_w hs hcd hcd8 hq1 e1 z (hbool _ (Or.inl rfl) _ p10)
  have w2 := oqQuery_sound_w hs hcd hcd8 hq2 e1 z (hbool _ (Or.inr rfl) _ pe1')
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
  exact ⟨_, p10, w1, pe1', w2, c1, c7⟩

/-- **A deeper iteration** at `x = g^i`, its query at its witness. -/
theorem oqIter0_sound_w {s : Oq} (hs : s.RowShape) (hcd : 2 ≤ s.cd) (hcd8 : s.cd ≤ 8) {i : ℕ}
    (hA : ∀ a, Stmt.atom a ∈ oqLoop0A s → a.Holds rd σ) (hx : σ (.n 0) = gen ^ i)
    (hbool : ∀ bp, LoadHolds rd (σ (.n 2)) i bp →
      ∀ l < s.pd + s.cd, ∀ w, LoadHolds rd bp l w → w = 0 ∨ w = 1) :
    ∃ v : E, LoadHolds rd (σ (.n 2)) i (σ (.n 9)) ∧
      QueryW rd s (σ (.n 3)) (σ (.n 4)) (σ (.n 5)) (σ (.n 9)) (oqQueryW s rd (σ (.n 9)) 10 true σ)
        (σ (.n (oqDot s 10))) ∧
      LoadHolds rd (σ (.n 6)) i v ∧
      LoadHolds rd (σ (.n 6)) (i + 1) ((v + σ (.n (oqDot s 10))) * σ (.n 7)) := by
  have p8 := hA _ (by simp [oqLoop0A] : Stmt.atom (.mul (.n 8) (.n 2) (.n 0)) ∈ _)
  have p9 := hA _ (by simp [oqLoop0A] : Stmt.atom (.load (.n 9) (.n 8) 0) ∈ _)
  simp only [Atom.Holds] at p8 p9
  rw [p8, hx, loadHolds_mul_gen_pow, Nat.add_zero] at p9
  have hq := fun a h => hA a (oqLoop0A_mem_q h)
  obtain ⟨-, -, hpd, -, -, -⟩ := oqQuery_pieces hq
  obtain ⟨e1, z⟩ := oqPad_values (hpd rfl)
  have w1 := oqQuery_sound_w hs hcd hcd8 hq e1 z (hbool _ p9)
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
  exact ⟨_, p9, w1, c1, c5⟩

/-! ## A guarded loop's frames -/

/-- **A guarded loop's iterations hold at their frames**: under a call relation unfolding at `V`,
when the loop is called at `1` with the bound `N_v = g^N`, its iterations `j < N` hold at the
frames `V f (g^j :: N_v :: rest) []`. -/
theorem loopV_frames {C : CallRel} {V : FrameMap} (hU : UnfoldsV rd C V) {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) {A : List Stmt} {c : ℕ} {args : List Core.V}
    (hb : fn.body = A ++ [.callIf (.n c) f args, .ret []]) (hA : AllAtoms A) {Nv : E}
    {rest : List E}
    (hc : ∀ (τ : Val) (x : E), fn.params.map τ = x :: Nv :: rest →
      (∀ a, Stmt.atom a ∈ A → a.Holds rd τ) →
      τ (.n c) = x * gen + Nv ∧ args.map τ = x * gen :: Nv :: rest)
    {N : ℕ} (hN : Nv = gen ^ N) (hNo : N < ordG) (h0 : 0 < N → C f (1 :: Nv :: rest) []) :
    ∀ j < N, fn.params.map (V f (gen ^ j :: Nv :: rest) []) = gen ^ j :: Nv :: rest ∧
      ∀ a, Stmt.atom a ∈ A → a.Holds rd (V f (gen ^ j :: Nv :: rest) []) := by
  have unf : ∀ j, C f (gen ^ j :: Nv :: rest) [] →
      fn.params.map (V f (gen ^ j :: Nv :: rest) []) = gen ^ j :: Nv :: rest ∧
      (∀ a, Stmt.atom a ∈ A → a.Holds rd (V f (gen ^ j :: Nv :: rest) [])) ∧
      (V f (gen ^ j :: Nv :: rest) [] (.n c) ≠ 0 →
        C f (args.map (V f (gen ^ j :: Nv :: rest) [])) []) := by
    intro j hC
    obtain ⟨fn', hf', hp, hh⟩ := hU _ _ _ hC
    rw [hf] at hf'
    cases hf'
    rw [hb, holdsList_append, holdsList_atoms hA] at hh
    obtain ⟨hall, h⟩ := hh
    simp only [Stmt.HoldsList, Stmt.Holds] at h
    exact ⟨hp, hall, h.2.1⟩
  have calls : ∀ j < N, C f (gen ^ j :: Nv :: rest) [] := by
    intro j hj
    induction j with
    | zero => rw [pow_zero]; exact h0 hj
    | succ j ih =>
      obtain ⟨hp, hall, hcall⟩ := unf j (ih (by omega))
      obtain ⟨e1, e2⟩ := hc _ _ hp hall
      have := hcall (by
        rw [e1, hN, ← pow_succ]
        intro h
        have := gen_pow_inj (lt_trans (show j + 1 < N by omega) hNo) hNo (e_add_eq_zero_iff.mp h)
        omega)
      rwa [e2, ← pow_succ] at this
  intro j hj
  obtain ⟨hp, hall, -⟩ := unf j (calls j hj)
  exact ⟨hp, hall⟩

end
end LeanVM.Guest.B1
