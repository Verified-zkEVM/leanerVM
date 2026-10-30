/-
  LeanVM.Guest.B1.Da.VerifyW

  `da_verify`'s witness, named: the blob matrix and the vector as functions of `da_verify`'s
  valuation and the frame map.
-/

module

public import LeanVM.Guest.B1.Da.Verify
public import LeanVM.Guest.B1.Main.LoopsC
public import LeanVM.Guest.B1.Main.Facts

/-!
# `da_verify`, its witness named

Under a call relation `C` that unfolds at the frame map `Vm` (`UnfoldsV`) and lies below
`coreProgram.Rel`, the column loops' iterations, the columns, their row loops' iterations, the
cell checks and the vector checks are calls of `C`, each holding at `Vm`'s valuation of it. The
witness (`dvWit σ Vm`) reads the symbols off each cell check's valuation (`cellSymsOf`) and the
weights off each vector check's (`vecWsOf`), at the calls `da_verify`'s structure makes:
column `j`'s call `dvColArgs σ j`, its row loop's iteration `i`, its cell check. It mentions no
hash. `da_verify_sound_w`: the returned words are a root and a vector digest that it opens.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

/-! ## The witness -/

/-- Column `j`'s function. -/
def colNm (j : ℕ) : String := if j < 64 then "da_verify_column__L1" else "da_verify_column__L0"

/-- Column `j`'s row loop. -/
def rowNm (j : ℕ) : String := if j < 64 then "__loop415" else "__loop417"

/-- Column `j`'s call's words. -/
def dvColArgs (σ : Val) (j : ℕ) : List E :=
  [gen ^ j, σ (.n 1), σ (.n 3), σ (.n 4), σ (.n 2), σ (.n 13), σ (.n 31), σ (.n 27), σ (.n 17)]

/-- Column `j`'s valuation. -/
def dvColV (σ : Val) (Vm : FrameMap) (j : ℕ) : Val := Vm (colNm j) (dvColArgs σ j) []

/-- Row `i`'s iteration of column `j`'s row loop, its valuation. -/
def dvRowV (σ : Val) (Vm : FrameMap) (i j : ℕ) : Val :=
  Vm (rowNm j) [gen ^ i, σ (.n 1), dvColV σ Vm j (.n 11), σ (.n 27), gen ^ j, dvColV σ Vm j (.n 14),
    σ (.n 13)] []

/-- Column `j`'s weights: its vector check's. -/
def dvWs (σ : Val) (Vm : FrameMap) (j : ℕ) : List E :=
  vecWsOf (Vm "da_vector_cell" [σ (.n 17) * (gen ^ j) ^ 2] [dvColV σ Vm j (.n 11)])

/-- Cell `(i, j)`'s symbols: its cell check's. -/
def dvSyms (σ : Val) (Vm : FrameMap) (i j : ℕ) : List K :=
  cellSymsOf (Vm "da_verify_cell" [dvColV σ Vm j (.n 11)]
    [dvRowV σ Vm i j (.n 7), dvRowV σ Vm i j (.n 8), dvRowV σ Vm i j (.n 9)])

/-- The symbols, padded outside the matrix. -/
noncomputable def dvSymsP (σ : Val) (Vm : FrameMap) (i j : ℕ) : List K :=
  if i < gLog (σ (.n 1)) ∧ j < 128 then dvSyms σ Vm i j else List.replicate 256 0

/-- The weights, padded outside the vector. -/
def dvWsP (σ : Val) (Vm : FrameMap) (j : ℕ) : List E :=
  if j < 128 then dvWs σ Vm j else List.replicate 256 0

/-- **`da_verify`'s witness**: the rows of the cells' symbols, as many as the shape's count, and
the vector of the columns' weights. -/
noncomputable def dvWit (σ : Val) (Vm : FrameMap) : LeanVM.Da.MatrixWitness :=
  ⟨daRows (gLog (σ (.n 1))) (dvSymsP σ Vm), daVector (dvWsP σ Vm)⟩

/-! ## The calls, at the frame map -/

variable {rd : Reader} {C : CallRel} {Vm : FrameMap}

/-- **Row `x`'s cell of a column, its check at the loop's valuation `σr`.** -/
def RowStepW (C : CallRel) (rd : Reader) (σr : Val) (lv rowbase xb node pb : E) (store : Bool)
    (x : E) : Prop :=
  C "da_verify_cell" [lv] [σr (.n 7), σr (.n 8), σr (.n 9)] ∧
    LoadHolds rd (rowbase * x) 0 (memAt rd (rowbase * x) 0) ∧
    LoadHolds rd (memAt rd (rowbase * x) 0 * xb) 1
      (memAt rd (memAt rd (rowbase * x) 0 * xb) 0 + σr (.n 9)) ∧
    LoadHolds rd (node * x ^ 2) 0 (σr (.n 7)) ∧ LoadHolds rd (node * x ^ 2) 1 (σr (.n 8)) ∧
    (store = true → LoadHolds rd (memAt rd (pb * x) 0 * xb ^ 2) 0 (σr (.n 7)) ∧
      LoadHolds rd (memAt rd (pb * x) 0 * xb ^ 2) 1 (σr (.n 8)))

theorem row_stepW (hVm : UnfoldsV rd C Vm) {f : String} {j : ℕ} {store : Bool} (hj : j < coreProgram.length)
    (hok : (rowOk (coreProgram.getD j default) f store &&
      decide (coreProgram.indexOf? f = some j)) = true) {x : E} {ps : List E}
    (h : C f (x :: ps) []) :
    (∀ N lv rowbase xb node pb, ps = [N, lv, rowbase, xb, node, pb] →
      RowStepW C rd (Vm f (x :: ps) []) lv rowbase xb node pb store x) ∧
      (x * gen + ps.headD 0 ≠ 0 → C f (x * gen :: ps) []) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hok, hidx⟩ := hok
  have hf := find_of_idx hidx hj
  unfold rowOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hcall⟩, hm10⟩, hl11⟩, hm12⟩, hl13⟩, ha14⟩, hl14⟩, hm15⟩,
    hm16⟩, hl7⟩, hl8⟩, hst⟩ := hok
  obtain ⟨hx, hps, hall, hnext⟩ := loop_stepV hVm hf hshape h
  set σ := Vm f (x :: ps) [] with hσ
  refine ⟨fun N lv rowbase xb node pb hN => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD j default).params =
      [V.n 0, V.n 1, V.n 2, V.n 3, V.n 4, V.n 5, V.n 6] := by
    have hs := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, h3, h4, h5, h6⟩ := hps
  have c := call_of_flat hall hcall
  simp only [List.map_cons, List.map_nil] at c
  rw [h2] at c
  have p10 : σ (.n 10) = rowbase * x := by rw [isMul_sound hm10 hat, h3, hx]
  have l11 := load_sound hl11 hat
  rw [p10] at l11
  have e11 := memAt_of_load l11
  have p12 : σ (.n 12) = memAt rd (rowbase * x) 0 * xb := by rw [isMul_sound hm12 hat, e11, h4]
  have l13 := load_sound hl13 hat
  rw [p12] at l13
  have l14 := load_sound hl14 hat
  rw [p12, add_sound ha14 hat, ← memAt_of_load l13] at l14
  have p16 : σ (.n 16) = node * x ^ 2 := by rw [isMul_sound hm16 hat, isMul_sound hm15 hat, h5, hx, sq]
  have l7 := load_sound hl7 hat
  have l8 := load_sound hl8 hat
  rw [p16] at l7 l8
  refine ⟨c, by rw [e11]; exact l11, l14, l7, l8, fun hs => ?_⟩
  rcases hst with hs' | hst
  · rw [hs] at hs'; exact absurd hs' (by decide)
  obtain ⟨⟨⟨⟨⟨hm17, hl18⟩, hm19⟩, hm20⟩, hl7'⟩, hl8'⟩ := hst
  have l18 := load_sound hl18 hat
  rw [isMul_sound hm17 hat, h6, hx] at l18
  have p20 : σ (.n 20) = memAt rd (pb * x) 0 * xb ^ 2 := by
    rw [isMul_sound hm20 hat, isMul_sound hm19 hat, memAt_of_load l18, h4, sq]
  have l7' := load_sound hl7' hat
  have l8' := load_sound hl8' hat
  rw [p20] at l7' l8'
  exact ⟨l7', l8'⟩


/-- **A loop from `g^a`**: a run at `g^a` gives the body at every `g^j`, `a ≤ j < m`. -/
theorem loop_fromC {f : String} {ps : List E} {N : E} {m a : ℕ} {B : E → Prop}
    (hm : m < ordG) (hN : N = gen ^ m)
    (hstep : ∀ x, C f (x :: ps) [] →
      B x ∧ (x * gen + N ≠ 0 → C f (x * gen :: ps) []))
    (h : C f (gen ^ a :: ps) []) : ∀ j, a ≤ j → j < m → B (gen ^ j) := by
  have key : ∀ t k, k + t = m → C f (gen ^ k :: ps) [] →
      ∀ j, k ≤ j → j < m → B (gen ^ j) := by
    intro t
    induction t with
    | zero => intro k hk _ j h1 h2; omega
    | succ t ih =>
      intro k hk hrun j h1 h2
      obtain ⟨hB, hnext⟩ := hstep _ hrun
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · exact hB
      · have hne : gen ^ k * gen + N ≠ 0 := by
          intro he
          rw [gen_pow_add_eq_zero_iff, hN] at he
          have := gen_pow_inj hm (by unfold ordG at hm; omega) he
          omega
        have := hnext hne
        rw [gen_pow_mul_gen] at this
        exact ih (k + 1) (by omega) this j hlt h2
  intro j h1 h2
  exact key (m - a) a (by omega) h j h1 h2

theorem col_loop_stepW (hVm : UnfoldsV rd C Vm) {f col : String} {j endLo : ℕ} (hj : j < coreProgram.length)
    (hok : (colLoopOk (coreProgram.getD j default) col f endLo &&
      decide (coreProgram.indexOf? f = some j)) = true) {x : E} {ps : List E}
    (h : C f (x :: ps) []) :
    C col (x :: ps) [] ∧
      (x * gen + word endLo 0 0 ≠ 0 → C f (x * gen :: ps) []) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hok, hidx⟩ := hok
  unfold colLoopOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hparams, hbody⟩ := hok
  obtain ⟨hpar, hb⟩ := body_ofV hVm (find_of_idx hidx hj) h
  set σ := Vm f (x :: ps) [] with hσ
  rw [stmtsEqb_sound hbody] at hb
  have r9 : (List.range 9).map V.n = [V.n 0, V.n 1, V.n 2, V.n 3, V.n 4, V.n 5, V.n 6, V.n 7, V.n 8] :=
    rfl
  have r8 : (List.range 8).map (fun k => V.n (k + 1)) =
      [V.n 1, V.n 2, V.n 3, V.n 4, V.n 5, V.n 6, V.n 7, V.n 8] := rfl
  rw [hparams, r9] at hpar
  simp only [List.map_cons, List.map_nil] at hpar
  obtain ⟨hx, hps⟩ := List.cons.inj hpar
  simp only [colLoopBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, r9, r8, List.map_cons,
    List.map_nil] at hb
  obtain ⟨hc, h9, h10, h11, h12, h13, h14, -, hcall, -⟩ := hb
  refine ⟨?_, fun hne => ?_⟩
  · rw [← hx, ← hps]; exact hc
  · have e12 : σ (.n 12) = x * gen + word endLo 0 0 := by rw [h12, h10, h9, h11, word_gen, hx]
    have e14 : σ (.n 14) = x * gen := by rw [h14, h13, word_gen, hx]
    have := hcall (by rw [e12]; exact hne)
    rw [e14] at this
    rw [← hps]
    exact this

/-- **A column's run.** -/
theorem col_stepW (hVm : UnfoldsV rd C Vm) (hle : CallRel.Le C (coreProgram.Rel rd))
    {fname rl gl : String} {jc jr jg : ℕ} {store : Bool}
    (hjc : jc < coreProgram.length) (hjr : jr < coreProgram.length) (hjg : jg < coreProgram.length)
    (hcol : (colOk (coreProgram.getD jc default) rl gl &&
      decide (coreProgram.indexOf? fname = some jc)) = true)
    (hrow : (rowOk (coreProgram.getD jr default) rl store &&
      decide (coreProgram.indexOf? rl = some jr)) = true)
    (hgap : (gapOk (coreProgram.getD jg default) gl padCellLo.1 padCellLo.2.1 padCellLo.2.2.1
      padCellLo.2.2.2 && decide (coreProgram.indexOf? gl = some jg)) = true)
    {xb a1 npad a3 glp pb coltree rowbase cd : E} {r gp : ℕ} (hr : r < ordG) (hg : gp < ordG)
    (ha1 : a1 = gen ^ r) (ha3 : a3 = gen ^ gp)
    (h : C fname [xb, a1, npad, a3, glp, pb, coltree, rowbase, cd] []) :
    C "da_vector_cell" [cd * xb ^ 2]
        [Vm fname [xb, a1, npad, a3, glp, pb, coltree, rowbase, cd] [] (.n 11)] ∧
      (∀ i < r, RowStepW C rd (Vm rl [gen ^ i, a1,
        Vm fname [xb, a1, npad, a3, glp, pb, coltree, rowbase, cd] [] (.n 11), rowbase, xb,
        Vm fname [xb, a1, npad, a3, glp, pb, coltree, rowbase, cd] [] (.n 14), pb] [])
        (Vm fname [xb, a1, npad, a3, glp, pb, coltree, rowbase, cd] [] (.n 11)) rowbase xb
        (Vm fname [xb, a1, npad, a3, glp, pb, coltree, rowbase, cd] [] (.n 14)) pb store
        (gen ^ i)) ∧
      (∀ d < gp, GapStepC rd (Vm fname [xb, a1, npad, a3, glp, pb, coltree, rowbase, cd] [] (.n 14))
        (gen ^ r) (gen ^ d)) ∧
      (∃ k < 11, glp = ofK (Parameters.gpow k) ∧
        coreProgram.Rel rd (daLevelsName k)
          [Vm fname [xb, a1, npad, a3, glp, pb, coltree, rowbase, cd] [] (.n 14)]
          [Vm fname [xb, a1, npad, a3, glp, pb, coltree, rowbase, cd] [] (.n 21),
            Vm fname [xb, a1, npad, a3, glp, pb, coltree, rowbase, cd] [] (.n 22)]) ∧
      LoadHolds rd (coltree * xb ^ 2) 0
        (Vm fname [xb, a1, npad, a3, glp, pb, coltree, rowbase, cd] [] (.n 21)) ∧
      LoadHolds rd (coltree * xb ^ 2) 1
        (Vm fname [xb, a1, npad, a3, glp, pb, coltree, rowbase, cd] [] (.n 22)) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcol
  obtain ⟨hok, hidx⟩ := hcol
  obtain ⟨hpar, hb⟩ := body_ofV hVm (find_of_idx hidx hjc) h
  set σ := Vm fname [xb, a1, npad, a3, glp, pb, coltree, rowbase, cd] [] with hσ
  unfold colOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hparams, hok⟩ := hok
  split at hok
  · rename_i P vs hsr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨rfl, hflat⟩, hm9⟩, hm10⟩, hvc⟩, hg16⟩, hg19⟩, hdisp⟩, hm23⟩, hm24⟩, hl21⟩,
      hl22⟩ := hok
    rw [splitRet_eq hsr, holdsList_append] at hb
    obtain ⟨hall, -⟩ := holdsList_flat P hflat _ _ hb
    have hallR : ∀ s ∈ P, Stmt.Holds (coreProgram.Rel rd) rd σ s True (fun rs => rs = []) :=
      fun s hs => holds_mono hle s id (fun _ h => h) (hall s hs)
    have hat := atoms_of_flat hall
    rw [hparams, show (List.range 9).map V.n = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7,
      .n 8] from rfl] at hpar
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
    obtain ⟨h0, h1, -, h3, h4, h5, h6, h7, h8⟩ := hpar
    have c := call_of_flat hall hvc
    simp only [List.map_cons, List.map_nil] at c
    rw [isMul_sound hm10 hat, isMul_sound hm9 hat, h0, h8, ← sq] at c
    have L1 := loop_soundC (C := C) (f := rl) (ps := [a1, σ (.n 11), rowbase, xb, σ (.n 14), pb])
        (B := fun y => RowStepW C rd (Vm rl (y :: [a1, σ (.n 11), rowbase, xb, σ (.n 14), pb]) [])
          (σ (.n 11)) rowbase xb (σ (.n 14)) pb store y) hr ha1
        (fun y hy => by
          obtain ⟨k1, k2⟩ := row_stepW hVm hjr hrow hy
          exact ⟨k1 _ _ _ _ _ _ rfl, k2⟩)
        (fun hne => by
          have := guard_soundC hg16 hall (by rw [h1]; exact hne)
          simpa [h1, h7, h0, h5] using this)
    have L2 : ∀ d < gp, GapStepC rd (σ (.n 14)) (gen ^ r) (gen ^ d) :=
      loop_sound (f := gl) (ps := [gen ^ gp, σ (.n 14), gen ^ r]) hg rfl
        (fun y hy => by
          obtain ⟨k1, k2⟩ := gap_step hjg hgap hy
          exact ⟨k1 _ _ _ rfl, k2⟩)
        (fun hne => by
          have := guard_sound hg19 hallR (by rw [h3, ha3]; exact hne)
          simpa [h3, h1, ha1, ha3] using this)
    obtain ⟨k, hk, hk4, hrel⟩ := dispatch_of_flat hallR hdisp
    simp only [dlNames, List.length_map, List.length_range] at hk
    have p24 : σ (.n 24) = coltree * xb ^ 2 := by
      rw [isMul_sound hm24 hat, isMul_sound hm23 hat, h6, h0, sq]
    have l21 := load_sound hl21 hat
    have l22 := load_sound hl22 hat
    rw [p24] at l21 l22
    refine ⟨c, L1, L2, ⟨k, hk, by rw [← h4, hk4], ?_⟩,
      l21, l22⟩
    simpa [dlNames] using hrel
  · exact absurd hok (by simp)

/-! ## `da_verify` -/

set_option maxHeartbeats 4000000 in
/-- **`da_verify`, soundly, its witness named**: under a call relation that unfolds at `Vm` and
lies below `coreProgram.Rel`, on a memory image with the exponent table at its argument, the
returned words are a root and a vector digest that `dvWit σ Vm` opens. -/
theorem da_verify_sound_w (hVm : UnfoldsV rd C Vm) (hle : CallRel.Le C (coreProgram.Rel rd))
    (hm : MemOk rd) {σ : Val} {gsq : E} {rets : List E} (hpar0 : Data.core25.params.map σ = [gsq])
    (hb : Stmt.HoldsList C rd σ (Fn.body Data.core25) False (fun rs => rs = rets))
    (hsq0 : SquaresAt rd gsq) :
    ∃ root vd : Digest, (dvWit σ Vm).Opens root vd ∧ rets = digestCells root ++ digestCells vd := by
  have hok := dv_ok
  unfold dvOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hparams, hbody⟩, hflat⟩, hcrs⟩, hm11⟩, hg18⟩, hm25⟩, hg19⟩,
    hc32⟩, hc20⟩, hc33⟩, hc21⟩, hg22⟩, hc7⟩, hm40⟩, hg23⟩, hg24⟩, hdisp⟩, hroot⟩, hcp993⟩,
    hcp994⟩, hld17⟩, hvshape⟩, hvnb⟩, hcp995⟩, hcp996⟩ := hok
  have hσ0 : σ (.n 0) = gsq := by
    rw [hparams] at hpar0
    simpa using hpar0
  have hsq : SquaresAt rd (σ (.n 0)) := by rw [hσ0]; exact hsq0
  rw [stmtsEqb_sound hbody, holdsList_append] at hb
  obtain ⟨hallC, hret⟩ := holdsList_flat dvP hflat _ _ hb
  have hall : ∀ s ∈ dvP, Stmt.Holds (coreProgram.Rel rd) rd σ s True (fun rs => rs = rets) :=
    fun s hs => holds_mono hle s id (fun _ h => h) (hallC s hs)
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hret
  have hat := atoms_of_flat hall
  -- the shape
  have hrs := da_row_shape_holds rd hm _ _ (call_of_flat hall hcrs)
  simp only [List.map_cons, List.map_nil, MeaningDaRowShape] at hrs
  obtain ⟨r, L, hr1, hr, hL, h1, h2, hnp, h34⟩ := hrs hsq
  simp only [List.cons.injEq, and_true] at h34
  obtain ⟨h3, h4⟩ := h34
  unfold LeanDa.maxRows at hr
  have hL2 : 2 ^ L ≤ 1024 := by
    calc 2 ^ L ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) hL
      _ = 1024 := by norm_num
  have hrL : r ≤ 2 ^ L := by
    rw [hnp, LeanDa.nPad, LeanDa.logPad]; exact Nat.le_pow_clog (by norm_num) r
  -- the prefix bases and the running sums
  have L18 : ∀ i < r, LoadHolds rd (σ (.n 13) * gen ^ i) 0 (σ (.n 12) * (gen ^ i) ^ 128) :=
    loop_sound (f := "__loop17") (ps := [σ (.n 1), σ (.n 13), σ (.n 12)]) (ordG_of (by omega)) h1
      (fun y hy => by
        obtain ⟨k1, k2⟩ := l18_step hy
        exact ⟨k1 _ _ _ rfl, k2⟩)
      (fun hne => by simpa using guardK_sound hg18 hall hne)
  have L19 : ∀ i < r, LoadHolds rd (σ (.n 27) * gen ^ i) 0 (σ (.n 26) * (gen ^ i) ^ 129) ∧
      LoadHolds rd (σ (.n 26) * (gen ^ i) ^ 129) 0 0 :=
    loop_sound (f := "__loop18") (ps := [σ (.n 1), σ (.n 26), σ (.n 27)]) (ordG_of (by omega)) h1
      (fun y hy => by
        obtain ⟨k1, k2⟩ := l19_step hy
        exact ⟨k1 _ _ _ rfl, k2⟩)
      (fun hne => by simpa using guardK_sound hg19 hall hne)
  have L22 : ∀ i < r, ∃ ch, LoadHolds rd (σ (.n 27) * gen ^ i) 0 ch ∧ LoadHolds rd ch 128 0 :=
    loop_sound (f := "__loop21") (ps := [σ (.n 1), σ (.n 27)]) (ordG_of (by omega)) h1
      (fun y hy => by
        obtain ⟨k1, k2⟩ := l22_step hy
        exact ⟨k1 _ _ rfl, k2⟩)
      (fun hne => by simpa using guardK_sound hg22 hall hne)
  -- the columns
  have c20 := call_of_flat hallC hc20
  have c21 := call_of_flat hallC hc21
  simp only [List.map_cons, List.map_nil] at c20 c21
  rw [const_sound hc32 hat, word_one, ← pow_zero gen] at c20
  rw [const_sound hc33 hat, word_g64] at c21
  have h3' : σ (.n 3) = gen ^ 2 ^ L := h3
  have C1 : ∀ j < 64, C "da_verify_column__L1" (dvColArgs σ j) [] := fun j hj =>
    loop_fromC (C := C) (f := "__loop19") (N := gen ^ 64) (m := 64) (a := 0) (ordG_of (by omega)) rfl
      (fun y hy => by
        obtain ⟨k1, k2⟩ := col_loop_stepW hVm (by rw [coreProgram_length]; omega) l20_ok hy
        exact ⟨k1, by rw [← word_g64]; exact k2⟩) c20 j (Nat.zero_le _) hj
  have C0 : ∀ j, 64 ≤ j → j < 128 → C "da_verify_column__L0" (dvColArgs σ j) [] :=
    loop_fromC (C := C) (f := "__loop20") (N := gen ^ 128) (m := 128) (a := 64) (ordG_of (by omega))
      rfl
      (fun y hy => by
        obtain ⟨k1, k2⟩ := col_loop_stepW hVm (by rw [coreProgram_length]; omega) l21_ok hy
        exact ⟨k1, by rw [← word_g128]; exact k2⟩) c21
  have hr' : r < ordG := ordG_of (by omega)
  have hg' : 2 ^ L - r < ordG := ordG_of (by omega)
  let lv : ℕ → E := fun j => dvColV σ Vm j (.n 11)
  let node : ℕ → E := fun j => dvColV σ Vm j (.n 14)
  let c0 : ℕ → E := fun j => dvColV σ Vm j (.n 21)
  let c1 : ℕ → E := fun j => dvColV σ Vm j (.n 22)
  have hcol : ∀ j < 128, C "da_vector_cell" [σ (.n 17) * (gen ^ j) ^ 2] [lv j] ∧
      (∀ i < r, RowStepW C rd (dvRowV σ Vm i j) (lv j) (σ (.n 27)) (gen ^ j) (node j) (σ (.n 13))
        (decide (j < 64)) (gen ^ i)) ∧
      (∀ d < 2 ^ L - r, GapStepC rd (node j) (gen ^ r) (gen ^ d)) ∧
      (∃ k < 11, gen ^ L = ofK (Parameters.gpow k) ∧
        coreProgram.Rel rd (daLevelsName k) [node j] [c0 j, c1 j]) ∧
      LoadHolds rd (σ (.n 31) * (gen ^ j) ^ 2) 0 (c0 j) ∧
      LoadHolds rd (σ (.n 31) * (gen ^ j) ^ 2) 1 (c1 j) := by
    intro j hj
    by_cases hj64 : j < 64
    · have hcn : colNm j = "da_verify_column__L1" := by simp [colNm, hj64]
      have hrn : rowNm j = "__loop415" := by simp [rowNm, hj64]
      have k := col_stepW (store := true) hVm hle (by rw [coreProgram_length]; omega)
          (by rw [coreProgram_length]; omega) (by rw [coreProgram_length]; omega) col1_ok row417_ok
          gap418_ok hr' hg' h1 h4 (C1 j hj64)
      simp only [lv, node, c0, c1, dvRowV, dvColV, dvColArgs, hcn, hrn, ← h2, decide_eq_true hj64]
      exact k
    · have hcn : colNm j = "da_verify_column__L0" := by simp [colNm, hj64]
      have hrn : rowNm j = "__loop417" := by simp [rowNm, hj64]
      have k := col_stepW (store := false) hVm hle (by rw [coreProgram_length]; omega)
          (by rw [coreProgram_length]; omega) (by rw [coreProgram_length]; omega) col0_ok row419_ok
          gap420_ok hr' hg' h1 h4 (C0 j (by omega) hj)
      simp only [lv, node, c0, c1, dvRowV, dvColV, dvColArgs, hcn, hrn, ← h2, decide_eq_false hj64]
      exact k
  -- the columns' weights
  let ws : ℕ → List E := dvWs σ Vm
  have hws : ∀ j < 128, (ws j).length = 256 ∧
      (∀ k < 256, ∀ w, rd ((lv j).limb 0 * Parameters.gpow k) = some w → w = (ws j).getD k 0) ∧
      ReadsAt rd (σ (.n 17) * (gen ^ j) ^ 2) (digestCells (keccak256 ((ws j).flatMap Node.extensionElementBytes))) := by
    intro j hj
    obtain ⟨hp, hbv⟩ := body_ofV hVm find_da_vector_cell (hcol j hj).1
    obtain ⟨dg, hdg, hrv, hl, -, hfr, hrd⟩ := da_vector_cell_val hp hbv
    simp only [List.cons.injEq, and_true] at hdg hrv
    refine ⟨hl, fun k hk w hw => ?_, by rw [hdg]; exact hrd⟩
    rw [hrv] at hw
    exact hfr k hk w hw
  -- the cells
  let syms : ℕ → ℕ → List K := dvSyms σ Vm
  let s : ℕ → ℕ → E := fun i j => dvRowV σ Vm i j (.n 9)
  have hcell : ∀ i j, i < r → j < 128 → (syms i j).length = 256 ∧
      s i j = ∑ e ∈ Finset.range 256, (ws j).getD e 0 * ofK ((syms i j).getD e 0) ∧
      LoadHolds rd (node j * (gen ^ i) ^ 2) 0 (digestScalars (keccak256 ((syms i j).flatMap kBytes))).1 ∧
      LoadHolds rd (node j * (gen ^ i) ^ 2) 1 (digestScalars (keccak256 ((syms i j).flatMap kBytes))).2 ∧
      LoadHolds rd (memAt rd (σ (.n 27) * gen ^ i) 0 * gen ^ j) 1
        (memAt rd (memAt rd (σ (.n 27) * gen ^ i) 0 * gen ^ j) 0 + s i j) ∧
      (j < 64 → LoadHolds rd (memAt rd (σ (.n 13) * gen ^ i) 0 * (gen ^ j) ^ 2) 0
          (digestScalars (keccak256 ((syms i j).flatMap kBytes))).1 ∧
        LoadHolds rd (memAt rd (σ (.n 13) * gen ^ i) 0 * (gen ^ j) ^ 2) 1
          (digestScalars (keccak256 ((syms i j).flatMap kBytes))).2) := by
    intro i j hi hj
    obtain ⟨hc, -, hch, hn0, hn1, hst⟩ := (hcol j hj).2.1 i hi
    obtain ⟨hp, hbc⟩ := body_ofV hVm find_da_verify_cell hc
    obtain ⟨lv', hlv, hsl, hwrd, hwl, hrets⟩ := da_verify_cell_val hp hbc
    simp only [List.cons.injEq, and_true] at hlv
    rw [← hlv] at hwrd hwl hrets
    simp only [digestCells, List.cons_append, List.nil_append, List.cons.injEq, and_true] at hrets
    obtain ⟨e0, e1, es⟩ := hrets
    have e0' : dvRowV σ Vm i j (.n 7) = (digestScalars (keccak256 ((syms i j).flatMap kBytes))).1 :=
      e0
    have e1' : dvRowV σ Vm i j (.n 8) = (digestScalars (keccak256 ((syms i j).flatMap kBytes))).2 :=
      e1
    obtain ⟨-, hfr, -⟩ := hws j hj
    have hwc : ∀ e < 256, (memRun rd (lv j) 256).getD e 0 = (ws j).getD e 0 := by
      intro e he
      have := hwrd e (by unfold LeanDa.cellSymbols at hwl; omega)
      rw [List.getD_eq_getElem _ _ (by unfold LeanDa.cellSymbols at hwl; omega)]
      exact hfr e he _ this.2
    refine ⟨hsl, ?_, ?_, ?_, hch, fun h64 => ?_⟩
    · show dvRowV σ Vm i j (.n 9) = _
      rw [es, list_sum_range]
      exact Finset.sum_congr rfl fun e he => by rw [hwc e (Finset.mem_range.mp he)]; rfl
    · rw [← e0']; exact hn0
    · rw [← e1']; exact hn1
    · obtain ⟨k0, k1⟩ := hst (by simp [h64])
      rw [← e0', ← e1']; exact ⟨k0, k1⟩
  -- the witness's data, padded outside the run's ranges
  have hgr : gLog (σ (.n 1)) = r := by rw [h1, gLog_gen_pow (by omega)]
  let symsP : ℕ → ℕ → List K := dvSymsP σ Vm
  let wsP : ℕ → List E := dvWsP σ Vm
  have hsP : ∀ i j, i < r → j < 128 → symsP i j = syms i j := fun i j hi hj => by
    simp only [symsP, dvSymsP, hgr, hi, hj, and_self, ite_true]; rfl
  have hwP : ∀ j, j < 128 → wsP j = ws j := fun j hj => by
    simp only [wsP, dvWsP, hj, ite_true]; rfl
  have hsL : ∀ i j, (symsP i j).length = 256 := fun i j => by
    by_cases h : i < r ∧ j < 128
    · rw [hsP i j h.1 h.2]; exact (hcell i j h.1 h.2).1
    · show (dvSymsP σ Vm i j).length = 256
      unfold dvSymsP
      rw [hgr, ite_neg' h, List.length_replicate]
  have hwL : ∀ j, (wsP j).length = 256 := fun j => by
    by_cases h : j < 128
    · rw [hwP j h]; exact (hws j h).1
    · show (dvWsP σ Vm j).length = 256
      unfold dvWsP
      rw [ite_neg' h, List.length_replicate]
  -- the rows' sums
  have hdot : ∀ i < r, ∑ j ∈ Finset.range 128, ∑ e ∈ Finset.range 256,
      (wsP j).getD e 0 * ofK ((symsP i j).getD e 0) = 0 := by
    intro i hi
    obtain ⟨hb0, hz⟩ := L19 i hi
    have hm27 := memAt_of_load hb0
    have acc : ∀ j ≤ 128, LoadHolds rd (σ (.n 26) * (gen ^ i) ^ 129) j
        (∑ j' ∈ Finset.range j, s i j') := by
      intro j
      induction j with
      | zero => intro _; simpa using hz
      | succ j ih =>
        intro hj
        have ih' := ih (by omega)
        obtain ⟨-, -, -, -, hst, -⟩ := hcell i j hi (by omega)
        rw [hm27] at hst
        have e0 := memAt_of_load ((loadHolds_mul_gen_pow rd _ j 0 _).mpr ih')
        rw [e0] at hst
        rw [Finset.sum_range_succ]
        exact (loadHolds_mul_gen_pow rd _ j 1 _).mp hst
    obtain ⟨ch, hc1, hc2⟩ := L22 i hi
    rw [loadHolds_unique hc1 hb0] at hc2
    have hsum := loadHolds_unique (acc 128 le_rfl) hc2
    refine (Finset.sum_congr rfl fun j hj => ?_).trans hsum
    have hj' := Finset.mem_range.mp hj
    rw [(hcell i j hi hj').2.1, hsP i j hi hj', hwP j hj']
  -- the columns' roots
  have hcr : ∀ j < 128, (c0 j, c1 j) = digestScalars (mRoot L (cellLeaf r symsP j)) := by
    intro j hj
    obtain ⟨-, -, hgaps, ⟨k, hk, hkL, hrel⟩, -, -⟩ := hcol j hj
    refine levels_root_of hk hL hkL.symm hrel fun i hi => ?_
    by_cases hir : i < r
    · obtain ⟨-, -, hn0, hn1, -, -⟩ := hcell i j hir hj
      rw [shift2] at hn0 hn1
      simp only [cellLeaf, hir, ite_true, cellD, hsP i j hir hj]
      exact ⟨by simpa using hn0, hn1⟩
    · obtain ⟨g0, g1⟩ := hgaps (i - r) (by omega)
      rw [← pow_mul, shift, show r * 2 + 2 * (i - r) = 2 * i by omega] at g0 g1
      simp only [cellLeaf, hir, ite_false]
      exact ⟨by simpa using g0, g1⟩
  -- the column tree
  have hct : (σ (.n 37), σ (.n 38)) = digestScalars (mRoot 7 fun j => mRoot L (cellLeaf r symsP j)) := by
    have c7 := call_of_flat hall hc7
    simp only [List.map_cons, List.map_nil] at c7
    refine levels_root_of (k := 7) (L := 7) (by norm_num) (by norm_num) (gen_pow_eq_ofK 7).symm c7
      fun j hj => ?_
    obtain ⟨-, -, -, -, s0, s1⟩ := hcol j (by simpa using hj)
    rw [shift2] at s0 s1
    have e := hcr j (by simpa using hj)
    simp only [Prod.ext_iff] at e
    rw [← e.1, ← e.2]
    exact ⟨by simpa using s0, s1⟩
  -- the row tree
  have L23 : ∀ i < r, ∃ run, LoadHolds rd (σ (.n 13) * gen ^ i) 0 run ∧
      ReadsAt rd run (memRun rd run 128) ∧
      LoadHolds rd (σ (.n 41) * (gen ^ i) ^ 2) 0
        (digestScalars (keccak256 (cellsBytes (memRun rd run 128)))).1 ∧
      LoadHolds rd (σ (.n 41) * (gen ^ i) ^ 2) 1
        (digestScalars (keccak256 (cellsBytes (memRun rd run 128)))).2 :=
    loop_sound (f := "__loop22") (ps := [σ (.n 1), σ (.n 13), σ (.n 41)]) (ordG_of (by omega)) h1
      (fun y hy => by
        obtain ⟨k1, k2⟩ := l23_step hy
        exact ⟨k1 _ _ _ rfl, k2⟩)
      (fun hne => by simpa using guardK_sound hg23 hall hne)
  have L24 : ∀ d < 2 ^ L - r, GapRowC rd (σ (.n 41)) (σ (.n 1)) (gen ^ d) :=
    loop_sound (f := "__loop23") (ps := [σ (.n 4), σ (.n 41), σ (.n 1)]) hg' h4
      (fun y hy => by
        obtain ⟨k1, k2⟩ := l24_step hy
        exact ⟨k1 _ _ _ rfl, k2⟩)
      (fun hne => by simpa using guardK_sound hg24 hall hne)
  have hrowd : ∀ i < r, LoadHolds rd (σ (.n 41)) (2 * i) (digestScalars (rowD symsP i)).1 ∧
      LoadHolds rd (σ (.n 41)) (2 * i + 1) (digestScalars (rowD symsP i)).2 := by
    intro i hi
    obtain ⟨run, hrun, -, k0, k1⟩ := L23 i hi
    have hm13 := memAt_of_load hrun
    have hmem : memRun rd run 128 = (List.range 64).flatMap fun j => digestCells (cellD symsP i j) := by
      refine list_eq_getD (n := 128) (by simp) (by
        rw [length_flatMap_range _ 2 _ (fun j => rfl)]) fun c hc => ?_
      have hc' : c = 2 * (c / 2) + c % 2 := by omega
      rw [hc', flatMap_getD (fun j => digestCells (cellD symsP i j)) 2 (fun j => rfl) 0 64 (c / 2)
        (c % 2) (by omega) (by omega)]
      simp only [memRun, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (show 2 * (c / 2) + c % 2 < 128 by omega), Option.map_some,
        Option.getD_some]
      obtain ⟨-, -, -, -, -, hpre⟩ := hcell i (c / 2) hi (by omega)
      obtain ⟨p0, p1⟩ := hpre (by omega)
      rw [hm13, shift2] at p0 p1
      have e2 : cellD symsP i (c / 2) = keccak256 ((syms i (c / 2)).flatMap kBytes) := by
        rw [cellD, hsP i (c / 2) hi (by omega)]
      rcases (show c % 2 = 0 ∨ c % 2 = 1 by omega) with h | h
      · rw [h, memAt_of_load (by simpa using p0), e2]; rfl
      · rw [h, memAt_of_load p1, e2]; rfl
    have hbytes : cellsBytes (memRun rd run 128) =
        (List.range 64).flatMap fun j => digestBytes (cellD symsP i j) := by
      rw [hmem, cellsBytes, List.flatMap_assoc]
      refine List.flatMap_congr fun j _ => ?_
      rw [digestBytes_eq_cells, cellsBytes]; rfl
    rw [hbytes, shift2] at k0 k1
    exact ⟨by simpa [rowD] using k0, by simpa [rowD] using k1⟩
  have hrt : (σ (.n 48), σ (.n 49)) = digestScalars (mRoot L (rowLeaf r symsP)) := by
    obtain ⟨k, hk, hk2, hrel⟩ := dispatch_of_flat hall hdisp
    simp only [dlNames, List.length_map, List.length_range] at hk
    simp only [dlNames, List.getElem_map, List.getElem_range, List.map_cons, List.map_nil] at hrel
    refine levels_root_of hk hL (by rw [← hk2, h2]) hrel fun i hi => ?_
    by_cases hir : i < r
    · simp only [rowLeaf, hir, ite_true]
      exact hrowd i hir
    · obtain ⟨g0, g1⟩ := L24 (i - r) (by omega)
      rw [h1, ← pow_mul, shift, show r * 2 + 2 * (i - r) = 2 * i by omega] at g0 g1
      simp only [rowLeaf, hir, ite_false]
      exact ⟨by simpa using g0, g1⟩
  -- the root
  have hrootd : [σ (.n 993), σ (.n 994)] = digestCells (daRoot r L symsP) := by
    obtain ⟨hd, -⟩ := chain_final hroot rfl hat (pre := []) (n := 0) rfl
      (fun c => (cellsOfState_zero false c).symm)
    have hv : ((rootSpec (atomsIn dvP)).vals σ).take ((rootSpec (atomsIn dvP)).len / 16) =
        [σ (.n 48), σ (.n 49), σ (.n 37), σ (.n 38)] := by
      simp [rootSpec, ChainSpec.vals, srcVal]
    rw [hv, List.nil_append] at hd
    simp only [Prod.ext_iff] at hrt hct
    rw [hrt.1, hrt.2, hct.1, hct.2] at hd
    have hb : cellsBytes [(digestScalars (mRoot L (rowLeaf r symsP))).1,
        (digestScalars (mRoot L (rowLeaf r symsP))).2,
        (digestScalars (mRoot 7 fun j => mRoot L (cellLeaf r symsP j))).1,
        (digestScalars (mRoot 7 fun j => mRoot L (cellLeaf r symsP j))).2] =
        digestBytes (mRoot L (rowLeaf r symsP)) ++
          digestBytes (mRoot 7 fun j => mRoot L (cellLeaf r symsP j)) := by
      rw [digestBytes_eq_cells, digestBytes_eq_cells]
      simp [cellsBytes]
    rw [hb, ← daRoot] at hd
    rw [copy_sound hcp993 hat, copy_sound hcp994 hat, digestCells]
    simp only [Prod.ext_iff] at hd
    rw [← hd.1, ← hd.2]
  -- the vector's digest
  have hvd : [σ (.n 995), σ (.n 996)] = digestCells (daVd wsP) := by
    have hchk : (vdSpec (atomsIn dvP)).check (atomsIn dvP) = true :=
      ChainSpec.check_of_parts hvshape fun k hk => by
        rcases Nat.lt_or_ge k 8 with a | a
        · exact ChainSpec.partOk_sound vd_chain0_ok k (by omega) a
        rcases Nat.lt_or_ge k 16 with b | b
        · exact ChainSpec.partOk_sound vd_chain1_ok k a b
        rcases Nat.lt_or_ge k 24 with c | c
        · exact ChainSpec.partOk_sound vd_chain2_ok k b c
        · exact ChainSpec.partOk_sound vd_chain3_ok k c (by omega)
    obtain ⟨hd, -⟩ := chain_final hchk rfl hat (pre := []) (n := 0) rfl
      (fun c => (cellsOfState_zero false c).symm)
    have hr := loads_sound hld17 hat
    have hv0 : (((List.range 256).map fun i => some (V.n (69 + i))).map (srcVal σ)) =
        memRun rd (σ (.n 17)) 256 := by
      have := readsAt_memRun hr
      simpa using this
    have hv : ((vdSpec (atomsIn dvP)).vals σ).take ((vdSpec (atomsIn dvP)).len / 16) =
        memRun rd (σ (.n 17)) 256 := by
      rw [← hv0, show (vdSpec (atomsIn dvP)).len / 16 = 256 by simp [vdSpec]]
      simp [vdSpec, ChainSpec.vals]
    have hmem : memRun rd (σ (.n 17)) 256 =
        (List.range 128).flatMap fun j => digestCells (colD wsP j) := by
      refine list_eq_getD (n := 256) (by simp) (by
        rw [length_flatMap_range _ 2 _ (fun j => rfl)]) fun c hc => ?_
      have hc' : c = 2 * (c / 2) + c % 2 := by omega
      rw [hc', flatMap_getD (fun j => digestCells (colD wsP j)) 2 (fun j => rfl) 0 128 (c / 2)
        (c % 2) (by omega) (by omega)]
      simp only [memRun, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (show 2 * (c / 2) + c % 2 < 256 by omega), Option.map_some,
        Option.getD_some]
      obtain ⟨-, -, hrd⟩ := hws (c / 2) (by omega)
      have p0 := hrd 0 (by simp [digestCells])
      have p1 := hrd 1 (by simp [digestCells])
      rw [shift2] at p0 p1
      have e2 : colD wsP (c / 2) = keccak256 ((ws (c / 2)).flatMap Node.extensionElementBytes) := by
        rw [colD, hwP (c / 2) (by omega)]
      rcases (show c % 2 = 0 ∨ c % 2 = 1 by omega) with h | h
      · rw [h, memAt_of_load (by simpa using p0), e2]; rfl
      · rw [h, memAt_of_load p1, e2]; rfl
    have hbytes : cellsBytes ((List.range 128).flatMap fun j => digestCells (colD wsP j)) =
        (List.range 128).flatMap fun j => digestBytes (colD wsP j) := by
      rw [cellsBytes, List.flatMap_assoc]
      refine List.flatMap_congr fun j _ => ?_
      rw [digestBytes_eq_cells, cellsBytes]; rfl
    rw [hv, hmem, hbytes, List.nil_append, ← daVd] at hd
    rw [copy_sound hcp995 hat, copy_sound hcp996 hat, digestCells]
    simp only [Prod.ext_iff] at hd
    rw [← hd.1, ← hd.2]
  refine ⟨daRoot r L symsP, daVd wsP, ?_, ?_⟩
  · show (⟨daRows (gLog (σ (.n 1))) symsP, daVector wsP⟩ : LeanVM.Da.MatrixWitness).Opens _ _
    rw [hgr]
    exact opens_of hr1 (by unfold LeanDa.maxRows; exact hr) hnp.symm hrL hsL hwL hdot
  · rw [← hret, ← hrootd, ← hvd]
    rfl


end
end LeanVM.Guest.B1.Da
