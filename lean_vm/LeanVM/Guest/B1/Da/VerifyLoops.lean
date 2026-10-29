/-
  LeanVM.Guest.B1.Da.VerifyLoops

  What a run of each of `da_verify`'s loops establishes.
-/

module

public import LeanVM.Guest.B1.Da.VerifyChk
public import LeanVM.Guest.B1.Da.VerifyLoopsChk
public import LeanVM.Guest.B1.Da.VerifyL23Chk

/-!
# `da_verify`'s loops

`l18_step` (prefix bases), `l19_step` (running sums), `l22_step` (the sums' check), `l23_step`
(a row's digest), `l24_step` (padding rows), `col_loop_step` (`__loop19`, `__loop20`), and
`loop_from`: a `mul_range` loop started at `g^a` gives its body at every `g^j`, `a ≤ j < m`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

variable {rd : Reader}

/-- **A loop from `g^a`**: a run at `g^a` gives the body at every `g^j`, `a ≤ j < m`. -/
theorem loop_from {f : String} {ps : List E} {N : E} {m a : ℕ} {B : E → Prop}
    (hm : m < ordG) (hN : N = gen ^ m)
    (hstep : ∀ x, coreProgram.Rel rd f (x :: ps) [] →
      B x ∧ (x * gen + N ≠ 0 → coreProgram.Rel rd f (x * gen :: ps) []))
    (h : coreProgram.Rel rd f (gen ^ a :: ps) []) : ∀ j, a ≤ j → j < m → B (gen ^ j) := by
  have key : ∀ t k, k + t = m → coreProgram.Rel rd f (gen ^ k :: ps) [] →
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

/-- Unpacking a checked loop's parameters. -/
theorem loop_params {j : ℕ} {f : String} (hshape : loopShapeF (coreProgram.getD j default) f = true)
    {n : ℕ} (hlen : (coreProgram.getD j default).params.length = n) :
    (coreProgram.getD j default).params = (List.range n).map V.n := by
  have hs := hshape
  simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
  rw [hs.1.2, hlen]

theorem l18_step {x : E} {ps : List E} (h : coreProgram.Rel rd "__loop17" (x :: ps) []) :
    (∀ N pbT pd, ps = [N, pbT, pd] → LoadHolds rd (pbT * x) 0 (pd * x ^ 128)) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd "__loop17" (x * gen :: ps) []) := by
  have hok := l18_ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, l18Ok] at hok
  obtain ⟨⟨⟨⟨⟨hshape, hlen⟩, hm11⟩, hm12⟩, hl⟩, hidx⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ :=
    loop_stepF (find_of_idx hidx (by rw [coreProgram_length]; omega)) hshape h
  refine ⟨fun N pbT pd hN => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD 356 default).params = [V.n 0, V.n 1, V.n 2, V.n 3] := by
    rw [loop_params hshape hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, h3⟩ := hps
  have := load_sound hl hat
  rwa [isMul_sound hm12 hat, monoIs_sound hm11 hat, h2, h3, hx] at this

theorem l19_step {x : E} {ps : List E} (h : coreProgram.Rel rd "__loop18" (x :: ps) []) :
    (∀ N acc rb, ps = [N, acc, rb] →
      LoadHolds rd (rb * x) 0 (acc * x ^ 129) ∧ LoadHolds rd (acc * x ^ 129) 0 0) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd "__loop18" (x * gen :: ps) []) := by
  have hok := l19_ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, l19Ok] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hm12⟩, hm13⟩, hl12⟩, hc14⟩, hl14⟩, hidx⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ :=
    loop_stepF (find_of_idx hidx (by rw [coreProgram_length]; omega)) hshape h
  refine ⟨fun N acc rb hN => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD 357 default).params = [V.n 0, V.n 1, V.n 2, V.n 3] := by
    rw [loop_params hshape hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, h3⟩ := hps
  have p12 : σ (.n 12) = acc * x ^ 129 := by rw [monoIs_sound hm12 hat, h2, hx]
  have a := load_sound hl12 hat
  have b := load_sound hl14 hat
  rw [isMul_sound hm13 hat, h3, hx, p12] at a
  rw [p12, const_sound hc14 hat, word_zero] at b
  exact ⟨a, b⟩

theorem l22_step {x : E} {ps : List E} (h : coreProgram.Rel rd "__loop21" (x :: ps) []) :
    (∀ N rb, ps = [N, rb] → ∃ ch, LoadHolds rd (rb * x) 0 ch ∧ LoadHolds rd ch 128 0) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd "__loop21" (x * gen :: ps) []) := by
  have hok := l22_ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, l22Ok] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hm3⟩, hl4⟩, hl5⟩, hc6⟩, hae⟩, hidx⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ :=
    loop_stepF (find_of_idx hidx (by rw [coreProgram_length]; omega)) hshape h
  refine ⟨fun N rb hN => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD 360 default).params = [V.n 0, V.n 1, V.n 2] := by
    rw [loop_params hshape hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2⟩ := hps
  have a := load_sound hl4 hat
  have b := load_sound hl5 hat
  rw [isMul_sound hm3 hat, h2, hx] at a
  rw [assertEq_sound hae hat, const_sound hc6 hat, word_zero] at b
  exact ⟨_, a, b⟩

theorem l23_step {x : E} {ps : List E} (h : coreProgram.Rel rd "__loop22" (x :: ps) []) :
    (∀ N pbT rt, ps = [N, pbT, rt] → ∃ run, LoadHolds rd (pbT * x) 0 run ∧
      ReadsAt rd run (memRun rd run 128) ∧
      LoadHolds rd (rt * x ^ 2) 0 (digestScalars (keccak256 (cellsBytes (memRun rd run 128)))).1 ∧
      LoadHolds rd (rt * x ^ 2) 1 (digestScalars (keccak256 (cellsBytes (memRun rd run 128)))).2) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd "__loop22" (x * gen :: ps) []) := by
  have hok := l23_ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, l23Ok] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hm4⟩, hl5⟩, hlds⟩, hchk⟩, hm477⟩, hm478⟩, hd0⟩, hd1⟩, hidx⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ :=
    loop_stepF (find_of_idx hidx (by rw [coreProgram_length]; omega)) hshape h
  refine ⟨fun N pbT rt hN => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD 362 default).params = [V.n 0, V.n 1, V.n 2, V.n 3] := by
    rw [loop_params hshape hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, h3⟩ := hps
  have a := load_sound hl5 hat
  rw [isMul_sound hm4 hat, h2, hx] at a
  have hr := loads_sound hlds hat
  have hv : (((List.range 128).map fun i => some (V.n (6 + i))).map (srcVal σ)) =
      memRun rd (σ (.n 5)) 128 := by
    have := readsAt_memRun hr
    simpa using this
  rw [hv] at hr
  obtain ⟨hd, -⟩ := chain_final hchk rfl hat (pre := []) (n := 0) rfl
    (fun c => (cellsOfState_zero false c).symm)
  have hv' : ((rowSpec (atomsIn (loopPre (coreProgram.getD 362 default)))).vals σ).take
      ((rowSpec (atomsIn (loopPre (coreProgram.getD 362 default)))).len / 16) =
      memRun rd (σ (.n 5)) 128 := by
    rw [← hv, show (rowSpec (atomsIn (loopPre (coreProgram.getD 362 default)))).len / 16 = 128
      by simp [rowSpec]]
    simp [rowSpec, ChainSpec.vals]
  rw [hv', List.nil_append] at hd
  have p478 : σ (.n 478) = rt * x ^ 2 := by
    rw [isMul_sound hm478 hat, isMul_sound hm477 hat, h3, hx, sq]
  refine ⟨σ (.n 5), a, hr, ?_, ?_⟩
  · have := load_sound hd0 hat
    rw [show ((rowSpec (atomsIn (loopPre (coreProgram.getD 362 default)))).outV
      ((rowSpec (atomsIn (loopPre (coreProgram.getD 362 default)))).nb - 1) 0) =
      ((rowSpec (atomsIn (loopPre (coreProgram.getD 362 default)))).outV
      ((rowSpec (atomsIn (loopPre (coreProgram.getD 362 default)))).nb - 1) ((0 : Fin 13) : ℕ))
      from rfl, p478] at this
    rw [← hd]; exact this
  · have := load_sound hd1 hat
    rw [show ((rowSpec (atomsIn (loopPre (coreProgram.getD 362 default)))).outV
      ((rowSpec (atomsIn (loopPre (coreProgram.getD 362 default)))).nb - 1) 1) =
      ((rowSpec (atomsIn (loopPre (coreProgram.getD 362 default)))).outV
      ((rowSpec (atomsIn (loopPre (coreProgram.getD 362 default)))).nb - 1) ((1 : Fin 13) : ℕ))
      from rfl, p478] at this
    rw [← hd]; exact this

/-- **A padding row**: the padding row's two cells at node `n_blob + x`. -/
def GapRowC (rd : Reader) (node nb : E) (x : E) : Prop :=
  LoadHolds rd (node * nb ^ 2 * x ^ 2) 0 (digestScalars daPadRowDigest).1 ∧
    LoadHolds rd (node * nb ^ 2 * x ^ 2) 1 (digestScalars daPadRowDigest).2

theorem l24_step {x : E} {ps : List E} (h : coreProgram.Rel rd "__loop23" (x :: ps) []) :
    (∀ N node nb, ps = [N, node, nb] → GapRowC rd node nb x) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd "__loop23" (x * gen :: ps) []) := by
  have hok := l24_ok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hok, hidx⟩ := hok
  unfold gapOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hm4⟩, hm5⟩, hm6⟩, hm7⟩, hc8⟩, hl8⟩, hc9⟩, hl9⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ :=
    loop_stepF (find_of_idx hidx (by rw [coreProgram_length]; omega)) hshape h
  refine ⟨fun N node nb hN => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD 363 default).params = [V.n 0, V.n 1, V.n 2, V.n 3] := by
    rw [loop_params hshape hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, h3⟩ := hps
  have p7 : σ (.n 7) = node * nb ^ 2 * x ^ 2 := by
    rw [isMul_sound hm7 hat, isMul_sound hm5 hat, isMul_sound hm4 hat, isMul_sound hm6 hat, h2, h3,
      hx, sq, sq]
  have l8 := load_sound hl8 hat
  have l9 := load_sound hl9 hat
  rw [p7, const_sound hc8 hat] at l8
  rw [p7, const_sound hc9 hat] at l9
  unfold GapRowC
  rw [← daPadRow_cells]
  exact ⟨l8, l9⟩

/-- **A column loop**: the column at `x`, then the loop at `x·g` until `g^e`. -/
theorem col_loop_step {f col : String} {j endLo : ℕ} (hj : j < coreProgram.length)
    (hok : (colLoopOk (coreProgram.getD j default) col f endLo &&
      decide (coreProgram.indexOf? f = some j)) = true) {x : E} {ps : List E}
    (h : coreProgram.Rel rd f (x :: ps) []) :
    coreProgram.Rel rd col (x :: ps) [] ∧
      (x * gen + word endLo 0 0 ≠ 0 → coreProgram.Rel rd f (x * gen :: ps) []) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hok, hidx⟩ := hok
  unfold colLoopOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hparams, hbody⟩ := hok
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem (find_of_idx hidx hj) _ _).mp h
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

end
end LeanVM.Guest.B1.Da
