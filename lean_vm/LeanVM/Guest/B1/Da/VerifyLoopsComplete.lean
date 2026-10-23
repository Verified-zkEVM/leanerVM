/-
  LeanVM.Guest.B1.Da.VerifyLoopsComplete

  `da_verify`'s small loops and column loops, completely.
-/

module

public import LeanVM.Guest.B1.Da.VerifyLoopsCChk
public import LeanVM.Guest.B1.Da.ColumnComplete

/-!
# `da_verify`'s loops, completely

The blocks of `__loop18` (a row's prefix base), `__loop19` (a row's running sum, its first word
zero), `__loop22` (word `128` of a row's sum zero) and `__loop24` (a padding row in the row tree),
each from the memory words it reads and writes; `colLoop_complete`: a column loop (`__loop20`,
`__loop21`) runs from `g^a` to its constant end `g^m` when every column holds.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

variable {rd : Reader}

set_option maxRecDepth 20000 in
/-- **A row's prefix base** (`__loop18`). -/
theorem l18_block {x N pb pd : E} (h : LoadHolds rd (pb * x) 0 (pd * x ^ 128)) :
    LoopBlock rd (coreProgram.getD 359 default) x N [pb, pd] := by
  obtain ⟨⟨hs, hl⟩, -⟩ := dvloops_shape
  refine ⟨Val.ofArgs [x, N, pb, pd, x ^ 2, x ^ 4, x ^ 8, x ^ 16, x ^ 32, x ^ 64, x ^ 128,
    pd * x ^ 128, pb * x, word 2 0 0, x * word 2 0 0, x * word 2 0 0 + N, word 2 0 0,
    x * word 2 0 0], by rw [params_of_shape hs hl]; rfl, ?_⟩
  rw [loopPre_of_body core359_body (by decide)]
  intro st hst
  simp only [l18Pre, sq7, stepAt, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hst
  rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals simp (config := {failIfUnchanged := false}) only [Stmt.Holds, Atom.Holds, ofArgs_n,
    List.getD_cons_succ, List.getD_cons_zero, and_true]
  all_goals try ring1
  exact h

set_option maxRecDepth 20000 in
/-- **A row's running sum** (`__loop19`): its pointer at `rowbase·x`, its first word zero. -/
theorem l19_block {x N acc rb : E} (h1 : LoadHolds rd (rb * x) 0 (acc * x ^ 129))
    (h2 : LoadHolds rd (acc * x ^ 129) 0 0) :
    LoopBlock rd (coreProgram.getD 360 default) x N [acc, rb] := by
  obtain ⟨-, ⟨hs, hl⟩, -⟩ := dvloops_shape
  have e : x ^ 129 = x ^ 128 * x := pow_succ x 128
  rw [e] at h1 h2
  rw [← word_zero] at h2
  refine ⟨Val.ofArgs [x, N, acc, rb, x ^ 2, x ^ 4, x ^ 8, x ^ 16, x ^ 32, x ^ 64, x ^ 128,
    x ^ 128 * x, acc * (x ^ 128 * x), rb * x, word 0 0 0, word 2 0 0, x * word 2 0 0,
    x * word 2 0 0 + N, word 2 0 0, x * word 2 0 0], by rw [params_of_shape hs hl]; rfl, ?_⟩
  rw [loopPre_of_body core360_body (by decide)]
  intro st hst
  simp only [l19Pre, sq7, stepAt, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hst
  rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  all_goals simp (config := {failIfUnchanged := false}) only [Stmt.Holds, Atom.Holds, ofArgs_n,
    List.getD_cons_succ, List.getD_cons_zero, and_true]
  all_goals try ring1
  exacts [h1, h2]

set_option maxRecDepth 20000 in
/-- **A row's sum ends at zero** (`__loop22`). -/
theorem l22_block {x N rb a : E} (h1 : LoadHolds rd (rb * x) 0 a) (h2 : LoadHolds rd a 128 0) :
    LoopBlock rd (coreProgram.getD 363 default) x N [rb] := by
  obtain ⟨-, -, ⟨hs, hl⟩, -⟩ := dvloops_shape
  refine ⟨Val.ofArgs [x, N, rb, rb * x, a, 0, word 0 0 0, word 2 0 0, x * word 2 0 0,
    x * word 2 0 0 + N, word 2 0 0, x * word 2 0 0], by rw [params_of_shape hs hl]; rfl, ?_⟩
  rw [loopPre_of_body core363_body (by decide)]
  intro st hst
  simp only [l22Pre, stepAt, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hst
  rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp (config := {failIfUnchanged := false}) only [Stmt.Holds, Atom.Holds, ofArgs_n,
    List.getD_cons_succ, List.getD_cons_zero, and_true]
  · exact h1
  · exact h2
  · rw [word_zero, zero_add]

set_option maxRecDepth 20000 in
/-- **A padding row in the row tree** (`__loop24`). -/
theorem l24_block {x N rt nb : E}
    (h0 : LoadHolds rd (rt * (nb * nb) * (x * x)) 0 (digestScalars daPadRowDigest).1)
    (h1 : LoadHolds rd (rt * (nb * nb) * (x * x)) 1 (digestScalars daPadRowDigest).2) :
    LoopBlock rd (coreProgram.getD 366 default) x N [rt, nb] := by
  obtain ⟨-, -, -, hs, hl⟩ := dvloops_shape
  have e := daPadRow_cells
  simp only [Prod.ext_iff] at e
  rw [← e.1] at h0
  rw [← e.2] at h1
  refine ⟨Val.ofArgs [x, N, rt, nb, nb * nb, rt * (nb * nb), x * x, rt * (nb * nb) * (x * x),
    word 4665334884586258498 1553031596697948144 0, word 7487832681283088925 14683883899259534590 0,
    word 2 0 0, x * word 2 0 0, x * word 2 0 0 + N, word 2 0 0, x * word 2 0 0],
    by rw [params_of_shape hs hl]; rfl, ?_⟩
  rw [loopPre_of_body core366_body (by decide)]
  intro st hst
  simp only [l24Pre, stepAt, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hst
  rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp (config := {failIfUnchanged := false}) only [Stmt.Holds, Atom.Holds, ofArgs_n,
    List.getD_cons_succ, List.getD_cons_zero, and_true]
  · exact h0
  · exact h1

set_option maxRecDepth 20000 in
/-- **A column loop runs** from `g^a` to its constant end `g^m`, every column holding. -/
theorem colLoop_complete {f col : String} {j endLo : ℕ} (hj : j < coreProgram.length)
    (hok : (colLoopOk (coreProgram.getD j default) col f endLo &&
      decide (coreProgram.indexOf? f = some j)) = true)
    {p1 p2 p3 p4 p5 p6 p7 p8 : E} {a m : ℕ} (hw : word endLo 0 0 = gen ^ m)
    (hcol : ∀ k, a ≤ k → k < m → coreProgram.Rel rd col [gen ^ k, p1, p2, p3, p4, p5, p6, p7, p8] []) :
    ∀ k, a ≤ k → k < m → coreProgram.Rel rd f [gen ^ k, p1, p2, p3, p4, p5, p6, p7, p8] [] := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hok, hidx⟩ := hok
  have hf := find_of_idx hidx hj
  unfold colLoopOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hparams, hbody⟩ := hok
  have key : ∀ t k, a ≤ k → k + 1 + t = m →
      coreProgram.Rel rd f [gen ^ k, p1, p2, p3, p4, p5, p6, p7, p8] [] := by
    intro t
    induction t with
    | zero => ?_
    | succ t ih => ?_
    all_goals
      intro k hak hk
      refine (rel_iff_sem hf _ _).mpr ⟨Val.ofArgs [gen ^ k, p1, p2, p3, p4, p5, p6, p7, p8,
        word 2 0 0, gen ^ k * word 2 0 0, word endLo 0 0, gen ^ k * word 2 0 0 + word endLo 0 0,
        word 2 0 0, gen ^ k * word 2 0 0], by rw [hparams]; rfl, ?_⟩
      rw [stmtsEqb_sound hbody]
      simp only [colLoopBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
        ofArgs_n, List.getD_cons_succ, List.getD_cons_zero, true_and, and_true,
        show (List.range 9).map V.n = [V.n 0, V.n 1, V.n 2, V.n 3, V.n 4, V.n 5, V.n 6, V.n 7, V.n 8]
          from rfl,
        show (List.range 8).map (fun k => V.n (k + 1)) =
          [V.n 1, V.n 2, V.n 3, V.n 4, V.n 5, V.n 6, V.n 7, V.n 8] from rfl]
      refine ⟨hcol k hak (by omega), ?_, fun hne => ?_⟩
      · rw [word_gen, gen_pow_mul_gen, hw]; exact gen_pow_add_isInK _ _
      rw [word_gen, gen_pow_mul_gen]
    · exfalso; apply hne
      rw [word_gen, gen_pow_mul_gen, hw, show k + 1 = m by omega]
      exact e_add_eq_zero_iff.mpr rfl
    · exact ih (k + 1) (by omega) (by omega)
  intro k hak hk
  exact key (m - k - 1) k hak (by omega)

end
end LeanVM.Guest.B1.Da
