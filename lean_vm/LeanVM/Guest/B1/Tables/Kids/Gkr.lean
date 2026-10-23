/-
  LeanVM.Guest.B1.Tables.Kids.Gkr

  `verify_bus_gkr`'s rounds (`gkr_rounds__L1`, `gkr_rounds__L2`, `__loop29`) load from any region
  holding their records, points and the round polynomials at the records' cursors.
-/

module

public import LeanVM.Guest.B1.Tables.Kids.Loop8
public import LeanVM.Guest.B1.Gkr.Loop29

/-!
# The GKR rounds, loading from a region

A round record holds its fields `862` words apart (`gkCap`), its cursor at `5·862 = 4310`.

* `gkr_rounds_relIn`: `gkr_rounds__L{n}`, `n ∈ {1, 2}`, on a record `rec` (`5173 + n` words) and
  a point `pt` (`42 + n`), reads the `4n` words at the record's cursor; a kernel check
  (`grCheck`) of its body: no call, loads through `rec`, `pt` and the cursor only.
* `loop29_relIn`: iteration `k < K` of `__loop29` (four rounds) on the record `head·g^(4k)`
  (`5177` words) and the point `ptrow·g^(4k)` (`46`), reading `16` words at the record's cursor.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- `gkr_rounds__L{n}`'s pointers and their runs. -/
def grTbl (n : ℕ) : List (ℕ × ℕ) := [(0, 5173 + n), (1, 42 + n), (7, 4 * n)]

/-- `gkr_rounds__L{n}`'s body, checked: two parameters, a `ret []` last, no call, its loads
through `grTbl n`, its cursor read at `rec·g^4310` into `.n 7`. -/
noncomputable def grCheck (n : ℕ) : Bool :=
  match coreProgram.find? (lName "gkr_rounds" n) with
  | some fn => decide (fn.params = [.n 0, .n 1]) &&
      (match fn.body.getLast? with
        | some (.ret vs) => decide (vs = [])
        | _ => false) &&
      fn.body.dropLast.all Stmt.flat && fn.body.dropLast.all seqB &&
      fn.body.dropLast.all noCallSB && fn.body.dropLast.all (loadsViaB (grTbl n)) &&
      fn.body.dropLast.any fun s ↦ tbStmtsEqb [s] [.atom (.load (.n 7) (.n 0) 4310)]
  | none => false

theorem gr_check : grCheck 1 = true ∧ grCheck 2 = true := ⟨by decide +kernel, by decide +kernel⟩

/-- **`gkr_rounds__L{n}` loads from `R`**, `n ∈ {1, 2}`. -/
theorem gkr_rounds_relIn {n : ℕ} (hn : n = 1 ∨ n = 2) {rd : Reader} {R : ℕ → Prop}
    {rec pt : E} {rets : List E} (hrec : PtrIn R rec (5173 + n)) (hpt : PtrIn R pt (42 + n))
    (hcur : ∀ c, LoadHolds rd rec 4310 c → PtrIn R c (4 * n))
    (h : coreProgram.Rel rd (lName "gkr_rounds" n) [rec, pt] rets) :
    coreProgram.RelIn rd R (lName "gkr_rounds" n) [rec, pt] rets := by
  have hck : grCheck n = true := by rcases hn with rfl | rfl; exacts [gr_check.1, gr_check.2]
  unfold grCheck at hck
  split at hck
  swap
  · exact absurd hck (by simp)
  rename_i fn hf
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at hck
  obtain ⟨⟨⟨⟨⟨⟨hp, hlast⟩, hfl⟩, hseq⟩, hnc⟩, hld⟩, s7, hs7, hs7e⟩ := hck
  have hb : fn.body = fn.body.dropLast ++ [.ret []] := by
    split at hlast
    · rename_i vs hl
      simp only [decide_eq_true_eq] at hlast
      subst hlast
      exact (List.dropLast_append_getLast? _ hl).symm
    · exact absurd hlast (by simp)
  have hs7' : s7 = .atom (.load (.n 7) (.n 0) 4310) := by
    have := tbStmtsEqb_sound hs7e; simpa using this
  subst hs7'
  have hnl : fn.body.dropLast.all noLoadIte = true := List.all_eq_true.mpr fun s hs ↦
    noLoadIte_of_seqB (List.all_eq_true.mp hseq s hs)
  refine relIn_of_flatRel (hnl := hnl) hf hb hfl h fun σ hpar hh ↦ ?_
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
  obtain ⟨p0, p1⟩ := hpar
  rw [hb, holdsList_append] at hh
  have h7 := holds_of_mem_seq _ hseq hh _ hs7
  simp only [Fwd.SHolds, Atom.Holds] at h7
  refine ⟨fun s hs ↦ dispOk_of_noCall (List.all_eq_true.mp hnc s hs),
    loads_via hld fun pb hpb ↦ ?_, fun c hc _ ↦ ?_⟩
  · simp only [grTbl, List.mem_cons, List.not_mem_nil, or_false] at hpb
    rcases hpb with rfl | rfl | rfl
    · rw [p0]; exact hrec
    · rw [p1]; exact hpt
    · rw [p0] at h7; exact hcur _ h7
  · exfalso
    obtain ⟨t, ht, -⟩ := List.mem_map.mp hc
    obtain ⟨s, hs, hst⟩ := List.mem_filterMap.mp ht
    rw [callSF_none (List.all_eq_true.mp hnc s hs)] at hst
    exact absurd hst (by simp)

/-! ## `__loop29` -/

/-- `__loop29`'s statements before its `ret`. -/
def l29Pre : List Stmt := l29Body.dropLast

theorem l29Body_pre_eq : l29Body = l29Pre ++ [.ret []] :=
  (List.dropLast_append_getLast? (l := l29Body) (.ret []) rfl).symm

theorem l29_flat : l29Pre.all Stmt.flat = true := by decide +kernel

theorem l29_noDisp : l29Pre.all noDispB = true := by decide +kernel

theorem l29_seq : l29Pre.all seqB = true := by decide +kernel

theorem l29_loads : l29Pre.all (loadsViaB [(6, 5177), (7, 46), (13, 16)]) = true := by
  decide +kernel

theorem l29_calls : l29Pre.filterMap Main.Stmt.callS =
    [(some (.n 315), "__loop29", [.n 317, .n 1, .n 2, .n 3], [])] := by decide +kernel

/-- **`__loop29` loads from `R`**, every iteration `k < K`. -/
theorem loop29_relIn {rd : Reader} {R : ℕ → Prop} {K : ℕ}
    {head ptrow : E} (hh : PtrIn R head (4 * K + 5173)) (hp : PtrIn R ptrow (4 * K + 42))
    (hcur : ∀ k < K, ∀ c, LoadHolds rd (head * gen ^ (4 * k)) 4310 c → PtrIn R c 16) :
    ∀ d k, k < K → coreProgram.relN rd d "__loop29" [gen ^ k, gen ^ K, head, ptrow] [] →
      coreProgram.RelIn rd R "__loop29" [gen ^ k, gen ^ K, head, ptrow] [] := by
  intro d
  induction d with
  | zero => intro k _ h; exact h.elim
  | succ d ih =>
    intro k hk h
    obtain ⟨fn, hf, hsem⟩ := h
    obtain ⟨fn', hf', hpm, hb⟩ := l29Found
    rw [hf] at hf'
    obtain rfl := Option.some.inj hf'
    refine relIn_of_flat hf (by rw [hb, l29Body_pre_eq]) l29_flat hsem fun σ hpar hhl ↦ ?_
    rw [hpm] at hpar
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
    obtain ⟨p0, p1, p2, p3⟩ := hpar
    rw [hb, l29Body_pre_eq, holdsList_append] at hhl
    have hS := holds_of_mem_seq _ l29_seq hhl
    have m4 := hS _ (mem_of_slice (i := 0) (s := .atom (.mul (.n 4) (.n 0) (.n 0))) (by decide +kernel))
    have m5 := hS _ (mem_of_slice (i := 1) (s := .atom (.mul (.n 5) (.n 4) (.n 4))) (by decide +kernel))
    have m6 := hS _ (mem_of_slice (i := 2) (s := .atom (.mul (.n 6) (.n 2) (.n 5))) (by decide +kernel))
    have m7 := hS _ (mem_of_slice (i := 3) (s := .atom (.mul (.n 7) (.n 3) (.n 5))) (by decide +kernel))
    have l13 := hS _ (mem_of_slice (i := 9) (s := .atom (.load (.n 13) (.n 6) 4310))
      (by decide +kernel))
    have c313 := hS _ (mem_of_slice (i := 260) (s := .atom (.const (.n 313) (word 2 0 0)))
      (by decide +kernel))
    have m314 := hS _ (mem_of_slice (i := 261) (s := .atom (.mul (.n 314) (.n 0) (.n 313)))
      (by decide +kernel))
    have a315 := hS _ (mem_of_slice (i := 262) (s := .atom (.add (.n 315) (.n 314) (.n 1)))
      (by decide +kernel))
    have c316 := hS _ (mem_of_slice (i := 263) (s := .atom (.const (.n 316) (word 2 0 0)))
      (by decide +kernel))
    have m317 := hS _ (mem_of_slice (i := 264) (s := .atom (.mul (.n 317) (.n 0) (.n 316)))
      (by decide +kernel))
    have hci := hS _ (mem_of_slice (i := 265)
      (s := .callIf (.n 315) "__loop29" [.n 317, .n 1, .n 2, .n 3]) (by decide +kernel))
    simp only [Fwd.SHolds, Atom.Holds] at m4 m5 m6 m7 l13 c313 m314 a315 c316 m317 hci
    rw [tb_word_gen] at c313 c316
    have e6 : σ (.n 6) = head * gen ^ (4 * k) := by rw [m6, m5, m4, p0, p2]; ring
    have e7 : σ (.n 7) = ptrow * gen ^ (4 * k) := by rw [m7, m5, m4, p0, p3]; ring
    refine ⟨fun s hs ↦ dispOk_of_noDisp (List.all_eq_true.mp l29_noDisp s hs),
      loads_via l29_loads fun pb hpb ↦ ?_, fun c hc ht ↦ ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hpb
      rcases hpb with rfl | rfl | rfl
      · rw [e6]; exact ptrIn_mul (ptrIn_mono hh (by omega))
      · rw [e7]; exact ptrIn_mul (ptrIn_mono hp (by omega))
      · rw [e6] at l13; exact hcur k hk _ l13
    · rw [filterMap_callSF l29_noDisp, l29_calls] at hc
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
      subst hc
      simp only [Main.mkCall, decide_eq_true_eq] at ht ⊢
      have e317 : σ (.n 317) = gen ^ (k + 1) := by rw [m317, c316, p0, pow_succ]
      have e315 : σ (.n 315) = gen ^ (k + 1) + gen ^ K := by rw [a315, m314, c313, p0, p1, pow_succ]
      have hk1 : k + 1 < K := by
        rcases Nat.lt_or_ge (k + 1) K with h' | h'
        · exact h'
        · exfalso
          apply ht
          rw [e315, show k + 1 = K by omega, e_add_eq_zero_iff]
      have hrel := hci.2 ht
      simp only [List.map_cons, List.map_nil, e317, p1, p2, p3] at hrel ⊢
      exact ih (k + 1) hk1 hrel

end
end LeanVM.Guest.B1.Tables
