/-
  LeanVM.Guest.B1.Eq.RsWords

  `rs_eq_run`'s words, by hand (it has no words certificate): on `count < 64` coordinates, its frame
  and `__loop5`'s `count / 2` iterations (or `__loop5`'s frame when it is skipped).
-/

module

public import LeanVM.Guest.B1.Eq.RsEqRun
public import LeanVM.Guest.B1.Tables.FlatAt
public import LeanVM.Guest.Budget.Kids
public import LeanVM.Guest.Memory.LoopPre

/-!
# `rs_eq_run` within its words

On a valid tree of `rs_eq_run` at arguments whose count is `g^c`, `c < 64` (`TotalLeOn`): its
body is flat (`rsBody = rsA ++ rsT ++ [ret]`, the `ite` on the odd tail of atoms only), so its
walk's events are its statements' and its only frame is `__loop5`'s (`rs_calls`), it allocates
nothing. Its first `41` atoms (`rsA`, events of the walk) hold, so `half_g = σ 33 = g^H` and
`g^(2H + O) = count_g = g^c` (as in `rs_eq_run_holds`): `H = c / 2`. With `__loop5`'s words per
iteration (`TotalLeOn … LoopPre`, as `Count.wSK_totalLeOn` gives it), `rs_totalLeOn` bounds the
tree by `fs "rs_eq_run" + max (fs "__loop5") (c / 2 · K6)`; `rs_totalLeOn34`, for `c ≤ 34`, by
`fs "rs_eq_run" + max (fs "__loop5") (17 · K6)`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `rs_eq_run`'s atoms before `__loop5`: the count's bits, `half_g`, `odd_g`, the check. -/
def rsA : List Stmt :=
  [.atom (.hint (.bitsExp (.n 3) 6 (.stack [.n 4, .n 5, .n 6, .n 7, .n 8, .n 9]))),
    .atom (.mul (.n 4) (.n 4) (.n 4)), .atom (.mul (.n 5) (.n 5) (.n 5)),
    .atom (.const (.n 10) (word 1 0 0)), .atom (.const (.n 11) (word 3 0 0)),
    .atom (.mul (.n 12) (.n 5) (.n 11)), .atom (.add (.n 13) (.n 10) (.n 12)),
    .atom (.mul (.n 6) (.n 6) (.n 6)), .atom (.const (.n 14) (word 1 0 0)),
    .atom (.const (.n 15) (word 5 0 0)), .atom (.mul (.n 16) (.n 6) (.n 15)),
    .atom (.add (.n 17) (.n 14) (.n 16)), .atom (.mul (.n 18) (.n 13) (.n 17)),
    .atom (.mul (.n 7) (.n 7) (.n 7)), .atom (.const (.n 19) (word 1 0 0)),
    .atom (.const (.n 20) (word 17 0 0)), .atom (.mul (.n 21) (.n 7) (.n 20)),
    .atom (.add (.n 22) (.n 19) (.n 21)), .atom (.mul (.n 23) (.n 18) (.n 22)),
    .atom (.mul (.n 8) (.n 8) (.n 8)), .atom (.const (.n 24) (word 1 0 0)),
    .atom (.const (.n 25) (word 257 0 0)), .atom (.mul (.n 26) (.n 8) (.n 25)),
    .atom (.add (.n 27) (.n 24) (.n 26)), .atom (.mul (.n 28) (.n 23) (.n 27)),
    .atom (.mul (.n 9) (.n 9) (.n 9)), .atom (.const (.n 29) (word 1 0 0)),
    .atom (.const (.n 30) (word 65537 0 0)), .atom (.mul (.n 31) (.n 9) (.n 30)),
    .atom (.add (.n 32) (.n 29) (.n 31)), .atom (.mul (.n 33) (.n 28) (.n 32)),
    .atom (.const (.n 34) (word 1 0 0)), .atom (.const (.n 35) (word 3 0 0)),
    .atom (.mul (.n 36) (.n 4) (.n 35)), .atom (.add (.n 37) (.n 34) (.n 36)),
    .atom (.mul (.n 38) (.n 33) (.n 33)), .atom (.mul (.n 39) (.n 38) (.n 37)),
    .atom (.assertEq (.n 39) (.n 3)), .atom (.const (.n 40) (word 1 0 0)),
    .atom (.add (.n 41) (.n 40) (.n 33)), .atom (.const (.n 42) (word 1 0 0))]

/-- `rs_eq_run`'s statements after them, before its `ret`. -/
def rsT : List Stmt := (rsBody.drop rsA.length).dropLast

theorem rsBody_split : rsBody = (rsA ++ rsT) ++ [.ret [.n 319]] := rfl

theorem rs_flat : (rsA ++ rsT).all Stmt.flat = true := by decide +kernel

theorem rsA_atoms : rsA.all (fun s ↦ match s with | .atom _ => true | _ => false) = true := by
  decide +kernel

theorem rs_noDispB : (rsA ++ rsT).all (fun s ↦ match s with | .dispatch .. => false | _ => true) =
    true := by decide +kernel

theorem rs_dispOk (σ : Val) : ∀ s ∈ rsA ++ rsT, DispOk σ s := fun s hs ↦ by
  have := List.all_eq_true.mp rs_noDispB s hs
  cases s <;> simp_all [DispOk]

theorem rs_callSF (σ : Val) : (rsA ++ rsT).filterMap (Stmt.callSF σ) =
    [(some (.n 41), "__loop5", [.n 42, .n 33, .n 1, .n 2, .n 0], [])] := rfl

theorem rs_allocSz : (rsA ++ rsT).filterMap Main.Stmt.allocSz = [] := rfl

theorem rs_walk (σ : Val) :
    walk σ (Fn.body Data.core5) = .ret ((rsA ++ rsT).flatMap (flEvs σ)) [.n 319] := by
  rw [core5_body, rsBody_split]
  exact walk_flat σ _ _ rs_flat (rs_dispOk σ)

theorem rs_calls (σ : Val) : calls ((rsA ++ rsT).flatMap (flEvs σ)) =
    [⟨"__loop5", [.n 42, .n 33, .n 1, .n 2, .n 0], [], decide (σ (.n 41) ≠ 0)⟩] := by
  rw [(flat_parts σ _ rs_flat).2.2.2.1, rs_callSF]
  rfl

/-- A block of atoms each of which holds holds. -/
theorem rs_holdsList_of_atoms {C : CallRel} {rd : Reader} {σ : Val} :
    ∀ (l : List Stmt), l.all (fun s ↦ match s with | .atom _ => true | _ => false) = true →
      (∀ a, Stmt.atom a ∈ l → a.Holds rd σ) → Stmt.HoldsList C rd σ l True (fun _ ↦ True)
  | [], _, _ => trivial
  | s :: l, hl, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hl
    match s, hl.1 with
    | .atom a, _ =>
      exact ⟨h a List.mem_cons_self,
        rs_holdsList_of_atoms l hl.2 fun b hb ↦ h b (List.mem_cons_of_mem _ hb)⟩

/-- **`half_g` and the count**: on a valuation satisfying `rsA`, `σ 33 = g^H` and
`σ 3 = g^(2H + O)`, `H < 32`, `O < 2`. -/
theorem rsA_vals {rd : Reader} {σ : Val}
    (h : Stmt.HoldsList (fun _ _ _ ↦ True) rd σ rsA True (fun _ ↦ True)) :
    ∃ H O : ℕ, H < 32 ∧ O < 2 ∧ σ (.n 33) = gen ^ H ∧ σ (.n 3) = gen ^ (2 * H + O) ∧
      σ (.n 41) = 1 + σ (.n 33) ∧ σ (.n 42) = 1 := by
  obtain ⟨w3, w5, w17, w257, w65537⟩ := rs_consts
  simp only [rsA, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and, and_true] at h
  obtain ⟨b0, b1, h10, h11, h12, h13, b2, h14, h15, h16, h17, h18, b3, h19, h20, h21,
    h22, h23, b4, h24, h25, h26, h27, h28, b5, h29, h30, h31, h32, h33, h34, h35, h36, h37,
    h38, h39, ha, h40, h41, h42⟩ := h
  have hbH : ∀ j < 5, σ (.n (5 + j)) * σ (.n (5 + j)) = σ (.n (5 + j)) := by
    intro j hj
    interval_cases j
    exacts [b1.symm, b2.symm, b3.symm, b4.symm, b5.symm]
  have hg : σ (.n 33) = ∏ j ∈ Finset.range 5, (1 + σ (.n (5 + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h33, h28, h23, h18, h13, h17, h22, h27, h32, h12, h16, h21, h26, h31, h10, h14, h19,
      h24, h29, h11, h15, h20, h25, h30, w3, w5, w17, w257, w65537, word_one]
  rw [prod_gen_pow_of_bool hbH] at hg
  have hH := bitsVal_lt (fun j => decide (σ (.n (5 + j)) = 1)) 5
  have hb0 : ∀ j < 1, σ (.n (4 + j)) * σ (.n (4 + j)) = σ (.n (4 + j)) := by
    intro j hj
    interval_cases j
    exact b0.symm
  have og : σ (.n 37) = ∏ j ∈ Finset.range 1, (1 + σ (.n (4 + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_one]
    rw [h37, h36, h34, h35, w3, word_one]
  rw [prod_gen_pow_of_bool hb0] at og
  have hO := bitsVal_lt (fun j => decide (σ (.n (4 + j)) = 1)) 1
  refine ⟨_, _, by simpa using hH, by simpa using hO, hg, ?_, by rw [h41, h40, word_one],
    by rw [h42, word_one]⟩
  rw [← e_add_eq_zero_iff.mp ha, h39, h38, hg, og, ← pow_add, ← pow_add, two_mul]

variable {fs : String → ℕ}

/-- **`rs_eq_run` is within its words**: on a count `g^c`, `c < 64`, its frame and `__loop5`'s
`c / 2` iterations of at most `K6` words (or `__loop5`'s frame when skipped). -/
theorem rs_totalLeOn {K6 : ℕ}
    (h6 : TotalLeOn coreProgram fs "__loop5" LoopPre fun a ↦ logG (a.getD 1 0) * K6) {c : ℕ}
    (hc : c < 64) :
    TotalLeOn coreProgram fs "rs_eq_run" (fun a ↦ a.getD 3 0 = gen ^ c)
      (fun _ ↦ fs "rs_eq_run" + max (fs "__loop5") (c / 2 * K6)) := by
  intro rd t args rets hname h3 hv hb
  cases t with
  | phantom => exact hv.elim
  | node f σ bufs ks =>
  simp only [Tree.name] at hname
  subst hname
  have hv' := hv
  obtain ⟨fn, hf, hpar, es, vs, hw, -, hes, -⟩ := hv'
  rw [find_rs_eq_run, Option.some.injEq] at hf
  subst hf
  rw [rs_walk, Out.ret.injEq] at hw
  obtain ⟨rfl, -⟩ := hw
  have hA : ∀ a, Stmt.atom a ∈ rsA → a.Holds rd σ := fun a ha ↦
    hes (.atom a) (List.mem_flatMap.mpr ⟨.atom a, List.mem_append_left _ ha,
      by rw [show flEvs σ (.atom a) = [.atom a] from rfl]; exact List.mem_singleton_self _⟩)
  obtain ⟨H, O, hH, hO, hg, hcg, h41, h42⟩ :=
    rsA_vals (rs_holdsList_of_atoms (C := fun _ _ _ ↦ True) rsA rsA_atoms hA)
  have h3' : σ (.n 3) = gen ^ c := by
    rw [← hpar] at h3
    exact h3
  have hHc : 2 * H + O = c := gen_pow_inj (by omega) (by omega) (hcg.symm.trans h3')
  have hc2 : c / 2 = H := by omega
  have hbufs : bufs = [] := by
    have h := hb.1
    rw [Tree.events, Tree.name, find_rs_eq_run] at h
    simp only [Tree.val, rs_walk] at h
    rw [(flat_parts σ _ rs_flat).2.1, rs_allocSz] at h
    simpa using h
  subst hbufs
  have htot := Budget.node_total_le fs (fun _ ↦ c / 2 * K6) [fun _ ↦ True]
    (cs := [⟨"__loop5", [.n 42, .n 33, .n 1, .n 2, .n 0], [], decide (σ (.n 41) ≠ 0)⟩]) hv hb
    (fun fn' es' vs' hf' hw' ↦ by
      rw [find_rs_eq_run, Option.some.injEq] at hf'
      subst hf'
      rw [rs_walk, Out.ret.injEq] at hw'
      rw [← hw'.1, rs_calls])
    (by simp) (by cases ks <;> simp [KidsT]) (fun c' Q hc' ht t' rets' htn htv htb _ ↦ ?_)
  · refine htot.trans ?_
    simp only [Budget.callsT, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    generalize c / 2 * K6 = X
    have h1 := le_max_left (fs "__loop5") X
    have h2 := le_max_right (fs "__loop5") X
    generalize max (fs "__loop5") X = M at h1 h2 ⊢
    split <;> omega
  · simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at hc'
    obtain ⟨rfl, -⟩ := hc'
    simp only [decide_eq_true_eq] at ht
    have hH0 : 0 < H := by
      rcases Nat.eq_zero_or_pos H with h0 | h0
      · exfalso
        apply ht
        rw [h41, hg, h0, pow_zero]
        exact e_add_self 1
      · exact h0
    have := h6 rd t' _ rets' htn (by
      simp only [List.map_cons, List.map_nil, h42, hg]
      exact loopPre_gen hH0 (by omega) _) htv htb
    simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero, hg,
      gen_pow_eq_ofK, logG_spec (show H < 2 ^ 64 - 1 by omega)] at this
    rw [hc2]
    exact this

/-- **`rs_eq_run` on at most `34` coordinates is within `fs "rs_eq_run" + max (fs "__loop5")
(17 · K6)` words** (`rs_totalLeOn`, `c / 2 ≤ 17`). -/
theorem rs_totalLeOn34 {K6 : ℕ}
    (h6 : TotalLeOn coreProgram fs "__loop5" LoopPre fun a ↦ logG (a.getD 1 0) * K6) :
    ∀ c ≤ 34, TotalLeOn coreProgram fs "rs_eq_run" (fun a ↦ a.getD 3 0 = gen ^ c)
      (fun _ ↦ fs "rs_eq_run" + max (fs "__loop5") (17 * K6)) := by
  intro c hc rd t args rets hn hp hv hb
  have h := rs_totalLeOn h6 (c := c) (by omega) rd t args rets hn hp hv hb
  refine h.trans (Nat.add_le_add_left (max_le_max le_rfl (Nat.mul_le_mul_right _ ?_)) _)
  omega

end
end LeanVM.Guest.B1
