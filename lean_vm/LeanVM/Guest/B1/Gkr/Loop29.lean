/-
  LeanVM.Guest.B1.Gkr.Loop29

  `verify_bus_gkr`'s inner loop `__loop27`: four GKR rounds an iteration, from one round record
  to the record four on.
-/

module

public import LeanVM.Guest.B1.Gkr.Rounds

/-!
# `__loop27` (G:1704-1734)

`for x4 in mul_range(1, half)` in a layer of `verify_bus_gkr`: the record at
`rd = rounds·pos·x4^4`, the point row `pt = point_row·x4^4`, four rounds (`gkRoundT`, from values
`15 + 74q`), and the record at `rd·g^4` written. `l29_step`: an iteration is
`TbGkrRoundsOut 4` from its record; `l29_holds`: the loop from `g^0` to `half = g^h` is
`TbGkrRoundsOut (4h)` from the first record.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- Round `q`'s first value. -/
def l29B (q : ℕ) : ℕ := 15 + 74 * q

/-- Round `q`'s claim. -/
def l29Claim (q : ℕ) : ℕ := if q = 0 then 14 else l29B (q - 1) + 73

/-- Round `q`'s capacity. -/
def l29Cap (q : ℕ) : List V :=
  if q = 0 then [.n 8, .n 9, .n 10, .n 11, .n 12]
  else (List.range 5).map fun k ↦ .n (l29B (q - 1) + 48 + k)

/-- `__loop27`'s body. -/
def l29Body : List Stmt :=
  [.atom (.mul (.n 4) (.n 0) (.n 0)), .atom (.mul (.n 5) (.n 4) (.n 4)),
    .atom (.mul (.n 6) (.n 2) (.n 5)), .atom (.mul (.n 7) (.n 3) (.n 5)),
    .atom (.load (.n 8) (.n 6) 0), .atom (.load (.n 9) (.n 6) 862),
    .atom (.load (.n 10) (.n 6) 1724), .atom (.load (.n 11) (.n 6) 2586),
    .atom (.load (.n 12) (.n 6) 3448), .atom (.load (.n 13) (.n 6) 4310),
    .atom (.load (.n 14) (.n 6) 5172)] ++
  ((List.range 4).map fun q ↦ gkRoundT (l29B q) q (.n 13) (.n 7) (.n (l29Claim q)) (l29Cap q)).flatten ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (285 + k)) (.n 6) (4 + 862 * k))) ++
  [.atom (.const (.n 311) (word 65536 0 0)), .atom (.mul (.n 312) (.n 13) (.n 311)),
    .atom (.load (.n 312) (.n 6) 4314), .atom (.load (.n 310) (.n 6) 5176),
    .atom (.const (.n 313) (word 2 0 0)), .atom (.mul (.n 314) (.n 0) (.n 313)),
    .atom (.add (.n 315) (.n 314) (.n 1)), .atom (.const (.n 316) (word 2 0 0)),
    .atom (.mul (.n 317) (.n 0) (.n 316)),
    .callIf (.n 315) "__loop27" [.n 317, .n 1, .n 2, .n 3], .ret []]

noncomputable def l29Check : Bool :=
  match coreProgram.find? "__loop27" with
  | some fn => decide (fn.params = [.n 0, .n 1, .n 2, .n 3]) && tbStmtsEqb fn.body l29Body
  | none => false

theorem l29Check_eq : l29Check = true := by decide +kernel

theorem l29Found : ∃ fn : Fn, coreProgram.find? "__loop27" = some fn ∧
    fn.params = [.n 0, .n 1, .n 2, .n 3] ∧ fn.body = l29Body := by
  have h := l29Check_eq
  unfold l29Check at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, tbStmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

/-- The sponge after a squeeze has nothing waiting. -/
theorem tb_squeeze_eta (s : Fs) : s.squeeze.2 = ⟨s.squeeze.2.cap, []⟩ := rfl

/-- One round of `gkrRun`, from what the guest's round gives. -/
theorem tb_gkrRun_cons_of {c : List E} {cs : List (List E)} {e : E} {es : List E} {claim ch : E}
    {cap cap' : List E} (hch : ch = ((⟨cap, []⟩ : Fs).absorbAll c dsObserve).squeeze.1)
    (hcap : cap' = ((⟨cap, []⟩ : Fs).absorbAll c dsObserve).squeeze.2.cap) :
    gkrRun (c :: cs) (e :: es) claim ⟨cap, []⟩ =
      (ch :: (gkrRun cs es (polyEval ((claim + e * sumE c) :: c) ch) ⟨cap', []⟩).1,
        (gkrRun cs es (polyEval ((claim + e * sumE c) :: c) ch) ⟨cap', []⟩).2) := by
  subst hch hcap
  rfl

section Sem

variable {rd : Reader}

theorem l29_round_cap (q : ℕ) (σ : Val) :
    (l29Cap (q + 1)).map σ = (List.range 5).map fun k ↦ σ (.n (l29B q + 48 + k)) := by
  simp [l29Cap]

/-- **An iteration of `__loop27`**: four rounds from the record at `head·x^4`. -/
theorem l29_step {N head ptrow : E} (d : ℕ) (x : E)
    (h : coreProgram.relN rd (d + 1) "__loop27" (x :: [N, head, ptrow]) []) :
    TbGkrRoundsOut 4 rd (head * x ^ 4) (ptrow * x ^ 4) ∧
      (x * gen + N ≠ 0 → coreProgram.relN rd d "__loop27" (x * gen :: [N, head, ptrow]) []) := by
  obtain ⟨fn, hf, σ, hpar, hbody⟩ := h
  obtain ⟨fn', hf', hp, hb⟩ := l29Found
  rw [hf] at hf'
  obtain rfl := Option.some.inj hf'
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hpar
  have nR := tb_noRetList_flatten_range 4 (fun q ↦ gkRoundT (l29B q) q (.n 13) (.n 7)
    (.n (l29Claim q)) (l29Cap q)) (fun q => gkRoundT_noRet _ _ _ _ _ _)
  rw [hb, l29Body, holdsList_append, holdsList_noRet _ (by
      simp only [tb_noRetList_append, nR, tb_noRetList_mapAtoms]; rfl),
    tb_holdsList_append_noRet (by simp only [tb_noRetList_append, nR]; rfl),
    tb_holdsList_append_noRet (by rfl), tb_holdsList_flatten_range _ _ (fun q =>
      gkRoundT_noRet _ _ _ _ _ _), tb_holdsList_mapAtoms] at hbody
  obtain ⟨⟨⟨hh, hrounds⟩, hst⟩, htl⟩ := hbody
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, List.map_cons, List.map_nil] at hh htl
  obtain ⟨h4, h5, h6, h7, l8, l9, l10, l11, l12, l13, l14⟩ := hh
  obtain ⟨c311, m312, s312, s310, c313, m314, a315, c316, m317, -, hnext⟩ := htl
  refine ⟨?_, fun hne => ?_⟩
  swap
  · have := hnext (by rw [a315, m314, c313, tb_word_gen]; exact hne)
    rw [m317, c316, tb_word_gen] at this
    exact this
  have R := fun q (hq : q < 4) => holds_gkRound (hrounds q hq)
  obtain ⟨can0, xs0, hx0, hr0, hc0, hcap0, hs0, e0, he0, hcl0⟩ := R 0 (by norm_num)
  obtain ⟨-, xs1, hx1, hr1, hc1, hcap1, hs1, e1, he1, hcl1⟩ := R 1 (by norm_num)
  obtain ⟨-, xs2, hx2, hr2, hc2, hcap2, hs2, e2, he2, hcl2⟩ := R 2 (by norm_num)
  obtain ⟨-, xs3, hx3, hr3, hc3, hcap3, hs3, e3, he3, hcl3⟩ := R 3 (by norm_num)
  rw [l29_round_cap 0 σ] at hc1 hcap1
  rw [l29_round_cap 1 σ] at hc2 hcap2
  rw [l29_round_cap 2 σ] at hc3 hcap3
  have ecap0 : (l29Cap 0).map σ = [σ (.n 8), σ (.n 9), σ (.n 10), σ (.n 11), σ (.n 12)] := rfl
  rw [ecap0] at can0 hc0 hcap0
  simp only [l29B, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd,
    Nat.reduceMul] at hc0 hc1 hc2 hc3 hcap0 hcap1 hcap2 hcap3
  simp only [l29B, l29Claim, Nat.mul_zero, Nat.add_zero, Nat.mul_one, ↓reduceIte, Nat.reduceAdd,
    Nat.reduceMul, Nat.reduceSub, Nat.reduceEqDiff] at hs0 hs1 hs2 hs3 hcl0 hcl1 hcl2 hcl3
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at hr0 hr1 hr2 hr3
  -- the run
  have hrun : gkrRun [xs0, xs1, xs2, xs3] [e0, e1, e2, e3] (σ (.n 14))
      ⟨[σ (.n 8), σ (.n 9), σ (.n 10), σ (.n 11), σ (.n 12)], []⟩ =
      ([σ (.n 74), σ (.n 148), σ (.n 222), σ (.n 296)], σ (.n 310),
        ⟨(List.range 5).map fun k ↦ σ (.n (285 + k)), []⟩) := by
    rw [tb_gkrRun_cons_of hc0 hcap0, ← hcl0, tb_gkrRun_cons_of hc1 hcap1, ← hcl1,
      tb_gkrRun_cons_of hc2 hcap2, ← hcl2, tb_gkrRun_cons_of hc3 hcap3, ← hcl3]
    simp [gkrRun]
  have hx4 : ∀ l : List E, l.length = 4 → ∃ a b c d, l = [a, b, c, d] := fun l hl => by
    match l, hl with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  obtain ⟨a0, b0, c0, d0, rfl⟩ := hx4 xs0 hx0
  obtain ⟨a1, b1, c1, d1, rfl⟩ := hx4 xs1 hx1
  obtain ⟨a2, b2, c2, d2, rfl⟩ := hx4 xs2 hx2
  obtain ⟨a3, b3, c3, d3, rfl⟩ := hx4 xs3 hx3
  have e6 : σ (.n 6) = σ (.n 2) * σ (.n 0) ^ 4 := by rw [h6, h5, h4]; ring
  have e7 : σ (.n 7) = σ (.n 3) * σ (.n 0) ^ 4 := by rw [h7, h5, h4]; ring
  rw [← e6, ← e7]
  refine ⟨[σ (.n 8), σ (.n 9), σ (.n 10), σ (.n 11), σ (.n 12)], σ (.n 13), σ (.n 14),
    [[a0, b0, c0, d0], [a1, b1, c1, d1], [a2, b2, c2, d2], [a3, b3, c3, d3]], [e0, e1, e2, e3],
    ⟨rfl, fun j hj => ?_⟩, can0, l13, l14, rfl, by simp, fun k hk => ?_, rfl, fun k hk => ?_, ?_,
    ⟨by rw [hrun]; simp, fun j hj => ?_⟩, ?_, ?_⟩
  · have hj' : j < 5 := hj
    interval_cases j
    · exact l8
    · exact l9
    · exact l10
    · exact l11
    · exact l12
  · simp only [List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
      List.append_nil, List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact hr0 0 (by omega)
    · exact hr0 1 (by omega)
    · exact hr0 2 (by omega)
    · exact hr0 3 (by omega)
    · exact hr1 0 (by omega)
    · exact hr1 1 (by omega)
    · exact hr1 2 (by omega)
    · exact hr1 3 (by omega)
    · exact hr2 0 (by omega)
    · exact hr2 1 (by omega)
    · exact hr2 2 (by omega)
    · exact hr2 3 (by omega)
    · exact hr3 0 (by omega)
    · exact hr3 1 (by omega)
    · exact hr3 2 (by omega)
    · exact hr3 3 (by omega)
  · simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · simpa using he0
    · simpa using he1
    · simpa using he2
    · simpa using he3
  · rw [hrun]
    intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    rw [tb_loadHolds_mul_gen_pow]
    interval_cases k
    · simpa using hs0
    · simpa using hs1
    · simpa using hs2
    · simpa using hs3
  · generalize hR : gkrRun [[a0, b0, c0, d0], [a1, b1, c1, d1], [a2, b2, c2, d2],
      [a3, b3, c3, d3]] [e0, e1, e2, e3] (σ (.n 14))
      ⟨[σ (.n 8), σ (.n 9), σ (.n 10), σ (.n 11), σ (.n 12)], []⟩ = R at hj ⊢
    rw [hrun] at hR
    subst hR
    simp only [List.length_map, List.length_range] at hj
    have := hst j hj
    simp only [Atom.Holds] at this
    simpa [gkCap, Nat.mul_comm] using this
  · rw [show σ (.n 13) * gen ^ (4 * 4) = σ (.n 312) by
      rw [m312, c311, show (65536 : ℕ) = 2 ^ 16 by norm_num, tb_word_two_pow (by norm_num)]]
    exact s312
  · rw [hrun]
    exact s310

/-- No rounds: a record's facts. -/
theorem gkrRoundsOut_zero {rd : Reader} {rec pt : E} {cap : List E} {cur claim : E}
    (hc : TbCapAt rd rec 0 gkCap cap) (hcan : AllCanonical cap)
    (hcur : LoadHolds rd rec (5 * gkCap) cur) (hcl : LoadHolds rd rec (6 * gkCap) claim) :
    TbGkrRoundsOut 0 rd rec pt :=
  ⟨cap, cur, claim, [], [], hc, hcan, hcur, hcl, rfl, by simp, tbReadsAt_nil _ _, rfl,
    tbReadsAt_nil _ _, tbReadsAt_nil _ _, by simpa [gkrRun] using hc,
    by simpa using hcur, by simpa [gkrRun] using hcl⟩

/-- **`__loop27` behind its guard**: from the record at `head`, `half = g^h` iterations are the
`4h` rounds to the record at `head·g^(4h)`. -/
theorem l29_loop {rd : Reader} {half head ptrow : E} {h : ℕ} (hh : half = gen ^ h)
    (hhb : h < 2 ^ 62)
    (hcall : 1 + half ≠ 0 → coreProgram.Rel rd "__loop27" [1, half, head, ptrow] [])
    (h0 : TbGkrRoundsOut 0 rd head ptrow) : TbGkrRoundsOut (4 * h) rd head ptrow := by
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · simpa using h0
  have hne : 1 + half ≠ 0 := by
    rw [hh]
    intro h0'
    have := gen_pow_inj (by omega) (by decide) ((e_add_eq_zero_iff.mp h0').symm.trans
      (pow_zero gen).symm)
    omega
  have hrun := hcall hne
  rw [← pow_zero gen] at hrun
  obtain ⟨m, -, hN, hall⟩ := tb_loop_sound (B := fun x ↦ TbGkrRoundsOut 4 rd (head * x ^ 4)
    (ptrow * x ^ 4)) (fun d x hx => l29_step d x hx) 0 hrun
  have hmh : h ≤ m := by
    by_contra hc
    have := gen_pow_inj (by omega) (by omega) (hh.symm.trans hN)
    omega
  have key : ∀ i ≤ h, TbGkrRoundsOut (4 * i) rd head ptrow := by
    intro i hi
    induction i with
    | zero => simpa using h0
    | succ i ih =>
      have hb := hall i (by omega) (by omega)
      rw [← pow_mul, mul_comm i 4] at hb
      rw [show 4 * (i + 1) = 4 * i + 4 by ring]
      exact gkrRoundsOut_append (ih (by omega)) hb
  exact key h le_rfl

end Sem

end
end LeanVM.Guest.B1.Tables
