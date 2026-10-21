/-
  LeanVM.Guest.Count.StaticS

  `Static.lean` under any semantics of `BLAKE2S` (`S : BlakeSem`).
-/

module

public import LeanVM.Guest.Count.Static
public import LeanVM.Guest.Memory.GuestCntXB
public import LeanVM.Guest.Memory.GuestCntMB
public import LeanVM.Guest.Memory.GuestCntSB
public import LeanVM.Guest.Memory.GuestCntDB
public import LeanVM.Guest.Memory.GuestCntJB
public import LeanVM.Guest.Memory.GuestCntBB

/-!
# `Static.lean` under any `BLAKE2S` semantics

Each definition and lemma of `Static.lean` that mentions the semantics, with `S : BlakeSem` a
parameter and a `S` in its name.
-/

namespace LeanVM.Guest.Count

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest

@[expose] public section

variable {S : BlakeSem}

/-- **`exponent_tables`'s instructions.** -/
theorem kcExpS_weightLe (op : Opcode) :
    WeightLeB S coreProgram (kcOm op) "exponent_tables" fun _ => kcExp op := by
  cases op
  · exact kwxB_weightLe (by rw [kwxcertOf_of_idx (j := 2) (by decide +kernel)]; rfl : kwxcertOf "exponent_tables" = .stat [] ⟨0, []⟩ [])
  · exact kwmB_weightLe (by rw [kwmcertOf_of_idx (j := 2) (by decide +kernel)]; rfl : kwmcertOf "exponent_tables" = .stat [] ⟨2, []⟩ [])
  · exact kwsB_weightLe (by rw [kwscertOf_of_idx (j := 2) (by decide +kernel)]; rfl : kwscertOf "exponent_tables" = .stat [] ⟨62, []⟩ [])
  · exact kwdB_weightLe (by rw [kwdcertOf_of_idx (j := 2) (by decide +kernel)]; rfl : kwdcertOf "exponent_tables" = .stat [] ⟨68, []⟩ [])
  · exact kwjB_weightLe (by rw [kwjcertOf_of_idx (j := 2) (by decide +kernel)]; rfl : kwjcertOf "exponent_tables" = .stat [] ⟨1, []⟩ [])
  · exact kwbB_weightLe (by rw [kwbcertOf_of_idx (j := 2) (by decide +kernel)]; rfl : kwbcertOf "exponent_tables" = .stat [] ⟨0, []⟩ [])

/-- **`da_list_digest`'s instructions.** -/
theorem kcDlS_weightLe (op : Opcode) :
    WeightLeB S coreProgram (kcOm op) "da_list_digest" fun _ => kcDl op := by
  cases op
  · exact kwxB_weightLe (by rw [kwxcertOf_of_idx (j := 27) (by decide +kernel)]; rfl : kwxcertOf "da_list_digest" = .stat [] ⟨0, []⟩ [])
  · exact kwmB_weightLe (by rw [kwmcertOf_of_idx (j := 27) (by decide +kernel)]; rfl : kwmcertOf "da_list_digest" = .stat [] ⟨6, []⟩ [])
  · exact kwsB_weightLe (by rw [kwscertOf_of_idx (j := 27) (by decide +kernel)]; rfl : kwscertOf "da_list_digest" = .stat [] ⟨21, []⟩ [])
  · exact kwdB_weightLe (by rw [kwdcertOf_of_idx (j := 27) (by decide +kernel)]; rfl : kwdcertOf "da_list_digest" = .stat [] ⟨70, []⟩ [])
  · exact kwjB_weightLe (by rw [kwjcertOf_of_idx (j := 27) (by decide +kernel)]; rfl : kwjcertOf "da_list_digest" = .stat [] ⟨3, []⟩ [])
  · exact kwbB_weightLe (by rw [kwbcertOf_of_idx (j := 27) (by decide +kernel)]; rfl : kwbcertOf "da_list_digest" = .stat [] ⟨16, []⟩ [])

/-- **`cover_da_root`'s instructions.** -/
theorem kcCovS_weightLe (op : Opcode) :
    WeightLeB S coreProgram (kcOm op) "cover_da_root" fun _ => kcCov op := by
  cases op
  · exact kwxB_weightLe (by rw [kwxcertOf_of_idx (j := 28) (by decide +kernel)]; rfl : kwxcertOf "cover_da_root" = .stat [] ⟨0, []⟩ [])
  · exact kwmB_weightLe (by rw [kwmcertOf_of_idx (j := 28) (by decide +kernel)]; rfl : kwmcertOf "cover_da_root" = .stat [] ⟨6, []⟩ [])
  · exact kwsB_weightLe (by rw [kwscertOf_of_idx (j := 28) (by decide +kernel)]; rfl : kwscertOf "cover_da_root" = .stat [] ⟨2, []⟩ [])
  · exact kwdB_weightLe (by rw [kwdcertOf_of_idx (j := 28) (by decide +kernel)]; rfl : kwdcertOf "cover_da_root" = .stat [] ⟨7, []⟩ [])
  · exact kwjB_weightLe (by rw [kwjcertOf_of_idx (j := 28) (by decide +kernel)]; rfl : kwjcertOf "cover_da_root" = .stat [] ⟨1, []⟩ [])
  · exact kwbB_weightLe (by rw [kwbcertOf_of_idx (j := 28) (by decide +kernel)]; rfl : kwbcertOf "cover_da_root" = .stat [] ⟨0, []⟩ [])

/-- **`statement_digest`'s instructions.** -/
theorem kcSdS_weightLe (op : Opcode) :
    WeightLeB S coreProgram (kcOm op) "statement_digest" fun _ => kcSd op := by
  cases op
  · exact kwxB_weightLe (by rw [kwxcertOf_of_idx (j := 18) (by decide +kernel)]; rfl : kwxcertOf "statement_digest" = .stat [] ⟨188, []⟩ [])
  · exact kwmB_weightLe (by rw [kwmcertOf_of_idx (j := 18) (by decide +kernel)]; rfl : kwmcertOf "statement_digest" = .stat [] ⟨195, []⟩ [])
  · exact kwsB_weightLe (by rw [kwscertOf_of_idx (j := 18) (by decide +kernel)]; rfl : kwscertOf "statement_digest" = .stat [] ⟨29, []⟩ [])
  · exact kwdB_weightLe (by rw [kwdcertOf_of_idx (j := 18) (by decide +kernel)]; rfl : kwdcertOf "statement_digest" = .stat [] ⟨55, []⟩ [])
  · exact kwjB_weightLe (by rw [kwjcertOf_of_idx (j := 18) (by decide +kernel)]; rfl : kwjcertOf "statement_digest" = .stat [] ⟨82, []⟩ [])
  · exact kwbB_weightLe (by rw [kwbcertOf_of_idx (j := 18) (by decide +kernel)]; rfl : kwbcertOf "statement_digest" = .stat [] ⟨22, []⟩ [])

variable (S) in
/-- A loop helper's instructions from `g^a` to `g^e`: `K` per iteration. -/
def KcLoopS (op : Opcode) (f : String) (K : ℕ) : Prop :=
  ∀ (rd : Reader) (t : Tree) (args rets : List E) (a e : ℕ), t.name = f → t.ValidB S coreProgram rd args rets →
    t.BufsOk coreProgram → args.getD 0 0 = ofK (gpow a) → args.getD 1 0 = ofK (gpow e) → a < e →
      e < 2 ^ 64 - 1 → t.weight (kcOm op) ≤ (e - a) * K

/-- **`__loop0`'s instructions.** -/
theorem kcL0S_loop (op : Opcode) : KcLoopS S op "__loop0" (kcL0 op) := by
  intro rd t args rets a e hn hv hb ha he hae heo
  cases op
  · exact kwxB_weight_le_of_loop (by rw [kwxcertOf_of_idx (j := 30) (by decide +kernel)]; rfl : kwxcertOf "__loop0" = .loop none [] ⟨1, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwmB_weight_le_of_loop (by rw [kwmcertOf_of_idx (j := 30) (by decide +kernel)]; rfl : kwmcertOf "__loop0" = .loop none [] ⟨11, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwsB_weight_le_of_loop (by rw [kwscertOf_of_idx (j := 30) (by decide +kernel)]; rfl : kwscertOf "__loop0" = .loop none [] ⟨4, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwdB_weight_le_of_loop (by rw [kwdcertOf_of_idx (j := 30) (by decide +kernel)]; rfl : kwdcertOf "__loop0" = .loop none [] ⟨0, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwjB_weight_le_of_loop (by rw [kwjcertOf_of_idx (j := 30) (by decide +kernel)]; rfl : kwjcertOf "__loop0" = .loop none [] ⟨2, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwbB_weight_le_of_loop (by rw [kwbcertOf_of_idx (j := 30) (by decide +kernel)]; rfl : kwbcertOf "__loop0" = .loop none [] ⟨0, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)

/-- **`__loop1`'s instructions.** -/
theorem kcL1S_loop (op : Opcode) : KcLoopS S op "__loop1" (kcL1 op) := by
  intro rd t args rets a e hn hv hb ha he hae heo
  cases op
  · exact kwxB_weight_le_of_loop (by rw [kwxcertOf_of_idx (j := 31) (by decide +kernel)]; rfl : kwxcertOf "__loop1" = .loop none [] ⟨1, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwmB_weight_le_of_loop (by rw [kwmcertOf_of_idx (j := 31) (by decide +kernel)]; rfl : kwmcertOf "__loop1" = .loop none [] ⟨13, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwsB_weight_le_of_loop (by rw [kwscertOf_of_idx (j := 31) (by decide +kernel)]; rfl : kwscertOf "__loop1" = .loop none [] ⟨4, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwdB_weight_le_of_loop (by rw [kwdcertOf_of_idx (j := 31) (by decide +kernel)]; rfl : kwdcertOf "__loop1" = .loop none [] ⟨0, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwjB_weight_le_of_loop (by rw [kwjcertOf_of_idx (j := 31) (by decide +kernel)]; rfl : kwjcertOf "__loop1" = .loop none [] ⟨2, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwbB_weight_le_of_loop (by rw [kwbcertOf_of_idx (j := 31) (by decide +kernel)]; rfl : kwbcertOf "__loop1" = .loop none [] ⟨0, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)

/-- **`__loop2`'s instructions.** -/
theorem kcL2S_loop (op : Opcode) : KcLoopS S op "__loop2" (kcL2 op) := by
  intro rd t args rets a e hn hv hb ha he hae heo
  cases op
  · exact kwxB_weight_le_of_loop (by rw [kwxcertOf_of_idx (j := 32) (by decide +kernel)]; rfl : kwxcertOf "__loop2" = .loop none [] ⟨1, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwmB_weight_le_of_loop (by rw [kwmcertOf_of_idx (j := 32) (by decide +kernel)]; rfl : kwmcertOf "__loop2" = .loop none [] ⟨13, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwsB_weight_le_of_loop (by rw [kwscertOf_of_idx (j := 32) (by decide +kernel)]; rfl : kwscertOf "__loop2" = .loop none [] ⟨4, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwdB_weight_le_of_loop (by rw [kwdcertOf_of_idx (j := 32) (by decide +kernel)]; rfl : kwdcertOf "__loop2" = .loop none [] ⟨0, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwjB_weight_le_of_loop (by rw [kwjcertOf_of_idx (j := 32) (by decide +kernel)]; rfl : kwjcertOf "__loop2" = .loop none [] ⟨2, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwbB_weight_le_of_loop (by rw [kwbcertOf_of_idx (j := 32) (by decide +kernel)]; rfl : kwbcertOf "__loop2" = .loop none [] ⟨0, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)

/-- **`__loop3`'s instructions.** -/
theorem kcL3S_loop (op : Opcode) : KcLoopS S op "__loop3" (kcL3 op) := by
  intro rd t args rets a e hn hv hb ha he hae heo
  cases op
  · exact kwxB_weight_le_of_loop (by rw [kwxcertOf_of_idx (j := 33) (by decide +kernel)]; rfl : kwxcertOf "__loop3" = .loop none [] ⟨183, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwmB_weight_le_of_loop (by rw [kwmcertOf_of_idx (j := 33) (by decide +kernel)]; rfl : kwmcertOf "__loop3" = .loop none [] ⟨232, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwsB_weight_le_of_loop (by rw [kwscertOf_of_idx (j := 33) (by decide +kernel)]; rfl : kwscertOf "__loop3" = .loop none [] ⟨269, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwdB_weight_le_of_loop (by rw [kwdcertOf_of_idx (j := 33) (by decide +kernel)]; rfl : kwdcertOf "__loop3" = .loop none [] ⟨132, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwjB_weight_le_of_loop (by rw [kwjcertOf_of_idx (j := 33) (by decide +kernel)]; rfl : kwjcertOf "__loop3" = .loop none [] ⟨84, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwbB_weight_le_of_loop (by rw [kwbcertOf_of_idx (j := 33) (by decide +kernel)]; rfl : kwbcertOf "__loop3" = .loop none [] ⟨201, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)

/-- **`__loop4`'s instructions.** -/
theorem kcL4S_loop (op : Opcode) : KcLoopS S op "__loop4" (kcL4 op) := by
  intro rd t args rets a e hn hv hb ha he hae heo
  cases op
  · exact kwxB_weight_le_of_loop (by rw [kwxcertOf_of_idx (j := 34) (by decide +kernel)]; rfl : kwxcertOf "__loop4" = .loop none [] ⟨595, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwmB_weight_le_of_loop (by rw [kwmcertOf_of_idx (j := 34) (by decide +kernel)]; rfl : kwmcertOf "__loop4" = .loop none [] ⟨343, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwsB_weight_le_of_loop (by rw [kwscertOf_of_idx (j := 34) (by decide +kernel)]; rfl : kwscertOf "__loop4" = .loop none [] ⟨673, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwdB_weight_le_of_loop (by rw [kwdcertOf_of_idx (j := 34) (by decide +kernel)]; rfl : kwdcertOf "__loop4" = .loop none [] ⟨294, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwjB_weight_le_of_loop (by rw [kwjcertOf_of_idx (j := 34) (by decide +kernel)]; rfl : kwjcertOf "__loop4" = .loop none [] ⟨128, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwbB_weight_le_of_loop (by rw [kwbcertOf_of_idx (j := 34) (by decide +kernel)]; rfl : kwbcertOf "__loop4" = .loop none [] ⟨427, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)

/-- **`__loop100`'s instructions.** -/
theorem kcL100S_loop (op : Opcode) : KcLoopS S op "__loop100" (kcL100 op) := by
  intro rd t args rets a e hn hv hb ha he hae heo
  cases op
  · exact kwxB_weight_le_of_loop (by rw [kwxcertOf_of_idx (j := 573) (by decide +kernel)]; rfl : kwxcertOf "__loop100" = .loop none [] ⟨1, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwmB_weight_le_of_loop (by rw [kwmcertOf_of_idx (j := 573) (by decide +kernel)]; rfl : kwmcertOf "__loop100" = .loop none [] ⟨24, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwsB_weight_le_of_loop (by rw [kwscertOf_of_idx (j := 573) (by decide +kernel)]; rfl : kwscertOf "__loop100" = .loop none [] ⟨7, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwdB_weight_le_of_loop (by rw [kwdcertOf_of_idx (j := 573) (by decide +kernel)]; rfl : kwdcertOf "__loop100" = .loop none [] ⟨21, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwjB_weight_le_of_loop (by rw [kwjcertOf_of_idx (j := 573) (by decide +kernel)]; rfl : kwjcertOf "__loop100" = .loop none [] ⟨4, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)
  · exact kwbB_weight_le_of_loop (by rw [kwbcertOf_of_idx (j := 573) (by decide +kernel)]; rfl : kwbcertOf "__loop100" = .loop none [] ⟨0, []⟩ []) hn hv hb ha he hae heo (fun _ h => (List.not_mem_nil h).elim)

/-- **`aggregate_claims`' instructions** on `g^n`. -/
theorem kcAggS_le (op : Opcode) : ∀ (rd : Reader) (t : Tree) (args rets : List E) (n : ℕ),
    t.name = "aggregate_claims" → t.ValidB S coreProgram rd args rets → t.BufsOk coreProgram →
      args.getD 0 0 = ofK (gpow n) → 0 < n → n < 2 ^ 64 - 1 →
        t.weight (kcOm op) ≤ kcAggC op + kcAggD op * n := by
  intro rd t args rets n hn hv hb ha h0 h1
  have hpre : ArgsPre [(0, 0)] args := by
    intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    exact ⟨n, h0, h1, ha⟩
  have hx : argExp args 0 = n := by rw [argExp, ha, logG_ofK h1]
  cases op
  · have := kwxB_weight_le_of_stat (by rw [kwxcertOf_of_idx (j := 29) (by decide +kernel)]; rfl : kwxcertOf "aggregate_claims" = .stat [(0, 0)] ⟨568, [(0, 323), (0, 7), (0, 91), (0, 10), (0, 282)]⟩ [(.n 34, 0), (.n 49, 0), (.n 68, 0), (.n 83, 0), (.n 514, 0)]) hn hv hb hpre
    simp only [Aff.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hx] at this
    simp only [kcAggC, kcAggD]; omega
  · have := kwmB_weight_le_of_stat (by rw [kwmcertOf_of_idx (j := 29) (by decide +kernel)]; rfl : kwmcertOf "aggregate_claims" = .stat [(0, 0)] ⟨576, [(0, 189), (0, 23), (0, 61), (0, 26), (0, 390)]⟩ [(.n 34, 0), (.n 49, 0), (.n 68, 0), (.n 83, 0), (.n 514, 0)]) hn hv hb hpre
    simp only [Aff.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hx] at this
    simp only [kcAggC, kcAggD]; omega
  · have := kwsB_weight_le_of_stat (by rw [kwscertOf_of_idx (j := 29) (by decide +kernel)]; rfl : kwscertOf "aggregate_claims" = .stat [(0, 0)] ⟨35, [(0, 10), (0, 11), (0, 4), (0, 11), (0, 69)]⟩ [(.n 34, 0), (.n 49, 0), (.n 68, 0), (.n 83, 0), (.n 514, 0)]) hn hv hb hpre
    simp only [Aff.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hx] at this
    simp only [kcAggC, kcAggD]; omega
  · have := kwdB_weight_le_of_stat (by rw [kwdcertOf_of_idx (j := 29) (by decide +kernel)]; rfl : kwdcertOf "aggregate_claims" = .stat [(0, 0)] ⟨598, [(0, 167), (0, 12), (0, 72), (0, 14), (0, 275)]⟩ [(.n 34, 0), (.n 49, 0), (.n 68, 0), (.n 83, 0), (.n 514, 0)]) hn hv hb hpre
    simp only [Aff.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hx] at this
    simp only [kcAggC, kcAggD]; omega
  · have := kwjB_weight_le_of_stat (by rw [kwjcertOf_of_idx (j := 29) (by decide +kernel)]; rfl : kwjcertOf "aggregate_claims" = .stat [(0, 0)] ⟨161, [(0, 163), (0, 4), (0, 2), (0, 5), (0, 2)]⟩ [(.n 34, 0), (.n 49, 0), (.n 68, 0), (.n 83, 0), (.n 514, 0)]) hn hv hb hpre
    simp only [Aff.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hx] at this
    simp only [kcAggC, kcAggD]; omega
  · have := kwbB_weight_le_of_stat (by rw [kwbcertOf_of_idx (j := 29) (by decide +kernel)]; rfl : kwbcertOf "aggregate_claims" = .stat [(0, 0)] ⟨151, [(0, 161), (0, 2), (0, 0), (0, 3), (0, 0)]⟩ [(.n 34, 0), (.n 49, 0), (.n 68, 0), (.n 83, 0), (.n 514, 0)]) hn hv hb hpre
    simp only [Aff.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hx] at this
    simp only [kcAggC, kcAggD]; omega

end
end LeanVM.Guest.Count
