/-
  LeanVM.Guest.B1.Tables.VtC.Val

  `verify_tables`' honest valuation: its evaluation list evaluated through its own stores, from
  the arguments, a memory `rd0` of the words it reads that it does not store itself, and an
  oracle `w` (allocations' bases, callees' returns, witnesses).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.Glue

/-!
# The honest valuation

`VtIn`: the arguments, the memory `rd0` and the oracle `w`. `VtIn.σ`, `VtIn.log`: the valuation
and the stores of `evM rd0 w args [] vtEvL`. `VtIn.good`: every statement of the list satisfies
its equations for the memory of its step (a prefix of the log over `rd0`). `VtIn.MemOk rd`: the
memory `rd` holds `rd0`'s words and the first word logged at every logged address.

`VtIn.load_holds`: a load the list evaluated from memory holds on such a memory when its address
is one of `rd0`'s or logged before it; `VtIn.store_holds`: a store holds when its address was not
logged before it.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The honest inputs of `verify_tables`' evaluation. -/
structure VtIn where
  /-- The `22` arguments. -/
  args : List E
  /-- The words it reads that it does not store itself. -/
  rd0 : Reader
  /-- The allocations' bases, the callees' returns, the witnesses. -/
  w : ℕ → E

namespace VtIn

variable (I : VtIn)

/-- The evaluation. -/
noncomputable def run : List E × SLog := evM I.rd0 I.w I.args [] vtEvL

/-- **The honest valuation.** -/
noncomputable def σ : Val := B1.Val.ofArgs I.run.1

/-- The stores, in order. -/
noncomputable def log : SLog := I.run.2

/-- The stores of the list. -/
noncomputable def S : List Atom := storesOf 22 vtEvL

theorem good (hl : I.args.length = 22) : ∀ s ∈ vtEvL, ∃ (lg : SLog) (c : ℕ),
    lg ++ stWr c I.σ s <+: I.log ∧ storeHd c s ⊆ S ∧ GoodS (ovl I.rd0 lg) S I.w I.σ s := by
  have h := (evM_spec I.rd0 I.w vtEvL I.args [] (by rw [hl]; exact vt_chk)).2.2.2
  rw [hl] at h
  intro s hs
  obtain ⟨lg, c, -, h1, h2, h3⟩ := h s hs
  exact ⟨lg, c, h1, h2, h3⟩

theorem params (hl : I.args.length = 22) {i : ℕ} (hi : i < 22) : I.σ (.n i) = I.args.getD i 0 := by
  obtain ⟨-, ⟨m, hm⟩, -⟩ := evM_spec I.rd0 I.w vtEvL I.args [] (by rw [hl]; exact vt_chk)
  show B1.Val.ofArgs I.run.1 (.n i) = _
  rw [run, hm, Fwd.ofArgs_old (by rw [hl]; exact hi)]
  rfl

end VtIn

/-- The memory holds `rd0`'s words and the first word logged at each logged address. -/
def MemOkL (rd0 : Reader) (log : SLog) (rd : Reader) : Prop :=
  (∀ a v, rd0 a = some v → rd a = some v) ∧ ∀ e ∈ log, rd e.1 = ovl rd0 log e.1

/-- The memory holds the honest evaluation's words. -/
def VtIn.MemOk (I : VtIn) (rd : Reader) : Prop := MemOkL I.rd0 I.log rd

/-! ## Membership -/

theorem mem_flatIte_of {s : Stmt} (hni : ∀ c z n, s ≠ .ite c z n) :
    ∀ {ss : List Stmt}, s ∈ ss → s ∈ flatIte ss
  | [], h => absurd h (by simp)
  | t :: ss, h => by
    rcases List.mem_cons.mp h with rfl | h
    · cases s with
      | ite c z n => exact absurd rfl (hni c z n)
      | _ => simp [flatIte]
    · have ih := mem_flatIte_of hni h
      cases t with
      | ite c z n => simp [flatIte, ih]
      | _ => simp [flatIte, ih]

theorem mem_flatIte_ite {c : V} {z n : List Stmt} :
    ∀ {ss : List Stmt}, Stmt.ite c z n ∈ ss → ∀ t ∈ z ++ n, t ∈ flatIte ss
  | [], h => absurd h (by simp)
  | u :: ss, h => by
    intro t ht
    rcases List.mem_cons.mp h with rfl | h
    · simp only [flatIte, List.mem_append]
      rcases List.mem_append.mp ht with ht | ht
      · exact Or.inl (Or.inl ht)
      · exact Or.inl (Or.inr ht)
    · have ih := mem_flatIte_ite h t ht
      cases u with
      | ite c' z' n' => simp [flatIte, ih]
      | _ => simp [flatIte, ih]

/-- A statement of the body, not an `ite`, is in the list as `fixNe` reads it. -/
theorem vtEvL_mem {s : Stmt} (hs : s ∈ vtPre) (hni : ∀ c z n, s ≠ .ite c z n) :
    fixNe s ∈ vtEvL :=
  List.mem_map_of_mem (mem_flatIte_of hni hs)

/-- An `ite`'s branches are in the list. -/
theorem vtEvL_mem_ite {c : V} {z n : List Stmt} (hs : Stmt.ite c z n ∈ vtPre) {t : Stmt}
    (ht : t ∈ z ++ n) : fixNe t ∈ vtEvL :=
  List.mem_map_of_mem (mem_flatIte_ite hs t ht)

/-- The statement at a position of the body, by kernel comparison. -/
theorem vt_mem_at (p : ℕ) (s : Stmt) (h : tbStmtsEqb [s] ((vtPre.drop p).take 1) = true) :
    s ∈ vtPre := by
  have e := tbStmtsEqb_sound h
  have : s ∈ (vtPre.drop p).take 1 := by rw [← e]; simp
  exact List.mem_of_mem_drop (List.mem_of_mem_take this)

/-! ## Loads and stores -/

theorem ovl_prefix {rd0 : Reader} {lg log : SLog} (hp : lg <+: log) {a : K}
    (ha : ∃ e ∈ lg, e.1 = a) : ovl rd0 lg a = ovl rd0 log a := by
  obtain ⟨t, rfl⟩ := hp
  obtain ⟨e, he, hea⟩ := ha
  unfold ovl
  rw [List.find?_append]
  have : (lg.find? fun e => decide (e.1 = a)).isSome := by
    rw [List.find?_isSome]; exact ⟨e, he, by simp [hea]⟩
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp this
  rw [hx]
  rfl

theorem ovl_not {rd0 : Reader} {lg : SLog} {a : K} (ha : ¬ ∃ e ∈ lg, e.1 = a) :
    ovl rd0 lg a = rd0 a := by
  unfold ovl
  rw [List.find?_eq_none.mpr (fun e he => by simpa using fun h => ha ⟨e, he, h⟩)]

/-- **A load read from memory holds** when its address is `rd0`'s or logged before it. -/
theorem load_holdsL {rd0 : Reader} {log : SLog} {rd : Reader} (hm : MemOkL rd0 log rd) {lg : SLog}
    (hlg : lg <+: log) {p d : E}
    {off : ℕ} (hd : d = rdAt (ovl rd0 lg) p off) (hp : IsInK p)
    (ha : (rd0 (p.limb 0 * gpow off)).isSome ∨ ∃ e ∈ lg, e.1 = p.limb 0 * gpow off) :
    LoadHolds rd p off d := by
  refine ⟨hp, ?_⟩
  by_cases hin : ∃ e ∈ lg, e.1 = p.limb 0 * gpow off
  · obtain ⟨e, he, hea⟩ := hin
    have h1 := ovl_prefix (rd0 := rd0) hlg ⟨e, he, hea⟩
    have hel : e ∈ log := by obtain ⟨t, ht⟩ := hlg; rw [← ht]; exact List.mem_append_left _ he
    have h2 := hm.2 e hel
    rw [hea] at h2
    have hsome : ∃ v, ovl rd0 log (p.limb 0 * gpow off) = some v := by
      unfold ovl
      have : (log.find? fun e => decide (e.1 = p.limb 0 * gpow off)).isSome := by
        rw [List.find?_isSome]; exact ⟨e, hel, by simp [hea]⟩
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp this
      exact ⟨x.2, by rw [hx]⟩
    obtain ⟨v, hv⟩ := hsome
    rw [hd, rdAt, h1, hv, h2, hv]
    rfl
  · rcases ha with ha | ha
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ha
      rw [hd, rdAt, ovl_not hin, hv, hm.1 _ _ hv]
      rfl
    · exact absurd ha hin


/-- **A store holds** when its address was not logged before it. -/
theorem store_holdsL {rd0 : Reader} {log : SLog} {rd : Reader} (hm : MemOkL rd0 log rd)
    {lg : SLog} {p d : E} {off : ℕ} (hlg : lg ++ [(p.limb 0 * gpow off, d)] <+: log)
    (hp : IsInK p) (hnew : ¬ ∃ e ∈ lg, e.1 = p.limb 0 * gpow off) : LoadHolds rd p off d := by
  refine ⟨hp, ?_⟩
  have hel : (p.limb 0 * gpow off, d) ∈ log := by
    obtain ⟨t, ht⟩ := hlg; rw [← ht]; simp
  rw [hm.2 _ hel]
  obtain ⟨t, rfl⟩ := hlg
  unfold ovl
  rw [List.append_assoc, List.find?_append, List.find?_eq_none.mpr
    (fun e he => by simpa using fun h => hnew ⟨e, he, h⟩)]
  simp


end
end LeanVM.Guest.B1.Tables
