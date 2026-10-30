/-
  LeanVM.Guest.B1.Gkr.Loop29Complete

  `__loop27`, completely: four GKR rounds from the record at `head·x^4` at every iteration give
  its relation from `1` below `half`.
-/

module

public import LeanVM.Guest.B1.Gkr.Loop29
public import LeanVM.Guest.B1.Gkr.GkBody
public import LeanVM.Guest.B1.Common.Loops

/-!
# `__loop27`, completely (G:1699-1729)

An iteration of `__loop27` is B1-a's `gkBody 4` (the four rounds between records) renamed six
values on (`l29Body_eq`, by kernel evaluation), after the record's and the row's pointers
`head·x^4`, `ptrow·x^4`, and before the guard and the next call. The honest valuation of an
iteration (`l29Val`) takes the four rounds' from `gk_body_holds` (`σgk`, renamed), the pointers
and the guard around them. `l29_complete`: when every iteration's four rounds hold
(`TbGkrRoundsOut 4` at `head·g^(4j)`, `ptrow·g^(4j)`), the loop holds from `1` below `g^h`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1

@[expose] public section

/-- Six values on. -/
def sh6 (v : V) : V := .n (v.idx + 6)

/-- The iteration's pointers. -/
def l29Pre : List Stmt :=
  [.atom (.mul (.n 4) (.n 0) (.n 0)), .atom (.mul (.n 5) (.n 4) (.n 4)),
    .atom (.mul (.n 6) (.n 2) (.n 5)), .atom (.mul (.n 7) (.n 3) (.n 5))]

/-- The guard and the next call's argument. -/
def l29Post : List Stmt :=
  [.atom (.const (.n 313) (word 2 0 0)), .atom (.mul (.n 314) (.n 0) (.n 313)),
    .atom (.add (.n 315) (.n 314) (.n 1)), .atom (.const (.n 316) (word 2 0 0)),
    .atom (.mul (.n 317) (.n 0) (.n 316))]

/-- The iteration's atoms. -/
def l29A : List Stmt := l29Pre ++ Stmt.renameList sh6 (gkBody 4).dropLast ++ l29Post

set_option maxRecDepth 100000 in
theorem l29Body_eq' : tbStmtsEqb l29Body
    (l29A ++ [.callIf (.n 315) "__loop27" [.n 317, .n 1, .n 2, .n 3], .ret []]) = true := by
  decide +kernel

theorem l29Body_eq : l29Body =
    l29A ++ [.callIf (.n 315) "__loop27" [.n 317, .n 1, .n 2, .n 3], .ret []] :=
  tbStmtsEqb_sound l29Body_eq'

/-- Every statement of `gkBody 4` but its `ret` is an atom over values `.n k`, `k ≤ 306`. -/
def gk4Ok : Stmt → Bool
  | .atom a => a.vals.all fun v => decide (v = .n v.idx) && decide (v.idx ≤ 306)
  | _ => false

set_option maxRecDepth 100000 in
theorem gk4_ok : (gkBody 4).dropLast.all gk4Ok = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gkBody4_eq : gkBody 4 = (gkBody 4).dropLast ++ [.ret []] :=
  tbStmtsEqb_sound (by decide +kernel)

theorem atom_congr' {rd : Reader} {σ σ' : Val} {a : Atom} (h : ∀ v ∈ a.vals, σ v = σ' v) :
    a.Holds rd σ ↔ a.Holds rd σ' := by
  cases a with
  | keccak ins outs inOdd outOdd =>
    simp only [Atom.vals, List.mem_append] at h
    have hi : ins.map σ = ins.map σ' := List.map_congr_left fun v hv ↦ h v (.inl hv)
    have ho : outs.map σ = outs.map σ' := List.map_congr_left fun v hv ↦ h v (.inr hv)
    simp only [Atom.Holds, hi, ho]
  | frameAddr q run =>
    simp only [Atom.vals, List.mem_cons, forall_eq_or_imp] at h
    simp only [Atom.Holds, h.1]
    refine and_congr_right fun _ ↦ forall_congr' fun k ↦ forall_congr' fun hk ↦ ?_
    rw [h.2 _ (List.getElem_mem hk)]
  | hint => simp [Atom.Holds]
  | _ => simp_all [Atom.vals, Atom.Holds]

theorem mem_renameList {r : V → V} : ∀ {ss : List Stmt} {s : Stmt}, s ∈ Stmt.renameList r ss →
    ∃ t ∈ ss, s = t.rename r
  | [], _, h => absurd h (by simp [Stmt.renameList])
  | t :: ss, s, h => by
    simp only [Stmt.renameList, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨t, List.mem_cons_self, rfl⟩
    · obtain ⟨u, hu, rfl⟩ := mem_renameList h
      exact ⟨u, List.mem_cons_of_mem _ hu, rfl⟩

theorem l29A_atoms : AllAtoms l29A := by
  intro s hs
  simp only [l29A, List.mem_append] at hs
  rcases hs with (hs | hs) | hs
  · simp only [l29Pre, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · obtain ⟨t, ht, rfl⟩ := mem_renameList hs
    have := List.all_eq_true.mp gk4_ok t ht
    cases t with
    | atom a => exact ⟨_, rfl⟩
    | _ => simp [gk4Ok] at this
  · simp only [l29Post, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

/-- **The honest valuation of an iteration** at `x`, the four rounds' `σgk` renamed. -/
def l29Val (x N head ptrow : E) (σgk : Val) (v : V) : E :=
  if v.idx < 6 then [x, N, head, ptrow, x * x, x * x * (x * x)].getD v.idx 0
  else if v.idx ≤ 312 then σgk (.n (v.idx - 6))
  else [gen, x * gen, x * gen + N, gen, x * gen].getD (v.idx - 313) 0

theorem gkBody4_atoms {C : CallRel} {rd : Reader} {σ : Val}
    (h : Stmt.HoldsList C rd σ (gkBody 4) False (fun rs => rs = [])) :
    ∀ a, Stmt.atom a ∈ (gkBody 4).dropLast → a.Holds rd σ := by
  have hA : AllAtoms (gkBody 4).dropLast := by
    intro t ht
    have := List.all_eq_true.mp gk4_ok t ht
    cases t with
    | atom a => exact ⟨_, rfl⟩
    | _ => simp [gk4Ok] at this
  rw [gkBody4_eq, holdsList_append, holdsList_atoms hA] at h
  exact h.1

set_option maxRecDepth 10000 in
/-- **An iteration of `__loop27`, completely.** -/
theorem l29_iter {rd : Reader} (x N head ptrow : E)
    (hT : TbGkrRoundsOut 4 rd (head * (x * x * (x * x))) (ptrow * (x * x * (x * x)))) :
    AtomsBody rd [.n 0, .n 1, .n 2, .n 3] l29A [x, N, head, ptrow] := by
  obtain ⟨σgk, hσv, h0, h1, hh⟩ := gk_body_holds 4 (by norm_num) (by norm_num)
    (coreProgram.Rel rd) rd _ _ ⟨rfl, hT⟩
  have hgk := gkBody4_atoms hh
  refine ⟨l29Val x N head ptrow σgk, by simp [l29Val], fun a ha => ?_⟩
  simp only [l29A, List.mem_append] at ha
  rcases ha with (ha | ha) | ha
  · simp only [l29Pre, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> simp [Atom.Holds, l29Val, h0, h1]
  · obtain ⟨t, ht, he⟩ := mem_renameList ha
    cases t with
    | atom b =>
      simp only [Stmt.rename, Stmt.atom.injEq] at he
      subst he
      rw [Atom.holds_rename]
      refine (atom_congr' fun v hv => ?_).mpr (hgk b ht)
      have hok := List.all_eq_true.mp gk4_ok _ ht
      simp only [gk4Ok, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨hvn, hvi⟩ := hok v hv
      show l29Val x N head ptrow σgk (sh6 v) = σgk v
      rw [hσv v]
      have i1 : ¬ v.idx + 6 < 6 := by omega
      have i2 : v.idx + 6 ≤ 312 := by omega
      simp only [l29Val, sh6, i1, i2, ↓reduceIte, Nat.add_sub_cancel]
    | _ =>
      have hok := List.all_eq_true.mp gk4_ok _ ht
      simp [gk4Ok] at hok
  · simp only [l29Post, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp [Atom.Holds, l29Val, tb_word_gen]

set_option maxRecDepth 10000 in
/-- **`__loop27`, completely**: four rounds from the record at `head·g^(4j)` at every iteration
`j < h` give the loop from `1` below `g^h`. -/
theorem l29_complete {rd : Reader} {head ptrow : E} {h : ℕ} (hpos : 0 < h) (hhb : h < 2 ^ 62)
    (hr : ∀ j < h, TbGkrRoundsOut 4 rd (head * gen ^ (4 * j)) (ptrow * gen ^ (4 * j))) :
    coreProgram.Rel rd "__loop27" [1, gen ^ h, head, ptrow] [] := by
  obtain ⟨fn, hf, hp, hb⟩ := l29Found
  rw [l29Body_eq] at hb
  have hstep : ∀ d x, coreProgram.relN rd (d + 1) "__loop27" (x :: [gen ^ h, head, ptrow]) [] ↔
      AtomsBody rd fn.params l29A (x :: [gen ^ h, head, ptrow]) ∧ IsInK (x * gen + gen ^ h) ∧
        (x * gen + gen ^ h ≠ 0 →
          coreProgram.relN rd d "__loop27" (x * gen :: [gen ^ h, head, ptrow]) []) := by
    intro d x
    refine loop_step_atoms hf hb l29A_atoms (fun σ hpar hall => ?_) d
    rw [hp] at hpar
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
    obtain ⟨h0, h1, h2, h3⟩ := hpar
    have m := fun a (ha : Stmt.atom a ∈ l29Post) => hall a (by
      simp only [l29A, List.mem_append]; exact Or.inr ha)
    simp only [l29Post, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq,
      forall_eq_or_imp, forall_eq, Atom.Holds] at m
    obtain ⟨c313, m314, a315, c316, m317⟩ := m
    rw [tb_word_gen] at c313 c316
    refine ⟨by rw [a315, m314, c313, h0, h1], ?_⟩
    simp only [List.map_cons, List.map_nil, m317, c316, h0, h1, h2, h3]
  rw [← pow_zero gen]
  refine (loop_iff hstep 0).mpr ⟨h, hpos, rfl, first_hit_of_lt (by unfold ordG; omega) rfl,
    fun j _ hj => ?_⟩
  rw [hp]
  apply l29_iter
  have := hr j hj
  rwa [show gen ^ j * gen ^ j * (gen ^ j * gen ^ j) = gen ^ (4 * j) by ring]

end
end LeanVM.Guest.B1.Tables
