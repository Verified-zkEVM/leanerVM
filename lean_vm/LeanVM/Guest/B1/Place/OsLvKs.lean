/-
  LeanVM.Guest.B1.Place.OsLvKs

  open_stacked's level frames one at a time, and the kinds of the callees they name.
-/

module

public import LeanVM.Guest.B1.Place.OsNamesL
public import LeanVM.Guest.B1.Place.OsCallsOk

/-!
# The levels' frames, one at a time

`osLvKOf_get`: level `j`'s frames are its block before the squeezes', the squeeze loop's and its
block after's, from the state the levels before it leave. `lvA_named`, `tail_named`: the callees
those blocks name have kinds (`OsNames`); `lvB_named`: those after the squeezes, but
`opening_queries`; `finish_named`: the finish's, but the residual loops.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir

@[expose] public section

theorem lvM_state (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (lvM c lvl lv s).2.1 = (osLevelA c lvl lv s).2.1 := by
  unfold lvM osLevelA; split_ifs <;> rfl

theorem osLvKOf_length (σ : Val) (c : OsCfg) : ∀ (lvl : ℕ) (lvs : List OsLv) (s : OsSt),
    (osLvKOf σ c lvl lvs s).length = lvs.length
  | _, [], _ => rfl
  | lvl, _ :: rest, s => by simp [osLvKOf, osLvKOf_length σ c (lvl + 1) rest]

/-- **Level `j`'s frames.** -/
theorem osLvKOf_get (σ : Val) (c : OsCfg) : ∀ (lvl : ℕ) (lvs : List OsLv) (s : OsSt) (j : ℕ)
    (hj : j < lvs.length),
    (osLvKOf σ c lvl lvs s)[j]'(by rw [osLvKOf_length]; exact hj) =
      ⟨((lvA c (lvl + j) lvs[j] (osLevels c lvl (lvs.take j) s).2).filterMap Main.Stmt.callS).map
          (Main.mkCall σ),
        Main.mkCall σ (sqCallS c (lvl + j)
          (osLevelA c (lvl + j) lvs[j] (osLevels c lvl (lvs.take j) s).2).2.1.k),
        ((lvB c (lvl + j) lvs[j] (osLevels c lvl (lvs.take j) s).2).filterMap Main.Stmt.callS).map
          (Main.mkCall σ)⟩
  | _, [], _, _, hj => absurd hj (by simp)
  | lvl, lv :: rest, s, 0, _ => by
    simp only [osLvKOf, List.getElem_cons_zero, Nat.add_zero, List.take_zero, lvM_state]
    rfl
  | lvl, lv :: rest, s, j + 1, hj => by
    have ih := osLvKOf_get σ c (lvl + 1) rest (osLevel c lvl lv s).2 j (by simpa using hj)
    simp only [osLvKOf, List.getElem_cons_succ, ih, show lvl + 1 + j = lvl + (j + 1) by omega]
    rfl

/-- A call's callee is one its block names. -/
theorem mem_cnames {σ : Val} {l : List Stmt} {c : Call}
    (h : c ∈ (l.filterMap Main.Stmt.callS).map (Main.mkCall σ)) : c.f ∈ cnames l := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  refine List.mem_map.mpr ⟨x, hx, ?_⟩
  obtain ⟨cv, f, a, r⟩ := x
  cases cv <;> rfl

/-- **The callees a level names before its squeezes have kinds.** -/
theorem lvA_named {c : OsCfg} (hN : OsNames c) {l : ℕ} (hl : l < c.levels.length) {f : String}
    (hf : f ∈ lvANames c l (lvAt c l)) : ∃ K, osKindOf f = some K := by
  simp only [lvANames, List.mem_append, List.mem_replicate, List.mem_singleton] at hf
  rcases hf with ((⟨-, rfl⟩ | hf) | rfl)
  · exact ⟨_, osKindOf_fold⟩
  · split_ifs at hf with hfin
    · rw [List.mem_singleton] at hf; subst hf; exact ⟨_, hN.fm⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl
      · exact ⟨_, osKindOf_can⟩
      · exact ⟨_, osKindOf_can⟩
      · exact ⟨_, hN.ood l hl hfin⟩
  · exact ⟨_, hN.grind l hl⟩

/-- **The callees a level names after its squeezes, but `opening_queries`, have kinds.** -/
theorem lvB_named {c : OsCfg} (hN : OsNames c) {l : ℕ} (hl : l < c.levels.length) {f : String}
    (hf : f ∈ lvBNames l (lvAt c l)) (hq : f ≠ osQueriesName l (lvAt c l)) :
    ∃ K, osKindOf f = some K := by
  simp only [lvBNames, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact ⟨_, hN.rw l hl⟩
  · exact ⟨_, hN.cap l hl⟩
  · exact absurd rfl hq

/-- **The tail's callees have kinds.** -/
theorem tail_named {c : OsCfg} {s : OsSt} {f : String} (hf : f ∈ cnames (osTail c s).1) :
    ∃ K, osKindOf f = some K := by
  rw [osTail_cnames, List.mem_replicate] at hf
  rw [hf.2]; exact ⟨_, osKindOf_fold⟩

/-- **The finish's callees, but the residual loops, have kinds.** -/
theorem finish_named {c : OsCfg} (hN : OsNames c) {st : OsSt} {tch : ℕ} {f : String}
    (hf : f ∈ cnames (osFinishA c st tch)) (hr : ∀ l < c.levels.length, f ≠ c.resLoop l) :
    ∃ K, osKindOf f = some K := by
  rw [osFinishA_cnames, List.mem_cons, List.mem_map] at hf
  rcases hf with rfl | ⟨l, hl, rfl⟩
  · exact ⟨_, hN.ffm⟩
  · exact absurd rfl (hr l (by simpa using hl))

end
end LeanVM.Guest.B1
