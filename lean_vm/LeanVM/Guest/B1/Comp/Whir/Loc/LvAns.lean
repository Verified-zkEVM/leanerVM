/-
  LeanVM.Guest.B1.Comp.Whir.Loc.LvAns

  A level's openings, answered by the model: its cap's climbs and its queries' (`OqAns`).
-/

module

public import LeanVM.Guest.B1.Comp.Whir.Loc.OsKidsLv

/-!
# A level's openings, answered

From the chain's facts of a level over a model (`OsLvFactsW`, its `OsLvAns`) and the model agreeing
with `Ht` where it answers: every opening of the level is answered at its position
(`OsData.lv_ansC`, from `openAll_answered`), so its cap's climbs are (`osCapAns_of`) and every
query's leaf and climb below the cap are (`oqAns_of_opening`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub
open LeanVM.E2E.Complete

@[expose] public section

variable {Ht : Bytes → Digest} {CM : CompModel}

/-- **A cap's climbs are answered** when each of its openings is. -/
theorem osCapAns_of {root : Digest} {depth width : ℕ} {qs : List (ℕ × Opening)}
    (h : ∀ a ∈ qs, OpeningAns CM.H Ht root depth width a.1 a.2) : OsCapAns CM Ht depth qs := by
  intro a ha l hl
  obtain ⟨-, hp, -, hc, -⟩ := h a ha
  exact hc l (by rw [hp]; exact hl)

theorem climbAtW_take {D : Digest} {q : ℕ} {sibs : List Digest} {pd l : ℕ} (hl : l ≤ pd) :
    climbAtW Ht D q (sibs.take pd) l = climbAtW Ht D q sibs l := by
  unfold climbAtW
  rw [List.take_take, Nat.min_eq_left hl]

theorem climbLvlBytes_take {D : Digest} {q : ℕ} {sibs : List Digest} {pd l : ℕ} (hl : l < pd) :
    climbLvlBytes Ht D q (sibs.take pd) l = climbLvlBytes Ht D q sibs l := by
  have hg : (sibs.take pd).getD l default = sibs.getD l default := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hl, ↓reduceIte]
  unfold climbLvlBytes
  rw [hg, climbAtW_take hl.le]

/-- **A query below the cap is answered** when its opening is. -/
theorem oqAns_of_opening {root : Digest} {height width q pd : ℕ} {o : Opening}
    (h : OpeningAns CM.H Ht root height width q o) (hpd : pd ≤ height) :
    OqAns CM Ht pd o.leaf q (o.path.take pd) := by
  obtain ⟨-, hp, hl, hc, -⟩ := h
  refine ⟨hl, fun l hl' => ?_⟩
  rw [climbLvlBytes_take hl', climbAtW_take (by omega)]
  exact hc l (by omega)

namespace OsData

variable {cfg : OsCfg} {d : OsData}

/-- **A level's openings are answered**, each at its position. -/
theorem lv_ansC (hHt : ∀ x d, CM.H x = some d → d = Ht x) {μ : ℕ} {Lall : List Whir.Level}
    {Q : List (ℕ × List (ℕ × Opening))} {l : ℕ}
    (hF : OsLvFactsW CM.hm Ht cfg μ d.xs Lall Q (d.lvW Ht cfg l)) (hlv : (d.lvW Ht cfg l).lvl = l) :
    ∀ a ∈ (osHQsW Ht cfg l d.xs (d.lvW Ht cfg l).p (d.lvW Ht cfg l).H.cv1).zip (d.lvW Ht cfg l).osp,
      OpeningAns CM.H Ht (d.rtW Ht cfg l) (cfg.lv l).depth (oqR (if l = 0 then 1 else 0) (2 ^ (cfg.lv l).folds))
        a.1 a.2 := by
  obtain ⟨rt', hrt'⟩ := hF.root
  obtain ⟨rt, hh, ww, hr, hoa⟩ := hF.ok.open_
  have ho := hF.ans.open_ rt hh ww hr
  rw [hlv] at hrt' hr hoa ho
  have hlt : l < (d.lvW Ht cfg l).roots.length := by
    rcases Nat.lt_or_ge l (d.lvW Ht cfg l).roots.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hrt'; cases hrt'
  have e : (osHRootsEnd cfg l (d.lvW Ht cfg l).roots (d.lvW Ht cfg l).H)[l]? = (d.lvW Ht cfg l).roots[l]? := by
    unfold osHRootsEnd; split
    · rfl
    · exact List.getElem?_append_left hlt
  rw [e, hrt'] at hr
  simp only [Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl, rfl⟩ := hr
  have hrt : d.rtW Ht cfg l = rt' := by
    unfold rtW; rw [List.getD_eq_getElem?_getD, hrt']; rfl
  rw [hrt]
  have hs : openAll (m := Option) CM.H rt' (cfg.lv l).depth (oqR (if l = 0 then 1 else 0) (2 ^ (cfg.lv l).folds))
      (osHQsW Ht cfg l d.xs (d.lvW Ht cfg l).p (d.lvW Ht cfg l).H.cv1) (d.lvW Ht cfg l).osp =
      some (some ((d.lvW Ht cfg l).H.rows, (d.lvW Ht cfg l).H.osq)) := by
    rw [← hoa]; exact ho
  exact (openAll_answered hHt hs).2

end OsData

end
end LeanVM.Guest.B1
