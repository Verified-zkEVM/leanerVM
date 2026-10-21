/-
  LeanVM.Guest.B1.Comp.Whir.Loc.OsLayout

  The levels of a run over a total hash (`Whir/OsLayout.lean`)
-/

module

public import LeanVM.Guest.B1.Whir.OsLayout
public import LeanVM.Guest.B1.Comp.Whir.Loc.Support

/-!
# The levels of a run over a total hash (`Whir/OsLayout.lean`)
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub
open LeanVM.E2E.Complete
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol (Digest)

@[expose] public section

variable {Ht : Bytes → Digest} {CM : CompModel}

/-- The levels from level `lvl`. -/
def osLvsListW (Ht : Bytes → Digest) (cfg : OsCfg) (xs : List E) :
    ℕ → Digest → ℕ → WhirState → List Opening → List (Digest × ℕ × ℕ) → List OsLvH → List OsLvP
  | _, _, _, _, _, _, [] => []
  | lvl, cv, p, w, osp, roots, H :: Hs =>
    ⟨lvl, cv, p, w, osp, roots, H⟩ :: osLvsListW Ht cfg xs (lvl + 1) (osHCvEndW Ht cfg lvl xs p H.cv1) (osHPEnd cfg lvl p)
      (osHWEndW Ht cfg lvl xs p H) H.osq (osHRootsEnd cfg lvl roots H) Hs

theorem os_lvsList_lengthC (cfg : OsCfg) (xs : List E) : ∀ (Hs : List OsLvH) lvl cv p w osp roots,
    (osLvsListW Ht cfg xs lvl cv p w osp roots Hs).length = Hs.length
  | [], _, _, _, _, _, _ => rfl
  | H :: Hs, lvl, cv, p, w, osp, roots => by
    simp only [osLvsListW, List.length_cons, os_lvsList_lengthC cfg xs Hs]

/-- A level's memory facts, from the levels'. -/
theorem os_lvsMem_memC {rd : Reader} {cfg : OsCfg} {xs : List E} {cur : E} {P : OsPtrs} {sqz : ℕ → E} :
    ∀ (Hs : List OsLvH) lvl cv p w osp roots,
      (∀ L ∈ osLvsListW Ht cfg xs lvl cv p w osp roots Hs,
        OsLvMemW Ht rd cfg L.lvl xs L.p L.H (L.roots.getD L.lvl default).1 P (sqz L.lvl) cur) →
      OsLvsMemW Ht rd cfg xs cur P sqz lvl cv p w roots Hs
  | [], _, _, _, _, _, _, _ => trivial
  | _ :: Hs, _, _, _, _, _, _, h =>
    ⟨h _ List.mem_cons_self, os_lvsMem_memC Hs _ _ _ _ _ _ fun L hL => h L (List.mem_cons_of_mem _ hL)⟩

/-- A level's call hypotheses, from the levels'. -/
theorem os_lvsCallH_memC {CA CB Csq : ℕ → CallRel} {cfg : OsCfg} {xs : List E} {cur : E} {P : OsPtrs}
    {sqz rew : ℕ → E} : ∀ (Hs : List OsLvH) lvl cv p w osp roots,
      (∀ L ∈ osLvsListW Ht cfg xs lvl cv p w osp roots Hs,
        OsLvCallHC CM Ht (CA L.lvl) (CB L.lvl) (Csq L.lvl) cfg L.lvl xs L.p L.H (L.roots.getD L.lvl default).1 P (sqz L.lvl)
          (rew L.lvl) cur) →
      OsLvsCallHC CM Ht CA CB Csq cfg xs cur P sqz rew lvl p w roots Hs
  | [], _, _, _, _, _, _, _ => trivial
  | _ :: Hs, _, _, _, _, _, _, h =>
    ⟨h _ List.mem_cons_self, os_lvsCallH_memC Hs _ _ _ _ _ _ fun L hL => h L (List.mem_cons_of_mem _ hL)⟩

/-- What the chain says of a level. -/
structure OsLvFactsW (M : HashModel) (Ht : Bytes → Digest) (cfg : OsCfg) (μ : ℕ) (xs : List E) (Lall : List Whir.Level)
    (Q : List (ℕ × List (ℕ × Opening))) (L : OsLvP) : Prop where
  ok : OsLvOkW Ht cfg L.lvl xs L.p μ (Lall.getD L.lvl default) L.cv L.w L.osp L.roots L.H
  root : ∃ rt, L.roots[L.lvl]? = some (rt, (cfg.lv L.lvl).depth,
    oqR (if L.lvl = 0 then 1 else 0) (2 ^ (cfg.lv L.lvl).folds))
  step : ((cfg.lv L.lvl).depth, (osHQsW Ht cfg L.lvl xs L.p L.H.cv1).zip L.osp) ∈ Q
  ans : OsLvAns M Ht cfg L.lvl xs L.p (Lall.getD L.lvl default) L.cv L.w L.osp L.roots L.H

/-- **The chain's facts of each level.** -/
theorem os_chain_memC {cfg : OsCfg} {μ lane : ℕ} {xs : List E} {Lall : List Whir.Level} {e : WhirEnd} {sp' : St}
    {Q : List (ℕ × List (ℕ × Opening))} : ∀ (Hs : List OsLvH) lvl cv p w osp roots,
      OsChainC CM.hm Ht cfg μ lane xs Lall e sp' Q lvl cv p w osp roots Hs →
      ∀ L ∈ osLvsListW Ht cfg xs lvl cv p w osp roots Hs, OsLvFactsW CM.hm Ht cfg μ xs Lall Q L
  | [], _, _, _, _, _, _, h => h.elim
  | H :: Hs, lvl, cv, p, w, osp, roots, h => by
    obtain ⟨hok, hans, ⟨rt, hrt, hq⟩, hl, hn⟩ := h
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hL'
    · exact ⟨hok, ⟨rt, hrt⟩, hq, hans⟩
    · by_cases hy : lvl = cfg.yrLevel
      · obtain ⟨rfl, -⟩ := hl hy
        simp [osLvsListW] at hL'
      · exact os_chain_memC Hs _ _ _ _ _ _ (hn hy) L hL'

/-- The levels' indices. -/
theorem os_lvsList_lvlC (cfg : OsCfg) (xs : List E) : ∀ (Hs : List OsLvH) lvl cv p w osp roots,
    ∀ i (hi : i < (osLvsListW Ht cfg xs lvl cv p w osp roots Hs).length),
      ((osLvsListW Ht cfg xs lvl cv p w osp roots Hs)[i]).lvl = lvl + i
  | [], _, _, _, _, _, _, i, hi => absurd hi (by simp [osLvsListW])
  | H :: Hs, lvl, cv, p, w, osp, roots, i, hi => by
    rcases i with _ | i
    · rfl
    · simp only [osLvsListW, List.getElem_cons_succ]
      rw [os_lvsList_lvlC cfg xs Hs _ _ _ _ _ _ i (by simpa [osLvsListW] using hi)]
      ring

end
end LeanVM.Guest.B1
