/-
  LeanVM.Guest.B1.Comp.Whir.LocT.OsRunT

  A run of the stacked opening over a completeness model reads exactly the guest's stream words and
  openings.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.Loc.OsFinal0
public import LeanVM.Guest.B1.Comp.Whir.LoadsT.OsLen

/-!
# The run's words and openings, exactly

`os_kit_of_runCT`: `os_kit_of_runC` with what the run's end gives: the stream has exactly
`osStreamLen cfg` words (`open_stacked`'s reads), and the last level leaves no opening.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub
open LeanVM.E2E.Complete
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol (Digest)

@[expose] public section

variable {Ht : Bytes → Digest} {CM : CompModel}

/-- The levels' end position is `osLvsPos`'s. -/
theorem osLvsEndW_pos (Ht : Bytes → Digest) (cfg : OsCfg) (xs : List E) :
    ∀ (Hs : List OsLvH) (lvl : ℕ) (cv : Digest) (p : ℕ) (w : WhirState) (roots : List (Digest × ℕ × ℕ))
      (L : List OsLvl), L.length = Hs.length → (osLvsEndW Ht cfg xs lvl cv p w roots Hs).2.1 = osLvsPos cfg lvl L p
  | [], _, _, _, _, _, [], _ => rfl
  | _ :: Hs, lvl, _, p, _, roots, _ :: L, h =>
    osLvsEndW_pos Ht cfg xs Hs (lvl + 1) _ _ _ _ L (by simpa using h)
  | [], _, _, _, _, _, _ :: _, h => absurd h (by simp)
  | _ :: _, _, _, _, _, _, [], h => absurd h (by simp)

/-- **A run's kit, its stream and openings consumed exactly.** -/
theorem os_kit_of_runCT {cfg : OsCfg} {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) {target : E}
    {cv cv' : Digest} {xs : List E} {os : List Opening} {root : Digest} {roots' : List (Digest × ℕ × ℕ)} {w : WhirEnd}
    (hHt : ∀ x d, CM.H x = some d → d = Ht x)
    (h : RunsWithM CM.hm (whirOpen μ r target) cv xs os [(root, stackShape μ r)] w cv' roots')
    (hcap : CapAgreesW Ht μ r root cv xs os target) :
    ∃ d : OsData, d.xs = xs ∧ d.cv = cv ∧ d.target = target ∧ d.root = root ∧ d.os = os ∧
      OsRunKitC CM Ht cfg μ Lall d w ∧ d.xs.length = osStreamLen cfg ∧ ((d.lvsW Ht cfg).getLastD default).H.osq = [] := by
  obtain ⟨hx2, a0, a1, Hs, hHl, hch⟩ := os_open_invC (M := CM.hm) hok hHt h
  obtain ⟨w1, chs, cv1, ospT, rootsT, hr, hA, hsq, hcl, hw⟩ := os_tail_dataC (Ht := Ht) (CM := CM) hok hHl hch
  refine ⟨⟨xs, cv, target, root, os, Hs, w1, chs, cv1⟩, rfl, rfl, rfl, rfl, rfl, ⟨hx2, hHl, a0, a1,
    ⟨_, _, fun x hx => hcap x hx, hch⟩, ⟨ospT, rootsT, hr, hA⟩, hsq, hcl, by rw [hw]; rfl⟩, ?_⟩
  -- the run's end
  have hn := hok.len2
  have hne : Hs ≠ [] := by intro h; rw [h] at hHl; simp at hHl; omega
  have ht := os_chain_tailC Hs 0 _ _ _ _ _ hch
  rw [os_lvsLast_eqC (Ht := Ht) cfg xs Hs 0 _ 2 _ os _ hne] at ht
  set Ls := osLvsListW Ht cfg xs 0 (obsCvW Ht (obsCvW Ht cv (xs.getD 0 0)) (xs.getD 1 0)) 2 (osW0 target xs) os
    [(root, (cfg.lv 0).depth, 2 ^ (cfg.lv 0).folds)] Hs with hLs
  have hLl : Ls.length = cfg.levels.length := by rw [os_lvsList_lengthC (Ht := Ht), hHl]
  have hlast : Ls.getLastD default = Ls.getD cfg.yrLevel default := by
    rw [hok.yrLevel, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, hLl, List.getD_eq_getElem?_getD]
  have hlv : (Ls.getD cfg.yrLevel default).lvl = cfg.yrLevel := by
    rw [List.getD_eq_getElem _ _ (by rw [hLl, hok.yrLevel]; omega)]
    have := os_lvsList_lvlC (Ht := Ht) cfg xs Hs 0 _ 2 _ os _ cfg.yrLevel (by rw [hLl, hok.yrLevel]; omega)
    rw [Nat.zero_add] at this
    exact this
  have hlast' := hlast
  rw [hlast, hlv] at ht
  have hml : μ - osLevelF cfg cfg.yrLevel = cfg.yrLog := by
    rw [hok.yrLevel, hok.nFolds, ← hok.total]; omega
  rw [hml] at ht
  obtain ⟨w1', chs', st1, hr', -, -, -, hst⟩ := os_tailOpen_invC (M := CM.hm) (by have := hok.yr2; omega) ht.1 ht.2
  obtain ⟨hs1, ho1, -, hlen⟩ := os_foldRounds_stW hr'
  have e1 := congrArg St.stream hst
  have e2 := congrArg St.openings hst
  simp only at e1 e2
  rw [hs1] at e1
  rw [ho1] at e2
  have hpos := osLvsEndW_pos Ht cfg xs Hs 0 (obsCvW Ht (obsCvW Ht cv (xs.getD 0 0)) (xs.getD 1 0)) 2
    (osW0 target xs) [(root, (cfg.lv 0).depth, 2 ^ (cfg.lv 0).folds)] cfg.levels hHl.symm
  refine ⟨?_, ?_⟩
  · show xs.length = osStreamLen cfg
    have hle := List.drop_eq_nil_iff.mp e1.symm
    rcases hlen with h0 | h0
    · have := hok.yr2; omega
    · unfold osStreamLen
      rw [← hpos]
      omega
  · show (Ls.getLastD default).H.osq = []
    rw [hlast']
    exact e2.symm

end
end LeanVM.Guest.B1
