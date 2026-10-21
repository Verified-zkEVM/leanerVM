/-
  LeanVM.Guest.B1.Comp.Whir.Loc.OsAsm3

  The tail's data over a completeness model (`Whir/OsAsm3.lean`)
-/

module

public import LeanVM.Guest.B1.Whir.OsAsm3
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsAsm2

/-!
# The tail's data over a completeness model (`Whir/OsAsm3.lean`)
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

/-- **The tail of a run**, from the levels' data. -/
theorem os_tail_dataC {cfg : OsCfg} {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) {xs : List E}
    {cv0 : Digest} {w0 : WhirState} {os : List Opening} {roots : List (Digest × ℕ × ℕ)} {Hs : List OsLvH}
    {e : WhirEnd} {sp' : St} {Q : List (ℕ × List (ℕ × Opening))} (hHl : Hs.length = cfg.levels.length)
    (hch : OsChainC CM.hm Ht cfg μ (cfg.lv 0).folds xs Lall e sp' Q 0 cv0 2 w0 os roots Hs) :
    ∃ (w1 : WhirState) (chs : List E) (cv1 : Digest) (ospT : List Opening) (rootsT : List (Digest × ℕ × ℕ)),
      RunsW Ht (foldRounds (cfg.yrLog - 1) ⟨(osLvsEndW Ht cfg xs 0 cv0 2 w0 roots Hs).2.2.target,
          (osLvsEndW Ht cfg xs 0 cv0 2 w0 roots Hs).2.2.quad, [], []⟩ [])
        ⟨(osLvsEndW Ht cfg xs 0 cv0 2 w0 roots Hs).1, xs.drop (osLvsEndW Ht cfg xs 0 cv0 2 w0 roots Hs).2.1, ospT, rootsT⟩
        (w1, chs) ⟨cv1, xs.drop ((osLvsEndW Ht cfg xs 0 cv0 2 w0 roots Hs).2.1 + 2 * (cfg.yrLog - 1)), ospT, rootsT⟩ ∧
      AnsRun CM.hm.H Ht (foldRounds (cfg.yrLog - 1) ⟨(osLvsEndW Ht cfg xs 0 cv0 2 w0 roots Hs).2.2.target,
          (osLvsEndW Ht cfg xs 0 cv0 2 w0 roots Hs).2.2.quad, [], []⟩ [])
        ⟨(osLvsEndW Ht cfg xs 0 cv0 2 w0 roots Hs).1, xs.drop (osLvsEndW Ht cfg xs 0 cv0 2 w0 roots Hs).2.1, ospT, rootsT⟩ ∧
      sqCvM CM.hm cv1 = some (sqCvW Ht cv1) ∧
      chs.length = cfg.yrLog - 1 ∧
      e = ⟨((osLvsEndW Ht cfg xs 0 cv0 2 w0 roots Hs).2.2.folds ++ (chs ++ [challengeOf (sqCvW Ht cv1)])).drop (cfg.lv 0).folds ++
          ((osLvsEndW Ht cfg xs 0 cv0 2 w0 roots Hs).2.2.folds ++ (chs ++ [challengeOf (sqCvW Ht cv1)])).take (cfg.lv 0).folds,
        (osLvsEndW Ht cfg xs 0 cv0 2 w0 roots Hs).2.2.glued.foldl (fun w c ↦ w + c.scalar * c.weightAt
          ((osLvsEndW Ht cfg xs 0 cv0 2 w0 roots Hs).2.2.folds.drop c.foldStart ++ (chs ++ [challengeOf (sqCvW Ht cv1)]))) 0,
        multilinearEval (osHMs cfg cfg.yrLevel xs ((osLvsListW Ht cfg xs 0 cv0 2 w0 os roots Hs).getD cfg.yrLevel default).p)
          (chs ++ [challengeOf (sqCvW Ht cv1)]),
        polyEval w1.quad (challengeOf (sqCvW Ht cv1))⟩ := by
  have hn := hok.len2
  have hne : Hs ≠ [] := by intro h; rw [h] at hHl; simp at hHl; omega
  have ht := os_chain_tailC Hs 0 _ _ _ _ _ hch
  rw [os_lvsLast_eqC (Ht := Ht) cfg xs Hs 0 cv0 2 w0 os roots hne] at ht
  set Ls := osLvsListW Ht cfg xs 0 cv0 2 w0 os roots Hs
  have hLl : Ls.length = cfg.levels.length := by rw [os_lvsList_lengthC (Ht := Ht), hHl]
  have hlast : Ls.getLastD default = Ls.getD cfg.yrLevel default := by
    rw [hok.yrLevel, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, hLl, List.getD_eq_getElem?_getD]
  have hlv : (Ls.getD cfg.yrLevel default).lvl = cfg.yrLevel := by
    rw [List.getD_eq_getElem _ _ (by rw [hLl, hok.yrLevel]; omega)]
    have := os_lvsList_lvlC (Ht := Ht) cfg xs Hs 0 cv0 2 w0 os roots cfg.yrLevel (by rw [hLl, hok.yrLevel]; omega)
    simpa using this
  rw [hlast, hlv] at ht
  have hml : μ - osLevelF cfg cfg.yrLevel = cfg.yrLog := by
    rw [hok.yrLevel, hok.nFolds, ← hok.total]; omega
  rw [hml] at ht
  obtain ⟨w1, chs, st1, hr, hA, hsq, he, -⟩ := os_tailOpen_invC (M := CM.hm) (by have := hok.yr2; omega) ht.1 ht.2
  obtain ⟨hs1, ho1, hr1, -⟩ := os_foldRounds_stW hr
  obtain ⟨chs', -, hc2, hc3⟩ := os_foldRounds_foldsW hr
  simp only [List.nil_append] at hc2
  refine ⟨w1, chs, st1.cv, (Ls.getD cfg.yrLevel default).H.osq, (Ls.getD cfg.yrLevel default).roots, ?_, hA, hsq,
    by rw [hc2, hc3], he⟩
  have est : st1 = ⟨st1.cv, xs.drop ((osLvsEndW Ht cfg xs 0 cv0 2 w0 roots Hs).2.1 + 2 * (cfg.yrLog - 1)),
      (Ls.getD cfg.yrLevel default).H.osq, (Ls.getD cfg.yrLevel default).roots⟩ := by
    cases st1; simp only at hs1 ho1 hr1 ⊢; rw [hs1, ho1, hr1]
  rw [← est]; exact hr

end
end LeanVM.Guest.B1
