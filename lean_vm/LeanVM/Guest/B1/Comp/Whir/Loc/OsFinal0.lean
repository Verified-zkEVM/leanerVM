/-
  LeanVM.Guest.B1.Comp.Whir.Loc.OsFinal0

  A run's kit over a completeness model (`Whir/OsFinal0.lean`)
-/

module

public import LeanVM.Guest.B1.Whir.OsFinal0
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsAsm3

/-!
# A run's kit over a completeness model (`Whir/OsFinal0.lean`)
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

/-- The state after the levels, of a run's data. -/
def OsData.endLW (Ht : Bytes → Digest) (cfg : OsCfg) (d : OsData) : Digest × ℕ × WhirState :=
  osLvsEndW Ht cfg d.xs 0 (d.cv0W Ht) 2 (osW0 d.target d.xs) (d.roots0 cfg) d.Hs

/-- **What `open_stacked`'s completeness uses of a run.** -/
structure OsRunKitC (CM : CompModel) (Ht : Bytes → Digest) (cfg : OsCfg) (μ : ℕ) (Lall : List Whir.Level) (d : OsData) (w : WhirEnd) : Prop where
  x2 : 2 ≤ d.xs.length
  len : d.Hs.length = cfg.levels.length
  ah0 : obsCvM CM.hm d.cv (d.xs.getD 0 0) = some (obsCvW Ht d.cv (d.xs.getD 0 0))
  ah1 : obsCvM CM.hm (obsCvW Ht d.cv (d.xs.getD 0 0)) (d.xs.getD 1 0) = some (d.cv0W Ht)
  chain : ∃ (sp' : St) (Q : List (ℕ × List (ℕ × Opening))), (∀ x ∈ Q, BatchAgreesW Ht x.1 x.2) ∧
    OsChainC CM.hm Ht cfg μ (cfg.lv 0).folds d.xs Lall w sp' Q 0 (d.cv0W Ht) 2 (osW0 d.target d.xs) d.os (d.roots0 cfg) d.Hs
  tail : ∃ (ospT : List Opening) (rootsT : List (Digest × ℕ × ℕ)),
    RunsW Ht (foldRounds (cfg.yrLog - 1) ⟨(d.endLW Ht cfg).2.2.target, (d.endLW Ht cfg).2.2.quad, [], []⟩ [])
      ⟨(d.endLW Ht cfg).1, d.xs.drop (d.endLW Ht cfg).2.1, ospT, rootsT⟩ (d.w1t, d.chst)
      ⟨d.cv1t, d.xs.drop ((d.endLW Ht cfg).2.1 + 2 * (cfg.yrLog - 1)), ospT, rootsT⟩ ∧
    AnsRun CM.hm.H Ht (foldRounds (cfg.yrLog - 1) ⟨(d.endLW Ht cfg).2.2.target, (d.endLW Ht cfg).2.2.quad, [], []⟩ [])
      ⟨(d.endLW Ht cfg).1, d.xs.drop (d.endLW Ht cfg).2.1, ospT, rootsT⟩
  sqT : sqCvM CM.hm d.cv1t = some (sqCvW Ht d.cv1t)
  chst : d.chst.length = cfg.yrLog - 1
  w : w = ⟨((d.endLW Ht cfg).2.2.folds ++ d.tfW Ht).drop (cfg.lv 0).folds ++ ((d.endLW Ht cfg).2.2.folds ++ d.tfW Ht).take (cfg.lv 0).folds,
    (d.endLW Ht cfg).2.2.glued.foldl (fun w c ↦ w + c.scalar * c.weightAt ((d.endLW Ht cfg).2.2.folds.drop c.foldStart ++ d.tfW Ht)) 0,
    multilinearEval (d.fmsgCW Ht cfg) (d.tfW Ht), polyEval d.w1t.quad (d.lastW Ht)⟩

/-- **A run's kit.** -/
theorem os_kit_of_runC {cfg : OsCfg} {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) {target : E}
    {cv cv' : Digest} {xs : List E} {os : List Opening} {root : Digest} {roots' : List (Digest × ℕ × ℕ)} {w : WhirEnd}
    (hHt : ∀ x d, CM.H x = some d → d = Ht x)
    (h : RunsWithM CM.hm (whirOpen μ r target) cv xs os [(root, stackShape μ r)] w cv' roots')
    (hcap : CapAgreesW Ht μ r root cv xs os target) :
    ∃ d : OsData, d.xs = xs ∧ d.cv = cv ∧ d.target = target ∧ d.root = root ∧ OsRunKitC CM Ht cfg μ Lall d w := by
  obtain ⟨hx2, a0, a1, Hs, hHl, hch⟩ := os_open_invC (M := CM.hm) hok hHt h
  obtain ⟨w1, chs, cv1, ospT, rootsT, hr, hA, hsq, hcl, hw⟩ := os_tail_dataC (Ht := Ht) (CM := CM) hok hHl hch
  refine ⟨⟨xs, cv, target, root, os, Hs, w1, chs, cv1⟩, rfl, rfl, rfl, rfl, hx2, hHl, a0, a1,
    ⟨_, _, fun x hx => hcap x hx, hch⟩, ⟨ospT, rootsT, hr, hA⟩, hsq, hcl, ?_⟩
  rw [hw]; rfl

end
end LeanVM.Guest.B1
