/-
  LeanVM.Guest.B1.Comp.Whir.LocT.OsInstBaseT

  A level's `opening_queries` by trees decoding to its openings, within `open_stacked`'s callees'
  bound (`Loc/OsInstBaseB.lean`'s `queries` field with the decoding).
-/

module

public import LeanVM.Guest.B1.Comp.Whir.LocT.OsFinal3T
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsInstBaseB

/-!
# The queries' tree forms within the bound

`osLvKidsAtBT_mkC`: a level's `opening_queries` placed by trees decoding to its openings, at the
bound of its frame, chain and loop frames, within the callees' bound `osBdC`.
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

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

theorem osLvKidsAtBT_mkC {k : ℕ} {h1 : OsCalleesAtBC CM fs cert k} {hm : OsCalleesMaxC CM h1}
    {hp : OsPureSizesC CM fs} {cfg : OsCfg} {l : ℕ} (hl : l < cfg.levels.length) {loop : String}
    (hq : OqCompleteAtBCT CM Ht fs cert κ (if l = 0 then 1 else 0) (2 ^ (cfg.lv l).folds) (cfg.lv l).depth
      (cfg.lv l).capDepth (cfg.lv l).queriesFn fun n => fs (cfg.lv l).queriesFn + (n + 1) + (n + 1) * fs loop)
    (hloop : osOqLoop (cfg.lv l).queriesFn = loop) :
    ∃ B, OqCompleteAtBCT CM Ht fs cert κ (if l = 0 then 1 else 0) (2 ^ (cfg.lv l).folds) (cfg.lv l).depth
      (cfg.lv l).capDepth (cfg.lv l).queriesFn B ∧ B (cfg.lv l).queries ≤ osBdC CM fs hm hp cfg (cfg.lv l).queriesFn :=
  ⟨_, hq, le_trans (by rw [← hloop]; exact le_max_of_le_left (by simp)) (osBd_lvC (CM := CM) hm hp cfg hl _)⟩

end
end LeanVM.Guest.B1
