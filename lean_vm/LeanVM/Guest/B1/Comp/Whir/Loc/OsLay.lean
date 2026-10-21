/-
  LeanVM.Guest.B1.Comp.Whir.Loc.OsLay

  The buffers' layout over a total hash (`Whir/OsLay.lean`)
-/

module

public import LeanVM.Guest.B1.Whir.OsLay
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsCont

/-!
# The buffers' layout over a total hash (`Whir/OsLay.lean`)
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.E2E.Complete
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol (Digest)

@[expose] public section

variable {Ht : Bytes → Digest} {CM : CompModel}

private theorem os_forall₂_appendC {a b : List (List E)} {c d : List ℕ}
    (h1 : List.Forall₂ (fun c s => c.length ≤ s) a c) (h2 : List.Forall₂ (fun c s => c.length ≤ s) b d) :
    List.Forall₂ (fun c s => c.length ≤ s) (a ++ b) (c ++ d) := List.rel_append h1 h2

private theorem os_forall₂_rangeC {f : ℕ → List (List E)} {g : ℕ → List ℕ} :
    ∀ n, (∀ l < n, List.Forall₂ (fun c s => c.length ≤ s) (f l) (g l)) →
      List.Forall₂ (fun c s => c.length ≤ s) ((List.range n).flatMap f) ((List.range n).flatMap g)
  | 0, _ => by simp
  | n + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append]
    exact os_forall₂_appendC (os_forall₂_rangeC n fun l hl => h l (by omega)) (by simpa using h n (by omega))

/-- **The honest words fit the buffers.** -/
theorem os_own_fitsC {cfg : OsCfg} (hlay : OsLayoutOk cfg) (hyr5 : cfg.yrLog ≤ 5) {d : OsData} (hch : d.chst.length + 1 ≤ cfg.yrLog)
    {Q : List E} (hQ : Q.length ≤ cfg.posLen) (hfl : (d.fchCW Ht cfg).length ≤ cfg.nFolds) :
    List.Forall₂ (fun c s => c.length ≤ s) (d.ownQW Ht cfg Q) (osSizes cfg) := by
  have hseg : ∀ (sz : ℕ) (segs : List (ℕ × List E)), (osSegC sz segs).length ≤ sz := fun sz segs => by
    rw [os_length_segC]
  unfold OsData.ownQW osSizes
  refine os_forall₂_appendC (os_forall₂_appendC (os_forall₂_appendC ?_ ?_) ?_) ?_
  · simp only [osHeadSizes, OsData.capsCW, OsData.flagsCW, OsData.rootsCW, OsData.qwCW, OsData.qposCW,
      OsData.oodzCW, OsData.oodCW, OsData.betasCW, OsData.fmsgCW, osHMs]
    refine .cons (hseg _ _) (.cons (hseg _ _) (.cons ?_ (.cons (hseg _ _) (.cons hfl (.cons ?_
      (.cons (hseg _ _) (.cons (hseg _ _) (.cons hQ (.cons (hseg _ _) (.cons (hseg _ _) .nil))))))))))
    · simp
    · simp
  · rw [show (List.range cfg.levels.length).flatMap (fun _ => [2 * (cfg.maxSq + 1), cfg.maxIl]) =
        (List.range cfg.levels.length).flatMap (fun l => [2 * (cfg.maxSq + 1), cfg.maxIl]) from rfl]
    refine os_forall₂_rangeC _ fun l hl => .cons ?_ (.cons ?_ .nil)
    · simp only [OsData.sqzCW, List.length_flatMap, List.length_cons, List.length_nil, List.map_const',
        List.length_range, List.sum_replicate, smul_eq_mul]
      have := hlay.sq l hl; omega
    · simp [OsData.rewCW]; exact hlay.il l hl
  · refine .cons ?_ (.cons (by simp [OsData.ptCW]) (.cons (hseg _ _) (.cons (hseg _ _)
      (.cons (by simp [OsData.ichCW]) .nil))))
    simp [OsData.tchCW, OsData.tfW]; omega
  · rw [show List.replicate cfg.levels.length (cfg.maxQ + 1) =
        (List.range cfg.levels.length).map (fun _ => cfg.maxQ + 1) by simp [List.map_const']]
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr fun l hl => ?_
    simp only [OsData.chvCW, List.length_map, List.length_range]
    have := hlay.qw l (List.mem_range.mp hl); omega

end
end LeanVM.Guest.B1
