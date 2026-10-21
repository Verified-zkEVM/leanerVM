/-
  LeanVM.E2E.Complete.DecodeMain

  `main`'s frame on the honest memory: the words V_I's decoder reads off it are the honest tree's
  root valuation's.
-/

module

public import LeanVM.E2E.Complete.DecodeSplit
public import LeanVM.Guest.B2C.B2B
public import LeanVM.Guest.B2C.FrameAll

/-!
# `main`'s frame, decoded

`mainFrame L = valG L 1 (certOf 1)` reads `main`'s frame cells at word `0` of the memory. On the
honest memory of a tree of `main` (`HonestAtB`), B2's frame facts (`B2HypsB.frame`,
`FrameHolds.val`) put every value `main`'s path names in its cell:

* `mainPreUses`: the values `main`'s straight-line prologue names (the decoder's words among
  them);
* `mainFrame_eq`: at such a value with its cell in the frame, `mainFrame` is the root valuation's.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (mainPre mainEvs walk_mainBody mainBody)
open LeanVM.Guest.B2C (cellJ fsN)

@[expose] public section

/-- The values `main`'s prologue's atoms name. -/
def mainPreUses : List V :=
  mainPre.flatMap fun s => match s with
    | .atom a => atomUses a
    | _ => []

theorem mem_mainEvs_uses {σ : Val} {v : V} (hv : v ∈ mainPreUses) :
    v ∈ (mainEvs σ).flatMap Ev.uses := by
  obtain ⟨s, hs, hv⟩ := List.mem_flatMap.mp hv
  cases s with
  | atom a =>
      refine List.mem_flatMap.mpr ⟨.atom a, ?_, by simpa [Ev.uses] using hv⟩
      rw [mainEvs]
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, hs, by simp [slEvs]⟩)
  | _ => simp at hv

theorem coreOf_one_body : (coreOf 1).body = mainBody := B1.Main.core0_body

/-- **`main`'s frame reads its root valuation** at a value its prologue names, its cell in the
frame. -/
theorem mainFrame_eq {S : BlakeSem} (hB : B2C.B2HypsB S) {hdr : E × E} {rd : Reader} {T : Tree}
    (hname : T.name = "main")
    (hH : HonestAtB S coreProgram B2C.fs B2C.H B2C.C hdr T B2C.cert rd [] [])
    {σ : Val} {bufs : List ℕ} {ks : List Tree} (hT : T = .node "main" σ bufs ks) {v : V}
    (hv : v ∈ mainPreUses) (h2 : 2 ≤ cellJ 1 v) (hn : cellJ 1 v < fsN 1) :
    mainFrame (honest coreProgram B2C.fs B2C.H B2C.C hdr T) v = σ v := by
  obtain ⟨I, hI, hIt, hfp, -⟩ := root_inst (P := coreProgram) (fs := B2C.fs) (H := B2C.H) (hdr := hdr)
    (T := T)
  have hw : walk σ (coreOf 1).body = .ret (mainEvs σ) [] := by
    rw [coreOf_one_body]; exact walk_mainBody σ
  have hF := hB.frame hdr rd T hname hH I hI "main" σ bufs ks (by rw [hIt, hT]) 1 B2C.idxOf_main
    (mainEvs σ) [] hw
  have := hF.val v (by
    simp only [B2C.namedOf, List.mem_append]
    exact Or.inl (Or.inr (mem_mainEvs_uses hv))) h2 hn
  rw [hfp, Nat.zero_add] at this
  show (Check.wd (honest coreProgram B2C.fs B2C.H B2C.C hdr T) 1 ((certOf 1).locs.getD v.idx 0)) = σ v
  unfold Check.wd
  rw [one_mul]
  show ((honest coreProgram B2C.fs B2C.H B2C.C hdr T).read (Parameters.gpow (cellJ 1 v))).getD 0 = σ v
  rw [this]
  rfl

end
end LeanVM.E2E.Complete
