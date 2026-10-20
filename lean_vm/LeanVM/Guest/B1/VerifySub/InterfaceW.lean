/-
  LeanVM.Guest.B1.VerifySub.InterfaceW

  `open_stacked`'s soundness with its openings named: a witness function of its argument and
  return words.
-/

module

public import LeanVM.Guest.B1.VerifySub.Interface

/-!
# `open_stacked`, its openings named

`SoundOpen` says that some openings exist over which the stacked opening runs. `OpenOutW` is
`OpenOut` at given openings `os`, and `SoundOpenW wO` says that the openings `wO name args rets`
are such, for every relation of `open_stacked` at a candidate `name = openName μ r` with
arguments `args` and returns `rets`: the run of `whirOpen μ r` from the stack's root reads them
(every one authenticates under the root of the level it opens, `Compile.openAll`) and ends where
the function's returns say.

`soundOpen_of_w` recovers `SoundOpen` from any witness function, and `exists_soundOpenW` builds
one from `SoundOpen` (by choice: what any witness function satisfying `SoundOpenW` gives does not
depend on how it was built).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable (rd : Reader)

/-- **`OpenOut` at the openings `os`**: from the state of `cv`, the stack's root `root` committed
with its shape, the words `xs` at the cursor and the openings `os` run `whirOpen μ r target` to
`w`; the function returns `w`'s claim, a buffer holding its point (zero-padded to `42`), its glued
weight and its residual's value; the point has `μ` coordinates. -/
def OpenOutW (μ r : ℕ) (root : Digest) (fs0 fs1 target cur : E) (rets : List E)
    (os : List Opening) : Prop :=
  ∃ (cv : Digest) (xs : List E) (w : WhirEnd) (cv' : Digest)
    (roots' : List (Digest × ℕ × ℕ)), (fs0, fs1) = digestScalars cv ∧ ReadsAt rd cur xs ∧
    RunsWith (whirOpen μ r target) cv xs os [(root, stackShape μ r)] w cv' roots' ∧
    ∃ pt, rets = [w.target, pt, w.inner, w.residual] ∧
      ReadsAt rd pt (w.point ++ List.replicate (pointCap - w.point.length) 0) ∧ w.point.length = μ

/-- **`open_stacked` is sound with the openings `wO`**: at every candidate `(μ, r)`, the relation
of `openName μ r` on the arguments `args` and the returns `rets` gives `OpenOutW` at the openings
`wO (openName μ r) args rets`. -/
def SoundOpenW (wO : String → List E → List E → List Opening) : Prop :=
  ∀ μ r, 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 →
    ∀ (root : Digest) fs0 fs1 target root0 root1 cur rets, (root0, root1) = digestScalars root →
      coreProgram.Rel rd (openName μ r) [fs0, fs1, target, root0, root1, cur] rets →
        OpenOutW rd μ r root fs0 fs1 target cur rets
          (wO (openName μ r) [fs0, fs1, target, root0, root1, cur] rets)

variable {rd}

theorem OpenOutW.openOut {μ r : ℕ} {root : Digest} {fs0 fs1 target cur : E} {rets : List E}
    {os : List Opening} (h : OpenOutW rd μ r root fs0 fs1 target cur rets os) :
    OpenOut rd μ r root fs0 fs1 target cur rets := by
  obtain ⟨cv, xs, w, cv', roots', hcv, hxs, hrun, hpt⟩ := h
  exact ⟨cv, xs, os, w, cv', roots', hcv, hxs, hrun, hpt⟩

theorem OpenOut.exists_w {μ r : ℕ} {root : Digest} {fs0 fs1 target cur : E} {rets : List E}
    (h : OpenOut rd μ r root fs0 fs1 target cur rets) :
    ∃ os, OpenOutW rd μ r root fs0 fs1 target cur rets os := by
  obtain ⟨cv, xs, os, w, cv', roots', hcv, hxs, hrun, hpt⟩ := h
  exact ⟨os, cv, xs, w, cv', roots', hcv, hxs, hrun, hpt⟩

/-- `SoundOpenW` gives `SoundOpen`. -/
theorem soundOpen_of_w {wO : String → List E → List E → List Opening} (h : SoundOpenW rd wO) :
    SoundOpen rd := fun μ r h1 h2 h3 h4 root fs0 fs1 target root0 root1 cur rets hroot hrel =>
  (h μ r h1 h2 h3 h4 root fs0 fs1 target root0 root1 cur rets hroot hrel).openOut

theorem openNames_nodup : openNames.Nodup := by decide

/-- The candidates' names are distinct. -/
theorem openName_inj {μ μ' r r' : ℕ} (h1 : 22 ≤ μ) (h2 : μ ≤ 28) (h3 : 1 ≤ r) (h4 : r ≤ 4)
    (g1 : 22 ≤ μ') (g2 : μ' ≤ 28) (g3 : 1 ≤ r') (g4 : r' ≤ 4) (h : openName μ r = openName μ' r') :
    μ = μ' ∧ r = r' := by
  unfold openName at h
  have hl : openNames.length = 28 := rfl
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at h
  have := (List.Nodup.getElem_inj_iff openNames_nodup).mp h
  omega

/-- What the openings `os` must satisfy for `open_stacked` named `name` on `args` and `rets`. -/
def OpenOk (rd : Reader) (name : String) (args rets : List E) (os : List Opening) : Prop :=
  ∀ μ r, 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 → name = openName μ r →
    ∀ (root : Digest) fs0 fs1 target root0 root1 cur, (root0, root1) = digestScalars root →
      args = [fs0, fs1, target, root0, root1, cur] → coreProgram.Rel rd name args rets →
        OpenOutW rd μ r root fs0 fs1 target cur rets os

theorem exists_openOk (h : SoundOpen rd) (name : String) (args rets : List E) :
    ∃ os, OpenOk rd name args rets os := by
  by_cases hx : ∃ μ r, 22 ≤ μ ∧ μ ≤ 28 ∧ 1 ≤ r ∧ r ≤ 4 ∧ name = openName μ r ∧
      ∃ (root : Digest) (fs0 fs1 target root0 root1 cur : E), (root0, root1) = digestScalars root ∧
        args = [fs0, fs1, target, root0, root1, cur] ∧ coreProgram.Rel rd name args rets
  · obtain ⟨μ, r, h1, h2, h3, h4, hn, root, fs0, fs1, target, root0, root1, cur, hroot, ha, hrel⟩ := hx
    subst hn ha
    obtain ⟨os, hos⟩ := (h μ r h1 h2 h3 h4 root fs0 fs1 target root0 root1 cur rets hroot hrel).exists_w
    refine ⟨os, fun μ' r' g1 g2 g3 g4 hn' root' fs0' fs1' target' root0' root1' cur' hroot' ha' _ => ?_⟩
    obtain ⟨rfl, rfl⟩ := openName_inj h1 h2 h3 h4 g1 g2 g3 g4 hn'
    simp only [List.cons.injEq, and_true] at ha'
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := ha'
    rw [hroot] at hroot'
    rw [← digestScalars_injective hroot']
    exact hos
  · exact ⟨[], fun μ r h1 h2 h3 h4 hn root fs0 fs1 target root0 root1 cur hroot ha hrel =>
      absurd ⟨μ, r, h1, h2, h3, h4, hn, root, fs0, fs1, target, root0, root1, cur, hroot, ha, hrel⟩ hx⟩

/-- `SoundOpen` gives a witness function: `open_stacked`'s openings exist for every relation. -/
theorem exists_soundOpenW (h : SoundOpen rd) :
    ∃ wO : String → List E → List E → List Opening, SoundOpenW rd wO := by
  choose wO hwO using exists_openOk h
  exact ⟨wO, fun μ r h1 h2 h3 h4 root fs0 fs1 target root0 root1 cur rets hroot hrel =>
    hwO _ _ _ μ r h1 h2 h3 h4 rfl root fs0 fs1 target root0 root1 cur hroot rfl hrel⟩

end
end LeanVM.Guest.B1.VerifySub
