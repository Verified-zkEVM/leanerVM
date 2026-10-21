/-
  LeanVM.Guest.Memory.GuestWordsB

  The words bounds of the guest's functions (`GuestWords.lean`) over the trees valid under
  any semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.Memory.GuestWords
public import LeanVM.Guest.Memory.StaticWordsB

/-!
# Words bounds of the guest under any `BLAKE2S` semantics

`GuestWords.lean`'s bounds with `S : BlakeSem` a parameter, from the same kernel-checked
certificate facts (`coreProgram_wchecked`, `wcertOf_of_idx`): `handOkB_of`, `coreB_total_le_of_stat`,
`coreB_total_le_of_loop`, `coreB_totalLe` (`TotalLeB S coreProgram fs f`).

Made by `mkB.py` from the generated `GuestWords.lean` (W2-1's pattern, `docs/roadmap/t6-completeness.md`
§4.2): remake it, do not edit it, when that file is regenerated.
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics Core Memory Data

@[expose] public section

variable {S : BlakeSem}

/-- `HandOkB` function by function: each hand bound by `boundB_of_total`, its certificate read by
`wcertOf_of_idx`. -/
theorem handOkB_of {fs : String → ℕ}
    (h : ∀ q ∈ whandJ, ∀ (rd : Reader) (t : Tree) (args rets : List E), t.name = q.2 →
      t.ValidB S coreProgram rd args rets → t.BufsOk coreProgram → Bound coreProgram true wcertOf fs t args) :
    HandOkB S coreProgram fs wcertOf wHandX := by
  rintro f ⟨q, hq, rfl⟩
  exact h q hq

/-- **A guest function's words**, by its certificate counting words. -/
theorem coreB_total_le_of_stat {fs : String → ℕ}
    (hF : ∀ j (hj : j < coreProgram.length), fs coreProgram[j].name = wfsJ j)
    (hX : HandOkB S coreProgram fs wcertOf wHandX) {f : String}
    {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)} (hcf : wcertOf f = .stat pre b ks)
    {rd : Reader} {t : Tree} {args rets : List E} (hn : t.name = f)
    (hv : t.ValidB S coreProgram rd args rets) (hb : t.BufsOk coreProgram) (hpre : ArgsPre pre args) :
    t.total fs ≤ b.eval args :=
  totalB_le_of_stat (coreProgram_wchecked hF) hX hcf hn hv hb hpre

/-- **A guest loop's words**, by its certificate counting words. -/
theorem coreB_total_le_of_loop {fs : String → ℕ}
    (hF : ∀ j (hj : j < coreProgram.length), fs coreProgram[j].name = wfsJ j)
    (hX : HandOkB S coreProgram fs wcertOf wHandX) {f : String} {endc : Option ℕ}
    {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)} (hcf : wcertOf f = .loop endc pre b ks)
    {rd : Reader} {t : Tree} {args rets : List E} (hn : t.name = f)
    (hv : t.ValidB S coreProgram rd args rets) (hb : t.BufsOk coreProgram) {a e : ℕ}
    (ha : args.getD 0 0 = ofK (gpow a)) (he : endOf endc args = ofK (gpow e)) (hae : a < e)
    (heo : e < 2 ^ 64 - 1) (hpre : ArgsPre pre args) : t.total fs ≤ (e - a) * b.eval args :=
  totalB_le_of_loop (coreProgram_wchecked hF) hX hcf hn hv hb ha he hae heo hpre

/-- **A guest function's words, constant.** -/
theorem coreB_totalLe {fs : String → ℕ}
    (hF : ∀ j (hj : j < coreProgram.length), fs coreProgram[j].name = wfsJ j)
    (hX : HandOkB S coreProgram fs wcertOf wHandX) {f : String} {B : ℕ}
    {ks : List (V × ℕ)} (hcf : wcertOf f = .stat [] ⟨B, []⟩ ks) : TotalLeB S coreProgram fs f fun _ => B :=
  totalLeB_of_stat (coreProgram_wchecked hF) hX hcf

end
end LeanVM.Guest
