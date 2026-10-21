/-
  LeanVM.Guest.Memory.GuestCntJB

  The weight bounds of `GuestCntJ.lean`'s checked certificates under any semantics of
  `BLAKE2S`.
-/

module

public import LeanVM.Guest.Memory.GuestCntJ
public import LeanVM.Guest.Memory.StaticSoundB

/-!
# Weight bounds of `GuestCntJ.lean` under any `BLAKE2S` semantics

The certificates and their check (`kwj_checked`) are `GuestCntJ.lean`'s; the weight bounds they give
are over the trees valid under `S : BlakeSem` here (`kwjB_weightLe`, by `weightLeB_of_stat`; at
`blakeDeployed` the deployed `kwj_weightLe` by `weightLeB_deployed`).

Made by `mkB.py` from the generated `GuestCntJ.lean` (W2-1's pattern, `docs/roadmap/t6-completeness.md`
§4.2): remake it, do not edit it, when that file is regenerated.
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics Core Memory Data

@[expose] public section

variable {S : BlakeSem}

/-- A function with a constant certificate counting `jump` instructions. -/
theorem kwjB_weightLe {f : String} {B : ℕ} {ks : List (V × ℕ)}
    (hcf : kwjcertOf f = .stat [] ⟨B, []⟩ ks) : WeightLeB S coreProgram (kcOm .jump) f fun _ => B :=
  weightLeB_of_stat kwj_checked hcf

/-- A function with a certificate counting `jump` instructions, under its preconditions. -/
theorem kwjB_weight_le_of_stat {f : String} {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)}
    (hcf : kwjcertOf f = .stat pre b ks) {rd : Reader} {t : Tree} {args rets : List E}
    (hn : t.name = f) (hv : t.ValidB S coreProgram rd args rets) (hb : t.BufsOk coreProgram)
    (hpre : ArgsPre pre args) : t.weight (kcOm .jump) ≤ b.eval args :=
  weightB_le_of_stat kwj_checked hcf hn hv hb hpre

/-- A loop helper's `jump` instructions, from `g^a` to `g^e`. -/
theorem kwjB_weight_le_of_loop {f : String} {endc : Option ℕ} {pre : List (ℕ × ℕ)} {b : Aff}
    {ks : List (V × ℕ)} (hcf : kwjcertOf f = .loop endc pre b ks) {rd : Reader} {t : Tree}
    {args rets : List E} (hn : t.name = f) (hv : t.ValidB S coreProgram rd args rets)
    (hb : t.BufsOk coreProgram) {a e : ℕ} (ha : args.getD 0 0 = ofK (gpow a))
    (he : endOf endc args = ofK (gpow e)) (hae : a < e) (heo : e < 2 ^ 64 - 1)
    (hpre : ArgsPre pre args) : t.weight (kcOm .jump) ≤ (e - a) * b.eval args :=
  weightB_le_of_loop kwj_checked hcf hn hv hb ha he hae heo hpre

end
end LeanVM.Guest
