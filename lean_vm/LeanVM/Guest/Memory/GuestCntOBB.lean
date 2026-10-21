/-
  LeanVM.Guest.Memory.GuestCntOBB

  The weight bounds of `GuestCntOB.lean`'s checked certificates under any semantics of
  `BLAKE2S`.
-/

module

public import LeanVM.Guest.Memory.GuestCntOB
public import LeanVM.Guest.Memory.StaticSoundB

/-!
# Weight bounds of `GuestCntOB.lean` under any `BLAKE2S` semantics

The certificates and their check (`kwob_checked`) are `GuestCntOB.lean`'s; the weight bounds they give
are over the trees valid under `S : BlakeSem` here (`kwobB_weightLe`, by `weightLeB_of_stat`; at
`blakeDeployed` the deployed `kwob_weightLe` by `weightLeB_deployed`).

Made by `mkB.py` from the generated `GuestCntOB.lean` (W2-1's pattern, `docs/roadmap/t6-completeness.md`
§4.2): remake it, do not edit it, when that file is regenerated.
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics Core Memory Data

@[expose] public section

variable {S : BlakeSem}

/-- A function with a constant certificate counting `blake2s` instructions. -/
theorem kwobB_weightLe {f : String} {B : ℕ} {ks : List (V × ℕ)}
    (hcf : kwobcertOf f = .stat [] ⟨B, []⟩ ks) : WeightLeB S coreProgram (kcOm .blake2s) f fun _ => B :=
  weightLeB_of_stat kwob_checked hcf

/-- A function with a certificate counting `blake2s` instructions, under its preconditions. -/
theorem kwobB_weight_le_of_stat {f : String} {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)}
    (hcf : kwobcertOf f = .stat pre b ks) {rd : Reader} {t : Tree} {args rets : List E}
    (hn : t.name = f) (hv : t.ValidB S coreProgram rd args rets) (hb : t.BufsOk coreProgram)
    (hpre : ArgsPre pre args) : t.weight (kcOm .blake2s) ≤ b.eval args :=
  weightB_le_of_stat kwob_checked hcf hn hv hb hpre

/-- A loop helper's `blake2s` instructions, from `g^a` to `g^e`. -/
theorem kwobB_weight_le_of_loop {f : String} {endc : Option ℕ} {pre : List (ℕ × ℕ)} {b : Aff}
    {ks : List (V × ℕ)} (hcf : kwobcertOf f = .loop endc pre b ks) {rd : Reader} {t : Tree}
    {args rets : List E} (hn : t.name = f) (hv : t.ValidB S coreProgram rd args rets)
    (hb : t.BufsOk coreProgram) {a e : ℕ} (ha : args.getD 0 0 = ofK (gpow a))
    (he : endOf endc args = ofK (gpow e)) (hae : a < e) (heo : e < 2 ^ 64 - 1)
    (hpre : ArgsPre pre args) : t.weight (kcOm .blake2s) ≤ (e - a) * b.eval args :=
  weightB_le_of_loop kwob_checked hcf hn hv hb ha he hae heo hpre

end
end LeanVM.Guest
