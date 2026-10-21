/-
  LeanVM.Guest.B1.Comp.Sig.Hashing

  The signature verifiers' compressions over a completeness model: one final block and two blocks
  under the IV, from the model's answer for their bytes (the backward halves of
  `compress_final_iff` and `compress_two_iff`).
-/

module

public import LeanVM.Guest.B1.Comp.Basic
public import LeanVM.Guest.B1.Sig.Model.Hashing

/-!
# Compressions from answered hashes

`Model/Hashing.lean` reads a checked row under a hash model as an answered hash
(`compress_final_model`, `compress_two_model`). Over a completeness model the converse holds: the
model's answer for a string of at most two blocks gives the rows of its chain under `CM.sem`.

* `compress_final_comp`, `compress4_comp`, `compress3_comp`: one final block under the IV
  (`compress_final_iff.mpr`, `compress4_iff.mpr`, `compress3_iff.mpr`);
* `hmidC CM b0`: the chaining value after one non-final block, the model's cells of that whole
  block (`hmid` at the deployed model, `hmidC_deployed`);
* `compress_two_comp`: a non-final block under the IV, then a final one (`compress_two_iff.mpr`).

At `CompModel.deployed` they are the deployed backward directions (`compress_final_of_comp`,
`compress_two_of_comp`, …).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.E2E.Complete

@[expose] public section

variable (CM : CompModel)

/-- **One final compression under the IV over a completeness model** (`compress_final_iff.mpr`):
canonical cells whose data bytes `r` the model answers check into the answer's cells. -/
theorem compress_final_comp {m : Fin 4 → E} {o0 o1 : E} {r : List UInt8}
    (hr : blockBytes m = r ++ List.replicate (64 - r.length) 0) (hlen : r.length ≤ 64)
    (hm : ∀ i, IsCanonical128 (m i)) (h : hbWith CM.H r = some (o0, o1)) :
    CM.sem.check m iv0 iv1 o0 o1 (mdw r.length true) := by
  obtain ⟨d, hd, ho⟩ := hbWith_some.mp h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj ho
  have hchk := CM.chain_checks (n := 0) (blocks := fun _ => m)
    (md := fun _ => metadataCell r.length true) hd (by omega)
    (by simp only [zero_add, List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      Nat.mul_one]; exact hr)
    (fun _ _ => hm) (fun j hj => absurd hj (Nat.not_lt_zero _)) rfl 0 le_rfl
  rw [CM.chainSt_zero, CM.chainSt_succ_of d (n := 0) (by omega)] at hchk
  rw [iv0_eq, iv1_eq, mdw_eq]
  exact hchk

/-- One final block of four cells under the IV over a completeness model (`compress4_iff.mpr`). -/
theorem compress4_comp {a b c d o0 o1 : E}
    (hc : IsCanonical128 a ∧ IsCanonical128 b ∧ IsCanonical128 c ∧ IsCanonical128 d)
    (h : hcellWith CM.H [a, b, c, d] = some (o0, o1)) :
    CM.sem.check ![a, b, c, d] iv0 iv1 o0 o1 (mdw 64 true) := by
  have hl : ([a, b, c, d].flatMap cellBytes).length = 64 := by
    rw [length_flatMap_cellBytes']; rfl
  have := compress_final_comp CM (blockBytes_four' a b c d) (by rw [hl]) (fin4_canonical.mpr hc) h
  rwa [hl] at this

/-- One final block of three cells and a zero under the IV over a completeness model
(`compress3_iff.mpr`). -/
theorem compress3_comp {a b c o0 o1 : E}
    (hc : IsCanonical128 a ∧ IsCanonical128 b ∧ IsCanonical128 c)
    (h : hcellWith CM.H [a, b, c] = some (o0, o1)) :
    CM.sem.check ![a, b, c, 0] iv0 iv1 o0 o1 (mdw 48 true) := by
  have hl : ([a, b, c].flatMap cellBytes).length = 48 := by
    rw [length_flatMap_cellBytes']; rfl
  have := compress_final_comp CM (blockBytes_three a b c) (by rw [hl]; omega)
    (fin4_canonical.mpr ⟨hc.1, hc.2.1, hc.2.2, isCanonical128_zero⟩) h
  rwa [hl] at this

/-- **The chaining value after one non-final block under the IV, over a completeness model**: the
model's cells of that whole block (`hmid`). -/
def hmidC (b0 : Fin 4 → E) : E × E := CM.st [blockBytes b0]

/-- **Two compressions over a completeness model** (`compress_two_iff.mpr`): a non-final block
under the IV into `hmidC`, then a final one with data bytes `r`, from the model's answer for all
the bytes. -/
theorem compress_two_comp {b0 b1 : Fin 4 → E} {o0 o1 : E} {r : List UInt8}
    (hr : blockBytes b1 = r ++ List.replicate (64 - r.length) 0) (hlen : r.length ≤ 64)
    (hpos : 1 ≤ r.length) (hc0 : ∀ i, IsCanonical128 (b0 i)) (hc1 : ∀ i, IsCanonical128 (b1 i))
    (h : hbWith CM.H (blockBytes b0 ++ r) = some (o0, o1)) :
    CM.sem.check b0 iv0 iv1 (hmidC CM b0).1 (hmidC CM b0).2 (mdw 64 false) ∧
      CM.sem.check b1 (hmidC CM b0).1 (hmidC CM b0).2 o0 o1 (mdw (64 + r.length) true) := by
  obtain ⟨d, hd, ho⟩ := hbWith_some.mp h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj ho
  have hxl : (blockBytes b0 ++ r).length = 64 + r.length := by
    rw [List.length_append, length_blockBytes]
  have hn : ((blockBytes b0 ++ r).length - 1) / 64 = 1 := by rw [hxl]; omega
  have hchk := CM.chain_checks (n := 1) (blocks := fun j => if j = 0 then b0 else b1)
    (md := fun j => if j = 0 then metadataCell 64 false else metadataCell (64 + r.length) true) hd hn
    (by
      rw [hxl, show List.range (1 + 1) = [0, 1] from rfl]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, ↓reduceIte, one_ne_zero, hr,
        List.append_assoc]
      rw [show 64 * (1 + 1) - (64 + r.length) = 64 - r.length by omega])
    (fun j _ => by split <;> assumption)
    (fun j hj => by rw [show j = 0 by omega]; rfl)
    (by simp only [one_ne_zero, ↓reduceIte, hxl])
  have hmid1 : CM.chainSt (blockBytes b0 ++ r) d 1 = hmidC CM b0 := by
    rw [CM.chainSt_of_le d (by show 1 ≤ ((blockBytes b0 ++ r).length - 1) / 64; rw [hn])]
    unfold hmidC prefixAt blockAt
    rw [show List.range 1 = [0] from rfl, List.map_singleton, Nat.mul_zero, List.drop_zero,
      List.take_left' (length_blockBytes b0)]
  have h0 := hchk 0 (Nat.zero_le _)
  have h1 := hchk 1 le_rfl
  simp only [↓reduceIte, one_ne_zero] at h0 h1
  rw [CM.chainSt_zero, hmid1] at h0
  rw [hmid1, CM.chainSt_succ_of d hn] at h1
  rw [iv0_eq, iv1_eq, mdw_eq, mdw_eq]
  exact ⟨h0, h1⟩

/-! ## At the deployed model -/

theorem hmidC_deployed (b0 : Fin 4 → E) : hmidC CompModel.deployed b0 = hmid b0 := rfl

theorem hbWith_comp_deployed (bs : List UInt8) :
    hbWith CompModel.deployed.H bs = some (hb bs) := rfl

/-- The deployed `compress_final_iff.mpr`, from the model's at `CompModel.deployed`. -/
theorem compress_final_of_comp {m : Fin 4 → E} {o0 o1 : E} {r : List UInt8}
    (hr : blockBytes m = r ++ List.replicate (64 - r.length) 0) (hlen : r.length ≤ 64)
    (hm : ∀ i, IsCanonical128 (m i)) (ho : (o0, o1) = hb r) :
    CompressCells m iv0 iv1 o0 o1 (mdw r.length true) :=
  compress_final_comp CompModel.deployed hr hlen hm (by rw [ho]; rfl)

/-- The deployed `compress_two_iff.mpr`, from the model's at `CompModel.deployed`. -/
theorem compress_two_of_comp {b0 b1 : Fin 4 → E} {x0 x1 o0 o1 : E} {r : List UInt8}
    (hr : blockBytes b1 = r ++ List.replicate (64 - r.length) 0) (hlen : r.length ≤ 64)
    (hpos : 1 ≤ r.length) (hc0 : ∀ i, IsCanonical128 (b0 i)) (hc1 : ∀ i, IsCanonical128 (b1 i))
    (hx : (x0, x1) = hmid b0) (ho : (o0, o1) = hb (blockBytes b0 ++ r)) :
    CompressCells b0 iv0 iv1 x0 x1 (mdw 64 false) ∧
      CompressCells b1 x0 x1 o0 o1 (mdw (64 + r.length) true) := by
  have := compress_two_comp CompModel.deployed hr hlen hpos hc0 hc1 (by rw [ho]; rfl)
  rw [hmidC_deployed, ← hx] at this
  exact this

end
end LeanVM.Guest.B1.Sig
