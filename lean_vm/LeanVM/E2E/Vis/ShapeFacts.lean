/-
  LeanVM.E2E.Vis.ShapeFacts

  W-vis: the remaining facts of P2a. The batching's baked start and leanVM chain inputs are not
  hidden prefixes; and a truncated scheme output fixes two of the three limbs of a digest's
  challenge (the obstruction of decision E2E-6).
-/

module

public import LeanVM.E2E.Vis.Shape
public import LeanVM.E2E.Reduction.World
public import LeanVM.Guest.B1.Main.AggSoundM

/-!
# Input classes: further facts (W-vis, P2a)

* `bytes24_of_inPfx`: a hidden prefix has zero bytes `24..32` (the address's zero half), so
  `not_inPfx_of_bytes24` excludes every digest with a nonzero byte there.
* `not_inPfx_aggSeedD`: the batching's baked start is no hidden prefix.
* `not_hid_chainInput`: an input whose first 32 bytes are a digest that is no hidden prefix, and
  whose rest is not 8 or 11 bytes long (the seed derivations' tails), is not hidden.
* `paramPrefix_eq_sphincs`: both schemes share the parameter derivation's prefix.
* `challengeOf_limbs_of_truncate` (**E2E-6**): two digests with the same 128-bit truncation, as
  the schemes keep it (`truncateHash ∘ digestBits`), have challenges with the same limbs `0` and
  `1`. A signature revealing a truncated output thus fixes two thirds of the challenge of that
  output, and T3's prediction event on a visible log is a 64-bit guess.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom

@[expose] public section

/-! ## Hidden prefixes have a zero half-address -/

/-- The zero half of the parameter prefix's address. -/
theorem paramPrefix_bytes24 : (paramPrefix.drop 24).take 8 = List.replicate 8 0 := by
  decide

/-- Both schemes derive the parameter under the same prefix. -/
theorem paramPrefix_eq_sphincs :
    paramPrefix = List.replicate 16 0 ++ Sphincs.fieldBytes (Sphincs.keygenDomainFields .parameter) := by
  decide

variable {nx ns : ℕ} [Sphincs.Params]

/-- The honest keys' parameters are 16 bytes long. -/
theorem length_of_mem_keyParams {keys : Keys nx ns} {p : Bytes} (hp : p ∈ keyParams keys) :
    p.length = 16 := by
  unfold keyParams at hp
  rcases List.mem_append.mp hp with h | h <;>
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp h <;> simp [LeanXmss.bytesLE, Sphincs.bytesLE]

/-- **A hidden prefix has zero bytes `24..32`.** -/
theorem bytes24_of_inPfx {keys : Keys nx ns} {d : Digest} (h : InPfx keys d) :
    ((digestBytes d).drop 24).take 8 = List.replicate 8 0 := by
  rcases h with ⟨p, hp, a, ⟨ha16, ha⟩, hd⟩ | hd
  · have hp16 := length_of_mem_keyParams hp
    have e : (p ++ a).drop 24 = a.drop 8 := by
      rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, hp16]
    rw [hd, e, ha]
    simp
  · rw [hd]; exact paramPrefix_bytes24

/-- A digest with a nonzero byte among `24..32` is no hidden prefix. -/
theorem not_inPfx_of_bytes24 {keys : Keys nx ns} {d : Digest}
    (h : ((digestBytes d).drop 24).take 8 ≠ List.replicate 8 0) : ¬ InPfx keys d :=
  fun hp ↦ h (bytes24_of_inPfx hp)

/-- **The batching's baked start is no hidden prefix.** -/
theorem not_inPfx_aggSeedD (keys : Keys nx ns) : ¬ InPfx keys Guest.B1.Main.aggSeedD := by
  refine not_inPfx_of_bytes24 ?_
  rw [Guest.B1.Main.aggSeedD_eq, Guest.B1.Main.batchLabel_eq]
  decide +kernel

/-- **A chain input is not hidden**: its first 32 bytes, a digest that is no hidden prefix, rule
out the schemes' `P ‖ A` and the parameter derivation, and its length the seed derivations. -/
theorem not_hid_chainInput {keys : Keys nx ns} {c : Digest} (hc : ¬ InPfx keys c) {b : Bytes}
    (hb8 : b.length ≠ 8) (hb11 : b.length ≠ 11) : ¬ Hid keys (digestBytes c ++ b) := by
  have hl : (digestBytes c ++ b).length = 32 + b.length := by
    simp [digestBytes_length]
  rintro (⟨p, hp, a, ha, r, hr⟩ | h)
  · have hp16 := length_of_mem_keyParams hp
    refine hc (Or.inl ⟨p, hp, a, ha, ?_⟩)
    have hpa : (p ++ a).length = 32 := by simp [hp16, ha.1]
    have := congrArg (List.take 32) hr
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
      List.take_append_of_le_length (by rw [digestBytes_length]),
      List.take_of_length_le (by rw [digestBytes_length])] at this
    exact this.symm
  · rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, r, hr⟩
    · omega
    · omega
    · refine hc (Or.inr ?_)
      have := congrArg (List.take 32) hr
      rw [List.take_append_of_le_length (by decide), List.take_of_length_le (by decide),
        List.take_append_of_le_length (by rw [digestBytes_length]),
        List.take_of_length_le (by rw [digestBytes_length])] at this
      exact this.symm

/-! ## E2E-6: a truncated output fixes two limbs of the challenge -/

omit [Sphincs.Params] in
/-- The little-endian value of a concatenation. -/
theorem foldr_bytes_append (l₁ l₂ : List UInt8) :
    (l₁ ++ l₂).foldr (fun b acc ↦ b.toNat + 256 * acc) 0 =
      l₁.foldr (fun b acc ↦ b.toNat + 256 * acc) 0 +
        256 ^ l₁.length * l₂.foldr (fun b acc ↦ b.toNat + 256 * acc) 0 := by
  induction l₁ with
  | nil => simp
  | cons b l ih =>
    simp only [List.cons_append, List.foldr_cons, ih, List.length_cons, pow_succ]
    ring

omit [Sphincs.Params] in
/-- The truncation the schemes keep is the value of a digest's first 16 bytes. -/
theorem truncateHash_digestBits_toNat (d : Digest) :
    (LeanXmss.truncateHash (LeanVM.Node.digestBits d)).toNat =
      ((digestBytes d).take 16).foldr (fun b acc ↦ b.toNat + 256 * acc) 0 := by
  set A := ((digestBytes d).take 16).foldr (fun b acc ↦ b.toNat + 256 * acc) 0 with hA
  set B := ((digestBytes d).drop 16).foldr (fun b acc ↦ b.toNat + 256 * acc) 0 with hB
  have hlt : (digestBytes d).foldr (fun b acc ↦ b.toNat + 256 * acc) 0 < 2 ^ 256 := by
    have h := foldr_bytes_lt (digestBytes d)
    rw [digestBytes_length] at h
    exact h.trans_le (by norm_num)
  have hsplit : (digestBytes d).foldr (fun b acc ↦ b.toNat + 256 * acc) 0 = A + 2 ^ 128 * B := by
    have h := foldr_bytes_append ((digestBytes d).take 16) ((digestBytes d).drop 16)
    rw [List.take_append_drop, List.length_take, digestBytes_length] at h
    rw [h, hA, hB]
    norm_num
  have hAlt : A < 2 ^ 128 := by
    have h := foldr_bytes_lt ((digestBytes d).take 16)
    rw [List.length_take, digestBytes_length] at h
    exact h.trans_le (by norm_num)
  have h1 : (LeanVM.Node.digestBits d).toNat =
      (digestBytes d).foldr (fun b acc ↦ b.toNat + 256 * acc) 0 := by
    unfold LeanVM.Node.digestBits
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hlt
  change (BitVec.extractLsb' 0 128 (LeanVM.Node.digestBits d : BitVec 256)).toNat = A
  rw [BitVec.extractLsb'_toNat, h1, Nat.shiftRight_zero, hsplit, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hAlt]

omit [Sphincs.Params] in
/-- A digest's first 16 bytes are its first four words. -/
theorem take16_digestBytes (d : Digest) :
    (digestBytes d).take 16 = wordBytes d[0] ++ wordBytes d[1] ++ wordBytes d[2] ++ wordBytes d[3] := by
  obtain ⟨⟨l⟩, hl⟩ := d
  match l, hl with
  | [w0, w1, w2, w3, w4, w5, w6, w7], _ =>
    simp [digestBytes, wordBytes]

omit [Sphincs.Params] in
/-- **E2E-6's obstruction.** Equal scheme truncations give challenges with equal limbs `0` and
`1`: a revealed truncated output fixes all but 64 bits of its challenge. -/
theorem challengeOf_limbs_of_truncate {d d' : Digest}
    (h : LeanXmss.truncateHash (LeanVM.Node.digestBits d) =
      LeanXmss.truncateHash (LeanVM.Node.digestBits d')) :
    (challengeOf d).limb 0 = (challengeOf d').limb 0 ∧
      (challengeOf d).limb 1 = (challengeOf d').limb 1 := by
  have hv := congrArg BitVec.toNat h
  rw [truncateHash_digestBits_toNat, truncateHash_digestBits_toNat] at hv
  have ht := foldr_bytes_inj (by simp [digestBytes_length]) hv
  rw [take16_digestBytes, take16_digestBytes] at ht
  simp only [List.append_assoc] at ht
  obtain ⟨h0, ht⟩ := List.append_inj ht (by simp [wordBytes_length])
  obtain ⟨h1, ht⟩ := List.append_inj ht (by simp [wordBytes_length])
  obtain ⟨h2, h3⟩ := List.append_inj ht (by simp [wordBytes_length])
  have e0 := wordBytes_injective h0
  have e1 := wordBytes_injective h1
  have e2 := wordBytes_injective h2
  have e3 := wordBytes_injective h3
  unfold challengeOf
  rw [limb_ofLimbs, limb_ofLimbs, limb_ofLimbs, limb_ofLimbs]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [e0, e1, e2, e3]
  exact ⟨rfl, rfl⟩

end
end LeanVM.E2E
