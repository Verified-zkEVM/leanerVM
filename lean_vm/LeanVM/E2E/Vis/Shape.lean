/-
  LeanVM.E2E.Vis.Shape

  W-vis: the input classes of the visible accounting. The hidden class (`Hid`) holds every hash
  input of the honest key generations and signers; the format events say that a decoder-relevant
  answer is the first 32 bytes of a hidden input.
-/

module

public import LeanVM.E2E.Statement
public import LeanVM.Protocol.Verifier.Cost

/-!
# Input classes (W-vis)

The plan is `docs/roadmap/w-vis.md`. Both signature schemes hash `P ‖ A ‖ payload`: the key's
16-byte public parameter, then a 16-byte address whose last 8 bytes are zero (`fieldBytes`). The
exceptions are the key generation's derivations: `"leanXMSS" ‖ S0` (40 bytes), `"leanSPHINCS" ‖ S0`
(43 bytes) and the parameter derivation `0^16 ‖ A_param ‖ S` (64 bytes, `A_param` the same in both
schemes).

* `AddrOK a`: `a` is a scheme address.
* `AddrShaped x`: `x` has an address at bytes `16..32`, a static shape.
* `DerivShape x`: `x` is shaped as a derivation.
* `SchemeIn keys x`: `x` starts with an honest key's parameter and an address.
* `Hid keys x`: the hidden class, `SchemeIn keys x ∨ DerivShape x`.
* `InPfx keys d`: the digest `d` is the first 32 bytes of a hidden input, an honest key's
  `P ‖ A` or `0^16 ‖ A_param`.
* `FormatT keys ℓ`: a non-hidden entry answers such a prefix (the statement's format event).
* `FormatI keys k0 ℓ`: an entry from index `k0` on, not shaped as a derivation, answers such a
  prefix (the analysis's format event, `k0` the end of key generation).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom

@[expose] public section

/-- **A scheme address**: 16 bytes, the last 8 zero (`lo ‖ hi ‖ type ‖ 0^8`, both schemes). -/
def AddrOK (a : Bytes) : Prop := a.length = 16 ∧ a.drop 8 = List.replicate 8 0

instance (a : Bytes) : Decidable (AddrOK a) := inferInstanceAs (Decidable (_ ∧ _))

/-- **Address-shaped**: some 16 bytes, then an address. A static shape, independent of the keys. -/
def AddrShaped (x : Bytes) : Prop := 32 ≤ x.length ∧ AddrOK ((x.drop 16).take 16)

instance (x : Bytes) : Decidable (AddrShaped x) := inferInstanceAs (Decidable (_ ∧ _))

/-- `0^16 ‖ A_param`, the first 32 bytes of the parameter derivation of both schemes
(`keygenDomainFields .parameter = tweakFields 5 0 0 0` in both). -/
def paramPrefix : Bytes :=
  List.replicate 16 0 ++ LeanXmss.fieldBytes (LeanXmss.keygenDomainFields .parameter)

/-- **Shaped as a key-generation derivation**: `"leanXMSS" ‖ S0` (40 bytes), `"leanSPHINCS" ‖ S0`
(43 bytes), or `0^16 ‖ A_param ‖ S` (64 bytes). -/
def DerivShape (x : Bytes) : Prop :=
  (x.length = 40 ∧ LeanXmss.seedTag <+: x) ∨ (x.length = 43 ∧ Sphincs.seedTag <+: x) ∨
    (x.length = 64 ∧ paramPrefix <+: x)

instance (x : Bytes) : Decidable (DerivShape x) := by
  unfold DerivShape; infer_instance

variable {nx ns : ℕ} [Sphincs.Params]

/-- **The honest keys' parameters**, 16 bytes each, from the secret keys (what `sign` uses). -/
def keyParams (keys : Keys nx ns) : List Bytes :=
  List.ofFn (fun j ↦ LeanXmss.bytesLE 16 (keys.xmss j).2.parameter) ++
    List.ofFn (fun j ↦ Sphincs.bytesLE 16 (keys.sphincs j).2.parameter)

/-- **An honest key's input after key generation**: its parameter, an address, anything. -/
def SchemeIn (keys : Keys nx ns) (x : Bytes) : Prop :=
  ∃ p ∈ keyParams keys, ∃ a, AddrOK a ∧ p ++ a <+: x

/-- **The hidden class**: every input of the honest key generations and signers. -/
def Hid (keys : Keys nx ns) (x : Bytes) : Prop := SchemeIn keys x ∨ DerivShape x

/-- **A hidden prefix**: the digest's 32 bytes are an honest key's `P ‖ A`, or `0^16 ‖ A_param`. -/
def InPfx (keys : Keys nx ns) (d : Digest) : Prop :=
  (∃ p ∈ keyParams keys, ∃ a, AddrOK a ∧ digestBytes d = p ++ a) ∨ digestBytes d = paramPrefix

/-- **The format event of the statement**: a non-hidden entry answers a hidden prefix. -/
def FormatT (keys : Keys nx ns) (ℓ : Log) : Prop := ∃ e ∈ ℓ, ¬ Hid keys e.1 ∧ InPfx keys e.2

/-- **The format event of the analysis**: an entry from index `k0` on, not shaped as a
derivation, answers a hidden prefix. -/
def FormatI (keys : Keys nx ns) (k0 : ℕ) (ℓ : Log) : Prop :=
  ∃ (i : ℕ) (hi : i < ℓ.length), k0 ≤ i ∧ ¬ DerivShape ℓ[i].1 ∧ InPfx keys ℓ[i].2

/-! ## Static facts -/

omit [Sphincs.Params] in
/-- The IV prefix has no address at bytes `16..32`. -/
theorem not_addrShaped_ivPrefix_append (d : Bytes) : ¬ AddrShaped (ivPrefix ++ d) := by
  rintro ⟨-, -, h⟩
  have e : ((ivPrefix ++ d).drop 16).take 16 = (ivPrefix.drop 16).take 16 := by
    simp [ivPrefix, r1csDigest]
  rw [e] at h
  revert h
  decide

/-- A scheme input is address-shaped. -/
theorem SchemeIn.addrShaped {keys : Keys nx ns} {x : Bytes} (h : SchemeIn keys x) :
    AddrShaped x := by
  obtain ⟨p, hp, a, ha, ⟨r, rfl⟩⟩ := h
  have hp16 : p.length = 16 := by
    unfold keyParams at hp
    rcases List.mem_append.mp hp with h | h <;>
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp h <;> simp [LeanXmss.bytesLE, Sphincs.bytesLE]
  have ha16 := ha.1
  refine ⟨by simp [hp16, ha16]; omega, ?_⟩
  have e : ((p ++ a ++ r).drop 16).take 16 = a := by
    rw [List.append_assoc, List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le
      (by omega), List.nil_append, List.take_append_of_le_length (by omega),
      List.take_of_length_le (by omega)]
  rw [e]; exact ha

/-- The IV's preimage is not hidden: it is neither address-shaped nor a derivation. -/
theorem not_hid_ivPrefix_append (keys : Keys nx ns) (d : Digest) :
    ¬ Hid keys (ivPrefix ++ digestBytes d) := by
  rintro (h | h)
  · exact not_addrShaped_ivPrefix_append _ h.addrShaped
  · have hl : (ivPrefix ++ digestBytes d).length = 78 := by
      simp [ivPrefix, r1csDigest, digestBytes_length]
    rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega

/-- The batching's label is not hidden (31 bytes). -/
theorem not_hid_batchLabel (keys : Keys nx ns) : ¬ Hid keys LeanVM.Node.batchLabel := by
  have hl : LeanVM.Node.batchLabel.length = 31 := by
    rw [LeanVM.Node.batchLabel, String.toUTF8_eq_toByteArray, ← String.utf8Encode_toList]
    decide +kernel
  rintro (h | h)
  · have := h.addrShaped.1; omega
  · rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega

/-- The DA label is not hidden (23 bytes). -/
theorem not_hid_daLabel (keys : Keys nx ns) : ¬ Hid keys LeanDa.label := by
  have hl : LeanDa.label.length = 23 := by
    rw [LeanDa.label, String.toUTF8_eq_toByteArray, ← String.utf8Encode_toList]
    decide +kernel
  rintro (h | h)
  · have := h.addrShaped.1; omega
  · rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega

/-- The statement's format event is the analysis's, when the first `k0` entries are hidden. -/
theorem FormatT.formatI {keys : Keys nx ns} {ℓ : Log} {k0 : ℕ}
    (hkg : ∀ (i : ℕ) (hi : i < ℓ.length), i < k0 → Hid keys ℓ[i].1) (h : FormatT keys ℓ) :
    FormatI keys k0 ℓ := by
  obtain ⟨e, he, hnh, hp⟩ := h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  refine ⟨i, hi, ?_, fun hd ↦ hnh (Or.inr hd), hp⟩
  by_contra hlt
  exact hnh (hkg i hi (by omega))

end
end LeanVM.E2E
