module

public import XmssSecurity.Proof.IdealStatement
public import XmssSecurity.Proof.HashInputLemmas

@[expose] public section

namespace XmssSecurity

private theorem fin_of_ofNat32_eq {n : Nat} {a b : Fin n} (hn : n ≤ 2 ^ 32)
    (h : BitVec.ofNat 32 a.val = BitVec.ofNat 32 b.val) : a = b := by
  apply Fin.ext
  have ha := a.isLt.trans_le hn
  have hb := b.isLt.trans_le hn
  have heq := congrArg BitVec.toNat h
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using heq

theorem keygenDomainFields_injective : Function.Injective keygenDomainFields := by
  intro left right h
  have htag := congrArg TweakFields.tag h
  have hhi := congrArg (fun fields => (TweakFields.hi fields).toNat) h
  have hlo := congrArg (fun fields => (TweakFields.lo fields).toNat) h
  cases left <;> cases right <;>
    simp only [keygenDomainFields, tweakFields, BitVec.toNat_ofNat] at htag hhi hlo
  all_goals first
    | rfl
    | (simp at htag)
    | skip
  all_goals
    rename_i a b c d
    first
    | (have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
       simp only [lifetime, topLifetime, treeHeight, numChains, topFlag] at *
       first
        | (exfalso; omega)
        | (congr 1 <;> apply Fin.ext <;> omega))

theorem keygenHashInput_injective {p₁ p₂ : PublicParameter} {d₁ d₂ : KeygenDomain}
    {s₁ s₂ : MasterSeed} (h : keygenHashInput p₁ d₁ s₁ = keygenHashInput p₂ d₂ s₂) :
    p₁ = p₂ ∧ d₁ = d₂ ∧ s₁ = s₂ := by
  unfold keygenHashInput at h
  obtain ⟨hprefix, hseed⟩ := List.append_inj' h (by simp)
  obtain ⟨hparameter, htweak⟩ := List.append_inj' hprefix (by simp)
  exact ⟨bytesLE_injective 16 hparameter,
    keygenDomainFields_injective (fieldBytes_injective htweak), bytesLE_injective 32 hseed⟩

end XmssSecurity
