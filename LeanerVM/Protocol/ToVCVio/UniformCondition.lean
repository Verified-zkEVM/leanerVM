/-
  LeanerVM.Protocol.ToVCVio.UniformCondition

  A uniform sample conditioned on one coordinate: a tuple by its first entry, a pair by either
  entry, and any bijective combination of two samples. Candidate for VCVio.
-/

module

public import LeanerVM.Protocol.ToVCVio.EventExpectation
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Conditioning a uniform sample on a coordinate

A uniform sample of a type that a bijection splits into two coordinates is two independent
uniform samples. `prEvent_uniformSample_finCons` reads a uniform tuple of `n + 1` entries as a
uniform first entry and a uniform tuple of the rest, the mirror of VCVio's
`SampleableType.prEvent_uniformSample_finSnoc`. `prEvent_uniformSample_eq_lintegral_of_bijective`
writes the probability of an event as the expectation, over one coordinate, of its probability
over the other (`∫⁻ r, r ∂𝒟[f <$> mx]`), the form a supermartingale step integrates against a
fresh answer; `prEvent_uniformSample_prod_eq_lintegral` and
`prEvent_uniformSample_prod_finCons_eq_lintegral` are its two uses, conditioning a pair on its
first entry and a pair with a tuple on the tuple's first entry.
-/

namespace LeanerVM.Protocol

open OracleComp
open scoped ENNReal

public section

section Condition

variable {α β γ : Type} [SampleableType α] [SampleableType β] [SampleableType γ]

/-- **A uniform tuple, first entry first.** A uniform tuple of `n + 1` entries is a uniform first
entry followed by a uniform tuple of `n`. -/
theorem prEvent_uniformSample_finCons {n : ℕ} (p : (Fin (n + 1) → α) → Prop) :
    Pr{let v ← $ᵗ (Fin (n + 1) → α)}[p v] =
      Pr{let x ← $ᵗ α; let w ← $ᵗ (Fin n → α)}[p (Fin.cons x w)] := by
  refine (SampleableType.prEvent_uniformSample_pair_of_bijective
    (g := fun (x : α) (w : Fin n → α) ↦ (Fin.cons x w : Fin (n + 1) → α)) ⟨?_, ?_⟩ p).symm
  · rintro ⟨x₁, w₁⟩ ⟨x₂, w₂⟩ h
    obtain ⟨rfl, rfl⟩ := Fin.cons_inj.mp h
    rfl
  · exact fun v ↦ ⟨(v 0, Fin.tail v), Fin.cons_self_tail v⟩

/-- **Conditioning on a coordinate.** If `g` combines a sample of `α` and one of `β` bijectively
into one of `γ`, an event of a uniform sample of `γ` has as probability the expectation, over a
uniform `x`, of its probability at `g x y` over a uniform `y`. -/
theorem prEvent_uniformSample_eq_lintegral_of_bijective {g : α → β → γ}
    (hg : Function.Bijective (Function.uncurry g)) (p : γ → Prop) :
    Pr{let z ← $ᵗ γ}[p z] =
      ∫⁻ r, r ∂𝒟[(fun x ↦ Pr{let y ← $ᵗ β}[p (g x y)]) <$> ($ᵗ α)] := by
  rw [← SampleableType.prEvent_uniformSample_pair_of_bijective hg p]
  have := prEvent_bind_eq_lintegral_id_evalDist_map ($ᵗ α) (fun x ↦ g x <$> ($ᵗ β)) p
  simpa [map_eq_bind_pure_comp] using this

/-- An event of a uniform pair has as probability the expectation, over a uniform first entry, of
its probability over a uniform second entry. -/
theorem prEvent_uniformSample_prod_eq_lintegral (p : α × β → Prop) :
    Pr{let z ← $ᵗ (α × β)}[p z] =
      ∫⁻ r, r ∂𝒟[(fun x ↦ Pr{let y ← $ᵗ β}[p (x, y)]) <$> ($ᵗ α)] :=
  prEvent_uniformSample_eq_lintegral_of_bijective (g := Prod.mk) Function.bijective_id p

/-- An event of a uniform pair whose second entry is a tuple of `n + 1` has as probability the
expectation, over a uniform first entry of the tuple, of its probability over a uniform pair with
a tuple of the other `n`. -/
theorem prEvent_uniformSample_prod_finCons_eq_lintegral {n : ℕ}
    (p : γ × (Fin (n + 1) → α) → Prop) :
    Pr{let z ← $ᵗ (γ × (Fin (n + 1) → α))}[p z] =
      ∫⁻ r, r ∂𝒟[(fun x ↦ Pr{let z ← $ᵗ (γ × (Fin n → α))}[
        p (z.1, (Fin.cons x z.2 : Fin (n + 1) → α))]) <$> ($ᵗ α)] := by
  refine prEvent_uniformSample_eq_lintegral_of_bijective
    (g := fun (x : α) (z : γ × (Fin n → α)) ↦ (z.1, (Fin.cons x z.2 : Fin (n + 1) → α)))
    ⟨?_, ?_⟩ p
  · rintro ⟨x₁, c₁, w₁⟩ ⟨x₂, c₂, w₂⟩ h
    obtain ⟨rfl, h⟩ := Prod.mk.inj h
    obtain ⟨rfl, rfl⟩ := Fin.cons_inj.mp h
    rfl
  · exact fun z ↦ ⟨(z.2 0, z.1, Fin.tail z.2), by simp [Fin.cons_self_tail]⟩

end Condition

end
end LeanerVM.Protocol
