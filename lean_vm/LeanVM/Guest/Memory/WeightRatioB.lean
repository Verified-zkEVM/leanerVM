/-
  LeanVM.Guest.Memory.WeightRatioB

  A weight bounded by a ratio of weights (`WeightRatio.lean`) under any semantics of
  `BLAKE2S`.
-/

module

public import LeanVM.Guest.Memory.WeightRatio
public import LeanVM.Guest.Memory.SizeTotalB

/-!
# Weight ratios under any `BLAKE2S` semantics

`WeightRatio.lean`'s `weight_le_ratio` over the trees valid under `S : BlakeSem`
(`weightB_le_ratio`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable {S : BlakeSem}

variable {P : Core.Program} {fs ω : String → ℕ} {Sz : String → Prop} {rd : Reader} {p q : ℕ}

mutual
/-- **A valid tree's weight within the ratio of its words.** -/
theorem weightB_le_ratio (hc : CallsIn P Sz) (hω : ∀ g, Sz g → q * ω g ≤ p * fs g) :
    ∀ (t : Tree) {args rets : List E}, Sz t.name → t.ValidB S P rd args rets →
      q * t.weight ω ≤ p * t.total fs
  | .node f σ bufs kids, args, rets, hs, hv => by
      obtain ⟨fn, hf, -, es, vs, hw, -, -, hk⟩ := hv
      have hkk := weightKidsB_le_ratio hc hω kids hk (hc f hs fn hf σ es vs hw)
      have h1 := hω f hs
      rw [Tree.weight, Tree.total]
      nlinarith [Nat.zero_le (p * bufs.sum)]
  | .phantom .., _, _, _, hv => hv.elim

theorem weightKidsB_le_ratio (hc : CallsIn P Sz) (hω : ∀ g, Sz g → q * ω g ≤ p * fs g) :
    ∀ (ks : List Tree) {σ : Val} {cs : List Call}, Tree.KidsValidB S P rd σ cs ks →
      (∀ c ∈ cs, Sz c.f) → q * Tree.weightKids ω ks ≤ p * Tree.totalKids fs ks
  | [], _, [], _, _ => by simp only [Tree.weightKids, Tree.totalKids]; omega
  | [], _, _ :: _, hv, _ => hv.elim
  | _ :: _, _, [], hv, _ => hv.elim
  | k :: ks, σ, c :: cs, hv, hs => by
      obtain ⟨hn, hk, hv'⟩ := hv
      have ih := weightKidsB_le_ratio hc hω ks hv' fun c' hc' => hs c' (List.mem_cons_of_mem _ hc')
      rw [Tree.weightKids, Tree.totalKids]
      by_cases ht : c.taken = true
      · simp only [ht, ↓reduceIte] at hk
        have := weightB_le_ratio hc hω k (hn ▸ hs c List.mem_cons_self) hk
        nlinarith
      · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hk
        obtain ⟨⟨f', σ', rfl⟩, -⟩ := hk
        rw [Tree.weight]
        nlinarith [Nat.zero_le (p * (Tree.phantom f' σ').total fs)]
end

end
end LeanVM.Guest.Memory
