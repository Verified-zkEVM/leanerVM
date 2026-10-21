/-
  LeanVM.Guest.Memory.SizeTransferB

  Moving weight and word bounds between programs (`SizeTransfer.lean`) under any semantics
  of `BLAKE2S`.
-/

module

public import LeanVM.Guest.Memory.SizeTransfer
public import LeanVM.Guest.Memory.SizeTotalB

/-!
# Transferring bounds under any `BLAKE2S` semantics

`SizeTransfer.lean`'s lemmas with `S : BlakeSem` a parameter: `totalLeB_transfer`,
`totalLeOnB_transfer`, `weightLeB_transfer`.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable {S : BlakeSem}

variable {P : Core.Program} {Sz : String → Prop} {rd : Reader}

section Congr

variable {fs fs' : String → ℕ}

mutual
/-- **The words of a tree of `Sz` at two frame sizes agreeing on `Sz`.** -/
theorem totalB_congr (hc : CallsIn P Sz) (hS : ∀ g, Sz g → ∀ fn, P.find? g = some fn → fs g = fs' g) :
    ∀ (t : Tree) {args rets : List E}, Sz t.name → t.ValidB S P rd args rets → t.total fs = t.total fs'
  | .node f σ bufs kids, args, rets, hs, hv => by
      obtain ⟨fn, hf, -, es, vs, hw, -, -, hk⟩ := hv
      rw [Tree.total, Tree.total, hS f hs fn hf, totalKidsB_congr hc hS kids hk (hc f hs fn hf σ es vs hw)]
  | .phantom .., _, _, _, hv => hv.elim

theorem totalKidsB_congr (hc : CallsIn P Sz) (hS : ∀ g, Sz g → ∀ fn, P.find? g = some fn → fs g = fs' g) :
    ∀ (ks : List Tree) {σ : Val} {cs : List Call}, Tree.KidsValidB S P rd σ cs ks → (∀ c ∈ cs, Sz c.f) →
      Tree.totalKids fs ks = Tree.totalKids fs' ks
  | [], _, [], _, _ => rfl
  | [], _, _ :: _, hv, _ => hv.elim
  | _ :: _, _, [], hv, _ => hv.elim
  | k :: ks, σ, c :: cs, hv, hs => by
      obtain ⟨hn, hk, hv'⟩ := hv
      rw [Tree.totalKids, Tree.totalKids,
        totalKidsB_congr hc hS ks hv' fun c' h => hs c' (List.mem_cons_of_mem _ h)]
      congr 1
      have hkn : Sz k.name := hn ▸ hs c List.mem_cons_self
      by_cases ht : c.taken = true
      · simp only [ht, ↓reduceIte] at hk
        exact totalB_congr hc hS k hkn hk
      · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hk
        obtain ⟨⟨f', σ', rfl⟩, fn', hfn', -⟩ := hk
        simp only [Tree.name] at hkn hfn'
        rw [Tree.total, Tree.total, hS f' hkn fn' hfn']
end

end Congr

section WCongr

variable {ω ω' : String → ℕ}

mutual
/-- **The weight of a tree of `Sz` at two weights agreeing on `Sz`.** -/
theorem weightB_congr (hc : CallsIn P Sz) (hS : ∀ g, Sz g → ∀ fn, P.find? g = some fn → ω g = ω' g) :
    ∀ (t : Tree) {args rets : List E}, Sz t.name → t.ValidB S P rd args rets → t.weight ω = t.weight ω'
  | .node f σ bufs kids, args, rets, hs, hv => by
      obtain ⟨fn, hf, -, es, vs, hw, -, -, hk⟩ := hv
      rw [Tree.weight, Tree.weight, hS f hs fn hf, weightKidsB_congr hc hS kids hk (hc f hs fn hf σ es vs hw)]
  | .phantom .., _, _, _, hv => hv.elim

theorem weightKidsB_congr (hc : CallsIn P Sz) (hS : ∀ g, Sz g → ∀ fn, P.find? g = some fn → ω g = ω' g) :
    ∀ (ks : List Tree) {σ : Val} {cs : List Call}, Tree.KidsValidB S P rd σ cs ks → (∀ c ∈ cs, Sz c.f) →
      Tree.weightKids ω ks = Tree.weightKids ω' ks
  | [], _, [], _, _ => rfl
  | [], _, _ :: _, hv, _ => hv.elim
  | _ :: _, _, [], hv, _ => hv.elim
  | k :: ks, σ, c :: cs, hv, hs => by
      obtain ⟨hn, hk, hv'⟩ := hv
      rw [Tree.weightKids, Tree.weightKids,
        weightKidsB_congr hc hS ks hv' fun c' h => hs c' (List.mem_cons_of_mem _ h)]
      congr 1
      have hkn : Sz k.name := hn ▸ hs c List.mem_cons_self
      by_cases ht : c.taken = true
      · simp only [ht, ↓reduceIte] at hk
        exact weightB_congr hc hS k hkn hk
      · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hk
        obtain ⟨⟨f', σ', rfl⟩, -⟩ := hk
        rfl
end

end WCongr

variable {fs fs' ω ω' : String → ℕ} {f : String}

/-- **`TotalLeB` transfers** between frame sizes agreeing on `Sz`. -/
theorem totalLeB_transfer (hc : CallsIn P Sz) (hS : ∀ g, Sz g → ∀ fn, P.find? g = some fn → fs g = fs' g) (hf : Sz f)
    {B : List E → ℕ} (h : TotalLeB S P fs f B) : TotalLeB S P fs' f B :=
  fun rd t args rets hn hv hb => by
    rw [← totalB_congr hc hS t (hn ▸ hf) hv]; exact h rd t args rets hn hv hb

/-- **`TotalLeOnB` transfers** between frame sizes agreeing on `Sz`. -/
theorem totalLeOnB_transfer (hc : CallsIn P Sz) (hS : ∀ g, Sz g → ∀ fn, P.find? g = some fn → fs g = fs' g) (hf : Sz f)
    {Pre : List E → Prop} {B : List E → ℕ} (h : TotalLeOnB S P fs f Pre B) : TotalLeOnB S P fs' f Pre B :=
  fun rd t args rets hn hp hv hb => by
    rw [← totalB_congr hc hS t (hn ▸ hf) hv]; exact h rd t args rets hn hp hv hb

/-- **`WeightLeB` transfers** between weights agreeing on `Sz`. -/
theorem weightLeB_transfer (hc : CallsIn P Sz) (hS : ∀ g, Sz g → ∀ fn, P.find? g = some fn → ω g = ω' g) (hf : Sz f)
    {B : List E → ℕ} (h : WeightLeB S P ω f B) : WeightLeB S P ω' f B :=
  fun rd t args rets hn hv hb => by
    rw [← weightB_congr hc hS t (hn ▸ hf) hv]; exact h rd t args rets hn hv hb

end
end LeanVM.Guest.Memory
