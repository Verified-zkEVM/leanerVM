/-
  LeanVM.Guest.Memory.SizeTotalB

  Words bounded by weights (`SizeTotal.lean`) under any semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.Memory.SizeTotal
public import LeanVM.Guest.Memory.SizeB

/-!
# Words from weights under any `BLAKE2S` semantics

`SizeTotal.lean`'s lemmas with `S : BlakeSem` a parameter: `totalB_le_weight`,
`totalLeB_of_weightLe`, `totalB_le_self`, and `TotalLeOnB` (`TotalLeOn` over the trees valid
under `S`; `totalLeOnB_deployed` at `blakeDeployed`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable {S : BlakeSem}

variable (S) in
/-- `TotalLeB` on the arguments satisfying `Pre`. -/
def TotalLeOnB (P : Core.Program) (fs : String → ℕ) (f : String) (Pre : List E → Prop)
    (B : List E → ℕ) : Prop :=
  ∀ (rd : Reader) (t : Tree) (args rets : List E), t.name = f → Pre args → t.ValidB S P rd args rets →
    t.BufsOk P → t.total fs ≤ B args

section Total

variable {P : Core.Program} {fs ω : String → ℕ} {Sz : String → Prop} {rd : Reader}

mutual
/-- **A weight bounds the words.** -/
theorem totalB_le_weight (hl : LocLe P fs ω Sz) (hc : CallsIn P Sz) :
    ∀ (t : Tree) {args rets : List E}, Sz t.name → t.ValidB S P rd args rets → t.BufsOk P →
      t.total fs ≤ t.weight ω
  | .node f σ bufs kids, args, rets, hs, hv, hb => by
      obtain ⟨fn, hf, -, es, vs, hw, -, -, hk⟩ := hv
      simp only [Tree.BufsOk] at hb
      obtain ⟨hbufs, hbk⟩ := hb
      have he : (Tree.node f σ bufs kids).events P = es := by
        simp only [Tree.events, Tree.name, Tree.val, hf, hw]
      have hloc := hl f hs fn hf σ es vs hw
      rw [sum_words] at hloc
      have hkk := totalKidsB_le_weight hl hc kids hk hbk (hc f hs fn hf σ es vs hw)
      rw [Tree.total, Tree.weight, hbufs, he]
      omega
  | .phantom .., _, _, _, hv, _ => hv.elim

theorem totalKidsB_le_weight (hl : LocLe P fs ω Sz) (hc : CallsIn P Sz) :
    ∀ (ks : List Tree) {σ : Val} {cs : List Call}, Tree.KidsValidB S P rd σ cs ks →
      Tree.BufsOkKids P ks → (∀ c ∈ cs, Sz c.f) →
      Tree.totalKids fs ks ≤ Tree.weightKids ω ks + skipWords fs cs
  | [], _, [], _, _, _ => by simp only [Tree.totalKids, Tree.weightKids, skipWords]; omega
  | [], _, _ :: _, hv, _, _ => hv.elim
  | _ :: _, _, [], hv, _, _ => hv.elim
  | k :: ks, σ, c :: cs, hv, hb, hs => by
      obtain ⟨hn, hk, hv'⟩ := hv
      simp only [Tree.BufsOkKids] at hb
      have ih := totalKidsB_le_weight hl hc ks hv' hb.2 fun c' hc' => hs c' (List.mem_cons_of_mem _ hc')
      rw [Tree.totalKids, Tree.weightKids, skipWords]
      by_cases ht : c.taken = true
      · simp only [ht, ↓reduceIte] at hk ⊢
        have := totalB_le_weight hl hc k (hn ▸ hs c List.mem_cons_self) hk hb.1
        omega
      · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hk ⊢
        obtain ⟨⟨f', σ', rfl⟩, -⟩ := hk
        simp only [Tree.name] at hn
        rw [Tree.total, Tree.weight, hn]
        omega
end

/-- **TotalLe from WeightLe.** -/
theorem totalLeB_of_weightLe (hl : LocLe P fs ω Sz) (hc : CallsIn P Sz) {f : String} (hf : Sz f)
    {B : List E → ℕ} (hw : WeightLeB S P ω f B) : TotalLeB S P fs f B :=
  fun rd t args rets hn hv hb => (totalB_le_weight hl hc t (hn ▸ hf) hv hb).trans (hw rd t args rets hn hv hb)

mutual
/-- **A function calling only itself weighs `ω f` per instance.** -/
theorem weightB_self {f : String} (hc : CallsIn P (· = f)) :
    ∀ (t : Tree) {args rets : List E}, t.name = f → t.ValidB S P rd args rets →
      t.weight ω = ω f * t.weight (fun _ => 1)
  | .node g σ bufs kids, args, rets, hn, hv => by
      simp only [Tree.name] at hn
      subst hn
      obtain ⟨fn, hf, -, es, vs, hw, -, -, hk⟩ := hv
      rw [Tree.weight, Tree.weight, weightKidsB_self hc kids hk (hc g rfl fn hf σ es vs hw)]
      ring
  | .phantom .., _, _, _, hv => hv.elim

theorem weightKidsB_self {f : String} (hc : CallsIn P (· = f)) :
    ∀ (ks : List Tree) {σ : Val} {cs : List Call}, Tree.KidsValidB S P rd σ cs ks → (∀ c ∈ cs, c.f = f) →
      Tree.weightKids ω ks = ω f * Tree.weightKids (fun _ => 1) ks
  | [], _, [], _, _ => by simp [Tree.weightKids]
  | [], _, _ :: _, hv, _ => hv.elim
  | _ :: _, _, [], hv, _ => hv.elim
  | k :: ks, σ, c :: cs, hv, hs => by
      obtain ⟨hn, hk, hv'⟩ := hv
      have ih := weightKidsB_self hc ks hv' fun c' hc' => hs c' (List.mem_cons_of_mem _ hc')
      rw [Tree.weightKids, Tree.weightKids, ih, Nat.mul_add]
      congr 1
      by_cases ht : c.taken = true
      · simp only [ht, ↓reduceIte] at hk
        exact weightB_self hc k (hn.trans (hs c List.mem_cons_self)) hk
      · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hk
        obtain ⟨⟨f', σ', rfl⟩, -⟩ := hk
        simp [Tree.weight]
end

/-- **The words of a function calling only itself**, by its instances: `n` instances at most
weigh `n * ω f`, at most `n * ω' f` words. -/
theorem totalB_le_self {f : String} {ω' : String → ℕ} (hl : LocLe P fs ω' (· = f))
    (hc : CallsIn P (· = f)) {t : Tree} {args rets : List E} (hn : t.name = f)
    (hv : t.ValidB S P rd args rets) (hb : t.BufsOk P) {n : ℕ} (hω : 0 < ω f)
    (hw : t.weight ω ≤ n * ω f) : t.total fs ≤ n * ω' f := by
  have h1 := totalB_le_weight hl hc t hn hv hb
  rw [weightB_self (ω := ω') hc t hn hv] at h1
  rw [weightB_self (ω := ω) hc t hn hv, Nat.mul_comm] at hw
  have := Nat.le_of_mul_le_mul_right hw hω
  calc t.total fs ≤ ω' f * t.weight (fun _ => 1) := h1
    _ ≤ ω' f * n := Nat.mul_le_mul_left _ this
    _ = n * ω' f := Nat.mul_comm _ _

end Total

/-! ## At the deployed semantics -/

section Deployed

variable {P : Core.Program}

/-- At the deployed semantics, `TotalLeOnB` is `SizeTotal.lean`'s `TotalLeOn`. -/
theorem totalLeOnB_deployed (fs : String → ℕ) (f : String) (Pre : List E → Prop)
    (B : List E → ℕ) : TotalLeOnB blakeDeployed P fs f Pre B = TotalLeOn P fs f Pre B := by
  simp only [TotalLeOnB, TotalLeOn, validB_deployed]

end Deployed

end
end LeanVM.Guest.Memory
