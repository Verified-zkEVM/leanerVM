/-
  LeanVM.Guest.B1.Whir.CVal

  Building a valuation block by block, for the completeness direction.
-/

module

public import LeanVM.Guest.B1.Whir.Flat

/-!
# Valuations, block by block

The template numbers its values in order: a block reads values below its first `k` and writes
`[k, k')`. `Blk C rd σ k k' ss Out`: from the valuation `σ` (its values below `k` fixed), some
values `f` on `[k, k')` make every valuation agreeing with `σ` below `k` and with `f` on
`[k, k')` hold `ss` and `Out`. Blocks compose in sequence (`Blk.seq`), the second built on any
valuation the first leaves (`fill`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1

@[expose] public section

/-- `σ'` agrees with `σ` on the values `.n i`, `i < k`. -/
def AgreeBelow (k : ℕ) (σ σ' : Val) : Prop := ∀ i < k, σ' (.n i) = σ (.n i)

/-- `σ` holds `f i` at `.n i`, `k ≤ i < k'`. -/
def RangeVals (σ : Val) (k k' : ℕ) (f : ℕ → E) : Prop := ∀ i, k ≤ i → i < k' → σ (.n i) = f i

/-- `σ` with `f` on `[k, k')`. -/
def fill (σ : Val) (k k' : ℕ) (f : ℕ → E) : Val := fun v ↦
  if v.path = [] ∧ v.tag = 0 ∧ k ≤ v.idx ∧ v.idx < k' then f v.idx else σ v

theorem fill_lt {σ : Val} {k k' i : ℕ} {f : ℕ → E} (h : i < k) : fill σ k k' f (.n i) = σ (.n i) := by
  unfold fill
  rw [ite_eq_right_iff]
  intro h'
  exact absurd h'.2.2.1 (by simp; omega)

theorem fill_in {σ : Val} {k k' i : ℕ} {f : ℕ → E} (h1 : k ≤ i) (h2 : i < k') :
    fill σ k k' f (.n i) = f i := by
  unfold fill
  rw [ite_eq_left_iff]
  intro h'
  exact absurd ⟨rfl, rfl, h1, h2⟩ h'

theorem agree_fill (σ : Val) (k k' : ℕ) (f : ℕ → E) : AgreeBelow k σ (fill σ k k' f) :=
  fun _ h ↦ fill_lt h

theorem range_fill (σ : Val) (k k' : ℕ) (f : ℕ → E) : RangeVals (fill σ k k' f) k k' f :=
  fun _ h1 h2 ↦ fill_in h1 h2

theorem AgreeBelow.trans {k : ℕ} {σ σ' σ'' : Val} (h : AgreeBelow k σ σ') (h' : AgreeBelow k σ' σ'') :
    AgreeBelow k σ σ'' := fun i hi ↦ (h' i hi).trans (h i hi)

theorem AgreeBelow.mono {k k' : ℕ} {σ σ' : Val} (h : AgreeBelow k' σ σ') (hk : k ≤ k') :
    AgreeBelow k σ σ' := fun i hi ↦ h i (by omega)

/-- **A block**: some values on `[k, k')` make `ss` and `Out` hold. -/
def Blk (C : CallRel) (rd : Reader) (σ : Val) (k k' : ℕ) (ss : List Stmt) (Out : Val → Prop) :
    Prop :=
  ∃ f : ℕ → E, ∀ σ', AgreeBelow k σ σ' → RangeVals σ' k k' f → AllOk C rd σ' ss ∧ Out σ'

variable {C : CallRel} {rd : Reader}

/-- **Two blocks in sequence**, the second from any valuation the first leaves. -/
theorem Blk.seq {σ : Val} {k k1 k2 : ℕ} {A B : List Stmt} {OutA OutB : Val → Prop}
    (h1 : k ≤ k1) (h2 : k1 ≤ k2) (hA : Blk C rd σ k k1 A OutA)
    (hB : ∀ σ1, AgreeBelow k σ σ1 → OutA σ1 → Blk C rd σ1 k1 k2 B OutB) :
    Blk C rd σ k k2 (A ++ B) (fun σ' ↦ OutA σ' ∧ OutB σ') := by
  obtain ⟨fA, hfA⟩ := hA
  set σ1 := fill σ k k1 fA with hσ1
  have ⟨_, hO1⟩ := hfA σ1 (agree_fill _ _ _ _) (range_fill _ _ _ _)
  obtain ⟨fB, hfB⟩ := hB σ1 (agree_fill _ _ _ _) hO1
  refine ⟨fun i ↦ if i < k1 then fA i else fB i, fun σ' ha hr ↦ ?_⟩
  have hrA : RangeVals σ' k k1 fA := fun i hi1 hi2 ↦ by
    rw [hr i hi1 (by omega)]; simp only [hi2, ↓reduceIte]
  have hrB : RangeVals σ' k1 k2 fB := fun i hi1 hi2 ↦ by
    rw [hr i (by omega) hi2]; simp only [show ¬ i < k1 by omega, ↓reduceIte]
  have hab : AgreeBelow k1 σ1 σ' := fun i hi ↦ by
    by_cases hk : i < k
    · rw [ha i hk, hσ1, fill_lt hk]
    · rw [hrA i (by omega) hi, hσ1, fill_in (by omega) hi]
  obtain ⟨okA, oA⟩ := hfA σ' ha hrA
  obtain ⟨okB, oB⟩ := hfB σ' hab hrB
  exact ⟨allOk_append.mpr ⟨okA, okB⟩, oA, oB⟩

theorem Blk.mono {σ : Val} {k k' : ℕ} {ss : List Stmt} {Out Out' : Val → Prop}
    (h : Blk C rd σ k k' ss Out) (hO : ∀ σ', Out σ' → Out' σ') : Blk C rd σ k k' ss Out' := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun σ' ha hr ↦ ⟨(hf σ' ha hr).1, hO _ (hf σ' ha hr).2⟩⟩

theorem Blk.nil {σ : Val} {k : ℕ} {Out : Val → Prop} (hO : ∀ σ', AgreeBelow k σ σ' → Out σ') :
    Blk C rd σ k k [] Out :=
  ⟨fun _ ↦ 0, fun σ' ha _ ↦ ⟨allOk_nil, hO σ' ha⟩⟩

/-- A block whose outcome holds of every later valuation agreeing below `k'`. -/
def Stable (k' : ℕ) (Out : Val → Prop) : Prop := ∀ σ σ', Out σ → AgreeBelow k' σ σ' → Out σ'

end
end LeanVM.Guest.B1.Whir
