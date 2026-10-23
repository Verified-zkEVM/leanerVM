/-
  LeanVM.Guest.B1.Tables.VtC.SBase

  Helpers for `verify_tables`' completeness on its honest valuation: statements' relations by
  kind, range checks of small powers of `g`, reads of words the memory holds.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.Hon
public import LeanVM.Guest.B1.Tables.Vt.Sort
public import LeanVM.Guest.B1.Tables.Vt.Pads
public import LeanVM.Guest.B1.Tables.Vt.Shared
public import LeanVM.Guest.B1.Placement.CertifyComplete

/-!
# Helpers

`vsh_atom`, `vsh_ite`, `vsh_call`, `vsh_dispatch`: `VSH` by kind. `rdAt_of_load`: the word a
load holds is the one `rdAt` reads. `rc_holds`: a range check of `g^a` against `g^K`, `a ≤ K`,
on a memory defined below `2^κ`, `K < 2^κ`, holds from its equations, its `y` being `g^(K-a)`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

theorem vsh_atom {a : Atom} : VSH C rd σ (.atom a) ↔ a.Holds rd σ := Iff.rfl

theorem vsh_ite {c : V} {z n : List Stmt} :
    VSH C rd σ (.ite c z n) ↔ IsInK (σ c) ∧ (σ c = 0 → ∀ s ∈ z, SHolds C rd σ s) ∧
      (σ c ≠ 0 → ∀ s ∈ n, SHolds C rd σ s) := Iff.rfl

theorem vsh_call {f : String} {args rets : List V} :
    VSH C rd σ (.call f args rets) ↔ C f (args.map σ) (rets.map σ) := Iff.rfl

theorem vsh_dispatch {x : V} {fs : List String} {args rets : List V} :
    VSH C rd σ (.dispatch x fs args rets) ↔
      ∃ (j : ℕ) (h : j < fs.length), σ x = ofK (gpow j) ∧ C fs[j] (args.map σ) (rets.map σ) :=
  Iff.rfl

theorem rdAt_of_load {p : E} {off : ℕ} {v : E} (h : LoadHolds rd p off v) : rdAt rd p off = v := by
  rw [rdAt, h.2]; rfl

/-- A read of a word the memory holds. -/
theorem read_of {d p : V} {off : ℕ} {v : E} (he : σ d = rdAt rd (σ p) off)
    (hm : LoadHolds rd (σ p) off v) : σ d = v ∧ (Atom.load d p off).Holds rd σ := by
  have e : σ d = v := by rw [he, rdAt_of_load hm]
  exact ⟨e, by show LoadHolds rd _ _ _; rw [e]; exact hm⟩

theorem gen_pow_div {a K : ℕ} (ha : a ≤ K) : gen ^ K * (gen ^ a)⁻¹ = gen ^ (K - a) := by
  rw [show K = (K - a) + a by omega, pow_add, mul_assoc, mul_inv_cancel₀ (gen_pow_ne_zero a),
    mul_one, Nat.add_sub_cancel]

theorem lowDefB_load {κ : ℕ} (hlow : LowDefB κ rd) {a : ℕ} (ha : a < 2 ^ κ) :
    LoadHolds rd (gen ^ a) 0 (rdAt rd (gen ^ a) 0) := by
  rw [gen_pow_eq_ofK]
  refine ⟨tb_isInK_ofK _, ?_⟩
  rw [tb_addr_ofK, Nat.add_zero]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hlow a ha)
  rw [rdAt, tb_addr_ofK, Nat.add_zero, hv]; rfl

/-- **A range check of `g^a` against `g^K`** holds from its equations. -/
theorem rc_holds {κ a K : ℕ} (hlow : LowDefB κ rd) {x y t1 t2 k : V}
    (h1 : σ t1 = rdAt rd (σ x) 0) (h2 : σ t2 = rdAt rd (σ y) 0) (h3 : σ y = σ k * (σ x)⁻¹)
    (hx : σ x = gen ^ a) (hk : σ k = gen ^ K) (ha : a ≤ K) (hK : K < 2 ^ κ) :
    (Atom.rangeCheck x y t1 t2 k).Holds rd σ ∧ σ y = gen ^ (K - a) := by
  have hy : σ y = gen ^ (K - a) := by rw [h3, hx, hk, gen_pow_div ha]
  refine ⟨⟨?_, ?_, ?_⟩, hy⟩
  · rw [h1, hx]; exact lowDefB_load hlow (by omega)
  · rw [hk, hx, hy, ← pow_add, Nat.add_sub_cancel' ha]
  · rw [h2, hy]; exact lowDefB_load hlow (by omega)

/-- A product `d = x·y` read as `x = d / y` holds when `y ≠ 0`. -/
theorem mulDiv_holds {d x y : V} (h : σ x = σ d * (σ y)⁻¹) (hy : σ y ≠ 0) :
    (Atom.mul d x y).Holds rd σ := by
  show σ d = σ x * σ y
  rw [h, mul_assoc, inv_mul_cancel₀ hy, mul_one]

theorem vtW152_gen : vtW152 = gen ^ 152 := by rw [vtW152_eq, gen_pow_eq_ofK]

theorem vtW33_gen : vtW33 = gen ^ 33 := by rw [vtW33, word_g33, gen_pow_eq_ofK]

theorem vtW28_gen : vtW28 = gen ^ 28 := by rw [vtW28_eq, gen_pow_eq_ofK]

theorem isInK_gpow' (a : ℕ) : IsInK (gen ^ a) := tb_gen_pow_isInK a

end
end LeanVM.Guest.B1.Tables
