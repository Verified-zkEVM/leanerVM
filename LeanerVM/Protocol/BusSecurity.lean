/-
  LeanerVM.Protocol.BusSecurity

  Round-by-round knowledge soundness of the bus phase at the slot's error: the fingerprint
  challenges at `4·2^{μ_bus}/|E|`, the grand-product argument at its own errors, the roots and
  the boundary values at none.
-/

module

public import LeanerVM.Protocol.Bus
public import LeanerVM.Protocol.ToArkLib.GrandProductSecurity

/-!
# Knowledge soundness of the bus phase

`busSecurity I h` is the security half of `busPhase I h` at the slot's error `busError I`, from
`Seam.commit` to `Seam.bus`. The stack is the oracle and every witness is trivial, so it is
round-by-round soundness: a stack outside `M3Holds` reaches `Seam.bus` only through a bad
challenge. It is composed from the four steps' halves, at the same intermediate relations as
`busComplete`, so every challenge keeps the error the slot assigns it:

* **The challenges `(α, β)`** (`challengeSecurity`), at `4·2^{μ_bus}/|E|` (Theorem 5.1). The
  state after them is `afterChallenge`: the push and pull products agree at `(α, β)`, every count
  cell is nonzero, every constraint vanishes, and the public lines and the Flock predicate hold.
  It asks the products to agree, not the multisets, since a collision of the products could be
  charged to no later challenge. A stack outside `M3Holds` that meets the clauses no challenge
  touches is unbalanced, and its two multisets of at most `2^{μ_bus}` tuples collide at no more
  than `4·2^{μ_bus}·|E|⁴` of the `|E|⁵` challenges (`card_sideProduct_collision_le`).
* **The roots** (`rootsSecurity`), at no error: a root that passes the check `R_c ≠ 0` and is
  the product of its leaves makes every count cell nonzero (`prod_countLeaves_ne_zero_iff`), and
  one root for both sides makes the products agree. This is where the check is load-bearing: a
  zero count is otherwise balanced on the bus (the tests' zero-count mutation).
* **The grand-product argument** (`gkrSecurity`), at `gkrError` from the unit `1/|E|`. Its riders
  carry the constraints and the public lines with the Flock predicate, so its state function
  carries the zerocheck: a constraint that does not vanish on the cube has a nonzero extension
  restricted to the coordinates of `ζ` drawn so far, which a coordinate makes zero at one value at
  most, inside the argument's own bound.
* **The boundary values** (`valuesSecurity`), at no error: the claims of `Seam.bus` force the
  values sent to be the boundary columns' extensions, and then the forms sum to the totals
  exactly when the leaf claims hold (`sum_forms_eq_total_iff`); the zerocheck clause gives the
  riders' vanishing.

Every part takes no real number and no `Fintype` instance as an argument, and the compositions
are inlined, so the security computes, its extractor included.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

namespace Bus

variable {I : M3Instance}

/-! ## The challenges -/

/-- A push or pull side's tuples number its leaves. -/
theorem length_tuples {k : Fin 3} {s : Side} (hk : sources I k = sideSources I s)
    (q : Column I.μ) : (I.tuples q s).length = leafCount I k := by
  rw [← (sideTuples_perm q s).length_eq, sideTuples, List.length_flatMap, leafCount, hk]
  exact congrArg List.sum (List.map_congr_left fun src _ ↦ by simp)

/-- `|E| = 2^192`, counted with `Nat.card`. -/
private theorem natCard_E : Nat.card E = 2 ^ 192 := by
  rw [Nat.card_eq_fintype_card, card_E]

/-- From a stack outside `M3Holds`, at most `4·2^{μ_bus}·|E|⁴` challenges `(α, β)` lead into
`afterChallenge`: none if a clause no challenge touches fails, a collision of the two products
otherwise. -/
private theorem card_afterChallenge_le (h : Conditions I) (s : I.Stmt) (o : ∀ i, TheOracle I i)
    (hs : ¬ M3Holds I s (theStack o)) :
    Nat.card {ab : (Fin 4 → E) × E // (((s, ab), o), ()) ∈ afterChallenge I} ≤
      4 * 2 ^ I.μBus * (2 ^ 192) ^ 4 := by
  rw [← natCard_E]
  by_cases hrest : I.CountsNonzero (theStack o) ∧ I.ConstraintsVanish (theStack o) ∧
      I.PublicLinesHold s (theStack o) ∧ I.aux (theStack o)
  · have hb : ¬ I.Balanced (theStack o) := fun hb ↦
      hs ⟨hrest.2.1, hb, hrest.1, hrest.2.2.1, hrest.2.2.2⟩
    have hne : (I.tuples (theStack o) .push : Multiset (Vector K 16)) ≠
        (I.tuples (theStack o) .pull : Multiset (Vector K 16)) :=
      fun he ↦ hb (Multiset.coe_eq_coe.mp he)
    have hP : (I.tuples (theStack o) .push : Multiset (Vector K 16)).card ≤ 2 ^ I.μBus := by
      rw [Multiset.coe_card, length_tuples (k := 0) rfl, ← blocks_total]
      exact push_fits I
    have hQ : (I.tuples (theStack o) .pull : Multiset (Vector K 16)).card ≤ 2 ^ I.μBus := by
      rw [Multiset.coe_card, length_tuples (k := 1) rfl]
      exact h.pull_fits
    refine (Finite.card_le_of_embedding (Subtype.impEmbedding _ _ fun ab hab ↦ ?_)).trans
      (card_sideProduct_collision_le hne hP hQ)
    have hprod := hab.1
    change ∏ x : Fin (2 ^ I.μBus), (pushLeaves I ab.1 ab.2 (theStack o))[x] =
      ∏ x : Fin (2 ^ I.μBus), (pullLeaves I ab.1 ab.2 (theStack o))[x] at hprod
    rwa [prod_pushLeaves, prod_pullLeaves h] at hprod
  · have : IsEmpty {ab : (Fin 4 → E) × E // (((s, ab), o), ()) ∈ afterChallenge I} :=
      ⟨fun ab ↦ hrest ab.2.2⟩
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

/-- The challenges' count over their number is the slot's error, `4·2^{μ_bus}/|E|`. -/
private theorem challenge_error_eq :
    ((4 * 2 ^ I.μBus * (2 ^ 192) ^ 4 : ℕ) : ℝ≥0) / (Nat.card ((Fin 4 → E) × E) : ℝ≥0) =
      overE (4 * 2 ^ I.μBus) := by
  rw [← natCard_E]
  have hE : (Nat.card E : ℝ≥0) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero
  rw [overE, ← Nat.card_eq_fintype_card, Nat.card_prod, Nat.card_fun, Nat.card_fin]
  push_cast
  rw [mul_comm ((Nat.card E : ℝ≥0) ^ 4) (Nat.card E : ℝ≥0),
    mul_div_mul_right _ _ (pow_ne_zero 4 hE)]

/-- The challenges' security half, at `4·2^{μ_bus}/|E|` (Theorem 5.1). -/
def challengeSecurity (h : Conditions I) :
    Component.Security (challengeStep I) (Seam.commit I) (afterChallenge I)
      (drawError _ (overE (4 * 2 ^ I.μBus))) :=
  (Component.sampleChallengeSecurity _ _ _ _ (4 * 2 ^ I.μBus * (2 ^ 192) ^ 4) fun s o _ ↦
    Component.card_badChallenge_le_of_unit _ _ _ _ s o fun hs ↦
      by exact card_afterChallenge_le h s o hs).mono fun _ ↦ by exact le_of_eq challenge_error_eq

/-! ## The roots -/

/-- The roots' security half, at no error: a nonzero count root that is the product of its
leaves makes every count cell nonzero, and one root for push and pull makes their products
agree. -/
def rootsSecurity (h : Conditions I) :
    Component.Security (rootsStep I) (afterChallenge I)
      (Gkr.relIn 3 I.μBus (leaves I) (riders I)) (sayError _) :=
  Component.sendCheckedSecurity _ _ _ _ _ fun x o w r hc hout ↦ by
    cases w
    obtain ⟨hz, hroots⟩ := hout
    obtain ⟨hcons, hl, ha⟩ := (ridersZero_iff h x o).mp hz
    have h0 : r.1 = ∏ i : Fin (2 ^ I.μBus), (leaves I x o 0)[i] := hroots 0
    have h1 : r.1 = ∏ i : Fin (2 ^ I.μBus), (leaves I x o 1)[i] := hroots 1
    have h2 : r.2 = ∏ i : Fin (2 ^ I.μBus), (leaves I x o 2)[i] := hroots 2
    have hnz : r.2 ≠ 0 := of_decide_eq_true hc
    rw [h2] at hnz
    exact ⟨h0.symm.trans h1, (prod_countLeaves_ne_zero_iff h _ _ _).mp hnz, hcons, hl, ha⟩

/-! ## The boundary values -/

/-- The values' security half, at no error: the boundary claims force the values sent, the forms
summing to the totals then force the leaf claims, and the zerocheck clause the riders'
vanishing. -/
def valuesSecurity (h : Conditions I) :
    Component.Security (valuesStep I h) (Gkr.relOut 3 I.μBus (leaves I) (riders I))
      (Seam.bus I) (sayError _) :=
  Component.sendCheckedSecurity _ _ _ _ _ fun ℓ o w vals _ hout ↦ by
    cases w
    obtain ⟨hzero, hforms, hclaims, hl, ha⟩ := hout
    have hvals : ∀ i : Fin I.busClaims, vals[i] = eval₂Mle
        (I.column (theStack o) I.boundaryColumns[i]).values (algebraMap K E)
        (columnPoint h ℓ.2.1 i) := fun i ↦
      (hclaims ⟨I.boundaryColumns[i], columnPoint h ℓ.2.1 i, vals[i]⟩
        (by simp only [busOut, Vector.toList_ofFn, List.mem_ofFn]; exact ⟨i, rfl⟩)).symm
    refine ⟨fun k ↦ (sum_forms_eq_total_iff h k _ _ _ _ _ _ hvals).mp (hforms k),
      (riders_vanish_iff ℓ.1 o ℓ.2.1).mpr ⟨fun j hj C hC ↦ ?_, hl, ha⟩⟩
    have := hzero ⟨j, Or.inl (List.ne_nil_of_mem hC)⟩ C hC
    rwa [show (busOut h ℓ vals).point = point h ℓ.2.1 from rfl, lowPoint_point] at this

end Bus

/-- **Knowledge soundness of the bus phase**, at the slot's error `busError I`, from
`Seam.commit` to `Seam.bus`, with the extractor that keeps the trivial witness: from a stack
outside `M3Holds`, each challenge turns the state from false to true with probability at most the
error the slot charges it. It computes, extractor included. -/
def busSecurity (I : M3Instance) (h : Bus.Conditions I) :
    Phase.Security I (busPhase I h).toDef (Seam.commit I) (Seam.bus I) (busError I) :=
  (((Bus.challengeSecurity h).append (Bus.rootsSecurity h)).append
    ((gkrSecurity 3 I.μBus (Bus.leaves I) (Bus.riders I)).mono fun _ ↦ by rw [overE_one])).append
    (Bus.valuesSecurity h)

end
end LeanerVM.Protocol
