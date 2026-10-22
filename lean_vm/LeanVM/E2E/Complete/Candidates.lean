/-
  LeanVM.E2E.Complete.Candidates

  The candidates of an honest commitment: the stacks within level 0's Johnson radius of the exact
  encoding of a stack are that stack alone.
-/

module

public import LeanVM.E2E.Statement
public import LeanVM.Protocol.Whir.Complete.Encoding

/-!
# The candidates of an honest word

V_I (`LeanVM/E2E/Statement.lean`, `blindCandidates`) follows every stack whose encoding agrees with
a node's committed word on at least level 0's Johnson threshold of columns. For the honest prover
the word is the exact encoding of its stack `q₀` (`stackWord`); a candidate's lanes then agree with
`q₀`'s on at least `thr ≥ 2^κ` points, and two messages whose encodings (polynomials of degree
`< 2^κ`) agree on `2^κ` points are equal (`enc_eq_of_agreeOn`). So the candidates are `q₀` alone
(`eq_of_mem_candidates_stackWord`), and at the deployed codes of an admissible shape
(`eq_of_mem_blindCandidates`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Whir
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir.Complete LeanVM.Protocol.Whir.Sound
open Polynomial

@[expose] public section

/-- **Encodings agreeing on `2^κ` points encode one message.** -/
theorem enc_eq_of_agreeOn {κ R : ℕ} (h : κ + R ≤ 64) {g g' : (Fin κ → Bool) → E}
    (S : Finset (Fin (2 ^ (κ + R)))) (hS : 2 ^ κ ≤ S.card)
    (hagr : ∀ v ∈ S, enc κ R g v = enc κ R g' v) : g = g' := by
  have hmem : msgPoly κ (g - g') ∈ degreeLT E (2 ^ κ) :=
    range_msgPoly (show κ ≤ 64 by omega) ▸ LinearMap.mem_range_self _ _
  have hz : msgPoly κ (g - g') = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero _
      (f := fun v : S ↦ domain κ R h v.1)
      (fun a b hab ↦ Subtype.ext ((domain κ R h).injective hab)) (fun v ↦ ?_) ?_
    · have e := congrFun (enc_eq_evalOnPoints h (g - g')) v.1
      rw [map_sub, Pi.sub_apply, hagr v.1 v.2, sub_self] at e
      exact e.symm
    · rw [Fintype.card_coe]
      refine lt_of_lt_of_le ?_ hS
      rw [mem_degreeLT] at hmem
      by_cases h0 : msgPoly κ (g - g') = 0
      · rw [h0, natDegree_zero]
        exact Nat.two_pow_pos κ
      · exact (natDegree_lt_iff_degree_lt h0).mpr hmem
  have := msgPoly_injective (show κ ≤ 64 by omega) (hz.trans (map_zero _).symm)
  exact sub_eq_zero.mp this

/-- **The candidates of an exact encoding are its stack.** -/
theorem eq_of_mem_candidates_stackWord {μ R : ℕ} (P₀ : LevelCode) (hκ : P₀.κ = μ - laneBits)
    (hR : P₀.R = R) (hμ : laneBits ≤ μ) {q₀ q : Column μ}
    (hq : q ∈ Candidates μ R P₀.thr (stackWord μ q₀)) : q = q₀ := by
  have hthr := P₀.two_pow_le_thr
  rcases P₀ with ⟨κ, R', η, h64, hκ1, hR1, hη, hagr⟩
  simp only at hκ hR hthr
  subst hκ hR
  obtain ⟨S, hS, hag⟩ := hq
  have h0 := stackWord_agrees μ R' q₀
  refine eq_of_blockOf_eq hμ fun u ↦ enc_eq_of_agreeOn h64 S (le_trans hthr hS) fun v hv ↦ ?_
  rw [← hag v hv u, h0 v (Finset.mem_univ v) u]

/-- **V_I's candidates of an honest word**: at the deployed codes of an admissible shape, a
candidate of the exact encoding of `q₀` is `q₀`. -/
theorem eq_of_mem_candidates_deployed {μ R : ℕ} (h : Whir.Admissible μ R) {level : Whir.Level}
    {rest : List Whir.Level} (hc : Verifier.deriveConfig μ R = some (level :: rest))
    {q₀ q : Column μ} (hq : q ∈ Candidates μ R (Sound.thrOf μ R) (stackWord μ q₀)) : q = q₀ := by
  obtain ⟨-, hμ, hκ, hR, -⟩ := Params.deployed_spec_hyps h hc
  exact eq_of_mem_candidates_stackWord _ hκ hR hμ hq

/-! ## Partial words (decision E2E-10) -/

/-- **The strict candidates of an exact partial word are its stack**: if every present column of
`P` is the encoding of `q₀`, a stack agreeing with `P` on the Johnson threshold of present
columns is `q₀`. -/
theorem eq_of_mem_sCandidates_exact {μ R ht : ℕ} (P₀ : LevelCode) (hκ : P₀.κ = μ - laneBits)
    (hR : P₀.R = R) (hμ : laneBits ≤ μ) {P : PWord} {q₀ q : Column μ}
    (hex : ∀ v : Fin (2 ^ (μ - laneBits + R)), P.Present ht v →
      ∀ u, laneOf P.word u v = enc (μ - laneBits) R (blockOf q₀ u) v)
    (hq : q ∈ SCandidates μ R P₀.thr ht P) : q = q₀ := by
  have hthr := P₀.two_pow_le_thr
  rcases P₀ with ⟨κ, R', η, h64, hκ1, hR1, hη, hagr⟩
  simp only at hκ hR hthr
  subst hκ hR
  obtain ⟨S, hS, hag⟩ := hq
  refine eq_of_blockOf_eq hμ fun u ↦ enc_eq_of_agreeOn h64 S (le_trans hthr hS) fun v hv ↦ ?_
  obtain ⟨hp, hl⟩ := hag v hv
  rw [← hl u, hex v hp u]

/-- **V_I's strict candidates of an exact partial word**, at the deployed codes of an admissible
shape, are its stack. -/
theorem eq_of_mem_sCandidates_deployed {μ R ht : ℕ} (h : Whir.Admissible μ R)
    {level : Whir.Level} {rest : List Whir.Level}
    (hc : Verifier.deriveConfig μ R = some (level :: rest)) {P : PWord} {q₀ q : Column μ}
    (hex : ∀ v : Fin (2 ^ (μ - laneBits + R)), P.Present ht v →
      ∀ u, laneOf P.word u v = enc (μ - laneBits) R (blockOf q₀ u) v)
    (hq : q ∈ SCandidates μ R (Sound.thrOf μ R) ht P) : q = q₀ := by
  obtain ⟨-, hμ, hκ, hR, -⟩ := Params.deployed_spec_hyps h hc
  exact eq_of_mem_sCandidates_exact _ hκ hR hμ hex hq

open Classical in
/-- **An exact partial word with enough present columns has its stack as a strict
candidate.** -/
theorem mem_sCandidates_of_exact {μ R A ht : ℕ} {P : PWord} {q : Column μ}
    (hex : ∀ v : Fin (2 ^ (μ - laneBits + R)), P.Present ht v →
      ∀ u, laneOf P.word u v = enc (μ - laneBits) R (blockOf q u) v)
    (hA : A ≤ (Finset.univ.filter fun v : Fin (2 ^ (μ - laneBits + R)) ↦ P.Present ht v).card) :
    q ∈ SCandidates μ R A ht P :=
  ⟨_, hA, fun v hv ↦ by
    have hp : P.Present ht v := (Finset.mem_filter.mp hv).2
    exact ⟨hp, hex v hp⟩⟩

end
end LeanVM.E2E.Complete
