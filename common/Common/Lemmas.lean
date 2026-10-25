import Common.Prob
import Common.Sponge
import Statement.RandomPermutation

/-!
# Lemmas for games built on the transfer

Weight bounds (`IsWeightBound`) through maps, smaller weights and stateful simulations
(`isWeightBound_run_simulateQ`), a byte as a residue (`uInt8EquivFin`), and the number of
permutation calls of a Keccak-256 hash (`keccakPad_length`).
-/

open OracleComp OracleSpec

namespace Common

/-! ## Weight bounds through simulations -/

section Weight

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {σ α β : Type}

theorem isWeightBound_pure (a : α) (w : ι → ℕ) (Q : ℕ) :
    IsWeightBound (pure a : OracleComp spec α) w Q := trivial

theorem isWeightBound_map (f : α → β) {oa : OracleComp spec α} {w : ι → ℕ} {Q : ℕ}
    (h : IsWeightBound oa w Q) : IsWeightBound (f <$> oa) w Q := by
  have := h.bind (fun a ↦ isWeightBound_pure (f a) w 0)
  rwa [Nat.add_zero, bind_pure_comp] at this

/-- A smaller weight keeps a bound. -/
theorem IsWeightBound.mono_weight {oa : OracleComp spec α} {w w' : ι → ℕ} {Q : ℕ}
    (h : IsWeightBound oa w' Q) (hw : ∀ t, w t ≤ w' t) : IsWeightBound oa w Q := by
  induction oa using OracleComp.inductionOn generalizing Q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at h ⊢
    exact ⟨(hw t).trans h.1, fun u ↦ (ih u (h.2 u)).mono (by have := hw t; omega)⟩

/-- **Weight bounds through a stateful simulation**: if every step of `impl` from every state
weighs at most the query's weight, a simulated run weighs at most the computation's bound. -/
theorem isWeightBound_run_simulateQ (impl : QueryImpl spec (StateT σ (OracleComp spec')))
    (w : ι → ℕ) (w' : ι' → ℕ) (hstep : ∀ t s, IsWeightBound ((impl t).run s) w' (w t))
    {oa : OracleComp spec α} {Q : ℕ} (h : IsWeightBound oa w Q) (s : σ) :
    IsWeightBound ((simulateQ impl oa).run s) w' Q := by
  induction oa using OracleComp.inductionOn generalizing Q s with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    exact ((hstep t s).bind fun z ↦ ih z.1 (h.2 z.1) z.2).mono (by omega)

/-- **Coins weigh nothing**: a lifted coin computation weighs nothing when coins do. -/
theorem isWeightBound_liftM_probComp {ι : Type} {hs : OracleSpec ι}
    (w : (unifSpec + hs).Domain → ℕ) (hw : ∀ n, w (.inl n) = 0) (p : ProbComp α) :
    IsWeightBound (liftM p : OracleComp (unifSpec + hs) α) w 0 := by
  change IsWeightBound (OracleComp.liftComp p (unifSpec + hs)) w 0
  induction p using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind n k ih =>
    rw [OracleComp.liftComp_bind, OracleComp.liftComp_query]
    simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
    change IsWeightBound (liftM ((unifSpec + hs).query (.inl n)) >>= fun u ↦
      OracleComp.liftComp (k u) (unifSpec + hs)) w 0
    exact (isWeightBound_query_bind_iff _ _ _ _).mpr ⟨(hw n).le, fun u ↦ by
      rw [hw n]; exact ih u⟩

end Weight

/-- Splitting a list whose length is a multiple of 136 gives a block per 136 bytes. -/
theorem toBlocks_length (bs : List UInt8) (h : bs.length % 136 = 0) :
    (toBlocks bs).length = bs.length / 136 := by
  induction bs using toBlocks.induct with
  | case1 => simp [toBlocks]
  | case2 b bs ih =>
    rw [toBlocks, List.length_cons, ih (by simp only [List.length_drop]; omega)]
    simp only [List.length_drop, List.length_cons] at h ⊢
    have : 0 < bs.length + 1 := by omega
    omega

/-- **A Keccak-256 hash of `n` bytes calls the permutation `⌊n / 136⌋ + 1` times.** -/
theorem keccakPad_length (m : List UInt8) : (keccakPadding.pad m).length = m.length / 136 + 1 := by
  change (toBlocks (keccakPadBytes m)).length = _
  rw [toBlocks_length _ (by rw [keccakPadBytes_length]; omega), keccakPadBytes_length]
  omega

end Common
