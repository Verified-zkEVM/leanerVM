import LeanerVM.Protocol.LeanIsa.Sound

/-!
# Tests: the adaptor, soundness

* **The statement, by type**, at the BLAKE2s inhabitant of `FlockSpec`: admissible sizes and
  `M3Holds` of the leanISA instance give `SatisfiedBy` of the witness read off the stack, with no
  other hypothesis. Its BLAKE2s conjunct alone needs only the Flock clause.
* **The bus as one bus.** On any witness of the ensemble, the two sides' tuples are one multiset
  exactly when the three channels balance, pushes against pulls.
* **The caps bound the interactions.** Within `Caps`, each channel carries fewer than `2^64`
  interactions (`interactionsWith_length_lt`): at most thirty-two a row of eight tables of at most
  `2^32` rows, and the verifier's two. Clean's multiset balance once also required that bound;
  within the caps the old and the new balance agree (`balanced_multiset_iff_bounded`), so
  `SatisfiedBy` means what it meant before Clean dropped it.
* **The relation's clauses are equivalences**, the direction this module does not use included:
  the counts, on a stack and a witness that agree.
* **The limbs are read at the deployed slots.** At a size vector of the instance tests, the
  pinned Rust places `QFLOCK` at offset `4980736`, and limb `k` of row `x` is read at the stack's
  cell `4980736 + slot k + 256 x`, with the slots of `hash_flock.rs:93-115`; a transposed strided
  read would fail this.
-/

namespace LeanerVMTests.Protocol.LeanIsaSound

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization LeanerVM.Protocol
open LeanerVM.Protocol.LeanIsa
open Air.Flat (EnsembleWitness)

/-- The adaptor's soundness at the BLAKE2s inhabitant. -/
example (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) (input : PublicInput)
    (hs : s.Admissible prog)
    (h : M3Holds (leanIsaInstance Blake2sFlock.blake2sFlockSpec prog s) input q) :
    SatisfiedBy prog input (witnessOf Blake2sFlock.blake2sFlockSpec prog s q) :=
  satisfiedBy_witnessOf _ prog s q hs h

/-- The BLAKE2s validity needs the Flock clause alone. -/
example (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s))
    (h : (leanIsaInstance Blake2sFlock.blake2sFlockSpec prog s).aux q) :
    Blake2sRowsValid (witnessOf Blake2sFlock.blake2sFlockSpec prog s q) :=
  blake2sRowsValid_witnessOf _ prog s q h

/-- The bus as one bus, on any witness. -/
example (prog : Program) (κ : ℕ) (w : EnsembleWitness (leanIsaEnsemble prog κ)) :
    (sideTuples w .push).Perm (sideTuples w .pull) ↔
      (messagesOn w StateChannel.toRaw .push).Perm (messagesOn w StateChannel.toRaw .pull) ∧
        (messagesOn w MemChannel.toRaw .push).Perm (messagesOn w MemChannel.toRaw .pull) ∧
          (messagesOn w BytecodeChannel.toRaw .push).Perm
            (messagesOn w BytecodeChannel.toRaw .pull) := by
  rw [balanced_iff]
  exact ⟨fun h ↦ ⟨h 0, h 1, h 2⟩, fun h k ↦ by fin_cases k; exacts [h.1, h.2.1, h.2.2]⟩

/-! ## The caps bound the interactions -/

/-- Every channel of the ensemble is one of the three. -/
theorem exists_channelAt {prog : Program} {κ : ℕ} {c : RawChannel K}
    (hc : c ∈ (leanIsaEnsemble prog κ).channels) : ∃ k : Fin 3, c = channelAt k := by
  simp only [leanIsaEnsemble, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]

/-- Every component of the ensemble emits at most thirty-two interactions a row. -/
theorem tables_interactions_le {prog : Program} {κ : ℕ} :
    ∀ c ∈ (leanIsaEnsemble prog κ).tables, c.rowOperations.interactions.length ≤ 32 := by
  have hop : ∀ j : Fin 6, (opcodeComponent j).rowOperations.interactions.length ≤ 32 := by
    decide +kernel
  intro c hc
  simp only [leanIsaEnsemble, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [hop 0, hop 1, hop 2, hop 3, hop 4, hop 5,
    (by decide +kernel : (memComponent 0).rowOperations.interactions.length ≤ 32),
    (by decide +kernel : (bytecodeComponent ⟨0, Nat.zero_le _, fun _ ↦ .jump 0 0 0⟩
      ).rowOperations.interactions.length ≤ 32)]

/-- Within the caps, a witness has fewer than `2^64` interactions on each channel. -/
theorem interactionsWith_length_lt {prog : Program} {κ : ℕ}
    {w : EnsembleWitness (leanIsaEnsemble prog κ)} (hc : Caps w) (k : Fin 3) :
    (w.interactionsWith (channelAt k)).length < 2 ^ 64 := by
  rw [EnsembleWitness.interactionsWith_eq_filter_name (channelAt_mem k)]
  refine lt_of_le_of_lt (List.length_filter_le _ _) ?_
  have ht : ∀ t ∈ w.tables, t.interactions.length ≤ 2 ^ maxLogRows * 32 := by
    intro t ht
    obtain ⟨τ, hτ, hlen⟩ := hc.heights t ht
    rw [Air.Flat.Table.interactions, List.length_flatMap]
    refine (List.sum_le_length_nsmul _ 32 fun n hn ↦ ?_).trans ?_
    · obtain ⟨row, -, rfl⟩ := List.mem_map.mp hn
      simp only [Operations.interactionValues, List.length_map,
        Air.Flat.Component.interactions_eq]
      exact tables_interactions_le _ (EnsembleWitness.component_mem_tables_of_mem ht)
    · rw [List.length_map, hlen, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hτ)
  have h8 : w.tables.length = 8 := w.same_length.symm
  have hv : (leanIsaEnsemble prog κ).verifierOperations.interactions.length = 2 := rfl
  rw [EnsembleWitness.interactions, List.length_append, Operations.interactionValues,
    List.length_map, hv, List.length_flatMap]
  have hs := List.sum_le_length_nsmul (w.tables.map fun t ↦ t.interactions.length)
    (2 ^ maxLogRows * 32) (fun n hn ↦ by
      obtain ⟨t, htm, rfl⟩ := List.mem_map.mp hn
      exact ht t htm)
  rw [List.length_map, h8, smul_eq_mul] at hs
  have : 2 + 8 * (2 ^ maxLogRows * 32) < 2 ^ 64 := by decide
  omega

/-- Within the caps, Clean's multiset balance is its form with the interaction bound it dropped,
`fewer than FiniteField.size K = 2^64 interactions on each channel`, and the three channels'
permutations. -/
theorem balanced_multiset_iff_bounded {prog : Program} {κ : ℕ}
    {w : EnsembleWitness (leanIsaEnsemble prog κ)} (hc : Caps w) :
    w.Balanced .multiset ↔
      (∀ c ∈ (leanIsaEnsemble prog κ).channels,
        (w.interactionsWith c).length < FiniteField.size K) ∧
      ∀ k : Fin 3, (messagesOn w (channelAt k) .push).Perm (messagesOn w (channelAt k) .pull) :=
  (balanced_multiset_iff w).trans ⟨fun h ↦ ⟨fun c hc' ↦ by
    obtain ⟨k, rfl⟩ := exists_channelAt hc'
    exact interactionsWith_length_lt hc k, h⟩, And.right⟩

/-- `SatisfiedBy` bounds the interactions of every channel, through its caps. -/
example (prog : Program) (input : PublicInput) (κ : ℕ)
    (w : EnsembleWitness (leanIsaEnsemble prog κ)) (h : SatisfiedBy prog input w) :
    ∀ c ∈ (leanIsaEnsemble prog κ).channels, (w.interactionsWith c).length < FiniteField.size K :=
  ((balanced_multiset_iff_bounded h.caps).mp h.balanced).1

/-- The counts, both ways, on a stack and a witness that agree. -/
example (F : FlockSpec) (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) (κ : ℕ)
    (w : EnsembleWitness (leanIsaEnsemble prog κ)) (h : Agrees F s q w) :
    CountsNonzero w ↔ (leanIsaInstance F prog s).CountsNonzero q :=
  countsNonzero_iff h

/-! ## The limbs' cells -/

/-- Four `XOR` instructions. -/
def prog4 : Program := ⟨2, by decide, fun _ ↦ .xor 0 0 0⟩

/-- The second size vector of the instance tests, the `BLAKE2S` table at the floor. -/
def s₂ : Sizes := ⟨18, by decide, ![2, 18, 5, 0, 7, 3]⟩

#guard (List.finRange 18).all fun k ↦ (List.finRange (2 ^ s₂.τ 5)).all fun x ↦
  (boolIndex ((layout prog4 s₂ Blake2sFlock.blake2sFlockSpec.slot).extend (limbCol k)
      (boolVec x))).val ==
    4980736 + [10, 11, 12, 13, 14, 15, 16, 17, 4, 5, 6, 7, 0, 1, 2, 3, 18, 19][k]! + 256 * x

end LeanerVMTests.Protocol.LeanIsaSound
