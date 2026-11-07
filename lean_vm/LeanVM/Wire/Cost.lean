/-
  LeanVM.Wire.Cost

  The decoding's cost: `Proof.fromBytes` over the random permutation makes at most
  `wireDecodePermutationCalls = 73728` permutation calls on every path, and `fromBytesWithHash H`
  at most `wireDecodeHashCalls` calls of `H`, each on at most `512` bytes.
-/

module

public import Common.Prob
public import Common.PiOnly
public import LeanVM.Wire.Spec

/-!
# The decoding's cost

Decoding reads the bytes first (`readProof`), which queries nothing, then unprunes each phase:
it hashes each distinct leaf once and, at each level, each parent once. A phase `readPhase`
accepts has at most `wireMaxQueries` distinct positions (`distinctPositions` of at most
`wireMaxQueries` queries), as many leaves, each of at most `wireMaxLeafWords` words (`512`
bytes), and one level of carried siblings per level of the tree, at most `wireMaxHeight`; a
level has at most as many parents as nodes, so at most `wireMaxQueries`, each the hash of two
digests (`64` bytes). With at most `wireMaxPhases` phases:

* `fromBytesWithHash_queryCost`: with a hash `H` costing at most `leafCost` on at most `512`
  bytes and `pairCost` on `64` bytes, decoding costs at most
  `wireMaxPhases * (wireMaxQueries * leafCost + wireMaxHeight * (wireMaxQueries * pairCost))`;
  one per call, `wireDecodeHashCalls` (`fromBytesWithHash_hashCalls`);
* `fromBytes_queryCost`: Keccak-256 over `π` makes `⌊n / 136⌋ + 1` permutation calls on `n`
  bytes, four on a leaf and one on a pair, so `Proof.fromBytes queryPermutation` makes at most
  `wireDecodePermutationCalls = 73728` (`wireDecodePermutationCalls_eq`);
* `bind_fromBytes_queryCost`: an adversary within `Q` calls whose bytes are then decoded is
  within `Q + wireDecodePermutationCalls`.
-/

@[expose] public section

namespace LeanVM.Wire

open OracleComp OracleSpec
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile

/-! ## The bounds `readProof` guarantees

Helpers in `LeanVM.Wire.Cost`, apart from the other wire modules' names. -/

namespace Cost

theorem length_dedupByKey_le {α β : Type} [DecidableEq β] (key : α → β) :
    ∀ l : List α, (dedupByKey key l).length ≤ l.length
  | [] => le_rfl
  | a :: rest => by
    have ih := length_dedupByKey_le key rest
    simp only [dedupByKey]
    split
    · simp
    · rename_i b kept h
      rw [h] at ih
      split <;> simp_all; omega

theorem length_distinctPositions_le (queries : List ℕ) :
    (distinctPositions queries).length ≤ queries.length :=
  (length_dedupByKey_le _ _).trans (List.length_mergeSort _).le

theorem readU32s_length : ∀ (count : ℕ) (input : Bytes) (values : List ℕ) (rest : Bytes),
    readU32s count input = some (values, rest) → values.length = count
  | 0, input, values, rest, h => by simp [readU32s] at h; simp [← h.1]
  | count + 1, input, values, rest, h => by
    simp only [readU32s, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨value, input'⟩, -, ⟨⟨values', input''⟩, h2, h3⟩⟩ := h
    simp only [Option.some.injEq, Prod.mk.injEq] at h3
    rw [← h3.1, List.length_cons, readU32s_length count input' values' input'' h2]

theorem readWords_length (count : ℕ) (input : Bytes) (words : List K) (rest : Bytes)
    (h : readWords count input = some (words, rest)) : words.length = count := by
  simp only [readWords, Option.map_eq_some_iff] at h
  obtain ⟨_, -, h⟩ := h
  simp only [Prod.mk.injEq] at h
  rw [← h.1, List.length_map, List.length_range]

theorem readRows_spec (rowWords : ℕ) : ∀ (count : ℕ) (input : Bytes) (rows : List (List K))
    (rest : Bytes), readRows rowWords count input = some (rows, rest) →
      rows.length = count ∧ ∀ row ∈ rows, row.length = rowWords
  | 0, input, rows, rest, h => by simp [readRows] at h; obtain ⟨rfl, -⟩ := h; simp
  | count + 1, input, rows, rest, h => by
    simp only [readRows, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨row, input'⟩, h1, ⟨⟨rows', input''⟩, h2, h3⟩⟩ := h
    simp only [Option.some.injEq, Prod.mk.injEq] at h3
    obtain ⟨ih1, ih2⟩ := readRows_spec rowWords count input' rows' input'' h2
    rw [← h3.1]
    refine ⟨by simp [ih1], fun r hr ↦ ?_⟩
    rcases List.mem_cons.mp hr with rfl | hr
    · exact readWords_length _ _ _ _ h1
    · exact ih2 r hr

theorem readCarriedSiblings_length (positions : List ℕ) : ∀ (level remaining : ℕ) (input : Bytes)
    (carried : List (List (ℕ × Digest))) (rest : Bytes),
    readCarriedSiblings positions level remaining input = some (carried, rest) →
      carried.length = remaining
  | _, 0, input, carried, rest, h => by simp [readCarriedSiblings] at h; simp [← h.1]
  | level, remaining + 1, input, carried, rest, h => by
    simp only [readCarriedSiblings, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨digests, input'⟩, -, ⟨⟨above, input''⟩, h2, h3⟩⟩ := h
    simp only [Option.some.injEq, Prod.mk.injEq] at h3
    rw [← h3.1, List.length_cons,
      readCarriedSiblings_length positions (level + 1) remaining input' above input'' h2]

theorem of_guard_eq_some {p : Prop} [Decidable p] {u : Unit}
    (h : (guard p : Option Unit) = some u) : p := by
  simp only [guard] at h
  split at h
  · assumption
  · simp [failure] at h

/-- The bounds of a phase `readPhase` accepts that its unpruning's cost depends on. -/
structure PhaseWithinBounds (phase : PrunedPhase) : Prop where
  leaves_le : phase.leaves.length ≤ wireMaxQueries
  leaf_le : ∀ leaf ∈ phase.leaves, leaf.length ≤ wireMaxLeafWords
  positions_le : phase.positions.length ≤ wireMaxQueries
  carried_le : phase.carried.length ≤ wireMaxHeight

theorem readPhase_withinBounds (input : Bytes) (phase : PrunedPhase) (rest : Bytes)
    (h : readPhase input = some (phase, rest)) : PhaseWithinBounds phase := by
  simp only [readPhase, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨count, input1⟩, -, _, hCount, ⟨queries, input2⟩, hQueries, ⟨height, input3⟩, -,
    ⟨leafWords, input4⟩, -, ⟨rowWords, input5⟩, -, _, hShape, ⟨rows, input6⟩, hRows, _, -,
    ⟨carried, input7⟩, hCarried, hPhase⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq] at hPhase
  obtain ⟨rfl, -⟩ := hPhase
  have hCount' := of_guard_eq_some hCount
  have hShape' := of_guard_eq_some hShape
  have hq := readU32s_length _ _ _ _ hQueries
  obtain ⟨hRows1, hRows2⟩ := readRows_spec _ _ _ _ _ hRows
  have hp := length_distinctPositions_le queries
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [List.length_map, hRows1]; omega
  · intro leaf hleaf
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hleaf
    simp only [paddedLeaf, List.length_append, List.length_replicate, hRows2 row hrow]
    omega
  · simp only; omega
  · simp only [readCarriedSiblings_length _ _ _ _ _ _ hCarried]; exact hShape'.1

theorem readPhases_withinBounds : ∀ (count : ℕ) (input : Bytes) (phases : List PrunedPhase)
    (rest : Bytes), readPhases count input = some (phases, rest) →
      phases.length = count ∧ ∀ phase ∈ phases, PhaseWithinBounds phase
  | 0, input, phases, rest, h => by simp [readPhases] at h; obtain ⟨rfl, -⟩ := h; simp
  | count + 1, input, phases, rest, h => by
    simp only [readPhases, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨phase, input'⟩, h1, ⟨⟨phases', input''⟩, h2, h3⟩⟩ := h
    simp only [Option.some.injEq, Prod.mk.injEq] at h3
    obtain ⟨ih1, ih2⟩ := readPhases_withinBounds count input' phases' input'' h2
    rw [← h3.1]
    refine ⟨by simp [ih1], fun p hp ↦ ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact readPhase_withinBounds _ _ _ h1
    · exact ih2 p hp

theorem readProof_withinBounds (bytes : Bytes) (stream : List E) (phases : List PrunedPhase)
    (h : readProof bytes = some (stream, phases)) :
    phases.length ≤ wireMaxPhases ∧ ∀ phase ∈ phases, PhaseWithinBounds phase := by
  simp only [readProof, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, ⟨phaseCount, input⟩, _, _, hCount, ⟨phases', rest⟩, hPhases, _, _, hProof⟩ :=
    h
  simp only [Option.some.injEq, Prod.mk.injEq] at hProof
  obtain ⟨-, rfl⟩ := hProof
  obtain ⟨h1, h2⟩ := readPhases_withinBounds _ _ _ _ hPhases
  exact ⟨h1 ▸ of_guard_eq_some hCount, h2⟩

/-! ## Costs through `mapM` and Keccak-256 over `π`; `fromBytes` as `fromBytesWithHash` -/

section Generic

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} (w : ι → ℕ)

/-- **A `mapM`, then a continuation**: `c` per element, then `Q` for the continuation on every
list as long as the input. -/
theorem mapM_bind_queryCost {α β γ : Type} (f : α → OracleComp spec β)
    (g : List β → OracleComp spec γ) (c Q : ℕ) :
    ∀ l : List α, (∀ a ∈ l, Common.QueryCostAtMost (f a) w c) →
      (∀ results : List β, results.length = l.length → Common.QueryCostAtMost (g results) w Q) →
        Common.QueryCostAtMost (l.mapM f >>= g) w (l.length * c + Q)
  | [], _, hg => by simpa using hg [] rfl
  | a :: l, hf, hg => by
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    have h := (hf a List.mem_cons_self).bind fun b ↦
      mapM_bind_queryCost f (fun results ↦ g (b :: results)) c Q l
        (fun a' ha' ↦ hf a' (List.mem_cons_of_mem a ha'))
        (fun results hr ↦ hg (b :: results) (by simp [hr]))
    exact h.mono (by rw [List.length_cons, Nat.succ_mul]; omega)

/-- A computation, then a pure function of its result: the computation's cost. -/
theorem bind_pure_queryCost {α β : Type} {oa : OracleComp spec α} {f : α → β} {Q : ℕ}
    (h : Common.QueryCostAtMost oa w Q) :
    Common.QueryCostAtMost (oa >>= fun a ↦ pure (f a)) w Q := by
  rw [bind_pure_comp]
  exact Common.isWeightBound_map f h

theorem length_digestBytes (digest : Digest) : (digestBytes digest).length = 32 := by
  simp [digestBytes, wordBytes]

end Generic

/-- **Keccak-256 over `π` makes `⌊n / 136⌋ + 1` permutation calls** on `n` bytes. -/
theorem keccak256With_queryCost (data : Bytes) :
    Common.QueryCostAtMost (keccak256With Common.queryPermutation data) Common.permutationCallCost
      (data.length / 136 + 1) := by
  have h := Common.isWeightBound_absorbWith (Q' := 0)
    (g := fun state ↦ (pure #v[Keccak.lane state 0, Keccak.lane state 1, Keccak.lane state 2,
      Keccak.lane state 3] : OracleComp Common.RandomPermutationOracles Digest))
    (fun _ ↦ Common.isWeightBound_pure _ _ 0) (data.length / rate) (Vector.replicate 25 0) data
  simpa [keccak256With, rate] using h

section Bridge

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

theorem climbLevels_eq_withHash : ∀ (carried : List (List (ℕ × Digest)))
    (nodes : List (ℕ × Digest)),
    climbLevels π carried nodes = climbLevelsWithHash (keccak256With π) carried nodes
  | [], _ => rfl
  | level :: above, nodes => by
    simp only [climbLevels, climbLevelsWithHash, climbLevel, climbLevelWithHash,
      climbLevels_eq_withHash above]

/-- `Proof.fromBytes π` is `fromBytesWithHash` with Keccak-256 over `π`. -/
theorem fromBytes_eq_fromBytesWithHash (bytes : Bytes) :
    Proof.fromBytes π bytes = fromBytesWithHash (keccak256With π) bytes := by
  have h : unprunePhase π = unprunePhaseWithHash (keccak256With π) := by
    funext phase
    simp only [unprunePhase, unprunePhaseWithHash, climbLevels_eq_withHash]
  simp only [Proof.fromBytes, fromBytesWithHash, h]
  rcases readProof bytes with _ | ⟨stream, phases⟩ <;> rfl

end Bridge

end Cost

open Cost

/-! ## The cost of unpruning, with a hash of its own -/

section WithHash

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} (w : ι → ℕ) (H : Bytes → OracleComp spec Digest)

/-- **The climb's cost**: at each level at most as many parents as nodes, each one hash of
`64` bytes. -/
theorem climbLevelsWithHash_queryCost (pairCost : ℕ)
    (hPair : ∀ x : Bytes, x.length = 64 → Common.QueryCostAtMost (H x) w pairCost) (nodeCount : ℕ) :
    ∀ (carried : List (List (ℕ × Digest))) (nodes : List (ℕ × Digest)), nodes.length ≤ nodeCount →
      Common.QueryCostAtMost (climbLevelsWithHash H carried nodes) w
        (carried.length * (nodeCount * pairCost))
  | [], _, _ => trivial
  | level :: above, nodes, hNodes => by
    simp only [climbLevelsWithHash, climbLevelWithHash, bind_assoc, pure_bind]
    have hFilter := (List.length_filter_le (fun x : ℕ × Digest ↦
      decide (x.1 % 2 = 0 ∨ x.1 ^^^ 1 ∉ nodes.map (·.1))) nodes).trans hNodes
    refine (mapM_bind_queryCost w _ _ pairCost (above.length * (nodeCount * pairCost)) _ ?_ ?_).mono
      ?_
    · intro x _
      apply bind_pure_queryCost
      apply hPair
      simp [length_digestBytes]
    · intro parents hParents
      apply bind_pure_queryCost
      exact climbLevelsWithHash_queryCost pairCost hPair nodeCount above parents
        (hParents ▸ hFilter)
    have := Nat.mul_le_mul_right pairCost hFilter
    rw [List.length_cons, Nat.succ_mul]
    omega

/-- **A phase's unpruning cost**: each leaf hashed once, then the climb. -/
theorem unprunePhaseWithHash_queryCost (leafCost pairCost : ℕ)
    (hLeaf : ∀ x : Bytes, x.length ≤ 8 * wireMaxLeafWords → Common.QueryCostAtMost (H x) w leafCost)
    (hPair : ∀ x : Bytes, x.length = 64 → Common.QueryCostAtMost (H x) w pairCost)
    (phase : PrunedPhase) (hPhase : PhaseWithinBounds phase) :
    Common.QueryCostAtMost (unprunePhaseWithHash H phase) w
      (wireMaxQueries * leafCost + wireMaxHeight * (wireMaxQueries * pairCost)) := by
  simp only [unprunePhaseWithHash]
  refine (mapM_bind_queryCost w _ _ leafCost (wireMaxHeight * (wireMaxQueries * pairCost)) _ ?_
    ?_).mono ?_
  · intro leaf hMem
    apply hLeaf
    have := hPhase.leaf_le leaf hMem
    simp [List.length_flatMap, K.toBytes, wordBytes]
    omega
  · intro digests hDigests
    apply bind_pure_queryCost
    refine (climbLevelsWithHash_queryCost w H pairCost hPair wireMaxQueries _ _ ?_).mono ?_
    · rw [List.length_zip]; exact (min_le_left _ _).trans hPhase.positions_le
    · exact Nat.mul_le_mul_right _ hPhase.carried_le
  · exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hPhase.leaves_le) _

/-- **The decoding's cost with a hash of its own**: with `H` costing at most `leafCost` on at
most `512` bytes and `pairCost` on `64` bytes, at most `wireMaxPhases` phases of at most
`wireMaxQueries` leaves and `wireMaxHeight` levels of at most `wireMaxQueries` parents. -/
theorem fromBytesWithHash_queryCost (leafCost pairCost : ℕ)
    (hLeaf : ∀ x : Bytes, x.length ≤ 8 * wireMaxLeafWords → Common.QueryCostAtMost (H x) w leafCost)
    (hPair : ∀ x : Bytes, x.length = 64 → Common.QueryCostAtMost (H x) w pairCost) (bytes : Bytes) :
    Common.QueryCostAtMost (fromBytesWithHash H bytes) w
      (wireMaxPhases *
        (wireMaxQueries * leafCost + wireMaxHeight * (wireMaxQueries * pairCost))) := by
  unfold fromBytesWithHash
  split
  · trivial
  · rename_i stream phases hRead
    obtain ⟨hCount, hPhases⟩ := readProof_withinBounds bytes stream phases hRead
    apply bind_pure_queryCost
    have h := mapM_bind_queryCost w (unprunePhaseWithHash H) pure
      (wireMaxQueries * leafCost + wireMaxHeight * (wireMaxQueries * pairCost)) 0 phases
      (fun phase hMem ↦ unprunePhaseWithHash_queryCost w H leafCost pairCost hLeaf hPair phase
        (hPhases phase hMem))
      (fun _ _ ↦ Common.isWeightBound_pure _ w 0)
    rw [bind_pure] at h
    exact h.mono (by simpa using Nat.mul_le_mul_right _ hCount)

/-- **The decoding's hash calls**: at most `wireDecodeHashCalls` calls of `H`, each on at most
`512` bytes, when each call costs at most one. -/
theorem fromBytesWithHash_hashCalls
    (hCall : ∀ x : Bytes, x.length ≤ 8 * wireMaxLeafWords → Common.QueryCostAtMost (H x) w 1)
    (bytes : Bytes) : Common.QueryCostAtMost (fromBytesWithHash H bytes) w wireDecodeHashCalls := by
  have h := fromBytesWithHash_queryCost w H 1 1 hCall
    (fun x hx ↦ hCall x (by simp [hx, wireMaxLeafWords])) bytes
  simpa [wireDecodeHashCalls] using h

end WithHash

/-! ## Over the random permutation -/

/-- **The decoding's permutation calls**: `Proof.fromBytes` over the random permutation makes at
most `wireDecodePermutationCalls` calls of `π` on every path: a leaf of at most `512` bytes is
four calls of Keccak-256, a pair of digests (`64` bytes) one. -/
theorem fromBytes_queryCost (bytes : Bytes) :
    Common.QueryCostAtMost (Proof.fromBytes Common.queryPermutation bytes)
      Common.permutationCallCost wireDecodePermutationCalls := by
  rw [fromBytes_eq_fromBytesWithHash]
  have h := fromBytesWithHash_queryCost Common.permutationCallCost
    (keccak256With Common.queryPermutation) 4 1
    (fun x hx ↦ (keccak256With_queryCost x).mono (by simp only [wireMaxLeafWords] at hx; omega))
    (fun x hx ↦ (keccak256With_queryCost x).mono (by omega)) bytes
  simpa [wireDecodePermutationCalls, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

theorem wireDecodePermutationCalls_eq : wireDecodePermutationCalls = 73728 := by
  decide

theorem wireDecodeHashCalls_eq : wireDecodeHashCalls = 67584 := by
  decide

/-- **An adversary, then the decoding of its bytes**: within `Q + wireDecodePermutationCalls`
permutation calls when the adversary is within `Q`. -/
theorem bind_fromBytes_queryCost {α : Type}
    {adversary : OracleComp Common.RandomPermutationOracles α} (bytesOf : α → Bytes) {Q : ℕ}
    (hAdversary : Common.QueryCostAtMost adversary Common.permutationCallCost Q) :
    Common.QueryCostAtMost
      (adversary >>= fun a ↦ Proof.fromBytes Common.queryPermutation (bytesOf a))
      Common.permutationCallCost (Q + wireDecodePermutationCalls) :=
  hAdversary.bind fun a ↦ fromBytes_queryCost (bytesOf a)

end LeanVM.Wire

end
