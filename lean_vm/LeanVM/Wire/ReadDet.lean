/-
  LeanVM.Wire.ReadDet

  The bytes a pruned proof encodes to (`encodePhase`, `encodePruned`) and the reader's determinism:
  bytes `readPhase` / `readProof` accept are the encoding of what they read.
-/

module

public import LeanVM.Wire.Spec

/-!
# The reader's determinism

`encodePhase ph` is what `Prover.phaseToBytes` writes, computed from the pruned form `ph` instead of
the paths: the queries' count and positions, the height, the leaf width and the row width (the leaf
width less the zero words common to the fronts of the leaves, `zeroPrefix`, as `phaseToBytes`
computes them), each leaf without that prefix, and the carried siblings' digests level by level, in
order. `encodePruned` is `Proof.toBytes` from the pruned form: the stream's length and elements, the
phase count and each phase.

The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven).
-/

@[expose] public section

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile

/-- The number of zero words common to the fronts of the leaves, as `Prover.phaseToBytes` computes
it: the least, over the leaves, of the length of the leaf's leading run of zeros; `0` for no leaf. -/
def zeroPrefix (leaves : List (List K)) : ℕ :=
  ((leaves.map fun leaf ↦ (leaf.takeWhile fun word ↦ decide (word = 0)).length).min?).getD 0

/-- The bytes of a pruned phase: the queries' count and positions; the height, the leaf width and
the row width `leafWords - zeroPrefix leaves`; each leaf without the common zero prefix; then the
carried siblings' digests, level by level, in order. -/
def encodePhase (ph : PrunedPhase) : Bytes :=
  let zeros := zeroPrefix ph.leaves
  Prover.u32Bytes ph.queries.length ++ ph.queries.flatMap Prover.u32Bytes ++
    Prover.u32Bytes ph.height ++ Prover.u32Bytes ph.leafWords ++
    Prover.u32Bytes (ph.leafWords - zeros) ++
    ph.leaves.flatMap (fun leaf ↦ (leaf.drop zeros).flatMap K.toBytes) ++
    ph.carried.flatMap fun level ↦ level.flatMap fun carried ↦ digestBytes carried.2

/-- The bytes of a pruned proof, as `Proof.toBytes` writes them: the stream's length, then each
element as its three words; the number of phases, then each phase (`encodePhase`). -/
def encodePruned (x : List E × List PrunedPhase) : Bytes :=
  Prover.u32Bytes x.1.length ++ x.1.flatMap E.toBytes ++
    Prover.u32Bytes x.2.length ++ x.2.flatMap encodePhase

/-! ## What `readPhase` guarantees -/

/-- **Everything `readPhase` guarantees about the phase it reads** (`phaseRead_of_readPhase`): at
most `wireMaxQueries` queries, each below `2 ^ 32`; height at most `wireMaxHeight`, leaf width at
most `wireMaxLeafWords`; the positions the queries' distinct ones ascending, at least one, all
below `2 ^ height`; one leaf per position, each of the leaf width; the row width minimal (some
`rowWords ≤ leafWords` with every leaf `rowWords` words after `leafWords - rowWords` zeros, and
`rowWords = 0` or some leaf's word at `leafWords - rowWords` nonzero; hence
`zeroPrefix leaves = leafWords - rowWords`, `PhaseRead.zeroPrefix_eq`); and, level by level, the
carried siblings keyed by `carriedSiblings (levelNodes positions level)`, one list per level. -/
structure PhaseRead (ph : PrunedPhase) : Prop where
  queries_length_le : ph.queries.length ≤ wireMaxQueries
  queries_lt : ∀ query ∈ ph.queries, query < 2 ^ 32
  height_le : ph.height ≤ wireMaxHeight
  leafWords_le : ph.leafWords ≤ wireMaxLeafWords
  positions_eq : ph.positions = distinctPositions ph.queries
  positions_ne_nil : ph.positions ≠ []
  positions_lt : ∀ position ∈ ph.positions, position < 2 ^ ph.height
  leaves_length : ph.leaves.length = ph.positions.length
  leaf_length : ∀ leaf ∈ ph.leaves, leaf.length = ph.leafWords
  rowWidth : ∃ rowWords ≤ ph.leafWords,
    (∀ leaf ∈ ph.leaves, ∃ row, row.length = rowWords ∧ leaf = paddedLeaf row ph.leafWords) ∧
    (rowWords = 0 ∨ ∃ leaf ∈ ph.leaves, leaf.getD (ph.leafWords - rowWords) 0 ≠ 0)
  carried_keys : ph.carried.map (·.map Prod.fst) =
    (List.range ph.height).map fun level ↦ carriedSiblings (levelNodes ph.positions level)

/-! ## The readers' converse forms (`LeanVM.Wire.ReadWrite`, rtrw) -/

/-- The basic readers' determinism: a 32-bit word read is below `2 ^ 32` and its four bytes; words
read are their bytes, as many as asked; a digest read is its 32 bytes. Proved in
`LeanVM.Wire.ReadWrite`; a hypothesis here until it is merged. -/
structure ReaderConverse : Prop where
  u32_eq : ∀ bytes value rest, readU32 bytes = some (value, rest) →
    value < 2 ^ 32 ∧ bytes = Prover.u32Bytes value ++ rest
  words_eq : ∀ count bytes words rest, readWords count bytes = some (words, rest) →
    bytes = words.flatMap K.toBytes ++ rest ∧ words.length = count
  digest_eq : ∀ bytes digest rest, readDigest bytes = some (digest, rest) →
    bytes = digestBytes digest ++ rest

namespace ReaderConverse

variable (hc : ReaderConverse)
include hc

theorem u32s_eq : ∀ count bytes values rest, readU32s count bytes = some (values, rest) →
    values.length = count ∧ (∀ value ∈ values, value < 2 ^ 32) ∧
      bytes = values.flatMap Prover.u32Bytes ++ rest
  | 0, bytes, values, rest, h => by
    simp only [readU32s, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | count + 1, bytes, values, rest, h => by
    simp only [readU32s, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨value, input, hvalue, values', input', hvalues, rfl, rfl⟩ := h
    obtain ⟨hlt, rfl⟩ := hc.u32_eq _ _ _ hvalue
    obtain ⟨hlength, hall, rfl⟩ := u32s_eq count _ _ _ hvalues
    refine ⟨by simp [hlength], ?_, by simp⟩
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    exacts [hlt, hall w hw]

theorem digests_eq : ∀ count bytes digests rest, readDigests count bytes = some (digests, rest) →
    digests.length = count ∧ bytes = digests.flatMap digestBytes ++ rest
  | 0, bytes, digests, rest, h => by
    simp only [readDigests, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | count + 1, bytes, digests, rest, h => by
    simp only [readDigests, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨digest, input, hdigest, digests', input', hdigests, rfl, rfl⟩ := h
    have := hc.digest_eq _ _ _ hdigest
    subst this
    obtain ⟨hlength, rfl⟩ := digests_eq count _ _ _ hdigests
    exact ⟨by simp [hlength], by simp⟩

theorem rows_eq (rowWords : ℕ) : ∀ count bytes rows rest,
    readRows rowWords count bytes = some (rows, rest) →
      rows.length = count ∧ (∀ row ∈ rows, row.length = rowWords) ∧
        bytes = rows.flatMap (·.flatMap K.toBytes) ++ rest
  | 0, bytes, rows, rest, h => by
    simp only [readRows, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | count + 1, bytes, rows, rest, h => by
    simp only [readRows, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨row, input, hrow, rows', input', hrows, rfl, rfl⟩ := h
    obtain ⟨rfl, hrowLength⟩ := hc.words_eq _ _ _ _ hrow
    obtain ⟨hlength, hall, rfl⟩ := rows_eq rowWords count _ _ _ hrows
    refine ⟨by simp [hlength], ?_, by simp⟩
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    exacts [hrowLength, hall r hr]

theorem carriedSiblings_eq (positions : List ℕ) : ∀ level remaining bytes carried rest,
    readCarriedSiblings positions level remaining bytes = some (carried, rest) →
      carried.map (·.map Prod.fst) =
          (List.range' level remaining).map (fun l ↦ carriedSiblings (levelNodes positions l)) ∧
        bytes = carried.flatMap (fun lvl ↦ lvl.flatMap fun x ↦ digestBytes x.2) ++ rest
  | _, 0, bytes, carried, rest, h => by
    simp only [readCarriedSiblings, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | level, remaining + 1, bytes, carried, rest, h => by
    simp only [readCarriedSiblings, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨digests, input, hdigests, above, input', habove, rfl, rfl⟩ := h
    obtain ⟨hlength, rfl⟩ := digests_eq hc _ _ _ _ hdigests
    obtain ⟨hkeys, rfl⟩ := carriedSiblings_eq positions (level + 1) remaining _ _ _ habove
    refine ⟨?_, ?_⟩
    · rw [List.range'_succ, List.map_cons, List.map_cons, hkeys,
        List.map_fst_zip (by omega)]
    · have hsnd := List.map_snd_zip (l₁ := carriedSiblings (levelNodes positions level))
        (l₂ := digests) (by omega)
      have : (List.zip (carriedSiblings (levelNodes positions level)) digests).flatMap
          (fun x ↦ digestBytes x.2) = digests.flatMap digestBytes := by
        conv_rhs => rw [← hsnd]
        rw [List.flatMap_map]
      simp only [List.flatMap_cons, this, List.append_assoc]

end ReaderConverse

end LeanVM.Wire

end
