/-
  LeanVM.Wire.OneEncoding

  Bytes that decode to a proof are that proof's encoding (`oneEncoding`): the encoding is the only
  one, decoding refuses every other byte string.
-/

module

public import LeanVM.Wire.RoundTrip

/-!
# One encoding

`fromBytesWithHash h bytes = some proof → proof.toBytes = bytes`, for every hash `h`. The decoding
reads the bytes (`readProof`) and unprunes each phase; the encoding writes them back:

* the stream's length and words, regrouped into elements of three words and back
  (`flatMap_toBytes_regroup`); the number of phases;
* each phase: re-encoding the phase unpruned gives back the bytes it was read from
  (`readPhase b = some (phase, rest) → b = phaseToBytes (unprunePhaseWithHash h phase) ++ rest`),
  from the determinism of the reading (`LeanVM.Wire.toBytes_of_readProof`, the phase's bytes are
  `encodePhase phase`) and the encoding of the unpruned phase (its header and rows,
  `LeanVM.Wire.OneEncodingRow`; its siblings, `LeanVM.Wire.OneEncodingSib`).

`oneEncoding_of` composes them from the readers' determinism and that phase step, taken as
hypotheses; `oneEncoding` instantiates them.

The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven).
-/

public section

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile

/-- The stream's words, regrouped by three into elements as `readProof` does, are written back as
the same words. -/
theorem flatMap_toBytes_regroup (count : ℕ) (words : List K) (hlength : words.length = 3 * count) :
    ((List.range count).map fun i ↦ E.ofLimbs (words.getD (3 * i) 0) (words.getD (3 * i + 1) 0)
        (words.getD (3 * i + 2) 0)).flatMap E.toBytes = words.flatMap K.toBytes := by
  induction count generalizing words with
  | zero =>
    cases words with
    | nil => rfl
    | cons => simp at hlength
  | succ count ih =>
    match words, hlength with
    | c0 :: c1 :: c2 :: rest, hlength =>
      have hrest : rest.length = 3 * count := by simp at hlength; omega
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [List.flatMap_cons]
      rw [← ih rest hrest]
      have hshift : ∀ i j, (c0 :: c1 :: c2 :: rest).getD (3 * (i + 1) + j) 0 = rest.getD (3 * i + j) 0 :=
        fun i j ↦ by
          rw [show 3 * (i + 1) + j = (3 * i + j) + 1 + 1 + 1 by omega]
          simp only [List.getD_cons_succ]
      have hshift0 := fun i ↦ hshift i 0
      simp only [Nat.add_zero] at hshift0
      simp only [Function.comp_def, Nat.succ_eq_add_one, hshift0, List.getD_cons_zero,
        List.getD_cons_succ, Nat.mul_zero, Nat.zero_add, E.toBytes,
        List.append_assoc]
      rfl

/-- `count` phases read back are written back by the phase step. -/
theorem readPhases_eq_toBytes (h : Bytes → Digest)
    (phase_eq : ∀ bytes phase rest, readPhase bytes = some (phase, rest) →
      bytes = Prover.phaseToBytes (unprunePhaseWithHash (m := Id) h phase) ++ rest) :
    ∀ (count : ℕ) (bytes : Bytes) (phases : List PrunedPhase) (rest : Bytes),
      readPhases count bytes = some (phases, rest) →
        phases.length = count ∧
          bytes = (phases.map (unprunePhaseWithHash (m := Id) h)).flatMap Prover.phaseToBytes ++
            rest
  | 0, bytes, phases, rest, hread => by
    simp only [readPhases, Option.some.injEq, Prod.mk.injEq] at hread
    obtain ⟨rfl, rfl⟩ := hread
    simp
  | count + 1, bytes, phases, rest, hread => by
    simp only [readPhases, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at hread
    obtain ⟨phase, input, hphase, phases', input', hphases, hsome⟩ := hread
    simp only [Option.some.injEq, Prod.mk.injEq] at hsome
    obtain ⟨rfl, hrest⟩ := hsome
    obtain ⟨hlength, hbytes⟩ := readPhases_eq_toBytes h phase_eq count input phases' input' hphases
    refine ⟨by simp [hlength], ?_⟩
    rw [phase_eq bytes phase input hphase, hbytes, hrest]
    simp only [List.map_cons, List.flatMap_cons, List.append_assoc]

/-- **One encoding from its steps**: the readers' determinism (a 32-bit word, words) and the phase
step (re-encoding a phase read back and unpruned gives the bytes it was read from). -/
theorem oneEncoding_of
    (u32_eq : ∀ bytes value rest, readU32 bytes = some (value, rest) →
      value < 2 ^ 32 ∧ bytes = Prover.u32Bytes value ++ rest)
    (words_eq : ∀ count bytes words rest, readWords count bytes = some (words, rest) →
      bytes = words.flatMap K.toBytes ++ rest ∧ words.length = count)
    (phase_eq : ∀ (h : Bytes → Digest) bytes phase rest, readPhase bytes = some (phase, rest) →
      bytes = Prover.phaseToBytes (unprunePhaseWithHash (m := Id) h phase) ++ rest) :
    OneEncodingStatement := by
  intro h bytes proof hdecode
  unfold fromBytesWithHash at hdecode
  cases hread : readProof bytes with
  | none => rw [hread] at hdecode; cases hdecode
  | some x =>
    obtain ⟨stream, phases⟩ := x
    rw [hread] at hdecode
    change some (⟨stream, (phases.mapM (unprunePhaseWithHash (m := Id) h)).run⟩ : Proof) =
      some proof at hdecode
    rw [List.idRun_mapM, Option.some.injEq] at hdecode
    subst hdecode
    simp only [readProof, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists,
      Option.guard_eq_some', Option.some.injEq, Prod.mk.injEq] at hread
    obtain ⟨length, input₁, hlength, words, input₂, hwords, phaseCount, input₃, hcount, -, -,
      phases', input₄, hphases, -, hempty, rfl, rfl⟩ := hread
    obtain ⟨-, hbytes₁⟩ := u32_eq _ _ _ hlength
    obtain ⟨hbytes₂, hwordsLength⟩ := words_eq _ _ _ _ hwords
    obtain ⟨-, hbytes₃⟩ := u32_eq _ _ _ hcount
    obtain ⟨hphasesLength, hbytes₄⟩ := readPhases_eq_toBytes h (phase_eq h) _ _ _ _ hphases
    have hempty' : input₄ = [] := by simpa using hempty
    subst hempty'
    rw [hbytes₁, hbytes₂, hbytes₃, hbytes₄]
    simp only [Proof.toBytes, List.length_map, List.length_range, hphasesLength,
      flatMap_toBytes_regroup length words hwordsLength, List.append_nil, List.append_assoc]
    rfl

end LeanVM.Wire

end
