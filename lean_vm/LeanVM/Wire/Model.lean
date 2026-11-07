/-
  LeanVM.Wire.Model

  Decoding the honest proof's bytes after the prover's run, in the random-permutation model: it
  answers `some proof` and leaves the lazily sampled permutation as it was.
-/

module

public import LeanVM.Protocol.WithHash
public import Common.PiOnly
public import LeanVM.Wire.ModelPerm
public import LeanVM.Wire.ModelDecode

/-!
# Decoding after the honest prover, in the model

The completeness experiment on the wire runs the honest prover, encodes its proof, decodes the
bytes and verifies the result, Keccak-256 the sponge over the lazily sampled permutation and
Keccak-f[1600] the permutation (`keccakCallsOverRandomPermutation`). Decoding hashes Merkle nodes,
and a fresh query would change the permutation's later answers. `fromBytesWithHash_run_of` shows it
makes none: after a run of a computation `X` that ends with a proof `p` and edges `s`, decoding
`p.toBytes` returns `some p` and leaves `s` as it was, provided `X`'s proofs survive their encoding
with the hash they were computed with (`hwd`) and `X` hashed every input its proofs' paths climb
through (`hlog`): the honest prover does both (`proveWithHash_wireDecodable`,
`proveWithHash_climbInputsIn`, `LeanVM/Wire/Honest.lean`). The steps:

1. the two calls are computations over the permutation (`toPermutationCalls`), so the generic
   replay and cache apply (`LeanVM/Wire/ModelPerm.lean`); `s` lies on a permutation `σ`;
2. replay: `X`'s run is its run with `σ`'s answers, the hash `keccak256With σ` (`hashOf σ`), so its
   proof survives its encoding with that hash (`hwd`), and every call it made is recorded in `s`;
3. decoding with `keccak256With σ` hashes only inputs the proof's paths climb through
   (`logsIn_fromBytesWithHash`), which `X` hashed (`hlog`), so every call decoding makes is
   recorded in `s`;
4. cache: decoding runs from `s` to its result with `σ`, adding no edge, and that result is
   `some p` (`roundTrip`).
-/

@[expose] public section

open OracleComp OracleSpec

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile
open Common (PermutationEdges PermutationQuery permutationOracleSpec lazyRandomPermutation)

/-! ## Decoding commutes with simulation -/

section Commute

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls r)

theorem simulateQ_climbLevelWithHash (nodes carried : List (ℕ × Digest)) :
    simulateQ impl (climbLevelWithHash callKeccak256 nodes carried) =
      climbLevelWithHash (fun x ↦ impl (.inl x)) nodes carried := by
  unfold climbLevelWithHash
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_list_mapM]
  congr 2
  funext x
  rcases x with ⟨node, digest⟩
  simp only [callKeccak256, simulateQ_spec_query]

theorem simulateQ_climbLevelsWithHash :
    ∀ (carried : List (List (ℕ × Digest))) (nodes : List (ℕ × Digest)),
      simulateQ impl (climbLevelsWithHash callKeccak256 carried nodes) =
        climbLevelsWithHash (fun x ↦ impl (.inl x)) carried nodes
  | [], _ => rfl
  | c :: above, nodes => by
    simp only [climbLevelsWithHash, simulateQ_bind, simulateQ_pure, simulateQ_climbLevelWithHash,
      simulateQ_climbLevelsWithHash above]

theorem simulateQ_unprunePhaseWithHash (phase : PrunedPhase) :
    simulateQ impl (unprunePhaseWithHash callKeccak256 phase) =
      unprunePhaseWithHash (fun x ↦ impl (.inl x)) phase := by
  unfold unprunePhaseWithHash
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_list_mapM, simulateQ_climbLevelsWithHash,
    callKeccak256, simulateQ_spec_query]

/-- **Decoding commutes with simulation.** -/
theorem simulateQ_fromBytesWithHash (bytes : Bytes) :
    simulateQ impl (fromBytesWithHash callKeccak256 bytes) =
      fromBytesWithHash (fun x ↦ impl (.inl x)) bytes := by
  unfold fromBytesWithHash
  split
  · rfl
  · simp only [simulateQ_bind, simulateQ_pure, simulateQ_list_mapM,
      simulateQ_unprunePhaseWithHash]

end Commute

/-! ## The calls over the permutation -/

/-- The permutation's forward query. -/
def forwardQuery (x : KeccakState) : OracleComp (permutationOracleSpec KeccakState) KeccakState :=
  liftM ((permutationOracleSpec KeccakState).query (.forward x))

/-- **The two calls as computations over the permutation**: Keccak-256 the sponge over it,
Keccak-f[1600] a forward query. -/
def toPermutationCalls : QueryImpl KeccakCalls (OracleComp (permutationOracleSpec KeccakState))
  | .inl x => keccak256With forwardQuery x
  | .inr s => forwardQuery s

theorem lazy_comp_toPermutationCalls :
    lazyRandomPermutation ∘ₛ toPermutationCalls = keccakCallsOverRandomPermutation := by
  funext t
  rcases t with x | s
  · show simulateQ lazyRandomPermutation (keccak256With forwardQuery x) =
      keccak256With lazyPermutationForward x
    rw [Common.simulateQ_keccak256With]
    congr 1
    funext y
    simp only [forwardQuery, simulateQ_spec_query]
    rfl
  · show simulateQ lazyRandomPermutation (forwardQuery s) = lazyPermutationForward s
    simp only [forwardQuery, simulateQ_spec_query]
    rfl

/-- Keccak-256 over the permutation `σ`. -/
def hashOf (σ : Equiv.Perm KeccakState) (x : Bytes) : Digest := keccak256With (m := Id) σ x

/-- The two calls answered by a hash and a permutation. -/
def pureCalls (h : Bytes → Digest) (F : KeccakState → KeccakState) : QueryImpl KeccakCalls Id
  | .inl x => h x
  | .inr s => F s

/-- The two calls answered by a hash and a permutation, the hash's inputs logged
(`loggedHash`, `loggedPerm`). -/
def loggedCalls (h : Bytes → Digest) (F : KeccakState → KeccakState) :
    QueryImpl KeccakCalls (StateM (List Bytes))
  | .inl x => loggedHash h x
  | .inr s => loggedPerm F s

theorem callAnswer_inl (σ : Equiv.Perm KeccakState) (x : Bytes) :
    callAnswer toPermutationCalls σ (.inl x) = hashOf σ x := by
  show simulateQ (pureImpl (permAnswer σ)) (keccak256With forwardQuery x) = _
  rw [Common.simulateQ_keccak256With]
  rfl

theorem pureImpl_callAnswer (σ : Equiv.Perm KeccakState) :
    pureImpl (callAnswer toPermutationCalls σ) = pureCalls (hashOf σ) σ := by
  funext t
  rcases t with x | s
  · exact callAnswer_inl σ x
  · rfl

/-- The hash inputs of a call. -/
def hashInput : Bytes ⊕ KeccakState → List Bytes
  | .inl x => [x]
  | .inr _ => []

theorem logImpl_callAnswer (σ : Equiv.Perm KeccakState) :
    logImpl hashInput (callAnswer toPermutationCalls σ) = loggedCalls (hashOf σ) σ := by
  funext t
  rcases t with x | s
  · show (do modify (· ++ [x]); pure (callAnswer toPermutationCalls σ (.inl x))) = _
    rw [callAnswer_inl]
    rfl
  · apply StateT.ext
    intro l
    simp [logImpl, loggedCalls, loggedPerm, hashInput, callAnswer, toPermutationCalls,
      forwardQuery, pureImpl, permAnswer]

theorem implH_logImpl_callAnswer (σ : Equiv.Perm KeccakState) :
    (fun x ↦ logImpl (fun q ↦ [q]) (callAnswer toPermutationCalls σ) (.inl x)) =
      tagHash Sum.inl (hashOf σ) := by
  funext x
  show (do modify (· ++ [Sum.inl x]); pure (callAnswer toPermutationCalls σ (.inl x))) = _
  rw [callAnswer_inl]
  rfl

/-! ## Decoding after a run -/

/-- **Decoding after a run that hashed its proof's paths**, in the random-permutation model: if a
computation `X`'s proofs survive their encoding with the hash they were computed with (`hwd`)
and `X` hashed every input its proofs' paths climb through (`hlog`), then after a run of `X` that
ends with the proof `p` and the edges `s`, decoding `p.toBytes` returns `some p` and leaves `s` as
it was. -/
theorem fromBytesWithHash_run_of (X : OracleComp KeccakCalls (Option Proof))
    (hwd : ∀ (h : Bytes → Digest) (F : KeccakState → KeccakState) (p : Proof),
      simulateQ (pureCalls h F) X = some p → WireDecodable h p)
    (hlog : ∀ (h : Bytes → Digest) (F : KeccakState → KeccakState) (p : Proof)
      (log : List Bytes), (simulateQ (loggedCalls h F) X).run [] = (some p, log) →
        ClimbInputsIn h p log)
    {p : Proof} {s : PermutationEdges KeccakState}
    (hp : (some p, s) ∈ support ((simulateQ keccakCallsOverRandomPermutation X).run [])) :
    (simulateQ keccakCallsOverRandomPermutation (fromBytesWithHash callKeccak256 p.toBytes)).run s =
      pure (some p, s) := by
  rw [← lazy_comp_toPermutationCalls] at hp ⊢
  obtain ⟨σ, hσ⟩ := exists_onPerm_of_mem_support_calls toPermutationCalls X hp
  obtain ⟨hrun, hrec⟩ := replay_calls toPermutationCalls X hp hσ
  rw [pureImpl_callAnswer] at hrun
  have hw : WireDecodable (hashOf σ) p := hwd _ _ p hrun
  have hlog' : ClimbInputsIn (hashOf σ) p
      ((queriesWith (callAnswer toPermutationCalls σ) X).flatMap hashInput) := by
    refine hlog _ σ p _ ?_
    rw [← logImpl_callAnswer, run_logImpl, pureImpl_callAnswer, hrun, List.nil_append]
  set D := fromBytesWithHash callKeccak256 p.toBytes
  have hD : simulateQ (pureImpl (callAnswer toPermutationCalls σ)) D = some p := by
    rw [simulateQ_fromBytesWithHash, pureImpl_callAnswer]
    exact roundTrip _ p hw
  rw [cached_calls toPermutationCalls D hσ ?_, hD]
  intro t ht
  have hlogD := logsIn_fromBytesWithHash (γ := Bytes ⊕ KeccakState) Sum.inl hw []
  obtain ⟨d, hd, hdP⟩ := hlogD
  have e : queriesWith (callAnswer toPermutationCalls σ) D = d := by
    unfold queriesWith
    rw [simulateQ_fromBytesWithHash, implH_logImpl_callAnswer, hd, List.nil_append]
  rw [e] at ht
  obtain ⟨phase, hphase, path, hpath, level, hlevel, rfl⟩ := hdP t ht
  have hmem := hlog' phase hphase path hpath level hlevel
  obtain ⟨t', ht', hx⟩ := List.mem_flatMap.1 hmem
  rcases t' with x | s'
  · simp only [hashInput, List.mem_singleton] at hx
    subst hx
    exact hrec _ ht'
  · simp [hashInput] at hx

end LeanVM.Wire

end
