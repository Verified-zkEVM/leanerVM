/-
  LeanVM.Guest.Value.HashModel

  What the guest's proofs know of the hash its `BLAKE2S` instructions compute: a model with the
  machine's `BLAKE2S` relation, an answered hash of byte strings, and the chain laws; the deployed
  model, BLAKE2s itself.
-/

module

public import LeanVM.Guest.Value.Hash
public import LeanVM.Spec.IsaWith

/-!
# Hash models

The guest hashes a byte string as a chain of `BLAKE2S` instructions from the IV
(`Value/Hash.lean`). Its proofs need four facts, and only these: a checked row's cells are
canonical (`canonical`), a chain of whole blocks from the IV is a *prefix* of the bytes it
absorbed (`Prefix`, `prefix_nil`, `prefix_step`), and the last block of a prefix gives the
hash of the whole string, which the model answers (`final`). A `HashModel` states them for a
semantics of `BLAKE2S` (`sem`) and an answered hash of byte strings (`H`, `none` where the model
does not answer):

* `deployed`: the compression function, every string answered by `blake2sBytes`; a prefix's
  chaining value is `absorbBlocks` of its blocks (`Value/Hash.lean`);
* the oracle model of the end-to-end security theorem (`docs/roadmap/e2e-security.md` D4, the
  guest package of §6): the Flock-blind semantics restricted to an execution's rows, `H` a log's
  lookup; there a prefix's chaining value is free and only the table's standard chains are bound
  to the hash.

The model fixes what a proof may use: a guest proof over `HashModel` never reads an intermediate
chaining value, which the oracle model leaves free, and every hash it concludes is one the model
answers, so its conclusions are the `…With` statements at `H` (`NodeRelWith`).
-/

namespace LeanVM.Guest.Value

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash

@[expose] public section

/-- **A model of the guest's hash.** `Prefix bs st`: whole blocks `bs` from the IV, absorbed by
`BLAKE2S` rows of the model, reach the chaining-value cells `st`. -/
structure HashModel where
  /-- The relation `BLAKE2S` checks. -/
  sem : BlakeSem
  /-- A checked row's cells are canonical. -/
  canonical : ∀ {m : Fin 4 → E} {cv0 cv1 out0 out1 md : E}, sem.check m cv0 cv1 out0 out1 md →
    CanonicalCells m cv0 cv1 out0 out1 md
  /-- The answered hash of a byte string. -/
  H : List UInt8 → Option Digest
  /-- A prefix of whole blocks and the chaining value it reaches. -/
  Prefix : List (List UInt8) → E × E → Prop
  /-- The empty prefix is the IV. -/
  prefix_nil : Prefix [] ivCells
  /-- A non-final block, at the counter of the bytes up to it, extends a prefix. -/
  prefix_step : ∀ {bs : List (List UInt8)} {st st' : E × E} {m : Fin 4 → E},
    Prefix bs st →
    sem.check m st.1 st.2 st'.1 st'.2 (metadataCell (64 * (bs.length + 1)) false) →
    Prefix (bs ++ [blockBytes m]) st'
  /-- The last block of a prefix, the rest `r` of the string zero-filled, at the counter of the
  whole string with the last-block flag, gives the hash of the string, which `H` answers. -/
  final : ∀ {bs : List (List UInt8)} {st : E × E} {m : Fin 4 → E} {r : List UInt8}
    {out0 out1 : E},
    Prefix bs st → r.length ≤ 64 → (bs = [] ∨ r ≠ []) →
    blockBytes m = r ++ List.replicate (64 - r.length) 0 →
    sem.check m st.1 st.2 out0 out1 (metadataCell (64 * bs.length + r.length) true) →
    ∃ d, H (bs.flatten ++ r) = some d ∧ (out0, out1) = digestScalars d

/-- The deployed model's prefixes: whole blocks, reaching `absorbBlocks` of them. -/
def DeployedPrefix (bs : List (List UInt8)) (st : E × E) : Prop :=
  (∀ b ∈ bs, b.length = 64) ∧ st = digestScalars (absorbBlocks paramIv 0 bs)

/-- **The deployed model**: the compression function, every string answered by BLAKE2s-256. -/
def HashModel.deployed : HashModel where
  sem := blakeDeployed
  canonical := canonicalCells_of_compressCells
  H x := some (blake2sBytes x)
  Prefix := DeployedPrefix
  prefix_nil := ⟨fun _ h ↦ absurd h List.not_mem_nil, rfl⟩
  prefix_step := by
    intro bs st st' m hp hc
    obtain ⟨hlen, rfl⟩ := hp
    refine ⟨fun b hb ↦ ?_, ?_⟩
    · rcases List.mem_append.mp hb with hb | hb
      · exact hlen b hb
      · rw [List.mem_singleton.mp hb]; exact length_blockBytes m
    · have := compressCells_eq hc
      rw [unpackMetadata_metadataCell] at this
      simp only [Bool.false_eq_true, ↓reduceIte] at this
      rw [absorbBlocks_append, absorbBlocks, absorbBlocks, Nat.zero_add,
        show 64 * bs.length + 64 = 64 * (bs.length + 1) by ring, ← this]
  final := by
    intro bs st m r out0 out1 hp hr hr' hm hc
    obtain ⟨hlen, rfl⟩ := hp
    refine ⟨_, rfl, ?_⟩
    have := compressCells_eq hc
    rw [unpackMetadata_metadataCell, hm, blockWords_append_zeros] at this
    rw [this, blake2sBytes_split bs hlen r hr hr']
    rfl

end
end LeanVM.Guest.Value
