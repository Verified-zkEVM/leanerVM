/-
  LeanVM.E2E.Complete.Model

  What the guest's completeness needs of the hash its `BLAKE2S` instructions compute: a
  functional semantics of the rows, an answered hash of byte strings, and for every answered
  string the rows of its standard chain; the deployed model, BLAKE2s itself, and the honest
  table's model of T6-det.
-/

module

public import LeanVM.E2E.Complete.Table

/-!
# Completeness models

The guest's soundness over a hash (W2, `Guest/Value/HashModel.lean`) *reads* digests off checked
rows: a chain of checked rows from the IV is a prefix, and its last row gives the answered hash.
Its completeness (T6-det, `docs/roadmap/t6-completeness.md` L2) *builds* rows: for every string
the node's checks hash, the rows of its standard chain must check, with the cells after each
whole block (`st`) and the answered digest at the end. A `CompModel` states this:

* `sem`, functional (`Functional`, the guest's compiled code shares equal compressions) and of
  canonical cells;
* `H : Bytes → Option Digest`, the answered hash (deployed: every string, by BLAKE2s-256);
* `st p`: the chaining-value cells after the whole blocks `p`, the IV's after none;
* `step`: block `i` of an answered string checks from `st` of its first `i` blocks to `st` of its
  first `i + 1`; `final`: its last block checks from `st` of its whole blocks to the answer.

`CompModel.deployed`: the compression function, `st p` the digest of `absorbBlocks` (the deployed
completeness's `chainRun`); `CompModel.chain I H`: the honest table's semantics `chainSem I H`
(`E2E/Complete/Table.lean`), every string of `D` answered by `H`, `st` the codes of the prefixes.
A guest completeness proved over a `CompModel` is the deployed one at `deployed`, and gives an
execution whose rows V_I's table check accepts at `chain`.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.Value LeanVM.Protocol.Verifier LeanVM.Protocol.Compile

@[expose] public section

/-- **A model of the guest's hash, for completeness.** -/
structure CompModel where
  /-- The relation `BLAKE2S` checks. -/
  sem : BlakeSem
  /-- A row's inputs determine its output. -/
  functional : Functional sem
  /-- A checked row's cells are canonical. -/
  canonical : ∀ {m : Fin 4 → E} {cv0 cv1 out0 out1 md : E}, sem.check m cv0 cv1 out0 out1 md →
    CanonicalCells m cv0 cv1 out0 out1 md
  /-- The answered hash. -/
  H : Bytes → Option Digest
  /-- The chaining-value cells after whole blocks. -/
  st : List (List UInt8) → E × E
  /-- After none, the IV. -/
  st_nil : st [] = ivCells
  /-- The cells are canonical. -/
  st_canonical : ∀ p, IsCanonical128 (st p).1 ∧ IsCanonical128 (st p).2
  /-- **A whole block of an answered string checks**, between the cells after the blocks before
  it and after it. -/
  step : ∀ {x : Bytes} {d : Digest}, H x = some d → ∀ {i : ℕ}, i < nBlocks x →
    ∀ {m : Fin 4 → E}, (∀ j, IsCanonical128 (m j)) → blockBytes m = blockAt x i →
    sem.check m (st (prefixAt x i)).1 (st (prefixAt x i)).2
      (st (prefixAt x (i + 1))).1 (st (prefixAt x (i + 1))).2 (metadataCell (64 * (i + 1)) false)
  /-- **The last block of an answered string checks**, from the cells after its whole blocks to
  the answer. -/
  final : ∀ {x : Bytes} {d : Digest}, H x = some d →
    ∀ {m : Fin 4 → E}, (∀ j, IsCanonical128 (m j)) →
    blockBytes m = tailOf x ++ List.replicate (64 - (tailOf x).length) 0 →
    sem.check m (st (prefixAt x (nBlocks x))).1 (st (prefixAt x (nBlocks x))).2
      (digestScalars d).1 (digestScalars d).2 (metadataCell x.length true)

/-! ## The deployed model -/

/-- The compression function's output is a function of its inputs. -/
theorem functional_deployed : Functional blakeDeployed := by
  intro m cv0 cv1 o0 o1 o0' o1' md h h'
  have e : (o0, o1) = (o0', o1') :=
    (pair_eq_digestScalars_iff.mpr ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2⟩).trans
      (pair_eq_digestScalars_iff.mpr ⟨h'.2.2.2.1, h'.2.2.2.2.1, h'.2.2.2.2.2.2⟩).symm
  simpa only [Prod.mk.injEq] using e

/-- The whole blocks of a string have 64 bytes each. -/
theorem length_of_mem_prefixAt {x : Bytes} {b : List UInt8}
    (hb : b ∈ prefixAt x (nBlocks x)) : b.length = 64 := by
  simp only [prefixAt, List.mem_map, List.mem_range] at hb
  obtain ⟨i, hi, rfl⟩ := hb
  exact length_blockAt hi

/-- **The deployed model**: the compression function, every string answered by BLAKE2s-256, the
cells after whole blocks those of `absorbBlocks`. -/
def CompModel.deployed : CompModel where
  sem := blakeDeployed
  functional := functional_deployed
  canonical := canonicalCells_of_compressCells
  H x := some (blake2sBytes x)
  st p := digestScalars (absorbBlocks paramIv 0 p)
  st_nil := rfl
  st_canonical _ := isCanonical128_digestScalars _
  step := by
    intro x d _ i hi m hm hb
    refine (compressCells_iff hm (isCanonical128_metadataCell _ _)).mpr ?_
    rw [unpackMetadata_metadataCell, prefixAt_succ, absorbBlocks_append, hb]
    simp only [length_prefixAt, Nat.zero_add, absorbBlocks, Bool.false_eq_true, ↓reduceIte]
    rw [show 64 * i + 64 = 64 * (i + 1) by ring]
  final := by
    intro x d hd m hm hb
    obtain rfl : d = blake2sBytes x := (Option.some.inj hd).symm
    refine (compressCells_iff hm (isCanonical128_metadataCell _ _)).mpr ?_
    rw [unpackMetadata_metadataCell, hb, blockWords_append_zeros]
    simp only [↓reduceIte]
    have hr' : prefixAt x (nBlocks x) = [] ∨ tailOf x ≠ [] := by
      rcases Nat.eq_zero_or_pos x.length with h0 | h0
      · left
        have : nBlocks x = 0 := by unfold nBlocks; omega
        rw [this]; rfl
      · right
        intro e
        have := congrArg List.length e
        rw [length_tailOf] at this
        unfold nBlocks at this
        simp only [List.length_nil] at this
        omega
    have hsplit := blake2sBytes_split (prefixAt x (nBlocks x))
      (fun b hb ↦ length_of_mem_prefixAt hb) (tailOf x) (length_tailOf_le x) hr'
    rw [← eq_flatten_tailOf x, length_prefixAt, length_tailOf,
      show 64 * nBlocks x + (x.length - 64 * nBlocks x) = x.length by unfold nBlocks; omega]
      at hsplit
    rw [hsplit]

/-! ## The honest table's model -/

/-- The answers of `H` on the strings `D`. -/
noncomputable def answeredOn (D : List Bytes) (H : Bytes → Digest) (x : Bytes) : Option Digest :=
  open Classical in if x ∈ D then some (H x) else none

/-- An answer on `D` is `H` on a string of `D`. -/
theorem answeredOn_some {D : List Bytes} {H : Bytes → Digest} {x : Bytes} {d : Digest}
    (h : answeredOn D H x = some d) : x ∈ D ∧ d = H x := by
  unfold answeredOn at h
  split at h
  · exact ⟨‹_›, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- **The honest table's model** of T6-det: the semantics of the chain rows of the strings `D`
under the codes `I`, every string of `D` answered by `H`. -/
noncomputable def CompModel.chain {D : List Bytes} (I : Intermediates D) (H : Bytes → Digest) :
    CompModel where
  sem := chainSem I H
  functional := chainSem_functional
  canonical h := h.1
  H := answeredOn D H
  st := I.st
  st_nil := Intermediates.st_nil
  st_canonical _ := Intermediates.isCanonical_st _
  step hd _ hi _ hm hb := chainSem_step (answeredOn_some hd).1 hi hm hb
  final hd _ hm hb := by
    obtain ⟨hx, rfl⟩ := answeredOn_some hd
    exact chainSem_final hx hm hb

/-- **The honest model's executions pass V_I's table check**: every row V_I lists, under the
Flock-blind semantics, of an execution valid under the honest table's semantics, is a canonical
chain row, so `tableOKWith` with `H` accepts them. -/
theorem tableOKWith_of_validB {D : List Bytes} {I : Intermediates D} {H : Bytes → Digest}
    {prog : Program} {input : PublicInput} {t : Trace prog}
    (hv : ValidExecutionB (CompModel.chain I H).sem prog input t) :
    tableOKWith (m := Id) (fun x ↦ (pure (H x) : Id Digest)) (t.blakeRows blakeFree) = true :=
  tableOKWith_chainRows fun b hb ↦ chainSem_row.mp (blakeRows_of_validB chainSem_le_free hv b hb)

/-- The honest model's executions are the ones V_I re-runs. -/
theorem haltingRunB_of_validChain {D : List Bytes} {I : Intermediates D} {H : Bytes → Digest}
    {prog : Program} {input : PublicInput} {t : Trace prog}
    (hv : ValidExecutionB (CompModel.chain I H).sem prog input t) :
    haltingRunB blakeFree prog t.image = some t :=
  haltingRunB_of_validB chainSem_le_free hv

end
end LeanVM.E2E.Complete
