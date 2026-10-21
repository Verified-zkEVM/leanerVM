/-
  LeanVM.Guest.B1.Sig.Model.Hashing

  The signature verifiers' compressions under a hash model: one final block and two blocks under
  the IV as answered hashes of byte strings (the forward halves of `compress_final_iff` and
  `compress_two_iff`), the answered hash of cells, and the statement-level vocabulary the model
  proofs of `Sig` share.
-/

module

public import LeanVM.Guest.B1.Sig.Hashing
public import LeanVM.Guest.Value.ModelChain
public import LeanVM.Guest.CoreB
public import LeanVM.Spec.NodeWith

/-!
# Compressions as answered hashes

`Hashing.lean` reads the guest's `BLAKE2S` rows as `hb`, BLAKE2s of bytes. Under a hash model
(`Value/HashModel.lean`) a row only gives an *answered* hash: `hbWith H bs` is the two cells of
the digest `H` answers for `bs`, `none` where it does not answer, and `hcellWith H cs` the same
over the cells' bytes. At the deployed hash they are `some (hb bs)` and `some (hcell cs)`
(`hbWith_deployed`, `hcellWith_deployed`).

* `compress_final_model`, `compress4_model`, `compress3_model`: one final block under the IV
  (`compress_final_iff.mp`, `compress4_iff.mp`, `compress3_iff.mp`);
* `compress_two_model`: a non-final block under the IV, then a final one
  (`compress_two_iff.mp`); the chaining value between them is a prefix of the first block's
  bytes, never a named digest (`hmid` has no model counterpart);
* `holdsListB_free`: a statement list with no `BLAKE2S` atom and no call holds under every
  semantics exactly when it holds under the deployed one, so the hash-free blocks of the
  templates keep their deployed lemmas;
* `truncateHash_digestBits`: a digest's truncation, as the schemes read it, is its first cell.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-! ## Answered hashes -/

/-- The answered hash of bytes, as its two cells: `none` where `H` does not answer. -/
def hbWith (H : List UInt8 → Option Digest) (bs : List UInt8) : Option (E × E) :=
  (H bs).map digestScalars

/-- The answered hash of the bytes of cells. -/
def hcellWith (H : List UInt8 → Option Digest) (cs : List E) : Option (E × E) :=
  hbWith H (cs.flatMap cellBytes)

theorem hbWith_deployed (bs : List UInt8) : hbWith HashModel.deployed.H bs = some (hb bs) := rfl

theorem hcellWith_deployed (cs : List E) : hcellWith HashModel.deployed.H cs = some (hcell cs) := rfl

theorem hbWith_some {H : List UInt8 → Option Digest} {bs : List UInt8} {o : E × E} :
    hbWith H bs = some o ↔ ∃ d, H bs = some d ∧ o = digestScalars d := by
  unfold hbWith
  rw [Option.map_eq_some_iff]
  exact exists_congr fun d => and_congr Iff.rfl eq_comm

theorem hbWith_of {H : List UInt8 → Option Digest} {bs : List UInt8} {d : Digest} {o : E × E}
    (hd : H bs = some d) (ho : o = digestScalars d) : hbWith H bs = some o :=
  hbWith_some.mpr ⟨d, hd, ho⟩

/-- An answered hash's cells are canonical. -/
theorem isCanonical128_hbWith {H : List UInt8 → Option Digest} {bs : List UInt8} {o : E × E}
    (h : hbWith H bs = some o) : IsCanonical128 o.1 ∧ IsCanonical128 o.2 := by
  obtain ⟨d, -, rfl⟩ := hbWith_some.mp h
  exact isCanonical128_digestScalars d

theorem isCanonical128_hcellWith {H : List UInt8 → Option Digest} {cs : List E} {o : E × E}
    (h : hcellWith H cs = some o) : IsCanonical128 o.1 ∧ IsCanonical128 o.2 :=
  isCanonical128_hbWith h

/-! ## One and two blocks -/

theorem iv0_eq : iv0 = Value.ivCells.1 := by rw [ivCells_eq_iv]

theorem iv1_eq : iv1 = Value.ivCells.2 := by rw [ivCells_eq_iv]

variable {M : HashModel}

/-- **One final compression under the IV, under a model** (`compress_final_iff.mp`): the block's
cells are canonical and the output is the answered hash of its data bytes `r`. -/
theorem compress_final_model {m : Fin 4 → E} {o0 o1 : E} {r : List UInt8}
    (hr : blockBytes m = r ++ List.replicate (64 - r.length) 0) (hlen : r.length ≤ 64)
    (h : M.sem.check m iv0 iv1 o0 o1 (mdw r.length true)) :
    (∀ i, IsCanonical128 (m i)) ∧ hbWith M.H r = some (o0, o1) := by
  refine ⟨(M.canonical h).1, ?_⟩
  rw [iv0_eq, iv1_eq, mdw_eq] at h
  obtain ⟨d, hd, ho⟩ := M.final (bs := []) (st := Value.ivCells) M.prefix_nil hlen (Or.inl rfl) hr
    (by simpa using h)
  exact hbWith_of (by simpa using hd) ho

/-- **Two compressions under a model** (`compress_two_iff.mp`): a non-final block under the IV,
then a final one with data bytes `r`. The cells are canonical, the chaining value between them is
the prefix of the first block's bytes, and the output is the answered hash of all the bytes. -/
theorem compress_two_model {b0 b1 : Fin 4 → E} {x0 x1 o0 o1 : E} {r : List UInt8}
    (hr : blockBytes b1 = r ++ List.replicate (64 - r.length) 0) (hlen : r.length ≤ 64)
    (hpos : 1 ≤ r.length) (h0 : M.sem.check b0 iv0 iv1 x0 x1 (mdw 64 false))
    (h1 : M.sem.check b1 x0 x1 o0 o1 (mdw (64 + r.length) true)) :
    (∀ i, IsCanonical128 (b0 i)) ∧ (∀ i, IsCanonical128 (b1 i)) ∧ M.Prefix [blockBytes b0] (x0, x1) ∧
      hbWith M.H (blockBytes b0 ++ r) = some (o0, o1) := by
  refine ⟨(M.canonical h0).1, (M.canonical h1).1, ?_⟩
  rw [iv0_eq, iv1_eq, mdw_eq] at h0
  rw [mdw_eq] at h1
  have hp : M.Prefix [blockBytes b0] (x0, x1) :=
    M.prefix_step (bs := []) (st := Value.ivCells) (st' := (x0, x1)) M.prefix_nil (by simpa using h0)
  refine ⟨hp, ?_⟩
  have hne : r ≠ [] := fun he => by rw [he] at hpos; simp at hpos
  obtain ⟨d, hd, ho⟩ := M.final (bs := [blockBytes b0]) (st := (x0, x1)) hp hlen (Or.inr hne) hr
    (by simpa using h1)
  exact hbWith_of (by simpa using hd) ho

/-- One final block of four cells under the IV, under a model (`compress4_iff.mp`). -/
theorem compress4_model {a b c d o0 o1 : E}
    (h : M.sem.check ![a, b, c, d] iv0 iv1 o0 o1 (mdw 64 true)) :
    (IsCanonical128 a ∧ IsCanonical128 b ∧ IsCanonical128 c ∧ IsCanonical128 d) ∧
      hcellWith M.H [a, b, c, d] = some (o0, o1) := by
  have hl : ([a, b, c, d].flatMap cellBytes).length = 64 := by
    rw [length_flatMap_cellBytes']; rfl
  obtain ⟨hc, ho⟩ := compress_final_model (M := M) (blockBytes_four' a b c d) (by rw [hl])
    (by rw [hl]; exact h)
  exact ⟨fin4_canonical.mp hc, ho⟩

/-- One final block of three cells and a zero under the IV, under a model
(`compress3_iff.mp`). -/
theorem compress3_model {a b c o0 o1 : E}
    (h : M.sem.check ![a, b, c, 0] iv0 iv1 o0 o1 (mdw 48 true)) :
    (IsCanonical128 a ∧ IsCanonical128 b ∧ IsCanonical128 c) ∧
      hcellWith M.H [a, b, c] = some (o0, o1) := by
  have hl : ([a, b, c].flatMap cellBytes).length = 48 := by
    rw [length_flatMap_cellBytes']; rfl
  obtain ⟨hc, ho⟩ := compress_final_model (M := M) (blockBytes_three a b c) (by rw [hl]; omega)
    (by rw [hl]; exact h)
  obtain ⟨h1, h2, h3, -⟩ := fin4_canonical.mp hc
  exact ⟨⟨h1, h2, h3⟩, ho⟩

/-! ## Statements under a semantics -/

variable {S : BlakeSem} {C : CallRel} {rd : Reader}

@[simp] theorem holdsListB_cons_atom (a : Atom) (ss : List Stmt) (next : Prop) (kret : List E → Prop)
    (σ : Val) :
    Stmt.HoldsListB S C rd σ (.atom a :: ss) next kret ↔
      a.HoldsB S rd σ ∧ Stmt.HoldsListB S C rd σ ss next kret :=
  Iff.rfl

@[simp] theorem holdsListB_nil (next : Prop) (kret : List E → Prop) (σ : Val) :
    Stmt.HoldsListB S C rd σ [] next kret ↔ next :=
  Iff.rfl

/-- **A block with no `BLAKE2S` atom and no call** holds under any semantics exactly when it holds
under the deployed one. -/
theorem holdsListB_free {ss : List Stmt} (hfree : Stmt.freeInList [] ss = true) (σ : Val)
    (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsListB S C rd σ ss next kret ↔ Stmt.HoldsList C rd σ ss next kret := by
  rw [holdsListB_freeIn (S' := blakeDeployed) (C' := C) (fun f hf => by simp at hf) ss hfree,
    holdsListB_deployed]

/-! ## Truncation -/

theorem digestBits_toNat (d : Digest) :
    (Node.digestBits d).toNat = cellNat (digestScalars d).1 + 2 ^ 128 * cellNat (digestScalars d).2 := by
  have h0 := cellNat_lt (digestScalars d).1
  have h1 := cellNat_lt (digestScalars d).2
  have e : (digestBytes d).foldr (fun b acc ↦ b.toNat + 256 * acc) 0 = leNat (digestBytes d) := rfl
  rw [Node.digestBits, BitVec.toNat_ofNat, e, leNat_digestBytes, Nat.mod_eq_of_lt (by omega)]

/-- **A digest's truncation is its first cell.** -/
theorem truncateHash_digestBits (d : Digest) :
    LeanXmss.truncateHash (Node.digestBits d) = cellVal (digestScalars d).1 := by
  apply BitVec.eq_of_toNat_eq
  have h : (LeanXmss.truncateHash (Node.digestBits d)).toNat = (Node.digestBits d).toNat % 2 ^ 128 := by
    show ((Node.digestBits d).toNat >>> 0) % 2 ^ 128 = _
    rw [Nat.shiftRight_zero]
  have h0 := cellNat_lt (digestScalars d).1
  rw [h, digestBits_toNat, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
  exact (toNat_cellVal _).symm

theorem sphincs_truncateHash_digestBits (d : Digest) :
    Sphincs.truncateHash (Node.digestBits d) = cellVal (digestScalars d).1 :=
  truncateHash_digestBits d

end
end LeanVM.Guest.B1.Sig
