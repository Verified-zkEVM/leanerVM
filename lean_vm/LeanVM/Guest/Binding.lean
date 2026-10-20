/-
  LeanVM.Guest.Binding

  The statement's digest binds the seed and the statement, unless one of five named pairs of
  byte strings is a BLAKE2s collision.
-/

module

public import LeanVM.Spec.Node

/-!
# The statement's digest binds

`statementDigest seed s` hashes the seed, the signer set's digest, the DA list's digest and the
deferred claim's cells; the signer set's digest hashes the two claim lists' digests. Every
encoding on the way is injective at a fixed width (`digestBytes`, 32 bytes; `claimBytes`, 64;
`eBytes`, 24; a DA claim, 64), and the zero fill depends only on the length. So two statements
with the same digest are equal, or one of the five hashes on the way was given two different
inputs with the same output: the pairs `collisionCandidates` lists (`statementDigest_binds`).

The deferred claim's cells carry no lengths: `[x] ++ [y, …]` and `[x, y] ++ […]` are the same
cells. The binding needs the two deferred claims' points to have the same lengths, which
`DeferredClaim.Shaped` gives at one bytecode (`statementDigest_binds_of_length` takes the
lengths themselves). Nothing else is assumed of the statements.

A consumer compares the public input's digest with that of its own statement under the deployed
seed, while the guest's execution decodes a seed and a statement of that digest
(`decoded_binds`, and `decoded_binds_of_nodeRel` for a decoded statement the guest establishes
and an expected one whose deferred claim holds).
-/

namespace LeanVM.Guest.Binding

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Node

@[expose] public section

/-! ## The bytes each digest hashes -/

/-- The deferred claim's cells, an odd count paired with a zero cell. -/
def paddedCells (c : DeferredClaim) : List E :=
  c.cells ++ if c.cells.length % 2 = 1 then [0] else []

/-- The bytes of a statement under `seed`, before the zero fill. -/
def statementBytes (seed : Digest) (s : NodeStatement) : List UInt8 :=
  digestBytes seed ++ digestBytes (signersDigest s.claims.xmss s.claims.sphincs) ++
    digestBytes (daListDigest s.claims.da) ++ (paddedCells s.defer).flatMap eBytes

/-- The bytes `statementDigest seed s` hashes: zero-filled to whole 64-byte blocks. -/
def statementPreimage (seed : Digest) (s : NodeStatement) : List UInt8 :=
  statementBytes seed s ++
    List.replicate ((64 - (statementBytes seed s).length % 64) % 64) 0

/-- The bytes `signersDigest xmss sphincs` hashes. -/
def signersPreimage (xmss : List XmssClaim) (sphincs : List SphincsClaim) : List UInt8 :=
  digestBytes (xmssListDigest xmss) ++ digestBytes (sphincsListDigest sphincs)

/-- The bytes `xmssListDigest claims` hashes. -/
def xmssPreimage (claims : List XmssClaim) : List UInt8 :=
  claims.flatMap fun c ↦ claimBytes c.1.root c.1.parameter c.2

/-- The bytes `sphincsListDigest claims` hashes. -/
def sphincsPreimage (claims : List SphincsClaim) : List UInt8 :=
  claims.flatMap fun c ↦ claimBytes c.1.root c.1.parameter c.2

/-- The bytes `daListDigest claims` hashes. -/
def daPreimage (claims : List DaClaim) : List UInt8 :=
  claims.flatMap fun c ↦ digestBytes c.1 ++ digestBytes c.2

theorem statementDigest_eq (seed : Digest) (s : NodeStatement) :
    statementDigest seed s = blake2sBytes (statementPreimage seed s) := rfl

theorem signersDigest_eq (xmss : List XmssClaim) (sphincs : List SphincsClaim) :
    signersDigest xmss sphincs = blake2sBytes (signersPreimage xmss sphincs) := rfl

theorem xmssListDigest_eq (claims : List XmssClaim) :
    xmssListDigest claims = blake2sBytes (xmssPreimage claims) := rfl

theorem sphincsListDigest_eq (claims : List SphincsClaim) :
    sphincsListDigest claims = blake2sBytes (sphincsPreimage claims) := rfl

theorem daListDigest_eq (claims : List DaClaim) :
    daListDigest claims = blake2sBytes (daPreimage claims) := rfl

/-- **The candidate collisions** of two statements' digests: the pairs of inputs of the five
hashes the digests compute, the outer one, the signer set's, the two claim lists' and the DA
list's. -/
def collisionCandidates (seed : Digest) (s : NodeStatement) (seed' : Digest)
    (s' : NodeStatement) : List (List UInt8 × List UInt8) :=
  [(statementPreimage seed s, statementPreimage seed' s'),
    (signersPreimage s.claims.xmss s.claims.sphincs,
      signersPreimage s'.claims.xmss s'.claims.sphincs),
    (xmssPreimage s.claims.xmss, xmssPreimage s'.claims.xmss),
    (sphincsPreimage s.claims.sphincs, sphincsPreimage s'.claims.sphincs),
    (daPreimage s.claims.da, daPreimage s'.claims.da)]

/-! ## Fixed-width encodings are injective -/

theorem length_flatMap_const {α β : Type} {f : α → List β} {n : ℕ}
    (hlen : ∀ a, (f a).length = n) : ∀ l : List α, (l.flatMap f).length = n * l.length
  | [] => by simp
  | a :: l => by
    rw [List.flatMap_cons, List.length_append, hlen, length_flatMap_const hlen l,
      List.length_cons, Nat.mul_succ, Nat.add_comm]

/-- A concatenation of encodings of one positive width is injective. -/
theorem flatMap_inj {α β : Type} {f : α → List β} {n : ℕ} (hn : 0 < n)
    (hlen : ∀ a, (f a).length = n) (hf : ∀ a b, f a = f b → a = b) :
    ∀ {l l' : List α}, l.flatMap f = l'.flatMap f → l = l'
  | [], [], _ => rfl
  | [], b :: l', h => by
    have := congrArg List.length h
    rw [List.flatMap_nil, List.flatMap_cons, List.length_append, hlen] at this
    simp at this
    omega
  | a :: l, [], h => by
    have := congrArg List.length h
    rw [List.flatMap_nil, List.flatMap_cons, List.length_append, hlen] at this
    simp at this
    omega
  | a :: l, b :: l', h => by
    rw [List.flatMap_cons, List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by rw [hlen, hlen])
    rw [hf a b h1, flatMap_inj hn hlen hf h2]

theorem wordBytes_inj {w w' : UInt32} (h : wordBytes w = wordBytes w') : w = w' := by
  simp only [wordBytes, List.cons.injEq, and_true] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  have e : ∀ x y : UInt8, x = y → x.toNat = y.toNat := fun _ _ h ↦ h ▸ rfl
  have e0 := e _ _ h0
  have e1 := e _ _ h1
  have e2 := e _ _ h2
  have e3 := e _ _ h3
  simp only [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow] at e0 e1 e2 e3
  have hw := w.toNat_lt
  have hw' := w'.toNat_lt
  apply UInt32.toNat_inj.mp
  norm_num at e0 e1 e2 e3 hw hw'
  omega

theorem length_digestBytes (d : Digest) : (digestBytes d).length = 32 := by
  rw [digestBytes, length_flatMap_const (n := 4) (fun _ ↦ rfl), Vector.length_toList]

theorem digestBytes_inj {d d' : Digest} (h : digestBytes d = digestBytes d') : d = d' :=
  Vector.toList_inj.mp (flatMap_inj (n := 4) (by decide) (fun _ ↦ rfl)
    (fun _ _ ↦ wordBytes_inj) h)

theorem length_kBytes (a : K) : (kBytes a).length = 8 := rfl

theorem kBytes_inj {a b : K} (h : kBytes a = kBytes b) : a = b := by
  obtain ⟨hl, hh⟩ := List.append_inj h rfl
  have l := congrArg UInt32.toBitVec (wordBytes_inj hl)
  have u := congrArg UInt32.toBitVec (wordBytes_inj hh)
  simp only [lowWord, highWord] at l u
  apply BF64.toBitVec_injective
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hi32 : i < 32
  · have := congrArg (·.getLsbD i) l
    simpa [BitVec.getLsbD_extractLsb', hi32] using this
  · have := congrArg (·.getLsbD (i - 32)) u
    have hi' : 32 + (i - 32) = i := by omega
    simpa [BitVec.getLsbD_extractLsb', hi', show i - 32 < 32 by omega] using this

theorem length_eBytes (x : E) : (eBytes x).length = 24 := rfl

theorem eBytes_inj {x y : E} (h : eBytes x = eBytes y) : x = y := by
  obtain ⟨h12, h3⟩ := List.append_inj h rfl
  obtain ⟨h1, h2⟩ := List.append_inj h12 rfl
  apply CompPoly.Extension.Ext.ext
  rintro ⟨i, hi⟩
  match i, hi with
  | 0, _ => exact kBytes_inj h1
  | 1, _ => exact kBytes_inj h2
  | 2, _ => exact kBytes_inj h3
  | n + 3, hi => exact absurd hi (by simp)

theorem length_bytesLE (n : ℕ) (v : BitVec (8 * n)) : (LeanXmss.bytesLE n v).length = n :=
  List.length_ofFn

theorem bytesLE_inj {n : ℕ} {v v' : BitVec (8 * n)}
    (h : LeanXmss.bytesLE n v = LeanXmss.bytesLE n v') : v = v' := by
  have hf := List.ofFn_injective h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have e := congrArg (fun f ↦ (f ⟨j / 8, by omega⟩ : UInt8).toBitVec.getLsbD (j % 8)) hf
  have hj' : 8 * (j / 8) + j % 8 = j := by omega
  simpa [BitVec.getLsbD_extractLsb', hj', Nat.mod_lt] using e

theorem claimBytes_inj {r p r' p' : BitVec 128} {m m' : BitVec 256}
    (h : claimBytes r p m = claimBytes r' p' m') : r = r' ∧ p = p' ∧ m = m' := by
  obtain ⟨h12, h3⟩ := List.append_inj h (by simp [bytes16, length_bytesLE])
  obtain ⟨h1, h2⟩ := List.append_inj h12 (by simp [bytes16, length_bytesLE])
  exact ⟨bytesLE_inj (n := 16) h1, bytesLE_inj (n := 16) h2, bytesLE_inj (n := 32) h3⟩

theorem length_claimBytes (r p : BitVec 128) (m : BitVec 256) :
    (claimBytes r p m).length = 64 := by
  simp [claimBytes, bytes16, length_bytesLE]

theorem xmssPreimage_inj {l l' : List XmssClaim} (h : xmssPreimage l = xmssPreimage l') :
    l = l' :=
  flatMap_inj (n := 64) (by decide) (fun _ ↦ length_claimBytes _ _ _)
    (fun ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ h ↦ by
      obtain ⟨rfl, rfl, rfl⟩ := claimBytes_inj h
      rfl) h

theorem sphincsPreimage_inj {l l' : List SphincsClaim}
    (h : sphincsPreimage l = sphincsPreimage l') : l = l' :=
  flatMap_inj (n := 64) (by decide) (fun _ ↦ length_claimBytes _ _ _)
    (fun ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ h ↦ by
      obtain ⟨rfl, rfl, rfl⟩ := claimBytes_inj h
      rfl) h

theorem daPreimage_inj {l l' : List DaClaim} (h : daPreimage l = daPreimage l') : l = l' :=
  flatMap_inj (n := 64) (by decide)
    (fun _ ↦ by rw [List.length_append, length_digestBytes, length_digestBytes])
    (fun _ _ h ↦ by
      obtain ⟨h1, h2⟩ := List.append_inj h (by rw [length_digestBytes, length_digestBytes])
      exact Prod.ext (digestBytes_inj h1) (digestBytes_inj h2)) h

theorem signersPreimage_inj {x x' : List XmssClaim} {p p' : List SphincsClaim}
    (h : signersPreimage x p = signersPreimage x' p') :
    xmssListDigest x = xmssListDigest x' ∧ sphincsListDigest p = sphincsListDigest p' := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by rw [length_digestBytes, length_digestBytes])
  exact ⟨digestBytes_inj h1, digestBytes_inj h2⟩

/-- Two deferred claims with the same cells and points of the same lengths are equal. -/
theorem cells_inj {c c' : DeferredClaim}
    (hb : c.bytecodePoint.length = c'.bytecodePoint.length)
    (hm : c.matrixPoint.length = c'.matrixPoint.length) (h : c.cells = c'.cells) : c = c' := by
  obtain ⟨b, v, m, x, y⟩ := c
  obtain ⟨b', v', m', x', y'⟩ := c'
  simp only [DeferredClaim.cells] at h hb hm
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [hb, hm])
  obtain ⟨h3, h4⟩ := List.append_inj h1 (by simp [hb])
  obtain ⟨h5, h6⟩ := List.append_inj h3 hb
  simp only [List.cons.injEq, and_true] at h2 h6
  obtain ⟨rfl, rfl⟩ := h2
  subst h4 h5 h6
  rfl

theorem length_paddedCells (c : DeferredClaim) :
    (paddedCells c).length = c.cells.length + if c.cells.length % 2 = 1 then 1 else 0 := by
  unfold paddedCells
  split <;> simp

theorem length_statementBytes (seed : Digest) (s : NodeStatement) :
    (statementBytes seed s).length = 96 + 24 * (paddedCells s.defer).length := by
  simp only [statementBytes, List.length_append, length_digestBytes,
    length_flatMap_const length_eBytes]

/-- The outer preimage determines the seed, the two nested digests and, at fixed point lengths,
the deferred claim. -/
theorem statementPreimage_inj {seed seed' : Digest} {s s' : NodeStatement}
    (hb : s.defer.bytecodePoint.length = s'.defer.bytecodePoint.length)
    (hm : s.defer.matrixPoint.length = s'.defer.matrixPoint.length)
    (h : statementPreimage seed s = statementPreimage seed' s') :
    seed = seed' ∧
      signersDigest s.claims.xmss s.claims.sphincs =
        signersDigest s'.claims.xmss s'.claims.sphincs ∧
      daListDigest s.claims.da = daListDigest s'.claims.da ∧ s.defer = s'.defer := by
  have hc : s.defer.cells.length = s'.defer.cells.length := by
    simp [DeferredClaim.cells, hb, hm]
  have hlen : (statementBytes seed s).length = (statementBytes seed' s').length := by
    rw [length_statementBytes, length_statementBytes, length_paddedCells, length_paddedCells, hc]
  obtain ⟨hB, -⟩ := List.append_inj h hlen
  unfold statementBytes at hB
  obtain ⟨h123, h4⟩ := List.append_inj hB (by simp [length_digestBytes])
  obtain ⟨h12, h3⟩ := List.append_inj h123 (by simp [length_digestBytes])
  obtain ⟨h1, h2⟩ := List.append_inj h12 (by simp [length_digestBytes])
  have hp := flatMap_inj (n := 24) (by decide) length_eBytes (fun _ _ ↦ eBytes_inj) h4
  unfold paddedCells at hp
  obtain ⟨hcells, -⟩ := List.append_inj hp hc
  exact ⟨digestBytes_inj h1, digestBytes_inj h2, digestBytes_inj h3, cells_inj hb hm hcells⟩

/-! ## The binding -/

/-- **The statement's digest binds**, at point lengths equal on both sides: the seeds and the
statements are equal, or a candidate pair is a BLAKE2s collision. -/
theorem statementDigest_binds_of_length {seed seed' : Digest} {s s' : NodeStatement}
    (hb : s.defer.bytecodePoint.length = s'.defer.bytecodePoint.length)
    (hm : s.defer.matrixPoint.length = s'.defer.matrixPoint.length)
    (h : statementDigest seed s = statementDigest seed' s') :
    (seed = seed' ∧ s = s') ∨ ∃ p ∈ collisionCandidates seed s seed' s',
      p.1 ≠ p.2 ∧ blake2sBytes p.1 = blake2sBytes p.2 := by
  by_cases h0 : statementPreimage seed s = statementPreimage seed' s'
  swap
  · exact Or.inr ⟨(statementPreimage seed s, statementPreimage seed' s'),
      by simp [collisionCandidates], h0, h⟩
  obtain ⟨hseed, hsig, hda, hdef⟩ := statementPreimage_inj hb hm h0
  by_cases h1 : signersPreimage s.claims.xmss s.claims.sphincs =
      signersPreimage s'.claims.xmss s'.claims.sphincs
  swap
  · exact Or.inr ⟨(signersPreimage s.claims.xmss s.claims.sphincs,
      signersPreimage s'.claims.xmss s'.claims.sphincs), by simp [collisionCandidates], h1, hsig⟩
  obtain ⟨hx, hp⟩ := signersPreimage_inj h1
  by_cases h2 : xmssPreimage s.claims.xmss = xmssPreimage s'.claims.xmss
  swap
  · exact Or.inr ⟨(xmssPreimage s.claims.xmss, xmssPreimage s'.claims.xmss),
      by simp [collisionCandidates], h2, hx⟩
  by_cases h3 : sphincsPreimage s.claims.sphincs = sphincsPreimage s'.claims.sphincs
  swap
  · exact Or.inr ⟨(sphincsPreimage s.claims.sphincs, sphincsPreimage s'.claims.sphincs),
      by simp [collisionCandidates], h3, hp⟩
  by_cases h4 : daPreimage s.claims.da = daPreimage s'.claims.da
  swap
  · exact Or.inr ⟨(daPreimage s.claims.da, daPreimage s'.claims.da),
      by simp [collisionCandidates], h4, hda⟩
  left
  refine ⟨hseed, ?_⟩
  have e1 := xmssPreimage_inj h2
  have e2 := sphincsPreimage_inj h3
  have e3 := daPreimage_inj h4
  obtain ⟨⟨x, p, d⟩, c⟩ := s
  obtain ⟨⟨x', p', d'⟩, c'⟩ := s'
  dsimp only at e1 e2 e3 hdef
  subst e1 e2 e3 hdef
  rfl

/-- **The statement's digest binds the seed and the statement**, for two statements whose
deferred claims have the shape of one bytecode: the seeds and the statements are equal, or one
of the candidate pairs is a BLAKE2s collision. The shape fixes the lengths of the deferred
claim's two points, which its cells do not record. -/
theorem statementDigest_binds {b : List K} {seed seed' : Digest} {s s' : NodeStatement}
    (hs : s.defer.Shaped b) (hs' : s'.defer.Shaped b)
    (h : statementDigest seed s = statementDigest seed' s') :
    (seed = seed' ∧ s = s') ∨ ∃ p ∈ collisionCandidates seed s seed' s',
      p.1 ≠ p.2 ∧ blake2sBytes p.1 = blake2sBytes p.2 :=
  statementDigest_binds_of_length (hs.1.trans hs'.1.symm) (hs.2.trans hs'.2.symm) h

/-! ## What a consumer learns -/

/-- **A consumer learns the decoded statement**: it checks that the public input's digest is its
statement `s₀`'s under the deployed seed `iv`; an execution decodes a seed and a statement `s` of
the same digest. Then the decoded seed is `iv` and `s` is `s₀`, or a candidate pair is a BLAKE2s
collision. -/
theorem decoded_binds {b : List K} {iv seed : Digest} {s₀ s : NodeStatement}
    {input : PublicInput} (hs₀ : s₀.defer.Shaped b) (hs : s.defer.Shaped b)
    (hpub : publicDigest input = statementDigest iv s₀)
    (hdec : statementDigest seed s = publicDigest input) :
    (seed = iv ∧ s = s₀) ∨ ∃ p ∈ collisionCandidates seed s iv s₀,
      p.1 ≠ p.2 ∧ blake2sBytes p.1 = blake2sBytes p.2 :=
  statementDigest_binds hs hs₀ (hdec.trans hpub)

/-- `decoded_binds` with the shapes from where they come: the decoded statement is one the guest
`bytecode` establishes (`NodeRel`), and the consumer's deferred claim holds of `bytecode`, as the
outer verifier checks (`verifyAggregate`). -/
theorem decoded_binds_of_nodeRel {bytecode : List K} {iv seed : Digest} {s₀ s : NodeStatement}
    {w : NodeWitness} {input : PublicInput} (hs₀ : s₀.defer.Holds bytecode)
    (hrel : NodeRel bytecode seed s w)
    (hpub : publicDigest input = statementDigest iv s₀)
    (hdec : statementDigest seed s = publicDigest input) :
    (seed = iv ∧ s = s₀) ∨ ∃ p ∈ collisionCandidates seed s iv s₀,
      p.1 ≠ p.2 ∧ blake2sBytes p.1 = blake2sBytes p.2 :=
  decoded_binds hs₀.1 hrel.1 hpub hdec

end
end LeanVM.Guest.Binding
