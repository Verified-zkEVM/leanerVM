/-
  LeanVM.Guest.Binding

  The statement's digest binds the seed and the statement, unless one of five named pairs of
  byte strings is a Keccak-256 collision.
-/

module

public import Statement.LeanVmGuest
public import LeanXmss.Scheme
public import Sphincs.Scheme
public import Statement.Fast.Schemes
public import LeanDa.Scheme
public import Statement.Fast.Keccak
public import Statement.Fast.CubicExt
public import Statement.Fast.FieldWords
public import LeanVM.Facts.Verifier
public import LeanVM.Protocol.KeccakHash

/-!
# The statement's digest binds

`statementDigest seed s` hashes the seed, the signer set's digest, the DA list's digest and the
deferred claim's cells, an odd count paired with a zero cell (`statement_digest`,
`crates/rec_aggregation/src/aggregation.rs:344-365` at leanVM `3375f7a13`); the signer set's
digest hashes the two claim lists' digests. Every encoding on the way is injective at a fixed
width (`digestBytes`, 32 bytes; `claimBytes`, 64; `eBytes`, 24; a DA claim, 64). So two statements
with the same digest are equal, or one of the five Keccak-256 hashes on the way was given two
different inputs with the same output: the pairs `collisionCandidates` lists
(`statementDigest_binds`).

The deferred claim's cells carry no lengths: `[x] ++ [y]` and `[x, y] ++ []` are the same cells.
The binding needs the two deferred claims' points to have the same length, which
`DeferredClaim.Shaped` gives at one bytecode (`statementDigest_binds_of_length` takes the length
itself). Nothing else is assumed of the statements.

A consumer compares the public input's digest with that of its own statement under the deployed
seed, while the guest's execution decodes a seed and a statement of that digest
(`decoded_binds`, and `decoded_binds_of_nodeRel` for a decoded statement the guest establishes
and an expected one whose deferred claim holds).
-/

namespace LeanVM.Guest.Binding

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Node

@[expose] public section

/-! ## The bytes each digest hashes (`Statement/LeanVmGuest.lean`) -/

theorem statementDigest_eq (seed : Digest) (s : NodeStatement) :
    statementDigest seed s = keccak256 (statementPreimage seed s) := rfl

theorem signersDigest_eq (xmss : List XmssClaim) (sphincs : List SphincsClaim) :
    signersDigest xmss sphincs = keccak256 (signersPreimage xmss sphincs) := rfl

theorem xmssListDigest_eq (claims : List XmssClaim) :
    xmssListDigest claims = keccak256 (xmssPreimage claims) := rfl

theorem sphincsListDigest_eq (claims : List SphincsClaim) :
    sphincsListDigest claims = keccak256 (sphincsPreimage claims) := rfl

theorem daListDigest_eq (claims : List DaClaim) :
    daListDigest claims = keccak256 (daPreimage claims) := rfl

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

theorem kBytes_inj {a b : K} (h : kBytes a = kBytes b) : a = b :=
  K.lane_injective (wordBytes_injective h)

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
    (fun _ ↦ by rw [List.length_append, digestBytes_length, digestBytes_length])
    (fun ⟨r, v⟩ ⟨r', v'⟩ h ↦ by
      obtain ⟨h1, h2⟩ := List.append_inj h (by rw [digestBytes_length, digestBytes_length])
      have e1 : r = r' := digestBytes_injective h1
      have e2 : v = v' := digestBytes_injective h2
      subst e1 e2
      rfl) h

theorem signersPreimage_inj {x x' : List XmssClaim} {p p' : List SphincsClaim}
    (h : signersPreimage x p = signersPreimage x' p') :
    xmssListDigest x = xmssListDigest x' ∧ sphincsListDigest p = sphincsListDigest p' := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by rw [digestBytes_length, digestBytes_length])
  exact ⟨digestBytes_injective h1, digestBytes_injective h2⟩

/-- Two deferred claims with the same cells and points of the same length are equal. -/
theorem cells_inj {c c' : DeferredClaim}
    (hb : c.bytecodePoint.length = c'.bytecodePoint.length) (h : c.cells = c'.cells) : c = c' := by
  obtain ⟨b, v⟩ := c
  obtain ⟨b', v'⟩ := c'
  simp only [DeferredClaim.cells] at h hb
  obtain ⟨h1, h2⟩ := List.append_inj h hb
  simp only [List.cons.injEq, and_true] at h2
  subst h1 h2
  rfl

/-- The outer preimage determines the seed, the two nested digests and, at a fixed point
length, the deferred claim. -/
theorem statementPreimage_inj {seed seed' : Digest} {s s' : NodeStatement}
    (hb : s.defer.bytecodePoint.length = s'.defer.bytecodePoint.length)
    (h : statementPreimage seed s = statementPreimage seed' s') :
    seed = seed' ∧
      signersDigest s.claims.xmss s.claims.sphincs =
        signersDigest s'.claims.xmss s'.claims.sphincs ∧
      daListDigest s.claims.da = daListDigest s'.claims.da ∧ s.defer = s'.defer := by
  have hc : s.defer.cells.length = s'.defer.cells.length := by
    simp [DeferredClaim.cells, hb]
  unfold statementPreimage at h
  obtain ⟨h123, h4⟩ := List.append_inj h (by simp [digestBytes_length])
  obtain ⟨h12, h3⟩ := List.append_inj h123 (by simp [digestBytes_length])
  obtain ⟨h1, h2⟩ := List.append_inj h12 (by simp [digestBytes_length])
  have hp := flatMap_inj (n := 24) (by decide) length_eBytes (fun _ _ ↦ eBytes_inj) h4
  unfold paddedCells at hp
  obtain ⟨hcells, -⟩ := List.append_inj hp hc
  exact ⟨digestBytes_injective h1, digestBytes_injective h2, digestBytes_injective h3,
    cells_inj hb hcells⟩

/-! ## The binding -/

/-- **The statement's digest binds**, at point lengths equal on both sides: the seeds and the
statements are equal, or a candidate pair is a Keccak-256 collision. -/
theorem statementDigest_binds_of_length {seed seed' : Digest} {s s' : NodeStatement}
    (hb : s.defer.bytecodePoint.length = s'.defer.bytecodePoint.length)
    (h : statementDigest seed s = statementDigest seed' s') :
    (seed = seed' ∧ s = s') ∨ HasCollision (collisionCandidates seed s seed' s') := by
  by_cases h0 : statementPreimage seed s = statementPreimage seed' s'
  swap
  · exact Or.inr ⟨(statementPreimage seed s, statementPreimage seed' s'),
      by simp [collisionCandidates], h0, h⟩
  obtain ⟨hseed, hsig, hda, hdef⟩ := statementPreimage_inj hb h0
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
of the candidate pairs is a Keccak-256 collision. The shape fixes the length of the deferred
claim's point, which its cells do not record. -/
theorem statementDigest_binds {b : List K} {seed seed' : Digest} {s s' : NodeStatement}
    (hs : s.defer.Shaped b) (hs' : s'.defer.Shaped b)
    (h : statementDigest seed s = statementDigest seed' s') :
    (seed = seed' ∧ s = s') ∨ HasCollision (collisionCandidates seed s seed' s') :=
  statementDigest_binds_of_length (hs.trans hs'.symm) h

/-! ## What a consumer learns -/

/-- **A consumer learns the decoded statement**: it checks that the public input's digest is its
statement `s₀`'s under the deployed seed `iv`; an execution decodes a seed and a statement `s` of
the same digest. Then the decoded seed is `iv` and `s` is `s₀`, or a candidate pair is a
Keccak-256 collision. -/
theorem decoded_binds {b : List K} {iv seed : Digest} {s₀ s : NodeStatement}
    {input : PublicInput} (hs₀ : s₀.defer.Shaped b) (hs : s.defer.Shaped b)
    (hpub : publicDigest input = statementDigest iv s₀)
    (hdec : statementDigest seed s = publicDigest input) :
    (seed = iv ∧ s = s₀) ∨ HasCollision (collisionCandidates seed s iv s₀) :=
  statementDigest_binds hs hs₀ (hdec.trans hpub)

/-- `decoded_binds` with the decoded statement's shape from where it comes: one the guest
`bytecode` establishes (`NodeRel`); the consumer's deferred claim has the shape of `bytecode`
(`AggregateSound` assumes it). -/
theorem decoded_binds_of_nodeRel {bytecode : List K} {iv seed : Digest} {s₀ s : NodeStatement}
    {w : NodeWitness} {input : PublicInput} (hs₀ : s₀.defer.Shaped bytecode)
    (hrel : NodeRel bytecode seed s w)
    (hpub : publicDigest input = statementDigest iv s₀)
    (hdec : statementDigest seed s = publicDigest input) :
    (seed = iv ∧ s = s₀) ∨ HasCollision (collisionCandidates seed s iv s₀) :=
  decoded_binds hs₀ hrel.1 hpub hdec

end
end LeanVM.Guest.Binding
