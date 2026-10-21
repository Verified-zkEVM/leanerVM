/-
  LeanVM.E2E.Da.Log

  The DA leg of the end-to-end theorem, in the random-oracle model: LeanDA's byte encodings, the
  uniform challenge of a digest, and the DA failure event of a log with its count and the order
  facts that hold without it.
-/

module

public import LeanVM.E2E.Statement
public import LeanDa.Dual

/-!
# The DA leg: encodings and failure

The DA claim of a root `ρ` (`Witness.OpensWith`, `outerChecksWith`) is answered by the oracle's
log: LeanDA's hash `daHash (look ℓ)` is the log's lookup read as LeanDA's 32 bytes (`toBytes`).
This module collects what the proof of the DA leg (`LeanVM.E2E.Da`) reads off a log.

**Encodings.** A symbol is its eight bytes (`ofBytes_kBytes`, `kBytes_ofBytes`), a root its four
words (`eq_of_obsBlock`, through the two blocks the challenge chain observes, `obsBlock`), a
vector its bytes (`vecBytes_injective`), a codeword its cells (`eq_of_listCell`). The
challenge squeezed into a state (`daChallenge`) is the verifier's (`daChallenge_eq`), so the
challenge of a uniform digest is uniform (`sum_daChallenge_div`).

**Failure.** A fresh answer `u` at `t`, appended to `ℓ`, *fails for DA* (`BadDA pc`) if

* it is an output of `ℓ` (a collision);
* it is the padding digest `pc` of the column tree (as LeanDA's bytes);
* it is a 32-byte chunk at offset `0` or `32` of `t` or of an input of `ℓ` (a prediction: the
  Merkle nodes' inputs carry their children there, the challenge chain's its state);
* it is the root an input of `t :: ℓ` completes (`DaRootOf`): `d ‖ obsBlock ρ 1` with `d` the
  output of the first entry of `ℓ` producing it, that entry's input ending in `obsBlock ρ 0`.

`FailDA pc ℓ` holds if some entry fails with respect to the entries before it. At most
`4 (|ℓ| + 1)` answers fail at a fresh input (`sum_badDA_le`). Without failure, outputs are
distinct (`look_inj_of_not_failDA`), no output is `pc`, and an entry whose output is a chunk or
the completed root of an entry's input comes before it (`lt_of_chunk_da`,
`not_daRootOf_of_not_failDA`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

/-! ## Symbols, words and digests as bytes -/

/-- A symbol has eight bytes. -/
theorem daKBytes_length (a : K) : (LeanDa.kBytes a).length = 8 := by simp [LeanDa.kBytes]

/-- A symbol is its eight little-endian bytes. -/
theorem ofBytes_kBytes (a : K) : LeanDa.ofBytes (LeanDa.kBytes a) = a := by
  apply BF64.ext
  have hn := a.toBitVec.isLt
  simp only [LeanDa.ofBytes, LeanDa.kBytes, LeanDa.K.ofBits, BF64.toBitVec_ofBitVec,
    List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.foldr_cons, List.foldr_nil, Nat.toUInt8, UInt8.toNat_ofNat',
    Nat.shiftRight_eq_div_pow]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

/-- A symbol is determined by its bytes. -/
theorem daKBytes_injective : Function.Injective LeanDa.kBytes := fun a b h ↦ by
  rw [← ofBytes_kBytes a, ← ofBytes_kBytes b, h]

/-- Eight bytes are the bytes of their symbol. -/
theorem kBytes_ofBytes {bs : List UInt8} (h : bs.length = 8) :
    LeanDa.kBytes (LeanDa.ofBytes bs) = bs := by
  match bs, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
  simp only [LeanDa.ofBytes, LeanDa.kBytes, LeanDa.K.ofBits, BF64.toBitVec_ofBitVec,
    List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.foldr_cons, List.foldr_nil, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt; have := b3.toNat_lt
  have := b4.toNat_lt; have := b5.toNat_lt; have := b6.toNat_lt; have := b7.toNat_lt
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
    simp only [Nat.toUInt8, UInt8.toNat_ofNat'] <;> omega

/-- Two lists of symbols with the same bytes are equal. -/
theorem flatMap_daKBytes_inj {l l' : List K}
    (h : l.flatMap LeanDa.kBytes = l'.flatMap LeanDa.kBytes) :
    l = l' := by
  have hl : l.length = l'.length := by
    have := congrArg List.length h
    simp only [List.length_flatMap, daKBytes_length, List.map_const', List.sum_replicate,
      smul_eq_mul] at this
    omega
  exact flatMap_inj_of_length daKBytes_length daKBytes_injective hl h

/-- The symbol of two little-endian words is `ofWords`. -/
theorem ofBytes_wordBytes (a b : UInt32) :
    LeanDa.ofBytes (wordBytes a ++ wordBytes b) = ofWords a b := by
  apply BF64.ext
  simp only [LeanDa.ofBytes, wordBytes, ofWords, LeanDa.K.ofBits, BF64.toBitVec_ofBitVec,
    List.cons_append, List.nil_append, List.foldr_cons, List.foldr_nil]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_append]
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  simp only [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, UInt32.toNat_toBitVec,
    Nat.shiftRight_eq_div_pow, UInt32.reduceToNat, Nat.reduceMod, Nat.reducePow]
  rw [← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq]
  omega

/-- A digest's LeanDA bytes are its bytes. -/
theorem toBytes_toList (d : Digest) : (Da.toBytes d).toList = digestBytes d := rfl

/-- A digest is determined by its LeanDA bytes. -/
theorem toBytes_injective : Function.Injective Da.toBytes := fun d d' h ↦
  digestBytes_injective (by rw [← toBytes_toList, ← toBytes_toList, h])

/-- Word `i` of a digest's LeanDA bytes is its words `2i` and `2i + 1`. -/
theorem word_toBytes (d : Digest) (i : ℕ) (hi : i < 4) :
    LeanDa.word (Da.toBytes d) i =
      ofWords (d.toList.getD (2 * i) 0) (d.toList.getD (2 * i + 1) 0) := by
  rw [← ofBytes_wordBytes]
  unfold LeanDa.word
  congr 1
  change ((digestBytes d).drop (8 * i)).take 8 = _
  obtain ⟨⟨l⟩, hl⟩ := d
  simp only [List.size_toArray] at hl
  match l, hl with
  | [w0, w1, w2, w3, w4, w5, w6, w7], _ =>
    interval_cases i <;> rfl

/-! ## The challenge of a state -/

/-- **The challenge squeezed into a state** (`LeanDa.squeezes`): the element of its first three
words. -/
def daChallenge (d : Digest) : E :=
  LeanDa.ofLimbs (LeanDa.word (Da.toBytes d) 0) (LeanDa.word (Da.toBytes d) 1)
    (LeanDa.word (Da.toBytes d) 2)

/-- The DA challenge of a state is the verifier's. -/
theorem daChallenge_eq (d : Digest) : daChallenge d = challengeOf d := by
  rw [daChallenge, word_toBytes d 0 (by norm_num), word_toBytes d 1 (by norm_num),
    word_toBytes d 2 (by norm_num), challengeOf]
  obtain ⟨⟨l⟩, hl⟩ := d
  simp only [List.size_toArray] at hl
  match l, hl with
  | [w0, w1, w2, w3, w4, w5, w6, w7], _ => rfl

/-- `|E| = 2^192`. -/
theorem card_E_da : Fintype.card E = 2 ^ 192 := BF64.card_ext3

/-- **The challenge of a uniform digest is uniform**: every challenge has `2^64` preimages
(`challengeEquiv`). -/
theorem sum_daChallenge_div (f : E → ℝ≥0∞) :
    (∑ d : Digest, f (daChallenge d)) / Fintype.card Digest =
      (∑ c : E, f c) / Fintype.card E := by
  have hs : ∑ d : Digest, f (daChallenge d) =
      (Fintype.card (UInt32 × UInt32) : ℝ≥0∞) * ∑ c : E, f c := by
    rw [Fintype.sum_equiv challengeEquiv (fun d ↦ f (daChallenge d)) (fun p ↦ f p.1)
      (fun d ↦ by rw [daChallenge_eq]; rfl), Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
  have hc : (Fintype.card Digest : ℝ≥0∞) =
      (Fintype.card (UInt32 × UInt32) : ℝ≥0∞) * Fintype.card E := by
    rw [Fintype.card_congr challengeEquiv, Fintype.card_prod, Nat.cast_mul, mul_comm]
  rw [hs, hc, ENNReal.mul_div_mul_left]
  · exact_mod_cast Fintype.card_ne_zero
  · exact ENNReal.natCast_ne_top _

/-! ## The blocks of the challenge chain -/

/-- The block observing half `i` of a root: its words `2i` and `2i + 1`, then `0` and the tag
`1` (`DS_OBSERVE`). -/
def obsBlock (ρ : LeanDa.Digest) (i : ℕ) : Bytes :=
  [LeanDa.word ρ (2 * i), LeanDa.word ρ (2 * i + 1), 0, LeanDa.K.ofBits 1].flatMap LeanDa.kBytes

/-- The squeeze block: three zeros and the tag `2` (`DS_SQUEEZE`). -/
def sqBlock : Bytes := [0, 0, 0, LeanDa.K.ofBits 2].flatMap LeanDa.kBytes

/-- The input of a squeeze from the state `d`. -/
def sqIn (d : Digest) : Bytes := digestBytes d ++ sqBlock

/-- An observation block has 32 bytes. -/
theorem obsBlock_length (ρ : LeanDa.Digest) (i : ℕ) : (obsBlock ρ i).length = 32 := rfl

/-- A root is its four words. -/
theorem eq_of_words {ρ ρ' : LeanDa.Digest} (h : ∀ i < 4, LeanDa.word ρ i = LeanDa.word ρ' i) :
    ρ = ρ' := by
  have hs : ∀ σ : LeanDa.Digest, σ.toList =
      [LeanDa.word σ 0, LeanDa.word σ 1, LeanDa.word σ 2, LeanDa.word σ 3].flatMap
        LeanDa.kBytes := by
    intro σ
    have hl : σ.toList.length = 32 := by simp
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, LeanDa.word]
    rw [kBytes_ofBytes (by simp [hl]), kBytes_ofBytes (by simp [hl]),
      kBytes_ofBytes (by simp [hl]), kBytes_ofBytes (by simp [hl])]
    refine List.ext_getElem (by simp [hl]) fun n h₁ _ ↦ ?_
    simp only [List.getElem_append, List.getElem_take, List.getElem_drop, List.length_take,
      List.length_drop, hl]
    split_ifs <;> (congr 1; omega)
  apply Vector.toList_inj.mp
  rw [hs ρ, hs ρ', h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num)]

/-- **A root is its two observed blocks.** -/
theorem eq_of_obsBlock {ρ ρ' : LeanDa.Digest} (h0 : obsBlock ρ 0 = obsBlock ρ' 0)
    (h1 : obsBlock ρ 1 = obsBlock ρ' 1) : ρ = ρ' := by
  have e0 := flatMap_daKBytes_inj h0
  have e1 := flatMap_daKBytes_inj h1
  simp only [List.cons.injEq] at e0 e1
  refine eq_of_words fun i hi ↦ ?_
  interval_cases i
  · exact e0.1
  · exact e0.2.1
  · exact e1.1
  · exact e1.2.1

/-! ## Vectors and codewords as bytes -/

/-- The bytes of a vector the vector digest hashes. -/
def vecBytes (v : List E) : Bytes :=
  (v.flatMap fun e ↦ [LeanDa.limb e 0, LeanDa.limb e 1, LeanDa.limb e 2]).flatMap LeanDa.kBytes

/-- **A vector is its bytes.** -/
theorem vecBytes_injective : Function.Injective vecBytes := by
  intro v v' h
  have h1 := flatMap_daKBytes_inj h
  have hlen : v.length = v'.length := by
    have := congrArg List.length h1
    simp only [List.length_flatMap, List.length_cons, List.length_nil, List.map_const',
      List.sum_replicate, smul_eq_mul] at this
    omega
  refine flatMap_inj_of_length (n := 3) (fun _ ↦ rfl) (fun e e' he ↦ ?_) hlen h1
  simp only [List.cons.injEq, and_true] at he
  rw [← ofLimbs_limb e, ← ofLimbs_limb e']
  change E.ofLimbs (LeanDa.limb e 0) (LeanDa.limb e 1) (LeanDa.limb e 2) =
    E.ofLimbs (LeanDa.limb e' 0) (LeanDa.limb e' 1) (LeanDa.limb e' 2)
  rw [he.1, he.2.1, he.2.2]

/-- The vector digest hashes the vector's bytes. -/
theorem vectorDigestWith_eq {m : Type → Type} [Monad m] (HD : List UInt8 → m LeanDa.Digest)
    (v : List E) : Da.vectorDigestWith HD v = HD (vecBytes v) := rfl

/-- A cell of a codeword has `256` symbols. -/
theorem length_listCell {row : List K} (h : row.length = 2 ^ LeanDa.logM) {j : ℕ}
    (hj : j < LeanDa.cellsPerRow) : (LeanDa.listCell row j).length = LeanDa.cellSymbols := by
  simp only [LeanDa.listCell, List.length_take, List.length_drop, h, LeanDa.cellSymbols,
    LeanDa.logM, LeanDa.cellsPerRow] at hj ⊢
  omega

/-- **A codeword is its cells.** -/
theorem eq_of_listCell {row row' : List K} (h : row.length = 2 ^ LeanDa.logM)
    (h' : row'.length = 2 ^ LeanDa.logM)
    (hc : ∀ j < LeanDa.cellsPerRow, LeanDa.listCell row j = LeanDa.listCell row' j) :
    row = row' := by
  refine List.ext_getElem (by rw [h, h']) fun p hp hp' ↦ ?_
  have hj : p / 256 < LeanDa.cellsPerRow := by
    simp only [LeanDa.cellsPerRow]; rw [h] at hp; simp only [LeanDa.logM] at hp; omega
  have hcell := congrArg (fun l ↦ l[p % 256]?) (hc _ hj)
  simp only [LeanDa.listCell, LeanDa.cellSymbols, List.getElem?_take, List.getElem?_drop] at hcell
  rw [ite_eq_left (Nat.mod_lt _ (by norm_num)), ite_eq_left (Nat.mod_lt _ (by norm_num)),
    show p / 256 * 256 + p % 256 = p by omega] at hcell
  rw [List.getElem?_eq_getElem hp, List.getElem?_eq_getElem hp'] at hcell
  exact Option.some.inj hcell

/-! ## The root an input completes -/

/-- **The root the input `x` completes in `ℓ`**: `x = d ‖ obsBlock ρ 1` with `d` the output of
the first entry of `ℓ` producing it, that entry's input ending in `obsBlock ρ 0` (the chain's
observation of the root's two halves). -/
def DaRootOf (ℓ : Log) (x : Bytes) (ρ : LeanDa.Digest) : Prop :=
  ∃ (d : Digest) (e : Bytes × Digest), x = digestBytes d ++ obsBlock ρ 1 ∧
    ℓ.find? (fun e ↦ decide (e.2 = d)) = some e ∧ e.1.drop 32 = obsBlock ρ 0

/-- A root is determined by the input that completes it. -/
theorem daRootOf_unique {ℓ : Log} {x : Bytes} {ρ ρ' : LeanDa.Digest} (h : DaRootOf ℓ x ρ)
    (h' : DaRootOf ℓ x ρ') : ρ = ρ' := by
  obtain ⟨d, e, hx, hf, he⟩ := h
  obtain ⟨d', e', hx', hf', he'⟩ := h'
  obtain ⟨hd, hb⟩ := List.append_inj (hx.symm.trans hx')
    (by rw [digestBytes_length, digestBytes_length])
  cases digestBytes_injective hd
  rw [hf] at hf'
  cases hf'
  exact eq_of_obsBlock (he.symm.trans he') hb

/-! ## Failure -/

/-- **A fresh answer `u` at `t` appended to `ℓ` fails for DA**: it collides with an output of
`ℓ`, is the padding digest `pc`, or is a chunk or the completed root of `t` or of an input of
`ℓ`. -/
def BadDA (pc : LeanDa.Digest) (ℓ : Log) (t : Bytes) (u : Digest) : Prop :=
  (∃ e ∈ ℓ, e.2 = u) ∨ Da.toBytes u = pc ∨
    ∃ x ∈ t :: ℓ.map Prod.fst, chunk0 x = digestBytes u ∨ chunk1 x = digestBytes u ∨
      DaRootOf ℓ x (Da.toBytes u)

/-- **Some entry of the log failed for DA** with respect to the entries before it. -/
def FailDA (pc : LeanDa.Digest) (ℓ : Log) : Prop :=
  ∃ (i : ℕ) (hi : i < ℓ.length), BadDA pc (ℓ.take i) ℓ[i].1 ℓ[i].2

/-- The empty log has not failed. -/
theorem not_failDA_nil (pc : LeanDa.Digest) : ¬ FailDA pc [] := fun ⟨_, hi, _⟩ ↦ by
  simp at hi

/-- The log with one more entry fails for DA exactly if the log does or the entry does. -/
theorem failDA_append (pc : LeanDa.Digest) (ℓ : Log) (t : Bytes) (u : Digest) :
    FailDA pc (ℓ ++ [(t, u)]) ↔ FailDA pc ℓ ∨ BadDA pc ℓ t u := by
  constructor
  · rintro ⟨i, hi, h⟩
    rw [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · left
      refine ⟨i, hi', ?_⟩
      rwa [List.getElem_append_left hi', List.take_append_of_le_length hi'.le] at h
    · right
      simpa using h
  · rintro (⟨i, hi, h⟩ | h)
    · refine ⟨i, by simp; omega, ?_⟩
      rwa [List.getElem_append_left hi, List.take_append_of_le_length hi.le]
    · exact ⟨ℓ.length, by simp, by simpa using h⟩

/-- A prefix of a log without DA failure has none. -/
theorem not_failDA_take {pc : LeanDa.Digest} {ℓ : Log} (h : ¬ FailDA pc ℓ) (n : ℕ) :
    ¬ FailDA pc (ℓ.take n) := by
  rintro ⟨i, hi, hb⟩
  simp only [List.length_take] at hi
  refine h ⟨i, by omega, ?_⟩
  rwa [List.take_take, min_eq_left (by omega), List.getElem_take] at hb

/-! ## The count of failing answers -/

/-- **The count of failing answers**: at most `4 (|ℓ| + 1)` digests fail for DA at an input. -/
theorem sum_badDA_le (pc : LeanDa.Digest) (ℓ : Log) (t : Bytes) :
    ∑ u, ind (BadDA pc ℓ t u) ≤ ((4 * (ℓ.length + 1) : ℕ) : ℝ≥0∞) := by
  set L := t :: ℓ.map Prod.fst
  let g : Bytes → Digest → ℝ≥0∞ := fun x u ↦ ind (chunk0 x = digestBytes u) +
    ind (chunk1 x = digestBytes u) + ind (DaRootOf ℓ x (Da.toBytes u))
  have hpt : ∀ u, ind (BadDA pc ℓ t u) ≤
      (ℓ.map fun e ↦ ind (e.2 = u)).sum + ind (Da.toBytes u = pc) +
        (L.map fun x ↦ g x u).sum := by
    intro u
    refine (ind_or_le _ _).trans ?_
    rw [add_assoc]
    refine add_le_add (ind_exists_le _ _) ((ind_or_le _ _).trans (add_le_add le_rfl ?_))
    refine (ind_exists_le _ _).trans (List.sum_le_sum fun x _ ↦ ?_)
    refine (ind_or_le _ _).trans ?_
    simp only [g, add_assoc]
    exact add_le_add le_rfl (ind_or_le _ _)
  have h1 : ∀ e ∈ ℓ, ∑ u, ind (e.2 = u) ≤ 1 := fun e _ ↦
    sum_ind_le_one fun u u' hu hu' ↦ hu.symm.trans hu'
  have hpc : ∑ u, ind (Da.toBytes u = pc) ≤ 1 :=
    sum_ind_le_one fun u u' hu hu' ↦ toBytes_injective (hu.trans hu'.symm)
  have h2 : ∀ x ∈ L, ∑ u, g x u ≤ (3 : ℕ) := by
    intro x _
    simp only [g, Finset.sum_add_distrib]
    have hc0 : ∑ u, ind (chunk0 x = digestBytes u) ≤ 1 :=
      sum_ind_le_one fun u u' hu hu' ↦ digestBytes_injective (hu.symm.trans hu')
    have hc1 : ∑ u, ind (chunk1 x = digestBytes u) ≤ 1 :=
      sum_ind_le_one fun u u' hu hu' ↦ digestBytes_injective (hu.symm.trans hu')
    have hr : ∑ u, ind (DaRootOf ℓ x (Da.toBytes u)) ≤ 1 :=
      sum_ind_le_one fun u u' hu hu' ↦ toBytes_injective (daRootOf_unique hu hu')
    calc _ ≤ 1 + 1 + 1 := by gcongr
      _ = ((3 : ℕ) : ℝ≥0∞) := by norm_num
  calc ∑ u, ind (BadDA pc ℓ t u)
      ≤ ∑ u, ((ℓ.map fun e ↦ ind (e.2 = u)).sum + ind (Da.toBytes u = pc) +
          (L.map fun x ↦ g x u).sum) := Finset.sum_le_sum fun u _ ↦ hpt u
    _ = (ℓ.map fun e ↦ ∑ u, ind (e.2 = u)).sum + ∑ u, ind (Da.toBytes u = pc) +
          (L.map fun x ↦ ∑ u, g x u).sum := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_list_sum_comm,
          sum_list_sum_comm]
    _ ≤ ℓ.length * 1 + 1 + L.length * ((3 : ℕ) : ℝ≥0∞) :=
        add_le_add (add_le_add (list_sum_le _ _ _ h1) hpc) (list_sum_le _ _ _ h2)
    _ = _ := by
        simp only [L, List.length_cons, List.length_map, mul_one]
        push_cast
        ring

/-! ## Order facts without failure -/

section Order

variable {pc : LeanDa.Digest} {ℓ : Log}

/-- Without DA failure, outputs are distinct. -/
theorem output_ne_da (h : ¬ FailDA pc ℓ) {i j : ℕ} (hi : i < ℓ.length) (hj : j < ℓ.length)
    (hij : i < j) : ℓ[i].2 ≠ ℓ[j].2 := by
  intro heq
  refine h ⟨j, hj, Or.inl ⟨ℓ[i], ?_, heq⟩⟩
  exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩

/-- Without DA failure, two entries with one output are one entry. -/
theorem index_eq_of_output_da (h : ¬ FailDA pc ℓ) {i j : ℕ} (hi : i < ℓ.length)
    (hj : j < ℓ.length) (heq : ℓ[i].2 = ℓ[j].2) : i = j := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact absurd heq (output_ne_da h hi hj hij)
  · rfl
  · exact absurd heq.symm (output_ne_da h hj hi hij)

/-- Without DA failure, the log's answers have no collision. -/
theorem look_inj_of_not_failDA (h : ¬ FailDA pc ℓ) {x y : Bytes} {v : Digest}
    (hx : look ℓ x = some v) (hy : look ℓ y = some v) : x = y := by
  obtain ⟨i, hi, hei, -⟩ := (look_eq_some_iff ℓ x v).mp hx
  obtain ⟨j, hj, hej, -⟩ := (look_eq_some_iff ℓ y v).mp hy
  have := index_eq_of_output_da h hi hj (by rw [hei, hej])
  subst this
  rw [hei] at hej
  exact (Prod.mk.inj hej).1

/-- Without DA failure, LeanDA's hash on the log has no collision. -/
theorem daHash_inj_of_not_failDA (h : ¬ FailDA pc ℓ) {x y : Bytes} {ρ : LeanDa.Digest}
    (hx : Da.daHash (look ℓ) x = some ρ) (hy : Da.daHash (look ℓ) y = some ρ) : x = y := by
  simp only [Da.daHash, Option.map_eq_map, Option.map_eq_some_iff] at hx hy
  obtain ⟨v, hv, rfl⟩ := hx
  obtain ⟨v', hv', he⟩ := hy
  cases toBytes_injective he
  exact look_inj_of_not_failDA h hv hv'

/-- Without DA failure, no answer of the log is the padding digest. -/
theorem daHash_ne_pc_of_not_failDA (h : ¬ FailDA pc ℓ) (x : Bytes) :
    Da.daHash (look ℓ) x ≠ some pc := by
  intro hx
  simp only [Da.daHash, Option.map_eq_map, Option.map_eq_some_iff] at hx
  obtain ⟨v, hv, hpc⟩ := hx
  obtain ⟨i, hi, hei, -⟩ := (look_eq_some_iff ℓ x v).mp hv
  exact h ⟨i, hi, Or.inr (Or.inl (by rw [hei]; exact hpc))⟩

/-- The inputs of the entries up to `i` are those the failure condition of entry `i` reads. -/
theorem mem_inputs_of_le_da {i j : ℕ} (hi : i < ℓ.length) (hji : j ≤ i) :
    ℓ[j].1 ∈ ℓ[i].1 :: (ℓ.take i).map Prod.fst := by
  rcases Nat.lt_or_eq_of_le hji with hlt | rfl
  · refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨ℓ[j], ?_, rfl⟩)
    exact List.mem_iff_getElem.mpr ⟨j, by simp; omega, by simp⟩
  · exact List.mem_cons_self

/-- Without DA failure, an entry whose output is a chunk of an entry's input comes before it. -/
theorem lt_of_chunk_da (h : ¬ FailDA pc ℓ) {i j : ℕ} (hi : i < ℓ.length) (hj : j < ℓ.length)
    (hc : chunk0 ℓ[j].1 = digestBytes ℓ[i].2 ∨ chunk1 ℓ[j].1 = digestBytes ℓ[i].2) : i < j := by
  by_contra hji
  refine h ⟨i, hi, Or.inr (Or.inr ⟨ℓ[j].1, mem_inputs_of_le_da hi (by omega), ?_⟩)⟩
  rcases hc with hc | hc
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)

/-- Without DA failure, no answer is a chunk of its input or of an earlier one. -/
theorem not_chunk_of_not_failDA (h : ¬ FailDA pc ℓ) {j : ℕ} (hj : j < ℓ.length) :
    ∀ x ∈ ℓ[j].1 :: (ℓ.take j).map Prod.fst,
      chunk0 x ≠ digestBytes ℓ[j].2 ∧ chunk1 x ≠ digestBytes ℓ[j].2 :=
  fun x hx ↦ ⟨fun hc ↦ h ⟨j, hj, Or.inr (Or.inr ⟨x, hx, Or.inl hc⟩)⟩,
    fun hc ↦ h ⟨j, hj, Or.inr (Or.inr ⟨x, hx, Or.inr (Or.inl hc)⟩)⟩⟩

/-- Without DA failure, no answer is the root its input or an earlier one completes. -/
theorem not_daRootOf_of_not_failDA (h : ¬ FailDA pc ℓ) {j : ℕ} (hj : j < ℓ.length) :
    ∀ x ∈ ℓ[j].1 :: (ℓ.take j).map Prod.fst, ¬ DaRootOf (ℓ.take j) x (Da.toBytes ℓ[j].2) :=
  fun x hx hr ↦ h ⟨j, hj, Or.inr (Or.inr ⟨x, hx, Or.inr (Or.inr hr)⟩)⟩

end Order

end
end LeanVM.E2E
