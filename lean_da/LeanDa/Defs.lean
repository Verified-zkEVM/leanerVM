import PqDas.Defs
import Common.SimDefs

/-!
# LeanDA in Benedikt Wagner's framework: the definitions of the proofs

LeanDA's code checker and vector commitment, the collision of two openings and the reduction that
computes it, the challenges' duplex (`daDuplex`, a `Common.Duplex.DuplexSpec`), the opening's
check with a pure hash (`verifyCell`), the uniform samplers of `K` and `E`, and Wagner's
terms for a uniformly random table of the hash (`ksExpH`, `wpbCollExpH`, `forkCollExpH`), moved
here from `Statement/LeanDa.lean`: they are steps of the proofs, and no end statement names them.

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

/-! ## LeanDA's Merkle collisions -/

section

namespace LeanDa

/-- Uniform sampling of `K` through its bits. -/
instance : SampleableType K := SampleableType.ofEquiv BF64.equivFin.symm

/-- Uniform sampling of `E` limb by limb. -/
instance : SampleableType E := SampleableType.ofEquiv (CompPoly.Extension.Ext.equivFn _).symm

variable (H : List UInt8 → Digest)

/-- Climb from `node` at index `idx` along the siblings `path`. -/
def walk : ℕ → Digest → List Digest → Digest
  | _, node, [] => node
  | idx, node, s :: rest =>
    walk (idx / 2) (if idx % 2 = 0 then H (pairBytes node s) else H (pairBytes s node)) rest

/-- **Verification of a cell opening** with a pure hash (`verifyCellM` over `Id`): a path of the
column tree's height that climbs from the cell's digest to a column root, which hashed after the
row root gives the commitment. -/
def verifyCell (r : ℕ) (com : Digest) (p : Fin (r * 128)) (x : Cell) (τ : Opening) : Bool :=
  decide (τ.path.length = 7 + logPad r) &&
    decide (H (pairBytes τ.rowRoot (walk H (colIndex p) (cellDigest H x) τ.path)) = com)

/-- The hash inputs from a cell's bytes `a` at index `idx` up to the root, the last one
`rowRoot ‖ colRoot`. -/
def hashInputs : ℕ → List UInt8 → List Digest → Digest → List (List UInt8)
  | _, a, [], rr => [a, pairBytes rr (H a)]
  | idx, a, s :: rest, rr =>
    a :: hashInputs (idx / 2) (if idx % 2 = 0 then pairBytes (H a) s else pairBytes s (H a)) rest rr

/-- The first pair of inputs, level by level, that differ and hash alike. -/
def findCollision : List (List UInt8) → List (List UInt8) → List UInt8 × List UInt8
  | a :: as, b :: bs => if a ≠ b ∧ H a = H b then (a, b) else findCollision as bs
  | _, _ => ([], [])

/-- The collision two openings of one position give. -/
def openingsCollision (r : ℕ) (p : Fin (r * 128)) (x : Cell) (τ : Opening) (x' : Cell)
    (τ' : Opening) : List UInt8 × List UInt8 :=
  findCollision H (hashInputs H (colIndex p) (cellBytes x) τ.path τ.rowRoot)
    (hashInputs H (colIndex p) (cellBytes x') τ'.path τ'.rowRoot)

end LeanDa

end

section

open PqDas OracleComp OracleSpec ENNReal

namespace LeanDa

/-- **LeanDA's code checker**: the membership test on challenges `z ∈ E^14`. -/
noncomputable def checker (r : ℕ) : CodeChecker Cell (r * 128) Challenges := ⟨membershipCheck⟩

/-- **LeanDA's vector commitment** with hash `H`: the root of the two Merkle trees, cells opened
by their column-tree paths. It needs no key. -/
def merkleVC (r : ℕ) (H : List UInt8 → Digest) :
    VectorCommitment Cell (r * 128) Unit Digest Opening where
  setup := pure ()
  commit _ c := commitCells H c
  openAt _ c p := openCell H c p
  verify _ com p x τ := verifyCell H r com p x τ

/-- The collision experiment for a hash function: a finder wins if it outputs two different
byte strings with the same hash. -/
def hashCollisionExp (H : List UInt8 → Digest) (B : ProbComp (List UInt8 × List UInt8)) :
    ProbComp Bool := do
  let (a, b) ← B
  return (decide (a ≠ b) && decide (H a = H b))

/-- **The reduction from position binding to a collision**: run the adversary and climb its two
openings (`openingsCollision`). -/
def merkleCollider (r : ℕ) (H : List UInt8 → Digest)
    (A : VectorCommitment.PosBindingAdv Cell (r * 128) Unit Digest Opening) :
    ProbComp (List UInt8 × List UInt8) := do
  let (_, p, x, τ, x', τ') ← A ()
  return openingsCollision H r p x τ x' τ'

/-- An argument of knowledge for Wagner's scheme relation of LeanDA (`Relation`, by
`relation_eq`). -/
abbrev WArgument (r : ℕ) (H : List UInt8 → Digest) (Crs Proof : Type) :=
  Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof
    (schemeRel (merkleVC r H) (checker r))

/-- The verifier's oracles (`VerSpec`), by the name of the proofs. -/
abbrev Rom2 := VerSpec

/-- The relation is Wagner's scheme relation for LeanDA's vector commitment and code checker. -/
theorem relation_eq (r : ℕ) (H : List UInt8 → Digest) :
    Relation r H = schemeRel (merkleVC r H) (checker r) := rfl

end LeanDa

end

section

namespace LeanDa

/-- Byte `p` of lanes of eight bytes each is byte `p % 8` of lane `p / 8`. -/
theorem getD_flatMap_laneBytes (l : List K) (p : ℕ) :
    (l.flatMap fun a ↦ (laneBytes a).toList).getD p 0 =
      if h : p / 8 < l.length then (laneBytes l[p / 8])[p % 8] else 0 := by
  induction l generalizing p with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons]
    by_cases hp : p < 8
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hp)]
      have h0 : p / 8 = 0 := by omega
      simp [h0, Nat.mod_eq_of_lt hp, Vector.getElem?_eq_getElem hp]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega), ← List.getD_eq_getElem?_getD]
      simp only [Vector.length_toList]
      rw [ih (p - 8)]
      have h1 : (p - 8) / 8 = p / 8 - 1 := by omega
      have h2 : (p - 8) % 8 = p % 8 := by omega
      simp only [h1, h2, List.length_cons]
      by_cases hl : p / 8 - 1 < l.length
      · have h3 : p / 8 < l.length + 1 := by omega
        simp only [hl, h3, ↓reduceDIte]
        rw [List.getElem_cons (by omega)]
        simp [show p / 8 ≠ 0 by omega]
      · have h3 : ¬ p / 8 < l.length + 1 := by omega
        simp [hl, h3]

end LeanDa

end

/-! ## LeanDA's challenge duplex -/

section

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common Common.Duplex
open scoped ENNReal

namespace LeanDa

/-- Byte `p` of a state. -/
def byteAt (y : KState) (p : ℕ) : UInt8 := y.toBytes.getD p 0

theorem toBytes_length (y : KState) : y.toBytes.length = 200 := by
  simp only [KState.toBytes, List.length_append, Vector.length_toList]

theorem getD_toBytes_lt32 (y : KState) (p : ℕ) (hp : p < 32) :
    y.toBytes.getD p 0 = y.1.1[p] := by
  rw [List.getD_eq_getElem?_getD, KState.toBytes, List.append_assoc,
    List.getElem?_append_left (by rw [Vector.length_toList]; exact hp),
    Vector.getElem?_toList, Vector.getElem?_eq_getElem hp, Option.getD_some]

theorem getD_toBytes_lt136 (y : KState) (p : ℕ) (hp : 32 ≤ p) (hp' : p < 136) :
    y.toBytes.getD p 0 = y.1.2[p - 32]'(by omega) := by
  rw [List.getD_eq_getElem?_getD, KState.toBytes, List.append_assoc,
    List.getElem?_append_right (by rw [Vector.length_toList]; exact hp), Vector.length_toList,
    List.getElem?_append_left (by rw [Vector.length_toList]; omega),
    Vector.getElem?_toList, Vector.getElem?_eq_getElem (by omega), Option.getD_some]

theorem getD_toBytes_lt200 (y : KState) (p : ℕ) (hp : 136 ≤ p) (hp' : p < 200) :
    y.toBytes.getD p 0 = y.2[p - 136]'(by omega) := by
  have hlen : (y.1.1.toList ++ y.1.2.toList).length = 136 := by
    rw [List.length_append, Vector.length_toList, Vector.length_toList]
  rw [List.getD_eq_getElem?_getD, KState.toBytes, List.getElem?_append_right (by rw [hlen]; exact hp),
    hlen, Vector.getElem?_toList, Vector.getElem?_eq_getElem (by omega), Option.getD_some]

theorem ofBytes_toBytes (y : KState) : KState.ofBytes y.toBytes = y := by
  obtain ⟨⟨a, b⟩, c⟩ := y
  refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> apply Vector.ext <;> intro i hi <;>
    simp only [KState.ofBytes, Vector.getElem_ofFn]
  · exact getD_toBytes_lt32 ((a, b), c) i hi
  · rw [getD_toBytes_lt136 ((a, b), c) (32 + i) (by omega) (by omega)]
    simp only [Nat.add_sub_cancel_left]
  · rw [getD_toBytes_lt200 ((a, b), c) (136 + i) (by omega) (by omega)]
    simp only [Nat.add_sub_cancel_left]

theorem toBytes_ofBytes {l : List UInt8} (hl : l.length = 200) : (KState.ofBytes l).toBytes = l := by
  apply List.ext_getElem (by rw [toBytes_length, hl])
  intro p h1 h2
  rw [toBytes_length] at h1
  rw [← List.getD_eq_getElem _ 0]
  by_cases hp : p < 32
  · rw [getD_toBytes_lt32 _ p hp]
    simp only [KState.ofBytes, Vector.getElem_ofFn]
    rw [List.getD_eq_getElem _ 0 h2]
  · by_cases hp' : p < 136
    · rw [getD_toBytes_lt136 _ p (by omega) hp']
      simp only [KState.ofBytes, Vector.getElem_ofFn]
      rw [show 32 + (p - 32) = p by omega, List.getD_eq_getElem _ 0 h2]
    · rw [getD_toBytes_lt200 _ p (by omega) (by omega)]
      simp only [KState.ofBytes, Vector.getElem_ofFn]
      rw [show 136 + (p - 136) = p by omega, List.getD_eq_getElem _ 0 h2]

/-- **A state is its 200 bytes.** -/
def bytesEquiv : KState ≃ (Fin 200 → UInt8) where
  toFun y i := byteAt y i
  invFun f := KState.ofBytes (List.ofFn f)
  left_inv y := by
    have : List.ofFn (fun i : Fin 200 ↦ byteAt y i) = y.toBytes :=
      List.ext_getElem (by rw [List.length_ofFn, toBytes_length]) fun p h1 h2 ↦ by
        rw [List.getElem_ofFn]; exact List.getD_eq_getElem _ 0 h2
    show KState.ofBytes (List.ofFn _) = y
    rw [this, ofBytes_toBytes]
  right_inv f := by
    funext i
    show byteAt (KState.ofBytes (List.ofFn f)) i = f i
    rw [byteAt, toBytes_ofBytes (List.length_ofFn), List.getD_eq_getElem _ 0
      (by rw [List.length_ofFn]; exact i.2), List.getElem_ofFn]

theorem length_lanesBytes (L : Lanes) :
    (L.toList.flatMap fun a ↦ (laneBytes a).toList).length = 200 := by
  rw [List.length_flatMap]
  simp only [Vector.length_toList]
  rw [List.map_const', List.sum_replicate, Vector.length_toList]
  rfl

theorem byteAt_lanesToState (L : Lanes) (p : ℕ) (hp : p < 200) :
    byteAt (lanesToState L) p = (laneBytes L[p / 8])[p % 8] := by
  rw [byteAt, lanesToState, toBytes_ofBytes (length_lanesBytes L), getD_flatMap_laneBytes]
  simp only [Vector.length_toList, show p / 8 < 25 by omega, ↓reduceDIte, Vector.getElem_toList]

theorem byteAt_stateToLanes (y : KState) (p : ℕ) (hp : p < 200) :
    (laneBytes (stateToLanes y)[p / 8])[p % 8] = byteAt y p := by
  simp only [stateToLanes, Vector.getElem_ofFn, Equiv.apply_symm_apply, byteAt]
  congr 1
  omega

theorem lanesToState_injective : Function.Injective lanesToState := by
  intro L L' h
  apply Vector.ext
  intro i hi
  apply laneBytes.injective
  apply Vector.ext
  intro j hj
  have h1 := byteAt_lanesToState L (8 * i + j) (by omega)
  have h2 := byteAt_lanesToState L' (8 * i + j) (by omega)
  have e1 : (8 * i + j) / 8 = i := by omega
  have e2 : (8 * i + j) % 8 = j := by omega
  rw [h] at h1
  have h3 := h1.symm.trans h2
  have h4 : ∀ (M : Lanes) (a b : ℕ) (ha : a = i) (hb : b = j) (h1 : a < 25) (h2 : b < 8),
      (laneBytes M[a])[b] = (laneBytes M[i])[j] := by
    intro M a b ha hb _ _; subst ha hb; rfl
  rw [h4 L _ _ e1 e2, h4 L' _ _ e1 e2] at h3
  exact h3

/-- Bytes `0 … m-1` and `m … m+k-1`. -/
def splitEquiv (m k : ℕ) : (Fin (m + k) → UInt8) ≃ (Fin m → UInt8) × (Fin k → UInt8) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl _)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

theorem splitEquiv_snd {m k : ℕ} (f : Fin (m + k) → UInt8) (j : Fin k) :
    (splitEquiv m k f).2 j = f (Fin.natAdd m j) := by
  simp [splitEquiv, Equiv.sumArrowEquivProdArrow, Equiv.arrowCongr]

/-- **The challenge of 24 bytes**: three lanes, the limbs of an element of `E`. -/
def limbsEquiv : (Fin 24 → UInt8) ≃ E :=
  (Equiv.arrowCongr (finProdFinEquiv (m := 3) (n := 8)).symm (Equiv.refl UInt8)).trans <|
    (Equiv.curry _ _ _).trans <|
      (Equiv.arrowCongr (Equiv.refl _)
        ((arrayVectorEquivFin UInt8 8).symm.trans laneBytes.symm)).trans
        (CompPoly.Extension.Ext.equivFn BF64.ext3Params).symm

/-- The rest of an answer after its challenge: bytes `24 … 127`, and the capacity, bytes
`128 … 199`. -/
abbrev DaW := (Fin 104 → UInt8) × (Fin 72 → UInt8)

/-- The capacity: bytes `128 … 199`, lanes `16 … 24`. -/
abbrev DaCp := Fin 72 → UInt8

/-- **An answer from its challenge and its rest.** -/
def daBuild : E × DaW ≃ KState :=
  (Equiv.prodCongr limbsEquiv.symm (splitEquiv 104 72).symm).trans
    ((splitEquiv 24 176).symm.trans bytesEquiv.symm)

theorem daBuild_symm_cap (y : KState) (j : Fin 72) :
    (daBuild.symm y).2.2 j = byteAt y (128 + j) := by
  simp only [daBuild, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map_snd]
  rw [splitEquiv_snd, splitEquiv_snd]
  show byteAt y (24 + (104 + (j : ℕ))) = _
  congr 1
  omega

/-- The scalars the root's words make (`membership_challenges`). -/
def rootScalars (root : Digest) : List (E × K) :=
  [(ofLimbs (word root 0) (word root 1) 0, dsObserve), (ofLimbs (word root 2) (word root 3) 0, dsObserve)]

/-- The initial state: the label's hash in lanes `0 … 3` (`Sponge.new`). -/
def daInit (iv : Digest) : KState := lanesToState (newInput iv (Vector.replicate 32 0))

/-- The state absorbing the root after the answer `y₀`. -/
def daFirst (root : Digest) (y : KState) : KState :=
  lanesToState (duplexInput ⟨stateToLanes y, rootScalars root⟩)

/-- The state of a sample after the answer `y`. -/
def daNext (y : KState) : KState := lanesToState (duplexInput ⟨stateToLanes y, []⟩)

theorem duplexInput_high (s : Sponge) (i : ℕ) (hi : 16 ≤ i) (hi' : i < 25) :
    (duplexInput s)[i] = s.state[i] := by
  simp only [duplexInput, Vector.getElem_ofFn, rateLanes, show ¬ i < 16 by omega, ↓reduceIte]
  rfl

theorem duplexInput_low (s : Sponge) (i : ℕ) (hi : i < 16) :
    (duplexInput s)[i] = (rateWords s.pending).getD i 0 := by
  simp only [duplexInput, Vector.getElem_ofFn, rateLanes, hi, ↓reduceIte]

/-- A duplexing keeps the capacity bytes. -/
theorem byteAt_duplexInput (y : KState) (pending : List (E × K)) (p : ℕ) (hp : 128 ≤ p)
    (hp' : p < 200) : byteAt (lanesToState (duplexInput ⟨stateToLanes y, pending⟩)) p = byteAt y p := by
  rw [byteAt_lanesToState _ p hp', ← byteAt_stateToLanes y p hp']
  have := duplexInput_high ⟨stateToLanes y, pending⟩ (p / 8) (by omega) (by omega)
  simp only at this
  rw [this]

theorem foldr_bytes_lt (l : List UInt8) : l.foldr (fun b acc ↦ b.toNat + 256 * acc) 0 < 256 ^ l.length := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldr_cons, List.length_cons, pow_succ]
    have := b.toNat_lt
    omega

theorem foldr_bytes_digit (l : List UInt8) (t : ℕ) (ht : t < l.length) :
    (l.foldr (fun b acc ↦ b.toNat + 256 * acc) 0 / 256 ^ t) % 256 = l[t].toNat := by
  induction l generalizing t with
  | nil => simp at ht
  | cons b l ih =>
    have hb := b.toNat_lt
    simp only [List.foldr_cons]
    rcases t with _ | t
    · simp only [pow_zero, Nat.div_one, List.getElem_cons_zero]
      omega
    · simp only [List.getElem_cons_succ]
      rw [pow_succ', ← Nat.div_div_eq_div_mul,
        show (b.toNat + 256 * l.foldr (fun b acc ↦ b.toNat + 256 * acc) 0) / 256 =
          l.foldr (fun b acc ↦ b.toNat + 256 * acc) 0 by omega]
      exact ih t (by simpa using ht)

/-- **Eight bytes read as a word and written back.** -/
theorem kBytes_ofBytes (l : List UInt8) (hl : l.length = 8) : kBytes (ofBytes l) = l := by
  have hN := foldr_bytes_lt l
  rw [hl] at hN
  apply List.ext_getElem (by simp [kBytes, hl])
  intro t h1 h2
  simp only [kBytes, List.getElem_map, List.getElem_range, ofBytes, K.ofBits,
    BF64.toBitVec_ofBitVec, BitVec.toNat_ofNat]
  apply UInt8.toNat_inj.mp
  rw [Nat.mod_eq_of_lt (by simpa using hN), Nat.shiftRight_eq_div_pow, pow_mul]
  simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat']
  exact foldr_bytes_digit l t h2

theorem word_bytes (d : Digest) (p : ℕ) (hp : p < 32) :
    d.toList[p]'(by simpa using hp) =
      (kBytes (word d (p / 8)))[p % 8]'(by simp [kBytes]; omega) := by
  have hlen : ((d.toList.drop (8 * (p / 8))).take 8).length = 8 := by
    simp only [List.length_take, List.length_drop, Vector.length_toList]; omega
  simp only [word]
  rw [List.getElem_of_eq (kBytes_ofBytes _ hlen), List.getElem_take, List.getElem_drop]
  congr 1
  omega

/-- **A digest is its four words.** -/
theorem eq_of_words {d d' : Digest} (h : ∀ i < 4, word d i = word d' i) : d = d' := by
  apply Vector.toList_inj.mp
  apply List.ext_getElem (by simp)
  intro p h1 h2
  have hp : p < 32 := by simpa using h1
  rw [word_bytes d p hp, word_bytes d' p hp]
  congr 2
  exact h (p / 8) (by omega)

theorem limb_ofLimbs_0 (a b c : K) : limb (ofLimbs a b c) 0 = a := rfl
theorem limb_ofLimbs_1 (a b c : K) : limb (ofLimbs a b c) 1 = b := rfl

theorem rateWords_rootScalars (root : Digest) :
    rateWords (rootScalars root) = [word root 0, word root 1, limb (ofLimbs (word root 0) (word root 1) 0) 2,
      dsObserve, word root 2, word root 3, limb (ofLimbs (word root 2) (word root 3) 0) 2, dsObserve] := by
  simp only [rateWords, rootScalars, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    limb_ofLimbs_0, limb_ofLimbs_1, List.cons_append, List.nil_append]

/-- **Absorbing different roots gives different states.** -/
theorem daFirst_injective (y : KState) : Function.Injective fun r ↦ daFirst r y := by
  intro r r' h
  have h' := lanesToState_injective h
  have hl : ∀ i (hi : i < 16), (rateWords (rootScalars r)).getD i 0 =
      (rateWords (rootScalars r')).getD i 0 := fun i hi ↦ by
    have := congrArg (fun L : Lanes ↦ L[i]) h'
    rwa [duplexInput_low _ i hi, duplexInput_low _ i hi] at this
  refine eq_of_words fun i hi ↦ ?_
  have h0 := hl 0 (by omega)
  have h1 := hl 1 (by omega)
  have h4 := hl 4 (by omega)
  have h5 := hl 5 (by omega)
  simp only [rateWords_rootScalars] at h0 h1 h4 h5
  interval_cases i
  · exact h0
  · exact h1
  · exact h4
  · exact h5

/-- The root a state absorbs after `y`, if any. -/
noncomputable def daDec (y x : KState) : Option Digest := by
  classical
  exact if h : ∃ r, daFirst r y = x then some h.choose else none

theorem daDec_iff (y x : KState) (r : Digest) : daDec y x = some r ↔ daFirst r y = x := by
  classical
  unfold daDec
  constructor
  · intro h
    split at h
    · next hx =>
      cases h
      exact hx.choose_spec
    · cases h
  · intro h
    have hx : ∃ r, daFirst r y = x := ⟨r, h⟩
    simp only [hx, ↓reduceDIte]
    congr 1
    exact daFirst_injective y (hx.choose_spec.trans h.symm)

/-- **LeanDA's challenges as a duplex**: `14` challenges of `E` from the label's hash and the
root, the capacity lanes `16 … 24` kept by every duplexing. -/
noncomputable def daDuplex : DuplexSpec (List UInt8) KDigest KState Digest E DaW DaCp 14 where
  label := label
  init := daInit
  first := daFirst
  next := daNext
  build := daBuild
  capW := Prod.snd
  dec := daDec
  dec_iff := daDec_iff
  n_pos := by norm_num
  cap_first r y := by
    funext j
    rw [daBuild_symm_cap, daBuild_symm_cap]
    exact byteAt_duplexInput y _ _ (by omega) (by omega)
  cap_next y := by
    funext j
    rw [daBuild_symm_cap, daBuild_symm_cap]
    exact byteAt_duplexInput y _ _ (by omega) (by omega)

end LeanDa

end

/-! ## Wagner's terms, for a uniformly random table of the hash -/

section

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common Common.Duplex PqDas
open scoped ENNReal

namespace LeanDa

/-- Wagner's oracles: coins and the challenges `G`, a random oracle of the roots. -/
abbrev WSpec := unifSpec + (Digest →ₒ Challenges)

/-- The challenges and `H`. -/
abbrev TSpec := (Digest →ₒ Challenges) + roSpec (List UInt8) KDigest

/-- A cache of `H`. -/
abbrev HCache := (roSpec (List UInt8) KDigest).QueryCache

/-- A short string: at most `2048` bytes, a cell's. -/
def shortP (a : List UInt8) : Prop := a.length ≤ 2048

instance : DecidablePred shortP := fun a ↦ inferInstanceAs (Decidable (a.length ≤ 2048))

noncomputable instance : Fintype {a : List UInt8 // shortP a} :=
  (List.finite_length_le (α := UInt8) 2048).fintype

/-- A table of `H` on the short strings. -/
abbrev HTab := {a : List UInt8 // shortP a} → KDigest

/-- **The hash of a table**: the table's answer on a short string, `default` on a long one. -/
def Hh (h : HTab) (a : List UInt8) : Digest := if ha : shortP a then h ⟨a, ha⟩ else default

/-- **`H` from a table, in Wagner's world**: the table on short strings, lazily sampled on long
ones (the state), the challenges forwarded to Wagner's random oracle. -/
noncomputable def tImpl (h : HTab) : QueryImpl (unifSpec + TSpec) (StateT HCache (OracleComp WSpec))
  | .inl k => StateT.mk fun c ↦ (·, c) <$> liftM (WSpec.query (.inl k))
  | .inr (.inl d) => StateT.mk fun c ↦ (·, c) <$> liftM (WSpec.query (.inr d))
  | .inr (.inr a) =>
      if ha : shortP a then StateT.mk fun c ↦ pure (h ⟨a, ha⟩, c)
      else StateT.mk fun c ↦ liftM (((roSpec (List UInt8) KDigest).randomOracle a).run c)

/-- The simulated world's oracles from a table `h` of `H`. -/
noncomputable def phiG (h : HTab) :
    QueryImpl (unifSpec + GSpec (List UInt8) KDigest Digest E 14) (StateT HCache (OracleComp WSpec)) :=
  tImpl h ∘ₛ (swapImpl ∘ₛ toV)

section Adversary

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Digest × Challenges → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof rel)

/-- The crs the adversary runs with: the given one when the setup can output it, else one it
can (the bound on the adversary's queries holds for these). -/
noncomputable def fixCrs (crs : Crs) : Crs := by
  classical
  exact if crs ∈ support ps.setup then crs else (support_nonempty ps.setup).some

/-- The adversary in the simulated world: `H` queried at the label, then the RPM adversary with
its permutation queries simulated from `H` and `F`, `F` answered by the duplex lemma's simulator. -/
noncomputable def advSim (A : CodeBindingAdvRpm r Crs Proof) (crs : Crs) :
    OracleComp (unifSpec + GSpec (List UInt8) KDigest Digest E 14)
      ((Digest × Proof) × List (Fin (r * 128) × Cell × Opening)) :=
  (simulateQ (simImpl daDuplex hP gaP) (hQ (St := KState) daDuplex.label >>= fun _ ↦
    advS2 keccakPadding KState.zero (A ((), crs)))).run' SimSt.init

/-- **Wagner's adversary for the table `h` of `H`**: the simulated adversary, with `H` answered
from `h` on short strings and lazily on long ones, and the challenges `G` from Wagner's random
oracle. -/
noncomputable def advH (A : CodeBindingAdvRpm r Crs Proof) (h : HTab) :
    ErasureCodeCommitment.CodeBindingAdv (OracleComp WSpec) Cell (r * 128) (Unit × Crs)
      (Digest × Proof) Opening :=
  fun ck ↦ (simulateQ (phiG h) (advSim r A (fixCrs r ps ck.2))).run' ∅

end Adversary

section Verify

variable (r : ℕ) {Crs Proof : Type}

/-- The argument for the relation of a hash `H`, from an argument for any relation. -/
def argH {rel : Unit × Digest × Challenges → (Fin (r * 128) → Cell) → Bool}
    (ps : Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof rel)
    (H : List UInt8 → Digest) : WArgument r H Crs Proof :=
  ⟨ps.setup, ps.prove, ps.verify⟩

end Verify

section Final

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Digest × Challenges → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof rel)

/-- Wagner's knowledge-soundness experiment for the table `h`: his reduction `ksReduction` from
`advH h`, against the argument `ps` for the relation with the hash `Hh h`. -/
noncomputable def ksExpH
    (ext : Nark.Extractor (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof)
    (A : CodeBindingAdvRpm r Crs Proof) (h : HTab) : ProbComp Bool :=
  (argH r ps (Hh h)).knowledgeSoundnessExp ext (ksReduction (merkleVC r (Hh h)) (advH r ps A h))

/-- The collision experiment of `Hh h` against Wagner's weak-position-binding reduction from
`advH h`, through `merkleCollider`. -/
noncomputable def wpbCollExpH [NeZero r]
    (ext : Nark.Extractor (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof)
    (A : CodeBindingAdvRpm r Crs Proof) (h : HTab) : ProbComp Bool :=
  hashCollisionExp (Hh h) (merkleCollider r (Hh h)
    ((wpbReduction (argH r ps (Hh h)) ext (advH r ps A h)).toPosBindingAdv (merkleVC r (Hh h))))

/-- The collision experiment of `Hh h` against Wagner's forking reduction from `advH h` (at most
`Q + 1` queries of the challenges), through `merkleCollider`. -/
noncomputable def forkCollExpH [NeZero r]
    (ext : Nark.Extractor (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof)
    (A : CodeBindingAdvRpm r Crs Proof) (Q : ℕ) (h : HTab) : ProbComp Bool :=
  hashCollisionExp (Hh h) (merkleCollider r (Hh h)
    ((CommittedSoundness.forkCollisionReduction (code r) (merkleVC r (Hh h)) (checker r)
      (csReduction (argH r ps (Hh h)) ext (advH r ps A h)) (Q + 1)).toPosBindingAdv
        (merkleVC r (Hh h))))

end Final

end LeanDa

end
