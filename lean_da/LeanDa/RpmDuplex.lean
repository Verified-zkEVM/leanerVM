import LeanDa.RpmScheme
import Common.Duplex.Vec
import Common.Rerun

/-!
# LeanDA's challenges as a duplex

The challenges' sponge (`membershipChallengesM`) over the direct calls `F` of the two-oracle model
is a duplex challenge derivation in the sense of `Common.Duplex` (`daDuplex`): the initial state
is the label's hash in lanes `0 … 3` (`Sponge.new`), absorbing the root writes its words and tags
over the rate (`first`), a later sample writes zeros over the rate (`next`), and a challenge is
the three lanes `0 … 2` of an answer (`out`). Every one of these keeps lanes `16 … 24`, the bytes
`128 … 199` of the state (`cap_first`, `cap_next`), which the duplex lemma calls the capacity:
`72` bytes, so a uniform state has a given capacity with probability `2^-576` (`daDuplex_cap`).
Over `F`, the challenges are the duplex's (`membershipChallengesM_eq_chalP`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common Common.Duplex
open scoped ENNReal

namespace LeanDa

/-! ## The state as bytes -/

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

theorem bytesEquiv_apply (y : KState) (i : Fin 200) : bytesEquiv y i = byteAt y i := rfl

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

/-! ## Splitting the bytes -/

/-- Bytes `0 … m-1` and `m … m+k-1`. -/
def splitEquiv (m k : ℕ) : (Fin (m + k) → UInt8) ≃ (Fin m → UInt8) × (Fin k → UInt8) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl _)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

theorem splitEquiv_fst {m k : ℕ} (f : Fin (m + k) → UInt8) (j : Fin m) :
    (splitEquiv m k f).1 j = f (Fin.castAdd k j) := by
  simp [splitEquiv, Equiv.sumArrowEquivProdArrow, Equiv.arrowCongr]

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

theorem daBuild_symm_fst (y : KState) :
    (daBuild.symm y).1 = limbsEquiv fun j : Fin 24 ↦ byteAt y j := by
  simp only [daBuild, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map_fst]
  congr 1

theorem daBuild_symm_cap (y : KState) (j : Fin 72) :
    (daBuild.symm y).2.2 j = byteAt y (128 + j) := by
  simp only [daBuild, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map_snd]
  rw [splitEquiv_snd, splitEquiv_snd]
  show byteAt y (24 + (104 + (j : ℕ))) = _
  congr 1
  omega

/-! ## The duplex -/

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

/-! ## The root's words determine the root -/

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

/-! ## The challenge of an answer -/

theorem limbsEquiv_apply (f : Fin 24 → UInt8) :
    limbsEquiv f = CompPoly.Extension.Ext.ofFn (P := BF64.ext3Params) fun a : Fin 3 ↦
      laneBytes.symm (Vector.ofFn fun b : Fin 8 ↦ f (finProdFinEquiv (a, b))) := rfl

theorem ofFn_eq_ofLimbs (g : Fin 3 → K) :
    (CompPoly.Extension.Ext.ofFn (P := BF64.ext3Params) g : E) = ofLimbs (g 0) (g 1) (g 2) := by
  simp only [CompPoly.Extension.Ext.ofFn, ofLimbs]
  congr 1

/-- **The challenge an answer carries is its lanes `0 … 2`** (`Sponge.sample`). -/
theorem daBuild_symm_fst_eq (y : KState) :
    (daBuild.symm y).1 =
      ofLimbs (stateToLanes y)[0] (stateToLanes y)[1] (stateToLanes y)[2] := by
  rw [daBuild_symm_fst, limbsEquiv_apply]
  have key : ∀ a : Fin 3, laneBytes.symm (Vector.ofFn fun b : Fin 8 ↦
      byteAt y (finProdFinEquiv (a, b) : ℕ)) = (stateToLanes y)[(a : ℕ)] := by
    intro a
    simp only [stateToLanes, Vector.getElem_ofFn, byteAt]
    refine congrArg laneBytes.symm ?_
    apply Vector.ext
    intro b hb
    simp only [Vector.getElem_ofFn, finProdFinEquiv_apply_val]
    congr 1
    ring
  rw [ofFn_eq_ofLimbs, key 0, key 1, key 2]
  rfl

/-! ## LeanDA's duplex -/

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

theorem card_bytes (k : ℕ) : Fintype.card (Fin k → UInt8) = 256 ^ k := by
  rw [Fintype.card_fun, card_uInt8, Fintype.card_fin]

/-- **A capacity is hit with probability `2^-576`.** -/
theorem daDuplex_cap (c : DaCp) :
    Pr{let w ← ($ᵗ DaW : ProbComp DaW)}[daDuplex.capW w = c] ≤ (2 ^ 576 : ℝ≥0∞)⁻¹ := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  have hf : (Finset.univ.filter fun w : DaW ↦ daDuplex.capW w = c) =
      (Finset.univ : Finset (Fin 104 → UInt8)) ×ˢ {c} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton]
    exact Iff.rfl
  simp only [hf, Finset.card_product, Finset.card_singleton, mul_one, Finset.card_univ, Fintype.card_prod, card_bytes, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have h256 : (256 : ℝ≥0∞) ^ 72 = 2 ^ 576 := by
    rw [show (256 : ℝ≥0∞) = 2 ^ 8 by norm_num, ← pow_mul]
  have ha : (256 : ℝ≥0∞) ^ 104 ≠ 0 := pow_ne_zero _ (by norm_num)
  have ha' : (256 : ℝ≥0∞) ^ 104 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  refine le_of_eq ?_
  rw [h256, ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl ha) (Or.inl ha'),
    mul_comm ((256 : ℝ≥0∞) ^ 104)⁻¹, mul_assoc, ENNReal.inv_mul_cancel ha ha', mul_one]

/-! ## The challenges over `F` are the duplex's -/

theorem daDuplex_out (y : KState) :
    daDuplex.out y = ofLimbs (stateToLanes y)[0] (stateToLanes y)[1] (stateToLanes y)[2] :=
  daBuild_symm_fst_eq y

theorem samplesM_eq_chainP (k : ℕ) (y : KState) :
    Sponge.samplesM pR k ⟨stateToLanes y, []⟩ = chainP daDuplex k y := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih =>
    simp only [Sponge.samplesM, Sponge.sampleM, Sponge.duplexM, pR, lanePerm, chainP,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine bind_congr fun y' ↦ ?_
    rw [ih, daDuplex_out]

/-- **Over `F`, LeanDA's challenges are the duplex's.** -/
theorem membershipChallengesM_eq_chalP (root : Digest) :
    membershipChallengesM hR pR root = chalP daDuplex root := by
  simp only [membershipChallengesM, Sponge.fromLabelM, Sponge.newM, Sponge.observeM,
    Sponge.absorbM, pR, lanePerm, chalP, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  refine bind_congr fun iv ↦ bind_congr fun y₀ ↦ ?_
  have h0 : ¬ ([] : List (E × K)).length = rateScalars := by simp [rateScalars]
  simp only [h0, ↓reduceIte, pure_bind, List.nil_append]
  show Sponge.samplesM pR (13 + 1) ⟨stateToLanes y₀, rootScalars root⟩ = _
  rw [Sponge.samplesM]
  simp only [Sponge.sampleM, Sponge.duplexM, pR, lanePerm,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  refine bind_congr fun y₁ ↦ ?_
  rw [samplesM_eq_chainP, daDuplex_out]

end LeanDa
