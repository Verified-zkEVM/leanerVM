import SphincsFors.BridgeSignerPost
import SphincsFors.BridgeVirtual
import SphincsFors.BridgeImplication

/-! The FORS potential of the lazy run. Every cached landed message-randomizer pair is an item;
the unsigned ones are candidates whose value is the virtual-future forecast of their witness
count; the remaining budget may create future pairs, each paying the excess forecast of a new
pair. This file defines the potential and proves the facts about fresh pairs, ordinary queries
and signing calls that the one-coin potentials of `BridgeForsPotentialOnce` and `BridgeForsGeneric`
build on. -/

open OracleComp OracleSpec ENNReal

namespace SphincsFors.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

/-- A message and a randomizer. -/
abbrev Pair := Message × Randomness

abbrev State := DebtState HashInput HashOutput Coordinate

instance : Inhabited View := ⟨(⟨0, Nat.two_pow_pos _⟩, fun _ => ⟨0, Nat.two_pow_pos _⟩)⟩

omit [Params] in
theorem payload_pair_injective (root : Digest) {m m' : Message} {ρ ρ' : Randomness}
    (h : messageDigestPayload root m ρ = messageDigestPayload root m' ρ') : m = m' ∧ ρ = ρ' := by
  have hparts := List.append_inj h (by simp [bytesLE_length])
  exact ⟨bytesLE_injective hparts.1, bytesLE_injective hparts.2⟩

section Defs

variable (parameter : PublicParameter) (data : PublicData)

/-- Block `call` of a pair. -/
abbrev pblk (p : Pair) (call : Fin 2) : HashInput := blk parameter data p.1 p.2 call

omit [Params] in
theorem pblk_injective {p q : Pair} {call call' : Fin 2}
    (h : pblk parameter data p call = pblk parameter data q call') : p = q ∧ call = call' := by
  obtain ⟨hfields, -, hpayload⟩ := tweakableInput_injective h
  obtain ⟨hm, hρ⟩ := payload_pair_injective data.root hpayload
  refine ⟨Prod.ext hm hρ, ?_⟩
  have := congrArg TweakFields.hi hfields
  simp only [hashDomainFields, tweakFields] at this
  exact Fin.ext (by
    have h1 := call.isLt
    have h2 := call'.isLt
    have := congrArg BitVec.toNat this
    simp at this
    omega)

omit [Params] in
theorem pblk_ne_of_ne {p q : Pair} (h : p ≠ q) (call call' : Fin 2) :
    pblk parameter data p call ≠ pblk parameter data q call' := fun heq =>
  h (pblk_injective parameter data heq).1

omit [Params] in
theorem pblk_ne_call (p : Pair) : pblk parameter data p 0 ≠ pblk parameter data p 1 := fun heq =>
  absurd (pblk_injective parameter data heq).2 (by decide)

/-- The kept view of a pair whose two blocks are cached. -/
noncomputable def pview (s : State) (p : Pair) : View :=
  (s.cache (pblk parameter data p 0)).elim default fun u0 =>
    (s.cache (pblk parameter data p 1)).elim default fun u1 => viewOf u0 u1

/-- Block 0 of the pair is cached and lands. -/
def LandedIn (s : State) (p : Pair) : Prop :=
  ∃ u0, s.cache (pblk parameter data p 0) = some u0 ∧ Landed parameter (blockIndex u0)

/-- The items are exactly the landed pairs; landed pairs have both blocks; no pair has only
its second block. -/
structure PInv (s : State) (P : List Pair) : Prop where
  nodup : P.Nodup
  mem : ∀ p, p ∈ P ↔ LandedIn parameter data s p
  second : ∀ p, LandedIn parameter data s p → s.cache (pblk parameter data p 1) ≠ none
  first : ∀ p, s.cache (pblk parameter data p 0) = none → s.cache (pblk parameter data p 1) = none

/-- The local index of a leaf index. -/
def localIdx (i : Index) : Fin (2 ^ subtreeHeight) := ⟨i.val % 2 ^ subtreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

theorem localDigestView_fst (digest : MessageDigest) :
    (Lifetime.localDigestView digest).1 = localIdx (digestIndex digest) := rfl

theorem localDigestView_snd (digest : MessageDigest) :
    (Lifetime.localDigestView digest).2 = digestLeaves digest := rfl

/-- The disclosed views account for every revealed FORS secret. -/
def DInv (R : List Coordinate) (d : Multiset View) : Prop :=
  ∀ i t l, Coordinate.ftsSecret i t l ∈ R → ∃ v ∈ d, v.1 = localIdx i ∧ v.2 t = l

/-- The pair was never signed in the log. -/
def Unsigned (L : QueryLog SigningSpec) (p : Pair) : Prop :=
  ∀ entry ∈ L, ∀ sig, entry.2 = some sig → ¬(entry.1 = p.1 ∧ sig.randomness = p.2)

variable (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

/-- The excess of the price over the baseline. -/
noncomputable def excess (D : Multiset View) : ℝ≥0∞ := price D - b0

/-- Share of kept views at failing indices. -/
noncomputable def failMass : ℝ≥0∞ :=
  freshAvg Finset.univ fun v : View => if v.1 ∈ Fail then 1 else 0

/-- Witness count of a target as a value. -/
noncomputable def witnessFn (v : View) (D : Multiset View) : ℝ≥0∞ := (witness v D : ℝ≥0∞)

/-- Views of a list of pairs. -/
noncomputable def items (s : State) (P : List Pair) : List View := P.map (pview parameter data s)

/-- The forecast of a candidate. -/
noncomputable def candValue (s : State) (P : List Pair) (d : Multiset View) (n k : ℕ) (p : Pair) : ℝ≥0∞ :=
  creations Finset.univ landing (fun I => virtual Finset.univ wbar (witnessFn (pview parameter data s p)) n I d) k
    (items parameter data s (P.erase p))

/-- The excess forecast of a new pair. -/
noncomputable def hValue (s : State) (P : List Pair) (d : Multiset View) (n k : ℕ) : ℝ≥0∞ :=
  creations Finset.univ landing (fun I => virtual Finset.univ wbar (excess b0) n I d) k (items parameter data s P)

/-- The value of a candidate: one at a failing index, its forecast otherwise; zero once signed. -/
noncomputable def cand (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ)
    (p : Pair) : ℝ≥0∞ :=
  if Unsigned L p then (if (pview parameter data s p).1 ∈ Fail then 1 else candValue parameter data wbar s P d n k p)
  else 0

/-- The potential without the hit and transcript tests. -/
noncomputable def core (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ) :
    ℝ≥0∞ :=
  (P.map (cand parameter data wbar Fail s P L d n k)).sum +
    k * (hValue parameter data wbar b0 s P d n k + failMass Fail) + n * failMass Fail

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)

/-- **The potential.** -/
noncomputable def pot (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (k : ℕ) : ℝ≥0∞ :=
  if Realized tg initial s ∨ signatureLimit < L.length then 0
  else core parameter data wbar b0 Fail s P L d (signatureLimit - L.length) k

end Defs

/-! ### The law of a fresh pair -/

section Mean

theorem landing_le_one : landing ≤ 1 := by
  unfold landing
  exact ENNReal.inv_le_one.2 (by exact_mod_cast Nat.one_le_two_pow)

theorem unlanded_mass (parameter : PublicParameter) :
    ∑' u0, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u0] *
      (if Landed parameter (blockIndex u0) then (0 : ℝ≥0∞) else 1) = 1 - landing := by
  have htot : (∑' u0, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u0] *
      (if Landed parameter (blockIndex u0) then (1 : ℝ≥0∞) else 0)) +
    ∑' u0, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u0] *
      (if Landed parameter (blockIndex u0) then (0 : ℝ≥0∞) else 1) = 1 := by
    rw [← ENNReal.tsum_add]
    calc _ = ∑' u0, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u0] := by
          refine tsum_congr fun u0 => ?_
          split_ifs <;> simp [-SampleableType.prEvent_uniformSample]
      _ = 1 := OracleComp.tsum_prEvent_eq_one _
  rw [landed_mass parameter] at htot
  exact ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top (by rw [add_comm]; exact htot)

/-- **Mean over a fresh pair.** -/
theorem pair_mean (parameter : PublicParameter) (F : View → ℝ≥0∞) (C : ℝ≥0∞) :
    ∑' u0, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u0] *
      ∑' u1, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u1] *
        (if Landed parameter (blockIndex u0) then F (viewOf u0 u1) else C) =
      landing * freshAvg Finset.univ F + (1 - landing) * C := by
  have hsplit : ∀ u0, ∑' u1, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u1] *
      (if Landed parameter (blockIndex u0) then F (viewOf u0 u1) else C) =
      (∑' u1, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u1] *
        (if Landed parameter (blockIndex u0) then F (Lifetime.localDigestView (truncateMessageDigest u0 u1)) else 0)) +
      C * (if Landed parameter (blockIndex u0) then 0 else 1) := by
    intro u0
    split_ifs
    · simp [-SampleableType.prEvent_uniformSample, viewOf]
    · simp only [mul_zero, tsum_zero, zero_add, mul_one]
      rw [ENNReal.tsum_mul_right, OracleComp.tsum_prEvent_eq_one _, one_mul]
  simp only [hsplit, mul_add, ENNReal.tsum_add]
  rw [fresh_view_mean parameter F]
  congr 1
  simp only [mul_left_comm _ C, ENNReal.tsum_mul_left]
  rw [unlanded_mass parameter, mul_comm]

end Mean

/-! ### Expectation over the two blocks of a fresh pair -/

section PairE

/-- Expectation over two fresh blocks. -/
noncomputable def pairE (F : HashOutput → HashOutput → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' u0, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u0] *
    ∑' u1, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u1] * F u0 u1

omit [Params] in
theorem pairE_add (F G : HashOutput → HashOutput → ℝ≥0∞) :
    pairE (fun a b => F a b + G a b) = pairE F + pairE G := by
  simp only [pairE, mul_add, ENNReal.tsum_add]

omit [Params] in
theorem pairE_const (c : ℝ≥0∞) : pairE (fun _ _ => c) = c := by
  simp only [pairE, ENNReal.tsum_mul_right, OracleComp.tsum_prEvent_eq_one _, one_mul]

end PairE

/-! ### A new pair -/

section NewPair

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

/-- Both blocks of a new pair stored. -/
noncomputable def withPair (s : State) (p : Pair) (u0 u1 : HashOutput) : State :=
  (s.store (pblk parameter data p 0) u0).store (pblk parameter data p 1) u1

/-- The items after a new pair. -/
noncomputable def addPair (P : List Pair) (p : Pair) (u0 : HashOutput) : List Pair :=
  if Landed parameter (blockIndex u0) then p :: P else P

variable {parameter data}

omit [Params] in
theorem withPair_other (s : State) (p : Pair) (u0 u1 : HashOutput) (x : HashInput)
    (h0 : x ≠ pblk parameter data p 0) (h1 : x ≠ pblk parameter data p 1) :
    (withPair parameter data s p u0 u1).cache x = s.cache x := by
  unfold withPair
  rw [store_cache_ne _ _ _ h1, store_cache_ne _ _ _ h0]

omit [Params] in
theorem withPair_zero (s : State) (p : Pair) (u0 u1 : HashOutput) :
    (withPair parameter data s p u0 u1).cache (pblk parameter data p 0) = some u0 := by
  unfold withPair
  rw [store_cache_ne _ _ _ (pblk_ne_call parameter data p)]
  simp [DebtState.store]

omit [Params] in
theorem withPair_one (s : State) (p : Pair) (u0 u1 : HashOutput) :
    (withPair parameter data s p u0 u1).cache (pblk parameter data p 1) = some u1 := by
  unfold withPair
  simp [DebtState.store]

omit [Params] in
theorem withPair_other_pair (s : State) (p q : Pair) (hq : q ≠ p) (u0 u1 : HashOutput) (call : Fin 2) :
    (withPair parameter data s p u0 u1).cache (pblk parameter data q call) = s.cache (pblk parameter data q call) :=
  withPair_other s p u0 u1 _ (pblk_ne_of_ne parameter data hq _ _) (pblk_ne_of_ne parameter data hq _ _)

theorem pview_withPair_other (s : State) (p q : Pair) (hq : q ≠ p) (u0 u1 : HashOutput) :
    pview parameter data (withPair parameter data s p u0 u1) q = pview parameter data s q := by
  simp only [pview, withPair_other_pair s p q hq]

theorem not_mem_of_fresh {s : State} {P : List Pair} (hP : PInv parameter data s P) {p : Pair}
    (hp0 : s.cache (pblk parameter data p 0) = none) : p ∉ P := by
  intro hp
  obtain ⟨u, hu, _⟩ := (hP.mem p).1 hp
  rw [hp0] at hu
  cases hu

end NewPair

/-! ### Properties of the forecast -/

section NewPairCore

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

theorem excess_props (hb0 : b0 ≠ ⊤) :
    Monotone' (excess b0) ∧ Supermodular (excess b0) ∧ ∀ D, excess b0 D ≠ ⊤ :=
  ⟨excess_mono price_mono b0, excess_super price_mono price_super price_ne_top b0 hb0,
    fun D => ne_top_of_le_ne_top (price_ne_top D) tsub_le_self⟩

theorem witness_props (v : View) :
    Monotone' (witnessFn v) ∧ Supermodular (witnessFn v) ∧ ∀ D, witnessFn v D ≠ ⊤ :=
  ⟨witness_mono v, witness_super v, fun _ => ENNReal.natCast_ne_top _⟩

theorem virtual_cons_le (hw : wbar ≤ 1) {f : Multiset View → ℝ≥0∞}
    (hf : Monotone' f ∧ Supermodular f ∧ ∀ D, f D ≠ ⊤) (n : ℕ) (d : Multiset View) :
    ∀ v I, virtual Finset.univ wbar f n I d ≤ virtual Finset.univ wbar f n (v :: I) d :=
  fun v I => virtual_le_cons Finset.univ_nonempty hw hf.1 hf.2.1 hf.2.2 n I v d

theorem virtual_perm' {f : Multiset View → ℝ≥0∞} (n : ℕ) (d : Multiset View) :
    ∀ I I' : List View, I.Perm I' → virtual Finset.univ wbar f n I d = virtual Finset.univ wbar f n I' d :=
  fun _ _ h => virtual_perm n h d

end NewPairCore

/-! ### Order and congruence of the potential -/

section Order

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

variable {parameter data}

theorem candValue_mono (hw : wbar ≤ 1) (s : State) (P : List Pair) (d : Multiset View) (n : ℕ) {k k' : ℕ}
    (hk : k ≤ k') (p : Pair) :
    candValue parameter data wbar s P d n k p ≤ candValue parameter data wbar s P d n k' p :=
  creations_mono_count Finset.univ_nonempty landing_le_one
    (virtual_cons_le wbar hw (witness_props _) n d) (virtual_perm' wbar n d) hk _

theorem hValue_mono (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (s : State) (P : List Pair) (d : Multiset View) (n : ℕ)
    {k k' : ℕ} (hk : k ≤ k') :
    hValue parameter data wbar b0 s P d n k ≤ hValue parameter data wbar b0 s P d n k' :=
  creations_mono_count Finset.univ_nonempty landing_le_one
    (virtual_cons_le wbar hw (excess_props b0 hb0) n d) (virtual_perm' wbar n d) hk _

theorem core_mono (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (s : State) (P : List Pair) (L : QueryLog SigningSpec)
    (d : Multiset View) (n : ℕ) {k k' : ℕ} (hk : k ≤ k') :
    core parameter data wbar b0 Fail s P L d n k ≤ core parameter data wbar b0 Fail s P L d n k' := by
  unfold core
  refine add_le_add (add_le_add (List.sum_le_sum fun q _ => ?_) ?_) le_rfl
  · unfold cand
    split_ifs
    · exact le_rfl
    · exact candValue_mono wbar hw s P d n hk q
    · exact le_rfl
  · exact mul_le_mul' (by exact_mod_cast hk) (add_le_add (hValue_mono wbar b0 hw hb0 s P d n hk) le_rfl)

end Order

/-! ### Counting cached randomizers -/

section Count

variable {parameter : PublicParameter} {data : PublicData}

omit [Params] in
theorem blk_zero_injective (m : Message) : Function.Injective fun ρ : Randomness => blk parameter data m ρ 0 := by
  intro ρ ρ' h
  by_contra hne
  exact blk_ne_of_ne parameter data m ρ ρ' 0 0 (Or.inl hne) h

variable (parameter data) in
/-- Block-0 inputs of a message. -/
noncomputable def zeroInputs (m : Message) : Finset HashInput :=
  Finset.univ.image fun ρ => blk parameter data m ρ 0

omit [Params] in
theorem cachedCount_eq (m : Message) (s : State) :
    cachedCount parameter data m s = ((zeroInputs parameter data m).filter fun x => s.cache x ≠ none).card := by
  unfold cachedCount zeroInputs
  rw [Finset.filter_image, Finset.card_image_of_injective _ (blk_zero_injective m)]

omit [Params] in
theorem card_filter_store_of_not_mem (T : Finset HashInput) (s : State) (x : HashInput) (hx : x ∉ T)
    (u : HashOutput) :
    (T.filter fun y => (s.store x u).cache y ≠ none).card = (T.filter fun y => s.cache y ≠ none).card := by
  congr 1
  refine Finset.filter_congr fun y hy => ?_
  rw [store_cache_ne s x y (fun h => hx (h ▸ hy)) u]

end Count

/-! ### Paid programs -/

section Good

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot : ℕ) {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- The final value: a FORS cover with no decided hit. -/
noncomputable def finalValue (R : List Coordinate) (out : Run HashInput Coordinate HiddenBridge.Outcome × State) :
    ℝ≥0∞ :=
  out.1.1.elim 0 fun outcome =>
    if HiddenBridge.ForsCover parameter data.root outcome (R ++ out.1.2.1) out.2.cache ∧ ¬Realized tg initial out.2
    then 1 else 0

/-- Cached block-0 entries of every message, plus the remaining budget, stay bounded. -/
def CountInv (s : State) (budget : ℕ) : Prop :=
  ∀ m : Message, cachedCount parameter data m s + budget ≤ Qtot

/-- A program whose final value is paid by the potential and the baseline payments. -/
def Good (L : QueryLog SigningSpec) (prog : OracleComp CostSpec HiddenBridge.Outcome) : Prop :=
  ∀ budget (s : State) (P : List Pair) (d : Multiset View) (R : List Coordinate),
    Prepared initial s → PInv parameter data s P → DInv R d → CountInv parameter data Qtot s budget →
      ∑' out, Pr{let x ← interp tg initial model prog budget s}[x = out] * finalValue parameter data tg initial R out ≤
        pot parameter data wbar b0 Fail tg initial s P L d budget + b0 * expectedFlagged tg initial model prog budget s

end Good

/-! ### One ordinary query -/

section Ordinary

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

omit [Params] in
theorem readOutside_cache_ne (x : HashInput) (s : State) :
    ∀ r ∈ support (readOutside x s), ∀ y, y ≠ x → r.2.cache y = s.cache y := by
  intro r hr y hy
  rcases readOutside_support x s r hr with h | ⟨_, h⟩
  · rw [h]
  · rw [h]; exact store_cache_ne s x y hy r.1

theorem forsCover_mono (parameter : PublicParameter) (root : Digest) (outcome : HiddenBridge.Outcome)
    (reveals : List Coordinate) {c c' : QueryCache HashSpec} (h : ∀ x v, c x = some v → c' x = some v)
    (hc : HiddenBridge.ForsCover parameter root outcome reveals c) :
    HiddenBridge.ForsCover parameter root outcome reveals c' := by
  obtain ⟨hvalid, digest, hdig, hrest⟩ := hc
  refine ⟨hvalid, digest, ?_, hrest⟩
  unfold HiddenBridge.cachedDigest at hdig ⊢
  cases h0 : c (tweakableHashInput parameter (.message 0)
      (messageDigestPayload root outcome.1.message outcome.1.signature.randomness)) with
  | none => rw [h0] at hdig; cases hdig
  | some a =>
      cases h1 : c (tweakableHashInput parameter (.message 1)
          (messageDigestPayload root outcome.1.message outcome.1.signature.randomness)) with
      | none => rw [h0, h1] at hdig; cases hdig
      | some b =>
          rw [h0, h1] at hdig
          rw [h _ _ h0, h _ _ h1]
          exact hdig

variable (parameter : PublicParameter) (data : PublicData)

omit [Params] in
theorem interp_mass {α : Type} (computation : OracleComp CostSpec α) (budget : ℕ) (s : State) :
    ∑' out, Pr{let x ← interp tg initial model computation budget s}[x = out] = 1 :=
  OracleComp.tsum_prEvent_eq_one _

end Ordinary

/-! ### Leaves and verification -/

section Leaf

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot : ℕ) {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

end Leaf

/-! ### What a signing call adds -/

/-- The pairs that are not excluded. -/
noncomputable def others (excl : Pair → Prop) (P : List Pair) : List Pair := P.filter fun q => ¬excl q

section SignDefs

variable (parameter : PublicParameter) (data : PublicData) (m : Message) (s : State)

/-- Randomizers of the message whose block 0 is new and lands. -/
noncomputable def newRand (s' : State) : Finset Randomness :=
  Finset.univ.filter fun ρ => s.cache (blk parameter data m ρ 0) = none ∧ LandedIn parameter data s' (m, ρ)

/-- Pairs created by a signing call. -/
noncomputable def newPairs (s' : State) : List Pair := (newRand parameter data m s s').toList.map fun ρ => (m, ρ)

/-- Disclosure of an existing pair signed by the call. -/
noncomputable def poolDisc (out : Run HashInput Coordinate (Option Signature) × State) : Multiset View :=
  out.1.1.elim 0 fun r => r.elim 0 fun sig =>
    if s.cache (blk parameter data m sig.randomness 0) = none then 0
    else {pview parameter data out.2 (m, sig.randomness)}

/-- Disclosures after a signing call. -/
noncomputable def discAfter (d : Multiset View) (out : Run HashInput Coordinate (Option Signature) × State) :
    Multiset View :=
  d + ((newPairs parameter data m s out.2).map (pview parameter data out.2) : Multiset View) +
    poolDisc parameter data m s out

theorem newPairs_nodup (s' : State) : (newPairs parameter data m s s').Nodup :=
  (Finset.nodup_toList _).map fun _ _ h => (Prod.ext_iff.1 h).2

theorem mem_newPairs {s' : State} {q : Pair} :
    q ∈ newPairs parameter data m s s' ↔ q.1 = m ∧ s.cache (pblk parameter data q 0) = none ∧
      LandedIn parameter data s' q := by
  unfold newPairs newRand
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ρ, ⟨h0, hl⟩, rfl⟩
    exact ⟨rfl, h0, hl⟩
  · rintro ⟨hm, h0, hl⟩
    exact ⟨q.2, ⟨by rw [← hm]; exact h0, by rw [← hm]; exact hl⟩, by rw [← hm]⟩

end SignDefs

/-! ### The three shapes of a completed signing call -/

section SignShape

variable (parameter : PublicParameter) (data : PublicData) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (m : Message) {s : State}

theorem newRand_eq_empty {s' : State} (h : ∀ ρ, RelatedAt parameter data m s s' ρ) :
    newRand parameter data m s s' = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun ρ hρ => ?_
  simp only [newRand, Finset.mem_filter, Finset.mem_univ, true_and] at hρ
  obtain ⟨h0, u, hu, hl⟩ := hρ
  rcases (h ρ).2 with he | ⟨_, u', hu', hnl⟩
  · change s'.cache (blk parameter data m ρ 0) = some u at hu
    rw [he, h0] at hu; cases hu
  · change s'.cache (blk parameter data m ρ 0) = some u at hu
    rw [hu'] at hu; cases hu; exact hnl hl

theorem newRand_eq_single {s' : State} {ρ : Randomness} (h : ∀ ρ', ρ' ≠ ρ → RelatedAt parameter data m s s' ρ')
    (h0 : s.cache (blk parameter data m ρ 0) = none) (hl : LandedIn parameter data s' (m, ρ)) :
    newRand parameter data m s s' = {ρ} := by
  ext ρ'
  simp only [newRand, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨h0', u, hu, hl'⟩
    by_contra hne
    rcases (h ρ' hne).2 with he | ⟨_, u', hu', hnl⟩
    · change s'.cache (blk parameter data m ρ' 0) = some u at hu
      rw [he, h0'] at hu; cases hu
    · change s'.cache (blk parameter data m ρ' 0) = some u at hu
      rw [hu'] at hu; cases hu; exact hnl hl'
  · rintro rfl
    exact ⟨h0, hl⟩

theorem newRand_eq_empty_of_pool {s' : State} {ρ : Randomness} (h : ∀ ρ', ρ' ≠ ρ → RelatedAt parameter data m s s' ρ')
    (h0 : s.cache (blk parameter data m ρ 0) ≠ none) : newRand parameter data m s s' = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun ρ' hρ' => ?_
  simp only [newRand, Finset.mem_filter, Finset.mem_univ, true_and] at hρ'
  obtain ⟨h0', u, hu, hl'⟩ := hρ'
  by_cases hne : ρ' = ρ
  · subst hne; exact h0 h0'
  · rcases (h ρ' hne).2 with he | ⟨_, u', hu', hnl⟩
    · change s'.cache (blk parameter data m ρ' 0) = some u at hu
      rw [he, h0'] at hu; cases hu
    · change s'.cache (blk parameter data m ρ' 0) = some u at hu
      rw [hu'] at hu; cases hu; exact hnl hl'

end SignShape

/-! ### Upper values of a signing outcome -/

section SignUpper

variable (parameter : PublicParameter) (data : PublicData) (wbar : ℝ≥0∞) (m : Message) (s : State) (n : ℕ)
  (d : Multiset View) (f : Multiset View → ℝ≥0∞)

/-- The value without disclosure. -/
noncomputable def baseV (J : List View) : ℝ≥0∞ := virtual Finset.univ wbar f n J d

/-- Gain of a fresh view that is disclosed and becomes an item. -/
noncomputable def gainF (J : List View) (u : View) : ℝ≥0∞ :=
  virtual Finset.univ wbar f n (u :: J) (d + {u}) - baseV wbar n d f J

/-- Gain of disclosing an existing item. -/
noncomputable def gainP (J : List View) (v : View) : ℝ≥0∞ :=
  virtual Finset.univ wbar f n J (d + {v}) - baseV wbar n d f J

/-- Upper value of one signing outcome, for future items `J`. -/
noncomputable def upper (excl : Pair → Prop) (out : Run HashInput Coordinate (Option Signature) × State)
    (J : List View) : ℝ≥0∞ :=
  baseV wbar n d f J + freshNewWeight parameter data m s (gainF wbar n d f J) out +
    outWeight parameter data m s 0 (fun ρ v => if excl (m, ρ) then 0 else gainP wbar n d f J v) out

variable {parameter data wbar m s n d f}

theorem pview_of_cached {s' : State} {q : Pair} {u0 u1 : HashOutput} (h0 : s'.cache (pblk parameter data q 0) = some u0)
    (h1 : s'.cache (pblk parameter data q 1) = some u1) : pview parameter data s' q = viewOf u0 u1 := by
  simp only [pview, h0, h1, Option.elim]

end SignUpper

/-! ### The fair-share hypotheses -/

section SignExpect

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (wbar : ℝ≥0∞) (m : Message) (s : State) (n : ℕ)
  (d : Multiset View) (f : Multiset View → ℝ≥0∞)

/-- The fair-share hypotheses of the grinding signer. -/
structure Fair (Cmax : ℕ) : Prop where
  ne_top : wbar ≠ ⊤
  le_one : wbar ≤ 1
  cmax : Cmax ≤ 2 ^ 128
  share : ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ ≤ wbar * (((2 ^ 128 - Cmax : ℕ) : ℝ≥0∞) / ((2 ^ 128 : ℕ) : ℝ≥0∞)) * landing

end SignExpect

/-! ### The state after a signing call -/

section SignParams

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (Fail : Finset (Fin (2 ^ subtreeHeight))) (Qtot : ℕ)
  (m : Message)

variable {parameter data m}

theorem other_message_kept (attempts budget : ℕ) (s : State)
    (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg initial model (signCostSourceLoop parameter data m attempts) budget s))
    (q : Pair) (hq : q.1 ≠ m) (call : Fin 2) :
    out.2.cache (pblk parameter data q call) = s.cache (pblk parameter data q call) := by
  refine interp_avoids_cache tg initial model _ _ (avoids_loop parameter data m attempts) budget s out hout _ ⟨?_, ?_⟩
  · exact msgInput_digestInput parameter data.root q.1 q.2 call
  · intro ρ c h
    exact hq (congrArg Prod.fst
      (pblk_injective parameter data (show pblk parameter data q call = pblk parameter data (m, ρ) c from h)).1)

theorem landed_of_cached {s : State} {P : List Pair} (hP : PInv parameter data s P) {q : Pair}
    (hq : q ∈ P) : ∃ u0 u1, s.cache (pblk parameter data q 0) = some u0 ∧ Landed parameter (blockIndex u0) ∧
      s.cache (pblk parameter data q 1) = some u1 := by
  obtain ⟨u0, h0, hl⟩ := (hP.mem q).1 hq
  obtain ⟨u1, h1⟩ := Option.ne_none_iff_exists'.1 (hP.second q ⟨u0, h0, hl⟩)
  exact ⟨u0, u1, h0, hl, h1⟩

end SignParams

/-! ### The bound for one signing outcome -/

section SignPoint

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (m : Message) (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View)

omit [Params] in
theorem erase_eq_filter' {P : List Pair} (hP : P.Nodup) (q : Pair) : P.erase q = others (· = q) P := by
  rw [hP.erase_eq_filter]
  unfold others
  congr 1
  funext q'
  rw [Bool.eq_iff_iff]
  simp [bne_iff_ne]

omit [Params] in
theorem filter_false' (P : List Pair) : others (fun _ => False) P = P := by unfold others; simp

/-- Bound for one outcome of a signing call. -/
noncomputable def canon (n k : ℕ) (out : Run HashInput Coordinate (Option Signature) × State) : ℝ≥0∞ :=
  freshNewWeight parameter data m s (fun v => if v.1 ∈ Fail then 1 else 0) out +
  (P.map fun q => if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1 else
      creations Finset.univ landing (fun J => upper parameter data wbar m s n d (witnessFn (pview parameter data s q))
        (· = q) out J) k (items parameter data s (others (· = q) P))) else 0).sum +
  k * (creations Finset.univ landing (fun J => upper parameter data wbar m s n d (excess b0) (fun _ => False) out J) k
      (items parameter data s (others (fun _ => False) P)) + failMass Fail) +
  n * failMass Fail

variable {parameter data wbar b0 Fail m s P L d}

end SignPoint

/-! ### Interpreting a continuation -/

section SignGood

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot : ℕ)

end SignGood

end SphincsFors.Security.ForsPotential
