/-
  LeanVM.Guest.B1.Sig.SphincsScheme

  leanSPHINCS verification with Keccak-256 (`Node.sphincsVerify`) as pure functions of the guest's
  cells.
-/

module

public import LeanVM.Guest.B1.Sig.XmssScheme

/-!
# leanSPHINCS over cells

As for leanXMSS (`XmssScheme`): the lemmas hold for any oracle instance on `Id` with `SQ`, that it
is Keccak-256, so that the kernel never unfolds the hash, and each routine is a pure function of
cells.

* `sVerify_iff`, `sphincsVerify_iff`: verification is the message digest, the forest key it selects
  (`forestRecover`, the sixteen top nodes, no hash), the one-time leaf over the forest key and the
  counter (`encode`, 292 bytes), and the tree, whose root is the key's;
* the one-time signature and the tree: `sOtsLeaf_id`, `sChainWalk_succ`, `sRecoverChain_cells`
  (over `sChain`), `sLeafHash_cells`, `sTreeFold_cells` (over `xFold`), `sEncode_cells`,
  `bytesLE_counter`, and the target-sum code (`sDecode_lit`, `sDecode_iff`);
* the message digest: `sMessageDigest_cells` (the two cells of one hash, truncated to 234 bits),
  `digestIndex_ofNat`, `digestField_ofNat`, `digestByte_ofNat`, the marks (`digestMarks_*_val`);
* the forest: `sForestWalk_cells`, `sForestRecoverChain_cells` (over `fChain`),
  `sChildRecover_cells`, `sSubFold_cells`, `sTopFold_cells`, `sSuperHash_cells`, `coordRecover_id`,
  `forestRecover_id`, `lut_val`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open Sphincs Sphincs.Concrete

@[expose] public section

/-- The oracle is Keccak-256. -/
def SQ (inst : HasQuery Sphincs.HashSpec Id) : Prop :=
  ∀ x, (inst.query (spec := Sphincs.HashSpec) x : Id HashOutput) = Node.keccakBits x

theorem sq_keccak : SQ ⟨Node.keccakBits⟩ := fun _ => rfl

variable {inst : HasQuery Sphincs.HashSpec Id}

/-- A cell as a leanSPHINCS digest. -/
def sv (x : E) : Sphincs.Digest := cellVal x

/-- A cell as a leanSPHINCS public parameter. -/
def spp (x : E) : Sphincs.PublicParameter := cellVal x

theorem bytesLE_sv (x : E) : Sphincs.bytesLE 16 (sv x) = cellBytes x := sphincs_bytesLE_cellVal x

theorem bytesLE_spp (x : E) : Sphincs.bytesLE 16 (spp x) = cellBytes x := sphincs_bytesLE_cellVal x

theorem sflatMap_bytesLE_sv : ∀ (l : List E),
    List.flatMap (Sphincs.bytesLE 16) (l.map sv) = l.flatMap cellBytes
  | [] => rfl
  | x :: l => by
      show Sphincs.bytesLE 16 (sv x) ++ List.flatMap (Sphincs.bytesLE 16) (l.map sv) =
        cellBytes x ++ l.flatMap cellBytes
      rw [bytesLE_sv, sflatMap_bytesLE_sv l]

/-- **A hash of bytes**: a tweakable hash is the value of the first digest cell of its input. -/
theorem sHash_bytes (hq : SQ inst) {P : PublicParameter} {dom : HashDomain}
    {payload : HashInput} {r : List UInt8} (h : tweakableHashInput P dom payload = r) :
    @tweakableHash Id _ inst P dom payload = sv (digestScalars (keccak256 r)).1 := by
  rw [tweakableHash.eq_def]
  simp only [bind, pure, oracleHash]
  rw [hq, h, sphincs_truncateHash_keccakBits]
  rfl

/-- **A hash of cells**: a tweakable hash whose input is the bytes of cells is the value of the
first cell of their `hcell`. -/
theorem sHash_cells (hq : SQ inst) {P : PublicParameter} {dom : HashDomain}
    {payload : HashInput} {cs : List E} (h : tweakableHashInput P dom payload = cs.flatMap cellBytes) :
    @tweakableHash Id _ inst P dom payload = sv (hcell cs).1 := sHash_bytes hq h

theorem sSequenceFin_id {α : Type} : ∀ {n : Nat} (f : Fin n → Id α),
    Sphincs.Concrete.sequenceFin f = f
  | 0, f => funext fun i => i.elim0
  | n + 1, f => by
      simp only [Sphincs.Concrete.sequenceFin]
      have := sSequenceFin_id (fun i : Fin n => f i.succ)
      rw [this]
      funext i
      refine Fin.cases rfl (fun j => rfl) i

/-! ## Addresses -/

theorem sTweak (tag step hi lo : Nat) :
    Sphincs.fieldBytes (Sphincs.tweakFields tag step hi lo) =
      cellBytes (eOfNat (addrNat tag step hi lo)) :=
  sphincs_fieldBytes_tweakFields tag step hi lo

/-! ## Verification -/

/-- The path a signature carries, as the verifier folds it: zero above the tree's height. -/
def signaturePath (σ : Signature) (l : Nat) : Sphincs.Digest :=
  if h : l < totalHeight then σ.path ⟨l, h⟩ else 0

/-- **Verification**: the digest selects the forest key, which the one-time signature signs
under a leaf whose path reaches the key's root. -/
theorem sVerify_iff (pk : PublicKey) (msg : Message) (σ : Signature) :
    @Sphincs.Concrete.verify Id _ inst pk msg σ = true ↔
      ∃ leaf, @otsLeaf Id _ inst pk.parameter
          (digestIndex (@messageDigest Id _ inst pk.parameter pk.root msg σ.randomness))
          (@forestRecover Id _ inst pk.parameter
            (digestIndex (@messageDigest Id _ inst pk.parameter pk.root msg σ.randomness))
            (digestMarks (@messageDigest Id _ inst pk.parameter pk.root msg σ.randomness)) σ.forest)
          σ.counter σ.chainValues = some leaf ∧
        @treeFold Id _ inst pk.parameter
          (digestIndex (@messageDigest Id _ inst pk.parameter pk.root msg σ.randomness))
          (signaturePath σ) totalHeight leaf = pk.root := by
  rw [Sphincs.Concrete.verify.eq_def]
  simp only [bind, pure]
  split
  next v hv =>
    rw [decide_eq_true_iff]
    constructor
    · intro hr; exact ⟨v, hv, hr⟩
    · rintro ⟨v', hv', hr⟩
      rw [hv] at hv'
      cases hv'
      exact hr
  next h =>
    refine ⟨fun h => absurd h Bool.false_ne_true, ?_⟩
    rintro ⟨v, hv, -⟩
    exact absurd hv (h v)

theorem sphincsVerify_iff (pk : PublicKey) (msg : Message) (σ : Signature) :
    Node.sphincsVerify pk msg σ = true ↔
      ∃ leaf, @otsLeaf Id _ ⟨Node.keccakBits⟩ pk.parameter
          (digestIndex (@messageDigest Id _ ⟨Node.keccakBits⟩ pk.parameter pk.root msg
            σ.randomness))
          (@forestRecover Id _ ⟨Node.keccakBits⟩ pk.parameter
            (digestIndex (@messageDigest Id _ ⟨Node.keccakBits⟩ pk.parameter pk.root msg σ.randomness))
            (digestMarks (@messageDigest Id _ ⟨Node.keccakBits⟩ pk.parameter pk.root msg σ.randomness))
            σ.forest)
          σ.counter σ.chainValues = some leaf ∧
        @treeFold Id _ ⟨Node.keccakBits⟩ pk.parameter
          (digestIndex (@messageDigest Id _ ⟨Node.keccakBits⟩ pk.parameter pk.root msg
            σ.randomness))
          (signaturePath σ) totalHeight leaf = pk.root := by
  rw [Node.sphincsVerify.eq_def, idRun]
  exact sVerify_iff pk msg σ

theorem signaturePath_lt (σ : Signature) (l : Nat) (hl : l < totalHeight) :
    signaturePath σ l = σ.path ⟨l, hl⟩ := by
  simp [signaturePath, hl]

/-! ## The one-time signature -/

theorem encode_id (P : PublicParameter) (leaf : Index)
    (K : ForestKey) (ctr : Counter) :
    @encode Id _ inst P leaf K ctr =
      TargetSum.decodeDigest (@tweakableHash Id _ inst P (.encoding leaf)
        (rootsPayload K ++ Sphincs.bytesLE 4 ctr)) := rfl

theorem sOtsLeaf_id (P : PublicParameter) (leaf : Index)
    (K : ForestKey) (ctr : Counter) (vals : ChainIndex → Sphincs.Digest) :
    @otsLeaf Id _ inst P leaf K ctr vals =
      (@encode Id _ inst P leaf K ctr).map fun enc =>
        @leafHash Id _ inst P leaf fun i =>
          @recoverChain Id _ inst P leaf i (enc i) (vals i) := by
  rw [otsLeaf.eq_def]
  simp only [bind, pure]
  split
  next enc h => rw [h, sSequenceFin_id]; rfl
  next h =>
    cases h' : @encode Id _ inst P leaf K ctr with
    | none => rfl
    | some enc => exact absurd h' (h enc)

theorem sChainWalk_succ (P : PublicParameter) (leaf : Index)
    (i : ChainIndex) (start n : Nat) (v : Sphincs.Digest) :
    @chainWalk Id _ inst P leaf i start (n + 1) v =
      if hstep : start + n < chainLength - 1 then
        @tweakableHash Id _ inst P (.chain leaf i ⟨start + n, hstep⟩)
          (Sphincs.bytesLE 16 (@chainWalk Id _ inst P leaf i start n v))
      else 0 := by
  rw [chainWalk_eq_succ]
  simp only [bind]
  split <;> rfl

theorem sChainWalk_shift (P : PublicParameter) (leaf : Index)
    (i : ChainIndex) :
    ∀ (n start : Nat) (v : Sphincs.Digest) (hs : start < chainLength - 1),
      start + n + 1 ≤ chainLength - 1 →
      @chainWalk Id _ inst P leaf i start (n + 1) v =
        @chainWalk Id _ inst P leaf i (start + 1) n
          (@tweakableHash Id _ inst P (.chain leaf i ⟨start, hs⟩) (Sphincs.bytesLE 16 v))
  | 0, start, v, hs, _ => by
      rw [sChainWalk_succ, dite_of (by omega), chainWalk_eq_zero, chainWalk_eq_zero]
      rfl
  | n + 1, start, v, hs, h => by
      have h1 : start + (n + 1) < chainLength - 1 := by omega
      have h2 : start + 1 + n < chainLength - 1 := by omega
      rw [sChainWalk_succ, dite_of h1, sChainWalk_shift P leaf i n start v hs (by omega),
        sChainWalk_succ, dite_of h2]
      have : (⟨start + (n + 1), h1⟩ : ChainStep) = ⟨start + 1 + n, h2⟩ := Fin.ext (by simp only; omega)
      rw [this]

/-- **A one-time chain step over cells.** -/
theorem sChainStep_cells (hq : SQ inst) {pp a x : E} {leaf : Index} {i : ChainIndex} {s : ChainStep}
    (ha : cellBytes a = tweakBytes (.chain leaf i s)) :
    @tweakableHash Id _ inst (spp pp) (.chain leaf i s) (Sphincs.bytesLE 16 (sv x)) =
      sv (hcell [pp, a, x]).1 := by
  apply sHash_cells hq
  show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ Sphincs.bytesLE 16 (sv x) = _
  rw [bytesLE_spp, bytesLE_sv, ← ha]
  simp

/-- `n` one-time chain steps from position `s` on cells: the step leaving position `s` hashes `P`,
its address `adr s` and the value. -/
def sChain (pp : E) (adr : Nat → E) : Nat → Nat → E → E
  | 0, _, x => x
  | n + 1, s, x => sChain pp adr n (s + 1) (hcell [pp, adr s, x]).1

/-- **A one-time chain walked from digit `d` over cells**, its step addresses' bytes the steps'
tweaks. -/
theorem sRecoverChain_cells (hq : SQ inst) {pp : E} {adr : Nat → E}
    {leaf : Index} {i : ChainIndex}
    (hadr : ∀ (s : ChainStep), cellBytes (adr s) = tweakBytes (.chain leaf i s)) :
    ∀ (d : Digit) (x : E), @recoverChain Id _ inst (spp pp) leaf i d (sv x) =
      sv (sChain pp adr (3 - d.val) d.val x) := by
  have hwalk : ∀ (n start : Nat) (x : E), start + n ≤ chainLength - 1 →
      @chainWalk Id _ inst (spp pp) leaf i start n (sv x) = sv (sChain pp adr n start x) := by
    intro n
    induction n with
    | zero => intro start x _; rw [chainWalk_eq_zero]; rfl
    | succ n ih =>
        intro start x h
        rw [sChainWalk_shift _ _ _ _ _ _ (by omega) h, sChainStep_cells hq (hadr ⟨start, by omega⟩),
          ih (start + 1) _ (by omega)]
        rfl
  intro d x
  have hd := d.isLt
  simp only [chainLength, winternitzBits] at hd
  rw [recoverChain, show chainLength - 1 - d.val = 3 - d.val by simp [chainLength, winternitzBits]]
  exact hwalk _ _ _ (by simp [chainLength, winternitzBits]; omega)

/-- **The one-time leaf over cells.** -/
theorem sLeafHash_cells (hq : SQ inst) {pp a : E} {leaf : Index} (tips : Nat → E) (ha : cellBytes a = tweakBytes (.leaf leaf)) :
    @leafHash Id _ inst (spp pp) leaf (fun i => sv (tips i.val)) =
      sv (hcell (pp :: a :: (List.range numChains).map tips)).1 := by
  apply sHash_cells hq
  show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++
    (List.ofFn fun i : ChainIndex => sv (tips i.val)).flatMap (Sphincs.bytesLE 16) = _
  rw [bytesLE_spp, ← ha, show (List.ofFn fun i : ChainIndex => sv (tips i.val)) =
      ((List.range numChains).map tips).map sv
    from (ofFn_val_eq numChains (fun i => sv (tips i))).trans (List.map_map.symm)]
  exact (congrArg (fun t => cellBytes pp ++ cellBytes a ++ t) (sflatMap_bytesLE_sv _)).trans (by simp)

/-- **The tree over cells**: the fold of a path whose addresses' bytes are the nodes' tweaks, its
bits the leaf's. -/
theorem sTreeFold_cells (hq : SQ inst) {pp : E} {A : Nat → E} {leaf : Index}
    (hA : ∀ l < totalHeight,
      cellBytes (A l) = tweakBytes (.node (l + 1) (leaf.val / 2 ^ (l + 1))))
    (sibs : Nat → E) :
    ∀ m ≤ totalHeight, ∀ x : E,
      @treeFold Id _ inst (spp pp) leaf (fun l => sv (sibs l)) m (sv x) =
        sv (xFold pp A (fun l => leaf.val.testBit l) sibs m x)
  | 0, _, x => by rw [treeFold_eq_zero]; rfl
  | m + 1, hm, x => by
      rw [treeFold_eq_succ]
      simp only [bind, xFold]
      rw [sTreeFold_cells hq hA sibs m (by omega) x]
      split
      · apply sHash_cells hq
        show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (Sphincs.bytesLE 16 (sv (sibs m)) ++
          Sphincs.bytesLE 16 (sv _)) = _
        rw [bytesLE_spp, bytesLE_sv, bytesLE_sv, ← hA m (by omega)]
        simp_all
      · apply sHash_cells hq
        show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (Sphincs.bytesLE 16 (sv _) ++
          Sphincs.bytesLE 16 (sv (sibs m))) = _
        rw [bytesLE_spp, bytesLE_sv, bytesLE_sv, ← hA m (by omega)]
        simp_all

/-- The counter's four bytes are a cell's first four, for a cell below `2^32`. -/
theorem bytesLE_counter {x : E} (h : cellNat x < 2 ^ 32) :
    Sphincs.bytesLE 4 (BitVec.ofNat (8 * 4) (cellNat x)) = (cellBytes x).take 4 := by
  rw [sphincs_bytesLE_eq, cellBytes_eq_leBytes, show (16 : Nat) = 4 + 12 from rfl, ← leBytes_append,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), List.take_left' (by simp)]

/-- **The encoding over cells**: the hash of `P`, the encoding's address, the sixteen top nodes and
the counter's four bytes, the first `292` bytes of the cells. -/
theorem sEncode_cells (hq : SQ inst) {pp aE x : E} {leaf : Index} {K : ForestKey} {ctr : Counter} (T : Nat → E)
    (hK : ∀ c : Coord, K c = (sv (T (2 * c.val)), sv (T (2 * c.val + 1))))
    (hE : cellBytes aE = tweakBytes (.encoding leaf))
    (hc : Sphincs.bytesLE 4 ctr = (cellBytes x).take 4) :
    @encode Id _ inst (spp pp) leaf K ctr =
      TargetSum.decodeDigest
        (sv (digestScalars (keccak256 ((cellsBytes
          (pp :: aE :: (List.range 16).map T ++ [x])).take 292))).1) := by
  rw [encode_id, sHash_bytes hq]
  show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (rootsPayload K ++ Sphincs.bytesLE 4 ctr) = _
  rw [bytesLE_spp, ← hE, hc]
  have hK' : K = fun c => (sv (T (2 * c.val)), sv (T (2 * c.val + 1))) := funext hK
  subst hK'
  have hr : rootsPayload (fun c : Coord => (sv (T (2 * c.val)), sv (T (2 * c.val + 1)))) =
      ((List.range 16).map T).flatMap cellBytes := by
    simp only [rootsPayload, nodePayload]
    rw [show (List.ofFn fun c : Coord => (sv (T (2 * c.val)), sv (T (2 * c.val + 1)))) =
        (List.range 8).map (fun k => (sv (T (2 * k)), sv (T (2 * k + 1)))) from
      ofFn_val_eq forestCoords (fun k => (sv (T (2 * k)), sv (T (2 * k + 1))))]
    simp [List.range_succ, bytesLE_sv]
  rw [hr, cellsBytes_eq_flatMap]
  have hl : (cellBytes pp ++ cellBytes aE ++ ((List.range 16).map T).flatMap cellBytes).length = 288 := by
    simp [List.range_succ]
  have e : (pp :: aE :: (List.range 16).map T ++ [x]).flatMap cellBytes =
      (cellBytes pp ++ cellBytes aE ++ ((List.range 16).map T).flatMap cellBytes) ++ cellBytes x := by
    simp
  rw [e, List.take_append, hl, List.take_of_length_le
    (l := cellBytes pp ++ cellBytes aE ++ ((List.range 16).map T).flatMap cellBytes) (by rw [hl]; omega)]
  simp

/-! ## The target-sum code -/

theorem sDigit_val (d : Sphincs.Digest) (i : ChainIndex) :
    (TargetSum.digestEncoding d i).val = d.toNat / 4 ^ i.val % 4 := by
  show (BitVec.extractLsb' (2 * i.val) 2 d).toNat = _
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

theorem sDigit_ofNat (N : Nat) (i : ChainIndex) :
    (TargetSum.digestEncoding (BitVec.ofNat 128 N) i).val = N % 2 ^ 128 / 4 ^ i.val % 4 := by
  have := sDigit_val (BitVec.ofNat 128 N) i
  simpa [digestBits] using this

/-- **A codeword's digits**: the digest holding the literal of `64` digits below 4 summing to
123 decodes to them. -/
theorem sDecode_lit {dig : Nat → Nat} (hd : ∀ j, dig j < 4)
    (hs : ∑ i ∈ Finset.range numChains, dig i = targetSum) :
    TargetSum.decodeDigest (sv (lit (∑ j ∈ Finset.range numChains, dig j * 4 ^ j))) =
      some fun i => ⟨dig i.val, hd _⟩ := by
  have hlt := base4_lt hd numChains
  have hlt' : ∑ j ∈ Finset.range numChains, dig j * 4 ^ j < 2 ^ 128 := by
    have : (4 : Nat) ^ numChains = 2 ^ 128 := by norm_num [numChains]
    omega
  rw [show sv (lit (∑ j ∈ Finset.range numChains, dig j * 4 ^ j)) =
      BitVec.ofNat 128 (∑ j ∈ Finset.range numChains, dig j * 4 ^ j) from cellVal_lit _]
  have henc : TargetSum.digestEncoding
      (BitVec.ofNat 128 (∑ j ∈ Finset.range numChains, dig j * 4 ^ j)) =
        fun i => ⟨dig i.val, hd _⟩ := by
    funext i
    apply Fin.ext
    rw [sDigit_ofNat, Nat.mod_eq_of_lt (a := ∑ j ∈ Finset.range numChains, dig j * 4 ^ j) hlt']
    exact base4_digit hd _ _ i.isLt
  have hv : TargetSum.Valid (fun i : ChainIndex => (⟨dig i.val, hd _⟩ : Digit)) := by
    rw [TargetSum.Valid, TargetSum.sum, ← hs, ← Fin.sum_univ_eq_sum_range]
  simp only [TargetSum.decodeDigest, henc, hv, ↓reduceIte]

/-- **`decodeDigest`**: a digest decodes exactly when its 64 digits sum to `123`, to its digits. -/
theorem sDecode_iff {d : Sphincs.Digest} {enc : Encoding} :
    TargetSum.decodeDigest d = some enc ↔
      ∑ i ∈ Finset.range numChains, d.toNat / 4 ^ i % 4 = targetSum ∧
        ∀ i : ChainIndex, (enc i).val = d.toNat / 4 ^ i.val % 4 := by
  have hsum : TargetSum.Valid (TargetSum.digestEncoding d) ↔
      ∑ i ∈ Finset.range numChains, d.toNat / 4 ^ i % 4 = targetSum := by
    rw [TargetSum.Valid, TargetSum.sum, ← Fin.sum_univ_eq_sum_range]
    exact Eq.congr_left (Finset.sum_congr rfl fun i _ => sDigit_val d i)
  simp only [TargetSum.decodeDigest]
  split
  next hv =>
    simp only [Option.some.injEq]
    constructor
    · rintro rfl; exact ⟨hsum.mp hv, sDigit_val d⟩
    · rintro ⟨-, he⟩
      funext i
      exact Fin.ext ((sDigit_val d i).trans (he i).symm)
  next hv =>
    simp only [reduceCtorEq, false_iff, not_and]
    exact fun h => absurd (hsum.mpr h) hv

/-! ## The message digest -/

theorem truncateMessageDigest_keccakBits (I : List UInt8) :
    truncateMessageDigest (Node.keccakBits I) =
      BitVec.ofNat messageDigestBits
        (cellNat (digestScalars (keccak256 I)).1 + 2 ^ 128 * cellNat (digestScalars (keccak256 I)).2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  show ((Node.keccakBits I).toNat >>> 0) % 2 ^ messageDigestBits = _
  rw [Nat.shiftRight_zero, keccakBits_toNat]

/-- **The message digest over cells**: the two cells of the hash of `P | A | m | ρ`. -/
theorem sMessageDigest_cells (hq : SQ inst) {pp a m0 m1 rho : E} {root : Sphincs.Digest}
    {m : Message} (ha : cellBytes a = tweakBytes .message)
    (hm : Sphincs.bytesLE 32 m = cellBytes m0 ++ cellBytes m1) :
    @messageDigest Id _ inst (spp pp) root m (sv rho) =
      BitVec.ofNat messageDigestBits (cellNat (hcell [pp, a, m0, m1, rho]).1 +
        2 ^ 128 * cellNat (hcell [pp, a, m0, m1, rho]).2) := by
  have hI : tweakableHashInput (spp pp) .message (messageDigestPayload root m (sv rho)) =
      [pp, a, m0, m1, rho].flatMap cellBytes := by
    show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++
      (Sphincs.bytesLE 32 m ++ Sphincs.bytesLE 16 (sv rho)) = _
    rw [bytesLE_spp, bytesLE_sv, ← ha, hm]
    simp
  rw [messageDigest.eq_def]
  simp only [bind, pure, messageDigestCall, oracleHash]
  rw [hq, truncateMessageDigest_keccakBits, hI]
  rfl

theorem mod_div_mod {x n k w : Nat} (h : k + w ≤ n) :
    x % 2 ^ n / 2 ^ k % 2 ^ w = x / 2 ^ k % 2 ^ w := by
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self x, ← pow_add,
    Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 h)]

theorem digest_div {c0 c1 k : Nat} (h0 : c0 < 2 ^ 128) :
    (c0 + 2 ^ 128 * c1) % 2 ^ messageDigestBits / 2 ^ (128 + k) = c1 % 2 ^ (234 - 128) / 2 ^ k := by
  have e1 : (c0 + 2 ^ 128 * c1) % 2 ^ 128 = c0 := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
  have e2 : (c0 + 2 ^ 128 * c1) / 2 ^ 128 = c1 := by
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt h0, Nat.zero_add]
  rw [show messageDigestBits = 128 + (234 - 128) from rfl, pow_add 2 128 (234 - 128), Nat.mod_mul, e1,
    e2, pow_add 2 128 k, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt h0, Nat.zero_add]

/-- The index a digest of two cells selects: the low 26 bits of the second. -/
theorem digestIndex_ofNat {c0 c1 : Nat} (h0 : c0 < 2 ^ 128) :
    (digestIndex (BitVec.ofNat messageDigestBits (c0 + 2 ^ 128 * c1))).val = c1 % 2 ^ 26 := by
  show ((BitVec.ofNat messageDigestBits (c0 + 2 ^ 128 * c1)).extractLsb' 128 26).toNat = _
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    show (128 : Nat) = 128 + 0 from rfl, digest_div h0, pow_zero, Nat.div_one,
    Nat.mod_mod_of_dvd _ (by norm_num)]

/-- A field of the second cell. -/
theorem digestField_ofNat {c0 c1 : Nat} (h0 : c0 < 2 ^ 128) {k w : Nat} (hk : k + w ≤ 106) :
    ((BitVec.ofNat messageDigestBits (c0 + 2 ^ 128 * c1)).extractLsb' (128 + k) w).toNat =
      c1 / 2 ^ k % 2 ^ w := by
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, digest_div h0,
    mod_div_mod (by omega)]

/-- A byte of the first cell. -/
theorem digestByte_ofNat {c0 c1 : Nat} {k : Nat} (hk : k + 8 ≤ 128) :
    ((BitVec.ofNat messageDigestBits (c0 + 2 ^ 128 * c1)).extractLsb' k 8).toNat =
      c0 / 2 ^ k % 2 ^ 8 := by
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have e : c0 + 2 ^ 128 * c1 = c0 + 2 ^ k * (2 ^ 8 * (2 ^ (120 - k) * c1)) := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← pow_add, ← pow_add, show k + 8 + (120 - k) = 128 by omega]
  have hm : (c0 + 2 ^ 128 * c1) % 2 ^ messageDigestBits / 2 ^ k % 2 ^ 8 =
      (c0 + 2 ^ 128 * c1) / 2 ^ k % 2 ^ 8 :=
    mod_div_mod (show k + 8 ≤ messageDigestBits by
      simp only [messageDigestBits, totalHeight, forestCoords, coordBits]; omega)
  rw [hm, e, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

theorem digestMarks_super_val (D : Sphincs.MessageDigest) (c : Sphincs.Coord) :
    ((digestMarks D c).super).val = (D.extractLsb' (superOffset c) topHeight).toNat := rfl

theorem digestMarks_child_val (D : Sphincs.MessageDigest) (c : Sphincs.Coord) (j : Sphincs.SubIdx) :
    ((digestMarks D c).child j).val = (D.extractLsb' (childOffset c j) subHeight).toNat := rfl

theorem digestMarks_word_val (D : Sphincs.MessageDigest) (c : Sphincs.Coord) (j : Sphincs.SubIdx) :
    ((digestMarks D c).word j).val = (D.extractLsb' (wordOffset c j) 8).toNat := rfl

/-- The marks of a digest of two cells: the super-child and the child fields of the second, the
codeword byte of the first. -/
theorem digestMarks_ofNat {c0 c1 : Nat} (h0 : c0 < 2 ^ 128) (c : Sphincs.Coord) (j : Sphincs.SubIdx) :
    ((digestMarks (BitVec.ofNat messageDigestBits (c0 + 2 ^ 128 * c1)) c).super).val =
        c1 / 2 ^ (26 + 4 * c.val) % 2 ^ 4 ∧
      ((digestMarks (BitVec.ofNat messageDigestBits (c0 + 2 ^ 128 * c1)) c).child j).val =
        c1 / 2 ^ (58 + 3 * (2 * c.val + j.val)) % 2 ^ 3 ∧
      ((digestMarks (BitVec.ofNat messageDigestBits (c0 + 2 ^ 128 * c1)) c).word j).val =
        c0 / 2 ^ (8 * (2 * c.val + j.val)) % 2 ^ 8 := by
  have hc := c.isLt
  have hj := j.isLt
  simp only [forestCoords] at hc
  refine ⟨?_, ?_, ?_⟩
  · rw [digestMarks_super_val, superOffset, show 154 + 4 * c.val = 128 + (26 + 4 * c.val) by omega]
    exact digestField_ofNat h0 (by simp only [topHeight]; omega)
  · rw [digestMarks_child_val, childOffset,
      show 186 + 3 * (2 * c.val + j.val) = 128 + (58 + 3 * (2 * c.val + j.val)) by omega]
    exact digestField_ofNat h0 (by simp only [subHeight]; omega)
  · rw [digestMarks_word_val, wordOffset]
    exact digestByte_ofNat (by omega)

/-! ## The forest -/

/-- `n` steps of forest chain `i` from position `s` over cells, under the key's address `ka`: the
step from position `t` hashes `P`, `ka + (TW_FCHAIN + i·2^43 + t·2^61)` and the value
(`sp_forest_top`). -/
def fChain (pp ka : E) (i s : Nat) (v : E) : Nat → E
  | 0 => v
  | n + 1 => (hcell [pp, ka + eOfNat (tw 15 + i * 2 ^ 43 + (s + n) * stepMul), fChain pp ka i s v n]).1

/-- **A forest chain over cells.** -/
theorem sForestWalk_cells (hq : SQ inst) {pp ka : E} {index : Index} {c : Coord} {s : SuperIdx}
    {j : SubIdx} {a : ChildIdx} {i : FChain}
    (hadr : ∀ t : FStep, cellBytes (ka + eOfNat (tw 15 + i.val * 2 ^ 43 + t.val * stepMul)) =
      tweakBytes (.fchain index c s j a i t)) (start : Nat) (x : E) :
    ∀ n, start + n ≤ chainTop →
      @forestWalk Id _ inst (spp pp) index c s j a i start n (sv x) = sv (fChain pp ka i.val start x n)
  | 0, _ => by rw [forestWalk_eq_zero]; rfl
  | n + 1, h => by
      rw [forestWalk_eq_succ]
      simp only [bind]
      rw [sForestWalk_cells hq hadr start x n (by omega), dite_of (by omega)]
      apply sHash_cells hq
      show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ Sphincs.bytesLE 16 (sv _) = _
      rw [bytesLE_spp, bytesLE_sv, ← hadr ⟨start + n, by omega⟩]
      simp

/-- **A forest chain from its deficit.** -/
theorem sForestRecoverChain_cells (hq : SQ inst) {pp ka : E} {index : Index} {c : Coord}
    {s : SuperIdx} {j : SubIdx} {a : ChildIdx} {i : FChain}
    (hadr : ∀ t : FStep, cellBytes (ka + eOfNat (tw 15 + i.val * 2 ^ 43 + t.val * stepMul)) =
      tweakBytes (.fchain index c s j a i t)) (d : FPos) (x : E) :
    @forestRecoverChain Id _ inst (spp pp) index c s j a i d (sv x) =
      sv (fChain pp ka i.val (4 - d.val) x d.val) :=
  sForestWalk_cells hq hadr _ x _ (by have := d.isLt; simp only [chainTop] at this ⊢; omega)

/-- The end of chain `k` of a child opened at `word` from the value `vals k`. -/
def fEnds (pp ka : E) (word : Codeword) (vals : Nat → E) (k : Nat) : E :=
  fChain pp ka k (4 - (word ⟨k % 6, Nat.mod_lt _ (by norm_num)⟩).val) (vals k)
    (word ⟨k % 6, Nat.mod_lt _ (by norm_num)⟩).val

/-- **A child leaf over cells**: the hash of the six chain ends. -/
theorem sChildRecover_cells (hq : SQ inst) {pp ka aL : E} {index : Index} {c : Coord}
    {s : SuperIdx} {j : SubIdx} {a : ChildIdx} (word : Codeword) (vals : Nat → E)
    (hadr : ∀ (i : FChain) (t : FStep),
      cellBytes (ka + eOfNat (tw 15 + i.val * 2 ^ 43 + t.val * stepMul)) =
        tweakBytes (.fchain index c s j a i t))
    (hL : cellBytes aL = tweakBytes (.childLeaf index c s j a)) :
    @childRecover Id _ inst (spp pp) index c s j a word (fun i => sv (vals i.val)) =
      sv (hcell (pp :: aL :: (List.range 6).map (fEnds pp ka word vals))).1 := by
  rw [childRecover.eq_def]
  simp only [bind, sSequenceFin_id]
  apply sHash_cells hq
  show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (List.ofFn _).flatMap (Sphincs.bytesLE 16) = _
  rw [bytesLE_spp, ← hL]
  simp only [sForestRecoverChain_cells hq (hadr _)]
  have e : (fun i : FChain => sv (fChain pp ka i.val (4 - (word i).val) (vals i.val) (word i).val)) =
      fun i : FChain => sv (fEnds pp ka word vals i.val) := funext fun i => by
    rw [fEnds, show (⟨i.val % 6, Nat.mod_lt _ (by norm_num)⟩ : FChain) = i from
      Fin.ext (Nat.mod_eq_of_lt i.isLt)]
  rw [e]
  erw [show (List.ofFn fun i : FChain => sv (fEnds pp ka word vals i.val)) =
      ((List.range 6).map (fEnds pp ka word vals)).map sv from
    (ofFn_val_eq childChains (fun k => sv (fEnds pp ka word vals k))).trans List.map_map.symm]
  exact (congrArg (fun t => cellBytes pp ++ cellBytes aL ++ t) (sflatMap_bytesLE_sv _)).trans
    (by simp)

/-- A sub-tree folded over cells: its addresses' bytes are the nodes' tweaks, its bits the child's. -/
theorem sSubFold_cells (hq : SQ inst) {pp : E} {A : Nat → E} {index : Index} {c : Coord}
    {s : SuperIdx} {j : SubIdx} {a : ChildIdx}
    (hA : ∀ (l : Fin subHeight) (node : ChildIdx), node.val = a.val / 2 ^ (l.val + 1) →
      cellBytes (A l.val) = tweakBytes (.subNode index c s j l node))
    (sibs : Nat → E) :
    ∀ m ≤ subHeight, ∀ x : E,
      @subFold Id _ inst (spp pp) index c s j a (fun l => sv (sibs l.val)) m (sv x) =
        sv (xFold pp A (fun l => a.val.testBit l) sibs m x)
  | 0, _, x => by rw [subFold_eq_zero]; rfl
  | m + 1, hm, x => by
      rw [subFold_eq_succ]
      simp only [bind, xFold]
      rw [sSubFold_cells hq hA sibs m (by omega) x, dite_of (by omega)]
      split
      · apply sHash_cells hq
        show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (Sphincs.bytesLE 16 (sv (sibs m)) ++
          Sphincs.bytesLE 16 (sv _)) = _
        rw [bytesLE_spp, bytesLE_sv, bytesLE_sv, ← hA ⟨m, by omega⟩ _ rfl]
        simp_all
      · apply sHash_cells hq
        show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (Sphincs.bytesLE 16 (sv _) ++
          Sphincs.bytesLE 16 (sv (sibs m))) = _
        rw [bytesLE_spp, bytesLE_sv, bytesLE_sv, ← hA ⟨m, by omega⟩ _ rfl]
        simp_all

/-- A top tree folded over cells. -/
theorem sTopFold_cells (hq : SQ inst) {pp : E} {A : Nat → E} {index : Index} {c : Coord}
    {s : SuperIdx}
    (hA : ∀ (l : Fin topHeight) (node : SuperIdx), node.val = s.val / 2 ^ (l.val + 1) →
      cellBytes (A l.val) = tweakBytes (.topNode index c l node))
    (sibs : Nat → E) :
    ∀ m ≤ topHeight, ∀ x : E,
      @topFold Id _ inst (spp pp) index c s (fun l => sv (sibs l.val)) m (sv x) =
        sv (xFold pp A (fun l => s.val.testBit l) sibs m x)
  | 0, _, x => by rw [topFold_eq_zero]; rfl
  | m + 1, hm, x => by
      rw [topFold_eq_succ]
      simp only [bind, xFold]
      rw [sTopFold_cells hq hA sibs m (by omega) x, dite_of (by omega)]
      split
      · apply sHash_cells hq
        show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (Sphincs.bytesLE 16 (sv (sibs m)) ++
          Sphincs.bytesLE 16 (sv _)) = _
        rw [bytesLE_spp, bytesLE_sv, bytesLE_sv, ← hA ⟨m, by omega⟩ _ rfl]
        simp_all
      · apply sHash_cells hq
        show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (Sphincs.bytesLE 16 (sv _) ++
          Sphincs.bytesLE 16 (sv (sibs m))) = _
        rw [bytesLE_spp, bytesLE_sv, bytesLE_sv, ← hA ⟨m, by omega⟩ _ rfl]
        simp_all

/-- **A super-child over cells**: the hash of the four level-2 nodes. -/
theorem sSuperHash_cells (hq : SQ inst) {pp aS t00 t01 t10 t11 : E} {index : Index} {c : Coord}
    {s : SuperIdx} {tops : SubIdx → Sphincs.Digest × Sphincs.Digest}
    (h0 : tops 0 = (sv t00, sv t01)) (h1 : tops 1 = (sv t10, sv t11))
    (hS : cellBytes aS = tweakBytes (.superChild index c s)) :
    @superHash Id _ inst (spp pp) index c s tops = sv (hcell [pp, aS, t00, t01, t10, t11]).1 := by
  apply sHash_cells hq
  show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ superPayload _ = _
  rw [bytesLE_spp, ← hS]
  simp [superPayload, nodePayload, bytesLE_sv, h0, h1]

/-- A coordinate's two top nodes in `Id`: each sub-tree's child leaf folded and ordered, the
super-child hashed, folded and ordered. -/
theorem coordRecover_id (P : PublicParameter) (index : Index) (c : Coord) (mark : CoordMark)
    (opening : CoordOpening) :
    @coordRecover Id _ inst P index c mark opening =
      orderTops (mark.super.val.testBit (topHeight - 1))
        (@topFold Id _ inst P index c mark.super opening.top (topHeight - 1)
          (@superHash Id _ inst P index c mark.super fun j =>
            orderTops ((mark.child j).val.testBit (subHeight - 1))
              (@subFold Id _ inst P index c mark.super j (mark.child j) (opening.sub j).path
                (subHeight - 1)
                (@childRecover Id _ inst P index c mark.super j (mark.child j) (lut (mark.word j))
                  (opening.sub j).values))
              ((opening.sub j).path subTopLevel)))
        (opening.top topTopLevel) := by
  rw [coordRecover.eq_def]
  simp only [bind, pure, sSequenceFin_id]

/-- The forest key in `Id`: each coordinate's two top nodes. -/
theorem forestRecover_id (P : PublicParameter) (index : Index) (marks : Coord → CoordMark)
    (opening : Coord → CoordOpening) :
    @forestRecover Id _ inst P index marks opening =
      fun c => @coordRecover Id _ inst P index c (marks c) (opening c) := by
  rw [forestRecover.eq_def, sSequenceFin_id]

theorem orderTops_fst (bit : Bool) (current sibling : Sphincs.Digest) :
    (orderTops bit current sibling).1 = if bit then sibling else current := by
  cases bit <;> rfl

theorem orderTops_snd (bit : Bool) (current sibling : Sphincs.Digest) :
    (orderTops bit current sibling).2 = if bit then current else sibling := by
  cases bit <;> rfl

/-- The codeword table's entries, as base-5 digits. -/
theorem lut_val (t : LutIdx) (i : FChain) :
    (lut t i).val = codewordCodes.getD t.val 0 / 5 ^ (5 - i.val) % 5 := rfl

end
end LeanVM.Guest.B1.Sig
