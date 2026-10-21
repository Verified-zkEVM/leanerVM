/-
  LeanVM.Guest.B1.Sig.Model.SphincsScheme

  leanSPHINCS verification with an answered hash (`Node.sphincsVerifyWith`) over the guest's cells:
  each routine run in `Option` under the hash `H` is `some` of the cells' answered hashes.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsScheme
public import LeanVM.Guest.B1.Sig.Model.XmssScheme

/-!
# leanSPHINCS over cells, with an answered hash

As `Model/XmssScheme` for leanXMSS: `Node.sphincsVerifyWith H` runs `Sphincs.Concrete.verify` in
`Option` with the oracle `digestBits <$> H`; the lemmas hold for any instance with `SQW H`. The
one-time signature (`sRecoverChain_cellsW`, `sLeafHash_cellsW`, `sOtsLeaf_someW`), the tree
(`sTreeFold_cellsW`), the message digest (`sMessageDigest_cellsW`), the forest
(`fChainWith`, `sForestWalk_cellsW`, `sChildRecover_cellsW`, `sSubFold_cellsW`, `sTopFold_cellsW`,
`sSuperHash_cellsW`, `sCoordRecover_someW`, `sForestRecover_cellsW`) and the verification
(`sVerify_of`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Value Sphincs Sphincs.Concrete

@[expose] public section

/-- The oracle answers `H`, its digests read as bits. -/
def SQW (H : List UInt8 → Option Protocol.Digest) (inst : HasQuery Sphincs.HashSpec Option) : Prop :=
  ∀ x, (inst.query (spec := Sphincs.HashSpec) x : Option HashOutput) = Node.digestBits <$> H x

theorem sqw_with (H : List UInt8 → Option Protocol.Digest) : SQW H ⟨fun x ↦ Node.digestBits <$> H x⟩ :=
  fun _ => rfl

variable {H : List UInt8 → Option Protocol.Digest} {inst : HasQuery Sphincs.HashSpec Option}

/-- **A hash of bytes, answered.** -/
theorem sHash_bytesW (hq : SQW H inst) {P : PublicParameter} {dom : HashDomain} {payload : HashInput}
    {r : List UInt8} {o : E × E} (h : tweakableHashInput P dom payload = r) (ho : hbWith H r = some o) :
    @tweakableHash Option _ inst P dom payload = some (sv o.1) := by
  obtain ⟨d, hd, rfl⟩ := hbWith_some.mp ho
  rw [tweakableHash.eq_def]
  simp only [oracleHash]
  rw [hq, h, hd]
  show some (Sphincs.truncateHash (Node.digestBits d)) = _
  rw [sphincs_truncateHash_digestBits]
  rfl

/-- **A hash of cells, answered.** -/
theorem sHash_cellsW (hq : SQW H inst) {P : PublicParameter} {dom : HashDomain} {payload : HashInput}
    {cs : List E} {o : E × E} (h : tweakableHashInput P dom payload = cs.flatMap cellBytes)
    (ho : hcellWith H cs = some o) : @tweakableHash Option _ inst P dom payload = some (sv o.1) :=
  sHash_bytesW hq h ho

theorem sSequenceFin_someW {α : Type} : ∀ {n : Nat} {f : Fin n → Option α} {g : Fin n → α},
    (∀ i, f i = some (g i)) → Sphincs.Concrete.sequenceFin f = some g
  | 0, f, g, _ => by
      simp only [Sphincs.Concrete.sequenceFin]
      exact congrArg some (funext fun i => i.elim0)
  | n + 1, f, g, h => by
      simp only [Sphincs.Concrete.sequenceFin]
      rw [h 0, Option.bind_eq_bind, Option.bind_some,
        sSequenceFin_someW (f := fun i : Fin n => f i.succ) (g := fun i => g i.succ) (fun i => h i.succ),
        Option.bind_eq_bind, Option.bind_some]
      exact congrArg some (funext fun i => Fin.cases rfl (fun _ => rfl) i)

/-! ## The one-time signature -/

theorem sChainWalk_succW (P : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (i : ChainIndex) (start n : Nat) (v : Sphincs.Digest) :
    @chainWalk Option _ inst P lay tree leaf i start (n + 1) v =
      (@chainWalk Option _ inst P lay tree leaf i start n v).bind fun prev =>
        if hstep : start + n < chainLength - 1 then
          @tweakableHash Option _ inst P (.chain lay tree leaf i ⟨start + n, hstep⟩) (Sphincs.bytesLE 16 prev)
        else some 0 := by
  rw [chainWalk.eq_2]
  rfl

theorem sChainWalk_shiftW (P : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (i : ChainIndex) :
    ∀ (n start : Nat) (v : Sphincs.Digest) (hs : start < chainLength - 1), start + n + 1 ≤ chainLength - 1 →
      @chainWalk Option _ inst P lay tree leaf i start (n + 1) v =
        (@tweakableHash Option _ inst P (.chain lay tree leaf i ⟨start, hs⟩) (Sphincs.bytesLE 16 v)).bind fun v' =>
          @chainWalk Option _ inst P lay tree leaf i (start + 1) n v'
  | 0, start, v, hs, _ => by
      rw [sChainWalk_succW]
      simp only [Nat.add_zero, hs, ↓reduceDIte, chainWalk.eq_1, Option.pure_def, Option.bind_some]
      cases @tweakableHash Option _ inst P (.chain lay tree leaf i ⟨start, hs⟩) (Sphincs.bytesLE 16 v) <;> rfl
  | n + 1, start, v, hs, h => by
      have h1 : start + (n + 1) < chainLength - 1 := by omega
      have h2 : start + 1 + n < chainLength - 1 := by omega
      rw [sChainWalk_succW, sChainWalk_shiftW P lay tree leaf i n start v hs (by omega), Option.bind_assoc]
      simp only [h1, ↓reduceDIte]
      congr 1
      funext v'
      rw [sChainWalk_succW]
      simp only [h2, ↓reduceDIte]
      have : (⟨start + (n + 1), h1⟩ : ChainStep) = ⟨start + 1 + n, h2⟩ := Fin.ext (by simp only; omega)
      rw [this]

/-- **A one-time chain step over cells, answered.** -/
theorem sChainStep_cellsW (hq : SQW H inst) {pp a x : E} {lay : Layer} {tree : TreeIndex} {leaf : LeafIndex}
    {i : ChainIndex} {s : ChainStep} (ha : cellBytes a = tweakBytes (.chain lay tree leaf i s)) {o : E × E}
    (ho : hcellWith H [pp, a, x] = some o) :
    @tweakableHash Option _ inst (spp pp) (.chain lay tree leaf i s) (Sphincs.bytesLE 16 (sv x)) = some (sv o.1) := by
  apply sHash_cellsW hq _ ho
  show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ Sphincs.bytesLE 16 (sv x) = _
  rw [bytesLE_spp, bytesLE_sv, ← ha]
  simp

/-- **A one-time chain walked from digit `d` over cells, answered**, its step addresses
`idx + A(i, s)`. -/
theorem sRecoverChain_cellsW (hq : SQW H inst) {pp idx : E} {lay : Layer} {tree : TreeIndex} {leaf : LeafIndex}
    {i : ChainIndex}
    (hadr : ∀ (s : ChainStep), cellBytes (idx + eOfNat (tw 1 + i.val * hiMul + s.val * stepMul)) =
      tweakBytes (.chain lay tree leaf i s)) :
    ∀ (d : Digit) (x : E) {p : E × E}, tipPairWith H false pp (fun _ => 0) idx i.val d.val x = some p →
      @recoverChain Option _ inst (spp pp) lay tree leaf i d (sv x) = some (sv p.1) := by
  have hwalk : ∀ (n start : Nat) (x : E) {p : E × E}, start + n + 1 ≤ chainLength - 1 →
      chainFromWith H false pp (fun _ => 0) idx i.val n start x = some p →
      @chainWalk Option _ inst (spp pp) lay tree leaf i start (n + 1) (sv x) = some (sv p.1) := by
    intro n
    induction n with
    | zero =>
        intro start x p h hp
        rw [sChainWalk_shiftW _ _ _ _ _ _ _ _ (by omega) h, sChainStep_cellsW hq (hadr ⟨start, by omega⟩) hp]
        rfl
    | succ n ih =>
        intro start x p h hp
        simp only [chainFromWith, Option.bind_eq_some_iff] at hp
        obtain ⟨o, ho, hp⟩ := hp
        rw [sChainWalk_shiftW _ _ _ _ _ _ _ _ (by omega) h, sChainStep_cellsW hq (hadr ⟨start, by omega⟩) ho,
          Option.bind_some]
        exact ih (start + 1) _ (by omega) hp
  intro d x p hp
  have hd := d.isLt
  simp only [chainLength, winternitzBits] at hd
  by_cases h3 : d.val = 3
  · simp only [tipPairWith, h3, ↓reduceIte, Option.some.injEq] at hp
    subst hp
    simp only [recoverChain, h3, chainLength, winternitzBits]
    rw [show 2 ^ 2 - 1 - 3 = 0 from rfl, chainWalk.eq_1]
    rfl
  · simp only [tipPairWith, h3, ↓reduceIte] at hp
    simp only [recoverChain]
    rw [show chainLength - 1 - d.val = (2 - d.val) + 1 by simp [chainLength, winternitzBits]; omega]
    exact hwalk _ _ _ (by simp [chainLength, winternitzBits]; omega) hp

/-- **The one-time leaf over cells, answered.** -/
theorem sLeafHash_cellsW (hq : SQW H inst) {pp a : E} {lay : Layer} {tree : TreeIndex} {leaf : LeafIndex}
    (tips : Nat → E) (ha : cellBytes a = tweakBytes (.leaf lay tree leaf)) {o : E × E}
    (ho : hcellWith H (pp :: a :: (List.range numChains).map tips) = some o) :
    @leafHash Option _ inst (spp pp) lay tree leaf (fun i => sv (tips i.val)) = some (sv o.1) := by
  apply sHash_cellsW hq _ ho
  show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++
    (List.ofFn fun i : ChainIndex => sv (tips i.val)).flatMap (Sphincs.bytesLE 16) = _
  rw [bytesLE_spp, ← ha, show (List.ofFn fun i : ChainIndex => sv (tips i.val)) =
      ((List.range numChains).map tips).map sv
    from (ofFn_val_eq numChains (fun i => sv (tips i))).trans (List.map_map.symm)]
  exact (congrArg (fun t => cellBytes pp ++ cellBytes a ++ t) (sflatMap_bytesLE_sv _)).trans (by simp)

/-- **The one-time leaf, answered**: the encoding digest decodes, the chains recover their tips,
and the leaf is their hash. -/
theorem sOtsLeaf_someW {P : PublicParameter} {lay : Layer} {tree : TreeIndex} {leaf : LeafIndex}
    {msg : Sphincs.Digest} {ctr : Counter} {vals : ChainIndex → Sphincs.Digest} {dg : Sphincs.Digest}
    {enc : Encoding} {tips : ChainIndex → Sphincs.Digest} {lv : Sphincs.Digest}
    (henc : @tweakableHash Option _ inst P (.encoding lay tree leaf) (Sphincs.bytesLE 16 msg ++ Sphincs.bytesLE 4 ctr) =
      some dg)
    (hdec : TargetSum.decodeDigest dg = some enc)
    (hrec : ∀ i, @recoverChain Option _ inst P lay tree leaf i (enc i) (vals i) = some (tips i))
    (hleaf : @leafHash Option _ inst P lay tree leaf tips = some lv) :
    @otsLeaf Option _ inst P lay tree leaf msg ctr vals = some (some lv) := by
  have he : @encode Option _ inst P lay tree leaf msg ctr = some (some enc) := by
    rw [encode.eq_def]
    simp only [bind, pure]
    rw [henc, Option.bind_some, hdec]
  rw [otsLeaf.eq_def]
  simp only [bind, pure]
  rw [he, Option.bind_some]
  simp only
  rw [sSequenceFin_someW hrec, Option.bind_some, hleaf]
  rfl

/-! ## The tree -/

/-- **The tree over cells, answered**: the fold of a path whose addresses' bytes are the nodes'
tweaks, its bits the leaf's. -/
theorem sTreeFold_cellsW (hq : SQW H inst) {pp : E} {A : Nat → E} {lay : Layer} {tree : TreeIndex}
    {leaf : LeafIndex}
    (hA : ∀ l < maxLayerHeight, cellBytes (A l) = tweakBytes (.node lay tree (l + 1) (leaf.val / 2 ^ (l + 1))))
    (sibs : Nat → E) :
    ∀ m ≤ maxLayerHeight, ∀ (x : E) {r : E}, mFoldWith H pp A (fun l => leaf.val.testBit l) sibs m 0 x = some r →
      @treeFold Option _ inst (spp pp) lay tree leaf (fun l => sv (sibs l)) m (sv x) = some (sv r)
  | 0, _, x, r, h => by
      cases h
      rw [treeFold.eq_1]
      rfl
  | m + 1, hm, x, r, h => by
      rw [mFoldWith_succ, Option.bind_eq_some_iff] at h
      obtain ⟨y, hy, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨o, ho, rfl⟩ := h
      simp only [Nat.zero_add] at ho
      rw [treeFold.eq_2]
      simp only [bind]
      rw [sTreeFold_cellsW hq hA sibs m (by omega) x hy, Option.bind_some]
      split
      · next hb =>
        simp only [hb, ↓reduceIte] at ho
        apply sHash_cellsW hq _ ho
        show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (Sphincs.bytesLE 16 (sv (sibs m)) ++
          Sphincs.bytesLE 16 (sv _)) = _
        rw [bytesLE_spp, bytesLE_sv, bytesLE_sv, ← hA m (by omega)]
        simp
      · next hb =>
        simp only [hb, Bool.false_eq_true, ↓reduceIte] at ho
        apply sHash_cellsW hq _ ho
        show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (Sphincs.bytesLE 16 (sv _) ++
          Sphincs.bytesLE 16 (sv (sibs m))) = _
        rw [bytesLE_spp, bytesLE_sv, bytesLE_sv, ← hA m (by omega)]
        simp

/-! ## The message digest -/

theorem truncateMessageDigest_digestBits (d : Protocol.Digest) :
    truncateMessageDigest (Node.digestBits d) =
      BitVec.ofNat messageDigestBits (cellNat (digestScalars d).1 + 2 ^ 128 * cellNat (digestScalars d).2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  show ((Node.digestBits d).toNat >>> 0) % 2 ^ messageDigestBits = _
  rw [Nat.shiftRight_zero, digestBits_toNat]

/-- **The message digest over cells, answered**: the two cells of the answered hash of
`P | A | m | ρ`. -/
theorem sMessageDigest_cellsW (hq : SQW H inst) {pp a m0 m1 rho : E} {root : Sphincs.Digest} {m : Message}
    (ha : cellBytes a = tweakBytes .message) (hm : Sphincs.bytesLE 32 m = cellBytes m0 ++ cellBytes m1)
    {o : E × E} (ho : hcellWith H [pp, a, m0, m1, rho] = some o) :
    @messageDigest Option _ inst (spp pp) root m (sv rho) =
      some (BitVec.ofNat messageDigestBits (cellNat o.1 + 2 ^ 128 * cellNat o.2)) := by
  obtain ⟨d, hd, rfl⟩ := hbWith_some.mp ho
  have hI : tweakableHashInput (spp pp) .message (messageDigestPayload root m (sv rho)) =
      [pp, a, m0, m1, rho].flatMap cellBytes := by
    show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (Sphincs.bytesLE 32 m ++ Sphincs.bytesLE 16 (sv rho)) = _
    rw [bytesLE_spp, bytesLE_sv, ← ha, hm]
    simp
  rw [messageDigest.eq_def]
  simp only [messageDigestCall, oracleHash]
  rw [hq, hI, hd]
  show some (truncateMessageDigest (Node.digestBits d)) = _
  rw [truncateMessageDigest_digestBits]

/-! ## The forest -/

/-- `n` steps of forest chain `i` from position `s` over cells, under the key's address `ka`, every
hash answered by `H` (`fChain`). -/
def fChainWith (H : List UInt8 → Option Protocol.Digest) (pp ka : E) (i s : Nat) (v : E) : Nat → Option E
  | 0 => some v
  | n + 1 => (fChainWith H pp ka i s v n).bind fun y =>
      (hcellWith H [pp, ka + eOfNat (tw 15 + i * 2 ^ 43 + (s + n) * stepMul), y]).map Prod.fst

theorem fChainWith_deployed (pp ka : E) (i s : Nat) (v : E) :
    ∀ n, fChainWith HashModel.deployed.H pp ka i s v n = some (fChain pp ka i s v n)
  | 0 => rfl
  | n + 1 => by
      simp only [fChainWith, fChainWith_deployed pp ka i s v n, Option.bind_some, hcellWith_deployed,
        Option.map_some, fChain]

/-- **A forest chain over cells, answered.** -/
theorem sForestWalk_cellsW (hq : SQW H inst) {pp ka : E} {index : Index} {c : Coord} {s : SuperIdx}
    {j : SubIdx} {a : ChildIdx} {i : FChain}
    (hadr : ∀ t : FStep, cellBytes (ka + eOfNat (tw 15 + i.val * 2 ^ 43 + t.val * stepMul)) =
      tweakBytes (.fchain index c s j a i t)) (start : Nat) (x : E) :
    ∀ n, start + n ≤ chainTop → ∀ {r : E}, fChainWith H pp ka i.val start x n = some r →
      @forestWalk Option _ inst (spp pp) index c s j a i start n (sv x) = some (sv r)
  | 0, _, r, h => by
      cases h
      rw [forestWalk.eq_1]
      rfl
  | n + 1, hn, r, h => by
      simp only [fChainWith, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨y, hy, o, ho, rfl⟩ := h
      rw [forestWalk.eq_2]
      simp only [bind]
      rw [sForestWalk_cellsW hq hadr start x n (by omega) hy, Option.bind_some]
      simp only [show start + n < chainTop by omega, ↓reduceDIte]
      apply sHash_cellsW hq _ ho
      show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ Sphincs.bytesLE 16 (sv _) = _
      rw [bytesLE_spp, bytesLE_sv, ← hadr ⟨start + n, by omega⟩]
      simp

/-- The end of chain `k` of a child opened at `word` from the value `vals k`, answered (`fEnds`). -/
def fEndsWith (H : List UInt8 → Option Protocol.Digest) (pp ka : E) (word : Codeword) (vals : Nat → E) (k : Nat) :
    Option E :=
  fChainWith H pp ka k (4 - (word ⟨k % 6, Nat.mod_lt _ (by norm_num)⟩).val) (vals k)
    (word ⟨k % 6, Nat.mod_lt _ (by norm_num)⟩).val

/-- **A child leaf over cells, answered**: the answered hash of the six chain ends. -/
theorem sChildRecover_cellsW (hq : SQW H inst) {pp ka aL : E} {index : Index} {c : Coord} {s : SuperIdx}
    {j : SubIdx} {a : ChildIdx} (word : Codeword) (vals ends : Nat → E)
    (hadr : ∀ (i : FChain) (t : FStep), cellBytes (ka + eOfNat (tw 15 + i.val * 2 ^ 43 + t.val * stepMul)) =
      tweakBytes (.fchain index c s j a i t))
    (hL : cellBytes aL = tweakBytes (.childLeaf index c s j a))
    (hends : ∀ k < 6, fEndsWith H pp ka word vals k = some (ends k)) {o : E × E}
    (ho : hcellWith H (pp :: aL :: (List.range 6).map ends) = some o) :
    @childRecover Option _ inst (spp pp) index c s j a word (fun i => sv (vals i.val)) = some (sv o.1) := by
  have hrec : ∀ i : FChain, @forestRecoverChain Option _ inst (spp pp) index c s j a i (word i) (sv (vals i.val)) =
      some (sv (ends i.val)) := fun i => by
    have he := hends i.val i.isLt
    rw [fEndsWith, show (⟨i.val % 6, Nat.mod_lt _ (by norm_num)⟩ : FChain) = i from
      Fin.ext (Nat.mod_eq_of_lt i.isLt)] at he
    exact sForestWalk_cellsW hq (hadr i) _ _ _ (by have := (word i).isLt; simp only [chainTop] at this ⊢; omega) he
  rw [childRecover.eq_def]
  simp only [bind]
  rw [sSequenceFin_someW hrec, Option.bind_some]
  apply sHash_cellsW hq _ ho
  show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (List.ofFn _).flatMap (Sphincs.bytesLE 16) = _
  rw [bytesLE_spp, ← hL]
  show cellBytes pp ++ cellBytes aL ++
    (List.ofFn fun i : FChain => sv (ends i.val)).flatMap (Sphincs.bytesLE 16) = _
  rw [show (List.ofFn fun i : FChain => sv (ends i.val)) = ((List.range 6).map ends).map sv from
    (ofFn_val_eq childChains (fun k => sv (ends k))).trans List.map_map.symm]
  exact (congrArg (fun t => cellBytes pp ++ cellBytes aL ++ t) (sflatMap_bytesLE_sv _)).trans (by simp)

/-- A tree of the forest folded over cells, answered. -/
theorem sSubFold_cellsW (hq : SQW H inst) {pp : E} {A : Nat → E} {index : Index} {c : Coord} {s : SuperIdx}
    {j : SubIdx} {a : ChildIdx}
    (hA : ∀ (l : Fin subHeight) (node : ChildIdx), node.val = a.val / 2 ^ (l.val + 1) →
      cellBytes (A l.val) = tweakBytes (.subNode index c s j l node))
    (sibs : Nat → E) :
    ∀ m ≤ subHeight, ∀ (x : E) {r : E}, mFoldWith H pp A (fun l => a.val.testBit l) sibs m 0 x = some r →
      @subFold Option _ inst (spp pp) index c s j a (fun l => sv (sibs l.val)) m (sv x) = some (sv r)
  | 0, _, x, r, h => by
      cases h
      rw [subFold.eq_1]
      rfl
  | m + 1, hm, x, r, h => by
      rw [mFoldWith_succ, Option.bind_eq_some_iff] at h
      obtain ⟨y, hy, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨o, ho, rfl⟩ := h
      simp only [Nat.zero_add] at ho
      rw [subFold.eq_2]
      simp only [bind]
      rw [sSubFold_cellsW hq hA sibs m (by omega) x hy, Option.bind_some]
      simp only [show m < subHeight by omega, ↓reduceDIte]
      split
      · next hb =>
        simp only [hb, ↓reduceIte] at ho
        apply sHash_cellsW hq _ ho
        show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (Sphincs.bytesLE 16 (sv (sibs m)) ++
          Sphincs.bytesLE 16 (sv _)) = _
        rw [bytesLE_spp, bytesLE_sv, bytesLE_sv, ← hA ⟨m, by omega⟩ _ rfl]
        simp
      · next hb =>
        simp only [hb, Bool.false_eq_true, ↓reduceIte] at ho
        apply sHash_cellsW hq _ ho
        show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (Sphincs.bytesLE 16 (sv _) ++
          Sphincs.bytesLE 16 (sv (sibs m))) = _
        rw [bytesLE_spp, bytesLE_sv, bytesLE_sv, ← hA ⟨m, by omega⟩ _ rfl]
        simp

/-- A coordinate's top tree folded over cells, answered. -/
theorem sTopFold_cellsW (hq : SQW H inst) {pp : E} {A : Nat → E} {index : Index} {c : Coord} {s : SuperIdx}
    (hA : ∀ (l : Fin topHeight) (node : SuperIdx), node.val = s.val / 2 ^ (l.val + 1) →
      cellBytes (A l.val) = tweakBytes (.topNode index c l node))
    (sibs : Nat → E) :
    ∀ m ≤ topHeight, ∀ (x : E) {r : E}, mFoldWith H pp A (fun l => s.val.testBit l) sibs m 0 x = some r →
      @topFold Option _ inst (spp pp) index c s (fun l => sv (sibs l.val)) m (sv x) = some (sv r)
  | 0, _, x, r, h => by
      cases h
      rw [topFold.eq_1]
      rfl
  | m + 1, hm, x, r, h => by
      rw [mFoldWith_succ, Option.bind_eq_some_iff] at h
      obtain ⟨y, hy, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨o, ho, rfl⟩ := h
      simp only [Nat.zero_add] at ho
      rw [topFold.eq_2]
      simp only [bind]
      rw [sTopFold_cellsW hq hA sibs m (by omega) x hy, Option.bind_some]
      simp only [show m < topHeight by omega, ↓reduceDIte]
      split
      · next hb =>
        simp only [hb, ↓reduceIte] at ho
        apply sHash_cellsW hq _ ho
        show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (Sphincs.bytesLE 16 (sv (sibs m)) ++
          Sphincs.bytesLE 16 (sv _)) = _
        rw [bytesLE_spp, bytesLE_sv, bytesLE_sv, ← hA ⟨m, by omega⟩ _ rfl]
        simp
      · next hb =>
        simp only [hb, Bool.false_eq_true, ↓reduceIte] at ho
        apply sHash_cellsW hq _ ho
        show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (Sphincs.bytesLE 16 (sv _) ++
          Sphincs.bytesLE 16 (sv (sibs m))) = _
        rw [bytesLE_spp, bytesLE_sv, bytesLE_sv, ← hA ⟨m, by omega⟩ _ rfl]
        simp

/-- **A super-child over cells, answered.** -/
theorem sSuperHash_cellsW (hq : SQW H inst) {pp aS t00 t01 t10 t11 : E} {index : Index} {c : Coord}
    {s : SuperIdx} (hS : cellBytes aS = tweakBytes (.superChild index c s)) {o : E × E}
    (ho : hcellWith H [pp, aS, t00, t01, t10, t11] = some o) :
    @superHash Option _ inst (spp pp) index c s (fun j => if j = 0 then (sv t00, sv t01) else (sv t10, sv t11)) =
      some (sv o.1) := by
  apply sHash_cellsW hq _ ho
  show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ superPayload _ = _
  rw [bytesLE_spp, ← hS]
  simp [superPayload, nodePayload, bytesLE_sv]

/-- **A coordinate's recovery, answered**: each sub-tree's leaf and fold, the super-child and the top
fold. -/
theorem sCoordRecover_someW {P : PublicParameter} {index : Index} {c : Coord} {mark : CoordMark}
    {opening : CoordOpening} {leaf node : SubIdx → Sphincs.Digest} {sup top : Sphincs.Digest}
    (hleaf : ∀ j, @childRecover Option _ inst P index c mark.super j (mark.child j) (lut (mark.word j))
      (opening.sub j).values = some (leaf j))
    (hnode : ∀ j, @subFold Option _ inst P index c mark.super j (mark.child j) (opening.sub j).path (subHeight - 1)
      (leaf j) = some (node j))
    (hsup : @superHash Option _ inst P index c mark.super (fun j =>
      orderTops ((mark.child j).val.testBit (subHeight - 1)) (node j) ((opening.sub j).path subTopLevel)) = some sup)
    (htop : @topFold Option _ inst P index c mark.super opening.top (topHeight - 1) sup = some top) :
    @coordRecover Option _ inst P index c mark opening =
      some (orderTops (mark.super.val.testBit (topHeight - 1)) top (opening.top topTopLevel)) := by
  rw [coordRecover.eq_def]
  simp only [bind, pure]
  rw [sSequenceFin_someW (g := fun j => orderTops ((mark.child j).val.testBit (subHeight - 1)) (node j)
    ((opening.sub j).path subTopLevel)) (fun j => by rw [hleaf j, Option.bind_some, hnode j, Option.bind_some]),
    Option.bind_some, hsup, Option.bind_some, htop]
  rfl

/-- **The forest key over cells, answered**: the answered hash of the sixteen top nodes. -/
theorem sForestRecover_cellsW (hq : SQW H inst) {pp aR : E} {index : Index} {marks : Coord → CoordMark}
    {opening : Coord → CoordOpening} (T : Nat → E)
    (hc : ∀ c : Coord, @coordRecover Option _ inst (spp pp) index c (marks c) (opening c) =
      some (sv (T (2 * c.val)), sv (T (2 * c.val + 1))))
    (hR : cellBytes aR = tweakBytes (.roots index)) {o : E × E}
    (ho : hcellWith H (pp :: aR :: (List.range 16).map T) = some o) :
    @forestRecover Option _ inst (spp pp) index marks opening = some (sv o.1) := by
  rw [forestRecover.eq_def]
  simp only [bind]
  rw [sSequenceFin_someW hc, Option.bind_some]
  apply sHash_cellsW hq _ ho
  show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ rootsPayload _ = _
  rw [bytesLE_spp, ← hR]
  simp only [rootsPayload, nodePayload]
  show cellBytes pp ++ cellBytes aR ++ (List.ofFn fun c : Coord => (sv (T (2 * c.val)), sv (T (2 * c.val + 1)))).flatMap
    (fun p => Sphincs.bytesLE 16 p.1 ++ Sphincs.bytesLE 16 p.2) = _
  rw [show (List.ofFn fun c : Coord => (sv (T (2 * c.val)), sv (T (2 * c.val + 1)))) =
      (List.range 8).map (fun k => (sv (T (2 * k)), sv (T (2 * k + 1)))) from
    ofFn_val_eq forestCoords (fun k => (sv (T (2 * k)), sv (T (2 * k + 1))))]
  simp [List.range_succ, bytesLE_sv]

/-! ## Verification -/

/-- **Verification, answered**: the message digest, the forest key it selects, the one-time leaf and
the tree reaching the key's root. -/
theorem sVerify_of {pk : PublicKey} {msg : Message} {σ : Signature} {D : MessageDigest} {fk leaf : Sphincs.Digest}
    (hD : @messageDigest Option _ inst pk.parameter pk.root msg σ.randomness = some D)
    (hF : @forestRecover Option _ inst pk.parameter (digestIndex D) (digestMarks D) σ.forest = some fk)
    (hots : @otsLeaf Option _ inst pk.parameter topLayer 0 (leafIndexAt (digestIndex D) topLayer) fk
      (σ.layers topLayer).counter (σ.layers topLayer).chainValues = some (some leaf))
    (htree : @treeFold Option _ inst pk.parameter topLayer 0 (leafIndexAt (digestIndex D) topLayer)
      (signaturePath σ topLayer) (layerHeight topLayer) leaf = some pk.root) :
    @Sphincs.Concrete.verify Option _ inst pk msg σ = some true := by
  have hL : @verifyLayers Option _ inst pk.parameter (digestIndex D) σ numLayers fk = some (some pk.root) := by
    rw [show numLayers = 0 + 1 from rfl, verifyLayers.eq_2]
    simp only [bind, pure, show (0 : Nat) < numLayers from Nat.one_pos, ↓reduceDIte, treeIndexAt]
    have hots' : @otsLeaf Option _ inst pk.parameter ⟨0, Nat.one_pos⟩ 0
        (leafIndexAt (digestIndex D) ⟨0, Nat.one_pos⟩) fk (σ.layers ⟨0, Nat.one_pos⟩).counter
        (σ.layers ⟨0, Nat.one_pos⟩).chainValues = some (some leaf) := hots
    have htree' : @treeFold Option _ inst pk.parameter ⟨0, Nat.one_pos⟩ 0
        (leafIndexAt (digestIndex D) ⟨0, Nat.one_pos⟩) (signaturePath σ ⟨0, Nat.one_pos⟩)
        (layerHeight ⟨0, Nat.one_pos⟩) leaf = some pk.root := htree
    rw [hots', Option.bind_some]
    simp only
    rw [htree', Option.bind_some, verifyLayers.eq_1]
    rfl
  rw [Sphincs.Concrete.verify.eq_def]
  simp only [bind, pure]
  rw [hD, Option.bind_some, hF, Option.bind_some, hL, Option.bind_some]
  simp

end
end LeanVM.Guest.B1.Sig
