/-
  LeanVM.Guest.B1.Sig.Model.XmssScheme

  leanXMSS verification with an answered hash (`Node.xmssVerifyWith`) over the guest's cells: each
  routine run in `Option` under the hash `H` is `some` of the cells' answered hashes.
-/

module

public import LeanVM.Guest.B1.Sig.XmssScheme
public import LeanVM.Guest.B1.Sig.Model.Merkle

/-!
# leanXMSS over cells, with an answered hash

`Node.xmssVerifyWith H` runs `LeanXmss.Concrete.verify` in `Option` with the oracle
`fun x ↦ digestBits <$> H x`. As `XmssScheme` does for BLAKE2s, the lemmas here hold for any
oracle instance on `Option` with the hypothesis `XQW H` that it is that one, so the kernel never
compares instances. A routine whose hashes are the answered hashes of the guest's cells
(`hcellWith`, `tipPairWith`, `mFoldWith`) runs to `some` of their first cells:
`tweakableHash_cellsW`, `recoverChain_cellsW`, `leafHash_cellsW`, `messageDigest_cellsW`,
`treeFold_cellsW`, and `layerRoot_cellsW`, `verify_of_roots` put them together.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Value LeanXmss LeanXmss.Concrete

@[expose] public section

/-- The oracle answers `H`, its digests read as bits. -/
def XQW (H : List UInt8 → Option Protocol.Digest) (inst : HasQuery LeanXmss.HashSpec Option) : Prop :=
  ∀ x, (inst.query (spec := LeanXmss.HashSpec) x : Option HashOutput) = Node.digestBits <$> H x

theorem xqw_with (H : List UInt8 → Option Protocol.Digest) : XQW H ⟨fun x ↦ Node.digestBits <$> H x⟩ :=
  fun _ => rfl

variable {H : List UInt8 → Option Protocol.Digest} {inst : HasQuery LeanXmss.HashSpec Option}

/-- **A hash of cells, answered**: a tweakable hash whose input is the bytes of cells is the first
cell of their answered hash. -/
theorem tweakableHash_cellsW (hq : XQW H inst) {P : PublicParameter} {dom : HashDomain}
    {payload : HashInput} {cs : List E} {o : E × E}
    (h : tweakableHashInput P dom payload = cs.flatMap cellBytes) (ho : hcellWith H cs = some o) :
    @tweakableHash Option _ inst P dom payload = some (xv o.1) := by
  obtain ⟨d, hd, rfl⟩ := hbWith_some.mp ho
  rw [tweakableHash.eq_def]
  simp only [oracleHash]
  rw [hq, h, hd]
  show some (truncateHash (Node.digestBits d)) = _
  rw [truncateHash_digestBits]
  rfl

/-- **A chain step over cells, answered.** -/
theorem chainStep_cellsW (hq : XQW H inst) {pp a x : E} {lay : Layer} {key : KeyIndex} {i : ChainIndex}
    {s : ChainStep} (ha : cellBytes a = tweakBytes (.chain lay key s)) {o : E × E}
    (ho : hcellWith H [pp, a, x, eOfNat i.val] = some o) :
    @tweakableHash Option _ inst (xpp pp) (.chain lay key s) (chainPayload i (xv x)) = some (xv o.1) := by
  apply tweakableHash_cellsW hq _ ho
  show bytesLE 16 (xpp pp) ++ tweakBytes _ ++ (bytesLE 16 (xv x) ++ bytesLE 16 (BitVec.ofNat 128 i.val)) = _
  rw [bytesLE_xpp, bytesLE_xv, ← ha, bytesLE_ofNat_cell (by have := i.isLt; simp [numChains] at this; omega)]
  simp

theorem chainWalk_succW (P : PublicParameter) (lay : Layer) (key : KeyIndex) (i : ChainIndex) (start n : Nat)
    (v : LeanXmss.Digest) :
    @chainWalk Option _ inst P lay key i start (n + 1) v =
      (@chainWalk Option _ inst P lay key i start n v).bind fun prev =>
        if hstep : start + n < chainLength - 1 then
          @tweakableHash Option _ inst P (.chain lay key ⟨start + n, hstep⟩) (chainPayload i prev)
        else some 0 := by
  rw [chainWalk.eq_2]
  rfl

/-- The first step of a walk taken first, in `Option`. -/
theorem chainWalk_shiftW (P : PublicParameter) (lay : Layer) (key : KeyIndex) (i : ChainIndex) :
    ∀ (n start : Nat) (v : LeanXmss.Digest) (hs : start < chainLength - 1), start + n + 1 ≤ chainLength - 1 →
      @chainWalk Option _ inst P lay key i start (n + 1) v =
        (@tweakableHash Option _ inst P (.chain lay key ⟨start, hs⟩) (chainPayload i v)).bind fun v' =>
          @chainWalk Option _ inst P lay key i (start + 1) n v'
  | 0, start, v, hs, _ => by
      rw [chainWalk_succW]
      simp only [Nat.add_zero, hs, ↓reduceDIte, chainWalk.eq_1, Option.pure_def, Option.bind_some]
      cases @tweakableHash Option _ inst P (.chain lay key ⟨start, hs⟩) (chainPayload i v) <;> rfl
  | n + 1, start, v, hs, h => by
      have h1 : start + (n + 1) < chainLength - 1 := by omega
      have h2 : start + 1 + n < chainLength - 1 := by omega
      rw [chainWalk_succW, chainWalk_shiftW P lay key i n start v hs (by omega), Option.bind_assoc]
      simp only [h1, ↓reduceDIte]
      congr 1
      funext v'
      rw [chainWalk_succW]
      simp only [h2, ↓reduceDIte]
      have : (⟨start + (n + 1), h1⟩ : ChainStep) = ⟨start + 1 + n, h2⟩ := Fin.ext (by simp only; omega)
      rw [this]

/-- **A chain walked from digit `d` over cells, answered.** -/
theorem recoverChain_cellsW (hq : XQW H inst) {pp : E} {adr : Nat → E} {lay : Layer} {key : KeyIndex}
    {i : ChainIndex} (hadr : ∀ (s : ChainStep), cellBytes (adr s) = tweakBytes (.chain lay key s)) :
    ∀ (d : Digit) (x : E) {p : E × E}, tipPairWith H true pp adr 0 i.val d.val x = some p →
      @recoverChain Option _ inst (xpp pp) lay key i d (xv x) = some (xv p.1) := by
  have hwalk : ∀ (n start : Nat) (x : E) {p : E × E}, start + n + 1 ≤ chainLength - 1 →
      chainFromWith H true pp adr 0 i.val n start x = some p →
      @chainWalk Option _ inst (xpp pp) lay key i start (n + 1) (xv x) = some (xv p.1) := by
    intro n
    induction n with
    | zero =>
        intro start x p h hp
        rw [chainWalk_shiftW _ _ _ _ _ _ _ (by omega) h, chainStep_cellsW hq (hadr ⟨start, by omega⟩) hp]
        rfl
    | succ n ih =>
        intro start x p h hp
        simp only [chainFromWith, Option.bind_eq_some_iff] at hp
        obtain ⟨o, ho, hp⟩ := hp
        rw [chainWalk_shiftW _ _ _ _ _ _ _ (by omega) h, chainStep_cellsW hq (hadr ⟨start, by omega⟩) ho,
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
theorem leafHash_cellsW (hq : XQW H inst) {pp a : E} {lay : Layer} {key : KeyIndex} (tips : Nat → E)
    (ha : cellBytes a = tweakBytes (.leaf lay key)) {o : E × E}
    (ho : hcellWith H (pp :: a :: (List.range numChains).map tips) = some o) :
    @leafHash Option _ inst (xpp pp) lay key (fun i => xv (tips i.val)) = some (xv o.1) := by
  apply tweakableHash_cellsW hq _ ho
  show bytesLE 16 (xpp pp) ++ tweakBytes _ ++ (List.ofFn fun i : ChainIndex => xv (tips i.val)).flatMap (bytesLE 16) = _
  rw [bytesLE_xpp, ← ha, show (List.ofFn fun i : ChainIndex => xv (tips i.val)) = ((List.range numChains).map tips).map xv
    from (ofFn_val_eq numChains (fun i => xv (tips i))).trans (List.map_map.symm)]
  exact (congrArg (fun t => cellBytes pp ++ cellBytes a ++ t) (flatMap_bytesLE_xv _)).trans (by simp)

/-- **The message digest over cells, answered.** -/
theorem messageDigest_cellsW (hq : XQW H inst) {pp a rho : E} {lay : Layer} {key : KeyIndex} {Mi : HashInput}
    {cs : List E} (ha : cellBytes a = tweakBytes (.message lay key)) (hM : Mi = cs.flatMap cellBytes) {o : E × E}
    (ho : hcellWith H (pp :: a :: cs ++ [rho]) = some o) :
    @messageDigest Option _ inst (xpp pp) lay key Mi (xv rho) = some (xv o.1) := by
  apply tweakableHash_cellsW hq _ ho
  show bytesLE 16 (xpp pp) ++ tweakBytes _ ++ (Mi ++ bytesLE 16 (xv rho)) = _
  rw [bytesLE_xpp, bytesLE_xv, ← ha, hM]
  simp

/-- A path's fold, its last level taken last, answered. -/
theorem mFoldWith_succ (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) :
    ∀ (m l : Nat) (x : E), mFoldWith H pp A bits sibs (m + 1) l x =
      (mFoldWith H pp A bits sibs m l x).bind fun y =>
        (hcellWith H [pp, A (l + m), if bits (l + m) then sibs (l + m) else y,
          if bits (l + m) then y else sibs (l + m)]).map Prod.fst
  | 0, l, x => by
      simp only [mFoldWith, Nat.add_zero, Option.bind_some]
      cases hcellWith H [pp, A l, if bits l then sibs l else x, if bits l then x else sibs l] <;> rfl
  | m + 1, l, x => by
      rw [mFoldWith, mFoldWith]
      simp only [Option.bind_assoc]
      congr 1
      funext h
      rw [mFoldWith_succ pp A bits sibs m (l + 1)]
      simp only [show l + 1 + m = l + (m + 1) by omega]

/-- **A layer's tree over cells, answered**: the fold of a path whose addresses' bytes are the
nodes' tweaks, its bits the key's. -/
theorem treeFold_cellsW (hq : XQW H inst) {pp : E} {A : Nat → E} {lay : Layer} {key : KeyIndex}
    (hA : ∀ l < layerHeight, cellBytes (A l) = tweakBytes (.node lay (l + 1) (key.val / 2 ^ (l + 1))))
    (sibs : Nat → E) :
    ∀ m ≤ layerHeight, ∀ (x : E) {r : E}, mFoldWith H pp A (fun l => key.val.testBit l) sibs m 0 x = some r →
      @treeFold Option _ inst (xpp pp) lay key (fun l => xv (sibs l.val)) m (xv x) = some (xv r)
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
      rw [treeFold_cellsW hq hA sibs m (by omega) x hy, Option.bind_some, dite_of (by omega)]
      split
      · next hb =>
        simp only [hb, ↓reduceIte] at ho
        apply tweakableHash_cellsW hq _ ho
        show bytesLE 16 (xpp pp) ++ tweakBytes _ ++ (bytesLE 16 (xv (sibs m)) ++ bytesLE 16 (xv _)) = _
        rw [bytesLE_xpp, bytesLE_xv, bytesLE_xv, ← hA m (by omega)]
        simp
      · next hb =>
        simp only [hb, Bool.false_eq_true, ↓reduceIte] at ho
        apply tweakableHash_cellsW hq _ ho
        show bytesLE 16 (xpp pp) ++ tweakBytes _ ++ (bytesLE 16 (xv _) ++ bytesLE 16 (xv (sibs m))) = _
        rw [bytesLE_xpp, bytesLE_xv, bytesLE_xv, ← hA m (by omega)]
        simp

/-! ## The layers and the verification -/

theorem sequenceFin_someW {α : Type} : ∀ {n : Nat} {f : Fin n → Option α} {g : Fin n → α},
    (∀ i, f i = some (g i)) → LeanXmss.Concrete.sequenceFin f = some g
  | 0, f, g, _ => by
      simp only [LeanXmss.Concrete.sequenceFin]
      exact congrArg some (funext fun i => i.elim0)
  | n + 1, f, g, h => by
      simp only [LeanXmss.Concrete.sequenceFin]
      rw [h 0, Option.bind_eq_bind, Option.bind_some,
        sequenceFin_someW (f := fun i : Fin n => f i.succ) (g := fun i => g i.succ) (fun i => h i.succ),
        Option.bind_eq_bind, Option.bind_some]
      exact congrArg some (funext fun i => Fin.cases rfl (fun _ => rfl) i)

/-- **A layer's root, answered**: the message digest decodes, the chains recover their tips, the
leaf and the tree. -/
theorem layerRoot_cellsW {P : PublicParameter} {lay : Layer} {key : KeyIndex} {Mi : HashInput}
    {part : LayerSignature} {d : LeanXmss.Digest} {enc : Encoding} {tips : ChainIndex → LeanXmss.Digest}
    {leaf root : LeanXmss.Digest}
    (hd : @messageDigest Option _ inst P lay key Mi part.randomness = some d)
    (hdec : Codeword.decode d = some enc)
    (htips : ∀ i, @recoverChain Option _ inst P lay key i (enc i) (part.chainValues i) = some (tips i))
    (hleaf : @leafHash Option _ inst P lay key tips = some leaf)
    (hroot : @treeFold Option _ inst P lay key part.path layerHeight leaf = some root) :
    @layerRoot Option _ inst P lay key Mi part = some (some root) := by
  have hots : @otsLeaf Option _ inst P lay key Mi part.randomness part.chainValues = some (some leaf) := by
    rw [otsLeaf.eq_def]
    simp only [bind, pure]
    rw [hd, Option.bind_some]
    simp only [hdec]
    rw [sequenceFin_someW htips, Option.bind_some, hleaf]
    rfl
  rw [layerRoot.eq_def]
  simp only [bind, pure]
  rw [hots, Option.bind_some]
  simp only
  rw [hroot]
  rfl

/-- **Verification, answered**: the bottom layer's root, then the top layer's from it, is the
key's. -/
theorem verify_of_roots {pk : PublicKey} {msg : Message} {σ : Signature} {r0 : LeanXmss.Digest}
    (h0 : @layerRoot Option _ inst pk.parameter bottomLayer (keyAt σ.leafIndex bottomLayer) (bytesLE 32 msg)
      (σ.layers bottomLayer) = some (some r0))
    (h1 : @layerRoot Option _ inst pk.parameter topLayer (keyAt σ.leafIndex topLayer) (bytesLE 16 r0)
      (σ.layers topLayer) = some (some pk.root)) :
    @LeanXmss.Concrete.verify Option _ inst pk msg σ = some true := by
  rw [LeanXmss.Concrete.verify.eq_def]
  simp only [bind, pure]
  rw [h0, Option.bind_some]
  simp only
  rw [h1, Option.bind_some]
  simp

end
end LeanVM.Guest.B1.Sig
