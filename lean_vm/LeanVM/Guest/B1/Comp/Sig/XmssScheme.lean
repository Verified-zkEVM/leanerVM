/-
  LeanVM.Guest.B1.Comp.Sig.XmssScheme

  leanXMSS verification with an answered hash, taken apart: a run in `Option` that returns is
  the answered values of the guest's cells, so every string the guest's cells hash is answered.
-/

module

public import LeanVM.Guest.B1.Comp.Sig.Values

/-!
# leanXMSS runs with an answered hash, taken apart

`Model/XmssScheme.lean` builds the scheme's `Option` run from the answered hashes of the guest's
cells (`tweakableHash_cellsW`, `recoverChain_cellsW`, …). The completeness needs the converse: a
run that returns `some` answers every hash it makes, so the cells' answered values exist. Each
routine here is an *equation*: the run is the cells' answered value, mapped (`…_cellsE`), so a
`some` of the run is a `some` of the cells. `layerRoot_someW` and `verify_someW` take the
layers and the verification apart.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Value LeanXmss LeanXmss.Concrete

@[expose] public section

variable {H : List UInt8 → Option Protocol.Digest} {inst : HasQuery LeanXmss.HashSpec Option}

/-- **A hash of cells, as an equation**: the run is the first cell of the cells' answered hash. -/
theorem tweakableHash_cellsE (hq : XQW H inst) {P : PublicParameter} {dom : HashDomain}
    {payload : HashInput} {cs : List E} (h : tweakableHashInput P dom payload = cs.flatMap cellBytes) :
    @tweakableHash Option _ inst P dom payload = (hcellWith H cs).map fun o => xv o.1 := by
  cases ho : hcellWith H cs with
  | none =>
      rw [tweakableHash.eq_def]
      simp only [oracleHash]
      rw [hq, h]
      unfold hcellWith hbWith at ho
      rw [Option.map_eq_none_iff] at ho
      rw [ho]
      rfl
  | some o => exact tweakableHash_cellsW hq h ho

/-- A chain step over cells, as an equation (`chainStep_cellsW`). -/
theorem chainStep_cellsE (hq : XQW H inst) {pp a x : E} {lay : Layer} {key : KeyIndex}
    {i : ChainIndex} {s : ChainStep} (ha : cellBytes a = tweakBytes (.chain lay key s)) :
    @tweakableHash Option _ inst (xpp pp) (.chain lay key s) (chainPayload i (xv x)) =
      (hcellWith H [pp, a, x, eOfNat i.val]).map fun o => xv o.1 := by
  cases ho : hcellWith H [pp, a, x, eOfNat i.val] with
  | none =>
      have e : tweakableHashInput (xpp pp) (.chain lay key s) (chainPayload i (xv x)) =
          [pp, a, x, eOfNat i.val].flatMap cellBytes := by
        show bytesLE 16 (xpp pp) ++ tweakBytes _ ++ (bytesLE 16 (xv x) ++
          bytesLE 16 (BitVec.ofNat 128 i.val)) = _
        rw [bytesLE_xpp, bytesLE_xv, ← ha,
          bytesLE_ofNat_cell (by have := i.isLt; simp [numChains] at this; omega)]
        simp
      rw [tweakableHash_cellsE hq e, ho]
  | some o => exact chainStep_cellsW hq ha ho

/-- **A chain walked over cells, as an equation** (`recoverChain_cellsW`'s walk). -/
theorem chainWalk_cellsE (hq : XQW H inst) {pp : E} {adr : Nat → E} {lay : Layer} {key : KeyIndex}
    {i : ChainIndex} (hadr : ∀ (s : ChainStep), cellBytes (adr s) = tweakBytes (.chain lay key s)) :
    ∀ (n start : Nat) (x : E), start + n + 1 ≤ chainLength - 1 →
      @chainWalk Option _ inst (xpp pp) lay key i start (n + 1) (xv x) =
        (chainFromWith H true pp adr 0 i.val n start x).map fun p => xv p.1 := by
  intro n
  induction n with
  | zero =>
      intro start x h
      rw [chainWalk_shiftW _ _ _ _ _ _ _ (by omega) h, chainStep_cellsE hq (hadr ⟨start, by omega⟩),
        show chainFromWith H true pp adr 0 i.val 0 start x = hcellWith H [pp, adr start, x, eOfNat i.val]
          from rfl]
      cases hcellWith H [pp, adr start, x, eOfNat i.val] <;> rfl
  | succ n ih =>
      intro start x h
      rw [chainWalk_shiftW _ _ _ _ _ _ _ (by omega) h, chainStep_cellsE hq (hadr ⟨start, by omega⟩)]
      rw [show chainFromWith H true pp adr 0 i.val (n + 1) start x =
        (hcellWith H [pp, adr start, x, eOfNat i.val]).bind fun h =>
          chainFromWith H true pp adr 0 i.val n (start + 1) h.1 from rfl]
      cases hcellWith H [pp, adr start, x, eOfNat i.val] with
      | none => rfl
      | some o =>
          simp only [Option.map_some, Option.bind_some]
          exact ih (start + 1) o.1 (by omega)

/-- **A chain recovered from digit `d` over cells, as an equation** (`recoverChain_cellsW`). -/
theorem recoverChain_cellsE (hq : XQW H inst) {pp : E} {adr : Nat → E} {lay : Layer}
    {key : KeyIndex} {i : ChainIndex}
    (hadr : ∀ (s : ChainStep), cellBytes (adr s) = tweakBytes (.chain lay key s)) (d : Digit) (x : E) :
    @recoverChain Option _ inst (xpp pp) lay key i d (xv x) =
      (tipPairWith H true pp adr 0 i.val d.val x).map fun p => xv p.1 := by
  have hd := d.isLt
  simp only [chainLength, winternitzBits] at hd
  by_cases h3 : d.val = 3
  · simp only [tipPairWith, h3, ↓reduceIte, Option.map_some]
    simp only [recoverChain, h3, chainLength, winternitzBits]
    rw [show 2 ^ 2 - 1 - 3 = 0 from rfl, chainWalk.eq_1]
    rfl
  · simp only [tipPairWith, h3, ↓reduceIte]
    simp only [recoverChain]
    rw [show chainLength - 1 - d.val = (2 - d.val) + 1 by simp [chainLength, winternitzBits]; omega]
    exact chainWalk_cellsE hq hadr _ _ _ (by simp [chainLength, winternitzBits]; omega)

/-- The one-time leaf over cells, as an equation (`leafHash_cellsW`). -/
theorem leafHash_cellsE (hq : XQW H inst) {pp a : E} {lay : Layer} {key : KeyIndex} (tips : Nat → E)
    (ha : cellBytes a = tweakBytes (.leaf lay key)) :
    @leafHash Option _ inst (xpp pp) lay key (fun i => xv (tips i.val)) =
      (hcellWith H (pp :: a :: (List.range numChains).map tips)).map fun o => xv o.1 := by
  apply tweakableHash_cellsE hq
  show bytesLE 16 (xpp pp) ++ tweakBytes _ ++ (List.ofFn fun i : ChainIndex => xv (tips i.val)).flatMap
    (bytesLE 16) = _
  rw [bytesLE_xpp, ← ha, show (List.ofFn fun i : ChainIndex => xv (tips i.val)) =
    ((List.range numChains).map tips).map xv from (ofFn_val_eq numChains (fun i => xv (tips i))).trans
      (List.map_map.symm)]
  exact (congrArg (fun t => cellBytes pp ++ cellBytes a ++ t) (flatMap_bytesLE_xv _)).trans (by simp)

/-- The message digest over cells, as an equation (`messageDigest_cellsW`). -/
theorem messageDigest_cellsE (hq : XQW H inst) {pp a rho : E} {lay : Layer} {key : KeyIndex}
    {Mi : HashInput} {cs : List E} (ha : cellBytes a = tweakBytes (.message lay key))
    (hM : Mi = cs.flatMap cellBytes) :
    @messageDigest Option _ inst (xpp pp) lay key Mi (xv rho) =
      (hcellWith H (pp :: a :: cs ++ [rho])).map fun o => xv o.1 := by
  apply tweakableHash_cellsE hq
  show bytesLE 16 (xpp pp) ++ tweakBytes _ ++ (Mi ++ bytesLE 16 (xv rho)) = _
  rw [bytesLE_xpp, bytesLE_xv, ← ha, hM]
  simp

/-- **A layer's tree over cells, as an equation** (`treeFold_cellsW`). -/
theorem treeFold_cellsE (hq : XQW H inst) {pp : E} {A : Nat → E} {lay : Layer} {key : KeyIndex}
    (hA : ∀ l < layerHeight, cellBytes (A l) = tweakBytes (.node lay (l + 1) (key.val / 2 ^ (l + 1))))
    (sibs : Nat → E) :
    ∀ m ≤ layerHeight, ∀ (x : E),
      @treeFold Option _ inst (xpp pp) lay key (fun l => xv (sibs l.val)) m (xv x) =
        (mFoldWith H pp A (fun l => key.val.testBit l) sibs m 0 x).map xv
  | 0, _, x => by rw [treeFold.eq_1]; rfl
  | m + 1, hm, x => by
      rw [mFoldWith_succ, treeFold.eq_2]
      simp only [bind]
      rw [treeFold_cellsE hq hA sibs m (by omega) x]
      cases hy : mFoldWith H pp A (fun l => key.val.testBit l) sibs m 0 x with
      | none => rfl
      | some y =>
          simp only [Option.map_some, Option.bind_some, dite_of (show m < layerHeight by omega),
            Nat.zero_add]
          split
          · next hb =>
            rw [tweakableHash_cellsE hq (cs := [pp, A m, sibs m, y])]
            · cases hcellWith H [pp, A m, sibs m, y] <;> rfl
            · show bytesLE 16 (xpp pp) ++ tweakBytes _ ++ (bytesLE 16 (xv (sibs m)) ++ bytesLE 16 (xv _)) = _
              rw [bytesLE_xpp, bytesLE_xv, bytesLE_xv, ← hA m (by omega)]
              simp
          · next hb =>
            rw [tweakableHash_cellsE hq (cs := [pp, A m, y, sibs m])]
            · cases hcellWith H [pp, A m, y, sibs m] <;> rfl
            · show bytesLE 16 (xpp pp) ++ tweakBytes _ ++ (bytesLE 16 (xv _) ++ bytesLE 16 (xv (sibs m))) = _
              rw [bytesLE_xpp, bytesLE_xv, bytesLE_xv, ← hA m (by omega)]
              simp

/-! ## The layers and the verification, taken apart -/

theorem sequenceFin_some_invW {α : Type} : ∀ {n : Nat} {f : Fin n → Option α} {g : Fin n → α},
    LeanXmss.Concrete.sequenceFin f = some g → ∀ i, f i = some (g i)
  | 0, _, _, _, i => i.elim0
  | n + 1, f, g, h, i => by
      simp only [LeanXmss.Concrete.sequenceFin] at h
      rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨a, ha, h⟩ := h
      rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨t, ht, h⟩ := h
      have hg : g = Fin.cases a t := (Option.some.inj h).symm
      subst hg
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ha
      · exact sequenceFin_some_invW (f := fun j : Fin n => f j.succ) ht j

/-- **A layer's root, taken apart** (the converse of `layerRoot_cellsW`): the message digest, its
codeword, the recovered chains, the leaf and the tree all return. -/
theorem layerRoot_someW {P : PublicParameter} {lay : Layer} {key : KeyIndex} {Mi : HashInput}
    {part : LayerSignature} {root : LeanXmss.Digest}
    (h : @layerRoot Option _ inst P lay key Mi part = some (some root)) :
    ∃ (d : LeanXmss.Digest) (enc : Encoding) (tips : ChainIndex → LeanXmss.Digest) (leaf : LeanXmss.Digest),
      @messageDigest Option _ inst P lay key Mi part.randomness = some d ∧
      Codeword.decode d = some enc ∧
      (∀ i, @recoverChain Option _ inst P lay key i (enc i) (part.chainValues i) = some (tips i)) ∧
      @leafHash Option _ inst P lay key tips = some leaf ∧
      @treeFold Option _ inst P lay key part.path layerHeight leaf = some root := by
  rw [layerRoot.eq_def] at h
  simp only [bind, pure] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨ol, hol, h⟩ := h
  cases ol with
  | none => exact absurd h (by simp)
  | some leaf =>
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨r, hr, hrr⟩ := h
    obtain rfl : r = root := by simpa using hrr
    rw [otsLeaf.eq_def] at hol
    simp only [bind, pure] at hol
    rw [Option.bind_eq_some_iff] at hol
    obtain ⟨d, hd, hol⟩ := hol
    cases henc : Codeword.decode d with
    | none => simp [henc] at hol
    | some enc =>
      simp only [henc] at hol
      rw [Option.bind_eq_some_iff] at hol
      obtain ⟨tips, htips, hol⟩ := hol
      rw [Option.bind_eq_some_iff] at hol
      obtain ⟨l', hl', e⟩ := hol
      obtain rfl : l' = leaf := by simpa using e
      exact ⟨d, enc, tips, l', hd, henc, sequenceFin_some_invW htips, hl', hr⟩

/-- **Verification, taken apart** (the converse of `verify_of_roots`). -/
theorem verify_someW {pk : PublicKey} {msg : Message} {σ : Signature}
    (h : @LeanXmss.Concrete.verify Option _ inst pk msg σ = some true) :
    ∃ r0, @layerRoot Option _ inst pk.parameter bottomLayer (keyAt σ.leafIndex bottomLayer)
        (bytesLE 32 msg) (σ.layers bottomLayer) = some (some r0) ∧
      @layerRoot Option _ inst pk.parameter topLayer (keyAt σ.leafIndex topLayer) (bytesLE 16 r0)
        (σ.layers topLayer) = some (some pk.root) := by
  rw [LeanXmss.Concrete.verify.eq_def] at h
  simp only [bind, pure] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨o0, h0, h⟩ := h
  cases o0 with
  | none => exact absurd h (by simp)
  | some r0 =>
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨o1, h1, h⟩ := h
    cases o1 with
    | none => exact absurd h (by simp)
    | some r =>
      simp only [Option.some.injEq, decide_eq_true_eq] at h
      exact ⟨r0, h0, h ▸ h1⟩

end
end LeanVM.Guest.B1.Sig
