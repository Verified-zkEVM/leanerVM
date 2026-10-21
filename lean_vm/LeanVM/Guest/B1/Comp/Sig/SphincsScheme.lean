/-
  LeanVM.Guest.B1.Comp.Sig.SphincsScheme

  leanSPHINCS verification with an answered hash, taken apart: a run in `Option` that returns is
  the answered values of the guest's cells, so every string the guest's cells hash is answered.
-/

module

public import LeanVM.Guest.B1.Comp.Sig.Values
public import LeanVM.Guest.B1.Sig.Model.SphincsScheme

/-!
# leanSPHINCS runs with an answered hash, taken apart

The leanSPHINCS counterpart of `Comp/Sig/XmssScheme.lean`: each routine of the scheme run in
`Option` under an answered hash is an *equation* in the cells' answered values (`…_cellsE`), so a
run that returns `some` answers every string its cells hash; the compound runs are taken apart
(`…_someInv`): the one-time leaf, a child leaf, a coordinate, the forest key, the verification.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Value Sphincs Sphincs.Concrete

@[expose] public section

variable {H : List UInt8 → Option Protocol.Digest} {inst : HasQuery Sphincs.HashSpec Option}

/-- **A hash of bytes, as an equation**: the run is the first cell of the bytes' answered hash. -/
theorem sHash_bytesE (hq : SQW H inst) {P : PublicParameter} {dom : HashDomain} {payload : HashInput}
    {r : List UInt8} (h : tweakableHashInput P dom payload = r) :
    @tweakableHash Option _ inst P dom payload = (hbWith H r).map fun o => sv o.1 := by
  cases ho : hbWith H r with
  | none =>
      rw [tweakableHash.eq_def]
      simp only [oracleHash]
      rw [hq, h]
      unfold hbWith at ho
      rw [Option.map_eq_none_iff] at ho
      rw [ho]
      rfl
  | some o => exact sHash_bytesW hq h ho

/-- **A hash of cells, as an equation.** -/
theorem sHash_cellsE (hq : SQW H inst) {P : PublicParameter} {dom : HashDomain} {payload : HashInput}
    {cs : List E} (h : tweakableHashInput P dom payload = cs.flatMap cellBytes) :
    @tweakableHash Option _ inst P dom payload = (hcellWith H cs).map fun o => sv o.1 :=
  sHash_bytesE hq h

theorem sSequenceFin_some_invW {α : Type} : ∀ {n : Nat} {f : Fin n → Option α} {g : Fin n → α},
    Sphincs.Concrete.sequenceFin f = some g → ∀ i, f i = some (g i)
  | 0, _, _, _, i => i.elim0
  | n + 1, f, g, h, i => by
      simp only [Sphincs.Concrete.sequenceFin] at h
      rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨a, ha, h⟩ := h
      rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨t, ht, h⟩ := h
      have hg : g = Fin.cases a t := (Option.some.inj h).symm
      subst hg
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ha
      · exact sSequenceFin_some_invW (f := fun j : Fin n => f j.succ) ht j

/-! ## The one-time signature -/

/-- A one-time chain step over cells, as an equation (`sChainStep_cellsW`). -/
theorem sChainStep_cellsE (hq : SQW H inst) {pp a x : E} {lay : Layer} {tree : TreeIndex}
    {leaf : LeafIndex} {i : ChainIndex} {s : ChainStep} (ha : cellBytes a = tweakBytes (.chain lay tree leaf i s)) :
    @tweakableHash Option _ inst (spp pp) (.chain lay tree leaf i s) (Sphincs.bytesLE 16 (sv x)) =
      (hcellWith H [pp, a, x]).map fun o => sv o.1 := by
  apply sHash_cellsE hq
  show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ Sphincs.bytesLE 16 (sv x) = _
  rw [bytesLE_spp, bytesLE_sv, ← ha]
  simp

/-- **A one-time chain walked over cells, as an equation**, its step addresses `idx + A(i, s)`. -/
theorem sChainWalk_cellsE (hq : SQW H inst) {pp idx : E} {lay : Layer} {tree : TreeIndex}
    {leaf : LeafIndex} {i : ChainIndex}
    (hadr : ∀ (s : ChainStep), cellBytes (idx + eOfNat (tw 1 + i.val * hiMul + s.val * stepMul)) =
      tweakBytes (.chain lay tree leaf i s)) :
    ∀ (n start : Nat) (x : E), start + n + 1 ≤ chainLength - 1 →
      @chainWalk Option _ inst (spp pp) lay tree leaf i start (n + 1) (sv x) =
        (chainFromWith H false pp (fun _ => 0) idx i.val n start x).map fun p => sv p.1 := by
  intro n
  induction n with
  | zero =>
      intro start x h
      rw [sChainWalk_shiftW _ _ _ _ _ _ _ _ (by omega) h, sChainStep_cellsE hq (hadr ⟨start, by omega⟩),
        show chainFromWith H false pp (fun _ => 0) idx i.val 0 start x =
          hcellWith H [pp, idx + eOfNat (tw 1 + i.val * hiMul + start * stepMul), x] from rfl]
      cases hcellWith H [pp, idx + eOfNat (tw 1 + i.val * hiMul + start * stepMul), x] <;> rfl
  | succ n ih =>
      intro start x h
      rw [sChainWalk_shiftW _ _ _ _ _ _ _ _ (by omega) h, sChainStep_cellsE hq (hadr ⟨start, by omega⟩),
        show chainFromWith H false pp (fun _ => 0) idx i.val (n + 1) start x =
          (hcellWith H [pp, idx + eOfNat (tw 1 + i.val * hiMul + start * stepMul), x]).bind fun h =>
            chainFromWith H false pp (fun _ => 0) idx i.val n (start + 1) h.1 from rfl]
      cases hcellWith H [pp, idx + eOfNat (tw 1 + i.val * hiMul + start * stepMul), x] with
      | none => rfl
      | some o =>
          simp only [Option.map_some, Option.bind_some]
          exact ih (start + 1) o.1 (by omega)

/-- **A one-time chain recovered from digit `d` over cells, as an equation**
(`sRecoverChain_cellsW`). -/
theorem sRecoverChain_cellsE (hq : SQW H inst) {pp idx : E} {lay : Layer} {tree : TreeIndex}
    {leaf : LeafIndex} {i : ChainIndex}
    (hadr : ∀ (s : ChainStep), cellBytes (idx + eOfNat (tw 1 + i.val * hiMul + s.val * stepMul)) =
      tweakBytes (.chain lay tree leaf i s)) (d : Digit) (x : E) :
    @recoverChain Option _ inst (spp pp) lay tree leaf i d (sv x) =
      (tipPairWith H false pp (fun _ => 0) idx i.val d.val x).map fun p => sv p.1 := by
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
    exact sChainWalk_cellsE hq hadr _ _ _ (by simp [chainLength, winternitzBits]; omega)

/-- The one-time leaf over cells, as an equation (`sLeafHash_cellsW`). -/
theorem sLeafHash_cellsE (hq : SQW H inst) {pp a : E} {lay : Layer} {tree : TreeIndex} {leaf : LeafIndex}
    (tips : Nat → E) (ha : cellBytes a = tweakBytes (.leaf lay tree leaf)) :
    @leafHash Option _ inst (spp pp) lay tree leaf (fun i => sv (tips i.val)) =
      (hcellWith H (pp :: a :: (List.range numChains).map tips)).map fun o => sv o.1 := by
  apply sHash_cellsE hq
  show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++
    (List.ofFn fun i : ChainIndex => sv (tips i.val)).flatMap (Sphincs.bytesLE 16) = _
  rw [bytesLE_spp, ← ha, show (List.ofFn fun i : ChainIndex => sv (tips i.val)) =
      ((List.range numChains).map tips).map sv
    from (ofFn_val_eq numChains (fun i => sv (tips i))).trans (List.map_map.symm)]
  exact (congrArg (fun t => cellBytes pp ++ cellBytes a ++ t) (sflatMap_bytesLE_sv _)).trans (by simp)

/-- **The one-time leaf, taken apart** (the converse of `sOtsLeaf_someW`). -/
theorem sOtsLeaf_someInv {P : PublicParameter} {lay : Layer} {tree : TreeIndex} {leaf : LeafIndex}
    {msg : Sphincs.Digest} {ctr : Counter} {vals : ChainIndex → Sphincs.Digest} {lv : Sphincs.Digest}
    (h : @otsLeaf Option _ inst P lay tree leaf msg ctr vals = some (some lv)) :
    ∃ (dg : Sphincs.Digest) (enc : Encoding) (tips : ChainIndex → Sphincs.Digest),
      @tweakableHash Option _ inst P (.encoding lay tree leaf) (Sphincs.bytesLE 16 msg ++ Sphincs.bytesLE 4 ctr) =
        some dg ∧ TargetSum.decodeDigest dg = some enc ∧
      (∀ i, @recoverChain Option _ inst P lay tree leaf i (enc i) (vals i) = some (tips i)) ∧
      @leafHash Option _ inst P lay tree leaf tips = some lv := by
  rw [otsLeaf.eq_def] at h
  simp only [bind, pure] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨oe, hoe, h⟩ := h
  rw [encode.eq_def] at hoe
  simp only [bind, pure] at hoe
  rw [Option.bind_eq_some_iff] at hoe
  obtain ⟨dg, hdg, hoe⟩ := hoe
  cases oe with
  | none => exact absurd h (by simp)
  | some enc =>
    simp only [Option.some.injEq] at hoe
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨tips, htips, l', hl', e⟩ := h
    obtain rfl : l' = lv := by simpa using e
    have hr : ∀ i, @recoverChain Option _ inst P lay tree leaf i (enc i) (vals i) = some (tips i) :=
      sSequenceFin_some_invW htips
    exact ⟨dg, enc, tips, hdg, hoe, hr, hl'⟩

/-! ## The tree -/

/-- **The tree over cells, as an equation** (`sTreeFold_cellsW`). -/
theorem sTreeFold_cellsE (hq : SQW H inst) {pp : E} {A : Nat → E} {lay : Layer} {tree : TreeIndex}
    {leaf : LeafIndex}
    (hA : ∀ l < maxLayerHeight, cellBytes (A l) = tweakBytes (.node lay tree (l + 1) (leaf.val / 2 ^ (l + 1))))
    (sibs : Nat → E) :
    ∀ m ≤ maxLayerHeight, ∀ (x : E),
      @treeFold Option _ inst (spp pp) lay tree leaf (fun l => sv (sibs l)) m (sv x) =
        (mFoldWith H pp A (fun l => leaf.val.testBit l) sibs m 0 x).map sv
  | 0, _, x => by rw [treeFold.eq_1]; rfl
  | m + 1, hm, x => by
      rw [mFoldWith_succ, treeFold.eq_2]
      simp only [bind]
      rw [sTreeFold_cellsE hq hA sibs m (by omega) x]
      cases mFoldWith H pp A (fun l => leaf.val.testBit l) sibs m 0 x with
      | none => rfl
      | some y =>
          simp only [Option.map_some, Option.bind_some, Nat.zero_add]
          split
          · next hb =>
            rw [sHash_cellsE hq (cs := [pp, A m, sibs m, y])]
            · cases hcellWith H [pp, A m, sibs m, y] <;> rfl
            · show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (Sphincs.bytesLE 16 (sv (sibs m)) ++
                Sphincs.bytesLE 16 (sv _)) = _
              rw [bytesLE_spp, bytesLE_sv, bytesLE_sv, ← hA m (by omega)]
              simp
          · next hb =>
            rw [sHash_cellsE hq (cs := [pp, A m, y, sibs m])]
            · cases hcellWith H [pp, A m, y, sibs m] <;> rfl
            · show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (Sphincs.bytesLE 16 (sv _) ++
                Sphincs.bytesLE 16 (sv (sibs m))) = _
              rw [bytesLE_spp, bytesLE_sv, bytesLE_sv, ← hA m (by omega)]
              simp

/-! ## The message digest -/

/-- **The message digest over cells, as an equation** (`sMessageDigest_cellsW`). -/
theorem sMessageDigest_cellsE (hq : SQW H inst) {pp a m0 m1 rho : E} {root : Sphincs.Digest} {m : Message}
    (ha : cellBytes a = tweakBytes .message) (hm : Sphincs.bytesLE 32 m = cellBytes m0 ++ cellBytes m1) :
    @messageDigest Option _ inst (spp pp) root m (sv rho) =
      (hcellWith H [pp, a, m0, m1, rho]).map fun o =>
        BitVec.ofNat messageDigestBits (cellNat o.1 + 2 ^ 128 * cellNat o.2) := by
  cases ho : hcellWith H [pp, a, m0, m1, rho] with
  | none =>
      have hI : tweakableHashInput (spp pp) .message (messageDigestPayload root m (sv rho)) =
          [pp, a, m0, m1, rho].flatMap cellBytes := by
        show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (Sphincs.bytesLE 32 m ++ Sphincs.bytesLE 16 (sv rho)) = _
        rw [bytesLE_spp, bytesLE_sv, ← ha, hm]
        simp
      unfold hcellWith hbWith at ho
      rw [Option.map_eq_none_iff] at ho
      rw [messageDigest.eq_def]
      simp only [messageDigestCall, oracleHash]
      rw [hq, hI, ho]
      rfl
  | some o => exact sMessageDigest_cellsW hq ha hm ho

/-! ## The forest -/

/-- **A forest chain over cells, as an equation** (`sForestWalk_cellsW`). -/
theorem sForestWalk_cellsE (hq : SQW H inst) {pp ka : E} {index : Index} {c : Coord} {s : SuperIdx}
    {j : SubIdx} {a : ChildIdx} {i : FChain}
    (hadr : ∀ t : FStep, cellBytes (ka + eOfNat (tw 15 + i.val * 2 ^ 43 + t.val * stepMul)) =
      tweakBytes (.fchain index c s j a i t)) (start : Nat) (x : E) :
    ∀ n, start + n ≤ chainTop →
      @forestWalk Option _ inst (spp pp) index c s j a i start n (sv x) =
        (fChainWith H pp ka i.val start x n).map sv
  | 0, _ => by rw [forestWalk.eq_1]; rfl
  | n + 1, hn => by
      rw [forestWalk.eq_2]
      simp only [bind]
      rw [sForestWalk_cellsE hq hadr start x n (by omega)]
      simp only [fChainWith]
      cases fChainWith H pp ka i.val start x n with
      | none => rfl
      | some y =>
          simp only [Option.map_some, Option.bind_some, show start + n < chainTop by omega, ↓reduceDIte]
          rw [sHash_cellsE hq (cs := [pp, ka + eOfNat (tw 15 + i.val * 2 ^ 43 + (start + n) * stepMul), y])]
          · cases hcellWith H [pp, ka + eOfNat (tw 15 + i.val * 2 ^ 43 + (start + n) * stepMul), y] <;> rfl
          · show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ Sphincs.bytesLE 16 (sv _) = _
            rw [bytesLE_spp, bytesLE_sv, ← hadr ⟨start + n, by omega⟩]
            simp

/-- **A child leaf, taken apart** (the converse of `sChildRecover_cellsW`): its six chain ends are
answered, and so is the hash of the ends. -/
theorem sChildRecover_someInv (hq : SQW H inst) {pp ka aL : E} {index : Index} {c : Coord} {s : SuperIdx}
    {j : SubIdx} {a : ChildIdx} (word : Codeword) (vals : Nat → E)
    (hadr : ∀ (i : FChain) (t : FStep), cellBytes (ka + eOfNat (tw 15 + i.val * 2 ^ 43 + t.val * stepMul)) =
      tweakBytes (.fchain index c s j a i t))
    (hL : cellBytes aL = tweakBytes (.childLeaf index c s j a)) {v : Sphincs.Digest}
    (h : @childRecover Option _ inst (spp pp) index c s j a word (fun i => sv (vals i.val)) = some v) :
    ∃ ends : Nat → E, (∀ k < 6, fEndsWith H pp ka word vals k = some (ends k)) ∧
      ∃ o, hcellWith H (pp :: aL :: (List.range 6).map ends) = some o ∧ v = sv o.1 := by
  rw [childRecover.eq_def] at h
  simp only [bind] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨E6, hE6, h⟩ := h
  have hrec := sSequenceFin_some_invW hE6
  have hends : ∀ i : FChain, ∃ e, fEndsWith H pp ka word vals i.val = some e ∧ E6 i = sv e := by
    intro i
    have he := hrec i
    simp only [forestRecoverChain] at he
    rw [sForestWalk_cellsE hq (hadr i) _ _ _ (by have := (word i).isLt; simp only [chainTop] at this ⊢; omega)]
      at he
    obtain ⟨e, he1, he2⟩ := Option.map_eq_some_iff.mp he
    refine ⟨e, ?_, he2.symm⟩
    rw [fEndsWith, show (⟨i.val % 6, Nat.mod_lt _ (by norm_num)⟩ : FChain) = i from
      Fin.ext (Nat.mod_eq_of_lt i.isLt)]
    exact he1
  choose ends0 hends0 using hends
  let ends : Nat → E := fun k => if hk : k < 6 then ends0 ⟨k, hk⟩ else 0
  have hE : E6 = fun i => sv (ends i.val) := funext fun i => by
    show E6 i = sv (if hk : i.val < 6 then ends0 ⟨i.val, hk⟩ else 0)
    simp only [show i.val < 6 from i.isLt, ↓reduceDIte]
    exact (hends0 i).2
  refine ⟨ends, fun k hk => by
    show fEndsWith H pp ka word vals k = some (if hk : k < 6 then ends0 ⟨k, hk⟩ else 0)
    simp only [hk, ↓reduceDIte]; exact (hends0 ⟨k, hk⟩).1, ?_⟩
  rw [hE] at h
  have e := sHash_cellsE (H := H) hq (P := spp pp) (dom := .childLeaf index c s j a)
    (payload := childPayload fun i : FChain => sv (ends i.val)) (cs := pp :: aL :: (List.range 6).map ends) (by
      show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (List.ofFn _).flatMap (Sphincs.bytesLE 16) = _
      rw [bytesLE_spp, ← hL]
      show cellBytes pp ++ cellBytes aL ++
        (List.ofFn fun i : FChain => sv (ends i.val)).flatMap (Sphincs.bytesLE 16) = _
      rw [show (List.ofFn fun i : FChain => sv (ends i.val)) = ((List.range 6).map ends).map sv from
        (ofFn_val_eq childChains (fun k => sv (ends k))).trans List.map_map.symm]
      exact (congrArg (fun t => cellBytes pp ++ cellBytes aL ++ t) (sflatMap_bytesLE_sv _)).trans (by simp))
  have h' : @tweakableHash Option _ inst (spp pp) (.childLeaf index c s j a)
      (childPayload fun i : FChain => sv (ends i.val)) = some v := h
  rw [e] at h'
  obtain ⟨o, ho, hv⟩ := Option.map_eq_some_iff.mp h'
  exact ⟨o, ho, hv.symm⟩

/-- **A tree of the forest folded over cells, as an equation** (`sSubFold_cellsW`). -/
theorem sSubFold_cellsE (hq : SQW H inst) {pp : E} {A : Nat → E} {index : Index} {c : Coord} {s : SuperIdx}
    {j : SubIdx} {a : ChildIdx}
    (hA : ∀ (l : Fin subHeight) (node : ChildIdx), node.val = a.val / 2 ^ (l.val + 1) →
      cellBytes (A l.val) = tweakBytes (.subNode index c s j l node))
    (sibs : Nat → E) :
    ∀ m ≤ subHeight, ∀ (x : E),
      @subFold Option _ inst (spp pp) index c s j a (fun l => sv (sibs l.val)) m (sv x) =
        (mFoldWith H pp A (fun l => a.val.testBit l) sibs m 0 x).map sv
  | 0, _, x => by rw [subFold.eq_1]; rfl
  | m + 1, hm, x => by
      rw [mFoldWith_succ, subFold.eq_2]
      simp only [bind]
      rw [sSubFold_cellsE hq hA sibs m (by omega) x]
      cases mFoldWith H pp A (fun l => a.val.testBit l) sibs m 0 x with
      | none => rfl
      | some y =>
          simp only [Option.map_some, Option.bind_some, Nat.zero_add, show m < subHeight by omega,
            ↓reduceDIte]
          split
          · next hb =>
            rw [sHash_cellsE hq (cs := [pp, A m, sibs m, y])]
            · cases hcellWith H [pp, A m, sibs m, y] <;> rfl
            · show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (Sphincs.bytesLE 16 (sv (sibs m)) ++
                Sphincs.bytesLE 16 (sv _)) = _
              rw [bytesLE_spp, bytesLE_sv, bytesLE_sv, ← hA ⟨m, by omega⟩ _ rfl]
              simp
          · next hb =>
            rw [sHash_cellsE hq (cs := [pp, A m, y, sibs m])]
            · cases hcellWith H [pp, A m, y, sibs m] <;> rfl
            · show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (Sphincs.bytesLE 16 (sv _) ++
                Sphincs.bytesLE 16 (sv (sibs m))) = _
              rw [bytesLE_spp, bytesLE_sv, bytesLE_sv, ← hA ⟨m, by omega⟩ _ rfl]
              simp

/-- **A coordinate's top tree folded over cells, as an equation** (`sTopFold_cellsW`). -/
theorem sTopFold_cellsE (hq : SQW H inst) {pp : E} {A : Nat → E} {index : Index} {c : Coord} {s : SuperIdx}
    (hA : ∀ (l : Fin topHeight) (node : SuperIdx), node.val = s.val / 2 ^ (l.val + 1) →
      cellBytes (A l.val) = tweakBytes (.topNode index c l node))
    (sibs : Nat → E) :
    ∀ m ≤ topHeight, ∀ (x : E),
      @topFold Option _ inst (spp pp) index c s (fun l => sv (sibs l.val)) m (sv x) =
        (mFoldWith H pp A (fun l => s.val.testBit l) sibs m 0 x).map sv
  | 0, _, x => by rw [topFold.eq_1]; rfl
  | m + 1, hm, x => by
      rw [mFoldWith_succ, topFold.eq_2]
      simp only [bind]
      rw [sTopFold_cellsE hq hA sibs m (by omega) x]
      cases mFoldWith H pp A (fun l => s.val.testBit l) sibs m 0 x with
      | none => rfl
      | some y =>
          simp only [Option.map_some, Option.bind_some, Nat.zero_add, show m < topHeight by omega,
            ↓reduceDIte]
          split
          · next hb =>
            rw [sHash_cellsE hq (cs := [pp, A m, sibs m, y])]
            · cases hcellWith H [pp, A m, sibs m, y] <;> rfl
            · show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (Sphincs.bytesLE 16 (sv (sibs m)) ++
                Sphincs.bytesLE 16 (sv _)) = _
              rw [bytesLE_spp, bytesLE_sv, bytesLE_sv, ← hA ⟨m, by omega⟩ _ rfl]
              simp
          · next hb =>
            rw [sHash_cellsE hq (cs := [pp, A m, y, sibs m])]
            · cases hcellWith H [pp, A m, y, sibs m] <;> rfl
            · show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (Sphincs.bytesLE 16 (sv _) ++
                Sphincs.bytesLE 16 (sv (sibs m))) = _
              rw [bytesLE_spp, bytesLE_sv, bytesLE_sv, ← hA ⟨m, by omega⟩ _ rfl]
              simp

/-- **A super-child over cells, as an equation** (`sSuperHash_cellsW`). -/
theorem sSuperHash_cellsE (hq : SQW H inst) {pp aS t00 t01 t10 t11 : E} {index : Index} {c : Coord}
    {s : SuperIdx} (hS : cellBytes aS = tweakBytes (.superChild index c s)) :
    @superHash Option _ inst (spp pp) index c s (fun j => if j = 0 then (sv t00, sv t01) else (sv t10, sv t11)) =
      (hcellWith H [pp, aS, t00, t01, t10, t11]).map fun o => sv o.1 := by
  apply sHash_cellsE hq
  show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ superPayload _ = _
  rw [bytesLE_spp, ← hS]
  simp [superPayload, nodePayload, bytesLE_sv]

/-- **A coordinate's recovery, taken apart** (the converse of `sCoordRecover_someW`): each sub-tree's
leaf and fold, the super-child and the top fold return. -/
theorem sCoordRecover_someInv {P : PublicParameter} {index : Index} {c : Coord} {mark : CoordMark}
    {opening : CoordOpening} {x : Sphincs.Digest × Sphincs.Digest}
    (h : @coordRecover Option _ inst P index c mark opening = some x) :
    ∃ (leaf node : SubIdx → Sphincs.Digest) (sup top : Sphincs.Digest),
      (∀ j, @childRecover Option _ inst P index c mark.super j (mark.child j) (lut (mark.word j))
        (opening.sub j).values = some (leaf j)) ∧
      (∀ j, @subFold Option _ inst P index c mark.super j (mark.child j) (opening.sub j).path (subHeight - 1)
        (leaf j) = some (node j)) ∧
      @superHash Option _ inst P index c mark.super (fun j =>
        orderTops ((mark.child j).val.testBit (subHeight - 1)) (node j) ((opening.sub j).path subTopLevel)) =
        some sup ∧
      @topFold Option _ inst P index c mark.super opening.top (topHeight - 1) sup = some top ∧
      x = orderTops (mark.super.val.testBit (topHeight - 1)) top (opening.top topTopLevel) := by
  rw [coordRecover.eq_def] at h
  simp only [bind, pure] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨tops, htops, h⟩ := h
  have hj := sSequenceFin_some_invW htops
  have hj' : ∀ j, ∃ l n, @childRecover Option _ inst P index c mark.super j (mark.child j) (lut (mark.word j))
      (opening.sub j).values = some l ∧ @subFold Option _ inst P index c mark.super j (mark.child j)
        (opening.sub j).path (subHeight - 1) l = some n ∧
      tops j = orderTops ((mark.child j).val.testBit (subHeight - 1)) n ((opening.sub j).path subTopLevel) := by
    intro j
    have := hj j
    simp only [Option.bind_eq_some_iff] at this
    obtain ⟨l, hl, n, hn, e⟩ := this
    exact ⟨l, n, hl, hn, (Option.some.inj e).symm⟩
  choose leaf node hl hn ht using hj'
  have htops' : tops = fun j => orderTops ((mark.child j).val.testBit (subHeight - 1)) (node j)
      ((opening.sub j).path subTopLevel) := funext ht
  subst htops'
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨sup, hsup, top, htop, e⟩ := h
  exact ⟨leaf, node, sup, top, hl, hn, hsup, htop, (Option.some.inj e).symm⟩

/-- **The forest key, taken apart** (the converse of `sForestRecover_cellsW`). -/
theorem sForestRecover_someInv {P : PublicParameter} {index : Index} {marks : Coord → CoordMark}
    {opening : Coord → CoordOpening} {fk : Sphincs.Digest}
    (h : @forestRecover Option _ inst P index marks opening = some fk) :
    ∃ tops : Coord → Sphincs.Digest × Sphincs.Digest,
      (∀ c, @coordRecover Option _ inst P index c (marks c) (opening c) = some (tops c)) ∧
      @tweakableHash Option _ inst P (.roots index) (rootsPayload tops) = some fk := by
  rw [forestRecover.eq_def] at h
  simp only [bind] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨tops, htops, h⟩ := h
  exact ⟨tops, sSequenceFin_some_invW htops, h⟩

/-- The sixteen top nodes' bytes, as cells (`sForestRecover_cellsW`'s payload). -/
theorem rootsPayload_cells {pp aR : E} {index : Index} (hR : cellBytes aR = tweakBytes (.roots index))
    (T : Nat → E) :
    tweakableHashInput (spp pp) (.roots index)
      (rootsPayload fun c : Coord => (sv (T (2 * c.val)), sv (T (2 * c.val + 1)))) =
      (pp :: aR :: (List.range 16).map T).flatMap cellBytes := by
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

/-- **Verification, taken apart** (the converse of `sVerify_of`): the message digest, the forest
key it selects, the one-time leaf and the tree reaching the key's root. -/
theorem sVerify_someInv {pk : PublicKey} {msg : Message} {σ : Signature}
    (h : @Sphincs.Concrete.verify Option _ inst pk msg σ = some true) :
    ∃ (D : MessageDigest) (fk leaf : Sphincs.Digest),
      @messageDigest Option _ inst pk.parameter pk.root msg σ.randomness = some D ∧
      @forestRecover Option _ inst pk.parameter (digestIndex D) (digestMarks D) σ.forest = some fk ∧
      @otsLeaf Option _ inst pk.parameter topLayer 0 (leafIndexAt (digestIndex D) topLayer) fk
        (σ.layers topLayer).counter (σ.layers topLayer).chainValues = some (some leaf) ∧
      @treeFold Option _ inst pk.parameter topLayer 0 (leafIndexAt (digestIndex D) topLayer)
        (signaturePath σ topLayer) (layerHeight topLayer) leaf = some pk.root := by
  rw [Sphincs.Concrete.verify.eq_def] at h
  simp only [bind, pure] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨D, hD, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨fk, hF, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨oL, hL, h⟩ := h
  cases oL with
  | none => exact absurd h (by simp)
  | some r =>
    simp only [Option.some.injEq, decide_eq_true_eq] at h
    subst h
    rw [show numLayers = 0 + 1 from rfl, verifyLayers.eq_2] at hL
    simp only [bind, pure, show (0 : Nat) < numLayers from Nat.one_pos, ↓reduceDIte, treeIndexAt] at hL
    rw [Option.bind_eq_some_iff] at hL
    obtain ⟨ol, hol, hL⟩ := hL
    cases ol with
    | none => exact absurd hL (by simp)
    | some leaf =>
      simp only at hL
      rw [Option.bind_eq_some_iff] at hL
      obtain ⟨root, hroot, hL⟩ := hL
      rw [verifyLayers.eq_1] at hL
      obtain rfl : root = pk.root := by simpa using hL
      exact ⟨D, fk, leaf, hD, hF, hol, hroot⟩

end
end LeanVM.Guest.B1.Sig
