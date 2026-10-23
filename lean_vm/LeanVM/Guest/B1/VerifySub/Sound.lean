/-
  LeanVM.Guest.B1.VerifySub.Sound

  **`verify_sub` is sound**: a run of its body gives a child proof, read off its valuation,
  the memory and the frame map, that the deferring verifier accepts.
-/

module

public import LeanVM.Guest.B1.VerifySub.Back
public import LeanVM.Guest.B1.VerifySub.Stack
-- DISPATCH_IMPORT
public import LeanVM.Guest.B1.Terminal.Holds
public import LeanVM.Guest.B1.Ring.Target
public import LeanVM.Guest.B1.Selectors.ColumnSelector
public import LeanVM.Guest.B1.Selectors.SelectorTables
public import LeanVM.Guest.B1.KeccakGkr.VkHolds
public import LeanVM.Guest.B1.Main.SoundV

/-!
# `verify_sub` is sound

`verify_sub_sound_w`: for a bytecode of `2^23` words, on a memory image of at most `2^32` words,
under any call relation below `coreProgram.Rel` that unfolds at the frame map `V`, a run of
`verify_sub`'s body with the exponent tables at its arguments `4`, `5` returns nothing, and the
deferring verifier accepts the child proof `vsPiOf L.read σ V` for the statement at its
arguments: `Main.SubSoundW bytecode vsPiOf`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem readsAt_cons_uniq {rd : Reader} {p : E} {xs ys : List E} (hl : xs.length = ys.length)
    (hx : ReadsAt rd p xs) (hy : ReadsAt rd p ys) : xs = ys := readsAt_ext hl hx hy

/-- The announced words are the memory's log, the rows and the rate, as integer words. -/
theorem vsWords_eq {bytecode : List K} {C : CallRel} {rd : Reader} {σ : Val}
    (F : VsFront bytecode C rd σ) :
    vsWords σ = eOfNat F.logMem :: F.rowsN.map eOfNat ++ [eOfNat F.lir] := by
  have hr : [σ (.n 39), σ (.n 49), σ (.n 59), σ (.n 82), σ (.n 92), σ (.n 102)] =
      F.rowsN.map eOfNat := by
    refine readsAt_ext (by simp [F.hrowsL]) (fun k hk ↦ ?_) F.hrows
    simp only [List.length_cons, List.length_nil] at hk
    have := F.hrw k hk
    interval_cases k <;> exact this
  rw [vsWords, ← hr, ← F.e29, ← F.e112]
  rfl


theorem stackClaims_values (L : Layout) (claims : List ColumnClaim) (out : ColumnClaim)
    (rp sl chs : List E) : (stackClaims L claims [out] rp sl chs).map (·.2) =
      polyEval (sl.map (phiMap · chs)) gen :: ((notLanes claims).map (·.value) ++ [out.value]) := by
  simp [stackClaims, ringSwitchClaim, ColumnClaim.onStack, notLanes]

theorem stackClaims_length (L : Layout) (claims : List ColumnClaim) (out : ColumnClaim)
    (rp sl chs : List E) :
    (stackClaims L claims [out] rp sl chs).length = (notLanes claims).length + 2 := by
  simp [stackClaims, notLanes]

theorem stackClaims_weight (L : Layout) (claims : List ColumnClaim) (out : ColumnClaim)
    (rp sl chs : List E) (lam : E) (x : List E) :
    dot (powers lam (stackClaims L claims [out] rp sl chs).length)
        ((stackClaims L claims [out] rp sl chs).map fun c ↦ c.1 x) =
      stackWeight L (openedClaims claims [out]) rp (ringCoefficients chs) lam x := rfl

/-- **`verify_sub` is sound**, its child proof read off its valuation, the memory and the frame
map. -/
theorem verify_sub_sound_w (bytecode : List K) : Main.SubSoundW bytecode vsPiOf := by
  intro hbl κ L hκ C V hU hLe σ rets hb hpre
  have hexp : ExpTables L.read (σ (.n 4)) (σ (.n 5)) := by
    simpa [VerifySubPre, vs_params] using hpre
  rw [vs_body, vsT_split, holdsList_append] at hb
  obtain ⟨hF0, hR⟩ := (holdsList_noRet vsFrontT vsFrontT_noRet _ _).1 hb
  have hz := hF0
  simp only [vsFrontT, holdsList_append] at hz
  obtain ⟨h10, h11, h12, h13, -, -⟩ := vsHeadT_holds hz
  -- the memory holds at least `64` words (the coefficients' table)
  have hκ6 : 6 ≤ κ := by
    have hR' := hR
    rw [holdsList_append, holdsList_append] at hR'
    obtain ⟨-, hmR, hR'⟩ := vsMapsT_holds h10 h11 h12 h13 hR'
    obtain ⟨hct, -⟩ := vsCtabT_holds (chs := σ (.n 870) :: vsChs σ) rfl hmR hR'
    have := mem_size hκ L (n := 64) (by norm_num) (fun j hj ↦
      ⟨_, hct j (by simp [ringCoefficients, kBits]; omega)⟩)
    by_contra hlt
    have : 2 ^ κ ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨⟨F⟩, -⟩ := vs_front hκ hκ6 L hLe bytecode (Tables.verify_bus_gkr_holdsC hκ L hLe)
    (Tables.verify_tables_holdsC hκ L bytecode hbl hLe) hexp hF0
  have hctx := F.hctx
  simp only [Tables.TCtx] at hctx
  obtain ⟨chis0, hbp, hgmu, -, -, -, hcl, hcol, -⟩ := hctx
  obtain ⟨hmaps, hchR, hct, hrstC, hlam, hpw, h1884, h1886, hcp, hl2, e1892, r1, e1901, r2, hdisp,
    hterm, hd1, hd2, hd3, hkret⟩ := vs_back h10 h11 h12 h13 hcol F.hpool hR
  refine ⟨hkret.symm, ?_⟩
  -- the output lanes
  obtain ⟨chis, hchiR, hτc, hlcol, hlpt, hout, hl25⟩ := vs_lanes hbl F
  have hτ9 := tau_ge F.hrowsL
  have hτ28 : vsTau F.rowsN ≤ 28 := by have := tau_lt F.hrowsL F.hh29; omega
  have hsL := tableHeights_length _ F.hrowsL
  have htg : σ (.n 858) = gen ^ vsTau F.rowsN := by
    refine loadHolds_unique F.l858 ?_
    have := F.hdims 6 (by simp [hsL])
    simpa [vsTau, List.getD_eq_getElem _ _ (show 5 < (Tables.tableHeightsOf F.rowsN).length by
      omega)] using this
  -- `verify_keccak`
  have hk := verify_keccak_holds L.read _ _ (hLe _ _ _ F.hkc)
  simp only [MeaningVerifyKeccak] at hk
  obtain ⟨xsK, op, point, slices, capK, word, m0, hxsK, hrunK, hop, hpoint, hsl, hretK⟩ :=
    hk (vsTau F.rowsN) chis ((lanesOf F.claims).map (·.value)) hτ9 hτ28 htg hτc hchiR
      (by simp [hl25]) (by rw [F.e862, word_g110]; exact hout)
  have hretK' : [σ (.n 863), σ (.n 864), σ (.n 865), σ (.n 866), σ (.n 867)] ++
      [σ (.n 868), σ (.n 869), σ (.n 870)] = capK ++ [σ (.n 854) * gen ^ xsK.length, word, m0] :=
    hretK
  obtain ⟨hcapK, hK3⟩ := List.append_inj' hretK' rfl
  simp only [List.cons.injEq, and_true] at hK3
  obtain ⟨e868, e869, e870⟩ := hK3
  -- the ring switch's target
  have hrt := ring_switch_target_holds L.read _ _ (hLe _ _ _ hrstC)
  simp only [MeaningRingTarget] at hrt
  obtain ⟨s', ch', hs'L, hch'L, hs'R, hch'R, hr1303⟩ := hrt
  have ech' : ch' = σ (.n 870) :: vsChs σ := readsAt_ext (by rw [hch'L]; rfl) hch'R hchR
  simp only [List.cons.injEq, and_true] at hr1303
  -- the stack
  obtain ⟨hμ22, hμ28, hcand, hP, hKB⟩ :=
    vs_stack hκ hκ6 L hLe hbl F hexp hcp hl2 e1892 r1 e1901 r2
  sorry

end
end LeanVM.Guest.B1.VerifySub
