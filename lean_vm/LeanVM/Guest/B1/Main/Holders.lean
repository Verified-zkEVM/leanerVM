/-
  LeanVM.Guest.B1.Main.Holders

  The raw signatures, by their marks, and the holders of `main`'s declared claims, by the marks in
  their slots: a raw signature's or the child's whose segment holds the mark; and the DA digest at
  the slot `da_pick`.
-/

module

public import LeanVM.Guest.B1.Main.Sound

/-!
# The raw signatures and the declared claims' holders

`signatures_held`: the decoded witness (`decWit`) holds the decoded claims (`decStmt`), as
`SignatureClaimsHeld` asks. The `j`-th raw leanXMSS signature is read at the slot holding the mark
`j` (`slotOf`, the writer's slot `sl j`, `slotOf_lx`): its writer's check is at that slot
(`CalleesW.xmss`), so it verifies its slot's claim (`xmss_raw_verify`); likewise for leanSPHINCS
at the mark `n_raw_x + j` (`sphincs_raw_verify`). The mark `m` in a declared claim's slot has its
writer there (`Cover`); in the leanXMSS region the writer is a raw leanXMSS signature (`m < RX`,
the `m`-th raw signature, at that slot) or a child's claim (the child `kid m`, whose rebuilt list
holds the slot's claim, `kidStmt_eq`): `xmss_covered`; likewise for leanSPHINCS.

`da_rel`: the DA digest at the slot `da_pick` (G:4203-4206) is, with the direct DA check, the
node's own slot, the digest of the claim `da_verify` returns (`CalleesW.da` opens it); without it,
the node's own slot's zeros or child `da_pick`'s digest.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

variable {C : CallRel}

variable {rd : Reader} {σ : Val} {Kr : ℕ → KidRec} {sl : ℕ → ℕ}

/-- Claims at slots: `slotCells` of four loads. -/
theorem slot_claimAt {p : E} {k : ℕ} {a b c d : E} (h : Sig.ClaimAt rd (p * gen ^ (4 * k)) a b c d) :
    slotCells rd p k = [a, b, c, d] := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  have := slotCells_of_loads (rd := rd) (p := p) (o := k) (v := fun i => [a, b, c, d].getD i 0)
    (fun i hi => by
      rw [← loadHolds_mul_gen_pow]
      interval_cases i
      · exact h0
      · exact h1
      · exact h2
      · exact h3)
  exact this

theorem region_raw (S : Segs) (m : ℕ) :
    (m < S.RX → S.region m = 0) ∧ (S.RX ≤ m → m < S.RX + S.RS → S.region m = 1) := by
  refine ⟨fun h => ?_, fun h1 h2 => ?_⟩ <;> unfold Segs.region
  · rw [ite_pos' h]
  · rw [ite_neg' (by omega), ite_pos' h2]

section Held

variable (MF : MainFacts C rd σ) (hK : ∀ c < lg σ 6, KidOk C rd σ c (Kr c))
  (hW : Writers rd (σ (.n 67)) (segsOf σ Kr) (LXS σ) (LSS σ))
  (hC : Cover rd (σ (.n 67)) (segsOf σ Kr) (LXS σ) (LSS σ) sl)
include MF hW hC

omit hW in
/-- The slot of the leanXMSS region holding a mark written there is its writer's. -/
theorem slotOf_lx {m : ℕ} (hm : m < LXS σ + LSS σ) (hr : sl m < LXS σ) :
    slotOf rd σ 0 (lxSlots σ) m = sl m := by
  have hT := MF.total.2
  have hs : LXS σ + LSS σ < 2 ^ 34 := by unfold LXS LSS; omega
  unfold slotOf; simp only [markOf_eq]
  rw [lxSlots_eq MF, slot_search hC hs hm (by omega) (by omega) (by omega), Nat.sub_zero]

omit hW in
/-- The slot of the leanSPHINCS region holding a mark written there is its writer's, less the
leanXMSS region. -/
theorem slotOf_ls {m : ℕ} (hm : m < LXS σ + LSS σ) (h1 : LXS σ ≤ sl m) (h2 : sl m < LXS σ + LSS σ) :
    slotOf rd σ (lxSlots σ) (lsSlots σ) m = sl m - LXS σ := by
  have hT := MF.total.2
  have hs : LXS σ + LSS σ < 2 ^ 34 := by unfold LXS LSS; omega
  unfold slotOf; simp only [markOf_eq]
  rw [lxSlots_eq MF, lsSlots_eq MF, slot_search hC hs hm h1 h2 le_rfl]

omit MF hC in
/-- The raw signatures' marks lie below the table's size. -/
theorem raw_le_total : lg σ 2 + lg σ 5 ≤ LXS σ + LSS σ := by
  have h := (segsOf σ Kr).a_mono (Nat.zero_le (segsOf σ Kr).NC)
  rw [hW.total, Segs.a.eq_1, segsOf_RX, segsOf_RS] at h
  exact h

omit MF hC in
/-- The writer of a mark at or past the raw writers is a child's, in its segment. -/
theorem mark_kid {m : ℕ} (h0 : (segsOf σ Kr).a 0 ≤ m) (hm : m < LXS σ + LSS σ) :
    (segsOf σ Kr).kid m < lg σ 6 ∧ (segsOf σ Kr).a ((segsOf σ Kr).kid m) ≤ m ∧
      m < (segsOf σ Kr).a ((segsOf σ Kr).kid m + 1) := by
  have := (segsOf σ Kr).kid_spec h0 (by rw [hW.total]; exact hm)
  rwa [segsOf_NC] at this

variable {bytecode : List K} {wX : E → LeanXmss.Signature} {wS : E → Sphincs.Signature}
  {wD : List E → List E → LeanVM.Da.MatrixWitness} {wV : List E → Proof}
  {wA : List E → BatchingHints}

/-- **Every raw leanXMSS signature verifies its claim.** -/
theorem xmss_raw_verify (cw : CalleesWC bytecode C rd (σ (.n 68)) wX wS wD wV wA) :
    ∀ raw ∈ (decWit σ rd wX wS wD wV wA).xmssSignatures,
      LeanXmss.verifyWithKeccak raw.1.1 raw.1.2 raw.2 = true := by
  have hT := MF.total.2
  have eX : LXS σ = lg σ 0 + lg σ 1 := rfl
  have hRT := raw_le_total hW
  intro raw hraw
  obtain ⟨j, hj, rfl⟩ :=
    List.mem_map.mp (show raw ∈ (List.range (nRawX σ)).map (rawXmss rd σ wX) from hraw)
  rw [List.mem_range, nRawX_eq] at hj
  obtain ⟨s, hbl, hl, hcall⟩ := MF.rawx j hj
  have hsLXS := belowLog_lt (by omega) MF.lxs hbl
  have hsj : s = sl j := hC.uniq s (by omega) j (by omega) hl
  have hslot : slotOf rd σ 0 (lxSlots σ) j = s := by
    rw [slotOf_lx MF hC (by omega) (by rw [← hsj]; exact hsLXS), hsj]
  obtain ⟨a, b, c, d, hat, hv⟩ := cw.xmss _ hcall
  simp only [rawXmss, hslot]
  unfold xmssAt
  rw [slot_claimAt hat]
  exact hv

/-- **Every raw leanSPHINCS signature verifies its claim.** -/
theorem sphincs_raw_verify (cw : CalleesWC bytecode C rd (σ (.n 68)) wX wS wD wV wA) :
    ∀ raw ∈ (decWit σ rd wX wS wD wV wA).sphincsSignatures,
      Sphincs.verifyWithKeccak raw.1.1 raw.1.2 raw.2 = true := by
  have hT := MF.total.2
  have eX : LXS σ = lg σ 0 + lg σ 1 := rfl
  have eS : LSS σ = lg σ 3 + lg σ 4 := rfl
  have hRT := raw_le_total hW
  intro raw hraw
  obtain ⟨j, hj, rfl⟩ :=
    List.mem_map.mp (show raw ∈ (List.range (nRawS σ)).map (rawSphincs rd σ wS) from hraw)
  rw [List.mem_range, nRawS_eq] at hj
  obtain ⟨s, hbl, hl, hcall⟩ := MF.raws j hj
  have hsLSS := belowLog_lt (by omega) MF.lss hbl
  rw [MF.lxs, (MF.counts 2 (by simp)).1, ← pow_add, ← pow_add, loadHolds_mul_gen_pow,
    Nat.add_zero] at hl
  have hsj := hC.uniq _ (by omega) _ (by omega) hl
  have hslot : slotOf rd σ (lxSlots σ) (lsSlots σ) (nRawX σ + j) = s := by
    rw [nRawX_eq, slotOf_ls MF hC (by omega) (by omega) (by omega)]
    omega
  obtain ⟨a, b, c, d, hat, hv⟩ := cw.sphincs _ hcall MF.bytes
  simp only [rawSphincs, hslot]
  unfold sphincsAt
  rw [slot_claimAt hat]
  exact hv

include hK

/-- **Every declared leanXMSS claim is a raw signature's or in a child's list.** -/
theorem xmss_covered :
    ∀ claim ∈ (decStmt σ rd).claims.xmss,
      claim ∈ (decWit σ rd wX wS wD wV wA).xmssSignatures.map (·.1) ∨
        ∃ child ∈ (decWit σ rd wX wS wD wV wA).children, claim ∈ child.statement.claims.xmss := by
  have hT := MF.total.2
  have eX : LXS σ = lg σ 0 + lg σ 1 := rfl
  have eS : LSS σ = lg σ 3 + lg σ 4 := rfl
  intro claim hclaim
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp
    (show claim ∈ (List.range (gLog (σ (.n 0)))).map (xmssAt rd (σ (.n 53))) from hclaim)
  rw [List.mem_range, gLog_lg] at hk
  have hkT : k < LXS σ + LSS σ := by omega
  obtain ⟨hmT, hslm⟩ := hC.mark k hkT
  rw [← markOf_eq] at hmT hslm
  set m := markOf rd σ k
  have hreg := (inRegion_iff (hC.reg m hmT) (region_le _ _)).1
  have hr0 : (segsOf σ Kr).region m = 0 := hreg.mp (by rw [hslm]; omega)
  by_cases hraw : m < lg σ 2
  · refine Or.inl (List.mem_map.mpr ⟨rawXmss rd σ wX m,
      List.mem_map.mpr ⟨m, List.mem_range.mpr (by rw [nRawX_eq]; exact hraw), rfl⟩, ?_⟩)
    simp only [rawXmss, slotOf_lx MF hC hmT (by rw [hslm]; omega), hslm]
  · refine Or.inr ?_
    have h0 : (segsOf σ Kr).a 0 ≤ m := by
      obtain ⟨-, rr1⟩ := region_raw (segsOf σ Kr) m
      simp only [segsOf_RX, segsOf_RS] at rr1
      rw [Segs.a.eq_1, segsOf_RX, segsOf_RS]
      by_contra hlt
      rw [rr1 (by omega) (by omega)] at hr0
      omega
    obtain ⟨hc, h1, h2⟩ := mark_kid hW h0 hmT
    set c := (segsOf σ Kr).kid m
    refine ⟨decKid rd σ wV c,
      List.mem_map.mpr ⟨c, List.mem_range.mpr (by rw [nKids_eq]; exact hc), rfl⟩, ?_⟩
    have hj := (region_kid' (by rw [segsOf_NC]; exact hc) h1 h2).1.mp hr0
    rw [segsOf_ex] at hj
    show xmssAt rd (σ (.n 53)) k ∈ (kidStmt rd σ c).claims.xmss
    rw [kidStmt_eq MF hK hW hC hc]
    refine List.mem_map.mpr ⟨m - (segsOf σ Kr).a c, List.mem_range.mpr (by omega), ?_⟩
    obtain ⟨hlt', hl⟩ := kid_wx MF hK hc (j := m - (segsOf σ Kr).a c) (by omega)
    rw [Nat.add_sub_cancel' h1] at hl
    rw [hC.uniq _ (by omega) m hmT hl, hslm]

/-- **Every declared leanSPHINCS claim is a raw signature's or in a child's list.** -/
theorem sphincs_covered :
    ∀ claim ∈ (decStmt σ rd).claims.sphincs,
      claim ∈ (decWit σ rd wX wS wD wV wA).sphincsSignatures.map (·.1) ∨
        ∃ child ∈ (decWit σ rd wX wS wD wV wA).children,
          claim ∈ child.statement.claims.sphincs := by
  have hT := MF.total.2
  have eX : LXS σ = lg σ 0 + lg σ 1 := rfl
  have eS : LSS σ = lg σ 3 + lg σ 4 := rfl
  intro claim hclaim
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp
    (show claim ∈ (List.range (gLog (σ (.n 3)))).map (sphincsAt rd (σ (.n 56))) from hclaim)
  rw [List.mem_range, gLog_lg] at hk
  have hkT : LXS σ + k < LXS σ + LSS σ := by omega
  obtain ⟨hmT, hslm⟩ := hC.mark (LXS σ + k) hkT
  rw [← markOf_eq] at hmT hslm
  set m := markOf rd σ (LXS σ + k)
  have hreg := (inRegion_iff (hC.reg m hmT) (region_le _ _)).2
  have hr1 : (segsOf σ Kr).region m = 1 := hreg.mp (by rw [hslm]; omega)
  obtain ⟨rr0, rr1⟩ := region_raw (segsOf σ Kr) m
  simp only [segsOf_RX, segsOf_RS] at rr0 rr1
  have hRX : lg σ 2 ≤ m := by by_contra h; rw [rr0 (by omega)] at hr1; omega
  by_cases hraw : m < lg σ 2 + lg σ 5
  · refine Or.inl (List.mem_map.mpr ⟨rawSphincs rd σ wS (m - lg σ 2),
      List.mem_map.mpr ⟨m - lg σ 2, List.mem_range.mpr (by rw [nRawS_eq]; omega), rfl⟩, ?_⟩)
    simp only [rawSphincs, nRawX_eq, Nat.add_sub_cancel' hRX,
      slotOf_ls MF hC hmT (by rw [hslm]; omega) (by rw [hslm]; omega), hslm, Nat.add_sub_cancel_left]
  · refine Or.inr ?_
    have h0 : (segsOf σ Kr).a 0 ≤ m := by
      rw [Segs.a.eq_1, segsOf_RX, segsOf_RS]; omega
    obtain ⟨hc, h1, h2⟩ := mark_kid hW h0 hmT
    set c := (segsOf σ Kr).kid m
    refine ⟨decKid rd σ wV c,
      List.mem_map.mpr ⟨c, List.mem_range.mpr (by rw [nKids_eq]; exact hc), rfl⟩, ?_⟩
    have hj := (region_kid' (by rw [segsOf_NC]; exact hc) h1 h2).2.mp hr1
    rw [segsOf_ex, segsOf_es] at hj
    show sphincsAt rd (σ (.n 56)) k ∈ (kidStmt rd σ c).claims.sphincs
    rw [kidStmt_eq MF hK hW hC hc]
    refine List.mem_map.mpr ⟨m - (segsOf σ Kr).a c - (Kr c).ex, List.mem_range.mpr (by omega), ?_⟩
    obtain ⟨hlt', hl⟩ := kid_ws MF hK hc (j := m - (segsOf σ Kr).a c - (Kr c).ex) (by omega)
    rw [show (segsOf σ Kr).a c + (Kr c).ex + (m - (segsOf σ Kr).a c - (Kr c).ex) = m by omega] at hl
    have := hC.uniq _ (by omega) m hmT hl
    rw [show (Kr c).os (m - (segsOf σ Kr).a c - (Kr c).ex) = k by omega]

/-- **The decoded witness holds the decoded signature claims** (`SignatureClaimsHeld`). -/
theorem signatures_held (cw : CalleesWC bytecode C rd (σ (.n 68)) wX wS wD wV wA) :
    SignatureClaimsHeld (decStmt σ rd) (decWit σ rd wX wS wD wV wA) :=
  ⟨xmss_raw_verify MF hW hC cw, sphincs_raw_verify MF hW hC cw, xmss_covered MF hK hW hC,
    sphincs_covered MF hK hW hC⟩

omit hK hW hC in
/-- **The DA digest**: with the direct DA check, the digest of the claim it returns, which the
decoded matrix opens; without it, zeros or a child's. -/
theorem da_rel {bytecode : List K} {wX : E → LeanXmss.Signature} {wS : E → Sphincs.Signature}
    {wD : List E → List E → LeanVM.Da.MatrixWitness} {wV : List E → Proof} {wA : List E → BatchingHints}
    (cw : CalleesWC bytecode C rd (σ (.n 68)) wX wS wD wV wA) :
    (∀ c m, (decWit σ rd wX wS wD wV wA).daMatrix = some (c, m) →
      (decStmt σ rd).claims.daDigest = daClaimDigest c ∧ m.Opens c.daRoot c.membershipVectorDigest) ∧
    ((decWit σ rd wX wS wD wV wA).daMatrix = none → (decStmt σ rd).claims.daDigest = zeroDigest ∨
      ∃ c ∈ (decWit σ rd wX wS wD wV wA).children,
        c.statement.claims.daDigest = (decStmt σ rd).claims.daDigest) := by
  have eD : (decStmt σ rd).claims.daDigest = daDigestAt rd σ (lg σ 387) := by
    unfold decStmt; simp only [gLog_lg]
  obtain ⟨-, hpl, hp1⟩ := MF.pick
  have h7 := MF.direct.2
  have hown := MF.own
  by_cases hd : lg σ 7 = 1
  · have hdec : (decWit σ rd wX wS wD wV wA).daMatrix =
        some (dvClaim σ, wD [σ (.n 50)] [σ (.n 339), σ (.n 340), σ (.n 341), σ (.n 342)]) := by
      unfold decWit; simp only [nDirect_eq, hd, ↓reduceIte]
    refine ⟨fun c m h => ?_, fun h => (by rw [hdec] at h; cases h)⟩
    rw [hdec, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hcall, -, l0, l1⟩ := MF.da hd
    rw [hown, loadHolds_gen_pow_iff, Nat.add_zero] at l0
    rw [hown, loadHolds_gen_pow_iff] at l1
    obtain ⟨root, vd, hop, hrets⟩ := cw.da _ _ hcall (fun j hj => (MF.exp j hj).2)
    simp only [digestCells, List.cons_append, List.nil_append, List.cons.injEq, and_true] at hrets
    obtain ⟨r0, r1, r2, r3⟩ := hrets
    have hdv : dvClaim σ = ⟨root, vd⟩ := by
      unfold dvClaim; rw [r0, r1, r2, r3, digestOfCells_scalars, digestOfCells_scalars]
    refine ⟨?_, by rw [hdv]; exact hop⟩
    rw [eD, hp1 hd, (daDigestAt_of_loads l0 l1).1, digestOfCells_scalars]
    unfold daClaimDigest
    rw [hdv, ← digestOfCells_scalars root, ← digestOfCells_scalars vd, digestBytes_ofCells,
      digestBytes_ofCells, ← r0, ← r1, ← r2, ← r3]
    simp [cellsBytes]
  · have hd0 : lg σ 7 = 0 := by omega
    have hdec : (decWit σ rd wX wS wD wV wA).daMatrix = none := by
      unfold decWit; simp only [nDirect_eq, hd, ↓reduceIte]
    refine ⟨fun c m h => (by rw [hdec] at h; cases h), fun _ => ?_⟩
    rcases Nat.lt_or_ge (lg σ 387) (lg σ 6) with hlt | hge
    · show _ ∨ ∃ c ∈ (List.range (nKids σ)).map (decKid rd σ wV), _
      refine Or.inr ⟨decKid rd σ wV (lg σ 387),
        List.mem_map.mpr ⟨lg σ 387, List.mem_range.mpr (by rw [nKids_eq]; exact hlt), rfl⟩, ?_⟩
      rw [eD]; rfl
    · have hpe : lg σ 387 = lg σ 6 := by omega
      obtain ⟨z0, z1⟩ := MF.daz hd0
      rw [hown, loadHolds_gen_pow_iff, Nat.add_zero] at z0
      rw [hown, loadHolds_gen_pow_iff] at z1
      refine Or.inl ?_
      rw [eD, hpe, (daDigestAt_of_loads z0 z1).1, digestOfCells_zero]

end Held

end
end LeanVM.Guest.B1.Main
