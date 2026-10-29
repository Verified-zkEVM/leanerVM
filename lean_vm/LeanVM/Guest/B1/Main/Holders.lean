/-
  LeanVM.Guest.B1.Main.Holders

  The holders of `main`'s declared claims, by the marks in their slots: a raw signature's check or
  the child whose segment holds the mark; and the DA digest at the slot `da_pick`.
-/

module

public import LeanVM.Guest.B1.Main.Sound

/-!
# The holders of the declared claims

`xmss_held`, `sphincs_held`: the decoded holders (`decWit`) hold the decoded claims (`decStmt`),
`List.Forall₂` as `NodeRel` asks. The mark `m` in a declared claim's slot has its writer there
(`Cover`); in the leanXMSS region the writer is a raw leanXMSS signature (`m < RX`, its check at
the slot: `CalleesW.xmss`) or a child's claim (the child `kidOf m`, whose rebuilt list holds the
slot's claim, `kidStmt_eq`); likewise for leanSPHINCS.

`da_rel`: the DA digest at the slot `da_pick` (G:4208-4211) is, with the direct DA check, the
node's own slot, the digest of the claim `da_verify` returns (`CalleesW.da` opens it); without it,
the node's own slot's zeros or child `da_pick`'s digest.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

variable {C : CallRel}

theorem forall₂_map_range {α β : Type} {R : α → β → Prop} :
    ∀ (n : ℕ) {f : ℕ → α} {g : ℕ → β}, (∀ k < n, R (f k) (g k)) →
      List.Forall₂ R ((List.range n).map f) ((List.range n).map g)
  | 0, _, _, _ => by simp
  | n + 1, f, g, h => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_cons, List.map_map, List.map_map]
    exact .cons (h 0 (by omega)) (forall₂_map_range n fun k hk => h (k + 1) (by omega))

variable {rd : Reader} {σ : Val} {Kr : ℕ → KidRec} {sl : ℕ → ℕ}

/-- The children of the decoded witness. -/
noncomputable abbrev kidsOf (rd : Reader) (σ : Val) (wV : List E → Proof) : List Child :=
  (List.range (nKids σ)).map (decKid rd σ wV)

theorem kidsOf_get {wV : List E → Proof} {c : ℕ} (hc : c < lg σ 6) :
    (kidsOf rd σ wV)[c]? = some (decKid rd σ wV c) := by
  rw [List.getElem?_map, List.getElem?_range (by rw [nKids_eq]; exact hc)]; rfl

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
include MF hK hW hC

omit MF hK hC in
/-- The writer of a mark at or past the raw writers is a child's, in its segment. -/
theorem mark_kid {m : ℕ} (h0 : (segsOf σ Kr).a 0 ≤ m) (hm : m < LXS σ + LSS σ) :
    (segsOf σ Kr).kid m < lg σ 6 ∧ (segsOf σ Kr).a ((segsOf σ Kr).kid m) ≤ m ∧
      m < (segsOf σ Kr).a ((segsOf σ Kr).kid m + 1) := by
  have := (segsOf σ Kr).kid_spec h0 (by rw [hW.total]; exact hm)
  rwa [segsOf_NC] at this

theorem xmss_held {bytecode : List K} {wX : E → LeanXmss.Signature} {wS : E → Sphincs.Signature}
    {wD : List E → List E → LeanVM.Da.Witness} {wV : List E → Proof} {wA : List E → BatchHints}
    (cw : CalleesWC bytecode C rd (σ (.n 68)) wX wS wD wV wA) :
    List.Forall₂ (Held (fun (c : XmssClaim) σ ↦ xmssVerify c.1 c.2 σ = true) Claims.xmss (kidsOf rd σ wV)) (decStmt σ rd).claims.xmss
      (decWit σ rd wX wS wD wV wA).xmss := by
  have hT := MF.total.2
  have eX : LXS σ = lg σ 0 + lg σ 1 := rfl
  have eS : LSS σ = lg σ 3 + lg σ 4 := rfl
  unfold decStmt decWit
  simp only [gLog_lg]
  refine forall₂_map_range _ fun k hk => ?_
  have hkT : k < LXS σ + LSS σ := by omega
  obtain ⟨hmT, hslm⟩ := hC.mark k hkT
  rw [← markOf_eq] at hmT hslm
  set m := markOf rd σ k
  have hreg := (inRegion_iff (hC.reg m hmT) (region_le _ _)).1
  have hr0 : (segsOf σ Kr).region m = 0 := hreg.mp (by rw [hslm]; omega)
  simp only [nRawX_eq]
  by_cases hraw : m < lg σ 2
  · rw [ite_pos' hraw]
    obtain ⟨s, hbl, hl, hcall⟩ := MF.rawx m hraw
    have hsLXS := belowLog_lt (by omega) MF.lxs hbl
    have hsk : s = k := by rw [hC.uniq s (by omega) m hmT hl, hslm]
    subst hsk
    obtain ⟨a, b, c, d, hat, hv⟩ := cw.xmss _ hcall
    show xmssVerify (xmssAt rd (σ (.n 53)) s).1 (xmssAt rd (σ (.n 53)) s).2 _ = true
    unfold xmssAt
    rw [slot_claimAt hat]
    exact hv
  · rw [ite_neg' hraw]
    have h0 : (segsOf σ Kr).a 0 ≤ m := by
      obtain ⟨-, rr1⟩ := region_raw (segsOf σ Kr) m
      simp only [segsOf_RX, segsOf_RS] at rr1
      rw [Segs.a.eq_1, segsOf_RX, segsOf_RS]
      by_contra hlt
      rw [rr1 (by omega) (by omega)] at hr0
      omega
    obtain ⟨hc, h1, h2⟩ := mark_kid hW h0 hmT
    set c := (segsOf σ Kr).kid m
    have hkid : kidOf rd σ m = c := kidOf_eq MF hK hc h1 h2
    rw [hkid]
    refine ⟨decKid rd σ wV c, kidsOf_get hc, ?_⟩
    have hj := (region_kid' (by rw [segsOf_NC]; exact hc) h1 h2).1.mp hr0
    rw [segsOf_ex] at hj
    show xmssAt rd (σ (.n 53)) k ∈ (kidStmt rd σ c).claims.xmss
    rw [kidStmt_eq MF hK hW hC hc]
    refine List.mem_map.mpr ⟨m - (segsOf σ Kr).a c, List.mem_range.mpr (by omega), ?_⟩
    obtain ⟨hlt', hl⟩ := kid_wx MF hK hc (j := m - (segsOf σ Kr).a c) (by omega)
    rw [Nat.add_sub_cancel' h1] at hl
    rw [hC.uniq _ (by omega) m hmT hl, hslm]

theorem sphincs_held {bytecode : List K} {wX : E → LeanXmss.Signature} {wS : E → Sphincs.Signature}
    {wD : List E → List E → LeanVM.Da.Witness} {wV : List E → Proof} {wA : List E → BatchHints}
    (cw : CalleesWC bytecode C rd (σ (.n 68)) wX wS wD wV wA) :
    List.Forall₂ (Held (fun (c : SphincsClaim) σ ↦ sphincsVerify c.1 c.2 σ = true) Claims.sphincs (kidsOf rd σ wV)) (decStmt σ rd).claims.sphincs
      (decWit σ rd wX wS wD wV wA).sphincs := by
  have hT := MF.total.2
  have eX : LXS σ = lg σ 0 + lg σ 1 := rfl
  have eS : LSS σ = lg σ 3 + lg σ 4 := rfl
  unfold decStmt decWit
  simp only [gLog_lg, lxSlots_eq MF]
  refine forall₂_map_range _ fun k hk => ?_
  have hkT : LXS σ + k < LXS σ + LSS σ := by omega
  obtain ⟨hmT, hslm⟩ := hC.mark (LXS σ + k) hkT
  rw [← markOf_eq] at hmT hslm
  set m := markOf rd σ (LXS σ + k)
  have hreg := (inRegion_iff (hC.reg m hmT) (region_le _ _)).2
  have hr1 : (segsOf σ Kr).region m = 1 := hreg.mp (by rw [hslm]; omega)
  obtain ⟨rr0, rr1⟩ := region_raw (segsOf σ Kr) m
  simp only [segsOf_RX, segsOf_RS] at rr0 rr1
  have hRX : lg σ 2 ≤ m := by by_contra h; rw [rr0 (by omega)] at hr1; omega
  simp only [nRawX_eq, nRawS_eq]
  by_cases hraw : m < lg σ 2 + lg σ 5
  · rw [ite_pos' hraw]
    obtain ⟨s, hbl, hl, hcall⟩ := MF.raws (m - lg σ 2) (by omega)
    have hsLSS := belowLog_lt (by omega) MF.lss hbl
    rw [MF.lxs, (MF.counts 2 (by simp)).1, ← pow_add, ← pow_add, loadHolds_mul_gen_pow,
      Nat.add_zero, Nat.add_sub_cancel' hRX] at hl
    have hsk : s = k := by have := hC.uniq _ (by omega) m hmT hl; omega
    subst hsk
    obtain ⟨a, b, c, d, hat, hv⟩ := cw.sphincs _ hcall MF.bytes
    show sphincsVerify (sphincsAt rd (σ (.n 56)) s).1 (sphincsAt rd (σ (.n 56)) s).2 _ = true
    unfold sphincsAt
    rw [slot_claimAt hat]
    exact hv
  · rw [ite_neg' hraw]
    have h0 : (segsOf σ Kr).a 0 ≤ m := by
      rw [Segs.a.eq_1, segsOf_RX, segsOf_RS]; omega
    obtain ⟨hc, h1, h2⟩ := mark_kid hW h0 hmT
    set c := (segsOf σ Kr).kid m
    have hkid : kidOf rd σ m = c := kidOf_eq MF hK hc h1 h2
    rw [hkid]
    refine ⟨decKid rd σ wV c, kidsOf_get hc, ?_⟩
    have hj := (region_kid' (by rw [segsOf_NC]; exact hc) h1 h2).2.mp hr1
    rw [segsOf_ex, segsOf_es] at hj
    show sphincsAt rd (σ (.n 56)) k ∈ (kidStmt rd σ c).claims.sphincs
    rw [kidStmt_eq MF hK hW hC hc]
    refine List.mem_map.mpr ⟨m - (segsOf σ Kr).a c - (Kr c).ex, List.mem_range.mpr (by omega), ?_⟩
    obtain ⟨hlt', hl⟩ := kid_ws MF hK hc (j := m - (segsOf σ Kr).a c - (Kr c).ex) (by omega)
    rw [show (segsOf σ Kr).a c + (Kr c).ex + (m - (segsOf σ Kr).a c - (Kr c).ex) = m by omega] at hl
    have := hC.uniq _ (by omega) m hmT hl
    rw [show (Kr c).os (m - (segsOf σ Kr).a c - (Kr c).ex) = k by omega]

omit hK hW hC in
/-- **The DA digest**: with the direct DA check, the digest of the claim it returns, which the
decoded matrix opens; without it, zeros or a child's. -/
theorem da_rel {bytecode : List K} {wX : E → LeanXmss.Signature} {wS : E → Sphincs.Signature}
    {wD : List E → List E → LeanVM.Da.Witness} {wV : List E → Proof} {wA : List E → BatchHints}
    (cw : CalleesWC bytecode C rd (σ (.n 68)) wX wS wD wV wA) :
    (∀ c m, (decWit σ rd wX wS wD wV wA).da = some (c, m) →
      (decStmt σ rd).claims.da = daClaimDigest c ∧ m.Opens c.daRoot c.membershipVectorDigest) ∧
    ((decWit σ rd wX wS wD wV wA).da = none → (decStmt σ rd).claims.da = zeroDigest ∨
      ∃ c ∈ (decWit σ rd wX wS wD wV wA).children,
        c.statement.claims.da = (decStmt σ rd).claims.da) := by
  have eD : (decStmt σ rd).claims.da = daDigestAt rd σ (lg σ 387) := by
    unfold decStmt; simp only [gLog_lg]
  obtain ⟨-, hpl, hp1⟩ := MF.pick
  have h7 := MF.direct.2
  have hown := MF.own
  by_cases hd : lg σ 7 = 1
  · have hdec : (decWit σ rd wX wS wD wV wA).da =
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
    unfold daClaimDigest daPreimage
    rw [hdv, ← digestOfCells_scalars root, ← digestOfCells_scalars vd, digestBytes_ofCells,
      digestBytes_ofCells, ← r0, ← r1, ← r2, ← r3]
    simp [cellsBytes]
  · have hd0 : lg σ 7 = 0 := by omega
    have hdec : (decWit σ rd wX wS wD wV wA).da = none := by
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
