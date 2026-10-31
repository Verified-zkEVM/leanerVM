/-
  LeanVM.Guest.B1.KeccakGkr.LayerCPlacedB

  **`keccak_layer` is complete, placed, within a bound** (`CompleteAtFB`), for its four
  specializations: its frame, its buffers and its callees' words.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerCPlaced
public import LeanVM.Guest.B1.KeccakGkr.FlatFB
public import LeanVM.Guest.Memory.LoopPre

/-!
# `keccak_layer`, complete and placed within a bound

`layer_completeAtFB` is `layer_completeAtF` with the size of the layer's run bounded before the
memory, by

  `layerWords fs first odd y KP KR =
    fs (layerName first odd) + (y + 228) + (fs (packLoopName first odd) + ⌊y/2⌋ * KP) + odd * KR`:

the layer's frame; its buffers (`allocDyn` of `y` words for the pack challenges, then 128 for the
round records, 11 for the local point, 25 for the next claim's lanes and 64 for its slices); the
pack loop's call (`⌊y/2⌋` iterations of at most `KP` words each when it is entered, its frame
`fs (packLoopName first odd)` when it is skipped, which is when `y = 1`); for odd `y`, the last
round's (at most `KR` words). `y ≤ 30` makes it at most
`fs (layerName first odd) + 258 + fs (packLoopName first odd) + 15 * KP + KR`.

The hypotheses on the callees are fs-generic: the pack loop's words per iteration
(`TotalLeOn … LoopPre`, the form of `Count.wSK_totalLeOn`) and `keccak_round`'s
(`TotalLe`, the form of `Count.wSB_totalLe`). The proof is `layer_completeAtF`'s with
`completeAt_flatOutFB`, the pure callees placed within their bounds by `completeAtDTB_of_relIn`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.Lift LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)
open LeanVM.Protocol.KeccakGkr

@[expose] public section

/-- **`keccak_layer`'s words**: its frame, its buffers (`y + 128 + 11 + 25 + 64`), the pack loop's
(`⌊y/2⌋` iterations of at most `KP` words, or its frame when skipped) and, for odd `y`, the last
round's (at most `KR`). -/
def layerWords (fs : String → ℕ) (first odd y KP KR : ℕ) : ℕ :=
  fs (layerName first odd) + (y + 228) + (fs (packLoopName first odd) + y / 2 * KP) + odd * KR

theorem packLoopName_ne_round (first odd : ℕ) : packLoopName first odd ≠ "keccak_round" := by
  unfold packLoopName; split <;> decide

/-- The words of the layer's callees, an entered one's bound, a skipped one's frame. -/
theorem layerKids_bound (fs : String → ℕ) (D : LayerData) {first odd : ℕ} (ho : odd < 2)
    (CL : ClaimLay) (bcur bout b KP KR : ℕ) :
    kidsBound fs (fun k ↦ if k.f = "keccak_round" then KR else D.y / 2 * KP)
      (layerKids D first odd CL bcur bout b) ≤
      fs (packLoopName first odd) + D.y / 2 * KP + odd * KR := by
  have hne := packLoopName_ne_round first odd
  rcases (by omega : odd = 0 ∨ odd = 1) with rfl | rfl <;>
    simp only [kidsBound, layerKids, hne, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, List.cons_append, List.nil_append, List.append_nil, ↓reduceIte,
      show (0 : ℕ) ≠ 1 by decide] <;>
    split_ifs <;> omega

variable {fs : String → ℕ} {cert : String → V → ℕ}

set_option maxRecDepth 20000 in
/-- **`keccak_layer` is complete, placed, within `layerWords fs first odd D.y KP KR` words**, for
its four specializations: `layer_completeAtF` with the pack loop at most `KP` words per iteration
and `keccak_round` at most `KR`. -/
theorem layer_completeAtFB {first odd : ℕ} (hf : first < 2) (ho : odd < 2) (κ : ℕ) (D : LayerData)
    (CL : ClaimLay) (bcur bout : ℕ) {p0 p1 iota : E} {KP KR : ℕ}
    (hP : TotalLeOn coreProgram fs (packLoopName first odd) LoopPre
      fun a ↦ logG (a.getD 1 0) * KP)
    (hR : TotalLe coreProgram fs "keccak_round" fun _ ↦ KR)
    (hcl : D.cap.length = 5) (hcap : AllCanonical D.cap)
    (hw : first = 1 → (p0, p1) = Keccak.scalarCells D.w0 dsObserve)
    (hy : D.y % 2 = odd) (hy1 : 1 ≤ D.y) (hy30 : D.y ≤ 30) (hpl : D.product.length = 47)
    (hpm : D.packMsgs.length = D.y) (hlm : D.localMsgs.length = 11)
    (hproj : projectedOf D.c D.product + iota * sumE D.c.mu = D.c.value)
    (hfin : LayerFinal D.c (D.s0 first) D.product D.packMsgs D.localMsgs D.t)
    (hCL : CL.Ok first D.c D.y) :
    CompleteAtFB fs cert κ (layerName first odd)
      (fun fp ↦ layerLin D first CL bcur bout (fp + fs (layerName first odd)))
      (D.cap ++ [p0, p1, ptr bcur, gen ^ D.y, gen ^ (D.y / 2), gen ^ (D.y / 2 + odd), ptr CL.bclaim,
        ptr bout, iota])
      (fun fp rets Lout ↦ rets = D.rets first (ptr bcur) ∧
        Lout = layerBufs D first (ptr bcur) (fp + fs (layerName first odd)))
      (layerWords fs first odd D.y KP KR) := by
  obtain ⟨fn, hfind, hbody, hparams⟩ := layer_fn hf ho
  obtain ⟨hflat, haddrs, halloc, -, -, hloads⟩ := layerPre_kernel hf ho
  have hlocL : (D.locPt first).length = 11 := by
    rw [LayerData.locPt, LayerData.loc, layerLocal, localRunF_length, hlm]
  have hne := packLoopName_ne_round first odd
  refine CompleteAtFB.mono_bound ?_ (show fs (layerName first odd) + (layerSizes D).sum +
      (fs (packLoopName first odd) + D.y / 2 * KP + odd * KR) ≤ layerWords fs first odd D.y KP KR by
    simp only [layerSizes, layerWords, List.sum_cons, List.sum_nil]; omega)
  refine completeAt_flatOutFB (fs := fs) (cert := cert) hfind (layer_loop hf ho) κ _ _
    (fun _ ↦ D.rets first (ptr bcur)) _ (hbody.trans (layerT_pre first odd)) hflat haddrs
    (layerPre_noLoadIte hf ho)
    (layerSizes D) (fun _ ↦ layerOwn D first (ptr bcur)) (fun _ ↦ ?_) (fun _ ↦ ⟨rfl, rfl⟩)
    (fun fp ↦ layerKids D first odd CL bcur bout (fp + fs (layerName first odd)))
    (fun k ↦ if k.f = "keccak_round" then KR else D.y / 2 * KP)
    (fs (packLoopName first odd) + D.y / 2 * KP + odd * KR) ?_
    (fun fp ↦ layerKids_bound fs D ho CL bcur bout _ KP KR) ?_ ?_ ?_
  · -- the buffers' words fit
    simp only [layerOwn, layerSizes, List.forall₂_cons, List.Forall₂.nil, and_true]
    refine ⟨by rw [LayerData.chs_length hpm], by rw [recWords_length], by rw [hlocL],
      by rw [lanesOut_length], by rw [eqKernel_length, List.length_take, hlocL]; norm_num⟩
  · -- the callees, placed within their bounds
    intro fp k hk ht
    simp only [layerKids, List.mem_append, List.mem_singleton] at hk
    rcases hk with rfl | hk
    · have hne1 : 1 + gen ^ (D.y / 2) ≠ 0 := by simpa using ht
      have hm0 : 0 < D.y / 2 := by
        rcases Nat.eq_zero_or_pos (D.y / 2) with h0 | h0
        · exact absurd (e_add_eq_zero_iff.mpr (by rw [h0, pow_zero])) hne1
        · exact h0
      simp only [hne, ↓reduceIte]
      refine CompleteAtDTB.toCompleteAtB (completeAtDTB_of_relIn
        layerKidS_pure (packLoopName_mem first odd) (fun rd t rets' hn hv hb ↦ ?_)
        fun rd _ hm ↦ (layer_kids D CL bcur bout _ hy hy30 hpl hpm hlm hm).1 hne1)
      have h1 := hP rd t _ rets' hn (loopPre_gen hm0 (by omega) _) hv hb
      simp only [List.getD_cons_succ, List.getD_cons_zero] at h1
      rwa [gen_pow_eq_ofK, logG_spec (by omega)] at h1
    · split at hk
      · rename_i hodd1
        simp only [List.mem_singleton] at hk
        subst hk
        simp only [↓reduceIte]
        exact CompleteAtDTB.toCompleteAtB (completeAtDTB_of_relIn
          layerKidS_pure (by simp [layerKidS]) (fun rd t rets' hn hv hb ↦ hR rd t _ rets' hn hv hb)
          fun rd _ hm ↦ (layer_kids D CL bcur bout _ hy hy30 hpl hpm hlm hm).2 hodd1)
      · simp at hk
  · intro fp k hk _ i hi
    rw [layerKids_lin k hk] at hi
    obtain ⟨q, hq, h1, h2⟩ := hi
    rcases List.mem_append.mp hq with hq | hq
    · exact Or.inl ⟨q, hq, h1, h2⟩
    · exact Or.inr ⟨q, hq, h1, h2⟩
  · intro fp rd hB hLin k hk
    rw [layerKids_lin k hk]
    exact Main.memL_append.mpr ⟨hLin, hB⟩
  · -- the honest valuation
    intro fp outs hout rd _ hB hLin
    generalize hbdef : fp + fs (layerName first odd) = b at hB hLin hout ⊢
    have hm : MemL rd (layerLin D first CL bcur bout b ++ layerBufs D first (ptr bcur) b) :=
      Main.memL_append.mpr ⟨hLin, hB⟩
    obtain ⟨hK1, hK2⟩ := layer_kids D CL bcur bout b hy hy30 hpl hpm hlm hm
    obtain ⟨w1309, w1310, w1325, w34, w278⟩ := layerW_vals hf ho D b
    have hcr0 := hCL
    obtain ⟨hcwL, -, -, -, -, h2, h3, -, -, hwt⟩ := hcr0
    have mem : ∀ q ∈ layerLin D first CL bcur bout b ++ layerBufs D first (ptr bcur) b,
        ReadsAt rd (ptr q.1) q.2 := hm
    have hCLm : MemL rd (CL.L first D.c) := fun q hq ↦ hLin q (by simp [layerLin, hq])
    have hcr := ClaimLay.claimRec hCL hCLm
    have mB : ∀ {bb ws}, (bb, ws) ∈ layerBufs D first (ptr bcur) b → ReadsAt rd (ptr bb) ws :=
      fun hq ↦ mem _ (List.mem_append_right _ hq)
    have mL : ∀ {bb ws}, (bb, ws) ∈ layerLin D first CL bcur bout b → ReadsAt rd (ptr bb) ws :=
      fun hq ↦ mem _ (List.mem_append_left _ hq)
    have hcw : ReadsAt rd (ptr CL.bclaim) CL.cw := mL (by simp [layerLin, ClaimLay.L])
    have hxs : ReadsAt rd (ptr bcur) D.xs := mL (by simp [layerLin])
    have hout' : ReadsAt rd (ptr bout) (D.outW first (layerW D first odd b 1309)
        (layerW D first odd b (weightEnd first (4 * odd) + 34))
        (layerW D first odd b (4 * odd + 1325))
        (layerW D first odd b (weightEnd first (4 * odd) + 278))) := by
      rw [w1309, w34, w1325, w278]; exact mL (by simp [layerLin])
    have hbody' := layer_body_complete hf ho D (rd := rd) (w := layerW D first odd b) (p0 := p0)
      (p1 := p1) (cur := ptr bcur) (claim := ptr CL.bclaim) (out := ptr bout) (iota := iota)
      (cw := CL.cw) hcl hcap hw hy hy1 hy30 hpl hpm hlm hproj hfin hcr hcw (by omega) hxs
      (by rw [w1309]; exact mB (by simp [layerBufs_eq]))
      (by rw [w1310]; exact mB (by simp [layerBufs_eq]))
      (by rw [w1325]; exact mB (by simp [layerBufs_eq]))
      (by rw [w34]; exact mB (by simp [layerBufs_eq]))
      (by rw [w278]; exact mB (by simp [layerBufs_eq])) hout'
      (fun hne ↦ by rw [w1310, w1309, h2]; exact (hK1 hne).rel)
      (fun h ↦ by rw [w1310, w1309, h2]; exact (hK2 h).rel)
    obtain ⟨⟨e1317, e1323, e2085, e2086, e1308⟩, hH⟩ := hbody'
    -- the valuation's equations
    have hl : (D.cap ++ [p0, p1, ptr bcur, gen ^ D.y, gen ^ (D.y / 2), gen ^ (D.y / 2 + odd),
        ptr CL.bclaim, ptr bout, iota]).length = 14 := by simp [hcl]
    have hG := layer_good (rd := rd) (w := layerW D first odd b) hf ho hl
    have hpar := fun i (hi : i < 14) ↦ layer_param (rd := rd) (w := layerW D first odd b) hf ho hl hi
    generalize layerσ rd (layerW D first odd b) (D.cap ++ [p0, p1, ptr bcur, gen ^ D.y,
      gen ^ (D.y / 2), gen ^ (D.y / 2 + odd), ptr CL.bclaim, ptr bout, iota]) first odd = σ
      at hG hpar hH e1317 e1323 e2085 e2086 e1308 ⊢
    have hGpre : ∀ s ∈ layerPre first odd, GoodS rd (layerSt first odd) (layerW D first odd b) σ s :=
      fun s hs ↦ hG s (by rw [layerT_pre]; exact List.mem_append_left _ hs)
    have ga := alloc_good hGpre
    rw [halloc] at ga
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at ga
    obtain ⟨a1309, a1310, a1325, a34, a278⟩ := ga
    simp only [V.n] at a1309 a1310 a1325 a34 a278
    rw [w1309] at a1309
    rw [w1310] at a1310
    rw [w1325] at a1325
    rw [w34] at a34
    rw [w278] at a278
    rw [layerT_sections] at hG
    have gP : ∀ s ∈ packSetupT first odd, GoodS rd (layerSt first odd) (layerW D first odd b) σ s :=
      fun s hs ↦ hG s (by simp [hs])
    obtain ⟨f0, f1, f2, f3, f4, hcapE⟩ := five_of_length' hcl
    rw [hcapE] at hpar
    have a7 : σ (.n 7) = ptr bcur := hpar 7 (by norm_num)
    have a8 : σ (.n 8) = gen ^ D.y := hpar 8 (by norm_num)
    have a9 : σ (.n 9) = gen ^ (D.y / 2) := hpar 9 (by norm_num)
    have a11 : σ (.n 11) = ptr CL.bclaim := hpar 11 (by norm_num)
    have a12 : σ (.n 12) = ptr bout := hpar 12 (by norm_num)
    refine ⟨σ, ?_, layerPre_disp hf ho σ, by rw [hbody]; exact hH, ?_, ?_, ?_, ?_⟩
    · -- the parameters
      rw [hparams, hcapE]
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      refine List.ext_getElem (by simp) fun i h1 h2 ↦ ?_
      simp only [List.length_cons, List.length_nil] at h1
      have := hpar i (by omega)
      interval_cases i <;> simpa using this
    · -- the sizes
      rw [halloc]
      simp only [List.map_cons, List.map_nil, Sum.elim_inl, Sum.elim_inr, id, layerSizes, a8,
        gen_pow_eq_ofK]
      rw [logG_spec (by omega)]
    · -- the bases
      rw [halloc]
      simp only [List.map_cons, List.map_nil, a1309, a1310, a1325, a34, a278, layerSizes, bases]
    · -- the calls
      rw [layerPre_callSF hf ho σ]
      have hg0 := fun s hs ↦ gP s (by rw [packSetupT]; exact List.mem_append_left _ hs)
      simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
        and_true, GoodS, Good] at hg0
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, e1314, e1315, e1316⟩ := hg0
      have e1315' : σ (.n 1315) = 1 + gen ^ (D.y / 2) := by rw [e1315, e1314, a9, word_one]
      rw [word_one] at e1316
      have epp : σ (.n 1308) = ptr CL.bpp := by rw [e1308, h2]
      by_cases hodd1 : odd = 1
      · have hg1 := fun s hs ↦ gP s (by rw [packSetupT]; exact List.mem_append_right _ hs)
        simp only [hodd1, ↓reduceIte, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
          implies_true, and_true, GoodS, Good, V.n] at hg1
        obtain ⟨e17, e18, e19, e20⟩ := hg1
        rw [ite_pos' (by simp)] at e17 e18 e19 e20
        simp only [layerCalls, layerKids, hodd1, ↓reduceIte, List.cons_append, List.nil_append,
          List.map_cons, List.map_nil] at hout ⊢
        match outs, hout with
        | [o1, o2], ⟨ho1, ho2, _⟩ =>
          refine ⟨rfl, by simp [Main.mkCall, e1315'], fun ht ↦ ⟨?_, ?_⟩, rfl, rfl,
            fun _ ↦ ⟨?_, ?_⟩, trivial⟩
          · simp [Main.mkCall, e1316, a9, a1310, epp, a1309]
          · simp only [Main.mkCall, List.map_nil]; exact ((ho1 ht).1).symm
          · simp only [Main.mkCall, List.map_cons, List.map_nil, e18, e19, e20, e17, a1310, a9,
              epp, a1309, sq]
          · simp only [Main.mkCall, List.map_nil]; exact ((ho2 rfl).1).symm
      · simp only [layerCalls, layerKids, hodd1, ↓reduceIte, List.append_nil, List.map_cons,
          List.map_nil] at hout ⊢
        match outs, hout with
        | [o1], ⟨ho1, _⟩ =>
          refine ⟨rfl, by simp [Main.mkCall, e1315'], fun ht ↦ ⟨?_, ?_⟩, trivial⟩
          · simp [Main.mkCall, e1316, a9, a1310, epp, a1309]
          · simp only [Main.mkCall, List.map_nil]; exact ((ho1 ht).1).symm
    · -- the loads
      have fin : ∀ {bb : ℕ} {ws : List E} {j off : ℕ},
          (bb, ws) ∈ layerLin D first CL bcur bout b ++ layerBufs D first (ptr bcur) b →
          j + off < ws.length → ∃ i, (ptr bb * gen ^ j).limb 0 * Parameters.gpow off =
            Parameters.gpow i ∧ (RegionL (layerLin D first CL bcur bout b) i ∨
              RegionL (layerBufs D first (ptr bcur) b) i) :=
        fun hq h ↦ inR_split (inR_entry hq h)
      have fin0 : ∀ {bb : ℕ} {ws : List E} {off : ℕ},
          (bb, ws) ∈ layerLin D first CL bcur bout b ++ layerBufs D first (ptr bcur) b →
          off < ws.length → ∃ i, (ptr bb).limb 0 * Parameters.gpow off =
            Parameters.gpow i ∧ (RegionL (layerLin D first CL bcur bout b) i ∨
              RegionL (layerBufs D first (ptr bcur) b) i) := fun {bb ws off} hq h ↦ by
        have := fin (bb := bb) (ws := ws) (j := 0) (off := off) hq (by omega)
        simpa using this
      have hxl := LayerData.xs_length hpl hpm hlm
      have hcl' := LayerData.chs_length (D := D) (first := first) hpm
      intro q hq
      have hg := List.all_eq_true.mp hloads q hq
      simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hg
      obtain ⟨g, hgm, hg1, hg2⟩ := hg
      obtain ⟨p, off⟩ := q
      simp only at hg1 hg2 ⊢
      subst hg1
      simp only [layerGroups, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hgm
      rcases hgm with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hgm
      · rw [a7]; exact fin0 (bb := bcur) (ws := D.xs) (by simp [layerLin]) (by simp only at hg2; omega)
      · rw [a11]; exact fin0 (bb := CL.bclaim) (ws := CL.cw) (by simp [layerLin, ClaimLay.L])
          (by simp only at hg2; omega)
      · rw [a12]; exact fin0 (bb := bout) (ws := D.outW first (ptr b) (ptr (b + D.y + 139))
          (ptr (b + D.y + 128)) (ptr (b + D.y + 164))) (by simp [layerLin])
          (by simp [LayerData.outW, LayerData.next, layerClaim, keccakInstanceWeights_length]; omega)
      · rw [a1310]; exact fin0 (bb := b + D.y) (ws := D.recWords first (ptr bcur))
          (by simp [layerBufs_eq]) (by rw [recWords_length]; omega)
      · rw [e1317, w1310]; exact fin (bb := b + D.y) (ws := D.recWords first (ptr bcur))
          (by simp [layerBufs_eq]) (by rw [recWords_length]; omega)
      · rw [e1323]; exact fin (bb := bcur) (ws := D.xs) (by simp [layerLin]) (by simp only at hg2; omega)
      · rw [e2085, h3]; exact fin0 (bb := CL.blp) (ws := CL.lanes) (by simp [layerLin, ClaimLay.L])
          (by have := hCL.2.2.2.2.2.2.2.2.1; simp only at hg2; omega)
      · rw [a1325]; exact fin0 (bb := b + D.y + 128) (ws := D.locPt first) (by simp [layerBufs_eq]) (by simp only at hg2; omega)
      · rw [a34]; exact fin0 (bb := b + D.y + 139) (ws := lanesOut (D.locPt first) (D.beta first).1)
          (by simp [layerBufs_eq]) (by rw [lanesOut_length]; omega)
      · rw [a278]; exact fin0 (bb := b + D.y + 164) (ws := eqKernel ((D.locPt first).take 6))
          (by simp [layerBufs_eq])
          (by rw [eqKernel_length, List.length_take, hlocL]; simp only at hg2; norm_num; omega)
      · split at hgm
        · simp at hgm
        · rename_i hf1
          simp only [List.mem_singleton] at hgm
          subst hgm
          have hf0 : first = 0 := by omega
          simp only [hf1, ↓reduceIte] at hwt
          obtain ⟨h4, -, hlcl, -⟩ := hwt
          rw [e2086 hf0, h4]
          exact fin0 (bb := CL.blc) (ws := CL.locC) (by simp [layerLin, ClaimLay.L, hf1]) (by simp only at hg2; omega)

end
end LeanVM.Guest.B1.VerifySub
