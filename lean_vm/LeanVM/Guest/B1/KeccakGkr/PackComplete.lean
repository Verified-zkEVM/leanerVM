/-
  LeanVM.Guest.B1.KeccakGkr.PackComplete

  The pack rounds' loop helpers, completely: an honest iteration at every counter gives the loop's
  relation (and its guard at `keccak_layer`'s call).
-/

module

public import LeanVM.Guest.B1.KeccakGkr.PackLoop
public import LeanVM.Guest.B1.KeccakGkr.RoundComplete
public import LeanVM.Guest.B1.Digest.LoopComplete

/-!
# The pack rounds' loop, completely

`packBlock_complete`: from an iteration's meaning at `x` (`PackStep`), the honest valuation
(`Fwd.ev` of the block `packPre` on `[x, N, rec, pp, pt]`) makes every statement of the block
hold. `packLoop_complete`: with the block holding at every `g^j`, `j < m`, the guard and the loop
run (`Digest.guard_complete`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The loop's block: its statements before the self-call. -/
def packPre : List Stmt := ((packLoopT "").dropLast).dropLast

theorem packLoopT_split (name : String) :
    packLoopT name = packPre ++ [.callIf (.n 130) name [.n 132, .n 1, .n 2, .n 3, .n 4], .ret []] :=
  rfl

theorem pack_chk : Fwd.chk 5 packPre = some 133 := by decide +kernel

theorem pack_stores : storesOf 5 packPre =
    [.load (.n 62) (.n 8) 0, .load (.n 114) (.n 8) 1, .load (.n 103) (.n 5) 1,
      .load (.n 104) (.n 5) 17, .load (.n 105) (.n 5) 33, .load (.n 106) (.n 5) 49,
      .load (.n 107) (.n 5) 65, .load (.n 127) (.n 5) 81, .load (.n 124) (.n 5) 97,
      .load (.n 125) (.n 5) 113] := by
  decide +kernel

/-- **The loop's block, completely**: an iteration's meaning at `x` makes the honest valuation of
the block hold. -/
theorem packBlock_complete {rd : Reader} {x N rec pp pt : E} (hs : PackStep rd rec pp pt x) :
    ∃ σ : Val, [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] = [x, N, rec, pp, pt] ∧
      (∀ s ∈ packPre, Stmt.Holds (coreProgram.Rel rd) rd σ s True (fun rs ↦ rs = [])) ∧
      σ (.n 5) = rec * x ∧ σ (.n 7) = pp * x ^ 2 ∧ σ (.n 8) = pt * x ^ 2 ∧
      LoadHolds rd (rec * x) 80 (σ (.n 14)) ∧ σ (.n 130) = x * gen + N ∧
      σ (.n 132) = x * gen := by
  obtain ⟨cap, cur, claim, scale, r0, r1, g1, g2, g1', g2', ⟨⟨hcl, hcap⟩, lcur, lcl, lsc⟩, hcan,
    lr0, lr1, hxs, lc1, lc2, ⟨⟨hcl', hcap'⟩, lcur', lcl', lsc'⟩⟩ := hs
  obtain ⟨c0, c1, c2, c3, c4, rfl⟩ := five_of_length hcl
  have L0 : LoadHolds rd (rec * x) 0 c0 := hcap 0 (by simp)
  have L16 : LoadHolds rd (rec * x) 16 c1 := hcap 1 (by simp)
  have L32 : LoadHolds rd (rec * x) 32 c2 := hcap 2 (by simp)
  have L48 : LoadHolds rd (rec * x) 48 c3 := hcap 3 (by simp)
  have L64 : LoadHolds rd (rec * x) 64 c4 := hcap 4 (by simp)
  have L80 : LoadHolds rd (rec * x) 80 cur := lcur
  have L96 : LoadHolds rd (rec * x) 96 claim := lcl
  have L112 : LoadHolds rd (rec * x) 112 scale := lsc
  have Lg1 : LoadHolds rd cur 0 g1 := hxs 0 (by simp)
  have Lg2 : LoadHolds rd cur 1 g2 := hxs 1 (by simp)
  have Lg1' : LoadHolds rd cur 2 g1' := hxs 2 (by simp)
  have Lg2' : LoadHolds rd cur 3 g2' := hxs 3 (by simp)
  -- the honest valuation
  set l : List E := [x, N, rec, pp, pt] with hl
  have g := (ev_spec rd (fun _ ↦ 0) packPre l pack_chk).2.2
  have pq : ∀ i (hi : i < 5), Val.ofArgs (ev rd (fun _ ↦ 0) l packPre) (.n i) = l.getD i 0 :=
    fun i hi ↦ ev_params rd (fun _ ↦ 0) (l := l) pack_chk (by simpa [hl] using hi)
  rw [show l.length = 5 from rfl, pack_stores] at g
  generalize Val.ofArgs (ev rd (fun _ ↦ 0) l packPre) = σ at g pq
  have p0 : σ (.n 0) = x := pq 0 (by norm_num)
  have p1 : σ (.n 1) = N := pq 1 (by norm_num)
  have p2 : σ (.n 2) = rec := pq 2 (by norm_num)
  have p3 : σ (.n 3) = pp := pq 3 (by norm_num)
  have p4 : σ (.n 4) = pt := pq 4 (by norm_num)
  simp only [packPre, packLoopT, List.dropLast_cons_cons, List.dropLast_singleton] at g
  simp only [List.forall_mem_cons] at g
  simp (config := {decide := true}) only [GoodS, Good, List.mem_cons, List.not_mem_nil,
    Atom.load.injEq, false_or, or_false, true_or, true_and, ↓reduceIte, List.length_cons,
    List.length_nil, Nat.reduceAdd, false_implies, implies_true, and_true] at g
  obtain ⟨e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, l18, e22, e23, e24, e25,
    e26, e27, e28, l28, e32, e33, e34, e35, e36, e37, e38, e39, e40, e41, e42, k43, l44, e57, e58,
    e59, e60, e61, e62, e63, e64, e65, e66, e67, e68, e69, e70, e71, e72, e73, e74, e75, l75, e79,
    e80, e81, e82, e83, e84, e85, l85, e89, e90, e91, e92, e93, e94, k95, l96, e109, e110, e111,
    e112, e113, e114, e115, e116, e117, e118, e119, e120, e121, e122, e123, e124, e125, e126, e127,
    e128, e129, e130, e131, e132⟩ := g
  -- the words read
  have v5 : σ (.n 5) = rec * x := by rw [e5, p2, p0]
  have v6 : σ (.n 6) = x * x := by rw [e6, p0]
  have v7 : σ (.n 7) = pp * x ^ 2 := by rw [e7, p3, v6, pow_two]
  have v8 : σ (.n 8) = pt * x ^ 2 := by rw [e8, p4, v6, pow_two]
  rw [v5, rdAt_of_load' L0] at e9
  rw [v5, rdAt_of_load' L16] at e10
  rw [v5, rdAt_of_load' L32] at e11
  rw [v5, rdAt_of_load' L48] at e12
  rw [v5, rdAt_of_load' L64] at e13
  rw [v5, rdAt_of_load' L80] at e14
  rw [v5, rdAt_of_load' L96] at e15
  rw [v5, rdAt_of_load' L112] at e16
  rw [v7, rdAt_of_load' lr0] at e17
  rw [v7, rdAt_of_load' lr1] at e74
  rw [e14, rdAt_of_load' Lg1] at e18
  rw [e14, rdAt_of_load' Lg2] at e28
  rw [e14, rdAt_of_load' Lg1'] at e75
  rw [e14, rdAt_of_load' Lg2'] at e85
  -- the four words, packed
  have pack : ∀ {b : ℕ}, (∀ j (h : j < 3), σ ([V.n (b + 1), .n (b + 2), .n (b + 3)][j]) =
      limbAt (σ (.n b)) j) → σ (.n (b + 4)) = word 1 0 0 → σ (.n (b + 5)) = word 0 0 1 →
      σ (.n (b + 6)) = σ (.n (b + 5)) * σ (.n (b + 3)) → σ (.n (b + 7)) = σ (.n b) + σ (.n (b + 6)) →
      σ (.n (b + 8)) = word 0 1 0 → σ (.n (b + 9)) = σ (.n (b + 3)) + σ (.n (b + 8)) →
      FsPackOk σ (.n b) (b + 1) dsObserve ∧ IsCanonical128 (σ (.n (b + 7))) := by
    intro b hl a4 a5 a6 a7 a8 a9
    have v3 : σ (.n (b + 3)) = ofK ((σ (.n b)).limb 2) := hl 2 (by norm_num)
    refine ⟨⟨a4, by rw [v3]; exact ofK_isInK _, by rw [a4, word_eOfNat]; exact eOfNat_isInK _, a5,
      a6, a7, a8, a9⟩, ?_⟩
    rw [a7, a6, a5, v3]; exact (fsPackVals_canonical (σ (.n b)) dsObserve).1
  obtain ⟨hp1, c25⟩ := pack (b := 18) l18 e22 e23 e24 e25 e26 e27
  obtain ⟨hp2, c35⟩ := pack (b := 28) l28 e32 e33 e34 e35 e36 e37
  obtain ⟨hp3, c82⟩ := pack (b := 75) l75 e79 e80 e81 e82 e83 e84
  obtain ⟨hp4, c92⟩ := pack (b := 85) l85 e89 e90 e91 e92 e93 e94
  have s1 := fsNext_scalar hp1 c25
  have s2 := fsNext_scalar hp2 c35
  have s3 := fsNext_scalar hp3 c82
  have s4 := fsNext_scalar hp4 c92
  rw [e18] at s1
  rw [e28] at s2
  rw [e75] at s3
  rw [e85] at s4
  have snd : ∀ {a b : E} {v : E}, (a, b) = Keccak.scalarCells v dsObserve → IsCanonical128 b := by
    intro a b v h
    have := congrArg Prod.snd h; simp only at this
    rw [this]; exact (scalarCells_canonical v dsObserve).2
  have cz : IsCanonical128 (word 0 0 0) := by
    rw [word_zero]; unfold IsCanonical128; exact limb_zero 2
  have hc' : ∀ y ∈ [c0, c1, c2, c3, c4], IsCanonical128 y := hcan
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hc'
  obtain ⟨h0, h1, h2, h3, h4⟩ := hc'
  -- the first squeeze
  have hk1 : (Atom.keccak [.n 25, .n 27, .n 35, .n 37, .n 39, .n 40, .n 41, .n 42, .n 9, .n 10,
      .n 11, .n 12, .n 13] [.n 43, .n 44, .n 45, .n 46, .n 47, .n 48, .n 49, .n 50, .n 51, .n 52,
      .n 53, .n 54, .n 55] false false).Holds rd σ := by
    refine keccakA_of rfl rfl ?_ (funext k43)
    intro c hc
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact c25
    · exact snd s1
    · exact c35
    · exact snd s2
    · rw [e39]; exact cz
    · rw [e40]; exact cz
    · rw [e41]; exact cz
    · rw [e42]; exact cz
    · rw [e9]; exact h0
    · rw [e10]; exact h1
    · rw [e11]; exact h2
    · rw [e12]; exact h3
    · rw [e13]; exact h4
  obtain ⟨-, -, -, hout1⟩ := keccak_outs hk1
  have co1 : ∀ k (hk : k < 13), IsCanonical128 (σ ([V.n 43, .n 44, .n 45, .n 46, .n 47, .n 48,
      .n 49, .n 50, .n 51, .n 52, .n 53, .n 54, .n 55].getD k default)) := fun k hk ↦ by
    rw [hout1 k hk]; exact cellsOfState_canonical _ _ _
  have ch1 : ChallengeOk σ (.n 43) (.n 44) 56 := challengeOk_of_vals (co1 1 (by norm_num))
    fun i hi ↦ by
      have v56 : σ (.n 56) = ofK ((σ (.n 44)).limb 0) := l44 0 (by norm_num)
      interval_cases i
      · exact v56
      · show σ (.n 57) = σ (.n 44) + ofK ((σ (.n 44)).limb 0); rw [e57, v56]
      · exact e58
      · show σ (.n 59) = (σ (.n 44) + ofK ((σ (.n 44)).limb 0)) * word 1 0 1
        rw [e59, e57, v56, e58]
      · exact e60
      · show σ (.n 61) = word 0 0 1 * ofK ((σ (.n 44)).limb 0); rw [e61, e60, v56]
      · show σ (.n 62) = σ (.n 43) + word 0 0 1 * ofK ((σ (.n 44)).limb 0); rw [e62, e61, e60, v56]
  set sA : Fs := ⟨[c0, c1, c2, c3, c4], [(g1, dsObserve), (g2, dsObserve)]⟩ with hsA
  have hin1 : [V.n 25, .n 27, .n 35, .n 37, .n 39, .n 40, .n 41, .n 42, .n 9, .n 10, .n 11, .n 12,
      .n 13].map σ = rateOf sA.pend ++ sA.cap := by
    rw [hsA, rateOf_two, ← s1, ← s2]
    simp only [List.map_cons, List.map_nil, e39, e40, e41, e42, word_zero, e9, e10, e11, e12, e13,
      List.cons_append, List.nil_append]
  obtain ⟨hc62, hcapA⟩ := squeeze_atom (rd := rd) hk1 hin1 ch1
  simp only [List.drop, List.map_cons, List.map_nil] at hcapA
  have hsA' : sA.squeeze.2 = ⟨[σ (.n 51), σ (.n 52), σ (.n 53), σ (.n 54), σ (.n 55)], []⟩ := by
    rw [hcapA]; rfl
  -- the second squeeze
  have hk2 : (Atom.keccak [.n 82, .n 84, .n 92, .n 94, .n 39, .n 40, .n 41, .n 42, .n 51, .n 52,
      .n 53, .n 54, .n 55] [.n 95, .n 96, .n 97, .n 98, .n 99, .n 100, .n 101, .n 102, .n 103,
      .n 104, .n 105, .n 106, .n 107] false false).Holds rd σ := by
    refine keccakA_of rfl rfl ?_ (funext k95)
    intro c hc
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact c82
    · exact snd s3
    · exact c92
    · exact snd s4
    · rw [e39]; exact cz
    · rw [e40]; exact cz
    · rw [e41]; exact cz
    · rw [e42]; exact cz
    · exact co1 8 (by norm_num)
    · exact co1 9 (by norm_num)
    · exact co1 10 (by norm_num)
    · exact co1 11 (by norm_num)
    · exact co1 12 (by norm_num)
  obtain ⟨-, -, -, hout2⟩ := keccak_outs hk2
  have ch2 : ChallengeOk σ (.n 95) (.n 96) 108 := challengeOk_of_vals (by
      have := hout2 1 (by norm_num)
      simp only [List.getD_cons_succ, List.getD_cons_zero] at this
      rw [this]; exact cellsOfState_canonical _ _ _)
    fun i hi ↦ by
      have v108 : σ (.n 108) = ofK ((σ (.n 96)).limb 0) := l96 0 (by norm_num)
      interval_cases i
      · exact v108
      · show σ (.n 109) = σ (.n 96) + ofK ((σ (.n 96)).limb 0); rw [e109, v108]
      · exact e110
      · show σ (.n 111) = (σ (.n 96) + ofK ((σ (.n 96)).limb 0)) * word 1 0 1
        rw [e111, e109, v108, e110]
      · exact e112
      · show σ (.n 113) = word 0 0 1 * ofK ((σ (.n 96)).limb 0); rw [e113, e112, v108]
      · show σ (.n 114) = σ (.n 95) + word 0 0 1 * ofK ((σ (.n 96)).limb 0)
        rw [e114, e113, e112, v108]
  set sB : Fs := ⟨[σ (.n 51), σ (.n 52), σ (.n 53), σ (.n 54), σ (.n 55)],
    [(g1', dsObserve), (g2', dsObserve)]⟩ with hsB
  have hin2 : [V.n 82, .n 84, .n 92, .n 94, .n 39, .n 40, .n 41, .n 42, .n 51, .n 52, .n 53, .n 54,
      .n 55].map σ = rateOf sB.pend ++ sB.cap := by
    rw [hsB, rateOf_two, ← s3, ← s4]
    simp only [List.map_cons, List.map_nil, e39, e40, e41, e42, word_zero, List.cons_append,
      List.nil_append]
  obtain ⟨hc114, hcapB⟩ := squeeze_atom (rd := rd) hk2 hin2 ch2
  simp only [List.drop, List.map_cons, List.map_nil] at hcapB
  -- the meaning's outputs
  have habsA : (⟨[c0, c1, c2, c3, c4], []⟩ : Fs).absorbAll [g1, g2] dsObserve = sA := rfl
  have habsB : (⟨[σ (.n 51), σ (.n 52), σ (.n 53), σ (.n 54), σ (.n 55)], []⟩ : Fs).absorbAll
      [g1', g2'] dsObserve = sB := rfl
  simp only [eqRound, habsA, hsA', habsB] at lc1 lc2 hcap' lcur' lcl' lsc'
  have h62 : σ (.n 62) = sA.squeeze.1 := hc62
  have h114 : σ (.n 114) = sB.squeeze.1 := hc114
  have v72 : σ (.n 72) = (1 + (r0 + sA.squeeze.1)) *
      (claim + (r0 + sA.squeeze.1) * g1 + (r0 + sA.squeeze.1 * sA.squeeze.1) * g2) := by
    rw [e72, e65, e64, e71, e67, e70, e69, e68, e66, e63, e15, e17, e18, e28, h62, word_one]
  have v73 : σ (.n 73) = scale * (1 + (r0 + sA.squeeze.1)) := by
    rw [e73, e16, e65, e64, e63, e17, h62, word_one]
  have v117 : σ (.n 117) = 1 + (r1 + sB.squeeze.1) := by rw [e117, e116, e115, e74, h114, word_one]
  have v124 : σ (.n 124) = (1 + (r1 + sB.squeeze.1)) *
      ((1 + (r0 + sA.squeeze.1)) * (claim + (r0 + sA.squeeze.1) * g1 +
        (r0 + sA.squeeze.1 * sA.squeeze.1) * g2) + (r1 + sB.squeeze.1) * g1' +
        (r1 + sB.squeeze.1 * sB.squeeze.1) * g2') := by
    rw [e124, v117, e123, e122, e121, e120, e119, e118, e115, v72, e74, e75, e85, h114]
  have v125 : σ (.n 125) = scale * (1 + (r0 + sA.squeeze.1)) * (1 + (r1 + sB.squeeze.1)) := by
    rw [e125, v73, v117]
  have v127 : σ (.n 127) = cur * gen ^ 4 := by rw [e127, e14, e126, word_16]
  have hcO : ∀ j (hj : j < 5), LoadHolds rd (rec * x) (1 + j * 16)
      ([σ (.n 103), σ (.n 104), σ (.n 105), σ (.n 106), σ (.n 107)][j]'(by simpa using hj)) := by
    intro j hj
    have := hcap' j (by rw [← hcapB]; simpa using hj)
    simp only [krCap] at this
    convert this using 2
  have ld : ∀ {d p : V} {off : ℕ} {pv dv : E}, σ p = pv → σ d = dv → LoadHolds rd pv off dv →
      (Atom.load d p off).Holds rd σ := by
    intro d p off pv dv hp hd h
    show LoadHolds rd (σ p) off (σ d)
    rw [hp, hd]; exact h
  have inK : ∀ {a b : V}, IsInK (σ a) → IsInK (σ b) → (Atom.assertInK a b).Holds rd σ :=
    fun ha hb ↦ ⟨ha, hb⟩
  refine ⟨σ, by rw [p0, p1, p2, p3, p4], ?_, v5, v7, v8, by rw [e14]; exact L80,
    by rw [e130, e129, e128, p0, p1, word_gen], by rw [e132, e131, p0, word_gen]⟩
  simp only [packPre, packLoopT, List.dropLast_cons_cons, List.dropLast_singleton,
    List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
    Stmt.Holds]
  exact ⟨e5, e6, e7, e8, ld v5 e9 L0, ld v5 e10 L16, ld v5 e11 L32, ld v5 e12 L48, ld v5 e13 L64,
    ld v5 e14 L80, ld v5 e15 L96, ld v5 e16 L112, ld v7 e17 lr0, ld e14 e18 Lg1, trivial, e22,
    inK hp1.2.1 hp1.2.2.1, e23, e24, e25, e26, e27, ld e14 e28 Lg2, trivial, e32,
    inK hp2.2.1 hp2.2.2.1, e33, e34, e35, e36, e37, e38, e39, e40, e41, e42, hk1, trivial, e57,
    e58, e59, inK ch1.2.2.2.1 ch1.2.2.2.2.1, e60, e61, e62, ld v8 h62 lc1, e63, e64, e65, e66,
    e67, e68, e69, e70, e71, e72, e73, ld v7 e74 lr1, ld e14 e75 Lg1', trivial, e79,
    inK hp3.2.1 hp3.2.2.1, e80, e81, e82, e83, e84, ld e14 e85 Lg2', trivial, e89,
    inK hp4.2.1 hp4.2.2.1, e90, e91, e92, e93, e94, hk2, trivial, e109, e110, e111,
    inK ch2.2.2.2.1 ch2.2.2.2.2.1, e112, e113, e114, ld v8 h114 lc2, e115, e116, e117, e118, e119,
    e120, e121, e122, e123, e124, e125, ld v5 rfl (hcO 0 (by norm_num)),
    ld v5 rfl (hcO 1 (by norm_num)), ld v5 rfl (hcO 2 (by norm_num)),
    ld v5 rfl (hcO 3 (by norm_num)), ld v5 rfl (hcO 4 (by norm_num)), e126, e127,
    ld v5 v127 lcur', ld v5 v124 lcl', ld v5 v125 lsc', e128, e129, e130, e131, e132⟩



end
end LeanVM.Guest.B1.VerifySub
