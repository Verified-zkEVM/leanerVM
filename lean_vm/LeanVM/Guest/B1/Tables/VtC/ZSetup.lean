/-
  LeanVM.Guest.B1.Tables.VtC.ZSetup

  `verify_tables`' statements `5152 ..< 5259`, completely: the table sumcheck's round count, its
  batching challenge and target, its rounds and its equality prefix.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.ZBase

/-!
# The table sumcheck's setup, completely (G:2178-2223)

Helpers for the honest valuation: a read of a word the memory holds (`z_read`), a product read
as a quotient (`z_div`), a passing range check (`z_rc`, `z_rcd`), a `KECCAK` of canonical cells
(`z_keccak`), `challenge_from_state` (`z_challenge`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

section Helpers
variable {rd : Reader} {σ : Val}

theorem z_canon_zero : IsCanonical128 (0 : E) := by
  rw [zero_eq_ofLimbs]; exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl

/-- A read of a word the memory holds. -/
theorem z_read {d p : V} {off : ℕ} {v : E}
    (hg : Atom.load d p off ∈ vtSL ∨ σ d = rdAt rd (σ p) off) (hS : Atom.load d p off ∉ vtSL)
    (hm : LoadHolds rd (σ p) off v) : σ d = v ∧ (Atom.load d p off).Holds rd σ := by
  have e : σ d = v := by rw [hg.resolve_left hS, rdAt, hm.2]; rfl
  exact ⟨e, by show LoadHolds rd _ _ _; rw [e]; exact hm⟩

/-- A product read as a quotient. -/
theorem z_div {d x y : V} (hg : σ x = σ d * (σ y)⁻¹) (hy : σ y ≠ 0) :
    (Atom.mul d x y).Holds rd σ := by
  show σ d = σ x * σ y
  rw [hg, mul_assoc, inv_mul_cancel₀ hy, mul_one]

theorem z_gen_addr (a : ℕ) : (gen ^ a).limb 0 * Parameters.gpow 0 = Parameters.gpow a := by
  rw [gen_pow_eq_ofK]; simp [Parameters.gpow]

theorem z_low_load {a : ℕ} (h : (rd (Parameters.gpow a)).isSome) :
    LoadHolds rd (gen ^ a) 0 (rdAt rd (gen ^ a) 0) :=
  load_of_rdAt rfl (gen_pow_isInK a) (by rw [z_gen_addr]; exact h)

/-- **A passing range check**: `x = g^a`, `a ≤ K`, `k = g^K`, on a memory defined at `g^a` and
`g^(K - a)`. -/
theorem z_rc {x y t1 t2 k : V} {a K : ℕ} (haK : a ≤ K) (hx : σ x = gen ^ a) (hk : σ k = gen ^ K)
    (hg : σ t1 = rdAt rd (σ x) 0 ∧ σ t2 = rdAt rd (σ y) 0 ∧ σ y = σ k * (σ x)⁻¹)
    (h1 : (rd (Parameters.gpow a)).isSome) (h2 : (rd (Parameters.gpow (K - a))).isSome) :
    (Atom.rangeCheck x y t1 t2 k).Holds rd σ := by
  obtain ⟨e1, e2, ey⟩ := hg
  have ey' : σ y = gen ^ (K - a) := by rw [ey, hk, hx, ← pow_sub₀ _ gen_ne_zero haK]
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, hx]; exact z_low_load h1
  · rw [hk, hx, ey', ← pow_add, Nat.add_sub_cancel' haK]
  · rw [e2, ey']; exact z_low_load h2

/-- A range check's facts, as `eq_prefix_chain` states them. -/
theorem z_rcd {a K : ℕ} (haK : a ≤ K) (h1 : (rd (Parameters.gpow a)).isSome)
    (h2 : (rd (Parameters.gpow (K - a))).isSome) : RangeChecked rd (gen ^ a) (gen ^ K) :=
  ⟨gen ^ (K - a), _, _, z_low_load h1, by rw [← pow_add, Nat.add_sub_cancel' haK],
    z_low_load h2⟩

/-- **A `KECCAK` of canonical cells.** -/
theorem z_keccak {S : List Atom} {w : ℕ → E} {ins outs : List V} {i o : Bool}
    (hg : Good rd S w σ (.keccak ins outs i o)) (hc : AllCanonical (ins.map σ)) :
    (Atom.keccak ins outs i o).Holds rd σ := by
  refine holds_of_good hg fun c => ?_
  simp only [cells13, List.getD_eq_getElem?_getD]
  rcases h : (ins.map σ)[c.val]? with _ | x
  · exact z_canon_zero
  · exact hc x (List.mem_of_getElem? h)

theorem z_w32 : word 4294967296 0 0 = gen ^ 32 := by
  rw [show (4294967296 : ℕ) = 2 ^ 32 by norm_num, tb_word_two_pow (by norm_num)]

/-- **`challenge_from_state`'s atoms** on a canonical cell `s1`, by their equations. -/
theorem z_challenge {w : ℕ → E} {s0 s1 : V} {b : ℕ} (hg : GoodL rd w σ (challengeT s0 s1 b))
    (hc : IsCanonical128 (σ s1)) : ChallengeOk σ s0 s1 b := by
  simp only [challengeT, GoodL, GoodS, Good, fixNe] at hg
  obtain ⟨h0, h1, h2, h3, -, h5, h6, h7, -⟩ := hg
  rw [ite_pos' (by simp)] at h3 h6
  refine challengeOk_of_vals hc fun i hi => ?_
  have e0 : σ (.n b) = ofK ((σ s1).limb 0) := by
    have := h0 0 (by simp); simpa [limbAt] using this
  interval_cases i
  · exact e0
  · rw [h1, e0]; rfl
  · exact h2
  · rw [h3, h1, h2, e0]; rfl
  · exact h5
  · rw [h6, h5, e0]; rfl
  · rw [h7, h6, h5, e0]; rfl

end Helpers

/-- The bus target: `ξ²·T_0 + ξ³·T_1 + ξ⁴·T_2` on the sides' totals. -/
def zTarget (σ : Val) (ξ : E) : E :=
  ξ ^ 2 * σ (.n 4411) + ξ ^ 3 * σ (.n 4924) + ξ ^ 4 * σ (.n 5816)

/-- What statements `5152 ..< 5259` give: `g^n`, `ξ` (the squeeze of `S`), the sponge after it,
the target, the buffers' sizes and pointers, and the last record (the sponge, the cursor `3n`
words on, the final claim). -/
def ZOut (σ : Val) (w : ℕ → E) (S : Fs) (xs : List E) (n : ℕ) : Prop :=
  σ (.n 5817) = gen ^ n ∧ σ (.n 5895) = S.squeeze.1 ∧
    [σ (.n 5884), σ (.n 5885), σ (.n 5886), σ (.n 5887), σ (.n 5888)] = S.squeeze.2.cap ∧
    σ (.n 5905) = zTarget σ S.squeeze.1 ∧ σ (.n 5911) = gen ^ (7 * (n + 1)) ∧
    σ (.n 5914) = gen ^ (n + 1) ∧ σ (.n 5935) = gen ^ (n + 1) ∧ σ (.n 5912) = w 5912 ∧
    σ (.n 5915) = w 5915 ∧ σ (.n 5936) = w 5936 ∧
    [σ (.n 5927), σ (.n 5928), σ (.n 5929), σ (.n 5930), σ (.n 5931)] =
      (zcRec S.squeeze.2.cap (zTarget σ S.squeeze.1) xs n).1 ∧
    σ (.n 5932) = σ (.n 5) * gen ^ 5 * gen ^ (3 * n) ∧
    σ (.n 5933) = (zcRec S.squeeze.2.cap (zTarget σ S.squeeze.1) xs n).2

/-- The statements evaluation alone does not settle. -/
noncomputable def zRest : List Stmt := [
    .atom (.load (.n 5818) (.n 10) 1),
    .atom (.mul (.n 5817) (.n 5820) (.n 5818)),
    .atom (.rangeCheck (.n 5820) (.n 5821) (.n 5822) (.n 5823) (.n 5819)),
    .atom (.load (.n 5825) (.n 10) 2),
    .atom (.mul (.n 5817) (.n 5827) (.n 5825)),
    .atom (.rangeCheck (.n 5827) (.n 5828) (.n 5829) (.n 5830) (.n 5826)),
    .atom (.load (.n 5833) (.n 10) 3),
    .atom (.mul (.n 5817) (.n 5835) (.n 5833)),
    .atom (.rangeCheck (.n 5835) (.n 5836) (.n 5837) (.n 5838) (.n 5834)),
    .atom (.load (.n 5841) (.n 10) 4),
    .atom (.mul (.n 5817) (.n 5843) (.n 5841)),
    .atom (.rangeCheck (.n 5843) (.n 5844) (.n 5845) (.n 5846) (.n 5842)),
    .atom (.load (.n 5849) (.n 10) 5),
    .atom (.mul (.n 5817) (.n 5851) (.n 5849)),
    .atom (.rangeCheck (.n 5851) (.n 5852) (.n 5853) (.n 5854) (.n 5850)),
    .atom (.load (.n 5857) (.n 10) 6),
    .atom (.mul (.n 5817) (.n 5859) (.n 5857)),
    .atom (.rangeCheck (.n 5859) (.n 5860) (.n 5861) (.n 5862) (.n 5858)),
    .atom (.assertEq (.n 5864) (.n 5865)),
    .atom (.mul (.n 9) (.n 5867) (.n 5817)),
    .atom (.rangeCheck (.n 5867) (.n 5868) (.n 5869) (.n 5870) (.n 5866)),
    .atom (.keccak [.n 4509, .n 4511, .n 5872, .n 5872, .n 5872, .n 5873, .n 5874, .n 5875, .n 4497, .n 4498, .n 4499, .n 4500, .n 4501] [.n 5876, .n 5877, .n 5878, .n 5879, .n 5880, .n 5881, .n 5882, .n 5883, .n 5884, .n 5885, .n 5886, .n 5887, .n 5888] false false),
    .atom (.assertInK (.n 5889) (.n 5892)),
    .atom (.load (.n 5884) (.n 5912) 0),
    .atom (.load (.n 5885) (.n 5912) 1),
    .atom (.load (.n 5886) (.n 5912) 2),
    .atom (.load (.n 5887) (.n 5912) 3),
    .atom (.load (.n 5888) (.n 5912) 4),
    .atom (.load (.n 5917) (.n 5912) 5),
    .atom (.load (.n 5905) (.n 5912) 6),
    .atom (.load (.n 5918) (.n 5915) 0),
    .callIf (.n 5920) "__loop9" [.n 5921, .n 5817, .n 5912, .n 18, .n 5817, .n 5915],
    .atom (.load (.n 5927) (.n 5926) 0),
    .atom (.load (.n 5928) (.n 5926) 1),
    .atom (.load (.n 5929) (.n 5926) 2),
    .atom (.load (.n 5930) (.n 5926) 3),
    .atom (.load (.n 5931) (.n 5926) 4),
    .atom (.load (.n 5932) (.n 5926) 5),
    .atom (.load (.n 5933) (.n 5926) 6),
    .call "eq_prefix_chain" [.n 5936, .n 5937, .n 18, .n 2767, .n 5817] []]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **Statements `5152 ..< 5259`, completely** (G:2178-2223): the hinted `g^n` with `n` the
largest `τ_t` (at most `m = |point|`), the squeeze `ξ` of the sponge `S` after the bus words,
the target, the first record, `__loop9`'s rounds on the honest buffers (records, running
products, `chi`) and words `xs` at the cursor five on, the last record, `eq_prefix_chain` into
the prefix weights of `chi` against `zeta1`. -/
theorem vtZ_complete {rd : Reader} {w : ℕ → E} {args : List E} (hl : args.length = 22)
    {m n : ℕ} {τ : ℕ → ℕ} (hτ : ∀ t < 6, τ t ≤ n) (hτn : ∃ t < 6, τ t = n) (hnm : n ≤ m)
    (hm : m ≤ 32) (h9 : vtσ rd w args (.n 9) = gen ^ m)
    (hdim : ∀ t < 6, LoadHolds rd (vtσ rd w args (.n 10)) (t + 1) (gen ^ τ t))
    (hlow : ∀ i < 64, (rd (Parameters.gpow i)).isSome) (hwn : w 5817 = gen ^ n) {S : Fs}
    (hSr : rateOf S.pend = [vtσ rd w args (.n 4509), vtσ rd w args (.n 4511), 0, 0, 0, 0, 0, 0])
    (hSc : S.cap = [vtσ rd w args (.n 4497), vtσ rd w args (.n 4498), vtσ rd w args (.n 4499),
      vtσ rd w args (.n 4500), vtσ rd w args (.n 4501)])
    (hcan : AllCanonical (rateOf S.pend ++ S.cap)) {xs : List E} (hxl : xs.length = 3 * n)
    (hxs : TbReadsAt rd (vtσ rd w args (.n 5) * gen ^ 5) xs)
    (hR : TbReadsAt rd (w 5912) (zcRoundsW S.squeeze.2.cap (zTarget (vtσ rd w args) S.squeeze.1)
      (vtσ rd w args (.n 5) * gen ^ 5) xs n))
    (hC : TbReadsAt rd (w 5915) (zcCprodW S.squeeze.2.cap (zTarget (vtσ rd w args) S.squeeze.1) xs n))
    (hchi : TbReadsAt rd (vtσ rd w args (.n 18))
      (zcChis S.squeeze.2.cap (zTarget (vtσ rd w args) S.squeeze.1) xs n))
    {zs1 : List E} (hz1 : TbReadsAt rd (vtσ rd w args (.n 2767)) zs1) (hz1l : n ≤ zs1.length)
    (hP : TbReadsAt rd (w 5936) ((List.range (n + 1)).map (prefixProd 1
      (zcChis S.squeeze.2.cap (zTarget (vtσ rd w args) S.squeeze.1) xs n) (zs1.take n)))) :
    (∀ s ∈ (vtPre.drop 5152).take 107, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) ∧
      ZOut (vtσ rd w args) w S xs n := by
  have g : GoodL rd w (vtσ rd w args) zBlk := vt_goodL hl 5152 zBlk zBlk_at
  have gk : Good rd vtSL w (vtσ rd w args) (.keccak [.n 4509, .n 4511, .n 5872, .n 5872, .n 5872,
      .n 5873, .n 5874, .n 5875, .n 4497, .n 4498, .n 4499, .n 4500, .n 4501] (lyOuts 5876) false
      false) := (vt_goodL (rd := rd) (w := w) hl 5198 [.atom (.keccak [.n 4509, .n 4511, .n 5872,
      .n 5872, .n 5872, .n 5873, .n 5874, .n 5875, .n 4497, .n 4498, .n 4499, .n 4500, .n 4501]
      (lyOuts 5876) false false)] (by decide +kernel)).1
  have gch : GoodL rd w (vtσ rd w args) (challengeT (.n 5876) (.n 5877) 5889) :=
    vt_goodL hl 5199 _ (by decide +kernel)
  have e := tbStmtsEqb_sound zBlk_at
  have hlen107 : zBlk.length = 107 := rfl
  suffices H : (∀ s ∈ zRest, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) ∧
      ZOut (vtσ rd w args) w S xs n by
    refine ⟨fun s hs => ?_, H.2⟩
    rw [← hlen107, ← e] at hs
    exact vt_block hl 5152 zBlk zBlk_at zRest (by decide +kernel) H.1 s hs
  generalize vtσ rd w args = σ at *
  simp only [zBlk, GoodL, GoodS, Good, fixNe, List.forall_mem_cons, Nat.reduceLT, and_true,
    and_false, ↓reduceIte] at g
  obtain ⟨g5152, g5153, g5154, g5155, g5156, g5157, g5158, g5159, g5160, g5161, g5162, g5163, g5164, g5165, g5166, g5167, g5168, g5169, g5170, g5171, g5172, g5173, g5174, g5175, g5176, g5177, g5178, g5179, g5180, g5181, g5182, g5183, g5184, g5185, g5186, g5187, g5188, g5189, g5190, g5191, g5192, g5193, g5194, g5195, g5196, g5197, g5198, g5199, g5200, g5201, g5202, g5203, g5204, g5205, g5206, g5207, g5208, g5209, g5210, g5211, g5212, g5213, g5214, g5215, g5216, g5217, g5218, g5219, g5220, g5221, g5222, g5223, g5224, g5225, g5226, g5227, g5228, g5229, g5230, g5231, g5232, g5233, g5234, g5235, g5236, g5237, g5238, g5239, g5240, g5241, g5242, g5243, g5244, g5245, g5246, g5247, g5248, g5249, g5250, g5251, g5252, g5253, g5254, g5255, g5256, g5257, g5258⟩ := g
  have v5817 : σ (.n 5817) = gen ^ n := g5152.1.trans hwn
  obtain ⟨d0, r5153⟩ := z_read g5153 (by decide +kernel) (hdim 0 (by norm_num))
  have x0 : σ (.n 5820) = gen ^ (n - τ 0) := by
    rw [g5155, v5817, d0, ← pow_sub₀ _ gen_ne_zero (hτ 0 (by norm_num))]
  have rc5156 := z_rc (a := n - τ 0) (K := 32) (by omega) x0 (g5154.trans z_w32) g5156
    (hlow _ (by omega)) (hlow _ (by omega))
  have m5155 := z_div (rd := rd) g5155 (by rw [d0]; exact pow_ne_zero _ gen_ne_zero)
  obtain ⟨d1, r5158⟩ := z_read g5158 (by decide +kernel) (hdim 1 (by norm_num))
  have x1 : σ (.n 5827) = gen ^ (n - τ 1) := by
    rw [g5160, v5817, d1, ← pow_sub₀ _ gen_ne_zero (hτ 1 (by norm_num))]
  have rc5161 := z_rc (a := n - τ 1) (K := 32) (by omega) x1 (g5159.trans z_w32) g5161
    (hlow _ (by omega)) (hlow _ (by omega))
  have m5160 := z_div (rd := rd) g5160 (by rw [d1]; exact pow_ne_zero _ gen_ne_zero)
  obtain ⟨d2, r5164⟩ := z_read g5164 (by decide +kernel) (hdim 2 (by norm_num))
  have x2 : σ (.n 5835) = gen ^ (n - τ 2) := by
    rw [g5166, v5817, d2, ← pow_sub₀ _ gen_ne_zero (hτ 2 (by norm_num))]
  have rc5167 := z_rc (a := n - τ 2) (K := 32) (by omega) x2 (g5165.trans z_w32) g5167
    (hlow _ (by omega)) (hlow _ (by omega))
  have m5166 := z_div (rd := rd) g5166 (by rw [d2]; exact pow_ne_zero _ gen_ne_zero)
  obtain ⟨d3, r5170⟩ := z_read g5170 (by decide +kernel) (hdim 3 (by norm_num))
  have x3 : σ (.n 5843) = gen ^ (n - τ 3) := by
    rw [g5172, v5817, d3, ← pow_sub₀ _ gen_ne_zero (hτ 3 (by norm_num))]
  have rc5173 := z_rc (a := n - τ 3) (K := 32) (by omega) x3 (g5171.trans z_w32) g5173
    (hlow _ (by omega)) (hlow _ (by omega))
  have m5172 := z_div (rd := rd) g5172 (by rw [d3]; exact pow_ne_zero _ gen_ne_zero)
  obtain ⟨d4, r5176⟩ := z_read g5176 (by decide +kernel) (hdim 4 (by norm_num))
  have x4 : σ (.n 5851) = gen ^ (n - τ 4) := by
    rw [g5178, v5817, d4, ← pow_sub₀ _ gen_ne_zero (hτ 4 (by norm_num))]
  have rc5179 := z_rc (a := n - τ 4) (K := 32) (by omega) x4 (g5177.trans z_w32) g5179
    (hlow _ (by omega)) (hlow _ (by omega))
  have m5178 := z_div (rd := rd) g5178 (by rw [d4]; exact pow_ne_zero _ gen_ne_zero)
  obtain ⟨d5, r5182⟩ := z_read g5182 (by decide +kernel) (hdim 5 (by norm_num))
  have x5 : σ (.n 5859) = gen ^ (n - τ 5) := by
    rw [g5184, v5817, d5, ← pow_sub₀ _ gen_ne_zero (hτ 5 (by norm_num))]
  have rc5185 := z_rc (a := n - τ 5) (K := 32) (by omega) x5 (g5183.trans z_w32) g5185
    (hlow _ (by omega)) (hlow _ (by omega))
  have m5184 := z_div (rd := rd) g5184 (by rw [d5]; exact pow_ne_zero _ gen_ne_zero)

  -- n ≤ m
  have x6 : σ (.n 5867) = gen ^ (m - n) := by
    rw [g5191, h9, v5817, ← pow_sub₀ _ gen_ne_zero hnm]
  have rc5192 := z_rc (a := m - n) (K := 32) (by omega) x6 (g5190.trans z_w32) g5192
    (hlow _ (by omega)) (hlow _ (by omega))
  have m5191 := z_div (rd := rd) g5191 (by rw [v5817]; exact pow_ne_zero _ gen_ne_zero)
  -- some τ_t is n
  have hz : σ (.n 5864) = 0 := by
    rw [g5187, g5181, g5175, g5169, g5163, g5157, g5162, g5168, g5174, g5180, g5186, v5817, d0, d1,
      d2, d3, d4, d5]
    obtain ⟨t, ht, hte⟩ := hτn
    interval_cases t <;> simp [hte, CharTwo.add_self_eq_zero]
  have a5189 : (Atom.assertEq (.n 5864) (.n 5865)).Holds rd σ := by
    show σ (.n 5864) + σ (.n 5865) = 0
    rw [hz, g5188, tb_word_zero, add_zero]
  -- the squeeze
  have hz0 : σ (.n 5872) = 0 := g5194.trans tb_word_zero
  have hz1' : σ (.n 5873) = 0 := g5195.trans tb_word_zero
  have hz2 : σ (.n 5874) = 0 := g5196.trans tb_word_zero
  have hz3 : σ (.n 5875) = 0 := g5197.trans tb_word_zero
  have hin : ([.n 4509, .n 4511, .n 5872, .n 5872, .n 5872, .n 5873, .n 5874, .n 5875, .n 4497,
      .n 4498, .n 4499, .n 4500, .n 4501] : List V).map σ = rateOf S.pend ++ S.cap := by
    rw [hSr, hSc]; simp [hz0, hz1', hz2, hz3]
  have k5198 : (Atom.keccak [.n 4509, .n 4511, .n 5872, .n 5872, .n 5872, .n 5873, .n 5874,
      .n 5875, .n 4497, .n 4498, .n 4499, .n 4500, .n 4501] (lyOuts 5876) false false).Holds rd σ :=
    z_keccak gk (by rw [hin]; exact hcan)
  obtain ⟨-, hPk, -⟩ := ly_keccak k5198
  rw [hin] at hPk
  have hch : ChallengeOk σ (.n 5876) (.n 5877) 5889 :=
    z_challenge gch
      (by rw [hPk 1 (by norm_num)]; exact cellsOfState_canonical _ _ _)
  have vξ : σ (.n 5895) = S.squeeze.1 :=
    challengeT_value hch (hPk 0 (by norm_num)) (hPk 1 (by norm_num))
  have hcap0 : [σ (.n 5884), σ (.n 5885), σ (.n 5886), σ (.n 5887), σ (.n 5888)] =
      S.squeeze.2.cap := by
    rw [hPk 8 (by norm_num), hPk 9 (by norm_num), hPk 10 (by norm_num), hPk 11 (by norm_num),
      hPk 12 (by norm_num)]
    rfl
  have vT : σ (.n 5905) = zTarget σ S.squeeze.1 := by
    rw [g5216, g5214, g5212, g5213, g5215, g5211, g5210, g5209, g5208, g5207, tb_word_one, vξ,
      zTarget]
    ring
  -- the buffers
  set cap0 := S.squeeze.2.cap with hcap0d
  set cl0 := zTarget σ S.squeeze.1 with hcl0d
  have h5 : cap0.length = 5 := rfl
  have hcan0 : AllCanonical cap0 := tb_capOf_canonical _
  have v5912 : σ (.n 5912) = w 5912 := g5223
  have v5915 : σ (.n 5915) = w 5915 := g5226
  have v5936 : σ (.n 5936) = w 5936 := g5256
  have r0 := zcRoundsW_reads h5 hR 0 (by omega)
  rw [Nat.mul_zero, pow_zero, mul_one, zcRecW, ← v5912] at r0
  simp only [zcRec, Nat.mul_zero, pow_zero, mul_one, ← hcap0, ← vT] at r0
  have v5917 : σ (.n 5917) = σ (.n 5) * gen ^ 5 := by
    rw [g5233, g5232, show (32 : ℕ) = 2 ^ 5 by norm_num, tb_word_two_pow (by norm_num)]
  have s5237 : (Atom.load (.n 5918) (.n 5915) 0).Holds rd σ := by
    show LoadHolds rd _ _ _
    rw [g5236, tb_word_one, v5915]
    simpa [zcCprodW] using hC 0 (by simp [zcCprodW])
  -- the rounds
  have v5920 : σ (.n 5920) = 1 + gen ^ n := by rw [g5239, g5238, tb_word_one, v5817]
  have c5241 : VSH (coreProgram.Rel rd) rd σ
      (.callIf (.n 5920) "__loop9" [.n 5921, .n 5817, .n 5912, .n 18, .n 5817, .n 5915]) := by
    refine ⟨by rw [v5920]; exact isInK_add (by simpa using gen_pow_isInK 0) (gen_pow_isInK n),
      fun hne => ?_⟩
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · exact absurd (by rw [v5920, pow_zero]; exact CharTwo.add_self_eq_zero 1) hne
      · exact h
    simp only [List.map_cons, List.map_nil]
    rw [g5240, tb_word_one, v5817, v5912, v5915]
    exact l10_complete hn0 (zc_l10B h5 hcan0 hR hC hchi hxs hxl)
  -- the last record
  have v5926 : σ (.n 5926) = w 5912 * gen ^ (7 * n) := by
    rw [g5246, g5245, g5244, g5243, g5242, v5817, v5912]; ring
  have rn := zcRoundsW_reads h5 hR n le_rfl
  rw [zcRecW, ← v5926] at rn
  have hlen := zcRec_len (cl0 := cl0) (xs := xs) h5 n
  obtain ⟨e0, r5247⟩ := z_read g5247 (by decide +kernel) (rn 0 (by simp [hlen]))
  obtain ⟨e1, r5248⟩ := z_read g5248 (by decide +kernel) (rn 1 (by simp [hlen]))
  obtain ⟨e2, r5249⟩ := z_read g5249 (by decide +kernel) (rn 2 (by simp [hlen]))
  obtain ⟨e3, r5250⟩ := z_read g5250 (by decide +kernel) (rn 3 (by simp [hlen]))
  obtain ⟨e4, r5251⟩ := z_read g5251 (by decide +kernel) (rn 4 (by simp [hlen]))
  obtain ⟨e5, r5252⟩ := z_read g5252 (by decide +kernel) (rn 5 (by simp [hlen]))
  obtain ⟨e6, r5253⟩ := z_read g5253 (by decide +kernel) (rn 6 (by simp [hlen]))
  -- the equality prefix
  have c5258 : VSH (coreProgram.Rel rd) rd σ
      (.call "eq_prefix_chain" [.n 5936, .n 5937, .n 18, .n 2767, .n 5817] []) := by
    show coreProgram.Rel rd _ _ _
    simp only [List.map_cons, List.map_nil]
    rw [g5257, tb_word_one, v5817, v5936]
    refine (eq_prefix_chain_holds rd _ _).mpr ⟨rfl, z_rcd (by omega) (hlow _ (by omega))
      (hlow _ (by omega)), n, by omega, rfl, zcChis cap0 cl0 xs n, zs1.take n, by simp [zcChis],
      by simp; omega, hchi, tbReadsAt_take hz1 n, fun j hj => ?_⟩
    have := hP j (by simp; omega)
    simpa using this
  -- the statements
  have i5203 : (Atom.assertInK (.n 5889) (.n 5892)).Holds rd σ := ⟨hch.2.2.2.1, hch.2.2.2.2.1⟩
  have s5227 : (Atom.load (.n 5884) (.n 5912) 0).Holds rd σ := r0 0 (by simp)
  have s5228 : (Atom.load (.n 5885) (.n 5912) 1).Holds rd σ := r0 1 (by simp)
  have s5229 : (Atom.load (.n 5886) (.n 5912) 2).Holds rd σ := r0 2 (by simp)
  have s5230 : (Atom.load (.n 5887) (.n 5912) 3).Holds rd σ := r0 3 (by simp)
  have s5231 : (Atom.load (.n 5888) (.n 5912) 4).Holds rd σ := r0 4 (by simp)
  have s5234 : (Atom.load (.n 5917) (.n 5912) 5).Holds rd σ := by
    show LoadHolds rd _ _ _; rw [v5917]; exact r0 5 (by simp)
  have s5235 : (Atom.load (.n 5905) (.n 5912) 6).Holds rd σ := r0 6 (by simp)
  have hrest : ∀ s ∈ zRest, VSH (coreProgram.Rel rd) rd σ s := by
    intro s hs
    simp only [zRest, List.mem_cons, List.not_mem_nil, or_false] at hs
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl := hs
    · exact r5153
    · exact m5155
    · exact rc5156
    · exact r5158
    · exact m5160
    · exact rc5161
    · exact r5164
    · exact m5166
    · exact rc5167
    · exact r5170
    · exact m5172
    · exact rc5173
    · exact r5176
    · exact m5178
    · exact rc5179
    · exact r5182
    · exact m5184
    · exact rc5185
    · exact a5189
    · exact m5191
    · exact rc5192
    · exact k5198
    · exact i5203
    · exact s5227
    · exact s5228
    · exact s5229
    · exact s5230
    · exact s5231
    · exact s5234
    · exact s5235
    · exact s5237
    · exact c5241
    · exact r5247
    · exact r5248
    · exact r5249
    · exact r5250
    · exact r5251
    · exact r5252
    · exact r5253
    · exact c5258
  refine ⟨hrest, v5817, vξ, hcap0, vT, ?_, ?_, ?_, v5912, v5915, v5936, ?_, ?_, ?_⟩
  · rw [g5222, g5221, g5220, g5219, g5218, g5217, tb_word_gen, v5817]; ring
  · rw [g5225, g5224, tb_word_gen, v5817]; ring
  · rw [g5255, g5254, tb_word_gen, v5817]; ring
  · change [σ (.n 5927), σ (.n 5928), σ (.n 5929), σ (.n 5930), σ (.n 5931)] =
      (zcRec cap0 cl0 xs n).1
    apply List.ext_getElem (by simp [hlen])
    intro k h1 h2
    simp only [List.length_cons, List.length_nil] at h1
    interval_cases k
    · rw [List.getElem_cons_zero, e0, List.getElem_append_left]
    · rw [List.getElem_cons_succ, List.getElem_cons_zero, e1, List.getElem_append_left]
    · rw [List.getElem_cons_succ, List.getElem_cons_succ, List.getElem_cons_zero, e2,
        List.getElem_append_left]
    · rw [List.getElem_cons_succ, List.getElem_cons_succ, List.getElem_cons_succ,
        List.getElem_cons_zero, e3, List.getElem_append_left]
    · rw [List.getElem_cons_succ, List.getElem_cons_succ, List.getElem_cons_succ,
        List.getElem_cons_succ, List.getElem_cons_zero, e4, List.getElem_append_left]
  · rw [e5, List.getElem_append_right (by omega)]; simp [hlen]
  · change σ (.n 5933) = (zcRec cap0 cl0 xs n).2
    rw [e6, List.getElem_append_right (by omega)]; simp [hlen]

end
end LeanVM.Guest.B1.Tables
