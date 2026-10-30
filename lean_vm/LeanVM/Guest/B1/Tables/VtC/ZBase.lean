/-
  LeanVM.Guest.B1.Tables.VtC.ZBase

  The table sumcheck's honest rounds (from the transcript words, the capacity and the target), the
  buffers they fill, and `verify_tables`' statements `5152 ..< 5259` and `10209 ..< 10251`.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.Hon
public import LeanVM.Guest.B1.Tables.VtC.ZLoop10
public import LeanVM.Guest.B1.Tables.Vt.ZcRun
public import LeanVM.Guest.B1.Tables.Vt.Pi

/-!
# The table sumcheck, honestly

`zcRec cap0 cl0 xs j`: the capacity and the claim before round `j` of the plain degree-4
sumcheck from the capacity `cap0` and the claim `cl0`, round `j` reading the words
`xs[3j], xs[3j+1], xs[3j+2]` (`c0, c2, c3`); `zcCh`: round `j`'s challenge. The buffers:
`zcRoundsW` (record `j ≤ n`: the capacity, the cursor `cur0·g^(3j)`, the claim), `zcCprodW`
(the challenges' running products), `zcChis` (the challenges, last first, as `chi` holds them).

`zc_run`: the rounds are the specification's `sumcheck cl0 4 (replicate n none)`.
`zc_l10B`: on a memory holding the buffers and the words, every iteration of `__loop9` has
its facts.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## The statements -/

/-- `verify_tables`' statements `5152 ..< 5259` (G:2183-2228). -/
noncomputable def zBlk : List Stmt := [
    .atom (.hint (.witness "zc_tau_max" (.stack [.n 5817]))),
    .atom (.load (.n 5818) (.n 10) 1),
    .atom (.const (.n 5819) (word 4294967296 0 0)),
    .atom (.mul (.n 5817) (.n 5820) (.n 5818)),
    .atom (.rangeCheck (.n 5820) (.n 5821) (.n 5822) (.n 5823) (.n 5819)),
    .atom (.add (.n 5824) (.n 5817) (.n 5818)),
    .atom (.load (.n 5825) (.n 10) 2),
    .atom (.const (.n 5826) (word 4294967296 0 0)),
    .atom (.mul (.n 5817) (.n 5827) (.n 5825)),
    .atom (.rangeCheck (.n 5827) (.n 5828) (.n 5829) (.n 5830) (.n 5826)),
    .atom (.add (.n 5831) (.n 5817) (.n 5825)),
    .atom (.mul (.n 5832) (.n 5824) (.n 5831)),
    .atom (.load (.n 5833) (.n 10) 3),
    .atom (.const (.n 5834) (word 4294967296 0 0)),
    .atom (.mul (.n 5817) (.n 5835) (.n 5833)),
    .atom (.rangeCheck (.n 5835) (.n 5836) (.n 5837) (.n 5838) (.n 5834)),
    .atom (.add (.n 5839) (.n 5817) (.n 5833)),
    .atom (.mul (.n 5840) (.n 5832) (.n 5839)),
    .atom (.load (.n 5841) (.n 10) 4),
    .atom (.const (.n 5842) (word 4294967296 0 0)),
    .atom (.mul (.n 5817) (.n 5843) (.n 5841)),
    .atom (.rangeCheck (.n 5843) (.n 5844) (.n 5845) (.n 5846) (.n 5842)),
    .atom (.add (.n 5847) (.n 5817) (.n 5841)),
    .atom (.mul (.n 5848) (.n 5840) (.n 5847)),
    .atom (.load (.n 5849) (.n 10) 5),
    .atom (.const (.n 5850) (word 4294967296 0 0)),
    .atom (.mul (.n 5817) (.n 5851) (.n 5849)),
    .atom (.rangeCheck (.n 5851) (.n 5852) (.n 5853) (.n 5854) (.n 5850)),
    .atom (.add (.n 5855) (.n 5817) (.n 5849)),
    .atom (.mul (.n 5856) (.n 5848) (.n 5855)),
    .atom (.load (.n 5857) (.n 10) 6),
    .atom (.const (.n 5858) (word 4294967296 0 0)),
    .atom (.mul (.n 5817) (.n 5859) (.n 5857)),
    .atom (.rangeCheck (.n 5859) (.n 5860) (.n 5861) (.n 5862) (.n 5858)),
    .atom (.add (.n 5863) (.n 5817) (.n 5857)),
    .atom (.mul (.n 5864) (.n 5856) (.n 5863)),
    .atom (.const (.n 5865) (word 0 0 0)),
    .atom (.assertEq (.n 5864) (.n 5865)),
    .atom (.const (.n 5866) (word 4294967296 0 0)),
    .atom (.mul (.n 9) (.n 5867) (.n 5817)),
    .atom (.rangeCheck (.n 5867) (.n 5868) (.n 5869) (.n 5870) (.n 5866)),
    .atom (.const (.n 5871) (word 1 0 0)),
    .atom (.const (.n 5872) (word 0 0 0)),
    .atom (.const (.n 5873) (word 0 0 0)),
    .atom (.const (.n 5874) (word 0 0 0)),
    .atom (.const (.n 5875) (word 0 0 0)),
    .atom (.keccak [.n 4509, .n 4511, .n 5872, .n 5872, .n 5872, .n 5873, .n 5874, .n 5875, .n 4497, .n 4498, .n 4499, .n 4500, .n 4501] [.n 5876, .n 5877, .n 5878, .n 5879, .n 5880, .n 5881, .n 5882, .n 5883, .n 5884, .n 5885, .n 5886, .n 5887, .n 5888] false false),
    .atom (.hint (.limbs (.n 5877) [.n 5889])),
    .atom (.add (.n 5890) (.n 5877) (.n 5889)),
    .atom (.const (.n 5891) (word 1 0 1)),
    .atom (.mul (.n 5892) (.n 5890) (.n 5891)),
    .atom (.assertInK (.n 5889) (.n 5892)),
    .atom (.const (.n 5893) (word 0 0 1)),
    .atom (.mul (.n 5894) (.n 5893) (.n 5889)),
    .atom (.add (.n 5895) (.n 5876) (.n 5894)),
    .atom (.const (.n 5896) (word 1 0 0)),
    .atom (.mul (.n 5897) (.n 5896) (.n 5895)),
    .atom (.mul (.n 5898) (.n 5897) (.n 5895)),
    .atom (.mul (.n 5899) (.n 5898) (.n 5895)),
    .atom (.mul (.n 5900) (.n 5899) (.n 5895)),
    .atom (.mul (.n 5901) (.n 5898) (.n 4411)),
    .atom (.mul (.n 5902) (.n 5899) (.n 4924)),
    .atom (.add (.n 5903) (.n 5901) (.n 5902)),
    .atom (.mul (.n 5904) (.n 5900) (.n 5816)),
    .atom (.add (.n 5905) (.n 5903) (.n 5904)),
    .atom (.const (.n 5906) (word 2 0 0)),
    .atom (.mul (.n 5907) (.n 5817) (.n 5906)),
    .atom (.mul (.n 5908) (.n 5907) (.n 5907)),
    .atom (.mul (.n 5909) (.n 5908) (.n 5907)),
    .atom (.mul (.n 5910) (.n 5909) (.n 5909)),
    .atom (.mul (.n 5911) (.n 5910) (.n 5907)),
    .atom (.hint (.allocDyn (.n 5912) (.n 5911))),
    .atom (.const (.n 5913) (word 2 0 0)),
    .atom (.mul (.n 5914) (.n 5817) (.n 5913)),
    .atom (.hint (.allocDyn (.n 5915) (.n 5914))),
    .atom (.load (.n 5884) (.n 5912) 0),
    .atom (.load (.n 5885) (.n 5912) 1),
    .atom (.load (.n 5886) (.n 5912) 2),
    .atom (.load (.n 5887) (.n 5912) 3),
    .atom (.load (.n 5888) (.n 5912) 4),
    .atom (.const (.n 5916) (word 32 0 0)),
    .atom (.mul (.n 5917) (.n 5) (.n 5916)),
    .atom (.load (.n 5917) (.n 5912) 5),
    .atom (.load (.n 5905) (.n 5912) 6),
    .atom (.const (.n 5918) (word 1 0 0)),
    .atom (.load (.n 5918) (.n 5915) 0),
    .atom (.const (.n 5919) (word 1 0 0)),
    .atom (.add (.n 5920) (.n 5919) (.n 5817)),
    .atom (.const (.n 5921) (word 1 0 0)),
    .callIf (.n 5920) "__loop9" [.n 5921, .n 5817, .n 5912, .n 18, .n 5817, .n 5915],
    .atom (.mul (.n 5922) (.n 5817) (.n 5817)),
    .atom (.mul (.n 5923) (.n 5922) (.n 5817)),
    .atom (.mul (.n 5924) (.n 5923) (.n 5923)),
    .atom (.mul (.n 5925) (.n 5924) (.n 5817)),
    .atom (.mul (.n 5926) (.n 5912) (.n 5925)),
    .atom (.load (.n 5927) (.n 5926) 0),
    .atom (.load (.n 5928) (.n 5926) 1),
    .atom (.load (.n 5929) (.n 5926) 2),
    .atom (.load (.n 5930) (.n 5926) 3),
    .atom (.load (.n 5931) (.n 5926) 4),
    .atom (.load (.n 5932) (.n 5926) 5),
    .atom (.load (.n 5933) (.n 5926) 6),
    .atom (.const (.n 5934) (word 2 0 0)),
    .atom (.mul (.n 5935) (.n 5817) (.n 5934)),
    .atom (.hint (.allocDyn (.n 5936) (.n 5935))),
    .atom (.const (.n 5937) (word 1 0 0)),
    .call "eq_prefix_chain" [.n 5936, .n 5937, .n 18, .n 2767, .n 5817] []]

/-- `verify_tables`' statements `10209 ..< 10251` (G:2299-2312). -/
noncomputable def zTail : List Stmt := [
    .atom (.keccak [.n 9416, .n 9418, .n 5872, .n 5872, .n 5872, .n 5873, .n 5874, .n 5875, .n 9404, .n 9405, .n 9406, .n 9407, .n 9408] [.n 11198, .n 11199, .n 11200, .n 11201, .n 11202, .n 11203, .n 11204, .n 11205, .n 11206, .n 11207, .n 11208, .n 11209, .n 11210] false false),
    .atom (.hint (.limbs (.n 11199) [.n 11211])),
    .atom (.add (.n 11212) (.n 11199) (.n 11211)),
    .atom (.const (.n 11213) (word 1 0 1)),
    .atom (.mul (.n 11214) (.n 11212) (.n 11213)),
    .atom (.assertInK (.n 11211) (.n 11214)),
    .atom (.const (.n 11215) (word 0 0 1)),
    .atom (.mul (.n 11216) (.n 11215) (.n 11211)),
    .atom (.add (.n 11217) (.n 11198) (.n 11216)),
    .atom (.hint (.limbs (.n 6) [.n 11218])),
    .atom (.add (.n 11219) (.n 6) (.n 11218)),
    .atom (.const (.n 11220) (word 1 0 1)),
    .atom (.mul (.n 11221) (.n 11219) (.n 11220)),
    .atom (.assertInK (.n 11218) (.n 11221)),
    .atom (.copy (.n 11222) (.n 11218)),
    .atom (.hint (.limbs (.n 7) [.n 11223])),
    .atom (.add (.n 11224) (.n 7) (.n 11223)),
    .atom (.const (.n 11225) (word 1 0 1)),
    .atom (.mul (.n 11226) (.n 11224) (.n 11225)),
    .atom (.assertInK (.n 11223) (.n 11226)),
    .atom (.copy (.n 11227) (.n 11223)),
    .atom (.add (.n 11228) (.n 11222) (.n 11227)),
    .atom (.mul (.n 11229) (.n 11217) (.n 11228)),
    .atom (.add (.n 11230) (.n 11222) (.n 11229)),
    .atom (.load (.n 11230) (.n 16) 162),
    .atom (.add (.n 11231) (.n 11221) (.n 11226)),
    .atom (.mul (.n 11232) (.n 11217) (.n 11231)),
    .atom (.add (.n 11233) (.n 11221) (.n 11232)),
    .atom (.load (.n 11233) (.n 16) 163),
    .atom (.const (.n 11234) (word 0 0 0)),
    .atom (.load (.n 11234) (.n 16) 164),
    .atom (.copy (.n 11235) (.n 11206)),
    .atom (.copy (.n 11236) (.n 11207)),
    .atom (.copy (.n 11237) (.n 11208)),
    .atom (.copy (.n 11238) (.n 11209)),
    .atom (.copy (.n 11239) (.n 11210)),
    .atom (.const (.n 11240) (word 174483046400 0 0)),
    .atom (.mul (.n 11241) (.n 5932) (.n 11240)),
    .atom (.copy (.n 11242) (.n 11241)),
    .atom (.copy (.n 11243) (.n 5817)),
    .atom (.copy (.n 11244) (.n 2639)),
    .atom (.copy (.n 11245) (.n 11217))]

theorem zBlk_at : tbStmtsEqb zBlk ((vtPre.drop 5152).take zBlk.length) = true := by decide +kernel

theorem zTail_at : tbStmtsEqb zTail ((vtPre.drop 10209).take zTail.length) = true := by
  decide +kernel

/-! ## The honest rounds -/

/-- The capacity and the claim before round `j`. -/
def zcRec (cap0 : List E) (cl0 : E) (xs : List E) : ℕ → List E × E
  | 0 => (cap0, cl0)
  | j + 1 =>
    let r := zcRec cap0 cl0 xs j
    let c0 := xs.getD (3 * j) 0
    let c2 := xs.getD (3 * j + 1) 0
    let c3 := xs.getD (3 * j + 2) 0
    let s := ((⟨r.1, []⟩ : Fs).absorbAll [c0, c2, c3] dsObserve).squeeze
    (s.2.cap, polyEval [c0, r.2 + sumE [c2, c3], c2, c3] s.1)

/-- Round `j`'s challenge. -/
def zcCh (cap0 : List E) (cl0 : E) (xs : List E) (j : ℕ) : E :=
  ((⟨(zcRec cap0 cl0 xs j).1, []⟩ : Fs).absorbAll
    [xs.getD (3 * j) 0, xs.getD (3 * j + 1) 0, xs.getD (3 * j + 2) 0] dsObserve).squeeze.1

/-- Record `j`: the capacity, the cursor, the claim. -/
def zcRecW (cap0 : List E) (cl0 cur0 : E) (xs : List E) (j : ℕ) : List E :=
  (zcRec cap0 cl0 xs j).1 ++ [cur0 * gen ^ (3 * j), (zcRec cap0 cl0 xs j).2]

/-- The records `0 ..= n` (`zc_rounds`). -/
def zcRoundsW (cap0 : List E) (cl0 cur0 : E) (xs : List E) (n : ℕ) : List E :=
  (List.range (n + 1)).flatMap (zcRecW cap0 cl0 cur0 xs)

/-- The challenges' running products (`zc_cprod`). -/
def zcCprodW (cap0 : List E) (cl0 : E) (xs : List E) (n : ℕ) : List E :=
  (List.range (n + 1)).map fun j ↦ ((List.range j).map (zcCh cap0 cl0 xs)).prod

/-- The challenges, last first (`chi`). -/
def zcChis (cap0 : List E) (cl0 : E) (xs : List E) (n : ℕ) : List E :=
  ((List.range n).map (zcCh cap0 cl0 xs)).reverse

theorem zcRec_len {cap0 : List E} {cl0 : E} {xs : List E} (h : cap0.length = 5) :
    ∀ j, (zcRec cap0 cl0 xs j).1.length = 5
  | 0 => h
  | _ + 1 => rfl

theorem zcRec_canon {cap0 : List E} {cl0 : E} {xs : List E} (h : AllCanonical cap0) :
    ∀ j, AllCanonical (zcRec cap0 cl0 xs j).1
  | 0 => h
  | _ + 1 => tb_capOf_canonical _

theorem zcRecW_len {cap0 : List E} {cl0 cur0 : E} {xs : List E} (h : cap0.length = 5) (j : ℕ) :
    (zcRecW cap0 cl0 cur0 xs j).length = 7 := by
  simp [zcRecW, zcRec_len h]

theorem zcRoundsW_len {cap0 : List E} {cl0 cur0 : E} {xs : List E} (h : cap0.length = 5) :
    ∀ n, (zcRoundsW cap0 cl0 cur0 xs n).length = 7 * (n + 1)
  | 0 => by simp [zcRoundsW, zcRecW_len h]
  | n + 1 => by
    rw [zcRoundsW, List.range_succ, List.flatMap_append, List.length_append, ← zcRoundsW,
      zcRoundsW_len h n]
    simp [zcRecW_len h]; ring

/-- **The records**, one by one. -/
theorem zcRoundsW_reads {rd : Reader} {R : E} {cap0 : List E} {cl0 cur0 : E} {xs : List E}
    (h : cap0.length = 5) {n : ℕ} (hR : TbReadsAt rd R (zcRoundsW cap0 cl0 cur0 xs n)) :
    ∀ j ≤ n, TbReadsAt rd (R * gen ^ (7 * j)) (zcRecW cap0 cl0 cur0 xs j) := by
  induction n with
  | zero =>
    intro j hj
    obtain rfl : j = 0 := by omega
    simpa [zcRoundsW] using hR
  | succ n ih =>
    rw [zcRoundsW, List.range_succ, List.flatMap_append, ← zcRoundsW, tbReadsAt_append,
      zcRoundsW_len h] at hR
    intro j hj
    rcases Nat.lt_or_ge j (n + 1) with hj' | hj'
    · exact ih hR.1 j (by omega)
    · obtain rfl : j = n + 1 := by omega
      simpa using hR.2

/-- A record's parts. -/
theorem zc_rec_parts {rd : Reader} {p : E} {cap : List E} {a b : E} (h5 : cap.length = 5)
    (h : TbReadsAt rd p (cap ++ [a, b])) :
    CapAt rd p 0 1 cap ∧ LoadHolds rd p 5 a ∧ LoadHolds rd p 6 b := by
  rw [tbReadsAt_append, h5, tbReadsAt_cons, tbReadsAt_singleton, tb_loadHolds_mul_gen_pow,
    mul_assoc, ← pow_succ, tb_loadHolds_mul_gen_pow] at h
  refine ⟨⟨h5, fun j hj => ?_⟩, h.2.1, h.2.2⟩
  simpa using h.1 j hj

/-- **Every iteration of `__loop9` has its facts** on the honest buffers and words. -/
theorem zc_l10B {rd : Reader} {R chi C : E} {cap0 : List E} {cl0 cur0 : E} {xs : List E} {n : ℕ}
    (h5 : cap0.length = 5) (hc : AllCanonical cap0)
    (hR : TbReadsAt rd R (zcRoundsW cap0 cl0 cur0 xs n))
    (hC : TbReadsAt rd C (zcCprodW cap0 cl0 xs n)) (hchi : TbReadsAt rd chi (zcChis cap0 cl0 xs n))
    (hxs : TbReadsAt rd cur0 xs) (hxl : xs.length = 3 * n) :
    ∀ j < n, L10B rd R chi (gen ^ n) C (gen ^ j) := by
  intro j hj
  have e7 : R * (gen ^ j) ^ 7 = R * gen ^ (7 * j) := by rw [← pow_mul, mul_comm j 7]
  obtain ⟨hc0, hcur, hcl⟩ := zc_rec_parts (zcRec_len h5 j) (zcRoundsW_reads h5 hR j (by omega))
  obtain ⟨hc1, hcur1, hcl1⟩ := zc_rec_parts (zcRec_len h5 (j + 1))
    (zcRoundsW_reads h5 hR (j + 1) (by omega))
  have e71 : R * gen ^ (7 * (j + 1)) = R * gen ^ (7 * j) * gen ^ 7 := by ring
  rw [e71] at hc1 hcur1 hcl1
  rw [tb_loadHolds_mul_gen_pow] at hcur1 hcl1
  have hrd : ReadsAt rd (cur0 * gen ^ (3 * j))
      [xs.getD (3 * j) 0, xs.getD (3 * j + 1) 0, xs.getD (3 * j + 2) 0] := by
    intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    rw [tb_loadHolds_mul_gen_pow]
    have hk' := hxs (3 * j + k) (by omega)
    interval_cases k
    · show LoadHolds rd cur0 (3 * j + 0) (xs.getD (3 * j) 0)
      rw [List.getD_eq_getElem _ _ (by omega)]; exact hk'
    · show LoadHolds rd cur0 (3 * j + 1) (xs.getD (3 * j + 1) 0)
      rw [List.getD_eq_getElem _ _ (by omega)]; exact hk'
    · show LoadHolds rd cur0 (3 * j + 2) (xs.getD (3 * j + 2) 0)
      rw [List.getD_eq_getElem _ _ (by omega)]; exact hk'
  refine ⟨cur0 * gen ^ (3 * j), (zcRec cap0 cl0 xs j).2, cur0 * gen ^ (3 * j) * gen ^ 3,
    (zcRec cap0 cl0 xs (j + 1)).2, zcCh cap0 cl0 xs j, by rw [e7]; exact hcur, by rw [e7]; exact hcl,
    ?_, ?_, by rw [e7]; exact hcl1, ⟨gen ^ (n - 1 - j), ?_, ?_⟩, ((List.range j).map (zcCh cap0 cl0 xs)).prod, ?_, ?_⟩
  · rw [e7]
    refine (sumcheck_round4_holds rd _ _).mpr ⟨(zcRec cap0 cl0 xs j).1, _, _, _, hc0,
      zcRec_canon hc j, hrd, hc1, rfl⟩
  · rw [e7, show cur0 * gen ^ (3 * j) * gen ^ 3 = cur0 * gen ^ (3 * (j + 1)) by ring]
    exact hcur1
  · have hw := vtWInvGen_mul
    calc gen ^ n * vtWInvGen = gen ^ (n - 1 - j) * gen ^ j * (vtWInvGen * gen) := by
          rw [← pow_add, show n - 1 - j + j = n - 1 by omega, mul_comm vtWInvGen gen, ← mul_assoc,
            ← pow_succ, show n - 1 + 1 = n by omega]
      _ = gen ^ (n - 1 - j) * gen ^ j := by rw [hw, mul_one]
  · rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]
    have := hchi (n - 1 - j) (by simp [zcChis]; omega)
    simp only [zcChis, List.getElem_reverse, List.getElem_map, List.getElem_range,
      List.length_map, List.length_range] at this
    rwa [show n - 1 - (n - 1 - j) = j by omega] at this
  · rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]
    have := hC j (by simp [zcCprodW]; omega)
    simpa [zcCprodW] using this
  · rw [tb_loadHolds_mul_gen_pow]
    have := hC (j + 1) (by simp [zcCprodW]; omega)
    simp only [zcCprodW, List.getElem_map, List.getElem_range] at this
    rwa [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton] at this

theorem zc_slice {xs : List E} {j k : ℕ} (h : 3 * (j + k + 1) ≤ xs.length) :
    (xs.drop (3 * j)).take (3 * (k + 1)) =
      [xs.getD (3 * j) 0, xs.getD (3 * j + 1) 0, xs.getD (3 * j + 2) 0] ++
        (xs.drop (3 * (j + 1))).take (3 * k) := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_drop]
    rcases Nat.lt_or_ge i 3 with hi | hi
    · rw [List.getElem_append_left (by simpa using hi)]
      interval_cases i <;> simp <;> rw [List.getElem?_eq_getElem (by omega)] <;> rfl
    · rw [List.getElem_append_right (by simpa using hi)]
      simp only [List.length_cons, List.length_nil, List.getElem_take, List.getElem_drop]
      congr 1; omega

/-- **The honest rounds are the specification's sumcheck.** -/
theorem zc_run (cap0 : List E) (cl0 : E) {xs : List E} {n : ℕ} (hxl : xs.length = 3 * n) :
    RunsTo (sumcheck cl0 4 (List.replicate n none)) ⟨cap0, []⟩ xs
      ((List.range n).map (zcCh cap0 cl0 xs), (zcRec cap0 cl0 xs n).2)
      ⟨(zcRec cap0 cl0 xs n).1, []⟩ := by
  have key : ∀ k j, j + k = n → RunsTo (sumcheck (zcRec cap0 cl0 xs j).2 4 (List.replicate k none))
      ⟨(zcRec cap0 cl0 xs j).1, []⟩ ((xs.drop (3 * j)).take (3 * k))
      ((List.range k).map (fun i ↦ zcCh cap0 cl0 xs (j + i)), (zcRec cap0 cl0 xs n).2)
      ⟨(zcRec cap0 cl0 xs n).1, []⟩ := by
    intro k
    induction k with
    | zero =>
      intro j hj
      obtain rfl : j = n := by omega
      exact runsTo_sumcheck_nil _ _ _
    | succ k ih =>
      intro j hj
      have h1 := runsTo_roundPolyNone ⟨(zcRec cap0 cl0 xs j).1, []⟩ (zcRec cap0 cl0 xs j).2
        (xs.getD (3 * j) 0) [xs.getD (3 * j + 1) 0, xs.getD (3 * j + 2) 0] 4 rfl
      have h2 := ih (j + 1) (by omega)
      have e : ((⟨(zcRec cap0 cl0 xs j).1, []⟩ : Fs).absorb (xs.getD (3 * j) 0) dsObserve).absorbAll
          [xs.getD (3 * j + 1) 0, xs.getD (3 * j + 2) 0] dsObserve =
          (⟨(zcRec cap0 cl0 xs j).1, []⟩ : Fs).absorbAll
            [xs.getD (3 * j) 0, xs.getD (3 * j + 1) 0, xs.getD (3 * j + 2) 0] dsObserve := rfl
      rw [e] at h1
      have h := runsTo_sumcheck_cons h1 h2
      rw [List.replicate_succ, zc_slice (by omega), List.range_succ_eq_map, List.map_cons,
        List.map_map]
      refine h.of_eq rfl rfl ?_ rfl
      rw [Nat.add_zero]
      refine Prod.ext (congrArg₂ List.cons rfl (List.map_congr_left fun i _ => ?_)) rfl
      simp only [Function.comp_apply]
      rw [show j + 1 + i = j + (i + 1) by omega]
  have := key n 0 (by omega)
  simp only [Nat.mul_zero, List.drop_zero, Nat.zero_add] at this
  rw [← hxl, List.take_length] at this
  exact this

end
end LeanVM.Guest.B1.Tables
