/-
  LeanVM.Guest.B1.Tables.VtC.ZBase

  The table sumcheck's honest rounds (from the transcript words, the capacity and the target), the
  buffers they fill, and `verify_tables`' statements `2571 ..< 2672` and `6251 ..< 6294`.
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

/-- `verify_tables`' statements `2571 ..< 2672` (G:2373-2423). -/
noncomputable def zBlk : List Stmt := [
    .atom (.hint (.witness "zc_tau_max" (.stack [.n 2500]))),
    .atom (.const (.n 2501) (word 4294967296 0 0)),
    .atom (.mul (.n 2500) (.n 2502) (.n 30)),
    .atom (.rangeCheck (.n 2502) (.n 2503) (.n 2504) (.n 2505) (.n 2501)),
    .atom (.add (.n 2506) (.n 2500) (.n 30)),
    .atom (.const (.n 2507) (word 4294967296 0 0)),
    .atom (.mul (.n 2500) (.n 2508) (.n 31)),
    .atom (.rangeCheck (.n 2508) (.n 2509) (.n 2510) (.n 2511) (.n 2507)),
    .atom (.add (.n 2512) (.n 2500) (.n 31)),
    .atom (.mul (.n 2513) (.n 2506) (.n 2512)),
    .atom (.const (.n 2514) (word 4294967296 0 0)),
    .atom (.mul (.n 2500) (.n 2515) (.n 32)),
    .atom (.rangeCheck (.n 2515) (.n 2516) (.n 2517) (.n 2518) (.n 2514)),
    .atom (.add (.n 2519) (.n 2500) (.n 32)),
    .atom (.mul (.n 2520) (.n 2513) (.n 2519)),
    .atom (.const (.n 2521) (word 4294967296 0 0)),
    .atom (.mul (.n 2500) (.n 2522) (.n 33)),
    .atom (.rangeCheck (.n 2522) (.n 2523) (.n 2524) (.n 2525) (.n 2521)),
    .atom (.add (.n 2526) (.n 2500) (.n 33)),
    .atom (.mul (.n 2527) (.n 2520) (.n 2526)),
    .atom (.const (.n 2528) (word 4294967296 0 0)),
    .atom (.mul (.n 2500) (.n 2529) (.n 34)),
    .atom (.rangeCheck (.n 2529) (.n 2530) (.n 2531) (.n 2532) (.n 2528)),
    .atom (.add (.n 2533) (.n 2500) (.n 34)),
    .atom (.mul (.n 2534) (.n 2527) (.n 2533)),
    .atom (.const (.n 2535) (word 4294967296 0 0)),
    .atom (.mul (.n 2500) (.n 2536) (.n 35)),
    .atom (.rangeCheck (.n 2536) (.n 2537) (.n 2538) (.n 2539) (.n 2535)),
    .atom (.add (.n 2540) (.n 2500) (.n 35)),
    .atom (.mul (.n 2541) (.n 2534) (.n 2540)),
    .atom (.const (.n 2542) (word 0 0 0)),
    .atom (.assertEq (.n 2541) (.n 2542)),
    .atom (.const (.n 2543) (word 4294967296 0 0)),
    .atom (.mul (.n 9) (.n 2544) (.n 2500)),
    .atom (.rangeCheck (.n 2544) (.n 2545) (.n 2546) (.n 2547) (.n 2543)),
    .atom (.const (.n 2548) (word 1 0 0)),
    .atom (.const (.n 2549) (word 0 0 0)),
    .atom (.const (.n 2550) (word 0 0 0)),
    .atom (.const (.n 2551) (word 0 0 0)),
    .atom (.const (.n 2552) (word 0 0 0)),
    .atom (.keccak [.n 1897, .n 1899, .n 2549, .n 2549, .n 2549, .n 2550, .n 2551, .n 2552, .n 1885, .n 1886, .n 1887, .n 1888, .n 1889] [.n 2553, .n 2554, .n 2555, .n 2556, .n 2557, .n 2558, .n 2559, .n 2560, .n 2561, .n 2562, .n 2563, .n 2564, .n 2565] false false),
    .atom (.hint (.limbs (.n 2554) [.n 2566])),
    .atom (.add (.n 2567) (.n 2554) (.n 2566)),
    .atom (.const (.n 2568) (word 1 0 1)),
    .atom (.mul (.n 2569) (.n 2567) (.n 2568)),
    .atom (.assertInK (.n 2566) (.n 2569)),
    .atom (.const (.n 2570) (word 0 0 1)),
    .atom (.mul (.n 2571) (.n 2570) (.n 2566)),
    .atom (.add (.n 2572) (.n 2553) (.n 2571)),
    .atom (.const (.n 2573) (word 1 0 0)),
    .atom (.mul (.n 2574) (.n 2573) (.n 2572)),
    .atom (.mul (.n 2575) (.n 2574) (.n 2572)),
    .atom (.mul (.n 2576) (.n 2575) (.n 2572)),
    .atom (.mul (.n 2577) (.n 2576) (.n 2572)),
    .atom (.mul (.n 2578) (.n 2575) (.n 1812)),
    .atom (.mul (.n 2579) (.n 2576) (.n 2057)),
    .atom (.add (.n 2580) (.n 2578) (.n 2579)),
    .atom (.mul (.n 2581) (.n 2577) (.n 2499)),
    .atom (.add (.n 2582) (.n 2580) (.n 2581)),
    .atom (.const (.n 2583) (word 2 0 0)),
    .atom (.mul (.n 2584) (.n 2500) (.n 2583)),
    .atom (.mul (.n 2585) (.n 2584) (.n 2584)),
    .atom (.mul (.n 2586) (.n 2585) (.n 2584)),
    .atom (.mul (.n 2587) (.n 2586) (.n 2586)),
    .atom (.mul (.n 2588) (.n 2587) (.n 2584)),
    .atom (.hint (.allocDyn (.n 2589) (.n 2588))),
    .atom (.const (.n 2590) (word 2 0 0)),
    .atom (.mul (.n 2591) (.n 2500) (.n 2590)),
    .atom (.hint (.allocDyn (.n 2592) (.n 2591))),
    .atom (.load (.n 2561) (.n 2589) 0),
    .atom (.load (.n 2562) (.n 2589) 1),
    .atom (.load (.n 2563) (.n 2589) 2),
    .atom (.load (.n 2564) (.n 2589) 3),
    .atom (.load (.n 2565) (.n 2589) 4),
    .atom (.const (.n 2593) (word 32 0 0)),
    .atom (.mul (.n 2594) (.n 5) (.n 2593)),
    .atom (.load (.n 2594) (.n 2589) 5),
    .atom (.load (.n 2582) (.n 2589) 6),
    .atom (.const (.n 2595) (word 1 0 0)),
    .atom (.load (.n 2595) (.n 2592) 0),
    .atom (.const (.n 2596) (word 1 0 0)),
    .atom (.add (.n 2597) (.n 2596) (.n 2500)),
    .atom (.const (.n 2598) (word 1 0 0)),
    .callIf (.n 2597) "__loop9" [.n 2598, .n 2500, .n 2589, .n 16, .n 2500, .n 2592],
    .atom (.mul (.n 2599) (.n 2500) (.n 2500)),
    .atom (.mul (.n 2600) (.n 2599) (.n 2500)),
    .atom (.mul (.n 2601) (.n 2600) (.n 2600)),
    .atom (.mul (.n 2602) (.n 2601) (.n 2500)),
    .atom (.mul (.n 2603) (.n 2589) (.n 2602)),
    .atom (.load (.n 2604) (.n 2603) 0),
    .atom (.load (.n 2605) (.n 2603) 1),
    .atom (.load (.n 2606) (.n 2603) 2),
    .atom (.load (.n 2607) (.n 2603) 3),
    .atom (.load (.n 2608) (.n 2603) 4),
    .atom (.load (.n 2609) (.n 2603) 5),
    .atom (.load (.n 2610) (.n 2603) 6),
    .atom (.const (.n 2611) (word 2 0 0)),
    .atom (.mul (.n 2612) (.n 2500) (.n 2611)),
    .atom (.hint (.allocDyn (.n 2613) (.n 2612))),
    .atom (.const (.n 2614) (word 1 0 0)),
    .call "eq_prefix_chain" [.n 2613, .n 2614, .n 16, .n 703, .n 2500] []]

/-- `verify_tables`' statements `6251 ..< 6294` (G:2526-2539). -/
noncomputable def zTail : List Stmt := [
    .atom (.keccak [.n 5696, .n 5698, .n 2549, .n 2549, .n 2549, .n 2550, .n 2551, .n 2552, .n 5684, .n 5685, .n 5686, .n 5687, .n 5688] [.n 6818, .n 6819, .n 6820, .n 6821, .n 6822, .n 6823, .n 6824, .n 6825, .n 6826, .n 6827, .n 6828, .n 6829, .n 6830] false false),
    .atom (.hint (.limbs (.n 6819) [.n 6831])),
    .atom (.add (.n 6832) (.n 6819) (.n 6831)),
    .atom (.const (.n 6833) (word 1 0 1)),
    .atom (.mul (.n 6834) (.n 6832) (.n 6833)),
    .atom (.assertInK (.n 6831) (.n 6834)),
    .atom (.const (.n 6835) (word 0 0 1)),
    .atom (.mul (.n 6836) (.n 6835) (.n 6831)),
    .atom (.add (.n 6837) (.n 6818) (.n 6836)),
    .atom (.hint (.limbs (.n 6) [.n 6838])),
    .atom (.add (.n 6839) (.n 6) (.n 6838)),
    .atom (.const (.n 6840) (word 1 0 1)),
    .atom (.mul (.n 6841) (.n 6839) (.n 6840)),
    .atom (.assertInK (.n 6838) (.n 6841)),
    .atom (.copy (.n 6842) (.n 6838)),
    .atom (.hint (.limbs (.n 7) [.n 6843])),
    .atom (.add (.n 6844) (.n 7) (.n 6843)),
    .atom (.const (.n 6845) (word 1 0 1)),
    .atom (.mul (.n 6846) (.n 6844) (.n 6845)),
    .atom (.assertInK (.n 6843) (.n 6846)),
    .atom (.copy (.n 6847) (.n 6843)),
    .atom (.add (.n 6848) (.n 6842) (.n 6847)),
    .atom (.mul (.n 6849) (.n 6837) (.n 6848)),
    .atom (.add (.n 6850) (.n 6842) (.n 6849)),
    .atom (.load (.n 6850) (.n 15) 162),
    .atom (.add (.n 6851) (.n 6841) (.n 6846)),
    .atom (.mul (.n 6852) (.n 6837) (.n 6851)),
    .atom (.add (.n 6853) (.n 6841) (.n 6852)),
    .atom (.load (.n 6853) (.n 15) 163),
    .atom (.const (.n 6854) (word 0 0 0)),
    .atom (.load (.n 6854) (.n 15) 164),
    .atom (.copy (.n 6855) (.n 6826)),
    .atom (.copy (.n 6856) (.n 6827)),
    .atom (.copy (.n 6857) (.n 6828)),
    .atom (.copy (.n 6858) (.n 6829)),
    .atom (.copy (.n 6859) (.n 6830)),
    .atom (.const (.n 6860) (word 174483046400 0 0)),
    .atom (.mul (.n 6861) (.n 2609) (.n 6860)),
    .atom (.copy (.n 6862) (.n 6861)),
    .atom (.copy (.n 6863) (.n 2500)),
    .atom (.copy (.n 6864) (.n 581)),
    .atom (.copy (.n 6865) (.n 6837)),
    .atom (.copy (.n 6866) (.n 2609))]

theorem zBlk_at : tbStmtsEqb zBlk ((vtPre.drop 2571).take zBlk.length) = true := by
  simp only [vtPre_drop]; decide +kernel

theorem zTail_at : tbStmtsEqb zTail ((vtPre.drop 6251).take zTail.length) = true := by
  simp only [vtPre_drop]; decide +kernel

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
