/-
  LeanVM.Guest.B1.Comp.Tables.FlockSegsC1

  `verify_flock`'s first segments over a completeness model: the prelude, round 1, the skip
  challenge, the numerators, the interpolation, its scaling, and the sumchecks' rounds.
-/

module

public import LeanVM.Guest.B1.Comp.Tables.FlockLoopsC
public import LeanVM.Guest.B1.Tables.FlockCRounds
public import LeanVM.Guest.B1.Tables.FlockCTail
public import LeanVM.Guest.B1.Tables.FlockM

/-!
# `verify_flock`'s first segments over a completeness model

The segments of `FlockCBody.lean` and `FlockCRounds.lean` under a completeness model's semantics
(`CompletesB CM.sem` at `coreProgram.RelB CM.sem rd`), over the honest memory at the model's total
hash (`FlMemC`), the run's hashes answered (`FlAns`): `c_p0C` (its call of `__loop81` the model's,
`loop81_completeC`), `c_rd1C`, `c_sq1C` and the rounds `c_frC`, `c_lcC` (their Fiat-Shamir blocks
the model's answers, `completesB_fsNextT_comp`, `completesB_squeezeT_comp`). The segments without
`BLAKE2S` are the deployed ones carried over (`Completes.toB`, `Completes.toBC`): the numerators
(`c_lag`), the interpolation (`c_ipG`, `c_ip` over any memory holding round 1's words) and its
scaling (`c_p5G`, at any skip challenge).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.Guest.B1.Sig LeanVM.E2E.Complete

@[expose] public section

section
variable {CM : CompModel} {rd : Reader} {τ : ℕ} {cv : Digest} {xs : List E}
  {cur zchis lrs zpart p11 p24 p40 p2220 : E}

/-! ## The prelude -/

/-- What the prelude leaves, at the total hash (`flP0Out`). -/
def flP0OutC (M : HashModel) (τ : ℕ) (cv : Digest) (p11 p24 p40 : E) : List (ℕ × E) :=
  [(11, p11), (24, p24), (38, (digestScalars (flCvST M τ cv)).1),
    (39, (digestScalars (flCvST M τ cv)).2), (40, p40), (10, gen ^ τ * word 16384 0 0),
    (23, gen ^ τ * word 16384 0 0 * word 4 0 0 * (gen ^ τ * word 16384 0 0 * word 4 0 0)),
    (26, p24 * word 67108864 0 0), (37, p24 * (gen ^ τ * word 16384 0 0 * (gen ^ τ * word 16384 0 0))),
    (30, word 8192 0 0 + gen ^ τ * word 16384 0 0), (31, word 8192 0 0), (33, gen ^ τ * word 16384 0 0)]

theorem fixed_getDT (M : HashModel) (τ : ℕ) (cv : Digest) {i : ℕ} (hi : i < 7) :
    flET M τ cv i = fixedWords.getD i 0 := by
  simp only [flET]
  rw [getD_append_lt (by rw [fixedChallenges_length]; exact hi), fixed_words]

/-- **The prelude over a completeness model** (`c_p0`). -/
theorem c_p0C (hτ : τ < 29) (hM : FlMemC CM.hm rd τ cv xs cur zchis lrs zpart p11 p24 p40 p2220)
    (hA : FlAns CM.hm τ cv xs) (σ : Val) (hσ : Fixes σ (flArgs τ cv cur zchis lrs zpart)) :
    CompletesB CM.sem (coreProgram.RelB CM.sem rd) rd 7 41 flP0 σ
      (fun σ' => Fixes σ' (flP0OutC CM.hm τ cv p11 p24 p40)) := by
  have h0 : σ (.n 0) = (digestScalars cv).1 := hσ.get (by simp [flArgs])
  have h1 : σ (.n 1) = (digestScalars cv).2 := hσ.get (by simp [flArgs])
  have h3 : σ (.n 3) = gen ^ τ := hσ.get (by simp [flArgs])
  have hz : ∀ i < 7, LoadHolds rd p11 (6 + i) (fixedWords.getD i 0) := fun i hi => by
    rw [← fixed_getDT CM.hm τ cv hi]; exact hM.zr i (by omega)
  obtain ⟨a0, a1⟩ := hM.pts 0 (by omega)
  obtain ⟨b0, b1⟩ := hM.pts (τ + 1) le_rfl
  refine completesB_upds [(7, (digestScalars cv).1), (8, (digestScalars cv).2),
    (9, word 16384 0 0), (10, gen ^ τ * word 16384 0 0), (11, p11),
    (12, word 5772811086190238293 0 0), (13, word 18376177690117868746 0 0),
    (14, word 1537792354547671042 0 0),
    (15, word 3877548338577296374 1367482035892397521 13373126565067795492),
    (16, word 7200243516802924451 16251485319816311889 13522021764491415548),
    (17, word 14498505783250251438 16564499533431716054 16770611540025040673),
    (18, word 3934799921294095118 853327055063395975 1309330797735322834),
    (19, word 16384 0 0), (20, gen ^ τ * word 16384 0 0), (21, word 4 0 0),
    (22, gen ^ τ * word 16384 0 0 * word 4 0 0),
    (23, gen ^ τ * word 16384 0 0 * word 4 0 0 * (gen ^ τ * word 16384 0 0 * word 4 0 0)),
    (24, p24), (25, word 67108864 0 0), (26, p24 * word 67108864 0 0), (27, word 8192 0 0),
    (28, word 16384 0 0), (29, gen ^ τ * word 16384 0 0), (30, word 8192 0 0 + gen ^ τ * word 16384 0 0),
    (31, word 8192 0 0), (32, word 16384 0 0), (33, gen ^ τ * word 16384 0 0), (34, word 16384 0 0),
    (35, gen ^ τ * word 16384 0 0), (36, gen ^ τ * word 16384 0 0 * (gen ^ τ * word 16384 0 0)),
    (37, p24 * (gen ^ τ * word 16384 0 0 * (gen ^ τ * word 16384 0 0))),
    (38, (digestScalars (flCvST CM.hm τ cv)).1), (39, (digestScalars (flCvST CM.hm τ cv)).2),
    (40, p40)] (by simp) (fun next kret hn => ?_) ?_
  · simp only [flP0, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil]
    vs_ev
    rw [h0, h1, h3]
    simp only [true_and, word_g13, word_g14, word_g26]
    refine ⟨hz 0 (by omega), hz 1 (by omega), hz 2 (by omega), hz 3 (by omega), hz 4 (by omega),
      hz 5 (by omega), hz 6 (by omega), lh_back a0 (by omega), lh_back a1 (by omega), ?_, ?_, ?_,
      ?_, hn⟩
    · exact isInK_add (gen_pow_isInK _) (isInK_mul (gen_pow_isInK _) (gen_pow_isInK _))
    · intro _
      rw [← pow_add]
      exact loop81_completeC hτ hM hA
    · rw [← pow_add, gen_pow_sq]
      exact lh_back b0 (by omega)
    · rw [← pow_add, gen_pow_sq]
      exact lh_back b1 (by omega)
  · intro p hp
    simp only [flP0OutC, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [upds_n]

/-! ## Round 1 and the skip challenge -/

theorem flP_take (xs : List E) {i : ℕ} (hi : i ≤ 64) : (flP xs).take i = xs.take i := by
  simp only [flP, List.take_take, Nat.min_eq_left hi]

/-- **Round 1's words over a completeness model** (`c_rd1`): read, absorbed at the model's
answers, stored at `flock_pts_r1`. -/
theorem c_rd1C (hM : FlMemC CM.hm rd τ cv xs cur zchis lrs zpart p11 p24 p40 p2220)
    (hA : FlAns CM.hm τ cv xs) (hlen : xs.length = flLen τ) (σ : Val)
    (hF : Fixes σ [(2, cur), (40, p40)])
    (hs : (σ (.n 38), σ (.n 39)) = digestScalars (flCvST CM.hm τ cv)) :
    CompletesB CM.sem (coreProgram.RelB CM.sem rd) rd 41 1001 ((List.range 64).map rd1Blk).flatten σ
      (fun σ' => Fixes σ' [(2, cur), (40, p40)] ∧
        (σ' (.n 999), σ' (.n 1000)) = digestScalars (flCvPT CM.hm τ cv xs)) := by
  have hpl : (flP xs).length = 64 := by simp [flP]; unfold flLen at hlen; omega
  have := CompletesB.flatten (S := CM.sem) (C := coreProgram.RelB CM.sem rd) (rd := rd)
    (blk := rd1Blk) (st := fun i => 41 + 15 * i)
    (Inv := fun i σ => Fixes σ [(2, cur), (40, p40)] ∧ (σ (.n (rd1S i)), σ (.n (rd1S i + 1))) =
      digestScalars (obsAllT CM.hm (flCvST CM.hm τ cv) ((flP xs).take i))) 64 (fun i _ => by omega)
    (fun i hi => numBelow_of_B (rd1_below i hi)) (fun i hi σ ⟨hF, hs⟩ => ?_) σ
    ⟨hF, by show (σ (.n 38), σ (.n 39)) = _; rw [List.take_zero]; exact hs⟩
  · rw [List.take_of_length_le (by omega)] at this
    exact this
  · rw [show 41 + 15 * (i + 1) = 41 + 15 * i + 15 by ring]
    have hb : rd1S i + 1 < 41 + 15 * i := by unfold rd1S; split <;> omega
    have hgi : (flP xs).getD i 0 = xs.getD i 0 := by
      simp only [flP]; exact getD_take' _ hi
    refine CompletesB.append_atom (P := fun σ' => Ext (41 + 15 * i) (41 + 15 * i + 15) σ σ' ∧
      σ' (.n (41 + 15 * i)) = xs.getD i 0 ∧ (σ' (.n (41 + 15 * i + 13)), σ' (.n (41 + 15 * i + 14))) =
        digestScalars (obsAllT CM.hm (flCvST CM.hm τ cv) ((flP xs).take (i + 1))))
      (completesB_fsNextT_comp ⟨_, by omega, rfl⟩ ⟨_, hb, rfl⟩ ⟨2, by omega, rfl⟩ hs
        (by rw [hF.get (k := 2) (e := cur) (by simp)]; exact hM.words i (by unfold flLen; omega))
        (by rw [← hgi]; exact hA.p1 i (by omega))
        fun σ' he hb ho => ⟨he, hb, ho⟩) fun σ' ⟨he, hx, ho⟩ => ⟨?_, ?_, ?_⟩
    · show LoadHolds rd (σ' (.n 40)) i (σ' (.n (41 + 15 * i)))
      rw [he.apply (Or.inl (by omega)), hF.get (k := 40) (e := p40) (by simp), hx]
      exact hM.p1 i hi
    · exact hF.of_ext he (by simp; omega)
    · rw [show rd1S (i + 1) = 41 + 15 * i + 13 by unfold rd1S; simp; omega]
      exact ho

/-- **The skip challenge over a completeness model** (`c_sq1`). -/
theorem c_sq1C (σ : Val) {cvP d : Digest} (hs : (σ (.n 999), σ (.n 1000)) = digestScalars cvP)
    (hd : sqCvM CM.hm cvP = some d) :
    CompletesB CM.sem (coreProgram.RelB CM.sem rd) rd 1001 1015 (squeezeT (.n 999) (.n 1000) 1001)
      σ (fun σ' => (σ' (.n 1006), σ' (.n 1007)) = digestScalars d ∧
        σ' (.n 1014) = challengeOf d) :=
  completesB_squeezeT_comp ⟨999, by omega, rfl⟩ ⟨1000, by omega, rfl⟩ hs hd
    fun _ _ h1 h2 => ⟨h1, h2⟩

/-! ## The numerators, the interpolation and its scaling -/

theorem lag64_hi_free : Stmt.freeInList [] (lag64T (.n 1014) (phi8From 64) 1015) = true := by
  decide +kernel

theorem lag64_lo_free : Stmt.freeInList [] (lag64T (.n 1014) (phi8From 0) 2273) = true := by
  decide +kernel

/-- `c_ip` over any memory holding round 1's words at `flock_pts_r1`, at any call relation. -/
theorem c_ipG {C : CallRel} (hp1 : ∀ i < 64, LoadHolds rd p40 i (xs.getD i 0)) {z : E}
    (σ : Val) (h0 : IpInv p40 z xs 0 σ) :
    Completes C rd 1465 1845 ((List.range 64).map ipBlk).flatten σ
      (fun σ' => IpInv p40 z xs 64 σ') := by
  refine Completes.flatten (st := ipSt) (Inv := IpInv p40 z xs) 64
    (fun i _ => by unfold ipSt; split <;> split <;> omega)
    (fun i hi => numBelow_of_B (ip_below i hi)) (fun i hi σ hI => ?_) σ h0
  have h40 : σ (.n 40) = p40 := hI.1.get (k := 40) (e := p40) (by simp)
  have hz : σ (.n 1014) = z := hI.1.get (k := 1014) (e := z) (by simp)
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · refine completes_upds [(1465, xs.getD 0 0), (1466, numHi z 0 * xs.getD 0 0)] (by simp [ipSt])
      (fun next kret hn => ?_) ?_
    · simp only [ipBlk, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
      vs_ev
      rw [h40, hI.2.1 0 (by omega)]
      exact ⟨hp1 0 (by omega), rfl, hn⟩
    · have he := upds_ext (lo := 1465) (hi := 1467) σ [(1465, xs.getD 0 0),
        (1466, numHi z 0 * xs.getD 0 0)] (by simp)
      refine ⟨(ipInv_keep hI he le_rfl).1, (ipInv_keep hI he le_rfl).2, fun _ => ⟨?_, ?_⟩⟩
      · simp only [Nat.zero_add, ↓reduceIte, Finset.prod_range_one, phi_zero, add_zero]
        rw [upds_of_not_mem σ _ (by simp), hz]
      · simp only [Nat.zero_add, ↓reduceIte, Finset.sum_range_one]
        vs_ev
  · obtain ⟨hP, hS⟩ := hI.2.2 hpos
    have hi' : ¬ i = 0 := by omega
    set P := σ (.n (if i = 1 then 1014 else 1457 + 6 * i))
    set S := σ (.n (if i = 1 then 1466 else 1460 + 6 * i))
    have hsi : ipSt i = 1461 + 6 * i := by simp [ipSt, hi']
    have hsi1 : ipSt (i + 1) = 1461 + 6 * i + 6 := by simp [ipSt]; omega
    rw [hsi, hsi1]
    refine completes_upds (ipVals z P S xs i) (ipVals_range z P S xs i) (fun next kret hn => ?_) ?_
    · simp only [ipBlk, hi', ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
      have e1 : ∀ k < 1461 + 6 * i, upds σ (ipVals z P S xs i) (.n k) = σ (.n k) := fun k hk =>
        upds_of_not_mem σ _ fun p hp => by
          have := ipVals_range z P S xs i p hp
          simp only [ne_eq, V.mk.injEq, true_and]; omega
      rw [e1 1014 (by omega), e1 40 (by omega), e1 (1401 + i) (by omega),
        e1 (if i = 1 then 1014 else 1457 + 6 * i) (by split <;> omega),
        e1 (if i = 1 then 1466 else 1460 + 6 * i) (by split <;> omega), hz, h40,
        hI.2.1 i (by omega)]
      simp only [ipVals]
      fl_ev
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hn⟩ <;> first | trivial | rfl | exact hp1 i hi
    · have he := upds_ext σ _ (ipVals_range z P S xs i)
      obtain ⟨k1, k2⟩ := ipInv_keep hI he (by omega)
      refine ⟨k1, k2, fun _ => ⟨?_, ?_⟩⟩
      · rw [ite_neg' (by omega), show 1457 + 6 * (i + 1) = 1463 + 6 * i by ring]
        simp only [ipVals]
        fl_ev
        rw [hP, word_phi8Words (by omega), Finset.prod_range_succ]
      · rw [ite_neg' (by omega), show 1460 + 6 * (i + 1) = 1466 + 6 * i by ring]
        simp only [ipVals]
        fl_ev
        rw [hS, Finset.sum_range_succ]

/-- `c_p5` at any skip challenge `z`, at any call relation. -/
theorem c_p5G {C : CallRel} (hlen : xs.length = flLen τ) (σ : Val) {z : E}
    (h3 : σ (.n 3) = gen ^ τ) (hP : σ (.n 1841) = ∏ j ∈ Finset.range 64, (z + phi j))
    (hS : σ (.n 1844) = ∑ j ∈ Finset.range 64, numHi z j * xs.getD j 0) :
    Completes C rd 1845 1852 flP5 σ
      (fun σ' => σ' (.n 1847) = lagrangeInterpolate 128 (List.replicate 64 0 ++ flP xs) z ∧
        σ' (.n 1851) = gen ^ τ * word 16384 0 0 * word 2017612633061982209 0 0) := by
  refine completes_upds [(1845, word 233317187178767959 0 0),
    (1846, σ (.n 1841) * word 233317187178767959 0 0),
    (1847, σ (.n 1844) * (σ (.n 1841) * word 233317187178767959 0 0)), (1848, word 16384 0 0),
    (1849, gen ^ τ * word 16384 0 0), (1850, word 2017612633061982209 0 0),
    (1851, gen ^ τ * word 16384 0 0 * word 2017612633061982209 0 0)] (by simp)
    (fun next kret hn => ?_) ?_
  · simp only [flP5, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
    vs_ev
    rw [h3]
    simp only [true_and]
    exact hn
  · refine ⟨?_, by vs_ev⟩
    vs_ev
    rw [hP, hS, interp_eq _ _ (by simp [flP]; unfold flLen at hlen; omega)]
    refine congrArg (· * _) (Finset.sum_congr rfl fun i hi => ?_)
    rw [flP, getD_take' _ (Finset.mem_range.mp hi)]
    rfl

/-! ## The fixed rounds -/

/-- The invariant of the fixed rounds before round `i`, at the total hash (`FrInv`). -/
def FrInvC (M : HashModel) (τ : ℕ) (cv : Digest) (xs : List E) (cur zchis p11 : E) (i : ℕ)
    (σ : Val) : Prop :=
  Fixes σ [(2, cur), (4, zchis), (11, p11)] ∧ σ (.n (frC i)) = (flScAtT M τ cv xs i).1 ∧
    (σ (.n (frS i)), σ (.n (frS i + 1))) = digestScalars (flScAtT M τ cv xs i).2

/-- **Fixed round `i` over a completeness model** (`c_fr`). -/
theorem c_frC (hM : FlMemC CM.hm rd τ cv xs cur zchis lrs zpart p11 p24 p40 p2220)
    (hA : FlAns CM.hm τ cv xs) {i : ℕ} (hi : i < 7) (σ : Val)
    (hI : FrInvC CM.hm τ cv xs cur zchis p11 i σ) :
    CompletesB CM.sem (coreProgram.RelB CM.sem rd) rd (frB i) (frB (i + 1)) (frBlk i) σ
      (FrInvC CM.hm τ cv xs cur zchis p11 (i + 1)) := by
  obtain ⟨hF, hc, hs⟩ := hI
  obtain ⟨b1, b2, b3, hsB, hcB, b4⟩ := fr_below i hi
  obtain ⟨o1, o2, o3⟩ := hA.sc i (by omega)
  have h2 : σ (.n 2) = cur := hF.get (k := 2) (e := cur) (by simp)
  have h4 : σ (.n 4) = zchis := hF.get (k := 4) (e := zchis) (by simp)
  have h11 : σ (.n 11) = p11 := hF.get (k := 11) (e := p11) (by simp)
  have hB1 : frB (i + 1) = frB i + 52 := by simp [frB]; ring
  have h11B : 11 < frB i := by simp [frB]; omega
  rw [hB1]
  simp only [frBlk, List.append_assoc]
  rw [List.cons_append]
  set B := frB i with hB
  set st := flScAtT CM.hm τ cv xs i
  set g1 := xs.getD (64 + 2 * i) 0
  set g2 := xs.getD (65 + 2 * i) 0
  set e := flET CM.hm τ cv i
  set cv2 := obsCvT CM.hm st.2 g1
  set cv3 := obsCvT CM.hm cv2 g2
  set ch := challengeOf (sqCvT CM.hm cv3)
  refine CompletesB.atom_cons e (by omega) (NumBelow.cons ⟨B, by omega, rfl⟩
    (NumBelow.cons ⟨11, by omega, rfl⟩ (NumBelow.nil _))) ?_ ?_
  · show LoadHolds rd (Function.update σ (.n B) e (.n 11)) (6 + i)
      (Function.update σ (.n B) e (.n B))
    rw [upd_ne (by omega), upd_eq, h11]; exact hM.zr i (by omega)
  set σ1 := Function.update σ (.n B) e
  have k1 : ∀ j < B, σ1 (.n j) = σ (.n j) := fun j hj => upd_ne (by omega)
  refine CompletesB.append (m := B + 16) (by omega) (by omega) (numBelow_of_B b1)
    (completesB_fsNextT_comp (x := g1) (cv := st.2) ⟨_, by omega, rfl⟩ ⟨_, by omega, rfl⟩
      ⟨2, by omega, rfl⟩ (by rw [k1 _ (by omega), k1 _ (by omega)]; exact hs)
      (by rw [k1 _ (by omega), h2]; exact hM.words _ (by unfold flLen; omega)) o1
      (Post := fun σ' => Ext (B + 1) (B + 16) σ1 σ' ∧ σ' (.n (B + 1)) = g1 ∧
        (σ' (.n (B + 1 + 13)), σ' (.n (B + 1 + 14))) = digestScalars cv2)
      fun σ' he hb ho => ⟨he, hb, ho⟩) fun σ2 _ ⟨he2, hg1, ho2⟩ => ?_
  refine CompletesB.append (m := B + 31) (by omega) (by omega) (numBelow_of_B b2)
    (completesB_fsNextT_comp (x := g2) (cv := cv2) ⟨_, by omega, rfl⟩ ⟨_, by omega, rfl⟩
      ⟨2, by omega, rfl⟩
      (by rw [show B + 14 = B + 1 + 13 by ring, show B + 15 = B + 1 + 14 by ring]; exact ho2)
      (by rw [he2.apply (Or.inl (by omega)), k1 _ (by omega), h2]
          exact hM.words _ (by unfold flLen; omega)) o2
      (Post := fun σ' => Ext (B + 16) (B + 31) σ2 σ' ∧ σ' (.n (B + 16)) = g2 ∧
        (σ' (.n (B + 16 + 13)), σ' (.n (B + 16 + 14))) = digestScalars cv3)
      fun σ' he hb ho => ⟨he, hb, ho⟩) fun σ3 _ ⟨he3, hg2, ho3⟩ => ?_
  have a3 : ∀ j < B + 1, σ3 (.n j) = σ1 (.n j) := fun j hj => by
    rw [he3.apply (Or.inl (by omega)), he2.apply (Or.inl (by omega))]
  have f1 : σ3 (.n (B + 1)) = g1 := by rw [he3.apply (Or.inl (by omega))]; exact hg1
  have fB : σ3 (.n B) = e := by rw [a3 B (by omega)]; simp [σ1]
  have fC : σ3 (.n (frC i)) = st.1 := by rw [a3 _ (by omega), k1 _ hcB, hc]
  have f4 : σ3 (.n 4) = zchis := by rw [a3 _ (by omega), k1 _ (by omega), h4]
  have hs3 : (σ3 (.n (B + 29)), σ3 (.n (B + 30))) = digestScalars cv3 := by
    rw [show B + 29 = B + 16 + 13 by ring, show B + 30 = B + 16 + 14 by ring]; exact ho3
  set l1 : List (ℕ × E) := [(B + 31, g1 + g2), (B + 32, e * (g1 + g2)),
    (B + 33, st.1 + e * (g1 + g2))]
  have r1 : ∀ p ∈ l1, B + 31 ≤ p.1 ∧ p.1 < B + 34 := by
    simp only [l1, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl) <;> simp
  have u1 : ∀ j < B + 31, upds σ3 l1 (.n j) = σ3 (.n j) := fun j hj =>
    upds_of_not_mem σ3 _ fun p hp => by
      have := r1 p hp; simp only [ne_eq, V.mk.injEq, true_and]; omega
  refine CompletesB.append (m := B + 34) (by omega) (by omega)
    (numBelow_of_B b4)
    (completesB_upds l1 r1 (fun next kret hn => ?_) (Post := fun σ' => σ' = upds σ3 l1) rfl)
    fun σ4 _ hσ4 => ?_
  · simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB]
    rw [u1 (B + 1) (by omega), u1 (B + 16) (by omega), u1 B (by omega), u1 (frC i) (by omega), f1,
      hg2, fB, fC]
    simp only [l1]
    fl_ev
    exact ⟨trivial, trivial, trivial, hn⟩
  subst hσ4
  refine CompletesB.append (m := B + 48) (by omega) (by omega) (numBelow_of_B b3)
    (completesB_squeezeT_comp (cv := cv3) ⟨_, by omega, rfl⟩ ⟨_, by omega, rfl⟩
      (by rw [u1 (B + 29) (by omega), u1 (B + 30) (by omega)]; exact hs3) o3
      (Post := fun σ' => Ext (B + 34) (B + 48) (upds σ3 l1) σ' ∧
        (σ' (.n (B + 34 + 5)), σ' (.n (B + 34 + 6))) = digestScalars (sqCvT CM.hm cv3) ∧
        σ' (.n (B + 34 + 13)) = ch) fun σ' he h1 h2 => ⟨he, h1, h2⟩)
    fun σ5 _ ⟨he5, hs5, hch⟩ => ?_
  have a5 : ∀ j < B + 31, σ5 (.n j) = σ3 (.n j) := fun j hj => by
    rw [he5.apply (Or.inl (by omega)), u1 j hj]
  have f33 : σ5 (.n (B + 33)) = st.1 + e * (g1 + g2) := by
    rw [he5.apply (Or.inl (by omega))]; simp only [l1]; fl_ev
  set l2 : List (ℕ × E) := [(B + 48, ch * g2), (B + 49, g1 + ch * g2), (B + 50, ch * (g1 + ch * g2)),
    (B + 51, st.1 + e * (g1 + g2) + ch * (g1 + ch * g2))]
  have r2 : ∀ p ∈ l2, B + 48 ≤ p.1 ∧ p.1 < B + 52 := by
    simp only [l2, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl) <;> simp
  have u2 : ∀ j < B + 48, upds σ5 l2 (.n j) = σ5 (.n j) := fun j hj =>
    upds_of_not_mem σ5 _ fun p hp => by
      have := r2 p hp; simp only [ne_eq, V.mk.injEq, true_and]; omega
  refine completesB_upds l2 r2 (fun next kret hn => ?_) ⟨fun p hp => ?_, ?_, ?_⟩
  · simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB]
    rw [u2 4 (by omega), u2 (B + 47) (by omega), u2 (B + 16) (by omega), u2 (B + 1) (by omega),
      u2 (B + 33) (by omega), a5 4 (by omega), a5 (B + 16) (by omega), a5 (B + 1) (by omega),
      show B + 47 = B + 34 + 13 by ring, hch, f1, hg2, f4, f33]
    simp only [l2]
    fl_ev
    exact ⟨hM.chis i (by omega), trivial, trivial, trivial, trivial, hn⟩
  · have hp' : p.1 < 12 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp
    rw [u2 _ (by omega), a5 _ (by omega), a3 _ (by omega), k1 _ (by omega)]
    exact hF p hp
  · rw [show frC (i + 1) = B + 51 by simp [frC, hB, frB]; omega]
    simp only [l2]
    fl_ev
    rfl
  · rw [show frS (i + 1) = B + 39 by simp [frS, hB, frB]; omega, u2 _ (by omega), u2 _ (by omega),
      show B + 39 = B + 34 + 5 by ring, show B + 34 + 5 + 1 = B + 34 + 6 by ring]
    exact hs5

/-! ## The lincheck's rounds -/

/-- The lincheck's state after `j` rounds at the total hash (`flLcAt`). -/
abbrev flLcAtT (M : HashModel) (τ : ℕ) (cv : Digest) (xs : List E) (j : ℕ) : E × Digest :=
  lcStT M (flG' τ xs) (flSt0'T M τ cv xs) j

/-- The invariant of the lincheck before round `i`, at the total hash (`LcInv`). -/
def LcInvC (M : HashModel) (τ : ℕ) (cv : Digest) (xs : List E) (cur lrs : E) (i : ℕ) (σ : Val) :
    Prop :=
  Fixes σ [(5, lrs), (2240, cur * gen ^ (64 + 2 * (τ + 8)))] ∧
    σ (.n (lcC i)) = (flLcAtT M τ cv xs i).1 ∧
    (σ (.n (lcS i)), σ (.n (lcS i + 1))) = digestScalars (flLcAtT M τ cv xs i).2

/-- **Lincheck round `i` over a completeness model** (`c_lc`). -/
theorem c_lcC (hM : FlMemC CM.hm rd τ cv xs cur zchis lrs zpart p11 p24 p40 p2220)
    (hA : FlAns CM.hm τ cv xs) {i : ℕ} (hi : i < 8) (σ : Val)
    (hI : LcInvC CM.hm τ cv xs cur lrs i σ) :
    CompletesB CM.sem (coreProgram.RelB CM.sem rd) rd (lcB i) (lcB (i + 1)) (lcBlk i) σ
      (LcInvC CM.hm τ cv xs cur lrs (i + 1)) := by
  obtain ⟨hF, hc, hs⟩ := hI
  obtain ⟨b1, b2, b3, hsB, hcB, hCB, b4⟩ := lc_below i hi
  obtain ⟨o1, o2, o3⟩ := hA.lc i hi
  have h5 : σ (.n 5) = lrs := hF.get (k := 5) (e := lrs) (by simp)
  have hcu : σ (.n 2240) = cur * gen ^ (64 + 2 * (τ + 8)) :=
    hF.get (k := 2240) (e := cur * gen ^ (64 + 2 * (τ + 8))) (by simp)
  have hB1 : lcB (i + 1) = lcB i + 49 := by simp [lcB]; ring
  rw [hB1]
  simp only [lcBlk, List.append_assoc]
  set B := lcB i with hB
  set st := flLcAtT CM.hm τ cv xs i
  set g1 := xs.getD (66 + 2 * (τ + 8) + 2 * i) 0
  set g2 := xs.getD (67 + 2 * (τ + 8) + 2 * i) 0
  set cv2 := obsCvT CM.hm st.2 g1
  set cv3 := obsCvT CM.hm cv2 g2
  set r := challengeOf (sqCvT CM.hm cv3)
  refine CompletesB.append (m := B + 15) (by omega) (by omega) (numBelow_of_B b1)
    (completesB_fsNextT_comp (x := g1) (cv := st.2) ⟨_, by omega, rfl⟩ ⟨_, by omega, rfl⟩
      ⟨2240, by omega, rfl⟩ hs
      (by rw [hcu]; exact lh_back (hM.words _ (by unfold flLen; omega)) (by omega)) o1
      (Post := fun σ' => Ext B (B + 15) σ σ' ∧ σ' (.n B) = g1 ∧
        (σ' (.n (B + 13)), σ' (.n (B + 14))) = digestScalars cv2)
      fun σ' he hb ho => ⟨he, hb, ho⟩) fun σ2 _ ⟨he2, hg1, ho2⟩ => ?_
  refine CompletesB.append (m := B + 30) (by omega) (by omega) (numBelow_of_B b2)
    (completesB_fsNextT_comp (x := g2) (cv := cv2) ⟨_, by omega, rfl⟩ ⟨_, by omega, rfl⟩
      ⟨2240, by omega, rfl⟩ ho2
      (by rw [he2.apply (Or.inl (by omega)), hcu]
          exact lh_back (hM.words _ (by unfold flLen; omega)) (by omega)) o2
      (Post := fun σ' => Ext (B + 15) (B + 30) σ2 σ' ∧ σ' (.n (B + 15)) = g2 ∧
        (σ' (.n (B + 15 + 13)), σ' (.n (B + 15 + 14))) = digestScalars cv3)
      fun σ' he hb ho => ⟨he, hb, ho⟩) fun σ3 _ ⟨he3, hg2, ho3⟩ => ?_
  have a3 : ∀ j < B, σ3 (.n j) = σ (.n j) := fun j hj => by
    rw [he3.apply (Or.inl (by omega)), he2.apply (Or.inl (by omega))]
  have f1 : σ3 (.n B) = g1 := by rw [he3.apply (Or.inl (by omega))]; exact hg1
  have fC : σ3 (.n (lcC i)) = st.1 := by rw [a3 _ hcB, hc]
  have f5 : σ3 (.n 5) = lrs := by rw [a3 _ (by omega), h5]
  have hs3 : (σ3 (.n (B + 28)), σ3 (.n (B + 29))) = digestScalars cv3 := by
    rw [show B + 28 = B + 15 + 13 by ring, show B + 29 = B + 15 + 14 by ring]; exact ho3
  set l1 : List (ℕ × E) := [(B + 30, st.1 + g2)]
  have r1 : ∀ p ∈ l1, B + 30 ≤ p.1 ∧ p.1 < B + 31 := by simp [l1]
  have u1 : ∀ j < B + 30, upds σ3 l1 (.n j) = σ3 (.n j) := fun j hj =>
    upds_of_not_mem σ3 _ fun p hp => by
      have := r1 p hp; simp only [ne_eq, V.mk.injEq, true_and]; omega
  refine CompletesB.append (m := B + 31) (by omega) (by omega) (numBelow_of_B b4)
    (completesB_upds l1 r1 (fun next kret hn => ?_) (Post := fun σ' => σ' = upds σ3 l1) rfl)
    fun σ4 _ hσ4 => ?_
  · simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB]
    rw [u1 (B + 15) (by omega), u1 (lcC i) (by omega), hg2, fC]
    simp only [l1]
    fl_ev
    exact ⟨trivial, hn⟩
  subst hσ4
  refine CompletesB.append (m := B + 45) (by omega) (by omega) (numBelow_of_B b3)
    (completesB_squeezeT_comp (cv := cv3) ⟨_, by omega, rfl⟩ ⟨_, by omega, rfl⟩
      (by rw [u1 (B + 28) (by omega), u1 (B + 29) (by omega)]; exact hs3) o3
      (Post := fun σ' => Ext (B + 31) (B + 45) (upds σ3 l1) σ' ∧
        (σ' (.n (B + 31 + 5)), σ' (.n (B + 31 + 6))) = digestScalars (sqCvT CM.hm cv3) ∧
        σ' (.n (B + 31 + 13)) = r) fun σ' he h1 h2 => ⟨he, h1, h2⟩)
    fun σ5 _ ⟨he5, hs5, hch⟩ => ?_
  have a5 : ∀ j < B + 30, σ5 (.n j) = σ3 (.n j) := fun j hj => by
    rw [he5.apply (Or.inl (by omega)), u1 j hj]
  have f30 : σ5 (.n (B + 30)) = st.1 + g2 := by
    rw [he5.apply (Or.inl (by omega))]; simp only [l1]; fl_ev
  set l2 : List (ℕ × E) := [(B + 45, r * g2), (B + 46, st.1 + g2 + r * g2),
    (B + 47, r * (st.1 + g2 + r * g2)), (B + 48, g1 + r * (st.1 + g2 + r * g2))]
  have r2 : ∀ p ∈ l2, B + 45 ≤ p.1 ∧ p.1 < B + 49 := by
    simp only [l2, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl) <;> simp
  have u2 : ∀ j < B + 45, upds σ5 l2 (.n j) = σ5 (.n j) := fun j hj =>
    upds_of_not_mem σ5 _ fun p hp => by
      have := r2 p hp; simp only [ne_eq, V.mk.injEq, true_and]; omega
  refine completesB_upds l2 r2 (fun next kret hn => ?_) ⟨fun p hp => ?_, ?_, ?_⟩
  · simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB]
    rw [u2 5 (by omega), u2 (B + 44) (by omega), u2 (B + 15) (by omega), u2 (B + 30) (by omega),
      u2 B (by omega), a5 5 (by omega), a5 (B + 15) (by omega), a5 B (by omega),
      show B + 44 = B + 31 + 13 by ring, hch, f1, hg2, f5, f30]
    simp only [l2]
    fl_ev
    exact ⟨hM.rcs i hi, trivial, trivial, trivial, trivial, hn⟩
  · have hp' : p.1 < 2241 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp
    rw [u2 _ (by omega), a5 _ (by omega), a3 _ (by omega)]
    exact hF p hp
  · rw [show lcC (i + 1) = B + 48 by simp [lcC, hB, lcB]; omega]
    simp only [l2]
    fl_ev
    rfl
  · rw [show lcS (i + 1) = B + 36 by simp [lcS, hB, lcB]; omega, u2 _ (by omega), u2 _ (by omega),
      show B + 36 = B + 31 + 5 by ring, show B + 31 + 5 + 1 = B + 31 + 6 by ring]
    exact hs5

end

end
end LeanVM.Guest.B1
