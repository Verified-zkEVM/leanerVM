/-
  LeanVM.Guest.B1.Comp.Tables.FlockAllC

  `verify_flock` complete over a completeness model (`verify_flock_complete` over `CM`), and the
  deployed completeness recovered at `CompModel.deployed`.
-/

module

public import LeanVM.Guest.B1.Comp.Tables.FlockSegsC2
public import LeanVM.Guest.B1.Comp.Tables.DeployedC
public import LeanVM.Guest.B1.Tables.FlockCAll
public import LeanVM.Guest.B1.VerifySub.InterfaceM

/-!
# `verify_flock` over a completeness model

`flock_body_completeC`: the seventeen segments of `flSegs` complete in sequence under the model's
semantics over the honest memory at the total hash (`FlMemC`), the run's hashes answered
(`FlAns`), the matrices' value passing the terminal check (`flTermT`). `verify_flock_relC`: then
`verify_flock` holds under the model of the run's returns. `verify_flock_completeC`:
`CompleteFlockC CM rd (FlockMemC CM.hm)`, the deployed `CompleteFlock` over the model: from an
answered run (`FlockOutM CM.hm`, read back by `flock_invC`) and the honest buffers, the relation
under `CM.sem`.

At `CompModel.deployed` the total hash is BLAKE2s (`flET_hm_deployed`, …), every hash is
answered (`flAns_hm_deployed`), and the lemmas give the deployed ones: `loop81_complete_of_comp`,
`loop82_complete_of_comp`, `verify_flock_rel_of_comp`, `verify_flock_complete_of_comp`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.Guest.B1.Sig LeanVM.E2E.Complete

@[expose] public section

/-! ## The segments without `BLAKE2S` or calls -/

theorem flP13_free : Stmt.freeInList [] flP13 = true := by decide +kernel

theorem flPEnd_free : Stmt.freeInList [] flPEnd = true := by decide +kernel

theorem cpe_free : Stmt.freeInList [] ((List.range 8).map cpeBlk).flatten = true := by
  decide +kernel

theorem cs_free : Stmt.freeInList [] ((List.range 64).map csBlk).flatten = true := by
  decide +kernel

section
variable {CM : CompModel} {rd : Reader} {τ : ℕ} {cv : Digest} {xs : List E}
  {cur zchis lrs zpart p11 p24 p40 p2220 : E}

/-- **The terminal check in the guest's form at the total hash** (`flTerm_guest`). -/
theorem flTerm_guestC (M : HashModel) (hlen : xs.length = flLen τ) {mv : E}
    (hterm : flTermT M τ cv xs mv) :
    (flLcT M τ cv xs).1 = mv + flAlphaT M τ cv xs * flAlphaT M τ cv xs * flAlphaT M τ cv xs *
        pinW (lcChT M (flG' τ xs) (flSt0'T M τ cv xs)) * xs.getD (82 + 2 * (τ + 8)) 0 +
      flAlphaT M τ cv xs * flAlphaT M τ cv xs *
        (∏ t ∈ Finset.range 8, (1 + scChT M (flET M τ cv) (flG xs) (flSt0T M τ cv xs) t +
          lcChT M (flG' τ xs) (flSt0'T M τ cv xs) (7 - t))) *
        ((∑ j ∈ Finset.range 64, numLo (flZT M τ cv xs) j * xs.getD (82 + 2 * (τ + 8) + j) 0) *
          word 11666641484232641359 0 0) := by
  have hsl : (flS τ xs).length = 64 := by simp [flS]; unfold flLen at hlen; omega
  have hrl : (flRcT M τ cv xs).length = 8 := by simp [flRcT]
  have hcl : (flChiT M τ cv xs).length = τ + 8 := by simp [flChiT]
  rw [← (show _ = (flLcT M τ cv xs).1 from hterm), ← cslice_eq _ _ hsl, colWeight_pin _ _ hrl hsl,
    Main.eqEval_prod _ _ 8 (by simp [hcl]) (by simp [hrl])]
  have hS : ∑ i ∈ Finset.range 64, (∏ j ∈ (Finset.range 64).erase i, (flZT M τ cv xs + phi j)) *
      (flS τ xs).getD i 0 =
      ∑ j ∈ Finset.range 64, numLo (flZT M τ cv xs) j * xs.getD (82 + 2 * (τ + 8) + j) 0 :=
    Finset.sum_congr rfl fun i hi => by
      rw [flS_getD τ xs (Finset.mem_range.mp hi), numLo]
      simp only [Nat.zero_add]
  have hE : ∏ k ∈ Finset.range 8, (1 + ((flChiT M τ cv xs).take 8).getD k 0 +
      (flRcT M τ cv xs).reverse.getD k 0) = ∏ t ∈ Finset.range 8,
        (1 + scChT M (flET M τ cv) (flG xs) (flSt0T M τ cv xs) t +
          lcChT M (flG' τ xs) (flSt0'T M τ cv xs) (7 - t)) :=
    Finset.prod_congr rfl fun t ht => by
      have ht' := Finset.mem_range.mp ht
      rw [getD_take' _ ht', flChiT, getD_map_range _ _ (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_reverse (by omega), hrl, ← List.getD_eq_getElem?_getD, flRcT,
        getD_map_range _ _ (by omega), show 8 - 1 - t = 7 - t by omega]
  rw [hS, hE, flS_getD τ xs (by omega)]
  simp only [flRcT, getD_map_range _ _ (show 0 < 8 by omega), getD_map_range _ _ (show 1 < 8 by omega),
    getD_map_range _ _ (show 2 < 8 by omega), getD_map_range _ _ (show 3 < 8 by omega),
    getD_map_range _ _ (show 4 < 8 by omega), getD_map_range _ _ (show 5 < 8 by omega),
    getD_map_range _ _ (show 6 < 8 by omega), getD_map_range _ _ (show 7 < 8 by omega), pinW,
    Nat.add_zero]
  ring

set_option maxHeartbeats 4000000 in
/-- **`verify_flock`'s body completes over a completeness model** (`flock_body_complete`) from
its arguments over the honest memory at the total hash, the run's hashes answered, the matrices'
value `mv` passing the terminal check: its returns are the run's. -/
theorem flock_body_completeC (hτ : τ < 29)
    (hM : FlMemC CM.hm rd τ cv xs cur zchis lrs zpart p11 p24 p40 p2220) (hA : FlAns CM.hm τ cv xs)
    (hlen : xs.length = flLen τ) {mv : E} (hterm : flTermT CM.hm τ cv xs mv) (σ0 : Val)
    (hσ0 : Fixes σ0 (flArgs τ cv cur zchis lrs zpart)) :
    CompletesB CM.sem (coreProgram.RelB CM.sem rd) rd 7 4377 flSegs.flatten σ0 (fun σ' =>
      [σ' (.n 4369), σ' (.n 4370), σ' (.n 4373), σ' (.n 4374), σ' (.n 4375), σ' (.n 4376)] =
        [(digestScalars (obsAllT CM.hm (flLcT CM.hm τ cv xs).2 (flS τ xs))).1,
          (digestScalars (obsAllT CM.hm (flLcT CM.hm τ cv xs).2 (flS τ xs))).2,
          cur * gen ^ (64 + 2 * (τ + 8)) * gen ^ 82, flZT CM.hm τ cv xs, flAlphaT CM.hm τ cv xs, mv] ∧
      Fixes σ' (flP0OutC CM.hm τ cv p11 p24 p40) ∧ Fixes σ' (flP7OutC CM.hm τ cv xs cur p2220
        (gen ^ τ * word 16384 0 0 * word 2017612633061982209 0 0))) := by
  simp only [flSegs, List.flatten_cons, List.flatten_nil, List.append_nil]
  have a0 : ∀ k < 7, ∀ v, (k, v) ∈ flArgs τ cv cur zchis lrs zpart → σ0 (.n k) = v :=
    fun k _ v hv => hσ0 _ hv
  -- the prelude
  refine CompletesB.append (m := 41) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (c_p0C hτ hM hA σ0 hσ0) fun σ1 e1 p1 => ?_
  have E1 := e1
  have g2 : σ1 (.n 2) = cur := E1.get (by omega) (a0 2 (by omega) _ (by simp [flArgs]))
  -- round 1
  refine CompletesB.append (m := 1001) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (c_rd1C hM hA hlen σ1 (fixes_two g2 (p1.get (by simp [flP0OutC])))
      (Prod.ext (p1.get (by simp [flP0OutC])) (p1.get (by simp [flP0OutC]))))
    fun σ2 e2 ⟨q2, p2⟩ => ?_
  have E2 := E1.trans e2 (by omega) (by omega)
  -- the skip challenge
  refine CompletesB.append (m := 1015) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (c_sq1C σ2 p2 hA.z) fun σ3 e3 ⟨p3a, p3b⟩ => ?_
  have E3 := E2.trans e3 (by omega) (by omega)
  have hZ : σ3 (.n 1014) = flZT CM.hm τ cv xs := p3b
  -- the upper numerators
  refine CompletesB.append (m := 1465) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    ((c_lag (n := 450) (by omega) (by omega) (by rw [lag64V_length, lgLen_hi.1, lgLen_hi.2]) σ3
      hZ).toBC lag64_hi_free)
    fun σ4 e4 p4 => ?_
  rw [lgOut_hi] at p4
  have E4 := E3.trans e4 (by omega) (by omega)
  -- the interpolation
  refine CompletesB.append (m := 1845) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    ((c_ipG hM.p1 σ4 ⟨fixes_two (e4.get (by omega) (e3.get (by omega) (q2.get (by simp))))
      (e4.get (by omega) hZ), p4, fun h => absurd h (by omega)⟩).toB
      (noBlakeList_flatten_range 64 ipBlk ipBlk_noBlake)) fun σ5 e5 p5 => ?_
  have E5 := E4.trans e5 (by omega) (by omega)
  obtain ⟨-, -, p5'⟩ := p5
  obtain ⟨hP, hS⟩ := p5' (by omega)
  simp only [Nat.reduceEqDiff, ↓reduceIte, Nat.reduceMul, Nat.reduceAdd] at hP hS
  -- the first claim
  refine CompletesB.append (m := 1852) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    ((c_p5G hlen σ5 (E5.get (by omega) (a0 3 (by omega) _ (by simp [flArgs]))) hP hS).toB
      flP5_noBlake)
    fun σ6 e6 ⟨p6, p6b⟩ => ?_
  have E6 := E5.trans e6 (by omega) (by omega)
  have g11 : σ6 (.n 11) = p11 := e6.get (by omega) (e5.get (by omega) (e4.get (by omega)
    (e3.get (by omega) (e2.get (by omega) (p1.get (by simp [flP0OutC]))))))
  have fF6 : Fixes σ6 [(2, cur), (3, gen ^ τ), (4, zchis), (11, p11)] := by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact E6.get (by omega) (a0 2 (by omega) _ (by simp [flArgs]))
    · exact E6.get (by omega) (a0 3 (by omega) _ (by simp [flArgs]))
    · exact E6.get (by omega) (a0 4 (by omega) _ (by simp [flArgs]))
    · exact g11
  -- the fixed rounds
  refine CompletesB.append (m := 2216) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (CompletesB.flatten (st := frB) (Inv := FrInvC CM.hm τ cv xs cur zchis p11) 7
      (fun i _ => by simp only [frB]; omega)
      (fun i hi => numBelow_of_B (by revert i hi; decide +kernel))
      (fun i hi σ hI => c_frC hM hA hi σ hI) σ6
      ⟨fixes_sub fF6 (by simp), p6, by
        show (σ6 (.n 1006), σ6 (.n 1007)) = _
        rw [e6.get (by omega) (e5.get (by omega) (e4.get (by omega) (congrArg Prod.fst p3a))),
          e6.get (by omega) (e5.get (by omega) (e4.get (by omega) (congrArg Prod.snd p3a)))]
        rfl⟩) fun σ7 e7 p7 => ?_
  have E7 := E6.trans e7 (by omega) (by omega)
  -- the sampled rounds
  refine CompletesB.append (m := 2241) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (c_p7C hτ hM hA σ7 (fF6.of_ext e7 (by simp)) p7) fun σ8 e8 p8 => ?_
  have E8 := E7.trans e8 (by omega) (by omega)
  -- the final evaluations
  refine CompletesB.append (m := 2273) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (c_s8C hM hA σ8 p8) fun σ9 e9 ⟨q9a, q9b, q9c, q9d⟩ => ?_
  have E9 := E8.trans e9 (by omega) (by omega)
  have hZ9 : σ9 (.n 1014) = flZT CM.hm τ cv xs :=
    e9.get (by omega) (e8.get (by omega) (e7.get (by omega) (e6.get (by omega) (e5.get (by omega)
      (e4.get (by omega) hZ)))))
  -- the lower numerators
  refine CompletesB.append (m := 2719) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    ((c_lag (n := 446) (b := 0) (by omega) (by omega)
      (by rw [lag64V_length, lgLen_lo.1, lgLen_lo.2]) σ9 hZ9).toBC lag64_lo_free)
    fun σ10 e10 p10 => ?_
  rw [lgOut_lo] at p10
  have E10 := E9.trans e10 (by omega) (by omega)
  -- alpha
  refine CompletesB.append (m := 2741) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (c_s10C hA mv σ10 (e10.get (by omega) q9a) (e10.get (by omega) q9b)
      (Prod.ext (e10.get (by omega) (congrArg Prod.fst q9c))
        (e10.get (by omega) (congrArg Prod.snd q9c)))
      (e10.get (by omega) q9d)) fun σ11 e11 p11' => ?_
  have E11 := E10.trans e11 (by omega) (by omega)
  have g2240 : σ11 (.n 2240) = cur * gen ^ (64 + 2 * (τ + 8)) :=
    e11.get (by omega) (e10.get (by omega) (e9.get (by omega) (p8.get (by simp [flP7OutC]))))
  -- the lincheck
  refine CompletesB.append (m := 3133) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (CompletesB.flatten (st := lcB) (Inv := LcInvC CM.hm τ cv xs cur lrs) 8
      (fun i _ => by simp only [lcB]; omega)
      (fun i hi => numBelow_of_B (by revert i hi; decide +kernel))
      (fun i hi σ hI => c_lcC hM hA hi σ hI) σ11
      ⟨fixes_two (E11.get (by omega) (a0 5 (by omega) _ (by simp [flArgs]))) g2240,
        p11'.get (k := 2740) (e := (flSt0'T CM.hm τ cv xs).1) (by simp [flS10OutC]),
        Prod.ext (p11'.get (k := 2725) (e := (digestScalars (flSt0'T CM.hm τ cv xs).2).1)
            (by simp [flS10OutC]))
          (p11'.get (k := 2726) (e := (digestScalars (flSt0'T CM.hm τ cv xs).2).2)
            (by simp [flS10OutC]))⟩)
    fun σ12 e12 ⟨p12a, p12b, p12c⟩ => ?_
  have E12 := E11.trans e12 (by omega) (by omega)
  -- the slices
  refine CompletesB.append (m := 4093) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (c_zpC hM hA hlen σ12 (fixes_two (E12.get (by omega) (a0 6 (by omega) _ (by simp [flArgs])))
      (e12.get (by omega) g2240)) p12c) fun σ13 e13 ⟨_, p13⟩ => ?_
  have E13 := E12.trans e13 (by omega) (by omega)
  have g2735 : σ13 (.n 2735) = flAlphaT CM.hm τ cv xs * flAlphaT CM.hm τ cv xs *
      flAlphaT CM.hm τ cv xs :=
    e13.get (by omega) (e12.get (by omega) (p11'.get (by simp [flS10OutC])))
  -- the pin term
  refine CompletesB.append (m := 4125) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    ((c_p13 (rc := lcChT CM.hm (flG' τ xs) (flSt0'T CM.hm τ cv xs)) hM.rcs
      (by simpa using hM.sl 0 (by omega)) σ13
      (E13.get (by omega) (a0 5 (by omega) _ (by simp [flArgs])))
      (E13.get (by omega) (a0 6 (by omega) _ (by simp [flArgs]))) g2735).toBC flP13_free)
    fun σ14 e14 p14 => ?_
  have E14 := E13.trans e14 (by omega) (by omega)
  -- the points' equality
  refine CompletesB.append (m := 4172) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    ((c_cpe (chi := scChT CM.hm (flET CM.hm τ cv) (flG xs) (flSt0T CM.hm τ cv xs))
      (fun t ht => hM.chis t (by omega))
      hM.rcs σ14 ⟨fixes_two (E14.get (by omega) (a0 4 (by omega) _ (by simp [flArgs])))
        (E14.get (by omega) (a0 5 (by omega) _ (by simp [flArgs]))),
          fun h => absurd h (by omega)⟩).toBC cpe_free)
    fun σ15 e15 ⟨_, p15⟩ => ?_
  have E15 := E14.trans e15 (by omega) (by omega)
  have p15' := p15 (by omega)
  simp only [Nat.reduceEqDiff, ↓reduceIte, Nat.reduceMul, Nat.reduceAdd] at p15'
  -- the slices' sum
  refine CompletesB.append (m := 4363) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    ((c_cs (z := flZT CM.hm τ cv xs) (s := fun i => xs.getD (82 + 2 * (τ + 8) + i) 0) hM.sl σ15
      ⟨(fun p hp => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        subst hp
        exact E15.get (by omega) (a0 6 (by omega) _ (by simp [flArgs]))),
        e15.get64 (by omega) (e14.get64 (by omega) (e13.get64 (by omega) (e12.get64 (by omega)
          (e11.get64 (by omega) p10)))), fun h => absurd h (by omega)⟩).toBC cs_free)
    fun σ16 e16 ⟨_, _, p16⟩ => ?_
  have p16' := p16 (by omega)
  simp only [Nat.reduceEqDiff, ↓reduceIte, Nat.reduceMul, Nat.reduceAdd] at p16'
  -- the final check and the returns
  have p6b' : σ7 (.n 1851) = gen ^ τ * word 16384 0 0 * word 2017612633061982209 0 0 :=
    e7.get (by omega) p6b
  have fx0 : ∀ {σa σb : Val} {lo hi : ℕ}, Fixes σa (flP0OutC CM.hm τ cv p11 p24 p40) →
      Ext lo hi σa σb → 41 ≤ lo → Fixes σb (flP0OutC CM.hm τ cv p11 p24 p40) := fun h he hlo =>
    h.of_ext he (by simp [flP0OutC]; omega)
  have fx7 : ∀ {σa σb : Val} {lo hi : ℕ} {v : E}, Fixes σa (flP7OutC CM.hm τ cv xs cur p2220 v) →
      Ext lo hi σa σb → 2241 ≤ lo → Fixes σb (flP7OutC CM.hm τ cv xs cur p2220 v) :=
    fun h he hlo => h.of_ext he (by simp [flP7OutC]; omega)
  have t13 : ∀ {k : ℕ} {v : E}, k < 4093 → σ13 (.n k) = v → σ16 (.n k) = v := fun hk h =>
    e16.get (by omega) (e15.get (by omega) (e14.get (by omega) h))
  have t11 : ∀ {k : ℕ} {v : E}, k < 2741 → σ11 (.n k) = v → σ16 (.n k) = v := fun hk h =>
    t13 (by omega) (e13.get (by omega) (e12.get (by omega) h))
  refine ((c_end (mv := mv) (z := flZT CM.hm τ cv xs) (α := flAlphaT CM.hm τ cv xs) σ16
    (t13 (by omega) (e13.get (by omega) (p12b.trans (flTerm_guestC CM.hm hlen hterm))))
    p16' (t11 (by omega) (p11'.get (k := 2719) (e := mv) (by simp [flS10OutC])))
    (e16.get (by omega) (e15.get (by omega) p14))
    (t11 (by omega) (p11'.get (k := 2734) (e := flAlphaT CM.hm τ cv xs * flAlphaT CM.hm τ cv xs)
      (by simp [flS10OutC])))
    (e16.get (by omega) p15')
    (t13 (by omega) (congrArg Prod.fst p13)) (t13 (by omega) (congrArg Prod.snd p13))
    (t11 (by omega) g2240)
    (t11 (by omega) (e11.get (by omega) (e10.get (by omega) hZ9)))
    (t11 (by omega) (p11'.get (k := 2733) (e := flAlphaT CM.hm τ cv xs)
      (by simp [flS10OutC])))).toBC flPEnd_free).withExt.mono
    le_rfl le_rfl fun σ' ⟨h, he⟩ => ⟨by rw [h], (fx0 (fx0 (fx0 (fx0 (fx0 (fx0 (fx0 (fx0 (fx0 (fx0
      (fx0 (fx0 (fx0 (fx0 (fx0 (fx0 p1 e2 (by omega)) e3 (by omega)) e4 (by omega)) e5 (by omega))
      e6 (by omega)) e7 (by omega)) e8 (by omega)) e9 (by omega)) e10 (by omega)) e11 (by omega))
      e12 (by omega)) e13 (by omega)) e14 (by omega)) e15 (by omega)) e16 (by omega)) he
      (by omega)),
    (fx7 (fx7 (fx7 (fx7 (fx7 (fx7 (fx7 (fx7 (fx7 (by rw [← p6b']; exact p8) e9 (by omega)) e10
      (by omega)) e11 (by omega)) e12 (by omega)) e13 (by omega)) e14 (by omega)) e15 (by omega))
      e16 (by omega)) he (by omega))⟩

/-- **`verify_flock` holds over a completeness model** (`verify_flock_rel`) on the honest memory
of the run on `cv` and `xs` at the total hash, the run's hashes answered, the matrices' value
`mv` passing the terminal check. -/
theorem verify_flock_relC (hτ : τ < 29)
    (hM : FlMemC CM.hm rd τ cv xs cur zchis lrs zpart p11 p24 p40 p2220) (hA : FlAns CM.hm τ cv xs)
    (hlen : xs.length = flLen τ) {mv : E} (hterm : flTermT CM.hm τ cv xs mv) :
    coreProgram.RelB CM.sem rd "verify_flock"
      [(digestScalars cv).1, (digestScalars cv).2, cur, gen ^ τ, zchis, lrs, zpart]
      [(digestScalars (obsAllT CM.hm (flLcT CM.hm τ cv xs).2 (flS τ xs))).1,
        (digestScalars (obsAllT CM.hm (flLcT CM.hm τ cv xs).2 (flS τ xs))).2, cur * gen ^ flLen τ,
        flZT CM.hm τ cv xs, flAlphaT CM.hm τ cv xs, mv] := by
  rw [relB_iff_sem find_verify_flock, core12_body, core12_params]
  set args := [(digestScalars cv).1, (digestScalars cv).2, cur, gen ^ τ, zchis, lrs, zpart]
  obtain ⟨σ', he, hp, hh⟩ := flock_body_completeC hτ hM hA hlen hterm (Val.ofArgs args) (by
    intro p hp
    simp only [flArgs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  refine ⟨σ', ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil]
    rw [he.apply (Or.inl (by omega)), he.apply (Or.inl (by omega)), he.apply (Or.inl (by omega)),
      he.apply (Or.inl (by omega)), he.apply (Or.inl (by omega)), he.apply (Or.inl (by omega)),
      he.apply (Or.inl (by omega))]
    rfl
  · rw [holdsListB_append]
    refine hh _ _ ?_
    simp only [flRet, Stmt.HoldsListB, Stmt.HoldsB, List.map_cons, List.map_nil]
    rw [hp.1, mul_assoc, ← pow_add, show 64 + 2 * (τ + 8) + 82 = flLen τ by unfold flLen; omega]

end

/-! ## `verify_flock`'s completeness over a completeness model -/

/-- The buffers `verify_flock` allocates hold the honest words of the run on `cv` and `xs` at the
total hash (`FlBufs`). -/
structure FlBufsC (M : HashModel) (rd : Reader) (τ : ℕ) (cv : Digest) (xs : List E)
    (cur p11 p24 p40 p2220 : E) : Prop where
  zr : ∀ j < τ + 8, LoadHolds rd p11 (6 + j) (flET M τ cv j)
  pts : ∀ t ≤ τ + 1, LoadHolds rd p24 (26 + 2 * t) (digestScalars ((sqCvT M)^[t] cv)).1 ∧
    LoadHolds rd p24 (27 + 2 * t) (digestScalars ((sqCvT M)^[t] cv)).2
  p1 : ∀ i < 64, LoadHolds rd p40 i (xs.getD i 0)
  rnd : ∀ j, 7 ≤ j → j ≤ τ + 8 →
    LoadHolds rd p2220 (4 * j) (digestScalars (flScAtT M τ cv xs j).2).1 ∧
    LoadHolds rd p2220 (4 * j + 1) (digestScalars (flScAtT M τ cv xs j).2).2 ∧
    LoadHolds rd p2220 (4 * j + 2) (cur * gen ^ (64 + 2 * j)) ∧
    LoadHolds rd p2220 (4 * j + 3) (flScAtT M τ cv xs j).1

/-- **`verify_flock`'s honest memory at a hash model's total hash** (`FlockMem`). -/
def FlockMemC (M : HashModel) (rd : Reader) : List E → List E → List E → Prop
  | [p11, p24, p40, p2220], [fs0, fs1, cur, gt, _, _, _], _ =>
      ∃ (τ : ℕ) (cv : Digest) (xs : List E), τ < 29 ∧ gt = gen ^ τ ∧ (fs0, fs1) = digestScalars cv ∧
        ReadsAt rd cur xs ∧ xs.length = flLen τ ∧ FlBufsC M rd τ cv xs cur p11 p24 p40 p2220
  | _, _, _ => False

theorem flockEv_atM (M : HashModel) (alpha zSkip : E) (chiIn chiInPrime s : List E) (mv : E) :
    MatricesAtM M (flockEv alpha zSkip chiIn chiInPrime s mv) alpha zSkip chiIn chiInPrime s mv := by
  intro st
  simp [flockEv, Prog.require]
  rfl

end
end LeanVM.Guest.B1

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.E2E.Complete

@[expose] public section

/-- **`verify_flock` is complete over its honest scratch `FMem`, over a completeness model**
(`CompleteFlock` over `CM`): from an answered run, the relation under the model's semantics. -/
def CompleteFlockC (CM : CompModel) (rd : Reader)
    (FMem : Reader → List E → List E → List E → Prop) : Prop :=
  ∀ ptrs τ fs0 fs1 cur zchis lrs zpart rets, τ < 29 →
    FlockOutM CM.hm rd τ fs0 fs1 cur zchis lrs zpart rets →
    FMem rd ptrs [fs0, fs1, cur, gen ^ τ, zchis, lrs, zpart] rets →
      coreProgram.RelB CM.sem rd "verify_flock" [fs0, fs1, cur, gen ^ τ, zchis, lrs, zpart] rets

end
end LeanVM.Guest.B1.VerifySub

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.Guest.B1.Sig LeanVM.E2E.Complete

@[expose] public section

/-- **`verify_flock` is complete over a completeness model** (`verify_flock_complete` over `CM`):
`CompleteFlockC` over `FlockMemC CM.hm`. -/
theorem verify_flock_completeC (CM : CompModel) (rd : Reader) :
    CompleteFlockC CM rd (FlockMemC CM.hm) := by
  intro ptrs τ fs0 fs1 cur zchis lrs zpart rets hτ hout hmem
  obtain ⟨cv, xs, cv', zSkip, alpha, mv, chi, rcs, s, hcv, hxs, hcl, hrl, hsl, hchi, hrc, hs, hrun,
    hret⟩ := hout
  obtain ⟨hlen, hz, ha, hchiE, hrcE, hsE, hterm, hcv', hA⟩ :=
    flock_invC (hrun _ (flockEv_atM CM.hm alpha zSkip (chi.take 8) rcs.reverse s mv))
  match ptrs, hmem with
  | [p11, p24, p40, p2220], ⟨τ', cv0, xs0, hτ', hgt, hcv0, hxs0, hlen0, hB⟩ => ?_
  obtain rfl : τ' = τ := (gen_pow_inj' (by omega) (by omega) hgt).symm
  obtain rfl : cv0 = cv := digestScalars_injective (hcv0.symm.trans hcv)
  obtain rfl : xs0 = xs := readsAt_unique hxs0 hxs (by rw [hlen0, hlen])
  have hM : FlMemC CM.hm rd τ' cv0 xs0 cur zchis lrs zpart p11 p24 p40 p2220 :=
    { words := fun k hk => readsAt_iff_getD.mp hxs k (by omega)
      zr := hB.zr
      pts := hB.pts
      p1 := hB.p1
      rnd := hB.rnd
      chis := fun j hj => by
        have := readsAt_iff_getD.mp hchi j (by omega)
        rwa [hchiE, flChiT, getD_map_range _ _ hj] at this
      rcs := fun j hj => by
        have := readsAt_iff_getD.mp hrc j (by omega)
        rwa [hrcE, flRcT, getD_map_range _ _ hj] at this
      sl := fun i hi => by
        have := readsAt_iff_getD.mp hs i (by omega)
        rwa [hsE, flS_getD τ' xs0 hi] at this }
  rw [hret, hcv', hz, ha, hlen, show fs0 = (digestScalars cv0).1 from congrArg Prod.fst hcv,
    show fs1 = (digestScalars cv0).2 from congrArg Prod.snd hcv]
  exact verify_flock_relC hτ hM hA hlen hterm

end
end LeanVM.Guest.B1

/-! ## At the deployed model -/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.Guest.B1.Sig LeanVM.E2E.Complete

@[expose] public section

theorem scStT_hm_deployed (e : ℕ → E) (g : ℕ → E × E) (s0 : E × Digest) :
    ∀ j, scStT CompModel.deployed.hm e g s0 j = scSt e g s0 j
  | 0 => rfl
  | j + 1 => by rw [scStT, scSt, scStT_hm_deployed e g s0 j]; rfl

theorem scChT_hm_deployed (e : ℕ → E) (g : ℕ → E × E) (s0 : E × Digest) (j : ℕ) :
    scChT CompModel.deployed.hm e g s0 j = scCh e g s0 j := by
  rw [scChT, scCh, scStT_hm_deployed]; rfl

theorem scChT_hm_deployed' (e : ℕ → E) (g : ℕ → E × E) (s0 : E × Digest) :
    scChT CompModel.deployed.hm e g s0 = scCh e g s0 := funext (scChT_hm_deployed e g s0)

theorem lcStT_hm_deployed (g : ℕ → E × E) (s0 : E × Digest) :
    ∀ j, lcStT CompModel.deployed.hm g s0 j = lcSt g s0 j
  | 0 => rfl
  | j + 1 => by rw [lcStT, lcSt, lcStT_hm_deployed g s0 j]; rfl

theorem lcChT_hm_deployed (g : ℕ → E × E) (s0 : E × Digest) (j : ℕ) :
    lcChT CompModel.deployed.hm g s0 j = lcCh g s0 j := by
  rw [lcChT, lcCh, lcStT_hm_deployed]; rfl

theorem lcChT_hm_deployed' (g : ℕ → E × E) (s0 : E × Digest) :
    lcChT CompModel.deployed.hm g s0 = lcCh g s0 := funext (lcChT_hm_deployed g s0)

section
variable (τ : ℕ) (cv : Digest) (W : List E)

theorem flSamT_hm_deployed : flSamT CompModel.deployed.hm τ cv = (sqAll (τ + 1) cv).1 := by
  rw [sqAll_eq]; rfl

theorem flCvST_hm_deployed : flCvST CompModel.deployed.hm τ cv = flCvS τ cv := by
  rw [flCvS, sqAll_eq]; rfl

theorem flET_hm_deployed : flET CompModel.deployed.hm τ cv = flE τ cv := by
  funext j; simp only [flET, flE, flSamT_hm_deployed]

theorem flZT_hm_deployed : flZT CompModel.deployed.hm τ cv W = flZ τ cv W := by
  simp only [flZT, flZ, flCvPT, flCvST_hm_deployed]; rfl

theorem flSt0T_hm_deployed : flSt0T CompModel.deployed.hm τ cv W = flSt0 τ cv W := by
  simp only [flSt0T, flSt0, flZT_hm_deployed, flCvPT, flCvST_hm_deployed]; rfl

theorem flScT_hm_deployed : flScT CompModel.deployed.hm τ cv W = flSc τ cv W := by
  simp only [flScT, flSc, scStT_hm_deployed, flET_hm_deployed, flSt0T_hm_deployed]

theorem flScAtT_hm_deployed (j : ℕ) : flScAtT CompModel.deployed.hm τ cv W j = flScAt τ cv W j := by
  simp only [flScAtT, flScAt, scStT_hm_deployed, flET_hm_deployed, flSt0T_hm_deployed]

theorem flCv5T_hm_deployed : flCv5T CompModel.deployed.hm τ cv W = flCv5 τ cv W := by
  simp only [flCv5T, flCv4T, flCv5, flScT_hm_deployed]; rfl

theorem flAlphaT_hm_deployed : flAlphaT CompModel.deployed.hm τ cv W = flAlpha τ cv W := by
  simp only [flAlphaT, flAlpha, flCv5T_hm_deployed]; rfl

theorem flSt0'T_hm_deployed : flSt0'T CompModel.deployed.hm τ cv W = flSt0' τ cv W := by
  simp only [flSt0'T, flSt0', flAlphaT_hm_deployed, flScT_hm_deployed, flCv5T_hm_deployed]; rfl

theorem flLcT_hm_deployed : flLcT CompModel.deployed.hm τ cv W = flLc τ cv W := by
  simp only [flLcT, flLc, lcStT_hm_deployed, flSt0'T_hm_deployed]

theorem flChiT_hm_deployed : flChiT CompModel.deployed.hm τ cv W = flChi τ cv W := by
  simp only [flChiT, flChi, scChT_hm_deployed', flET_hm_deployed, flSt0T_hm_deployed]

theorem flRcT_hm_deployed : flRcT CompModel.deployed.hm τ cv W = flRc τ cv W := by
  simp only [flRcT, flRc, lcChT_hm_deployed', flSt0'T_hm_deployed]

theorem flTermT_hm_deployed (mv : E) :
    flTermT CompModel.deployed.hm τ cv W mv ↔ flTerm τ cv W mv := by
  simp only [flTermT, flTerm, flAlphaT_hm_deployed, flChiT_hm_deployed, flRcT_hm_deployed,
    flZT_hm_deployed, flLcT_hm_deployed]

/-- **At the deployed model every hash of the run is answered.** -/
theorem flAns_hm_deployed : FlAns CompModel.deployed.hm τ cv W :=
  ⟨fun t _ => by rw [Function.iterate_succ_apply']; rfl, obsAns_hm_deployed _ _, rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl,
    fun _ _ => ⟨rfl, rfl, rfl⟩, obsAns_hm_deployed _ _⟩

end

section
variable {rd : Reader} {τ : ℕ} {cv : Digest} {xs : List E}
  {cur zchis lrs zpart p11 p24 p40 p2220 : E}

theorem flMemC_of_flMem (hM : FlMem rd τ cv xs cur zchis lrs zpart p11 p24 p40 p2220) :
    FlMemC CompModel.deployed.hm rd τ cv xs cur zchis lrs zpart p11 p24 p40 p2220 where
  words := hM.words
  zr := by rw [flET_hm_deployed]; exact hM.zr
  pts := hM.pts
  p1 := hM.p1
  rnd := by simp only [flScAtT_hm_deployed]; exact hM.rnd
  chis := by
    simp only [scChT_hm_deployed, flET_hm_deployed, flSt0T_hm_deployed]; exact hM.chis
  rcs := by simp only [lcChT_hm_deployed, flSt0'T_hm_deployed]; exact hM.rcs
  sl := hM.sl

theorem flockMemC_of_flockMem {ptrs args rets : List E} (h : FlockMem rd ptrs args rets) :
    FlockMemC CompModel.deployed.hm rd ptrs args rets := by
  match ptrs, args, h with
  | [p11, p24, p40, p2220], [fs0, fs1, cur, gt, _, _, _], ⟨τ, cv, xs, hτ, hgt, hcv, hxs, hlen, hB⟩ =>
    exact ⟨τ, cv, xs, hτ, hgt, hcv, hxs, hlen,
      { zr := by rw [flET_hm_deployed]; exact hB.zr
        pts := hB.pts
        p1 := hB.p1
        rnd := by simp only [flScAtT_hm_deployed]; exact hB.rnd }⟩

/-- `__loop81`'s deployed completeness (`loop81_complete`), from the model's. -/
theorem loop81_complete_of_comp (hτ : τ < 29)
    (hM : FlMem rd τ cv xs cur zchis lrs zpart p11 p24 p40 p2220) :
    coreProgram.Rel rd "__loop81" [gen ^ 13, gen ^ (τ + 14), p24, p11] [] := by
  rw [← relB_deployed]
  exact loop81_completeC (CM := CompModel.deployed) hτ (flMemC_of_flMem hM) (flAns_hm_deployed ..)

/-- `__loop82`'s deployed completeness (`loop82_complete`), from the model's. -/
theorem loop82_complete_of_comp (hτ : τ < 29)
    (hM : FlMem rd τ cv xs cur zchis lrs zpart p11 p24 p40 p2220) :
    coreProgram.Rel rd "__loop82" [gen ^ 7, gen ^ (τ + 8), p2220, p11, zchis] [] := by
  rw [← relB_deployed]
  exact loop82_completeC (CM := CompModel.deployed) hτ (flMemC_of_flMem hM) (flAns_hm_deployed ..)

/-- `verify_flock`'s deployed relation on the honest memory (`verify_flock_rel`), from the
model's. -/
theorem verify_flock_rel_of_comp (hτ : τ < 29)
    (hM : FlMem rd τ cv xs cur zchis lrs zpart p11 p24 p40 p2220)
    (hlen : xs.length = flLen τ) {mv : E} (hterm : flTerm τ cv xs mv) :
    coreProgram.Rel rd "verify_flock"
      [(digestScalars cv).1, (digestScalars cv).2, cur, gen ^ τ, zchis, lrs, zpart]
      [(digestScalars (obsAll (flLc τ cv xs).2 (flS τ xs))).1,
        (digestScalars (obsAll (flLc τ cv xs).2 (flS τ xs))).2, cur * gen ^ flLen τ, flZ τ cv xs,
        flAlpha τ cv xs, mv] := by
  rw [← relB_deployed, ← flLcT_hm_deployed, ← flZT_hm_deployed, ← flAlphaT_hm_deployed,
    ← obsAllT_hm_deployed]
  exact verify_flock_relC (CM := CompModel.deployed) hτ (flMemC_of_flMem hM)
    (flAns_hm_deployed ..) hlen ((flTermT_hm_deployed τ cv xs mv).mpr hterm)

/-- **`verify_flock`'s deployed completeness** (`verify_flock_complete`), from the model's:
`CompleteFlock rd FlockMem`. -/
theorem verify_flock_complete_of_comp (rd : Reader) : CompleteFlock rd FlockMem := by
  intro ptrs τ fs0 fs1 cur zchis lrs zpart rets hτ hout hmem
  rw [← relB_deployed]
  exact verify_flock_completeC CompModel.deployed rd ptrs τ fs0 fs1 cur zchis lrs zpart rets hτ
    ((flockOutM_deployed (rd := rd)).mpr hout) (flockMemC_of_flockMem hmem)

end

end
end LeanVM.Guest.B1
