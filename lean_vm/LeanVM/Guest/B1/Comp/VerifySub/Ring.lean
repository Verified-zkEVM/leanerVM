/-
  LeanVM.Guest.B1.Comp.VerifySub.Ring

  `verify_sub`'s ring switch over a completeness model: the map's challenges from the model's
  squeezes, `c_table`, the target and `z_vals`.
-/

module

public import LeanVM.Guest.B1.Comp.VerifySub.Bus
public import LeanVM.Guest.B1.VerifySub.CRing

/-!
# The ring switch over a completeness model (G:2170-2210)

`VerifySub/CRing.lean` over a `CompModel`. The map's challenges are the model's squeezes from
Flock's state: a family of states `st` with `st 0 = D.cvF`, the challenges `mcsOf st` (the
deployed `D.mcs` at `st k = sqCv^[k] D.cvF`, `mcs_eq`), the state after them `st 6` (`D.cvM`).
`c_table`'s stages (`c_ctSlotG`, `c_ctStageG`) and `rs_chain` (`rsChainC`, `rsSumC`) are the
deployed ones at any challenges; `c_ring_comp` is `c_ring`, and `c_ring_of_comp` recovers it at
`CompModel.deployed`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig LeanVM.E2E.Complete

@[expose] public section

variable {C : CallRel} {rd : Reader} {D : VsData} {P : VsPtrs} {out : E}

/-! ## `c_table` at any challenges -/

/-- **Slot `sl` of stage `st` of `c_table`** (G:2183-2188, `c_ctSlot`), at any challenges `mcs`. -/
theorem c_ctSlotG (mcs : List E) (hl : mcs.length = 6) {st sl : ℕ} (hst : st < 6) (hsl : sl < 2 ^ st)
    (hct : ReadsAt rd P.ctab (ringCoefficients mcs)) (σ : Val) (h733 : σ (.n 733) = P.ctab)
    (hc : σ (.n (ctV st)) = mcs.getD st 0) (hlt : 733 < ctV st) :
    Completes C rd (ctV st + 1 + sl * (ctD st + 2))
      (ctV st + 1 + sl * (ctD st + 2) + (ctD st + 2)) (ctSlot st sl) σ
      (fun σ' => σ' (.n 733) = P.ctab ∧ σ' (.n (ctV st)) = mcs.getD st 0) := by
  set u := ctV st + 1 + sl * (ctD st + 2)
  obtain ⟨h0, h1⟩ := ctab_at mcs hl hst hsl
  have hrc : ∀ k < 64, LoadHolds rd P.ctab k ((ringCoefficients mcs).getD k 0) := fun k hk => by
    rw [List.getD_eq_getElem _ _ (by simpa [ringCoefficients, kBits] using hk)]
    exact hct k (by simpa [ringCoefficients, kBits] using hk)
  obtain ⟨hd0, -, -, hd3⟩ := ctD_facts st hst
  have hlt64 : sl * (2 * ctD st) + ctD st < 64 := by
    have : (sl + 1) * (2 * ctD st) ≤ 2 ^ st * (2 * ctD st) := Nat.mul_le_mul_right _ (by omega)
    rw [hd3] at this; nlinarith
  refine completes_setv (ctVals mcs st sl) (fun next kret hn => ?_) ?_
  · rw [ctSlot, holdsList_append, holdsList_append]
    have hs : ∀ i ≤ ctD st, setv σ u (ctD st + 2) (ctVals mcs st sl) (.n (u + i)) =
        ctTab mcs st (sl * (2 * ctD st)) ^ 2 ^ i := fun i hi => by
      rw [set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]; simp [ctVals, hi]
    have hlast : setv σ u (ctD st + 2) (ctVals mcs st sl) (.n (u + ctD st + 1)) =
        mcs.getD st 0 * ctTab mcs st (sl * (2 * ctD st)) ^ 2 ^ ctD st := by
      rw [set_n_in (by omega) (by omega), show u + ctD st + 1 - u = ctD st + 1 by omega]
      simp [ctVals]
    have e733 : setv σ u (ctD st + 2) (ctVals mcs st sl) (.n 733) = P.ctab := by
      rw [set_n_lt (by omega)]; exact h733
    have ec : setv σ u (ctD st + 2) (ctVals mcs st sl) (.n (ctV st)) = mcs.getD st 0 := by
      rw [set_n_lt (by omega)]; exact hc
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
    refine ⟨?_, ?_⟩
    · have hs0 := hs 0 (by omega)
      simp only [Nat.add_zero, pow_zero, pow_one] at hs0
      rw [e733]
      change LoadHolds rd P.ctab (sl * (2 * ctD st)) (setv σ u (ctD st + 2) (ctVals mcs st sl) (.n u))
      rw [hs0, ← h0]
      exact hrc _ (by omega)
    · rw [holdsList_noRet _ (sqChain_noRet _ _)]
      refine ⟨holds_sqChain_complete u (ctD st) _ hs, ?_, ?_, hn⟩
      · rw [hlast, ec, hs (ctD st) le_rfl]
      · rw [e733, hlast, ← h1]; exact hrc _ hlt64
  · refine ⟨?_, ?_⟩
    · rw [set_n_lt (by omega)]; exact h733
    · rw [set_n_lt (by omega)]; exact hc

/-- **Stage `st` of `c_table`** (G:2181-2189, `c_ctStage`), at any challenges `mcs`. -/
theorem c_ctStageG (mcs : List E) (hl : mcs.length = 6) {st : ℕ} (hst : st < 6)
    (hct : ReadsAt rd P.ctab (ringCoefficients mcs)) (hm : LoadHolds rd P.mcs st (mcs.getD st 0))
    (σ : Val) (h732 : σ (.n 732) = P.mcs) (h733 : σ (.n 733) = P.ctab) :
    Completes C rd (ctV st) (ctV (st + 1)) (ctStage st) σ
      (fun σ' => σ' (.n 732) = P.mcs ∧ σ' (.n 733) = P.ctab) := by
  have hge := ctV_ge st (by omega)
  rw [ctStage, ← List.singleton_append, ctV_succ]
  refine Completes.append (m := ctV st + 1) (P := fun σ' => σ' (.n 732) = P.mcs ∧
      σ' (.n 733) = P.ctab ∧ σ' (.n (ctV st)) = mcs.getD st 0) (by omega) (by omega)
    (numBelow_of_B (by simp [numBelowB, Stmt.vals, Atom.vals]; omega)) ?_ fun σ1 _ ⟨i732, i733, ic⟩ => ?_
  · refine completes_upds [(ctV st, mcs.getD st 0)] (by simp) (fun next kret hn => ?_) ?_
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, upds_n, upds_nil,
        show (732 : ℕ) ≠ ctV st by omega, ↓reduceIte, h732]
      exact ⟨hm, hn⟩
    · simp only [upds_n, upds_nil, show (732 : ℕ) ≠ ctV st by omega,
        show (733 : ℕ) ≠ ctV st by omega, ↓reduceIte, h732, h733]
      exact ⟨trivial, trivial, trivial⟩
  · have key := Completes.flatten (C := C) (rd := rd) (blk := ctSlot st)
      (st := fun sl ↦ ctV st + 1 + sl * (ctD st + 2)) (Inv := fun _ σ' ↦ σ' (.n 732) = P.mcs ∧
        σ' (.n 733) = P.ctab ∧ σ' (.n (ctV st)) = mcs.getD st 0) (2 ^ st)
      (fun sl _ => by show _ + sl * _ ≤ _ + (sl + 1) * _; rw [Nat.succ_mul]; omega) (numBelow_ctSlot st hst)
      (fun sl hsl σ' ⟨j732, j733, jc⟩ => by
        have c := (c_ctSlotG (C := C) mcs hl hst hsl hct σ' j733 jc (by omega)).keep (l := [(732, P.mcs)])
          (by intro p hp; simp at hp; subst hp; exact j732) (by simp; omega)
        rw [show ctV st + 1 + (sl + 1) * (ctD st + 2) = ctV st + 1 + sl * (ctD st + 2) + (ctD st + 2)
          by ring]
        exact c.post fun σ'' _ ⟨⟨k733, kc⟩, kf⟩ => ⟨kf.get (by simp), k733, kc⟩) σ1 ⟨i732, i733, ic⟩
    simp only [Nat.zero_mul, Nat.add_zero] at key
    exact key.post fun σ' _ ⟨k1, k2, _⟩ => ⟨k1, k2⟩

/-! ## `rs_chain` -/




theorem ctStage_free : ∀ st < 6, Stmt.freeInList [] (ctStage st) = true := by decide +kernel

/-! ## `rs_chain` at any challenges -/

/-- The running sum of `rs_chain`'s row `j` at the challenges `mcs` (`rsSum`). -/
def rsSumC (s mcs : List E) (j : ℕ) : E :=
  ((List.range j).map fun i ↦ phiMap (s.getD i 0) mcs * gen ^ i).sum

/-- `rs_chain` at the challenges `mcs` (`VsData.rsChain`). -/
def rsChainC (s mcs : List E) : List E :=
  (List.range 65).flatMap fun j ↦ [gen ^ j, rsSumC s mcs j]

theorem rsChainC_deployed : rsChainC D.s D.mcs = D.rsChain := rfl

theorem rsChainC_at (s mcs : List E) {j : ℕ} (hj : j ≤ 64) :
    (rsChainC s mcs).getD (2 * j) 0 = gen ^ j ∧ (rsChainC s mcs).getD (2 * j + 1) 0 = rsSumC s mcs j ∧
      (rsChainC s mcs).length = 130 :=
  getD_flatMap_pair _ _ 65 j (by omega)

theorem rsSumC_target {s mcs : List E} (hs : s.length = 64) : rsSumC s mcs 64 = ringTarget s mcs := by
  rw [ringTarget, polyEval_eq_sum, List.length_map, hs, rsSumC]
  refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
  have hi' : i < 64 := by simpa using hi
  rw [List.getD_eq_getElem _ _ (by simpa [hs] using hi'), List.getD_eq_getElem _ _ (by simpa [hs] using hi'),
    List.getElem_map]

/-! ## The block -/

/-- The map's challenges from the states `st`. -/
def mcsOf (st : ℕ → Digest) : List E := (List.range 6).map fun k ↦ challengeOf (st (k + 1))

/-- The values the ring block leaves, its state `cvM` and challenges `mcs` given (`ringOut`). -/
def ringOutC (D : VsData) (P : VsPtrs) (cvM : Digest) (mcs : List E) : List (ℕ × E) :=
  [(810, (digestScalars cvM).1), (811, (digestScalars cvM).2), (1144, P.rs),
    (1149, P.rs * word 325 0 0), (1150, ringTarget D.s mcs), (1160, word 1 0 0 + gen ^ D.tau)]

theorem ringOutC_deployed : ringOutC D P D.cvM D.mcs = ringOut D P := rfl

/-- **The ring switch over a completeness model** (G:2170-2210, `c_ring`): from Flock's state
`st 0 = D.cvF`, the model's six squeezes give the map's challenges `mcsOf st`, then `c_table`, the
target, `z_vals`; the state after them `st 6`. -/
theorem c_ring_comp {CM : CompModel} {st : ℕ → Digest} (h0 : st 0 = D.cvF)
    (hsq : ∀ k < 6, sqCvM CM.hm (st k) = some (st (k + 1))) (hsl : D.s.length = 64)
    (hrl : D.rcs.length = 8) (hmcs : ReadsAt rd P.mcs (mcsOf st))
    (hct : ReadsAt rd P.ctab (ringCoefficients (mcsOf st)))
    (hrs : ReadsAt rd P.rs (rsChainC D.s (mcsOf st))) (hlrs : ReadsAt rd P.lrs D.rcs)
    (hzv : ReadsAt rd P.zvals D.fpoint) (h84 : C "__loop84" [word 1 0 0, P.zpart, P.mcs, P.rs] [])
    (h85 : D.tau ≠ 0 →
      C "__loop85" [word 1 0 0, gen ^ D.tau, P.zvals * word 256 0 0, P.zchis * word 256 0 0] [])
    (σ : Val) (hσ : Fixes σ (ringIn D P)) :
    CompletesB CM.sem C rd 735 1166 bRing σ (fun σ' => Fixes σ' (ringOutC D P (st 6) (mcsOf st))) := by
  have e : ∀ k e, (k, e) ∈ ringIn D P → σ (.n k) = e := fun k e h => hσ.get h
  have hmc : ∀ k < 6, LoadHolds rd P.mcs k (challengeOf (st (k + 1))) := fun k hk => by
    have := hmcs k (by simp [mcsOf]; omega)
    simp only [mcsOf, List.getElem_map, List.getElem_range] at this
    exact this
  have hl : (mcsOf st).length = 6 := by simp [mcsOf]
  set mcs := mcsOf st with hmcs_def
  have hmc' : ∀ k < 6, LoadHolds rd P.mcs k (mcs.getD k 0) := fun k hk =>
    readsAt_getD hmcs (by omega)
  rw [bRing_eq]
  refine CompletesB.append (m := 1159) (P := fun σ' => σ' (.n 1150) = ringTarget D.s mcs ∧
      Fixes σ' ([(810, (digestScalars (st 6)).1), (811, (digestScalars (st 6)).2), (1144, P.rs),
        (1149, P.rs * word 325 0 0)] ++ ringIn D P))
    (by omega) (by omega) (numBelow_of_B (by decide +kernel)) ?_ fun σ5 _ ⟨j1150, jf⟩ => ?tailF
  refine CompletesB.append (m := 1151) (P := fun σ' => σ' (.n 1150) = ringTarget D.s mcs ∧
      Fixes σ' ([(810, (digestScalars (st 6)).1), (811, (digestScalars (st 6)).2), (1144, P.rs),
        (1149, P.rs * word 325 0 0)] ++ ringIn D P))
    (by omega) (by omega) (numBelow_of_B (by decide +kernel)) ?_ fun σ4 _ ⟨j1150, jf⟩ => ?copies
  refine CompletesB.append (m := 1144) (P := fun σ' => (σ' (.n 732) = P.mcs ∧ σ' (.n 733) = P.ctab) ∧
      Fixes σ' ([(810, (digestScalars (st 6)).1), (811, (digestScalars (st 6)).2)] ++ ringIn D P))
    (by omega) (by omega) (numBelow_of_B (by decide +kernel)) ?_ fun σ3 _ ⟨⟨j732, j733⟩, jf⟩ => ?chain
  refine CompletesB.append (m := 820) (P := fun σ' => (σ' (.n 732) = P.mcs ∧ σ' (.n 733) = P.ctab) ∧
      Fixes σ' ([(810, (digestScalars (st 6)).1), (811, (digestScalars (st 6)).2)] ++ ringIn D P))
    (by omega) (by omega) (numBelow_of_B (by decide +kernel)) ?_ fun σ2 _ ⟨⟨j732, j733⟩, jf⟩ => ?stages
  refine CompletesB.append (m := 819) (P := fun σ' => (σ' (.n 732) = P.mcs ∧
      (σ' (.n 810), σ' (.n 811)) = digestScalars (st 6)) ∧ Fixes σ' (ringIn D P))
    (by omega) (by omega) (numBelow_of_B (by decide +kernel)) ?_ fun σ1 _ ⟨⟨j732, j810⟩, jf⟩ => ?ct0
  · -- the six challenges
    exact ((c_squeezes_comp (m := 6) (s0 := 730) (b0 := 735) (out := .n 732) (po := P.mcs) (st := st)
      (by omega) (by omega) ⟨732, by omega, rfl⟩ hsq hmc numBelow_sq732 σ (e 732 P.mcs (by simp [ringIn]))
      (by rw [e 730 (digestScalars D.cvF).1 (by simp [ringIn]),
        e 731 (digestScalars D.cvF).2 (by simp [ringIn]), h0])).keep hσ
      (by intro p hp; simp [ringIn] at hp; rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp)).post fun σ' _ ⟨⟨k1, k2⟩, kf⟩ => ⟨⟨k1, k2⟩, kf⟩
  case ct0 =>
    refine completesB_upds [(819, word 1 0 0)] (by simp) (fun next kret hn => ?_) ?_
    · simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB]
      vs_ev
      rw [jf.get (k := 733) (e := P.ctab) (by simp [ringIn]), word_one]
      have := (ctab_at mcs hl (st := 0) (sl := 0) (by omega) (by omega)).1
      simp only [Nat.zero_mul, ctTab, ↓reduceIte] at this
      exact ⟨trivial, by rw [← this]; exact readsAt_getD hct (by simp [ringCoefficients, kBits]),
        hn⟩
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · vs_ev; exact j732
      · vs_ev; exact jf.get (k := 733) (e := P.ctab) (by simp [ringIn])
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
          rcases hp with rfl | rfl <;> vs_ev
          · exact congrArg Prod.fst j810
          · exact congrArg Prod.snd j810
        · rw [upds_of_not_mem _ _ (by
            intro q hq; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq; subst hq
            simp only [ringIn, List.mem_cons, List.mem_nil_iff, or_false] at hp
            rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)]
          exact jf p hp
  case stages =>
    have key := CompletesB.flatten (S := CM.sem) (C := C) (rd := rd) (blk := ctStage) (st := ctV)
      (Inv := fun _ σ' ↦ σ' (.n 732) = P.mcs ∧ σ' (.n 733) = P.ctab) 6
      (fun st hst => by rw [ctV_succ]; omega) numBelow_ctStage
      (fun st hst σ' ⟨k1, k2⟩ => CompletesB.of_free (ctStage_free st hst) (c_ctStageG mcs hl hst hct (hmc' st hst) σ' k1 k2)) σ2 ⟨j732, j733⟩
    rw [ctV_six] at key
    exact key.keep jf (by intro p hp; simp [ringIn] at hp; rcases hp with rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ctV])
  case chain =>
    obtain ⟨a0, b0, hlen⟩ := rsChainC_at D.s mcs (j := 0) (by omega)
    obtain ⟨-, b64, -⟩ := rsChainC_at D.s mcs (j := 64) (by omega)
    have j723 : σ3 (.n 723) = P.zpart := jf.get (by simp [ringIn])
    refine ((completesB_upds [(1144, P.rs), (1145, word 1 0 0), (1146, word 0 0 0), (1147, word 1 0 0),
      (1148, word 325 0 0), (1149, P.rs * word 325 0 0), (1150, rsSumC D.s mcs 64)] (by simp)
      (fun next kret hn => ?_) (Post := fun σ' => σ' (.n 1150) = rsSumC D.s mcs 64 ∧ σ' (.n 1144) = P.rs ∧
        σ' (.n 1149) = P.rs * word 325 0 0)
      (by vs_ev; exact ⟨trivial, trivial, trivial⟩)).keep jf
      (by intro p hp; simp [ringIn] at hp; rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;> simp)).post fun σ' _ ⟨⟨k1, k3, k4⟩, k2⟩ =>
          ⟨by rw [k1, rsSumC_target hsl], fun p hp => by
            rcases List.mem_append.mp hp with hp | hp
            · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
              rcases hp with rfl | rfl | rfl | rfl
              · exact k2.get (by simp)
              · exact k2.get (by simp)
              · exact k3
              · exact k4
            · exact k2 p (List.mem_append_right _ hp)⟩
    simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil]
    vs_ev
    rw [j723, j732]
    refine ⟨trivial, trivial, ?_, trivial, ?_, trivial, ?_, trivial, trivial, ?_, hn⟩
    · have h0 : (rsChainC D.s mcs).getD 0 0 = 1 := by simpa using a0
      rw [word_one, ← h0]; exact readsAt_getD hrs (by rw [hlen]; omega)
    · rw [word_zero, show (0 : E) = (rsChainC D.s mcs).getD (2 * 0 + 1) 0 by rw [b0]; simp [rsSumC]]
      exact readsAt_getD hrs (by rw [hlen]; omega)
    · exact h84
    · rw [word325, loadHolds_mul_gen_pow, ← b64]
      exact readsAt_getD hrs (by rw [hlen]; omega)
  case copies =>
    have key := CompletesB.flatten (S := CM.sem) (C := C) (rd := rd)
      (blk := fun t ↦ [.atom (.load (.n (1151 + t)) (.n 722) (7 - t)),
        .atom (.load (.n (1151 + t)) (.n 734) t)]) (st := fun t ↦ 1151 + t)
      (Inv := fun _ σ' ↦ σ' (.n 722) = P.lrs ∧ σ' (.n 734) = P.zvals) 8 (fun _ _ => by omega)
      (fun t ht => numBelow_of_B (by revert t ht; decide +kernel)) (fun t ht σ' ⟨k1, k2⟩ => ?_) σ4
      ⟨jf.get (by simp [ringIn]), jf.get (by simp [ringIn])⟩
    · exact (key.keep (l := (1150, ringTarget D.s mcs) :: ([(810, (digestScalars (st 6)).1),
        (811, (digestScalars (st 6)).2), (1144, P.rs), (1149, P.rs * word 325 0 0)] ++ ringIn D P)) (fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hp
          · exact j1150
          · exact jf p hp)
        (by intro p hp; simp [ringIn] at hp; rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)).post fun σ' _ ⟨_, kf⟩ =>
        ⟨kf.get (by simp), fun p hp => kf p (List.mem_cons_of_mem _ hp)⟩
    · have hrv : D.fpoint.getD t 0 = D.rcs.getD (7 - t) 0 := by
        have hrl := hrl
        rw [VsData.fpoint, List.getD_eq_getElem _ _ (by simp [hrl]; omega),
          List.getElem_append_left (by simp [hrl]; omega), List.getElem_reverse,
          List.getD_eq_getElem _ _ (by omega)]
        simp only [hrl]
      refine completesB_upds [(1151 + t, D.rcs.getD (7 - t) 0)] (by simp) (fun next kret hn => ?_) ?_
      · simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, upds_n, upds_nil,
          show (722 : ℕ) ≠ 1151 + t by omega, show (734 : ℕ) ≠ 1151 + t by omega, ↓reduceIte, k1, k2]
        refine ⟨readsAt_getD hlrs (by rw [hrl]; omega), ?_, hn⟩
        rw [← hrv]; exact readsAt_getD hzv (by simp [VsData.fpoint, hrl]; omega)
      · simp only [upds_n, upds_nil, show (722 : ℕ) ≠ 1151 + t by omega,
          show (734 : ℕ) ≠ 1151 + t by omega, ↓reduceIte, k1, k2, and_self]
  case tailF =>
    have j718 : σ5 (.n 718) = gen ^ D.tau := jf.get (by simp [ringIn])
    have j721 : σ5 (.n 721) = P.zchis := jf.get (by simp [ringIn])
    have j734 : σ5 (.n 734) = P.zvals := jf.get (by simp [ringIn])
    have w8 : word 256 0 0 = gen ^ 8 := word_two_pow (a := 8) (by decide)
    refine completesB_upds [(1159, word 1 0 0), (1160, word 1 0 0 + gen ^ D.tau), (1161, word 1 0 0),
      (1162, word 256 0 0), (1163, P.zvals * word 256 0 0), (1164, word 256 0 0),
      (1165, P.zchis * word 256 0 0)] (by simp) (fun next kret hn => ?_) ?_
    · simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil]
      vs_ev
      rw [j718, j721, j734]
      refine ⟨by vs_triv, by vs_triv, by vs_triv, by vs_triv, by vs_triv, by vs_triv, by vs_triv, ?_, ?_,
        hn⟩
      · rw [word_one, ← pow_zero gen]; exact isInK_add (gen_pow_isInK 0) (gen_pow_isInK _)
      · intro hne
        refine h85 fun h => hne ?_
        rw [h, word_one, pow_zero, e_add_eq_zero_iff]
    · intro p hp
      simp only [ringOutC, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> vs_ev
      · exact jf.get (by simp)
      · exact jf.get (by simp)
      · exact jf.get (by simp)
      · exact jf.get (by simp)
      · exact j1150

/-- The deployed `c_ring`, from the model's at `CompModel.deployed`. -/
theorem c_ring_of_comp {bytecode : List K} {lp sq : E} (hok : D.Ok bytecode) (hm : VsMem0 rd D P out)
    (hC : VsCallsOk C bytecode D P lp sq) (σ : Val) (hσ : Fixes σ (ringIn D P)) :
    Completes C rd 735 1166 bRing σ (fun σ' => Fixes σ' (ringOut D P)) := by
  have e : mcsOf (fun k ↦ sqCv^[k] D.cvF) = D.mcs := mcs_eq.symm
  have e6 : sqCv^[6] D.cvF = D.cvM := by simp [VsData.cvM, sqAll_eq]
  have := (c_ring_comp (CM := CompModel.deployed) (C := C) (st := fun k ↦ sqCv^[k] D.cvF) rfl
    (fun k _ ↦ sqCvM_iterate_deployed D.cvF k) hok.s_length hok.rcs_length (e ▸ hm.mcs)
    (e ▸ hm.ctab) (e ▸ hm.rs) hm.lrs hm.zvals hC.loop84 hC.loop85 σ hσ).of_deployed
  simp only [e, e6] at this
  exact this

end
end LeanVM.Guest.B1.VerifySub
