/-
  LeanVM.Guest.B1.Comp.VerifySub.Tail

  `verify_sub`'s last blocks over a completeness model: the three phase calls, the batching from
  the model's squeeze, the opening with the terminal, and the export.
-/

module

public import LeanVM.Guest.B1.Comp.VerifySub.Bus
public import LeanVM.Guest.B1.VerifySub.CTail

/-!
# The calls, the batching, the opening and `defer_out` over a completeness model (G:2150-2280)

`VerifySub/CCalls.lean` and `VerifySub/CTail.lean` over a `CompModel`.

* `c_callsB`, `c_openB`, `c_deferB`: the blocks with no `BLAKE2S` row (`bCalls`, `bOpen`,
  `bDefer`), under any semantics. The deployed lemmas take the run through `VsData.Ok`,
  `VsMem0` and `VsCallsOk`, whose fields name the deployed run's states; these take the states
  the blocks read as parameters (`cvB`, `beta`, `cvL`, `target`, the copied cells), the calls and
  the memory words by themselves (`c_callsG`, `c_openG`, `c_deferG`, proved as the deployed).
* `c_lam_comp`: the batching, `lam = challengeOf cvL` from the model's squeeze
  `sqCvM CM.hm cvM = some cvL`, the running target from the ring's `t0` (`lamTC`); at
  `CompModel.deployed` it is `c_lam` (`c_lam_of_comp`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig LeanVM.E2E.Complete

@[expose] public section

variable {S : BlakeSem} {C : CallRel} {rd : Reader} {D : VsData} {P : VsPtrs} {out : E}
  {bytecode : List K}

/-! ## GKR, the tables and Flock -/

/-- The values the calls read, the bus state `cvB` and `beta` given (`callsIn`). -/
def callsInC (D : VsData) (P : VsPtrs) (sq : E) (cvB : Digest) (beta : E) : List (ℕ × E) :=
  [(0, (digestScalars D.pi).1), (1, (digestScalars D.pi).2), (5, sq), (7, P.pool), (8, P.cplen),
    (30, P.rows), (143, P.dims), (163, P.bk), (417, gen ^ log2Ceil D.pushTotal), (418, P.zeta),
    (508, P.fpw), (690, (digestScalars cvB).1), (691, (digestScalars cvB).2), (698, beta),
    (700, curG P)]

theorem callsInC_deployed {sq : E} : callsInC D P sq D.cvB D.beta = callsIn D P sq := rfl

/-- **GKR, the tables and Flock** (G:2150-2168, `c_calls`), the bus state and the calls given. -/
theorem c_callsG {sq : E} {cvB : Digest} {beta : E} (hd6 : LoadHolds rd P.dims 6 (gen ^ D.tau))
    (hgkr : C "verify_bus_gkr" [(digestScalars cvB).1, (digestScalars cvB).2, curG P,
      gen ^ log2Ceil D.pushTotal, P.zeta]
      [(digestScalars D.cvG).1, (digestScalars D.cvG).2, curT D P, D.gr.2.2.getD 0 0,
        D.gr.2.2.getD 1 0, D.gr.2.2.getD 2 0])
    (htab : C "verify_tables" [(digestScalars D.cvG).1, (digestScalars D.cvG).2, curT D P,
      (digestScalars D.pi).1, (digestScalars D.pi).2, P.zeta, gen ^ log2Ceil D.pushTotal, P.dims,
      P.rows, P.bk, sq, P.fpw, beta, P.pool, P.cplen, P.chi, D.gr.2.2.getD 0 0, D.gr.2.2.getD 1 0,
      D.gr.2.2.getD 2 0] [(digestScalars D.cvT).1, (digestScalars D.cvT).2, curF D P, D.gzcn, D.bv, D.rm])
    (hfl : C "verify_flock" [(digestScalars D.cvT).1, (digestScalars D.cvT).2, curF D P,
      gen ^ D.tau, P.zchis, P.lrs, P.zpart]
      [(digestScalars D.cvF).1, (digestScalars D.cvF).2, curW D P, D.zSkip, D.alpha, D.mv])
    (σ : Val) (hσ : Fixes σ (callsInC D P sq cvB beta)) :
    Completes C rd 701 735 bCalls σ (fun σ' => Fixes σ' (callsOut D P)) := by
  have e : ∀ k e, (k, e) ∈ callsInC D P sq cvB beta → σ (.n k) = e := fun k e h => hσ.get h
  refine completes_upds [(701, (digestScalars D.cvG).1), (702, (digestScalars D.cvG).2),
    (703, curT D P), (704, D.gr.2.2.getD 0 0), (705, D.gr.2.2.getD 1 0), (706, D.gr.2.2.getD 2 0),
    (707, (digestScalars D.cvG).1), (708, (digestScalars D.cvG).2), (709, P.chi),
    (710, (digestScalars D.cvT).1), (711, (digestScalars D.cvT).2), (712, curF D P), (713, D.gzcn),
    (714, D.bv), (715, D.rm), (716, (digestScalars D.cvT).1), (717, (digestScalars D.cvT).2),
    (718, gen ^ D.tau), (719, word 256 0 0), (720, gen ^ D.tau * word 256 0 0), (721, P.zchis),
    (722, P.lrs), (723, P.zpart), (724, (digestScalars D.cvF).1), (725, (digestScalars D.cvF).2),
    (726, curW D P), (727, D.zSkip), (728, D.alpha), (729, D.mv), (730, (digestScalars D.cvF).1),
    (731, (digestScalars D.cvF).2), (732, P.mcs), (733, P.ctab), (734, P.zvals)] (by simp)
    (fun next kret hn => ?_) ?_
  · simp only [bCalls, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
    vs_ev
    simp only [e 0 (digestScalars D.pi).1 (by simp [callsInC]), e 1 (digestScalars D.pi).2 (by simp [callsInC]),
      e 5 sq (by simp [callsInC]),
      e 7 P.pool (by simp [callsInC]), e 8 P.cplen (by simp [callsInC]), e 30 P.rows (by simp [callsInC]),
      e 143 P.dims (by simp [callsInC]), e 163 P.bk (by simp [callsInC]),
      e 417 (gen ^ log2Ceil D.pushTotal) (by simp [callsInC]),
      e 418 P.zeta (by simp [callsInC]), e 508 P.fpw (by simp [callsInC]),
      e 690 (digestScalars cvB).1 (by simp [callsInC]),
      e 691 (digestScalars cvB).2 (by simp [callsInC]), e 698 beta (by simp [callsInC]),
      e 700 (curG P) (by simp [callsInC])]
    exact ⟨hgkr, trivial, trivial, trivial, htab, trivial, trivial, hd6, trivial, trivial,
      trivial, trivial, trivial, hfl, trivial, trivial, trivial, trivial, trivial, hn⟩
  · intro p hp
    simp only [callsOut, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> simp [upds_n]

theorem bCalls_free :
    Stmt.freeInList ["verify_bus_gkr", "verify_tables", "verify_flock"] bCalls = true := by decide

/-- **GKR, the tables and Flock under any semantics** (`c_calls`). -/
theorem c_callsB {sq : E} {cvB : Digest} {beta : E} (hd6 : LoadHolds rd P.dims 6 (gen ^ D.tau))
    (hgkr : C "verify_bus_gkr" [(digestScalars cvB).1, (digestScalars cvB).2, curG P,
      gen ^ log2Ceil D.pushTotal, P.zeta]
      [(digestScalars D.cvG).1, (digestScalars D.cvG).2, curT D P, D.gr.2.2.getD 0 0,
        D.gr.2.2.getD 1 0, D.gr.2.2.getD 2 0])
    (htab : C "verify_tables" [(digestScalars D.cvG).1, (digestScalars D.cvG).2, curT D P,
      (digestScalars D.pi).1, (digestScalars D.pi).2, P.zeta, gen ^ log2Ceil D.pushTotal, P.dims,
      P.rows, P.bk, sq, P.fpw, beta, P.pool, P.cplen, P.chi, D.gr.2.2.getD 0 0, D.gr.2.2.getD 1 0,
      D.gr.2.2.getD 2 0] [(digestScalars D.cvT).1, (digestScalars D.cvT).2, curF D P, D.gzcn, D.bv, D.rm])
    (hfl : C "verify_flock" [(digestScalars D.cvT).1, (digestScalars D.cvT).2, curF D P,
      gen ^ D.tau, P.zchis, P.lrs, P.zpart]
      [(digestScalars D.cvF).1, (digestScalars D.cvF).2, curW D P, D.zSkip, D.alpha, D.mv])
    (σ : Val) (hσ : Fixes σ (callsInC D P sq cvB beta)) :
    CompletesB S C rd 701 735 bCalls σ (fun σ' => Fixes σ' (callsOut D P)) :=
  CompletesB.of_free bCalls_free (c_callsG hd6 hgkr htab hfl σ hσ)

/-- The deployed `c_calls`, from the block's under any semantics at `blakeDeployed`. -/
theorem c_calls_of_comp {lp sq : E} (hok : D.Ok bytecode) (hm : VsMem0 rd D P out)
    (hC : VsCallsOk C bytecode D P lp sq) (σ : Val) (hσ : Fixes σ (callsIn D P sq)) :
    Completes C rd 701 735 bCalls σ (fun σ' => Fixes σ' (callsOut D P)) :=
  (c_callsB (S := blakeDeployed) (dims_six hok hm) hC.gkr hC.tables hC.flock σ hσ).of_deployed

/-! ## The batching -/

/-- The running target after claim `j`, from the ring's target `t0` and the challenge `lam`
(`lamT`). -/
def lamTC (t0 lam : E) (vs : List E) (j : ℕ) : E :=
  t0 + ((List.range (j + 1)).map fun i ↦ lam ^ (i + 1) * vs.getD i 0).sum

theorem lamTC_deployed (j : ℕ) : lamTC (ringTarget D.s D.mcs) D.lam (vals D) j = lamT D j := rfl

/-- **Claim `j + 1` of the batching** (G:2224-2228, `c_lpBlk`), at any challenge `lam` and
target `t0`. -/
theorem c_lpBlkG {j : ℕ} {t0 lam : E} (hj : j < 111) (hv : ReadsAt rd P.pool (vals D))
    (hvl : (vals D).length = 112) (hlp : ReadsAt rd P.lam (powersFrom lam lam 112)) (σ : Val)
    (hσ : σ (.n 1179) = lam ∧ σ (.n 1180) = P.lam ∧ σ (.n 7) = P.pool ∧
      σ (.n (lpP j)) = lam ^ (j + 1) ∧ σ (.n (lpT j)) = lamTC t0 lam (vals D) j) :
    Completes C rd (1184 + 4 * j) (1184 + 4 * (j + 1)) (lpBlk j) σ (fun σ' =>
      σ' (.n 1179) = lam ∧ σ' (.n 1180) = P.lam ∧ σ' (.n 7) = P.pool ∧
        σ' (.n (lpP (j + 1))) = lam ^ (j + 1 + 1) ∧
        σ' (.n (lpT (j + 1))) = lamTC t0 lam (vals D) (j + 1)) := by
  obtain ⟨h1179, h1180, h7, hP, hT⟩ := hσ
  have hpl := lpP_lt j
  have htl := lpT_lt j
  have hvj : LoadHolds rd P.pool (j + 1) ((vals D).getD (j + 1) 0) := readsAt_getD hv (by omega)
  have hlj : LoadHolds rd P.lam (j + 1) (lam ^ (j + 1 + 1)) := by
    have := readsAt_getD hlp (k := j + 1) (by rw [length_powersFrom]; omega)
    rwa [getD_powersFrom _ _ _ _ (by omega), ← pow_succ'] at this
  refine completes_upds [(1184 + 4 * j, lam ^ (j + 1 + 1)), (1185 + 4 * j, (vals D).getD (j + 1) 0),
    (1186 + 4 * j, lam ^ (j + 1 + 1) * (vals D).getD (j + 1) 0),
    (1187 + 4 * j, lamTC t0 lam (vals D) (j + 1))]
    (by simp; omega) (fun next kret hn => ?_) ?_
  · simp only [lpBlk, lpP_succ, lpT_succ, Stmt.HoldsList, Stmt.Holds, Atom.Holds, upds_n, upds_nil]
    simp only [show 1184 + 4 * j + 1 = 1185 + 4 * j by omega, show 1184 + 4 * j + 2 = 1186 + 4 * j by omega,
      show (1179 : ℕ) ≠ 1184 + 4 * j by omega, show (1179 : ℕ) ≠ 1185 + 4 * j by omega,
      show (1179 : ℕ) ≠ 1186 + 4 * j by omega, show (1179 : ℕ) ≠ 1187 + 4 * j by omega,
      show (1180 : ℕ) ≠ 1184 + 4 * j by omega, show (1180 : ℕ) ≠ 1185 + 4 * j by omega,
      show (1180 : ℕ) ≠ 1186 + 4 * j by omega, show (1180 : ℕ) ≠ 1187 + 4 * j by omega,
      show (7 : ℕ) ≠ 1184 + 4 * j by omega, show (7 : ℕ) ≠ 1185 + 4 * j by omega,
      show (7 : ℕ) ≠ 1186 + 4 * j by omega, show (7 : ℕ) ≠ 1187 + 4 * j by omega,
      show lpP j ≠ 1184 + 4 * j by omega, show lpP j ≠ 1185 + 4 * j by omega,
      show lpP j ≠ 1186 + 4 * j by omega, show lpP j ≠ 1187 + 4 * j by omega,
      show lpT j ≠ 1184 + 4 * j by omega, show lpT j ≠ 1185 + 4 * j by omega,
      show lpT j ≠ 1186 + 4 * j by omega, show lpT j ≠ 1187 + 4 * j by omega,
      show 1185 + 4 * j ≠ 1184 + 4 * j by omega, show 1186 + 4 * j ≠ 1184 + 4 * j by omega,
      show 1186 + 4 * j ≠ 1185 + 4 * j by omega, show 1187 + 4 * j ≠ 1184 + 4 * j by omega,
      show 1187 + 4 * j ≠ 1185 + 4 * j by omega, show 1187 + 4 * j ≠ 1186 + 4 * j by omega,
      ↓reduceIte, h1179, h1180, h7, hP, hT]
    refine ⟨by rw [← pow_succ], hlj, hvj, by vs_triv, ?_, hn⟩
    unfold lamTC
    rw [List.range_succ (n := j + 1)]
    simp [add_assoc]
  · simp only [lpP_succ, lpT_succ, upds_n, upds_nil,
      show (1179 : ℕ) ≠ 1184 + 4 * j by omega, show (1179 : ℕ) ≠ 1185 + 4 * j by omega,
      show (1179 : ℕ) ≠ 1186 + 4 * j by omega, show (1179 : ℕ) ≠ 1187 + 4 * j by omega,
      show (1180 : ℕ) ≠ 1184 + 4 * j by omega, show (1180 : ℕ) ≠ 1185 + 4 * j by omega,
      show (1180 : ℕ) ≠ 1186 + 4 * j by omega, show (1180 : ℕ) ≠ 1187 + 4 * j by omega,
      show (7 : ℕ) ≠ 1184 + 4 * j by omega, show (7 : ℕ) ≠ 1185 + 4 * j by omega,
      show (7 : ℕ) ≠ 1186 + 4 * j by omega, show (7 : ℕ) ≠ 1187 + 4 * j by omega,
      show 1187 + 4 * j ≠ 1184 + 4 * j by omega, show 1187 + 4 * j ≠ 1185 + 4 * j by omega,
      show 1187 + 4 * j ≠ 1186 + 4 * j by omega, ↓reduceIte, h1179, h1180, h7]
    exact ⟨trivial, trivial, trivial, trivial, trivial⟩

theorem lpBlk_free (j : ℕ) : Stmt.freeInList [] (lpBlk j) = true := rfl

/-- The values the batching reads, the ring's state `cvM` and target `t0` given (`lamIn`). -/
def lamInC (P : VsPtrs) (cvM : Digest) (t0 : E) : List (ℕ × E) :=
  [(7, P.pool), (810, (digestScalars cvM).1), (811, (digestScalars cvM).2), (1150, t0)]

/-- The values the batching leaves, its state `cvL` and target given (`lamOut`). -/
def lamOutC (P : VsPtrs) (cvL : Digest) (target : E) : List (ℕ × E) :=
  [(1171, (digestScalars cvL).1), (1172, (digestScalars cvL).2), (1180, P.lam), (1627, target)]

theorem lamInC_deployed : lamInC P D.cvM (ringTarget D.s D.mcs) = lamIn D P := rfl

/-- **The batching over a completeness model** (G:2219-2229, `c_lam`): the model answers the
squeeze of the ring's state `cvM` by `cvL`, `lam = challengeOf cvL`, its powers stored, the
opening's target `lamTC t0 lam (vals D) 111`. -/
theorem c_lam_comp {CM : CompModel} (hcl : D.claims.length = 112) {cvM cvL : Digest} {t0 : E}
    (hL : sqCvM CM.hm cvM = some cvL) (hv : ReadsAt rd P.pool (vals D))
    (hlp : ReadsAt rd P.lam (powersFrom (challengeOf cvL) (challengeOf cvL) 112)) (σ : Val)
    (hσ : Fixes σ (lamInC P cvM t0)) :
    CompletesB CM.sem C rd 1166 1629 bLam σ (fun σ' => Fixes σ' (lamOutC P cvL
      (lamTC t0 (challengeOf cvL) (vals D) 111))) := by
  set lam := challengeOf cvL
  have hvl : (vals D).length = 112 := by simp [vals, hcl]
  have h7 : σ (.n 7) = P.pool := hσ.get (by simp [lamInC])
  have h1150 : σ (.n 1150) = t0 := hσ.get (by simp [lamInC])
  rw [bLam_eq]
  refine CompletesB.append (m := 1628) (P := fun σ' => (σ' (.n 1179) = lam ∧ σ' (.n 1180) = P.lam ∧
      σ' (.n 7) = P.pool ∧ σ' (.n (lpP 111)) = lam ^ (111 + 1) ∧
      σ' (.n (lpT 111)) = lamTC t0 lam (vals D) 111) ∧
      Fixes σ' [(1171, (digestScalars cvL).1), (1172, (digestScalars cvL).2)])
    (by omega) (by omega) (numBelow_of_B (by decide +kernel)) ?_ fun σ3 _ ⟨⟨j1179, j1180, _, jP, jT⟩, jf⟩ => ?_
  · refine CompletesB.append (m := 1184) (P := fun σ' => (σ' (.n 1179) = lam ∧ σ' (.n 1180) = P.lam ∧
        σ' (.n 7) = P.pool ∧ σ' (.n (lpP 0)) = lam ^ (0 + 1) ∧
        σ' (.n (lpT 0)) = lamTC t0 lam (vals D) 0) ∧
        Fixes σ' [(1171, (digestScalars cvL).1), (1172, (digestScalars cvL).2)])
      (by omega) (by omega) (numBelow_of_B (by decide +kernel)) ?_ fun σ2 _ ⟨hi, jf⟩ => ?_
    · refine CompletesB.append (m := 1180) (P := fun σ' => (σ' (.n 1171), σ' (.n 1172)) =
          digestScalars cvL ∧ σ' (.n 1179) = lam ∧ σ' (.n 7) = P.pool ∧ σ' (.n 1150) = t0)
        (by omega) (by omega) (numBelow_of_B (by decide +kernel)) ?_ fun σ1 _ ⟨k1171, k1179, k7, k1150⟩ => ?_
      · exact completesB_squeezeT_comp (b := 1166) ⟨810, by omega, rfl⟩ ⟨811, by omega, rfl⟩
          (by rw [hσ.get (k := 810) (e := (digestScalars cvM).1) (by simp [lamInC]),
            hσ.get (k := 811) (e := (digestScalars cvM).2) (by simp [lamInC])]) hL
          fun σ' e h5 h13 => ⟨h5, h13, by rw [e.apply (by omega)]; exact h7,
            by rw [e.apply (by omega)]; exact h1150⟩
      · have hv0 : LoadHolds rd P.pool 0 ((vals D).getD 0 0) := readsAt_getD hv (by omega)
        have hl0 : LoadHolds rd P.lam 0 lam := by
          have := readsAt_getD hlp (k := 0) (by rw [length_powersFrom]; omega)
          rwa [getD_powersFrom _ _ _ _ (by omega), pow_zero, mul_one] at this
        refine completesB_upds [(1180, P.lam), (1181, (vals D).getD 0 0), (1182, lam * (vals D).getD 0 0),
          (1183, t0 + lam * (vals D).getD 0 0)] (by simp) (fun next kret hn => ?_) ?_
        · simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB]
          vs_ev
          rw [k1179, k7, k1150]
          exact ⟨trivial, hl0, hv0, by vs_triv, by vs_triv, hn⟩
        · refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
          · vs_ev; exact k1179
          · vs_ev
          · vs_ev; exact k7
          · simp only [lpP, ↓reduceIte]; vs_ev; rw [k1179]; simp
          · simp only [lpT, ↓reduceIte]; vs_ev; simp [lamTC]
          · intro p hp
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
            rcases hp with rfl | rfl <;> vs_ev
            · exact congrArg Prod.fst k1171
            · exact congrArg Prod.snd k1171
    · have key := CompletesB.flatten (S := CM.sem) (C := C) (rd := rd) (blk := lpBlk)
        (st := fun j ↦ 1184 + 4 * j)
        (Inv := fun j σ' ↦ σ' (.n 1179) = lam ∧ σ' (.n 1180) = P.lam ∧ σ' (.n 7) = P.pool ∧
          σ' (.n (lpP j)) = lam ^ (j + 1) ∧ σ' (.n (lpT j)) = lamTC t0 lam (vals D) j) 111
        (fun _ _ => by omega) numBelow_lp
        (fun j hj σ' h => CompletesB.of_free (lpBlk_free j) (c_lpBlkG hj hv hvl hlp σ' h)) σ2 hi
      exact key.keep jf (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> simp)
  · refine completesB_upds [(1628, lam ^ (111 + 1) * lam)] (by simp) (fun next kret hn => ?_) ?_
    · simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB]
      vs_ev
      rw [show (1624 : ℕ) = lpP 111 from rfl, jP, j1179]
      exact ⟨rfl, hn⟩
    · intro p hp
      simp only [lamOutC, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> vs_ev
      · exact jf.get (by simp)
      · exact jf.get (by simp)
      · exact j1180
      · rw [show (1627 : ℕ) = lpT 111 from rfl, jT]

/-- The deployed `c_lam`, from the model's at `CompModel.deployed`. -/
theorem c_lam_of_comp (hcl : D.claims.length = 112) (hm : VsMem0 rd D P out) (σ : Val)
    (hσ : Fixes σ (lamIn D P)) :
    Completes C rd 1166 1629 bLam σ (fun σ' => Fixes σ' (lamOut D P)) := by
  have := (c_lam_comp (CM := CompModel.deployed) (C := C) (cvM := D.cvM) (cvL := D.cvL)
    (t0 := ringTarget D.s D.mcs) hcl rfl hm.pool hm.lam σ hσ).of_deployed
  refine this.post fun σ' _ h => ?_
  rw [lamOut, target_eq hcl]
  exact h

/-! ## The stack's size, the opening and the terminal -/

/-- The values the opening block reads, the batching's state `cvL` and target given (`openIn`). -/
def openInC (D : VsData) (P : VsPtrs) (lp sq : E) (cvL : Digest) (target : E) : List (ℕ × E) :=
  [(4, lp), (5, sq), (8, P.cplen), (138, gen ^ (D.rate - 1)), (144, gen ^ D.logMem), (155, P.kbase),
    (417, gen ^ log2Ceil D.pushTotal), (418, P.zeta), (419, D.x0), (434, D.x1), (709, P.chi),
    (713, D.gzcn), (715, D.rm), (718, gen ^ D.tau), (726, curW D P), (733, P.ctab), (734, P.zvals),
    (1171, (digestScalars cvL).1), (1172, (digestScalars cvL).2), (1180, P.lam), (1627, target)]

theorem openInC_deployed {lp sq : E} : openInC D P lp sq D.cvL D.target = openIn D P lp sq := rfl

/-- **The stack's size, the opening and the terminal** (G:2231-2263, `c_open`), the run's sizes,
the batching's state and target, and the calls given. -/
theorem c_openG (hlow : LowDef 6 rd) {lp sq : E} {cvL : Digest} {target : E}
    (hb : bytecode.length = 2 ^ 22)
    (hs1 : 22 ≤ (layoutOf bytecode D.logMem D.rows).stackLog)
    (hs2 : (layoutOf bytecode D.logMem D.rows).stackLog ≤ 28) (hr1 : 1 ≤ D.rate) (hr2 : D.rate ≤ 4)
    (hcert : C "certify_placement" [P.kbase, sq] [gen ^ D.stackTot, P.off, P.kap])
    (hlog : C "log2_ceil_in_the_exponent__L15_L34" [gen ^ D.stackTot, lp, sq]
      [gen ^ max 15 (log2Ceil D.stackTot)])
    (hop : C (openName (layoutOf bytecode D.logMem D.rows).stackLog D.rate)
      [(digestScalars cvL).1, (digestScalars cvL).2, target, D.x0, D.x1, curW D P]
      [D.w.target, P.pt, D.w.inner, D.w.residual])
    (hterm : C "check_opening_terminal" [P.zeta, P.chi, D.rm, gen ^ log2Ceil D.pushTotal, D.gzcn,
      gen ^ D.logMem, gen ^ D.tau, P.cplen, P.lam, P.off, P.kap, P.zvals, P.ctab, P.pt, D.w.inner,
      D.w.residual, D.w.target] [])
    (σ : Val) (hσ : Fixes σ (openInC D P lp sq cvL target)) :
    Completes C rd 1629 1652 bOpen σ (fun _ => True) := by
  have e : ∀ k e, (k, e) ∈ openInC D P lp sq cvL target → σ (.n k) = e := fun k e h => hσ.get h
  set μ := (layoutOf bytecode D.logMem D.rows).stackLog with hμ
  have hμe : μ = max 15 (log2Ceil D.stackTot) := stackLog_eq hb _ _
  set r := D.rate
  set sel := μ - 22 + 7 * (r - 1)
  have hsel : sel < 28 := by omega
  refine completes_upds [(1629, gen ^ D.stackTot), (1630, P.off), (1631, P.kap), (1632, gen ^ μ),
    (1633, word 8198552432976855044 0 0), (1634, gen ^ (μ - 22)), (1635, word 64 0 0),
    (1636, (rcLow rd (μ - 22) 7).1), (1637, (rcLow rd (μ - 22) 7).2.1),
    (1638, (rcLow rd (μ - 22) 7).2.2), (1639, gen ^ (r - 1) * gen ^ (r - 1)),
    (1640, gen ^ (r - 1) * gen ^ (r - 1) * gen ^ (r - 1)),
    (1641, gen ^ (r - 1) * gen ^ (r - 1) * gen ^ (r - 1) * (gen ^ (r - 1) * gen ^ (r - 1) * gen ^ (r - 1))),
    (1642, gen ^ (r - 1) * gen ^ (r - 1) * gen ^ (r - 1) * (gen ^ (r - 1) * gen ^ (r - 1) * gen ^ (r - 1)) *
      gen ^ (r - 1)), (1643, gen ^ sel), (1644, word 134217728 0 0),
    (1645, (rcLow rd sel 28).1), (1646, (rcLow rd sel 28).2.1),
    (1647, (rcLow rd sel 28).2.2), (1648, D.w.target), (1649, P.pt), (1650, D.w.inner),
    (1651, D.w.residual)] (by simp) (fun next kret hn => ?_) trivial
  simp only [bOpen, Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hn⟩
  · vs_ev; rw [e 155 P.kbase (by simp [openInC]), e 5 sq (by simp [openInC])]; exact hcert
  · vs_ev
    rw [e 4 lp (by simp [openInC]), e 5 sq (by simp [openInC]), hμe]
    exact hlog
  · simp only [Atom.Holds]; vs_ev
  · simp only [Atom.Holds]; vs_ev
    conv_rhs => rw [show μ = (μ - 22) + 22 by omega, pow_add, mul_assoc, mul_comm (gen ^ 22),
      minShiftInv, mul_one]
  · simp only [Atom.Holds]; vs_ev
  · exact rc_holds_low hlow (K := 7) (e := μ - 22) (by omega) (by omega) (by vs_ev)
      (by vs_ev) (by vs_ev) (by vs_ev) (by vs_ev; exact word_two_pow (a := 6) (by decide))
  · simp only [Atom.Holds]; vs_ev; rw [e 138 (gen ^ (r - 1)) (by simp [openInC, r])]
  · simp only [Atom.Holds]; vs_ev; rw [e 138 (gen ^ (r - 1)) (by simp [openInC, r])]
  · simp only [Atom.Holds]; vs_ev
  · simp only [Atom.Holds]; vs_ev; rw [e 138 (gen ^ (r - 1)) (by simp [openInC, r])]
  · simp only [Atom.Holds]; vs_ev
    simp only [← pow_add]; congr 1; omega
  · simp only [Atom.Holds]; vs_ev
  · exact rc_holds_low hlow (K := 28) (e := sel) (by omega) hsel (by vs_ev)
      (by vs_ev) (by vs_ev) (by vs_ev) (by vs_ev; exact word_two_pow (a := 27) (by decide))
  · vs_ev
    refine ⟨sel, by simp [openNames]; omega, by rw [gen_pow_eq_ofK], ?_⟩
    rw [e 1171 (digestScalars cvL).1 (by simp [openInC]), e 1172 (digestScalars cvL).2 (by simp [openInC]),
      e 1627 target (by simp [openInC]),
      e 419 D.x0 (by simp [openInC]), e 434 D.x1 (by simp [openInC]), e 726 (curW D P) (by simp [openInC])]
    have hn : openNames[sel]'(by simp [openNames]; omega) = openName μ r := by
      rw [openName, ← openNames_getD (by omega)]
    rw [hn]
    exact hop
  · vs_ev
    rw [e 418 P.zeta (by simp [openInC]), e 709 P.chi (by simp [openInC]), e 715 D.rm (by simp [openInC]),
      e 417 (gen ^ log2Ceil D.pushTotal) (by simp [openInC]), e 713 D.gzcn (by simp [openInC]),
      e 144 (gen ^ D.logMem) (by simp [openInC]),
      e 718 (gen ^ D.tau) (by simp [openInC]), e 8 P.cplen (by simp [openInC]),
      e 1180 P.lam (by simp [openInC]),
      e 734 P.zvals (by simp [openInC]), e 733 P.ctab (by simp [openInC])]
    exact hterm

theorem bOpen_free : Stmt.freeInList (["certify_placement", "log2_ceil_in_the_exponent__L15_L34",
    "check_opening_terminal"] ++ openNames) bOpen = true := by decide +kernel

/-- **The opening under any semantics** (`c_open`). -/
theorem c_openB (hlow : LowDef 6 rd) {lp sq : E} {cvL : Digest} {target : E}
    (hb : bytecode.length = 2 ^ 22)
    (hs1 : 22 ≤ (layoutOf bytecode D.logMem D.rows).stackLog)
    (hs2 : (layoutOf bytecode D.logMem D.rows).stackLog ≤ 28) (hr1 : 1 ≤ D.rate) (hr2 : D.rate ≤ 4)
    (hcert : C "certify_placement" [P.kbase, sq] [gen ^ D.stackTot, P.off, P.kap])
    (hlog : C "log2_ceil_in_the_exponent__L15_L34" [gen ^ D.stackTot, lp, sq]
      [gen ^ max 15 (log2Ceil D.stackTot)])
    (hop : C (openName (layoutOf bytecode D.logMem D.rows).stackLog D.rate)
      [(digestScalars cvL).1, (digestScalars cvL).2, target, D.x0, D.x1, curW D P]
      [D.w.target, P.pt, D.w.inner, D.w.residual])
    (hterm : C "check_opening_terminal" [P.zeta, P.chi, D.rm, gen ^ log2Ceil D.pushTotal, D.gzcn,
      gen ^ D.logMem, gen ^ D.tau, P.cplen, P.lam, P.off, P.kap, P.zvals, P.ctab, P.pt, D.w.inner,
      D.w.residual, D.w.target] [])
    (σ : Val) (hσ : Fixes σ (openInC D P lp sq cvL target)) :
    CompletesB S C rd 1629 1652 bOpen σ (fun _ => True) :=
  CompletesB.of_free bOpen_free (c_openG hlow hb hs1 hs2 hr1 hr2 hcert hlog hop hterm σ hσ)

/-- The deployed `c_open`, from the block's under any semantics at `blakeDeployed`. -/
theorem c_open_of_comp (hlow : LowDef 6 rd) {lp sq : E} (hb : bytecode.length = 2 ^ 22)
    (hok : D.Ok bytecode) (hC : VsCallsOk C bytecode D P lp sq) (σ : Val)
    (hσ : Fixes σ (openIn D P lp sq)) :
    Completes C rd 1629 1652 bOpen σ (fun _ => True) :=
  (c_openB (S := blakeDeployed) hlow hb hok.stack_ge hok.stack_le hok.rate_ge hok.rate_le
    hC.certify hC.log2Stack hC.opening hC.terminal σ hσ).of_deployed

/-! ## `defer_out` -/

/-- The words `defer_out` copies, each at its source and at its place in `out` (`out_cells`,
`VsMem0`'s buffers): GKR's point, the bus challenges, Flock's point, its challenges, the slices. -/
structure DeferCells (rd : Reader) (D : VsData) (P : VsPtrs) (out : E) : Prop where
  zeta : ∀ k < 18, ∃ w, LoadHolds rd P.zeta k w ∧ LoadHolds rd out k w
  alpha : ∀ k < 4, ∃ w, LoadHolds rd P.alpha k w ∧ LoadHolds rd out (18 + k) w
  bv : LoadHolds rd out 22 D.bv
  alphaF : LoadHolds rd out 23 D.alpha
  zSkip : LoadHolds rd out 24 D.zSkip
  zchis : ∀ k < 8, ∃ w, LoadHolds rd P.zchis k w ∧ LoadHolds rd out (25 + k) w
  lrs : ∀ k < 8, ∃ w, LoadHolds rd P.lrs k w ∧ LoadHolds rd out (33 + k) w
  zpart : ∀ k < 64, ∃ w, LoadHolds rd P.zpart k w ∧ LoadHolds rd out (41 + k) w
  mv : LoadHolds rd out 105 D.mv

/-- The deployed run's memory gives its copied cells. -/
theorem deferCells_of (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode) (hm : VsMem0 rd D P out) :
    DeferCells rd D P out := by
  obtain ⟨o1, o2, o22, o23, o24, o3, o4, o5, o105⟩ := out_cells hb hok hm
  have hd := depth_ge hb hok
  have hal : D.alphas.length = 4 := by simp [VsData.alphas, sqAll_eq]
  exact ⟨fun k hk => ⟨_, readsAt_getD hm.zeta (by omega), o1 k hk⟩,
    fun k hk => ⟨_, readsAt_getD hm.alpha (by omega), o2 k hk⟩, o22, o23, o24,
    fun k hk => ⟨_, readsAt_getD hm.zchis (by rw [hok.chi_length]; omega), o3 k hk⟩,
    fun k hk => ⟨_, readsAt_getD hm.lrs (by rw [hok.rcs_length]; omega), o4 k hk⟩,
    fun k hk => ⟨_, readsAt_getD hm.zpart (by rw [hok.s_length]; omega), o5 k hk⟩, o105⟩

/-- **`defer_out`** (G:2265-2279, `c_defer`), its copied cells given. -/
theorem c_deferG (hc : DeferCells rd D P out) (σ : Val) (hσ : Fixes σ (deferIn D P out)) :
    Completes C rd 1652 1754 bDefer σ (fun _ => True) := by
  have get : ∀ {σ' : Val} {k e}, Fixes σ' (deferIn D P out) → (k, e) ∈ deferIn D P out → σ' (.n k) = e :=
    fun h hk => h.get hk
  rw [bDefer_eq]
  have fam : ∀ (n b : ℕ) (blk : ℕ → List Stmt), (∀ k < n, NumBelow (b + (k + 1)) (Stmt.valsList (blk k))) →
      (∀ k < n, ∀ σ', Fixes σ' (deferIn D P out) →
        Completes C rd (b + k) (b + (k + 1)) (blk k) σ' (fun σ'' => Fixes σ'' (deferIn D P out))) →
      ∀ σ', Fixes σ' (deferIn D P out) →
        Completes C rd b (b + n) ((List.range n).map blk).flatten σ' (fun σ'' => Fixes σ'' (deferIn D P out)) :=
    fun n b blk hnb hb σ' h => by
      have := Completes.flatten (C := C) (rd := rd) (blk := blk) (st := fun k ↦ b + k)
        (Inv := fun _ σ'' ↦ Fixes σ'' (deferIn D P out)) n (fun _ _ => by omega) hnb hb σ' h
      simpa using this
  refine Completes.append (m := 1754) (P := fun σ' => Fixes σ' (deferIn D P out)) (by omega) (by omega)
    (numBelow_of_B (by decide +kernel)) ?_ fun σ5 _ h5 => ?_
  · refine Completes.append (m := 1690) (P := fun σ' => Fixes σ' (deferIn D P out)) (by omega) (by omega)
      (numBelow_of_B (by decide +kernel)) ?_ fun σ4 _ h4 => ?_
    · refine Completes.append (m := 1674) (P := fun σ' => Fixes σ' (deferIn D P out)) (by omega) (by omega)
        (numBelow_of_B (by decide +kernel)) ?_ fun σ3 _ h3 => ?_
      · refine Completes.append (m := 1674) (hi := 1674) (P := fun σ' => Fixes σ' (deferIn D P out))
          (by omega) le_rfl (numBelow_of_B (by decide +kernel)) ?_ fun σ2 _ h2 => ?_
        · refine Completes.append (m := 1670) (P := fun σ' => Fixes σ' (deferIn D P out))
            (by omega) (by omega) (numBelow_of_B (by decide +kernel)) ?_ fun σ1 _ h1 => ?_
          · exact fam 18 1652 _ (fun k hk => numBelow_of_B (by revert k hk; decide +kernel))
              (fun k hk σ' h => let ⟨_, hw1, hw2⟩ := hc.zeta k hk
                c_cpKeep (ps := P.zeta) (by omega) hw1 hw2 σ' h (by omega) (by simp [deferIn])) σ hσ
          · exact fam 4 1670 _ (fun k hk => numBelow_of_B (by revert k hk; decide +kernel))
              (fun k hk σ' h => let ⟨_, hw1, hw2⟩ := hc.alpha k hk
                c_cpKeep (ps := P.alpha) (by omega) hw1 hw2 σ' h (by omega) (by simp [deferIn])) σ1 h1
        · refine completes_upds [] (by simp) (fun next kret hn => ?_) (by simpa using h2)
          simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, upds_nil]
          rw [get (e := out) h2 (by simp [deferIn]), get (e := D.bv) h2 (by simp [deferIn]),
            get (e := D.alpha) h2 (by simp [deferIn]), get (e := D.zSkip) h2 (by simp [deferIn])]
          exact ⟨hc.bv, hc.alphaF, hc.zSkip, hn⟩
      · have := Completes.flatten (C := C) (rd := rd) (blk := fun k ↦ cpBlk (1674 + 2 * k) (.n 721) k
          (25 + k) ++ cpBlk (1675 + 2 * k) (.n 722) k (33 + k)) (st := fun k ↦ 1674 + 2 * k)
          (Inv := fun _ σ'' ↦ Fixes σ'' (deferIn D P out)) 8 (fun _ _ => by omega)
          (fun k hk => numBelow_of_B (by revert k hk; decide +kernel)) (fun k hk σ' h => ?_) σ3 h3
        · simpa using this
        · refine Completes.append (m := 1675 + 2 * k) (P := fun σ'' => Fixes σ'' (deferIn D P out))
            (by omega) (by omega) (numBelow_of_B (by revert k hk; decide +kernel)) ?_
            fun σ'' _ h'' => ?_
          · obtain ⟨_, hz1, hz2⟩ := hc.zchis k hk
            rw [show 1675 + 2 * k = 1674 + 2 * k + 1 by omega]
            exact c_cpKeep (v := 1674 + 2 * k) (src := 721) (i := k) (j := 25 + k) (ps := P.zchis)
              (by omega) hz1 hz2 σ' h (by omega) (by simp [deferIn])
          · obtain ⟨_, hl1, hl2⟩ := hc.lrs k hk
            rw [show 1674 + 2 * (k + 1) = 1675 + 2 * k + 1 by omega]
            exact c_cpKeep (v := 1675 + 2 * k) (src := 722) (i := k) (j := 33 + k) (ps := P.lrs)
              (by omega) hl1 hl2 σ'' h'' (by omega) (by simp [deferIn])
    · exact fam 64 1690 _ (fun k hk => numBelow_of_B (by revert k hk; decide +kernel))
        (fun k hk σ' h => let ⟨_, hw1, hw2⟩ := hc.zpart k hk
          c_cpKeep (by omega) hw1 hw2 σ' h (by omega) (by simp [deferIn])) σ4 h4
  · refine completes_upds [] (by simp) (fun next kret hn => ⟨?_, hn⟩) trivial
    show LoadHolds rd (upds σ5 [] (.n 6)) 105 (upds σ5 [] (.n 729))
    rw [upds_nil, get (e := out) h5 (by simp [deferIn]), get (e := D.mv) h5 (by simp [deferIn])]
    exact hc.mv

theorem bDefer_free : Stmt.freeInList [] bDefer = true := by decide +kernel

/-- **`defer_out` under any semantics** (`c_defer`). -/
theorem c_deferB (hc : DeferCells rd D P out) (σ : Val) (hσ : Fixes σ (deferIn D P out)) :
    CompletesB S C rd 1652 1754 bDefer σ (fun _ => True) :=
  CompletesB.of_free bDefer_free (c_deferG hc σ hσ)

/-- The deployed `c_defer`, from the block's under any semantics at `blakeDeployed`. -/
theorem c_defer_of_comp (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode) (hm : VsMem0 rd D P out)
    (σ : Val) (hσ : Fixes σ (deferIn D P out)) :
    Completes C rd 1652 1754 bDefer σ (fun _ => True) :=
  (c_deferB (S := blakeDeployed) (deferCells_of hb hok hm) σ hσ).of_deployed

end
end LeanVM.Guest.B1.VerifySub
