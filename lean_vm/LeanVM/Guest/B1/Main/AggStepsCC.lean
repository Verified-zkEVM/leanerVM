/-
  LeanVM.Guest.B1.Main.AggStepsCC

  The batching loops' absorbing and squeezing iterations backward over an answered hash: the
  honest words in memory, the chain over `Ht` answered by `H`, give the iteration under `S`.
-/

module

public import LeanVM.Guest.B1.Main.AggStepsCS
public import LeanVM.Guest.B1.Main.RowsC

/-!
# The batching loops, backward, over an answered hash

`AggStepsC.lean`'s `obsChain_complete`, `loop95_back`, `loop96_back`, `loop98_back` under `S`
over the answered hash `H`: the chain's states are its values over the total hash `Ht`
(`obsAllH Ht`, `sqCvH Ht`), every absorb and squeeze answered by `H` (`ObsAns`, the squeezes'
answers), and each `BLAKE2S` row is `FsRowsC S H`'s. The valuations are `AggStepsC.lean`'s with
the outputs `fsValsD`, `sqValsD` of the answered digests (`chainVH`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {S : BlakeSem} {H : List UInt8 → Option Digest} (Ht : List UInt8 → Digest) {rd : Reader}

/-! ## `__loop95` -/

variable {Ht} in
/-- **An absorb chain over an answered hash, backward**: the words at the cursor, and the chain's
values the answered ones, from the state of `cv`. -/
theorem obsChainC_complete (hF : FsRowsC S H) {C : CallRel} {σ : Val} (s0 s1 cur : V) (B n : ℕ)
    (kret : List E → Prop) {cv : Digest} (xs : List E) (hl : xs.length = n)
    (hcv : (σ s0, σ s1) = digestScalars cv)
    (hx : ∀ k < n, σ (.n (B + 15 * k)) = xs.getD k 0)
    (hv : ∀ k < n, ∀ j, 2 ≤ j → j < 14 →
      σ (.n (B + 15 * k + 1 + j)) =
        fsValsD (xs.getD k 0) (obsCvH Ht (obsAllH Ht cv (xs.take k)) (xs.getD k 0)) 1 j)
    (hans : ObsAns H Ht cv xs) (hr : ReadsAt rd (σ cur) xs) :
    Stmt.HoldsListB S C rd σ (obsChainT s0 s1 cur B n) True kret := by
  have key : ∀ m ≤ n, (σ (chainS0 s0 B m), σ (chainS1 s1 B m)) =
      digestScalars (obsAllH Ht cv (xs.take m)) := by
    intro m hm
    induction m with
    | zero => simpa [chainS0, chainS1, obsAllH] using hcv
    | succ m ih =>
      rw [obsAllH_take_succ _ _ _ _ (by omega), chainS0, chainS1,
        show B + 15 * m + 13 = B + 15 * m + 1 + 12 by omega,
        show B + 15 * m + 14 = B + 15 * m + 1 + 13 by omega, hv m (by omega) 12 (by omega) (by omega),
        hv m (by omega) 13 (by omega) (by omega)]
      rfl
  rw [obsChainT, holdsListB_flatten_range _ _ (fun _ => rfl)]
  refine ⟨fun k hk => hF.fsNext _ _ _ _ _ ⟨⟨by rw [hx k hk]; exact readsAt_getD' hr (by omega),
    obsAllH Ht cv (xs.take k), obsCvH Ht (obsAllH Ht cv (xs.take k)) (xs.getD k 0), key k (by omega),
    by rw [hx k hk, obsAns_get hans k (by omega), obsAllH_take_succ _ _ _ _ (by omega)],
    fun j hj1 hj2 => ?_⟩, trivial⟩, trivial⟩
  rw [hv k hk j hj1 hj2, hx k hk]

/-- Value `o` of block `k` of an absorb chain over `xs` from the state of `cv`, over `Ht`. -/
def chainVH (xs : List E) (cv : Digest) (k o : ℕ) : E :=
  if o = 0 then xs.getD k 0 else
    fsValsD (xs.getD k 0) (obsCvH Ht (obsAllH Ht cv (xs.take k)) (xs.getD k 0)) 1 (o - 1)

variable {Ht}

/-- **`__loop95` at `x = g^c` over an answered hash, backward**: the row's words give the
iteration. -/
theorem loop95C_back (hF : FsRowsC S H) {N absorb cpi cfresh frow ccar crow : E} (d c : ℕ)
    (cv : Digest) (p0 p1 : E)
    (fs cs : List E) (hfl : fs.length = 106) (hcl : cs.length = 53)
    (hans : ObsAns H Ht cv (p0 :: p1 :: (fs ++ cs)))
    (h0 : LoadHolds rd absorb (2 * c) (digestScalars cv).1)
    (h1 : LoadHolds rd absorb (2 * c + 1) (digestScalars cv).2)
    (q0 : LoadHolds rd cpi (2 * c) p0) (q1 : LoadHolds rd cpi (2 * c + 1) p1)
    (hfr : ReadsAt rd (cfresh * gen ^ (106 * c)) fs) (hcr : ReadsAt rd (ccar * gen ^ (53 * c)) cs)
    (wf : LoadHolds rd frow c (cfresh * gen ^ (106 * c)))
    (wc : LoadHolds rd crow c (ccar * gen ^ (53 * c)))
    (o0 : LoadHolds rd absorb (2 * c + 2) (digestScalars (obsAllH Ht cv (p0 :: p1 :: (fs ++ cs)))).1)
    (o1 : LoadHolds rd absorb (2 * c + 3) (digestScalars (obsAllH Ht cv (p0 :: p1 :: (fs ++ cs)))).2)
    (hK : IsInK (gen ^ c * gen + N))
    (hnext : gen ^ c * gen + N ≠ 0 → coreProgram.relNB S rd d "__loop95"
      [gen ^ c * gen, N, absorb, cpi, cfresh, frow, ccar, crow] []) :
    coreProgram.relNB S rd (d + 1) "__loop95" [gen ^ c, N, absorb, cpi, cfresh, frow, ccar, crow] [] := by
  let cv1 := obsCvH Ht cv p0
  let cv2 := obsCvH Ht cv1 p1
  let cv3 := obsAllH Ht cv2 fs
  have hall : obsAllH Ht cv (p0 :: p1 :: (fs ++ cs)) = obsAllH Ht cv3 cs := by
    simp [cv3, cv2, cv1, obsAllH, List.foldl_append]
  obtain ⟨a0, a1, hafs⟩ := hans
  rw [obsAns_append] at hafs
  obtain ⟨afs, acs⟩ := hafs
  rw [hall] at o0 o1
  rw [relNS_succ_iff find_loop95]
  refine ⟨setl (setb (setl (setb (setl (setv (setl (setv (setl
      (Val.ofArgs [gen ^ c, N, absorb, cpi, cfresh, frow, ccar, crow]) 8
      [gen ^ (2 * c), absorb * gen ^ (2 * c), (digestScalars cv).1, (digestScalars cv).2,
        gen ^ (2 * c), cpi * gen ^ (2 * c), p0]) 15 14 (fsValsD p0 cv1 1)) 29
      [cpi * gen ^ (2 * c), p1]) 31 14 (fsValsD p1 cv2 1)) 45
      [gen ^ (2 * c), gen ^ (3 * c), gen ^ (6 * c), gen ^ (12 * c), gen ^ (13 * c), gen ^ (26 * c),
        gen ^ (52 * c), gen ^ (53 * c), gen ^ (106 * c), cfresh * gen ^ (106 * c), frow * gen ^ c])
      56 106 15 (chainVH Ht fs cv2)) 1646
      [gen ^ (2 * c), gen ^ (3 * c), gen ^ (6 * c), gen ^ (12 * c), gen ^ (13 * c), gen ^ (26 * c),
        gen ^ (52 * c), gen ^ (53 * c), ccar * gen ^ (53 * c), crow * gen ^ c])
      1656 53 15 (chainVH Ht cs cv3)) 2451
    [gen, gen ^ c * gen, gen ^ c * gen + N, gen, gen ^ c * gen],
    by simp only [show Fn.params Data.core566 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7]
      from rfl, List.map_cons, List.map_nil]; b1_lookb, ?_⟩
  rw [core566_body, l95Body]
  simp only [holdsListB_append]
  rw [holdsListB_noRet (fsNextT (.n 10) (.n 11) (.n 13) 0 14) rfl,
    holdsListB_noRet (fsNextT (.n 27) (.n 28) (.n 29) 1 30) rfl,
    holdsListB_noRet (obsChainT (.n 43) (.n 44) (.n 54) 56 106) (noRetList_obsChainT ..),
    holdsListB_noRet (obsChainT (.n 1644) (.n 1645) (.n 1654) 1656 53) (noRetList_obsChainT ..)]
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_gen]
  b1_lookb
  rw [setb_lit (i := 2449) (by omega) (by omega), setb_lit (i := 2450) (by omega) (by omega)]
  have e52 : obsAllH Ht cv3 cs = obsCvH Ht (obsAllH Ht cv3 (cs.take 52)) (cs.getD 52 0) := by
    rw [← obsAllH_take_succ _ _ _ _ (by omega), List.take_of_length_le (by omega)]
  simp only [Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod, chainVH, OfNat.ofNat_ne_zero, ↓reduceIte,
    loadHolds_mul_gen_pow, Nat.add_zero, true_and, and_true]
  rw [e52] at o0 o1
  refine ⟨by ring, h0, h1, by ring,
    hF.fsNext _ _ _ _ _ ⟨⟨by b1_lookb; rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact q0, cv, cv1,
      by b1_lookb, by b1_lookb; exact a0,
      fun k h1 h2 => by b1_lookb⟩, trivial⟩,
    hF.fsNext _ _ _ _ _ ⟨⟨by b1_lookb; rw [loadHolds_mul_gen_pow]; exact q1, cv1, cv2,
      by b1_lookb; rfl,
      by b1_lookb; exact a1, fun k h1 h2 => by b1_lookb⟩, trivial⟩,
    by ring, by ring, by ring, by ring, by ring, by ring,
    by ring, by ring, by ring, wf, ?_, by ring, by ring, by ring, by ring, by ring, by ring, by ring,
    by ring, wc, ?_, o0, o1, hK, hnext⟩
  · refine obsChainC_complete hF _ _ _ _ _ _ fs hfl (cv := cv2) (by b1_lookb; rfl) (fun k hk => ?_)
      (fun k hk j hj1 hj2 => ?_) afs (by b1_lookb; exact hfr)
    · b1_lookb; simp [chainVH]
    · b1_lookb
      rw [Nat.add_assoc (56 + 15 * k) 1 j, setb_in (by omega) (by omega)]
      simp [chainVH]
  · have e105 : obsAllH Ht cv2 fs = obsCvH Ht (obsAllH Ht cv2 (fs.take 105)) (fs.getD 105 0) := by
      rw [← obsAllH_take_succ _ _ _ _ (by omega), List.take_of_length_le (by omega)]
    refine obsChainC_complete hF _ _ _ _ _ _ cs hcl (cv := cv3) ?_ (fun k hk => ?_)
      (fun k hk j hj1 hj2 => ?_) acs (by b1_lookb; exact hcr)
    · b1_lookb
      rw [setb_lit (i := 1644) (by omega) (by omega), setb_lit (i := 1645) (by omega) (by omega)]
      simp only [Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod, chainVH, OfNat.ofNat_ne_zero,
        ↓reduceIte]
      show _ = digestScalars (obsAllH Ht cv2 fs)
      rw [e105]; rfl
    · b1_lookb; simp [chainVH]
    · b1_lookb
      rw [Nat.add_assoc (1656 + 15 * k) 1 j, setb_in (by omega) (by omega)]
      simp [chainVH]

/-! ## `__loop96`, `__loop98` -/

theorem sqValsD_five (d : Digest) : sqValsD d 5 = (digestScalars d).1 := rfl

theorem sqValsD_six (d : Digest) : sqValsD d 6 = (digestScalars d).2 := rfl

theorem sqValsD_ch (d : Digest) : sqValsD d 13 = challengeOf d := rfl

/-- **`__loop96` at `x = g^c` over an answered hash, backward**: the row's words give the
iteration, its two squeezes answered. -/
theorem loop96C_back (hF : FsRowsC S H) {N bcc lam frow crow : E} (d c : ℕ) (cv : Digest)
    (fp cp acc fv cv' : E)
    (a0 : H (digestBytes cv ++ blockOf 0 2) = some (sqCvH Ht cv))
    (a1 : H (digestBytes (sqCvH Ht cv) ++ blockOf 0 2) = some (sqCvH Ht (sqCvH Ht cv)))
    (h0 : LoadHolds rd bcc (3 * c) (digestScalars cv).1)
    (h1 : LoadHolds rd bcc (3 * c + 1) (digestScalars cv).2)
    (l0 : LoadHolds rd lam (2 * c) (challengeOf (sqCvH Ht cv)))
    (l1 : LoadHolds rd lam (2 * c + 1) (challengeOf (sqCvH Ht (sqCvH Ht cv))))
    (s0 : LoadHolds rd bcc (3 * c + 3) (digestScalars (sqCvH Ht (sqCvH Ht cv))).1)
    (s1 : LoadHolds rd bcc (3 * c + 4) (digestScalars (sqCvH Ht (sqCvH Ht cv))).2)
    (hf : LoadHolds rd frow c fp) (hc : LoadHolds rd crow c cp)
    (ha : LoadHolds rd bcc (3 * c + 2) acc) (hfv : LoadHolds rd fp 22 fv)
    (hcv : LoadHolds rd cp 22 cv')
    (hn : LoadHolds rd bcc (3 * c + 5)
      (acc + challengeOf (sqCvH Ht cv) * fv + challengeOf (sqCvH Ht (sqCvH Ht cv)) * cv'))
    (hK : IsInK (gen ^ c * gen + N))
    (hnext : gen ^ c * gen + N ≠ 0 →
      coreProgram.relNB S rd d "__loop96" [gen ^ c * gen, N, bcc, lam, frow, crow] []) :
    coreProgram.relNB S rd (d + 1) "__loop96" [gen ^ c, N, bcc, lam, frow, crow] [] := by
  set x := gen ^ c with hx
  have e3 : bcc * (x * x * x) = bcc * gen ^ (3 * c) := by rw [hx]; ring
  have e2 : lam * (x * x) = lam * gen ^ (2 * c) := by rw [hx]; ring
  have ef : frow * x = frow * gen ^ c := rfl
  have ec : crow * x = crow * gen ^ c := rfl
  rw [relNS_succ_iff find_loop96]
  refine ⟨setl (setv (setv (setl (Val.ofArgs [x, N, bcc, lam, frow, crow]) 6
      [x * x, x * x * x, bcc * (x * x * x), (digestScalars cv).1, (digestScalars cv).2]) 11 14
      (sqValsD (sqCvH Ht cv))) 25 14 (sqValsD (sqCvH Ht (sqCvH Ht cv)))) 39
    [x * x, lam * (x * x), lam * (x * x), frow * x, fp, crow * x, cp, acc, fv,
      challengeOf (sqCvH Ht cv) * fv, acc + challengeOf (sqCvH Ht cv) * fv, cv',
      challengeOf (sqCvH Ht (sqCvH Ht cv)) * cv',
      acc + challengeOf (sqCvH Ht cv) * fv + challengeOf (sqCvH Ht (sqCvH Ht cv)) * cv', gen, x * gen,
      x * gen + N, gen, x * gen], by
        simp only [show Fn.params Data.core567 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5]
          from rfl, List.map_cons, List.map_nil]; b1_look, ?_⟩
  rw [core567_body, l96Body]
  simp only [holdsListB_append]
  rw [holdsListB_noRet (squeezeT (.n 9) (.n 10) 11) rfl,
    holdsListB_noRet (squeezeT (.n 16) (.n 17) 25) rfl]
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_gen]
  b1_look
  simp only [sqValsD_five, sqValsD_six, sqValsD_ch, e3, e2, ef, ec, loadHolds_mul_gen_pow, Nat.add_zero,
    true_and, and_true]
  refine ⟨h0, h1, hF.squeeze _ _ _ ⟨⟨cv, _, by b1_look, a0, fun k hk => by b1_look⟩, trivial⟩,
    hF.squeeze _ _ _ ⟨⟨sqCvH Ht cv, _, by b1_look; rfl, a1, fun k hk => by b1_look⟩, trivial⟩,
    l0, l1, hf, hc, s0, s1, ha, hfv, hcv, hn, hK, hnext⟩

/-- **`__loop98` at `x = g^c` over an answered hash, backward**: the row's words give the
iteration, its three squeezes answered. -/
theorem loop98C_back (hF : FsRowsC S H) {N mcc lam frow crow : E} (d c : ℕ) (cv : Digest)
    (fp cp acc fv ca cb : E)
    (a0 : H (digestBytes cv ++ blockOf 0 2) = some (sqCvH Ht cv))
    (a1 : H (digestBytes (sqCvH Ht cv) ++ blockOf 0 2) = some (sqCvH Ht (sqCvH Ht cv)))
    (a2 : H (digestBytes (sqCvH Ht (sqCvH Ht cv)) ++ blockOf 0 2) =
      some (sqCvH Ht (sqCvH Ht (sqCvH Ht cv))))
    (h0 : LoadHolds rd mcc (3 * c) (digestScalars cv).1)
    (h1 : LoadHolds rd mcc (3 * c + 1) (digestScalars cv).2)
    (l0 : LoadHolds rd lam (3 * c) (challengeOf (sqCvH Ht cv)))
    (l1 : LoadHolds rd lam (3 * c + 1) (challengeOf (sqCvH Ht (sqCvH Ht cv))))
    (l2 : LoadHolds rd lam (3 * c + 2) (challengeOf (sqCvH Ht (sqCvH Ht (sqCvH Ht cv)))))
    (s0 : LoadHolds rd mcc (3 * c + 3) (digestScalars (sqCvH Ht (sqCvH Ht (sqCvH Ht cv)))).1)
    (s1 : LoadHolds rd mcc (3 * c + 4) (digestScalars (sqCvH Ht (sqCvH Ht (sqCvH Ht cv)))).2)
    (hf : LoadHolds rd frow c fp) (hc : LoadHolds rd crow c cp)
    (ha : LoadHolds rd mcc (3 * c + 2) acc) (hfv : LoadHolds rd fp 105 fv)
    (hca : LoadHolds rd cp 51 ca) (hcb : LoadHolds rd cp 52 cb)
    (hn : LoadHolds rd mcc (3 * c + 5) (acc + challengeOf (sqCvH Ht cv) * fv +
      challengeOf (sqCvH Ht (sqCvH Ht cv)) * ca + challengeOf (sqCvH Ht (sqCvH Ht (sqCvH Ht cv))) * cb))
    (hK : IsInK (gen ^ c * gen + N))
    (hnext : gen ^ c * gen + N ≠ 0 →
      coreProgram.relNB S rd d "__loop98" [gen ^ c * gen, N, mcc, lam, frow, crow] []) :
    coreProgram.relNB S rd (d + 1) "__loop98" [gen ^ c, N, mcc, lam, frow, crow] [] := by
  set x := gen ^ c with hx
  have e3 : mcc * (x * x * x) = mcc * gen ^ (3 * c) := by rw [hx]; ring
  have e3' : lam * (x * x * x) = lam * gen ^ (3 * c) := by rw [hx]; ring
  have ef : frow * x = frow * gen ^ c := rfl
  have ec : crow * x = crow * gen ^ c := rfl
  rw [relNS_succ_iff find_loop98]
  refine ⟨setl (setv (setv (setv (setl (Val.ofArgs [x, N, mcc, lam, frow, crow]) 6
      [x * x, x * x * x, mcc * (x * x * x), (digestScalars cv).1, (digestScalars cv).2]) 11 14
      (sqValsD (sqCvH Ht cv))) 25 14 (sqValsD (sqCvH Ht (sqCvH Ht cv)))) 39 14
      (sqValsD (sqCvH Ht (sqCvH Ht (sqCvH Ht cv))))) 53
    [x * x, x * x * x, lam * (x * x * x), lam * (x * x * x), lam * (x * x * x), frow * x, fp,
      crow * x, cp, acc, fv, challengeOf (sqCvH Ht cv) * fv, acc + challengeOf (sqCvH Ht cv) * fv, ca,
      challengeOf (sqCvH Ht (sqCvH Ht cv)) * ca,
      acc + challengeOf (sqCvH Ht cv) * fv + challengeOf (sqCvH Ht (sqCvH Ht cv)) * ca, cb,
      challengeOf (sqCvH Ht (sqCvH Ht (sqCvH Ht cv))) * cb,
      acc + challengeOf (sqCvH Ht cv) * fv + challengeOf (sqCvH Ht (sqCvH Ht cv)) * ca +
        challengeOf (sqCvH Ht (sqCvH Ht (sqCvH Ht cv))) * cb, gen, x * gen, x * gen + N, gen, x * gen],
    by simp only [show Fn.params Data.core570 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] from rfl,
      List.map_cons, List.map_nil]; b1_look, ?_⟩
  rw [core570_body, l98Body]
  simp only [holdsListB_append]
  rw [holdsListB_noRet (squeezeT (.n 9) (.n 10) 11) rfl,
    holdsListB_noRet (squeezeT (.n 16) (.n 17) 25) rfl,
    holdsListB_noRet (squeezeT (.n 30) (.n 31) 39) rfl]
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_gen]
  b1_look
  simp only [sqValsD_five, sqValsD_six, sqValsD_ch, e3, e3', ef, ec, loadHolds_mul_gen_pow,
    Nat.add_zero, true_and, and_true]
  refine ⟨h0, h1, hF.squeeze _ _ _ ⟨⟨cv, _, by b1_look, a0, fun k hk => by b1_look⟩, trivial⟩,
    hF.squeeze _ _ _ ⟨⟨sqCvH Ht cv, _, by b1_look; rfl, a1, fun k hk => by b1_look⟩, trivial⟩,
    hF.squeeze _ _ _ ⟨⟨sqCvH Ht (sqCvH Ht cv), _, by b1_look; rfl, a2, fun k hk => by b1_look⟩,
      trivial⟩, l0, l1, l2, hf, hc, s0, s1, ha, hfv, hca, hcb, hn, hK, hnext⟩

end
end LeanVM.Guest.B1.Main
