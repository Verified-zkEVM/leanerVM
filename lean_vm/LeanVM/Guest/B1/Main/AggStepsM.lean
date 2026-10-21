/-
  LeanVM.Guest.B1.Main.AggStepsM

  One iteration of each batching loop of `aggregate_claims`, read forward over a hash model
  (`AggSteps.lean`, `AggLoop99.lean` over a `HashModel`).
-/

module

public import LeanVM.Guest.B1.Main.AggChainM
public import LeanVM.Guest.B1.Main.AggLoop99

/-!
# The batching loops over a hash model, forward

The transcript loop (`__loop95`) and the lambda loops (`__loop96`, `__loop98`) hash: at `x = g^c`,
their iterations over `M.sem` give what they read and store with each absorb and squeeze answered
by the model (`loop95_stepM`, `loop96_stepM`, `loop98_stepM`). The weight loops (`__loop97`,
`__loop99`) are free of `BLAKE2S`, so their deployed iterations hold under every semantics
(`loop97_stepB`, `loop99_stepB`, by `Core.relB_iff_rel_of_freeOn`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {M : HashModel} {rd : Reader}

/-- **A block with no `BLAKE2S` atom and no call** holds under any semantics exactly when it holds
under the deployed one. -/
theorem holdsListB_noCall {S : BlakeSem} {C : CallRel} {σ : Val} {ss : List Stmt}
    (hfree : Stmt.freeInList [] ss = true) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsListB S C rd σ ss next kret ↔ Stmt.HoldsList C rd σ ss next kret := by
  rw [holdsListB_freeIn (S' := blakeDeployed) (C' := C) (fun f hf => by simp at hf) ss hfree,
    holdsListB_deployed]

/-! ## The weight loops, free of `BLAKE2S` -/

/-- `__loop97` is free of `BLAKE2S` and calls only itself. -/
theorem freeOn_loop97 : coreProgram.FreeOn ["__loop97"] = true := by decide +kernel

/-- `__loop99` is free of `BLAKE2S` and calls only itself. -/
theorem freeOn_loop99 : coreProgram.FreeOn ["__loop99"] = true := by decide +kernel

/-- **`__loop97` at `x` under any semantics** (`loop97_step`). -/
theorem loop97_stepB {S : BlakeSem} {N frow crow bcp wsum lam : E} (x : E)
    (h : coreProgram.RelB S rd "__loop97" [x, N, frow, crow, bcp, wsum, lam] []) :
    (∀ c, x = gen ^ c → ∃ fp cp : E, LoadHolds rd frow c fp ∧ LoadHolds rd crow c cp ∧
      ∃ r f g : List E, r.length = 22 ∧ f.length = 22 ∧ g.length = 22 ∧ ReadsAt rd bcp r ∧
        ReadsAt rd fp f ∧ ReadsAt rd cp g ∧ ∃ w lf lc : E, LoadHolds rd wsum c w ∧
        LoadHolds rd lam (2 * c) lf ∧ LoadHolds rd lam (2 * c + 1) lc ∧
        LoadHolds rd wsum (c + 1) (w + lf * eqEval f r + lc * eqEval g r)) ∧
      (x * gen + N ≠ 0 →
        coreProgram.RelB S rd "__loop97" [x * gen, N, frow, crow, bcp, wsum, lam] []) := by
  rw [relB_iff_rel_of_freeOn freeOn_loop97 (List.mem_singleton_self _)] at h
  obtain ⟨h1, h2⟩ := loop97_step x h
  exact ⟨h1, fun hne => (relB_iff_rel_of_freeOn freeOn_loop97 (List.mem_singleton_self _) _ _).mpr
    (h2 hne)⟩

/-- **`__loop99` at `x` under any semantics** (`loop99_step`). -/
theorem loop99_stepB {S : BlakeSem} {N frow eqR mp eqC crow lamm wsums : E} (x : E)
    (h : coreProgram.RelB S rd "__loop99" [x, N, frow, eqR, mp, eqC, crow, lamm, wsums] []) :
    (∀ c, x = gen ^ c → ∃ fp cp : E, LoadHolds rd frow c fp ∧ LoadHolds rd crow c cp ∧
      LoadHolds rd wsums (2 * c + 2) (cellAt rd wsums (2 * c) + cellAt rd lamm (3 * c) *
        guestU (cellAt rd fp 24) (fun k => cellAt rd fp (25 + k)) (fun j => cellAt rd fp (33 + j))
          (fun i => cellAt rd fp (41 + i)) (fun i => cellAt rd eqR (62 + i))
          (fun i => cellAt rd eqC (62 + i)) (fun k => cellAt rd mp k) +
        cellAt rd lamm (3 * c + 1) *
          ∏ k ∈ Finset.range 28, (1 + cellAt rd cp (23 + k) + cellAt rd mp k)) ∧
      LoadHolds rd wsums (2 * c + 3) (cellAt rd wsums (2 * c + 1) +
        cellAt rd lamm (3 * c) * cellAt rd fp 23 *
          guestU (cellAt rd fp 24) (fun k => cellAt rd fp (25 + k)) (fun j => cellAt rd fp (33 + j))
            (fun i => cellAt rd fp (41 + i)) (fun i => cellAt rd eqR (62 + i))
            (fun i => cellAt rd eqC (62 + i)) (fun k => cellAt rd mp k) +
        cellAt rd lamm (3 * c + 2) *
          ∏ k ∈ Finset.range 28, (1 + cellAt rd cp (23 + k) + cellAt rd mp k))) ∧
      (x * gen + N ≠ 0 → coreProgram.RelB S rd "__loop99"
        [x * gen, N, frow, eqR, mp, eqC, crow, lamm, wsums] []) := by
  rw [relB_iff_rel_of_freeOn freeOn_loop99 (List.mem_singleton_self _)] at h
  obtain ⟨h1, h2⟩ := loop99_step x h
  exact ⟨h1, fun hne => (relB_iff_rel_of_freeOn freeOn_loop99 (List.mem_singleton_self _) _ _).mpr
    (h2 hne)⟩

/-! ## The transcript -/

/-- **`__loop95` at `x = g^c` over a model** (`loop95_step`): from the transcript row `c`, the
state of `cv`, the child's public input's cells, its fresh and carried cells are absorbed, every
absorb answered, into row `c + 1`, the pointers stored. -/
theorem loop95_stepM {N absorb cpi cfresh frow ccar crow : E} (x : E)
    (h : coreProgram.RelB M.sem rd "__loop95" [x, N, absorb, cpi, cfresh, frow, ccar, crow] []) :
    (∀ c, x = gen ^ c → ∃ s0 s1, LoadHolds rd absorb (2 * c) s0 ∧
      LoadHolds rd absorb (2 * c + 1) s1 ∧ ∀ cv, (s0, s1) = digestScalars cv →
      ∃ (p0 p1 : E) (fs cs : List E), LoadHolds rd cpi (2 * c) p0 ∧ LoadHolds rd cpi (2 * c + 1) p1 ∧
        fs.length = 106 ∧ ReadsAt rd (cfresh * gen ^ (106 * c)) fs ∧ cs.length = 53 ∧
        ReadsAt rd (ccar * gen ^ (53 * c)) cs ∧ LoadHolds rd frow c (cfresh * gen ^ (106 * c)) ∧
        LoadHolds rd crow c (ccar * gen ^ (53 * c)) ∧
        ∃ cv', obsAllM M cv (p0 :: p1 :: (fs ++ cs)) = some cv' ∧
          LoadHolds rd absorb (2 * c + 2) (digestScalars cv').1 ∧
          LoadHolds rd absorb (2 * c + 3) (digestScalars cv').2) ∧
      (x * gen + N ≠ 0 →
        coreProgram.RelB M.sem rd "__loop95" [x * gen, N, absorb, cpi, cfresh, frow, ccar, crow] []) := by
  rw [relB_iff_sem find_loop95] at h
  obtain ⟨σ, hp, h⟩ := h
  simp only [show Fn.params Data.core566 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := hp
  rw [core566_body, l95Body] at h
  simp only [holdsListB_append] at h
  rw [holdsListB_noRet (fsNextT (.n 10) (.n 11) (.n 13) 0 14) rfl,
    holdsListB_noRet (fsNextT (.n 27) (.n 28) (.n 29) 1 30) rfl,
    holdsListB_noRet (obsChainT (.n 43) (.n 44) (.n 54) 56 106) (noRetList_obsChainT ..),
    holdsListB_noRet (obsChainT (.n 1644) (.n 1645) (.n 1654) 1656 53) (noRetList_obsChainT ..)] at h
  generalize hF1 : Stmt.HoldsListB M.sem (coreProgram.RelB M.sem rd) rd σ
    (fsNextT (.n 10) (.n 11) (.n 13) 0 14) True (fun rs => rs = []) = F1 at h
  generalize hF2 : Stmt.HoldsListB M.sem (coreProgram.RelB M.sem rd) rd σ
    (fsNextT (.n 27) (.n 28) (.n 29) 1 30) True (fun rs => rs = []) = F2 at h
  generalize hC1 : Stmt.HoldsListB M.sem (coreProgram.RelB M.sem rd) rd σ
    (obsChainT (.n 43) (.n 44) (.n 54) 56 106) True (fun rs => rs = []) = C1 at h
  generalize hC2 : Stmt.HoldsListB M.sem (coreProgram.RelB M.sem rd) rd σ
    (obsChainT (.n 1644) (.n 1645) (.n 1654) 1656 53) True (fun rs => rs = []) = C2 at h
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_gen] at h
  obtain ⟨h8, h9, l10, l11, h12, h13, hf1, h29, hf2, h45, h46, h47, h48, h49, h50, h51, h52, h53,
    h54, h55, l54, hc1, h1646, h1647, h1648, h1649, h1650, h1651, h1652, h1653, h1654, h1655, l1654,
    hc2, l2449, l2450, c2451, h2452, h2453, c2454, h2455, -, hcall, -⟩ := h
  refine ⟨fun c hx => ?_, fun hne => ?_⟩
  swap
  · have := hcall (by rw [h2453, h2452, c2451, p0, p1]; exact hne)
    rwa [h2455, c2454, p0, p1, p2, p3, p4, p5, p6, p7] at this
  have e9 : σ (.n 9) = absorb * gen ^ (2 * c) := by rw [h9, h8, p2, p0, hx, ← pow_add]; ring_nf
  have e13 : σ (.n 13) = cpi * gen ^ (2 * c) := by rw [h13, h12, p3, p0, hx, ← pow_add]; ring_nf
  have e29 : σ (.n 29) = cpi * gen ^ (2 * c) := by rw [h29, h12, p3, p0, hx, ← pow_add]; ring_nf
  have e53 : σ (.n 53) = gen ^ (106 * c) := by
    rw [h53, h52, h51, h50, h49, h48, h47, h46, h45, p0, hx]; ring
  have e1653 : σ (.n 1653) = gen ^ (53 * c) := by
    rw [h1653, h1652, h1651, h1650, h1649, h1648, h1647, h1646, p0, hx]; ring
  rw [e9, loadHolds_mul_gen_pow, Nat.add_zero] at l10
  rw [e9, loadHolds_mul_gen_pow] at l11
  refine ⟨σ (.n 10), σ (.n 11), l10, l11, fun cv hcv => ?_⟩
  obtain ⟨q14, d1, hd1, s27⟩ := fsNext_outM (holdsB_fsNextT _ _ _ _ _ (hF1 ▸ hf1)).1 hcv
  obtain ⟨q30, d2, hd2, s43⟩ := fsNext_outM (holdsB_fsNextT _ _ _ _ _ (hF2 ▸ hf2)).1 s27
  obtain ⟨⟨fs, hfl, hfr, d3, hd3, s1644⟩, -⟩ := obsChain_soundM _ _ _ _ _ (hC1 ▸ hc1) s43
  obtain ⟨⟨cs, hcl, hcr, d4, hd4, s2449⟩, -⟩ := obsChain_soundM _ _ _ _ _ (hC2 ▸ hc2) s1644
  rw [e13, loadHolds_mul_gen_pow, Nat.add_zero] at q14
  rw [e29, loadHolds_mul_gen_pow] at q30
  rw [h54, p4, e53] at hfr l54
  rw [h1654, p6, e1653] at hcr l1654
  rw [h55, p5, p0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at l54
  rw [h1655, p7, p0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at l1654
  have hall : obsAllM M cv (σ (.n 14) :: σ (.n 30) :: (fs ++ cs)) = some d4 := by
    simp only [obsAllM, hd1, Option.bind_some, hd2, obsAllM_append, hd3, hd4]
  rw [e9, loadHolds_mul_gen_pow] at l2449 l2450
  refine ⟨σ (.n 14), σ (.n 30), fs, cs, q14, q30, hfl, hfr, hcl, hcr, l54, l1654, d4, hall, ?_, ?_⟩
  · rw [← s2449]
    simpa [chainS0] using l2449
  · rw [← s2449]
    simpa [chainS1] using l2450

/-! ## The lambdas -/

/-- **`__loop96` at `x = g^c` over a model** (`loop96_step`): from row `c` of the chain, the state
of `cv`, two answered squeezes give the bytecode lambdas; row `c + 1` holds the new state and the
running claim. -/
theorem loop96_stepM {N bcc lam frow crow : E} (x : E)
    (h : coreProgram.RelB M.sem rd "__loop96" [x, N, bcc, lam, frow, crow] []) :
    (∀ c, x = gen ^ c → ∃ s0 s1, LoadHolds rd bcc (3 * c) s0 ∧ LoadHolds rd bcc (3 * c + 1) s1 ∧
      ∀ cv, (s0, s1) = digestScalars cv → ∃ a b, sqCvM M cv = some a ∧ sqCvM M a = some b ∧
      LoadHolds rd lam (2 * c) (challengeOf a) ∧
      LoadHolds rd lam (2 * c + 1) (challengeOf b) ∧
      LoadHolds rd bcc (3 * c + 3) (digestScalars b).1 ∧
      LoadHolds rd bcc (3 * c + 4) (digestScalars b).2 ∧
      ∃ fp cp acc fv cv' : E, LoadHolds rd frow c fp ∧ LoadHolds rd crow c cp ∧
        LoadHolds rd bcc (3 * c + 2) acc ∧ LoadHolds rd fp 22 fv ∧ LoadHolds rd cp 22 cv' ∧
        LoadHolds rd bcc (3 * c + 5) (acc + challengeOf a * fv + challengeOf b * cv')) ∧
      (x * gen + N ≠ 0 →
        coreProgram.RelB M.sem rd "__loop96" [x * gen, N, bcc, lam, frow, crow] []) := by
  rw [relB_iff_sem find_loop96] at h
  obtain ⟨σ, hp, h⟩ := h
  simp only [show Fn.params Data.core567 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := hp
  rw [core567_body, l96Body] at h
  simp only [holdsListB_append] at h
  rw [holdsListB_noRet (squeezeT (.n 9) (.n 10) 11) rfl,
    holdsListB_noRet (squeezeT (.n 16) (.n 17) 25) rfl] at h
  generalize hS1 : Stmt.HoldsListB M.sem (coreProgram.RelB M.sem rd) rd σ
    (squeezeT (.n 9) (.n 10) 11) True (fun rs => rs = []) = S1 at h
  generalize hS2 : Stmt.HoldsListB M.sem (coreProgram.RelB M.sem rd) rd σ
    (squeezeT (.n 16) (.n 17) 25) True (fun rs => rs = []) = S2 at h
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_gen] at h
  obtain ⟨h6, h7, h8, l9, l10, hs1, hs2, h39, h40, l24, h41, l38, h42, l43, h44, l45, l30, l31,
    l46, l47, h48, h49, l50, h51, h52, l52, c53, h54, h55, c56, h57, -, hcall, -⟩ := h
  refine ⟨fun c hx => ?_, fun hne => ?_⟩
  swap
  · have := hcall (by rw [h55, h54, c53, p0, p1]; exact hne)
    rwa [h57, c56, p0, p1, p2, p3, p4, p5] at this
  have e8 : σ (.n 8) = bcc * gen ^ (3 * c) := by rw [h8, h7, h6, p2, p0, hx]; ring
  have e40 : σ (.n 40) = lam * gen ^ (2 * c) := by rw [h40, h39, p3, p0, hx]; ring
  have e41 : σ (.n 41) = lam * gen ^ (2 * c) := by rw [h41, h39, p3, p0, hx]; ring
  rw [e8, loadHolds_mul_gen_pow, Nat.add_zero] at l9
  rw [e8, loadHolds_mul_gen_pow] at l10
  refine ⟨σ (.n 9), σ (.n 10), l9, l10, fun cv hcv => ?_⟩
  obtain ⟨a, ha, q16, q24⟩ := squeeze_outM (holdsB_squeezeT _ _ _ (hS1 ▸ hs1)).1 hcv
  obtain ⟨b, hb, q30, q38⟩ := squeeze_outM (holdsB_squeezeT _ _ _ (hS2 ▸ hs2)).1 q16
  simp only [Nat.reduceAdd] at q16 q24 q30 q38
  rw [e40, loadHolds_mul_gen_pow, Nat.add_zero, q24] at l24
  rw [e41, loadHolds_mul_gen_pow, q38] at l38
  rw [e8, loadHolds_mul_gen_pow] at l30 l31 l46 l52
  rw [h42, p4, p0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at l43
  rw [h44, p5, p0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at l45
  refine ⟨a, b, ha, hb, l24, l38, ?_, ?_, σ (.n 43), σ (.n 45), σ (.n 46), σ (.n 47), σ (.n 50),
    l43, l45, l46, l47, l50, ?_⟩
  · rw [← congrArg Prod.fst q30]; exact l30
  · rw [← congrArg Prod.snd q30]; exact l31
  · rw [h52, h51, h49, h48, q24, q38] at l52; exact l52

/-- **`__loop98` at `x = g^c` over a model** (`loop98_step`): from row `c` of the chain, the state
of `cv`, three answered squeezes give the matrix lambdas; row `c + 1` holds the new state and the
running claim. -/
theorem loop98_stepM {N mcc lam frow crow : E} (x : E)
    (h : coreProgram.RelB M.sem rd "__loop98" [x, N, mcc, lam, frow, crow] []) :
    (∀ c, x = gen ^ c → ∃ s0 s1, LoadHolds rd mcc (3 * c) s0 ∧ LoadHolds rd mcc (3 * c + 1) s1 ∧
      ∀ cv, (s0, s1) = digestScalars cv → ∃ a b e, sqCvM M cv = some a ∧ sqCvM M a = some b ∧
      sqCvM M b = some e ∧
      LoadHolds rd lam (3 * c) (challengeOf a) ∧
      LoadHolds rd lam (3 * c + 1) (challengeOf b) ∧
      LoadHolds rd lam (3 * c + 2) (challengeOf e) ∧
      LoadHolds rd mcc (3 * c + 3) (digestScalars e).1 ∧
      LoadHolds rd mcc (3 * c + 4) (digestScalars e).2 ∧
      ∃ fp cp acc fv ca cb : E, LoadHolds rd frow c fp ∧ LoadHolds rd crow c cp ∧
        LoadHolds rd mcc (3 * c + 2) acc ∧ LoadHolds rd fp 105 fv ∧ LoadHolds rd cp 51 ca ∧
        LoadHolds rd cp 52 cb ∧
        LoadHolds rd mcc (3 * c + 5) (acc + challengeOf a * fv + challengeOf b * ca +
          challengeOf e * cb)) ∧
      (x * gen + N ≠ 0 →
        coreProgram.RelB M.sem rd "__loop98" [x * gen, N, mcc, lam, frow, crow] []) := by
  rw [relB_iff_sem find_loop98] at h
  obtain ⟨σ, hp, h⟩ := h
  simp only [show Fn.params Data.core570 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := hp
  rw [core570_body, l98Body] at h
  simp only [holdsListB_append] at h
  rw [holdsListB_noRet (squeezeT (.n 9) (.n 10) 11) rfl,
    holdsListB_noRet (squeezeT (.n 16) (.n 17) 25) rfl,
    holdsListB_noRet (squeezeT (.n 30) (.n 31) 39) rfl] at h
  generalize hS1 : Stmt.HoldsListB M.sem (coreProgram.RelB M.sem rd) rd σ
    (squeezeT (.n 9) (.n 10) 11) True (fun rs => rs = []) = S1 at h
  generalize hS2 : Stmt.HoldsListB M.sem (coreProgram.RelB M.sem rd) rd σ
    (squeezeT (.n 16) (.n 17) 25) True (fun rs => rs = []) = S2 at h
  generalize hS3 : Stmt.HoldsListB M.sem (coreProgram.RelB M.sem rd) rd σ
    (squeezeT (.n 30) (.n 31) 39) True (fun rs => rs = []) = S3 at h
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_gen] at h
  obtain ⟨h6, h7, h8, l9, l10, hs1, hs2, hs3, h53, h54, h55, l24, h56, l38, h57, l52, h58, l59,
    h60, l61, l44, l45, l62, l63, h64, h65, l66, h67, h68, l69, h70, h71, l71, c72, h73, h74, c75,
    h76, -, hcall, -⟩ := h
  refine ⟨fun c hx => ?_, fun hne => ?_⟩
  swap
  · have := hcall (by rw [h74, h73, c72, p0, p1]; exact hne)
    rwa [h76, c75, p0, p1, p2, p3, p4, p5] at this
  have e8 : σ (.n 8) = mcc * gen ^ (3 * c) := by rw [h8, h7, h6, p2, p0, hx]; ring
  have e55 : σ (.n 55) = lam * gen ^ (3 * c) := by rw [h55, h54, h53, p3, p0, hx]; ring
  have e56 : σ (.n 56) = lam * gen ^ (3 * c) := by rw [h56, h54, h53, p3, p0, hx]; ring
  have e57 : σ (.n 57) = lam * gen ^ (3 * c) := by rw [h57, h54, h53, p3, p0, hx]; ring
  rw [e8, loadHolds_mul_gen_pow, Nat.add_zero] at l9
  rw [e8, loadHolds_mul_gen_pow] at l10
  refine ⟨σ (.n 9), σ (.n 10), l9, l10, fun cv hcv => ?_⟩
  obtain ⟨a, ha, q16, q24⟩ := squeeze_outM (holdsB_squeezeT _ _ _ (hS1 ▸ hs1)).1 hcv
  obtain ⟨b, hb, q30, q38⟩ := squeeze_outM (holdsB_squeezeT _ _ _ (hS2 ▸ hs2)).1 q16
  obtain ⟨e, he, q44, q52⟩ := squeeze_outM (holdsB_squeezeT _ _ _ (hS3 ▸ hs3)).1 q30
  simp only [Nat.reduceAdd] at q16 q24 q30 q38 q44 q52
  rw [e55, loadHolds_mul_gen_pow, Nat.add_zero, q24] at l24
  rw [e56, loadHolds_mul_gen_pow, q38] at l38
  rw [e57, loadHolds_mul_gen_pow, q52] at l52
  rw [e8, loadHolds_mul_gen_pow] at l44 l45 l62 l71
  rw [h58, p4, p0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at l59
  rw [h60, p5, p0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at l61
  refine ⟨a, b, e, ha, hb, he, l24, l38, l52, ?_, ?_, σ (.n 59), σ (.n 61), σ (.n 62), σ (.n 63),
    σ (.n 66), σ (.n 69), l59, l61, l62, l63, l66, l69, ?_⟩
  · rw [← congrArg Prod.fst q44]; exact l44
  · rw [← congrArg Prod.snd q44]; exact l45
  · rw [h71, h70, h68, h67, h65, h64, q24, q38, q52] at l71; exact l71

end
end LeanVM.Guest.B1.Main
