/-
  LeanVM.Guest.B1.VerifySub.H.Match

  `verify_sub`'s frames on an honest child are its callees: names, arguments, results; its
  dispatch's selector; its allocations' sizes and pointers.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Sigma

/-!
# The frames

`vs_rets`: a call's results are its result variables' values. `vs_callsMatch`: the thirteen
frames are the callees (`ChildSegs.kids`) on their results. `vs_dispOk`: the dispatch's selector
names one of its callees. `vs_alloc_sizes`, `vs_alloc_bases`: the allocations are the own buffers.
`ChildSegs.ownW_lens`: the own buffers' lengths the loads need.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

variable {bytecode : List K} {seed : Digest} {c : Child} {S : ChildSegs bytecode seed c}
  {bs : List ℕ} {sqE : ℕ} {outs : List (List E × Main.Layout)} {args : List E} {σ : Val}

/-- **A call's results** are its result variables' values. -/
theorem vs_rets (G : VsSig S bs sqE outs args σ) (j : ℕ) (hj : j < 13)
    (hlen : (vsRetVars.getD j []).length = (outs.getD j ([], [])).1.length) :
    ((vsRetVars.getD j []).map V.n).map σ = (outs.getD j ([], [])).1 := by
  apply List.ext_getElem (by simp only [List.length_map]; exact hlen)
  intro k h1 h2
  have hk : k < (vsRetVars.getD j []).length := by simpa using h1
  rw [List.getElem_map, List.getElem_map, ← List.getD_eq_getElem _ 0 hk, G.ret j hj k hk,
    List.getD_eq_getElem _ _ h2]

/-- The selector's candidate is below the dispatch's `28` callees. -/
theorem ChildSegs.candidate_lt (S : ChildSegs bytecode seed c) :
    B1.Whir.candidate S.μs S.rate < 28 := by
  have h1 : S.μs ≤ 28 := S.hmu28
  have h2 := S.hr4
  unfold B1.Whir.candidate
  omega

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
/-- **`verify_sub`'s frames are its callees.** -/
theorem vs_callsMatch (hbl : bytecode.length = 2 ^ 23) {lpE outE : ℕ}
    (hargs : args = [(digestScalars (statementDigest seed c.statement)).1,
      (digestScalars (statementDigest seed c.statement)).2, (digestScalars seed).1,
      (digestScalars seed).2, ofK (gpow lpE), ofK (gpow sqE), ofK (gpow outE)])
    (G : VsSig S bs sqE outs args σ) (O : VsOuts S bs lpE sqE outs) :
    CallsMatch σ ((vsCPre.filterMap (Core.Stmt.callSF σ)).map (mkCall σ))
      (kidsAt (S.kids bs lpE sqE) [] outs) outs := by
  have R := G.ret
  have P := G.ptr
  -- the parameters
  have a0 : σ (.n 0) = (digestScalars (statementDigest seed c.statement)).1 := by
    rw [G.par 0 (by norm_num), hargs]; rfl
  have a1 : σ (.n 1) = (digestScalars (statementDigest seed c.statement)).2 := by
    rw [G.par 1 (by norm_num), hargs]; rfl
  have a4 : σ (.n 4) = ofK (gpow lpE) := by rw [G.par 4 (by norm_num), hargs]; rfl
  have a5 : σ (.n 5) = ofK (gpow sqE) := by rw [G.par 5 (by norm_num), hargs]; rfl
  -- the pointers
  have q7 : σ (.n 7) = ofK (gpow (vb bs 0)) := P 0 (by norm_num)
  have q8 : σ (.n 8) = ofK (gpow (vb bs 1)) := P 1 (by norm_num)
  have q28 : σ (.n 28) = ofK (gpow (vb bs 3)) := P 3 (by norm_num)
  have q129 : σ (.n 129) = ofK (gpow (vb bs 4)) := P 4 (by norm_num)
  have q141 : σ (.n 141) = ofK (gpow (vb bs 5)) := P 5 (by norm_num)
  have q149 : σ (.n 149) = ofK (gpow (vb bs 6)) := P 6 (by norm_num)
  have q523 : σ (.n 523) = ofK (gpow (vb bs 7)) := P 7 (by norm_num)
  have q640 : σ (.n 640) = ofK (gpow (vb bs 9)) := P 9 (by norm_num)
  have q848 : σ (.n 848) = ofK (gpow (vb bs 10)) := P 10 (by norm_num)
  have q859 : σ (.n 859) = ofK (gpow (vb bs 11)) := P 11 (by norm_num)
  have q860 : σ (.n 860) = ofK (gpow (vb bs 12)) := P 12 (by norm_num)
  have q876 : σ (.n 876) = ofK (gpow (vb bs 13)) := P 13 (by norm_num)
  have q877 : σ (.n 877) = ofK (gpow (vb bs 14)) := P 14 (by norm_num)
  have q1324 : σ (.n 1324) = ofK (gpow (vb bs 15)) := P 15 (by norm_num)
  -- the results
  obtain ⟨-, -, -, ⟨K5, hK5⟩⟩ := S.runG' hbl
  obtain ⟨K7, hK7⟩ := S.s7_capOf hbl
  obtain ⟨e2, e120, e121, h9, -⟩ := O.o9
  obtain ⟨pb, pb1, h11, -⟩ := O.o11
  have r130 : σ (.n 130) = gen ^ S.logMem := by
    rw [show σ (.n 130) = _ from R 1 (by norm_num) 0 (by decide), O.o1]; rfl
  have r522 : σ (.n 522) = gen ^ S.μ := by
    rw [show σ (.n 522) = _ from R 2 (by norm_num) 0 (by decide), O.o2]; simp [ChildSegs.μ]
  have r5 : ∀ i < 9, σ (.n (839 + i)) = (outs.getD 5 ([], [])).1.getD i 0 := fun i hi ↦ by
    rw [← vsRetVars_runs.1 i hi]; exact R 5 (by norm_num) i (by rw [vsRetVars_lens.1]; exact hi)
  have r6 : ∀ i < 9, σ (.n (849 + i)) = (outs.getD 6 ([], [])).1.getD i 0 := fun i hi ↦ by
    rw [← vsRetVars_runs.2.1 i hi]; exact R 6 (by norm_num) i (by rw [vsRetVars_lens.2.1]; exact hi)
  have r844 : σ (.n 844) = ofK (gpow (S.cT bs)) := by
    rw [show σ (.n 844) = _ from r5 5 (by norm_num), O.o5, hK5]
    exact Tables.tb_ofK_gpow_mul _ _
  have r854 : σ (.n 854) = ofK (gpow (S.cK bs)) := by
    rw [show σ (.n 854) = _ from r6 5 (by norm_num), O.o6]
    show ofK (gpow (S.cT bs)) * gen ^ 5 * gen ^ (3 * S.H.n) * gen ^ 157 = _
    rw [Tables.tb_ofK_gpow_mul, Tables.tb_ofK_gpow_mul, Tables.tb_ofK_gpow_mul, ChildSegs.cK,
      (S.H_run hbl).2.2.2, show S.cT bs + 5 + 3 * S.H.n + 157 = S.cT bs + (5 + 3 * S.H.n + 157) by
        omega]
  have r855 : σ (.n 855) = gen ^ S.H.n := by
    rw [show σ (.n 855) = _ from r6 6 (by norm_num), O.o6]; rfl
  have r857 : σ (.n 857) = S.H.rm := by
    rw [show σ (.n 857) = _ from r6 8 (by norm_num), O.o6]; rfl
  have r868 : σ (.n 868) = ofK (gpow (S.cW bs)) := by
    rw [show σ (.n 868) = _ from R 7 (by norm_num) 5 (by decide), O.o7, hK7]
    exact Tables.tb_ofK_gpow_mul _ _
  have r1887 : σ (.n 1887) = gen ^ Tables.stackTotal S.kappas := by
    rw [show σ (.n 1887) = _ from R 9 (by norm_num) 0 (by decide), h9]; rfl
  have e6 : [σ (.n 849), σ (.n 850), σ (.n 851), σ (.n 852), σ (.n 853)] = S.s6.cap := by
    rw [S.s6_capOf hbl, show σ (.n 849) = _ from r6 0 (by norm_num),
      show σ (.n 850) = _ from r6 1 (by norm_num), show σ (.n 851) = _ from r6 2 (by norm_num),
      show σ (.n 852) = _ from r6 3 (by norm_num), show σ (.n 853) = _ from r6 4 (by norm_num),
      O.o6]
    rfl
  have hpl : S.point.length = S.μ := (S.runG' hbl).2.2.1
  have hvl := S.vals_length hbl
  have hc28 := S.candidate_lt
  -- the frames
  rw [vs_calls σ]
  refine callsMatch_kidsAt _ _ _ _ (by simp [vsCallsA, vsCallsB, ChildSegs.kids])
    (by rw [ChildSegs.kids_length, O.len]) fun j hj ↦ ?_
  have hj' : j < 13 := by simpa [vsCallsA, vsCallsB] using hj
  interval_cases j
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets G 0 (by norm_num) 
      (by rw [O.o0]; simp only [List.length_cons, List.length_nil]; rfl)⟩⟩
    show [σ (.n 112)] = [eOfNat S.rate]
    rw [G.e112]
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets G 1 (by norm_num) 
      (by rw [O.o1]; simp only [List.length_cons, List.length_nil]; rfl)⟩⟩
    show [σ (.n 29)] = [eOfNat S.logMem]
    rw [G.e29]
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets G 2 (by norm_num) 
      (by rw [O.o2]; simp only [List.length_cons, List.length_nil]; rfl)⟩⟩
    show [σ (.n 521), σ (.n 4), σ (.n 5)] =
      [gen ^ pushTotal S.logMem S.hs, ofK (gpow lpE), ofK (gpow sqE)]
    rw [G.e521, a4, a5]
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets G 3 (by norm_num) 
      (by rw [O.o3]; simp only [List.length_cons, List.length_nil]; rfl)⟩⟩
    show [σ (.n 537)] = [S.x0]
    rw [G.e537]
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets G 4 (by norm_num) 
      (by rw [O.o4]; simp only [List.length_cons, List.length_nil]; rfl)⟩⟩
    show [σ (.n 547)] = [S.x1]
    rw [G.e547]
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets G 5 (by norm_num)
      (by rw [vsRetVars_lens.1, O.o5, hK5]; simp [capOf, hvl])⟩⟩
    show [σ (.n 825), σ (.n 826), σ (.n 827), σ (.n 828), σ (.n 829), σ (.n 838), σ (.n 522),
      σ (.n 523)] = S.capS ++ [ofK (gpow (vcG bs)), gen ^ S.μ, ofK (gpow (vb bs 7))]
    rw [← G.e825, G.e838, r522, q523]; rfl
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets G 6 (by norm_num)
      (by rw [vsRetVars_lens.2.1, O.o6]; simp [Tables.VtHonest.retsH, Fs.squeeze, capOf])⟩⟩
    show [σ (.n 839), σ (.n 840), σ (.n 841), σ (.n 842), σ (.n 843), σ (.n 844), σ (.n 0),
      σ (.n 1), σ (.n 523), σ (.n 522), σ (.n 129), σ (.n 28), σ (.n 149), σ (.n 5), σ (.n 640),
      σ (.n 836), σ (.n 7), σ (.n 8), σ (.n 848), σ (.n 845), σ (.n 846), σ (.n 847)] =
      [S.s5.cap.getD 0 0, S.s5.cap.getD 1 0, S.s5.cap.getD 2 0, S.s5.cap.getD 3 0,
        S.s5.cap.getD 4 0, ofK (gpow (S.cT bs)), (digestScalars (statementDigest seed c.statement)).1,
        (digestScalars (statementDigest seed c.statement)).2, ofK (gpow (vb bs 7)),
        gen ^ S.point.length, ofK (gpow (vb bs 4)), ofK (gpow (vb bs 3)), ofK (gpow (vb bs 6)),
        ofK (gpow sqE), ofK (gpow (vb bs 9)), S.β, ofK (gpow (vb bs 0)), ofK (gpow (vb bs 1)),
        ofK (gpow (vb bs 10)), S.vals.getD 0 0, S.vals.getD 1 0, S.vals.getD 2 0]
    rw [show σ (.n 839) = _ from r5 0 (by norm_num), show σ (.n 840) = _ from r5 1 (by norm_num),
      show σ (.n 841) = _ from r5 2 (by norm_num), show σ (.n 842) = _ from r5 3 (by norm_num),
      show σ (.n 843) = _ from r5 4 (by norm_num), show σ (.n 845) = _ from r5 6 (by norm_num),
      show σ (.n 846) = _ from r5 7 (by norm_num), show σ (.n 847) = _ from r5 8 (by norm_num),
      r844, a0, a1, q523, r522, hpl, q129, q28, q149, a5, q640, G.e836, q7, q8, q848, O.o5, hK5]
    rfl
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets G 7 (by norm_num)
      (by rw [vsRetVars_lens.2.2.1, O.o7, hK7]; simp [capOf])⟩⟩
    show [σ (.n 849), σ (.n 850), σ (.n 851), σ (.n 852), σ (.n 853), σ (.n 854), σ (.n 858),
      σ (.n 848), σ (.n 862), σ (.n 859), σ (.n 860)] =
      S.s6.cap ++ [ofK (gpow (S.cK bs)), gen ^ S.τ, ofK (gpow (vb bs 10)),
        ofK (gpow (vb bs 0 + 110)), ofK (gpow (vb bs 11)), ofK (gpow (vb bs 12))]
    rw [← e6, r854, G.e858, q848, G.e862, q859, q860]; rfl
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets G 8 (by norm_num) 
      (by rw [O.o8]; simp only [List.length_cons, List.length_nil]; rfl)⟩⟩
    show [σ (.n 860), σ (.n 876)] = [ofK (gpow (vb bs 12)), ofK (gpow (vb bs 13))]
    rw [q860, q876]
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets G 9 (by norm_num)
      (by rw [h9]; simp only [List.length_cons, List.length_nil]; rfl)⟩⟩
    show [σ (.n 141), σ (.n 5)] = [ofK (gpow (vb bs 5)), ofK (gpow sqE)]
    rw [q141, a5]
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets G 10 (by norm_num) 
      (by rw [O.o10]; simp only [List.length_cons, List.length_nil]; rfl)⟩⟩
    show [σ (.n 1887), σ (.n 4), σ (.n 5)] =
      [gen ^ Tables.stackTotal S.kappas, ofK (gpow lpE), ofK (gpow sqE)]
    rw [r1887, a4, a5]
  · refine ⟨?_, rfl, fun _ ↦ ⟨?_, vs_rets G 11 (by norm_num)
      (by rw [h11]; simp only [List.length_cons, List.length_nil]; rfl)⟩⟩
    · show vsOpenNames.getD (logG (σ (.n 1901))) "" = B1.Whir.openName S.μs S.rate
      rw [G.e1901, logG_gen_pow (by omega), vsOpenNames_eq]
      rfl
    · show [σ (.n 1312), σ (.n 1313), σ (.n 1314), σ (.n 1315), σ (.n 1316), σ (.n 1886),
        σ (.n 537), σ (.n 547), σ (.n 868)] = capOf S.s8.perm ++ [S.target,
          (digestScalars S.root).1, (digestScalars S.root).2, ofK (gpow (S.cW bs))]
      rw [← G.e1312, G.e1886, G.e537, G.e547, r868, S.root_cells]
      rfl
  · refine ⟨rfl, ?_, fun _ ↦ ⟨?_, vs_rets G 12 (by norm_num)
      
      (by rw [O.o12, List.length_nil]; rfl)⟩⟩
    · show true = @decide (S.termOk (outs.take 12)) (Classical.propDecidable _)
      exact (@decide_eq_true _ (Classical.propDecidable _) O.term).symm
    · show [σ (.n 523), σ (.n 848), σ (.n 857), σ (.n 522), σ (.n 855), σ (.n 130), σ (.n 858),
        σ (.n 8), σ (.n 1884), σ (.n 1324), σ (.n 1888), σ (.n 1889), σ (.n 859), σ (.n 877),
        σ (.n 1907), σ (.n 1908), σ (.n 1909), σ (.n 1910), σ (.n 1906)] =
        [ofK (gpow (vb bs 7)), ofK (gpow (vb bs 10)), S.H.rm, gen ^ S.μ, gen ^ S.H.n,
          gen ^ S.logMem, gen ^ S.τ, ofK (gpow (vb bs 1)), S.lam ^ 141, ofK (gpow (vb bs 15)),
          ((outs.take 12).getD 9 ([], [])).1.getD 1 0, ((outs.take 12).getD 9 ([], [])).1.getD 2 0,
          ofK (gpow (vb bs 11)), ofK (gpow (vb bs 14)), ((outs.take 12).getD 11 ([], [])).1.getD 1 0,
          ((outs.take 12).getD 11 ([], [])).1.getD 2 0, ((outs.take 12).getD 11 ([], [])).1.getD 3 0,
          ((outs.take 12).getD 11 ([], [])).1.getD 4 0, ((outs.take 12).getD 11 ([], [])).1.getD 0 0]
      rw [take_getD _ _ (by norm_num : 9 < 12), take_getD _ _ (by norm_num : 11 < 12), q523, q848,
        r857, r522, r855, r130, G.e858, q8, G.e1884, q1324,
        show σ (.n 1888) = _ from R 9 (by norm_num) 1 (by decide),
        show σ (.n 1889) = _ from R 9 (by norm_num) 2 (by decide), q859, q877,
        show σ (.n 1906) = _ from R 11 (by norm_num) 0 (by decide),
        show σ (.n 1907) = _ from R 11 (by norm_num) 1 (by decide),
        show σ (.n 1908) = _ from R 11 (by norm_num) 2 (by decide),
        show σ (.n 1909) = _ from R 11 (by norm_num) 3 (by decide),
        show σ (.n 1910) = _ from R 11 (by norm_num) 4 (by decide)]

/-- **The dispatch's selector names one of its callees.** -/
theorem vs_dispOk (S : ChildSegs bytecode seed c)
    (h1901 : σ (.n 1901) = gen ^ B1.Whir.candidate S.μs S.rate) :
    ∀ s ∈ vsCPre, DispOk σ s := by
  intro s hs
  rw [vs_split_disp] at hs
  simp only [List.mem_append, List.mem_singleton] at hs
  have hc := S.candidate_lt
  rcases hs with (h | rfl) | h
  · have := List.all_eq_true.mp vs_noDisp.1 s h
    cases s with
    | dispatch => simp [noDispatchB] at this
    | _ => trivial
  · exact ⟨_, by simp [vsOpenNames]; exact hc, by omega, by rw [h1901, gen_pow_eq_ofK]⟩
  · have := List.all_eq_true.mp vs_noDisp.2 s h
    cases s with
    | dispatch => simp [noDispatchB] at this
    | _ => trivial

/-- **The allocations' sizes** are the own buffers'. -/
theorem vs_alloc_sizes (hbl : bytecode.length = 2 ^ 23) {lpE : ℕ} (G : VsSig S bs sqE outs args σ)
    (O : VsOuts S bs lpE sqE outs) :
    (vsCPre.filterMap Main.Stmt.allocSz).map (fun x ↦ x.2.elim id fun s ↦ logG (σ s)) =
      vsSizes S.μ := by
  have r522 : σ (.n 522) = gen ^ S.μ := by
    rw [show σ (.n 522) = _ from G.ret 2 (by norm_num) 0 (by decide), O.o2]; simp [ChildSegs.μ]
  have hμ : S.μ < 2 ^ 64 - 1 := by
    have := (S.μ_bounds hbl).2
    omega
  rw [vs_allocs]
  show [165, 165, 8192, 6, 7, 8, 153, logG (σ (.n 522)), 4, 16, 34, 78, 64, 6, 64, 165] = _
  rw [r522, logG_gen_pow hμ]
  rfl

/-- **The allocations' pointers** are the own buffers' first words. -/
theorem vs_alloc_bases (G : VsSig S bs sqE outs args σ) {b : ℕ} (hbs : bs = bases b (vsSizes S.μ)) :
    ((vsCPre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
      (bases b (vsSizes S.μ)).map (fun x ↦ ofK (gpow x)) := by
  have e : (vsCPre.filterMap Main.Stmt.allocSz).map Prod.fst = vsAllocVars.map V.n := by
    rw [vs_allocs]; rfl
  have hl : (bases b (vsSizes S.μ)).length = 16 := by rw [bases_length]; rfl
  have hv : vsAllocVars.length = 16 := rfl
  rw [e, ← hbs]
  apply List.ext_getElem (by simp [hv, hbs, hl])
  intro i h1 h2
  have hi : i < 16 := by simpa [hv] using h1
  simp only [List.getElem_map]
  rw [← List.getD_eq_getElem _ 0 (by omega : i < vsAllocVars.length), G.ptr i hi, vb,
    List.getD_eq_getElem _ _ (by rw [hbs, hl]; exact hi)]

/-- **The own buffers' lengths** the loads need. -/
theorem ChildSegs.ownW_lens (S : ChildSegs bytecode seed c) (hbl : bytecode.length = 2 ^ 23) :
    165 ≤ (S.ownW.getD 0 []).length ∧ 10 ≤ (S.ownW.getD 2 []).length ∧
      6 ≤ (S.ownW.getD 3 []).length ∧ 7 ≤ (S.ownW.getD 4 []).length ∧
      8 ≤ (S.ownW.getD 5 []).length ∧ 153 ≤ (S.ownW.getD 6 []).length ∧
      19 ≤ (S.ownW.getD 7 []).length ∧ 4 ≤ (S.ownW.getD 8 []).length ∧
      16 ≤ (S.ownW.getD 9 []).length ∧ 6 ≤ (S.ownW.getD 13 []).length ∧
      64 ≤ (S.ownW.getD 14 []).length ∧ 165 ≤ (S.ownW.getD 15 []).length := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 165 ≤ S.H.poolW.length
    rw [S.poolW_length hbl]
  · show 10 ≤ (vsStreamW c.proof.stream).length
    have := S.stream_length
    simp only [vsStreamW, List.length_append, List.length_replicate]
    omega
  · show 6 ≤ (S.rowsN.map eOfNat).length
    simp [S.hrowsL]
  · show 7 ≤ (vsDimsW S.logMem S.hs).length
    simp [vsDimsW, S.hs_length]
  · show 8 ≤ (vsKbW S.logMem S.hs).length
    simp [vsKbW, S.hs_length]
  · show 153 ≤ (vsBkW S.logMem S.hs).length
    simp [vsBkW, Tables.blockKappaWords]
  · show 19 ≤ S.point.length
    rw [(S.runG' hbl).2.2.1]
    have := (S.μ_bounds hbl).1
    omega
  · show 4 ≤ S.alphas.length
    rw [S.alphas_length]
  · show 16 ≤ (eqKernel S.alphas).length
    rw [KeccakGkr.eqKernel_length, S.alphas_length]
    norm_num
  · show 6 ≤ S.rchs.length
    rw [S.rchs_length]
  · show 64 ≤ (ringCoefficients S.rchs).length
    simp [ringCoefficients, kBits]
  · show 165 ≤ (lamW S.lam).length
    rw [lamW_length]

end
end LeanVM.Guest.B1.VerifySub
