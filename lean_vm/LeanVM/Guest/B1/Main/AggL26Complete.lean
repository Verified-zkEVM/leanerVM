/-
  LeanVM.Guest.B1.Main.AggL26Complete

  `__loop26` (a child's lambdas) and `__loop27` (a child's weight), completely.
-/

module

public import LeanVM.Guest.B1.Main.AggL26CChk

/-!
# A child's lambdas and weight, completely

`l26_block`: `__loop26`'s block at the child `x` holds on the evaluated valuation (`Fwd.ev`) when
its row (`sqT·x^14`) holds the honest words of a sponge and a running claim, the next row the
honest words of the sponge after two squeezes and the claim on, the lambdas' table the two
squeezes, and the pointer tables the child's claims' values. Its atoms but its stores hold (their
side conditions its loads and its challenges' `assert_in_k`, on canonical permutation cells), so
its permutations and challenges are the squeezes (as in `l26_step`), which its stores find.

`l27_block`: `__loop27`'s block at `x` holds when the pointer tables point to the claims' points,
`pt` holds the sumcheck's point, the lambdas' table the lambdas, and the weights' table at `x`
the weight and the weight on.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Da

@[expose] public section

variable {rd : Reader}

theorem rowW_snoc_lt {s : Fs} (hs : StOk s) (v : E) {o : ℕ} (ho : o < 13) :
    (rowW s ++ [v]).getD o 0 = (rowW s).getD o 0 :=
  List.getD_append _ _ _ _ (by rw [rowW_length hs]; exact ho)

theorem rowW_snoc_13 {s : Fs} (hs : StOk s) (v : E) : (rowW s ++ [v]).getD 13 0 = v := by
  rw [List.getD_append_right _ _ _ _ (by rw [rowW_length hs]), rowW_length hs]
  rfl

theorem capOf_getD (S : KState) {i : ℕ} (hi : i < 5) :
    (capOf S).getD i 0 = cellsOfState S false ⟨8 + i, by omega⟩ := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **A child's lambdas** (`__loop26`). -/
theorem l26_block {x N sqT lamT lfT lcT pf pc fv cv acc : E} {st : Fs} (hst : StOk st)
    (hrow : ReadsAt rd (sqT * x ^ 14) (rowW st ++ [acc]))
    (hnext : ReadsAt rd (sqT * x ^ 14 * gen ^ 14)
      (rowW st.squeeze.2.squeeze.2 ++ [acc + st.squeeze.1 * fv + st.squeeze.2.squeeze.1 * cv]))
    (hlam : ReadsAt rd (lamT * x ^ 2) [st.squeeze.1, st.squeeze.2.squeeze.1])
    (hlf : LoadHolds rd (lfT * x) 0 pf) (hlc : LoadHolds rd (lcT * x) 0 pc)
    (hfv : LoadHolds rd pf 23 fv) (hcv : LoadHolds rd pc 23 cv) :
    LoopBlock rd (coreProgram.getD 395 default) x N [sqT, lamT, lfT, lcT] := by
  obtain ⟨hshape, hlen⟩ := l26_shape
  have hcok := l26c_ok
  simp only [l26COk, Bool.and_eq_true, Option.isSome_iff_exists, decide_eq_true_eq] at hcok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c', hchk⟩, hatoms⟩, hcanA⟩, hneeds⟩, hrl⟩, hll⟩, hm11⟩, hk1⟩,
    hrin⟩, hc1⟩, hz⟩, hk2⟩, hc2⟩, hm74⟩, hm75⟩, hm76⟩, hm77⟩, hm79⟩, hzc⟩, hm91⟩, ha92⟩, hm94⟩,
    ha95⟩ := hcok
  simp only [List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    List.mem_range] at hatoms hneeds hrl hll hz hzc
  have hS := l26_stores
  set fn := coreProgram.getD 395 default
  set A := atomsIn (loopPre fn)
  let args : List E := [x, N, sqT, lamT, lfT, lcT]
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd (fun _ => 0) args fn.body) := ⟨_, rfl⟩
  have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
  obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) fn.body args hchk
  rw [show args.length = 6 from rfl, ← hσ, hS] at hgs
  have hg : ∀ a ∈ A, Good rd l26Stores (fun _ => 0) σ a := fun a ha =>
    hgs (.atom a) (loopPre_mem (atom_mem_of_atomsIn ha))
  have hpar : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] := by
    rw [params_of_shape hshape hlen]; rfl
  have par : ∀ i (hi : i < 6), σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args]; omega)
  have e0 : σ (.n 0) = x := par 0 (by omega)
  have hP : ∀ a ∈ A.filter pureB, a.Holds rd σ := pure_holds hg
  have p11 : σ (.n 11) = sqT * x ^ 14 := by rw [monoIs_sound hm11 hP, par 2 (by omega), e0]; rfl
  have p74 : σ (.n 74) = x ^ 2 := by rw [isMul_sound hm74 hP, e0, sq]
  have p75 : σ (.n 75) = lamT * x ^ 2 := by rw [isMul_sound hm75 hP, par 3 (by omega), p74]; rfl
  have p76 : σ (.n 76) = lamT * x ^ 2 := by rw [isMul_sound hm76 hP, par 3 (by omega), p74]; rfl
  have p77 : σ (.n 77) = lfT * x := by rw [isMul_sound hm77 hP, par 4 (by omega), e0]; rfl
  have p79 : σ (.n 79) = lcT * x := by rw [isMul_sound hm79 hP, par 5 (by omega), e0]; rfl
  -- the atoms but the stores
  have hg' : ∀ a ∈ l26A, Good rd l26Stores (fun _ => 0) σ a := fun a ha =>
    hg a (mem_l26A.mp ha).1
  have hnS : ∀ a ∈ l26A, a ∉ l26Stores := fun a ha => (mem_l26A.mp ha).2
  have hrowL : ∀ o < 14, LoadHolds rd (σ (.n 11)) o ((rowW st ++ [acc]).getD o 0) := fun o ho => by
    have hl : (rowW st ++ [acc]).length = 14 := by simp [rowW_length hst]
    rw [p11, List.getD_eq_getElem _ _ (by rw [hl]; exact ho)]
    exact hrow o (by rw [hl]; exact ho)
  have vrow : ∀ o < 13, σ (.n (12 + o)) = (rowW st).getD o 0 := fun o ho => by
    rw [← rowW_snoc_lt hst acc ho]
    exact (load_of_good (hnS _ (hrl o ho)) (hg' _ (hrl o ho)) (hrowL o (by omega))).1
  have m89 := hll (.load (.n 89) (.n 11) 13) (by simp [l26Loads])
  have m78 := hll (.load (.n 78) (.n 77) 0) (by simp [l26Loads])
  have m80 := hll (.load (.n 80) (.n 79) 0) (by simp [l26Loads])
  have m90 := hll (.load (.n 90) (.n 78) 23) (by simp [l26Loads])
  have m93 := hll (.load (.n 93) (.n 80) 23) (by simp [l26Loads])
  have L89 := load_of_good (hnS _ m89) (hg' _ m89) (hrowL 13 (by omega))
  rw [rowW_snoc_13 hst] at L89
  have L78 := load_of_good (hnS _ m78) (hg' _ m78) (by rw [p77]; exact hlf)
  have L80 := load_of_good (hnS _ m80) (hg' _ m80) (by rw [p79]; exact hlc)
  have L90 := load_of_good (hnS _ m90) (hg' _ m90) (by rw [L78.1]; exact hfv)
  have L93 := load_of_good (hnS _ m93) (hg' _ m93) (by rw [L80.1]; exact hcv)
  have hAc : ∀ i ∈ (List.range 13).map (12 + ·), IsCanonical128 (σ (.n i)) := by
    intro i hi
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hi
    have ho' := List.mem_range.mp ho
    rw [vrow o ho']
    exact rowW_canonical hst _ (getD_mem (by rw [rowW_length hst]; exact ho'))
  have c30 : IsCanonical128 (σ (.n 30)) := by
    have := keccak_out_canon (hg' _ hk1) (c := 1) (by omega)
    rwa [getD_k1o (by omega)] at this
  have c55 : IsCanonical128 (σ (.n 55)) := by
    have := keccak_out_canon (hg' _ hk2) (c := 1) (by omega)
    rwa [getD_k2o (by omega)] at this
  have hat' : ∀ a ∈ l26A, a.Holds rd σ := by
    refine atoms_holds hidx hcanA hg' hAc fun a ha hns => Or.inl ?_
    rcases hneeds a ha with (((h | rfl) | rfl) | h) | h
    · rw [hns] at h; exact absurd h (by simp)
    · exact chal_inK hc1 hg' c30
    · exact chal_inK hc2 hg' c55
    · cases a <;> simp only [isL26RowLoad, Bool.false_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at h
      rename_i d p o
      obtain ⟨⟨rfl, rfl⟩, ho⟩ := h
      exact (load_of_good (hnS _ ha) (hg' _ ha) (hrowL o (by omega))).2
    · simp only [l26Loads, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl
      · exact L89.2
      · exact L78.2
      · exact L80.2
      · exact L90.2
      · exact L93.2
  -- the first squeeze
  have hin := rowIn_sound hrin hat'
  rw [p11] at hin
  obtain ⟨hcan1, hout1⟩ := DupSpec.keccak_facts (hat' _ hk1)
  rw [hin] at hcan1 hout1
  have hperm := rowRel_perm (rowRel_of_reads hst (readsAt_append.mp hrow).1)
    (fun c hc => hcan1 c (List.mem_append_left _ hc))
  rw [← hperm] at hout1
  have o1 : ∀ c (hc : c < 13), σ (.n (29 + c)) = cellsOfState st.perm false ⟨c, hc⟩ :=
    fun c hc => by rw [← getD_k1o hc]; exact hout1 c hc
  have lf : σ (.n 48) = st.squeeze.1 :=
    challengeT_value (chal_sound hc1 hat') (o1 0 (by omega)) (o1 1 (by omega))
  -- the second
  obtain ⟨-, hout2⟩ := DupSpec.keccak_facts (hat' _ hk2)
  have z : ∀ i < 4, σ (.n (50 + i)) = 0 := fun i hi => by
    rw [const_sound (hz i hi) hP, word_zero]
  have hin2 : k2i.map σ = rateOf [] ++ capOf st.perm := by
    rw [rateOf_nil]
    simp only [k2i, List.map_cons, List.map_nil, capOf]
    rw [z 0 (by omega), z 1 (by omega), z 2 (by omega), z 3 (by omega), o1 8 (by omega),
      o1 9 (by omega), o1 10 (by omega), o1 11 (by omega), o1 12 (by omega)]
    rfl
  have hp2 : permOf (k2i.map σ) = st.squeeze.2.perm := by rw [hin2]; rfl
  rw [hp2] at hout2
  have o2 : ∀ c (hc : c < 13), σ (.n (54 + c)) = cellsOfState st.squeeze.2.perm false ⟨c, hc⟩ :=
    fun c hc => by rw [← getD_k2o hc]; exact hout2 c hc
  have lc : σ (.n 73) = st.squeeze.2.squeeze.1 :=
    challengeT_value (chal_sound hc2 hat') (o2 0 (by omega)) (o2 1 (by omega))
  -- the stores
  have hnx := stOk_squeeze st.squeeze.2
  have hnext' : ∀ k < 14, LoadHolds rd (σ (.n 11)) (14 + k)
      ((rowW st.squeeze.2.squeeze.2 ++ [acc + st.squeeze.1 * fv + st.squeeze.2.squeeze.1 * cv]).getD
        k 0) := by
    intro k hk
    have hl : (rowW st.squeeze.2.squeeze.2 ++
        [acc + st.squeeze.1 * fv + st.squeeze.2.squeeze.1 * cv]).length = 14 := by
      simp [rowW_length hnx]
    rw [p11, ← loadHolds_mul_gen_pow, List.getD_eq_getElem _ _ (by rw [hl]; exact hk)]
    exact hnext k (by rw [hl]; exact hk)
  have hstores : ∀ a ∈ l26Stores, a.Holds rd σ := by
    intro a haS
    simp only [l26Stores, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
      List.not_mem_nil, or_false] at haS
    rcases haS with (((rfl | rfl) | ⟨i, hi, rfl⟩) | ⟨c, hc, rfl⟩) | rfl
    · show LoadHolds rd (σ (.n 75)) 0 (σ (.n 48))
      rw [p75, lf]; exact hlam 0 (by simp)
    · show LoadHolds rd (σ (.n 76)) 1 (σ (.n 73))
      rw [p76, lc]; exact hlam 1 (by simp)
    · show LoadHolds rd (σ (.n 11)) (14 + i) (σ (.n (62 + i)))
      have e := hnext' i (by omega)
      rw [rowW_snoc_lt hnx _ (by omega), rowW_getD_cap hnx hi] at e
      rw [show σ (.n (62 + i)) = σ (.n (54 + (8 + i))) by rw [show 62 + i = 54 + (8 + i) by omega],
        o2 (8 + i) (by omega)]
      rw [show st.squeeze.2.squeeze.2.cap = capOf st.squeeze.2.perm from rfl, capOf_getD _ hi] at e
      exact e
    · show LoadHolds rd (σ (.n 11)) (19 + c) (σ (.n (81 + c)))
      have e := hnext' (5 + c) (by omega)
      rw [rowW_snoc_lt hnx _ (by omega), rowW_getD_rate hnx hc,
        Keccak.rateCell_past _ (by simp [Fs.squeeze])] at e
      rw [const_sound (hzc c hc) hP, word_zero, show 19 + c = 14 + (5 + c) by omega]
      exact e
    · show LoadHolds rd (σ (.n 11)) 27 (σ (.n 95))
      have e := hnext' 13 (by omega)
      rw [rowW_snoc_13 hnx] at e
      rw [add_sound ha95 hP, add_sound ha92 hP, isMul_sound hm91 hP, isMul_sound hm94 hP, L89.1,
        lf, L90.1, lc, L93.1]
      exact e
  have hat : ∀ a ∈ A, a.Holds rd σ := fun a ha => by
    by_cases haS : a ∈ l26Stores
    · exact hstores a haS
    · exact hat' a (mem_l26A.mpr ⟨ha, haS⟩)
  refine ⟨σ, ?_, fun s hs => ?_⟩
  · rw [hpar]
    simp only [List.map_cons, List.map_nil]
    rw [e0, par 1 (by omega), par 2 (by omega), par 3 (by omega), par 4 (by omega),
      par 5 (by omega)]
    rfl
  · have := hatoms s hs
    cases s <;> simp only [Bool.false_eq_true] at this
    rename_i a
    exact ⟨hat a (mem_atomsIn hs), trivial⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **A child's weight** (`__loop27`). -/
theorem l27_block {x N lfT lcT pt wT lamT pf pc lf lc wc : E} {pp pq r : List E}
    (hlf : LoadHolds rd (lfT * x) 0 pf) (hlc : LoadHolds rd (lcT * x) 0 pc)
    (hpf : ReadsAt rd pf pp) (hpc : ReadsAt rd pc pq) (hr : ReadsAt rd pt r)
    (hpl : pp.length = 23) (hql : pq.length = 23) (hrl : r.length = 23)
    (hlam : ReadsAt rd (lamT * x ^ 2) [lf, lc]) (hw : LoadHolds rd (wT * x) 0 wc)
    (hw1 : LoadHolds rd (wT * x) 1 (wc + lf * eqEval pp r + lc * eqEval pq r)) :
    LoopBlock rd (coreProgram.getD 397 default) x N [lfT, lcT, pt, wT, lamT] := by
  obtain ⟨hshape, hlen⟩ := l27_shape
  have hcok := l27c_ok
  simp only [l27COk, Bool.and_eq_true, Option.isSome_iff_exists] at hcok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c', hchk⟩, hatoms⟩, hcanA⟩, hneeds⟩, hm7⟩, hl8⟩, hm9⟩, hl10⟩, he1⟩,
    he2⟩, hm262⟩, hm263⟩, hl264⟩, hm265⟩, hl266⟩, hm267⟩, ha268⟩, hm269⟩, hl270⟩, hm271⟩, ha272⟩,
    hm273⟩ := hcok
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hatoms hneeds
  set fn := coreProgram.getD 397 default
  set A := atomsIn (loopPre fn)
  let args : List E := [x, N, lfT, lcT, pt, wT, lamT]
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd (fun _ => 0) args fn.body) := ⟨_, rfl⟩
  have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
  obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) fn.body args hchk
  rw [show args.length = 7 from rfl, ← hσ, l27_stores] at hgs
  have hg : ∀ a ∈ A, Good rd l27Stores (fun _ => 0) σ a := fun a ha =>
    hgs (.atom a) (loopPre_mem (atom_mem_of_atomsIn ha))
  have hpar : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] := by
    rw [params_of_shape hshape hlen]; rfl
  have par : ∀ i (hi : i < 7), σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args]; omega)
  have e0 : σ (.n 0) = x := par 0 (by omega)
  have e4 : σ (.n 4) = pt := par 4 (by omega)
  have hP : ∀ a ∈ A.filter pureB, a.Holds rd σ := pure_holds hg
  have p7 : σ (.n 7) = lfT * x := by rw [isMul_sound hm7 hP, par 2 (by omega), e0]; rfl
  have p9 : σ (.n 9) = lcT * x := by rw [isMul_sound hm9 hP, par 3 (by omega), e0]; rfl
  have p262 : σ (.n 262) = x ^ 2 := by rw [isMul_sound hm262 hP, e0, sq]
  have p263 : σ (.n 263) = wT * x := by rw [isMul_sound hm263 hP, par 5 (by omega), e0]; rfl
  have p265 : σ (.n 265) = lamT * x ^ 2 := by
    rw [isMul_sound hm265 hP, par 6 (by omega), p262]; rfl
  have p269 : σ (.n 269) = lamT * x ^ 2 := by
    rw [isMul_sound hm269 hP, par 6 (by omega), p262]; rfl
  have p273 : σ (.n 273) = wT * x := by rw [isMul_sound hm273 hP, par 5 (by omega), e0]; rfl
  have hl0 : LoadHolds rd (lamT * x ^ 2) 0 lf := hlam 0 (by simp)
  have hl1 : LoadHolds rd (lamT * x ^ 2) 1 lc := hlam 1 (by simp)
  -- the atoms but the store
  have hg' : ∀ a ∈ l27A, Good rd l27Stores (fun _ => 0) σ a := fun a ha =>
    hg a (mem_l27A.mp ha).1
  have hnS : ∀ a ∈ l27A, a ∉ l27Stores := fun a ha => (mem_l27A.mp ha).2
  have v8 : σ (.n 8) = pf := by rw [(load_any_val hnS hg' hl8).1, p7, rdAt_of_load hlf]
  have v10 : σ (.n 10) = pc := by rw [(load_any_val hnS hg' hl10).1, p9, rdAt_of_load hlc]
  have hat' : ∀ a ∈ l27A, a.Holds rd σ := by
    refine atoms_holds hidx hcanA hg' (fun i hi => absurd hi (by simp)) fun a ha hns => ?_
    rcases hneeds a ha with h | h
    · rw [hns] at h; exact absurd h (by simp)
    · cases a <;> simp only [isL27Load, Bool.false_eq_true, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at h
      rename_i d p o
      refine Or.inr (side_load (hnS _ ha) (v := memAt rd (σ p) o) ?_)
      rcases h with (((((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) |
        ⟨(rfl | rfl) | rfl, ho⟩)
      · rw [p7, memAt_of_load hlf]; exact hlf
      · rw [p9, memAt_of_load hlc]; exact hlc
      · rw [p263, memAt_of_load hw]; exact hw
      · rw [p265, memAt_of_load hl0]; exact hl0
      · rw [p269, memAt_of_load hl1]; exact hl1
      · rw [e4, memAt_of_load (hr o (by omega))]; exact hr o (by omega)
      · rw [v8, memAt_of_load (hpf o (by omega))]; exact hpf o (by omega)
      · rw [v10, memAt_of_load (hpc o (by omega))]; exact hpc o (by omega)
  -- the store
  have mp : memRun rd pf 23 = pp := by rw [← hpl]; exact (readsAt_memRun hpf).symm
  have mq : memRun rd pc 23 = pq := by rw [← hql]; exact (readsAt_memRun hpc).symm
  have mr : memRun rd pt 23 = r := by rw [← hrl]; exact (readsAt_memRun hr).symm
  have ef := eqChain_sound he1 hat'
  have ec := eqChain_sound he2 hat'
  rw [v8, e4, mp, mr] at ef
  rw [v10, e4, mq, mr] at ec
  have e264 := (load_any_val hnS hg' hl264).1
  have e266 := (load_any_val hnS hg' hl266).1
  have e270 := (load_any_val hnS hg' hl270).1
  rw [p263, rdAt_of_load hw] at e264
  rw [p265, rdAt_of_load hl0] at e266
  rw [p269, rdAt_of_load hl1] at e270
  have hat : ∀ a ∈ A, a.Holds rd σ := fun a ha => by
    by_cases haS : a ∈ l27Stores
    · simp only [l27Stores, List.mem_cons, List.not_mem_nil, or_false] at haS
      subst haS
      show LoadHolds rd (σ (.n 273)) 1 (σ (.n 272))
      rw [p273, add_sound ha272 hP, add_sound ha268 hP, isMul_sound hm267 hP,
        isMul_sound hm271 hP, e264, e266, e270, ef, ec]
      exact hw1
    · exact hat' a (mem_l27A.mpr ⟨ha, haS⟩)
  refine ⟨σ, ?_, fun s hs => ?_⟩
  · rw [hpar]
    simp only [List.map_cons, List.map_nil]
    rw [e0, par 1 (by omega), par 2 (by omega), par 3 (by omega), e4, par 5 (by omega),
      par 6 (by omega)]
    rfl
  · have := hatoms s hs
    cases s <;> simp only [Bool.false_eq_true] at this
    rename_i a
    exact ⟨hat a (mem_atomsIn hs), trivial⟩

end
end LeanVM.Guest.B1.Main
