/-
  LeanVM.Guest.B1.Whir.StackedQueriesM

  A level's queries in `open_stacked` under a hash model: the row weights, the cap's root,
  `opening_queries`, and the intro message, as the openings `queryP` reads over the model's
  answered hash and the enforced sum.
-/

module

public import LeanVM.Guest.B1.Whir.StackedLoopsM
public import LeanVM.Guest.B1.Whir.StackedQueries
public import LeanVM.Guest.B1.Whir.QueriesM

/-!
# A level's queries under a hash model (TRIAGE #36, through #28-30, #34, #35)

`Whir/StackedQueries.lean` over a `HashModel`: one opening per position (the leaf, the path's
siblings, then the cap's siblings), the model hashing its leaf and its path climbing (V:526, at
`Option` over `M.H`) to the cap's root, which the refutation argument (`cap_climbM`) reaches
from the cap leaf; the query sum is `enforcedSum` (V:1622) of the openings' rows.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {M : HashModel} {rd : Reader} {σ : Val}

/-- **A query's opening under a hash model** (V:543-552): an opening `o` with which query `i` at
`q` is `QueryOkM` has the shape, the model hashes its leaf, and its path climbs to the cap's
root. -/
theorem queryOkM_opening {base I depth cd : ℕ} {rew qsc qw qbp flags cap : E} {i q : ℕ}
    {root : Digest} (hcd : 1 ≤ cd) (hcdd : cd ≤ depth) (hq : q < 2 ^ depth)
    (hroot : CapHashedM M rd cap 1) (hint : ∀ c, 2 ≤ c → c < 2 ^ cd → CapFlaggedM M rd flags cap c)
    (hcell : CapCell rd cap 1 root) {o : Opening}
    (h : QueryOkM M base I depth cd rd rew qsc qw qbp flags cap i q o) :
    o.leaf.length = oqR base I ∧ o.path.length = depth ∧
      (∃ ld, M.H (o.leaf.flatMap kBytes) = some ld ∧ climb (m := Option) M.H ld q o.path = some root) ∧
      ∃ s w, LoadHolds rd qsc i s ∧ LoadHolds rd qw i w ∧ LoadHolds rd qsc (i + 1)
        (s + w * ∑ jw ∈ Finset.range I, leafRowWord base o.leaf jw * memAt rd rew jw) := by
  obtain ⟨-, -, -, hlen, -, hsum, sibs, hpath, hsl, ld, top, hld, hcl, hcc, hfl⟩ := h
  set x := q / 2 ^ (depth - cd)
  have hx : x < 2 ^ cd := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show cd + (depth - cd) = depth by omega]
    exact hq
  have hc1 : 2 ^ cd ≤ 2 ^ cd + x := Nat.le_add_right _ _
  have hc2 : 2 ^ cd + x < 2 ^ (cd + 1) := by rw [pow_succ]; omega
  have hhalf : (2 ^ cd + x) / 2 = 2 ^ (cd - 1) + q / 2 ^ (depth - cd + 1) := by
    obtain ⟨c, rfl⟩ : ∃ c, cd = c + 1 := ⟨cd - 1, by omega⟩
    rw [pow_succ, Nat.add_sub_cancel, pow_succ, ← Nat.div_div_eq_div_mul]
    omega
  have htop := cap_climbM hroot hint cd (2 ^ cd + x) hcd le_rfl hc1 hc2 (by rw [hhalf]; exact hfl)
  rw [capNode_eq hcc, capNode_eq hcell, Nat.add_sub_cancel_left] at htop
  refine ⟨hlen, ?_, ⟨ld, hld, ?_⟩, hsum⟩
  · rw [hpath]; simp only [List.length_append, length_capSibs, hsl]; omega
  · rw [hpath, climbM_append_list, hcl, Option.bind_some, hsl]
    exact htop

private theorem rowsOf_getDM (lvl : ℕ) (f : ℕ → Opening) (n i : ℕ) (hi : i < n) :
    (osRowsOf lvl (((List.range n).map f).map (·.leaf))).getD i [] =
      if lvl = 0 then (f i).leaf.reverse.map ofK else extRow (f i).leaf := by
  unfold osRowsOf
  split <;> simp [List.getD_eq_getElem?_getD, hi]

private theorem length_rowsOfM (lvl : ℕ) (words : List (List K)) :
    (osRowsOf lvl words).length = words.length := by
  unfold osRowsOf; split <;> simp

/-- A block under a call relation below the program's holds under the program's (`holdsList_rel`). -/
theorem holdsListB_rel {C : CallRel} (hC : CallRel.Le C (coreProgram.RelB M.sem rd)) {ss : List Stmt}
    {next : Prop} {kret : List E → Prop} (h : Stmt.HoldsListB M.sem C rd σ ss next kret) :
    Stmt.HoldsListB M.sem (coreProgram.RelB M.sem rd) rd σ ss next kret :=
  holdsListB_mono hC ss id (fun _ h => h) h

/-- **A level's queries under a hash model** (G:1176-1193), in the specification's terms: the
cap's root `root` at the level's root slot, openings `os`, one per position, each of the shape,
its leaf hashed and its path climbing to the root over the model (what `queryP` reads), the query
sum `enforcedSum` (V:1622) of their rows, and the intro message's `c0, c2` read and absorbed. -/
theorem osQueries_soundWM {C : CallRel} (hC : CallRel.Le C (coreProgram.RelB M.sem rd)) {cfg : OsCfg}
    {lv : OsLvl} {lvl rev : ℕ} (hrev : rev = if lvl = 0 then 1 else 0)
    (hrw : ∀ a r, coreProgram.RelB M.sem rd lv.rowWeights a r → MeaningOpeningRowWeights lv.folds rev rd a r)
    (hcapM : ∀ a r, coreProgram.RelB M.sem rd lv.verifyCap a r →
      MeaningVerifyMerkleCapWith M lv.capDepth rd a r)
    {w : List E → List E → List Opening}
    (hqW : SoundQueriesWCM M C rd lv.queriesFn rev (2 ^ lv.folds) lv.depth lv.capDepth w)
    (hcd : 1 ≤ lv.capDepth) (hcdd : lv.capDepth ≤ lv.depth)
    (hb1 : lv.foldsOff < 2 ^ 128) (hb2 : 4 * lv.capOff < 2 ^ 128) (hb4 : lvl * cfg.maxQ < 2 ^ 128)
    (hb5 : lv.posOff < 2 ^ 128) (hnq : lv.queries < 2 ^ 63)
    {lf : List E} (hlfl : lf.length = lv.folds)
    (hlf : ∀ j < lv.folds, LoadHolds rd (σ (.n osFch)) (lv.foldsOff + j) (lf.getD j 0))
    {lam : E} (hqw : ∀ i < lv.queries, LoadHolds rd (σ (.n osQw)) (lvl * cfg.maxQ + i) (lam ^ i))
    {pos : ℕ → ℕ} (hbits : QueryBits rd (σ (.n osQbp) * gen ^ lv.posOff) lv.queries lv.depth pos)
    {cur : E} {s : OsSt} {cv : Digest} {xs : List E} (hat : OsCur rd σ cur s cv xs)
    {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (osQueries cfg lv lvl s).1 True kret) :
    ∃ (root : Digest) (os : List Opening) (c0 c2 : E) (cvq : Digest),
      os = osQueriesOs cfg lv lvl s σ w ∧ LoadHolds rd (σ (.n osRoots)) (2 * lvl) (digestScalars root).1 ∧
      LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) (digestScalars root).2 ∧
      os.length = lv.queries ∧
      (∀ j (hj : j < os.length), (os[j]).leaf.length = oqR rev (2 ^ lv.folds) ∧
        (os[j]).path.length = lv.depth ∧
        ∃ ld, M.H ((os[j]).leaf.flatMap kBytes) = some ld ∧
          climb (m := Option) M.H ld (pos j) (os[j]).path = some root) ∧
      σ (.n (osQueries cfg lv lvl s).2.2.1) =
        enforcedSum (osRowsOf lvl (os.map (·.leaf))) lf (powers lam lv.queries) ∧
      (∃ e1, obsCvM M cv c0 = some e1 ∧ obsCvM M e1 c2 = some cvq) ∧
      OsCur rd σ cur (osQueries cfg lv lvl s).2.1 cvq (xs ++ [c0, c2]) ∧
      (osQueries cfg lv lvl s).2.1.co = s.co + 2 ∧
      σ (.n (osQueries cfg lv lvl s).2.2.2.1) = c0 ∧
      σ (.n (osQueries cfg lv lvl s).2.2.2.2.1) = σ (.n (osQueries cfg lv lvl s).2.2.1) + c2 ∧
      σ (.n (osQueries cfg lv lvl s).2.2.2.2.2) = c2 := by
  unfold osQueriesOs osQCall
  unfold osQueries at h ⊢
  simp only [List.map_cons, List.map_nil] at h ⊢
  generalize hp : osMat osFch lv.foldsOff (s.k + 2) = p at h ⊢
  generalize hcp : osMat osCaps (4 * lv.capOff) p.2.2 = cp at h ⊢
  generalize hfp : osMat osFlags lv.capOff cp.2.2 = fp at h ⊢
  generalize hcp2 : osMat osCaps (4 * lv.capOff) (fp.2.2 + 2) = cp2 at h ⊢
  generalize hfp2 : osMat osFlags lv.capOff cp2.2.2 = fp2 at h ⊢
  generalize hqp : osMat osQw (lvl * cfg.maxQ) fp2.2.2 = qp at h ⊢
  generalize hbp : osMat osQbp lv.posOff qp.2.2 = bp at h ⊢
  simp only [holdsListB_append] at h
  obtain ⟨-, h⟩ := holdsListB_true_of (by rfl) h
  obtain ⟨hP, h⟩ := holdsListB_split_free (by rw [← hp]; exact osMat_noBlake _ _ _)
    (by rw [← hp]; exact osMat_noRet _ _ _) h
  obtain ⟨hW, h⟩ := holdsListB_split_free rfl rfl h
  obtain ⟨hCP, h⟩ := holdsListB_split_free (by rw [← hcp]; exact osMat_noBlake _ _ _)
    (by rw [← hcp]; exact osMat_noRet _ _ _) h
  obtain ⟨hFP, h⟩ := holdsListB_split_free (by rw [← hfp]; exact osMat_noBlake _ _ _)
    (by rw [← hfp]; exact osMat_noRet _ _ _) h
  obtain ⟨hCap, h⟩ := holdsListB_split_free rfl rfl h
  obtain ⟨hCP2, h⟩ := holdsListB_split_free (by rw [← hcp2]; exact osMat_noBlake _ _ _)
    (by rw [← hcp2]; exact osMat_noRet _ _ _) h
  obtain ⟨hFP2, h⟩ := holdsListB_split_free (by rw [← hfp2]; exact osMat_noBlake _ _ _)
    (by rw [← hfp2]; exact osMat_noRet _ _ _) h
  obtain ⟨hQP, h⟩ := holdsListB_split_free (by rw [← hqp]; exact osMat_noBlake _ _ _)
    (by rw [← hqp]; exact osMat_noRet _ _ _) h
  obtain ⟨hBP, h⟩ := holdsListB_split_free (by rw [← hbp]; exact osMat_noBlake _ _ _)
    (by rw [← hbp]; exact osMat_noRet _ _ _) h
  obtain ⟨hQS, h⟩ := holdsListB_split_free rfl rfl h
  obtain ⟨hI0, h⟩ := holdsListB_true_of (by rfl) h
  obtain ⟨hI2, h⟩ := holdsListB_true_of (by rfl) h
  rw [holdsListB_iff_of_noBlake rfl] at h
  have ep := osMat_eq hp hb1 hP
  have ecp := osMat_eq hcp hb2 hCP
  have efp := osMat_eq hfp (by omega) hFP
  have ecp2 := osMat_eq hcp2 hb2 hCP2
  have efp2 := osMat_eq hfp2 (by omega) hFP2
  have eqp := osMat_eq hqp hb4 hQP
  have ebp := osMat_eq hbp hb5 hBP
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    and_true] at hW hCap hQS h
  -- the row weights are the level's fold challenges'
  obtain ⟨-, rs, hrsl, hrsr, hrew⟩ := hrw _ _ (hC _ _ _ hW)
  have hrs : rs = lf := List.ext_getElem (by rw [hrsl, hlfl]) fun j h1 h2 => by
    have := hrsr j h1
    rw [ep, loadHolds_mul_gen_pow] at this
    have h' := hlf j (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some] at h'
    exact loadHolds_unique this h'
  rw [hrs] at hrew
  -- the cap's root
  obtain ⟨hcapC, lr0, lr1⟩ := hCap
  obtain ⟨-, hroot, hint, root, hcell, hret⟩ := hcapM _ _ (hC _ _ _ hcapC)
  simp only [List.cons.injEq] at hret
  obtain ⟨r0, r1, -⟩ := hret
  -- the queries
  obtain ⟨eg, hqcall⟩ := hQS
  have hgw : σ (.n bp.2.2) = gen ^ lv.queries := by rw [eg, os_gw_eq (by omega)]
  rw [hgw]
  rw [hgw] at hqcall
  rw [← ebp] at hbits
  obtain ⟨qsc, -, l0, hosl, hok, sN, lN, hsN⟩ := hqW _ pos _ _ _ _ _ _ (by simp only [ordG]; omega) hbits hqcall
  generalize w [σ (.n cp2.2.1), σ (.n fp2.2.1), σ (.n qp.2.1), σ (.n bp.2.1), σ (.n (s.k + 1)),
    gen ^ lv.queries] [σ (.n (bp.2.2 + 1))] = os at hosl hok ⊢
  rw [ecp2, ← ecp, efp2, ← efp, eqp] at hok
  simp only [List.cons.injEq, and_true] at hsN
  set oOf : ℕ → Opening := fun i => os.getD i ⟨[], []⟩
  have hosR : os = (List.range lv.queries).map oOf := List.ext_getElem (by simp [hosl]) fun j h1 h2 => by
    simp [oOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  have hop := fun i (hi : i < lv.queries) =>
    queryOkM_opening (rd := rd) hcd hcdd (hbits i hi).1 hroot hint hcell (hok i hi)
  set D : ℕ → E := fun i => ∑ jw ∈ Finset.range (2 ^ lv.folds), leafRowWord rev (oOf i).leaf jw *
    memAt rd (σ (.n (s.k + 1))) jw
  have hchain : ∀ i ≤ lv.queries, LoadHolds rd qsc i (∑ i' ∈ Finset.range i, lam ^ i' * D i') := by
    intro i hi
    induction i with
    | zero => simpa using l0
    | succ i ih =>
      obtain ⟨s', w', ls, lw, ls1⟩ := (hop i (by omega)).2.2.2
      rw [loadHolds_mul_gen_pow] at lw
      have hw := loadHolds_unique lw (hqw i (by omega))
      have hs := loadHolds_unique ls (ih (by omega))
      rw [hw, hs] at ls1
      rw [Finset.sum_range_succ]
      exact ls1
  have hsum' := loadHolds_unique lN (hchain _ le_rfl)
  -- the intro message
  have hat1 : OsCur rd σ cur { s with k := bp.2.2 + 2 } cv xs := ⟨hat.fs, hat.reads, hat.cursor⟩
  obtain ⟨d1, hd1, hat2⟩ := osFsNext_soundM hat1 hI0
  obtain ⟨d2, hd2, hat3⟩ := osFsNext_soundM hat2 hI2
  rw [List.append_assoc, List.singleton_append] at hat3
  refine ⟨root, os, _, _, d2, rfl, ?_, ?_, hosl, fun j hj => ?_, ?_,
    ⟨d1, hd1, hd2⟩, ⟨hat3.fs, hat3.reads, hat3.cursor⟩, rfl, rfl, h, rfl⟩
  · rw [← r0]; exact lr0
  · rw [← r1]; exact lr1
  · have hj' : j < lv.queries := by rw [← hosl]; exact hj
    have e : os[j] = oOf j := by simp [oOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rw [e]
    exact ⟨(hop j hj').1, (hop j hj').2.1, (hop j hj').2.2.1⟩
  · rw [hosR, hsN, hsum', os_enforcedSum_eq _ _ _ (by simp [os_length_powersFrom, length_rowsOfM, powers]),
      length_rowsOfM, List.length_map, List.length_map, List.length_range]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [os_powers_getD hi', rowsOf_getDM _ _ _ _ hi']
    congr 1
    have hmem : ∀ jw < 2 ^ lv.folds, memAt rd (σ (.n (s.k + 1))) jw =
        (eqKernel lf).getD (orwSlot lv.folds rev jw) 0 := fun jw hjw => memAt_of_load (hrew jw hjw)
    simp only [D]
    rw [Finset.sum_congr rfl fun jw hjw => by rw [hmem jw (Finset.mem_range.mp hjw)]]
    have hlen := (hop i hi').1
    by_cases h0 : lvl = 0
    · simp only [h0, ↓reduceIte] at hrev ⊢
      subst hrev
      exact (os_dot_row0 (by rw [hlen]; simp [oqR]) hlfl).symm
    · simp only [h0, ↓reduceIte] at hrev ⊢
      subst hrev
      exact (os_dot_rowExt (by rw [hlen]; simp [oqR]) hlfl).symm

end
end LeanVM.Guest.B1
