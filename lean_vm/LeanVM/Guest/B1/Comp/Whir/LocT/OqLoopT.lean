/-
  LeanVM.Guest.B1.Comp.Whir.LocT.OqLoopT

  `opening_queries`' loop placed over a completeness model, its tree decoding to the queries'
  openings.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.LocT.OqCongr
public import LeanVM.Guest.B1.Comp.Whir.LocT.LoopT

/-!
# The loop's tree decodes to the openings

`OqLoopQ … j0 t`: on every reader satisfying `t`'s load equations and every frame valuation linked
to `t` that gives the loop's frame at `g^j0` the valuation of `t`, the frames at `g^j`,
`j0 ≤ j < n`, decode (`oqOpeningOf`) to the queries' openings: leaf, siblings below the cap, the
cap's siblings that reader holds. `oqLoop_relAtInCT` is `oqLoop_relAtInC` by such a tree.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.E2E.Complete

@[expose] public section

/-- The query `j`'s opening on the reader `rd`: its leaf, its siblings below the cap, the cap's
siblings `rd` holds from its cap leaf. -/
def oqHonest (pd cd : ℕ) (rd : Reader) (cap : E) (leaf : ℕ → List K) (pos : ℕ → ℕ) (sibs : ℕ → List Digest)
    (j : ℕ) : Opening :=
  ⟨leaf j, sibs j ++ capSibs rd cap cd (2 ^ cd + pos j / 2 ^ pd)⟩

/-- **The loop's tree from iteration `j0` decodes to the openings.** -/
def OqLoopQ (base I blocks pd cd : ℕ) (loop : String) (n : ℕ) (ps : List E) (cap : E) (leaf : ℕ → List K)
    (pos : ℕ → ℕ) (sibs : ℕ → List Digest) (j0 : ℕ) (t : Tree) : Prop :=
  ∀ (rd : Reader) (V : FrameVals), Sat rd (t.loadEqns coreProgram) → KidsLink V t →
    B2C.NodeAgree t (V loop (gen ^ j0 :: ps) []) →
    ∀ j, j0 ≤ j → j < n → oqOpeningOf base I blocks pd cd rd (V loop (gen ^ j :: ps) []) =
      oqHonest pd cd rd cap leaf pos sibs j

/-- **One iteration, by a tree decoding to the openings** (`oqLoop_iterC`). -/
theorem oqLoop_iterCT {CM : CompModel} {Ht : Bytes → Digest} (fs : String → ℕ) (cert : String → V → ℕ)
    {base I blocks pd cd : ℕ} (hs : OqShape base I blocks pd cd) {loop : String} {lf : Fn}
    (hfind : coreProgram.find? loop = some lf) (hp : lf.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7])
    (hb : lf.body = oqLoopBody base I blocks pd cd loop) (hpl : OqPlace base I blocks pd cd loop)
    (hlp : coreProgram.loop loop = true) (hNA : CellsOk loop (oqLoopReads base I blocks pd)) (hdec : loop ∈ osDecNames) {rd : Reader} {R : ℕ → Prop} {n j0 : ℕ}
    {rew qsc qw qbp flags cap : E} {leafF : ℕ → List K} {posF : ℕ → ℕ} {sibsF : ℕ → List Digest}
    (hleaf : (leafF j0).length = oqR base I) (hq : posF j0 < 2 ^ (pd + cd)) (hsl : (sibsF j0).length = pd)
    (fp : ℕ) {m : ℕ}
    (hw : ∀ jw < I, LoadHolds rd rew jw (memAt rd rew jw))
    (hs0 : LoadHolds rd (qsc * gen ^ j0) 0 (memAt rd (qsc * gen ^ j0) 0))
    (hw0 : LoadHolds rd (qw * gen ^ j0) 0 (memAt rd (qw * gen ^ j0) 0))
    (hs1 : LoadHolds rd (qsc * gen ^ j0) 1 (memAt rd (qsc * gen ^ j0) 0 + memAt rd (qw * gen ^ j0) 0 *
      ∑ jw ∈ Finset.range I, leafRowWord base (leafF j0) jw * memAt rd rew jw))
    (hdbp : LoadHolds rd (qbp * gen ^ j0) 0 (memAt rd (qbp * gen ^ j0) 0))
    (hbits : ∀ l < pd + cd, LoadHolds rd (memAt rd (qbp * gen ^ j0) 0) l (bitE ((posF j0).testBit l)))
    (hcell : ∀ j < 4 * pd, LoadHolds rd (ofK (Parameters.gpow (fp + cert loop (.n (oqP base I blocks))))) j
      ((climbCellsW Ht (hashWordsW Ht (leafF j0)) (posF j0) (sibsF j0)).getD j 0))
    (hflag : LoadHolds rd flags (2 ^ (cd - 1) + posF j0 / 2 ^ (pd + 1)) 1)
    (hcap : CapCell rd cap (2 ^ cd + posF j0 / 2 ^ pd) (climb (m := Id) Ht (hashWordsW Ht (leafF j0)) (posF j0) (sibsF j0)))
    (hleafA : CM.H ((leafF j0).flatMap kBytes) = some (hashWordsW Ht (leafF j0)))
    (hpathA : ∀ l < pd, CM.H (climbLvlBytes Ht (hashWordsW Ht (leafF j0)) (posF j0) (sibsF j0) l) =
      some (climbAtW Ht (hashWordsW Ht (leafF j0)) (posF j0) (sibsF j0) (l + 1)))
    (hK : IsInK (gen ^ j0 * gen + gen ^ n))
    (hlast : gen ^ j0 * gen + gen ^ n = 0 → j0 + 1 = n)
    (htail : if gen ^ j0 * gen + gen ^ n ≠ 0 then RelAtInBT CM.sem fs cert rd R (fun _ => False) (fp + fs loop) m loop
      [gen ^ j0 * gen, gen ^ n, rew, qsc, qw, qbp, flags, cap] []
      (OqLoopQ base I blocks pd cd loop n [gen ^ n, rew, qsc, qw, qbp, flags, cap] cap leafF posF sibsF (j0 + 1))
      else m = fs loop)
    (hRw : ∀ jw < I, OqIn R (rew.limb 0 * Parameters.gpow jw))
    (hRs : OqIn R ((qsc * gen ^ j0).limb 0 * Parameters.gpow 0) ∧ OqIn R ((qsc * gen ^ j0).limb 0 * Parameters.gpow 1))
    (hRq : OqIn R ((qw * gen ^ j0).limb 0 * Parameters.gpow 0)) (hRb : OqIn R ((qbp * gen ^ j0).limb 0 * Parameters.gpow 0))
    (hRd : ∀ l < pd + cd, OqIn R ((memAt rd (qbp * gen ^ j0) 0).limb 0 * Parameters.gpow l))
    (hRf : OqIn R ((flags * gen ^ (2 ^ (cd - 1) + posF j0 / 2 ^ (pd + 1))).limb 0 * Parameters.gpow 0))
    (hRc : OqIn R ((cap * gen ^ (2 * (2 ^ cd + posF j0 / 2 ^ pd))).limb 0 * Parameters.gpow 0) ∧
      OqIn R ((cap * gen ^ (2 * (2 ^ cd + posF j0 / 2 ^ pd) + 1)).limb 0 * Parameters.gpow 0)) :
    RelAtInBT CM.sem fs cert rd R (fun _ => False) fp (fs loop + m) loop
      [gen ^ j0, gen ^ n, rew, qsc, qw, qbp, flags, cap] []
      (OqLoopQ base I blocks pd cd loop n [gen ^ n, rew, qsc, qw, qbp, flags, cap] cap leafF posF sibsF j0) := by
  set x := gen ^ j0
  set N := gen ^ n
  set leaf := leafF j0
  set q := posF j0
  set sibs := sibsF j0
  set P := oqP base I blocks
  set c0 := fp + cert loop (.n P)
  set ptr : E := ofK (Parameters.gpow c0)
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = oqIterValC CM Ht rd [x, N, rew, qsc, qw, qbp, flags, cap] base I blocks pd cd leaf q sibs ptr :=
    ⟨_, rfl⟩
  have hptrK : IsInK ptr := (isInK_iff _).mpr ⟨_, rfl⟩
  have hbits' : ∀ l < pd + cd, memAt rd (memAt rd (qbp * x) 0) l = bitE (q.testBit l) :=
    fun l hl => memAt_of_load (hbits l hl)
  obtain ⟨p2, pk2, pk22, pk26, pk27, pdb, p86, plv, pf, pc0, pc1, p17, p19, pptr, parg⟩ :=
    oqIterValC_ptrs (CM := CM) (Ht := Ht) (rd := rd) (N := N) (rew := rew) (flags := flags) (cap := cap) (ptr := ptr) (leaf := leaf) hs hq
      hsl hbits'
  rw [← hσ] at p2 pk2 pk22 pk26 pk27 pdb p86 plv pf pc0 pc1 p17 p19 pptr parg
  change σ (.n (oqK7 base I blocks pd cd + 17)) = x * gen + N at p17
  change σ (.n (oqK7 base I blocks pd cd + 19)) = x * gen at p19
  have hargs : ([.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7] : List V).map σ = [x, N, rew, qsc, qw, qbp, flags, cap] := by
    simp only [List.map_cons, List.map_nil, parg 0 (by omega), parg 1 (by omega), parg 2 (by omega),
      parg 3 (by omega), parg 4 (by omega), parg 5 (by omega), parg 6 (by omega), parg 7 (by omega)]
    rfl
  have hnext : ([.n (oqK7 base I blocks pd cd + 19), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7] : List V).map σ =
      [x * gen, N, rew, qsc, qw, qbp, flags, cap] := by
    simp only [List.map_cons, List.map_nil, p19, parg 1 (by omega), parg 2 (by omega), parg 3 (by omega),
      parg 4 (by omega), parg 5 (by omega), parg 6 (by omega), parg 7 (by omega)]
    rfl
  have hholds : Stmt.HoldsListB CM.sem (coreProgram.RelB CM.sem rd) rd σ lf.body False (fun rs => rs = []) := by
    rw [hb, hσ]
    refine oqIter_holdsC hs hleaf hq hsl hw hs0 hw0 hs1 hdbp hbits hptrK hcell hflag hcap hK (fun hne => ?_)
      hleafA hpathA
    rw [ite_pos' hne] at htail
    exact htail.toB.relAt.rel
  have hbody : lf.body = oqLoopPre base I blocks pd cd loop ++ [.ret []] := hb.trans (oqLoopBody_split _ _ _ _ _ _)
  set es := (oqLoopPre base I blocks pd cd loop).flatMap (Main.slEvs σ)
  have hw' : walk σ lf.body = .ret es [] := by rw [hbody]; exact Main.walk_straight σ [] _ hpl.straight
  have hev := oq_holds_eventsB hfind hholds hw'
  obtain ⟨had, hal, hadr, hcl⟩ := Main.straight_parts σ _ hpl.straight
  have hal0 : allocs σ es = [] := by rw [hal, hpl.allocs]; rfl
  set c : Call := ⟨loop, [.n (oqK7 base I blocks pd cd + 19), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7],
      [], decide (σ (.n (oqK7 base I blocks pd cd + 17)) ≠ 0)⟩ with hc
  have hcalls : calls es = [] ++ [c] := by rw [hcl, hpl.calls]; rfl
  have hrun : (.n P, 80) ∈ runs es := by rw [oq_runs_straight σ _ hpl.straight, hpl.runs]; simp [P]
  have hown : ∀ t < 80, ownData cert fp (fp + fs loop + m) loop (allocs σ es) es (c0 + t) := fun t ht =>
    Or.inr ⟨_, hrun, Nat.le_add_right c0 t, Nat.add_lt_add_left ht c0⟩
  -- the decoding
  have hQ : ∀ (ks : List Tree) (k : Tree), Tree.KidsValidB CM.sem coreProgram rd σ [] ks →
      Tree.KidsValidB CM.sem coreProgram rd σ [c] [k] →
      (c.taken = true → OqLoopQ base I blocks pd cd loop n [N, rew, qsc, qw, qbp, flags, cap] cap leafF posF sibsF
        (j0 + 1) k) →
      OqLoopQ base I blocks pd cd loop n [N, rew, qsc, qw, qbp, flags, cap] cap leafF posF sibsF j0
        (Memory.Tree.node loop σ (allocs σ es) (ks ++ [k])) := by
    intro ks k hks _ hkq rd' V hsat hlink hV j hj1 hj2
    match ks, hks with
    | [], _ =>
    simp only [List.nil_append] at hsat hlink
    rcases Nat.eq_or_lt_of_le hj1 with rfl | hlt
    · have hag := fun v (hv : v ∈ oqLoopReads base I blocks pd) (hn : v ∈ B2C.namedOf lf.params es []) =>
        nodeAgree_read hfind hw' hV hNA hv hn
      rw [hp] at hag
      obtain ⟨n1, n2, n3, n4⟩ := oqIter_named hs loop σ ([] : List LeanVM.Guest.Core.V)
      rw [oqOpeningOf_congr (hag _ (by simp [oqLoopReads]) n4)
        (fun j hj => hag _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
          (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))) (n1 j hj))
        (hag _ (by simp [oqLoopReads]) n2)
        (fun k hk => hag _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _
          (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)))) (n3 k hk)), hσ]
      refine oqOpeningOf_iterC hs hleaf hq hsl hbits' fun l hl => ?_
      obtain ⟨d, hd⟩ := oqLoopPre_bitLoad (base := base) (I := I) (blocks := blocks) hs.cd1 loop l hl
      have hm := mem_loadEqns_load (P := coreProgram) (bufs := allocs σ es) (kids := [k]) hfind hw'
        (mem_slEvs_of (σ := σ) hd)
      have hld : LoadHolds rd (σ (.n (oqP base I blocks - 1))) l (σ d) := hev _ (mem_slEvs_of hd)
      rw [pdb] at hm hld
      have h1 : Sat rd [((memAt rd (qbp * x) 0).limb 0 * Parameters.gpow l, σ d)] := fun q' hq' => by
        rw [List.mem_singleton.mp hq']; exact hld.2
      have h2 : Sat rd' [((memAt rd (qbp * x) 0).limb 0 * Parameters.gpow l, σ d)] := fun q' hq' => by
        rw [List.mem_singleton.mp hq']; exact hsat _ hm
      exact memAt_agree h1 h2 (List.mem_singleton_self _)
    · have hne : x * gen + N ≠ 0 := fun h0 => by have := hlast h0; omega
      have ht : c.taken = true := by simp only [hc, p17]; exact decide_eq_true hne
      have hkQ := hkq ht
      obtain ⟨hcalls', hkids⟩ := hlink
      rw [events_node hfind hw', hcalls, List.nil_append] at hcalls'
      have hVk := hcalls'.1 ht hdec
      simp only [hc] at hVk
      rw [hnext] at hVk
      simp only [List.map_nil] at hVk
      refine hkQ rd' V (fun q' hq' => hsat q' (mem_loadEqns_kid (List.mem_singleton_self k) hq')) hkids.1 ?_ j
        (by omega) hj2
      rwa [gen_pow_mul_gen] at hVk
  have h := relAtInBT_of_walk_loopW (S := CM.sem) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    (R := R) (D := fun _ => False) (Dk := fun _ => False) (Rt := R) (Dt := fun _ => False) (fp := fp) (m := m)
    (N := 0) (Qt := OqLoopQ base I blocks pd cd loop n [N, rew, qsc, qw, qbp, flags, cap] cap leafF posF sibsF (j0 + 1))
    hfind hlp (hp ▸ hargs) hw' rfl hev hcalls ?_
    (by rw [had, hpl.allocs, hal0]; rfl)
    (fun q hq' => by
      rw [hadr, hpl.addrs] at hq'
      simp only [List.mem_singleton] at hq'
      subst hq'
      exact pptr)
    (by rw [hal0]; exact ⟨rfl, fun i h => h.elim⟩)
    (fun i hi => Or.inl hi)
    (fun A hA => ?_)
    (fun _ h => h.elim) hQ
  · rw [hal0, List.sum_nil, Nat.add_zero, Nat.add_zero] at h; exact h
  · by_cases ht : x * gen + N ≠ 0
    · rw [ite_pos' ht] at htail
      simp only [hc, p17]
      rw [ite_pos' (decide_eq_true ht), List.map_nil, hnext]
      exact htail
    · rw [ite_neg' ht] at htail
      simp only [hc, p17]
      rw [ite_neg' (by simpa using ht)]
      exact htail
  · rw [loadAddrs_straight σ _ hpl.straight] at hA
    obtain ⟨⟨p, off⟩, hq', rfl⟩ := List.mem_map.mp hA
    have hb' := List.all_eq_true.mp hpl.loads _ hq'
    simp only [oqLoadB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Prod.mk.injEq,
      List.any_eq_true, List.mem_range, or_assoc, oqK7] at hb'
    have inR : ∀ A, OqIn R A → ∃ i, A = Parameters.gpow i ∧
        (ownData cert fp (fp + fs loop + m) loop (allocs σ es) es i ∨ R i ∨ False ∨ (c.taken = true ∧ False)) :=
      fun A ⟨i, hi, hR⟩ => ⟨i, hi, Or.inr (Or.inl hR)⟩
    have inOwn : ∀ t < 80, ∃ i, Parameters.gpow (c0 + t) = Parameters.gpow i ∧
        (ownData cert fp (fp + fs loop + m) loop (allocs σ es) es i ∨ R i ∨ False ∨ (c.taken = true ∧ False)) :=
      fun t ht => ⟨_, rfl, Or.inl (hown t ht)⟩
    rcases hb' with ⟨rfl, ho⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, ho⟩ |
      ⟨rfl, ho⟩ | ⟨l, hl, ⟨hl1, rfl⟩, ho⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [p2]; exact inR _ (hRw off ho)
    · rw [pk2]; exact inR _ hRs.1
    · rw [pk22]; exact inR _ hRq
    · rw [pk26]; exact inR _ hRs.2
    · rw [pk27]; exact inR _ hRb
    · rw [pdb]; exact inR _ (hRd off ho)
    · rw [p86, oq_addr, Nat.add_assoc]
      exact inOwn _ (by cases q.testBit 0 <;> simp <;> omega)
    · rw [plv l hl1 hl, oq_addr, Nat.add_assoc]
      exact inOwn _ (by have := hs.pd20; cases q.testBit l <;> simp <;> omega)
    · rw [pf]; exact inR _ hRf
    · rw [pc0]; exact inR _ hRc.1
    · rw [pc1]; exact inR _ hRc.2

/-- **`oqLoop_relAtInC` by a tree decoding to the openings.** -/
theorem oqLoop_relAtInCT {CM : CompModel} {Ht : Bytes → Digest} (fs : String → ℕ) (cert : String → V → ℕ)
    {base I blocks pd cd : ℕ} (hs : OqShape base I blocks pd cd) {loop : String} {lf : Fn}
    (hfind : coreProgram.find? loop = some lf) (hp : lf.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7])
    (hb : lf.body = oqLoopBody base I blocks pd cd loop) (hpl : OqPlace base I blocks pd cd loop)
    (hlp : coreProgram.loop loop = true) (hNA : CellsOk loop (oqLoopReads base I blocks pd)) (hdec : loop ∈ osDecNames) {n : ℕ} (hn : n < ordG) {rd : Reader} {R : ℕ → Prop}
    {rew qsc qw qbp flags cap : E} {leaf : ℕ → List K} (hleaf : ∀ j < n, (leaf j).length = oqR base I)
    {pos : ℕ → ℕ} (hq : ∀ j < n, pos j < 2 ^ (pd + cd)) {sibs : ℕ → List Digest}
    (hsl : ∀ j < n, (sibs j).length = pd) {fp j0 : ℕ} (hj0 : j0 < n)
    (hd : ∀ j < n, OqIterMemW Ht rd base I pd cd rew qsc qw qbp flags cap (gen ^ j) (leaf j) (pos j) (sibs j) ∧
      OqIterReg R rd I pd cd rew qsc qw qbp flags cap (gen ^ j) (pos j) ∧ OqAns CM Ht pd (leaf j) (pos j) (sibs j))
    (hcell : ∀ j, j0 ≤ j → j < n → ∀ t < 4 * pd,
      LoadHolds rd (ofK (Parameters.gpow (fp + (j - j0) * (fs loop) + cert loop (.n (oqP base I blocks))))) t
        ((climbCellsW Ht (hashWordsW Ht (leaf j)) (pos j) (sibs j)).getD t 0)) :
    RelAtInBT CM.sem fs cert rd R (fun _ => False) fp ((n - j0 + 1) * fs loop) loop
      [gen ^ j0, gen ^ n, rew, qsc, qw, qbp, flags, cap] []
      (OqLoopQ base I blocks pd cd loop n [gen ^ n, rew, qsc, qw, qbp, flags, cap] cap leaf pos sibs j0) := by
  have hn' : n < 2 ^ 64 - 1 := hn
  have hstep : ∀ t j, j + t + 1 = n → j0 ≤ j →
      RelAtInBT CM.sem fs cert rd R (fun _ => False) (fp + (j - j0) * (fs loop))
        ((n - j + 1) * (fs loop)) loop [gen ^ j, gen ^ n, rew, qsc, qw, qbp, flags, cap] []
        (OqLoopQ base I blocks pd cd loop n [gen ^ n, rew, qsc, qw, qbp, flags, cap] cap leaf pos sibs j) := by
    intro t
    induction t with
    | zero =>
      intro j hj hlo
      obtain ⟨⟨m1, m2, m3, m4, m5, m6, m7, m8⟩, ⟨r1, r2, r3, r4, r5, r6, r7⟩, a1, a2⟩ := hd j (by omega)
      have h0 : gen ^ j * gen + gen ^ n = 0 := by rw [gen_pow_add_eq_zero_iff]; congr 1; omega
      have := oqLoop_iterCT (CM := CM) (Ht := Ht) fs cert hs hfind hp hb hpl hlp hNA hdec (rd := rd) (R := R) (n := n) (j0 := j)
        (leafF := leaf) (posF := pos) (sibsF := sibs)
        (hleaf j (by omega)) (hq j (by omega)) (hsl j (by omega)) (fp + (j - j0) * (fs loop)) (m := (fs loop))
        m1 m2 m3 m4 m5 m6 (hcell j hlo (by omega)) m7 m8 a1 a2
        (by rw [h0]; exact ((isInK_iff _).mpr ⟨0, ofK_zero.symm⟩)) (fun _ => by omega)
        (by rw [ite_neg' (by simp [h0])])
        r1 r2 r3 r4 r5 r6 r7
      rwa [show n - j + 1 = 2 by omega, two_mul]
    | succ t ih =>
      intro j hj hlo
      obtain ⟨⟨m1, m2, m3, m4, m5, m6, m7, m8⟩, ⟨r1, r2, r3, r4, r5, r6, r7⟩, a1, a2⟩ := hd j (by omega)
      have hne : gen ^ j * gen + gen ^ n ≠ 0 := by
        rw [ne_eq, gen_pow_add_eq_zero_iff]
        intro he
        have := gen_pow_inj (by omega) (by omega) he
        omega
      have ht := ih (j + 1) (by omega) (by omega)
      rw [show j + 1 - j0 = (j - j0) + 1 by omega, Nat.add_mul, Nat.one_mul, ← Nat.add_assoc] at ht
      have := oqLoop_iterCT (CM := CM) (Ht := Ht) fs cert hs hfind hp hb hpl hlp hNA hdec (rd := rd) (R := R) (n := n) (j0 := j)
        (leafF := leaf) (posF := pos) (sibsF := sibs)
        (hleaf j (by omega)) (hq j (by omega)) (hsl j (by omega)) (fp + (j - j0) * (fs loop))
        (m := (n - (j + 1) + 1) * (fs loop)) m1 m2 m3 m4 m5 m6 (hcell j hlo (by omega)) m7 m8 a1 a2
        (isInK_add (by rw [gen_pow_mul_gen]; exact gen_pow_isInK _) (gen_pow_isInK _)) (fun h => absurd h hne)
        (by rw [ite_pos' hne, gen_pow_mul_gen]; exact ht) r1 r2 r3 r4 r5 r6 r7
      rwa [show (n - j + 1) * (fs loop) = (fs loop) + (n - (j + 1) + 1) * (fs loop) by
        rw [show n - j + 1 = (n - (j + 1) + 1) + 1 by omega, Nat.add_mul, Nat.one_mul, Nat.add_comm]]
  have := hstep (n - j0 - 1) j0 (by omega) le_rfl
  rwa [Nat.sub_self, Nat.zero_mul, Nat.add_zero] at this

end
end LeanVM.Guest.B1
