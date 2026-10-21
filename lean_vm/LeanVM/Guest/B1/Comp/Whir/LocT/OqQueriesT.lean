/-
  LeanVM.Guest.B1.Comp.Whir.LocT.OqQueriesT

  `opening_queries`, placed over a completeness model, by a tree decoding to the queries' openings.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.LocT.OqLoopT
public import LeanVM.Guest.B1.Comp.Whir.Loc.QueriesAt

/-!
# `opening_queries` by a tree decoding to its openings

`OqQueriesQ … t`: on every reader satisfying `t`'s load equations and every frame valuation linked
to `t`, `opening_queries`' frame at `t` decodes (`oqQueriesOs` at `wlV`) to the queries' openings
(`oqHonest`). `oqLoop_completeAtCT`, `opening_queries_completeAtCT`: `oqLoop_completeAtC`,
`opening_queries_completeAtC` by such trees; `OqCompleteAtBCT`: `OqCompleteAtBC` by such trees, at
the loop helper and block count `oqLookup` gives the specialization.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)
open LeanVM.Guest.Located (oqLookup loopCount loopCount_eq)
open LeanVM.E2E.Complete

@[expose] public section

/-- **`opening_queries`' tree decodes to the queries' openings.** -/
def OqQueriesQ (base I blocks pd cd : ℕ) (loop : String) (n : ℕ) (cap : E) (leaf : ℕ → List K) (pos : ℕ → ℕ)
    (sibs : ℕ → List Digest) (t : Tree) : Prop :=
  ∀ (rd : Reader) (V : FrameVals) (σ' : Val), Sat rd (t.loadEqns coreProgram) → KidsLink V t →
    B2C.NodeAgree t σ' →
    oqQueriesOs (wlV rd V base I blocks pd cd loop) σ' = (List.range n).map (oqHonest pd cd rd cap leaf pos sibs)

variable {Ht : Bytes → Digest} {CM : CompModel}

/-- **`oqLoop_completeAtC` by a tree decoding to the openings.** -/
theorem oqLoop_completeAtCT (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) {base I blocks pd cd : ℕ}
    (hs : OqShape base I blocks pd cd) {loop : String} {lf : Fn} (hfind : coreProgram.find? loop = some lf)
    (hp : lf.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7])
    (hb : lf.body = oqLoopBody base I blocks pd cd loop) (hpl : OqPlace base I blocks pd cd loop)
    (hlp : coreProgram.loop loop = true) (hNA : CellsOk loop (oqLoopReads base I blocks pd))
    (hdec : loop ∈ osDecNames)
    (hfit : cert loop (.n (oqP base I blocks)) + 4 * pd ≤ fs loop) {n : ℕ} (hn : n < ordG) {Lin : Main.Layout} {rew qsc qw qbp flags cap : E} {leaf : ℕ → List K}
    (hleaf : ∀ j < n, (leaf j).length = oqR base I) {pos : ℕ → ℕ} (hq : ∀ j < n, pos j < 2 ^ (pd + cd))
    {sibs : ℕ → List Digest} (hsl : ∀ j < n, (sibs j).length = pd)
    (hans : ∀ j < n, OqAns CM Ht pd (leaf j) (pos j) (sibs j))
    (hmem : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < n,
      OqIterMemW Ht rd base I pd cd rew qsc qw qbp flags cap (gen ^ j) (leaf j) (pos j) (sibs j) ∧
        OqIterReg (RegionL Lin) rd I pd cd rew qsc qw qbp flags cap (gen ^ j) (pos j)) :
    ∀ j0 < n, CompleteAtBST CM.sem fs cert k loop Lin [gen ^ j0, gen ^ n, rew, qsc, qw, qbp, flags, cap] (Returns [])
      ((n - j0 + 1) * fs loop)
      (fun _ _ t => OqLoopQ base I blocks pd cd loop n [gen ^ n, rew, qsc, qw, qbp, flags, cap] cap leaf pos sibs j0 t) := by
  intro j0 hj0 fp
  have hn' : n < 2 ^ 64 - 1 := hn
  set P := oqP base I blocks
  refine ⟨(n - j0 + 1) * (fs loop), oqLoopRunsW Ht fs cert loop P fp j0 n leaf pos sibs, [], [], ⟨rfl, rfl⟩, ?_,
    ?_, le_rfl, fun rd hlow hmemL => ?_⟩
  · intro e he
    simp only [List.nil_append, oqLoopRunsW, List.mem_map, List.mem_range] at he
    obtain ⟨i, hi, rfl⟩ := he
    rw [oq_length_climbCellsW, hsl _ (by omega)]
    refine ⟨by omega, ?_⟩
    have : (i + 1) * (fs loop) ≤ (n - j0 + 1) * (fs loop) := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  · rw [List.nil_append]
    exact oq_disj_frames fun i hi => by rw [oq_length_climbCellsW, hsl _ (by omega)]; exact hfit
  simp only [List.nil_append] at hmemL
  obtain ⟨hruns, hlin⟩ := Main.memL_append.mp hmemL
  have hd := hmem rd hlow hlin
  have hcell : ∀ j, j0 ≤ j → j < n → ∀ t < 4 * pd,
      LoadHolds rd (ofK (Parameters.gpow (fp + (j - j0) * (fs loop) + cert loop (.n P)))) t
        ((climbCellsW Ht (hashWordsW Ht (leaf j)) (pos j) (sibs j)).getD t 0) := by
    intro j hj1 hj2 t ht
    have := hruns _ (List.mem_map.mpr ⟨j - j0, List.mem_range.mpr (by omega), rfl⟩)
    simp only [show j0 + (j - j0) = j by omega] at this
    have hlen : t < (climbCellsW Ht (hashWordsW Ht (leaf j)) (pos j) (sibs j)).length := by
      rw [oq_length_climbCellsW, hsl j hj2]; exact ht
    have h := this t hlen
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]
  have := oqLoop_relAtInCT (CM := CM) fs cert hs hfind hp hb hpl hlp hNA hdec hn hleaf hq hsl hj0
    (fun j hj => ⟨(hd j hj).1, (hd j hj).2, hans j hj⟩) hcell
  exact this.dmono fun i hi => by obtain ⟨q, hq', _⟩ := hi; simp at hq'

/-- `1 + g^n` is not zero for `0 < n` below the order of `g`. -/
theorem one_add_gen_pow_ne {n : ℕ} (h0 : 0 < n) (hn : n < 2 ^ 64 - 1) : 1 + gen ^ n ≠ 0 := by
  intro h
  have h1 : (1 : E) = gen ^ n := by
    have := congrArg (· + gen ^ n) h
    simpa [add_assoc, e_add_self] using this
  have := gen_pow_inj (a := 0) (b := n) (by omega) hn (by rw [pow_zero]; exact h1)
  omega

set_option maxHeartbeats 400000 in
/-- **`opening_queries_completeAtC` by a tree decoding to the openings.** -/
theorem opening_queries_completeAtCT (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) {base I blocks pd cd : ℕ}
    (hs : OqShape base I blocks pd cd) {name loop : String} {f lf : Fn} (hfind : coreProgram.find? name = some f)
    (hp : f.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5]) (hb : f.body = oqBody loop)
    (hnl : coreProgram.loop name = false) (hlfind : coreProgram.find? loop = some lf)
    (hlp' : lf.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7])
    (hlb : lf.body = oqLoopBody base I blocks pd cd loop) (hpl : OqPlace base I blocks pd cd loop)
    (hlp : coreProgram.loop loop = true) (hNAq : CellsOk name oqTopReads) (hNA : CellsOk loop (oqLoopReads base I blocks pd))
    (hdec : loop ∈ osDecNames)
    (hfit : cert loop (.n (oqP base I blocks)) + 4 * pd ≤ fs loop) {n : ℕ} (hn : n + 1 < ordG) {Lin : Main.Layout} {cap flags qw qbp rew : E} {leaf : ℕ → List K}
    (hleaf : ∀ j < n, (leaf j).length = oqR base I) {pos : ℕ → ℕ} (hq : ∀ j < n, pos j < 2 ^ (pd + cd))
    {sibs : ℕ → List Digest} (hsl : ∀ j < n, (sibs j).length = pd)
    (hans : ∀ j < n, OqAns CM Ht pd (leaf j) (pos j) (sibs j)) {wts qwV dbpV : ℕ → E}
    (hlin : ∀ rd, LowDef k rd → MemL rd Lin → OqTopMemW Ht rd I pd cd rew qw qbp flags cap wts qwV dbpV leaf pos sibs n)
    (hreg : OqTopReg (RegionL Lin) I pd cd rew qw qbp flags cap dbpV pos n) :
    CompleteAtBST CM.sem fs cert k name Lin [cap, flags, qw, qbp, rew, gen ^ n]
      (Returns [oqSum base I wts qwV leaf n]) (fs name + (n + 1) + (n + 1) * fs loop)
      (fun _ _ t => OqQueriesQ base I blocks pd cd loop n cap leaf pos sibs t) := by
  intro fp
  set b := fp + fs name
  set qscV : List E := (List.range (n + 1)).map (oqSum base I wts qwV leaf)
  set qsc : E := ofK (Parameters.gpow b)
  set Lq : Main.Layout := Lin ++ [(b, qscV)]
  set kid : Kid := ⟨loop, decide (1 + gen ^ n ≠ 0), [1, gen ^ n, rew, qsc, qw, qbp, flags, cap], Lq, Returns []⟩
  set qk : Kid → ℕ → Reader → Tree → Prop := fun _ _ _ t =>
    OqLoopQ base I blocks pd cd loop n [gen ^ n, rew, qsc, qw, qbp, flags, cap] cap leaf pos sibs 0 t with hqk
  have hqscV : ∀ j ≤ n, qscV.getD j 0 = oqSum base I wts qwV leaf j := fun j hj => by
    simp [qscV, List.getD_eq_getElem?_getD, List.getElem?_range (show j < n + 1 by omega)]
  have hqlen : qscV.length = n + 1 := by simp [qscV]
  have hkid : ∀ κ ∈ [kid], κ.taken = true →
      CompleteAtWST CM.sem fs cert wE k κ.f κ.Lin κ.args κ.Out ((n + 1) * fs loop) bwE (qk κ) := by
    intro κ hκ ht
    simp only [List.mem_singleton] at hκ
    subst hκ
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · simp [kid, h0] at ht
        exact absurd (e_add_self _) ht
      · exact h0
    have := oqLoop_completeAtCT (Ht := Ht) (CM := CM) fs cert k hs hlfind hlp' hlb hpl hlp hNA hdec hfit (by omega) (Lin := Lq)
      (rew := rew) (qsc := qsc) (qw := qw) (qbp := qbp) (flags := flags) (cap := cap) hleaf hq hsl hans ?_ 0 hn0
    · have h' := this.toWSTE
      simp only [Nat.sub_zero, pow_zero] at h'
      exact h'
    intro rd hlow hmem j hj
    obtain ⟨hL, hQ⟩ := Main.memL_append.mp hmem
    obtain ⟨m1, m2, m3, m4, m5, m6⟩ := hlin rd hlow hL
    obtain ⟨r1, r2, r3, r4, r5, r6⟩ := hreg
    have hqs : ReadsAt rd qsc qscV := hQ _ (List.mem_singleton.mpr rfl)
    have hq0 : ∀ i ≤ n, LoadHolds rd qsc i (oqSum base I wts qwV leaf i) := fun i hi => by
      have := hqs i (by omega)
      rwa [← hqscV i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hqscK : IsInK qsc := (isInK_iff _).mpr ⟨_, rfl⟩
    have e1 : memAt rd (qsc * gen ^ j) 0 = oqSum base I wts qwV leaf j :=
      memAt_of_load ((loadHolds_gen_pow rd qsc j _).mpr (hq0 j (by omega)))
    have e2 : memAt rd (qw * gen ^ j) 0 = qwV j := memAt_of_load ((loadHolds_gen_pow rd qw j _).mpr (m2 j hj))
    have e3 : memAt rd (qbp * gen ^ j) 0 = dbpV j := memAt_of_load ((loadHolds_gen_pow rd qbp j _).mpr (m3 j hj))
    have ew : ∀ jw < I, memAt rd rew jw = wts jw := fun jw hjw => memAt_of_load (m1 jw hjw)
    have inL : ∀ i, RegionL Lin i → RegionL Lq i := fun i ⟨q, hq', h⟩ => ⟨q, List.mem_append_left _ hq', h⟩
    have inQ : ∀ t ≤ n, RegionL Lq (b + t) := fun t ht =>
      ⟨(b, qscV), List.mem_append_right _ (List.mem_singleton.mpr rfl), Nat.le_add_right b t,
        by show b + t < b + qscV.length; rw [hqlen]; omega⟩
    refine ⟨⟨fun jw hjw => by rw [ew jw hjw]; exact m1 jw hjw, by rw [e1, loadHolds_gen_pow]; exact hq0 j (by omega),
      by rw [e2, loadHolds_gen_pow]; exact m2 j hj, ?_, by rw [e3, loadHolds_gen_pow]; exact m3 j hj,
      by rw [e3]; exact m4 j hj, m5 j hj, m6 j hj⟩, fun jw hjw => oq_in_mono inL (r1 jw hjw), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e1, e2, Finset.sum_congr rfl fun jw hjw => by rw [ew jw (Finset.mem_range.mp hjw)],
        loadHolds_mul_gen_pow]
      have := hq0 (j + 1) (by omega)
      rw [oqSum, Finset.sum_range_succ] at this
      exact this
    · refine ⟨⟨b + j + 0, by rw [oq_limb_mul_gen_pow hqscK]; simp [qsc, limb_ofK, Parameters.gpow, pow_add],
          inQ j (by omega)⟩,
        ⟨b + j + 1, by rw [oq_limb_mul_gen_pow hqscK]; simp [qsc, limb_ofK, Parameters.gpow, pow_add, mul_assoc],
          inQ (j + 1) (by omega)⟩⟩
    · rw [oq_limb_mul_gen_pow (m2 j hj).1, Nat.add_zero]; exact oq_in_mono inL (r2 j hj)
    · rw [oq_limb_mul_gen_pow (m3 j hj).1, Nat.add_zero]; exact oq_in_mono inL (r3 j hj)
    · intro l hl; rw [e3]; exact oq_in_mono inL (r4 j hj l hl)
    · rw [oq_limb_mul_gen_pow (m5 j hj).1, Nat.add_zero]; exact oq_in_mono inL (r5 j hj)
    · refine ⟨?_, ?_⟩
      · rw [oq_limb_mul_gen_pow (m6 j hj).1.1, Nat.add_zero]; exact oq_in_mono inL (r6 j hj).1
      · rw [oq_limb_mul_gen_pow (m6 j hj).1.1, Nat.add_zero]; exact oq_in_mono inL (r6 j hj).2
  obtain ⟨N, L, outs, ho, hW, hD, hNb, -, hK⟩ := kidsFromInWST_of_kidsBW (S := CM.sem) (fs := fs) (cert := cert)
    (w := wE) k (fun _ => (n + 1) * fs loop) (fun _ => bwE) qk [kid] hkid (b + (n + 1))
  have hNb' : N ≤ (n + 1) * fs loop := by
    refine le_trans hNb ?_
    simp only [kidsBound, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    split
    · exact le_rfl
    · exact Nat.le_mul_of_pos_left _ (Nat.succ_pos n)
  obtain ⟨o, rfl⟩ : ∃ o, outs = [o] := by
    match outs, ho with
    | [o], _ => exact ⟨o, rfl⟩
  have ho1 : kid.taken = true → o.1 = [] := fun ht => (ho.1 ht).1
  have hW1 : Within [(b, qscV)] b (n + 1) := fun e he => by
    simp only [List.mem_singleton] at he
    subst he
    simp only [hqlen]; omega
  refine ⟨fs name + (n + 1) + N, [(b, qscV)] ++ L, [oqSum base I wts qwV leaf n], [], ⟨rfl, rfl⟩, ?_,
    ?_, by omega, fun rd hlow hmem => ?_⟩
  · rw [List.nil_append, within_append]
    exact ⟨hW1.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  · rw [List.nil_append]
    exact disj_append (List.pairwise_singleton _ _) hD hW1 hW le_rfl
  obtain ⟨h1, hLin⟩ := Main.memL_append.mp hmem
  obtain ⟨-, h2⟩ := Main.memL_append.mp h1
  obtain ⟨hQ1, hL⟩ := Main.memL_append.mp h2
  have hQ : ReadsAt rd qsc qscV := hQ1 _ (List.mem_singleton_self _)
  have hq0 : ∀ i ≤ n, LoadHolds rd qsc i (oqSum base I wts qwV leaf i) := fun i hi => by
    have := hQ i (by omega)
    rwa [← hqscV i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  set σ := Val.ofArgs [cap, flags, qw, qbp, rew, gen ^ n, gen, gen ^ (n + 1), qsc, 0, 1, 1 + gen ^ n, 1,
    qsc * gen ^ n, oqSum base I wts qwV leaf n] with hσ
  have hbody : f.body = oqPre loop ++ [.ret [.n 14]] := by rw [hb]; rfl
  have hstr : (oqPre loop).all Main.Stmt.straight = true := rfl
  have hholds : Stmt.HoldsListB CM.sem (fun _ _ _ => True) rd σ f.body False
      (fun rs => rs = [oqSum base I wts qwV leaf n]) := by
    rw [hb]
    simp only [oqBody, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, hσ, ofArgs_n,
      List.getD_cons_zero, List.getD_cons_succ, word_gen, true_and, and_true]
    refine ⟨by rw [pow_succ], ?_, hq0 0 (by omega), ?_, ?_, ?_, fun _ => trivial, ?_⟩
    · show (0 : E) = word 0 0 0
      rw [word_zero]
    · show (1 : E) = word 1 0 0
      rw [word_one]
    · show (1 : E) = word 1 0 0
      rw [word_one]
    · exact isInK_add (by simpa using gen_pow_isInK 0) (gen_pow_isInK n)
    · have := hq0 n le_rfl
      rw [← loadHolds_gen_pow] at this
      exact this
  have hw : walk σ f.body = .ret ((oqPre loop).flatMap (Main.slEvs σ)) [.n 14] := by
    rw [hbody]; exact Main.walk_straight σ _ _ hstr
  have hev := oq_holds_eventsB hfind hholds hw
  obtain ⟨had, hal, hadr, hcl⟩ := Main.straight_parts σ _ hstr
  have hlog : logG (σ (.n 7)) = n + 1 := by
    show logG (gen ^ (n + 1)) = n + 1
    rw [gen_pow_eq_ofK]; exact logG_spec (by omega)
  have hal' : allocs σ ((oqPre loop).flatMap (Main.slEvs σ)) = [n + 1] := by
    rw [hal]; show [logG (σ (.n 7))] = [n + 1]; rw [hlog]
  set c : Call := ⟨loop, [.n 12, .n 5, .n 4, .n 8, .n 2, .n 3, .n 1, .n 0], [], decide (σ (.n 11) ≠ 0)⟩ with hc
  have hcalls : calls ((oqPre loop).flatMap (Main.slEvs σ)) = [c] := by
    rw [hcl]; rfl
  have hown : ∀ t ≤ n, ownData cert fp (fp + fs name) name (allocs σ ((oqPre loop).flatMap (Main.slEvs σ)))
      ((oqPre loop).flatMap (Main.slEvs σ)) (b + t) := fun t ht => by
    rw [hal']
    exact Or.inl ⟨(n + 1, fp + fs name), by simp [bases], by simp [b], by simp [b]; omega⟩
  have hcargs : c.args.map σ = [1, gen ^ n, rew, qsc, qw, qbp, flags, cap] := by
    simp [hc, hσ, ofArgs_n]
  have hQ' : ∀ ks : List Tree, Tree.KidsValidB CM.sem coreProgram rd σ (calls ((oqPre loop).flatMap (Main.slEvs σ))) ks →
      KidsSat (calls ((oqPre loop).flatMap (Main.slEvs σ))) ([kid].map fun κ b t => qk κ b rd t)
        (bases (fp + fs name + (allocs σ ((oqPre loop).flatMap (Main.slEvs σ))).sum) (ks.map (Tree.total fs))) ks →
      OqQueriesQ base I blocks pd cd loop n cap leaf pos sibs
        (Memory.Tree.node name σ (allocs σ ((oqPre loop).flatMap (Main.slEvs σ))) ks) := by
    intro ks hkv hks rd' V σ' hsat hlink hag
    rw [hcalls] at hkv hks
    match ks, hkv, hks with
    | [kt], ⟨_, _, _⟩, hks =>
    have hag' : ∀ v ∈ oqTopReads, v ∈ B2C.namedOf f.params ((oqPre loop).flatMap (Main.slEvs σ)) [.n 14] →
        σ' v = σ v := fun v hv hn => nodeAgree_read hfind hw hag hNAq hv hn
    rw [hp] at hag'
    rw [oqQueriesOs_congr fun i hi => hag' _ hi ?_]
    swap
    · simp only [oqTopReads, List.mem_cons, List.not_mem_nil, or_false] at hi
      have hci : Stmt.callIf (.n 11) loop [.n 12, .n 5, .n 4, .n 8, .n 2, .n 3, .n 1, .n 0] ∈ oqPre loop := by
        simp [oqPre, oqBody]
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact mem_named_param (by simp)
      · exact mem_named_param (by simp)
      · exact mem_named_param (by simp)
      · exact mem_named_param (by simp)
      · exact mem_named_param (by simp)
      · exact mem_named_param (by simp)
      · exact mem_named_callIf_arg hci (by simp)
      · exact mem_named_callIf_cond hci
      · exact mem_named_callIf_arg hci (by simp)
    show oqQueriesOs (wlV rd' V base I blocks pd cd loop) σ = _
    unfold oqQueriesOs
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · have e : σ (.n 11) = 0 := by
        simp only [hσ, ofArgs_n, List.getD_cons_succ, List.getD_cons_zero, h0, pow_zero]
        exact e_add_self 1
      rw [ite_eq_right_iff.mpr (fun h => absurd e h), h0]
      rfl
    · have hne : σ (.n 11) ≠ 0 := by
        simp only [hσ, ofArgs_n, List.getD_cons_succ, List.getD_cons_zero]
        exact one_add_gen_pow_ne h0 (by simp only [ordG] at hn; omega)
      have ht : c.taken = true := by simp only [hc]; exact decide_eq_true hne
      rw [ite_eq_left_iff.mpr (fun h => absurd hne h)]
      have hargs : [σ (.n 12), σ (.n 5), σ (.n 4), σ (.n 8), σ (.n 2), σ (.n 3), σ (.n 1), σ (.n 0)] =
          [1, gen ^ n, rew, qsc, qw, qbp, flags, cap] := hcargs
      rw [hargs]
      obtain ⟨hcl', hkl⟩ := hlink
      rw [events_node hfind hw, hcalls] at hcl'
      have hVk := hcl'.1 ht hdec
      rw [hcargs] at hVk
      simp only [hc, List.map_nil] at hVk
      have hkq : OqLoopQ base I blocks pd cd loop n [gen ^ n, rew, qsc, qw, qbp, flags, cap] cap leaf pos sibs 0 kt :=
        hks.1 ht
      have hsat' : Sat rd' (kt.loadEqns coreProgram) :=
        fun q' hq' => hsat q' (mem_loadEqns_kid (List.mem_singleton_self kt) hq')
      have hcount : loopCount 1 (gen ^ n) = n :=
        loopCount_eq h0 (by rw [one_mul]) fun j hj1 hj2 he => by
          rw [one_mul] at he
          have := gen_pow_inj (by simp only [ordG] at hn; omega) (by simp only [ordG] at hn; omega) he
          omega
      simp only [wlV, loopDecV, frameDecV, List.getD_cons_zero, hcount]
      refine List.map_congr_left fun j hj => ?_
      rw [one_mul]
      exact hkq rd' V hsat' hkl.1 (by rw [pow_zero]; exact hVk) j (Nat.zero_le _) (List.mem_range.mp hj)
  have h := relAtInWST_of_walk (S := CM.sem) (fs := fs) (cert := cert) (w := wE) (σ := σ) (rd := rd)
    (R := RegionL Lin) (D := RegionL []) (Dk := fun i => False ∨ outRegion [kid] [o] i) (fp := fp) (N := N)
    (bws := Main.kidsWs (fun _ => bwE) [kid])
    hfind (Or.inl hnl) (by rw [hp]) hw rfl hev
    (by rw [had, hal']; rfl)
    (fun q hq' => by
      rw [hadr, show (oqPre loop).filterMap Main.Stmt.addrS = [] from rfl] at hq'
      simp at hq')
    ?_ ?_ (fun i hi => by obtain ⟨q, hq', _⟩ := hi; simp at hq') hQ'
  · have h' := h.toBT
    rwa [hal', List.sum_singleton] at h'
  · rw [hcalls, hal', List.sum_singleton]
    refine hK rd σ [c] _ (fun _ => False) ?_ hlow hL ?_ ?_
    · refine ⟨rfl, rfl, fun ht => ⟨rfl, by rw [List.map_nil, ho1 ht]⟩, trivial⟩
    · simp only [Kid.lins, kid, Lq, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact Main.memL_append.mpr ⟨hLin, Main.memL_cons.mpr ⟨hQ, Main.memL_nil.mpr trivial⟩⟩
    · refine ⟨fun _ i hi => ?_, trivial⟩
      obtain ⟨q, hq', h1, h2⟩ := hi
      rcases List.mem_append.mp hq' with hq' | hq'
      · exact Or.inl (Or.inl ⟨q, hq', h1, h2⟩)
      · simp only [List.mem_singleton] at hq'
        subst hq'
        simp only [hqlen] at h1 h2
        have := hown (i - b) (by omega)
        rw [show b + (i - b) = i by omega, hal'] at this
        exact Or.inl (Or.inr this)
  · intro A hA
    rw [loadAddrs_straight σ _ hstr] at hA
    simp only [oqPre, oqBody, List.dropLast, List.filterMap_cons, Stmt.loadS, List.filterMap_nil,
      List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at hA
    rcases hA with rfl | rfl
    · refine ⟨b + 0, ?_, Or.inl (hown 0 (by omega))⟩
      simp [hσ, ofArgs_n, qsc, limb_ofK, Parameters.gpow]
    · refine ⟨b + n, ?_, Or.inl (hown n le_rfl)⟩
      simp only [hσ, ofArgs_n, List.getD_cons_succ, List.getD_cons_zero, qsc]
      rw [oq_limb_mul_gen_pow ((isInK_iff _).mpr ⟨_, rfl⟩)]
      simp [limb_ofK, Parameters.gpow, pow_add]

/-- **`OqCompleteAtBC` by trees decoding to the openings**, at the loop helper and block count
`oqLookup` gives the specialization. -/
def OqCompleteAtBCT (CM : CompModel) (Ht : Bytes → Digest) (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (base I depth cd : ℕ) (name : String) (B : ℕ → ℕ) : Prop :=
  ∃ loop blocks, oqLookup name = some (loop, base, I, blocks, depth - cd, cd) ∧
  ∀ (n : ℕ), n + 1 < ordG → ∀ (Lin : Main.Layout) (cap flags qw qbp rew : E) (leaf : ℕ → List K) (pos : ℕ → ℕ)
    (sibs : ℕ → List Digest) (wts qwV dbpV : ℕ → E),
    (∀ j < n, (leaf j).length = oqR base I) → (∀ j < n, pos j < 2 ^ depth) →
    (∀ j < n, (sibs j).length = depth - cd) → (∀ j < n, OqAns CM Ht (depth - cd) (leaf j) (pos j) (sibs j)) →
    (∀ rd, LowDef k rd → MemL rd Lin →
      OqTopMemW Ht rd I (depth - cd) cd rew qw qbp flags cap wts qwV dbpV leaf pos sibs n) →
    OqTopReg (RegionL Lin) I (depth - cd) cd rew qw qbp flags cap dbpV pos n →
    CompleteAtBST CM.sem fs cert k name Lin [cap, flags, qw, qbp, rew, gen ^ n] (Returns [oqSum base I wts qwV leaf n])
      (B n) (fun _ _ t => OqQueriesQ base I blocks (depth - cd) cd loop n cap leaf pos sibs t)

end
end LeanVM.Guest.B1
