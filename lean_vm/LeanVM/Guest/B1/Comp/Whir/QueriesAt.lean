/-
  LeanVM.Guest.B1.Comp.Whir.QueriesAt

  `opening_queries`' loop helper placed over a completeness model: one iteration and the chain of
  iterations, under the model's semantics.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.QueriesIter
public import LeanVM.Guest.B1.Whir.QueriesAt
public import LeanVM.Guest.Memory.RegionsB
public import LeanVM.Guest.Memory.TreeB

/-!
# One query, placed, over a completeness model (TRIAGE #28, #35)

`Whir/QueriesAt.lean`'s loop over a `CompModel` and a total hash `Ht`, at the placed relation
under `CM.sem` (`RelAtInB`, `Memory/RegionsB.lean`): `oqLoop_iterC` (`oqLoop_iter`, its body
`oqIter_holdsC` at `oqIterValC`, the query answered by the model, `OqAns`) and `oqLoop_relAtInC`
(the chain of iterations from `j0` that `oqLoop_completeAt` wraps). `OqIterMemW` and `oqLoopRunsW`
are `OqIterMem` and `oqLoopRuns` over `Ht`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.E2E.Complete

@[expose] public section

/-- The events of a walked body that holds under `S` hold (`oq_holds_events`). -/
theorem oq_holds_eventsB {S : BlakeSem} {C : CallRel} {rd : Reader} {σ : Val} {f : String} {fn : Fn}
    {es : List Memory.Ev} {vs : List V} {kret : List E → Prop} (hf : coreProgram.find? f = some fn)
    (hh : Stmt.HoldsListB S C rd σ fn.body False kret) (hw : walk σ fn.body = .ret es vs) :
    ∀ e ∈ es, e.HoldsB S rd σ := by
  have := walkB_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hh
  rw [hw] at this
  exact fun e he => (this.1 e he).1

/-- **One iteration of `opening_queries`' loop, placed at `fp`**: its tail at `fp + fs L` (or
skipped at the last), its frame run's first `4·pd` cells its own, every other load in `R`. -/
theorem oqLoop_iterC {CM : CompModel} {Ht : Bytes → Digest} (fs : String → ℕ) (cert : String → V → ℕ) {base I blocks pd cd : ℕ}
    (hs : OqShape base I blocks pd cd) {loop : String} {lf : Fn} (hfind : coreProgram.find? loop = some lf)
    (hp : lf.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7])
    (hb : lf.body = oqLoopBody base I blocks pd cd loop) (hpl : OqPlace base I blocks pd cd loop)
    (hlp : coreProgram.loop loop = true) {rd : Reader} {R : ℕ → Prop}
    {x N rew qsc qw qbp flags cap : E} {leaf : List K} (hleaf : leaf.length = oqR base I) {q : ℕ}
    (hq : q < 2 ^ (pd + cd)) {sibs : List Digest} (hsl : sibs.length = pd) (fp : ℕ) {m : ℕ}
    (hw : ∀ jw < I, LoadHolds rd rew jw (memAt rd rew jw))
    (hs0 : LoadHolds rd (qsc * x) 0 (memAt rd (qsc * x) 0))
    (hw0 : LoadHolds rd (qw * x) 0 (memAt rd (qw * x) 0))
    (hs1 : LoadHolds rd (qsc * x) 1 (memAt rd (qsc * x) 0 + memAt rd (qw * x) 0 *
      ∑ jw ∈ Finset.range I, leafRowWord base leaf jw * memAt rd rew jw))
    (hdbp : LoadHolds rd (qbp * x) 0 (memAt rd (qbp * x) 0))
    (hbits : ∀ l < pd + cd, LoadHolds rd (memAt rd (qbp * x) 0) l (bitE (q.testBit l)))
    (hcell : ∀ j < 4 * pd, LoadHolds rd (ofK (Parameters.gpow (fp + cert loop (.n (oqP base I blocks))))) j
      ((climbCellsW Ht (hashWordsW Ht leaf) q sibs).getD j 0))
    (hflag : LoadHolds rd flags (2 ^ (cd - 1) + q / 2 ^ (pd + 1)) 1)
    (hcap : CapCell rd cap (2 ^ cd + q / 2 ^ pd) (climb (m := Id) Ht (hashWordsW Ht leaf) q sibs))
    (hleafA : CM.H (leaf.flatMap kBytes) = some (hashWordsW Ht leaf))
    (hpathA : ∀ l < pd, CM.H (climbLvlBytes Ht (hashWordsW Ht leaf) q sibs l) =
      some (climbAtW Ht (hashWordsW Ht leaf) q sibs (l + 1)))
    (hK : IsInK (x * gen + N))
    (htail : if x * gen + N ≠ 0 then RelAtInB CM.sem coreProgram fs cert rd R (fun _ => False) (fp + fs loop) m loop
      [x * gen, N, rew, qsc, qw, qbp, flags, cap] [] else m = fs loop)
    (hRw : ∀ jw < I, OqIn R (rew.limb 0 * Parameters.gpow jw))
    (hRs : OqIn R ((qsc * x).limb 0 * Parameters.gpow 0) ∧ OqIn R ((qsc * x).limb 0 * Parameters.gpow 1))
    (hRq : OqIn R ((qw * x).limb 0 * Parameters.gpow 0)) (hRb : OqIn R ((qbp * x).limb 0 * Parameters.gpow 0))
    (hRd : ∀ l < pd + cd, OqIn R ((memAt rd (qbp * x) 0).limb 0 * Parameters.gpow l))
    (hRf : OqIn R ((flags * gen ^ (2 ^ (cd - 1) + q / 2 ^ (pd + 1))).limb 0 * Parameters.gpow 0))
    (hRc : OqIn R ((cap * gen ^ (2 * (2 ^ cd + q / 2 ^ pd))).limb 0 * Parameters.gpow 0) ∧
      OqIn R ((cap * gen ^ (2 * (2 ^ cd + q / 2 ^ pd) + 1)).limb 0 * Parameters.gpow 0)) :
    RelAtInB CM.sem coreProgram fs cert rd R (fun _ => False) fp (fs loop + m) loop [x, N, rew, qsc, qw, qbp, flags, cap] [] := by
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
  have hholds : Stmt.HoldsListB CM.sem (coreProgram.RelB CM.sem rd) rd σ lf.body False (fun rs => rs = []) := by
    rw [hb, hσ]
    refine oqIter_holdsC hs hleaf hq hsl hw hs0 hw0 hs1 hdbp hbits hptrK hcell hflag hcap hK (fun hne => ?_)
      hleafA hpathA
    rw [ite_pos' hne] at htail
    exact htail.relAt.rel
  have hbody : lf.body = oqLoopPre base I blocks pd cd loop ++ [.ret []] := hb.trans (oqLoopBody_split _ _ _ _ _ _)
  set es := (oqLoopPre base I blocks pd cd loop).flatMap (Main.slEvs σ)
  have hw' : walk σ lf.body = .ret es [] := by rw [hbody]; exact Main.walk_straight σ [] _ hpl.straight
  have hev := oq_holds_eventsB hfind hholds hw'
  obtain ⟨had, hal, hadr, hcl⟩ := Main.straight_parts σ _ hpl.straight
  have hal0 : allocs σ es = [] := by rw [hal, hpl.allocs]; rfl
  have hcalls : calls es = [] ++ [⟨loop, [.n (oqK7 base I blocks pd cd + 19), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7],
      [], decide (σ (.n (oqK7 base I blocks pd cd + 17)) ≠ 0)⟩] := by
    rw [hcl, hpl.calls]; rfl
  have hrun : (.n P, 80) ∈ runs es := by rw [oq_runs_straight σ _ hpl.straight, hpl.runs]; simp [P]
  have hown : ∀ t < 80, ownData cert fp (fp + fs loop + m) loop (allocs σ es) es (c0 + t) := fun t ht =>
    Or.inr ⟨_, hrun, Nat.le_add_right c0 t, Nat.add_lt_add_left ht c0⟩
  have h := relAtInB_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd) coreProgram_wf
    (R := R) (D := fun _ => False) (Dk := fun _ => False) (Rt := R) (Dt := fun _ => False) (fp := fp) (m := m)
    (N := 0) hfind hlp (hp ▸ hargs) hw' rfl hev hcalls ?_
    (by rw [had, hpl.allocs, hal0]; rfl)
    (fun q hq' => by
      rw [hadr, hpl.addrs] at hq'
      simp only [List.mem_singleton] at hq'
      subst hq'
      exact pptr)
    (by rw [hal0]; exact ⟨rfl, fun i h => h.elim⟩)
    (fun i hi => Or.inl hi)
    (fun A hA => ?_)
    (fun _ h => h.elim)
  · rw [hal0, List.sum_nil, Nat.add_zero, Nat.add_zero, List.map_nil] at h; exact h
  · by_cases ht : x * gen + N ≠ 0
    · rw [ite_pos' ht] at htail
      simp only [p17]
      rw [ite_pos' (decide_eq_true ht), List.map_nil]
      have : ([.n (oqK7 base I blocks pd cd + 19), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7] : List V).map σ =
          [x * gen, N, rew, qsc, qw, qbp, flags, cap] := by
        simp only [List.map_cons, List.map_nil, p19, parg 1 (by omega), parg 2 (by omega), parg 3 (by omega),
          parg 4 (by omega), parg 5 (by omega), parg 6 (by omega), parg 7 (by omega)]
        rfl
      rw [this]; exact htail
    · rw [ite_neg' ht] at htail
      simp only [p17]
      rw [ite_neg' (by simpa using ht)]
      exact htail
  · rw [loadAddrs_straight σ _ hpl.straight] at hA
    obtain ⟨⟨p, off⟩, hq', rfl⟩ := List.mem_map.mp hA
    have hb' := List.all_eq_true.mp hpl.loads _ hq'
    simp only [oqLoadB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Prod.mk.injEq,
      List.any_eq_true, List.mem_range, or_assoc, oqK7] at hb'
    have inR : ∀ A, OqIn R A → ∃ i, A = Parameters.gpow i ∧
        (ownData cert fp (fp + fs loop + m) loop (allocs σ es) es i ∨ R i ∨ False ∨
          ((⟨loop, [.n (oqK7 base I blocks pd cd + 19), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7], [],
            decide (σ (.n (oqK7 base I blocks pd cd + 17)) ≠ 0)⟩ : Call).taken = true ∧ False)) :=
      fun A ⟨i, hi, hR⟩ => ⟨i, hi, Or.inr (Or.inl hR)⟩
    have inOwn : ∀ t < 80, ∃ i, Parameters.gpow (c0 + t) = Parameters.gpow i ∧
        (ownData cert fp (fp + fs loop + m) loop (allocs σ es) es i ∨ R i ∨ False ∨
          ((⟨loop, [.n (oqK7 base I blocks pd cd + 19), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7], [],
            decide (σ (.n (oqK7 base I blocks pd cd + 17)) ≠ 0)⟩ : Call).taken = true ∧ False)) :=
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

/-! ## The loop -/

/-- What one query asks of the model: its leaf's bytes and its path's levels answered by `Ht`
(`oqIter_holdsC`'s `hleafA`, `hpathA`). -/
def OqAns (CM : CompModel) (Ht : Bytes → Digest) (pd : ℕ) (leaf : List K) (q : ℕ) (sibs : List Digest) :
    Prop :=
  CM.H (leaf.flatMap kBytes) = some (hashWordsW Ht leaf) ∧
    ∀ l < pd, CM.H (climbLvlBytes Ht (hashWordsW Ht leaf) q sibs l) =
      some (climbAtW Ht (hashWordsW Ht leaf) q sibs (l + 1))

/-- What one iteration at `x` reads from the caller's words, over `Ht` (`OqIterMem`). -/
def OqIterMemW (Ht : Bytes → Digest) (rd : Reader) (base I pd cd : ℕ) (rew qsc qw qbp flags cap x : E)
    (leaf : List K) (q : ℕ) (sibs : List Digest) : Prop :=
  (∀ jw < I, LoadHolds rd rew jw (memAt rd rew jw)) ∧
    LoadHolds rd (qsc * x) 0 (memAt rd (qsc * x) 0) ∧ LoadHolds rd (qw * x) 0 (memAt rd (qw * x) 0) ∧
    LoadHolds rd (qsc * x) 1 (memAt rd (qsc * x) 0 + memAt rd (qw * x) 0 *
      ∑ jw ∈ Finset.range I, leafRowWord base leaf jw * memAt rd rew jw) ∧
    LoadHolds rd (qbp * x) 0 (memAt rd (qbp * x) 0) ∧
    (∀ l < pd + cd, LoadHolds rd (memAt rd (qbp * x) 0) l (bitE (q.testBit l))) ∧
    LoadHolds rd flags (2 ^ (cd - 1) + q / 2 ^ (pd + 1)) 1 ∧
    CapCell rd cap (2 ^ cd + q / 2 ^ pd) (climb (m := Id) Ht (hashWordsW Ht leaf) q sibs)

theorem oqIterMemW_blake {rd : Reader} {base I pd cd : ℕ} {rew qsc qw qbp flags cap x : E} {leaf : List K}
    {q : ℕ} {sibs : List Digest} :
    OqIterMemW blake2sBytes rd base I pd cd rew qsc qw qbp flags cap x leaf q sibs ↔
      OqIterMem rd base I pd cd rew qsc qw qbp flags cap x leaf q sibs := Iff.rfl

theorem oqAns_deployed {pd : ℕ} (leaf : List K) (q : ℕ) {sibs : List Digest} (hsl : sibs.length = pd) :
    OqAns CompModel.deployed blake2sBytes pd leaf q sibs :=
  ⟨rfl, fun l hl => (climb_answered (H := CompModel.deployed.H) (Ht := blake2sBytes)
    (fun x d h => (Option.some.inj h).symm) (climb_some_blake _ q sibs)).2 l (by omega)⟩

/-- The loop's frame runs from iteration `j0` over `Ht` (`oqLoopRuns`). -/
def oqLoopRunsW (Ht : Bytes → Digest) (fs : String → ℕ) (cert : String → V → ℕ) (loop : String) (P : ℕ)
    (fp j0 n : ℕ) (leaf : ℕ → List K) (pos : ℕ → ℕ) (sibs : ℕ → List Digest) : Main.Layout :=
  (List.range (n - j0)).map fun i => (fp + i * fs loop + cert loop (.n P),
    climbCellsW Ht (hashWordsW Ht (leaf (j0 + i))) (pos (j0 + i)) (sibs (j0 + i)))

theorem oqLoopRunsW_blake : oqLoopRunsW blake2sBytes = oqLoopRuns := rfl

/-- **`opening_queries`' loop from iteration `j0`, placed at `fp`, over a completeness model**
(`oqLoop_completeAt`'s chain of iterations): on a memory holding each iteration's words and frame
run, each query answered by the model, the loop helper's relation under `CM.sem` holds by a tree of
`n - j0 + 1` frames. -/
theorem oqLoop_relAtInC {CM : CompModel} {Ht : Bytes → Digest} (fs : String → ℕ) (cert : String → V → ℕ)
    {base I blocks pd cd : ℕ} (hs : OqShape base I blocks pd cd) {loop : String} {lf : Fn}
    (hfind : coreProgram.find? loop = some lf) (hp : lf.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7])
    (hb : lf.body = oqLoopBody base I blocks pd cd loop) (hpl : OqPlace base I blocks pd cd loop)
    (hlp : coreProgram.loop loop = true) {n : ℕ} (hn : n < ordG) {rd : Reader} {R : ℕ → Prop}
    {rew qsc qw qbp flags cap : E} {leaf : ℕ → List K} (hleaf : ∀ j < n, (leaf j).length = oqR base I)
    {pos : ℕ → ℕ} (hq : ∀ j < n, pos j < 2 ^ (pd + cd)) {sibs : ℕ → List Digest}
    (hsl : ∀ j < n, (sibs j).length = pd) {fp j0 : ℕ} (hj0 : j0 < n)
    (hd : ∀ j < n, OqIterMemW Ht rd base I pd cd rew qsc qw qbp flags cap (gen ^ j) (leaf j) (pos j) (sibs j) ∧
      OqIterReg R rd I pd cd rew qsc qw qbp flags cap (gen ^ j) (pos j) ∧ OqAns CM Ht pd (leaf j) (pos j) (sibs j))
    (hcell : ∀ j, j0 ≤ j → j < n → ∀ t < 4 * pd,
      LoadHolds rd (ofK (Parameters.gpow (fp + (j - j0) * (fs loop) + cert loop (.n (oqP base I blocks))))) t
        ((climbCellsW Ht (hashWordsW Ht (leaf j)) (pos j) (sibs j)).getD t 0)) :
    RelAtInB CM.sem coreProgram fs cert rd R (fun _ => False) fp ((n - j0 + 1) * fs loop) loop
      [gen ^ j0, gen ^ n, rew, qsc, qw, qbp, flags, cap] [] := by
  have hn' : n < 2 ^ 64 - 1 := hn
  have hstep : ∀ t j, j + t + 1 = n → j0 ≤ j →
      RelAtInB CM.sem coreProgram fs cert rd R (fun _ => False) (fp + (j - j0) * (fs loop))
        ((n - j + 1) * (fs loop)) loop [gen ^ j, gen ^ n, rew, qsc, qw, qbp, flags, cap] [] := by
    intro t
    induction t with
    | zero =>
      intro j hj hlo
      obtain ⟨⟨m1, m2, m3, m4, m5, m6, m7, m8⟩, ⟨r1, r2, r3, r4, r5, r6, r7⟩, a1, a2⟩ := hd j (by omega)
      have h0 : gen ^ j * gen + gen ^ n = 0 := by rw [gen_pow_add_eq_zero_iff]; congr 1; omega
      have := oqLoop_iterC (CM := CM) (Ht := Ht) fs cert hs hfind hp hb hpl hlp (rd := rd) (R := R) (N := gen ^ n)
        (hleaf j (by omega)) (hq j (by omega)) (hsl j (by omega)) (fp + (j - j0) * (fs loop)) (m := (fs loop))
        m1 m2 m3 m4 m5 m6 (hcell j hlo (by omega)) m7 m8 a1 a2
        (by rw [h0]; exact ((isInK_iff _).mpr ⟨0, ofK_zero.symm⟩)) (by rw [ite_neg' (by simp [h0])])
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
      have := oqLoop_iterC (CM := CM) (Ht := Ht) fs cert hs hfind hp hb hpl hlp (rd := rd) (R := R) (N := gen ^ n)
        (hleaf j (by omega)) (hq j (by omega)) (hsl j (by omega)) (fp + (j - j0) * (fs loop))
        (m := (n - (j + 1) + 1) * (fs loop)) m1 m2 m3 m4 m5 m6 (hcell j hlo (by omega)) m7 m8 a1 a2
        (isInK_add (by rw [gen_pow_mul_gen]; exact gen_pow_isInK _) (gen_pow_isInK _))
        (by rw [ite_pos' hne, gen_pow_mul_gen]; exact ht) r1 r2 r3 r4 r5 r6 r7
      rwa [show (n - j + 1) * (fs loop) = (fs loop) + (n - (j + 1) + 1) * (fs loop) by
        rw [show n - j + 1 = (n - (j + 1) + 1) + 1 by omega, Nat.add_mul, Nat.one_mul, Nat.add_comm]]
  have := hstep (n - j0 - 1) j0 (by omega) le_rfl
  rwa [Nat.sub_self, Nat.zero_mul, Nat.add_zero] at this

end
end LeanVM.Guest.B1
