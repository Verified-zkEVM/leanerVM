/-
  LeanVM.Guest.B1.Terminal.TermSigma

  `check_opening_terminal`'s honest valuation: on a memory holding the caller's words (its
  precondition `TermPre`), its buffers and its callees' results, every statement holds, every
  load lies in those words, and the frames match its callees; its last check is the WHIR terminal.
-/

module

public import LeanVM.Guest.B1.Terminal.TermEval
public import LeanVM.Protocol.EndToEnd.Complete.BusStack

/-!
# The terminal's honest valuation

`termD`: the honest data of `TermPre`'s parameters. `term_sigma`: the evaluated valuation
(`termW`'s oracle) satisfies what `completeAt_flatDepR` asks: the parameters, the dispatches, the
body (its claims' blocks by `claimsT_complete`, its head, selectors and tail by `TermEval`), the
buffers, the frames (`callsMatch_kidsAt`) and the loads. Its last check: the sum the blocks build is
the opening's weight, as in the soundness proof (`claimsT_sound`, `claimTerm_eq`, `stackWeight_eq`),
so the honest terminal equation passes it.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol
open LeanVM.Protocol.Verifier hiding gpow
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Main (MemL RegionL)
open Finset

@[expose] public section

/-! ## Facts -/

theorem dvd_stackOffset (sizes : List ℕ) {b : ℕ} (hb : b < sizes.length) :
    2 ^ sizes.getD b 0 ∣ (stackOffsets sizes).1.getD b 0 := by
  obtain ⟨k, hk, e⟩ := List.getElem_of_mem (EndToEnd.Complete.mem_stackOrder.mpr hb)
  have := EndToEnd.Complete.dvd_blockOffset sizes k hk
  rw [e] at this
  exact this

theorem kc_getD {kappas : List ℕ} (hk : kappas.length = 163) {cc : ℕ} (hcc : cc < 99) :
    (Tables.committedKappas kappas).getD cc 0 = kappas.getD ((Tables.committedCols 163).getD cc 0) 0 := by
  have hlen : cc < (Tables.committedCols 163).length := by
    rw [Tables.committedCols_163_length]; exact hcc
  rw [Tables.committedKappas, hk, List.getD_eq_getElem _ _ (by simpa using hlen), List.getElem_map,
    ← List.getD_eq_getElem _ 0 hlen]

theorem claimCol_committed_all : ∀ j < 165, (termKind j = 0 ∨ termKind j = 1 ∨ termKind j = 3) →
    claimColOf j = colOfCommitted (termCol j) := by decide +kernel

theorem claimCol_committed {j : ℕ} (hj : j < 165) (hk : termKind j = 0 ∨ termKind j = 1 ∨ termKind j = 3) :
    claimColOf j = (Tables.committedCols 163).getD (termCol j) 0 := by
  rw [committedCols_getD (termCol_lt hj)]
  exact claimCol_committed_all j hj hk

theorem dispOk_of_noDisp {σ : Val} {s : Stmt} (h : noDispB s = true) : DispOk σ s := by
  cases s <;> simp_all [DispOk, noDispB]

def isAtomB : Stmt → Bool
  | .atom _ => true
  | _ => false

theorem claims_atoms : termClaims.all isAtomB = true := by decide +kernel

theorem sels_noDisp : ∀ c, (selBlockT c).filterMap Main.Stmt.callS = [] := fun _ => rfl

theorem getD_seg {α : Type} (A M Z : List α) (d : α) (hA : A.length = 4) (hM : M.length = 99)
    (j : ℕ) : (A ++ M ++ Z).getD j d =
      if j < 4 then A.getD j d else if j < 103 then M.getD (j - 4) d else Z.getD (j - 103) d := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.append_assoc, List.getElem?_append_left (by omega)]
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by omega), hA]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp [hA, hM]

theorem getD_map_lt {α β : Type} (f : α → β) {l : List α} {j : ℕ} (d : α) (d' : β)
    (h : j < l.length) : (l.map f).getD j d' = f (l.getD j d) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map, List.getD_eq_getElem _ _ h]

/-- The honest data of `TermPre`'s parameters. -/
def termD (B : TermBases) (layout : Layout) (bus : BusResult) (out : ColumnClaim)
    (ringPoint coeffs x chis : List E) (rm gmu gzcn glm gtau : E) : TermData where
  B := B
  rm := rm
  gmu := gmu
  gzcn := gzcn
  glm := glm
  gtau := gtau
  zs := bus.point
  chis := chis
  outPt := out.point
  ringPoint := ringPoint
  coeffs := coeffs
  x := x
  KC := Tables.committedKappas (columnKappas layout.logMemory layout.logBytecode layout.tableLogHeights)
  OF := (stackOffsets (Tables.committedKappas
    (columnKappas layout.logMemory layout.logBytecode layout.tableLogHeights))).1
  m := layout.logMemory
  τ := layout.tableLogHeights.getD opKeccak 0

theorem termKids_getD_sel (Lin : Main.Layout) (D : TermData) (b0 : ℕ) {c : ℕ} (hc : c < 99) :
    (termKids Lin D b0).getD (4 + c) noKid = selKid D c := by
  rw [termKids, getD_seg _ _ _ _ rfl (by simp [Tables.nCommittedCols]), ite_neg' (by omega),
    ite_pos' (by omega), show 4 + c - 4 = c by omega, List.getD_eq_getElem _ _ (by simp [Tables.nCommittedCols]; omega),
    List.getElem_map, List.getElem_range]

theorem termKids_getD_103 (Lin : Main.Layout) (D : TermData) (b0 : ℕ) :
    (termKids Lin D b0).getD 103 noKid = fun _ => ⟨"eq_prefix_chain", true,
      [ofK (gpow (b0 + 105)), word 1 0 0, ofK (gpow D.B.zv), ofK (gpow D.B.pt1), D.gtau * word 64 0 0],
      (b0 + 105, eqChain D.outPt ((p1Of D.x).take D.outPt.length)) :: Lin, Returns []⟩ := by
  rw [termKids, getD_seg _ _ _ _ rfl (by simp [Tables.nCommittedCols]), ite_neg' (by omega),
    ite_neg' (by omega)]
  rfl

theorem termKids_getD_104 (Lin : Main.Layout) (D : TermData) (b0 : ℕ) :
    (termKids Lin D b0).getD 104 noKid = fun _ => ⟨"ring_switch_weight", true,
      [ofK (gpow D.B.zv) * word 549755813888 0 0, ofK (gpow D.B.pt1), ofK (gpow D.B.ct),
        D.gtau * word 64 0 0],
      [(D.B.zv + 39, D.ringPoint), (D.B.pt1, (p1Of D.x).take (D.τ + 6)), (D.B.ct, D.coeffs)],
      Returns [ringWeight D.ringPoint (((p1Of D.x).take (D.τ + 6)).map (1 + ·)) D.coeffs]⟩ := by
  rw [termKids, getD_seg _ _ _ _ rfl (by simp [Tables.nCommittedCols]), ite_neg' (by omega),
    ite_neg' (by omega)]
  rfl

/-! ## The honest valuation -/

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
/-- **`check_opening_terminal`'s honest valuation**, on a memory holding the caller's words, the
buffers and the callees' results: what `completeAt_flatDepR` asks of it. -/
theorem term_sigma (B : TermBases) (Lin : Main.Layout) {layout : Layout} {bus : BusResult}
    {claims : List ColumnClaim} {out : ColumnClaim} {lam : E} {ringPoint coeffs x chis : List E}
    {rm gmu gzcn glm gtau lamOut inner yr target : E} (b0 : ℕ)
    (outs : List (List E × Main.Layout)) (rd : Reader)
    (P : TermPre rd layout bus claims out lam ringPoint coeffs x
      (termArgs B rm gmu gzcn glm gtau lamOut inner yr target))
    (hchis : ReadsAt rd (ofK (gpow B.chi)) chis) (hgz : gzcn = gen ^ chis.length)
    (hcl : chis.length ≤ 34)
    (hreg : ∀ i, TermRegion B bus.point.length chis.length (layout.tableLogHeights.getD opKeccak 0) i →
      RegionL Lin i)
    (hbus : bus.point.length ≤ 34)
    (hlen : ∀ c ∈ claims, c.point.length =
      (columnKappas layout.logMemory layout.logBytecode layout.tableLogHeights).getD c.column 0)
    (hfin : (inner + stackWeight layout (openedClaims claims [out]) ringPoint coeffs lam x) * yr =
      target)
    (hol : outs.length = 105)
    (ho : OutsOk (kidsAt (termKids Lin (termD B layout bus out ringPoint coeffs x chis rm gmu gzcn glm
      gtau) b0) [] outs) outs)
    (hB : MemL rd (bufL b0 [35, 35, 35, 41]
      (termOwn (termD B layout bus out ringPoint coeffs x chis rm gmu gzcn glm gtau)))) :
    ∃ σ : Val, Data.core17.params.map σ = termArgs B rm gmu gzcn glm gtau lamOut inner yr target ∧
      (∀ s ∈ termPre, DispOk σ s) ∧
      Stmt.HoldsList (fun _ _ _ => True) rd σ Data.core17.body False (fun r => r = []) ∧
      (termPre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) =
        [35, 35, 35, 41] ∧
      ((termPre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
        (bases b0 [35, 35, 35, 41]).map (fun b => ofK (gpow b)) ∧
      CallsMatch σ ((termPre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ))
        (kidsAt (termKids Lin (termD B layout bus out ringPoint coeffs x chis rm gmu gzcn glm gtau) b0)
          [] outs) outs ∧
      ∀ q ∈ termPre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * gpow q.2 = gpow i ∧
        (RegionL Lin i ∨ RegionL (bufL b0 [35, 35, 35, 41]
          (termOwn (termD B layout bus out ringPoint coeffs x chis rm gmu gzcn glm gtau))) i ∨
          outRegion (kidsAt (termKids Lin (termD B layout bus out ringPoint coeffs x chis rm gmu gzcn
            glm gtau) b0) [] outs) outs i) := by
  set D := termD B layout bus out ringPoint coeffs x chis rm gmu gzcn glm gtau with hD
  set args := termArgs B rm gmu gzcn glm gtau lamOut inner yr target with hargs
  -- the precondition
  simp only [TermPre, hargs, termArgs] at P
  obtain ⟨hT, hPC, -, hP, hSL, hSL28, hlm1, hlm32, hbus40, hHL, -, hglm, hgtau, hlamP, hlamO, hoc,
    hopl, hoz, hrpl, hrp, hcfl, hct, hxl, hpt, hpt1⟩ := P
  obtain ⟨chis', hzR, hgmu, hchR, hgzc, hchL, -, hcols, hpts⟩ := hT
  obtain ⟨hkap, hKr, hOr⟩ := hPC
  have hcc : chis' = chis := by
    have hl : chis'.length = chis.length :=
      gen_pow_inj_le (by omega) (by omega) (hgzc.symm.trans hgz)
    exact readsAt_unique hchR hchis hl
  subst hcc
  set kappas := columnKappas layout.logMemory layout.logBytecode layout.tableLogHeights with hkdef
  set KC := Tables.committedKappas kappas with hKCdef
  set τ := layout.tableLogHeights.getD opKeccak 0 with hτ
  set m := layout.logMemory with hmdef
  have hKClen : KC.length = Tables.nCommittedCols := Tables.committedKappas_length _ hkap
  have hLdef : layout.stackLog = max minStackedLog (stackOffsets KC).2 := by
    rw [hSL, placementsOf_snd]
  have hK : ∀ c < Tables.nCommittedCols, KC.getD c 0 ≤ layout.stackLog := fun c hc ↦ by
    have := size_le_stackOffsets KC (i := c) (by omega); rw [hLdef]; omega
  have hO : ∀ c, (stackOffsets KC).1.getD c 0 < 2 ^ layout.stackLog := fun c ↦
    lt_of_lt_of_le (stackOffsets_lt KC c) (Nat.pow_le_pow_right (by decide) (by rw [hLdef]; omega))
  have hdvd : ∀ c < Tables.nCommittedCols, 2 ^ KC.getD c 0 ∣ (stackOffsets KC).1.getD c 0 :=
    fun c hc ↦ dvd_stackOffset KC (by omega)
  have hkv' : ∀ c < Tables.nCommittedCols, LoadHolds rd (ofK (gpow B.kap)) c (gen ^ KC.getD c 0) :=
    fun c hc ↦ by
      have := hKr c (by simp; omega)
      rw [List.getElem_map] at this
      rw [List.getD_eq_getElem _ _ (by omega)]; exact this
  have hoff' : ∀ c < Tables.nCommittedCols,
      LoadHolds rd (ofK (gpow B.off)) c (gen ^ (stackOffsets KC).1.getD c 0) := fun c hc ↦ by
    have hl : c < (stackOffsets KC).1.length := by rw [stackOffsets_length]; omega
    have := hOr c (by simpa using hl)
    rw [List.getElem_map] at this
    rw [List.getD_eq_getElem _ _ hl]; exact this
  have hk6 : kappas.take 6 = [layout.logMemory, layout.logMemory, layout.logMemory,
      layout.logMemory, layout.logBytecode, τ + 6] := kappas_small hHL
  have hksmall : ∀ c < 6, kappas.getD c 0 =
      [layout.logMemory, layout.logMemory, layout.logMemory, layout.logMemory, layout.logBytecode,
        τ + 6].getD c 0 := fun c hc ↦ by
    rw [← hk6, getD_take_nat hc]
  have hK5 : KC.getD 5 0 = τ + 6 := by
    rw [committedKappas_small hkap (by decide), hksmall 5 (by decide)]; rfl
  have hmem : ∀ c < 3, KC.getD c 0 = layout.logMemory := fun c hc ↦ by
    rw [committedKappas_small hkap (by omega), hksmall c (by omega)]
    interval_cases c <;> rfl
  have hK5L := hK 5 (by decide)
  rw [hK5] at hK5L
  have hxl40 : x.length ≤ termPointCap := by simp only [termPointCap]; omega
  have hpl40 : (p1Of x).length = 40 := p1Of_length hxl40
  have hpt40 : (padPoint x).length = 40 := padPoint_length hxl40
  have hclen : claims.length = 165 := by
    rw [← List.length_map (f := (·.column)), hcols, claimColumns_eq]; simp
  have hptj : ∀ j < 165, (claims.map (·.point))[j]? = some (claims.getD j default).point :=
    fun j hj ↦ by
      rw [List.getElem?_map, List.getElem?_eq_getElem (by omega), List.getD_eq_getElem _ _ (by omega)]
      rfl
  let cp : ℕ → ℕ := fun j ↦ (claims.getD j default).point.length
  have hcpR : ∀ j < 162, LoadHolds rd (ofK (gpow B.cplen)) j (gen ^ cp j) := fun j hj ↦
    (hpts j _ (hptj j (by omega))).1 hj
  have hmemj : ∀ j < 165, claims.getD j default ∈ claims := fun j hj ↦ by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have hcpK : ∀ j < 165, (termKind j = 0 ∨ termKind j = 1 ∨ termKind j = 3) →
      cp j = KC.getD (termCol j) 0 := fun j hj hk ↦ by
    show (claims.getD j default).point.length = _
    rw [hlen _ (hmemj j hj), claim_column hcols hj, claimCol_committed hj hk,
      kc_getD hkap (termCol_lt hj)]
  have hcpτ : ∀ j < 165, termKind j = 2 → cp j = τ := fun j hj hk ↦ by
    show (claims.getD j default).point.length = _
    have h2 : (72 ≤ j ∧ j < 110) ∨ j = 135 := by unfold termKind at hk; split_ifs at hk <;> omega
    rw [hlen _ (hmemj j hj), claim_column hcols hj,
      show claimColOf j = j + 1 by unfold claimColOf; split_ifs <;> omega]
    exact kappas_keccak hHL (by omega) (by omega)
  have hpz' : ∀ j < 5, cp j ≤ bus.point.length := fun j hj ↦ by
    have := congrArg List.length ((hpts j _ (hptj j (by omega))).2.1 hj)
    rw [List.length_take] at this
    show (claims.getD j default).point.length ≤ _; omega
  have hpc' : ∀ j, 5 ≤ j → j < 162 → cp j ≤ chis'.length := fun j h1 h2 ↦ by
    have := congrArg List.length ((hpts j _ (hptj j (by omega))).2.2.1 h1 h2)
    rw [List.length_take] at this
    show (claims.getD j default).point.length ≤ _; omega
  -- the valuation
  obtain ⟨σ, hσdef⟩ : ∃ σ, σ = B1.Val.ofArgs (ev rd (termW b0 outs) args termT) := ⟨_, rfl⟩
  have hchk : chk args.length termT = some 2009 := term_chk
  have hgs : ∀ s ∈ termT, GoodS rd [.load (.n 26) (.n 25) 0, .load (.n 28) (.n 25) 1]
      (termW b0 outs) σ s := by
    have h := (ev_spec rd (termW b0 outs) termT args hchk).2.2
    rw [show args.length = 19 from rfl, term_stores, ← hσdef] at h
    exact h
  have ea : ∀ i, i < 19 → σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσdef]; exact ev_params rd _ hchk (by simpa [hargs, termArgs] using hi)
  have e2 : σ (.n 2) = rm := ea 2 (by omega)
  have e5 : σ (.n 5) = glm := ea 5 (by omega)
  have e6 : σ (.n 6) = gtau := ea 6 (by omega)
  have e7 : σ (.n 7) = ofK (gpow B.cplen) := ea 7 (by omega)
  have e9 : σ (.n 9) = ofK (gpow B.lamPool) := ea 9 (by omega)
  have e10 : σ (.n 10) = ofK (gpow B.off) := ea 10 (by omega)
  have e11 : σ (.n 11) = ofK (gpow B.kap) := ea 11 (by omega)
  have e14 : σ (.n 14) = ofK (gpow B.pt) := ea 14 (by omega)
  have e15 : σ (.n 15) = ofK (gpow B.pt1) := ea 15 (by omega)
  have hS : StoresAt25 [Atom.load (.n 26) (.n 25) 0, .load (.n 28) (.n 25) 1] := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> exact ⟨_, _, rfl⟩
  have gPre : ∀ s ∈ termPre, GoodS rd [.load (.n 26) (.n 25) 0, .load (.n 28) (.n 25) 1]
      (termW b0 outs) σ s := fun s hs => hgs s (by rw [termT_split]; exact List.mem_append_left _ hs)
  have gH : ∀ s ∈ termHeadT, GoodS rd [.load (.n 26) (.n 25) 0, .load (.n 28) (.n 25) 1]
      (termW b0 outs) σ s := fun s hs => gPre s (by
    unfold termPre
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hs)))
  have gS : ∀ s ∈ selsT, GoodS rd [.load (.n 26) (.n 25) 0, .load (.n 28) (.n 25) 1]
      (termW b0 outs) σ s := fun s hs => gPre s (by
    unfold termPre
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hs)))
  have gC : ∀ s ∈ termClaims, GoodS rd [.load (.n 26) (.n 25) 0, .load (.n 28) (.n 25) 1]
      (termW b0 outs) σ s := fun s hs => gPre s (by
    unfold termPre
    exact List.mem_append_left _ (List.mem_append_right _ hs))
  have gT : ∀ s ∈ termTailPre, GoodS rd [.load (.n 26) (.n 25) 0, .load (.n 28) (.n 25) 1]
      (termW b0 outs) σ s := fun s hs => gPre s (by
    unfold termPre
    exact List.mem_append_right _ hs)
  have hw64 : word 64 0 0 = gen ^ 6 := word_two_pow (a := 6) (by decide)
  have e6' : σ (.n 6) = gen ^ τ := by rw [e6, hgtau]
  have hoL : out.point.length = τ + 6 := by rw [hopl, Tables.qkeccakSlotBits_eq]
  -- the regions
  set R : ℕ → Prop := fun i => RegionL Lin i ∨
    RegionL (bufL b0 [35, 35, 35, 41] (termOwn D)) i ∨
    outRegion (kidsAt (termKids Lin D b0) [] outs) outs i with hR
  have aL : ∀ b k, TermRegion B bus.point.length chis'.length τ (b + k) →
      AddrIn R (ofK (gpow b)) k := fun b k h => ⟨b + k, Main.addr_ofK b k, Or.inl (hreg _ h)⟩
  have hBuf := hB
  rw [termBuf_eq] at hBuf
  have rB : ∀ i, RegionL [(b0, eqChain D.zs ((p1Of D.x).take D.zs.length)),
      (b0 + 35, eqChain D.chis ((p1Of D.x).take D.chis.length)),
      (b0 + 70, piW D.rm (p1Of D.x) D.m),
      (b0 + 105, eqChain D.outPt ((p1Of D.x).take D.outPt.length))] i → R i := fun i h =>
    Or.inr (Or.inl (by rw [termBuf_eq]; exact h))
  have m0 : (b0, eqChain bus.point ((p1Of x).take bus.point.length)) ∈
      [(b0, eqChain D.zs ((p1Of D.x).take D.zs.length)),
        (b0 + 35, eqChain D.chis ((p1Of D.x).take D.chis.length)),
        (b0 + 70, piW D.rm (p1Of D.x) D.m),
        (b0 + 105, eqChain D.outPt ((p1Of D.x).take D.outPt.length))] := List.mem_cons_self
  have m1 : (b0 + 35, eqChain chis' ((p1Of x).take chis'.length)) ∈
      [(b0, eqChain D.zs ((p1Of D.x).take D.zs.length)),
        (b0 + 35, eqChain D.chis ((p1Of D.x).take D.chis.length)),
        (b0 + 70, piW D.rm (p1Of D.x) D.m),
        (b0 + 105, eqChain D.outPt ((p1Of D.x).take D.outPt.length))] :=
    List.mem_cons_of_mem _ List.mem_cons_self
  have m2 : (b0 + 70, piW rm (p1Of x) m) ∈
      [(b0, eqChain D.zs ((p1Of D.x).take D.zs.length)),
        (b0 + 35, eqChain D.chis ((p1Of D.x).take D.chis.length)),
        (b0 + 70, piW D.rm (p1Of D.x) D.m),
        (b0 + 105, eqChain D.outPt ((p1Of D.x).take D.outPt.length))] :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have m3 : (b0 + 105, eqChain out.point ((p1Of x).take out.point.length)) ∈
      [(b0, eqChain D.zs ((p1Of D.x).take D.zs.length)),
        (b0 + 35, eqChain D.chis ((p1Of D.x).take D.chis.length)),
        (b0 + 70, piW D.rm (p1Of D.x) D.m),
        (b0 + 105, eqChain D.outPt ((p1Of D.x).take D.outPt.length))] :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  -- the head
  have h15 : LoadHolds rd (σ (.n 15)) 0 ((p1Of x).getD 0 0) := by
    rw [e15]; exact readsAt_getD hpt1 (by simp [padPoint_length hxl40])
  obtain ⟨hHs, hHl, e19, e20, e21, e22, e23, e24, e25, e30, e31, e33, e34, e35⟩ :=
    head_complete (R := R) hS gH (m := m) (rm := rm) (ps := p1Of x) hlm1 (by rw [e5, hglm]) e2 h15
      (by rw [e15]; exact aL _ _ (by simp only [TermRegion]; omega)) (hBuf _ m2)
      (fun k hk => rB _ ⟨_, m2, by omega, by rw [piW_length]; omega⟩)
  -- the selectors
  have hst3 : Tables.stOut B.pt B.pt1 (pt28 x) (pt128 x) (stRes outs).1 (stRes outs).2 := by
    have := outsOk_at ho 3 (by rw [termKids_length]; omega) (by omega) (by rw [termKid3])
    rw [termKid3] at this
    exact this
  have hKC29 : ∀ c < Tables.nCommittedCols, KC.getD c 0 < 29 := fun c hc => by
    have := hK c hc; omega
  have hsl : ∀ c, c < Tables.nCommittedCols →
      (∀ s ∈ selBlockT c, Fwd.SHolds TrivC rd σ s) ∧ (∀ s ∈ selBlockT c, DispOk σ s) ∧
      (∀ q ∈ (selBlockT c).filterMap Stmt.loadS, AddrIn R (σ q.1) q.2) ∧
      σ (.n (36 + 3 * c)) = gen ^ (stackOffsets KC).1.getD c 0 ∧
      σ (.n (37 + 3 * c)) = gen ^ KC.getD c 0 ∧
      σ (.n (selV c)) = (outs.getD (4 + c) ([], [])).1.getD 0 0 := fun c hc => by
    have hc' : c < 99 := hc
    exact sel_complete hS hc'
        (fun s hs => gS s (List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, hs⟩))
        (hKC29 c hc) (by rw [e10]; exact hoff' c hc)
        (by rw [e10]; exact aL _ _ (by simp only [TermRegion]; omega)) (by rw [e11]; exact hkv' c hc)
        (by rw [e11]; exact aL _ _ (by simp only [TermRegion]; omega))
  have hselv : ∀ c < Tables.nCommittedCols, σ (.n (selV c)) =
      selProd ((stackOffsets KC).1.getD c 0) (KC.getD c 0) (layout.stackLog - KC.getD c 0) x := by
    intro c hc
    have hc' : c < 99 := hc
    have ht : (kidAt (termKids Lin D b0) [] outs (4 + c)).taken = true := by
      unfold kidAt
      rw [List.nil_append, termKids_getD_sel Lin D b0 hc]
      refine @decide_eq_true _ (Classical.propDecidable _) ?_
      rw [stRes_take, ite_pos' (by omega)]
      exact hst3
    have := outsOk_at ho (4 + c) (by rw [termKids_length]; omega) (by omega) ht
    unfold kidAt at this
    rw [List.nil_append, termKids_getD_sel Lin D b0 hc] at this
    obtain ⟨h1, -⟩ := this
    rw [(hsl c hc).2.2.2.2.2, h1]
    show selRet x KC (stackOffsets KC).1 c = _
    unfold selRet pt28 pt128 p1Of
    rw [bitsEq_sel _ (by have := hK c hc; omega) hxl40,
      selProd_pad hxl (hO c) (hK c hc) (by omega)]
  -- the claims
  have hslot : ∀ k < 6, ∀ t, (t = 23 ∨ t = 24) →
      (∃ v, LoadHolds rd (σ (.n t)) k v) ∧ AddrIn R (σ (.n t)) k := by
    intro k hk t ht
    rcases ht with rfl | rfl
    · rw [e23, e14, e6']
      exact ⟨⟨_, (loadHolds_mul_gen_pow _ _ _ _ _).mpr (readsAt_getD hpt (k := τ + k) (by omega))⟩,
        ⟨B.pt + τ + k, rt_addr_mul _ _ _, Or.inl (hreg _ (by simp only [TermRegion]; omega))⟩⟩
    · rw [e24, e15, e6']
      exact ⟨⟨_, (loadHolds_mul_gen_pow _ _ _ _ _).mpr (readsAt_getD hpt1 (k := τ + k)
        (by simp [padPoint_length hxl40]; omega))⟩,
        ⟨B.pt1 + τ + k, rt_addr_mul _ _ _, Or.inl (hreg _ (by simp only [TermRegion]; omega))⟩⟩
  have hnotout : ∀ j < 165, termKind j ≠ 4 →
      Tables.claimColumns.getD j 0 ∉ keccakOutputColumns := fun j hj hk hm => hk (by
    have := (claimCol_out hj).mp hm; unfold termKind; split_ifs <;> omega)
  have hlamR : ∀ j < 165, termKind j ≠ 4 →
      (∃ v, LoadHolds rd (σ (.n 9)) j v) ∧ AddrIn R (σ (.n 9)) j := fun j hj hk => by
    rw [e9]
    exact ⟨⟨_, hlamP j hj (hnotout j hj hk)⟩, aL _ _ (by simp only [TermRegion]; omega)⟩
  have hin : ∀ j ∈ List.range 165, ClaimIn rd σ R cp j := by
    intro j hj
    have hj' := List.mem_range.mp hj
    have htc := termCol_lt hj'
    unfold ClaimIn
    split
    · rename_i hk
      have hj5 : j < 5 := by unfold termKind at hk; split_ifs at hk; omega
      have hle := hpz' j hj5
      obtain ⟨l9, a9⟩ := hlamR j hj' (by omega)
      refine ⟨by rw [e7]; exact hcpR j (by omega), by rw [e7]; exact aL _ _ (by simp only [TermRegion]; omega),
        ?_, ?_, by rw [e11, hcpK j hj' (Or.inl hk)]; exact hkv' _ htc,
        by rw [e11]; exact aL _ _ (by simp only [TermRegion]; omega), l9, a9⟩
      · exact ⟨_, by
          rw [e19, loadHolds_mul_gen_pow, Nat.add_zero]
          exact readsAt_getD (hBuf _ m0) (by rw [eqChain_length]; omega)⟩
      · rw [e19]
        exact ⟨b0 + cp j + 0, rt_addr_mul _ _ _, rB _ ⟨_, m0, by omega, by rw [eqChain_length]; omega⟩⟩
    · rename_i hk
      have hj5 : 5 ≤ j ∧ j < 162 := by unfold termKind at hk; split_ifs at hk <;> omega
      have hle := hpc' j hj5.1 hj5.2
      obtain ⟨l9, a9⟩ := hlamR j hj' (by omega)
      refine ⟨by rw [e7]; exact hcpR j (by omega), by rw [e7]; exact aL _ _ (by simp only [TermRegion]; omega),
        ?_, ?_, by rw [e11, hcpK j hj' (Or.inr (Or.inl hk))]; exact hkv' _ htc,
        by rw [e11]; exact aL _ _ (by simp only [TermRegion]; omega), l9, a9⟩
      · exact ⟨_, by
          rw [e21, loadHolds_mul_gen_pow, Nat.add_zero]
          exact readsAt_getD (hBuf _ m1) (by rw [eqChain_length]; omega)⟩
      · rw [e21]
        exact ⟨b0 + 35 + cp j + 0, rt_addr_mul _ _ _,
          rB _ ⟨_, m1, by omega, by rw [eqChain_length]; omega⟩⟩
    · rename_i hk
      have hj5 : 5 ≤ j ∧ j < 162 := by unfold termKind at hk; split_ifs at hk <;> omega
      have hle := hpc' j hj5.1 hj5.2
      obtain ⟨l9, a9⟩ := hlamR j hj' (by omega)
      refine ⟨by rw [e7]; exact hcpR j (by omega), by rw [e7]; exact aL _ _ (by simp only [TermRegion]; omega),
        ?_, ?_, ?_, by rw [e11]; exact aL _ _ (by simp only [TermRegion]; omega), l9, a9⟩
      · exact ⟨_, by
          rw [e21, loadHolds_mul_gen_pow, Nat.add_zero]
          exact readsAt_getD (hBuf _ m1) (by rw [eqChain_length]; omega)⟩
      · rw [e21]
        exact ⟨b0 + 35 + cp j + 0, rt_addr_mul _ _ _,
          rB _ ⟨_, m1, by omega, by rw [eqChain_length]; omega⟩⟩
      · rw [e11, hcpτ j hj' hk, hw64, ← pow_add, ← hK5]; exact hkv' 5 (by decide)
    · rename_i hk
      have hj5 : 162 ≤ j := by unfold termKind at hk; split_ifs at hk <;> omega
      have htc3 : termCol j < 3 := by unfold termCol; split_ifs <;> omega
      obtain ⟨l9, a9⟩ := hlamR j hj' (by omega)
      refine ⟨?_, by rw [e11]; exact aL _ _ (by simp only [TermRegion]; omega), l9, a9⟩
      rw [e11, e5, hglm, show m = KC.getD (termCol j) 0 from (hmem _ htc3).symm]
      exact hkv' _ htc
    · trivial
  obtain ⟨hCs, hCl⟩ := claimsT_complete (C := TrivC) hS hslot (List.range 165) claimsStart 16
    (by decide) (fun j hj => List.mem_range.mp hj) hin gC
  -- the tail
  have hchO : LoadHolds rd (ofK (gpow (b0 + 105))) (τ + 6)
      ((eqChain out.point ((p1Of x).take out.point.length)).getD (τ + 6) 0) :=
    readsAt_getD (hBuf _ m3) (by rw [eqChain_length]; omega)
  obtain ⟨hTs, hTl, e1993, e1994, e1996, e1998, e2000, e2001, e2003, e2008⟩ :=
    tail_complete (R := R) hS gT e6' (by rw [e11, ← hK5]; exact hkv' 5 (by decide))
      (by rw [e11]; exact aL _ _ (by simp only [TermRegion]; omega)) hchO
      (rB _ ⟨_, m3, by omega, by rw [eqChain_length]; omega⟩)
  -- the claims' sum
  have hclH : Stmt.HoldsList TrivC rd σ (claimsT (List.range 165) claimsStart 16).1 True
      (fun _ => True) := by
    refine holdsList_of_atoms _ (fun s hs => ?_) trivial
    have hat := List.all_eq_true.mp claims_atoms s hs
    cases s with
    | atom a => exact ⟨a, rfl, hCs _ hs⟩
    | _ => simp [isAtomB] at hat
  have hCp : ∀ j ∈ List.range 165, CpAt rd σ cp j := fun j hj hk v hv => by
    have hj' := List.mem_range.mp hj
    have hj2 : j < 162 := by unfold termKind at hk; split_ifs at hk <;> omega
    rw [e7] at hv
    exact loadHolds_unique hv (hcpR j hj2)
  obtain ⟨hsum, hoks, -⟩ := claimsT_sound (C := TrivC) (cp := cp) (List.range 165) claimsStart 16
    hCp hclH
  rw [show (claimsT (List.range 165) claimsStart 16).2.2 = 1989 by rw [claimsT_end]] at hsum
  -- the context of the claims' terms
  have hmem0 : (layout.placement memory0).vars = layout.logMemory := by
    have := placement_committed hkap hP (cc := 0) (by decide)
    rw [committedCols_getD (by decide), show colOfCommitted 0 = 0 from rfl] at this
    rw [show memory0 = 0 from rfl, this, hmem 0 (by decide)]
  have hmx : m ≤ x.length := by have := hK 0 (by decide); rw [hmem 0 (by decide)] at this; omega
  have htk : ∀ n i, i < n → i < 40 → ((p1Of x).take n).getD i 0 = 1 + x.getD i 0 :=
    fun n i hi h40 => by
      have : ((p1Of x).take n).getD i 0 = (p1Of x).getD i 0 := by
        simp [List.getD_eq_getElem?_getD, hi]
      rw [this]
      exact x1_getD hxl40 (by simp only [termPointCap]; omega)
  have hzc : ∀ n ≤ bus.point.length, n ≤ layout.stackLog →
      valOf rd (σ (.n 19)) n = eqEval (bus.point.take n) (x.take n) := fun n h1 h2 => by
    rw [e19, valOf_eq (readsAt_getD (hBuf _ m0) (by rw [eqChain_length]; omega))]
    simp only [eqChain]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]
    exact prefixProd_eq h1 (by simp [hpl40]; omega) (by omega) (fun i hi => htk _ i (by omega) (by omega))
  have hrc : ∀ n ≤ chis'.length, n ≤ layout.stackLog →
      valOf rd (σ (.n 21)) n = eqEval (chis'.take n) (x.take n) := fun n h1 h2 => by
    rw [e21, valOf_eq (readsAt_getD (hBuf _ m1) (by rw [eqChain_length]; omega))]
    simp only [eqChain]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]
    exact prefixProd_eq h1 (by simp [hpl40]; omega) (by omega) (fun i hi => htk _ i (by omega) (by omega))
  have hs1 : ∀ k < 6, valOf rd (σ (.n 23)) k = x.getD (τ + k) 0 := fun k hk => by
    rw [e23, e14, e6', valOf_eq ((loadHolds_mul_gen_pow _ _ _ _ _).mpr
      (readsAt_getD hpt (k := τ + k) (by omega)))]
    exact padPoint_getD x (τ + k)
  have hs0 : ∀ k < 6, valOf rd (σ (.n 24)) k = 1 + x.getD (τ + k) 0 := fun k hk => by
    rw [e24, e15, e6', valOf_eq ((loadHolds_mul_gen_pow _ _ _ _ _).mpr
      (readsAt_getD hpt1 (k := τ + k) (by simp [padPoint_length hxl40]; omega)))]
    exact x1_getD hxl40 (by simp only [termPointCap]; omega)
  have h33 : σ (.n 33) = eqEval (rm :: List.replicate (m - 1) 0) (x.take m) := by
    rw [e33, piW_getD le_rfl, ite_neg' (by omega)]
    show (rm + ((padPoint x).map (1 + ·)).getD 0 0) *
      ∏ i ∈ Ico 1 m, ((padPoint x).map (1 + ·)).getD i 0 = _
    rw [x1_getD hxl40 (by decide), ← piChain_eq hlm1 hmx]
    refine congrArg (_ * ·) (prod_congr rfl fun i hi ↦ ?_)
    rw [x1_getD hxl40 (by have := (mem_Ico.mp hi).2; simp only [termPointCap]; omega)]
  have T : TermCtx rd σ layout kappas claims bus.point chis' x lam rm cp :=
    { hkap := hkap, hP := hP, hx := hxl, hL := hSL28, hK := hK, hq := hdvd 5 (by decide),
      hK5 := hK5, hlane := fun g h1 h2 ↦ kappas_keccak hHL (by omega) (by omega), hmem := hmem,
      hlm := hlm1, hmem0 := hmem0, hcols := hcols, hzs := hbus40, hchis := hchL,
      hpz := fun j hj ↦ (hpts j _ (hptj j (by omega))).2.1 hj,
      hpc := fun j h1 h2 ↦ (hpts j _ (hptj j (by omega))).2.2.1 h1 h2,
      hpp := fun j h1 h2 ↦ (hpts j _ (hptj j h2)).2.2.2 h1,
      hcp := fun _ _ ↦ rfl,
      hlam := fun j hj hk ↦ by rw [e9]; exact valOf_eq (hlamP j hj (hnotout j hj hk)),
      hsel := hselv, hzc := hzc, hrc := hrc, hs1 := hs1, hs0 := hs0, h33 := h33,
      hok := fun j hj ↦ hoks j (List.mem_range.mpr hj),
      hkv := fun c hc ↦ by rw [e11]; exact valOf_eq (hkv' c hc) }
  -- the terminal check
  have hq5 := placement_committed hkap hP (cc := 5) (by decide)
  rw [committedCols_getD (by decide), show colOfCommitted 5 = 5 from rfl] at hq5
  have hret : σ (.n 2001) = ringWeight ringPoint (x.take (τ + 6)) coeffs := by
    have ht : (kidAt (termKids Lin D b0) [] outs 104).taken = true := by
      unfold kidAt; rw [List.nil_append, termKids_getD_104]
    have := outsOk_at ho 104 (by rw [termKids_length]; omega) (by omega) ht
    unfold kidAt at this
    rw [List.nil_append, termKids_getD_104] at this
    obtain ⟨h1, -⟩ := this
    rw [e2001, h1]
    show ringWeight ringPoint ((((padPoint x).map (1 + ·)).take (τ + 6)).map (1 + ·)) coeffs = _
    rw [map_one_take (by omega)]
  have h2003 : σ (.n 2003) = eqEval out.point (x.take (τ + 6)) := by
    rw [e2003]
    simp only [eqChain]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range, ← hoL,
      prefixProd_eq le_rfl (by simp [hpl40]; omega) (by omega) (fun i hi => htk _ i (by omega) (by omega)),
      List.take_of_length_le le_rfl]
  have h53 : σ (.n 53) = selProd ((stackOffsets KC).1.getD 5 0) (KC.getD 5 0)
      (layout.stackLog - KC.getD 5 0) x := hselv 5 (by decide)
  have hfin' : σ (.n 2008) = σ (.n 18) := by
    have e16 : σ (.n 16) = inner := ea 16 (by omega)
    have e17 : σ (.n 17) = yr := ea 17 (by omega)
    have e18 : σ (.n 18) = target := ea 18 (by omega)
    have e8 : σ (.n 8) = lamOut := ea 8 (by omega)
    rw [e18, ← hfin, stackWeight_eq layout out ringPoint coeffs lam x hcols, e2008, hsum, hret, e8,
      h2003, e16, e17, hlamO, list_sum_range,
      sum_congr rfl fun j hj ↦ claimTerm_eq T (mem_range.mp hj),
      ringClaim_eq (show layout.placement qkeccak = _ from hq5) hxl,
      wOf_committed (by rw [hoc]; exact hq5) (by rw [hoL, hK5]) hxl (hK 5 (by decide)), h53, hK5]
    ring
  -- the body
  have hall : ∀ s ∈ termPre, Fwd.SHolds TrivC rd σ s := by
    intro s hs
    simp only [termPre, List.mem_append] at hs
    rcases hs with ((h | h) | h) | h
    · exact hHs s h
    · obtain ⟨c, hc, h⟩ := List.mem_flatMap.mp h
      exact (hsl c (List.mem_range.mp hc)).1 s h
    · exact hCs s h
    · exact hTs hfin' s h
  refine ⟨σ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [term_params]
    apply List.ext_getElem (by simp [hargs, termArgs])
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [ea i (by simpa using h1), List.getD_eq_getElem _ _ h2]
  · intro s hs
    simp only [termPre, List.mem_append] at hs
    rcases hs with ((h | h) | h) | h
    · exact dispOk_of_noDisp (List.all_eq_true.mp head_noDisp s h)
    · obtain ⟨c, hc, h⟩ := List.mem_flatMap.mp h
      exact (hsl c (List.mem_range.mp hc)).2.1 s h
    · exact dispOk_of_noDisp (List.all_eq_true.mp claims_noDisp s h)
    · exact dispOk_of_noDisp (List.all_eq_true.mp tail_noDisp s h)
  · rw [term_body']
    exact Fwd.holdsList_straight termPre [] False _ hall rfl
  · rw [term_allocs]; rfl
  · rw [term_allocs]
    simp [bases, e19, e21, e25, e1993, Nat.add_assoc]
  · rw [term_callSF σ]
    refine callsMatch_kidsAt _ _ _ _ (by simp [termKids_length, Tables.nCommittedCols])
      (by rw [termKids_length, hol]) fun j hj => ?_
    have hj' : j < 105 := by simpa [Tables.nCommittedCols] using hj
    rw [getD_map_lt (Main.mkCall σ) (none, "", [], []) noCall (by simpa using hj),
      getD_seg _ _ _ _ rfl (by simp [Tables.nCommittedCols])]
    have hOK := fun (ht : (kidAt (termKids Lin D b0) [] outs j).taken = true) =>
      outsOk_at ho j (by rw [termKids_length]; omega) (by omega) ht
    unfold kidAt at hOK ⊢
    rw [List.nil_append] at hOK ⊢
    split_ifs with h4 h103
    · interval_cases j
      · refine ⟨rfl, rfl, fun ht => ⟨?_, (hOK ht).1.symm⟩⟩
        show [σ (.n 19), σ (.n 20), σ (.n 0), σ (.n 15), σ (.n 3)] = _
        rw [e19, e20, ea 0 (by omega), e15, ea 3 (by omega)]; rfl
      · refine ⟨rfl, rfl, fun ht => ⟨?_, (hOK ht).1.symm⟩⟩
        show [σ (.n 21), σ (.n 22), σ (.n 1), σ (.n 15), σ (.n 4)] = _
        rw [e21, e22, ea 1 (by omega), e15, ea 4 (by omega)]; rfl
      · refine ⟨rfl, ?_, fun ht => ⟨?_, (hOK ht).1.symm⟩⟩
        · show decide (σ (.n 30) ≠ 0) = decide (word 2 0 0 + glm ≠ 0)
          rw [e30, hglm]
        · show [σ (.n 31), σ (.n 5), σ (.n 25), σ (.n 15)] = _
          rw [e31, e5, e25, e15]; rfl
      · refine ⟨rfl, rfl, fun _ => ⟨?_, ?_⟩⟩
        · show [σ (.n 14), σ (.n 15)] = _
          rw [e14, e15]; rfl
        · obtain ⟨ese, esg, h1, -⟩ := hst3
          show [σ (.n 34), σ (.n 35)] = (stRes outs).1
          rw [e34, e35, h1]; rfl
    · obtain ⟨c, rfl⟩ : ∃ c, j = 4 + c := ⟨j - 4, by omega⟩
      have hc : c < 99 := by omega
      rw [show 4 + c - 4 = c by omega, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map,
        List.getElem_range]
      rw [termKids_getD_sel Lin D b0 hc] at hOK ⊢
      obtain ⟨-, -, -, e36, e37, esel⟩ := hsl c hc
      have hlog : logG (σ (.n (37 + 3 * c))) = KC.getD c 0 := by
        rw [e37, gen_pow_eq_ofK]; exact logG_spec (by have := hKC29 c hc; omega)
      refine ⟨?_, ?_, fun ht => ⟨?_, ?_⟩⟩
      · show colSelNames.getD (logG (σ (.n (37 + 3 * c)))) "" = Tables.lName "column_selector" (KC.getD c 0)
        rw [hlog, colSelNames, List.getD_eq_getElem _ _ (by simp; exact hKC29 c hc), List.getElem_map,
          List.getElem_range]
      · show true = @decide _ (Classical.propDecidable _)
        refine (@decide_eq_true _ (Classical.propDecidable _) ?_).symm
        rw [stRes_take, ite_pos' (by omega)]
        exact hst3
      · show [σ (.n (36 + 3 * c)), σ (.n 34), σ (.n 35)] = [gen ^ (stackOffsets KC).1.getD c 0,
          (stRes (outs.take (4 + c))).1.getD 0 0, (stRes (outs.take (4 + c))).1.getD 1 0]
        rw [stRes_take, ite_pos' (by omega), e36, e34, e35]
      · show [σ (.n (selV c))] = _
        rw [esel, (hOK ht).1]; rfl
    · have : j = 103 ∨ j = 104 := by omega
      rcases this with rfl | rfl
      · rw [termKids_getD_103] at hOK ⊢
        refine ⟨rfl, rfl, fun ht => ⟨?_, (hOK ht).1.symm⟩⟩
        show [σ (.n 1993), σ (.n 1994), σ (.n 12), σ (.n 15), σ (.n 1996)] =
          [ofK (gpow (b0 + 105)), word 1 0 0, ofK (gpow B.zv), ofK (gpow B.pt1), gtau * word 64 0 0]
        rw [e1993, e1994, ea 12 (by omega), e15, e1996, hgtau]; rfl
      · rw [termKids_getD_104] at hOK ⊢
        refine ⟨rfl, rfl, fun ht => ⟨?_, ?_⟩⟩
        · show [σ (.n 1998), σ (.n 15), σ (.n 13), σ (.n 2000)] =
            [ofK (gpow B.zv) * word 549755813888 0 0, ofK (gpow B.pt1), ofK (gpow B.ct),
              gtau * word 64 0 0]
          rw [e1998, ea 12 (by omega), e15, ea 13 (by omega), e2000, hgtau]; rfl
        · show [σ (.n 2001)] = _
          rw [e2001, (hOK ht).1]; rfl
  · intro q hq
    simp only [termPre, List.filterMap_append, List.mem_append] at hq
    rcases hq with ((h | h) | h) | h
    · exact hHl q h
    · obtain ⟨s, hs, hq⟩ := List.mem_filterMap.mp h
      obtain ⟨c, hc, hs⟩ := List.mem_flatMap.mp hs
      exact (hsl c (List.mem_range.mp hc)).2.2.1 q (List.mem_filterMap.mpr ⟨s, hs, hq⟩)
    · exact hCl q h
    · exact hTl q h

end
end LeanVM.Guest.B1.VerifySub
