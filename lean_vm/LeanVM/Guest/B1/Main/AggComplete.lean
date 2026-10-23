/-
  LeanVM.Guest.B1.Main.AggComplete

  `aggregate_claims`, completely: `m` children whose words the memory holds, the hints of an
  accepting batching and the memory an honest run leaves at its buffers give its core IR
  relation, the claim at `defer_stmt` the batching (TRIAGE G #97).
-/

module

public import LeanVM.Guest.B1.Main.AggMainCChk
public import LeanVM.Guest.B1.Main.AggL25Complete
public import LeanVM.Guest.B1.Main.AggL26Complete

/-!
# `aggregate_claims`, completely

The honest valuation is the body evaluated (`Fwd.ev`) on the arguments, the hints and the
sumcheck's returns its honest ones (`aggOrc`: the buffers `P`, `bc_star_hint`, the sumcheck's
final capacity and claim). Its atoms hold (their side conditions its loads, its packs'
`assert_in_k` and the final check, which `batch cs h = some out` is), its stores find the honest
rows, weights and claim; its calls hold by their completeness: the absorbing rows (`l25_block`),
the squeezing rows (`l26_block`), the sumcheck (`batch_sumcheck_holds`) and the weights
(`l27_block`).

`aggregate_claims_complete_mem` is pointer-parametric (any `AggPtrs` holding `AggMem`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Da LeanVM.Node

@[expose] public section

variable {rd : Reader}

/-- The oracle of `aggregate_claims`' hints and its sumcheck's returns `res`. -/
def aggOrc (P : AggPtrs) (h : BatchHints) (res : (List E × E) × Fs) (j : ℕ) : E :=
  if j = 5 then P.msgs else if j = 6 then h.bytecodeValue else if j = 7 then P.lf
  else if j = 8 then P.lc else if j = 60 then P.absorb else if j = 71 then P.lam
  else if j = 79 then P.sq else if j = 104 then P.pt else if j = 118 then P.w
  else if j = 115 then res.1.2 else if 110 ≤ j ∧ j < 115 then res.2.cap.getD (j - 110) 0 else 0

theorem const_good {S : List Atom} {w : ℕ → E} {σ : Val} {atoms : List Atom} {x : V} {lo hi : ℕ}
    (h : atoms.any (isConstAt x lo hi) = true) (hg : ∀ a ∈ atoms, Good rd S w σ a) :
    σ x = word lo hi 0 := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  have := hg a ha
  cases a <;> simp only [isConstAt, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨rfl, he⟩ := hp
  rw [← eEqb_sound he]
  exact this

/-- A guard's words: `1 + N` and the counter's `1`. -/
theorem guardOk_vals {σ : Val} {P : List Stmt} {gc : V} {f : String} {one N : V} {rest : List V}
    (h : guardOk P gc f one N rest = true) (hat : ∀ a ∈ atomsIn P, a.Holds rd σ) :
    σ gc = 1 + σ N ∧ σ one = 1 := by
  simp only [guardOk, Bool.and_eq_true] at h
  obtain ⟨⟨-, ha⟩, h1⟩ := h
  split at ha
  · rename_i p q hpq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
    obtain ⟨hp1, rfl⟩ := ha
    exact ⟨by rw [addOf_sound hpq hat, const_sound hp1 hat, word_one],
      by rw [const_sound h1 hat, word_one]⟩
  · exact absurd ha (by simp)

/-- The claim an accepting batching writes. -/
theorem batch_out {cs : List ChildClaims} {h : BatchHints} {out : DeferredClaim}
    (hb : batch cs h = some out) :
    out = aggOut cs h ∧ (aggRun cs h).1.2 =
      h.bytecodeValue * Batch.bytecodeWeight cs (aggLam cs).1 (aggRun cs h).1.1 := by
  rw [batch_fs] at hb
  split at hb
  · rename_i hc
    exact ⟨(Option.some.inj hb).symm, hc⟩
  · exact absurd hb (by simp)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`aggregate_claims` is complete** on `m` children whose words the memory holds, the hints of
an accepting batching (`batch cs h = some out`) and the honest memory at any choice of its
buffers `P`: its relation holds, and `defer_stmt` holds the batching's claim. -/
theorem aggregate_claims_complete_mem {m : ℕ} (hm1 : 1 ≤ m) {cpi cfresh ccarried dst : E}
    {cs : List ChildClaims} (hcl : cs.length = m)
    (hcw : ∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c])
    {h : BatchHints} {out : DeferredClaim} (hrl : h.bytecodeRounds.length = 23)
    (hb : batch cs h = some out) {P : AggPtrs} (hmem : AggMem rd cfresh ccarried dst cs h P) :
    coreProgram.Rel rd "aggregate_claims" [gen ^ m, cpi, cfresh, ccarried, dst] [] ∧
      ReadsAt rd dst out.cells := by
  subst hcl
  obtain ⟨hout, hfin⟩ := batch_out hb
  subst hout
  refine ⟨?_, hmem.dst⟩
  -- the checks
  have hok := agg_ok
  simp only [aggOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hparams⟩, hseed⟩, hp0⟩, hc23⟩, hp23⟩, hc33⟩,
    hp33⟩, hc43⟩, hp43⟩, -⟩, hg25⟩, -⟩, -⟩, hc93⟩, -⟩, hg26⟩, -⟩, -⟩,
    -⟩, -⟩, hc119⟩, -⟩, hg27⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hok
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at hseed
  have hcok := aggc_ok
  simp only [aggCOk, Bool.and_eq_true, Option.isSome_iff_exists] at hcok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c', hchk⟩, hcanA⟩, hneeds⟩, hpk⟩, hll⟩, hhints⟩, hcallsAll⟩, hcallsIn⟩, hm69⟩,
    hm102⟩, hm123⟩, hm125⟩ := hcok
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hneeds
  simp only [List.all_eq_true, decide_eq_true_eq] at hll hhints hcallsAll hcallsIn
  have hS := agg_stores
  have hbody := agg_shape
  -- the honest run
  obtain ⟨SF, hSF⟩ := bsRun_cap h.bytecodeRounds (Batch.claimBOf cs (aggLam cs).1) (aggLam cs).2
    (by intro h0; rw [h0] at hrl; simp at hrl)
  have hres2 : (aggRun cs h).2 = ⟨capOf SF, []⟩ := hSF
  have hptl : (aggRun cs h).1.1.length = 23 := by rw [aggRun, bsRun_len, hrl]
  -- the valuation
  let w : ℕ → E := aggOrc P h (aggRun cs h)
  let args : List E := [gen ^ cs.length, cpi, cfresh, ccarried, dst]
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd w args (Fn.body Data.core31)) := ⟨_, rfl⟩
  have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
  obtain ⟨-, -, hgs⟩ := ev_spec rd w (Fn.body Data.core31) args hchk
  rw [show args.length = 5 from rfl, ← hσ, hS] at hgs
  have hmemP : ∀ s ∈ aggP, s ∈ Fn.body Data.core31 := fun s hs => by
    rw [hbody]; exact List.mem_append_left _ hs
  have hg : ∀ a ∈ atomsIn aggP, Good rd aggStores w σ a := fun a ha =>
    hgs (.atom a) (hmemP _ (atom_mem_of_atomsIn ha))
  have par : ∀ i (hi : i < 5), σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args]; omega)
  have e0 : σ (.n 0) = gen ^ cs.length := par 0 (by omega)
  have e1 : σ (.n 1) = cpi := par 1 (by omega)
  have e2 : σ (.n 2) = cfresh := par 2 (by omega)
  have e3 : σ (.n 3) = ccarried := par 3 (by omega)
  have e4 : σ (.n 4) = dst := par 4 (by omega)
  -- the hints and the sumcheck's returns
  have hint : ∀ a ∈ aggHintsA, Good rd aggStores w σ a := fun a ha => hg a (hhints a ha)
  simp only [aggHintsA, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Good] at hint
  obtain ⟨h5, h6, h7, h8, h60, h71, h79, h104, h118⟩ := hint
  have v5 : σ (.n 5) = P.msgs := by rw [h5]; rfl
  have v6 : σ (.n 6) = h.bytecodeValue := by rw [h6]; rfl
  have v7 : σ (.n 7) = P.lf := by rw [h7]; rfl
  have v8 : σ (.n 8) = P.lc := by rw [h8]; rfl
  have v60 : σ (.n 60) = P.absorb := by rw [h60]; rfl
  have v71 : σ (.n 71) = P.lam := by rw [h71]; rfl
  have v79 : σ (.n 79) = P.sq := by rw [h79]; rfl
  have v104 : σ (.n 104) = P.pt := by rw [h104]; rfl
  have v118 : σ (.n 118) = P.w := by rw [h118]; rfl
  have hret : GoodS rd aggStores w σ (.call "batch_sumcheck__L23"
      [.n 105, .n 106, .n 107, .n 108, .n 109, .n 5, .n 103, .n 104]
      [.n 110, .n 111, .n 112, .n 113, .n 114, .n 115]) := by
    obtain ⟨s, hs, he⟩ := List.any_eq_true.mp (hcallsIn (.call "batch_sumcheck__L23"
      [.n 105, .n 106, .n 107, .n 108, .n 109, .n 5, .n 103, .n 104]
      [.n 110, .n 111, .n 112, .n 113, .n 114, .n 115])
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    rw [← stmtEqb_sound he]
    exact hgs s (hmemP s hs)
  simp only [GoodS, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hret
  obtain ⟨r110, r111, r112, r113, r114, r115⟩ := hret
  have v115 : σ (.n 115) = (aggRun cs h).1.2 := by rw [r115]; rfl
  -- the products
  have hP : ∀ a ∈ (atomsIn aggP).filter pureB, a.Holds rd σ := pure_holds hg
  have p69 : σ (.n 69) = P.absorb * (gen ^ cs.length) ^ 13 := by
    rw [monoIs_sound hm69 hP, v60, e0]
  have p102 : σ (.n 102) = P.sq * (gen ^ cs.length) ^ 14 := by
    rw [monoIs_sound hm102 hP, v79, e0]
  have p123 : σ (.n 123) = P.w * gen ^ cs.length := by rw [isMul_sound hm123 hP, v118, e0]
  -- the loads
  have hg' : ∀ a ∈ aggA, Good rd aggStores w σ a := fun a ha => hg a (mem_aggA.mp ha).1
  have hnS : ∀ a ∈ aggA, a ∉ aggStores := fun a ha => (mem_aggA.mp ha).2
  have hokA := aggAbs_ok cs
  have hlast := hmem.absorb cs.length le_rfl
  rw [absSt_last rfl] at hlast
  have hsqOk := sqSt_ok cs cs.length
  have hsqm := hmem.sq cs.length le_rfl
  have hsql : (rowW (sq2F cs.length (aggAbs cs)).2 ++ [claimAt cs cs.length]).length = 14 := by
    simp [rowW_length hsqOk]
  have L80 : ∀ k (hk : k < 13), σ (.n (80 + k)) = (rowW (aggAbs cs)).getD k 0 ∧
      (Atom.load (.n (80 + k)) (.n 69) k).Holds rd σ := fun k hk => by
    have hm : Atom.load (.n (80 + k)) (.n 69) k ∈ aggA := hll _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)))))
    refine load_of_good (hnS _ hm) (hg' _ hm) ?_
    rw [p69, List.getD_eq_getElem _ _ (by rw [rowW_length hokA]; exact hk)]
    exact hlast k (by rw [rowW_length hokA]; exact hk)
  have L103 : σ (.n 103) = claimAt cs cs.length ∧ (Atom.load (.n 103) (.n 102) 13).Holds rd σ := by
    have hm : Atom.load (.n 103) (.n 102) 13 ∈ aggA := hll _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_singleton_self _)))))
    rw [← rowW_snoc_13 hsqOk (claimAt cs cs.length)]
    refine load_of_good (hnS _ hm) (hg' _ hm) ?_
    rw [p102, List.getD_eq_getElem _ _ (by rw [hsql]; omega)]
    exact hsqm 13 (by rw [hsql]; omega)
  have L105 : ∀ i (hi : i < 5), σ (.n (105 + i)) = (sq2F cs.length (aggAbs cs)).2.cap.getD i 0 ∧
      (Atom.load (.n (105 + i)) (.n 102) i).Holds rd σ := fun i hi => by
    have hm : Atom.load (.n (105 + i)) (.n 102) i ∈ aggA := hll _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))))
    rw [← rowW_getD_cap hsqOk hi, ← rowW_snoc_lt hsqOk (claimAt cs cs.length) (by omega)]
    refine load_of_good (hnS _ hm) (hg' _ hm) ?_
    rw [p102, List.getD_eq_getElem _ _ (by rw [hsql]; omega)]
    exact hsqm i (by rw [hsql]; omega)
  have L124 : σ (.n 124) = weightAt cs h cs.length ∧ (Atom.load (.n 124) (.n 123) 0).Holds rd σ := by
    have hm : Atom.load (.n 124) (.n 123) 0 ∈ aggA := hll _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_singleton_self _)))
    refine load_of_good (hnS _ hm) (hg' _ hm) ?_
    rw [p123]
    exact hmem.w cs.length le_rfl
  have L126 : ∀ k (hk : k < 23), σ (.n (126 + k)) = (aggRun cs h).1.1.getD k 0 ∧
      (Atom.load (.n (126 + k)) (.n 104) k).Holds rd σ := fun k hk => by
    have hm : Atom.load (.n (126 + k)) (.n 104) k ∈ aggA := hll _ (List.mem_append_right _
      (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))
    refine load_of_good (hnS _ hm) (hg' _ hm) ?_
    rw [v104, List.getD_eq_getElem _ _ (by rw [hptl]; exact hk)]
    exact hmem.pt k (by rw [hptl]; exact hk)
  -- the atoms but the stores
  have hat' : ∀ a ∈ aggA, a.Holds rd σ := by
    refine atoms_holds hidx hcanA hg' (fun i hi => absurd hi (by simp)) fun a ha hns => Or.inl ?_
    rcases hneeds a ha with ((hx | hx) | hx) | rfl
    · rw [hns] at hx; exact absurd hx (by simp)
    · exact pack_inK hpk hg' hx
    · simp only [aggLoads, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with (((⟨k, hk, rfl⟩ | rfl) | ⟨i, hi, rfl⟩) | rfl) | ⟨k, hk, rfl⟩
      · exact (L80 k hk).2
      · exact L103.2
      · exact (L105 i hi).2
      · exact L124.2
      · exact (L126 k hk).2
    · show σ (.n 115) + σ (.n 125) = 0
      rw [isMul_sound hm125 hP, v115, v6, L124.1, weightAt_last rfl]
      exact e_add_eq_zero_iff.mpr hfin
  -- the stores
  have hst0 := absSt_ok cs.length cs 0
  have hrow0 := hmem.absorb 0 (Nat.zero_le _)
  rw [pow_zero, one_pow, mul_one] at hrow0
  have r0 : ∀ k < 13, LoadHolds rd (σ (.n 60)) k ((rowW (absSt cs.length cs 0)).getD k 0) :=
    fun k hk => by
      rw [v60, List.getD_eq_getElem _ _ (by rw [rowW_length hst0]; exact hk)]
      exact hrow0 k (by rw [rowW_length hst0]; exact hk)
  have hpack : ∀ j < 4, ∀ (x : V) (b : ℕ), packIn (atomsIn aggP) x b = true →
      σ x = [gen ^ cs.length, 0, 0, 0].getD j 0 →
      LoadHolds rd (σ (.n 60)) (5 + 2 * j) (σ (.n (b + 6))) ∧
        LoadHolds rd (σ (.n 60)) (6 + 2 * j) (σ (.n (b + 8))) := by
    intro j hj x b hpb hx
    have hpc := pack_cells hpb hg
    have hr := Keccak.rateCell_scalar (absSt cs.length cs 0).pend j (by rw [absSt_zero]; simp; omega)
    have hpj : (absSt cs.length cs 0).pend[j]'(by rw [absSt_zero]; simp; omega) =
        ([gen ^ cs.length, 0, 0, 0].getD j 0, dsObserve) := by
      simp only [absSt_zero]
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl
    rw [hpj, ← hx, ← hpc] at hr
    simp only [Prod.ext_iff] at hr
    have a := r0 (5 + 2 * j) (by omega)
    have b' := r0 (5 + (2 * j + 1)) (by omega)
    rw [rowW_getD_rate hst0 (by omega), hr.1] at a
    rw [rowW_getD_rate hst0 (by omega), hr.2, show 5 + (2 * j + 1) = 6 + 2 * j by omega] at b'
    exact ⟨a, b'⟩
  have hsq0 := hmem.sq 0 (Nat.zero_le _)
  rw [pow_zero, one_pow, mul_one] at hsq0
  have hsq0l : (rowW (sq2F 0 (aggAbs cs)).2 ++ [claimAt cs 0]).length = 14 := by
    simp [rowW_length (sqSt_ok cs 0)]
  have hdst := hmem.dst
  have hdl : (aggOut cs h).cells.length = 24 := by simp [aggOut, DeferredClaim.cells, hptl]
  have hstores : ∀ a ∈ aggStores, a.Holds rd σ := by
    intro a haS
    simp only [aggStores, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at haS
    rcases haS with (((((⟨i, hi, rfl⟩ | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)) |
      ⟨k, hk, rfl⟩) | (rfl | rfl)) | ⟨k, hk, rfl⟩) | rfl)
    · show LoadHolds rd (σ (.n 60)) i (σ (.n (9 + i)))
      have e := r0 i (by omega)
      rw [rowW_getD_cap hst0 hi, absSt_zero, ← seed_cells i hi, ← const_good (hseed i hi).1 hg] at e
      exact e
    · exact (hpack 0 (by omega) (.n 0) 14 hp0 (by rw [e0]; rfl)).1
    · exact (hpack 0 (by omega) (.n 0) 14 hp0 (by rw [e0]; rfl)).2
    · exact (hpack 1 (by omega) (.n 23) 24 hp23 (by rw [const_good hc23 hg, word_zero]; rfl)).1
    · exact (hpack 1 (by omega) (.n 23) 24 hp23 (by rw [const_good hc23 hg, word_zero]; rfl)).2
    · exact (hpack 2 (by omega) (.n 33) 34 hp33 (by rw [const_good hc33 hg, word_zero]; rfl)).1
    · exact (hpack 2 (by omega) (.n 33) 34 hp33 (by rw [const_good hc33 hg, word_zero]; rfl)).2
    · exact (hpack 3 (by omega) (.n 43) 44 hp43 (by rw [const_good hc43 hg, word_zero]; rfl)).1
    · exact (hpack 3 (by omega) (.n 43) 44 hp43 (by rw [const_good hc43 hg, word_zero]; rfl)).2
    · show LoadHolds rd (σ (.n 79)) k (σ (.n (80 + k)))
      have e := hsq0 k (by rw [hsq0l]; omega)
      rw [← List.getD_eq_getElem _ 0, rowW_snoc_lt (sqSt_ok cs 0) _ hk] at e
      rw [v79, (L80 k hk).1]
      exact e
    · show LoadHolds rd (σ (.n 79)) 13 (σ (.n 93))
      have e := hsq0 13 (by rw [hsq0l]; omega)
      rw [← List.getD_eq_getElem _ 0, rowW_snoc_13 (sqSt_ok cs 0), claimAt_zero] at e
      rw [v79, const_good hc93 hg, word_zero]
      exact e
    · show LoadHolds rd (σ (.n 118)) 0 (σ (.n 119))
      have e := hmem.w 0 (Nat.zero_le _)
      rw [pow_zero, mul_one, weightAt_zero] at e
      rw [v118, const_good hc119 hg, word_zero]
      exact e
    · show LoadHolds rd (σ (.n 4)) k (σ (.n (126 + k)))
      have e := hdst k (by rw [hdl]; omega)
      rw [← List.getD_eq_getElem _ 0] at e
      rw [e4, (L126 k hk).1]
      have : (aggOut cs h).cells.getD k 0 = (aggRun cs h).1.1.getD k 0 := by
        rw [aggOut, DeferredClaim.cells, List.getD_append _ _ _ _ (by rw [hptl]; exact hk)]
      rw [this] at e
      exact e
    · show LoadHolds rd (σ (.n 4)) 23 (σ (.n 6))
      have e := hdst 23 (by rw [hdl]; omega)
      rw [← List.getD_eq_getElem _ 0] at e
      rw [e4, v6]
      have : (aggOut cs h).cells.getD 23 0 = h.bytecodeValue := by
        rw [aggOut, DeferredClaim.cells, List.getD_append_right _ _ _ _ (by rw [hptl]), hptl]
        rfl
      rw [this] at e
      exact e
  have hat : ∀ a ∈ atomsIn aggP, a.Holds rd σ := fun a ha => by
    by_cases haS : a ∈ aggStores
    · exact hstores a haS
    · exact hat' a (mem_aggA.mpr ⟨ha, haS⟩)
  -- the calls
  have find394 := find_of_idx l25_idx (by rw [coreProgram_length]; omega)
  have find395 := find_of_idx l26_idx (by rw [coreProgram_length]; omega)
  have find397 := find_of_idx l27_idx (by rw [coreProgram_length]; omega)
  have s25 : loopShapeF (coreProgram.getD 394 default) "__loop25" = true := by
    have hok := l25_ok
    simp only [l25Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩,
      -⟩, -⟩ := hok
    exact hshape
  have hall : ∀ s ∈ aggP, SHolds (coreProgram.Rel rd) rd σ s := by
    intro s hs
    by_cases hsa : ∃ a, s = .atom a
    · obtain ⟨a, rfl⟩ := hsa
      exact hat a (mem_atomsIn hs)
    have hsk : aggCalls.any (stmtEqb s) = true := by
      have := hcallsAll s hs
      cases s with
      | atom a => exact absurd ⟨a, rfl⟩ hsa
      | _ => exact this
    obtain ⟨c, hc, he⟩ := List.any_eq_true.mp hsk
    rw [stmtEqb_sound he]
    simp only [aggCalls, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · show IsInK (σ (.n 62)) ∧ (σ (.n 62) ≠ 0 → coreProgram.Rel rd "__loop25"
        [σ (.n 63), σ (.n 0), σ (.n 60), σ (.n 2), σ (.n 7), σ (.n 3), σ (.n 8), σ (.n 1)] [])
      obtain ⟨g62, g63⟩ := guardOk_vals hg25 hat
      rw [g62, g63, e0, v60, e2, v7, e3, v8, e1]
      refine guard_complete find394 s25 (rest := [P.absorb, cfresh, P.lf, ccarried, P.lc, cpi])
        (m := cs.length) fun c hc => ?_
      obtain ⟨-, -, -, -, -, -, hpi, hfr, hca⟩ := kid_reads (hcw c hc)
      have hnext := hmem.absorb (c + 1) hc
      rw [absSt_succ hc (hcw c hc), show P.absorb * (gen ^ (c + 1)) ^ 13 =
        P.absorb * (gen ^ c) ^ 13 * gen ^ 13 by ring] at hnext
      exact l25_block (absSt_ok _ _ _) (absSt_pend hcw c hc.le) (hmem.absorb c hc.le) hnext
        (hmem.lf c hc) (hmem.lc c hc) hpi hfr hca
    · show IsInK (σ (.n 95)) ∧ (σ (.n 95) ≠ 0 → coreProgram.Rel rd "__loop26"
        [σ (.n 96), σ (.n 0), σ (.n 79), σ (.n 71), σ (.n 7), σ (.n 8)] [])
      obtain ⟨g95, g96⟩ := guardOk_vals hg26 hat
      rw [g95, g96, e0, v79, v71, v7, v8]
      refine guard_complete find395 l26_shape.1 (rest := [P.sq, P.lam, P.lf, P.lc])
        (m := cs.length) fun c hc => ?_
      obtain ⟨-, -, -, -, hfv, hcv, -, -, -⟩ := kid_reads (hcw c hc)
      have hnext := hmem.sq (c + 1) hc
      rw [sq2F_snoc, claimAt_succ hc, show P.sq * (gen ^ (c + 1)) ^ 14 =
        P.sq * (gen ^ c) ^ 14 * gen ^ 14 by ring] at hnext
      exact l26_block (sqSt_ok cs c) (hmem.sq c hc.le) hnext (hmem.lam c hc) (hmem.lf c hc)
        (hmem.lc c hc) hfv hcv
    · show coreProgram.Rel rd "batch_sumcheck__L23"
        ([V.n 105, V.n 106, V.n 107, V.n 108, V.n 109, V.n 5, V.n 103, V.n 104].map σ)
        ([V.n 110, V.n 111, V.n 112, V.n 113, V.n 114, V.n 115].map σ)
      obtain ⟨⟨S', hS'⟩, -, -⟩ := hsqOk
      have hcap : [σ (.n 105), σ (.n 106), σ (.n 107), σ (.n 108), σ (.n 109)] =
          (sq2F cs.length (aggAbs cs)).2.cap := by
        rw [show (105 : ℕ) = 105 + 0 from rfl, (L105 0 (by omega)).1, (L105 1 (by omega)).1,
          (L105 2 (by omega)).1, (L105 3 (by omega)).1, (L105 4 (by omega)).1, hS']
        rfl
      have hrun : bsRun h.bytecodeRounds (claimAt cs cs.length)
          ⟨(sq2F cs.length (aggAbs cs)).2.cap, []⟩ = aggRun cs h := by
        rw [aggRun, claimAt_last rfl, aggLam_snd rfl hm1]
      simp only [List.map_cons, List.map_nil]
      refine (batch_sumcheck_holds rd _ _).mpr ⟨?_, h.bytecodeRounds, hrl, ?_, ?_, ?_⟩
      · rw [hcap, hS']; exact capOf_canonical S'
      · rw [v5]; exact hmem.msgs
      · show ReadsAt rd (σ (.n 104)) (bsRun h.bytecodeRounds (σ (.n 103))
          ⟨[σ (.n 105), σ (.n 106), σ (.n 107), σ (.n 108), σ (.n 109)], []⟩).1.1
        rw [hcap, L103.1, hrun, v104]
        exact hmem.pt
      · show [σ (.n 110), σ (.n 111), σ (.n 112), σ (.n 113), σ (.n 114), σ (.n 115)] =
          (bsRun h.bytecodeRounds (σ (.n 103))
            ⟨[σ (.n 105), σ (.n 106), σ (.n 107), σ (.n 108), σ (.n 109)], []⟩).2.cap ++
          [(bsRun h.bytecodeRounds (σ (.n 103))
            ⟨[σ (.n 105), σ (.n 106), σ (.n 107), σ (.n 108), σ (.n 109)], []⟩).1.2]
        rw [hcap, L103.1, hrun, r110, r111, r112, r113, r114, r115]
        show [(aggRun cs h).2.cap.getD 0 0, (aggRun cs h).2.cap.getD 1 0,
          (aggRun cs h).2.cap.getD 2 0, (aggRun cs h).2.cap.getD 3 0,
          (aggRun cs h).2.cap.getD 4 0, (aggRun cs h).1.2] = _
        rw [hres2]
        rfl
    · show IsInK (σ (.n 121)) ∧ (σ (.n 121) ≠ 0 → coreProgram.Rel rd "__loop27"
        [σ (.n 122), σ (.n 0), σ (.n 7), σ (.n 8), σ (.n 104), σ (.n 118), σ (.n 71)] [])
      obtain ⟨g121, g122⟩ := guardOk_vals hg27 hat
      rw [g121, g122, e0, v7, v8, v104, v118, v71]
      refine guard_complete find397 l27_shape.1 (rest := [P.lf, P.lc, P.pt, P.w, P.lam])
        (m := cs.length) fun c hc => ?_
      obtain ⟨hpl, hql, hpf, hpc, -, -, -, -, -⟩ := kid_reads (hcw c hc)
      have hw1 := hmem.w (c + 1) hc
      rw [weightAt_succ hc, show P.w * gen ^ (c + 1) = P.w * gen ^ c * gen ^ 1 by ring,
        loadHolds_mul_gen_pow] at hw1
      exact l27_block (hmem.lf c hc) (hmem.lc c hc) hpf hpc hmem.pt hpl hql hptl (hmem.lam c hc)
        (hmem.w c hc.le) hw1
  refine (rel_iff_sem find_aggregate_claims _ _).mpr ⟨σ, ?_, ?_⟩
  · rw [hparams]
    simp only [List.map_cons, List.map_nil]
    rw [e0, e1, e2, e3, e4]
  · rw [hbody]
    exact holdsList_straight aggP [] _ _ hall rfl

end
end LeanVM.Guest.B1.Main
