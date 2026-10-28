/-
  LeanVM.Guest.B1.VerifySub.H.Sigma

  `verify_sub`'s honest valuation on an honest child: its parameters, pointers, the callees'
  results, and the values its calls pass (the batched target among them).
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Outs
public import LeanVM.Guest.B1.VerifySub.H.Sec

/-!
# The honest valuation

`ChildSegs.vals_length`: the GKR's three values. `ChildSegs.target_eq`: the opening's target is the
batch `verify_sub` computes at `1886`. `VsSig`: what the honest valuation holds;
`vs_sig`: it holds, with the section data `vsCPre_complete` takes.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- The GKR's three values. -/
theorem vals_length (hbl : bytecode.length = 2 ^ 23) : S.vals.length = 3 := by
  obtain ⟨hrun, -, -, -⟩ := S.runG' hbl
  obtain ⟨sp, hsp⟩ := S.capS_carries
  have hsc : capOf sp.state = S.capS := hsp.1
  have hcl : S.capS.length = 5 := S.capS_length
  have hcan : AllCanonical S.capS := by rw [← hsc]; exact Tables.tb_capOf_canonical _
  obtain ⟨-, -, -, -, -, -, hr, -⟩ := Tables.gk_walk hrun ⟨sp, hsp⟩
  show S.rG.2.2.length = 3
  rw [hr]
  exact (Tables.gkSl_inv hcl hcan _).2.2.2

/-- The bus challenges. -/
theorem alphas_length : S.alphas.length = 4 := by
  have e := congrArg (fun p ↦ p.1.length) S.halphas
  simp only [squeezeN_len] at e
  rw [← e]; rfl

/-- **The opening's target** is the batch `verify_sub` computes. -/
theorem target_eq (hbl : bytecode.length = 2 ^ 23) :
    S.target = polyEval (S.slices.map (phiMap · S.rchs)) gen +
      ∑ i ∈ Finset.range 140, S.lam ^ (i + 1) * S.H.poolW.getD (vsKept i) 0 +
        S.lam ^ 141 * S.word := by
  have hok := (S.H_run hbl).1
  have hr : S.H.rows.length = 6 := S.hrowsL
  have hk := kept_values (Tables.VtHonest.vtH_columns hok hr)
  rw [Tables.VtHonest.vtH_values hok hr, S.H_claims] at hk
  have hn : (notLanes S.claims).length = 140 := by
    have := congrArg List.length hk
    simpa [notLanes] using this
  unfold ChildSegs.target batchTarget
  rw [S.km_eq hbl]
  dsimp only
  have hv : (stackClaims S.layout S.claims [⟨qkeccak, S.op, S.word⟩] S.kpt S.slices
      (S.m0 :: S.chs)).map (·.2) =
      polyEval (S.slices.map (phiMap · (S.m0 :: S.chs))) gen ::
        ((notLanes S.claims).map (·.value) ++ [S.word]) := by
    simp [stackClaims, ringSwitchClaim, ColumnClaim.onStack, notLanes]
  have hl : (stackClaims S.layout S.claims [⟨qkeccak, S.op, S.word⟩] S.kpt S.slices
      (S.m0 :: S.chs)).length = 140 + 2 := by
    rw [← hn]; simp [stackClaims, notLanes]
  rw [show (notLanes S.claims).map (·.value) = _ from hk] at hv
  rw [hl, hv, dot_powers_batch]
  rfl

end ChildSegs

/-- **What the honest valuation holds.** -/
structure VsSig {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)
    (bs : List ℕ) (sqE : ℕ) (outs : List (List E × Main.Layout)) (args : List E) (σ : Val) :
    Prop where
  par : ∀ i < 7, σ (.n i) = args.getD i 0
  ptr : ∀ i < 16, σ (.n (vsAllocVars.getD i 0)) = ofK (gpow (vb bs i))
  ret : ∀ j < 13, ∀ k < (vsRetVars.getD j []).length,
    σ (.n ((vsRetVars.getD j []).getD k 0)) = (outs.getD j ([], [])).1.getD k 0
  e112 : σ (.n 112) = eOfNat S.rate
  e29 : σ (.n 29) = eOfNat S.logMem
  e521 : σ (.n 521) = gen ^ pushTotal S.logMem S.hs
  e537 : σ (.n 537) = S.x0
  e547 : σ (.n 547) = S.x1
  e825 : [σ (.n 825), σ (.n 826), σ (.n 827), σ (.n 828), σ (.n 829)] = S.capS
  e836 : σ (.n 836) = S.β
  e838 : σ (.n 838) = ofK (gpow (vcG bs))
  e858 : σ (.n 858) = gen ^ S.τ
  e862 : σ (.n 862) = ofK (gpow (vb bs 0 + 110))
  e1312 : [σ (.n 1312), σ (.n 1313), σ (.n 1314), σ (.n 1315), σ (.n 1316)] = capOf S.s8.perm
  e1884 : σ (.n 1884) = S.lam ^ 141
  e1886 : σ (.n 1886) = S.target
  e1901 : σ (.n 1901) = gen ^ B1.Whir.candidate S.μs S.rate
  push : ∀ b < 54, ∃ k < 34, σ (.n (vsPushPtr b)) = ofK (gpow (sqE + k))

variable {rd : Reader} {args : List E}

set_option maxHeartbeats 1000000 in
/-- **The honest valuation holds `VsSig`**, with the section data. -/
theorem vs_sig {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest} {c : Child}
    (S : ChildSegs bytecode seed c) {lpE sqE outE : ℕ}
    (hargs : args = [(digestScalars (statementDigest seed c.statement)).1,
      (digestScalars (statementDigest seed c.statement)).2, (digestScalars seed).1,
      (digestScalars seed).2, ofK (gpow lpE), ofK (gpow sqE), ofK (gpow outE)])
    (bs : List ℕ) (outs : List (List E × Main.Layout)) (O : VsOuts S bs lpE sqE outs) {κ : ℕ}
    (hκ : 16 ≤ κ) (hlow : LowDef κ rd)
    (hmem : ∀ i < 16, ReadsAt rd (ofK (gpow (bs.getD i 0))) (S.ownW.getD i []))
    (hlp : ReadsAt rd (ofK (gpow lpE)) ((List.range 34).map fun j ↦ eOfNat (2 ^ j)))
    (hsq : ReadsAt rd (ofK (gpow sqE)) Tables.gSquaresList)
    (hfx : ReadsAt rd (ofK (gpow outE)) (DeferredClaim.cells c.fresh)) :
    Nonempty (VsSecData rd (vsW bs outs) args) ∧
      VsSig S bs sqE outs args (vsσ rd (vsW bs outs) args) := by
  have hl : args.length = 7 := by rw [hargs]; rfl
  obtain ⟨D, hv, hlir, hlm, hhs, hm, hr, hτ, F, elam, es8, -, -⟩ :=
    vsSec hbl S hargs bs outs hκ hlow hmem hlp hsq hfx O.o0 O.o1 O.o6 O.o7 O.o10
  refine ⟨⟨D⟩, ?_⟩
  have par := fun i (hi : i < 7) ↦ vsC_param (rd := rd) (w := vsW bs outs) hl hi
  have ptr := fun i (hi : i < 16) ↦ vs_alloc_ptr (rd := rd) hl bs outs hi
  have ret := fun j (hj : j < 13) k (hk : k < (vsRetVars.getD j []).length) ↦
    vs_ret_val (rd := rd) hl bs outs hj hk
  have e112 := D.e112
  have e29 := D.e29
  rw [hlir] at e112
  rw [hlm] at e29
  have hpush := (vsPushT_complete (C := fun _ _ _ ↦ True) (next := True) (kret := fun _ ↦ True) hl
    D.hsl D.hh D.hm32 D.hbk D.hexp (fun _ _ ↦ trivial) trivial).1
  rw [hlm, hhs] at hpush
  have hpp : ∀ b < 54, vsσ rd (vsW bs outs) args (.n (vsPushPtr b)) =
      vsσ rd (vsW bs outs) args (.n 5) * gen ^ pushKappa D.logMem D.hs b :=
    fun b hb ↦ vs_push_ptr hl D.hsl D.hbk hb
  have hpk : ∀ b < 54, pushKappa D.logMem D.hs b < 34 := fun b hb ↦ pushKappa_lt D.hh D.hm32 hb
  have hcalls := vsCallsT_complete (C := fun _ _ _ ↦ True) (next := True) (kret := fun _ ↦ True) hl
    D.hd6 trivial trivial trivial trivial
  rw [hτ] at hcalls
  have hlam := vsLamT_complete (C := fun _ _ _ ↦ True) (next := True) (kret := fun _ ↦ True) hl
    D.hz D.hcap966 D.hpool D.hlam trivial
  rw [hv] at hlam
  have htail := (vsTailPre_complete (C := fun _ _ _ ↦ True) (next := True) (kret := fun _ ↦ True)
    hl D.hκ6 D.hlow D.hm22 D.hm28 D.hr1 D.hr4 D.e1890 D.e124 D.hzeta D.halpha D.hout D.hout'
    D.hout23 trivial trivial trivial trivial trivial).1
  rw [hm, hr] at htail
  have hL := vsH_lam (rd := rd) (w := vsW bs outs) hl D.hcap966
  obtain ⟨K7, hK7⟩ := S.s7_capOf hbl
  generalize vsσ rd (vsW bs outs) args = σ at *
  have p7 : σ (.n 7) = ofK (gpow (vb bs 0)) := ptr 0 (by norm_num)
  have p27 : σ (.n 27) = ofK (gpow (vb bs 2)) := ptr 2 (by norm_num)
  have e5 : σ (.n 5) = ofK (gpow sqE) := by rw [par 5 (by norm_num), hargs]; rfl
  have e1303 : σ (.n 1303) = polyEval (S.slices.map (phiMap · S.rchs)) gen := by
    have := ret 8 (by norm_num) 0 (by decide); rw [O.o8] at this; exact this
  have e869 : σ (.n 869) = S.word := by
    have := ret 7 (by norm_num) 6 (by decide); rw [O.o7, hK7] at this; exact this
  rw [← es8] at hL
  exact {
    par := par
    ptr := ptr
    ret := ret
    e112 := e112
    e29 := e29
    e521 := hpush
    e537 := F.h537
    e547 := F.h547
    e825 := (congrArg Fs.cap F.hs4).symm
    e836 := F.hβ
    e838 := by rw [hcalls.1, p27, Tables.tb_ofK_gpow_mul]; rfl
    e858 := hcalls.2.1
    e862 := by rw [hcalls.2.2.1, p7, Tables.tb_ofK_gpow_mul]
    e1312 := (congrArg (fun p ↦ p.2.cap) hL).symm
    e1884 := by rw [hlam.1, elam]
    e1886 := by rw [hlam.2.1, elam, e1303, e869, S.target_eq hbl]
    e1901 := htail
    push := fun b hb ↦ ⟨_, hpk b hb, by rw [hpp b hb, e5, Tables.tb_ofK_gpow_mul]⟩ }

end
end LeanVM.Guest.B1.VerifySub
