/-
  LeanVM.Guest.B1.Main.LoopsC

  `main`'s loops under a call relation that unfolds: the iterations' facts with the witness
  carrying calls (the signature checks, the child proof's check) in that relation.
-/

module

public import LeanVM.Guest.B1.Main.Loops
public import LeanVM.Guest.B1.Main.Frames

/-!
# `main`'s loops, under a call relation

G6's knowledge statement names the witnesses as functions of the execution's frames, so `main`'s
soundness is stated for any call relation `C` that **unfolds** (`Unfolds`: a call holds only when
the callee's body does at some valuation, its calls in `C`; `Check.RL` by `relL_iff`,
`coreProgram.Rel` by `rel_iff`) and lies below `coreProgram.Rel` (the deterministic callees'
statements then apply). `loop_stepC`, `loop_soundC`, `guard_soundC` are `loop_stepF`,
`loop_sound`, `guard_sound` under `C`; `RawXStepC`, `RawSStepC`, `KidStepC` keep the signature
checks and the child proof's check in `C`, the other calls in `coreProgram.Rel`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

/-- **A call relation of the program that unfolds**: a call holds only when the callee's body
holds at some valuation of its parameters, its own calls in the same relation. -/
def Unfolds (rd : Reader) (C : CallRel) : Prop :=
  ∀ f args rets, C f args rets → ∃ (fn : Fn) (σ : Val), coreProgram.find? f = some fn ∧
    fn.params.map σ = args ∧ Stmt.HoldsList C rd σ fn.body False (fun rs => rs = rets)

theorem unfolds_rel (rd : Reader) : Unfolds rd (coreProgram.Rel rd) := fun f args rets h => by
  obtain ⟨fn, hf, σ, hp, hb⟩ := (rel_iff coreProgram f args rets).mp h
  exact ⟨fn, σ, hf, hp, hb⟩

/-- A call relation unfolding at a frame map unfolds. -/
theorem unfolds_of_V {rd : Reader} {C : CallRel} {V : FrameMap} (h : UnfoldsV rd C V) :
    Unfolds rd C := fun f args rets hc => by
  obtain ⟨fn, hf, hp, hb⟩ := h f args rets hc
  exact ⟨fn, V f args rets, hf, hp, hb⟩

variable {rd : Reader} {C : CallRel}

/-- `loop_sound` under `C`. -/
theorem loop_soundC {f : String} {ps : List E} {N : E} {m : ℕ} {B : E → Prop}
    (hm : m < ordG) (hN : N = gen ^ m)
    (hstep : ∀ x, C f (x :: ps) [] → B x ∧ (x * gen + N ≠ 0 → C f (x * gen :: ps) []))
    (h : 1 + N ≠ 0 → C f (1 :: ps) []) : ∀ j < m, B (gen ^ j) := by
  have key : ∀ t k, k + t = m → C f (gen ^ k :: ps) [] → ∀ j, k ≤ j → j < m → B (gen ^ j) := by
    intro t
    induction t with
    | zero => intro k hk _ j h1 h2; omega
    | succ t ih =>
      intro k hk hrun j h1 h2
      obtain ⟨hB, hnext⟩ := hstep _ hrun
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · exact hB
      · have hne : gen ^ k * gen + N ≠ 0 := by
          intro he
          rw [gen_pow_add_eq_zero_iff, hN] at he
          have := gen_pow_inj hm (by unfold ordG at hm; omega) he
          omega
        have := hnext hne
        rw [gen_pow_mul_gen] at this
        exact ih (k + 1) (by omega) this j hlt h2
  intro j hj
  have h1 := h (by rw [hN]; exact one_add_gen_pow_ne_zero (by omega) hm)
  rw [← pow_zero gen] at h1
  exact key m 0 (by omega) h1 j (Nat.zero_le j) hj

/-- `guard_sound` under `C`. -/
theorem guard_soundC {σ : Val} {P : List Stmt} {gc : V} {f : String} {one N : V}
    {rest : List V} (h : guardOk P gc f one N rest = true)
    (hall : ∀ s ∈ P, Stmt.Holds C rd σ s True (fun rs => rs = [])) :
    1 + σ N ≠ 0 → C f (1 :: σ N :: rest.map σ) [] := by
  simp only [guardOk, Bool.and_eq_true] at h
  obtain ⟨⟨hc, ha⟩, h1⟩ := h
  have hat := atoms_of_flat hall
  have hcall := callIf_of_flat hall hc
  split at ha
  · rename_i p q hpq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
    obtain ⟨hp1, rfl⟩ := ha
    intro hne
    have hgc : σ gc = 1 + σ q := by rw [addOf_sound hpq hat, const_sound hp1 hat, word_one]
    have := hcall.2 (by rw [hgc]; exact hne)
    rwa [List.map_cons, List.map_cons, const_sound h1 hat, word_one] at this
  · exact absurd ha (by simp)

/-- **A loop helper's body at a valuation**: its counter and other parameters, its block, and,
while `x·g ≠ N`, the call at `x·g`. -/
theorem loop_of_body {f : String} {fn : Fn} (hok : loopShapeF fn f = true) {x : E} {ps : List E}
    {σ : Val} (hp : fn.params.map σ = x :: ps)
    (hb : Stmt.HoldsList C rd σ fn.body False (fun rs => rs = [])) :
    σ (V.n 0) = x ∧ fn.params.tail.map σ = ps ∧
      (∀ s ∈ loopPre fn, Stmt.Holds C rd σ s True (fun rs => rs = [])) ∧
      (x * gen + ps.headD 0 ≠ 0 → C f (x * gen :: ps) []) := by
  simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨h2, hpar⟩, hok⟩ := hok
  unfold loopPre
  split at hok
  · rename_i pre c g args hsl
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨hgf, hlen⟩, htail⟩, hg⟩, hc⟩ := hok
    obtain ⟨hbody, hflat⟩ := splitLoopF_eq hsl
    rw [hbody] at hb
    obtain ⟨hall, -, hcall⟩ := holds_loopBodyF hflat hb
    have hat := atoms_of_flat hall
    have hx0 : σ (V.n 0) = x := by
      have := congrArg List.head? hp
      rw [hpar] at this
      obtain ⟨k, hk⟩ : ∃ k, fn.params.length = k + 2 := ⟨fn.params.length - 2, by omega⟩
      rw [hk, List.range_succ_eq_map] at this
      simpa using this
    have hps : fn.params.tail.map σ = ps := by
      have := congrArg List.tail hp
      rwa [← List.map_tail] at this
    have hN : ps.headD 0 = σ (V.n 1) := by
      rw [← hps, hpar]
      obtain ⟨k, hk⟩ : ∃ k, fn.params.length = k + 2 := ⟨fn.params.length - 2, by omega⟩
      rw [hk, List.range_succ_eq_map, List.range_succ_eq_map]
      simp
    refine ⟨hx0, hps, by simpa [hsl] using hall, fun hne => ?_⟩
    split at hc
    · rename_i p q hpq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hp', rfl⟩ := hc
      have hcv : σ c = x * gen + ps.headD 0 := by
        rw [addOf_sound hpq hat, genMul_sound hp' hat, hx0, hN]
      have := hcall (by rw [hcv]; exact hne)
      have hargs : args.map σ = x * gen :: ps := by
        obtain ⟨a0, rest, rfl⟩ : ∃ a0 rest, args = a0 :: rest := by
          cases args with
          | nil => simp at hlen; omega
          | cons a0 rest => exact ⟨a0, rest, rfl⟩
        simp only [List.headD_cons] at hg
        simp only [List.tail_cons] at htail
        rw [List.map_cons, genMul_sound hg hat, hx0, htail, hps]
      rwa [hargs, hgf] at this
    · exact absurd hc (by simp)
  · exact absurd hok (by simp)

/-- `loop_stepF` under a call relation that unfolds. -/
theorem loop_stepC (hC : Unfolds rd C) {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hok : loopShapeF fn f = true) {x : E} {ps : List E} (h : C f (x :: ps) []) :
    ∃ σ : Val, σ (V.n 0) = x ∧ fn.params.tail.map σ = ps ∧
      (∀ s ∈ loopPre fn, Stmt.Holds C rd σ s True (fun rs => rs = [])) ∧
      (x * gen + ps.headD 0 ≠ 0 → C f (x * gen :: ps) []) := by
  obtain ⟨fn', σ, hf', hp, hb⟩ := hC _ _ _ h
  rw [hf] at hf'
  cases hf'
  exact ⟨σ, loop_of_body hok hp hb⟩

/-- **`loop_stepF` at the frame map's valuation** `Vm f (x :: ps) []`. -/
theorem loop_stepV {Vm : FrameMap} (hVm : UnfoldsV rd C Vm) {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) (hok : loopShapeF fn f = true) {x : E} {ps : List E}
    (h : C f (x :: ps) []) :
    Vm f (x :: ps) [] (V.n 0) = x ∧ fn.params.tail.map (Vm f (x :: ps) []) = ps ∧
      (∀ s ∈ loopPre fn, Stmt.Holds C rd (Vm f (x :: ps) []) s True (fun rs => rs = [])) ∧
      (x * gen + ps.headD 0 ≠ 0 → C f (x * gen :: ps) []) := by
  obtain ⟨fn', hf', hp, hb⟩ := hVm _ _ _ h
  rw [hf] at hf'
  cases hf'
  exact loop_of_body hok hp hb

/-- **The body of a called function at the frame map's valuation.** -/
theorem body_ofV {Vm : FrameMap} (hVm : UnfoldsV rd C Vm) {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) {args rets : List E} (h : C f args rets) :
    fn.params.map (Vm f args rets) = args ∧
      Stmt.HoldsList C rd (Vm f args rets) fn.body False (fun rs => rs = rets) := by
  obtain ⟨fn', hf', hp, hb⟩ := hVm _ _ _ h
  rw [hf] at hf'
  cases hf'
  exact ⟨hp, hb⟩

/-! ## The callees' contracts -/

/-- **The callees' contracts with witness functions**, on the calls of `C`. -/
structure CalleesWC (bytecode : List K) (C : CallRel) (rd : Reader) (bb0 : E)
    (wX : E → LeanXmss.Signature) (wS : E → Sphincs.Signature) (wD : List E → List E → LeanVM.Da.MatrixWitness)
    (wV : List E → Proof) (wA : List E → BatchingHints) : Prop where
  /-- A leanXMSS check: the signature `wX p` verifies the claim at `p`. -/
  xmss : ∀ p, C "verify_lean_xmss" [p] [] → Sig.XmssOut rd p (wX p)
  /-- A leanSPHINCS check with the byte table `bb0` (`main`'s): the signature `wS p` verifies the
  claim at `p`. -/
  sphincs : ∀ p, C "verify_sig_lean_sphincs" [p, bb0] [] →
    Sig.ByteBits rd bb0 → Sig.SphincsOut rd p (wS p)
  /-- The DA check with the exponent table: the matrix `wD args rets` opens the returned claim. -/
  da : ∀ gsq rets, C "da_verify" [gsq] rets → Da.SquaresAt rd gsq →
    ∃ root vd : Digest, (wD [gsq] rets).Opens root vd ∧ rets = digestCells root ++ digestCells vd
  /-- A child proof's check with the exponent tables: the proof `wV args`. -/
  sub : ∀ pi0 pi1 s0 s1 glp gsq out,
    C "verify_sub" [pi0, pi1, s0, s1, glp, gsq, out] [] → ExpTables rd glp gsq →
    VerifySubOut bytecode rd [pi0, pi1, s0, s1, glp, gsq, out] (wV [pi0, pi1, s0, s1, glp, gsq, out])
  /-- The batching, for `n_children_g = g^m`, `1 ≤ m ≤ 16`, with the hints `wA args`. -/
  agg : ∀ ncg cpi cfresh ccarried dst, C "aggregate_claims"
    [ncg, cpi, cfresh, ccarried, dst] [] → ∀ m, 1 ≤ m → m ≤ 16 → ncg = gen ^ m →
      ∃ out : DeferredClaim, out.bytecodePoint.length = bytecodeVars ∧ ReadsAt rd dst out.cells ∧
        ∀ cs : List ChildClaims, cs.length = m →
          (∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c]) →
          batch cs (wA [ncg, cpi, cfresh, ccarried, dst]) = some out

/-! ## The iterations -/

/-- **A raw leanXMSS signature** at the counter `x`: a slot `s` below the region's bound holding
the mark `x`, and the signature check of the claim at slot `s`. -/
def RawXStepC (C : CallRel) (rd : Reader) (lxs cover lxt x : E) : Prop :=
  ∃ s, BelowLog lxs s ∧ LoadHolds rd cover s x ∧
    C "verify_lean_xmss" [lxt * gen ^ (4 * s)] []

theorem l3_stepC {rd : Reader} {C : CallRel} (hC : Unfolds rd C) (hm : MemOk rd) {x : E} {ps : List E}
    (h : C "__loop2" (x :: ps) []) :
    (∀ N lxs cover lxt, ps = [N, lxs, cover, lxt] → RawXStepC C rd lxs cover lxt x) ∧
      (x * gen + ps.headD 0 ≠ 0 → C "__loop2" (x * gen :: ps) []) := by
  have hf := find_of_idx l3_idx (by rw [coreProgram_length]; omega)
  have hok := l3_ok
  simp only [l3Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hrc⟩, hm11⟩, hl⟩, hm14⟩, hcall⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ := loop_stepC hC hf hshape h
  refine ⟨fun N lxs cover lxt hN => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD 32 default).params = [V.n 0, V.n 1, V.n 2, V.n 3, V.n 4] := by
    have hs := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, hlxs, hcover, hlxt⟩ := hps
  obtain ⟨s, hs, hbl⟩ := rcBound_sound hm hrc hat
  refine ⟨s, by rwa [← hlxs], ?_, ?_⟩
  · have := load_sound hl hat
    rw [isMul_sound hm11 hat, hs, hcover, hx] at this
    simpa using (loadHolds_mul_gen_pow rd _ s 0 _).mp this
  · have := call_of_flat hall hcall
    rwa [List.map_cons, List.map_nil, monoIs_sound hm14 hat, hs, hlxt, ← pow_mul, mul_comm s 4]
      at this


/-- **A raw leanSPHINCS signature** at the counter `x`: a slot `s` below the region's bound
holding the mark `n_raw_x · x` (at `cover · lx_slots · g^s`), and the signature check of the
claim at slot `s`. -/
def RawSStepC (C : CallRel) (rd : Reader) (lss cover lxs nrx lst bb x : E) : Prop :=
  ∃ s, BelowLog lss s ∧ LoadHolds rd (cover * (lxs * gen ^ s)) 0 (nrx * x) ∧
    C "verify_sig_lean_sphincs" [lst * gen ^ (4 * s), bb] []

theorem l4_stepC {rd : Reader} {C : CallRel} (hC : Unfolds rd C) (hm : MemOk rd) {x : E} {ps : List E}
    (h : C "__loop3" (x :: ps) []) :
    (∀ N lss cover lxs nrx lst bb, ps = [N, lss, cover, lxs, nrx, lst, bb] →
      RawSStepC C rd lss cover lxs nrx lst bb x) ∧
      (x * gen + ps.headD 0 ≠ 0 → C "__loop3" (x * gen :: ps) []) := by
  have hf := find_of_idx l4_idx (by rw [coreProgram_length]; omega)
  have hok := l4_ok
  simp only [l4Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hrc⟩, hm14⟩, hm15⟩, hm16⟩, hl⟩, hm19⟩, hcall⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ := loop_stepC hC hf hshape h
  refine ⟨fun N lss cover lxs nrx lst bb hN => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD 33 default).params =
      [V.n 0, V.n 1, V.n 2, V.n 3, V.n 4, V.n 5, V.n 6, V.n 7] := by
    have hs := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, hlss, hcover, hlxs, hnrx, hlst, hbb⟩ := hps
  obtain ⟨s, hs, hbl⟩ := rcBound_sound hm hrc hat
  refine ⟨s, by rwa [← hlss], ?_, ?_⟩
  · have := load_sound hl hat
    rw [isMul_sound hm16 hat, isMul_sound hm15 hat, isMul_sound hm14 hat, hs, hcover, hlxs, hnrx,
      hx] at this
    exact this
  · have := call_of_flat hall hcall
    rwa [List.map_cons, List.map_cons, List.map_nil, monoIs_sound hm19 hat, hs, hlst, hbb,
      ← pow_mul, mul_comm s 4] at this


/-- **Child `x`'s facts**: its base `written[x]`, its counts `g^ex`, `g^es`, its two rebuilt claim
lists' digests, its DA digest's cells at `da_digests · x^2`, its statement's digest at
`child_pi · x^2`, its proof's check (in `C`), and `written[x · g] = base · g^(ex + es)`. -/
def KidStepC (C : CallRel) (rd : Reader) (written lxt cover lxs lst lss carried dadig s0 s1 cpi glp
    gsq cfresh x : E) : Prop :=
  ∃ (base cx0 cx1 cs0 cs1 d0 d1 p0 p1 : E) (ex es : ℕ),
    LoadHolds rd (written * x) 0 base ∧ ex ≤ 65535 ∧ es ≤ 65535 ∧
    coreProgram.Rel rd "child_claim_list_digest" [lxt, cover, base, 1, lxs, gen ^ ex] [cx0, cx1] ∧
    coreProgram.Rel rd "child_claim_list_digest" [lst, cover, base * gen ^ ex, lxs, lss, gen ^ es]
      [cs0, cs1] ∧
    LoadHolds rd (dadig * x ^ 2) 0 d0 ∧ LoadHolds rd (dadig * x ^ 2) 1 d1 ∧
    coreProgram.Rel rd "statement_digest" [s0, s1, cx0, cx1, cs0, cs1, d0, d1, carried * x ^ 24]
      [p0, p1] ∧
    LoadHolds rd (cpi * x ^ 2) 0 p0 ∧ LoadHolds rd (cpi * x ^ 2) 1 p1 ∧
    C "verify_sub" [p0, p1, s0, s1, glp, gsq, cfresh * x ^ 24] [] ∧
    LoadHolds rd (written * x) 1 (base * (gen ^ ex * gen ^ es))

theorem l5_stepC {rd : Reader} {C : CallRel} (hC : Unfolds rd C)
    (hle : CallRel.Le C (coreProgram.Rel rd)) (hm : MemOk rd) {x : E} {ps : List E}
    (h : C "__loop4" (x :: ps) []) :
    (∀ N written lxt cover lxs lst lss carried dadig s0 s1 cpi glp gsq cfresh,
      ps = [N, written, lxt, cover, lxs, lst, lss, carried, dadig, s0, s1, cpi, glp, gsq,
        cfresh] →
      KidStepC C rd written lxt cover lxs lst lss carried dadig s0 s1 cpi glp gsq cfresh x) ∧
      (x * gen + ps.headD 0 ≠ 0 → C "__loop4" (x * gen :: ps) []) := by
  have hf := find_of_idx l5_idx (by rw [coreProgram_length]; omega)
  have hok := l5_ok
  simp only [l5Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hm16⟩, hl17⟩, hrc18⟩, hrc19⟩, hm28⟩, hc29⟩, hcx⟩, hm32⟩, hcs⟩, hm40⟩, hm42⟩, hl43⟩, hl44⟩, hsd⟩, hm48⟩, hl45⟩, hm49⟩, hl46⟩, hm55⟩, hvs⟩, hm56⟩, hm57⟩, hl56⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ := loop_stepC hC hf hshape h
  refine ⟨fun N written lxt cover lxs lst lss carried dadig s0 s1 cpi glp gsq cfresh hN
    => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD 34 default).params = (List.range 16).map V.n := by
    have hs := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen]
  rw [hpar, hN] at hps
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, List.tail_cons, List.cons.injEq, and_true] at hps
  obtain ⟨-, hwr, hlxt, hcov, hlxs, hlst, hlss, hcar, hdad, hs0, hs1, hcpi, hglp, hgsq,
    hcf⟩ := hps
  obtain ⟨ex, hex, hnx⟩ := rcConst_sound hm (by norm_num) word_gmax hrc18 hat
  obtain ⟨es, hes, hns⟩ := rcConst_sound hm (by norm_num) word_gmax hrc19 hat
  have h29 : σ (.n 29) = 1 := by rw [const_sound hc29 hat, word_one]
  have h16 : σ (.n 16) = written * x := by rw [isMul_sound hm16 hat, hwr, hx]
  have h28 : σ (.n 28) = gen ^ ex * gen ^ es := by rw [isMul_sound hm28 hat, hnx, hns]
  refine ⟨σ (.n 17), σ (.n 30), σ (.n 31), σ (.n 33), σ (.n 34), σ (.n 43), σ (.n 44),
    σ (.n 45), σ (.n 46), ex, es, ?_, hex, hes, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := load_sound hl17 hat; rwa [h16] at this
  · have := hle _ _ _ (call_of_flat hall hcx)
    simpa [h29, hlxt, hcov, hlxs, hnx] using this
  · have := hle _ _ _ (call_of_flat hall hcs)
    simpa [isMul_sound hm32 hat, hlst, hcov, hlxs, hlss, hnx, hns] using this
  · have := load_sound hl43 hat; rwa [monoIs_sound hm42 hat, hdad, hx] at this
  · have := load_sound hl44 hat; rwa [monoIs_sound hm42 hat, hdad, hx] at this
  · have := hle _ _ _ (call_of_flat hall hsd)
    simpa [monoIs_sound hm40 hat, hs0, hs1, hcar, hx] using this
  · have := load_sound hl45 hat; rwa [monoIs_sound hm48 hat, hcpi, hx] at this
  · have := load_sound hl46 hat; rwa [monoIs_sound hm49 hat, hcpi, hx] at this
  · have := call_of_flat hall hvs
    simpa [monoIs_sound hm55 hat, hs0, hs1, hglp, hgsq, hcf, hx] using this
  · have := load_sound hl56 hat
    rwa [isMul_sound hm57 hat, isMul_sound hm56 hat, h28, hwr, hx] at this

end
end LeanVM.Guest.B1.Main
