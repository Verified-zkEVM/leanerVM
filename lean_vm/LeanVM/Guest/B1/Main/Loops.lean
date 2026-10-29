/-
  LeanVM.Guest.B1.Main.Loops

  B1 for `main`'s loop helpers: the raw signatures (`__loop2`, `__loop3`) and the children
  (`__loop4`), each body checked by evaluation.
-/

module

public import LeanVM.Guest.B1.Main.Basic
public import LeanVM.Guest.B1.Digest.Loops

/-!
# `main`'s loops

Each helper's body (`loopPre`) is checked by evaluation (`l3Ok`, `l4Ok`, `l5Ok`), and its run at
`x` gives one iteration's facts (`RawXStep`, `RawSStep`, `KidStep`) and the run at `x·g`
(`loop_stepF`).

* `__loop2` (G:4193-4202): a raw leanXMSS signature `i`: a slot `s` below the leanXMSS region,
  `cover[g^s] = g^i`, `verify_lean_xmss(lx_table · g^(4s))`;
* `__loop3` (G:4203-4207): a raw leanSPHINCS signature `j`: a slot `s` below the leanSPHINCS
  region, `cover[lx_slots · g^s] = n_raw_x · g^j`, `verify_sig_lean_sphincs(ls_table · g^(4s), byte_bits)`;
* `__loop4` (G:4180-4206): child `c`, its DA digest hinted at `da_digests · c^2`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

/-! ## Shared -/

/-- `P` holds the call `.call f args rets`. -/
def hasCall (P : List Stmt) (f : String) (args rets : List V) : Bool :=
  P.any (stmtEqb · (.call f args rets))

/-- `x = y · z`, by the first `MUL` into `x`. -/
def isMul (atoms : List Atom) (x y z : V) : Bool := decide (mulOf atoms x = some (y, z))

theorem isMul_sound {rd : Reader} {σ : Val} {atoms : List Atom} {x y z : V}
    (h : isMul atoms x y z = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) : σ x = σ y * σ z :=
  mulOf_sound (of_decide_eq_true h) hat

/-- **A guarded loop call** in a block: `callIf (1 + N) f [1, N, rest…]`, the two `1`s
constants. -/
def guardOk (P : List Stmt) (gc : V) (f : String) (one N : V) (rest : List V) : Bool :=
  P.any (stmtEqb · (.callIf gc f (one :: N :: rest))) &&
    (match addOf (atomsIn P) gc with
     | some (p, q) => (atomsIn P).any (isConstAt p 1 0) && decide (q = N)
     | none => false) &&
    (atomsIn P).any (isConstAt one 1 0)

theorem guard_sound {rd : Reader} {σ : Val} {P : List Stmt} {gc : V} {f : String} {one N : V}
    {rest : List V} (h : guardOk P gc f one N rest = true)
    (hall : ∀ s ∈ P, Stmt.Holds (coreProgram.Rel rd) rd σ s True (fun rs => rs = [])) :
    1 + σ N ≠ 0 → coreProgram.Rel rd f (1 :: σ N :: rest.map σ) [] := by
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

/-! ## `__loop2`: raw leanXMSS signatures -/

def l3Ok (fn : Fn) : Bool :=
  loopShapeF fn "__loop2" && decide (fn.params.length = 5) &&
    rcBoundOk (atomsIn (loopPre fn)) (.n 5) (.n 2) && isMul (atomsIn (loopPre fn)) (.n 11) (.n 3) (.n 5) &&
    (atomsIn (loopPre fn)).any (isLoadAt (.n 0) (.n 11) 0) &&
    monoIs (atomsIn (loopPre fn)) (.n 14) (.n 4) (.n 5) 4 &&
    hasCall (loopPre fn) "verify_lean_xmss" [.n 14] []

set_option maxRecDepth 100000 in
theorem l3_ok : l3Ok (coreProgram.getD 32 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l3_idx : coreProgram.indexOf? "__loop2" = some 32 := by decide +kernel

/-- **A raw leanXMSS signature** at the counter `x`: a slot `s` below the region's bound holding
the mark `x`, and the signature check of the claim at slot `s`. -/
def RawXStep (rd : Reader) (lxs cover lxt x : E) : Prop :=
  ∃ s, BelowLog lxs s ∧ LoadHolds rd cover s x ∧
    coreProgram.Rel rd "verify_lean_xmss" [lxt * gen ^ (4 * s)] []

theorem l3_step {rd : Reader} (hm : MemOk rd) {x : E} {ps : List E}
    (h : coreProgram.Rel rd "__loop2" (x :: ps) []) :
    (∀ N lxs cover lxt, ps = [N, lxs, cover, lxt] → RawXStep rd lxs cover lxt x) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd "__loop2" (x * gen :: ps) []) := by
  have hf := find_of_idx l3_idx (by rw [coreProgram_length]; omega)
  have hok := l3_ok
  simp only [l3Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hrc⟩, hm11⟩, hl⟩, hm14⟩, hcall⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ := loop_stepF hf hshape h
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

/-! ## `__loop3`: raw leanSPHINCS signatures -/

def l4Ok (fn : Fn) : Bool :=
  loopShapeF fn "__loop3" && decide (fn.params.length = 8) &&
    rcBoundOk (atomsIn (loopPre fn)) (.n 8) (.n 2) &&
    isMul (atomsIn (loopPre fn)) (.n 14) (.n 5) (.n 0) &&
    isMul (atomsIn (loopPre fn)) (.n 15) (.n 4) (.n 8) &&
    isMul (atomsIn (loopPre fn)) (.n 16) (.n 3) (.n 15) &&
    (atomsIn (loopPre fn)).any (isLoadAt (.n 14) (.n 16) 0) &&
    monoIs (atomsIn (loopPre fn)) (.n 19) (.n 6) (.n 8) 4 &&
    hasCall (loopPre fn) "verify_sig_lean_sphincs" [.n 19, .n 7] []

set_option maxRecDepth 100000 in
theorem l4_ok : l4Ok (coreProgram.getD 33 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l4_idx : coreProgram.indexOf? "__loop3" = some 33 := by decide +kernel

/-- **A raw leanSPHINCS signature** at the counter `x`: a slot `s` below the region's bound
holding the mark `n_raw_x · x` (at `cover · lx_slots · g^s`), and the signature check of the
claim at slot `s`. -/
def RawSStep (rd : Reader) (lss cover lxs nrx lst bb x : E) : Prop :=
  ∃ s, BelowLog lss s ∧ LoadHolds rd (cover * (lxs * gen ^ s)) 0 (nrx * x) ∧
    coreProgram.Rel rd "verify_sig_lean_sphincs" [lst * gen ^ (4 * s), bb] []

theorem l4_step {rd : Reader} (hm : MemOk rd) {x : E} {ps : List E}
    (h : coreProgram.Rel rd "__loop3" (x :: ps) []) :
    (∀ N lss cover lxs nrx lst bb, ps = [N, lss, cover, lxs, nrx, lst, bb] →
      RawSStep rd lss cover lxs nrx lst bb x) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd "__loop3" (x * gen :: ps) []) := by
  have hf := find_of_idx l4_idx (by rw [coreProgram_length]; omega)
  have hok := l4_ok
  simp only [l4Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hrc⟩, hm14⟩, hm15⟩, hm16⟩, hl⟩, hm19⟩, hcall⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ := loop_stepF hf hshape h
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

/-! ## A two-digest hash in a block -/

/-- The chain of `keccak([a, b], [c, d], out)`: four cells, `64` bytes, from the zero state. -/
def pairSpec (a b c d : V) (atoms : List Atom) : ChainSpec :=
  ⟨[some a, some b, some c, some d], 64, true, none, keccakBlocks atoms⟩

/-- `keccak([a, b], [c, d], out)` with the digest's two cells loaded into `p[0]`, `p[1]`. -/
def pairHashOk (atoms : List Atom) (a b c d p : V) : Bool :=
  (pairSpec a b c d atoms).check atoms &&
    atoms.any (isLoadAt ((pairSpec a b c d atoms).outV ((pairSpec a b c d atoms).nb - 1) 0) p 0) &&
    atoms.any (isLoadAt ((pairSpec a b c d atoms).outV ((pairSpec a b c d atoms).nb - 1) 1) p 1)

theorem pairHash_sound {rd : Reader} {σ : Val} {atoms : List Atom} {a b c d p : V}
    (h : pairHashOk atoms a b c d p = true) (hat : ∀ x ∈ atoms, x.Holds rd σ) :
    AllCanonical [σ a, σ b, σ c, σ d] ∧
      LoadHolds rd (σ p) 0 (digestScalars (keccak256 (cellsBytes [σ a, σ b, σ c, σ d]))).1 ∧
      LoadHolds rd (σ p) 1 (digestScalars (keccak256 (cellsBytes [σ a, σ b, σ c, σ d]))).2 := by
  simp only [pairHashOk, Bool.and_eq_true] at h
  obtain ⟨⟨hc, h0⟩, h1⟩ := h
  obtain ⟨hd, hcan⟩ := chain_final hc rfl hat (pre := []) (n := 0) rfl
    (fun c => (cellsOfState_zero false c).symm)
  have hv : ((pairSpec a b c d atoms).vals σ).take ((pairSpec a b c d atoms).len / 16) =
      [σ a, σ b, σ c, σ d] := by simp [pairSpec, ChainSpec.vals, srcVal]
  rw [hv, List.nil_append] at hd
  rw [hv] at hcan
  refine ⟨hcan, ?_, ?_⟩
  · have := load_sound h0 hat
    rw [show ((pairSpec a b c d atoms).outV ((pairSpec a b c d atoms).nb - 1) 0) =
      ((pairSpec a b c d atoms).outV ((pairSpec a b c d atoms).nb - 1) ((0 : Fin 13) : ℕ)) from rfl]
      at this
    rw [← hd]; exact this
  · have := load_sound h1 hat
    rw [show ((pairSpec a b c d atoms).outV ((pairSpec a b c d atoms).nb - 1) 1) =
      ((pairSpec a b c d atoms).outV ((pairSpec a b c d atoms).nb - 1) ((1 : Fin 13) : ℕ)) from rfl]
      at this
    rw [← hd]; exact this

/-! ## `__loop4`: the children -/

def isLoad (atoms : List Atom) (x p : V) (o : ℕ) : Bool := atoms.any (isLoadAt x p o)

def l5Ok (fn : Fn) : Bool :=
  let P := loopPre fn
  let A := atomsIn P
  loopShapeF fn "__loop4" &&
  decide (fn.params.length = 16) &&
  isMul A (.n 16) (.n 2) (.n 0) &&
  isLoad A (.n 17) (.n 16) 0 &&
  rcConstOk A (.n 18) 9272771591053052074 &&
  rcConstOk A (.n 19) 9272771591053052074 &&
  isMul A (.n 28) (.n 18) (.n 19) &&
  A.any (isConstAt (.n 29) 1 0) &&
  hasCall P "child_claim_list_digest" [.n 3, .n 4, .n 17, .n 29, .n 5, .n 18] [.n 30, .n 31] &&
  isMul A (.n 32) (.n 17) (.n 18) &&
  hasCall P "child_claim_list_digest" [.n 6, .n 4, .n 32, .n 5, .n 7, .n 19] [.n 33, .n 34] &&
  monoIs A (.n 40) (.n 8) (.n 0) 24 &&
  monoIs A (.n 42) (.n 9) (.n 0) 2 &&
  isLoad A (.n 43) (.n 42) 0 &&
  isLoad A (.n 44) (.n 42) 1 &&
  hasCall P "statement_digest" [.n 10, .n 11, .n 30, .n 31, .n 33, .n 34, .n 43, .n 44, .n 40]
    [.n 45, .n 46] &&
  monoIs A (.n 48) (.n 12) (.n 0) 2 &&
  isLoad A (.n 45) (.n 48) 0 &&
  monoIs A (.n 49) (.n 12) (.n 0) 2 &&
  isLoad A (.n 46) (.n 49) 1 &&
  monoIs A (.n 55) (.n 15) (.n 0) 24 &&
  hasCall P "verify_sub" [.n 45, .n 46, .n 10, .n 11, .n 13, .n 14, .n 55] [] &&
  isMul A (.n 56) (.n 17) (.n 28) &&
  isMul A (.n 57) (.n 2) (.n 0) &&
  isLoad A (.n 56) (.n 57) 1

set_option maxRecDepth 100000 in
theorem l5_ok : l5Ok (coreProgram.getD 34 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l5_idx : coreProgram.indexOf? "__loop4" = some 34 := by decide +kernel

/-- **Child `x`'s facts**: its base `written[x]`, its counts `g^ex`, `g^es`, its two rebuilt claim
lists' digests, its DA digest's cells at `da_digests · x^2`, its statement's digest at
`child_pi · x^2`, its proof's check, and `written[x · g] = base · g^(ex + es)`. -/
def KidStep (rd : Reader) (written lxt cover lxs lst lss carried dadig s0 s1 cpi glp gsq cfresh
    x : E) : Prop :=
  ∃ (base cx0 cx1 cs0 cs1 d0 d1 p0 p1 : E) (ex es : ℕ),
    LoadHolds rd (written * x) 0 base ∧ ex ≤ 65535 ∧ es ≤ 65535 ∧
    coreProgram.Rel rd "child_claim_list_digest" [lxt, cover, base, 1, lxs, gen ^ ex] [cx0, cx1] ∧
    coreProgram.Rel rd "child_claim_list_digest" [lst, cover, base * gen ^ ex, lxs, lss, gen ^ es]
      [cs0, cs1] ∧
    LoadHolds rd (dadig * x ^ 2) 0 d0 ∧ LoadHolds rd (dadig * x ^ 2) 1 d1 ∧
    coreProgram.Rel rd "statement_digest" [s0, s1, cx0, cx1, cs0, cs1, d0, d1, carried * x ^ 24]
      [p0, p1] ∧
    LoadHolds rd (cpi * x ^ 2) 0 p0 ∧ LoadHolds rd (cpi * x ^ 2) 1 p1 ∧
    coreProgram.Rel rd "verify_sub" [p0, p1, s0, s1, glp, gsq, cfresh * x ^ 24] [] ∧
    LoadHolds rd (written * x) 1 (base * (gen ^ ex * gen ^ es))

theorem l5_step {rd : Reader} (hm : MemOk rd) {x : E} {ps : List E}
    (h : coreProgram.Rel rd "__loop4" (x :: ps) []) :
    (∀ N written lxt cover lxs lst lss carried dadig s0 s1 cpi glp gsq cfresh,
      ps = [N, written, lxt, cover, lxs, lst, lss, carried, dadig, s0, s1, cpi, glp, gsq,
        cfresh] →
      KidStep rd written lxt cover lxs lst lss carried dadig s0 s1 cpi glp gsq cfresh x) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd "__loop4" (x * gen :: ps) []) := by
  have hf := find_of_idx l5_idx (by rw [coreProgram_length]; omega)
  have hok := l5_ok
  simp only [l5Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hm16⟩, hl17⟩, hrc18⟩, hrc19⟩, hm28⟩, hc29⟩, hcx⟩, hm32⟩, hcs⟩, hm40⟩, hm42⟩, hl43⟩, hl44⟩, hsd⟩, hm48⟩, hl45⟩, hm49⟩, hl46⟩, hm55⟩, hvs⟩, hm56⟩, hm57⟩, hl56⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ := loop_stepF hf hshape h
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
  · have := call_of_flat hall hcx
    simpa [h29, hlxt, hcov, hlxs, hnx] using this
  · have := call_of_flat hall hcs
    simpa [isMul_sound hm32 hat, hlst, hcov, hlxs, hlss, hnx, hns] using this
  · have := load_sound hl43 hat; rwa [monoIs_sound hm42 hat, hdad, hx] at this
  · have := load_sound hl44 hat; rwa [monoIs_sound hm42 hat, hdad, hx] at this
  · have := call_of_flat hall hsd
    simpa [monoIs_sound hm40 hat, hs0, hs1, hcar, hx] using this
  · have := load_sound hl45 hat; rwa [monoIs_sound hm48 hat, hcpi, hx] at this
  · have := load_sound hl46 hat; rwa [monoIs_sound hm49 hat, hcpi, hx] at this
  · have := call_of_flat hall hvs
    simpa [monoIs_sound hm55 hat, hs0, hs1, hglp, hgsq, hcf, hx] using this
  · have := load_sound hl56 hat
    rwa [isMul_sound hm57 hat, isMul_sound hm56 hat, h28, hwr, hx] at this

end
end LeanVM.Guest.B1.Main
