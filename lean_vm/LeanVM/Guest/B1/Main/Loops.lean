/-
  LeanVM.Guest.B1.Main.Loops

  B1 for `main`'s loop helpers: the raw signatures (`__loop3`, `__loop4`), a child's DA roots
  (`__loop28`) and the children (`__loop5`), each body checked by evaluation.
-/

module

public import LeanVM.Guest.B1.Main.Basic
public import LeanVM.Guest.B1.Digest.Loops

/-!
# `main`'s loops

Each helper's body (`loopPre`) is checked by evaluation (`l3Ok`, `l4Ok`, `l28Ok`, `l5Ok`), and its
run at `x` gives one iteration's facts (`RawXStep`, `RawSStep`, `KidDaStep`, `KidStep`) and the
run at `x·g` (`loop_stepF`).

* `__loop3` (G:4193-4202): a raw leanXMSS signature `i`: a slot `s` below the leanXMSS region,
  `cover[g^s] = g^i`, `verify_lean_xmss(lx_table · g^(4s))`;
* `__loop4` (G:4203-4207): a raw leanSPHINCS signature `j`: a slot `s` below the leanSPHINCS
  region, `cover[lx_slots · g^s] = n_raw_x · g^j`, `verify_sig_lean_sphincs(ls_table · g^(4s), byte_bits)`;
* `__loop28` (G:4231-4238): a child's DA root `d`: `cover_da_root(da_roots, da_cover, da_slots,
  base · n_sub · g^d)`, its four words copied to `child_da · g^(4d)`;
* `__loop5` (G:4219-4260): child `c`.
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

/-! ## `__loop3`: raw leanXMSS signatures -/

def l3Ok (fn : Fn) : Bool :=
  loopShapeF fn "__loop3" && decide (fn.params.length = 5) &&
    rcBoundOk (atomsIn (loopPre fn)) (.n 5) (.n 2) && isMul (atomsIn (loopPre fn)) (.n 11) (.n 3) (.n 5) &&
    (atomsIn (loopPre fn)).any (isLoadAt (.n 0) (.n 11) 0) &&
    monoIs (atomsIn (loopPre fn)) (.n 14) (.n 4) (.n 5) 4 &&
    hasCall (loopPre fn) "verify_lean_xmss" [.n 14] []

set_option maxRecDepth 100000 in
theorem l3_ok : l3Ok (coreProgram.getD 35 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l3_idx : coreProgram.indexOf? "__loop3" = some 35 := by decide +kernel

/-- **A raw leanXMSS signature** at the counter `x`: a slot `s` below the region's bound holding
the mark `x`, and the signature check of the claim at slot `s`. -/
def RawXStep (rd : Reader) (lxs cover lxt x : E) : Prop :=
  ∃ s, BelowLog lxs s ∧ LoadHolds rd cover s x ∧
    coreProgram.Rel rd "verify_lean_xmss" [lxt * gen ^ (4 * s)] []

theorem l3_step {rd : Reader} (hm : MemOk rd) {x : E} {ps : List E}
    (h : coreProgram.Rel rd "__loop3" (x :: ps) []) :
    (∀ N lxs cover lxt, ps = [N, lxs, cover, lxt] → RawXStep rd lxs cover lxt x) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd "__loop3" (x * gen :: ps) []) := by
  have hf := find_of_idx l3_idx (by rw [coreProgram_length]; omega)
  have hok := l3_ok
  simp only [l3Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hrc⟩, hm11⟩, hl⟩, hm14⟩, hcall⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ := loop_stepF hf hshape h
  refine ⟨fun N lxs cover lxt hN => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD 35 default).params = [V.n 0, V.n 1, V.n 2, V.n 3, V.n 4] := by
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

/-! ## `__loop4`: raw leanSPHINCS signatures -/

def l4Ok (fn : Fn) : Bool :=
  loopShapeF fn "__loop4" && decide (fn.params.length = 8) &&
    rcBoundOk (atomsIn (loopPre fn)) (.n 8) (.n 2) &&
    isMul (atomsIn (loopPre fn)) (.n 14) (.n 5) (.n 0) &&
    isMul (atomsIn (loopPre fn)) (.n 15) (.n 4) (.n 8) &&
    isMul (atomsIn (loopPre fn)) (.n 16) (.n 3) (.n 15) &&
    (atomsIn (loopPre fn)).any (isLoadAt (.n 14) (.n 16) 0) &&
    monoIs (atomsIn (loopPre fn)) (.n 19) (.n 6) (.n 8) 4 &&
    hasCall (loopPre fn) "verify_sig_lean_sphincs" [.n 19, .n 7] []

set_option maxRecDepth 100000 in
theorem l4_ok : l4Ok (coreProgram.getD 36 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l4_idx : coreProgram.indexOf? "__loop4" = some 36 := by decide +kernel

/-- **A raw leanSPHINCS signature** at the counter `x`: a slot `s` below the region's bound
holding the mark `n_raw_x · x` (at `cover · lx_slots · g^s`), and the signature check of the
claim at slot `s`. -/
def RawSStep (rd : Reader) (lss cover lxs nrx lst bb x : E) : Prop :=
  ∃ s, BelowLog lss s ∧ LoadHolds rd (cover * (lxs * gen ^ s)) 0 (nrx * x) ∧
    coreProgram.Rel rd "verify_sig_lean_sphincs" [lst * gen ^ (4 * s), bb] []

theorem l4_step {rd : Reader} (hm : MemOk rd) {x : E} {ps : List E}
    (h : coreProgram.Rel rd "__loop4" (x :: ps) []) :
    (∀ N lss cover lxs nrx lst bb, ps = [N, lss, cover, lxs, nrx, lst, bb] →
      RawSStep rd lss cover lxs nrx lst bb x) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd "__loop4" (x * gen :: ps) []) := by
  have hf := find_of_idx l4_idx (by rw [coreProgram_length]; omega)
  have hok := l4_ok
  simp only [l4Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hrc⟩, hm14⟩, hm15⟩, hm16⟩, hl⟩, hm19⟩, hcall⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ := loop_stepF hf hshape h
  refine ⟨fun N lss cover lxs nrx lst bb hN => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD 36 default).params =
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

/-! ## `__loop28`: a child's DA roots -/

def l28Ok (fn : Fn) : Bool :=
  loopShapeF fn "__loop28" && decide (fn.params.length = 8) &&
    monoIs (atomsIn (loopPre fn)) (.n 10) (.n 2) (.n 0) 4 &&
    isMul (atomsIn (loopPre fn)) (.n 11) (.n 6) (.n 7) &&
    isMul (atomsIn (loopPre fn)) (.n 12) (.n 11) (.n 0) &&
    hasCall (loopPre fn) "cover_da_root" [.n 3, .n 4, .n 5, .n 12] [.n 13, .n 14, .n 15, .n 16] &&
    (List.range 4).all fun c => (atomsIn (loopPre fn)).any (isLoadAt (.n (13 + c)) (.n 10) c)

set_option maxRecDepth 100000 in
theorem l28_ok : l28Ok (coreProgram.getD 398 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l28_idx : coreProgram.indexOf? "__loop28" = some 398 := by decide +kernel

/-- **A child's DA root** at the counter `x`: `cover_da_root` with the mark `base · n_sub · x`,
its four words copied to `child_da · x^4`. -/
def KidDaStep (rd : Reader) (cda roots dcov dslots base nsub x : E) : Prop :=
  ∃ r : List E, r.length = 4 ∧
    coreProgram.Rel rd "cover_da_root" [roots, dcov, dslots, base * nsub * x] r ∧
    ReadsAt rd (cda * x ^ 4) r

theorem l28_step {rd : Reader} {x : E} {ps : List E}
    (h : coreProgram.Rel rd "__loop28" (x :: ps) []) :
    (∀ N cda roots dcov dslots base nsub, ps = [N, cda, roots, dcov, dslots, base, nsub] →
      KidDaStep rd cda roots dcov dslots base nsub x) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd "__loop28" (x * gen :: ps) []) := by
  have hf := find_of_idx l28_idx (by rw [coreProgram_length]; omega)
  have hok := l28_ok
  simp only [l28Ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hm10⟩, hm11⟩, hm12⟩, hcall⟩, hl⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ := loop_stepF hf hshape h
  refine ⟨fun N cda roots dcov dslots base nsub hN => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD 398 default).params =
      [V.n 0, V.n 1, V.n 2, V.n 3, V.n 4, V.n 5, V.n 6, V.n 7] := by
    have hs := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, hcda, hroots, hdcov, hdslots, hbase, hnsub⟩ := hps
  have hc := call_of_flat hall hcall
  simp only [List.map_cons, List.map_nil] at hc
  rw [isMul_sound hm12 hat, isMul_sound hm11 hat, hroots, hdcov, hdslots, hbase, hnsub, hx] at hc
  refine ⟨_, rfl, hc, fun k hk => ?_⟩
  have hk4 : k < 4 := by simpa using hk
  have := load_sound (hl k hk4) hat
  rw [monoIs_sound hm10 hat, hcda, hx] at this
  interval_cases k <;> exact this

end
end LeanVM.Guest.B1.Main

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

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

/-! ## `__loop5`: the children -/

def isLoad (atoms : List Atom) (x p : V) (o : ℕ) : Bool := atoms.any (isLoadAt x p o)

def l5Ok (fn : Fn) : Bool :=
  let P := loopPre fn
  let A := atomsIn P
  loopShapeF fn "__loop5" && decide (fn.params.length = 18) &&
  isMul A (.n 18) (.n 2) (.n 0) && isLoad A (.n 19) (.n 18) 0 &&
  rcConstOk A (.n 20) 9272771591053052074 && rcConstOk A (.n 21) 9272771591053052074 &&
  isMul A (.n 30) (.n 20) (.n 21) && A.any (isConstAt (.n 31) 1 0) &&
  hasCall P "child_claim_list_digest" [.n 3, .n 4, .n 19, .n 31, .n 5, .n 20] [.n 32, .n 33] &&
  isMul A (.n 34) (.n 19) (.n 20) &&
  hasCall P "child_claim_list_digest" [.n 6, .n 4, .n 34, .n 5, .n 7, .n 21] [.n 35, .n 36] &&
  pairHashOk A (.n 32) (.n 33) (.n 35) (.n 36) (.n 56) &&
  monoIs A (.n 62) (.n 8) (.n 0) 24 &&
  rcConstOk A (.n 63) 65536 &&
  guardOk P (.n 72) "__loop28" (.n 73) (.n 63) [.n 70, .n 9, .n 10, .n 11, .n 19, .n 30] &&
  hasCall P "da_list_digest" [.n 70, .n 63] [.n 74, .n 75] &&
  hasCall P "statement_digest" [.n 12, .n 13, .n 56, .n 74, .n 75, .n 62] [.n 76, .n 77] &&
  monoIs A (.n 79) (.n 14) (.n 0) 2 && isLoad A (.n 76) (.n 79) 0 &&
  monoIs A (.n 80) (.n 14) (.n 0) 2 && isLoad A (.n 77) (.n 80) 1 &&
  monoIs A (.n 86) (.n 17) (.n 0) 24 &&
  hasCall P "verify_sub" [.n 76, .n 77, .n 12, .n 13, .n 15, .n 16, .n 86] [] &&
  isMul A (.n 87) (.n 19) (.n 30) && isMul A (.n 88) (.n 87) (.n 63) &&
  isMul A (.n 89) (.n 2) (.n 0) && isLoad A (.n 88) (.n 89) 1

set_option maxRecDepth 100000 in
theorem l5_ok : l5Ok (coreProgram.getD 37 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l5_idx : coreProgram.indexOf? "__loop5" = some 37 := by decide +kernel

/-- **Child `x`'s facts**: its base `written[x]`, its counts `g^ex`, `g^es`, `g^ed`, its two
rebuilt claim lists' digests, its signer-set digest at `sp`, its DA roots, its statement's
digest at `child_pi · x^2`, its proof's check, and `written[x · g] = base · g^(ex + es + ed)`. -/
def KidStep (rd : Reader) (written lxt cover lxs lst lss carried roots dcov dslots s0 s1 cpi glp
    gsq cfresh x : E) : Prop :=
  ∃ (base sp cx0 cx1 cs0 cs1 d0 d1 p0 p1 cda : E) (ex es ed : ℕ),
    LoadHolds rd (written * x) 0 base ∧ ex ≤ 65535 ∧ es ≤ 65535 ∧ ed ≤ 16 ∧
    coreProgram.Rel rd "child_claim_list_digest" [lxt, cover, base, 1, lxs, gen ^ ex] [cx0, cx1] ∧
    coreProgram.Rel rd "child_claim_list_digest" [lst, cover, base * gen ^ ex, lxs, lss, gen ^ es]
      [cs0, cs1] ∧
    AllCanonical [cx0, cx1, cs0, cs1] ∧
    LoadHolds rd sp 0 (digestScalars (keccak256 (cellsBytes [cx0, cx1, cs0, cs1]))).1 ∧
    LoadHolds rd sp 1 (digestScalars (keccak256 (cellsBytes [cx0, cx1, cs0, cs1]))).2 ∧
    (∀ d < ed, KidDaStep rd cda roots dcov dslots base (gen ^ ex * gen ^ es) (gen ^ d)) ∧
    coreProgram.Rel rd "da_list_digest" [cda, gen ^ ed] [d0, d1] ∧
    coreProgram.Rel rd "statement_digest" [s0, s1, sp, d0, d1, carried * x ^ 24] [p0, p1] ∧
    LoadHolds rd (cpi * x ^ 2) 0 p0 ∧ LoadHolds rd (cpi * x ^ 2) 1 p1 ∧
    coreProgram.Rel rd "verify_sub" [p0, p1, s0, s1, glp, gsq, cfresh * x ^ 24] [] ∧
    LoadHolds rd (written * x) 1 (base * (gen ^ ex * gen ^ es) * gen ^ ed)

theorem l5_step {rd : Reader} (hm : MemOk rd) {x : E} {ps : List E}
    (h : coreProgram.Rel rd "__loop5" (x :: ps) []) :
    (∀ N written lxt cover lxs lst lss carried roots dcov dslots s0 s1 cpi glp gsq cfresh,
      ps = [N, written, lxt, cover, lxs, lst, lss, carried, roots, dcov, dslots, s0, s1, cpi, glp,
        gsq, cfresh] →
      KidStep rd written lxt cover lxs lst lss carried roots dcov dslots s0 s1 cpi glp gsq cfresh
        x) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd "__loop5" (x * gen :: ps) []) := by
  have hf := find_of_idx l5_idx (by rw [coreProgram_length]; omega)
  have hok := l5_ok
  simp only [l5Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hm18⟩, hl19⟩, hrc20⟩, hrc21⟩, hm30⟩, hc31⟩,
    hcx⟩, hm34⟩, hcs⟩, hss⟩, hm62⟩, hrc63⟩, hg28⟩, hdl⟩, hsd⟩, hm79⟩, hl76⟩, hm80⟩, hl77⟩,
    hm86⟩, hvs⟩, hm87⟩, hm88⟩, hm89⟩, hl88⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ := loop_stepF hf hshape h
  refine ⟨fun N written lxt cover lxs lst lss carried roots dcov dslots s0 s1 cpi glp gsq cfresh hN
    => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD 37 default).params = (List.range 18).map V.n := by
    have hs := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen]
  rw [hpar, hN] at hps
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, List.tail_cons, List.cons.injEq, and_true] at hps
  obtain ⟨-, hwr, hlxt, hcov, hlxs, hlst, hlss, hcar, hroots, hdcov, hdsl, hs0, hs1, hcpi, hglp,
    hgsq, hcf⟩ := hps
  obtain ⟨ex, hex, hnx⟩ := rcConst_sound hm (by norm_num) word_gmax hrc20 hat
  obtain ⟨es, hes, hns⟩ := rcConst_sound hm (by norm_num) word_gmax hrc21 hat
  obtain ⟨ed, hed, hnd⟩ := rcConst_sound hm (by norm_num) word_g16 hrc63 hat
  have h31 : σ (.n 31) = 1 := by rw [const_sound hc31 hat, word_one]
  have h18 : σ (.n 18) = written * x := by rw [isMul_sound hm18 hat, hwr, hx]
  have h30 : σ (.n 30) = gen ^ ex * gen ^ es := by rw [isMul_sound hm30 hat, hnx, hns]
  obtain ⟨hcan, hsp0, hsp1⟩ := pairHash_sound hss hat
  -- the child's DA roots
  have hdas : ∀ d < ed, KidDaStep rd (σ (.n 70)) roots dcov dslots (σ (.n 19))
      (gen ^ ex * gen ^ es) (gen ^ d) := by
    have := loop_sound (f := "__loop28")
      (ps := [σ (.n 63), σ (.n 70), σ (.n 9), σ (.n 10), σ (.n 11), σ (.n 19), σ (.n 30)])
      (N := σ (.n 63)) (m := ed)
      (B := KidDaStep rd (σ (.n 70)) (σ (.n 9)) (σ (.n 10)) (σ (.n 11)) (σ (.n 19)) (σ (.n 30)))
      (by unfold ordG; omega) hnd
      (fun y hy => by
        obtain ⟨h1, h2⟩ := l28_step hy
        exact ⟨h1 _ _ _ _ _ _ _ rfl, h2⟩)
      (fun hne => by simpa using guard_sound hg28 hall hne)
    rwa [hroots, hdcov, hdsl, h30] at this
  refine ⟨σ (.n 19), σ (.n 56), σ (.n 32), σ (.n 33), σ (.n 35), σ (.n 36), σ (.n 74), σ (.n 75),
    σ (.n 76), σ (.n 77), σ (.n 70), ex, es, ed, ?_, hex, hes, hed, ?_, ?_, hcan, hsp0, hsp1, hdas,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := load_sound hl19 hat; rwa [h18] at this
  · have := call_of_flat hall hcx
    simpa [h31, hlxt, hcov, hlxs, hnx] using this
  · have := call_of_flat hall hcs
    simpa [isMul_sound hm34 hat, hlst, hcov, hlxs, hlss, hnx, hns] using this
  · have := call_of_flat hall hdl
    simpa [hnd] using this
  · have := call_of_flat hall hsd
    simpa [monoIs_sound hm62 hat, hs0, hs1, hcar, hx] using this
  · have := load_sound hl76 hat; rwa [monoIs_sound hm79 hat, hcpi, hx] at this
  · have := load_sound hl77 hat; rwa [monoIs_sound hm80 hat, hcpi, hx] at this
  · have := call_of_flat hall hvs
    simpa [monoIs_sound hm86 hat, hs0, hs1, hglp, hgsq, hcf, hx] using this
  · have := load_sound hl88 hat
    rwa [isMul_sound hm89 hat, isMul_sound hm88 hat, isMul_sound hm87 hat, h30, hnd, hwr, hx]
      at this

end
end LeanVM.Guest.B1.Main
