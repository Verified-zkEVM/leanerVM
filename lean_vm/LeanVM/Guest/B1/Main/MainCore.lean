/-
  LeanVM.Guest.B1.Main.MainCore

  `main`'s honest valuation: its body evaluated on the honest hints, `HeapBuf`s and calls' returns
  (`mOrc`), and what holds of it on a memory holding `main`'s honest words.
-/

module

public import LeanVM.Guest.B1.Main.MainLocChk
public import LeanVM.Guest.B1.Digest.ChainFilter
public import LeanVM.Guest.B1.Digest.PairComplete
public import LeanVM.Guest.B1.Digest.Range

/-!
# `main`'s honest valuation

`MainIn`: what `main`'s oracle supplies (the counts of `meta` and `da_meta`, the seed, the
exponent tables' pointers, its `HeapBuf`s, the digests its callees return, the leaf's deferred
value); `mσ rd m` is `mFlatE` evaluated on it (`Fwd.ev`). `main_core`: on a memory defined below
`2^16` (the range checks) holding `main`'s stored words (`MainMem`: the signer set's digest, the
byte table, the first and last running counts, the leaf's deferred claim, the header), for counts
within their bounds (`MainBounds`), every atom of the executed blocks holds and the words `main`
passes to its callees are the honest ones (`MVals`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## The oracle -/

/-- **What `main`'s oracle supplies.** -/
structure MainIn where
  nlx : ℕ
  nxd : ℕ
  nrx : ℕ
  nls : ℕ
  nsd : ℕ
  nrs : ℕ
  nc : ℕ
  nd : ℕ
  nda : ℕ
  ndd : ℕ
  seed : Digest
  et1 : E
  et2 : E
  a69 : E
  a77 : E
  a80 : E
  a116 : E
  a117 : E
  a119 : E
  a394 : E
  a400 : E
  a406 : E
  a409 : E
  a417 : E
  dad : Digest
  xd : Digest
  sd : Digest
  sdg : Digest
  daR : List E
  leaf : E

/-- The counts of `meta`. -/
def MainIn.cnt (m : MainIn) : List ℕ := [m.nlx, m.nxd, m.nrx, m.nls, m.nsd, m.nrs, m.nc, m.nd]

/-- The coverage table's slots. -/
def MainIn.total (m : MainIn) : ℕ := m.nlx + m.nxd + (m.nls + m.nsd) + (m.nda + m.ndd)

/-- **`main`'s oracle**: hints, `HeapBuf`s, calls' returns. -/
noncomputable def mOrc (m : MainIn) (j : ℕ) : E :=
  if j < 8 then gen ^ m.cnt.getD j 0
  else if j = 40 then gen ^ m.nda else if j = 41 then gen ^ m.ndd
  else if j = 63 then (digestScalars m.seed).1 else if j = 64 then (digestScalars m.seed).2
  else if j = 65 then m.et1 else if j = 66 then m.et2 else if j = 69 then m.a69
  else if j = 73 then (digestScalars m.dad).1 else if j = 74 then (digestScalars m.dad).2
  else if j = 77 then m.a77 else if j = 80 then m.a80
  else if j = 81 then (digestScalars m.xd).1 else if j = 82 then (digestScalars m.xd).2
  else if j = 83 then (digestScalars m.sd).1 else if j = 84 then (digestScalars m.sd).2
  else if j = 116 then m.a116 else if j = 117 then m.a117 else if j = 119 then m.a119
  else if 384 ≤ j ∧ j < 388 then m.daR.getD (j - 384) 0
  else if 389 ≤ j ∧ j < 393 then m.daR.getD (j - 389) 0
  else if j = 394 then m.a394 else if j = 400 then m.a400 else if j = 406 then m.a406
  else if j = 409 then m.a409 else if j = 417 then m.a417 else if j = 420 then m.leaf
  else if j = 444 then (digestScalars m.sdg).1 else if j = 445 then (digestScalars m.sdg).2
  else 0

/-- **`main`'s honest valuation.** -/
noncomputable def mσ (rd : Reader) (m : MainIn) : Val := B1.Val.ofArgs (ev rd (mOrc m) [] mFlatE)

/-- The counts' bounds (the range checks'), and a declared claim. -/
structure MainBounds (m : MainIn) : Prop where
  lx : m.nlx ≤ 65535
  xd : m.nxd ≤ 65535
  rx : m.nrx ≤ 65535
  ls : m.nls ≤ 65535
  sd : m.nsd ≤ 65535
  rs : m.nrs ≤ 65535
  nc : m.nc ≤ 16
  nd : m.nd ≤ 1
  nda : m.nda ≤ 16
  ndd : m.ndd ≤ 257
  slots : m.nda + m.ndd ≤ 257
  total : m.total ≤ 65535
  nz : m.nlx + m.nls + m.nda ≠ 0

/-- **The words `main` stores or reads in its buffers and its header.** -/
structure MainMem (rd : Reader) (m : MainIn) : Prop where
  sig : ReadsAt rd m.a116 (digestCells (keccak256 (cellsBytes (digestCells m.xd ++ digestCells m.sd))))
  bytes : ReadsAt rd m.a119 ((List.range 256).map fun v => word v 0 0)
  w0 : LoadHolds rd m.a409 0 (gen ^ (m.nrx + m.nrs + m.nd))
  wN : LoadHolds rd (m.a409 * gen ^ m.nc) 0 (gen ^ m.total)
  leaf : m.nc = 0 → ReadsAt rd m.a417 (List.replicate 23 0 ++ [m.leaf])
  h0 : LoadHolds rd 1 0 (digestScalars m.sdg).1
  h1 : LoadHolds rd gen 0 (digestScalars m.sdg).2

/-- **What holds of `main`'s honest valuation.** -/
structure MVals (rd : Reader) (σ : Val) (m : MainIn) : Prop where
  pre : ∀ a ∈ atomsIn mPre, a.Holds rd σ
  mid : ∀ a ∈ atomsIn mMid, a.Holds rd σ
  post : ∀ a ∈ atomsIn mPost, a.Holds rd σ
  da : ∀ a ∈ atomsIn mDa, a.Holds rd σ
  leaf : m.nc = 0 → ∀ a ∈ atomsIn mLeaf, a.Holds rd σ
  orc : ∀ j ∈ [0, 1, 2, 3, 4, 5, 6, 7, 40, 41, 63, 64, 65, 66, 69, 73, 74, 77, 80, 81, 82, 83, 84,
    116, 117, 119, 384, 385, 386, 387, 389, 390, 391, 392, 394, 400, 406, 409, 417, 420, 444, 445],
    σ (.n j) = mOrc m j
  v50 : σ (.n 50) = gen ^ (m.nda + m.ndd)
  v55 : σ (.n 55) = gen ^ (m.nlx + m.nxd)
  v56 : σ (.n 56) = gen ^ (m.nls + m.nsd)
  v57 : σ (.n 57) = gen ^ (m.nlx + m.nxd + (m.nls + m.nsd))
  v58 : σ (.n 58) = gen ^ m.total
  v68 : σ (.n 68) = gen ^ (4 * (m.nda + m.ndd))
  v76 : σ (.n 76) = gen ^ (4 * (m.nlx + m.nxd))
  v79 : σ (.n 79) = gen ^ (4 * (m.nls + m.nsd))
  v118 : σ (.n 118) = m.a117 * gen ^ (m.nlx + m.nxd + (m.nls + m.nsd))
  v388 : σ (.n 388) = gen ^ (m.nrx + m.nrs)
  v393 : σ (.n 393) = gen ^ (2 * m.nc)
  v399 : σ (.n 399) = gen ^ (24 * m.nc)
  v405 : σ (.n 405) = gen ^ (24 * m.nc)
  v408 : σ (.n 408) = gen ^ (m.nc + 1)
  g71 : σ (.n 71) = 1 + gen ^ (m.nda + m.ndd)
  g72 : σ (.n 72) = 1
  g86 : σ (.n 86) = 1 + gen ^ m.nxd
  g87 : σ (.n 87) = 1
  g89 : σ (.n 89) = 1 + gen ^ m.nsd
  g90 : σ (.n 90) = 1
  g377 : σ (.n 377) = 1 + gen ^ m.nrx
  g378 : σ (.n 378) = 1
  g380 : σ (.n 380) = 1 + gen ^ m.nrs
  g381 : σ (.n 381) = 1
  v383 : σ (.n 383) = gen ^ m.nd + gen
  g413 : σ (.n 413) = 1 + gen ^ m.nc
  g414 : σ (.n 414) = 1
  v419 : σ (.n 419) = gen ^ m.nc + 1
  v415 : σ (.n 415) = m.a409 * gen ^ m.nc
  v446 : σ (.n 446) = 1
  v450 : σ (.n 450) = gen

/-! ## Helpers -/

theorem mem_atomsIn' {ss : List Stmt} {a : Atom} (h : Stmt.atom a ∈ ss) : a ∈ atomsIn ss :=
  List.mem_filterMap.mpr ⟨_, h, rfl⟩

theorem atom_mem_of_atomsIn' {ss : List Stmt} {a : Atom} (h : a ∈ atomsIn ss) : Stmt.atom a ∈ ss := by
  obtain ⟨s, hs, hsa⟩ := List.mem_filterMap.mp h
  cases s <;> simp only [reduceCtorEq, Option.some.injEq] at hsa
  subst hsa
  exact hs

theorem gpow_mul_zero (e : ℕ) : (gen ^ e).limb 0 * Parameters.gpow 0 = Parameters.gpow e := by
  rw [gen_pow_eq_ofK]; simp [Parameters.gpow]

/-- A range check of `g^e` against `g^K` passes on a memory defined below `2^16`. -/
theorem rc_side {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} (hl : Sig.MemOK rd (2 ^ 16))
    {x y t1 t2 k : V} {e K : ℕ} (hx : σ x = gen ^ e) (hk : σ k = gen ^ K) (heK : e ≤ K)
    (hK : K < 2 ^ 16) (hlt : k.idx < y.idx) (hg : Good rd S w σ (.rangeCheck x y t1 t2 k)) :
    Side rd S σ (.rangeCheck x y t1 t2 k) := by
  simp only [Good] at hg
  rw [ite_pos' hlt] at hg
  have hy : σ y = gen ^ (K - e) := by
    rw [hg.2.2, hk, hx, show K = (K - e) + e by omega, pow_add, mul_inv_cancel_right₀
      (pow_ne_zero _ gen_ne_zero), Nat.add_sub_cancel]
  simp only [Side]
  rw [ite_pos' hlt, hx, hy, gpow_mul_zero, gpow_mul_zero]
  exact ⟨gen_pow_isInK _, hl _ (by omega), gen_pow_isInK _, hl _ (by omega),
    pow_ne_zero _ gen_ne_zero⟩

theorem good_mul' {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {d x y : ℕ} (hx : x < d)
    (hy : y < d) (h : Good rd S w σ (.mul (.n d) (.n x) (.n y))) : σ (.n d) = σ (.n x) * σ (.n y) := by
  simp only [Good] at h
  rwa [ite_pos' ⟨hx, hy⟩] at h

theorem one_add_ne' {a : ℕ} (ha : a < 2 ^ 64 - 1) (h0 : a ≠ 0) : (1 : E) + gen ^ a ≠ 0 := by
  rw [Ne, e_add_eq_zero_iff, eq_comm, gen_pow_eq_one_iff ha]; exact h0

/-- The values a statement defines from the oracle. -/
def defsOf : Stmt → List V
  | .atom (.hint (.witness _ (.stack vs))) => vs
  | .atom (.hint (.alloc d _)) => [d]
  | .atom (.hint (.allocDyn d _)) => [d]
  | .call _ _ rets => rets
  | _ => []

theorem goodS_defs {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {s : Stmt}
    (h : GoodS rd S w σ s) : ∀ v ∈ defsOf s, σ v = w v.idx := by
  intro v hv
  cases s with
  | atom a =>
    cases a with
    | hint hh =>
      cases hh with
      | witness n sp =>
        cases sp with
        | stack vs => exact h v hv
        | heap => simp [defsOf] at hv
      | alloc d n =>
        simp only [defsOf, List.mem_singleton] at hv
        subst hv
        exact h
      | allocDyn d n =>
        simp only [defsOf, List.mem_singleton] at hv
        subst hv
        exact h
      | _ => simp [defsOf] at hv
    | _ => simp [defsOf] at hv
  | call f args rets => exact h v hv
  | _ => simp [defsOf] at hv

/-- The oracle's values, as `MVals.orc` lists them. -/
def mOrcIdx : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 40, 41, 63, 64, 65, 66, 69, 73, 74, 77, 80, 81, 82,
  83, 84, 116, 117, 119, 384, 385, 386, 387, 389, 390, 391, 392, 394, 400, 406, 409, 417, 420, 444, 445]

set_option maxRecDepth 100000 in
theorem mOrcIdx_defs : ∀ j ∈ mOrcIdx, ∃ s ∈ mOrcStmts, V.n j ∈ defsOf s := by decide +kernel

end
end LeanVM.Guest.B1.Main
