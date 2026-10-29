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
public import LeanVM.Guest.B1.Digest.CoverComplete

/-!
# `main`'s honest valuation

`MainIn`: what `main`'s oracle supplies (the counts of `meta`, the seed, the exponent tables'
pointers, its `HeapBuf`s, the digests its callees return, the picked DA slot, the leaf's deferred
value); `mσ rd m` is `mFlatE` evaluated on it (`Fwd.ev`). `main_core`: on a memory defined below
`2^16` (the range checks) holding `main`'s stored and read words (`MainMem`: the byte table, the
first and last running counts, the own and the published DA digests, the leaf's deferred claim,
the header), for counts within their bounds (`MainBounds`), every atom of the executed blocks
holds and the words `main` passes to its callees are the honest ones (`MVals`).
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
  pick : ℕ
  seed : Digest
  et1 : E
  et2 : E
  a77 : E
  a80 : E
  a117 : E
  a119 : E
  aDa : E
  a394 : E
  a400 : E
  a406 : E
  a409 : E
  a417 : E
  xd : Digest
  sd : Digest
  sdg : Digest
  daR : List E
  dap : Digest
  leaf : E

/-- The counts of `meta`. -/
def MainIn.cnt (m : MainIn) : List ℕ := [m.nlx, m.nxd, m.nrx, m.nls, m.nsd, m.nrs, m.nc, m.nd]

/-- The coverage table's slots. -/
def MainIn.total (m : MainIn) : ℕ := m.nlx + m.nxd + (m.nls + m.nsd)

/-- The own DA digest's cells: the checked claim's digest, or zeros. -/
noncomputable def MainIn.ownDa (m : MainIn) : List E :=
  if m.nd = 1 then digestCells (keccak256 (cellsBytes m.daR)) else [0, 0]

/-- **`main`'s oracle**: hints, `HeapBuf`s, calls' returns. -/
noncomputable def mOrc (m : MainIn) (j : ℕ) : E :=
  if j < 8 then gen ^ m.cnt.getD j 0
  else if j = 47 then (digestScalars m.seed).1 else if j = 48 then (digestScalars m.seed).2
  else if j = 49 then m.et1 else if j = 50 then m.et2
  else if j = 53 then m.a77 else if j = 56 then m.a80
  else if j = 57 then (digestScalars m.xd).1 else if j = 58 then (digestScalars m.xd).2
  else if j = 59 then (digestScalars m.sd).1 else if j = 60 then (digestScalars m.sd).2
  else if j = 67 then m.a117 else if j = 68 then m.a119 else if j = 334 then m.aDa
  else if 339 ≤ j ∧ j < 343 then m.daR.getD (j - 339) 0
  else if j = 365 then m.a394 else if j = 371 then m.a400 else if j = 377 then m.a406
  else if j = 380 then m.a409 else if j = 387 then gen ^ m.pick else if j = 402 then m.a417
  else if j = 405 then m.leaf
  else if j = 431 then (digestScalars m.sdg).1 else if j = 432 then (digestScalars m.sdg).2
  else 0

/-- **`main`'s honest valuation.** -/
noncomputable def mσ (rd : Reader) (m : MainIn) : Val := B1.Val.ofArgs (ev rd (mOrc m) [] mFlatE)

/-- The counts' bounds (the range checks'), the picked DA slot, the checked claim's cells. -/
structure MainBounds (m : MainIn) : Prop where
  lx : m.nlx ≤ 65535
  xd : m.nxd ≤ 65535
  rx : m.nrx ≤ 65535
  ls : m.nls ≤ 65535
  sd : m.nsd ≤ 65535
  rs : m.nrs ≤ 65535
  nc : m.nc ≤ 16
  nd : m.nd ≤ 1
  total : m.total ≤ 65535
  pick : m.pick ≤ m.nc
  pickD : m.nd = 1 → m.pick = m.nc
  daR : m.nd = 1 → m.daR.length = 4 ∧ AllCanonical m.daR

/-- **The words `main` stores or reads in its buffers and its header.** -/
structure MainMem (rd : Reader) (m : MainIn) : Prop where
  bytes : ReadsAt rd m.a119 ((List.range 256).map fun v => word v 0 0)
  w0 : LoadHolds rd m.a409 0 (gen ^ (m.nrx + m.nrs))
  wN : LoadHolds rd (m.a409 * gen ^ m.nc) 0 (gen ^ m.total)
  own : ReadsAt rd (m.aDa * gen ^ (2 * m.nc)) m.ownDa
  dap : ReadsAt rd (m.aDa * gen ^ (2 * m.pick)) (digestCells m.dap)
  leaf : m.nc = 0 → ReadsAt rd m.a417 (List.replicate 23 0 ++ [m.leaf])
  h0 : LoadHolds rd 1 0 (digestScalars m.sdg).1
  h1 : LoadHolds rd gen 0 (digestScalars m.sdg).2

/-- **What holds of `main`'s honest valuation.** -/
structure MVals (rd : Reader) (σ : Val) (m : MainIn) : Prop where
  pre : ∀ a ∈ atomsIn mPre, a.Holds rd σ
  mid : ∀ a ∈ atomsIn mMid, a.Holds rd σ
  post : ∀ a ∈ atomsIn mPost, a.Holds rd σ
  da : m.nd = 1 → ∀ a ∈ atomsIn mDa, a.Holds rd σ
  daZ : m.nd ≠ 1 → ∀ a ∈ atomsIn mDaZ, a.Holds rd σ
  leaf : m.nc = 0 → ∀ a ∈ atomsIn mLeaf, a.Holds rd σ
  orc : ∀ j ∈ [0, 1, 2, 3, 4, 5, 6, 7, 47, 48, 49, 50, 53, 56, 57, 58, 59, 60, 67, 68, 334, 339,
    340, 341, 342, 365, 371, 377, 380, 387, 402, 405, 431, 432], σ (.n j) = mOrc m j
  v40 : σ (.n 40) = gen ^ (m.nlx + m.nxd)
  v41 : σ (.n 41) = gen ^ (m.nls + m.nsd)
  v42 : σ (.n 42) = gen ^ m.total
  v52 : σ (.n 52) = gen ^ (4 * (m.nlx + m.nxd))
  v55 : σ (.n 55) = gen ^ (4 * (m.nls + m.nsd))
  g62 : σ (.n 62) = 1 + gen ^ m.nxd
  g63 : σ (.n 63) = 1
  g65 : σ (.n 65) = 1 + gen ^ m.nsd
  g66 : σ (.n 66) = 1
  g326 : σ (.n 326) = 1 + gen ^ m.nrx
  g327 : σ (.n 327) = 1
  g329 : σ (.n 329) = 1 + gen ^ m.nrs
  g330 : σ (.n 330) = 1
  v333 : σ (.n 333) = gen ^ (2 * (m.nc + 1))
  v336 : σ (.n 336) = m.aDa * gen ^ (2 * m.nc)
  v338 : σ (.n 338) = gen ^ m.nd + gen
  v364 : σ (.n 364) = gen ^ (2 * m.nc)
  v370 : σ (.n 370) = gen ^ (24 * m.nc)
  v376 : σ (.n 376) = gen ^ (24 * m.nc)
  v379 : σ (.n 379) = gen ^ (m.nc + 1)
  v381 : σ (.n 381) = gen ^ (m.nrx + m.nrs)
  g383 : σ (.n 383) = 1 + gen ^ m.nc
  g384 : σ (.n 384) = 1
  v385 : σ (.n 385) = m.a409 * gen ^ m.nc
  v401 : σ (.n 401) = m.aDa * gen ^ (2 * m.pick)
  v404 : σ (.n 404) = gen ^ m.nc + 1
  r429 : σ (.n 429) = (digestScalars m.dap).1
  r430 : σ (.n 430) = (digestScalars m.dap).2
  v433 : σ (.n 433) = 1
  v437 : σ (.n 437) = gen

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
def mOrcIdx : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 47, 48, 49, 50, 53, 56, 57, 58, 59, 60, 67, 68, 334,
  339, 340, 341, 342, 365, 371, 377, 380, 387, 402, 405, 431, 432]

set_option maxRecDepth 100000 in
theorem mOrcIdx_defs : ∀ j ∈ mOrcIdx, ∃ s ∈ mOrcStmts, V.n j ∈ defsOf s := by decide +kernel

end
end LeanVM.Guest.B1.Main
