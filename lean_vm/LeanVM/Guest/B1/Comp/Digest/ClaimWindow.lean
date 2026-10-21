/-
  LeanVM.Guest.B1.Comp.Digest.ClaimWindow

  `claims_tail__L{k}` and `claims_window` complete under any semantics: the rows chained from the
  state handed to them hold, so the relation does.
-/

module

public import LeanVM.Guest.B1.Comp.Basic
public import LeanVM.Guest.B1.Digest.ClaimListM

/-!
# Claim windows and tails, backward, under any semantics

A tail and a window run their blocks from the state handed to them (pattern C of
`docs/roadmap/w2-guest-model.md`); W2 states the rows they check (`Meaning_claims_tailB S`,
`Meaning_claims_windowB S`, over `ChainSteps S`). Their backward halves hold under every
semantics: given the rows (`ChainSteps S`, whose states are the honest values of the chain, in
place of the deployed `chainRun`), the relation holds (`claims_tail_compB`, `claims_window_compB`).
The caller (`claim_list_digest`, over a completeness model) gives the rows of the model's chain.
At `blakeDeployed` they give the deployed backward directions (`claims_tail_of_compB`,
`claims_window_of_compB`), every `ChainCells` run being a `ChainSteps` one
(`chainSteps_of_chainCells`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- **A `ChainCells` run is a `ChainSteps` run at the deployed semantics** (`chainCells_of_chainSteps`'s
converse). -/
theorem chainSteps_of_chainCells {st out : E × E} {blocks : ℕ → Fin 4 → E} {md : ℕ → E} {n : ℕ}
    (h : ChainCells st blocks md n out) : ChainSteps blakeDeployed st blocks md n out := by
  rcases h with ⟨hn, ho⟩ | ⟨-, h, hs, hcan, ho⟩
  · subst hn
    exact ⟨fun _ => st, rfl, ho.symm, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  · subst hs ho
    exact ⟨fun j => digestScalars (chainRun h blocks md j), rfl, rfl, steps_of_chainCells hcan⟩

/-! ## `claims_tail__L{k}` -/

section
variable (k : ℕ) (s0 s1 base ptr : E) (cs : List E) (st : ℕ → E × E)

/-- The values of `claims_tail__L{k}` with the chain's states `st` (`ctVals` at the deployed
chain). -/
def ctValsS (i : ℕ) : E :=
  if i < 4 then [s0, s1, base, ptr].getD i 0 else
  if (i - 4) % 8 = 0 then (st ((i - 4) / 8)).1 else
  if (i - 4) % 8 = 1 then (st ((i - 4) / 8)).2 else
  if (i - 4) % 8 = 6 then word (64 * ((i - 4) / 8 + 1)) 0 0 else
  if (i - 4) % 8 = 7 then baseMd base ((i - 4) / 8) else
  if (i - 4) / 8 < k then cs.getD (4 * ((i - 4) / 8) + ((i - 4) % 8 - 2)) 0 else
  if (i - 4) % 8 = 2 then (st k).1 else
  if (i - 4) % 8 = 3 then (st k).2 else
  if (i - 4) % 8 = 4 then word (tailC.getD k 0) 0 0 else ptr * word (tailC.getD k 0) 0 0

theorem ctValsS_st (j : ℕ) :
    ctValsS k s0 s1 base ptr cs st (4 + 8 * j) = (st j).1 ∧
      ctValsS k s0 s1 base ptr cs st (5 + 8 * j) = (st j).2 := by
  constructor
  · simp only [ctValsS, show ¬(4 + 8 * j < 4) by omega, show (4 + 8 * j - 4) % 8 = 0 by omega,
      show (4 + 8 * j - 4) / 8 = j by omega, ↓reduceIte]
  · simp only [ctValsS, show ¬(5 + 8 * j < 4) by omega, show (5 + 8 * j - 4) % 8 = 1 by omega,
      show (5 + 8 * j - 4) / 8 = j by omega, ↓reduceIte, one_ne_zero]

theorem ctValsS_cell (j r : ℕ) (hj : j < k) (hr : r < 4) :
    ctValsS k s0 s1 base ptr cs st (6 + 8 * j + r) = cs.getD (4 * j + r) 0 := by
  simp only [ctValsS, show ¬(6 + 8 * j + r < 4) by omega,
    show (6 + 8 * j + r - 4) % 8 = r + 2 by omega, show (6 + 8 * j + r - 4) / 8 = j by omega,
    show r + 2 ≠ 0 by omega, show r + 2 ≠ 1 by omega, show r + 2 ≠ 6 by omega,
    show r + 2 ≠ 7 by omega, hj, ↓reduceIte, Nat.add_sub_cancel]

theorem ctValsS_md (j : ℕ) :
    ctValsS k s0 s1 base ptr cs st (10 + 8 * j) = word (64 * (j + 1)) 0 0 ∧
      ctValsS k s0 s1 base ptr cs st (11 + 8 * j) = baseMd base j := by
  constructor
  · simp only [ctValsS, show ¬(10 + 8 * j < 4) by omega, show (10 + 8 * j - 4) % 8 = 6 by omega,
      show (10 + 8 * j - 4) / 8 = j by omega, ↓reduceIte]
    simp
  · simp only [ctValsS, show ¬(11 + 8 * j < 4) by omega, show (11 + 8 * j - 4) % 8 = 7 by omega,
      show (11 + 8 * j - 4) / 8 = j by omega, ↓reduceIte]
    simp

theorem ctValsS_tail :
    ctValsS k s0 s1 base ptr cs st (6 + 8 * k) = (st k).1 ∧
      ctValsS k s0 s1 base ptr cs st (7 + 8 * k) = (st k).2 ∧
      ctValsS k s0 s1 base ptr cs st (8 + 8 * k) = word (tailC.getD k 0) 0 0 ∧
      ctValsS k s0 s1 base ptr cs st (9 + 8 * k) = ptr * word (tailC.getD k 0) 0 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [ctValsS, show ¬(6 + 8 * k < 4) by omega, show ¬(7 + 8 * k < 4) by omega,
      show ¬(8 + 8 * k < 4) by omega, show ¬(9 + 8 * k < 4) by omega,
      show (6 + 8 * k - 4) % 8 = 2 by omega, show (7 + 8 * k - 4) % 8 = 3 by omega,
      show (8 + 8 * k - 4) % 8 = 4 by omega, show (9 + 8 * k - 4) % 8 = 5 by omega,
      show (6 + 8 * k - 4) / 8 = k by omega, show (7 + 8 * k - 4) / 8 = k by omega,
      show (8 + 8 * k - 4) / 8 = k by omega, show (9 + 8 * k - 4) / 8 = k by omega,
      lt_irrefl, ↓reduceIte]
    simp

end

section Tail

variable {S : BlakeSem}

/-- `claims_tail__L{k}`'s body under `S`, `k ≥ 1`, backward: the rows give the relation. -/
theorem claims_tail_succ_compB (k : ℕ) (hk : k < 32) (rd : Reader) (name : String)
    (args rets : List E) (hm : Meaning_claims_tailB S k rd args rets) :
    Fn.SemB S (coreProgram.RelB S rd) rd ⟨name, [.n 0, .n 1, .n 2, .n 3], ctBody k⟩ args rets := by
  simp only [Fn.SemB, ctBody, holdsListB_atoms, holdsListB_ret, List.forall_mem_append,
    forall_mem_flatMap_range, ctBlk, List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff,
    and_true, true_and, List.map_cons, List.map_nil]
  obtain ⟨s0, s1, base, ptr, o0, o1, p', rfl, rfl, rfl, cs, hlen, hcells, sts, hst, hout, hstep⟩ :=
    hm
  have e := ctValsS_st k s0 s1 base ptr cs sts
  have ec := ctValsS_cell k s0 s1 base ptr cs sts
  have em := ctValsS_md k s0 s1 base ptr cs sts
  obtain ⟨t6, t7, t8, t9⟩ := ctValsS_tail k s0 s1 base ptr cs sts
  refine ⟨fun v => ctValsS k s0 s1 base ptr cs sts v.idx, rfl,
    ⟨⟨⟨?_, ?_⟩, fun j hj => ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show ctValsS k s0 s1 base ptr cs sts (4 + 8 * 0) = _
    rw [(e 0).1, hst]; rfl
  · show ctValsS k s0 s1 base ptr cs sts (5 + 8 * 0) = _
    rw [(e 0).2, hst]; rfl
  · dsimp only
    rw [show ctValsS k s0 s1 base ptr cs sts 3 = ptr from rfl]
    have l : ∀ r < 4, LoadHolds rd ptr (4 * j + r) (cs.getD (4 * j + r) 0) := fun r hr => by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact hcells _ (by omega)
    rw [show 6 + 8 * j = 6 + 8 * j + 0 by rfl, show 7 + 8 * j = 6 + 8 * j + 1 by omega,
      show 8 + 8 * j = 6 + 8 * j + 2 by omega, show 9 + 8 * j = 6 + 8 * j + 3 by omega,
      ec j 0 hj (by omega), ec j 1 hj (by omega), ec j 2 hj (by omega), ec j 3 hj (by omega),
      (em j).1, (em j).2, (e j).1, (e j).2, (e (j + 1)).1, (e (j + 1)).2]
    refine ⟨?_, l 1 (by omega), l 2 (by omega), l 3 (by omega), rfl, ?_, ?_⟩
    · simpa using l 0 (by omega)
    · show baseMd base j = base + word (64 * (j + 1)) 0 0
      rw [baseMd, word_md]
    · have := hstep j hj
      rwa [show blocksOf cs j = ![cs.getD (4 * j + 0) 0, cs.getD (4 * j + 1) 0,
        cs.getD (4 * j + 2) 0, cs.getD (4 * j + 3) 0] from rfl] at this
  · show ctValsS k s0 s1 base ptr cs sts (6 + 8 * k) = ctValsS k s0 s1 base ptr cs sts (4 + 8 * k)
    rw [t6, (e k).1]
  · show ctValsS k s0 s1 base ptr cs sts (7 + 8 * k) = ctValsS k s0 s1 base ptr cs sts (5 + 8 * k)
    rw [t7, (e k).2]
  · exact t8
  · show ctValsS k s0 s1 base ptr cs sts (9 + 8 * k) = ctValsS k s0 s1 base ptr cs sts 3 *
      ctValsS k s0 s1 base ptr cs sts (8 + 8 * k)
    rw [t9, t8]; rfl
  · show [ctValsS k s0 s1 base ptr cs sts (6 + 8 * k), ctValsS k s0 s1 base ptr cs sts (7 + 8 * k),
      ctValsS k s0 s1 base ptr cs sts (9 + 8 * k)] = _
    rw [t6, t7, t9, tailC_eq k hk, hout]

/-- `claims_tail__L0`'s body under `S`, backward. -/
theorem claims_tail_zero_compB (rd : Reader) (name : String) (args rets : List E)
    (hm : Meaning_claims_tailB S 0 rd args rets) :
    Fn.SemB S (coreProgram.RelB S rd) rd ⟨name, [.n 0, .n 1, .n 2, .n 3], ctBody0⟩ args rets := by
  simp only [Fn.SemB, ctBody0, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB]
  obtain ⟨s0, s1, base, ptr, o0, o1, p', rfl, rfl, hp', cs, -, -, hch⟩ := hm
  have hout := chainSteps_zero hch
  refine ⟨listVal [s0, s1, base, ptr, s0, s1, s0, s1, ptr], rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp only [Prod.mk.injEq] at hout
  show [s0, s1, ptr] = [o0, o1, p']
  rw [hout.1, hout.2, hp', Nat.mul_zero, pow_zero, mul_one]

/-- **`claims_tail__L{k}` is complete under any semantics**, `k < 32`: the rows chained from the
state give the relation. -/
theorem claims_tail_compB (k : ℕ) (hk : k < 32) (rd : Reader) (args rets : List E)
    (hm : Meaning_claims_tailB S k rd args rets) :
    coreProgram.RelB S rd (ctNames.getD k "") args rets := by
  rw [relB_of_find (find_claims_tail k hk)]
  rcases Nat.eq_zero_or_pos k with rfl | h
  · exact claims_tail_zero_compB rd _ args rets hm
  · simp only [show k ≠ 0 by omega, ↓reduceIte]
    exact claims_tail_succ_compB k hk rd _ args rets hm

end Tail

/-! ## `claims_window` -/

section
variable (s0 s1 base ptr xq gsq nxt : E) (cs : List E) (st : ℕ → E × E)

/-- The values of `claims_window` with the chain's states `st` (`cwVals` at the deployed chain). -/
def cwValsS (i : ℕ) : E :=
  if i < 9 then [s0, s1, base, ptr, xq, gsq, word 2 0 0, xq * word 2 0 0, nxt].getD i 0 else
  if (i - 9) % 8 = 0 then (st ((i - 9) / 8)).1 else
  if (i - 9) % 8 = 1 then (st ((i - 9) / 8)).2 else
  if (i - 9) % 8 = 6 then
    (if (i - 9) / 8 < 31 then word (64 * ((i - 9) / 8 + 1)) 0 0 else (st 32).1) else
  if (i - 9) % 8 = 7 then
    (if (i - 9) / 8 < 31 then baseMd base ((i - 9) / 8) else (st 32).2) else
  if (i - 9) / 8 < 32 then cs.getD (4 * ((i - 9) / 8) + ((i - 9) % 8 - 2)) 0 else nxt

theorem cwValsS_st (j : ℕ) :
    cwValsS s0 s1 base ptr xq gsq nxt cs st (9 + 8 * j) = (st j).1 ∧
      cwValsS s0 s1 base ptr xq gsq nxt cs st (10 + 8 * j) = (st j).2 := by
  constructor
  · simp only [cwValsS, show ¬(9 + 8 * j < 9) by omega, show (9 + 8 * j - 9) % 8 = 0 by omega,
      show (9 + 8 * j - 9) / 8 = j by omega, ↓reduceIte]
  · simp only [cwValsS, show ¬(10 + 8 * j < 9) by omega, show (10 + 8 * j - 9) % 8 = 1 by omega,
      show (10 + 8 * j - 9) / 8 = j by omega, ↓reduceIte, one_ne_zero]

theorem cwValsS_cell (j r : ℕ) (hj : j < 32) (hr : r < 4) :
    cwValsS s0 s1 base ptr xq gsq nxt cs st (11 + 8 * j + r) = cs.getD (4 * j + r) 0 := by
  simp only [cwValsS, show ¬(11 + 8 * j + r < 9) by omega,
    show (11 + 8 * j + r - 9) % 8 = r + 2 by omega, show (11 + 8 * j + r - 9) / 8 = j by omega,
    show r + 2 ≠ 0 by omega, show r + 2 ≠ 1 by omega, show r + 2 ≠ 6 by omega,
    show r + 2 ≠ 7 by omega, hj, ↓reduceIte, Nat.add_sub_cancel]

theorem cwValsS_md (j : ℕ) (hj : j < 31) :
    cwValsS s0 s1 base ptr xq gsq nxt cs st (15 + 8 * j) = word (64 * (j + 1)) 0 0 ∧
      cwValsS s0 s1 base ptr xq gsq nxt cs st (16 + 8 * j) = baseMd base j := by
  constructor
  · simp only [cwValsS, show ¬(15 + 8 * j < 9) by omega, show (15 + 8 * j - 9) % 8 = 6 by omega,
      show (15 + 8 * j - 9) / 8 = j by omega, hj, ↓reduceIte]
    simp
  · simp only [cwValsS, show ¬(16 + 8 * j < 9) by omega, show (16 + 8 * j - 9) % 8 = 7 by omega,
      show (16 + 8 * j - 9) / 8 = j by omega, hj, ↓reduceIte]
    simp

theorem cwValsS_tail :
    cwValsS s0 s1 base ptr xq gsq nxt cs st 263 = (st 32).1 ∧
      cwValsS s0 s1 base ptr xq gsq nxt cs st 264 = (st 32).2 ∧
      cwValsS s0 s1 base ptr xq gsq nxt cs st 267 = nxt := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [cwValsS]

end

/-- **`claims_window` is complete under any semantics**: the rows of its 32 claims chained from
the state give the relation. -/
theorem claims_window_compB {S : BlakeSem} {rd : Reader} {gsq : E} (hT : SquaresAt rd gsq)
    (s0 s1 base ptr xq : E) (rets : List E)
    (hm : Meaning_claims_windowB S rd [s0, s1, base, ptr, xq, gsq] rets) :
    coreProgram.RelB S rd "claims_window" [s0, s1, base, ptr, xq, gsq] rets := by
  rw [relB_of_find find_claims_window]
  simp only [Fn.SemB, cwBody, holdsListB_atoms, List.cons_append, List.nil_append,
    Stmt.HoldsListB, Stmt.HoldsB, List.forall_mem_append, forall_mem_flatMap_range,
    cwBlk, List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff, and_true, true_and, List.map_cons,
    List.map_nil]
  obtain ⟨s0', s1', base', ptr', xq', gsq', o0, o1, nxt, hargs, rfl, N, hN, hxq, hnxt, cs, hlen,
    hcells, sts, hst, hout, hstep⟩ := hm
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
  have est := cwValsS_st s0 s1 base ptr xq gsq nxt cs sts
  have ecl := cwValsS_cell s0 s1 base ptr xq gsq nxt cs sts
  have emd := cwValsS_md s0 s1 base ptr xq gsq nxt cs sts
  obtain ⟨t263, t264, t267⟩ := cwValsS_tail s0 s1 base ptr xq gsq nxt cs sts
  have hl : ∀ i < 128, LoadHolds rd ptr i (cs.getD i 0) := fun i hi => by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hcells _ (by omega)
  have hb : ∀ j, blocksOf cs j = ![cs.getD (4 * j + 0) 0, cs.getD (4 * j + 1) 0,
      cs.getD (4 * j + 2) 0, cs.getD (4 * j + 3) 0] := fun j => rfl
  refine ⟨fun v => cwValsS s0 s1 base ptr xq gsq nxt cs sts v.idx, rfl, rfl, rfl, ?_, ?_, ?_,
    ⟨fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (scaled_log_11_iffB hT _ _).mpr ⟨nxt, rfl, N, hN,
      by show xq * word 2 0 0 = gen ^ N; rw [word_eq_eOfNat]; exact hxq, hnxt⟩
  · show cwValsS s0 s1 base ptr xq gsq nxt cs sts (9 + 8 * 0) = _
    rw [(est 0).1, hst]; rfl
  · show cwValsS s0 s1 base ptr xq gsq nxt cs sts (10 + 8 * 0) = _
    rw [(est 0).2, hst]; rfl
  · dsimp only
    rw [show cwValsS s0 s1 base ptr xq gsq nxt cs sts 3 = ptr from rfl,
      show cwValsS s0 s1 base ptr xq gsq nxt cs sts 2 = base from rfl,
      show 11 + 8 * j = 11 + 8 * j + 0 by rfl, show 12 + 8 * j = 11 + 8 * j + 1 by omega,
      show 13 + 8 * j = 11 + 8 * j + 2 by omega, show 14 + 8 * j = 11 + 8 * j + 3 by omega,
      ecl j 0 (by omega) (by omega), ecl j 1 (by omega) (by omega), ecl j 2 (by omega) (by omega),
      ecl j 3 (by omega) (by omega), (emd j hj).1, (emd j hj).2, (est j).1, (est j).2,
      (est (j + 1)).1, (est (j + 1)).2]
    refine ⟨by simpa using hl (4 * j) (by omega), hl _ (by omega), hl _ (by omega),
      hl _ (by omega), rfl, by rw [baseMd, word_md], ?_⟩
    have := hstep j (by omega)
    rwa [windowMd, ite_pos' hj, hb] at this
  · exact hl 124 (by omega)
  · exact hl 125 (by omega)
  · exact hl 126 (by omega)
  · exact hl 127 (by omega)
  · show S.check ![cwValsS s0 s1 base ptr xq gsq nxt cs sts (11 + 8 * 31 + 0),
      cwValsS s0 s1 base ptr xq gsq nxt cs sts (11 + 8 * 31 + 1),
      cwValsS s0 s1 base ptr xq gsq nxt cs sts (11 + 8 * 31 + 2),
      cwValsS s0 s1 base ptr xq gsq nxt cs sts (11 + 8 * 31 + 3)]
      (cwValsS s0 s1 base ptr xq gsq nxt cs sts (9 + 8 * 31))
      (cwValsS s0 s1 base ptr xq gsq nxt cs sts (10 + 8 * 31))
      (cwValsS s0 s1 base ptr xq gsq nxt cs sts 263) (cwValsS s0 s1 base ptr xq gsq nxt cs sts 264)
      (cwValsS s0 s1 base ptr xq gsq nxt cs sts 8)
    rw [ecl 31 0 (by omega) (by omega), ecl 31 1 (by omega) (by omega),
      ecl 31 2 (by omega) (by omega), ecl 31 3 (by omega) (by omega), (est 31).1, (est 31).2,
      t263, t264, show cwValsS s0 s1 base ptr xq gsq nxt cs sts 8 = nxt from rfl]
    have := hstep 31 (by omega)
    rwa [windowMd, ite_neg' (by omega), hb] at this
  · show cwValsS s0 s1 base ptr xq gsq nxt cs sts (9 + 8 * 32) =
      cwValsS s0 s1 base ptr xq gsq nxt cs sts 263
    rw [(est 32).1, t263]
  · show cwValsS s0 s1 base ptr xq gsq nxt cs sts (10 + 8 * 32) =
      cwValsS s0 s1 base ptr xq gsq nxt cs sts 264
    rw [(est 32).2, t264]
  · show cwValsS s0 s1 base ptr xq gsq nxt cs sts 267 = cwValsS s0 s1 base ptr xq gsq nxt cs sts 8
    rw [t267]; rfl
  · show [cwValsS s0 s1 base ptr xq gsq nxt cs sts (9 + 8 * 32),
      cwValsS s0 s1 base ptr xq gsq nxt cs sts (10 + 8 * 32),
      cwValsS s0 s1 base ptr xq gsq nxt cs sts 267] = _
    rw [(est 32).1, (est 32).2, t267, hout]

/-! ## At the deployed semantics -/

theorem claims_tail_of_compB (k : ℕ) (hk : k < 32) (rd : Reader) (args rets : List E)
    (h : Meaning_claims_tail k rd args rets) :
    coreProgram.Rel rd (ctNames.getD k "") args rets := by
  rw [← relB_deployed]
  obtain ⟨s0, s1, base, ptr, o0, o1, p', ha, hr, hp, cs, hlen, hcells, hch⟩ := h
  exact claims_tail_compB k hk rd args rets
    ⟨s0, s1, base, ptr, o0, o1, p', ha, hr, hp, cs, hlen, hcells, chainSteps_of_chainCells hch⟩

theorem claims_window_of_compB {rd : Reader} {gsq : E} (hT : SquaresAt rd gsq)
    (s0 s1 base ptr xq : E) (rets : List E)
    (h : Meaning_claims_window rd [s0, s1, base, ptr, xq, gsq] rets) :
    coreProgram.Rel rd "claims_window" [s0, s1, base, ptr, xq, gsq] rets := by
  rw [← relB_deployed]
  obtain ⟨a, b, c, d, e, f, o0, o1, nxt, ha, hr, N, hN, hxq, hnxt, cs, hlen, hcells, hch⟩ := h
  exact claims_window_compB hT s0 s1 base ptr xq rets
    ⟨a, b, c, d, e, f, o0, o1, nxt, ha, hr, N, hN, hxq, hnxt, cs, hlen, hcells,
      chainSteps_of_chainCells hch⟩

end
end LeanVM.Guest.B1.Digest
