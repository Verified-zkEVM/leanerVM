/-
  LeanVM.Guest.Batch.Sound

  The batching's soundness: an accepted batching whose deferred claim holds makes every child's
  claims true, unless one of its challenges is bad.
-/

module

public import LeanVM.Guest.Batch.Rounds

/-!
# The batching is sound, challenge by challenge

`Node.batch` absorbs the children's claims, squeezes two lambdas per child, and runs one
sumcheck on the bytecode, deferring one claim. `batch_sound`: if the batching accepts and its
deferred claim holds, then every child's claims hold (its proof's, `FixedClaims.Holds`, and its
statement's, `DeferredClaim.Holds`), or a challenge is bad (`BatchBad`):

* **a lambda**: the children's claims leave nonzero gaps (claimed less true values), and the
  lambdas' combination of them vanishes. The last nonzero gap's lambda is then the one value the
  gaps and the earlier lambdas fix (`lambdaBad_fixed`);
* **a sumcheck round**: a round's challenge is a root of its gap, a nonzero polynomial of degree
  at most two that the round's claim, message and earlier challenges fix (`BadRound`,
  `badRound_roots`).

Every bad value is fixed before the challenge is squeezed from the sponge, which absorbed what
fixes it. The lambdas and challenges are Keccak-f[1600] outputs computed by the guest: that a bad
one is improbable is the in-guest hash heuristic, not a theorem here; `LeanVM.Guest.Batch.Rom`
bounds it with Keccak-256 and Keccak-f[1600] random oracles.
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-! ## The transcript -/

/-- The lambdas, a pair per child. -/
def lambdasB (cs : List ChildClaims) : List (E × E) := (sq2 cs.length (batchSponge cs)).1

/-- The batched claim. -/
def claimB (cs : List ChildClaims) : E := claimBOf cs (lambdasB cs)

/-- The sponge at the sumcheck. -/
def spB (cs : List ChildClaims) : Sponge := (sq2 cs.length (batchSponge cs)).2

/-- **`Node.batch` in the transcript's names**: the deferred claim at the sumcheck's
challenges, if the final check passes. -/
theorem batch_eq' (cs : List ChildClaims) (h : BatchHints) :
    batch cs h =
      if (rsRun h.bytecodeRounds (claimB cs) (spB cs)).1.2 = h.bytecodeValue *
            bytecodeWeight cs (lambdasB cs) (rsRun h.bytecodeRounds (claimB cs) (spB cs)).1.1 then
        some ⟨(rsRun h.bytecodeRounds (claimB cs) (spB cs)).1.1, h.bytecodeValue⟩
      else none :=
  batch_eq cs h

/-! ## The bad challenges -/

/-- The gaps the children's claims on the bytecode leave, claimed less true, in the order of
their lambdas. -/
def gapsB (bytecode : List K) (cs : List ChildClaims) : List E :=
  cs.flatMap fun c ↦
    [c.fresh.bytecodeValue - multilinearEval (bytecode.map ofK) c.fresh.bytecodePoint,
      c.carried.bytecodeValue - multilinearEval (bytecode.map ofK) c.carried.bytecodePoint]

/-- **The lambdas are bad** for the gaps: some gap is nonzero, and the lambdas' combination of
the gaps vanishes. -/
def LambdaBad (gaps lambdas : List E) : Prop :=
  (∃ g ∈ gaps, g ≠ 0) ∧ dot lambdas gaps = 0

/-- **A bad lambda is fixed by the earlier ones**: the last nonzero gap's lambda is the
combination of the earlier lambdas with their gaps, divided by its gap. -/
theorem lambdaBad_fixed {gaps lambdas : List E} (hl : lambdas.length = gaps.length)
    (h : LambdaBad gaps lambdas) :
    ∃ k < gaps.length, gaps.getD k 0 ≠ 0 ∧ (∀ i, k < i → gaps.getD i 0 = 0) ∧
      lambdas.getD k 0 =
        (∑ i ∈ Finset.range k, lambdas.getD i 0 * gaps.getD i 0) / gaps.getD k 0 := by
  obtain ⟨⟨g, hg, hg0⟩, hdot⟩ := h
  rw [Whir.Complete.dot_eq_sum _ _ hl] at hdot
  have hex : ∃ k, k < gaps.length ∧ gaps.getD k 0 ≠ 0 := by
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    exact ⟨k, hk, by rwa [List.getD_eq_getElem _ _ hk]⟩
  classical
  let k := Nat.findGreatest (fun k ↦ gaps.getD k 0 ≠ 0) gaps.length
  obtain ⟨k0, hk0, hk0'⟩ := hex
  have hkspec : gaps.getD k 0 ≠ 0 := Nat.findGreatest_spec (P := fun k ↦ gaps.getD k 0 ≠ 0)
    hk0.le hk0'
  have hklt : k < gaps.length := by
    by_contra hge
    exact hkspec (List.getD_eq_default _ _ (by omega))
  have hafter : ∀ i, k < i → gaps.getD i 0 = 0 := by
    intro i hi
    by_cases hil : i ≤ gaps.length
    · by_contra hne
      have := Nat.le_findGreatest (P := fun k ↦ gaps.getD k 0 ≠ 0) hil hne
      omega
    · exact List.getD_eq_default _ _ (by omega)
  refine ⟨k, hklt, hkspec, hafter, ?_⟩
  rw [eq_div_iff hkspec]
  have hIco : ∑ i ∈ Finset.Ico (k + 1) gaps.length, lambdas.getD i 0 * gaps.getD i 0 = 0 :=
    Finset.sum_eq_zero fun i hi ↦ by
      rw [hafter i (by simp only [Finset.mem_Ico] at hi; omega), mul_zero]
  have hsplit : ∑ i ∈ Finset.range lambdas.length, lambdas.getD i 0 * gaps.getD i 0 =
      ∑ i ∈ Finset.range k, lambdas.getD i 0 * gaps.getD i 0 +
        lambdas.getD k 0 * gaps.getD k 0 := by
    rw [hl, ← Finset.sum_range_add_sum_Ico _ (show k + 1 ≤ gaps.length by omega), hIco,
      add_zero, Finset.sum_range_succ]
  rw [hsplit] at hdot
  have := congrArg (· + lambdas.getD k 0 * gaps.getD k 0) hdot
  simpa [add_assoc, CharTwo.add_self_eq_zero] using this.symm

/-- The flattened pairs of lambdas. -/
abbrev flat2 (l : List (E × E)) : List E := l.flatMap fun p ↦ [p.1, p.2]

/-- **A challenge of the batching is bad**: its lambdas, or a round of its sumcheck. -/
def BatchBad (bytecode : List K) (cs : List ChildClaims) (h : BatchHints) : Prop :=
  LambdaBad (gapsB bytecode cs) (flat2 (lambdasB cs)) ∨
    ∃ j < h.bytecodeRounds.length, BadRound h.bytecodeRounds.length
      (bytecodePoly bytecode cs (lambdasB cs)) h.bytecodeRounds (claimB cs) (spB cs) j

/-! ## Soundness -/

/-- Claimed less true values, combined by pairs of lambdas, is the lambdas' combination of the
gaps. -/
theorem sub_pairs {α : Type} (cs : List α) (l : List (E × E)) (hl : l.length = cs.length)
    (a b a' b' : α → E) :
    sumE (List.zipWith (fun c l ↦ l.1 * a c + l.2 * b c) cs l) -
        sumE (List.zipWith (fun c l ↦ l.1 * a' c + l.2 * b' c) cs l) =
      dot (flat2 l) (cs.flatMap fun c ↦ [a c - a' c, b c - b' c]) := by
  induction cs generalizing l with
  | nil => simp
  | cons c cs ih =>
    obtain _ | ⟨x, l⟩ := l
    · simp at hl
    · simp only [List.zipWith_cons_cons, Whir.Complete.sumE_eq, List.sum_cons,
        List.flatMap_cons, List.cons_append, List.nil_append, Whir.Complete.dot_cons] at ih ⊢
      rw [← ih l (by simpa using hl)]
      ring

/-- Either every gap is zero, or the lambdas are bad, or the claimed combination is not the true
one. -/
theorem gaps_cases {gaps lambdas : List E} {claimed true_ : E}
    (h : claimed - true_ = dot lambdas gaps) :
    (∀ g ∈ gaps, g = 0) ∨ LambdaBad gaps lambdas ∨ claimed ≠ true_ := by
  by_cases hz : ∀ g ∈ gaps, g = 0
  · exact Or.inl hz
  · by_cases hd : dot lambdas gaps = 0
    · push Not at hz
      exact Or.inr (Or.inl ⟨hz, hd⟩)
    · exact Or.inr (Or.inr fun he ↦ hd (by rw [← h, he, sub_self]))

/-- The lambdas' combination of the claimed values, less that of the true ones, is their
combination of the gaps. -/
theorem claimB_sub (bytecode : List K) (cs : List ChildClaims) (l : List (E × E))
    (hl : l.length = cs.length) :
    claimBOf cs l - bytecodeTrue bytecode cs l = dot (flat2 l) (gapsB bytecode cs) :=
  sub_pairs cs l hl (fun c ↦ c.fresh.bytecodeValue) (fun c ↦ c.carried.bytecodeValue)
    (fun c ↦ multilinearEval (bytecode.map ofK) c.fresh.bytecodePoint)
    (fun c ↦ multilinearEval (bytecode.map ofK) c.carried.bytecodePoint)

/-- Zero gaps are true claims, for points of the bytecode's shape. -/
theorem holds_of_gaps {bytecode : List K} {cs : List ChildClaims}
    (hz : ∀ g ∈ gapsB bytecode cs, g = 0) (hpow : 2 ^ Nat.log2 bytecode.length = bytecode.length)
    (hc : ∀ c ∈ cs, c.carried.Shaped bytecode) :
    ∀ c ∈ cs, c.fresh.Holds bytecode ∧ c.carried.Holds bytecode := by
  intro c hc'
  have g := fun g hg ↦ hz g (List.mem_flatMap.mpr ⟨c, hc', hg⟩)
  have e1 := sub_eq_zero.mp (g _ (List.mem_cons_self ..))
  have e2 := sub_eq_zero.mp (g _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  refine ⟨e1.symm, hc c hc', ?_, e2.symm⟩
  rw [hc c hc', hpow]

/-- **The batching is sound, challenge by challenge**: an accepted batching whose deferred claim
holds, of children whose claims have the bytecode's shape, makes every child's claims true, or
one of its challenges is bad. -/
theorem batch_sound {bytecode : List K} {cs : List ChildClaims} {h : BatchHints}
    {d : DeferredClaim} (hb : batch cs h = some d) (hd : d.Holds bytecode)
    (hf : ∀ c ∈ cs, c.fresh.bytecodePoint.length = Nat.log2 bytecode.length)
    (hc : ∀ c ∈ cs, c.carried.Shaped bytecode) :
    (∀ c ∈ cs, c.fresh.Holds bytecode ∧ c.carried.Holds bytecode) ∨ BatchBad bytecode cs h := by
  rw [batch_eq'] at hb
  split_ifs at hb with hfin
  injection hb with hd'
  subst hd'
  obtain ⟨hlog, hpow, hval⟩ := hd
  simp only [DeferredClaim.Shaped] at hlog hpow hval
  rw [length_rsRun] at hlog hpow
  set n := h.bytecodeRounds.length
  have hlog' : Nat.log2 bytecode.length = n := by rw [← hpow, Nat.log2_two_pow]
  have hpB : ∀ c ∈ cs, c.fresh.bytecodePoint.length = n ∧ c.carried.bytecodePoint.length = n :=
    fun c hc' ↦ ⟨(hf c hc').trans hlog', (hc c hc').trans hlog'⟩
  rcases gaps_cases (claimB_sub bytecode cs (lambdasB cs) (length_sq2 _ _)) with hz | hbad | hne
  · exact Or.inl (holds_of_gaps hz (by rw [hlog', hpow]) hc)
  · exact Or.inr (Or.inl hbad)
  · refine Or.inr (Or.inr (rounds_sound rfl ?_ ?_))
    · rw [roundChallenges, hfin, bytecodePoly, hval]
    · rw [bytecode_cubeSum hpow.symm hpB]; exact hne

end
end LeanVM.Guest.Batch
