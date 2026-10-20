/-
  LeanVM.Guest.Batch.Sound

  The batching's soundness: an accepted batching whose deferred claim holds makes every child's
  claims true, unless one of its challenges is bad.
-/

module

public import LeanVM.Guest.Batch.Rounds
public import LeanVM.Guest.Batch.Bytecode
public import LeanVM.Guest.Batch.Matrix
public import LeanVM.Guest.B1.Main.BatchSpec

/-!
# The batching is sound, challenge by challenge

`Node.batch` absorbs the children's claims, squeezes lambdas, and runs two sumchecks, on the
bytecode and on flock's matrices, deferring one claim. `batch_sound`: if the batching accepts and
its deferred claim holds, then every child's claims hold (its proof's, `FixedClaims.Holds`, and
its statement's, `DeferredClaim.Holds`), or a challenge is bad (`BatchBad`):

* **a lambda step**: the children's claims leave nonzero gaps (claimed less true values), and the
  lambdas' combination of them vanishes. The last nonzero gap's lambda is then the one value the
  gaps and the earlier lambdas fix (`lambdaBad_fixed`);
* **a sumcheck round**: a round's challenge is a root of its gap, a nonzero polynomial of degree
  at most two that the round's claim, message and earlier challenges fix (`BadRound`,
  `badRound_roots`).

Every bad value is fixed before the challenge is squeezed from the chain, which absorbed what fixes
it. The lambdas and challenges are BLAKE2s outputs computed by the guest: that a bad one is
improbable is the in-guest hash heuristic, not a theorem here.
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Guest.B1 LeanVM.Guest.B1.Main

@[expose] public section

/-! ## The transcript -/

/-- The chain after absorbing the children's claims. -/
def batchCv (cs : List ChildClaims) : Digest :=
  obsAll (obsCv (blake2sBytes batchLabel) (ofK (gpow cs.length))) (cs.flatMap childCells)

/-- The bytecode's lambdas, a pair per child. -/
def lambdasB (cs : List ChildClaims) : List (E × E) := (sq2 cs.length (batchCv cs)).1

/-- The bytecode's batched claim. -/
def claimB (cs : List ChildClaims) : E :=
  sumE (List.zipWith (fun c l ↦ l.1 * c.fresh.bytecodeValue + l.2 * c.carried.bytecodeValue) cs
    (lambdasB cs))

/-- The chain at the bytecode's sumcheck. -/
def cvB (cs : List ChildClaims) : Digest := (sq2 cs.length (batchCv cs)).2

/-- The chain after the bytecode's sumcheck. -/
def cvB' (cs : List ChildClaims) (h : BatchHints) : Digest :=
  (bsRun h.bytecodeRounds (claimB cs) (cvB cs)).2

/-- The matrices' lambdas, a triple per child. -/
def lambdasM (cs : List ChildClaims) (h : BatchHints) : List (E × E × E) :=
  (sq3 cs.length (cvB' cs h)).1

/-- The matrices' batched claim. -/
def claimM (cs : List ChildClaims) (h : BatchHints) : E :=
  sumE (List.zipWith (fun c l ↦ l.1 * c.fresh.matrixValue + l.2.1 * c.carried.matrixA +
    l.2.2 * c.carried.matrixB) cs (lambdasM cs h))

/-- The chain at the matrices' sumcheck. -/
def cvM (cs : List ChildClaims) (h : BatchHints) : Digest := (sq3 cs.length (cvB' cs h)).2

/-- **`Node.batch` in the transcript's names**: the deferred claim at the two sumchecks'
challenges, if both final checks pass. -/
theorem batch_eq (cs : List ChildClaims) (h : BatchHints) :
    batch cs h =
      if (bsRun h.bytecodeRounds (claimB cs) (cvB cs)).1.2 = h.bytecodeValue *
            bytecodeWeight cs (lambdasB cs) (bsRun h.bytecodeRounds (claimB cs) (cvB cs)).1.1 ∧
          (bsRun h.matrixRounds (claimM cs h) (cvM cs h)).1.2 =
            h.matrixA * matrixWeightA cs (lambdasM cs h)
                (bsRun h.matrixRounds (claimM cs h) (cvM cs h)).1.1 +
              h.matrixB * matrixWeightB cs (lambdasM cs h)
                (bsRun h.matrixRounds (claimM cs h) (cvM cs h)).1.1 then
        some ⟨(bsRun h.bytecodeRounds (claimB cs) (cvB cs)).1.1, h.bytecodeValue,
          (bsRun h.matrixRounds (claimM cs h) (cvM cs h)).1.1, h.matrixA, h.matrixB⟩
      else none := by
  rw [batch_spec]
  simp only [batchRounds_run]
  rfl

/-! ## The bad challenges -/

/-- The gaps the children's claims on the bytecode leave, claimed less true, in the order of
their lambdas. -/
def gapsB (bytecode : List K) (cs : List ChildClaims) : List E :=
  cs.flatMap fun c ↦
    [c.fresh.bytecodeValue - multilinearEval (bytecode.map ofK) c.fresh.bytecodePoint,
      c.carried.bytecodeValue - multilinearEval (bytecode.map ofK) c.carried.bytecodePoint]

/-- The gaps the children's claims on the matrices leave, in the order of their lambdas. -/
def gapsM (cs : List ChildClaims) : List E :=
  cs.flatMap fun c ↦
    [c.fresh.matrixValue - blake2sBilinear c.fresh.alpha
        (lincheckRowWeights c.fresh.zSkip c.fresh.rowPoint)
        (lincheckColumnWeights c.fresh.columnPoint c.fresh.slices),
      c.carried.matrixA - (matrixValues c.carried.matrixPoint).1,
      c.carried.matrixB - (matrixValues c.carried.matrixPoint).2]

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

/-- **A challenge of the batching is bad**: the bytecode's lambdas, a round of its sumcheck, the
matrices' lambdas, or a round of theirs. -/
def BatchBad (bytecode : List K) (cs : List ChildClaims) (h : BatchHints) : Prop :=
  LambdaBad (gapsB bytecode cs) ((lambdasB cs).flatMap fun l ↦ [l.1, l.2]) ∨
  (∃ j < h.bytecodeRounds.length, BadRound h.bytecodeRounds.length
    (bytecodePoly bytecode cs (lambdasB cs)) h.bytecodeRounds (claimB cs) (cvB cs) j) ∨
  LambdaBad (gapsM cs) ((lambdasM cs h).flatMap fun l ↦ [l.1, l.2.1, l.2.2]) ∨
  ∃ j < h.matrixRounds.length, BadRound h.matrixRounds.length
    (matrixPoly cs (lambdasM cs h)) h.matrixRounds (claimM cs h) (cvM cs h) j

/-! ## Soundness -/

/-- A proof's claims on the fixed polynomials have the shapes of `bytecode`'s: the bus point of
`log₂` of its length, the lincheck's points of 8 coordinates and 64 slices. -/
def FreshShapedFor (bytecode : List K) (c : FixedClaims) : Prop :=
  c.bytecodePoint.length = Nat.log2 bytecode.length ∧ c.rowPoint.length = 8 ∧
    c.columnPoint.length = 8 ∧ c.slices.length = 64

theorem length_sq2 : ∀ (n : ℕ) (cv : Digest), (sq2 n cv).1.length = n
  | 0, _ => rfl
  | n + 1, cv => by simp [sq2, length_sq2 n]

theorem length_sq3 : ∀ (n : ℕ) (cv : Digest), (sq3 n cv).1.length = n
  | 0, _ => rfl
  | n + 1, cv => by simp [sq3, length_sq3 n]

theorem length_bsRun (rounds : List (E × E)) (claim : E) (cv : Digest) :
    (bsRun rounds claim cv).1.1.length = rounds.length := by
  rw [bsRun_eq]; simp

/-- Claimed less true values, combined by pairs of lambdas, is the lambdas' combination of the
gaps. -/
theorem sub_pairs {α : Type} (cs : List α) (l : List (E × E)) (hl : l.length = cs.length)
    (a b a' b' : α → E) :
    sumE (List.zipWith (fun c l ↦ l.1 * a c + l.2 * b c) cs l) -
        sumE (List.zipWith (fun c l ↦ l.1 * a' c + l.2 * b' c) cs l) =
      dot (l.flatMap fun l ↦ [l.1, l.2]) (cs.flatMap fun c ↦ [a c - a' c, b c - b' c]) := by
  induction cs generalizing l with
  | nil => simp
  | cons c cs ih =>
    obtain _ | ⟨x, l⟩ := l
    · simp at hl
    · simp only [List.zipWith_cons_cons, Whir.Complete.sumE_eq, List.sum_cons,
        List.flatMap_cons, List.cons_append, List.nil_append, Whir.Complete.dot_cons] at ih ⊢
      rw [← ih l (by simpa using hl)]
      ring

/-- Claimed less true values, combined by triples of lambdas. -/
theorem sub_triples {α : Type} (cs : List α) (l : List (E × E × E)) (hl : l.length = cs.length)
    (a b c a' b' c' : α → E) :
    sumE (List.zipWith (fun x l ↦ l.1 * a x + l.2.1 * b x + l.2.2 * c x) cs l) -
        sumE (List.zipWith (fun x l ↦ l.1 * a' x + l.2.1 * b' x + l.2.2 * c' x) cs l) =
      dot (l.flatMap fun l ↦ [l.1, l.2.1, l.2.2])
        (cs.flatMap fun x ↦ [a x - a' x, b x - b' x, c x - c' x]) := by
  induction cs generalizing l with
  | nil => simp
  | cons x cs ih =>
    obtain _ | ⟨y, l⟩ := l
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

/-- **The batching is sound, challenge by challenge**: an accepted batching whose deferred claim
holds, of children whose claims have the bytecode's shapes, makes every child's claims true, or
one of its challenges is bad. -/
theorem batch_sound {bytecode : List K} {cs : List ChildClaims} {h : BatchHints}
    {d : DeferredClaim} (hb : batch cs h = some d) (hd : d.Holds bytecode)
    (hf : ∀ c ∈ cs, FreshShapedFor bytecode c.fresh) (hc : ∀ c ∈ cs, c.carried.Shaped bytecode) :
    (∀ c ∈ cs, c.fresh.Holds bytecode ∧ c.carried.Holds bytecode) ∨ BatchBad bytecode cs h := by
  rw [batch_eq] at hb
  split_ifs at hb with hcond
  injection hb with hd'
  subst hd'
  obtain ⟨hfinB, hfinM⟩ := hcond
  obtain ⟨⟨hlogB, hlogM⟩, hpow, hvalB, hvalM⟩ := hd
  simp only at hlogB hlogM hpow hvalB hvalM
  rw [length_bsRun] at hlogB hlogM hpow
  set n := h.bytecodeRounds.length
  have hlog : Nat.log2 bytecode.length = n := by rw [← hpow, Nat.log2_two_pow]
  have hpB : ∀ c ∈ cs, c.fresh.bytecodePoint.length = n ∧ c.carried.bytecodePoint.length = n :=
    fun c hc' ↦ ⟨(hf c hc').1.trans hlog, (hc c hc').1.trans hlog⟩
  have hsM : ∀ c ∈ cs, MatrixShaped c :=
    fun c hc' ↦ ⟨(hf c hc').2.1, (hf c hc').2.2.1, (hf c hc').2.2.2, (hc c hc').2⟩
  -- the bytecode
  have hsubB := sub_pairs cs (lambdasB cs) (length_sq2 _ _)
    (fun c ↦ c.fresh.bytecodeValue) (fun c ↦ c.carried.bytecodeValue)
    (fun c ↦ multilinearEval (bytecode.map ofK) c.fresh.bytecodePoint)
    (fun c ↦ multilinearEval (bytecode.map ofK) c.carried.bytecodePoint)
  rcases gaps_cases hsubB with hzB | hbadB | hneB
  rotate_left
  · exact Or.inr (Or.inl hbadB)
  · refine Or.inr (Or.inr (Or.inl (rounds_sound rfl ?_ ?_)))
    · rw [roundChallenges, hfinB, bytecodePoly, hvalB]
    · rw [bytecode_cubeSum hpow.symm hpB]; exact hneB
  -- the matrices
  have hsubM := sub_triples cs (lambdasM cs h) (length_sq3 _ _)
    (fun c ↦ c.fresh.matrixValue) (fun c ↦ c.carried.matrixA) (fun c ↦ c.carried.matrixB)
    (fun c ↦ blake2sBilinear c.fresh.alpha (lincheckRowWeights c.fresh.zSkip c.fresh.rowPoint)
      (lincheckColumnWeights c.fresh.columnPoint c.fresh.slices))
    (fun c ↦ (matrixValues c.carried.matrixPoint).1)
    (fun c ↦ (matrixValues c.carried.matrixPoint).2)
  rcases gaps_cases hsubM with hzM | hbadM | hneM
  rotate_left
  · exact Or.inr (Or.inr (Or.inr (Or.inl hbadM)))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (rounds_sound rfl ?_ ?_))))
    · rw [roundChallenges, hfinM, matrixPoly, hvalM]
    · rw [hlogM, matrix_cubeSum hsM]; exact hneM
  -- every gap is zero
  refine Or.inl fun c hc' ↦ ?_
  have gB := fun g hg ↦ hzB g (List.mem_flatMap.mpr ⟨c, hc', hg⟩)
  have gM := fun g hg ↦ hzM g (List.mem_flatMap.mpr ⟨c, hc', hg⟩)
  have e1 := sub_eq_zero.mp (gB _ (List.mem_cons_self ..))
  have e2 := sub_eq_zero.mp (gB _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have e3 := sub_eq_zero.mp (gM _ (List.mem_cons_self ..))
  have e4 := sub_eq_zero.mp (gM _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have e5 := sub_eq_zero.mp
    (gM _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  refine ⟨⟨e1.symm, e3.symm⟩, hc c hc', ?_, e2.symm, Prod.ext e4.symm e5.symm⟩
  rw [(hpB c hc').2, hpow]

end
end LeanVM.Guest.Batch
