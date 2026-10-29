/-
  LeanVM.Guest.B1.Main.AggCMath

  The honest rows, claims and weights of `aggregate_claims`, step by step.
-/

module

public import LeanVM.Guest.B1.Main.AggCLib
public import LeanVM.Guest.Batch.Def

/-!
# Honest values, step by step

`absSt_succ`: the next absorbing row's sponge absorbs the child's words as `__loop24` reads
them; `absSt_pend`: four scalars wait on every row; `absSt_last`: the last row's sponge is the
batching's. `claimAt_succ`, `weightAt_succ`: the running claim and weight on one child.
`kid_reads`: a child's words in memory, as the loops read them. `bsRun_cap`: the sumcheck leaves a
state's capacity and nothing waiting.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

variable {rd : Reader}

theorem absSt_zero (m : ℕ) (cs : List ChildClaims) :
    absSt m cs 0 = ⟨capOf batchSeed, [gen ^ m, 0, 0, 0].map (·, dsObserve)⟩ := by
  rw [absSt, List.take_zero, List.flatMap_nil, List.append_nil, absorb_head]

theorem absSt_succ {cpi cfresh ccarried : E} {m c : ℕ} {cs : List ChildClaims}
    (hc : c < cs.length) (hcw : ChildWordsAt rd cpi cfresh ccarried c cs[c]) :
    absSt m cs (c + 1) =
      (absSt m cs c).absorbAll (l25Words rd cpi cfresh ccarried (gen ^ c)) dsObserve := by
  obtain ⟨-, -, -, -, hw⟩ := kid_words hcw
  rw [absSt, absSt, List.take_succ_eq_append_getElem hc, List.flatMap_append,
    List.flatMap_singleton, ← List.append_assoc, absorbAll_append, ← hw]

theorem absSt_pend {cpi cfresh ccarried : E} {m : ℕ} {cs : List ChildClaims}
    (hcw : ∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c]) :
    ∀ c ≤ cs.length, (absSt m cs c).pend.length = 4
  | 0, _ => by rw [absSt_zero]; rfl
  | c + 1, hc => by
    have ih := absSt_pend (m := m) hcw c (by omega)
    rw [absSt_succ (by omega) (hcw c (by omega)), pend_absorbAll _ _ _ (by omega) (by omega), ih]
    simp [l25Words]

theorem absSt_last {m : ℕ} {cs : List ChildClaims} (hcl : cs.length = m) :
    absSt m cs m = aggAbs cs := by
  rw [absSt, List.take_of_length_le (by omega), aggAbs, Batch.batchWords, hcl]

theorem claimAt_zero (cs : List ChildClaims) : claimAt cs 0 = 0 := by simp [claimAt, sumE]

theorem claimAt_succ {cs : List ChildClaims} {c : ℕ} (hc : c < cs.length) :
    claimAt cs (c + 1) = claimAt cs c + (lamOf (aggAbs cs) c).1 * cs[c].fresh.bytecodeValue +
      (lamOf (aggAbs cs) c).2 * cs[c].carried.bytecodeValue := by
  rw [claimAt, claimAt, zip_prefix _ _ _ hc]
  ring

theorem weightAt_zero (cs : List ChildClaims) (h : BatchHints) : weightAt cs h 0 = 0 := by
  simp [weightAt, sumE]

theorem weightAt_succ {cs : List ChildClaims} {h : BatchHints} {c : ℕ} (hc : c < cs.length) :
    weightAt cs h (c + 1) = weightAt cs h c +
      (lamOf (aggAbs cs) c).1 * eqEval cs[c].fresh.bytecodePoint (aggRun cs h).1.1 +
      (lamOf (aggAbs cs) c).2 * eqEval cs[c].carried.bytecodePoint (aggRun cs h).1.1 := by
  rw [weightAt, weightAt, zip_prefix _ _ _ hc]
  ring

theorem aggLam_fst {m : ℕ} {cs : List ChildClaims} (hcl : cs.length = m) :
    (aggLam cs).1 = (List.range m).map (lamOf (aggAbs cs)) := by
  rw [aggLam, hcl, sq2F_fst]

theorem claimAt_last {m : ℕ} {cs : List ChildClaims} (hcl : cs.length = m) :
    claimAt cs m = Batch.claimBOf cs (aggLam cs).1 := by
  rw [claimAt, aggLam_fst hcl, List.take_of_length_le (by omega)]
  rfl

theorem weightAt_last {m : ℕ} {cs : List ChildClaims} (hcl : cs.length = m) (h : BatchHints) :
    weightAt cs h m = Batch.bytecodeWeight cs (aggLam cs).1 (aggRun cs h).1.1 := by
  rw [weightAt, aggLam_fst hcl, List.take_of_length_le (by omega)]
  rfl

/-- The sumcheck leaves a state's capacity and nothing waiting. -/
theorem bsRun_cap : ∀ (rounds : List (E × E)) (claim : E) (s : Fs), rounds ≠ [] →
    ∃ S, (bsRun rounds claim s).2 = ⟨capOf S, []⟩
  | [], _, _, h => absurd rfl h
  | (g1, gInf) :: rest, claim, s, _ => by
    cases rest with
    | nil => exact ⟨((s.absorb g1 dsObserve).absorb gInf dsObserve).perm, rfl⟩
    | cons r rest' =>
      rw [bsRun]
      exact bsRun_cap _ _ _ (by simp)

/-- The squeezing rows' last sponge: a state's capacity, nothing waiting. -/
theorem aggLam_snd {m : ℕ} {cs : List ChildClaims} (hcl : cs.length = m) (hm : 1 ≤ m) :
    (aggLam cs).2 = ⟨(sq2F m (aggAbs cs)).2.cap, []⟩ := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [aggLam, hcl, sq2F_snoc]
  rfl

/-- **A child's words in memory**, as the loops read them. -/
theorem kid_reads {cpi cfresh ccarried : E} {c : ℕ} {cc : ChildClaims}
    (h : ChildWordsAt rd cpi cfresh ccarried c cc) :
    cc.fresh.bytecodePoint.length = 23 ∧ cc.carried.bytecodePoint.length = 23 ∧
    ReadsAt rd (cfresh * (gen ^ c) ^ 24) cc.fresh.bytecodePoint ∧
    ReadsAt rd (ccarried * (gen ^ c) ^ 24) cc.carried.bytecodePoint ∧
    LoadHolds rd (cfresh * (gen ^ c) ^ 24) 23 cc.fresh.bytecodeValue ∧
    LoadHolds rd (ccarried * (gen ^ c) ^ 24) 23 cc.carried.bytecodeValue ∧
    (∀ o < 2, ∃ v, LoadHolds rd (cpi * (gen ^ c) ^ 2) o v) ∧
    (∀ o < 24, ∃ v, LoadHolds rd (cfresh * (gen ^ c) ^ 24) o v) ∧
    (∀ o < 24, ∃ v, LoadHolds rd (ccarried * (gen ^ c) ^ 24) o v) := by
  obtain ⟨h1, h2, hp0, hp1, hf, hc⟩ := h
  have b23 : bytecodeVars = 23 := rfl
  rw [b23] at h1 h2
  have e24 : (gen ^ c) ^ 24 = gen ^ (24 * c) := by rw [← pow_mul, mul_comm]
  have e2 : (gen ^ c) ^ 2 = gen ^ (2 * c) := by rw [← pow_mul, mul_comm]
  rw [e24, e2]
  have hf' : ReadsAt rd (cfresh * gen ^ (24 * c)) (cc.fresh.bytecodePoint ++ [cc.fresh.bytecodeValue]) := hf
  have hc' : ReadsAt rd (ccarried * gen ^ (24 * c))
      (cc.carried.bytecodePoint ++ [cc.carried.bytecodeValue]) := hc
  have hfl : (cc.fresh.bytecodePoint ++ [cc.fresh.bytecodeValue]).length = 24 := by simp [h1]
  have hcl : (cc.carried.bytecodePoint ++ [cc.carried.bytecodeValue]).length = 24 := by simp [h2]
  refine ⟨h1, h2, (readsAt_append.mp hf').1, (readsAt_append.mp hc').1, ?_, ?_, ?_,
    fun o ho => ⟨_, hf' o (by rw [hfl]; exact ho)⟩, fun o ho => ⟨_, hc' o (by rw [hcl]; exact ho)⟩⟩
  · have := hf' 23 (by rw [hfl]; omega)
    rwa [List.getElem_append_right (by rw [h1]), List.getElem_singleton] at this
  · have := hc' 23 (by rw [hcl]; omega)
    rwa [List.getElem_append_right (by rw [h2]), List.getElem_singleton] at this
  · intro o ho
    rcases (show o = 0 ∨ o = 1 by omega) with rfl | rfl
    · exact ⟨_, (loadHolds_mul_gen_pow rd _ _ _ _).mpr (by rw [add_zero]; exact hp0)⟩
    · exact ⟨_, (loadHolds_mul_gen_pow rd _ _ _ _).mpr hp1⟩

end
end LeanVM.Guest.B1.Main
