/-
  LeanVM.Guest.B1.Whir.SpecPrim

  The Spec's primitive steps, run on the carried sponge (`runF`), read backwards: what an
  accepting run of a step followed by a continuation tells.
-/

module

public import LeanVM.Guest.B1.Whir.RunF
public import LeanVM.Guest.B1.Whir.Positions
public import LeanVM.Protocol.WithHash

/-!
# Primitive steps, backwards

For each primitive (`readE`, `readN`, `sampleE`, `sampleN`, `grindP`, `commitP`, `queryP`,
`require`, `sampleQueries`) followed by a continuation `k`, an accepting `runF` splits into the
step's effect on the state (`FSt`) and an accepting run of `k`. `readN`, `sampleN` and
`sampleQueries` are solved in closed form (`absorbAll`, `squeezeN`, `queriesOf`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {α β : Type}

theorem runF_ret_some {a : α} {st : FSt} {r : α × FSt} (h : runF (Prog.ret a) st = some r) :
    r = (a, st) := (Option.some.inj h).symm

theorem runF_readE_bind {k : E → Prog β} {F : Fs} {xs : List E} {os : List Opening}
    {R : List (Digest × ℕ × ℕ)} {r : β × FSt} (h : runF (Prog.readScalar.bind k) ⟨F, xs, os, R⟩ = some r) :
    ∃ x xs', xs = x :: xs' ∧ runF (k x) ⟨F.absorb x dsObserve, xs', os, R⟩ = some r := by
  cases xs with
  | nil => simp [Prog.readScalar, Prog.bind, runF] at h
  | cons x xs => exact ⟨x, xs, rfl, h⟩

theorem runF_sampleE_bind (k : E → Prog β) (F : Fs) (xs : List E) (os : List Opening)
    (R : List (Digest × ℕ × ℕ)) :
    runF (Prog.sampleChallenge.bind k) ⟨F, xs, os, R⟩ = runF (k F.squeeze.1) ⟨F.squeeze.2, xs, os, R⟩ := rfl

theorem runF_grindP_bind {bits : ℕ} {k : Unit → Prog β} {F : Fs} {xs : List E} {os : List Opening}
    {R : List (Digest × ℕ × ℕ)} {r : β × FSt}
    (h : runF ((Prog.grindProofOfWork bits).bind k) ⟨F, xs, os, R⟩ = some r) :
    ∃ n xs', xs = n :: xs' ∧ powOk bits n (F.absorb n dsPowNonce).squeeze.1 = true ∧
      runF (k ()) ⟨(F.absorb n dsPowNonce).squeeze.2, xs', os, R⟩ = some r := by
  cases xs with
  | nil => simp [Prog.grindProofOfWork, Prog.bind, runF] at h
  | cons n xs =>
    simp only [Prog.grindProofOfWork, Prog.bind, runF] at h
    split at h
    · rename_i hp
      exact ⟨n, xs, rfl, hp, h⟩
    · simp at h

theorem runF_commitP_bind {hh ww : ℕ} {k : Unit → Prog β} {F : Fs} {xs : List E}
    {os : List Opening} {R : List (Digest × ℕ × ℕ)} {r : β × FSt}
    (h : runF ((Prog.readCommitment hh ww).bind k) ⟨F, xs, os, R⟩ = some r) :
    ∃ x0 x1 xs' d, xs = x0 :: x1 :: xs' ∧ digestOfScalars (x0, x1) = some d ∧
      runF (k ()) ⟨(F.absorb x0 dsObserve).absorb x1 dsObserve, xs', os, R ++ [(d, hh, ww)]⟩ =
        some r := by
  match xs with
  | [] => simp [Prog.readCommitment, Prog.bind, runF] at h
  | [_] => simp [Prog.readCommitment, Prog.bind, runF] at h
  | x0 :: x1 :: xs =>
    simp only [Prog.readCommitment, Prog.bind, runF] at h
    split at h
    · rename_i d hd
      exact ⟨x0, x1, xs, d, rfl, hd, h⟩
    · simp at h

theorem runF_queryP_bind {i : ℕ} {ps : List ℕ} {k : List (List K) → Prog β} {F : Fs}
    {xs : List E} {os : List Opening} {R : List (Digest × ℕ × ℕ)} {r : β × FSt}
    (h : runF ((Prog.queryOpenings i ps).bind k) ⟨F, xs, os, R⟩ = some r) :
    ∃ (root : Digest) (height width : ℕ) (rows : List (List K)) (rest : List Opening),
      R[i]? = some (root, height, width) ∧
      Id.run (Compile.openAllWithHash (m := Id) keccak256 root height width ps os) = some (rows, rest) ∧
      runF (k rows) ⟨F, xs, rest, R⟩ = some r := by
  simp only [Prog.queryOpenings, Prog.bind, runF] at h
  split at h
  · simp at h
  · rename_i root height width hr
    split at h
    · rename_i rows rest ho
      exact ⟨root, height, width, rows, rest, hr, ho, h⟩
    · simp at h

theorem runF_require_bind {c : Prop} [Decidable c] {k : Unit → Prog β} {st : FSt} {r : β × FSt}
    (h : runF ((Prog.require c).bind k) st = some r) : c ∧ runF (k ()) st = some r := by
  by_cases hc : c
  · simp only [Prog.require, hc, ↓reduceIte, Prog.ret_bind] at h
    exact ⟨hc, h⟩
  · simp [Prog.require, hc, Prog.bind, runF] at h

/-- **`readN n`, backwards**: the next `n` words, absorbed. -/
theorem runF_readN_bind : ∀ (n : ℕ) {k : List E → Prog β} {F : Fs} {xs : List E}
    {os : List Opening} {R : List (Digest × ℕ × ℕ)} {r : β × FSt},
    runF ((Prog.readScalars n).bind k) ⟨F, xs, os, R⟩ = some r →
      n ≤ xs.length ∧
      runF (k (xs.take n)) ⟨F.absorbAll (xs.take n) dsObserve, xs.drop n, os, R⟩ = some r
  | 0, k, F, xs, os, R, r, h => by
    refine ⟨Nat.zero_le _, ?_⟩
    simpa [Prog.readScalars, Fs.absorbAll] using h
  | n + 1, k, F, xs, os, R, r, h => by
    have e : (Prog.readScalars (n + 1)).bind k =
        Prog.readScalar.bind fun x ↦ (Prog.readScalars n).bind fun xs ↦ k (x :: xs) := by
      simp only [Prog.readScalars, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind]
    rw [e] at h
    obtain ⟨x, xs', hs, h1⟩ := runF_readE_bind h
    obtain ⟨hl, h2⟩ := runF_readN_bind n h1
    subst hs
    refine ⟨by simp; omega, ?_⟩
    simpa [Fs.absorbAll, List.take_succ_cons, List.drop_succ_cons] using h2

/-- **`sampleN n`**: the next `n` challenges. -/
theorem runF_sampleN_bind : ∀ (n : ℕ) (k : List E → Prog β) (F : Fs) (xs : List E)
    (os : List Opening) (R : List (Digest × ℕ × ℕ)),
    runF ((Prog.sampleChallenges n).bind k) ⟨F, xs, os, R⟩ =
      runF (k (F.squeezeN n).1) ⟨(F.squeezeN n).2, xs, os, R⟩
  | 0, k, F, xs, os, R => by simp [Prog.sampleChallenges, Fs.squeezeN]
  | n + 1, k, F, xs, os, R => by
    have e : (Prog.sampleChallenges (n + 1)).bind k =
        Prog.sampleChallenge.bind fun x ↦ (Prog.sampleChallenges n).bind fun xs ↦ k (x :: xs) := by
      simp only [Prog.sampleChallenges, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind]
    rw [e, runF_sampleE_bind, runF_sampleN_bind n]
    rfl

/-- **The query positions**: `ceilDiv rem (192/d)` challenges, cut into positions. -/
theorem runF_sampleQueriesAux_bind (d : ℕ) (hd : 1 ≤ 192 / d) :
    ∀ (fuel rem : ℕ) (k : List ℕ → Prog β) (F : Fs) (xs : List E) (os : List Opening)
      (R : List (Digest × ℕ × ℕ)), ceilDiv rem (192 / d) ≤ fuel →
      runF ((sampleQueriesAux d fuel rem).bind k) ⟨F, xs, os, R⟩ =
        runF (k (queriesOf (192 / d) d (F.squeezeN (ceilDiv rem (192 / d))).1 rem))
          ⟨(F.squeezeN (ceilDiv rem (192 / d))).2, xs, os, R⟩
  | fuel, 0, k, F, xs, os, R, _ => by
    rw [ceilDiv_zero]
    rcases fuel with _ | fuel <;> simp [sampleQueriesAux, queriesOf, Fs.squeezeN]
  | 0, rem + 1, k, F, xs, os, R, h => by
    have := ceilDiv_step (a := rem + 1) hd (Nat.succ_pos rem); omega
  | fuel + 1, rem + 1, k, F, xs, os, R, h => by
    have hs := ceilDiv_step (a := rem + 1) hd (Nat.succ_pos rem)
    have hp : (sampleQueriesAux d (fuel + 1) (rem + 1)).bind k = Prog.sampleChallenge.bind fun w ↦
        (sampleQueriesAux d fuel (rem + 1 - min (192 / d) (rem + 1))).bind fun rest ↦
          k (((List.range (min (192 / d) (rem + 1))).map fun c ↦
            (eToNat w >>> (c * d)) % 2 ^ d) ++ rest) := by
      simp only [sampleQueriesAux, Nat.add_one_ne_zero, ↓reduceIte, Prog.bind_eq, Prog.pure_eq,
        Prog.bind_assoc, Prog.ret_bind]
    rw [hp, runF_sampleE_bind, runF_sampleQueriesAux_bind d hd fuel _ _ _ _ _ _ (by omega), hs,
      queriesOf_cons _ _ hd]
    rfl

theorem ceilDiv_le_self {a b : ℕ} (hb : 1 ≤ b) : ceilDiv a b ≤ a := by
  unfold ceilDiv
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp only [Nat.zero_add]; exact (Nat.div_eq_of_lt (by omega)).le
  · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    apply Nat.div_le_of_le_mul
    have e : a' + 1 + (b' + 1) - 1 = a' + b' + 1 := by omega
    rw [e]
    nlinarith [Nat.zero_le (a' * b')]

theorem runF_sampleQueries_bind {d q : ℕ} (hd : 1 ≤ 192 / d) (k : List ℕ → Prog β) (F : Fs)
    (xs : List E) (os : List Opening) (R : List (Digest × ℕ × ℕ)) :
    runF ((sampleQueries d q).bind k) ⟨F, xs, os, R⟩ =
      runF (k (queriesOf (192 / d) d (F.squeezeN (ceilDiv q (192 / d))).1 q))
        ⟨(F.squeezeN (ceilDiv q (192 / d))).2, xs, os, R⟩ :=
  runF_sampleQueriesAux_bind d hd q q k F xs os R (ceilDiv_le_self hd)

end
end LeanVM.Guest.B1.Whir
