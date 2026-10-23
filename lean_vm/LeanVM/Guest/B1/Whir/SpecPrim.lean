/-
  LeanVM.Guest.B1.Whir.SpecPrim

  The Spec's primitive steps, run on the carried sponge (`runF`), read backwards: what an
  accepting run of a step followed by a continuation tells.
-/

module

public import LeanVM.Guest.B1.Whir.RunF
public import LeanVM.Guest.B1.Whir.Positions

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

theorem runF_readE_bind {k : E → Prog β} {st : FSt} {r : β × FSt}
    (h : runF (Prog.readE.bind k) st = some r) :
    ∃ x xs, st.stream = x :: xs ∧
      runF (k x) { st with sponge := st.sponge.absorb x dsObserve, stream := xs } = some r := by
  obtain ⟨F, s, os, R⟩ := st
  cases s with
  | nil => simp [Prog.readE, Prog.bind, runF] at h
  | cons x xs => exact ⟨x, xs, rfl, h⟩

theorem runF_sampleE_bind (k : E → Prog β) (st : FSt) :
    runF (Prog.sampleE.bind k) st =
      runF (k st.sponge.squeeze.1) { st with sponge := st.sponge.squeeze.2 } := rfl

theorem runF_grindP_bind {bits : ℕ} {k : Unit → Prog β} {st : FSt} {r : β × FSt}
    (h : runF ((Prog.grindP bits).bind k) st = some r) :
    ∃ n xs, st.stream = n :: xs ∧ powOk bits n (st.sponge.absorb n dsPowNonce).squeeze.1 = true ∧
      runF (k ()) { st with sponge := (st.sponge.absorb n dsPowNonce).squeeze.2, stream := xs } =
        some r := by
  obtain ⟨F, s, os, R⟩ := st
  cases s with
  | nil => simp [Prog.grindP, Prog.bind, runF] at h
  | cons n xs =>
    simp only [Prog.grindP, Prog.bind, runF] at h
    split at h
    · rename_i hp
      exact ⟨n, xs, rfl, hp, h⟩
    · simp at h

theorem runF_commitP_bind {hh ww : ℕ} {k : Unit → Prog β} {st : FSt} {r : β × FSt}
    (h : runF ((Prog.commitP hh ww).bind k) st = some r) :
    ∃ x0 x1 xs d, st.stream = x0 :: x1 :: xs ∧ digestOfScalars (x0, x1) = some d ∧
      runF (k ()) { st with
        sponge := (st.sponge.absorb x0 dsObserve).absorb x1 dsObserve
        stream := xs
        roots := st.roots ++ [(d, hh, ww)] } = some r := by
  obtain ⟨F, s, os, R⟩ := st
  match s with
  | [] => simp [Prog.commitP, Prog.bind, runF] at h
  | [_] => simp [Prog.commitP, Prog.bind, runF] at h
  | x0 :: x1 :: xs =>
    simp only [Prog.commitP, Prog.bind, runF] at h
    split at h
    · rename_i d hd
      exact ⟨x0, x1, xs, d, rfl, hd, h⟩
    · simp at h

theorem runF_queryP_bind {i : ℕ} {ps : List ℕ} {k : List (List K) → Prog β} {st : FSt}
    {r : β × FSt} (h : runF ((Prog.queryP i ps).bind k) st = some r) :
    ∃ (root : Digest) (height width : ℕ) (rows : List (List K)) (rest : List Opening),
      st.roots[i]? = some (root, height, width) ∧
      Id.run (Compile.openAll (m := Id) keccak256 root height width ps st.openings) =
        some (rows, rest) ∧
      runF (k rows) { st with openings := rest } = some r := by
  obtain ⟨F, s, os, R⟩ := st
  simp only [Prog.queryP, Prog.bind, runF] at h
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
theorem runF_readN_bind : ∀ (n : ℕ) {k : List E → Prog β} {st : FSt} {r : β × FSt},
    runF ((Prog.readN n).bind k) st = some r →
      n ≤ st.stream.length ∧
      runF (k (st.stream.take n)) { st with
        sponge := st.sponge.absorbAll (st.stream.take n) dsObserve
        stream := st.stream.drop n } = some r
  | 0, k, st, r, h => by
    refine ⟨Nat.zero_le _, ?_⟩
    simpa [Prog.readN, Fs.absorbAll] using h
  | n + 1, k, st, r, h => by
    have e : (Prog.readN (n + 1)).bind k =
        Prog.readE.bind fun x ↦ (Prog.readN n).bind fun xs ↦ k (x :: xs) := by
      simp only [Prog.readN, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind]
    rw [e] at h
    obtain ⟨x, xs, hs, h⟩ := runF_readE_bind h
    obtain ⟨hl, h⟩ := runF_readN_bind n h
    obtain ⟨F, s, os, R⟩ := st
    simp only at hs
    subst hs
    simp only at hl h ⊢
    refine ⟨by simp; omega, ?_⟩
    simpa [Fs.absorbAll, List.take_succ_cons, List.drop_succ_cons] using h

/-- **`sampleN n`**: the next `n` challenges. -/
theorem runF_sampleN_bind : ∀ (n : ℕ) (k : List E → Prog β) (st : FSt),
    runF ((Prog.sampleN n).bind k) st =
      runF (k (st.sponge.squeezeN n).1) { st with sponge := (st.sponge.squeezeN n).2 }
  | 0, k, st => by simp [Prog.sampleN, Fs.squeezeN]
  | n + 1, k, st => by
    have e : (Prog.sampleN (n + 1)).bind k =
        Prog.sampleE.bind fun x ↦ (Prog.sampleN n).bind fun xs ↦ k (x :: xs) := by
      simp only [Prog.sampleN, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind]
    rw [e, runF_sampleE_bind, runF_sampleN_bind n]
    rfl

/-- **The query positions**: `ceilDiv rem (192/d)` challenges, cut into positions. -/
theorem runF_sampleQueriesAux_bind (d : ℕ) (hd : 1 ≤ 192 / d) :
    ∀ (fuel rem : ℕ) (k : List ℕ → Prog β) (st : FSt), ceilDiv rem (192 / d) ≤ fuel →
      runF ((sampleQueriesAux d fuel rem).bind k) st =
        runF (k (queriesOf (192 / d) d (st.sponge.squeezeN (ceilDiv rem (192 / d))).1 rem))
          { st with sponge := (st.sponge.squeezeN (ceilDiv rem (192 / d))).2 }
  | fuel, 0, k, st, _ => by
    rw [ceilDiv_zero]
    rcases fuel with _ | fuel <;> simp [sampleQueriesAux, queriesOf, Fs.squeezeN]
  | 0, rem + 1, k, st, h => by
    have := ceilDiv_step (a := rem + 1) hd (Nat.succ_pos rem); omega
  | fuel + 1, rem + 1, k, st, h => by
    have hs := ceilDiv_step (a := rem + 1) hd (Nat.succ_pos rem)
    have hp : (sampleQueriesAux d (fuel + 1) (rem + 1)).bind k = Prog.sampleE.bind fun w ↦
        (sampleQueriesAux d fuel (rem + 1 - min (192 / d) (rem + 1))).bind fun rest ↦
          k (((List.range (min (192 / d) (rem + 1))).map fun c ↦
            (eToNat w >>> (c * d)) % 2 ^ d) ++ rest) := by
      simp only [sampleQueriesAux, Nat.add_one_ne_zero, ↓reduceIte, Prog.bind_eq, Prog.pure_eq,
        Prog.bind_assoc, Prog.ret_bind]
    rw [hp, runF_sampleE_bind, runF_sampleQueriesAux_bind d hd fuel _ _ _ (by omega), hs,
      queriesOf_cons _ _ hd]
    rfl

theorem runF_sampleQueries_bind {d q : ℕ} (hd : 1 ≤ 192 / d) (k : List ℕ → Prog β) (st : FSt) :
    runF ((sampleQueries d q).bind k) st =
      runF (k (queriesOf (192 / d) d (st.sponge.squeezeN (ceilDiv q (192 / d))).1 q))
        { st with sponge := (st.sponge.squeezeN (ceilDiv q (192 / d))).2 } :=
  runF_sampleQueriesAux_bind d hd q q k st (ceilDiv_le' hd)
where
  ceilDiv_le' {a b : ℕ} (hb : 1 ≤ b) : ceilDiv a b ≤ a := by
    unfold ceilDiv
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp only [Nat.zero_add]; exact (Nat.div_eq_of_lt (by omega)).le
    · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      apply Nat.div_le_of_le_mul
      have e : a' + 1 + (b' + 1) - 1 = a' + b' + 1 := by omega
      rw [e]
      nlinarith [Nat.zero_le (a' * b')]

end
end LeanVM.Guest.B1.Whir
