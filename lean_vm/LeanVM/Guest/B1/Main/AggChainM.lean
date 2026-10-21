/-
  LeanVM.Guest.B1.Main.AggChainM

  The Fiat-Shamir blocks of the batching loops read forward over a hash model: one absorb, a chain
  of absorbs, one squeeze, every step answered (`AggChain.lean` over a `HashModel`).
-/

module

public import LeanVM.Guest.B1.Main.AggChain
public import LeanVM.Guest.B1.Main.CalleesWM

/-!
# Absorb chains and squeezes over a hash model, forward

`fsNext_outM`: an `fs_next` block from the state of `cv` reads a word `x`, the model answers the
absorb (`obsCvM M cv x = some d`), and the block leaves the state of `d`. `obsChain_soundM`: a
chain of `n` of them reads `n` words `xs` at the cursor, the model answers the whole run
(`obsAllM M cv xs = some cv'`), the chain leaves the state of `cv'`. `squeeze_outM`: a `squeeze`
block from the state of `cv` leaves the state of the answered `sqCvM M cv` and its challenge.
No chaining value is named: each state is the digest the model answered for the step before.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {M : HashModel} {C : CallRel} {rd : Reader} {σ : Val}

/-- Absorbing a concatenation over the model is absorbing one list, then the other. -/
theorem obsAllM_append (cv : Digest) (xs ys : List E) :
    obsAllM M cv (xs ++ ys) = (obsAllM M cv xs).bind fun c => obsAllM M c ys := by
  induction xs generalizing cv with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, obsAllM, Option.bind_assoc]
    congr 1
    funext c
    exact ih c

/-- One more word absorbed over the model. -/
theorem obsAllM_take_succ (cv : Digest) (xs : List E) (k : ℕ) (hk : k < xs.length) :
    obsAllM M cv (xs.take (k + 1)) =
      (obsAllM M cv (xs.take k)).bind fun c => obsCvM M c (xs.getD k 0) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, List.getD_eq_getElem _ _ hk,
    Option.toList_some, obsAllM_append]
  congr 1
  funext c
  simp only [obsAllM]
  cases obsCvM M c xs[k] <;> rfl

/-- **An `fs_next` block over a model, forward** (`fsNext_out`): from the state of `cv`, the word
read and the answered state after it. -/
theorem fsNext_outM {s0 s1 cur : V} {j b : ℕ} {cv : Digest}
    (h : LoadHolds rd (σ cur) j (σ (.n b)) ∧ ∃ cv d, (σ s0, σ s1) = digestScalars cv ∧
      obsCvM M cv (σ (.n b)) = some d ∧
        ∀ k, 2 ≤ k → k < 14 → σ (.n (b + 1 + k)) = fsValsD (σ (.n b)) d 1 k)
    (hcv : (σ s0, σ s1) = digestScalars cv) :
    LoadHolds rd (σ cur) j (σ (.n b)) ∧ ∃ d, obsCvM M cv (σ (.n b)) = some d ∧
      (σ (.n (b + 13)), σ (.n (b + 14))) = digestScalars d := by
  obtain ⟨hl, cv', d, hcv', hd, e⟩ := h
  obtain rfl := digestScalars_injective (hcv'.symm.trans hcv)
  refine ⟨hl, d, hd, ?_⟩
  rw [show b + 13 = b + 1 + 12 by omega, show b + 14 = b + 1 + 13 by omega,
    e 12 (by omega) (by omega), e 13 (by omega) (by omega)]
  rfl

/-- **A `squeeze` block over a model, forward** (`squeeze_out`): from the state of `cv`, the
answered state after the squeeze and its challenge. -/
theorem squeeze_outM {s0 s1 : V} {b : ℕ} {cv : Digest}
    (h : ∃ cv d, (σ s0, σ s1) = digestScalars cv ∧ sqCvM M cv = some d ∧
      ∀ k, k < 14 → σ (.n (b + k)) = sqValsD d k)
    (hcv : (σ s0, σ s1) = digestScalars cv) :
    ∃ d, sqCvM M cv = some d ∧ (σ (.n (b + 5)), σ (.n (b + 6))) = digestScalars d ∧
      σ (.n (b + 13)) = challengeOf d := by
  obtain ⟨cv', d, hcv', hd, e⟩ := h
  obtain rfl := digestScalars_injective (hcv'.symm.trans hcv)
  refine ⟨d, hd, ?_, e 13 (by omega)⟩
  rw [e 5 (by omega), e 6 (by omega)]
  rfl

/-- **An absorb chain over a model, forward** (`obsChain_sound`): from the state of `cv`, the `n`
words at the cursor are read and absorbed, every step answered. -/
theorem obsChain_soundM (s0 s1 cur : V) (B n : ℕ) {next : Prop} {kret : List E → Prop}
    {cv : Digest} (h : Stmt.HoldsListB M.sem C rd σ (obsChainT s0 s1 cur B n) next kret)
    (hcv : (σ s0, σ s1) = digestScalars cv) :
    (∃ xs : List E, xs.length = n ∧ ReadsAt rd (σ cur) xs ∧ ∃ cv', obsAllM M cv xs = some cv' ∧
      (σ (chainS0 s0 B n), σ (chainS1 s1 B n)) = digestScalars cv') ∧ next := by
  rw [obsChainT, holdsListB_range_flatten _ _ (fun _ => rfl)] at h
  obtain ⟨h, hn⟩ := h
  refine ⟨?_, hn⟩
  have h' : ∀ k < n, LoadHolds rd (σ cur) k (σ (.n (B + 15 * k))) ∧ ∃ cv d,
      (σ (chainS0 s0 B k), σ (chainS1 s1 B k)) = digestScalars cv ∧
      obsCvM M cv (σ (.n (B + 15 * k))) = some d ∧ ∀ j, 2 ≤ j → j < 14 →
        σ (.n (B + 15 * k + 1 + j)) = fsValsD (σ (.n (B + 15 * k))) d 1 j :=
    fun k hk => (holdsB_fsNextT _ _ _ _ _ (h k hk)).1
  let xs := (List.range n).map fun k => σ (.n (B + 15 * k))
  have hlen : xs.length = n := by simp [xs]
  have hx : ∀ k < n, xs.getD k 0 = σ (.n (B + 15 * k)) := fun k hk => by
    simp [xs, List.getD_eq_getElem?_getD, hk]
  have key : ∀ m ≤ n, ∃ cv', obsAllM M cv (xs.take m) = some cv' ∧
      (σ (chainS0 s0 B m), σ (chainS1 s1 B m)) = digestScalars cv' := by
    intro m hm
    induction m with
    | zero => exact ⟨cv, rfl, by simpa [chainS0, chainS1] using hcv⟩
    | succ m ih =>
      obtain ⟨c, hc, hs⟩ := ih (by omega)
      obtain ⟨-, d, hd, hs'⟩ := fsNext_outM (h' m (by omega)) hs
      refine ⟨d, ?_, hs'⟩
      rw [obsAllM_take_succ _ _ _ (by omega), hc, hx m (by omega)]
      exact hd
  refine ⟨xs, hlen, fun k hk => ?_, ?_⟩
  · have := (h' k (by omega)).1
    rwa [← hx k (by omega), List.getD_eq_getElem _ _ hk] at this
  · obtain ⟨c, hc, hs⟩ := key n le_rfl
    rw [← hlen, List.take_length] at hc
    exact ⟨c, hc, hs⟩

end
end LeanVM.Guest.B1.Main
