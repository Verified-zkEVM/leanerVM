/-
  LeanVM.Guest.B1.Terminal.Blocks

  The claims' blocks of `check_opening_terminal` (G:3094-3124): each adds its claim's term to the
  running sum and checks its low point's length against its column's.
-/

module

public import LeanVM.Guest.B1.Terminal.Template

/-!
# The claims' blocks

The words the blocks read are named by `valOf` (the word read at a place, by choice; a read
word is it, `valOf_eq`), the low points' lengths `cp j` given (`CpAt`). `claimsT_sound` gives
the sum's value: the start plus each claim's `claimTerm`, and each claim's length check
(`ClaimOk`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- The word at `p·g^k`, if one is read there (`0` otherwise). -/
noncomputable def valOf (rd : Reader) (p : E) (k : ℕ) : E :=
  open Classical in if h : ∃ v, LoadHolds rd p k v then h.choose else 0

theorem valOf_eq {p : E} {k : ℕ} {w : E} (h : LoadHolds rd p k w) : valOf rd p k = w := by
  have hex : ∃ v, LoadHolds rd p k v := ⟨w, h⟩
  simp only [valOf, hex, ↓reduceDIte]
  exact loadHolds_unique hex.choose_spec h

theorem eq_valOf {p : E} {k : ℕ} {w : E} (h : LoadHolds rd p k w) : w = valOf rd p k :=
  (valOf_eq h).symm

/-- Slot `s`'s eq factor over the six slot coordinates, top bit first. -/
def slotProd (s1 s0 : ℕ → E) (s : ℕ) : E :=
  let f := fun k ↦ if s.testBit k then s1 k else s0 k
  f 5 * f 4 * f 3 * f 2 * f 1 * f 0

/-- Claim `j`'s term of the sum, `cp j` its low point's length: the batching power at
`lam_pool` (`9`), the chain's value at `19` or `21`, the slot factor over the slot points (`23`,
`24`) or the public input's chain value (`33`), and the column's selector. -/
noncomputable def claimTerm (rd : Reader) (σ : Val) (cp : ℕ → ℕ) (j : ℕ) : E :=
  match termKind j with
  | 0 => valOf rd (σ (.n 9)) j * valOf rd (σ (.n 19)) (cp j) * σ (.n (selV (termCol j)))
  | 1 => valOf rd (σ (.n 9)) j * valOf rd (σ (.n 21)) (cp j) * σ (.n (selV (termCol j)))
  | 2 => valOf rd (σ (.n 9)) j * (slotProd (valOf rd (σ (.n 23))) (valOf rd (σ (.n 24))) (termSlot j) *
      valOf rd (σ (.n 21)) (cp j)) * σ (.n (selV 5))
  | 3 => valOf rd (σ (.n 9)) j * σ (.n 33) * σ (.n (selV (termCol j)))
  | _ => 0

/-- Claim `j`'s length check. -/
noncomputable def ClaimOk (rd : Reader) (σ : Val) (cp : ℕ → ℕ) (j : ℕ) : Prop :=
  match termKind j with
  | 0 => gen ^ cp j = valOf rd (σ (.n 11)) (termCol j)
  | 1 => gen ^ cp j = valOf rd (σ (.n 11)) (termCol j)
  | 2 => gen ^ cp j * word 64 0 0 = valOf rd (σ (.n 11)) 5
  | 3 => σ (.n 5) = valOf rd (σ (.n 11)) (termCol j)
  | _ => True

/-- Claim `j`'s length is read at `claim_cplen_g` as `g^(cp j)` (kinds `0 .. 2`). -/
def CpAt (rd : Reader) (σ : Val) (cp : ℕ → ℕ) (j : ℕ) : Prop :=
  termKind j < 3 → ∀ v, LoadHolds rd (σ (.n 7)) j v → v = gen ^ cp j

theorem zrT_sound {ch j c r acc n : ℕ} {CH KV L : E}
    (hcp : ∀ v, LoadHolds rd (σ (.n 7)) j v → v = gen ^ n)
    (hch : ∀ v, LoadHolds rd (σ (.n ch)) n v → v = CH)
    (hkv : ∀ v, LoadHolds rd (σ (.n 11)) c v → v = KV)
    (hlam : ∀ v, LoadHolds rd (σ (.n 9)) j v → v = L)
    {next : Prop} {kret : List E → Prop} (h : Stmt.HoldsList C rd σ (zrT ch j c r acc) next kret) :
    σ (.n (r + 7)) = σ (.n acc) + L * CH * σ (.n (selV c)) ∧ gen ^ n = KV ∧ next := by
  simp only [zrT, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨l0, e1, l2, l3, a4, l4, e5, e6, e7, hn⟩ := h
  have v0 := hcp _ l0
  rw [e1, v0, loadHolds_mul_gen_pow, Nat.add_zero] at l2
  refine ⟨?_, ?_, hn⟩
  · rw [e7, e6, e5, hlam _ l4, hch _ l2]
  · rw [← v0, ← hkv _ l3]; exact e_add_eq_zero_iff.mp a4

theorem slotPt_load {s k : ℕ} {s1 s0 : ℕ → E}
    (hs1 : ∀ k v, LoadHolds rd (σ (.n 23)) k v → v = s1 k)
    (hs0 : ∀ k v, LoadHolds rd (σ (.n 24)) k v → v = s0 k) {v : E}
    (h : LoadHolds rd (σ (.n (slotPt s k))) k v) : v = if s.testBit k then s1 k else s0 k := by
  unfold slotPt at h
  by_cases hb : s.testBit k
  · simp only [hb, ↓reduceIte] at h ⊢; exact hs1 _ _ h
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact hs0 _ _ h

theorem qT_sound {j s r acc n : ℕ} {CH KV L : E} {s1 s0 : ℕ → E}
    (hcp : ∀ v, LoadHolds rd (σ (.n 7)) j v → v = gen ^ n)
    (hch : ∀ v, LoadHolds rd (σ (.n 21)) n v → v = CH)
    (hkv : ∀ v, LoadHolds rd (σ (.n 11)) 5 v → v = KV)
    (hlam : ∀ v, LoadHolds rd (σ (.n 9)) j v → v = L)
    (hs1 : ∀ k v, LoadHolds rd (σ (.n 23)) k v → v = s1 k)
    (hs0 : ∀ k v, LoadHolds rd (σ (.n 24)) k v → v = s0 k)
    {next : Prop} {kret : List E → Prop} (h : Stmt.HoldsList C rd σ (qT j s r acc) next kret) :
    σ (.n (r + 21)) = σ (.n acc) + L * (slotProd s1 s0 s * CH) * σ (.n (selV 5)) ∧
      gen ^ n * word 64 0 0 = KV ∧ next := by
  simp only [qT, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨l0, l1, l2, e3, l4, e5, l6, e7, l8, e9, l10, e11, e12, l13, e14, c15, e16, l17, a18,
    l18, e19, e20, e21, hn⟩ := h
  have v0 := hcp _ l0
  rw [e12, v0, loadHolds_mul_gen_pow, Nat.add_zero] at l13
  refine ⟨?_, ?_, hn⟩
  · rw [e21, e20, e19, e14, e11, e9, e7, e5, e3, hlam _ l18, hch _ l13,
      slotPt_load hs1 hs0 l1, slotPt_load hs1 hs0 l2, slotPt_load hs1 hs0 l4,
      slotPt_load hs1 hs0 l6, slotPt_load hs1 hs0 l8, slotPt_load hs1 hs0 l10]
    rfl
  · rw [← v0, ← c15, ← e16, ← hkv _ l17]; exact e_add_eq_zero_iff.mp a18

theorem pT_sound {j c r acc : ℕ} {KV L : E}
    (hkv : ∀ v, LoadHolds rd (σ (.n 11)) c v → v = KV)
    (hlam : ∀ v, LoadHolds rd (σ (.n 9)) j v → v = L)
    {next : Prop} {kret : List E → Prop} (h : Stmt.HoldsList C rd σ (pT j c r acc) next kret) :
    σ (.n (r + 4)) = σ (.n acc) + L * σ (.n 33) * σ (.n (selV c)) ∧ σ (.n 5) = KV ∧ next := by
  simp only [pT, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨l0, a1, l1, e2, e3, e4, hn⟩ := h
  refine ⟨?_, ?_, hn⟩
  · rw [e4, e3, e2, hlam _ l1]
  · rw [← hkv _ l0]; exact e_add_eq_zero_iff.mp a1

/-- **The claims' blocks**: the sum's value is the start plus every claim's term, and every
claim's length check holds. -/
theorem claimsT_sound {cp : ℕ → ℕ} :
    ∀ (js : List ℕ) (r acc : ℕ) {next : Prop} {kret : List E → Prop},
      (∀ j ∈ js, CpAt rd σ cp j) →
      Stmt.HoldsList C rd σ (claimsT js r acc).1 next kret →
      σ (.n (claimsT js r acc).2.2) = σ (.n acc) + (js.map (claimTerm rd σ cp)).sum ∧
        (∀ j ∈ js, ClaimOk rd σ cp j) ∧ next
  | [], r, acc, next, kret, _, h => by
    simp only [claimsT, List.map_nil, List.sum_nil, add_zero, List.not_mem_nil,
      false_imp_iff, implies_true, true_and] at h ⊢
    exact h
  | j :: js, r, acc, next, kret, hb, h => by
    have hbj := hb j (List.mem_cons_self ..)
    have hbs : ∀ j' ∈ js, CpAt rd σ cp j' := fun j' h' ↦ hb j' (List.mem_cons_of_mem _ h')
    simp only [claimsT, holdsList_append] at h ⊢
    simp only [List.map_cons, List.sum_cons, List.forall_mem_cons]
    have L9 := fun v (h : LoadHolds rd (σ (.n 9)) j v) ↦ eq_valOf h
    have L11 := fun c v (h : LoadHolds rd (σ (.n 11)) c v) ↦ eq_valOf h
    rcases hk : termKind j with _ | _ | _ | _ | k
    · simp only [claimT, claimTerm, ClaimOk, hk] at h ⊢
      obtain ⟨e, ok, h⟩ := zrT_sound (hbj (by omega)) (fun v h ↦ eq_valOf h) (L11 _) L9 h
      obtain ⟨e', ok', hn⟩ := claimsT_sound js _ _ hbs h
      exact ⟨by rw [e', e, add_assoc], ⟨ok, ok'⟩, hn⟩
    · simp only [claimT, claimTerm, ClaimOk, hk] at h ⊢
      obtain ⟨e, ok, h⟩ := zrT_sound (hbj (by omega)) (fun v h ↦ eq_valOf h) (L11 _) L9 h
      obtain ⟨e', ok', hn⟩ := claimsT_sound js _ _ hbs h
      exact ⟨by rw [e', e, add_assoc], ⟨ok, ok'⟩, hn⟩
    · simp only [claimT, claimTerm, ClaimOk, hk] at h ⊢
      obtain ⟨e, ok, h⟩ := qT_sound (hbj (by omega)) (fun v h ↦ eq_valOf h) (L11 _) L9
        (fun _ _ h ↦ eq_valOf h) (fun _ _ h ↦ eq_valOf h) h
      obtain ⟨e', ok', hn⟩ := claimsT_sound js _ _ hbs h
      exact ⟨by rw [e', e, add_assoc], ⟨ok, ok'⟩, hn⟩
    · simp only [claimT, claimTerm, ClaimOk, hk] at h ⊢
      obtain ⟨e, ok, h⟩ := pT_sound (L11 _) L9 h
      obtain ⟨e', ok', hn⟩ := claimsT_sound js _ _ hbs h
      exact ⟨by rw [e', e, add_assoc], ⟨ok, ok'⟩, hn⟩
    · simp only [claimT, claimTerm, ClaimOk, hk] at h ⊢
      obtain ⟨e', ok', hn⟩ := claimsT_sound js _ _ hbs h
      exact ⟨by rw [e', zero_add], ⟨trivial, ok'⟩, hn⟩

end
end LeanVM.Guest.B1.VerifySub
