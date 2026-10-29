/-
  LeanVM.Guest.Budget.Covered

  What the deployed budget covers, proved: every recursion node within the deployed limits (at
  most `16` children, each at any of the guest's opening arms) of at most `2048` declared claims,
  coverage slots and children's claims, with no raw signature or blob held directly, and every
  leaf of at most `2048` raw signatures, declared claims and coverage slots, with no blob held
  directly, has a valid execution of the guest of committed size in `[2^22, 2^28]`.
-/

module

public import LeanVM.Guest.Budget.ClosedN
public import LeanVM.Guest.Count.Deployed
public import Statement.Corollaries

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Node LeanVM.Protocol
open LeanVM.Protocol.KeccakHash
open LeanVM.Guest.End (work bytecode publicInputOf)

@[expose] public section

/-- **`sizeOf` at counts within powers of two**: the words within `2^24` and each opcode's
instructions within `2^(k op)`. -/
theorem sizeOf_le_pow {w : ℕ} {i : Opcode → ℕ} (k : Opcode → ℕ) (hw : w ≤ 2 ^ 24)
    (hi : ∀ op, i op ≤ 2 ^ k op) :
    End.sizeOf w i ≤ 4 * 2 ^ 24 + 2 ^ 19 + 15 * 2 ^ k .xor + 15 * 2 ^ k .mulNative +
      8 * 2 ^ k .setConstant + 15 * 2 ^ k .deref + 14 * 2 ^ k .jump +
      26 * 2 ^ max (k .keccak) 9 + 2 ^ 6 * 2 ^ max (k .keccak) 9 := by
  have hh : ∀ op, 2 ^ Nat.clog 2 (i op) ≤ 2 ^ k op := fun op ↦
    Nat.pow_le_pow_right (by norm_num) (Nat.clog_le_of_le_pow (hi op))
  have hk : 2 ^ max (Nat.clog 2 (i .keccak)) 9 ≤ 2 ^ max (k .keccak) 9 :=
    Nat.pow_le_pow_right (by norm_num) (max_le_max (Nat.clog_le_of_le_pow (hi .keccak)) le_rfl)
  have hm : 2 ^ End.padLog w ≤ 2 ^ 24 := by
    refine Nat.pow_le_pow_right (by norm_num) (max_le (max_le ?_ (Nat.clog_le_of_le_pow hw)) ?_)
    · unfold minLogMem; omega
    · omega
  dsimp only [End.sizeOf]
  rw [guest_logSize]
  have := hh .xor; have := hh .mulNative; have := hh .setConstant; have := hh .deref
  have := hh .jump
  omega

/-- A list's entries within `M` bound its entries by index. -/
theorem getD_le_of_forall {l : List ℕ} {M : ℕ} (h : ∀ x ∈ l, x ≤ M) (i : ℕ) : l.getD i 0 ≤ M := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => exact Nat.zero_le _
  | some x => exact h x (List.mem_of_getElem? hi)

/-- The children's charges, each within `M`, at most `16` children. -/
theorem shapes_sum_le {ps : List (ℕ × ℕ)} (f : ℕ → ℕ → ℕ) {M : ℕ} (hf : ∀ μ r, f μ r ≤ M)
    (hl : ps.length ≤ 16) : (ps.map fun p ↦ f p.1 p.2).sum ≤ 16 * M := by
  have h := List.sum_le_length_nsmul (ps.map fun p ↦ f p.1 p.2) M (by
    intro x hx
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx
    exact hf p.1 p.2)
  rw [List.length_map, smul_eq_mul] at h
  exact h.trans (Nat.mul_le_mul_right M hl)

/-- **A recursion node of at most `2048` claims fits**: no raw signature or blob held directly,
at most `16` children (each charged at the largest of the guest's opening arms, `μ = 28` at rate
`1`), at most `2048` declared claims, coverage slots and children's claims. -/
theorem recursion_size_le (u : End.Work) (hx : u.rawXmss = 0) (hs : u.rawSphincs = 0)
    (hd : u.rawDa = 0) (hr : u.rawDaRows = 0) (hp : u.rawDaPad = 0) (hdecl : u.declared ≤ 2048)
    (hcov : u.coverage ≤ 2048) (hcc : u.childClaims ≤ 2048) (hch : u.children ≤ 16)
    (hlen : u.childShapes.length ≤ 16) :
    (deployedBudget deployedBvAt).size u ≤ 2 ^ 28 := by
  unfold End.Budget.size
  rw [Count.deployedBudget_words]
  simp only [Count.deployedBudget_instrs]
  refine le_trans (sizeOf_le_pow (fun op ↦ match op with
    | .xor => 21 | .mulNative => 22 | .setConstant => 20 | .deref => 21 | .jump => 19
    | .keccak => 18) ?_ ?_) (by norm_num)
  · have hb := shapes_sum_le deployedBvAt deployedBvAt_le hlen
    simp only [End.Linear.eval, Count.deployedWords]
    rw [hx, hs, hd, hr, hp]
    omega
  · intro op
    cases op
    · have hb := shapes_sum_le (Count.deployedInstrs .xor).childShape (M := 127240)
        (fun μ r ↦ getD_le_of_forall (by decide) (B1.Whir.candidate μ r)) hlen
      simp only [End.Linear.eval, Count.deployedInstrs] at hb ⊢
      rw [hx, hs, hd, hr, hp]
      omega
    · have hb := shapes_sum_le (Count.deployedInstrs .mulNative).childShape (M := 227525)
        (fun μ r ↦ getD_le_of_forall (by decide) (B1.Whir.candidate μ r)) hlen
      simp only [End.Linear.eval, Count.deployedInstrs] at hb ⊢
      rw [hx, hs, hd, hr, hp]
      omega
    · have hb := shapes_sum_le (Count.deployedInstrs .setConstant).childShape (M := 49330)
        (fun μ r ↦ getD_le_of_forall (by decide) (B1.Whir.candidate μ r)) hlen
      simp only [End.Linear.eval, Count.deployedInstrs] at hb ⊢
      rw [hx, hs, hd, hr, hp]
      omega
    · have hb := shapes_sum_le (Count.deployedInstrs .deref).childShape (M := 124274)
        (fun μ r ↦ getD_le_of_forall (by decide) (B1.Whir.candidate μ r)) hlen
      simp only [End.Linear.eval, Count.deployedInstrs] at hb ⊢
      rw [hx, hs, hd, hr, hp]
      omega
    · have hb := shapes_sum_le (Count.deployedInstrs .jump).childShape (M := 30812)
        (fun μ r ↦ getD_le_of_forall (by decide) (B1.Whir.candidate μ r)) hlen
      simp only [End.Linear.eval, Count.deployedInstrs] at hb ⊢
      rw [hx, hs, hd, hr, hp]
      omega
    · have hb := shapes_sum_le (Count.deployedInstrs .keccak).childShape (M := 9979)
        (fun μ r ↦ getD_le_of_forall (by decide) (B1.Whir.candidate μ r)) hlen
      simp only [End.Linear.eval, Count.deployedInstrs] at hb ⊢
      rw [hx, hs, hd, hr, hp]
      omega

/-- **A leaf of at most `2048` raw signatures fits**: no child and no blob held directly, at
most `2048` raw leanXMSS and leanSPHINCS signatures together, at most `2048` declared claims and
coverage slots. -/
theorem leaf_size_le (u : End.Work) (hxs : u.rawXmss + u.rawSphincs ≤ 2048) (hd : u.rawDa = 0)
    (hr : u.rawDaRows = 0) (hp : u.rawDaPad = 0) (hdecl : u.declared ≤ 2048) (hcov : u.coverage ≤ 2048)
    (hch : u.children = 0) (hcc : u.childClaims = 0) (hsh : u.childShapes = []) :
    (deployedBudget deployedBvAt).size u ≤ 2 ^ 28 := by
  unfold End.Budget.size
  rw [Count.deployedBudget_words]
  simp only [Count.deployedBudget_instrs]
  refine le_trans (sizeOf_le_pow (fun op ↦ match op with
    | .xor => 21 | .mulNative => 20 | .setConstant => 20 | .deref => 19 | .jump => 19
    | .keccak => 20) ?_ ?_) (by norm_num)
  · simp only [End.Linear.eval, Count.deployedWords]
    rw [hd, hr, hp, hch, hcc, hsh]
    simp only [List.map_nil, List.sum_nil]
    omega
  · intro op
    cases op <;> simp only [End.Linear.eval, Count.deployedInstrs] <;> rw [hd, hr, hp, hch, hcc, hsh] <;>
      simp only [List.map_nil, List.sum_nil] <;> omega

/-- **Every recursion node of at most `2048` claims has a valid execution of the guest**: for
every seed, statement `s` and witness `w` with `NodeRel`, within the deployed limits (so at most
`16` children, each at one of the guest's opening arms), the caps agreeing and no zero challenge
where the guest divides, holding no raw leanXMSS or leanSPHINCS signature and no blob directly,
with at most `2048` declared claims, coverage slots and children's claims, there is a valid
execution of the guest on the statement's digest of committed size in `[2^22, 2^28]`. -/
theorem guest_complete_recursion : GuestCompleteRecursion := by
  intro seed s w hrel hlim hok hx hs hd hdecl hcov hcc
  refine guest_complete_numeric seed s w hrel hlim hok (recursion_size_le _ hx hs
    (by simp [work, hd]) (by simp [work, hd]) (by simp [work, hd]) hdecl hcov hcc ?_ ?_)
  · simpa [work] using hlim.children
  · simpa [work] using hlim.children

/-- **Every leaf of at most `2048` raw signatures has a valid execution of the guest**: for every
seed, statement `s` and witness `w` with `NodeRel`, within the deployed limits, with no child and
no blob held directly, at most `2048` raw leanXMSS and leanSPHINCS signatures together and at most
`2048` declared claims and coverage slots, there is a valid execution of the guest on the
statement's digest of committed size in `[2^22, 2^28]`. -/
theorem guest_complete_leaf : GuestCompleteLeaf := by
  intro seed s w hrel hlim hok hch hd hxs hdecl hcov
  refine guest_complete_numeric seed s w hrel hlim hok (leaf_size_le _ hxs (by simp [work, hd])
    (by simp [work, hd]) (by simp [work, hd]) hdecl hcov ?_ ?_ ?_)
  · simp [work, hch]
  · simp [work, hch]
  · simp [work, hch]

end
end LeanVM.Guest.Budget
