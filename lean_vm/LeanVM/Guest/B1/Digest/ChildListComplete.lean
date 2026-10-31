/-
  LeanVM.Guest.B1.Digest.ChildListComplete

  `child_claim_list_digest`, completely: a child's claim list rebuilt at honest slots, and the
  memory an honest run leaves at its chain buffer, give its core IR relation.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListCLast
public import LeanVM.Guest.B1.Digest.ClaimListComplete

/-!
# `child_claim_list_digest`, completely

`ChildChainMem rd chain cells n`: the memory an honest run leaves at its chain buffer, the sponge
state after each group of `17` rebuilt claims at `chain · g^(13q)`.
`child_claim_list_digest_complete`: on a memory image, `n < 17 · 2^16` honest records
(`RecMem`, `ChildListOut`'s data: slots below the bound `g^L`, marks, canonical cells), the words
the range checks read (`BoundMem`) and that memory give the relation returning the cells' digest.
As `claim_list_digest_complete`: each branch evaluated on its own, the groups by `l17_block`
(`recMem_group`), the last claims by `ccLast_complete`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {rd : Reader}

/-- **The memory an honest run of `child_claim_list_digest` leaves** at its chain buffer `chain`:
after `q ≤ n / 17` groups, the sponge state after the first `68q` rebuilt cells, at
`chain · g^(13q)`. -/
def ChildChainMem (rd : Reader) (chain : E) (cells : List E) (n : ℕ) : Prop :=
  ∀ q ≤ n / 17, StateAt rd (chain * gen ^ (13 * q)) 0
    (absorbChunks (8 * q) zeroState (cellsBytes (cells.take (68 * q))))

/-- The records of the claims `s, …, s + k - 1`. -/
theorem recMem_group {cover origin limit entries base : E} {n : ℕ} {o : ℕ → ℕ} {cells : List E}
    (h : RecMem rd cover origin limit entries base n o cells) {s k : ℕ} (hsk : s + k ≤ n) :
    RecMem rd cover origin limit entries (base * gen ^ s) k (fun j => o (s + j))
      ((cells.drop (4 * s)).take (4 * k)) := by
  intro j hj
  obtain ⟨h1, h2, h3⟩ := h (s + j) (by omega)
  refine ⟨h1, by rwa [mul_assoc, ← pow_add], fun c hc => ?_⟩
  have e : ((cells.drop (4 * s)).take (4 * k)).getD (4 * j + c) 0 = cells.getD (4 * (s + j) + c) 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
    rw [ite_pos' (by omega), show 4 * s + (4 * j + c) = 4 * (s + j) + c by ring]
  rw [e]
  exact h3 c hc

theorem l17_shapeF : loopShapeF (coreProgram.getD 338 default) "__loop16" = true := by
  have h := l17c_ok
  simp only [l17cOk, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.1

/-- The groups of child claims: `__loop16`'s block at every group below `n / 17`. -/
theorem cc_blocks {entries cover base origin limit chain : E} {n L : ℕ} {o : ℕ → ℕ}
    {cells : List E} (hl : cells.length = 4 * n) (hc : AllCanonical cells)
    (hrec : RecMem rd cover origin limit entries base n o cells) (hL : limit = gen ^ L)
    (hL33 : L < 2 ^ 33) (hdef : BoundMem rd L) (hmem : ChildChainMem rd chain cells n) :
    ∀ j < n / 17, LoopBlock rd (coreProgram.getD 338 default) (gen ^ j) (gen ^ (n / 17))
      [chain, entries, cover, base, origin, limit] := by
  intro j hj
  have hS := hmem j (by omega)
  have hS1 := hmem (j + 1) (by omega)
  rw [show 68 * (j + 1) = 68 * j + 68 by ring, List.take_add, cellsBytes_append] at hS1
  have hpre : (cellsBytes (cells.take (68 * j))).length = rate * (8 * j) := by
    rw [length_cellsBytes, List.length_take, Nat.min_eq_left (by omega)]
    show 16 * (68 * j) = 136 * (8 * j); omega
  have hr := recMem_group hrec (s := 17 * j) (k := 17) (by omega)
  rw [show 4 * (17 * j) = 68 * j by ring, show 4 * 17 = 68 by rfl, mul_comm 17 j, pow_mul] at hr
  refine l17_block hpre (by rw [gen_pow_pow]; exact hS) (cells := ((cells.drop (68 * j)).take 68))
    (by simp; omega) (canon_take (canon_drop hc _) _) hr hL hL33 hdef fun c => ?_
  have := hS1 c
  rw [gen_pow_pow, loadHolds_mul_gen_pow]
  rw [loadHolds_mul_gen_pow, show 13 * (j + 1) + (0 + c.val) = 13 * j + (13 + c.val) by ring,
    show 8 * (j + 1) = 8 * j + 8 by ring] at this
  exact this

theorem cc_param (σ : Val) : (Fn.params Data.core24).map σ =
    [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5)] := rfl

theorem cc_cclNames {j : ℕ} (hj : j < cclNames.length) : cclNames[j] = cclNames.getD j "" := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl

end
end LeanVM.Guest.B1.Digest
