/-
  LeanVM.Guest.Child.Covered

  What the deployed budget covers beyond `Budget/Covered.lean`'s two families: recursion nodes of
  at most `8` children and `2^15` claims, mixed nodes, and nodes checking a matrix of up to `32`
  rows.
-/

module

public import LeanVM.Guest.Budget.Covered
public import Statement.LeanVmGuest

/-!
# The covered nodes

Each family of `Covered` is a size lemma like `recursion_size_le`: the budget's words within
`2^24` and each opcode's instructions within a power of two (`sizeOf_le_pow`), the children charged
at the largest opening arm (`shapes_sum_le_of`), the exponents chosen so that the committed size is
at most `2^28`:

| family | words | `XOR` | `MUL` | `SET` | `DEREF` | `JUMP` | `KECCAK` |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `≤ 8` children, `2^15` claims | `≤ 2^24` | `21` | `22` | `21` | `21` | `20` | `18` |
| `≤ 4` children, `1024` signatures, `8192` claims | `≤ 2^24` | `21` | `21` | `20` | `20` | `19` | `19` |
| `≤ 4` children, `32` rows, `8192` claims | `≤ 2^24` | `22` | `22` | `19` | `21` | `20` | `18` |
| `≤ 2` children, `256` signatures, `32` rows, `8192` claims | `≤ 2^24` | `22` | `22` | `19` | `21` | `20` | `18` |
| `≤ 2` children, `32` rows, `2^14` claims | `≤ 2^24` | `22` | `22` | `19` | `21` | `20` | `17` |
| no child, `32` rows, `2^15` claims | `≤ 2^24` | `22` | `22` | `20` | `21` | `20` | `17` |

A matrix of `r ≤ 32` rows is charged at its padded height `nPad r ≤ 32` too (`rawDaPad`).

`guest_complete_covered`: `GuestCompleteCovered`, from `guest_complete_numeric`.
-/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Node LeanVM.Protocol
open LeanVM.Protocol.KeccakHash
open LeanVM.Guest.End (work bytecode publicInputOf)

@[expose] public section

/-- The children's charges, each within `M`, at most `K` children. -/
theorem shapes_sum_le_of {ps : List (ℕ × ℕ)} (f : ℕ → ℕ → ℕ) {M K : ℕ} (hf : ∀ μ r, f μ r ≤ M)
    (hl : ps.length ≤ K) : (ps.map fun p ↦ f p.1 p.2).sum ≤ K * M := by
  have h := List.sum_le_length_nsmul (ps.map fun p ↦ f p.1 p.2) M (by
    intro x hx
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx
    exact hf p.1 p.2)
  rw [List.length_map, smul_eq_mul] at h
  exact h.trans (Nat.mul_le_mul_right M hl)

/-- The instruction charges of the children, each opcode's at its largest arm. -/
theorem instr_shapes {ps : List (ℕ × ℕ)} {K : ℕ} (hl : ps.length ≤ K) (op : Opcode) :
    (ps.map fun p ↦ (Count.deployedInstrs op).childShape p.1 p.2).sum ≤
      K * (match op with
        | .xor => 127240 | .mulNative => 227525 | .setConstant => 49330 | .deref => 124274
        | .jump => 30812 | .keccak => 9979) := by
  cases op <;>
    exact shapes_sum_le_of _ (fun μ r ↦ getD_le_of_forall (by decide) (B1.Whir.candidate μ r)) hl

/-- The size at the budget, from the words and each opcode's instructions. -/
theorem size_le_of (u : End.Work) (k : Opcode → ℕ)
    (hw : (Count.deployedWords deployedBvAt).eval u ≤ 2 ^ 24)
    (hi : ∀ op, (Count.deployedInstrs op).eval u ≤ 2 ^ k op)
    (hk : 4 * 2 ^ 24 + 2 ^ 19 + 15 * 2 ^ k .xor + 15 * 2 ^ k .mulNative +
      8 * 2 ^ k .setConstant + 15 * 2 ^ k .deref + 14 * 2 ^ k .jump +
      26 * 2 ^ max (k .keccak) 9 + 2 ^ 6 * 2 ^ max (k .keccak) 9 ≤ 2 ^ 28) :
    (deployedBudget deployedBvAt).size u ≤ 2 ^ 28 := by
  unfold End.Budget.size
  rw [Count.deployedBudget_words]
  simp only [Count.deployedBudget_instrs]
  exact le_trans (sizeOf_le_pow k hw hi) hk

/-- **A recursion node of at most `8` children and `2^15` claims fits.** -/
theorem narrow_size_le (u : End.Work) (hraw : u.rawXmss + u.rawSphincs = 0) (hd : u.rawDa = 0)
    (hr : u.rawDaRows = 0) (hp : u.rawDaPad = 0) (hdecl : u.declared ≤ 2 ^ 15) (hcov : u.coverage ≤ 2 ^ 15)
    (hcc : u.childClaims ≤ 2 ^ 15) (hch : u.children ≤ 8) (hlen : u.childShapes.length ≤ 8) :
    (deployedBudget deployedBvAt).size u ≤ 2 ^ 28 := by
  refine size_le_of u (fun op ↦ match op with
    | .xor => 21 | .mulNative => 22 | .setConstant => 21 | .deref => 21 | .jump => 20
    | .keccak => 18) ?_ (fun op ↦ ?_) (by norm_num)
  · have hb := shapes_sum_le_of deployedBvAt deployedBvAt_le hlen
    simp only [End.Linear.eval, Count.deployedWords]
    omega
  · have hb := instr_shapes hlen op
    cases op <;> simp only [End.Linear.eval, Count.deployedInstrs] at hb ⊢ <;> omega

/-- **A node of at most `4` children and `1024` raw signatures, with at most `8192` claims,
fits.** -/
theorem mixed_size_le (u : End.Work) (hraw : u.rawXmss + u.rawSphincs ≤ 1024) (hd : u.rawDa = 0)
    (hr : u.rawDaRows = 0) (hp : u.rawDaPad = 0) (hdecl : u.declared ≤ 8192) (hcov : u.coverage ≤ 8192)
    (hcc : u.childClaims ≤ 8192) (hch : u.children ≤ 4) (hlen : u.childShapes.length ≤ 4) :
    (deployedBudget deployedBvAt).size u ≤ 2 ^ 28 := by
  refine size_le_of u (fun op ↦ match op with
    | .xor => 21 | .mulNative => 21 | .setConstant => 20 | .deref => 20 | .jump => 19
    | .keccak => 19) ?_ (fun op ↦ ?_) (by norm_num)
  · have hb := shapes_sum_le_of deployedBvAt deployedBvAt_le hlen
    simp only [End.Linear.eval, Count.deployedWords]
    omega
  · have hb := instr_shapes hlen op
    cases op <;> simp only [End.Linear.eval, Count.deployedInstrs] at hb ⊢ <;> omega

/-- **A node of at most `4` children checking a matrix of at most `32` rows, with at most `8192` claims, fits.** -/
theorem blob_size_le (u : End.Work) (hraw : u.rawXmss + u.rawSphincs = 0) (hd : u.rawDa ≤ 1)
    (hr : u.rawDaRows ≤ 32) (hp : u.rawDaPad ≤ 32) (hdecl : u.declared ≤ 8192)
    (hcov : u.coverage ≤ 8192) (hcc : u.childClaims ≤ 8192) (hch : u.children ≤ 4)
    (hlen : u.childShapes.length ≤ 4) :
    (deployedBudget deployedBvAt).size u ≤ 2 ^ 28 := by
  refine size_le_of u (fun op ↦ match op with
    | .xor => 22 | .mulNative => 22 | .setConstant => 19 | .deref => 21 | .jump => 20
    | .keccak => 18) ?_ (fun op ↦ ?_) (by norm_num)
  · have hb := shapes_sum_le_of deployedBvAt deployedBvAt_le hlen
    simp only [End.Linear.eval, Count.deployedWords]
    omega
  · have hb := instr_shapes hlen op
    cases op <;> simp only [End.Linear.eval, Count.deployedInstrs] at hb ⊢ <;> omega

/-- **A node of at most `2` children and `256` raw signatures checking a matrix of at most `32` rows, with at most `8192` claims, fits.** -/
theorem blobMixed_size_le (u : End.Work) (hraw : u.rawXmss + u.rawSphincs ≤ 256) (hd : u.rawDa ≤ 1)
    (hr : u.rawDaRows ≤ 32) (hp : u.rawDaPad ≤ 32) (hdecl : u.declared ≤ 8192)
    (hcov : u.coverage ≤ 8192) (hcc : u.childClaims ≤ 8192) (hch : u.children ≤ 2)
    (hlen : u.childShapes.length ≤ 2) :
    (deployedBudget deployedBvAt).size u ≤ 2 ^ 28 := by
  refine size_le_of u (fun op ↦ match op with
    | .xor => 22 | .mulNative => 22 | .setConstant => 19 | .deref => 21 | .jump => 20
    | .keccak => 18) ?_ (fun op ↦ ?_) (by norm_num)
  · have hb := shapes_sum_le_of deployedBvAt deployedBvAt_le hlen
    simp only [End.Linear.eval, Count.deployedWords]
    omega
  · have hb := instr_shapes hlen op
    cases op <;> simp only [End.Linear.eval, Count.deployedInstrs] at hb ⊢ <;> omega

/-- **A node of at most `2` children checking a matrix of at most `32` rows, with at most `2^14` claims, fits.** -/
theorem blobWide_size_le (u : End.Work) (hraw : u.rawXmss + u.rawSphincs = 0) (hd : u.rawDa ≤ 1)
    (hr : u.rawDaRows ≤ 32) (hp : u.rawDaPad ≤ 32) (hdecl : u.declared ≤ 2 ^ 14)
    (hcov : u.coverage ≤ 2 ^ 14) (hcc : u.childClaims ≤ 2 ^ 14) (hch : u.children ≤ 2)
    (hlen : u.childShapes.length ≤ 2) :
    (deployedBudget deployedBvAt).size u ≤ 2 ^ 28 := by
  refine size_le_of u (fun op ↦ match op with
    | .xor => 22 | .mulNative => 22 | .setConstant => 19 | .deref => 21 | .jump => 20
    | .keccak => 17) ?_ (fun op ↦ ?_) (by norm_num)
  · have hb := shapes_sum_le_of deployedBvAt deployedBvAt_le hlen
    simp only [End.Linear.eval, Count.deployedWords]
    omega
  · have hb := instr_shapes hlen op
    cases op <;> simp only [End.Linear.eval, Count.deployedInstrs] at hb ⊢ <;> omega

/-- **A node of no child checking a matrix of at most `32` rows, with at most `2^15` declared claims and coverage slots, fits.** -/
theorem blobLeaf_size_le (u : End.Work) (hraw : u.rawXmss + u.rawSphincs = 0) (hd : u.rawDa ≤ 1)
    (hr : u.rawDaRows ≤ 32) (hp : u.rawDaPad ≤ 32) (hdecl : u.declared ≤ 2 ^ 15)
    (hcov : u.coverage ≤ 2 ^ 15) (hcc : u.childClaims = 0) (hch : u.children = 0)
    (hlen : u.childShapes.length ≤ 0) :
    (deployedBudget deployedBvAt).size u ≤ 2 ^ 28 := by
  refine size_le_of u (fun op ↦ match op with
    | .xor => 22 | .mulNative => 22 | .setConstant => 20 | .deref => 21 | .jump => 20
    | .keccak => 17) ?_ (fun op ↦ ?_) (by norm_num)
  · have hb := shapes_sum_le_of deployedBvAt deployedBvAt_le hlen
    simp only [End.Linear.eval, Count.deployedWords]
    omega
  · have hb := instr_shapes hlen op
    cases op <;> simp only [End.Linear.eval, Count.deployedInstrs] at hb ⊢ <;> omega

/-- **A matrix's padded height within a power of two**: at most one matrix held directly, of at
most `2^k` rows, is padded to at most `2^k` rows. -/
theorem pad_le {s : NodeStatement} {w : NodeWitness} {k : ℕ}
    (hd : (Hints.direct s.claims.da w.da).length ≤ 1) (hr : (work s w).rawDaRows ≤ 2 ^ k) :
    (work s w).rawDaPad ≤ 2 ^ k := by
  simp only [work] at hr ⊢
  match h : Hints.direct s.claims.da w.da, hd with
  | [], _ => simp
  | [p], _ =>
    rw [h] at hr
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
      LeanDa.nPad, LeanDa.logPad] at hr ⊢
    exact Nat.pow_le_pow_right (by norm_num) (Nat.clog_le_of_le_pow hr)
  | _ :: _ :: _, h' => simp at h'

/-- `Covered`, by the node's work: `Covered s w` is `CoveredW (work s w)` by definition. -/
def CoveredW (u : End.Work) : Prop :=
  (u.rawXmss + u.rawSphincs = 0 ∧ u.rawDa = 0 ∧
    u.declared ≤ 2048 ∧ u.coverage ≤ 2048 ∧ u.childClaims ≤ 2048) ∨
  (u.children = 0 ∧ u.rawDa = 0 ∧ u.rawXmss + u.rawSphincs ≤ 2048 ∧
    u.declared ≤ 2048 ∧ u.coverage ≤ 2048) ∨
  (u.children ≤ 8 ∧ u.rawXmss + u.rawSphincs = 0 ∧ u.rawDa = 0 ∧
    u.declared ≤ 2 ^ 15 ∧ u.coverage ≤ 2 ^ 15 ∧ u.childClaims ≤ 2 ^ 15) ∨
  (u.children ≤ 4 ∧ u.rawXmss + u.rawSphincs ≤ 1024 ∧ u.rawDa = 0 ∧
    u.declared ≤ 8192 ∧ u.coverage ≤ 8192 ∧ u.childClaims ≤ 8192) ∨
  (u.children ≤ 4 ∧ u.rawXmss + u.rawSphincs = 0 ∧ u.rawDaRows ≤ 32 ∧
    u.declared ≤ 8192 ∧ u.coverage ≤ 8192 ∧ u.childClaims ≤ 8192) ∨
  (u.children ≤ 2 ∧ u.rawXmss + u.rawSphincs ≤ 256 ∧ u.rawDaRows ≤ 32 ∧
    u.declared ≤ 8192 ∧ u.coverage ≤ 8192 ∧ u.childClaims ≤ 8192) ∨
  (u.children ≤ 2 ∧ u.rawXmss + u.rawSphincs = 0 ∧ u.rawDaRows ≤ 32 ∧
    u.declared ≤ 2 ^ 14 ∧ u.coverage ≤ 2 ^ 14 ∧ u.childClaims ≤ 2 ^ 14) ∨
  (u.children = 0 ∧ u.rawXmss + u.rawSphincs = 0 ∧ u.rawDaRows ≤ 32 ∧
    u.declared ≤ 2 ^ 15 ∧ u.coverage ≤ 2 ^ 15)

theorem covered_iff (s : NodeStatement) (w : NodeWitness) : Covered s w ↔ CoveredW (work s w) :=
  Iff.rfl

/-- **Every covered node has a valid execution of the guest.** -/
theorem guest_complete_covered : GuestCompleteCovered := by
  intro seed s w hrel hlim hok hcov
  replace hcov := (covered_iff s w).1 hcov
  have hlen : (work s w).childShapes.length = (work s w).children := by simp [work]
  have hch : (work s w).children ≤ 16 := by simpa [work] using hlim.children
  have hda : (work s w).rawDa ≤ 1 := by simpa [work] using hlim.directDa
  have hrows : (work s w).rawDa = 0 → (work s w).rawDaRows = 0 := by
    intro hd
    simp only [work, List.length_eq_zero_iff] at hd ⊢
    simp [hd]
  have hpad0 : (work s w).rawDa = 0 → (work s w).rawDaPad = 0 := by
    intro hd
    simp only [work, List.length_eq_zero_iff] at hd ⊢
    simp [hd]
  have hpad : (work s w).rawDaRows ≤ 32 → (work s w).rawDaPad ≤ 32 := fun h ↦ by
    simpa using pad_le (k := 5) hlim.directDa (by simpa using h)
  have hshapes : (work s w).children = 0 → (work s w).childShapes = [] ∧
      (work s w).childClaims = 0 := by
    intro h0
    simp only [work, List.length_eq_zero_iff] at h0 ⊢
    simp [h0]
  refine guest_complete_numeric seed s w hrel hlim hok ?_
  rcases hcov with ⟨hraw, hd, hdecl, hcov, hcc⟩ | ⟨h0, hd, hraw, hdecl, hcov⟩ |
    ⟨hk, hraw, hd, hdecl, hcov, hcc⟩ | ⟨hk, hraw, hd, hdecl, hcov, hcc⟩ |
    ⟨hk, hraw, hr, hdecl, hcov, hcc⟩ | ⟨hk, hraw, hr, hdecl, hcov, hcc⟩ |
    ⟨hk, hraw, hr, hdecl, hcov, hcc⟩ | ⟨h0, hraw, hr, hdecl, hcov⟩
  · exact recursion_size_le _ (by omega) (by omega) hd (hrows hd) (hpad0 hd) hdecl hcov hcc hch
      (by omega)
  · obtain ⟨hsh, hcc⟩ := hshapes h0
    exact leaf_size_le _ hraw hd (hrows hd) (hpad0 hd) hdecl hcov h0 hcc hsh
  · exact narrow_size_le _ hraw hd (hrows hd) (hpad0 hd) hdecl hcov hcc hk (by omega)
  · exact mixed_size_le _ hraw hd (hrows hd) (hpad0 hd) hdecl hcov hcc hk (by omega)
  · exact blob_size_le _ hraw hda hr (hpad hr) hdecl hcov hcc hk (by omega)
  · exact blobMixed_size_le _ hraw hda hr (hpad hr) hdecl hcov hcc hk (by omega)
  · exact blobWide_size_le _ hraw hda hr (hpad hr) hdecl hcov hcc hk (by omega)
  · obtain ⟨hsh, hcc⟩ := hshapes h0
    exact blobLeaf_size_le _ hraw hda hr (hpad hr) hdecl hcov hcc h0 (by simp [hsh])

end
end LeanVM.Guest.Budget
