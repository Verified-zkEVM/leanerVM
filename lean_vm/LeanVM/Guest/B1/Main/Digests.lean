/-
  LeanVM.Guest.B1.Main.Digests

  The digests of decoded statements: claim lists read off cells hash as the cells, and a
  statement's digest is the bytes `statement_digest` hashes.
-/

module

public import LeanVM.Guest.B1.Main.Decode

/-!
# Decoded digests

* `slotCells_of_loads`: a slot's four cells, from four loads;
* `xmss_digest`, `sphincs_digest`, `da_digest`: a list of claims decoded at slots whose cells are
  `cells`, four a slot, hashes as `cells`;
* `signers_eq`: the signer set's digest of two lists of digests `[cx0, cx1]`, `[cs0, cs1]`;
* `statementDigest_parts`: a statement's digest from the bytes of its header cells and deferred
  cells (`stmtBytes`);
* `deferOfCells_cells`, `fixedOfCells_cells`, `readCells_of_readsAt`: the deferred claims of
  `24` cells.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

variable {rd : Reader}

/-! ## Slots -/

theorem slotCells_of_loads {p : E} {o : ℕ} {v : ℕ → E}
    (h : ∀ i < 4, LoadHolds rd p (4 * o + i) (v i)) :
    slotCells rd p o = [v 0, v 1, v 2, v 3] := by
  simp only [slotCells, readCells_eq_memRun, memRun, List.range_succ, List.range_zero,
    List.nil_append, List.map_cons, List.map_nil, List.cons_append]
  have hl : ∀ k < 4, memAt rd (p * gen ^ (4 * o)) k = v k := fun k hk =>
    memAt_of_load ((loadHolds_mul_gen_pow rd p _ _ _).mpr (h k hk))
  rw [hl 0 (by omega), hl 1 (by omega), hl 2 (by omega), hl 3 (by omega)]

/-- The slots `o j`, `j < n`, of the table at `p` hold `cells`, four a slot. -/
def SlotsHold (rd : Reader) (p : E) (o : ℕ → ℕ) (n : ℕ) (cells : List E) : Prop :=
  cells.length = 4 * n ∧ ∀ j < n, ∀ i < 4, LoadHolds rd p (4 * o j + i) (cells.getD (4 * j + i) 0)

theorem slotsHold_of_readsAt {p : E} {n : ℕ} {cells : List E} (h : ReadsAt rd p cells)
    (hl : cells.length = 4 * n) : SlotsHold rd p id n cells := by
  refine ⟨hl, fun j hj i hi => ?_⟩
  have := h (4 * j + i) (by omega)
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem slotCells_slots {p : E} {o : ℕ → ℕ} {n : ℕ} {cells : List E} (h : SlotsHold rd p o n cells)
    {j : ℕ} (hj : j < n) :
    slotCells rd p (o j) = [cells.getD (4 * j) 0, cells.getD (4 * j + 1) 0,
      cells.getD (4 * j + 2) 0, cells.getD (4 * j + 3) 0] :=
  slotCells_of_loads (v := fun i => cells.getD (4 * j + i) 0) (h.2 j hj)

/-- A list of claims decoded at the slots `o j` of a table hashes as the slots' cells. -/
theorem claims_digest {α : Type} (dec : E → E → E → E → α) (bytes : α → List UInt8)
    (hb : ∀ a b c d, bytes (dec a b c d) = cellsBytes [a, b, c, d]) {p : E} {o : ℕ → ℕ} {n : ℕ}
    {cells : List E} (h : SlotsHold rd p o n cells) :
    ((List.range n).map fun j => let c := slotCells rd p (o j)
      dec (c.getD 0 0) (c.getD 1 0) (c.getD 2 0) (c.getD 3 0)).flatMap bytes = cellsBytes cells := by
  rw [← flatMap_slots dec bytes hb cells n h.1]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  rw [slotCells_slots h (List.mem_range.mp hj)]
  rfl

theorem xmss_digest {p : E} {o : ℕ → ℕ} {n : ℕ} {cells : List E} (h : SlotsHold rd p o n cells) :
    xmssListDigest ((List.range n).map fun j => xmssAt rd p (o j)) = keccak256 (cellsBytes cells) := by
  unfold xmssListDigest
  rw [← claims_digest Sig.xmssClaimOf (fun c : XmssClaim => claimBytes c.1.root c.1.parameter c.2)
    (fun a b c d => claimBytes_cells a b c d) h]
  rfl

theorem sphincs_digest {p : E} {o : ℕ → ℕ} {n : ℕ} {cells : List E} (h : SlotsHold rd p o n cells) :
    sphincsListDigest ((List.range n).map fun j => sphincsAt rd p (o j)) =
      keccak256 (cellsBytes cells) := by
  unfold sphincsListDigest
  rw [← claims_digest Sig.sphincsClaimOf
    (fun c : SphincsClaim => claimBytes c.1.root c.1.parameter c.2)
    (fun a b c d => claimBytes_cells a b c d) h]
  rfl

theorem da_digest {p : E} {o : ℕ → ℕ} {n : ℕ} {cells : List E} (h : SlotsHold rd p o n cells) :
    daListDigest ((List.range n).map fun j => daAt rd p (o j)) = keccak256 (cellsBytes cells) := by
  unfold daListDigest
  rw [← claims_digest (fun a b c d => (digestOfCells a b, digestOfCells c d))
    (fun c : DaClaim => digestBytes c.1 ++ digestBytes c.2)
    (fun a b c d => by
      simp only [digestBytes_ofCells, cellsBytes, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc]) h]
  rfl

theorem xmss_digest_id {p : E} {n : ℕ} {cells : List E} (h : SlotsHold rd p id n cells) :
    xmssListDigest ((List.range n).map (xmssAt rd p)) = keccak256 (cellsBytes cells) :=
  xmss_digest h

theorem sphincs_digest_id {p : E} {n : ℕ} {cells : List E} (h : SlotsHold rd p id n cells) :
    sphincsListDigest ((List.range n).map (sphincsAt rd p)) = keccak256 (cellsBytes cells) :=
  sphincs_digest h

theorem da_digest_id {p : E} {n : ℕ} {cells : List E} (h : SlotsHold rd p id n cells) :
    daListDigest ((List.range n).map (daAt rd p)) = keccak256 (cellsBytes cells) :=
  da_digest h

/-! ## The statement -/

theorem digestBytes_of_cells {d : Digest} {a b : E} (h : [a, b] = digestCells d) :
    digestBytes d = cellsBytes [a, b] := by
  rw [digestBytes_eq_cells]
  simp only [digestCells, List.cons.injEq, and_true] at h
  rw [h.1, h.2]

/-- **The signer set's digest**, of lists whose digests are `[cx0, cx1]`, `[cs0, cs1]`. -/
theorem signers_eq {xs : List XmssClaim} {ss : List SphincsClaim} {cx0 cx1 cs0 cs1 : E}
    (hx : [cx0, cx1] = digestCells (xmssListDigest xs))
    (hs : [cs0, cs1] = digestCells (sphincsListDigest ss)) :
    signersDigest xs ss = keccak256 (cellsBytes [cx0, cx1, cs0, cs1]) := by
  unfold signersDigest
  rw [digestBytes_of_cells hx, digestBytes_of_cells hs]
  simp [cellsBytes]

theorem cellsBytes_six (a b c d e f : E) :
    cellsBytes [a, b, c, d, e, f] = cellsBytes [a, b] ++ cellsBytes [c, d] ++ cellsBytes [e, f] := by
  simp [cellsBytes]

/-- **A statement's digest from its parts**: the header cells' bytes and the 24 deferred cells. -/
theorem statementDigest_parts {seed : Digest} {s : NodeStatement} {s0 s1 h0 h1 d0 d1 : E}
    {defer : List E} (hseed : digestBytes seed = cellsBytes [s0, s1])
    (hsig : digestBytes (signersDigest s.claims.xmss s.claims.sphincs) = cellsBytes [h0, h1])
    (hda : digestBytes (daListDigest s.claims.da) = cellsBytes [d0, d1])
    (hdef : s.defer.cells = defer) (hlen : defer.length = 24) :
    statementDigest seed s = keccak256 (stmtBytes [s0, s1, h0, h1, d0, d1] defer) := by
  unfold statementDigest stmtBytes
  rw [hseed, hsig, hda, hdef, hlen, cellsBytes_six]
  simp

/-! ## Deferred claims of 24 cells -/

theorem readCells_of_readsAt {p : E} {cells : List E} (h : ReadsAt rd p cells) (hl : cells.length = 24) :
    readCells rd p 24 = cells := by
  rw [readCells_eq_memRun, ← hl, ← readsAt_memRun h]

theorem deferOfCells_cells {cells : List E} (hl : cells.length = 24) :
    (deferOfCells cells).cells = cells := by
  have hb : bytecodeVars = 23 := rfl
  unfold deferOfCells DeferredClaim.cells
  rw [hb, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  simp only
  rw [← List.take_succ_eq_append_getElem (by omega), List.take_of_length_le (by omega)]

theorem deferOfCells_point {cells : List E} (hl : cells.length = 24) :
    (deferOfCells cells).bytecodePoint.length = bytecodeVars := by
  simp [deferOfCells, hl, bytecodeVars]

theorem fixedOfCells_cells {f : FixedClaims} (hl : f.bytecodePoint.length = bytecodeVars) :
    fixedOfCells (fixedCells f) = f := by
  have hb : bytecodeVars = 23 := rfl
  unfold fixedOfCells fixedCells
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl]
  simp

end
end LeanVM.Guest.B1.Main
